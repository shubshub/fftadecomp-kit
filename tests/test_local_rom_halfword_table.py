"""Synthetic closed table-copy tests with an independent raw Thumb oracle."""
import copy
import json
from pathlib import Path
import struct
import sys
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parents[1]
sys.dont_write_bytecode = True
sys.path.insert(0, str(HERE / 'tools'))
import match
import owner_admission_profile as owner
import local_rom_halfword_table_profile as table

ROOT, HELPER, SOURCE = 0x08000200, 0x08000400, 0x08000800


def bl(site, target):
    delta = target - site - 4
    return struct.pack('<HH', 0xf000 | ((delta >> 12) & 2047),
                       0xf800 | ((delta >> 1) & 2047))


def fixture(root=ROOT, helper=HELPER, source=SOURCE):
    root_words = [0xb510, 0xb082, 0x1c04, 0x0624, 0x0e24, 0x4906,
                  0x4668, 0x2208, 0, 0, 0x0064, 0x4669, 0x1908,
                  0x8800, 0xb002, 0xbc10, 0xbc02, 0x4708, 0, 0]
    data = bytearray(struct.pack('<20H', *root_words))
    data[16:20] = bl(root+16, helper)
    struct.pack_into('<I', data, 36, source)
    # Synthetic instruction assembly, independent of production byte constants.
    copy_words = [0xb530,0x1c05,0x1c2c,0x1c0b,0x2a0f,0xd919,
        0x1c18,0x4328,0x2103,0x4008,0x2800,0xd113,0x1c29,
        0xcb01,0xc101,0xcb01,0xc101,0xcb01,0xc101,0xcb01,0xc101,
        0x3a10,0x2a0f,0xd8f4,0x2a03,0xd904,0xcb01,0xc101,
        0x3a04,0x2a03,0xd8fa,0x1c0c,0x3a01,0x2001,0x4240,
        0x4282,0xd007,0x1c01,0x7818,0x7020,0x3301,0x3401,
        0x3a01,0x428a,0xd1f8,0x1c28,0xbc30,0xbc02,0x4708]
    helper_body = struct.pack('<49H', *copy_words)
    rom = bytearray(max(root+40, helper+98, source+8)-match.ROM_BASE)
    for address, raw in ((root,data),(helper,helper_body),
                         (source,bytes.fromhex('0001ff7f0080ffff'))):
        rom[address-match.ROM_BASE:address-match.ROM_BASE+len(raw)] = raw
    rows = [dict(rom=f'0x{a:08X}',end=f'0x{a+n:08X}',mode='thumb',instrs=c)
            for a,n,c in ((root,40,17),(helper,98,49))]
    return dict(root=root,helper=helper,source=source,data=bytes(data),rom=bytes(rom),
        mapping=json.dumps(rows).encode(),
        index=''.join(f'{a:08X} {a+n:08X} {n} {c} bx\n'
                      for a,n,c in ((root,40,17),(helper,98,49))).encode(),
        objects=json.dumps({'table_source':f'0x{source:08X}'}).encode(),
        bindings=dict(calls=[[16,f'func_{helper:08X}']],data=[[36,'table_source',0]],
                      functions=[],switches=[]))


def prove(env, expected=None, fingerprint='a'*64, selector=table.SELECTOR):
    return owner.verify(env['data'],env['root'],env['rom'],env['mapping'],env['index'],
        env['objects'],expected,bindings=env['bindings'],selector=selector,
        source_fingerprint=fingerprint)


def original_elf(env, helper_type=2, data_type=1, addend=0):
    raw_text=bytearray(env['data'])
    raw_text[16:20]=bl(env['root']+16,env['root']+16)
    struct.pack_into('<I',raw_text,36,addend)
    rows=[('',0,0,0,0),(f'func_{env["root"]:08X}',1,40,0x12,1),
          (f'func_{env["helper"]:08X}',0,0,0x10|helper_type,0),
          ('table_source',0,0,0x10|data_type,0)]
    strings=bytearray(b'\0');symbols=bytearray()
    for name,value,size,info,section in rows:
        offset=len(strings);strings+=name.encode()+b'\0'
        symbols+=struct.pack('<IIIBBH',offset,value,size,info,0,section)
    rel=struct.pack('<IIII',16,(2<<8)|10,36,(3<<8)|2)
    names=b'\0.text\0.symtab\0.strtab\0.rel.text\0.shstrtab\0'
    raw=bytearray(52);offsets=[]
    for part in (raw_text,symbols,strings,rel,names):
        while len(raw)%4:raw+=b'\0'
        offsets.append(len(raw));raw+=part
    sections=[(0,0,0,0,0,0,0,0,0,0),
        (1,1,6,0,offsets[0],40,0,0,4,0),
        (7,2,0,0,offsets[1],len(symbols),3,1,4,16),
        (15,3,0,0,offsets[2],len(strings),0,0,1,0),
        (23,9,0,0,offsets[3],len(rel),2,1,4,8),
        (33,3,0,0,offsets[4],len(names),0,0,1,0)]
    while len(raw)%4:raw+=b'\0'
    shoff=len(raw);raw+=b''.join(struct.pack('<10I',*row) for row in sections)
    raw[:16]=b'\x7fELF\x01\x01\x01'+b'\0'*9
    struct.pack_into('<HHIIIIIHHHHHH',raw,16,1,40,1,0,0,shoff,0,52,0,0,40,6,5)
    return bytes(raw)


def raw_run(env, index, sp, saved4, saved5):
    """Decode raw opcodes, perform concrete accesses, reject every unknown op.

    No production recognizer, transition, constants, graph or relation is used.
    """
    memory = {match.ROM_BASE+i:b for i,b in enumerate(env['rom'])}
    initial = [0x17395101+i*0x010101 for i in range(16)]
    initial[0], initial[4], initial[5], initial[13], initial[14] = index,saved4,saved5,sp,0x09123457
    registers = list(initial)
    pc, zero, carry, writes, trace = env['root'],False,False,[],[]

    def read(address, size):
        return sum(memory[address+i] << (8*i) for i in range(size))

    def write(address, value, size):
        for i in range(size):
            memory[address+i] = (value >> (8*i)) & 255
            writes.append((address+i, memory[address+i]))

    def cmp(a,b):
        return a == b, a >= b

    def sign(value,bits):
        return value - (1 << bits) if value & (1 << (bits-1)) else value

    for _ in range(256):
        trace.append(pc)
        instruction = read(pc,2)
        next_pc = pc+2
        if instruction & 0xfe00 == 0xb400:
            regs = [r for r in range(8) if instruction & (1 << r)]
            if instruction & 256: regs.append(14)
            registers[13] -= 4*len(regs)
            for n,r in enumerate(regs):write(registers[13]+4*n,registers[r],4)
        elif instruction & 0xfe00 == 0xbc00:
            assert not instruction & 256
            for r in range(8):
                if instruction & (1 << r):
                    registers[r]=read(registers[13],4);registers[13]+=4
        elif instruction & 0xff00 == 0xb000:
            registers[13] += (-1 if instruction & 128 else 1)*4*(instruction & 127)
        elif instruction & 0xf800 == 0xf000:
            low = read(pc+2,2);assert low & 0xf800 == 0xf800
            delta = sign(((instruction & 2047) << 12) | ((low & 2047) << 1),23)
            registers[14]=pc+5;next_pc=pc+4+delta
        elif instruction & 0xff87 == 0x4700:
            value=registers[(instruction >> 3) & 15]
            assert value & 1
            if value == initial[14]:
                return dict(registers=registers,initial=initial,memory=memory,writes=writes,trace=trace)
            next_pc=value & ~1
        elif instruction & 0xff00 == 0x4600:
            destination=(instruction & 7) | ((instruction >> 4) & 8)
            registers[destination]=registers[(instruction >> 3) & 15]
        elif instruction & 0xf800 in (0x0000,0x0800):
            destination, source, shift = instruction & 7,(instruction >> 3) & 7,(instruction >> 6) & 31
            registers[destination] = ((registers[source] << shift) & 0xffffffff
                if instruction & 0xf800 == 0 else registers[source] >> (shift or 32))
        elif instruction & 0xf800 == 0x1800:
            destination, left = instruction & 7,(instruction >> 3) & 7
            right=(instruction >> 6) & 7
            value=right if instruction & 1024 else registers[right]
            registers[destination]=(registers[left]+(-value if instruction & 512 else value)) & 0xffffffff
        elif instruction & 0xf800 == 0x2000:
            registers[(instruction >> 8) & 7] = instruction & 255
        elif instruction & 0xf800 in (0x3000,0x3800):
            destination=(instruction >> 8) & 7
            registers[destination]=(registers[destination]+(-1 if instruction & 0x800 else 1)*(instruction & 255)) & 0xffffffff
        elif instruction & 0xf800 == 0x2800:
            zero,carry=cmp(registers[(instruction >> 8) & 7],instruction & 255)
        elif instruction & 0xffc0 == 0x4280:
            zero,carry=cmp(registers[instruction & 7],registers[(instruction >> 3) & 7])
        elif instruction & 0xffc0 == 0x4240:
            registers[instruction & 7]=(-registers[(instruction >> 3) & 7]) & 0xffffffff
        elif instruction & 0xf000 == 0xd000:
            condition=(instruction >> 8) & 15
            take={0:zero,1:not zero,9:(not carry or zero)}[condition]
            if take: next_pc=pc+4+sign(instruction & 255,8)*2
        elif instruction & 0xf800 == 0x4800:
            registers[(instruction >> 8) & 7]=read(((pc+4)&~3)+4*(instruction & 255),4)
        elif instruction & 0xf800 in (0x7800,0x8800):
            size=1 if instruction & 0xf800 == 0x7800 else 2
            address=registers[(instruction >> 3) & 7]+size*((instruction >> 6)&31)
            registers[instruction & 7]=read(address,size)
        elif instruction & 0xf800 == 0x7000:
            write(registers[(instruction >> 3)&7]+((instruction >> 6)&31),registers[instruction&7],1)
        else:
            raise AssertionError(f'unsupported raw opcode {instruction:04X} at {pc:08X}')
        pc=next_pc
    raise AssertionError('raw execution exceeded closed instruction bound')


class TableTests(unittest.TestCase):
    def test_complete_generic_owner_helper_and_explicit_conditions(self):
        env=fixture();manifest,instructions=prove(env)
        effect=manifest['proof']['local_rom_halfword_table']
        self.assertEqual(len(instructions),17)
        self.assertEqual(effect['combined_frame'],[-28,0])
        self.assertFalse(effect['all_u8_inputs_in_bounds'])
        self.assertFalse(effect['physical_access_proved'])
        self.assertEqual([case['R0'] for case in effect['cases']],[256,32767,32768,65535])
        self.assertEqual(manifest['profile'],table.SCHEMA)

    def test_independent_raw_oracle_all_valid_indices_and_opaque_saves(self):
        env=fixture();manifest,_=prove(env)
        for case in manifest['proof']['local_rom_halfword_table']['cases']:
            for sp,saved4,saved5 in ((0x03007f00,0xdeadbeef,0x08001235),
                                   (0x02000100,0,0xffffffff)):
                index=case['index'];run=raw_run(env,0xabcd0000|index,sp,saved4,saved5)
                registers=run['registers']
                self.assertEqual(registers[0],case['R0'])
                self.assertEqual(registers[1:4],[run['initial'][14],0xffffffff,env['source']+8])
                for r in (4,5,6,7,8,9,10,11,12,13):
                    self.assertEqual(registers[r],run['initial'][r])
                expected=[]
                tokens={'entry_R4':saved4,'entry_R5':saved5,'entry_LR':run['initial'][14],
                        'root_BL_return':env['root']+21}
                for _,offset,value in case['writes']:
                    if isinstance(value,str):
                        token,byte=value.rsplit('.',1);value=(tokens[token] >> (8*int(byte))) & 255
                    expected.append((sp+offset,value))
                self.assertEqual(run['writes'],expected)
                self.assertEqual(sum(pc==env['helper']+76 for pc in run['trace']),8)

    def test_relocated_root_helper_and_source_are_not_address_whitelisted(self):
        env=fixture(0x08001000,0x08000800,0x08001800)
        manifest,_=prove(env)
        run=raw_run(env,3,0x02000100,13,17)
        self.assertEqual(manifest['proof']['local_rom_halfword_table']['cases'][3]['R0'],run['registers'][0])

    def test_numeric_domain_has_no_physical_permission(self):
        result=table.concrete_domain(0x03007f00,0x12340003,SOURCE,ROOT,HELPER)
        self.assertEqual(result['index'],3)
        self.assertFalse(result['physical_access_granted'])
        self.assertFalse(result['noninterference_granted'])

    def test_no_u8_bounds_assumption(self):
        for index in (4,255,-1,True):
            with self.subTest(index=index),self.assertRaises(ValueError):table.relation(b'\0'*8,index)
        for index in (4,255,0x123400ff):
            with self.subTest(index=index),self.assertRaises(ValueError):
                table.concrete_domain(0x03007f00,index,SOURCE,ROOT,HELPER)

    def test_reject_frame_wrap_alignment_and_source_code_aliases(self):
        for sp in (0,24,0x03000001,SOURCE+4,SOURCE+28,ROOT+28,HELPER+28):
            with self.subTest(sp=sp),self.assertRaises(ValueError):table.concrete_domain(sp,0,SOURCE,ROOT,HELPER)

    def test_every_root_opcode_is_closed(self):
        env=fixture()
        for offset in (0,2,4,6,8,10,12,14,20,22,24,26,28,30,32,34):
            # Bit 0 of the final bx is should-be-zero on ARMv4T, so change its register instead.
            changed=copy.deepcopy(env);body=bytearray(changed['data']);body[offset]^=8 if offset==34 else 1
            changed['data']=bytes(body);rom=bytearray(changed['rom']);rom[ROOT-match.ROM_BASE:ROOT-match.ROM_BASE+40]=body;changed['rom']=bytes(rom)
            with self.subTest(offset=offset),self.assertRaisesRegex(
                    ValueError,'root instruction grammar differs|structural inventory is not closed'):prove(changed)

    def test_complete_helper_including_unreached_path_is_bound(self):
        env=fixture()
        for offset in range(0,98,2):
            changed=copy.deepcopy(env);rom=bytearray(changed['rom']);rom[HELPER-match.ROM_BASE+offset]^=1;changed['rom']=bytes(rom)
            with self.subTest(offset=offset),self.assertRaises(ValueError):prove(changed)

    def test_counts_are_exact_in_both_indices(self):
        for owner_index in (0,1):
            for member in ('mapping','index'):
                env=fixture()
                if member=='mapping':
                    rows=json.loads(env[member]);rows[owner_index]['instrs']+=1;env[member]=json.dumps(rows).encode()
                else:
                    rows=env[member].decode().splitlines();words=rows[owner_index].split();words[3]=str(int(words[3])+1);rows[owner_index]=' '.join(words);env[member]='\n'.join(rows).encode()
                with self.subTest(owner_index=owner_index,member=member),self.assertRaises(ValueError):prove(env)

    def test_duplicate_overlapping_and_changed_spans_refused(self):
        for kind in ('duplicate','overlap','short','mode'):
            env=fixture();rows=json.loads(env['mapping'])
            if kind=='duplicate':rows.append(dict(rows[1]))
            elif kind=='overlap':rows.append(dict(rom=f'0x{HELPER+2:08X}',end=f'0x{HELPER+4:08X}',mode='thumb',instrs=1))
            elif kind=='short':rows[1]['end']=f'0x{HELPER+96:08X}'
            else:rows[1]['mode']='arm'
            env['mapping']=json.dumps(rows).encode()
            with self.subTest(kind=kind),self.assertRaises(ValueError):prove(env)

    def test_typed_bindings_cannot_supply_new_effects(self):
        for kind in ('call','data','addend','extra','alias','unmapped'):
            env=fixture()
            if kind=='call':env['bindings']['calls'][0][1]='func_08000900'
            elif kind=='data':env['bindings']['data'][0][1]='other'
            elif kind=='addend':env['bindings']['data'][0][2]=4
            elif kind=='extra':env['bindings']['functions']=[[36,'func_08000900']]
            elif kind=='alias':env['objects']=json.dumps({'table_source':hex(SOURCE),'alias':hex(SOURCE)}).encode()
            else:env['objects']=b'{}'
            with self.subTest(kind=kind),self.assertRaises(ValueError):prove(env)

    def test_source_requires_all_eight_rom_bytes(self):
        env=fixture();env['rom']=env['rom'][:-1]
        with self.assertRaises(ValueError):prove(env)

    def test_missing_or_invalid_source_fingerprint_refused(self):
        for value in (None,'a'*63,'A'*64,True):
            with self.subTest(value=value),self.assertRaises(ValueError):prove(fixture(),fingerprint=value)

    def test_changed_manifest_and_source_context_refused(self):
        env=fixture();manifest,_=prove(env)
        changed=copy.deepcopy(manifest)
        changed['proof']['local_rom_halfword_table']['cases'][0]['R0']+=1
        with self.assertRaises(ValueError):prove(env,changed)
        with self.assertRaises(ValueError):prove(env,manifest,fingerprint='b'*64)

    def test_old_default_guards_and_original_elf_preflight_remain(self):
        for selector in (owner.SELECTOR,owner.ACYCLIC_SELECTOR):
            with self.subTest(selector=selector),self.assertRaises(ValueError):prove(fixture(),selector=selector)
        env=fixture()
        with self.assertRaisesRegex(ValueError,'original ELF'):
            owner.preflight(env['data'],ROOT,env['rom'],env['mapping'],env['index'],env['objects'],selector=table.SELECTOR)

    def test_report_dispatch_and_original_elf_fingerprint_required(self):
        report=f'* verification: `{table.SCHEMA}`'
        self.assertTrue(owner.selected(report))
        self.assertEqual(owner.selector_for_report(report),table.SELECTOR)
        env=fixture();manifest,_=prove(env)
        with self.assertRaisesRegex(ValueError,'original ELF'):
            owner.fingerprint(ROOT,env['data'],manifest,'a'*64,env['mapping'],env['index'],env['objects'],env['rom'])


class TableAdmissionTests(unittest.TestCase):
    def test_genuine_original_function_and_data_relocations(self):
        env=fixture()
        bindings,targets=owner.original_bindings(match.elf_image(original_elf(env)),ROOT,
            env['rom'],env['mapping'],env['objects'],selector=table.SELECTOR,index=env['index'])
        self.assertEqual(bindings,env['bindings'])
        self.assertEqual(targets,{'func_08000400':(HELPER,False),'table_source':(SOURCE,True)})
        for types in ((1,1),(2,2)):
            with self.subTest(types=types),self.assertRaises(ValueError):
                owner.original_bindings(match.elf_image(original_elf(env,*types)),ROOT,
                    env['rom'],env['mapping'],env['objects'],selector=table.SELECTOR,index=env['index'])
        altered,_=owner.original_bindings(match.elf_image(original_elf(env,addend=4)),ROOT,
            env['rom'],env['mapping'],env['objects'],selector=table.SELECTOR,index=env['index'])
        env['bindings']=altered
        with self.assertRaisesRegex(ValueError,'zero-addend'):prove(env)

    def test_report_render_keeps_original_and_conditions(self):
        env=fixture();manifest,_=prove(env);original=original_elf(env)
        result=(env['data'],manifest,'a'*64,env['mapping'],env['index'],env['objects'],env['rom'],17,original)
        report=owner.render(ROOT,result)
        self.assertIn(f'* owner runtime: {table.SELECTOR}',report)
        self.assertIn(f'* control flow: {table.CONTROL_FLOW}',report)
        self.assertIn(table.sha(original),report)
        self.assertIn('no bound is inferred from u8 narrowing',report)
        with patch.object(owner,'build',return_value=result) as build:
            self.assertTrue(owner.report_matches(report,HERE,ROOT))
        self.assertEqual(build.call_args.kwargs['selector'],table.SELECTOR)

    def test_mixed_cli_policies_are_rejected_before_build(self):
        import argparse
        values=dict(mode='thumb',control_flow_profile='ordinary',software_double_profile=None,
            software_double_remainder_profile=None,function_address_profile=None,switch_profile=None,
            label=None,wsl='Ubuntu',wsl_path=match.DEFAULT_WSL_PATH,owner_runtime_profile=table.SELECTOR,
            signed_quotient_profile=None,signed_runtime_profile=None,unsigned_runtime_profile=None,
            addressed_signed_runtime_profile=None,switch_data_profile=None)
        for key in ('function_address_profile','signed_runtime_profile','unsigned_runtime_profile','switch_data_profile'):
            with self.subTest(key=key),patch.object(owner,'build') as build,self.assertRaises(ValueError):
                owner.issue(HERE,ROOT,argparse.Namespace(**dict(values,**{key:'forged'})))
            build.assert_not_called()


if __name__ == '__main__':
    unittest.main()
