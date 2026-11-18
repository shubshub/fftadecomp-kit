import argparse
import copy
import json
import os
from pathlib import Path
import random
import subprocess
import struct
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import library_units as units
import match
import match_evidence as evidence
import software_float_profile as runtime
import unit_double_multiply as mul
from test_unit_double_add_parts import OriginalCPU, ieee_bits, ieee_value, RECORD, FIXED, ONE, SIGN, INF, QUIET

MASK = (1 << 52)-1


def finite_components(bits):
    exponent, fraction = (bits >> 52) & 0x7ff, bits & MASK
    if exponent:
        return exponent-1023, fraction | (1 << 52)
    shift = 53-fraction.bit_length()
    return -1022-shift, fraction << shift


def expected_product(a, b, fixed):
    """Independent exact product plus the historical packer's subnormal rule."""
    sign = (a ^ b) & SIGN
    x, y = a & (SIGN-1), b & (SIGN-1)
    if x > INF or y > INF:
        return sign | QUIET | (x if x > INF else y)
    if x == INF or y == INF:
        return fixed if min(x, y) == 0 else sign | INF
    if x == 0 or y == 0:
        return sign
    ae, am = finite_components(x)
    be, bm = finite_components(y)
    product = am*bm
    exp = ae+be+product.bit_length()-105
    if exp >= -1022:
        return ieee_bits(ieee_value(a)*ieee_value(b))
    high, tail = divmod(product, 1 << (product.bit_length()-61))
    if high & 255 == 128 and (high & 256 or tail):
        high += 128
    return sign | high >> (-1022-exp+8)


@unittest.skipUnless(os.getenv('FFTA_DP_MULTIPLY_ROOT'), 'requires the original USA ROM and recovered double sources')
class DoubleMultiplyTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        from rompath import rom_path
        cls.root = Path(os.environ['FFTA_DP_MULTIPLY_ROOT']).resolve()
        cls.rom = Path(rom_path(cls.root)).read_bytes()
        cls.mapping, cls.index = evidence.mapping_snapshot(cls.root), runtime.index_snapshot(cls.root)
        cls.objects = evidence.data_snapshot(cls.root)
        cls.body, cls.report = mul.build(cls.root, mul.ADDRESS)
        tool = units.resolve(mul.TOOLCHAIN)
        runner = match.Runner(tool['cc'], root=cls.root, timeout=120)
        args = argparse.Namespace(cc=tool['cc'], flags=tool['flags'], cpp=match.DEFAULT_CPP,
                                  assembler=match.DEFAULT_AS, linker=match.DEFAULT_LD, objcopy=match.DEFAULT_OBJCOPY)
        with runner.workspace() as workspace:
            _, _, cls.original = match.compile_object(runner, workspace, args, cls.root, mul.ADDRESS, 'src/081430F0.c')
            cls.linked = match.link_typed_targets(runner, workspace, args, 'func_081430F0', mul.ADDRESS,
                                                  mul.TARGETS, {mul.DATA})

    def test_source_abi_and_original_and_linked_binding_controls(self):
        unit = units.containing(units.load(self.root), mul.ADDRESS, mul.END)
        self.assertIn(mul.SCHEMA, units.schemas(unit, mul.ADDRESS))
        for key, value in (('name', 'libgcc fp-bit'), ('identity', []), ('proof', '0x08142BE8'),
                           ('end', '0x081439C4'), ('toolchain', 'agbcc-O1-v1')):
            row = dict(unit.row, **{key: value})
            self.assertNotIn(mul.SCHEMA, units.schemas(units.Unit(row, units.canonical(row)), mul.ADDRESS))
        self.assertNotIn(mul.SCHEMA, units.schemas(unit, mul.ADDRESS, {}))
        self.assertNotIn(mul.SCHEMA, units.schemas(unit, mul.ADDRESS+2))
        relative = Path('src/081430F0.c')
        with tempfile.TemporaryDirectory(dir=self.root/'build') as directory:
            tree = Path(directory)
            for name in ('include/ffta.h', mul.HEADER[0], relative):
                dest = tree/name
                dest.parent.mkdir(exist_ok=True)
                dest.write_bytes((self.root/name).read_bytes())
            for name, old, new in ((relative,'ml * nh','ml * nl'), (relative,'mh * nh','__muldi3(mh, nh)'),
                                   (relative,'(const encoded_double *)&second','(const encoded_double *)&first'),
                                   (mul.HEADER[0], 's32 normal_exp;', 'u32 normal_exp;')):
                path = tree/name
                before = path.read_text()
                self.assertIn(old, before)
                path.write_text(before.replace(old,new))
                with self.subTest(new=new), self.assertRaises(ValueError):
                    mul.check_source(tree, relative)
                path.write_text(before)
        for change in ('remove-limb', 'wrong-limb-target', 'type', 'addend', 'data-weak', 'object-type',
                       'linked-word', 'linked-data-size', 'linked-thumb', 'unrelated-byte'):
            original, linked = copy.deepcopy(self.original), copy.deepcopy(self.linked)
            idx, = original['relocations']
            entries = list(struct.iter_unpack('<II', original['section_data'][idx]))
            at = next(i for i,(off,_) in enumerate(entries) if off == 0x110)
            _,info = entries[at]
            if change == 'remove-limb':
                entries.pop(at)
            elif change == 'wrong-limb-target':
                entries[at] = 0x110, next(value for off,value in entries if off==0x18)
            elif change == 'type':
                entries[at] = 0x110, info & ~255 | 2
            elif change == 'object-type':
                original['type'] = 2
            elif change == 'data-weak':
                next(s for s in original['symbols'] if s['name']==mul.DATA)['bind'] = 2
            elif change == 'linked-data-size':
                next(s for s in linked['symbols'] if s['name']==mul.DATA)['size'] = 20
            elif change == 'linked-thumb':
                next(s for s in linked['symbols'] if s['name']=='__muldi3')['value'] &= ~1
            else:
                image = original if change == 'addend' else linked
                text = bytearray(image['text'])
                text[{'addend':0x110,'linked-word':0x84,'unrelated-byte':0x13e}[change]] ^= 2
                image['text'] = bytes(text)
            original['section_data'][idx] = b''.join(struct.pack('<II', *entry) for entry in entries)
            with self.subTest(change=change), patch.object(match,'link_typed_targets',return_value=linked), self.assertRaises(ValueError):
                mul.link_object(None,None,None,original,self.root,relative,self.rom,self.mapping,self.index)

    def test_native_cfg_caller_and_report_negatives(self):
        saved = (self.root/'docs/match/081430F0.md').read_text()
        self.assertEqual(saved,self.report)
        self.assertTrue(evidence.report_matches(saved,self.root,mul.ADDRESS))
        for old,new in ((mul.CONTROL, 'forged'), ('"instructions":323','"instructions":324'),
                        ('* compiled : `','* compiled : `00')):
            self.assertIn(old,saved)
            self.assertFalse(evidence.report_matches(saved.replace(old,new),self.root,mul.ADDRESS))
        objects = json.loads(self.objects)
        objects[mul.DATA] = '0x03005E54'
        with self.assertRaises(ValueError):
            mul.native_proof(self.body,self.rom,self.mapping,self.index,json.dumps(objects).encode())
        for at in (0x0814316e, 0x08143174, *mul.CALLS, mul.WIDE, mul.PACK, mul.SHIFT,
                   0x081427B8, 0x081428FA, 0x08142906):
            changed = bytearray(self.rom)
            changed[at-match.ROM_BASE] ^= 2
            rom = bytes(changed)
            with self.subTest(at=hex(at)), patch.object(runtime,'ROM_SHA256',units.sha(rom)), self.assertRaises(ValueError):
                mul.native_proof(rom[mul.ADDRESS-match.ROM_BASE:mul.END-match.ROM_BASE],rom,
                                 self.mapping,self.index,self.objects)

    def test_existing_family_schemas_and_link_time_abi(self):
        selectors = {'08142D34':'elf-symbol-thumb-frame-v1', '08143528':'elf-symbol-cfg-leaf-v2'}
        for name, members in (
            ('selected-record', ('08143080','081430B4')), ('inline-division', ('0814339C',)),
            ('comparison', ('0814362C','0814365C','081436AC','081436FC','0814374C','0814379C','081437EC')),
            ('scalar-pack', ('0814383C',)), ('scalar-conversion', ('081438BC',)),
            ('unpack-pack', ('08143930',)), ('truncation', ('08143980',))):
            selectors.update({address: 'elf-symbol-thumb-private-double-'+name+'-v1' for address in members})
        for address, schema in selectors.items():
            report = (self.root/f'docs/match/{address}.md').read_text()
            with self.subTest(address=address):
                self.assertIn(f'* verification: `{schema}`',report)
                self.assertTrue(evidence.report_matches(report,self.root,int(address,16)))

        # Compile and link all twenty original translation units together.
        # The packer, component adder and constructor already used these exact
        # component types and can keep their own historical declarations.
        members = sorted(set(selectors) | {'081430F0','08142BE8','08142E10','08143958'})
        compiler = ['arm-none-eabi-gcc','-mcpu=arm7tdmi','-mthumb','-flto','-fno-builtin',
                    '-O2','-Iinclude','-Werror=lto-type-mismatch']
        with tempfile.TemporaryDirectory(dir=self.root/'build') as directory:
            objects = []
            for address in members:
                obj = Path(directory)/(address+'.o')
                subprocess.run([*compiler,'-c',f'src/{address}.c','-o',obj],cwd=self.root,check=True)
                objects.append(obj)
            subprocess.run([*compiler,'-nostdlib','-r','-flinker-output=nolto-rel',*objects,
                            '-o',Path(directory)/'linked.o'],cwd=self.root,check=True)

    def test_original_limb_visits_rounding_and_conditional_ram_reads(self):
        from unicorn import UC_HOOK_CODE
        cpu = OriginalCPU(self, self.rom)
        limbs = []
        def wide(machine, pc, size, user):
            limbs.append(tuple(machine.reg_read(r) for r in cpu.registers))
        cpu.uc.hook_add(UC_HOOK_CODE,wide,begin=mul.WIDE,end=mul.WIDE)
        rng = random.Random(mul.ADDRESS)
        one = ieee_bits(1.0)
        # (1 + 2^-52) * 1.5 is an exact halfway case with an odd retained LSB.
        pairs = [(0,SIGN),(SIGN,SIGN),(0,INF),(INF,SIGN),(INF,INF|SIGN),(INF,one),
                 (INF|7, INF|QUIET|18|SIGN),(one,INF|3|SIGN),(INF-1,ieee_bits(2.0)),
                 (1,ieee_bits(.75)),(1,ieee_bits(1.5)),((1<<52)-1,ieee_bits(1.5)),
                 (one+1,ieee_bits(1.5)),(one+3,ieee_bits(1.5)),(one+1,ieee_bits(1.5)+1),
                 (one+0xfffffffffffff,one+0xfffffffffffff)]
        pairs += [(rng.getrandbits(64),rng.getrandbits(64)) for _ in range(152)]
        seen = set()
        for fill,record,fixed_bits in ((0xa5,(1,1,15,37),SIGN|INF|QUIET|37),(0x39,(3,0,0,ONE),one)):
            cpu.uc.mem_write(FIXED,RECORD.pack(*record))
            for a,b in pairs:
                limbs.clear()
                high,low = cpu.invoke(mul.ADDRESS,(a>>32,a&0xffffffff,b>>32,b&0xffffffff),fill)
                x,y = a & (SIGN-1), b & (SIGN-1)
                with self.subTest(a=hex(a),b=hex(b),fill=fill):
                    self.assertEqual(high<<32|low,expected_product(a,b,fixed_bits))
                    if 0 < x < INF and 0 < y < INF:
                        af = finite_components(x)[1]<<8
                        bf = finite_components(y)[1]<<8
                        al,ah = af&0xffffffff,af>>32
                        bl,bh = bf&0xffffffff,bf>>32
                        self.assertEqual(limbs,[(bl,0,al,0),(bh,0,al,0),(bl,0,ah,0),(bh,0,ah,0)])
                    else:
                        self.assertEqual(limbs,[])
                    if (x,y) in ((0,INF),(INF,0)):
                        offsets = {0,4,12,16} if record[0]==1 else {0,4,8,12,16}
                        self.assertEqual({addr-FIXED for _,_,addr,_ in cpu.accesses},offsets)
                        self.assertTrue(all(access=='read' and mul.PACK<=pc<mul.UNPACK and width==4
                                            for access,pc,_,width in cpu.accesses))
                    else:
                        self.assertFalse(cpu.accesses)
                seen.add(len(limbs))
        self.assertEqual(seen,{0,4})

    def test_three_original_conversion_call_sites(self):
        from unicorn import UC_HOOK_CODE
        cpu = OriginalCPU(self,self.rom)
        calls = []
        def record(machine,pc,size,user):
            calls.append(pc)
        for sites in mul.CALLERS.values():
            for site in sites:
                cpu.uc.hook_add(UC_HOOK_CODE,record,begin=site,end=site)
        for value in (1, (1<<32)-1, 1<<32, (1<<47)+7, -(1<<47)-7, (1<<62)-1):
            bits = value & ((1<<64)-1)
            hi,lo = cpu.invoke(0x081428E4,(bits&0xffffffff,bits>>32))
            self.assertEqual(hi<<32|lo, ieee_bits(float(value)))
        for value in (1.0, 3.5, float((1<<32)+7), float((1<<47)+9)):
            bits = ieee_bits(value)
            lo,hi = cpu.invoke(0x0814278C,(bits>>32,bits&0xffffffff))
            self.assertEqual(hi<<32|lo,int(value))
        self.assertEqual(set(calls), {site for sites in mul.CALLERS.values() for site in sites})
