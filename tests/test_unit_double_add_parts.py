import argparse
import copy
import json
import os
from pathlib import Path
import random
import struct
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import library_units as units
import match
from match_evidence import data_snapshot, mapping_snapshot, report_matches
import software_float_profile as runtime
import unit_double_add_parts as add

A, B, T = 0x02000100, 0x02000200, 0x02000300
FIXED = add.selected.FIXED_RECORD
ONE = 1 << 60
SIGN, INF, QUIET = 1 << 63, 0x7ff0000000000000, 1 << 51
RECORD = struct.Struct('<IIiQ')


def combine(a, b):
    ac, a_sign, ae, af = a
    bc, b_sign, be, bf = b
    if ac <= 1:
        return A, None
    if bc <= 1:
        return B, None
    if ac == 4:
        return (FIXED if bc == 4 and a_sign != b_sign else A), None
    if bc == 4:
        return B, None
    if ac == bc == 2:
        return T, (ac, a_sign & b_sign, ae, af)
    if ac == 2 or bc == 2:
        return (B if ac == 2 else A), None

    def align(fraction, shift):
        if shift >= 64:
            return 0
        return fraction >> shift | bool(fraction & ((1 << shift)-1))

    exponent = max(ae, be)
    x = align(af, exponent-ae) * (-1 if a_sign else 1)
    y = align(bf, exponent-be) * (-1 if b_sign else 1)
    fraction = abs(x+y)
    if fraction and fraction < ONE:
        shift = 61-fraction.bit_length()
        fraction <<= shift
        exponent -= shift
    if fraction >= 2*ONE:
        fraction = align(fraction, 1)
        exponent += 1
    return T, (3, int(x+y < 0), exponent, fraction)


def ieee_bits(value):
    return int.from_bytes(struct.pack('>d', value), 'big')


def ieee_value(bits):
    return struct.unpack('>d', bits.to_bytes(8, 'big'))[0]


class OriginalCPU:
    def __init__(self, case, rom):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_MEM_READ, UC_HOOK_MEM_WRITE
        from unicorn import arm_const as arm
        self.case, self.arm = case, arm
        self.uc = uc = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        self.stack, self.stop = 0x03007000, 0x03002000
        uc.mem_map(0x08000000, 0x150000)
        uc.mem_write(0x08000000, rom[:0x150000])
        uc.mem_map(0x02000000, 0x1000)
        uc.mem_map(0x03000000, 0x8000)
        self.accesses = []
        self.registers = (arm.UC_ARM_REG_R0, arm.UC_ARM_REG_R1, arm.UC_ARM_REG_R2, arm.UC_ARM_REG_R3)
        def record(machine, access, address, width, value, label):
            self.accesses.append((label, machine.reg_read(arm.UC_ARM_REG_PC), address, width))
        for start, end in ((0x02000000, 0x02000fff), (FIXED-20, FIXED+39)):
            for hook, name in ((UC_HOOK_MEM_READ, 'read'), (UC_HOOK_MEM_WRITE, 'write')):
                uc.hook_add(hook, record, name, begin=start, end=end)

    def invoke(self, address, args, fill=0xa5):
        uc, arm = self.uc, self.arm
        uc.mem_write(self.stack-512, bytes([fill])*544)
        preserved = {r: 0x54321000+r for r in range(arm.UC_ARM_REG_R4, arm.UC_ARM_REG_R11+1)}
        for reg, value in preserved.items():
            uc.reg_write(reg, value)
        for reg, value in zip(self.registers, args):
            uc.reg_write(reg, value)
        self.accesses.clear()
        uc.reg_write(arm.UC_ARM_REG_LR, self.stop|1)
        uc.reg_write(arm.UC_ARM_REG_SP, self.stack)
        uc.emu_start(address|1, self.stop, count=15000)
        self.case.assertEqual(uc.reg_read(arm.UC_ARM_REG_PC), self.stop)
        self.case.assertEqual(uc.reg_read(arm.UC_ARM_REG_SP), self.stack)
        self.case.assertEqual({r: uc.reg_read(r) for r in preserved}, preserved)
        self.case.assertEqual(bytes(uc.mem_read(self.stack, 32)), bytes([fill])*32)
        return tuple(uc.reg_read(r) for r in self.registers[:2])


@unittest.skipUnless(os.getenv('FFTA_DP_ADD_PARTS_ROOT'), 'requires recovered dp-bit sources, USA ROM, old_agbcc')
class AddPartsTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        from rompath import rom_path
        cls.root = Path(os.environ['FFTA_DP_ADD_PARTS_ROOT']).resolve()
        cls.rom = Path(rom_path(cls.root)).read_bytes()
        cls.mapping, cls.index, cls.objects = mapping_snapshot(cls.root), runtime.index_snapshot(cls.root), data_snapshot(cls.root)
        cls.body, cls.report = add.build(cls.root, add.ADDRESS)
        tool = units.resolve(add.TOOLCHAIN)
        runner = match.Runner(tool['cc'], root=cls.root, timeout=120)
        args = argparse.Namespace(cc=tool['cc'], flags=tool['flags'], cpp=match.DEFAULT_CPP,
                                  assembler=match.DEFAULT_AS, linker=match.DEFAULT_LD, objcopy=match.DEFAULT_OBJCOPY)
        with runner.workspace() as workspace:
            _, _, cls.image = match.compile_object(runner, workspace, args, cls.root, add.ADDRESS, 'src/08142E10.c')
            cls.linked = match.link_typed_targets(runner, workspace, args, 'func_08142E10', add.ADDRESS,
                                                 add.TARGETS, {add.DATA})

    def test_original_unit_relocations_and_source(self):
        unit = units.containing(units.load(self.root), add.ADDRESS, add.END)
        self.assertIn(add.SCHEMA, units.schemas(unit, add.ADDRESS))
        for key, value in (('name','unidentified'), ('identity',[]), ('end','0x081439C4'),
                           ('proof','0x08142BE8'), ('toolchain','agbcc-O1-v1')):
            row = dict(unit.row, **{key: value})
            self.assertNotIn(add.SCHEMA, units.schemas(units.Unit(row, units.canonical(row)), add.ADDRESS))
        self.assertNotIn(add.SCHEMA, units.schemas(unit, add.ADDRESS, {}))
        self.assertNotIn(add.SCHEMA, units.schemas(unit, add.ADDRESS+2))
        def bind(image):
            add.source.fixed_bindings(image, add.ADDRESS, add.END, add.TARGETS, add.SITES, add.DATA)
        bind(self.image)
        for change in ('wrong-type', 'wrong-callee', 'missing', 'relocated', 'abs-addend', 'bl-addend', 'weak', 'size', 'image'):
            image = copy.deepcopy(self.image)
            idx, = image['relocations']
            entries = list(struct.iter_unpack('<II', image['section_data'][idx]))
            first_call = next(i for i,(off,_) in enumerate(entries) if off == 0x174)
            absolute = next(info for off,info in entries if off == 0x58)
            off, info = entries[first_call]
            if change == 'wrong-type':
                entries[first_call] = off, info & ~255 | 2
            elif change == 'wrong-callee':
                entries[first_call] = off, absolute & ~255 | 10
            elif change == 'missing':
                entries.pop(first_call)
            elif change == 'relocated':
                entries[first_call] = off+2, info
            elif change in ('abs-addend', 'bl-addend'):
                body = bytearray(image['text'])
                body[0x58 if change == 'abs-addend' else off] ^= 2
                image['text'] = bytes(body)
            elif change in ('size', 'weak'):
                symbol = next(item for item in image['symbols'] if item['name'] == add.DATA)
                symbol['size' if change == 'size' else 'bind'] = 2
            else:
                image['type'] = 2
            image['section_data'][idx] = b''.join(struct.pack('<II', *entry) for entry in entries)
            with self.subTest(change=change), self.assertRaises(ValueError):
                bind(image)
        with tempfile.TemporaryDirectory(dir=self.root/'build') as directory:
            tree = Path(directory)
            relative = Path('src/08142E10.c')
            (tree/'src').mkdir()
            (tree/'include').mkdir()
            (tree/'include/ffta.h').write_bytes((self.root/'include/ffta.h').read_bytes())
            original = (self.root/relative).read_text()
            for old,new in (('intfrac tfraction;', 'fractype tfraction;'), ('diff < 64','diff < 63'),
                            ('fp_number_type *a,','const fp_number_type *a,'), ('-tfraction;', '__negdi2(tfraction);')):
                self.assertIn(old, original)
                (tree/relative).write_text(original.replace(old,new))
                with self.assertRaises(ValueError):
                    add.check_source(tree, relative)

    def test_linked_relocation_roles_and_unrelated_bytes(self):
        relative = Path('src/08142E10.c')
        for change in ('data-type', 'data-size', 'code-size', 'data-value', 'code-thumb', 'other-byte', 'call', 'literal'):
            image = copy.deepcopy(self.linked)
            name = '__negdi2' if change.startswith('code-') else add.DATA
            symbol = next(item for item in image['symbols'] if item['name'] == name)
            if change.endswith('-size'):
                symbol['size'] = 4
            elif change == 'data-type':
                symbol['type'] = 2
            elif change in ('data-value', 'code-thumb'):
                symbol['value'] ^= 1
            else:
                at = {'literal': 0x58, 'call': 0x174, 'other-byte': 0x140}[change]
                text = bytearray(image['text'])
                text[at] ^= 2
                image['text'] = bytes(text)
            with self.subTest(change=change), patch.object(match, 'link_typed_targets', return_value=image), self.assertRaises(ValueError):
                add.link_object(None, None, None, self.image, self.root, relative, self.rom, self.mapping, self.index)

    def test_native_bindings_and_receipt_replay(self):
        self.assertEqual(self.report, (self.root/'docs/match/08142E10.md').read_text())
        self.assertTrue(report_matches(self.report, self.root, add.ADDRESS))
        for source, replacement in ((add.CONTROL, 'unknown'), ('"instructions":302','"instructions":301'),
                                    ('* compiled : `', '* compiled : `ff')):
            self.assertIn(source, self.report)
            self.assertFalse(report_matches(self.report.replace(source, replacement), self.root, add.ADDRESS))
        for address, end, _ in add.CALLERS:
            saved = (self.root/f'docs/match/{address:08X}.md').read_text()
            self.assertIn('* verification: `elf-symbol-thumb-private-double-selected-record-v1`', saved)
            expected = self.rom[address-match.ROM_BASE:end-match.ROM_BASE]
            self.assertIn(expected.hex(), saved)
            self.assertTrue(report_matches(saved, self.root, address))
        objects = json.loads(self.objects)
        objects[add.DATA] = '0x03005E54'
        with self.assertRaises(ValueError):
            add.native_proof(self.body, self.rom, self.mapping, self.index, json.dumps(objects).encode())
        for at in (0x08142E62, 0x08142E68, *add.CALLS, add.NEGATE, 0x081430A4, 0x081430E0, 0x081430D4, 0x08142BE8):
            rom = bytearray(self.rom)
            rom[at-match.ROM_BASE] ^= 2
            rom = bytes(rom)
            with self.subTest(at=hex(at)), patch.object(runtime, 'ROM_SHA256', units.sha(rom)), self.assertRaises(ValueError):
                add.native_proof(rom[add.ADDRESS-match.ROM_BASE:add.END-match.ROM_BASE], rom,
                                 self.mapping, self.index, self.objects)

    def test_component_arithmetic_selected_pointers_and_accesses(self):
        cpu = OriginalCPU(self, self.rom)
        rnd = random.Random(add.ADDRESS)
        classes = [(c,s,27,ONE+13) for c in range(5) for s in (0,1)]
        cases = [(a,b) for a in classes for b in classes]
        cases += [((3,s,0,ONE+1),(3,t,d,ONE+17)) for s in (0,1) for t in (0,1)
                  for d in (-64,-63,-1,0,1,63,64)]
        cases += [((3,rnd.randrange(2),rnd.randint(-80,80),ONE+rnd.randrange(ONE)),
                   (3,rnd.randrange(2),rnd.randint(-80,80),ONE+rnd.randrange(ONE))) for _ in range(80)]
        seen = set()
        for a,b in cases:
            for ptr,record in ((A,a),(B,b)):
                cpu.uc.mem_write(ptr, RECORD.pack(*record))
            empty = b'\xcd'*RECORD.size
            cpu.uc.mem_write(T, empty)
            expected, out = combine(a,b)
            ptr,_ = cpu.invoke(add.ADDRESS,(A,B,T))
            with self.subTest(a=a,b=b):
                self.assertEqual(ptr, expected)
                self.assertEqual(bytes(cpu.uc.mem_read(T,20)), empty if out is None else RECORD.pack(*out))
                for access,pc,address,width in cpu.accesses:
                    self.assertTrue(add.ADDRESS <= pc < add.END)
                    bases = (T,) if access == 'write' else (A,B,T)
                    self.assertTrue(width == 4 and any(address-base in (0,4,8,12,16) for base in bases))
            seen.add(ptr)
        self.assertEqual(seen,{A,B,T,FIXED})

    def test_real_add_and_subtract_against_binary64(self):
        cpu = OriginalCPU(self,self.rom)
        rnd = random.Random(0x143080)
        one = ieee_bits(1.0)
        pairs = [(0,0),(SIGN,SIGN),(0,SIGN),(1,1),((1<<52)-1,1),(one,one),
                 (one,one|SIGN),(one,ieee_bits(2**-53)),(one,ieee_bits(3*2**-53)),
                 (INF-1,INF-1),(INF,one),(INF,SIGN|INF),(INF,INF),
                 (INF+1,INF+QUIET+17),(one,INF+7|SIGN),(INF+QUIET+25,one)]
        pairs += [(rnd.getrandbits(64),rnd.getrandbits(64)) for _ in range(85)]
        for address, _, _ in add.CALLERS:
            subtract = address == add.CALLERS[1][0]
            for fill, fixed, fixed_bits in ((0x44,(1,1,25,19),SIGN|INF|QUIET|19),
                                            (0xa5,(3,0,0,ONE),one)):
                cpu.uc.mem_write(FIXED,RECORD.pack(*fixed))
                for a,b in pairs:
                    signed_b = b ^ (SIGN if subtract else 0)
                    a_mag, b_mag = a & (SIGN-1), signed_b & (SIGN-1)
                    fixed_selected = a_mag == b_mag == INF and (a^signed_b)&SIGN
                    if a_mag > INF:
                        expected = a | QUIET
                    elif b_mag > INF:
                        expected = signed_b | QUIET
                    elif fixed_selected:
                        expected = fixed_bits
                    else:
                        expected = ieee_bits(ieee_value(a)+ieee_value(signed_b))
                    high,low = cpu.invoke(address,(a>>32,a&0xffffffff,b>>32,b&0xffffffff),fill)
                    with self.subTest(address=hex(address),a=hex(a),b=hex(b),fill=fill):
                        self.assertEqual(high<<32|low, expected)
                        if fixed_selected:
                            offsets = {0, 4, 12, 16} if fixed[0] == 1 else {0, 4, 8, 12, 16}
                            self.assertEqual({offset-FIXED for _,_,offset,_ in cpu.accesses}, offsets)
                            self.assertTrue(all(access=='read' and 0x08142BE8<=pc<0x08142D34 and width==4
                                                for access,pc,_,width in cpu.accesses))
                        else:
                            self.assertFalse(cpu.accesses)
