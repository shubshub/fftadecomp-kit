import argparse
import copy
from fractions import Fraction
import math
import os
from pathlib import Path
import random
import struct
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import library_units as units
import match
from match_evidence import mapping_snapshot, report_matches
import unit_double_constructor as make


@unittest.skipUnless(os.getenv('FFTA_MAKE_DP_ROOT'), 'requires the recovered dp-bit source, USA ROM and old_agbcc')
class ConstructorTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        from rompath import rom_path
        from software_float_profile import index_snapshot
        cls.root = Path(os.environ['FFTA_MAKE_DP_ROOT']).resolve()
        cls.rom = Path(rom_path(cls.root)).read_bytes()
        cls.mapping = mapping_snapshot(cls.root)
        cls.index = index_snapshot(cls.root)
        cls.body, cls.report = make.build(cls.root, make.ADDRESS)
        tool = units.resolve(make.TOOLCHAIN)
        runner = match.Runner(tool['cc'], root=cls.root, timeout=120)
        args = argparse.Namespace(cc=tool['cc'], flags=tool['flags'], cpp=match.DEFAULT_CPP,
                                  assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY)
        with runner.workspace() as workspace:
            cls.raw, _, cls.image = match.compile_object(runner, workspace, args, cls.root,
                                                        make.ADDRESS, 'src/08143958.c')

    def test_library_row_original_object_and_alignment(self):
        unit = units.containing(units.load(self.root), make.ADDRESS, make.END)
        self.assertIn(make.SCHEMA, units.schemas(unit, make.ADDRESS))
        for key, value in (('name', 'unidentified'), ('proof', '0x08142BE8'), ('identity', []),
                           ('end', '0x081439C4'), ('toolchain', 'agbcc-O1-v1')):
            row = dict(unit.row, **{key: value})
            self.assertNotIn(make.SCHEMA, units.schemas(units.Unit(row, units.canonical(row)), make.ADDRESS))
        self.assertNotIn(make.SCHEMA, units.schemas(unit, make.ADDRESS, {}))
        self.assertNotIn(make.SCHEMA, units.schemas(unit, make.ADDRESS+2))
        self.assertEqual(self.body, self.rom[0x143958:0x14397e])
        self.assertEqual(make.original_bindings(self.image, self.rom, self.mapping, self.index), [[24, make.NAME]])
        for change in ('site', 'type', 'addend', 'tail', 'symbol', 'image'):
            image = copy.deepcopy(self.image)
            section, = image['relocations']
            offset, info = struct.unpack('<II', image['section_data'][section])
            if change in ('site', 'type'):
                image['section_data'][section] = struct.pack('<II', offset-2 if change == 'site' else offset,
                                                            info if change == 'site' else info & ~255 | 2)
            elif change == 'symbol':
                next(item for item in image['symbols'] if item['name'] == make.NAME)['size'] = 4
            elif change == 'image':
                image['type'] = 2
            else:
                data = bytearray(image['text'])
                data[24 if change == 'addend' else -1] ^= 1
                image['text'] = bytes(data)
            with self.subTest(change=change), self.assertRaises(ValueError):
                make.original_bindings(image, self.rom, self.mapping, self.index)

    def test_caller_source_and_report_controls(self):
        saved = (self.root/'docs/match/08143958.md').read_text()
        self.assertEqual(self.report, saved)
        self.assertTrue(report_matches(saved, self.root, make.ADDRESS))
        for old, new in (('dp-bit constructor evidence', 'constructor'), ('fraction low in R3', 'fraction high in R3'),
                         (make.UNIT_DIGEST, '0'*64), ('* compiled : `', '* compiled : `00')):
            self.assertIn(old, saved)
            self.assertFalse(report_matches(saved.replace(old, new), self.root, make.ADDRESS))
        for at in (0x14395e, 0x143962, 0x143970, 0x143978, 0x14397a, 0x142c5a, 0x144378, 0x144350):
            rom = bytearray(self.rom)
            rom[at] ^= 2
            with self.subTest(at=at), self.assertRaises(ValueError):
                make.native_proof(bytes(rom[0x143958:0x14397e]), bytes(rom), self.mapping, self.index, None)
        with tempfile.TemporaryDirectory(dir=self.root/'build') as directory:
            tree = Path(directory)
            relative = Path('src/08143958.c')
            (tree/'src').mkdir()
            (tree/'include').mkdir()
            (tree/'include/ffta.h').write_bytes((self.root/'include/ffta.h').read_bytes())
            src = (self.root/relative).read_text()
            for original, replacement in (('double func_08143958', 'fractype func_08143958'),
                                          ('number.sign = sign;', 'number.sign = exponent;'),
                                          ('fractype fraction)', 'u32 fraction)')):
                self.assertIn(original, src)
                (tree/relative).write_text(src.replace(original, replacement))
                with self.subTest(change=replacement), self.assertRaises(ValueError):
                    make.check_source(tree, relative)

    def cpu(self, fill):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_CODE
        from unicorn.arm_const import (UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3,
                                       UC_ARM_REG_R4, UC_ARM_REG_R11, UC_ARM_REG_SP, UC_ARM_REG_LR, UC_ARM_REG_PC)

        uc = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        uc.mem_map(0x08000000, 0x150000)
        uc.mem_write(0x08000000, self.rom[:0x150000])
        uc.mem_map(0x03000000, 0x8000)
        stack, stop = 0x03007000, 0x03002000
        registers = (UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3)
        incoming = []

        def words(ptr, n):
            return struct.unpack('<'+'I'*n, uc.mem_read(ptr, 4*n))

        def observe(machine, pc, size, data):
            sp = machine.reg_read(UC_ARM_REG_SP)
            if pc == make.ADDRESS:
                incoming[:] = [sp, *(machine.reg_read(reg) for reg in registers), *words(sp, 1)]
            else:
                self.assertEqual(machine.reg_read(registers[0]), incoming[0]-32)
                self.assertEqual(words(machine.reg_read(registers[0]), 5), tuple(incoming[1:]))

        for pc in (make.PACK, make.ADDRESS):
            uc.hook_add(UC_HOOK_CODE, observe, begin=pc, end=pc)

        def invoke(address, args):
            uc.mem_write(stack-512, bytes([fill])*544)
            for reg, arg in zip(registers, args):
                uc.reg_write(reg, arg & 0xFFFFFFFF)
            if len(args) == 5:
                uc.mem_write(stack, struct.pack('<I', args[4]))
            above = bytes(uc.mem_read(stack, 32))
            preserved = {reg: 0xC0000000+reg for reg in range(UC_ARM_REG_R4, UC_ARM_REG_R11+1)}
            for reg, value in preserved.items():
                uc.reg_write(reg, value)
            uc.reg_write(UC_ARM_REG_LR, stop | 1)
            uc.reg_write(UC_ARM_REG_SP, stack)
            incoming.clear()
            uc.emu_start(address | 1, stop, count=6000)
            self.assertEqual(uc.reg_read(UC_ARM_REG_PC), stop)
            self.assertEqual(uc.reg_read(UC_ARM_REG_SP), stack)
            self.assertEqual(bytes(uc.mem_read(stack, 32)), above)
            self.assertEqual({reg: uc.reg_read(reg) for reg in preserved}, preserved)
            self.assertEqual(len(incoming), 6)
            return uc.reg_read(registers[0]) << 32 | uc.reg_read(registers[1])

        return invoke

    def test_constructor_vectors_and_split_word_abi(self):
        call = self.cpu(0xA5)
        one = 1 << 60
        infinity = 0x7FF0000000000000
        mask = (1 << 52)-1
        for sign in (0, 1):
            for classification, exponent, fraction in (
                (0, 2000, 0x123456789ABCDEF0), (1, -1600, 1), (2, 71, one), (4, -97, one+7),
                (3, 3, 0), (3, -1074, one), (3, -1079, one-1), (3, -1023, one+0x3FF),
                (3, -1022, one), (3, 0, one+127), (3, 0, one+128), (3, 0, one+129),
                (3, 0, one+256+128), (3, 11, 2*one-1), (3, 1023, 2*one-1), (3, 1024, one),
            ):
                if classification in (0, 1):
                    expected = infinity | (1 << 51) | (fraction & mask)
                elif classification == 4:
                    expected = infinity
                elif classification == 2 or fraction == 0:
                    expected = 0
                elif exponent < -1022:
                    # The historical packer chops subnormal guard bits.
                    expected = fraction >> (-1022-exponent+8)
                else:
                    exact = Fraction(fraction, one) * Fraction(2) ** exponent
                    try:
                        rounded = float(exact)
                    except OverflowError:
                        rounded = math.inf
                    expected = int.from_bytes(struct.pack('>d', rounded), 'big')
                args = (classification, sign, exponent, fraction & 0xFFFFFFFF, fraction >> 32)
                with self.subTest(args=args):
                    self.assertEqual(call(make.ADDRESS, args), sign << 63 | expected)

    def test_genuine_single_to_double_caller_with_two_initial_stack_patterns(self):
        rnd = random.Random(0x143958)
        inputs = [0, 1, 0x007FFFFF, 0x00800000, 0x3F800000, 0x7F7FFFFF, 0x7F800000,
                  0x7F800001, 0x7F900000, 0x7FC01234, 0x7FFFFFFF]
        inputs += [bits ^ 0x80000000 for bits in inputs]
        inputs += [rnd.getrandbits(32) for _ in range(160)]
        for fill in (0, 0xA5):
            call = self.cpu(fill)
            for bits in inputs:
                fraction = bits & 0x7FFFFF
                if bits >> 23 & 255 == 255 and fraction:
                    expected = (bits >> 31 << 63) | 0x7FF8000000000000 | ((fraction << 30) & ((1 << 52)-1))
                else:
                    value, = struct.unpack('>f', bits.to_bytes(4, 'big'))
                    expected = int.from_bytes(struct.pack('>d', value), 'big')
                with self.subTest(bits=hex(bits), fill=fill):
                    self.assertEqual(call(make.CALLER, (bits,)), expected)
