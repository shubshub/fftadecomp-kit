"""Thumb walks admit only 16-bit ARMv4T encodings and bound BL pairs (kit #180)."""
import json
from pathlib import Path
import struct
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT / 'tools'))
from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
import armv4t
import match
import owner_admission_profile as owner
import owner_graph_profile as graph

BASE = 0x08000000
OWNER = match.ROM_BASE + 0x100
BX_LR = 0x4770
ENCODING = 'reachable Thumb instruction is not an ARMv4T encoding or a BL pair'
NON_LEAF = 'non-leaf calls and interrupts require linked CFG verification'
OWNER_GRAPH = 'owner graph instruction is not an ARMv4T encoding or a BL pair'


def halves(*values):
    return b''.join(struct.pack('<H', value) for value in values)


def body(*values):
    return halves(*values, BX_LR)


def decoder():
    engine = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    engine.detail = True
    return engine


class LeafEncodings(unittest.TestCase):
    def verify(self, data, calls=None):
        return match.verify_leaf_instructions(data, BASE, True, calls)

    def refused(self, data, message):
        with self.assertRaises(ValueError) as caught:
            self.verify(data)
        self.assertEqual(str(caught.exception), message)

    def test_ordinary_forms_are_admitted(self):
        self.verify(body(
            0x2001,  # movs r0, #1
            0x1840,  # adds r0, r0, r1
            0x4648,  # mov r0, r9 (hi register)
            0x46C0,  # nop (mov r8, r8)
            0x6808,  # ldr r0, [r1]
            0x2900,  # cmp r1, #0
            0xD000,  # beq +0
            0x4388,  # bics r0, r1
        ))

    def test_each_non_v4t_class_is_refused(self):
        cases = {
            'bkpt': 0xBE00, 'udf': 0xDE00, 'cpsie': 0xB662, 'setend': 0xB650, 'rev': 0xBA08,
            'sxtb': 0xB248, 'uxtb': 0xB2C8, 'cbz': 0xB100, 'it': 0xBF08, 'yield': 0xBF10,
            'sev': 0xBF40, 'wfi': 0xBF30, 'bx sbz': 0x4701, 'bx lr sbz': 0x4771,
            'mov lo,lo': 0x4608, 'add lo,lo': 0x4408, 'cmp lo,lo': 0x4508,
        }
        for name, half in cases.items():
            with self.subTest(name):
                self.refused(body(half), ENCODING)

    def test_interrupts_and_blx_keep_their_refusal(self):
        for name, data in (('svc', body(0xDF00)), ('blx r0', body(0x4780)),
                           ('blx pair', body(0xF000, 0xE800))):
            with self.subTest(name):
                self.refused(data, NON_LEAF)

    def test_thumb2_pair_is_refused(self):
        for pair in ((0xF04F, 0x0002), (0xF000, 0xB800), (0xF000, 0xF000)):
            with self.subTest(pair):
                self.refused(body(*pair), ENCODING)

    def test_stm_with_the_base_in_the_list(self):
        self.refused(body(0xC103), ENCODING)  # stmia r1!, {r0, r1}: base listed, not lowest
        self.verify(body(0xC003))             # stmia r0!, {r0, r1}: base is the lowest register
        self.verify(body(0xC102))             # stmia r1!, {r1}

    def test_only_46c0_is_a_nop(self):
        self.refused(body(0xBF00), ENCODING)  # the ARMv6T2 hint nop
        self.verify(body(0x46C0))             # mov r8, r8

    def test_bound_bl_pair_is_still_admitted(self):
        target = 0x08001000
        offset = (target - (BASE + 2 + 4)) >> 1
        pair = struct.pack('<HH', 0xF000 | (offset >> 11 & 0x7FF), 0xF800 | (offset & 0x7FF))
        data = struct.pack('<H', 0xB500) + pair + struct.pack('<H', 0xBD00)
        self.verify(data, {BASE + 2: target})

    def test_unreached_it_does_not_change_the_walk(self):
        # b over a data halfword that reads as "it al"; each reached address is decoded alone.
        reached = self.verify(body(0xE000, 0xBFE8, 0x1840))
        self.assertEqual([item.mnemonic for item in reached], ['b', 'adds', 'bx'])


class CheckerHelpers(unittest.TestCase):
    def one(self, raw):
        return next(decoder().disasm(raw, BASE))

    def test_checker_helpers(self):
        self.assertTrue(armv4t.instruction(self.one(halves(0x2001))))
        self.assertFalse(armv4t.instruction(self.one(halves(0xBE00))))
        self.assertFalse(armv4t.instruction(self.one(halves(0xF04F, 0x0002))))
        self.assertFalse(armv4t.encoding(self.one(halves(0xF04F, 0x0002))))

    def test_it_context_decode_is_decided_by_the_bits(self):
        # Within one decode Capstone carries Thumb-2 IT state past an "it" halfword, which
        # the ARM7TDMI does not have. Such an item is refused unless it decodes exactly as
        # it does alone.
        def in_context(first, half):
            items = list(decoder().disasm(halves(first, half, BX_LR), BASE - 2))
            return items[1] if len(items) > 1 and items[1].address == BASE else None

        def shape(item):
            return item.mnemonic, item.op_str, item.cc, item.update_flags

        for name, first, half in (('it al drops the s of adds', 0xBFE8, 0x1840),
                                  ('it al drops the s of subs', 0xBFE8, 0x1E40),
                                  ('it al drops the s of movs', 0xBFE8, 0x2001),
                                  ('it eq renames b', 0xBF08, 0xE000),
                                  ('it eq makes adds conditional', 0xBF08, 0x1840),
                                  ('it eq makes a hi-register mov conditional', 0xBF08, 0x4648),
                                  ('it eq makes bx conditional', 0xBF08, 0x4770)):
            with self.subTest(name):
                alone = self.one(halves(half))
                self.assertTrue(armv4t.encoding(alone))
                item = in_context(first, half)
                self.assertNotEqual(shape(item), shape(alone))
                self.assertFalse(armv4t.encoding(item))
        for first in (0xBF08, 0xBFE8, 0xBF0C, 0xBF14):
            for half in range(0, 0xE800, 37):
                item = in_context(first, half)
                if item is not None and item.size == 2 and armv4t.encoding(item):
                    self.assertEqual(shape(item), shape(self.one(halves(half))), (hex(first), hex(half)))

    def test_conditional_branch_condition_comes_from_the_field(self):
        for field in range(14):
            self.assertTrue(armv4t.encoding(self.one(halves(0xD000 | field << 8))), field)
        self.assertFalse(armv4t.encoding(self.one(halves(0xDE00))))  # undefined
        self.assertFalse(armv4t.encoding(self.one(halves(0xDF00))))  # swi: refused by its walk


class DeadAliasEncodings(unittest.TestCase):
    def dead(self, *values):
        return match.stack_alias_overwritten_before_use(
            body(*values), BASE, BASE, match.ARM_REG_R0 + 4, decoder())

    def test_non_v4t_instruction_before_the_overwrite_is_not_a_kill_proof(self):
        kill = 0x2400  # movs r4, #0
        self.assertTrue(self.dead(0x1C1A, kill))  # adds r2, r3, #0
        self.assertTrue(self.dead(0x46C0, kill))
        for name, values in (('mov lo,lo', (0x461A,)), ('rev', (0xBA1A,)), ('nop hint', (0xBF00,)),
                             ('bkpt', (0xBE00,)), ('thumb-2 pair', (0xF04F, 0x0002))):
            with self.subTest(name):
                self.assertFalse(self.dead(*values, kill))


class OwnerGraphEncodings(unittest.TestCase):
    def graph(self, *values):
        data = halves(*values)
        mapping = json.dumps([dict(rom=f'0x{OWNER:08X}', end=f'0x{OWNER + len(data):08X}',
                                   mode='thumb', instrs=len(values))]).encode()
        return graph.graph(data, OWNER, owner.refine(data, OWNER, mapping))

    def test_v4t_forms_are_admitted(self):
        for values in ((0x1C20, BX_LR),   # adds r0, r4, #0
                       (0x4648, BX_LR),   # mov r0, r9
                       (0x46C0, BX_LR),   # nop
                       (0xC003, BX_LR),   # stmia r0!, {r0, r1}
                       (0xC102, BX_LR)):  # stmia r1!, {r1}
            with self.subTest(values):
                self.assertEqual(len(self.graph(*values)[0]), 2)

    def test_non_v4t_forms_are_refused(self):
        for name, values in (('mov lo,lo', (0x4620, BX_LR)), ('add lo,lo', (0x4420, BX_LR)),
                             ('cmp lo,lo', (0x4520, BX_LR)), ('bx lr sbz', (0x1C20, 0x4771)),
                             ('stm base in list', (0xC103, BX_LR))):
            with self.subTest(name), self.assertRaises(ValueError) as caught:
                self.graph(*values)
            self.assertEqual(str(caught.exception), OWNER_GRAPH, name)


class UnpredictableOperands(unittest.TestCase):
    """Operand combinations ARMv4T leaves UNPREDICTABLE, and their defined neighbours."""

    def encoding(self, half):
        return armv4t.encoding(next(decoder().disasm(halves(half), BASE)))

    def refused(self, half):
        self.assertFalse(self.encoding(half))
        with self.assertRaises(ValueError) as caught:
            match.verify_leaf_instructions(body(half), BASE, True)
        self.assertEqual(str(caught.exception), ENCODING)

    def test_muls_with_one_register_twice(self):
        # ARM DDI 0100I A7.1.45: Rd == Rm is UNPREDICTABLE before ARMv6.
        for register in range(8):
            with self.subTest(register):
                self.refused(0x4340 | register << 3 | register)
                with self.assertRaises(ValueError) as caught:
                    OwnerGraphEncodings.graph(self, 0x4340 | register << 3 | register, BX_LR)
                self.assertEqual(str(caught.exception), OWNER_GRAPH)
        for rd in range(8):
            for rm in range(8):
                if rd != rm:
                    self.assertTrue(self.encoding(0x4340 | rm << 3 | rd), (rd, rm))
        match.verify_leaf_instructions(body(0x4348), BASE, True)  # muls r0, r1, r0
        match.verify_leaf_instructions(body(0x4341), BASE, True)  # muls r1, r0, r1
        self.assertEqual(len(OwnerGraphEncodings.graph(self, 0x4348, BX_LR)[0]), 2)

    def test_cmp_with_pc_as_the_first_operand(self):
        # ARM DDI 0100I A7.1.23: Rn can be any of R0 to R14 and Rm any of R0 to R15; H1 == 1 with
        # Rn == 0b111 is UNPREDICTABLE, and so is the form of two low registers.
        for rm in range(16):
            with self.subTest(rm):
                self.refused(0x4587 | rm << 3)  # cmp pc, rM, up to cmp pc, pc
        for rn in range(15):
            for rm in range(16):
                half = 0x4500 | (rn & 8) << 4 | rm << 3 | rn & 7
                self.assertEqual(self.encoding(half), rn >= 8 or rm >= 8, (rn, rm))
        for name, half in (('cmp r0, pc', 0x4578), ('cmp r7, pc', 0x457F), ('cmp r7, r8', 0x4547),
                           ('cmp r8, r0', 0x4580), ('cmp lr, r7', 0x45BE), ('cmp lr, pc', 0x45FE)):
            with self.subTest(name):
                self.assertTrue(self.encoding(half))
        match.verify_leaf_instructions(body(0x4580), BASE, True)  # cmp r8, r0
        match.verify_leaf_instructions(body(0x45BE), BASE, True)  # cmp lr, r7
        self.assertEqual(len(OwnerGraphEncodings.graph(self, 0x4580, BX_LR)[0]), 2)


if __name__ == '__main__':
    unittest.main()
