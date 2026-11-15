"""Base leaf verification admits only 16-bit ARMv4T Thumb encodings and bound BL pairs (kit #180)."""
import os
from pathlib import Path
import struct
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT / 'tools'))
import armv4t
import match

BASE = 0x08000000
BX_LR = 0x4770


def body(*halves):
    return b''.join(struct.pack('<H', half) for half in halves) + struct.pack('<H', BX_LR)


class LeafEncodings(unittest.TestCase):
    def verify(self, data, calls=None):
        return match.verify_leaf_instructions(data, BASE, True, calls)

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
            'sev': 0xBF40, 'wfi': 0xBF30, 'blx r0': 0x4780, 'bx sbz': 0x4701,
            'mov lo,lo': 0x4608 & ~0xC0 | 0, 'add lo,lo': 0x4400 | 0x08, 'cmp lo,lo': 0x4500 | 0x08,
            'svc': 0xDF00,
        }
        for name, half in cases.items():
            with self.subTest(name), self.assertRaises(ValueError) as caught:
                self.verify(body(half))
            self.assertNotIn('no verified return', str(caught.exception))

    def test_thumb2_pair_is_refused(self):
        for halves in ((0xF04F, 0x0002), (0xF000, 0xB800), (0xF000, 0xE800), (0xF000, 0xF000)):
            with self.subTest(halves), self.assertRaises(ValueError):
                self.verify(struct.pack('<HH', *halves) + struct.pack('<H', BX_LR))

    def test_bound_bl_pair_is_still_admitted(self):
        target = 0x08001000
        offset = (target - (BASE + 2 + 4)) >> 1
        pair = struct.pack('<HH', 0xF000 | (offset >> 11 & 0x7FF), 0xF800 | (offset & 0x7FF))
        data = struct.pack('<H', 0xB500) + pair + struct.pack('<H', 0xBD00)
        self.verify(data, {BASE + 2: target})

    def test_checker_helpers(self):
        from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
        decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
        decoder.detail = True
        one = lambda raw: next(decoder.disasm(raw, BASE))
        self.assertTrue(armv4t.instruction(one(struct.pack('<H', 0x2001))))
        self.assertFalse(armv4t.instruction(one(struct.pack('<H', 0xBE00))))
        self.assertFalse(armv4t.instruction(one(struct.pack('<HH', 0xF04F, 0x0002))))


if __name__ == '__main__':
    unittest.main()
