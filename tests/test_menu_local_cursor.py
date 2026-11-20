"""Bounded native cursor visits every word and preserves neighboring frame facts."""

import struct
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
from capstone.arm import ARM_REG_R2, ARM_REG_R4, ARM_REG_R6
import menu_local_cursor as cursor


class CursorTests(unittest.TestCase):
    def loop(self, bound=15, patch=None, bypass=None):
        # Straight-line panel arithmetic is only required to preserve the
        # cursor, count, zero and output address: use independent MOVS here.
        words = [*cursor.SETUP_WORDS, *([0x2000]*6), 0xc404, 0x3301, 0x2b00|bound, 0xddf5]
        if patch:
            pc, value = patch
            words[(pc-cursor.SETUP)//2] = value
        decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
        decoder.detail = True
        instructions = {ins.address:ins for ins in decoder.disasm(
            struct.pack('<'+'H'*len(words), *words), cursor.SETUP)}
        edges = {pc:(pc+2,) for pc in instructions}
        edges[cursor.LATCH] = (cursor.HEAD, cursor.LATCH+2)
        if bypass:
            edges[cursor.SETUP-2] = (bypass,)
        return cursor.MenuCursor(instructions, edges)

    def store(self, proof, n, *, offset=None, adjacent=64, zero=0, saved=None,
              returned=None, pointer=False):
        stack = [(False,False,True)]*18 + [(False,True,False)]*8
        if saved is not None:
            stack[saved] = (False,True,False)
        if returned is not None:
            stack[returned] = (True,False,True)
        bottom = -4*len(stack)
        dest = bottom + (4*n if offset is None else offset)
        proof.check_store(n, {ARM_REG_R4:dest, ARM_REG_R6:bottom+adjacent},
                          stack, {ARM_REG_R2:zero}, {dest:bottom+64} if pointer else {}, set())

    def test_zero_short_and_full_bounds_visit_exactly_the_allocated_words(self):
        for bound in (0, 7, 15):
            with self.subTest(bound=bound):
                proof = self.loop(bound)
                self.assertEqual(proof.state_key(cursor.HEAD-2, cursor.HEAD, 0), (cursor.HEAD,0))
                for i in range(bound+1):
                    self.store(proof, i)
                    self.assertEqual(proof.state_key(cursor.LATCH, cursor.HEAD, i),
                                     (cursor.HEAD,i+1) if i<bound else None)
                    self.assertEqual(proof.state_key(cursor.LATCH, cursor.LATCH+2, i),
                                     None if i<bound else cursor.LATCH+2)
                self.assertEqual(proof.evidence()['offsets'], list(range(0,4*(bound+1),4)))

    def test_crossing_the_output_wrong_stride_or_condition_refuses(self):
        with self.assertRaisesRegex(ValueError, 'SP\\+64'):
            self.loop(16)
        for pc, word in [(cursor.STORE, 0xc406), (cursor.STORE+2, 0x3302),
                         (cursor.LATCH, 0xdcf5), (cursor.SETUP, 0x2301),
                         (cursor.HEAD, 0x2400), (cursor.HEAD, 0x6820)]:
            with self.subTest(pc=pc, word=word), self.assertRaises(ValueError):
                self.loop(patch=(pc,word))

    def test_alternate_predecessor_refuses(self):
        for pc in (cursor.SETUP+2, cursor.HEAD, cursor.STORE, cursor.LATCH):
            with self.subTest(pc=pc), self.assertRaisesRegex(ValueError, 'bypasses'):
                self.loop(bypass=pc)

    def test_saved_word_pointer_word_or_wrong_runtime_alias_refuses(self):
        proof = self.loop()
        for change in (dict(saved=7), dict(saved=16), dict(returned=7), dict(pointer=True),
                       dict(offset=32), dict(adjacent=60), dict(zero=1)):
            with self.subTest(change=change), self.assertRaises(ValueError):
                self.store(proof,7,**change)

    def test_incomplete_visit_refuses(self):
        proof = self.loop()
        for i in range(15):
            self.store(proof,i)
        with self.assertRaisesRegex(ValueError, 'missing'):
            proof.evidence()


if __name__ == '__main__':
    unittest.main()
