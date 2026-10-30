"""Exact Thumb STMIA stack stores preserve bounds, aliases and return provenance."""
import struct
import unittest
from types import SimpleNamespace
from capstone.arm import ARM_CC_NE, ARM_REG_R8

import test_stack_alias_join_lifetime as fixtures
from test_switch_constants import fixed_args

match = fixtures.match
BASE = fixtures.BASE


class StackAliasStmTests(unittest.TestCase):
    setUp = fixtures.StackAliasJoinLifetimeTests.setUp
    body = fixtures.StackAliasJoinLifetimeTests.body

    def frame(self, middle, words=4):
        return ('push {r4, r5, lr}\nsub sp, #' + str(4 * words) + '\n' + middle +
                '\nadd sp, #' + str(4 * words) + '\npop {r4, r5}\npop {r1}\nbx r1')

    def verify(self, source):
        return match.verify_leaf_instructions(self.body(source), BASE, True)

    def instruction(self, encoded=0xC501):
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        return next(decoder.disasm(struct.pack('<H', encoded), BASE))

    def test_exact_witness_encoding_and_single_word_writeback(self):
        instruction = self.instruction()
        self.assertEqual(bytes(instruction.bytes), bytes.fromhex('01c5'))
        self.assertEqual(match.thumb_stack_alias_stm(instruction,
            {match.ARM_REG_R0 + 5: -16}, 4),
            (match.ARM_REG_R0 + 5, -16, (match.ARM_REG_R0,)))
        self.verify(self.frame('mov r5, sp\nstm r5!, {r0}\nstm r5!, {r1}\n'
                               'ldr r0, [r5]\nmovs r0, #0'))
        self.verify(self.frame('mov r0, sp\nstm r0!, {r1}\nmovs r0, #0'))

    def test_multiword_register_order_and_all_words_bounded(self):
        instruction = self.instruction(0xC507)
        self.assertEqual(match.thumb_stack_alias_stm(instruction,
            {match.ARM_REG_R0 + 5: -16}, 4)[2],
            (match.ARM_REG_R0, match.ARM_REG_R1, match.ARM_REG_R2))
        self.verify(self.frame('mov r5, sp\nstm r5!, {r0, r1, r2}\nstm r5!, {r3}'))
        for offset in (-20, -4, 0, -15):
            with self.subTest(offset=offset), self.assertRaisesRegex(ValueError, 'unaligned|outside'):
                match.thumb_stack_alias_stm(instruction, {match.ARM_REG_R0 + 5: offset}, 4)

    def test_writeback_is_observed_by_next_access(self):
        # The first word is at entry-SP-4; its writeback is the forbidden entry SP.
        with self.assertRaisesRegex(ValueError, 'outside the tracked frame'):
            self.verify(self.frame('add r5, sp, #24\nstm r5!, {r0}\nldr r2, [r5]'))
        # After one local store, this offset changes from entry-SP-4 to entry SP.
        with self.assertRaisesRegex(ValueError, 'outside the tracked frame'):
            self.verify(self.frame('mov r5, sp\nstm r5!, {r0}\nldr r2, [r5, #24]'))

    def test_misaligned_alias_and_stored_pointer_escape_refused(self):
        with self.assertRaisesRegex(ValueError, 'unaligned'):
            self.verify(self.frame('mov r5, sp\nadds r5, #1\nstm r5!, {r0}'))
        with self.assertRaisesRegex(ValueError, 'stored|spilled'):
            self.verify(self.frame('mov r5, sp\nmov r0, sp\nstm r5!, {r0}'))
        # An unknown destination does not authorize spilling a local stack pointer.
        with self.assertRaisesRegex(ValueError, 'escape'):
            self.verify(self.frame('mov r0, sp\nstm r5!, {r0}'))

    def test_saved_return_corruption_is_not_a_verified_return(self):
        with self.assertRaisesRegex(ValueError, 'verified return|indirect control flow'):
            self.verify(self.frame('add r5, sp, #24\nstm r5!, {r0}'))
        self.verify(self.frame('mov r0, lr\nadd r5, sp, #24\nstm r5!, {r0}'))
        with self.assertRaisesRegex(ValueError, 'verified return|indirect control flow'):
            self.verify(self.frame('mov r0, lr\nadd r5, sp, #20\nstm r5!, {r0, r1}'))
        self.verify(self.frame('mov r1, lr\nadd r5, sp, #20\nstm r5!, {r0, r1}'))

    def test_store_effects_preserve_return_and_pointer_word_rules(self):
        stack = [(True, True, False), (False, False, True)]
        slots = {-8: -4}
        match.stack_alias_store(stack, slots, {}, set(), -8, 4, match.ARM_REG_R0)
        self.assertEqual(stack, [(False, True, False), (False, False, True)])
        self.assertEqual(slots, {})
        match.stack_alias_store(stack, slots, {}, {match.ARM_REG_R1}, -4, 4, match.ARM_REG_R1)
        self.assertEqual(stack[1], (True, False, True))
        with self.assertRaisesRegex(ValueError, 'partial access'):
            match.stack_alias_store(stack, {-8: -4}, {}, set(), -8, 2, match.ARM_REG_R0)

    def test_encoding_modes_register_lists_and_decoder_effects_fail_closed(self):
        instruction = self.instruction()
        attributes = {name: getattr(instruction, name) for name in
                      ('mnemonic', 'operands', 'bytes', 'size', 'writeback', 'cc', 'regs_access')}
        aliases = {match.ARM_REG_R0 + 5: -16}
        self.assertIsNone(match.thumb_stack_alias_stm(instruction, {}, 4))
        mutations = ({'bytes': bytes.fromhex('01cd')},  # LDM opcode
                     {'bytes': bytes.fromhex('01c500')},  # mismatched raw width
                     {'bytes': bytes.fromhex('00c5')},  # empty list
                     {'bytes': bytes.fromhex('01c6')},  # different encoded base
                     {'size': 4}, {'writeback': False}, {'cc': ARM_CC_NE},
                     {'mnemonic': 'stmdb'},
                     {'regs_access': lambda: ([match.ARM_REG_R0], [match.ARM_REG_R0 + 5])},
                     {'regs_access': lambda: ([match.ARM_REG_R0, match.ARM_REG_R0 + 5], [])})
        for mutation in mutations:
            with self.subTest(mutation=mutation), self.assertRaisesRegex(ValueError, 'STM encoding'):
                match.thumb_stack_alias_stm(SimpleNamespace(**{**attributes, **mutation}), aliases, 4)
        with self.assertRaisesRegex(ValueError, 'STM encoding'):
            match.thumb_stack_alias_stm(self.instruction(0xC521), aliases, 4)
        for name in ('shift', 'subtracted', 'reg'):
            operands = [SimpleNamespace(type=o.type, reg=o.reg,
                shift=SimpleNamespace(type=o.shift.type, value=o.shift.value),
                subtracted=o.subtracted) for o in attributes['operands']]
            if name == 'shift':
                operands[1].shift.value = 1
            elif name == 'reg':
                operands[1].reg = ARM_REG_R8
            else:
                operands[1].subtracted = True
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, 'STM encoding'):
                match.thumb_stack_alias_stm(SimpleNamespace(**{**attributes, 'operands': operands}), aliases, 4)

    def test_exact_joins_pass_but_live_writeback_difference_and_loop_refuse(self):
        self.verify(self.frame('mov r5, sp\ncmp r2, #0\nbeq other\n'
            'stm r5!, {r0}\nb joined\nother:\nstm r5!, {r1}\njoined:\nldr r0, [r5]'))
        with self.assertRaisesRegex(ValueError, 'inconsistent stack aliases'):
            self.verify(self.frame('mov r5, sp\ncmp r2, #0\nbeq joined\n'
                'stm r5!, {r0}\njoined:\nldr r0, [r5]'))
        with self.assertRaisesRegex(ValueError, 'inconsistent stack aliases'):
            self.verify(self.frame('mov r5, sp\nloop:\nstm r5!, {r0}\nsubs r1, #1\nbne loop'))

    def test_fixed_o2_natural_record_copy_emits_bounded_stm(self):
        (self.root / 'src').mkdir()
        (self.root / 'include').mkdir()
        (self.root / 'src/08000000.c').write_text(
            'struct Record { unsigned first, second, third; };\n'
            'unsigned func_08000000(const struct Record *source)\n{\n'
            '    struct Record local = *source;\n'
            '    return local.first + local.second + local.third;\n}\n')
        runner = match.Runner(match.DEFAULT_CC, root=self.root, timeout=120)
        with runner.workspace() as workspace:
            original, data, image = match.compile_object(runner, workspace, fixed_args(),
                self.root, BASE, 'src/08000000.c')
            self.assertEqual(struct.unpack_from('<H', original, 16)[0], 1)
            symbol, _ = match.function_record(image, 'func_08000000', BASE, True)
            self.assertEqual(symbol['size'], len(data))
            instructions = match.verify_leaf_instructions(data, BASE, True)
            self.assertEqual(sum(i.mnemonic == 'stm' for i in instructions), 1)
            self.assertEqual(runner.read_binary(f'{workspace}/f.o'), original)


if __name__ == '__main__':
    unittest.main(verbosity=2)
