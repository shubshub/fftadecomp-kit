"""Exact inventory SP comparison without changing ordinary verifier policy."""
from pathlib import Path
import struct
import sys
from types import SimpleNamespace
import unittest
from capstone.arm import ARM_CC_NE, ARM_INS_MOV

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import stack_pointer_compare_profile as profile

BASE = 0x08000000


def body(*halfwords):
    return struct.pack('<' + 'H' * len(halfwords), *halfwords)


class StackPointerCompareTests(unittest.TestCase):
    def verify(self, data, calls=None, **options):
        return match.verify_leaf_instructions(data, BASE, True, calls,
            stack_pointer_compare_profile=profile.SELECTOR, **options)

    def instruction(self):
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        return next(decoder.disasm(body(0x4585), BASE))

    def test_exact_instruction_effects_and_balanced_leaf(self):
        instruction = self.instruction()
        self.assertIsNone(profile.verify_instruction(instruction))
        self.assertEqual(instruction.regs_access(),
                         ([match.ARM_REG_SP, match.ARM_REG_R0], [match.ARM_REG_CPSR]))
        self.assertEqual(len(self.verify(body(0x4585, 0x4770))), 2)
        self.assertEqual(len(self.verify(body(0xB500, 0xB081, 0x4585, 0xB001, 0xBC02, 0x4708))), 6)

    def test_default_and_previous_acyclic_policy_unchanged(self):
        data = body(0x4585, 0x4770)
        for options in ({}, {'acyclic_state_budget': 4096}):
            with self.subTest(options=options), self.assertRaisesRegex(ValueError, 'stack-address materialization'):
                match.verify_leaf_instructions(data, BASE, True, **options)
        self.assertEqual(len(match.verify_leaf_instructions(body(0x4770), BASE, True)), 1)

    def test_both_comparison_successors_are_verified(self):
        data = body(0xB500, 0xB081, 0x4585, 0xD801, 0x2000,
                    0xE000, 0x2001, 0xB001, 0xBC02, 0x4708)
        self.assertEqual(len(self.verify(data)), 10)
        # One branch returns while the frame is still allocated.
        with self.assertRaisesRegex(ValueError, 'does not balance'):
            self.verify(body(0xB500, 0xB081, 0x4585, 0xD803,
                             0xB001, 0xBC02, 0x4708, 0x46C0, 0x4770))

    def test_encoding_conditions_flags_and_effects_fail_closed(self):
        instruction = self.instruction()
        names = ('id', 'mnemonic', 'size', 'bytes', 'cc', 'update_flags',
                 'writeback', 'operands', 'regs_access')
        values = {name: getattr(instruction, name) for name in names}
        mutations = ({'bytes': body(0x4505)}, {'bytes': body(0x458D)},
                     {'bytes': body(0x4585, 0)}, {'size': 4},
                     {'id': ARM_INS_MOV}, {'mnemonic': 'cmn'},
                     {'cc': ARM_CC_NE}, {'cc': match.ARM_CC_INVALID},
                     {'update_flags': False}, {'writeback': True},
                     {'regs_access': lambda: ([match.ARM_REG_R0], [match.ARM_REG_CPSR])},
                     {'regs_access': lambda: ([match.ARM_REG_SP, match.ARM_REG_R0], [])},
                     {'regs_access': lambda: ([match.ARM_REG_SP, match.ARM_REG_R0], [match.ARM_REG_SP])},
                     {'regs_access': lambda: ([match.ARM_REG_SP, match.ARM_REG_R0, match.ARM_REG_LR], [match.ARM_REG_CPSR])})
        for change in mutations:
            with self.subTest(change=change), self.assertRaisesRegex(ValueError, 'exact unconditional read-only'):
                profile.verify_instruction(SimpleNamespace(**{**values, **change}))
        for change in ('register', 'reverse', 'shift', 'subtracted', 'operand_type'):
            operands = [SimpleNamespace(type=o.type, reg=o.reg, subtracted=o.subtracted,
                shift=SimpleNamespace(type=o.shift.type, value=o.shift.value)) for o in instruction.operands]
            if change == 'register':
                operands[1].reg = match.ARM_REG_R1
            elif change == 'reverse':
                operands.reverse()
            elif change == 'shift':
                operands[1].shift.value = 1
            elif change == 'subtracted':
                operands[1].subtracted = True
            else:
                operands[1].type = match.ARM_OP_IMM
            with self.subTest(change=change), self.assertRaisesRegex(ValueError, 'exact unconditional read-only'):
                profile.verify_instruction(SimpleNamespace(**{**values, 'operands': operands}))

    def test_sp_writes_and_other_sp_register_operations_refused(self):
        for encoding in (0x4685, 0x4485, 0x458D, 0x45E8):
            with self.subTest(encoding=encoding), self.assertRaises(ValueError):
                self.verify(body(encoding, 0x4770))

    def test_stack_alias_comparison_and_escape_stay_refused(self):
        # The current SP copied into r0 is an alias, not an ordinary scalar.
        with self.assertRaisesRegex(ValueError, 'alias use or escape'):
            self.verify(body(0xB081, 0x4668, 0x4585, 0xB001, 0x4770))
        # Comparing SP first grants no later store or spill of a stack alias.
        for escaped in (body(0x4668, 0x6008), body(0x4668, 0xB401)):
            with self.subTest(escaped=escaped), self.assertRaisesRegex(ValueError, 'escape|spilled'):
                self.verify(body(0xB081, 0x4585) + escaped + body(0xB001, 0x4770))

    def test_bad_return_frames_and_saved_return_corruption_refused(self):
        for data in (body(0xB081, 0x4585, 0x4770),
                     body(0xB500, 0x4585, 0xBC02, 0x4700),
                     body(0xB500, 0x9000, 0x4585, 0xBC02, 0x4708)):
            with self.subTest(data=data), self.assertRaises(ValueError):
                self.verify(data)

    def test_literal_ownership_and_direct_stack_bounds_retained(self):
        data = body(0x4801, 0x4585, 0x4770, 0, 0, 0x0200)
        self.assertEqual(len(self.verify(data)), 3)
        with self.assertRaisesRegex(ValueError, 'literal read.*inside the function'):
            self.verify(body(0x4802) + data[2:])
        with self.assertRaisesRegex(ValueError, 'outside the tracked frame'):
            self.verify(body(0x4585, 0x9000, 0x4770))

    def call_body(self, target):
        site = BASE + 4
        delta = target - (site + 4)
        data = body(0xB500, 0x4585, 0xF000 | ((delta >> 12) & 0x7FF),
                    0xF800 | ((delta >> 1) & 0x7FF), 0xBC02, 0x4708)
        return data, {site: target}

    def test_ordinary_call_remains_conditional_abi_and_exact_binding_required(self):
        data, calls = self.call_body(BASE + 0x100)
        self.assertEqual(len(self.verify(data, calls)), 5)
        with self.assertRaisesRegex(ValueError, 'calls and interrupts require'):
            self.verify(data)
        with self.assertRaisesRegex(ValueError, 'validated external direct'):
            self.verify(data, {BASE + 4: BASE + 0x102})

    def test_runtime_thunk_and_arithmetic_exclusions_retained(self):
        for target in (0x08142250, 0x08142252, 0x081426B8, 0x08142AB0, 0x08142B28,
                       0x08142950, 0x0814220C, 0x08143CEC, 0x08143080):
            data, calls = self.call_body(target)
            with self.subTest(target=target), self.assertRaisesRegex(ValueError, 'excludes runtime and thunk'):
                self.verify(data, calls)

    def test_version_mode_and_context_isolation(self):
        for selector in ('thumb-sp-r0-compare-inventory-v0', '', True, 1):
            with self.subTest(selector=selector), self.assertRaisesRegex(ValueError, 'isolated inventory-only'):
                match.verify_leaf_instructions(body(0x4770), BASE, True,
                                                stack_pointer_compare_profile=selector)
        with self.assertRaisesRegex(ValueError, 'isolated inventory-only'):
            match.verify_leaf_instructions(body(0x4770), BASE, False,
                                            stack_pointer_compare_profile=profile.SELECTOR)
        contexts = ('buffer_proof', 'call_resolver', 'switch_relocations', 'switch_data_relocations',
                    'udivsi3_context', 'preloaded_switch', 'modsi3_context', 'divsi3_context',
                    'inert_spin_context', 'double_context', 'function_thunk_context',
                    'allow_switch_constants', 'allow_switch_scalar_frame', 'umodsi3_context',
                    'ashldi3_context', 'float_context', 'acyclic_state_budget',
                    'ignored_leaf_alias_proof', 'signed_quotient_profile')
        for name in contexts:
            with self.subTest(context=name), self.assertRaisesRegex(ValueError, 'isolated inventory-only'):
                self.verify(body(0x4770), **{name: True})


if __name__ == '__main__':
    unittest.main(verbosity=2)
