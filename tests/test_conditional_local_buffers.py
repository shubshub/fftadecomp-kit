"""The opt-in contracts preserve frame bounds and expose their assumptions."""
from pathlib import Path
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import conditional_local_buffer_profile as local
import named_data_buffer_profile as named
import owner_admission_profile as owner

R0 = match.ARM_REG_R0
LOCAL = (False, False, True)
SAVED = (False, True, False)


def proof(policy, calls):
    result = object.__new__(local.ConditionalLocalBufferProof)
    result.policy, result.calls, result.observations = policy, calls, {}
    result.runtime_dependencies = []
    result.environment = {}
    return result


class ConditionalLocalBufferTests(unittest.TestCase):
    def test_scheduler_accepts_complete_descriptor_and_preserved_alias(self):
        p = proof(local.SCHEDULER, {100: 0x08005B6C})
        stack = [LOCAL]*7 + [SAVED]*4
        self.assertEqual(p.check_call(0x08005B6C, {R0+2: -44, R0+4: -44}, stack, site=100), {})
        manifest = p.contract_manifest()
        self.assertFalse(manifest['actual_callback_effects_proved'])
        self.assertFalse(manifest['nonescape_proved'])
        self.assertIn('ambient original R9', ' '.join(manifest['assumptions']))

    def test_scheduler_rejects_short_descriptor_and_saved_words(self):
        for offset in (-48, -40, -16, -4, 0):
            with self.subTest(offset=offset), self.assertRaises(ValueError):
                proof(local.SCHEDULER, {100: 0x08005B6C}).check_call(
                    0x08005B6C, {R0+2: offset}, [LOCAL]*7+[SAVED]*4, site=100)

    def test_scheduler_rejects_extra_argument_and_pointer_words(self):
        for aliases, slots in (({R0+2: -44, R0: -44}, None),
                               ({R0+2: -44}, {-40: -44})):
            with self.subTest(aliases=aliases, slots=slots), self.assertRaises(ValueError):
                proof(local.SCHEDULER, {100: 0x08005B6C}).check_call(
                    0x08005B6C, aliases, [LOCAL]*7+[SAVED]*4, slots, site=100)

    def test_state_clear_requires_constant_four_and_complete_local_word(self):
        p = proof(local.STATE, {100: 0x0814224C})
        self.assertEqual(p.check_call(0x0814224C, {R0: -20}, [LOCAL]*3+[SAVED]*2,
                                     constants={R0+1: 4}, site=100), {})
        self.assertIn('not a proof', ' '.join(p.contract_manifest()['assumptions']))
        for constants in ({}, {R0+1: 8}):
            with self.subTest(constants=constants), self.assertRaises(ValueError):
                p.check_call(0x0814224C, {R0: -20}, [LOCAL]*3+[SAVED]*2,
                             constants=constants, site=100)

    def test_visitor_requires_exact_pointer_word(self):
        p = proof(local.STATE, {100: 0x080C7CC0})
        self.assertEqual(p.check_call(0x080C7CC0, {R0+2: -16}, [LOCAL]*3+[SAVED]*2,
                                     {-16: -20}, site=100), {})
        for slots in ({}, {-16: -12}, {-12: -20}):
            with self.subTest(slots=slots), self.assertRaises(ValueError):
                p.check_call(0x080C7CC0, {R0+2: -16}, [LOCAL]*3+[SAVED]*2, slots, site=100)

    def test_unauthenticated_site_and_unobserved_call_refused(self):
        p = proof(local.SCHEDULER, {100: 0x08005B6C})
        with self.assertRaises(ValueError):
            p.check_call(0x08005B6C, {R0+2: -44}, [LOCAL]*7+[SAVED]*4, site=102)
        with self.assertRaises(ValueError):
            p.contract_manifest()

    def test_indirect_target_cannot_be_local_or_saved_return(self):
        p = proof(local.STATE, {100: 0x0814224C})
        p.check_indirect_target(0x0814224C, {R0: -20}, {match.ARM_REG_LR}, site=100)
        for aliases, returns in (({R0+2: -20}, ()), ({}, (R0+2,))):
            with self.subTest(aliases=aliases, returns=returns), self.assertRaises(ValueError):
                p.check_indirect_target(0x0814224C, aliases, returns, site=100)

    def test_profile_report_selection_is_explicit(self):
        for policy, schema in local.SCHEMAS.items():
            self.assertIn(policy, named.SELECTORS)
            self.assertEqual(owner.selector_for_report(f'* verification: `{schema}`'), policy)
        self.assertFalse(named.conditional_thunk_replay(None))


if __name__ == '__main__':
    unittest.main()
