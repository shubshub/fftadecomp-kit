"""Offset manager provenance against an independent raw Thumb load oracle."""
from pathlib import Path
import struct
import subprocess
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import owner_admission_profile as owner
import scheduler_entry_profile as entry
import scheduler_manager_field_profile as previous
import scheduler_manager_offset_profile as profile
from test_scheduler_entry import bound
from test_scheduler_manager_field import raw_until_call, POINT
from test_scheduler_predicates import A, half, bl


def caller(*, offset=32, literal_reg=1, pointer_reg=2, first=None, last=None,
           before_pointer=(), before_final=(), before_call=(), join=False,
           parent=0x9200, descriptor=1, frame=8):
    data = half(0xB500, 0xB080 + frame, 0xAB00 + descriptor, 0x4800)
    if join:
        data += half(0x2900, 0xD000)
    data += half(*before_pointer,
                 0x6800 | literal_reg << 3 | pointer_reg if first is None else first,
                 *before_final,
                 0x6800 | (offset // 4) << 6 | pointer_reg << 3 if last is None else last,
                 0x2200, parent, 0x2228, *before_call)
    site = A + len(data)
    data += bl(site, entry.DIRECT) + half(0xB000 + frame, 0xBC02, 0x4708)
    data += bytes((-len(data)) % 4)
    literal = len(data)
    instruction = 0x4800 | literal_reg << 8 | ((A + literal - ((A + 10) & ~3)) // 4)
    data = data[:6] + half(instruction) + data[8:] + struct.pack('<I', POINT)
    return data, {site: entry.DIRECT}, literal


def verified(**kwargs):
    data, calls, literal = caller(**kwargs)
    proof = bound(data, calls, policy=profile.SELECTOR)
    match.verify_leaf_instructions(data, A, True, calls, buffer_proof=proof)
    return proof, data, calls, literal


class ManagerOffsetTests(unittest.TestCase):
    def test_ordered_loads_with_register_changes_and_offsets(self):
        for offset in (0, 4, 32, 124):
            for registers in ((1, 2), (0, 0), (1, 1), (4, 5)):
                with self.subTest(offset=offset, registers=registers):
                    proof, data, calls, literal = verified(offset=offset,
                        literal_reg=registers[0], pointer_reg=registers[1])
                    report = proof.contract_manifest()
                    chain = report['entry']['manager']
                    self.assertEqual(chain['field_offset'], offset)
                    self.assertEqual(chain['literal_offset'], literal)
                    for pointer, manager in ((0x02005000, 0x02006000), (0x02009000, 0x02007000)):
                        regs, reads, site = raw_until_call(data, {POINT: pointer, pointer + offset: manager})
                        self.assertEqual(regs[0], manager)
                        self.assertEqual(reads, [(chain['pointer_load_site'], POINT),
                                                (chain['dereference_site'], pointer + offset)])
                        self.assertEqual(site, next(iter(calls)))

    def test_conditional_premises_and_exact_source_binding(self):
        report = verified()[0].contract_manifest()
        self.assertEqual(report['schema'], profile.SCHEMA)
        for flag in ('manager_memory_access_proved', 'actual_callback_effects_proved',
                     'nonescape_proved', 'termination_proved'):
            self.assertFalse(report[flag])
        for phrase in ('field offset 32', 'without address wraparound', 'ordered loads',
                       'intervening writes', 'both storage words', 'ambient original R9'):
            self.assertIn(phrase, ' '.join(report['assumptions']))
        with self.assertRaises(KeyError):
            raw_until_call(verified()[1], {POINT: 0x02005000})

    def test_previous_selectors_still_refuse_changed_chain(self):
        data, calls, _ = caller()
        for policy in (entry.SELECTOR, previous.SELECTOR):
            with self.subTest(policy=policy), self.assertRaises(ValueError):
                bound(data, calls, policy=policy)

    def test_wrong_width_or_register_index_refused(self):
        for instruction in (0x7810, 0x8810, 0x5810):
            with self.subTest(instruction=instruction), self.assertRaises(ValueError):
                verified(last=instruction)

    def test_first_dereference_offset_refused(self):
        with self.assertRaisesRegex(ValueError, 'zero-offset'):
            verified(first=0x684A)

    def test_extra_dereference_refused(self):
        with self.assertRaisesRegex(ValueError, 'PC-relative'):
            verified(before_pointer=(0x6809,))

    def test_overwritten_register_provenance_refused(self):
        for options in ({'before_pointer': (0x2100,)}, {'before_final': (0x2200,)},
                        {'before_call': (0x2000,)}):
            with self.subTest(options=options), self.assertRaises(ValueError):
                verified(**options)

    def test_join_cannot_supply_ambiguous_origin(self):
        with self.assertRaisesRegex(ValueError, 'straight-line'):
            verified(join=True)

    def test_extra_call_or_wrong_target_refused(self):
        for calls in ({}, {A: entry.POOL}, {A: entry.DIRECT, A+4: entry.DIRECT}):
            with self.subTest(calls=calls), self.assertRaisesRegex(ValueError, 'one direct'):
                profile.bind(b'', A, {}, {}, calls)

    def test_parent_local_alias_refused(self):
        with self.assertRaisesRegex(ValueError, 'additional register or pointer-word'):
            verified(parent=0x9300)

    def test_descriptor_and_frame_limits_retained(self):
        for options in ({'descriptor': 0}, {'frame': 7}, {'before_call': (0x1C19,)}):
            with self.subTest(options=options), self.assertRaises(ValueError):
                verified(**options)

    def test_literal_requires_exact_typed_zero_addend_binding(self):
        proof, _, _, literal = verified()
        report = proof.contract_manifest()
        profile.check_bindings(report, {'data': [[literal, 'data_02004000', 0]]})
        for rows in ([], [[literal, 'data_02004000', 4]], [[literal+4, 'data_02004000', 0]],
                     [[literal, 'data_02004000', 0], [literal, 'data_02004004', 0]]):
            with self.subTest(rows=rows), self.assertRaises(ValueError):
                profile.check_bindings(report, {'data': rows})

    def test_dependency_identity_remains_required(self):
        data, calls, _ = caller()
        with self.assertRaisesRegex(ValueError, 'dependency identity'):
            bound(data, calls, policy=profile.SELECTOR, pins={entry.DIRECT: (206, '0'*64)})

    def test_selector_registered_in_owner_and_cli(self):
        self.assertIn(profile.SELECTOR, owner.named_buffer.SELECTORS)
        self.assertEqual(owner.selector_for_report('* verification: `' + profile.SCHEMA + '`'), profile.SELECTOR)
        run = subprocess.run([sys.executable, '-B', str(Path(match.__file__)),
                              '--owner-runtime-profile', profile.SELECTOR, '--help'], capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stderr)


if __name__ == '__main__':
    unittest.main()
