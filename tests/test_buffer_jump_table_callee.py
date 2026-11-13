"""A selective-scratch nested callee may follow one canonical jump table, and nothing wider."""
import copy
import hashlib
import struct
import unittest

import test_nested_selective_scratch as base
import test_buffer_index as index_tests

nested = base.nested
match = base.match
A = base.A


def callee(bound='cmp r0, #2', guard='bls dispatch\nb default', dispatch=None, cases=None,
           table='table: .word case0, case1, case2', prefix='', buf='r3'):
    dispatch = dispatch or 'lsls r0, r0, #2\nldr r2, pointer\nadds r0, r0, r2\nldr r0, [r0]\nmov pc, r0'
    cases = cases or (f'case0: ldrh r0, [{buf}]\nb done\ncase1: ldrh r0, [{buf}, #2]\nb done\n'
                      f'case2: ldrb r0, [{buf}, #7]\nb done\n')
    return ('push {lr}\nlsls r0, r0, #24\nlsrs r0, r0, #24\n' + prefix + bound + '\n' + guard +
            '\ndispatch:\n' + dispatch + '\n.balign 4, 0\npointer: .word table\n' + table + '\n' +
            cases + 'default: movs r0, #0\ndone: movs r1, #0\npop {r2}\nbx r2')


class JumpTableCalleeTests(base.NestedSelectiveScratchTests):
    BODY = base.NestedSelectiveScratchTests.PREFIX + 'movs r3, #0' + base.NestedSelectiveScratchTests.SUFFIX

    def run_table(self, selector=nested.SELECTIVE_SELECTOR, manifest=None, **change):
        return self.verify(self.BODY, selector, manifest, helper=callee(**change))

    def refused(self, regex, **change):
        with self.assertRaisesRegex(ValueError, regex):
            self.run_table(**change)

    def test_canonical_table_is_followed_and_hash_bound(self):
        for guard in ('bls dispatch\nb default', 'bhi default'):
            with self.subTest(guard=guard):
                manifest, _ = self.run_table(guard=guard)
                row = next(r for r in manifest['proof']['buffers']['dependencies']
                           if r['structure']['kind'] == 'complete-guarded-buffer-switch-v1')
                args, _, _ = self.owner_inputs(self.BODY, callee(guard=guard))
                rom = args[2]
                body = rom[row['address'] - match.ROM_BASE:row['end'] - match.ROM_BASE]
                self.assertEqual(row['body_sha256'], hashlib.sha256(body).hexdigest())
                literal = row['structure']['switch']['literal']
                self.assertEqual(row['structure']['table_words_sha256'],
                                 hashlib.sha256(body[literal:literal + 16]).hexdigest())
                self.assertEqual(manifest['profile'], nested.SELECTIVE_SCHEMA)
                self.assertEqual(manifest['proof']['buffers']['nested_halfword_outputs']['schema'],
                                 nested.SELECTIVE_SCHEMA)
                self.assertEqual(self.run_table(guard=guard, manifest=manifest)[0], manifest)

    def test_existing_selectors_and_plain_proof_still_refuse(self):
        for selector in (nested.SELECTOR, nested.named.SCRATCH_SELECTOR):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                self.run_table(selector=selector)
        with self.assertRaisesRegex(ValueError, 'unresolved program-counter write'):
            self.run_table(selector=nested.SELECTOR)
        fixture = index_tests.BufferIndexTests.fixture
        case = index_tests.BufferIndexTests('test_register_copy_and_actual_signed_load_shape')
        case.setUp()
        self.addCleanup(case.doCleanups)
        with self.assertRaisesRegex(ValueError, 'unresolved program-counter write'):
            fixture(case, None, caller=index_tests.CALLER,
                    callee=callee(buf='r1'))

    def test_tampered_report_record_or_table_byte_is_refused(self):
        manifest, _ = self.run_table()
        row = next(r for r in manifest['proof']['buffers']['dependencies']
                   if r['structure']['kind'] == 'complete-guarded-buffer-switch-v1')
        for field in ('table_words_sha256', 'successors', 'transfer'):
            altered = copy.deepcopy(manifest)
            next(r for r in altered['proof']['buffers']['dependencies']
                 if r['address'] == row['address'])['structure'][field] = None
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'manifest differs'):
                self.run_table(manifest=altered)

    def test_table_word_changes_are_refused(self):
        # words outside the span, odd, into the pool or the table, or RAM are never recognised as a table
        for table in ('table: .word case0, case1, child', 'table: .word case0, case1, case2+1',
                      'table: .word case0, case1, table', 'table: .word case0, case1, pointer',
                      'table: .word case0, case1, 0x02000000'):
            with self.subTest(table=table):
                self.refused('unresolved program-counter write', table=table.replace('child', 'default+0x100'))

    def test_bound_and_dispatch_shape_are_exact(self):
        for change in (dict(bound='cmp r0, #3'), dict(bound='nop', guard='nop'),
                       dict(guard='bhs dispatch\nb default'),
                       dict(dispatch='lsls r0, r0, #1\nldr r2, pointer\nadds r0, r0, r2\nldr r0, [r0]\nmov pc, r0'),
                       dict(dispatch='lsls r0, r0, #2\nldr r2, pointer\nldr r0, [r0]\nmov pc, r0')):
            with self.subTest(change=change):
                self.refused('unresolved program-counter write', **change)
        self.refused('non-leaf indirect control flow',
                     dispatch='lsls r0, r0, #2\nldr r2, pointer\nadds r0, r0, r2\nldr r0, [r0]\nbx r0')

    def test_guard_bypass_into_the_dispatch_is_refused(self):
        self.refused('structural inventory is not closed', prefix='cmp r0, #0\nbeq dispatch\n')

    def test_second_table_is_refused(self):
        cases = ('case0: ldrh r0, [r3]\nb done\ncase1: ldrh r0, [r3, #2]\nb done\n'
                 'case2: cmp r0, #1\nbhi done\nlsls r0, r0, #2\nldr r2, pointer2\nadds r0, r0, r2\n'
                 'ldr r0, [r0]\nmov pc, r0\n.balign 4, 0\npointer2: .word table2\ntable2: .word done, done\n')
        self.refused('requires one guarded table', cases=cases)

    def test_backward_case_is_refused(self):
        self.refused('unresolved program-counter write', table='table: .word case0, case1, before',
                     prefix='b skip\nbefore: ldrh r0, [r3, #4]\nb done\nskip:\n')

    def test_calls_in_a_delegated_table_callee_are_refused(self):
        cases = 'case0: bl wrapper\nb done\ncase1: ldrh r0, [r3]\nb done\ncase2: ldrh r0, [r3]\nb done\n'
        self.refused('excludes calls', cases=cases)

    def test_every_case_keeps_buffer_bounds_and_nonescape(self):
        for cases, regex in (('case0: ldrh r0, [r3, #8]\nb done\ncase1: ldrh r0, [r3]\nb done\ncase2: ldrh r0, [r3]\nb done\n',
                              'outside allocated'),
                             ('case0: ldrh r0, [r3]\nb done\ncase1: str r3, [r3]\nb done\ncase2: ldrh r0, [r3]\nb done\n',
                              'stored or spilled')):
            with self.subTest(cases=cases):
                self.refused(regex, cases=cases)


if __name__ == '__main__':
    unittest.main(verbosity=2)
