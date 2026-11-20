"""An indexed switch leaf must prove every case, every local read, and its original bindings."""
import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import owner_admission_profile as owner
import stack_index_precondition_profile as stack_index
import test_owner_switch_buffers as switch_fixture


class StackIndexOwnerSwitchTests(unittest.TestCase):
    def setUp(self):
        self.assembler = switch_fixture.OwnerSwitchTests()
        self.assembler.setUp()
        self.addCleanup(self.assembler.doCleanups)

    def fixture(self, *, bound=2, initialize='strb r3, [r2,#2]', final='movs r0,#0',
                guard='bhi inspect', case='movs r1,#1', before_guard=''):
        body = f'''push {{r4,lr}}
            sub sp,#4
            mov r2,sp
            movs r3,#0
            strb r3,[r2]
            strb r3,[r2,#1]
            {initialize}
            {before_guard}
            cmp r0,#2
            {guard}
            lsls r0,r0,#2
            ldr r1,pointer
            adds r0,r0,r1
            ldr r0,[r0]
            mov pc,r0
            .balign 4,0
        pointer: .word table
        table: .word first,second,third
        first: {case}
            b inspect
        second: movs r1,#2
            b inspect
        third: movs r1,#3
        inspect: ldr r4,named
        next: mov r0,sp
            adds r1,r0,r3
            ldrb r0,[r1]
            ldrb r1,[r4]
            adds r3,#1
            cmp r3,#{bound}
            ble next
            {final}
            add sp,#4
            pop {{r4}}
            pop {{r1}}
            bx r1
            .balign 4,0
        named: .word 0x02002000'''
        fixture = self.assembler.fixture(body=body)
        calls, words = self.assembler.linked(fixture)
        return dict(fixture, address=switch_fixture.A, selector=stack_index.SELECTOR_V2,
                    objects=json.dumps({'data_table':'0x02002000'}).encode(),
                    bindings=dict(calls=[[s-switch_fixture.A, f'func_{d:08X}'] for s,d in sorted(calls.items())],
                                  switches=[list(row) for row in sorted(words.items())], functions=[],
                                  data=[[len(fixture['data'])-4,'data_table',0]]))

    def test_complete_table_private_bytes_and_r2_return_scratch(self):
        manifest, _ = owner.verify(**self.fixture())
        buffers = manifest['proof']['buffers']
        self.assertEqual(len(buffers['indexed_leaf_switch']['successors']), 3)
        bounded = buffers['stack_index_preconditions']
        self.assertEqual(bounded['preconditions'], [])
        self.assertEqual(bounded['accesses'][0][1:5], ['load', 1, -12, -10])
        self.assertEqual(buffers['root_return_scratch']['observations'][0][1:], [2, -12])

    def test_index_bounds_and_initialized_bytes(self):
        for args in (dict(bound=3), dict(bound=4), dict(initialize='movs r3,#0')):
            with self.subTest(args=args), self.assertRaisesRegex(ValueError, 'uninitialised|saved register|index range|runtime premise'):
                owner.verify(**self.fixture(**args))

    def test_one_case_indexes_uninitialised_byte_after_join(self):
        # All paths start with r3=0. Only the first case changes the shared loop index.
        owner.verify(**self.fixture(case='movs r3,#2'))
        with self.assertRaisesRegex(ValueError, 'index range reads uninitialised local bytes'):
            owner.verify(**self.fixture(case='movs r3,#3'))

    def test_return_registers_and_interior_paths_keep_escape_checks(self):
        for args in (dict(final='mov r0,sp'), dict(case='str r2,[r4]')):
            with self.subTest(args=args), self.assertRaisesRegex(ValueError, 'escape|cannot be stored'):
                owner.verify(**self.fixture(**args))

    def test_only_dispatch_may_read_table_and_only_leaf_is_admitted(self):
        with self.assertRaisesRegex(ValueError, 'canonical dispatch'):
            owner.verify(**self.fixture(before_guard='ldr r1,pointer'))
        with self.assertRaisesRegex(ValueError, 'excludes local BL and word switches'):
            owner.verify(**self.fixture(case='bl callee'))
        fixture = self.fixture()
        fixture['selector'] = stack_index.SELECTOR
        with self.assertRaisesRegex(ValueError, 'excludes local BL and word switches'):
            owner.verify(**fixture)

    def test_bindings_must_cover_actual_table_and_data(self):
        for binding in ('switches', 'data'):
            fixture = self.fixture()
            fixture['bindings'][binding].pop()
            with self.subTest(binding=binding), self.assertRaisesRegex(ValueError, 'guarded switch words|requires named data'):
                owner.verify(**fixture)

    def test_unguarded_transfer_has_no_authenticated_edges(self):
        with self.assertRaises(ValueError):
            owner.verify(**self.fixture(guard='bne inspect'))
