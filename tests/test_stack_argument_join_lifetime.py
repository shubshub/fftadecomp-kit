"""Stack-argument joins may forget only registers killed before observation."""
import json
import unittest

import test_stack_alias_join_lifetime as fixtures

match = fixtures.match
BASE = fixtures.BASE


class StackArgumentJoinLifetimeTests(unittest.TestCase):
    setUp = fixtures.StackAliasJoinLifetimeTests.setUp
    body = fixtures.StackAliasJoinLifetimeTests.body

    def joined(self, after='', *, second_offset=23, spill=False,
               result_zero=True):
        # Same R8/local-SP+21 versus R8/local-SP+23 shape as retained B4A1C.
        store = 'mov r0, r8\nstr r0, [sp]\nmovs r0, #0\n' if spill else ''
        return ('push {r4, lr}\nmov r4, r8\npush {r4}\nsub sp, #32\n'
                'cmp r0, #0\nbeq second\nmov r2, sp\nadds r2, #21\n'
                'mov r8, r2\nmovs r2, #0\n' + store + 'b joined\n'
                'second:\nmov r1, sp\nadds r1, #' + str(second_offset) + '\n'
                'mov r8, r1\nmovs r1, #0\n' + store + 'joined:\n' + after +
                ('\nmovs r0, #0' if result_zero else '') +
                '\nadd sp, #32\npop {r4}\nmov r8, r4\npop {r4}\npop {r1}\nbx r1')

    def verify(self, source, *, stack_arguments=True):
        data = self.body(source)
        rom = (self.root / 'join.bin').read_bytes()
        mapping = json.dumps([{'rom': f'0x{BASE + 0x100:08X}',
                               'end': f'0x{BASE + 0x102:08X}', 'mode': 'thumb'}])
        proof = match.BufferCallProof(rom, mapping, stack_arguments=stack_arguments)
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        calls = {item.address: item.operands[0].imm for item in decoder.disasm(data, BASE)
                 if match.CS_GRP_CALL in item.groups}
        return match.verify_leaf_instructions(data, BASE, True, calls, buffer_proof=proof)

    def test_real_shape_dead_r8_sp21_sp23(self):
        self.verify(self.joined())

    def test_all_successors_overwrite_before_use(self):
        self.verify(self.joined('cmp r0, #1\nbeq left\nmovs r2, #2\n'
            'mov r8, r2\nb done\nleft:\nmovs r3, #3\nmov r8, r3\ndone:'))

    def test_live_read_and_memory_access_before_overwrite_refused(self):
        for after in ('mov r2, r8\nmovs r2, #0',
                      'mov r1, r8\nldrb r0, [r1]\nmovs r1, #0'):
            with self.subTest(after=after), self.assertRaises(ValueError):
                self.verify(self.joined(after))

    def test_external_store_and_call_forwarding_refused(self):
        for after in ('mov r0, r8\nstr r0, [r3]\nmovs r0, #0',
                      'mov r0, r8\nbl callee\nmovs r0, #0',
                      'bl callee'):
            with self.subTest(after=after), self.assertRaises(ValueError):
                self.verify(self.joined(after))

    def test_one_live_successor_refused(self):
        with self.assertRaises(ValueError):
            self.verify(self.joined('cmp r0, #1\nbeq live\nmovs r2, #0\n'
                'mov r8, r2\nb done\nlive:\nmov r2, r8\nmovs r2, #0\ndone:'))

    def test_pointer_word_join_remains_rejected(self):
        with self.assertRaisesRegex(ValueError, 'inconsistent possible pointer offsets'):
            self.verify(self.joined(spill=True))

    def test_pointer_return_and_saved_return_corruption_refused(self):
        with self.assertRaises(ValueError):
            self.verify(self.joined('mov r0, r8', result_zero=False))
        with self.assertRaises(ValueError):
            self.verify(self.joined('movs r0, #0\nstr r0, [sp, #40]'))

    def test_equal_live_join_and_previous_nonstack_route_unchanged(self):
        self.verify(self.joined('mov r1, r8\nldrb r0, [r1]\nmovs r1, #0',
                               second_offset=21))
        self.verify(self.joined(), stack_arguments=False)


if __name__ == '__main__':
    unittest.main(verbosity=2)
