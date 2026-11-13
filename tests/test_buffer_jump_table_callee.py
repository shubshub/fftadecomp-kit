"""A buffer callee may follow one canonical compiler jump table, and nothing wider."""
import copy
import hashlib
import json
import struct
import sys
import unittest
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import named_data_buffer_profile as buffers
import owner_admission_profile as owner
import test_buffer_discarded_return_scratch as scratch_tests
import test_buffer_index as index_tests

B, C, BASE = scratch_tests.B, scratch_tests.C, index_tests.BASE

CALLER = ("push {r4, lr}\nsub sp, #8\nmov r1, sp\nmovs r0, #0\n"
          "bl callee\nadd sp, #8\npop {r4}\npop {r0}\nbx r0")


def callee(buf='r1', tail='movs r3, #0\n', bound='cmp r0, #2', guard='bls dispatch\nb default', dispatch=None, cases=None,
           table='table: .word case0, case1, case2'):
    dispatch = dispatch or 'lsls r0, r0, #2\nldr r2, pointer\nadds r0, r0, r2\nldr r0, [r0]\nmov pc, r0'
    cases = cases or (f'case0: ldrh r0, [{buf}]\nb done\ncase1: ldrh r0, [{buf}, #2]\nb done\n'
                      f'case2: ldrb r0, [{buf}, #7]\nb done\n')
    return ('push {lr}\nlsls r0, r0, #24\nlsrs r0, r0, #24\n' + bound + '\n' + guard +
            '\ndispatch:\n' + dispatch + '\n.balign 4, 0\npointer: .word table\n' + table + '\n' +
            cases + 'default: movs r0, #0\ndone: movs r1, #0\n' + tail + 'pop {r2}\nbx r2')


class PlainJumpTableTests(unittest.TestCase):
    setUp = index_tests.BufferIndexTests.setUp
    fixture = index_tests.BufferIndexTests.fixture

    def proof(self, **change):
        return self.fixture(None, caller=CALLER, callee=callee(**change))

    def test_canonical_table_is_followed_and_hash_bound(self):
        for guard in ('bls dispatch\nb default', 'bhi default'):
            with self.subTest(guard=guard):
                proof = self.proof(guard=guard) if guard.startswith('bhi') else self.proof()
                self.assertEqual(set(proof.dependencies), {BASE + 0x100})
                self.assertEqual(self.proof().fingerprint(), self.proof().fingerprint())

    def tamper(self, proof, index, value):
        data = bytearray(proof.dependencies[BASE + 0x100])
        table = struct.unpack_from('<I', data, next(
            offset for offset in range(0, len(data) - 3, 4)
            if BASE + 0x100 < struct.unpack_from('<I', data, offset)[0] < BASE + 0x100 + len(data) and
            struct.unpack_from('<I', data, offset)[0] == BASE + 0x100 + offset + 4))[0] - BASE - 0x100
        struct.pack_into('<I', data, table + 4 * index, value)
        rom = bytearray(proof.rom)
        rom[0x100:0x100 + len(data)] = data
        return match.BufferCallProof(bytes(rom), json.dumps(self.entries).encode(), stack_arguments=True)

    def run_caller(self, proof):
        return match.verify_leaf_instructions(self.body, BASE, True, buffer_proof=proof,
                                              call_resolver=proof.target)

    def test_tampered_table_bytes_change_the_proof_or_are_refused(self):
        proof = self.proof()
        data = proof.dependencies[BASE + 0x100]
        cases = [BASE + 0x100 + data.index(b'\x08\x88')]  # first ldrh case body
        swapped = self.tamper(proof, 0, struct.unpack_from('<I', data, len(data) and next(
            o for o in range(0, len(data) - 3, 4)
            if struct.unpack_from('<I', data, o)[0] == BASE + 0x100 + o + 4) + 8)[0])
        self.run_caller(swapped)
        self.assertNotEqual(swapped.fingerprint(), proof.fingerprint())
        for value in (BASE + 0x1FE, BASE + 0x100 + len(data), BASE + 0x100 + 1 + cases[0] - BASE - 0x100, 0x02000000):
            with self.subTest(value=hex(value)), self.assertRaises(ValueError):
                self.run_caller(self.tamper(proof, 1, value))

    def test_every_case_keeps_buffer_bounds_and_nonescape(self):
        for cases in ('case0: ldrh r0, [r1, #8]\nb done\ncase1: ldrh r0, [r1]\nb done\ncase2: ldrh r0, [r1]\nb done\n',
                      'case0: ldrh r0, [r1]\nb done\ncase1: str r1, [r1]\nb done\ncase2: ldrh r0, [r1]\nb done\n',
                      'case0: ldrh r0, [r1]\nb done\ncase1: ldrh r0, [r1]\nb done\ncase2: ldr r0, [r1, #8]\nb done\n'):
            with self.subTest(cases=cases), self.assertRaises(ValueError):
                self.proof(cases=cases)

    def test_noncanonical_guards_and_dispatch_are_refused(self):
        for change in (dict(bound='cmp r0, #3'),  # too wide for three words
                       dict(bound='nop', guard='nop'),  # missing bound check
                       dict(guard='bhs dispatch\nb default'),
                       dict(dispatch='lsls r0, r0, #1\nldr r2, pointer\nadds r0, r0, r2\nldr r0, [r0]\nmov pc, r0'),
                       dict(dispatch='lsls r0, r0, #2\nldr r2, pointer\nadds r0, r0, r2\nldr r0, [r0]\nbx r0'),
                       dict(dispatch='lsls r0, r0, #2\nldr r2, pointer\nldr r0, [r0]\nmov pc, r0')):
            with self.subTest(change=change), self.assertRaises(ValueError):
                self.proof(**change)

    def test_table_words_must_be_forward_aligned_cases_inside_the_span(self):
        for table in ('table: .word case0, case1, child',        # outside the callee span
                      'table: .word case0, case1, case2+1',      # misaligned
                      'table: .word case0, case1, table',        # into the table
                      'table: .word case0, case1, pointer',      # into the pool
                      'table: .word case0, case1, 0x02000000'):  # RAM word
            with self.subTest(table=table), self.assertRaises(ValueError):
                self.proof(table=table)

    def test_calls_inside_a_table_callee_are_refused(self):
        cases = ('case0: bl child\nb done\ncase1: ldrh r0, [r1]\nb done\ncase2: ldrh r0, [r1]\nb done\n')
        with self.assertRaises(ValueError):
            self.proof(cases=cases)


class NamedJumpTableTests(unittest.TestCase):
    setUp = scratch_tests.DiscardedReturnScratchTests.setUp
    fixture = scratch_tests.DiscardedReturnScratchTests.fixture
    switch_fixture = None

    def selected(self, selector=buffers.SCRATCH_SELECTOR, **change):
        f = self.fixture(after='movs r3, #0', callee=callee(buf='r3', tail='', **change))
        return dict(f, selector=selector)

    def test_scratch_selector_records_the_table_hash(self):
        for selector in (buffers.SCRATCH_SELECTOR,):
            with self.subTest(selector=selector):
                f = self.selected(selector)
                manifest, _ = owner.verify(**f)
                row, = manifest['proof']['buffers']['dependencies']
                self.assertEqual(row['structure']['kind'], 'complete-guarded-buffer-switch-v1')
                self.assertEqual(row['body_sha256'], hashlib.sha256(f['rom'][B - match.ROM_BASE:][:row['bytes']]).hexdigest())
                literal = row['structure']['switch']['literal']
                words = f['rom'][B - match.ROM_BASE + literal:][:16]
                self.assertEqual(row['structure']['table_words_sha256'], hashlib.sha256(words).hexdigest())

    def test_tampered_report_record_or_table_byte_is_refused(self):
        f = self.selected()
        manifest, _ = owner.verify(**f)
        for field in ('table_words_sha256', 'successors', 'transfer'):
            altered = copy.deepcopy(manifest)
            altered['proof']['buffers']['dependencies'][0]['structure'][field] = None
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'manifest differs'):
                owner.verify(**dict(f, manifest=altered))
        image = bytearray(f['rom'])
        table = manifest['proof']['buffers']['dependencies'][0]['structure']['switch']['table']
        struct.pack_into('<I', image, B - match.ROM_BASE + table, C)
        with self.assertRaises(ValueError):
            owner.verify(**dict(f, rom=bytes(image), manifest=manifest))

    def test_noncanonical_shapes_are_refused_by_buffer_selector(self):
        for change in (dict(bound='cmp r0, #3'),
                       dict(table='table: .word case0, case1, child'),
                       dict(table='table: .word case0, case1, case2+1'),
                       dict(table='table: .word case0, case1, table'),
                       dict(dispatch='lsls r0, r0, #2\nldr r2, pointer\nadds r0, r0, r2\nldr r0, [r0]\nbx r0')):
            with self.subTest(change=change), self.assertRaises(ValueError):
                owner.verify(**self.selected(**change))


if __name__ == '__main__':
    unittest.main(verbosity=2)
