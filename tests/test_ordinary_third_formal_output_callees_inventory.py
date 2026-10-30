"""Synthetic local-byte initialization and independent formal-output cases."""
import json
import os
from pathlib import Path
import struct
import subprocess
import sys
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
sys.path.insert(0, str(Path(__file__).resolve().parent))
from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
from capstone.arm import ARM_REG_R0, ARM_REG_R3
import ordinary_third_formal_output_callees_inventory as profile
from test_ordinary_second_formal_output_callees_inventory import FIRST_WORDS

A, F, T, O = 0x08010000, 0x08021000, 0x08023000, 0x08024000
CALLER = [0xB570, 0xB084, 0x466C, 0x340A, 0xAD03, 0xA802, 0x1C21, 0x1C2A, 'third',
    0xA802, 0x2100, 0x5E40, 0x2200, 0x5EA1, 0x2300, 0x5EEA,
    0x9400, 0x9501, 0xAB02, 'first', 0xA802, 0x8800, 'ordinary', 0xB004, 0xBC70, 0xBC01, 0x4700]


def machine(words, address):
    data = bytearray()
    for word in words:
        if type(word) is int:
            data += struct.pack('<H', word)
        else:
            delta = dict(first=F, third=T, ordinary=O)[word] - address - len(data) - 4
            data += struct.pack('<HH', 0xF000 | ((delta >> 12) & 0x7FF), 0xF800 | ((delta >> 1) & 0x7FF))
    return bytes(data)


def helper_words():
    words = [0xB570, 0x4646, 0xB440, 0xB082, 0x466D, 0x2301, 0x446B, 0x4698]
    literal_site = len(words)
    words.append(0)
    for offset, local in zip((13, 15, 10, 12, 14, 11), range(6)):
        words += [0x7823 | (offset << 6), 0x702B | (local << 6)]
    words += [0x782C, 0x466E, 0x3605, 0x7834, 0x4645, 0x782C, 0x466D,
              0x800C, 0x8014, 0x8004, 0x8808, 0x8008, 0x8810, 0x8010,
              0xB002, 0xBC08, 0x4698, 0xBC70, 0xBC08, 0x4718]
    if len(words) % 2 == 0:
        words.insert(-6, 0x0064)
    literal_offset = 2 * (len(words) + 1)
    pc = (T + 2 * literal_site + 4) & ~3
    words[literal_site] = 0x4C00 | ((T + literal_offset - pc) // 4)
    return words


HELPER = helper_words()


def fixture(caller=CALLER, helper=HELPER):
    body = machine(caller, A)
    first = machine(FIRST_WORDS, F) + struct.pack('<I', profile.named.GLOBAL)
    third = machine(helper, T) + b'\0\0' + struct.pack('<I', profile.GLOBAL)
    objects = [(A, body, len(caller)), (F, first, 34), (T, third, len(helper)), (O, b'\x70\x47', 1)]
    rows = [dict(rom=f'0x{address:08X}', end=f'0x{address+len(data):08X}', mode='thumb', instrs=count)
            for address, data, count in objects]
    mapping = (json.dumps(rows, indent=2) + '\n').encode()
    index = ''.join(f'{address:08X} {address+len(data):08X} {len(data)} {count} return\n'
                    for address, data, count in objects).encode()
    rom = bytearray(O - profile.parent.match.ROM_BASE + 2)
    for address, data, _ in objects:
        rom[address-profile.parent.match.ROM_BASE:address-profile.parent.match.ROM_BASE+len(data)] = data
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    decoder.detail = True
    calls = {item.address: item.operands[0].imm for item in decoder.disasm(body, A) if item.mnemonic == 'bl'}
    return dict(data=body, address=A, rom=bytes(rom), mapping=mapping, index=index,
        data_mapping=(json.dumps({profile.named.NAME: f'0x{profile.named.GLOBAL:08X}', profile.NAME: f'0x{profile.GLOBAL:08X}'}) + '\n').encode(),
        calls=calls, bindings={site: f'func_{target:08X}' for site, target in calls.items()}, selector=profile.SELECTOR,
        readonly_named_buffer_policy=profile.named.named_policy(), readonly_third_named_buffer_policy=profile.third_named_policy())


class ThirdOutputTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        first = machine(FIRST_WORDS, F) + struct.pack('<I', profile.named.GLOBAL)
        third = machine(HELPER, T) + b'\0\0' + struct.pack('<I', profile.GLOBAL)
        for module, name, identity in ((profile, 'FIRST', (F, F+len(first), 34, profile.sha(first))),
                (profile.prior.leaf, 'LEAF', (F, F+len(first), 34, profile.sha(first))),
                (profile, 'THIRD', (T, T+len(third), len(HELPER), profile.sha(third)))):
            change = patch.object(module, name, identity)
            change.start()
            cls.addClassCleanup(change.stop)

    def native(self, caller=CALLER, **changes):
        values = fixture(caller)
        values.update(changes)
        return profile.verify(**values)

    def changed_helper(self, position, word):
        words = list(HELPER)
        words[position] = word
        values = fixture(helper=words)
        data = machine(words, T) + b'\0\0' + struct.pack('<I', profile.GLOBAL)
        with patch.object(profile, 'THIRD', (T, T+len(data), len(words), profile.sha(data))):
            return profile.verify(**values)

    def test_full_API_and_CLI_fresh_local_initialization_and_three_frames(self):
        values = fixture()
        result, instructions = profile.verify(**values)
        self.assertEqual(len(instructions), len(CALLER))
        self.assertEqual(result['frame']['maximum_frame_bytes'], 32)
        leaves = result['frame']['formal_stack_callee']['callees']
        third = leaves[1]['native_leaf']
        self.assertEqual(third['frame']['maximum_frame_bytes'], 28)
        self.assertEqual(len(third['effects']['local_byte_writes']), 6)
        self.assertEqual([row[1] for row in third['effects']['local_byte_writes']], list(range(-28, -22)))
        self.assertEqual(third['effects']['store_event_count'], 5)
        self.assertEqual(len(third['effects']['formal_reads_after_own_writes']), 2)
        self.assertEqual(leaves[1]['calls'][0]['writes_entry_SP_offsets'], [[-24, 2], [-22, 2], [-20, 2]])
        self.assertFalse(result['source_or_ELF_admission'])
        root = Path(os.environ['FFTA_THIRD_OUTPUT_RETAIN'])
        root.mkdir(parents=True, exist_ok=True)
        for name, field in [('rom.bin', 'rom'), ('functions.json', 'mapping'), ('functions.txt', 'index'), ('data_symbols.json', 'data_mapping')]:
            (root / name).write_bytes(values[field])
        (root / 'api.json').write_text(json.dumps(result, indent=2) + '\n')
        code = ('import sys;sys.path.insert(0,sys.argv.pop(1));import ordinary_third_formal_output_callees_inventory as p;'
                f'p.FIRST={profile.FIRST!r};p.THIRD={profile.THIRD!r};p.prior.leaf.LEAF=p.FIRST;p.main()')
        run = subprocess.run([sys.executable, '-c', code, str(Path(profile.__file__).parent), '--profile', profile.SELECTOR,
            '--rom', str(root/'rom.bin'), '--mapping', str(root/'functions.json'), '--index', str(root/'functions.txt'),
            '--data-mapping', str(root/'data_symbols.json'), '--readonly-named-buffer-policy', profile.text(profile.named.named_policy()),
            '--readonly-third-named-buffer-policy', profile.text(profile.third_named_policy()), f'{A:08X}'], capture_output=True, text=True)
        (root / 'cli-stdout.json').write_text(run.stdout)
        (root / 'cli-stderr.txt').write_text(run.stderr)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertEqual(json.loads(run.stdout), result)

    def test_local_read_before_write_saved_overlap_and_local_width(self):
        for position, word in [(10, 0x782B), (10, 0x722B), (10, 0x802B), (7, 0x4618)]:
            with self.subTest(position=position), self.assertRaises(ValueError):
                self.changed_helper(position, word)

    def test_named_width_offset_store_and_pointer_spill_refused(self):
        for position, word in [(9, 0x7A63), (9, 0x8B63), (9, 0x7363), (10, 0x7028), (1, 0x4606)]:
            with self.subTest(position=position), self.assertRaises(ValueError):
                self.changed_helper(position, word)

    def test_formal_reads_require_own_prior_writes(self):
        position = HELPER.index(0x800C)
        with self.assertRaisesRegex(ValueError, 'formal read precedes'):
            self.changed_helper(position, 0x880C)

    def test_separate_exact_policy_types_and_binding(self):
        policy = profile.third_named_policy()
        for value in (None, {}, profile.named.named_policy(), dict(policy, initialized=1), dict(policy, readable=False),
                      dict(policy, reads=[[10, 2]]), dict(policy, reads=[[True, 1]]), dict(policy, extra=True)):
            with self.subTest(value=value), self.assertRaises(ValueError):
                self.native(readonly_third_named_buffer_policy=value)
        with self.assertRaises(ValueError):
            self.native(data_mapping=b'{}')
        with self.assertRaises(ValueError):
            self.native(selector=profile.prior.SELECTOR)

    def test_complete_helper_identity_dual_indices_and_manifest(self):
        values = fixture()
        rom = bytearray(values['rom'])
        rom[T-profile.parent.match.ROM_BASE] ^= 4
        with self.assertRaises(ValueError):
            self.native(rom=bytes(rom))
        with self.assertRaises(ValueError):
            self.native(index=values['index'].replace(f'{len(HELPER)} return'.encode(), b'999 return'))
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            self.native(manifest={'complete': True})

    def test_callset_and_unmarked_alias_calls(self):
        values = fixture()
        with self.assertRaises(ValueError):
            self.native(calls={})
        with self.assertRaises(ValueError):
            self.native(bindings={})
        position = CALLER.index('third')
        with self.assertRaisesRegex(ValueError, 'crossing calls'):
            self.native(CALLER[:position] + ['ordinary'] + CALLER[position:])

    def test_actual_formal_domains_lifetime_overlap_and_outgoing_words(self):
        values = fixture()
        third = machine(HELPER, T) + b'\0\0' + struct.pack('<I', profile.GLOBAL)
        proof = profile.LocalByteOutputLeafProof(third, T, values['rom'], values['mapping'], values['index'],
            values['data_mapping'], {A+16: T}, profile.third_named_policy())
        stack = [('local', None)]*4 + [('saved', None)]*4
        aliases = {ARM_REG_R0+n: frozenset(((offset, True),)) for n, offset in enumerate((-24, -22, -20))}
        self.assertEqual(proof.check_call(A+16, T, aliases, stack, {}), [(-24, 2), (-22, 2), (-20, 2)])
        for value in (frozenset(((-24, False),)), frozenset(((-22, True),)), frozenset(((-23, True),)),
                      frozenset(((-32, True),)), frozenset(((-16, True),)), frozenset(((-24, True), (-26, True)))):
            altered = dict(aliases)
            altered[ARM_REG_R0] = value
            with self.subTest(value=value), self.assertRaises(ValueError):
                proof.check_call(A+16, T, altered, stack, {})
        altered = dict(aliases)
        altered[ARM_REG_R3] = frozenset(((-18, True),))
        with self.assertRaises(ValueError):
            proof.check_call(A+16, T, altered, stack, {})
        proof._record['effects']['local_byte_reads'] = []
        with self.assertRaises(ValueError):
            proof.validate_calls({A+16: T})

    def test_default_frame_and_forged_proofs_stay_closed(self):
        values = fixture()
        ins, edges, calls, _ = profile.parent.complete(values['data'], A, values['rom'], values['mapping'], values['index'])
        with self.assertRaisesRegex(ValueError, 'crossing calls'):
            profile.parent.frame.prove_frame(ins, edges, A, {}, calls, stack_aliases=True,
                local_alias_slot_policy=profile.parent.slots.SELECTOR, zero_index_profile=profile.parent.zero_index.SELECTOR)
        with self.assertRaisesRegex(ValueError, 'exclusive fresh native'):
            profile.parent.frame.prove_frame(ins, edges, A, {}, calls, stack_aliases=True,
                local_alias_slot_policy=profile.parent.slots.SELECTOR, formal_stack_callee_proof={'complete': True})


if __name__ == '__main__':
    unittest.main()
