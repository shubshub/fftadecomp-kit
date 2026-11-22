"""External assembler alignment must not become part of the function contract."""
import json
import argparse
from pathlib import Path
import struct
import sys
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import canonical_integer_pair_native_profile as native
import match
import owner_admission_profile as owner
from test_canonical_integer_native_profile import fixture as scalar_fixture


def fixture(*, second_read=0x9D04, padding=True, copy=0x1C20, final=0x4700):
    values = scalar_fixture(prefix=(0xB530, 0x9C03, second_read, copy),
                            suffix=(0xBC30, 0xBC01, final))
    if padding:
        for index in (0, 1):
            raw = bytearray(values[index])
            image = match.elf_image(raw)
            text = image['sections'][image['text_index']]
            end = text[4] + text[5]
            assert text[5] == 18
            assert min(row[4] for row in image['sections'] if row[4] > text[4]) >= end + 2
            raw[end:end+2] = b'\xc0\x46'
            headers = struct.unpack_from('<I', raw, 32)[0]
            struct.pack_into('<I', raw, headers + 40*image['text_index'] + 20, 20)
            values[index] = bytes(raw)
    return values


def text_change(raw, offset, value):
    result = bytearray(raw)
    image = match.elf_image(raw)
    start = image['sections'][image['text_index']][4]
    result[start+offset:start+offset+len(value)] = value
    return bytes(result)


def section_change(raw, field, value):
    result = bytearray(raw)
    image = match.elf_image(raw)
    headers = struct.unpack_from('<I', raw, 32)[0]
    struct.pack_into('<I', result, headers + 40*image['text_index'] + field*4, value)
    return bytes(result)


class TwoWordsAlignmentTests(unittest.TestCase):
    def setUp(self):
        env = patch.object(native, 'environment_fingerprint', return_value={'alignment_fixture': True})
        env.start(); self.addCleanup(env.stop)
        closure = patch.object(native.inventory.core, 'prove_called_closures', return_value=({}, {}, []))
        self.closure = closure.start(); self.addCleanup(closure.stop)

    def verify(self, values):
        return native.verify_original(*values)

    def test_external_NOP_is_excluded_from_exact_owner_and_entry_contract(self):
        result, count = self.verify(fixture())
        proof = result['prerequisite']
        self.assertEqual(count, 8)
        self.assertEqual(proof['end'] - proof['address'], 18)
        self.assertEqual(proof['entry_stack_policy']['words'], [0, 1])
        self.assertFalse(proof['memory_safety_claim'])
        self.assertEqual(proof['entry_loaded_value_facts'], [])
        self.closure.assert_called_once()

    def test_same_new_frame_without_external_padding_remains_valid(self):
        result, count = self.verify(fixture(padding=False))
        self.assertEqual(count, 8)
        self.assertEqual(result['bindings']['data'], [])

    def test_original_tail_must_be_canonical_NOP(self):
        values = fixture(); values[0] = text_change(values[0], 18, b'\x00\x00')
        with self.assertRaisesRegex(ValueError, 'terminal alignment'):
            self.verify(values)
        self.closure.assert_not_called()

    def test_linked_tail_must_be_canonical_NOP(self):
        values = fixture(); values[1] = text_change(values[1], 18, b'\x70\x47')
        with self.assertRaisesRegex(ValueError, 'terminal alignment'):
            self.verify(values)
        self.closure.assert_not_called()

    def test_original_alignment_requires_four_byte_section_alignment(self):
        values = fixture(); values[0] = section_change(values[0], 8, 2)
        with self.assertRaisesRegex(ValueError, 'terminal alignment'):
            self.verify(values)

    def test_linked_alignment_requires_four_byte_section_alignment(self):
        values = fixture(); values[1] = section_change(values[1], 8, 2)
        with self.assertRaisesRegex(ValueError, 'terminal alignment'):
            self.verify(values)

    def test_padding_cannot_have_a_symbol_owner(self):
        values = fixture(); raw = bytearray(values[0]); image = match.elf_image(raw)
        for section_no, symbols in image['symbol_tables'].items():
            for number, symbol in enumerate(symbols):
                if symbol['type'] == 3 and symbol['section'] == image['text_index']:
                    struct.pack_into('<I', raw, image['sections'][section_no][4]+number*16+4, 18)
        values[0] = bytes(raw)
        with self.assertRaisesRegex(ValueError, 'symbol owner'):
            self.verify(values)

    def test_alignment_cannot_add_an_unread_incoming_word(self):
        with self.assertRaisesRegex(ValueError, 'every declared incoming word'):
            self.verify(fixture(second_read=0x9D03))
        self.closure.assert_not_called()

    def test_alignment_cannot_grant_a_third_incoming_word(self):
        with self.assertRaises(ValueError):
            self.verify(fixture(second_read=0x9D05))
        self.closure.assert_not_called()

    def test_alignment_cannot_permit_incoming_store(self):
        with self.assertRaises(ValueError):
            self.verify(fixture(second_read=0x9504))
        self.closure.assert_not_called()

    def test_owner_graph_refuses_encodings_the_ARM7TDMI_does_not_execute(self):
        # kit #180: this admission path replays the owner graph and never runs the base leaf walk.
        for name, change in (('mov r0, r4', dict(copy=0x4620)), ('add r0, r4', dict(copy=0x4420)),
                             ('cmp r0, r4', dict(copy=0x4520)), ('bx r0 with an SBZ bit', dict(final=0x4701))):
            with self.subTest(name), self.assertRaisesRegex(
                    ValueError, 'owner graph instruction is not an ARMv4T encoding or a BL pair'):
                self.verify(fixture(**change))
        self.closure.assert_not_called()

    def test_actual_sized_function_bytes_still_bind_ROM(self):
        values = fixture(); rom = bytearray(values[3]); rom[0x106] ^= 1; values[3] = bytes(rom)
        with self.assertRaises(ValueError):
            self.verify(values)
        self.closure.assert_not_called()

    def test_index_cannot_absorb_external_padding(self):
        values = fixture(); rows = json.loads(values[4]); rows[0]['end'] = f'0x{values[2]+20:08X}'
        values[4] = json.dumps(rows).encode()
        with self.assertRaises(ValueError):
            self.verify(values)
        self.closure.assert_not_called()

    def test_default_owner_selector_does_not_gain_alignment_permission(self):
        values = fixture()
        with self.assertRaisesRegex(ValueError, 'sole complete Thumb'):
            owner.original_bindings(match.elf_image(values[0]), values[2], values[3], values[4],
                                    b'{}', selector=owner.ACYCLIC_SELECTOR, index=values[5])

    def test_data_profile_keeps_its_named_object_requirement(self):
        import canonical_integer_two_words_native_profile as data_native
        values = fixture(padding=False)
        with self.assertRaisesRegex(ValueError, 'named objects'):
            owner.original_bindings(match.elf_image(values[0]), values[2], values[3], values[4],
                                    b'{}', selector=data_native.SELECTOR, index=values[5])

    def test_pair_profile_rejects_original_named_data_roles(self):
        from test_canonical_integer_two_words_native_profile import fixture as data_fixture
        values = data_fixture()
        with self.assertRaises(ValueError):
            self.verify(values)
        self.closure.assert_not_called()

    def test_new_report_routes_to_pair_selector_and_requires_original_ELF(self):
        values = fixture(); manifest, count = self.verify(values)
        original, linked, address, rom, mapping, index, bindings = values
        data = rom[0x100:0x112]
        result = (data, manifest, 'a'*64, mapping, index, b'{}', rom, count, original)
        report = owner.render(address, result)
        self.assertTrue(owner.selected(report))
        self.assertEqual(owner.selector_for_report(report), native.SELECTOR)
        self.assertIn('* control flow: '+native.CONTROL_FLOW, report)
        with self.assertRaisesRegex(ValueError, 'original ELF identity'):
            owner.fingerprint(address, data, manifest, 'a'*64, mapping, index, b'{}', rom)
        with patch.object(owner, 'build', return_value=result) as build:
            self.assertTrue(owner.report_matches(report, '.', address))
            self.assertEqual(build.call_args.kwargs['selector'], native.SELECTOR)

    def test_pair_selector_rejects_mixed_native_policies(self):
        options = dict(mode='thumb', control_flow_profile='ordinary', software_double_profile=None,
            software_double_remainder_profile=None, function_address_profile=None, switch_profile=None,
            label=None, wsl='Ubuntu', wsl_path=match.DEFAULT_WSL_PATH, owner_runtime_profile=native.SELECTOR)
        with patch.object(owner, 'build') as build, self.assertRaisesRegex(ValueError, 'excludes mixed'):
            owner.issue('.', 0x08000100, argparse.Namespace(**options, signed_runtime_profile='mixed'))
        build.assert_not_called()


if __name__ == '__main__':
    unittest.main()
