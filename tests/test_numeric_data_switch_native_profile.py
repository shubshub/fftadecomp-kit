"""Independent raw Thumb/ELF fixtures for numeric switch source admission."""
import json
from pathlib import Path
import struct
import sys
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import numeric_data_switch_native_profile as native
import owner_admission_profile as owner
import one_constant_scalar_switch_inventory as inventory
from test_canonical_integer_native_profile import symbol_change
from test_typed_switch_outgoing_frame import relocatable
BASE, CALLEE, POINT = 0x08000100, 0x08001000, 0x02001000
OBJECTS = json.dumps({'g_point': f'0x{POINT:08X}'}).encode()


def fixture(*, half=None, word=None, count=22, point=POINT, alignment=False):
    # Raw encoding; 22 reached instructions; numeric/table20..36, data64..68.
    body = bytearray(struct.pack('<10H', 0xB510, 0x4A04, 0x2801, 0xD819,
        0x0080, 0x4903, 0x1840, 0x6800, 0x4687, 0))
    switches = {24: 28, 28: 36, 32: 42}
    body.extend(struct.pack('<IIII', 0x1234, BASE+28, BASE+36, BASE+42))
    body.extend(struct.pack('<7H', 0x4806, 0x2400, 0xE000, 0x2401, 0x3401, 0x2C03, 0xD3FC))
    displacement = CALLEE - (BASE+54)
    body.extend(struct.pack('<HH5HI', 0xF000 | ((displacement >> 12) & 0x7ff),
        0xF800 | ((displacement >> 1) & 0x7ff), 0xBC10, 0xBC02, 0x4708, 0x2000, 0xE7FA, point))
    assert len(body) == 68
    if half: struct.pack_into('<H', body, *half)
    if word:
        struct.pack_into('<I', body, *word)
        if word[0] in switches: switches[word[0]] = word[1]-BASE
    size, data_site = 68, 64
    if alignment:
        struct.pack_into('<H', body, 6, 0xD816)  # Default enters restoring pop.
        struct.pack_into('<H', body, 36, 0x4805)  # Object pool is now at60.
        body[54:] = struct.pack('<3HI4H', 0xBC10, 0xE002, 0, point,
                               0x0000, 0xBC02, 0x4708, 0x46C0)
        size, data_site = 70, 60
    rows = [dict(rom=hex(BASE), end=hex(BASE+size), mode='thumb', instrs=count),
            dict(rom=hex(CALLEE), end=hex(CALLEE+2), mode='thumb', instrs=1)]
    original = relocatable((body, {'call': 50}, switches, {data_site: ('g_point', point)},
        {'calls': [[50, 'func_08001000']]}, rows))
    original = original.replace(b'func_08000000', b'func_08000100')
    original = symbol_change(original, 'func_08000100', 'size', size)
    image = match.elf_image(original)
    linked = bytearray(original); headers = struct.unpack_from('<I', original, 32)[0]
    struct.pack_into('<H', linked, 16, 2)
    section = image['sections'][image['text_index']]
    linked[section[4]:section[4]+section[5]] = body
    struct.pack_into('<I', linked, headers+40*image['text_index']+12, BASE)
    for number in image['relocations']:
        linked[headers+40*number:headers+40*(number+1)] = bytes(40)
    for section_no, symbols in image['symbol_tables'].items():
        section = image['sections'][section_no]
        for number, symbol in enumerate(symbols):
            offset = section[4]+16*number
            if symbol['name'] == 'func_08000100': struct.pack_into('<I', linked, offset+4, BASE | 1)
            elif symbol['type'] == 3 and symbol['section'] == image['text_index']:
                struct.pack_into('<I', linked, offset+4, BASE)
            elif symbol['name'] in ('func_08001000', 'g_point'):
                obj = symbol['name'] == 'g_point'
                struct.pack_into('<I', linked, offset+4, point if obj else CALLEE | 1)
                linked[offset+12] = 0x11 if obj else 0x12
                struct.pack_into('<H', linked, offset+14, 0xfff1)
    rom = bytes(0x100) + bytes(body[:size]).ljust(CALLEE-BASE, b'\0') + b'\x70\x47'
    index = ''.join(f'{int(r["rom"],16):08X} {int(r["end"],16):08X} '
        f'{int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n' for r in rows).encode()
    bindings = dict(calls=[[50, 'func_08001000']], data=[[data_site, 'g_point', 0]],
        functions=[], switches=[list(row) for row in sorted(switches.items())])
    return [original, bytes(linked), BASE, rom, json.dumps(rows).encode(), index, bindings]


def text_change(raw, site, encoded):
    image = match.elf_image(raw); offset = image['sections'][image['text_index']][4]+site
    result = bytearray(raw); result[offset:offset+len(encoded)] = encoded
    return bytes(result)


class NumericSwitchSourceTests(unittest.TestCase):
    def setUp(self):
        env = patch.object(native, 'environment_fingerprint', return_value={'synthetic': True})
        env.start(); self.addCleanup(env.stop)

    def verify(self, values=None, **kwargs):
        return native.verify_original(*(fixture() if values is None else values),
            objects=kwargs.pop('objects', OBJECTS), **kwargs)

    def test_a_rom_mirror_of_a_function_entry_is_a_function_address(self):
        # 0x0A000000-0x0DFFFFFF maps the same ROM as 0x08000000 (#377).
        from test_rom_mirror_literals import extra_reached_word
        for value in ((CALLEE | 1) + 0x02000000, CALLEE + 0x04000000):
            with self.subTest(value=hex(value)), extra_reached_word(value), \
                    self.assertRaisesRegex(ValueError, 'cannot materialize runtime or function addresses'):
                self.verify()
        # An SRAM word is a number, and so needs the u16 scalar category.
        with extra_reached_word((CALLEE | 1) + 0x06000000), \
                self.assertRaisesRegex(ValueError, 'bounded u16 category'):
            self.verify()

    def test_loop_and_saved_register_only_frame(self):
        result, count = self.verify(); self.assertEqual(count, 22)
        proof = result['prerequisite']; self.assertEqual(proof['stack_adjustments'], [])
        self.assertEqual(proof['numeric_word']['value'], 0x1234)
        self.assertFalse(proof['termination_claim']); self.assertFalse(proof['memory_safety_claim'])
        self.assertEqual(proof['numeric_input_preconditions'], [])

    def test_old_default_and_acyclic_numeric_policy_stay_closed(self):
        v = fixture(); data = v[3][0x100:0x144]
        # Without the interposed-pool rule the default owner refinement stops at the dispatch; with it,
        # the table is placed behind its pool and marked as that rule's (interposed_pool_switch).
        import interposed_pool_switch as pool
        from unittest import mock
        with mock.patch.object(pool.POLICY, 'enabled', False):
            self.assertFalse(owner.refine(data, BASE, v[4])['cfg_closed'])
        placed = owner.refine(data, BASE, v[4])['word_switches']
        self.assertTrue(placed and all(pool.marked(switch) for switch in placed))
        with self.assertRaisesRegex(ValueError, 'excludes local CFG cycles'):
            inventory.verify(data, BASE, *v[3:6], {BASE+50: CALLEE},
                {BASE+50: 'func_08001000'}, selector=inventory.SELECTOR)

    def test_guard_bypass_rejected(self):
        with self.assertRaises(ValueError): self.verify(fixture(half=(40, 0xE7EF)))
    def test_signed_guard_rejected(self):
        with self.assertRaises(ValueError): self.verify(fixture(half=(6, 0xDC19)))
    def test_table_cannot_enter_pool(self):
        with self.assertRaises(ValueError): self.verify(fixture(word=(28, BASE+20)))
    def test_table_cannot_leave_function(self):
        with self.assertRaises(ValueError): self.verify(fixture(word=(28, CALLEE)))
    def test_wide_interposed_numeric_rejected(self):
        with self.assertRaises(ValueError): self.verify(fixture(word=(20, 0x10000)))
    def test_unread_interposed_numeric_rejected(self):
        with self.assertRaises(ValueError): self.verify(fixture(half=(2, 0x2200)))
    def test_stack_address_materialization_rejected(self):
        with self.assertRaises(ValueError): self.verify(fixture(half=(38, 0x4668)))
    def test_saved_slot_write_rejected(self):
        with self.assertRaises(ValueError): self.verify(fixture(half=(38, 0x9000)))
    def test_incoming_stack_read_rejected(self):
        with self.assertRaises(ValueError): self.verify(fixture(half=(38, 0x9802)))
    def test_nonrestoring_saved_register_rejected(self):
        with self.assertRaises(ValueError): self.verify(fixture(half=(54, 0xBC08)))
    def test_nonreturning_region_rejected(self):
        with self.assertRaises(ValueError): self.verify(fixture(half=(40, 0xE7FE)))
    def test_exact_instruction_count_required(self):
        with self.assertRaisesRegex(ValueError, 'instruction counts'): self.verify(fixture(count=23))
    def test_named_object_cannot_be_function_identity(self):
        with self.assertRaises(ValueError):
            self.verify(fixture(point=CALLEE), objects=json.dumps({'g_point': f'0x{CALLEE:08X}'}).encode())
    def test_named_object_type_required(self):
        v = fixture(); v[1] = symbol_change(v[1], 'g_point', 'type', 2)
        with self.assertRaisesRegex(ValueError, 'typed absolute'): self.verify(v)
    def test_zero_sized_undefined_symbols_required(self):
        v = fixture(); v[0] = symbol_change(v[0], 'g_point', 'size', 4)
        with self.assertRaisesRegex(ValueError, 'zero size'): self.verify(v)
    def test_object_zero_addend_required(self):
        v = fixture(); v[0] = text_change(v[0], 64, struct.pack('<I', 4))
        with self.assertRaisesRegex(ValueError, 'zero-addend'): self.verify(v)
    def test_original_local_table_relocation_identity_required(self):
        v = fixture(); v[0] = text_change(v[0], 28, struct.pack('<I', 42))
        with self.assertRaises(ValueError): self.verify(v)
    def test_unrelocated_linker_mutation_rejected(self):
        v = fixture(); v[1] = text_change(v[1], 38, b'\x01\x24')
        with self.assertRaisesRegex(ValueError, 'outside original relocation'): self.verify(v)
    def test_full_ROM_and_extent_required(self):
        v = fixture(); v[3] = v[3][:0x100]+b'\0\0'+v[3][0x102:]
        with self.assertRaises(ValueError): self.verify(v)
    def test_source_only_route_rejected(self):
        v = fixture()
        with self.assertRaises(ValueError):
            owner.verify(v[3][0x100:0x144], BASE, *v[3:6], OBJECTS, bindings=v[6], selector=native.SELECTOR)
    def test_report_selection_and_original_fingerprint(self):
        report = f'* verification: `{native.SCHEMA}`\n'
        self.assertTrue(owner.selected(report)); self.assertEqual(owner.selector_for_report(report), native.SELECTOR)
        with self.assertRaises(ValueError):
            owner.fingerprint(BASE, b'', {'profile': native.SCHEMA}, '', b'', b'', OBJECTS, b'')
        with self.assertRaises(ValueError): owner.selected(report+f'* verification: `{owner.SCHEMA}`\n')
    def test_manifest_mutation_rejected(self):
        with self.assertRaisesRegex(ValueError, 'manifest differs'): self.verify(manifest={'profile': native.SCHEMA})

    def test_canonical_external_alignment(self):
        result, count = self.verify(fixture(alignment=True))
        self.assertEqual(count, 22)
        self.assertEqual(result['prerequisite']['end'], BASE+70)

    def test_noncanonical_external_padding_rejected(self):
        v=fixture(alignment=True)
        v[0]=text_change(v[0],70,b'\x00\x00')
        with self.assertRaisesRegex(ValueError,'noncanonical terminal alignment'): self.verify(v)

    def test_changed_linked_alignment_rejected(self):
        v=fixture(alignment=True)
        v[1]=text_change(v[1],70,b'\x00\x00')
        with self.assertRaisesRegex(ValueError,'noncanonical terminal alignment'): self.verify(v)

    def test_padding_cannot_be_extended_FUNC(self):
        v=fixture(alignment=True)
        v[0]=symbol_change(v[0],'func_08000100','size',72)
        with self.assertRaisesRegex(ValueError,'complete owner'): self.verify(v)

    def test_call_identity_type_and_mixed_policy_rejected(self):
        v=fixture(alignment=True)
        v[1]=symbol_change(v[1],'func_08001000','type',1)
        with self.assertRaisesRegex(ValueError,'typed absolute'): self.verify(v)
        import argparse
        with self.assertRaisesRegex(ValueError,'excludes'):
            owner.issue(Path('.'),BASE,argparse.Namespace(owner_runtime_profile=native.SELECTOR,
                switch_data_profile='unrelated', mode='thumb', control_flow_profile='ordinary',
                software_double_profile=None, software_double_remainder_profile=None,
                function_address_profile=None, switch_profile=None, label=None,
                wsl='Ubuntu', wsl_path=match.DEFAULT_WSL_PATH))


if __name__ == '__main__': unittest.main()
