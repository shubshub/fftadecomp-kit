"""Compiler-free original ELF fixtures for isolated complete multi-switch proof."""
import copy
import json
from pathlib import Path
import struct
import sys
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import multiple_switch_owner_prerequisite as policy
from test_typed_switch_outgoing_frame import relocatable as _relocatable

BASE, CALLEE = 0x08000100, 0x08001000


def fixture(count=2, *, call=True, scalar=True, highregs=False, local=False, table_counts=None, shared_backward=False):
    body, labels, fixups, switches = bytearray(), {}, [], {}
    instructions = 0
    def half(value):
        nonlocal instructions
        instructions += 1
        body.extend(struct.pack('<H', value))
    def label(name): labels[name] = len(body)
    def emit(kind, name, reg=0):
        nonlocal instructions
        fixups.append((len(body), kind, name, reg))
        body.extend(bytes(4 if kind == 'word' else 2))
        if kind != 'word': instructions += 1
    if highregs:
        for value in (0xB5F0, 0x4647, 0xB480, 0x4680): half(value)
    else:
        half(0xB500)
    if local: half(0xB081); half(0x9000)
    for n in range(count):
        entries = table_counts[n] if table_counts is not None else (3 if shared_backward and n else 2)
        label(f'cmp{n}'); half(0x2800 | (entries-1))
        label(f'guard{n}'); emit('bhi', f'default{n}')
        label(f'dispatch{n}'); half(0x0080)
        emit('ldr', f'pointer{n}', 1)
        half(0x1840); half(0x6800); half(0x4687)
        while len(body) % 4: body.extend(bytes(2))
        label(f'pointer{n}'); emit('word', f'table{n}')
        names = [f'case{n}{chr(97+i)}' for i in range(entries)]
        if shared_backward and n:
            names[-1] = 'case0a'
        label(f'table{n}')
        for name in names: emit('word', name)
        for number, name in enumerate(names):
            if shared_backward and n and name == 'case0a':
                continue
            label(name); half(0x2000 | number)
            if number == 0: label(f'branch{n}a')
            emit('b', 'epilogue' if shared_backward and n == 0 and number == 0 else f'join{n}')
        label(f'default{n}'); half(0x2002)
        label(f'join{n}')
    calls = []
    if call:
        label('call'); at = len(body); displacement = CALLEE-(BASE+at+4)
        body.extend(struct.pack('<HH', 0xF000 | ((displacement >> 12) & 0x7ff),
                                0xF800 | ((displacement >> 1) & 0x7ff)))
        instructions += 1; calls.append([at, 'func_08001000'])
    if scalar: emit('ldr', 'scalar', 0)
    if local: half(0xB001)
    label('epilogue')
    if highregs:
        for value in (0xBC08, 0x4698, 0xBCF0): half(value)
    half(0xBC02); half(0x4708)
    if scalar:
        while len(body) % 4: body.extend(bytes(2))
        label('scalar'); body.extend(struct.pack('<I', 0x15b))
    for at, kind, name, reg in fixups:
        to = labels[name]
        if kind == 'word':
            switches[at] = to; struct.pack_into('<I', body, at, BASE+to)
        elif kind == 'ldr':
            displacement = to-((at+4) & ~3)
            assert displacement >= 0 and displacement % 4 == 0
            struct.pack_into('<H', body, at, 0x4800 | reg << 8 | displacement//4)
        else:
            displacement = (to-at-4)//2
            struct.pack_into('<H', body, at, (0xD800 | displacement & 255)
                             if kind == 'bhi' else (0xE000 | displacement & 0x7ff))
    entries = [dict(rom=f'0x{BASE:08X}', end=f'0x{BASE+len(body):08X}', mode='thumb', instrs=instructions),
               dict(rom=f'0x{CALLEE:08X}', end=f'0x{CALLEE+2:08X}', mode='thumb', instrs=1)]
    return body, labels, switches, {}, dict(calls=calls), entries


def relocatable(f):
    return _relocatable(f).replace(b'func_08000000', b'func_08000100')


def executable(raw, f):
    output = bytearray(raw)
    image = match.elf_image(raw)
    headers = struct.unpack_from('<I', raw, 32)[0]
    struct.pack_into('<H', output, 16, 2)
    text = image['sections'][image['text_index']]
    output[text[4]:text[4]+text[5]] = f[0]
    struct.pack_into('<I', output, headers+40*image['text_index']+12, BASE)
    for section_no in image['relocations']:
        output[headers+40*section_no:headers+40*(section_no+1)] = bytes(40)
    for section_no, symbols in image['symbol_tables'].items():
        section = image['sections'][section_no]
        for number, symbol in enumerate(symbols):
            at = section[4]+16*number
            if symbol['name'] == 'func_08000100':
                struct.pack_into('<I', output, at+4, BASE | 1)
            elif symbol['type'] == 3 and symbol['section'] == image['text_index']:
                struct.pack_into('<I', output, at+4, BASE)
            elif symbol['name'] == 'func_08001000':
                struct.pack_into('<I', output, at+4, CALLEE | 1)
                output[at+12] = 0x12
                struct.pack_into('<H', output, at+14, 0xfff1)
    return bytes(output)


def inputs(f):
    raw = relocatable(f)
    linked = executable(raw, f)
    rom = (bytes(BASE-match.ROM_BASE)+bytes(f[0])).ljust(CALLEE-match.ROM_BASE, b'\0')+bytes.fromhex('7047')
    mapping = json.dumps(f[5]).encode()
    index = ''.join(f"{int(row['rom'],16):08X} {int(row['end'],16):08X} "
                    f"{int(row['end'],16)-int(row['rom'],16)} {row['instrs']} return\n"
                    for row in f[5]).encode()
    return raw, linked, BASE, rom, mapping, index


def verify(f=None, **kwargs):
    return policy.verify(*inputs(f if f is not None else fixture()), selector=policy.SELECTOR, **kwargs)


class MultipleSwitchTests(unittest.TestCase):
    def test_two_real_ELF_tables_and_reached_u16_literal(self):
        f = fixture()
        result = verify(f)
        self.assertEqual(len(result['switches']), 2)
        self.assertEqual(len(result['local_relocations']), 6)
        self.assertEqual(result['scalar_words'][0]['value'], 0x15b)
        self.assertEqual(result['instructions'], f[5][0]['instrs'])
        for key in ('source_or_ELF_admission', 'native_admission', 'memory_safety_claim',
                    'ordinary_callee_effects_proved', 'termination_claim'):
            self.assertFalse(result[key])

    def test_three_tables_leaf_and_scalar_private_frame(self):
        self.assertEqual(len(verify(fixture(3, call=False, scalar=False))['switches']), 3)
        self.assertTrue(verify(fixture(local=True))['frame'])

    def test_nonleaf_high_register_save_restore(self):
        self.assertTrue(verify(fixture(highregs=True))['frame'])

    def test_single_switch_default_stays_strict(self):
        f = fixture()
        with self.assertRaises(ValueError):
            match.call_bindings(match.elf_image(relocatable(f)), 'func_08000100', BASE,
                                json.dumps(f[5]).encode(), 8192, switch_relocations={})
        with self.assertRaisesRegex(ValueError, 'bounded immutable|at least two'):
            verify(fixture(1))

    def test_unknown_selector_and_mixed_context_refuse(self):
        f = fixture(); raw = match.elf_image(relocatable(f)); mapping = json.dumps(f[5]).encode()
        for kwargs in (dict(multiple_switch_profile=True),
                       dict(multiple_switch_profile=policy.SELECTOR, allow_switch_data=True),
                       dict(multiple_switch_profile=policy.SELECTOR, data_mapping=b'{}'),
                       dict(multiple_switch_profile=policy.SELECTOR, function_relocations={})):
            with self.subTest(kwargs=kwargs), self.assertRaisesRegex(ValueError, 'isolated explicit'):
                match.call_bindings(raw, 'func_08000100', BASE, mapping, 8192,
                                    switch_relocations={}, **kwargs)

    def test_missing_local_relocation_cannot_be_inferred_from_linked_bytes(self):
        f = fixture(); del f[2][f[1]['table1']+4]
        with self.assertRaises(ValueError): verify(f)

    def test_local_section_symbol_must_remain_unique_and_zero(self):
        f = fixture(); image = match.elf_image(relocatable(f))
        next(s for s in image['symbols'] if s['type'] == 3)['value'] = 4
        with self.assertRaisesRegex(ValueError, 'zero-valued local'):
            match.call_bindings(image, 'func_08000100', BASE, json.dumps(f[5]).encode(), 8192,
                                switch_relocations={}, multiple_switch_profile=policy.SELECTOR)

    def test_ordinary_call_addend_cannot_change_identity(self):
        args = list(inputs(fixture())); raw = bytearray(args[0]); image = match.elf_image(raw)
        offset = image['sections'][image['text_index']][4]+fixture()[1]['call']
        raw[offset:offset+4] = bytes.fromhex('00f000f8'); args[0] = bytes(raw)
        with self.assertRaisesRegex(ValueError, 'zero-addend'):
            policy.verify(*args, selector=policy.SELECTOR)

    def test_linked_target_type_and_unrelocated_byte_changes_refuse(self):
        args = list(inputs(fixture())); linked = bytearray(args[1]); image = match.elf_image(linked)
        for section_no, symbols in image['symbol_tables'].items():
            for n, s in enumerate(symbols):
                if s['name'] == 'func_08001000':
                    linked[image['sections'][section_no][4]+16*n+12] = 0x11
        args[1] = bytes(linked)
        with self.assertRaisesRegex(ValueError, 'absolute symbol type|unexpected linked function'):
            policy.verify(*args, selector=policy.SELECTOR)
        args = list(inputs(fixture())); linked = bytearray(args[1]); image = match.elf_image(linked)
        linked[image['sections'][image['text_index']][4]] ^= 1; args[1] = bytes(linked)
        with self.assertRaisesRegex(ValueError, 'outside permitted relocations'):
            policy.verify(*args, selector=policy.SELECTOR)

    def test_branch_bypass_of_second_guard_refuses(self):
        f = fixture(); at = f[1]['branch0a']; target = f[1]['dispatch1']
        struct.pack_into('<H', f[0], at, 0xE000 | ((target-at-4)//2 & 0x7ff))
        refinement = policy.owner.refine(bytes(f[0]), BASE, json.dumps(f[5]).encode())
        self.assertTrue(any('guard can be bypassed' in reason for reason in refinement['partial_reasons']))
        with self.assertRaisesRegex(ValueError, 'structural inventory is not closed'):
            verify(f)

    def test_equal_but_wrong_both_index_counts_reject_after_complete_link(self):
        f = fixture(); f[5][0]['instrs'] += 1
        with self.assertRaisesRegex(ValueError, 'dual-index instruction count'):
            verify(f)

    def test_original_and_linked_words_do_not_override_current_ROM(self):
        args = list(inputs(fixture())); rom = bytearray(args[3]); rom[BASE-match.ROM_BASE] ^= 1
        args[3] = bytes(rom)
        with self.assertRaisesRegex(ValueError, 'ROM'):
            policy.verify(*args, selector=policy.SELECTOR)

    def test_closed_body_cannot_cycle_between_two_guards(self):
        f = fixture(); at = f[1]['branch1a']; target = f[1]['cmp0']
        struct.pack_into('<H', f[0], at, 0xE000 | ((target-at-4)//2 & 0x7ff))
        with self.assertRaisesRegex(ValueError, 'CFG cycles'):
            verify(f)

    def test_default_single_switch_layout_still_accepts_its_original_shape(self):
        f = fixture(1)
        descriptor = match.selected_switch_layout(bytes(f[0]), BASE, f[2])
        self.assertEqual(descriptor['bound'], 1)
        self.assertEqual(descriptor['literal'], f[1]['pointer0'])
        with self.assertRaises(ValueError):
            match.selected_switch_layout(bytes(fixture()[0]), BASE, fixture()[2])

    def test_table_target_into_another_table_refuses(self):
        f = fixture(); at = f[1]['table0']; target = f[1]['table1']
        f[2][at] = target; struct.pack_into('<I', f[0], at, BASE+target)
        with self.assertRaises(ValueError): verify(f)

    def test_changed_guard_bound_and_nonzero_alignment_refuse(self):
        f = fixture(); struct.pack_into('<H', f[0], f[1]['cmp1'], 0x2802)
        with self.assertRaises(ValueError): verify(f)
        f = fixture(highregs=True); at = f[1]['pointer0']-2
        self.assertEqual(f[0][at:at+2], bytes(2))
        f[0][at:at+2] = bytes.fromhex('c046')
        with self.assertRaises(ValueError): verify(f)

    def test_extra_literal_cannot_grant_address_memory(self):
        f = fixture(); struct.pack_into('<I', f[0], f[1]['scalar'], 0x02000000)
        with self.assertRaisesRegex(ValueError, 'u16 scalars'):
            verify(f)

    def test_dual_index_count_and_extent_disagreement_refuse(self):
        args = list(inputs(fixture())); rows = json.loads(args[4]); rows[0]['instrs'] += 1
        args[4] = json.dumps(rows).encode()
        with self.assertRaises(ValueError): policy.verify(*args, selector=policy.SELECTOR)
        args = list(inputs(fixture())); args[5] = args[5].replace(b'08000100 ', b'08000102 ', 1)
        with self.assertRaises(ValueError): policy.verify(*args, selector=policy.SELECTOR)

    def test_missing_frame_restore_and_SP_escape_refuse(self):
        f = fixture(highregs=True); struct.pack_into('<H', f[0], f[1]['epilogue']+2, 0x4618)
        with self.assertRaises(ValueError): verify(f)
        f = fixture(); struct.pack_into('<H', f[0], f[1]['case0a'], 0x4668)
        with self.assertRaisesRegex(ValueError, 'stack address materialization'):
            verify(f)

    def test_forged_manifest_cannot_drop_a_table_or_add_native_credit(self):
        result = verify(); forged = copy.deepcopy(result); forged['switches'].pop()
        with self.assertRaisesRegex(ValueError, 'manifest differs'): verify(manifest=forged)
        forged = copy.deepcopy(result); forged['native_admission'] = True
        with self.assertRaisesRegex(ValueError, 'manifest differs'): verify(manifest=forged)

    def test_bounded_table_budget_fails_closed(self):
        with patch.object(policy, 'MAX_SWITCHES', 1), self.assertRaisesRegex(ValueError, 'table budget'):
            verify()

    def test_sixteen_and_nine_case_tables_keep_all_twenty_seven_local_words(self):
        result = verify(fixture(highregs=True, table_counts=(16, 9)))
        self.assertEqual([row['bound'] for row in result['switches']], [15, 8])
        self.assertEqual(len(result['local_relocations']), 27)
        self.assertEqual(result['partition']['literal_and_table_bytes'], 112)

    def test_cross_table_data_target_rejected_by_combined_CFG(self):
        f = fixture(); at = f[1]['table0']; target = f[1]['table1']
        f[2][at] = target; struct.pack_into('<I', f[0], at, BASE+target)
        with self.assertRaisesRegex(ValueError, 'structural inventory|CFG|overlap'):
            verify(f)

    def test_linked_profile_rejects_nonisolated_data_context(self):
        f = fixture(); raw, linked, _, _, mapping, _ = inputs(f)
        switches = {}
        calls, targets, _ = match.call_bindings(match.elf_image(raw), 'func_08000100', BASE,
            mapping, 8192, switch_relocations=switches, multiple_switch_profile=policy.SELECTOR)
        with self.assertRaisesRegex(ValueError, 'isolated explicit'):
            match.linked_function_bytes(match.elf_image(raw), match.elf_image(linked),
                'func_08000100', BASE, calls, targets, data_relocations={},
                switch_relocations=switches, multiple_switch_profile=policy.SELECTOR)


if __name__ == '__main__':
    unittest.main()
