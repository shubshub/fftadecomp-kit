"""New combined tests for typed switch words and owned scalar outgoing frames."""
import copy
import json
import os
from pathlib import Path
import struct
import sys
import unittest
from unittest.mock import patch
import tempfile
import argparse

ROOT = Path(__file__).resolve().parents[1]
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT / 'tools'))
if os.environ.get('FFTA_TEST_TOOLS_FALLBACK'):
    sys.path.append(os.environ['FFTA_TEST_TOOLS_FALLBACK'])
import match
import match_evidence as evidence
import typed_switch_outgoing_frame as frame

BASE = 0x08000000
CALLEE = BASE + 0x1000
OBJECTS = {'g_left': '0x02001000', 'g_right': '0x02002000', 'g_third': '0x02003000'}
POLICY = 'complete-reachable-object-words-v1'


def fixture(before=2, *, call=False, prefix=False):
    """An ordinary bounded switch reads named globals, with an optional fixed frame/BL."""
    body, labels, fixups = bytearray(), {}, []
    def half(value): body.extend(struct.pack('<H', value))
    def label(name): labels[name] = len(body)
    def emit(kind, name, reg=0):
        fixups.append((len(body), kind, name, reg))
        body.extend(bytes(4 if kind == 'word' else 2))
    if call:
        half(0xB510)  # push {r4,lr}
        half(0xB086)  # sub sp,#24
    if prefix:
        half(0x2100)
    for index in range(before):
        emit('ldr', f'object{index}', index + 2)
    if call:
        half(0x9300)  # str r3,[sp]
        half(0x2100)
        for slot in range(1, 6): half(0x9100 | slot)
    label('comparison'); half(0x2801)
    label('guard'); emit('bhi', 'default')
    label('dispatch'); half(0x0080)
    emit('ldr', 'pointer', 1)
    half(0x1840); half(0x6800); half(0x4687)
    while (BASE + len(body)) % 4: half(0)
    for index in range(before):
        label(f'object{index}')
        body.extend(struct.pack('<I', int(list(OBJECTS.values())[index], 16)))
    label('pointer'); emit('word', 'table')
    label('table'); emit('word', 'case0'); emit('word', 'case1')
    label('case0'); half(0x7810 if before else 0x2001)
    label('case0_skip'); emit('b', 'done')
    label('case1'); half(0x8818 if before > 1 else 0x2002)
    emit('b', 'done')
    label('default'); half(0x2000)
    label('done')
    calls = []
    if call:
        label('call')
        calls.append([len(body), 'func_08001000'])
        displacement = CALLEE - (BASE + len(body) + 4)
        half(0xF000 | ((displacement >> 12) & 0x7FF))
        half(0xF800 | ((displacement >> 1) & 0x7FF))
        half(0xB006); half(0xBC10); half(0xBC02); half(0x4708)
    else:
        half(0x4770)
    for at, kind, name, reg in fixups:
        target = labels[name]
        if kind == 'word': struct.pack_into('<I', body, at, BASE + target)
        elif kind == 'ldr':
            displacement = target - ((at + 4) & ~3)
            assert 0 <= displacement <= 1020 and displacement % 4 == 0
            struct.pack_into('<H', body, at, 0x4800 | reg << 8 | displacement // 4)
        else:
            displacement = (target - at - 4) // 2
            struct.pack_into('<H', body, at, (0xD800 | displacement & 255) if kind == 'bhi'
                             else (0xE000 | displacement & 0x7FF))
    switches = {labels['pointer']: labels['table'], labels['table']: labels['case0'],
                labels['table'] + 4: labels['case1']}
    data = {labels[f'object{i}']: (list(OBJECTS)[i], int(list(OBJECTS.values())[i], 16))
            for i in range(before)}
    descriptor = {name: labels[name] for name in ('comparison', 'guard', 'dispatch', 'default', 'table')}
    descriptor.update(literal=labels['pointer'], bound=1,
                      relocations=[list(row) for row in switches.items()])
    manifest = {'calls': calls, 'switch': descriptor}
    if data:
        manifest['data'] = [[at, name, 0] for at, (name, _) in data.items()]
        if len(data) > 1: manifest['data_policy'] = POLICY
    mapping = [{'rom': f'0x{BASE:08X}', 'end': f'0x{BASE + len(body):08X}', 'mode': 'thumb'},
               {'rom': f'0x{CALLEE:08X}', 'end': f'0x{CALLEE + 2:08X}', 'mode': 'thumb'}]
    return body, labels, switches, data, manifest, mapping


def relocatable(f):
    """Emit real minimal ARM ET_REL bytes; no compiler or assembler invocation."""
    body, labels, switches, data, manifest, _ = f
    text = bytearray(body)
    for at, addend in switches.items(): struct.pack_into('<I', text, at, addend)
    for at in data: struct.pack_into('<I', text, at, 0)
    if manifest['calls']: struct.pack_into('<HH', text, labels['call'], 0xF7FF, 0xFFFE)
    strings = bytearray(b'\0')
    def string(value):
        offset = len(strings); strings.extend(value.encode() + b'\0'); return offset
    symbols = [bytes(16), struct.pack('<IIIBBH', 0, 0, 0, 3, 0, 1),
               struct.pack('<IIIBBH', string('func_08000000'), 1, len(text), 0x12, 0, 1)]
    numbers = {}
    for name, _ in data.values():
        numbers[name] = len(symbols)
        symbols.append(struct.pack('<IIIBBH', string(name), 0, 0, 0x11, 0, 0))
    if manifest['calls']:
        numbers['func_08001000'] = len(symbols)
        symbols.append(struct.pack('<IIIBBH', string('func_08001000'), 0, 0, 0x12, 0, 0))
    rows = [(at, 1 << 8 | 2) for at in switches]
    rows += [(at, numbers[name] << 8 | 2) for at, (name, _) in data.items()]
    rows += [(at, numbers[name] << 8 | 10) for at, name in manifest['calls']]
    relocations = b''.join(struct.pack('<II', *row) for row in sorted(rows))
    names = b'\0.text\0.symtab\0.strtab\0.rel.text\0.shstrtab\0'
    payloads = [b'', bytes(text), b''.join(symbols), bytes(strings), relocations, names]
    headers = [(0,) * 10]
    raw = bytearray(bytes(52))
    for index, payload in enumerate(payloads[1:], 1):
        while len(raw) % 4: raw.append(0)
        offset = len(raw); raw.extend(payload)
        name = [None, '.text', '.symtab', '.strtab', '.rel.text', '.shstrtab'][index]
        kind = [None, 1, 2, 3, 9, 3][index]
        headers.append((names.index(name.encode()), kind, 6 if index == 1 else 0,
                        0, offset, len(payload), 3 if index == 2 else 2 if index == 4 else 0,
                        2 if index == 2 else 1 if index == 4 else 0,
                        4 if index in (1, 2, 4) else 1, 16 if index == 2 else 8 if index == 4 else 0))
    while len(raw) % 4: raw.append(0)
    section_offset = len(raw)
    raw.extend(b''.join(struct.pack('<10I', *row) for row in headers))
    raw[:16] = b'\x7fELF\x01\x01\x01' + bytes(9)
    struct.pack_into('<HHIIIIIHHHHHH', raw, 16, 1, 40, 1, 0, 0, section_offset, 0,
                     52, 0, 0, 40, len(headers), 5)
    return bytes(raw)


def produce(f, *, objects=None, image=None, allow_data=True):
    body, _, _, _, _, mapping = f
    switches = {}
    calls, targets, data = match.call_bindings(
        match.elf_image(relocatable(f)) if image is None else image,
        'func_08000000', BASE, json.dumps(mapping).encode(), 8192,
        data_mapping=json.dumps(OBJECTS if objects is None else objects).encode(),
        switch_relocations=switches, allow_switch_data=allow_data)
    return calls, targets, data, switches


def verify(f, *, manifest=None, objects=None, mapping=None, rom=None):
    body, _, _, _, expected, entries = f
    return match.verify_switches(bytes(body), BASE,
        bytes(body).ljust(8192, b'\0') if rom is None else rom,
        json.dumps(entries if mapping is None else mapping).encode(),
        expected if manifest is None else manifest,
        data_mapping=json.dumps(OBJECTS if objects is None else objects).encode() if 'data' in
        (expected if manifest is None else manifest) else None)


def combined():
    f = fixture(call=True, prefix=True)
    f[4]['frame_policy'] = frame.SELECTOR
    return f


def half_at(f, at, value):
    struct.pack_into('<H', f[0], at, value)


class TypedSwitchOutgoingFrameTests(unittest.TestCase):
    def test_real_ELF_producer_and_combined_complete_CFG(self):
        f = combined()
        calls, targets, objects, switches = produce(f)
        self.assertEqual(objects, f[3]); self.assertEqual(switches, f[2])
        self.assertEqual(calls, {BASE + f[1]['call']: CALLEE})
        instructions, summary = verify(f)
        self.assertEqual(summary, evidence.CALL_SUMMARY)
        self.assertTrue(any(i.mnemonic == 'bl' for i in instructions))
        self.assertEqual(frame.fingerprint(BASE, bytes(f[0]), f[4]),
                         frame.fingerprint(BASE, bytes(f[0]), copy.deepcopy(f[4])))
        bad = copy.deepcopy(f[4]); bad['frame_policy'] = 'other'
        self.assertNotEqual(frame.fingerprint(BASE, bytes(f[0]), f[4]),
                            frame.fingerprint(BASE, bytes(f[0]), bad))

    def test_default_explicit_selector_and_cross_policy_rejections(self):
        f = combined(); manifest = copy.deepcopy(f[4]); manifest.pop('frame_policy')
        with self.assertRaisesRegex(ValueError, 'excludes fixed frames'):
            verify(f, manifest=manifest)
        for token in (True, 1, '', 'two-constants-frame-v1', None):
            manifest = copy.deepcopy(f[4]); manifest['frame_policy'] = token
            with self.subTest(token=token), self.assertRaises(ValueError):
                verify(f, manifest=manifest)
        for key, value in [('allow_switch_constants', True),
                           ('allow_switch_scalar_frame', True),
                           ('function_thunk_context', {}), ('acyclic_state_budget', 10)]:
            with self.subTest(key=key), self.assertRaises(ValueError):
                match.verify_leaf_instructions(bytes(f[0]), BASE, True,
                    {BASE + f[1]['call']: CALLEE}, switch_relocations=f[2],
                    switch_data_relocations=f[3], typed_switch_outgoing_frame=frame.SELECTOR,
                    **{key: value})
        args = argparse.Namespace(switch_data_profile=frame.SELECTOR, mode='thumb',
            control_flow_profile='ordinary', signed_quotient_profile=None,
            signed_runtime_profile=None, addressed_signed_runtime_profile=None,
            unsigned_runtime_profile=None, software_double_profile=None,
            software_double_remainder_profile=None, function_address_profile=None,
            switch_profile=None, owner_runtime_profile=None, cc=match.DEFAULT_CC,
            cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY,
            linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        match.switch_u16_scalar_configuration(args)
        args.flags += ' -O1'
        with self.assertRaises(ValueError): match.switch_u16_scalar_configuration(args)

    def test_frame_bounds_balance_saved_words_and_incoming_reads_reject(self):
        # First store follows push, allocation, prefix and two actual object loads.
        f = combined(); first_store = 10
        self.assertEqual(struct.unpack_from('<H', f[0], first_store)[0], 0x9300)
        changes = [(2, 0xB085), (first_store, 0x9306), (first_store, 0x9B00),
                   (first_store, 0x9B08),
                   (f[1]['call'] + 4, 0xB005)]
        for at, value in changes:
            g = copy.deepcopy(f); half_at(g, at, value)
            with self.subTest(at=at, value=value), self.assertRaises(ValueError): verify(g)

    def test_all_path_initialization_and_no_stack_address_or_callback(self):
        f = combined()
        # Remove each outgoing store independently, retaining all real typed loads.
        for at in [10, 14, 16, 18, 20, 22]:
            g = copy.deepcopy(f); half_at(g, at, 0x1C09)
            with self.subTest(store=at), self.assertRaisesRegex(ValueError, 'initialized'):
                verify(g)
        g = copy.deepcopy(f)
        # Conditional edge skips the first outgoing slot on one reached path.
        half_at(g, 10, 0xD000)
        with self.assertRaises(ValueError): verify(g)
        for value in (0x4669, 0xA900, 0x4788, 0xB410):
            g = copy.deepcopy(f); half_at(g, 12, value)
            with self.subTest(operation=value), self.assertRaises(ValueError): verify(g)
        # Canonical runtime target cannot be re-labelled an ordinary call.
        g = copy.deepcopy(f); target = match.UDIVSI3_ADDRESS
        at = f[1]['call']; displacement = target - (BASE + at + 4)
        struct.pack_into('<HH', g[0], at, 0xF000 | (displacement >> 12 & 0x7FF),
                         0xF800 | (displacement >> 1 & 0x7FF))
        g[4]['calls'][0][1] = f'func_{target:08X}'
        g[5][1] = dict(rom=f'0x{target:08X}', end=f'0x{target + 2:08X}', mode='thumb')
        with self.assertRaises(ValueError): verify(g)

    def test_typed_table_whole_ELF_and_mapping_boundaries(self):
        f = combined()
        for before in (0, 1, 3):
            g = fixture(before, call=True, prefix=True); g[4]['frame_policy'] = frame.SELECTOR
            with self.subTest(objects=before), self.assertRaises(ValueError): verify(g)
        for field in ('comparison', 'dispatch', 'bound'):
            g = copy.deepcopy(f); g[4]['switch'][field] += 2
            with self.subTest(field=field), self.assertRaises(ValueError): verify(g)
        image = match.elf_image(relocatable(f)); image['type'] = 2
        with self.assertRaises(ValueError): produce(f, image=image)
        objects = dict(OBJECTS); objects['g_left'] = '0x02001004'
        with self.assertRaises(ValueError): verify(f, objects=objects)
        g = copy.deepcopy(f); g[4]['data'][0][0] = f[1]['pointer']
        with self.assertRaises(ValueError): verify(g)
        mapping = copy.deepcopy(f[5]); mapping[0]['end'] = f'0x{BASE + len(f[0]) - 2:08X}'
        with self.assertRaises(ValueError): verify(f, mapping=mapping)

    def test_native_report_source_binding_and_frame_marker_are_fail_closed(self):
        f = combined(); body = bytes(f[0]); mapping = json.dumps(f[5]).encode()
        objects = json.dumps(OBJECTS).encode(); source = 'a' * 64
        def lines(manifest=None, schema=None):
            manifest = f[4] if manifest is None else manifest
            return [f'* verification: `{schema or frame.SCHEMA}`',
                f'* source SHA-256: `{source}`',
                f'* mapping SHA-256: `{evidence.mapping_fingerprint(mapping)}`',
                f'* data symbols SHA-256: `{evidence.mapping_fingerprint(objects)}`',
                f'* switches: {frame.SUMMARY}', '* source plausibility: plausible',
                '* relocations: none',
                '* verified extent: complete ELF function symbol, including literal pools',
                f'* stack frame: {evidence.STACK_SUMMARY}',
                f'* compiled : `{body.hex()}`',
                f'* switch manifest: `{evidence.switch_manifest(manifest)}`',
                f'* switch proof SHA-256: `{frame.fingerprint(BASE, body, manifest)}`',
                f'* control flow: {evidence.CALL_SUMMARY}',
                f'* ROM bytes: `{body.hex()}` ({len(body)} bytes)',
                f'**MATCH - byte identical** - {len(body)}/{len(body)} bytes']
        with tempfile.TemporaryDirectory() as directory:
            rom = Path(directory) / 'synthetic.bin'; rom.write_bytes(body.ljust(8192, b'\0'))
            with patch.object(evidence, 'mapping_snapshot', return_value=mapping), \
                    patch.object(evidence, 'data_snapshot', return_value=objects), \
                    patch.object(evidence, 'source_fingerprint', return_value=source) as fingerprint, \
                    patch.object(evidence, 'report_rom_path', return_value=str(rom)):
                self.assertTrue(evidence.switch_report_matches(lines(), Path(directory), BASE, data_profile=True))
                bad = lines(); bad.remove(f'* stack frame: {evidence.STACK_SUMMARY}')
                self.assertFalse(evidence.switch_report_matches(bad, directory, BASE, data_profile=True))
                bad = lines(); bad.append('* buffer calls: unknown')
                self.assertFalse(evidence.switch_report_matches(bad, directory, BASE, data_profile=True))
                bad = copy.deepcopy(f[4]); bad.pop('frame_policy')
                self.assertFalse(evidence.switch_report_matches(lines(bad), directory, BASE, data_profile=True))
                self.assertFalse(evidence.switch_report_matches(lines(schema=evidence.SWITCH_MULTIPLE_DATA_SCHEMA),
                                                                directory, BASE, data_profile=True))
                fingerprint.return_value = 'b' * 64
                self.assertFalse(evidence.switch_report_matches(lines(), directory, BASE, data_profile=True))


if __name__ == '__main__':
    unittest.main()
