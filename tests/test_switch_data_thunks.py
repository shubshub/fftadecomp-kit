"""Canonical call thunks in switch-data functions (switch-thunks-v1 / switch-thunks-frame-v1)."""
import argparse
import contextlib
import copy
import io
import json
import os
from pathlib import Path
import struct
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT / 'tools'))
if os.environ.get('FFTA_TEST_TOOLS_FALLBACK'):
    sys.path.append(os.environ['FFTA_TEST_TOOLS_FALLBACK'])
import match
import match_evidence as evidence
import report_fixtures
import function_thunk_profile as function_thunk
import switch_data_thunks as thunks
import switch_pool_outgoing_frame as pool_switch_frame
import switch_wide_scalars as wide_scalars

BASE = 0x08000000
CALLEE = BASE + 0x1000
THUNK_R2 = function_thunk.ALIASES['_call_via_r2']
THUNK_R3 = function_thunk.ALIASES['_call_via_r3']
OBJECTS = {'g_left': '0x02001000', 'g_right': '0x02002000'}
POLICY = 'complete-reachable-object-words-v1'
SCALAR_POLICY = 'complete-reachable-u16-scalar-words-v1'
ROM_SIZE = 0x142280
PLAIN, FRAMED = 'switch-thunks-v1', 'switch-thunks-frame-v1'


def assemble(items):
    """Tiny two-pass Thumb assembler for the few encodings these fixtures need."""
    labels, layout, at = {}, [], 0
    for item in items:
        if item[0] == 'label':
            labels[item[1]] = at
            continue
        size = {'bl': 4, 'word': 4, 'address': 4}.get(item[0], 2)
        if item[0] == 'align':
            size = (-(BASE + at)) % 4
        layout.append((at, item))
        at += size
    body = bytearray(at)
    calls = []
    for at, item in layout:
        kind = item[0]
        if kind == 'h':
            struct.pack_into('<H', body, at, item[1])
        elif kind == 'word':
            struct.pack_into('<I', body, at, item[1])
        elif kind == 'address':
            struct.pack_into('<I', body, at, BASE + labels[item[1]])
        elif kind == 'ldr':
            displacement = labels[item[2]] - ((at + 4) & ~3)
            assert 0 <= displacement <= 1020 and displacement % 4 == 0
            struct.pack_into('<H', body, at, 0x4800 | item[1] << 8 | displacement // 4)
        elif kind in ('b', 'bhi'):
            displacement = (labels[item[1]] - at - 4) // 2
            struct.pack_into('<H', body, at, (0xD800 | displacement & 255) if kind == 'bhi'
                             else (0xE000 | displacement & 0x7FF))
        elif kind == 'bl':
            displacement = item[1] - (BASE + at + 4)
            struct.pack_into('<HH', body, at, 0xF000 | (displacement >> 12 & 0x7FF),
                             0xF800 | (displacement >> 1 & 0x7FF))
            calls.append((at, item[1]))
    return body, labels, calls


def switch_items():
    return [('label', 'comparison'), ('h', 0x2801), ('label', 'guard'), ('bhi', 'default'),
            ('label', 'dispatch'), ('h', 0x0080), ('ldr', 1, 'pointer'),
            ('h', 0x1840), ('h', 0x6800), ('h', 0x4687), ('align',),
            ('label', 'pointer'), ('address', 'table'),
            ('label', 'table'), ('address', 'case0'), ('address', 'case1'),
            ('label', 'case0'), ('h', 0x2401), ('b', 'done'),
            ('label', 'case1'), ('h', 0x2402), ('b', 'done'),
            ('label', 'default'), ('h', 0x2400), ('label', 'done')]


def descriptor(labels):
    switches = {labels['pointer']: labels['table'], labels['table']: labels['case0'],
                labels['table'] + 4: labels['case1']}
    result = {name: labels[name] for name in ('comparison', 'guard', 'dispatch', 'default', 'table')}
    result.update(literal=labels['pointer'], bound=1,
                  relocations=[list(row) for row in sorted(switches.items())])
    return result


def rom_image(body):
    rom = bytearray(ROM_SIZE)
    rom[:len(body)] = body
    for target in (THUNK_R2, THUNK_R3):
        register = (target - function_thunk.START) // 4
        struct.pack_into('<HH', rom, target - BASE, 0x4700 | register << 3, 0x46C0)
    return bytes(rom)


def mapping(body):
    return json.dumps([{'rom': f'0x{BASE:08X}', 'end': f'0x{BASE + len(body):08X}', 'mode': 'thumb'},
                       {'rom': f'0x{CALLEE:08X}', 'end': f'0x{CALLEE + 2:08X}', 'mode': 'thumb'}]).encode()


def build(*, pre=(), post=(('ldr', 2, 'object'), ('h', 0x6812)), scalar=False, frame=False,
          thunk_target=THUNK_R2, tail=(), scalar_value=0x1234):
    """A guarded two-case switch with one thunk call.

    `pre` runs before the guard and `post` loads the thunk target register (r2 by
    default). With `scalar` a reached u16 literal word is bound as well. With
    `frame` an 8-byte write-only outgoing frame is stored and consumed by a plain
    call to CALLEE ahead of the thunk call.
    """
    items = [('h', 0xB510), *(frame and [('h', 0xB082)] or []), *pre] + switch_items()
    if frame:
        items += [('h', 0x2200), ('label', 'store0'), ('h', 0x9200), ('label', 'store1'), ('h', 0x9201),
                  ('label', 'plain'), ('bl', CALLEE)]
    if scalar:
        items += [('ldr', 3, 'scalar')]
    items += [*post, ('h', 0x1C20), ('label', 'thunk'), ('bl', thunk_target), *tail,
              *(frame and [('h', 0xB002)] or []), ('h', 0xBC10), ('h', 0xBC01), ('h', 0x4700), ('align',),
              ('label', 'object'), ('word', 0x02002000)]
    if scalar:
        items += [('label', 'scalar'), ('word', scalar_value)]
    body, labels, calls = assemble(items)
    thunk_sites = [[at, name] for at, target in calls
                   for name, alias in function_thunk.ALIASES.items() if target == alias]
    manifest = {'calls': [[at, f'func_{target:08X}'] for at, target in calls
                          if target not in function_thunk.ALIASES.values()],
                'data': [[labels['object'], 'g_right', 0]], 'data_policy': POLICY,
                'dependencies': function_thunk.dependencies([name for _, name in thunk_sites], rom_image(body)),
                'switch': descriptor(labels), 'thunk_policy': thunks.POLICY, 'thunks': thunk_sites}
    if scalar:
        manifest['scalar_policy'] = SCALAR_POLICY
        manifest['scalars'] = [[labels['scalar'], scalar_value]]
    if frame:
        manifest['stack_policy'] = pool_switch_frame.STACK_POLICY
    return body, labels, manifest


def verify(fixture, manifest=None, *, rom=None):
    body, _, expected = fixture
    return match.verify_switches(bytes(body), BASE, rom_image(body) if rom is None else rom,
                                 mapping(body), expected if manifest is None else manifest,
                                 data_mapping=json.dumps(OBJECTS).encode())


def leaf(fixture, calls=None, **options):
    """verify_leaf_instructions on a fixture with the given switch_thunks options."""
    body, labels, manifest = fixture
    if calls is None:
        calls = {BASE + at: function_thunk.ALIASES[name] for at, name in manifest['thunks']}
        calls.update({BASE + at: CALLEE for at, _ in manifest['calls']})
    return match.verify_leaf_instructions(
        bytes(body), BASE, True, calls,
        switch_relocations={row[0]: row[1] for row in manifest['switch']['relocations']},
        switch_data_relocations={labels['object']: ('g_right', 0x02002000)},
        backward_switch_cases=True, **options)


SOURCE = '''typedef void (*Initializer)(void *destination, unsigned size);
extern void *data_02000100;
extern Initializer data_02000200[];
extern void *func_08000400(unsigned size);
extern unsigned char func_08000410(void);

void func_08000000(void *unused, unsigned char *state)
{
    switch (*state) {
    case 0:
        data_02000100 = func_08000400(44);
        data_02000200[0](data_02000100, 44);
        *state = 3;
        break;
    case 1:
        data_02000100 = 0;
        *state = 5;
        break;
    case 2:
        if (func_08000410() != 9)
            break;
        *state = 4;
        break;
    case 3:
        *state = 1;
        break;
    case 4:
        *state = 2;
        break;
    }
}
'''
# The same call written against the compiler's thunk, as in a forged 0804CAE4.
FORGED = SOURCE.replace(
    'extern unsigned char func_08000410(void);',
    'extern unsigned char func_08000410(void);\n'
    'extern void _call_via_r2(void *destination, unsigned size, Initializer target);').replace(
    'data_02000200[0](data_02000100, 44);', '_call_via_r2(data_02000100, 44, data_02000200[0]);')
# Calling the thunk's ROM address as an ordinary function is also not a thunk binding.
NAMED = SOURCE.replace(
    'extern unsigned char func_08000410(void);',
    'extern unsigned char func_08000410(void);\n'
    'extern void func_0814224C(void *destination, unsigned size, Initializer target);').replace(
    'data_02000200[0](data_02000100, 44);', 'func_0814224C(data_02000100, 44, data_02000200[0]);')
# kit #393: case 1 stores the constant 0x808 into a halfword object, then reads a halfword
# through a pointer loaded from memory and stores it shifted left by 16. If that pointer named
# the object, the stored word would be 0x08080000, inside the ROM: the sound walk refuses it,
# and only the load-bearing store premise at the pointer load admits it.
PREMISED = SOURCE.replace(
    'extern unsigned char func_08000410(void);',
    'extern unsigned char func_08000410(void);\n'
    'extern unsigned short data_02000300;\nextern unsigned short *data_02000304;\n'
    'extern unsigned data_02000308;').replace(
    '        data_02000100 = 0;\n',
    '        data_02000100 = 0;\n        data_02000300 = 0x808;\n'
    '        data_02000308 = *data_02000304 << 16;\n')


def with_object(address, tail):
    """verify_switches on build(tail=...) after ``ldr r1, =object``, the data object placed at ``address``."""
    body, labels, manifest = build(tail=(('ldr', 1, 'object'), *tail))
    struct.pack_into('<I', body, labels['object'], address)
    return match.verify_switches(bytes(body), BASE, rom_image(body), mapping(body), manifest,
                                 data_mapping=json.dumps({'g_right': f'0x{address:08X}'}).encode())


def premises(fixture, **options):
    """The store premises the CFG walk derives for a fixture (match.main's derive mode)."""
    record = thunks.StorePremises()
    leaf(fixture, switch_thunks=PLAIN, switch_thunk_premises=record, **options)
    return record.derived


class ProofTests(unittest.TestCase):
    def test_admitted_shapes_verify(self):
        for options in ({}, {'scalar': True}, {'frame': True}, {'frame': True, 'scalar': True}):
            with self.subTest(options=options):
                f = build(**options)
                instructions, summary = verify(f)
                self.assertEqual(summary, evidence.CALL_SUMMARY)
                self.assertTrue(any(item.mnemonic == 'mov' for item in instructions))

    def test_selector_follows_the_manifest_markers(self):
        self.assertEqual(thunks.selector_for_manifest(build()[2]), PLAIN)
        self.assertEqual(thunks.selector_for_manifest(build(frame=True)[2]), FRAMED)
        self.assertIsNone(thunks.selector_for_manifest({}))
        for manifest in (dict(build()[2], thunk_policy='other'), dict(build()[2], pool_policy='p')):
            with self.assertRaises(ValueError):
                thunks.selector_for_manifest(manifest)

    def test_default_and_other_policies_still_refuse(self):
        f = build()
        for key in ('thunk_policy', 'thunks', 'dependencies'):
            manifest = copy.deepcopy(f[2]); manifest.pop(key)
            with self.subTest(key=key), self.assertRaises(ValueError):
                verify(f, manifest)
        # Without the marker the thunk is an ordinary call to func_<thunk address>.
        manifest = {key: value for key, value in f[2].items()
                    if key not in ('thunk_policy', 'thunks', 'dependencies')}
        manifest['calls'] = [[f[1]['thunk'], f'func_{THUNK_R2:08X}']]
        with self.assertRaisesRegex(ValueError, 'runtime call thunks'):
            verify(f, manifest)
        # The CFG verifier itself refuses thunks unless the explicit selector is passed.
        with self.assertRaisesRegex(ValueError, 'runtime call thunks'):
            leaf(f)
        leaf(f, switch_thunks=PLAIN)

    def test_markers_and_manifest_shape_are_exact(self):
        f = build()
        for key, value in (('pool_policy', 'dispatch-identified-table-pointer-v1'),
                           ('function_policy', 'canonical-function-literals-v1'),
                           ('frame_policy', 'typed-outgoing-six-words-v1'),
                           ('thunk_policy', 'canonical-call-thunks-v2'), ('thunk_policy', None),
                           ('extra', 1)):
            manifest = copy.deepcopy(f[2]); manifest[key] = value
            with self.subTest(key=key, value=value), self.assertRaises(ValueError):
                verify(f, manifest)
        # A manifest without the complete-object policy cannot carry thunks.
        manifest = copy.deepcopy(f[2]); manifest.pop('data_policy')
        with self.assertRaises(ValueError):
            verify(f, manifest)

    def test_each_thunk_call_is_bound_exactly_once(self):
        f = build()
        site = f[1]['thunk']
        both = copy.deepcopy(f[2]); both['calls'] = [[site, f'func_{THUNK_R2:08X}']]
        with self.assertRaisesRegex(ValueError, 'overlapping'):
            verify(f, both)
        twice = copy.deepcopy(f[2]); twice['thunks'] = [[site, '_call_via_r2'], [site, '_call_via_r2']]
        with self.assertRaisesRegex(ValueError, 'unique ordered'):
            verify(f, twice)
        # A thunk call the manifest leaves out is a call the CFG cannot bind.
        missing = copy.deepcopy(f[2]); missing['thunks'] = []
        with self.assertRaises(ValueError):
            verify(f, missing)

    def test_tampered_thunk_evidence_rejects(self):
        f = build()
        for key, value in [('thunks', [[f[1]['thunk'], '_call_via_r3']]),
                           ('thunks', [[f[1]['thunk'] + 1, '_call_via_r2']]),
                           ('thunks', [[f[1]['thunk'], '_call_via_r13']]),
                           ('dependencies', []),
                           ('data', [[f[1]['object'], 'g_left', 0]])]:
            manifest = copy.deepcopy(f[2]); manifest[key] = value
            with self.subTest(key=key, value=value), self.assertRaises(ValueError):
                verify(f, manifest)
        rom = bytearray(rom_image(f[0])); struct.pack_into('<H', rom, THUNK_R2 - BASE, 0x4718)
        with self.assertRaises(ValueError):
            verify(f, rom=bytes(rom))
        manifest = copy.deepcopy(f[2])
        manifest['dependencies'][0][1] = float(manifest['dependencies'][0][1])
        with self.assertRaisesRegex(ValueError, 'dependencies differ'):
            verify(f, manifest)
        self.assertTrue(thunks.exact({'a': [1]}, {'a': [1]}))
        self.assertFalse(thunks.exact([True], [1]))

    def test_wrong_bytes_reject(self):
        f = build(); g = copy.deepcopy(f)
        struct.pack_into('<I', g[0], f[1]['object'], 0x02001000)
        with self.assertRaises(ValueError):
            verify(g, rom=rom_image(g[0]))

    def test_data_words_cannot_name_code_entries_or_thunks(self):
        f = build()
        for value in (CALLEE | 1, THUNK_R2, BASE + 8):
            g = copy.deepcopy(f); struct.pack_into('<I', g[0], f[1]['object'], value)
            with self.subTest(value=hex(value)), self.assertRaises(ValueError):
                verify(g, rom=rom_image(g[0]))
        for name, value in (('g_code', CALLEE), ('g_thunk', THUNK_R2)):
            objects = json.dumps({'g_left': '0x02001000', 'g_right': f'0x{value:08X}'}).encode()
            g = copy.deepcopy(f); struct.pack_into('<I', g[0], f[1]['object'], value)
            with self.subTest(name=name), self.assertRaises(ValueError):
                match.verify_switches(bytes(g[0]), BASE, rom_image(g[0]), mapping(g[0]), f[2],
                                      data_mapping=objects)

    def test_scalar_words_must_be_bound_when_present(self):
        f = build(scalar=True)
        for key, value in (('scalars', []), ('scalars', [[f[1]['scalar'], 0x1235]])):
            manifest = copy.deepcopy(f[2]); manifest[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                verify(f, manifest)
        manifest = copy.deepcopy(f[2]); manifest.pop('scalar_policy'); manifest.pop('scalars')
        with self.assertRaisesRegex(ValueError, 'literal-word coverage'):
            verify(f, manifest)
        manifest = copy.deepcopy(build()[2]); manifest['scalar_policy'] = SCALAR_POLICY
        with self.assertRaises(ValueError):
            verify(build(), manifest)

    def test_frame_variants_are_not_interchangeable(self):
        plain, framed = build(), build(frame=True)
        # A framed body under the frameless selector: the plain verifier refuses fixed frames.
        manifest = copy.deepcopy(framed[2]); manifest.pop('stack_policy')
        with self.assertRaisesRegex(ValueError, 'excludes fixed frames'):
            verify(framed, manifest)
        # A frameless body under the frame selector has no allocation to consume.
        manifest = copy.deepcopy(plain[2]); manifest['stack_policy'] = pool_switch_frame.STACK_POLICY
        with self.assertRaisesRegex(ValueError, 'one fixed allocation'):
            verify(plain, manifest)
        manifest = copy.deepcopy(framed[2]); manifest['stack_policy'] = 'other'
        with self.assertRaises(ValueError):
            verify(framed, manifest)
        self.assertNotEqual(thunks.fingerprint(BASE, b'', plain[2]), thunks.fingerprint(BASE, b'', framed[2]))

    def test_near_miss_frames_refuse(self):
        f = build(frame=True)
        changes = [('store0', 0x9A00),   # ldr r2,[sp]: outgoing words are write-only
                   ('store1', 0x1C12),   # the call sees only one outgoing word
                   ('store1', 0x9202),   # store outside the owned 8-byte allocation
                   ('store1', 0x466A)]   # mov r2,sp materializes a stack address
        for label, value in changes:
            g = copy.deepcopy(f); struct.pack_into('<H', g[0], g[1][label], value)
            with self.subTest(label=label, value=value), self.assertRaises(ValueError):
                verify(g, rom=rom_image(g[0]))

    def test_calls_not_through_a_register_thunk_refuse(self):
        # A thunk-less body is not a thunk selector body.
        f = build()
        body, labels, _ = f
        plain = build(thunk_target=CALLEE)
        with self.assertRaisesRegex(ValueError, 'thunk calls differ'):
            leaf(plain, calls={BASE + labels['thunk']: CALLEE}, switch_thunks=PLAIN)
        # Non-canonical reserved addresses are not aliases.
        with self.assertRaises(ValueError):
            thunks.check_link(PLAIN, {}, {'_call_via_r2': THUNK_R2 + 4})
        with self.assertRaises(ValueError):
            thunks.check_link(PLAIN, {}, {'func_08001000': CALLEE})
        with self.assertRaises(ValueError):
            thunks.check_link(PLAIN, {0x40: ('func_08001100', 0x08001101)}, {'_call_via_r2': THUNK_R2})
        self.assertEqual(thunks.check_link(PLAIN, {}, {'_call_via_r2': THUNK_R2, 'func_08001000': CALLEE}),
                         {'_call_via_r2'})

    def test_thunk_targets_cannot_hold_local_code_addresses(self):
        verify(build())
        verify(build(pre=(('h', 0x2200),)))
        # Each attack still reads the object word, so only the thunk register differs.
        attacks = {
            'table pointer before the guard, then a table entry':
                dict(pre=(('ldr', 2, 'pointer'),), post=(('h', 0x6812),)),
            'table pointer before the guard': dict(pre=(('ldr', 2, 'pointer'),), post=()),
            'dispatch table register live into a case': dict(post=(('h', 0x680A),)),
            'dispatch case address': dict(post=(('h', 0x1C02),)),
            'entry return address': dict(post=(('h', 0x4672),)),
            'table entry through a block load': dict(post=(('h', 0xC904),)),
            'stack round trip': dict(post=(('h', 0xB402), ('h', 0xBC04))),
        }
        for label, parts in attacks.items():
            parts['post'] = (('ldr', 3, 'object'), *parts['post'])
            # The taint walk refuses each one on its own; the replay refuses them too, and
            # also any second read of the table pointer.
            with self.subTest(label), self.assertRaisesRegex(ValueError, 'can hold a local code address'):
                leaf(build(**parts), switch_thunks=PLAIN)
            with self.subTest(label), self.assertRaisesRegex(
                    ValueError, 'can hold a local code address|read only by its dispatch load'):
                verify(build(**parts))
        # A harmless second read of the table pointer is still refused by the replay.
        g = build(pre=(('ldr', 2, 'pointer'),))
        leaf(g, switch_thunks=PLAIN)
        self.assertRaisesRegex(ValueError, 'read only by its dispatch load', verify, g)
        for label, post in {'object store': (('ldr', 3, 'object'), ('h', 0x6019), ('h', 0x681A)),
                            'block store': (('ldr', 3, 'object'), ('h', 0xC302), ('h', 0x681A))}.items():
            with self.subTest(label), self.assertRaisesRegex(ValueError, 'cannot be stored'):
                verify(build(post=post))
        # The check is part of the CFG verifier, so it does not depend on any manifest field.
        f = build(pre=(('ldr', 2, 'pointer'),), post=(('ldr', 3, 'object'), ('h', 0x6812)))
        with self.assertRaisesRegex(ValueError, 'can hold a local code address'):
            leaf(f, switch_thunks=PLAIN)
        # Under the frame selector the same attack is still refused.
        # (The plain call ahead of the thunk call clobbers earlier taint, so use the call's own LR.)
        f = build(frame=True, post=(('ldr', 3, 'object'), ('h', 0x4672)))
        with self.assertRaisesRegex(ValueError, 'can hold a local code address'):
            leaf(f, switch_thunks=FRAMED, switch_outgoing_stack=pool_switch_frame.STACK_POLICY,
                 switch_outgoing_stack_fixed_pool=True)

    def test_block_transfers_through_untainted_registers_stay_ordinary(self):
        verify(build(post=(('ldr', 3, 'object'), ('h', 0x6819), ('h', 0xC302),
                           ('ldr', 2, 'object'), ('h', 0x6812))))
        verify(build(post=(('ldr', 3, 'object'), ('h', 0xCB04))))

    def test_new_decode_refuses_wide_and_trapping_encodings(self):
        # The taint walk decodes every reached instruction: kit #180's rule applies to it.
        # Through the whole verifier the base leaf walk refuses these first; the pass's own
        # check is exercised directly below.
        for label, tail in {'bkpt': (('h', 0xBE00),), 'udf': (('h', 0xDE00),),
                            'svc': (('h', 0xDF00),), 'thumb-2 mov.w': (('h', 0xF04F), ('h', 0x0002))}.items():
            f = build(tail=tail)
            with self.subTest(label), self.assertRaisesRegex(
                    ValueError, 'non-leaf calls and interrupts' if label == 'svc' else 'not an ARMv4T encoding'):
                verify(f)
        with self.assertRaisesRegex(ValueError, '16-bit ARMv4T'):
            # Defence in depth: the walk itself refuses when handed such an instruction.
            from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
            decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB); decoder.detail = True
            wide = next(decoder.disasm(bytes.fromhex('4ff00200'), BASE))
            thunks.verify_thunk_targets({BASE: wide}, {BASE: ()}, BASE, {}, BASE + 8)
        for word in ('00be', '00de', '00df'):
            narrow = next(decoder.disasm(bytes.fromhex(word), BASE))
            with self.subTest(word=word), self.assertRaisesRegex(ValueError, '16-bit ARMv4T'):
                thunks.verify_thunk_targets({BASE: narrow}, {BASE: ()}, BASE, {}, BASE + 8)

    def test_objects_cannot_lie_inside_indexed_function_spans(self):
        verify(build())
        body, labels, manifest = build()
        # The issue's shape: 0x08001009 lies inside a 0x40-byte indexed function, not at its entry.
        wide = json.dumps([{'rom': f'0x{BASE:08X}', 'end': f'0x{BASE + len(body):08X}', 'mode': 'thumb'},
                           {'rom': f'0x{CALLEE:08X}', 'end': f'0x{CALLEE + 0x40:08X}', 'mode': 'thumb'}]).encode()
        for label, address in {'callee span': CALLEE + 9, 'own span': BASE + 8}.items():
            moved = bytearray(body)
            struct.pack_into('<I', moved, labels['object'], address)
            with self.subTest(label), self.assertRaisesRegex(
                    ValueError, 'code entries or indexed function spans|invalid interposed switch-data object'):
                match.verify_switches(bytes(moved), BASE, rom_image(bytes(moved)), wide, manifest,
                                      data_mapping=json.dumps({'g_right': f'0x{address:08X}'}).encode())

    def test_objects_cannot_name_a_rom_mirror_of_code(self):
        # 0x0A000000-0x0DFFFFFF maps the same ROM as 0x08000000 (#377); an addend that
        # carries the object word into a mirror names the code there.
        body, labels, manifest = build()
        wide = json.dumps([{'rom': f'0x{BASE:08X}', 'end': f'0x{BASE + len(body):08X}', 'mode': 'thumb'},
                           {'rom': f'0x{CALLEE:08X}', 'end': f'0x{CALLEE + 0x40:08X}', 'mode': 'thumb'}]).encode()
        cases = {'entry': ((CALLEE | 1) + 0x02000000, 'cannot bind indexed function entries as data'),
                 'thunk': (THUNK_R2 + 0x04000000, 'cannot bind indexed function entries as data'),
                 'callee span': (CALLEE + 9 + 0x04000000, 'code entries or indexed function spans'),
                 'own span': (BASE + 8 + 0x02000000, 'code entries or indexed function spans')}
        for label, (value, message) in cases.items():
            moved, bound = bytearray(body), copy.deepcopy(manifest)
            struct.pack_into('<I', moved, labels['object'], value)
            bound['data'] = [[labels['object'], 'g_right', value - 0x02002000]]
            with self.subTest(label), self.assertRaisesRegex(ValueError, message):
                match.verify_switches(bytes(moved), BASE, rom_image(bytes(moved)), wide, bound,
                                      data_mapping=json.dumps(OBJECTS).encode())
        # The SRAM/flash bus is not ROM.
        moved, bound = bytearray(body), copy.deepcopy(manifest)
        struct.pack_into('<I', moved, labels['object'], CALLEE + 9 + 0x06000000)
        bound['data'] = [[labels['object'], 'g_right', CALLEE + 9 + 0x06000000 - 0x02002000]]
        match.verify_switches(bytes(moved), BASE, rom_image(bytes(moved)), wide, bound,
                              data_mapping=json.dumps(OBJECTS).encode())

    def test_constants_built_from_immediates_cannot_be_thunk_targets(self):
        obj = (('ldr', 3, 'object'),)
        rom_address = (('h', 0x2280), ('h', 0x0512), ('h', 0x3231))  # movs #0x80; lsls #20; adds #0x31
        for label, post in {
                'rom address': (*obj, *rom_address),
                'rom address through a non-modelled operation': (*obj, *rom_address[:2], ('h', 0x4252)),
                'plain constant': (*obj, ('h', 0x2204)),
                'stored rom address': (*obj, *rom_address, ('h', 0x601A))}.items():
            with self.subTest(label), self.assertRaisesRegex(
                    ValueError, 'local code address|constant-derived|cannot be stored'):
                leaf(build(post=post), switch_thunks=PLAIN)
        # Small constants that never reach the thunk register stay ordinary.
        verify(build(post=(*obj, ('h', 0x6819), ('h', 0x6019), ('ldr', 2, 'object'), ('h', 0x6812))))
        # A constant mixed with a loaded value is constant-derived, but loading through it is ordinary.
        verify(build(post=(*obj, ('h', 0x6818), ('h', 0x3004), ('h', 0x6802))))

    def test_a_stored_constant_makes_every_later_load_constant_derived(self):
        # r3 = &g_right; [r3] = 0x04000000; [r3 + 4] = 0x04000031; then r2 = [r4] + [r4 + 4] = 0x08000031.
        def parts(*, first=(('h', 0x6019),), between=(), reload=(('ldr', 4, 'object'),)):
            return dict(post=(('ldr', 3, 'object'), ('h', 0x2180), ('h', 0x04C9), *first, *between,
                              ('h', 0x3131), ('h', 0x6059), *reload,
                              ('h', 0x6822), ('h', 0x6860), ('h', 0x1812)))
        # The stored words are exact at the object's address, so the sum is the ROM address itself
        # (kit #393). The writeback store moves r3 on by 4 first, so the second word lands at r3 + 8
        # and the reload of r3 + 4 holds no stored constant: constant-derived, but no exact value.
        rom, derived = 'can hold a local code address', 'holds a constant-derived value'
        variants = {
            'fresh literal reload': (parts(), rom),
            'rewrite of the base to itself': (parts(between=(('h', 0x3300),)), rom),
            'writeback store': (parts(first=(('h', 0xC302),), reload=(('ldr', 4, 'object'),)), derived),
            'copy of the base': (parts(reload=(('h', 0x1C1C),)), rom),
        }
        for label, (fixture, message) in variants.items():
            with self.subTest(label), self.assertRaisesRegex(ValueError, message):
                leaf(build(**fixture), switch_thunks=PLAIN)
        # The dirty flag survives a call, which could copy the memory.
        bl = (('bl', CALLEE),)
        with self.assertRaisesRegex(ValueError, 'holds a constant-derived value'):
            leaf(build(**parts(between=bl)), switch_thunks=PLAIN)
        # Storing only loaded values leaves later loads ordinary.
        verify(build(post=(('ldr', 3, 'object'), ('h', 0x6819), ('h', 0x6019), ('h', 0x6059),
                           ('ldr', 2, 'object'), ('h', 0x6812))))

    def test_literal_words_and_loaded_values_join_the_constant_model(self):
        obj = (('ldr', 0, 'object'),)
        lit = dict(scalar=True, scalar_value=0x0800)
        for label, (parts, message) in {
                'literal shifted into the rom': (dict(post=(*obj, ('h', 0x041A)), **lit), 'local code address'),
                'literal shifted and offset': (dict(post=(*obj, ('h', 0x041A), ('h', 0x3231)), **lit),
                                               'local code address'),
                'literal copied': (dict(post=(*obj, ('h', 0x1C1A)), **lit), 'constant-derived'),
                'object address plus offset': (dict(post=(('ldr', 2, 'object'), ('h', 0x3231))),
                                               'constant-derived'),
                'loaded value plus constant, shifted': (
                    dict(post=(('ldr', 3, 'object'), ('h', 0x6818), ('h', 0x3031), ('h', 0x0502))),
                    'constant-derived'),
                'constant stored and loaded back': (  # exact at the object: 0x80 << 20 (kit #393)
                    dict(post=(('ldr', 3, 'object'), ('h', 0x2180), ('h', 0x6019), ('h', 0x681A), ('h', 0x0512))),
                    'can hold a local code address'),
                'counting loop is widened': (
                    dict(post=(('ldr', 3, 'object'), ('h', 0x2100), ('label', 'again'), ('h', 0x3101),
                               ('h', 0x2905), ('bhi', 'again'), ('h', 0x6019),
                               ('ldr', 2, 'object'), ('h', 0x6812))),
                    'cannot be stored|constant-derived')}.items():
            with self.subTest(label), self.assertRaisesRegex(ValueError, message):
                leaf(build(**parts), switch_thunks=PLAIN)
        # The same literal used as a plain value, never as the thunk register, stays ordinary.
        verify(build(post=(*obj, ('h', 0x041A), ('ldr', 2, 'object'), ('h', 0x6812)), **lit))

    def test_widening_taints_only_the_constants_a_loop_changes(self):
        # r5 = [&g_right] + 4 is constant-derived (MIXED) and loop-invariant; r1 counts up, so
        # the loop head passes CONSTANT_BUDGET. Only r1 is widened: a store through r5 (or the
        # invariant object address in r3) after the loop stays ordinary.
        def loop(*after):
            return dict(post=(('ldr', 3, 'object'), ('h', 0x681D), ('h', 0x3504), ('h', 0x681E),
                              ('h', 0x2100), ('label', 'again'), ('h', 0x3101), ('h', 0x2905),
                              ('bhi', 'again'), *after, ('ldr', 2, 'object'), ('h', 0x6812)))
        verify(build(**loop(('h', 0x602E))))  # str r6, [r5]
        verify(build(**loop(('h', 0x601E), ('h', 0x602E))))  # str r6 through the invariant r3, then r5
        # The widened counter is still tainted: a store through it refuses (the first, unwidened
        # pass over the same store passes, so only the widening can refuse it).
        with self.assertRaisesRegex(ValueError, 'cannot be stored'):
            leaf(build(**loop(('h', 0x600E))), switch_thunks=PLAIN)  # str r6, [r1]
        # A register the loop rewrites with a changing constant is widened, whatever it held before.
        changing = dict(post=(('ldr', 3, 'object'), ('h', 0x681D), ('h', 0x3504), ('h', 0x681E),
                              ('h', 0x2100), ('label', 'again'), ('h', 0x3101), ('h', 0x1C4D),
                              ('h', 0x2905), ('bhi', 'again'), ('h', 0x602E),
                              ('ldr', 2, 'object'), ('h', 0x6812)))  # adds r5, r1, #1 in the loop
        with self.assertRaisesRegex(ValueError, 'cannot be stored'):
            leaf(build(**changing), switch_thunks=PLAIN)

    def test_widening_does_not_let_mixed_absorb_an_exact_rom_address(self):
        # r1 is [&g_right] + 1 (MIXED) on entry and 0x80 from the second pass on, so
        # (r1 << 20) + k is an exact address inside this caller on every later pass.
        # The join keeps the exact value arriving at the MIXED entry, so the entry changes.
        def callback(table, count):
            return dict(post=(('ldr', 3, 'object'), ('h', 0x6819), ('h', 0x3101), ('h', 0x2000 | count),
                              ('label', 'again'), ('h', 0x050C), ('h', 0x3400 | table), ('h', 0x2180),
                              ('h', 0x3801), ('h', 0x2800), ('bhi', 'again'), ('h', 0x6822)))
        table = build(**callback(0, 1))[1]['table']
        fixture = build(**callback(table, 20))  # r2 = table[0], a case address, past the budget
        self.assertEqual(fixture[1]['table'], table)
        with self.assertRaisesRegex(ValueError, 'local code address'):
            verify(fixture)
        # The same loop, counting r2 down from 20, stores r4 = (r1 << 20) + 0x15 on each pass:
        # from the second pass on that is 0x08000015, an address inside this caller.
        store = build(tail=(('ldr', 3, 'object'), ('h', 0x6819), ('h', 0x3101), ('h', 0x2214),
                            ('label', 'again'), ('h', 0x050C), ('h', 0x3415), ('h', 0x601C),
                            ('h', 0x2180), ('h', 0x3A01), ('h', 0x2A00), ('bhi', 'again')))
        with self.assertRaisesRegex(ValueError, 'cannot be stored'):
            verify(store)

    def test_a_mixed_path_cannot_hide_an_exact_value_at_a_join(self):
        # kit #367: r1 = [&g_right] + 1 (a constant met a loaded value) on one path and 0x80 on
        # another. Joined, r1 must keep 0x80 for the ROM check: (0x80 << 20) is this caller.
        mixed = (('ldr', 3, 'object'), ('h', 0x6819), ('h', 0x3101))  # ldr r1, [r3]; adds r1, #1
        rom = (('h', 0x050C),)                                         # lsls r4, r1, #20
        store = (*rom, ('h', 0x3415), ('h', 0x601C))                   # adds r4, #0x15; str r4, [r3]

        def count_down(count, body):
            # movs r0, #count; again: body; movs r1, #0x80; subs r0, #1; cmp r0, #0; bhi again
            return (*mixed, ('h', 0x2000 | count), ('label', 'again'), *body,
                    ('h', 0x2180), ('h', 0x3801), ('h', 0x2800), ('bhi', 'again'))

        def callback(table, count):
            # From the second pass on r4 is the caller's own table, so r2 is its case0 address.
            return (*count_down(count, (*rom, ('h', 0x3400 | table))), ('h', 0x6822))  # ldr r2, [r4]

        table = build(post=callback(0, 1))[1]['table']
        for count in (10, 20):
            body, labels, _ = fixture = build(post=callback(table, count))
            self.assertEqual(labels['table'], table)
            self.assertEqual(struct.unpack_from('<I', body, table)[0], BASE + labels['case0'])
            with self.subTest('callback from the own table', count=count), \
                    self.assertRaisesRegex(ValueError, 'thunk target register can hold a local code address'):
                verify(fixture)
        stores = {
            'count-down loop, 10 passes': count_down(10, store),
            'count-down loop, 20 passes': count_down(20, store),
            'count-up loop': (*mixed, ('h', 0x2200), ('label', 'again'), *store, ('h', 0x2180),
                              ('h', 0x3201), ('h', 0x2A14), ('bhi', 'again')),  # adds r2, #1; cmp r2, #20
            'loop without a counter': (*mixed, ('h', 0x2200), ('label', 'again'), *store, ('h', 0x2180),
                                       ('bhi', 'again')),
            # No loop: only the visit order differs between the two.
            'join, exact on the taken edge': (('ldr', 3, 'object'), ('h', 0x2180), ('h', 0x2A00), ('bhi', 'skip'),
                                              *mixed[1:], ('label', 'skip'), *store),
            'join, mixed on the taken edge': (*mixed, ('h', 0x2A00), ('bhi', 'skip'), ('h', 0x2180),
                                              ('label', 'skip'), *store),
        }
        for label, tail in stores.items():
            with self.subTest(label), self.assertRaisesRegex(ValueError, 'a local code address cannot be stored'):
                verify(build(tail=tail))
            with self.subTest(label), self.assertRaisesRegex(ValueError, 'a local code address cannot be stored'):
                leaf(build(tail=tail), switch_thunks=PLAIN)
        # Two exact values: the join covers both, so (0x80 << 20) is not lost behind 0x40.
        for first, second in ((0x2180, 0x2140), (0x2140, 0x2180)):  # movs r1, #0x80 / #0x40
            tail = (('ldr', 3, 'object'), ('h', first), ('h', 0x2A00), ('bhi', 'skip'), ('h', second),
                    ('label', 'skip'), *store)
            with self.subTest('two exact values', first=first), \
                    self.assertRaisesRegex(ValueError, 'a local code address cannot be stored'):
                leaf(build(tail=tail), switch_thunks=PLAIN)
        # The joined register stays constant-derived, so it is still no callback.
        for label, post in {
                'exact on the taken edge': (('ldr', 3, 'object'), ('h', 0x2204), ('h', 0x2900), ('bhi', 'skip'),
                                            ('h', 0x681A), ('h', 0x3201), ('label', 'skip')),
                'mixed on the taken edge': (('ldr', 3, 'object'), ('h', 0x681A), ('h', 0x3201), ('h', 0x2900),
                                            ('bhi', 'skip'), ('h', 0x2204), ('label', 'skip'))}.items():
            with self.subTest(label), self.assertRaisesRegex(ValueError, 'holds a constant-derived value'):
                verify(build(post=post))
        # Small exact values joined with mixed ones stay ordinary, as in shipped 08011860 (a store
        # tail where one path sets r0 = 5) and 080C5F94 (a clamp, then the value is narrowed and stored).
        for label, tail in {
                'shared store tail': (('ldr', 3, 'object'), ('h', 0x6819), ('h', 0x6818), ('h', 0x3001),
                                      ('h', 0x2A00), ('bhi', 'skip'), ('h', 0x2005), ('label', 'skip'),
                                      ('h', 0x7208)),                          # strb r0, [r1, #8]
                'clamp': (('ldr', 3, 'object'), ('h', 0x681A), ('h', 0x3201), ('h', 0x2A40), ('bhi', 'skip'),
                          ('h', 0x2240), ('label', 'skip'),
                          ('h', 0x03D2), ('h', 0x0C12), ('h', 0x605A))}.items():  # lsls #15; lsrs #16; str
            with self.subTest(label):
                verify(build(tail=tail))
                leaf(build(tail=tail), switch_thunks=PLAIN)

    def test_the_constant_join_keeps_every_exact_value(self):
        mixed, low, high = thunks.MIXED, (4, 4), (0x80, 0x90)
        self.assertEqual(thunks.join(mixed, mixed), mixed)
        for value in (low, high):
            self.assertEqual(thunks.join(mixed, value), value)
            self.assertEqual(thunks.join(value, mixed), value)
        self.assertEqual(thunks.join(low, high), (4, 0x90))
        self.assertEqual(thunks.join(high, low), (4, 0x90))

    def test_a_constant_reloaded_from_memory_keeps_its_rom_check(self):
        # kit #393: r3 = &g_right; each tail stores 0x08000015, an address inside this caller,
        # built from constants that went through memory at the object's exact address.
        obj, inside = ('ldr', 3, 'object'), (('h', 0x0524), ('h', 0x3415), ('h', 0x601C))  # lsls #20; adds; str
        for label, tail in {
                'word reload': (obj, ('h', 0x2180), ('h', 0x6019), ('h', 0x681C), *inside),
                'halfword reload': (obj, ('h', 0x2180), ('h', 0x8019), ('h', 0x881C), *inside),
                # three small stores assemble the word in memory; it is loaded and stored on
                'byte assembly': (obj, ('h', 0x2108), ('h', 0x70D9), ('h', 0x2100), ('h', 0x7099),
                                  ('h', 0x2115), ('h', 0x8019), ('h', 0x681C), ('h', 0x605C))}.items():
            f = build(tail=tail)
            with self.subTest(label), self.assertRaisesRegex(ValueError, 'a local code address cannot be stored'):
                verify(f)
            with self.subTest(label), self.assertRaisesRegex(ValueError, 'a local code address cannot be stored'):
                leaf(f, switch_thunks=PLAIN, switch_thunk_premises=thunks.StorePremises())
        # A callback loaded after a constant store is still refused.
        with self.assertRaisesRegex(ValueError, 'constant-derived'):
            verify(build(post=(obj, ('h', 0x2180), ('h', 0x6019), ('ldr', 2, 'object'), ('h', 0x6812))))
        # A store of a loaded value at the same exact address replaces the constant there.
        verify(build(tail=(obj, ('h', 0x2180), ('h', 0x6019), ('h', 0x6859), ('h', 0x6019),  # [r3] = [r3 + 4]
                           ('h', 0x681C), *inside)))
        # A join keeps the constant one path left, as kit #367 keeps a register's.
        with self.assertRaisesRegex(ValueError, 'a local code address cannot be stored'):
            verify(build(tail=(obj, ('h', 0x6859), ('h', 0x2A00), ('bhi', 'skip'), ('h', 0x2180),
                               ('label', 'skip'), ('h', 0x6019), ('h', 0x681C), *inside)))
        # One byte stored anywhere cannot fill a word: a word reloaded from the object stays MIXED.
        verify(build(tail=(obj, ('h', 0x6818), ('h', 0x2108), ('h', 0x7001),  # strb #8 through a loaded r0
                           ('h', 0x681C), ('h', 0x601C))))
        # An address exact on only one path is not exact: r2 is &g_right on the fall-through and a
        # loaded word on the taken edge, so storing a loaded r6 through it cannot erase the 0x80.
        with self.assertRaisesRegex(ValueError, 'a local code address cannot be stored'):
            verify(build(tail=(obj, ('h', 0x2180), ('h', 0x6019), ('h', 0x685A), ('h', 0x2800), ('bhi', 'skip'),
                               ('h', 0x1C1A), ('label', 'skip'), ('h', 0x1C12), ('h', 0x68DE), ('h', 0x6016),
                               ('h', 0x681C), *inside)))
        # Byte ranges cover every value: byte 3 is 7 or 8, so the reloaded word may be 0x08000000.
        with self.assertRaisesRegex(ValueError, 'a local code address cannot be stored'):
            verify(build(tail=(obj, ('h', 0x2107), ('h', 0x2800), ('bhi', 'skip'), ('h', 0x2108), ('label', 'skip'),
                               ('h', 0x70D9), ('h', 0x2200), ('h', 0x709A), ('h', 0x801A),  # [r3+3]; [r3+2]; [r3]
                               ('h', 0x681C), ('h', 0x605C))))
        # A reloaded 0 minus 1 is exactly 0xFFFFFFFF (an interval that wraps whole), not a code address.
        verify(build(tail=(obj, ('h', 0x2100), ('h', 0x6019), ('h', 0x681C), ('h', 0x3C01), ('h', 0x601C))))
        # Both paths store at the object, so the join keeps both bytes: 0x80 is not lost behind 0x04.
        with self.assertRaisesRegex(ValueError, 'a local code address cannot be stored'):
            verify(build(tail=(obj, ('h', 0x2180), ('h', 0x2800), ('bhi', 'skip'), ('h', 0x2104), ('label', 'skip'),
                               ('h', 0x7019), ('h', 0x781C), *inside)))  # strb r1, [r3]; ldrb r4, [r3]
        # Four bytes stored through a loaded pointer may assemble 0x08000015 at [r3 + 4]: the wild
        # hull covers every one of them.
        with self.assertRaisesRegex(ValueError, 'a local code address cannot be stored'):
            verify(build(tail=(obj, ('h', 0x6818), ('h', 0x2115), ('h', 0x7001), ('h', 0x2100), ('h', 0x7041),
                               ('h', 0x7081), ('h', 0x2108), ('h', 0x70C1),  # [r0] = 0x15, 0, 0, 8
                               ('h', 0x685C), ('h', 0x601C))))  # ldr r4, [r3, #4]; str r4, [r3]
        # A signed reload extends the sign: 0x8000 reloaded by ldrsh is 0xFFFF8000, and << 12 stays
        # outside the ROM (as an unsigned 0x8000 it would be 0x08000000).
        verify(build(tail=(obj, ('h', 0x2180), ('h', 0x0209), ('h', 0x8019), ('h', 0x2200),  # r1 = 0x8000; strh
                           ('h', 0x5E9C), ('h', 0x0324), ('h', 0x605C))))  # ldrsh r4, [r3, r2]; lsls #12; str
        # A signed reload of 0x7F or 0x80 is 0x7F or 0xFFFFFF80, not [0x7F, 0x80]: plus 0x0E000000
        # the second is 0x0DFFFF80, inside the ROM.
        with self.assertRaisesRegex(ValueError, 'a local code address cannot be stored'):
            verify(build(tail=(obj, ('h', 0x2180), ('h', 0x2800), ('bhi', 'skip'), ('h', 0x217F), ('label', 'skip'),
                               ('h', 0x7019), ('h', 0x2200), ('h', 0x569C),  # strb; ldrsb r4, [r3, r2]
                               ('h', 0x22E0), ('h', 0x0512), ('h', 0x18A4), ('h', 0x605C))))  # + (0xE0 << 20)

    def test_the_store_map_follows_the_arm7tdmi_memory_map(self):
        obj, inside = ('ldr', 3, 'object'), (('h', 0x0524), ('h', 0x3415))  # lsls r4, r4, #20; adds r4, #0x15
        stored = 'a local code address cannot be stored'
        for label, tail in {
                # Addresses are taken mod 2**32: r3 + (0 - 4) is the byte r3 - 4 names.
                'address sum mod 2**32': (obj, ('h', 0x2500), ('h', 0x3D04), ('h', 0x2180), ('h', 0x5159),
                                          ('h', 0x1F1E), ('h', 0x6834), *inside, ('h', 0x601C)),
                # EWRAM repeats every 256 KiB: r3 + (1 << 18) is the byte at r3.
                'EWRAM mirror': (obj, ('h', 0x2180), ('h', 0x6019), ('h', 0x2501), ('h', 0x04AD), ('h', 0x595C),
                                 *inside, ('h', 0x605C)),
                # STMIA writes back: after stmia r0!, {r2} the next store through r0 lands at r3 + 4.
                'stmia writeback': (obj, ('h', 0x1C18), ('h', 0x2200), ('h', 0x2180), ('h', 0xC004), ('h', 0x6001),
                                    ('h', 0x685C), *inside, ('h', 0x601C)),
                # ... and the base's own constant moves with it: r0 = 0x07FFFFF9, and six words later
                # it is 0x08000011, inside the ROM, stored as it is.
                'stmia base constant': (obj, ('h', 0x20FF), ('h', 0x04C0), ('h', 0x21FF), ('h', 0x02C9),
                                        ('h', 0x1840), *[('h', 0x30FF)] * 8, ('h', 0x3001), ('h', 0xC0F6),
                                        ('h', 0x6018)),  # stmia r0!, {r1, r2, r4-r7}; str r0, [r3]
                'ldmia base constant': (obj, ('h', 0x20FF), ('h', 0x04C0), ('h', 0x21FF), ('h', 0x02C9),
                                        ('h', 0x1840), *[('h', 0x30FF)] * 8, ('h', 0x3001), ('h', 0xC8F6),
                                        ('h', 0x6018)),  # ldmia r0!, {r1, r2, r4-r7}; str r0, [r3]
                # STR forces word alignment: str r1, [r3, #1 (r2)] writes the word at r3.
                'misaligned str': (obj, ('h', 0x2180), ('h', 0x2201), ('h', 0x5099), ('h', 0x681C), *inside,
                                   ('h', 0x601C)),
                # LDRH [odd] is the halfword at odd - 1 rotated right by 8: bytes 8, 0x15 read as 0x08000015.
                'misaligned ldrh': (obj, ('h', 0x2108), ('h', 0x7019), ('h', 0x2115), ('h', 0x7059), ('h', 0x2201),
                                    ('h', 0x5A9C), ('h', 0x605C)),
                # Through a loaded pointer the alignment is unknown, so the rotated form is possible too;
                # and the reload through the same unchanged register is no premise case.
                'misaligned ldrh through a pointer': (obj, ('h', 0x689D), ('h', 0x2108), ('h', 0x7029), ('h', 0x2115),
                                                      ('h', 0x7069), ('h', 0x886C), ('h', 0x605C)),
                # LDRSH [odd] is LDRSB: 0x80 reads as 0xFFFFFF80, and minus 0xF7FFFF6B that is 0x08000015.
                'misaligned ldrsh': (obj, ('h', 0x2180), ('h', 0x7019), ('h', 0x7059), ('h', 0x2201), ('h', 0x5E9C),
                                     ('h', 0x25F8), ('h', 0x062D), ('h', 0x3D95), ('h', 0x1B64), ('h', 0x605C)),
                # LDR [r3 + 1] rotates the stored word 8 to 0x08000000: exact, so never a premise case.
                'misaligned ldr': (obj, ('h', 0x2108), ('h', 0x6019), ('h', 0x2201), ('h', 0x589C), ('h', 0x3415),
                                   ('h', 0x605C)),
                # A reload through the same unchanged loaded pointer reads the store back: no premise,
                # nor through a copy of that pointer (adds r5, r0, #0).
                'same-pointer reload': (obj, ('h', 0x685D), ('h', 0x2180), ('h', 0x6029), ('h', 0x682C), *inside,
                                        ('h', 0x609C)),
                'reload through a copy': (obj, ('h', 0x6858), ('h', 0x689E), ('h', 0x2180), ('h', 0x6001),
                                          ('h', 0x1C05), ('h', 0x682C), *inside, ('h', 0x6034)),
                # IWRAM repeats every 32 KiB.
                'IWRAM mirror': (obj, ('h', 0x2503), ('h', 0x062D), ('h', 0x2601), ('h', 0x03F6), ('h', 0x1976),
                                 ('h', 0x2180), ('h', 0x6029), ('h', 0x6834), *inside, ('h', 0x601C)),
                # SRAM has an 8-bit bus: a word read repeats the byte, so a stored 8 reads as 0x08080808.
                'SRAM word read': (obj, ('h', 0x25E0), ('h', 0x052D), ('h', 0x2108), ('h', 0x7029), ('h', 0x682C),
                                   ('h', 0x601C)),
                # ... and the CPU rotates an odd halfword read on top (mGBA's GBALoad16): 8 stored at
                # 0x0E000001 reads back through ldrh [r5, r2] as 0x08000008, ...
                'SRAM odd ldrh': (obj, ('h', 0x25E0), ('h', 0x052D), ('h', 0x2108), ('h', 0x7069), ('h', 0x2201),
                                  ('h', 0x5AAC), ('h', 0x601C)),
                # ... and an odd ldrsh is ldrsb: 0x80 reads as 0xFFFFFF80, minus 0xF7FFFF6B is 0x08000015.
                'SRAM odd ldrsh': (obj, ('h', 0x25E0), ('h', 0x052D), ('h', 0x2180), ('h', 0x7069), ('h', 0x2201),
                                   ('h', 0x5EAC), ('h', 0x26F8), ('h', 0x0636), ('h', 0x3E95), ('h', 0x1BA4),
                                   ('h', 0x601C)),
                # An 8-bit store to palette RAM or BG VRAM fills both halves of the halfword: 0x0808 << 16.
                'palette byte store': (obj, ('h', 0x2505), ('h', 0x062D), ('h', 0x2108), ('h', 0x7029),
                                       ('h', 0x882C), ('h', 0x0424), ('h', 0x601C)),
                'BG VRAM byte store': (obj, ('h', 0x2506), ('h', 0x062D), ('h', 0x2108), ('h', 0x7069),
                                       ('h', 0x882C), ('h', 0x0424), ('h', 0x601C)),
                # ... so one byte stored through a loaded pointer may fill both halves read at 0x05000000.
                'wild byte store fills two lanes': (obj, ('h', 0x6858), ('h', 0x2108), ('h', 0x7001), ('h', 0x2505),
                                                    ('h', 0x062D), ('h', 0x882C), ('h', 0x0424), ('h', 0x601C)),
                # An 8-bit store to OAM is ignored, so the word stored there before is still there.
                'OAM byte store ignored': (obj, ('h', 0x2507), ('h', 0x062D), ('h', 0x2180), ('h', 0x6029),
                                           ('h', 0x689A), ('h', 0x702A), ('h', 0x682C), *inside, ('h', 0x601C)),
                # At 0x06010000 an 8-bit store may be a BG or an OBJ store (the display mode decides), so
                # the word stored there before may still be there.
                'VRAM byte store either way': (obj, ('h', 0x2560), ('h', 0x012D), ('h', 0x3501), ('h', 0x042D),
                                               ('h', 0x2180), ('h', 0x6029), ('h', 0x689A), ('h', 0x702A),
                                               ('h', 0x682C), *inside, ('h', 0x601C)),
                # A word read through the pointer an SRAM byte was stored through may repeat that byte.
                'SRAM word read through a pointer': (obj, ('h', 0x685D), ('h', 0x2108), ('h', 0x7029), ('h', 0x682C),
                                                     ('h', 0x601C)),
                # After stmia r0!, r0 may alias the store it just made from anywhere (here r0 - 4).
                'reload after writeback': (obj, ('h', 0x6858), ('h', 0x2180), ('h', 0xC002), ('h', 0x2200),
                                           ('h', 0x3A04), ('h', 0x5884), *inside, ('h', 0x601C))}.items():
            f = build(tail=tail)
            with self.subTest(label), self.assertRaisesRegex(ValueError, stored):
                verify(f)
            with self.subTest(label), self.assertRaisesRegex(ValueError, stored):
                premises(f)
        # The +4 control of the first case is refused the same way.
        with self.assertRaisesRegex(ValueError, stored):
            verify(build(tail=(obj, ('h', 0x2504), ('h', 0x2180), ('h', 0x5159), ('h', 0x1D1E), ('h', 0x6834),
                               *inside, ('h', 0x601C))))
        # The cartridge ROM ignores writes, so a load from a ROM object reads no stored byte: neither a
        # wild store nor its own stores reach it. The GPIO port and the 0x0D window (where an EEPROM
        # may answer) are no fixed byte, so bytes stored there may be read back.
        reload = (('h', 0x680C), ('h', 0x1C03), ('h', 0x601C))  # ldr r4, [r1]; movs r3, r0; str r4, [r3]
        assemble = (('h', 0x2215), ('h', 0x700A), ('h', 0x2200), ('h', 0x704A), ('h', 0x708A), ('h', 0x2208),
                    ('h', 0x70CA))  # [r1] = 0x15, 0, 0, 8
        with_object(0x08400000, (('ldr', 3, 'object'), ('h', 0x6858), ('h', 0x2208), ('h', 0x6002), *reload))
        with_object(0x08400000, (*assemble, *reload))
        # ... nor does a load through a pointer read from it: no stored byte exists to be read back.
        with_object(0x08400000, (*assemble, ('ldr', 3, 'object'), ('h', 0x689D), ('h', 0x682C), ('h', 0x6004)))
        with self.subTest('GPIO port'), self.assertRaisesRegex(ValueError, stored):
            with_object(0x080000C4, (*assemble, *reload))
        # The same bytes at 0x0D000000, reached as the ROM object plus an exact index (r2 = 0x04C00000)
        # rather than through a data symbol in that window (kit #406 refuses one there).
        index = (('h', 0x224C), ('h', 0x0512), ('h', 0x2515), ('h', 0x548D), ('h', 0x3201), ('h', 0x2500),
                 ('h', 0x548D), ('h', 0x3201), ('h', 0x548D), ('h', 0x3201), ('h', 0x2508), ('h', 0x548D),
                 ('h', 0x3A03))  # r2 = 0x4C << 20; [r1 + r2 + 0..3] = 0x15, 0, 0, 8; r2 -= 3
        with self.subTest('0x0D window'), self.assertRaisesRegex(ValueError, stored):
            with_object(0x08400000, (*index, ('h', 0x588C), ('h', 0x1C03), ('h', 0x601C)))  # ldr r4, [r1, r2]
        # Mirrors fold to one byte; SRAM and the unused regions are no fixed byte.
        self.assertIsNone(thunks.canonical(0x0A0000C9))
        self.assertEqual(thunks.canonical(0x0A0000CA), 0x080000CA)
        self.assertIsNone(thunks.canonical(0x0D000000))
        self.assertTrue(thunks.rom(0x09FFFFFF))
        self.assertFalse(thunks.rom(0x0A000000) or thunks.rom(None))
        self.assertEqual(thunks.canonical(0x02042000), 0x02002000)
        self.assertEqual(thunks.canonical(0x1_02001FFC), 0x02001FFC)
        self.assertEqual(thunks.canonical(0x03FF8004), 0x03000004)
        self.assertEqual(thunks.canonical(0x0601C000), 0x06014000)
        self.assertEqual(thunks.canonical(0x0C000010), 0x08000010)
        self.assertEqual(thunks.canonical(0x0412_0802), 0x04000802)
        self.assertIsNone(thunks.canonical(0x0E000000))
        self.assertIsNone(thunks.canonical(0x01000000))
        # Two accesses through one unknown register overlap by alignment: strh [r+8] and ldrh [r+10]
        # never share a byte, ldr [r+2] and strb [r+0] may (an aligned word at r + 2 - 2).
        self.assertFalse(thunks.may_overlap((8, 2), (10, 2)))
        self.assertTrue(thunks.may_overlap((0, 1), (2, 4)))
        self.assertTrue(thunks.may_overlap((1, 2), (0, 1)))
        # When no premise helps, the sound walk's reason is reported: the bound of the reload through
        # r5 reaches the ROM, and relaxed it is still a constant-derived thunk register.
        with self.assertRaisesRegex(ValueError, 'thunk target register can hold a local code address'):
            premises(build(post=(obj, ('h', 0x681D), ('h', 0x2180), ('h', 0x6019), ('h', 0x682A))))
        # STMIA stores a listed base: its constant makes every later load constant-derived.
        with self.assertRaisesRegex(ValueError, 'holds a constant-derived value'):
            verify(build(post=(('ldr', 0, 'object'), ('h', 0xC001), ('ldr', 2, 'object'), ('h', 0x6812))))

    def test_writeback_loops_end_and_calls_clear_aliases(self):
        # A zero fill through a loaded pointer with stmia writeback in a loop (agbcc's *p++ = 0)
        # reaches a fixed point: the base's alias entries collapse once it moves.
        fill = (('h', 0x2100), ('h', 0x2208), ('label', 'again'), ('h', 0xC002), ('h', 0x3A01), ('h', 0x2A00),
                ('bhi', 'again'))  # movs r1, #0; movs r2, #8; again: stmia r0!, {r1}; subs; cmp; bhi
        joins = []

        def bounded(old, new):  # fails fast where a walk would never reach its fixed point
            joins.append(1)
            self.assertLess(len(joins), 2000, 'the walk keeps finding new memory states')
            return join_memory(old, new)
        join_memory = thunks.join_memory
        with patch.object(thunks, 'join_memory', bounded):
            verify(build(tail=(('ldr', 3, 'object'), ('h', 0x6858), *fill)))  # r0 = [r3 + 4]
            self.assertEqual(premises(build(tail=(('ldr', 3, 'object'), ('h', 0x6858), *fill))), ())
        # Through a constant base the pointer keeps changing, so the widening taints it, as it does for
        # the same loop written with str and adds.
        for label, step in {'stmia': (('h', 0xC002),), 'str and adds': (('h', 0x6001), ('h', 0x3004))}.items():
            with self.subTest(label), self.assertRaisesRegex(ValueError, 'a local code address cannot be stored'):
                verify(build(tail=(('ldr', 0, 'object'), ('h', 0x2100), ('h', 0x2208), ('label', 'again'), *step,
                                   ('h', 0x3A01), ('h', 0x2A00), ('bhi', 'again'))))
        # A call replaces r0, so a store through the old r0 does not exclude the load through the new
        # one: the premise is offered and recorded.
        after_call = build(tail=(('ldr', 3, 'object'), ('h', 0x6858), ('h', 0x689E), ('h', 0x2180), ('label', 'store'),
                                 ('h', 0x6001), ('bl', CALLEE), ('label', 'reload'), ('h', 0x6804), ('h', 0x0524),
                                 ('h', 0x3415), ('h', 0x6034)))
        self.assertEqual(premises(after_call), ((after_call[1]['reload'], (after_call[1]['store'],)),))
        # A copy from a ROM table in two ldmia: after the first writeback the base is a ROM address,
        # tainted as kit main taints adds r1, #4 on it, so the second load cannot be stored. One ldmia
        # of both words, or an offset load, keeps the base and is admitted.
        copy_out = (('h', 0x1C03), ('h', 0xC314))  # movs r3, r0; stmia r3!, {r2, r4}
        with self.assertRaisesRegex(ValueError, 'a local code address cannot be stored'):
            with_object(0x08400000, (('h', 0xC904), ('h', 0xC910), *copy_out))  # ldmia r1!, {r2}; ldmia r1!, {r4}
        with_object(0x08400000, (('h', 0xC914), *copy_out))  # ldmia r1!, {r2, r4}
        with_object(0x08400000, (('h', 0x680A), ('h', 0x684C), *copy_out))  # ldr r2, [r1]; ldr r4, [r1, #4]
        # An 8-bit store to OAM leaves no byte, so the premise does not name it.
        with_oam = build(tail=(('ldr', 3, 'object'), ('h', 0x6858), ('h', 0x689E), ('h', 0x2180), ('label', 'store'),
                               ('h', 0x6001), ('h', 0x2507), ('h', 0x062D), ('h', 0x7029), ('bl', CALLEE),
                               ('label', 'reload'), ('h', 0x6804), ('h', 0x0524), ('h', 0x3415), ('h', 0x6034)))
        self.assertEqual(premises(with_oam), ((with_oam[1]['reload'], (with_oam[1]['store'],)),))

    def test_constant_bytes_cover_every_value(self):
        self.assertEqual(thunks.byte_range((7, 8), 0), (7, 8))
        self.assertEqual(thunks.byte_range((0x0700, 0x08FF), 1), (7, 8))
        self.assertEqual(thunks.byte_range((0x07FF, 0x0800), 0), (0, 0xFF))
        self.assertEqual(thunks.byte_range((0x12345678, 0x12345678), 2), (0x34, 0x34))
        self.assertEqual(thunks.byte_range((0, 0xFFFFFFFF), 3), (0, 0xFF))
        old = (((0x100, (4, 4)), (0x101, (0, 0))), (1, 1), 1, frozenset({2}), frozenset({(1, 0, 0, 4)}))
        new = (((0x100, (0x80, 0x80)), (0x102, (9, 9))), None, 0, frozenset({4}), frozenset({(2, 0, 4, 1)}))
        joined = (((0x100, (4, 0x80)), (0x101, (0, 0)), (0x102, (9, 9))), (1, 1), 1, frozenset({2, 4}),
                  frozenset({(1, 0, 0, 4), (2, 0, 4, 1)}))
        self.assertEqual(thunks.join_memory(old, new), joined)
        self.assertEqual(thunks.join_memory(new, old), joined)
        self.assertEqual(thunks.join_memory(thunks.CLEAN, old), old)

    def test_a_reload_through_a_loaded_pointer_needs_its_load_bearing_premise(self):
        # r5 = [&g_right] is a loaded pointer; the constant 0x80 is stored at the object, then a word
        # is read through r5, shifted into the ROM and stored. Only the premise that the load at
        # `reload` reads back no byte stored as a constant (at `store`) admits it.
        def shape(value, *after):
            return build(tail=(('ldr', 3, 'object'), ('h', 0x681D), ('h', 0x2100 | value), ('label', 'store'),
                               ('h', 0x6019), ('label', 'reload'), ('h', 0x682C), *after))
        f = shape(0x80, ('h', 0x0524), ('h', 0x3415), ('h', 0x601C))
        body, labels, manifest = f
        record = ((labels['reload'], (labels['store'],)),)
        self.assertEqual(premises(f), record)
        # Bytes 8 and 0x15 stored at exact addresses may be read back through a pointer of unknown
        # alignment as a rotated halfword, 0x08000008 or more, so that load needs its premise too.
        rotated = build(tail=(('ldr', 3, 'object'), ('h', 0x2108), ('label', 'first'), ('h', 0x7019), ('h', 0x2115),
                              ('label', 'second'), ('h', 0x7059), ('h', 0x689D), ('label', 'reload'), ('h', 0x882C),
                              ('h', 0x605C)))  # strb 8, [r3]; strb 0x15, [r3, #1]; ldrh r4, [[r3 + 8]]
        self.assertEqual(premises(rotated), ((rotated[1]['reload'], (rotated[1]['first'], rotated[1]['second'])),))
        with self.assertRaisesRegex(ValueError, 'a thunk store premise is required: \\* thunk store premise: '
                                    f'the load at 0x{BASE + labels["reload"]:08X} through a non-exact address'):
            verify(f)
        with self.assertRaisesRegex(ValueError, 'a thunk store premise is required'):
            leaf(f, switch_thunks=PLAIN)
        premised = dict(manifest, store_premises=thunks.premise_manifest(record))
        verify(f, premised)
        self.assertEqual(thunks.premise_lines(BASE, premised), [
            f'* thunk store premise: the load at 0x{BASE + labels["reload"]:08X} through a non-exact address '
            f'reads back no byte this function stored as a constant (stores at 0x{BASE + labels["store"]:08X})'])
        # A different or extra record, or a malformed one, is refused.
        for label, records in {'other load': [[labels['reload'] + 2, [labels['store']]]],
                               'other store': [[labels['reload'], [labels['store'] + 2]]],
                               'extra record': [[labels['reload'], [labels['store']]],
                                                [labels['reload'] + 2, [labels['store']]]]}.items():
            with self.subTest(label), self.assertRaisesRegex(ValueError, 'premises differ'):
                verify(f, dict(manifest, store_premises=records))
        for records in ([], [[labels['reload'], []]], [[labels['reload'], [labels['store']] * 2]],
                        [[labels['reload'] + 1, [labels['store']]]], [[labels['reload'], labels['store']]],
                        [[float(labels['reload']), [labels['store']]]], {}):
            with self.subTest(records=records), self.assertRaisesRegex(ValueError, 'invalid thunk store premises'):
                verify(f, dict(manifest, store_premises=records))
        # Not load-bearing: the same reload of a small constant is admitted by the sound walk,
        # so it records no premise, and a manifest that claims one is refused.
        small = shape(0x04, ('h', 0x601C))
        self.assertEqual(premises(small), ())
        verify(small)
        with self.assertRaisesRegex(ValueError, 'premises differ'):
            verify(small, dict(small[2], store_premises=[[small[1]['reload'], [small[1]['store']]]]))
        # Only the loads the verdict needs: an earlier reload through r5 into a register that is
        # never used again could also hold the ROM word, but the verdict does not depend on it.
        both = build(tail=(('ldr', 3, 'object'), ('h', 0x681D), ('h', 0x2180), ('label', 'store'), ('h', 0x6019),
                           ('label', 'unused'), ('h', 0x682E), ('label', 'reload'), ('h', 0x682C),
                           ('h', 0x0524), ('h', 0x3415), ('h', 0x601C)))  # ldr r6, [r5] is never read
        self.assertEqual(premises(both), ((both[1]['reload'], (both[1]['store'],)),))
        # A premise never admits what the sound walk refuses at an exact address.
        with self.assertRaisesRegex(ValueError, 'a local code address cannot be stored'):
            premises(build(tail=(('ldr', 3, 'object'), ('h', 0x2180), ('h', 0x6019), ('h', 0x681C),
                                 ('h', 0x0524), ('h', 0x601C))))
        # The premise option is only for the thunk selectors.
        with self.assertRaisesRegex(ValueError, 'premises require their switch thunk selector'):
            match.verify_leaf_instructions(bytes(body), BASE, True, {}, switch_thunk_premises=thunks.StorePremises())

    def test_identity_operations_are_moves(self):
        # A call result copied with adds rd, rs, #0, stored, then a callback loaded: no constant contributes.
        def copy_store(copy):
            return dict(post=(('bl', CALLEE), ('h', copy), ('ldr', 3, 'object'), ('h', 0x601C),
                              ('ldr', 2, 'object'), ('h', 0x6812)))
        verify(build(**copy_store(0x1C04)))  # adds r4, r0, #0
        verify(build(**copy_store(0x0004)))  # lsls r4, r0, #0
        # A nonzero immediate on the same loaded value is constant-derived and stays refused.
        for label, copy in {'adds #1': 0x1C44, 'subs #1': 0x1E44}.items():
            with self.subTest(label), self.assertRaisesRegex(ValueError, 'constant-derived'):
                verify(build(**copy_store(copy)))
        # A constant copied by an identity operation stays constant, and a thunk register may not hold one.
        for label, copy in {'adds #0': 0x1C1A, 'lsls #0': 0x001A}.items():  # r2 = r3 (the object address)
            with self.subTest(label), self.assertRaisesRegex(ValueError, 'constant-derived'):
                leaf(build(post=(('ldr', 3, 'object'), ('h', copy))), switch_thunks=PLAIN)
        # Taint survives identity operations.
        with self.assertRaisesRegex(ValueError, 'can hold a local code address'):
            leaf(build(post=(('ldr', 3, 'object'), ('h', 0x1C02), ('h', 0x0012))), switch_thunks=PLAIN)

    def test_only_armv4t_16_bit_encodings_are_admitted(self):
        verify(build(tail=(('h', 0x46C0), ('h', 0x4640))))
        for label, half in {'uxtb': 0xB2D2, 'sxth': 0xB212, 'rev': 0xBA12, 'cps': 0xB662, 'setend': 0xB650,
                            'nop hint': 0xBF00, 'yield': 0xBF10, 'sev': 0xBF40, 'blx register': 0x4790,
                            'stm base not lowest': 0xC418, 'low mov': 0x4612, 'low cmp': 0x4512, 'low add': 0x4412}.items():
            with self.subTest(label), self.assertRaisesRegex(
                    ValueError, 'not a validated external direct Thumb BL' if label == 'blx register'
                    else 'not an ARMv4T encoding'):
                verify(build(tail=(('h', half),)))
            with self.subTest(label), self.assertRaisesRegex(ValueError, '16-bit ARMv4T'):
                from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
                decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB); decoder.detail = True
                item = next(decoder.disasm(half.to_bytes(2, 'little'), BASE))
                thunks.verify_thunk_targets({BASE: item}, {BASE: ()}, BASE, {}, BASE + 8)

    def test_leaf_context_is_isolated(self):
        f = build(); frame = build(frame=True)
        for key, value in [('allow_switch_constants', True), ('function_thunk_context', {}),
                           ('typed_switch_outgoing_frame', 'typed-outgoing-six-words-v1'),
                           ('acyclic_state_budget', 10), ('preloaded_switch', True),
                           ('switch_interposed_pool', True), ('allow_switch_scalar_frame', True),
                           ('self_calls', frozenset({BASE}))]:
            with self.subTest(key=key), self.assertRaises(ValueError):
                leaf(f, switch_thunks=PLAIN, **{key: value})
        for selector in (None, '', 'canonical-thunks-v1', 'switch-thunks-v2', 1):
            if selector is None:
                continue
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                leaf(f, switch_thunks=selector)
        # The frame flags must agree with the selector in both directions.
        with self.assertRaises(ValueError):
            leaf(frame, switch_thunks=FRAMED)
        with self.assertRaises(ValueError):
            leaf(f, switch_thunks=FRAMED, switch_outgoing_stack=pool_switch_frame.STACK_POLICY,
                 switch_outgoing_stack_fixed_pool=True)
        with self.assertRaises(ValueError):
            leaf(frame, switch_thunks=PLAIN, switch_outgoing_stack=pool_switch_frame.STACK_POLICY,
                 switch_outgoing_stack_fixed_pool=True)
        leaf(frame, switch_thunks=FRAMED, switch_outgoing_stack=pool_switch_frame.STACK_POLICY,
             switch_outgoing_stack_fixed_pool=True)

    def test_binding_opt_in_is_isolated(self):
        for arguments in ((PLAIN, False, False), (PLAIN, True, True), ('other', True, False),
                          (PLAIN, True, False, True), (PLAIN, True, False, None, True)):
            with self.subTest(arguments=arguments), self.assertRaises(ValueError):
                match.check_switch_thunk_opt_in(*arguments)
        match.check_switch_thunk_opt_in(PLAIN, True, False, False)
        match.check_switch_thunk_opt_in(None, False, False)

    def test_selectors_use_the_isolated_fixed_configuration(self):
        for selector in thunks.SELECTORS:
            args = SimpleNamespace(
                switch_data_profile=selector,
                mode='thumb', control_flow_profile='ordinary', signed_quotient_profile=None,
                signed_runtime_profile=None, addressed_signed_runtime_profile=None,
                unsigned_runtime_profile=None, software_double_profile=None,
                software_double_remainder_profile=None, function_address_profile=None,
                switch_profile=None, owner_runtime_profile=None,
                cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
            match.switch_u16_scalar_configuration(args)
            # The two thunk families cannot be combined through their command-line selectors.
            args.function_address_profile = 'canonical-thunks-v1'
            with self.subTest(selector=selector), self.assertRaisesRegex(ValueError, 'isolated explicit selector'):
                match.switch_u16_scalar_configuration(args)


class EndToEndTests(unittest.TestCase):
    def test_compiled_switch_matches_and_relabels_fail(self):
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH', ROOT / 'build'))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix='switch_thunks_', dir=scratch)
        self.addCleanup(directory.cleanup)
        root = Path(directory.name)
        for name in ('src', 'include', 'config', 'symbols'):
            (root / name).mkdir()
        environment = {key: value for key, value in os.environ.items() if key != 'FFTA_ROM'}
        environment.update(TMPDIR=str(root), PYTHONDONTWRITEBYTECODE='1')
        with patch.dict(os.environ, environment, clear=True):
            source = root / 'src/08000000.c'
            source.write_text(SOURCE)
            objects = json.dumps({'data_02000100': '0x02000100', 'data_02000200': '0x02000200'}).encode()
            (root / 'config/data_symbols.json').write_bytes(objects)
            rom = bytearray(ROM_SIZE)
            struct.pack_into('<HH', rom, THUNK_R2 - BASE, 0x4710, 0x46C0)
            args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                                      objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD,
                                      flags=match.DEFAULT_FLAGS)
            runner = match.Runner(match.DEFAULT_CC, root=root, timeout=120)
            with runner.workspace() as workspace:
                _, _, original = match.compile_object(runner, workspace, args, root, BASE, 'src/08000000.c')
                symbol, _ = match.function_record(original, 'func_08000000', BASE, True)
                entries = [(BASE, symbol['size']), (BASE + 0x400, 2), (BASE + 0x410, 2)]
                functions = json.dumps([{'rom': f'0x{start:08X}', 'end': f'0x{start + size:08X}',
                                         'mode': 'thumb'} for start, size in entries]).encode()
                (root / 'config/functions.json').write_bytes(functions)
                (root / 'symbols/functions.txt').write_text(''.join(
                    f'{start:08X} {start + size:08X} {size} 1 return\n' for start, size in entries))
                body, calls, _ = match.link_calls(runner, workspace, args, original, BASE, functions, len(rom),
                                                  bytes(rom), objects, {}, {}, allow_switch_data=True,
                                                  switch_thunks=PLAIN)
            self.assertIn(THUNK_R2, calls.values())
            rom[:len(body)] = body
            (root / 'baserom.bin').write_bytes(rom)

            def run(*selector):
                output = io.StringIO()
                with patch.object(sys, 'argv', ['match.py', '--root', str(root), '0x08000000',
                                                *selector, '--no-write']), \
                        patch.object(match, 'ROOT', match.ROOT), contextlib.redirect_stdout(output):
                    try:
                        result = match.main()
                    except SystemExit as error:
                        result = error.code
                return result, output.getvalue()
            verdict = 'verdict MATCH - byte identical'
            result, output = run('--switch-data-profile', PLAIN)
            self.assertIn(verdict, output.splitlines(), result)
            # Other selectors and the default refuse the same source; a frame selector has no frame.
            for selector in ((), ('--switch-data-profile', 'u16-scalars-v1'),
                             ('--switch-data-profile', FRAMED),
                             ('--switch-data-profile', 'u16-scalars-functions-v1'),
                             ('--function-address-profile', 'canonical-thunks-v1')):
                result, output = run(*selector)
                with self.subTest(selector=selector):
                    self.assertNotIn(verdict, output.splitlines())
            # A source that names the thunk, by its name or its address, is not a compiler-emitted thunk.
            for text, message in ((FORGED, 'call-via identifiers are reserved for compiler emission'),
                                  (NAMED, 'compile failed')):
                source.write_text(text)
                for selector in thunks.SELECTORS:
                    result, output = run('--switch-data-profile', selector)
                    with self.subTest(selector=selector, message=message):
                        self.assertNotIn(verdict, output.splitlines())
                        if selector == thunks.music.SELECTOR:
                            self.assertIn('isolated fixed old-agbcc unit', str(result))
                        else:
                            self.assertIn(message, str(result))
            source.write_text(SOURCE)
            # The saved report replays and selects exactly one selector.
            result, output = run('--switch-data-profile', PLAIN)
            self.assertIn(verdict, output.splitlines(), result)
            output = io.StringIO()
            with patch.object(sys, 'argv', ['match.py', '--root', str(root), '0x08000000',
                                            '--switch-data-profile', PLAIN]), \
                    patch.object(match, 'ROOT', match.ROOT), contextlib.redirect_stdout(output):
                match.main()
            report = (root / 'docs/match/08000000.md').read_text()
            self.assertEqual(thunks.selector_for_report(report), PLAIN)
            import rebuild
            self.assertEqual(rebuild.saved_profile_arguments(report, str(root), BASE),
                             ['--switch-data-profile', PLAIN])
            self.assertTrue(evidence.report_matches(report, str(root), BASE))
            relabelled = report.replace(thunks.SCHEMAS[PLAIN], thunks.SCHEMAS[FRAMED]).replace(
                thunks.SUMMARIES[PLAIN], thunks.SUMMARIES[FRAMED])
            self.assertFalse(evidence.report_matches(relabelled, str(root), BASE))
            relabelled = report.replace(thunks.SCHEMAS[PLAIN], evidence.SWITCH_U16_SCALAR_SCHEMA)
            self.assertFalse(evidence.report_matches(relabelled, str(root), BASE))
            # Replay with the source changed no longer matches.
            source.write_text(SOURCE + '\n')
            self.assertFalse(evidence.report_matches(report, str(root), BASE))


    def test_a_load_bearing_store_premise_is_written_and_replayed(self):
        # kit #393: match.py derives the premise, records it in the manifest and states it once.
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH', ROOT / 'build'))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix='switch_thunks_premise_', dir=scratch)
        self.addCleanup(directory.cleanup)
        root = Path(directory.name)
        for name in ('src', 'include', 'config', 'symbols'):
            (root / name).mkdir()
        environment = {key: value for key, value in os.environ.items() if key != 'FFTA_ROM'}
        environment.update(TMPDIR=str(root), PYTHONDONTWRITEBYTECODE='1')
        with patch.dict(os.environ, environment, clear=True):
            (root / 'src/08000000.c').write_text(PREMISED)
            objects = json.dumps({f'data_{value:08X}': f'0x{value:08X}' for value in
                                  (0x02000100, 0x02000200, 0x02000300, 0x02000304, 0x02000308)}).encode()
            (root / 'config/data_symbols.json').write_bytes(objects)
            rom = bytearray(ROM_SIZE)
            struct.pack_into('<HH', rom, THUNK_R2 - BASE, 0x4710, 0x46C0)
            args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                                      objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD,
                                      flags=match.DEFAULT_FLAGS)
            runner = match.Runner(match.DEFAULT_CC, root=root, timeout=120)
            with runner.workspace() as workspace:
                _, _, original = match.compile_object(runner, workspace, args, root, BASE, 'src/08000000.c')
                symbol, _ = match.function_record(original, 'func_08000000', BASE, True)
                entries = [(BASE, symbol['size']), (BASE + 0x400, 2), (BASE + 0x410, 2)]
                functions = json.dumps([{'rom': f'0x{start:08X}', 'end': f'0x{start + size:08X}',
                                         'mode': 'thumb'} for start, size in entries]).encode()
                (root / 'config/functions.json').write_bytes(functions)
                (root / 'symbols/functions.txt').write_text(''.join(
                    f'{start:08X} {start + size:08X} {size} 1 return\n' for start, size in entries))
                body, _, _ = match.link_calls(runner, workspace, args, original, BASE, functions, len(rom),
                                              bytes(rom), objects, {}, {}, allow_switch_data=True,
                                              switch_thunks=PLAIN)
            rom[:len(body)] = body
            (root / 'baserom.bin').write_bytes(rom)
            output = io.StringIO()
            with patch.object(sys, 'argv', ['match.py', '--root', str(root), '0x08000000',
                                            '--switch-data-profile', PLAIN]), \
                    patch.object(match, 'ROOT', match.ROOT), contextlib.redirect_stdout(output):
                match.main()
            self.assertIn('verdict MATCH - byte identical', output.getvalue().splitlines())
            report = (root / 'docs/match/08000000.md').read_text()
            stated = [line for line in report.splitlines() if line.startswith('* thunk store premise:')]
            self.assertEqual(len(stated), 1, report)
            self.assertRegex(stated[0], r'^\* thunk store premise: the load at 0x080000[0-9A-F]{2} through a '
                                        r'non-exact address reads back no byte this function stored as a '
                                        r'constant \(stores at 0x080000[0-9A-F]{2}(, 0x080000[0-9A-F]{2})*\)$')
            self.assertIn('"store_premises":', report)
            self.assertTrue(evidence.report_matches(report, str(root), BASE))
            self.assertFalse(evidence.report_matches(report.replace(stated[0] + '\n', ''), str(root), BASE))


class ReportTests(unittest.TestCase):
    def lines(self, fixture, selector, *, manifest=None, schema=None, extra=()):
        body, _, expected = fixture
        manifest = expected if manifest is None else manifest
        # A manifest stripped of its thunk marker is signed as the thunk-free family would.
        proof = (thunks.fingerprint if 'thunk_policy' in manifest else
                 evidence.switch_multiple_data_fingerprint)(BASE, bytes(body), manifest)
        result = [f'* verification: `{schema or thunks.SCHEMAS[selector]}`',
                  f'* source SHA-256: `{self.source}`',
                  f'* mapping SHA-256: `{evidence.mapping_fingerprint(mapping(body))}`',
                  f'* data symbols SHA-256: `{evidence.mapping_fingerprint(self.objects)}`',
                  f'* switches: {thunks.SUMMARIES[selector]}',
                  '* source plausibility: plausible', '* relocations: none',
                  '* verified extent: complete ELF function symbol, including literal pools',
                  f'* compiled : `{bytes(body).hex()}`',
                  f'* switch manifest: `{evidence.switch_manifest(manifest)}`',
                  f'* switch proof SHA-256: `{proof}`',
                  f'* control flow: {evidence.CALL_SUMMARY}',
                  f'* ROM bytes: `{bytes(body).hex()}` ({len(body)} bytes)',
                  f'**MATCH - byte identical** - {len(body)}/{len(body)} bytes']
        if selector == FRAMED:
            result.append(f'* stack frame: {evidence.STACK_SUMMARY}')
        return result + list(extra)

    def test_report_replay_relabel_and_selector_recovery_fail_closed(self):
        import rebuild
        self.objects = json.dumps(OBJECTS).encode(); self.source = 'a' * 64
        for selector, f in ((PLAIN, build()), (PLAIN, build(scalar=True)), (FRAMED, build(frame=True))):
            body, _, manifest = f
            entries = mapping(body)
            with tempfile.TemporaryDirectory(dir=os.environ.get('TMPDIR')) as directory, \
                    self.subTest(selector=selector, scalar='scalar_policy' in manifest):
                rom = Path(directory) / 'synthetic.bin'; rom.write_bytes(rom_image(body))
                with patch.object(evidence, 'mapping_snapshot', return_value=entries), \
                        patch.object(evidence, 'data_snapshot', return_value=self.objects), \
                        patch.object(evidence, 'source_fingerprint', return_value=self.source) as fingerprint, \
                        patch.object(evidence, 'report_rom_path', return_value=str(rom)):
                    def valid(lines):
                        return evidence.switch_report_matches(lines, directory, BASE, data_profile=True)
                    good = self.lines(f, selector)
                    self.assertTrue(valid(good))
                    self.assertEqual(thunks.selector_for_report('\n'.join(good)), selector)
                    instructions, control_flow = match.verify_switches(
                        bytes(body), BASE, rom_image(body), entries, manifest, data_mapping=self.objects)
                    report_fixtures.source_at(self, f'src/{BASE:08X}.c')
                    complete = report_fixtures.complete(
                        directory, BASE, body, thunks.SCHEMAS[selector], instructions, mapped=True,
                        control_flow=control_flow, data_profile=True, switches=True, switch_evidence=manifest,
                        thunk_switch_selector=selector)
                    self.assertEqual(rebuild.saved_profile_arguments(report_fixtures.carried(complete, directory, BASE), directory, BASE),
                                     ['--switch-data-profile', selector])
                    with self.assertRaisesRegex(ValueError, 'invalid saved profile report'):
                        rebuild.saved_profile_arguments('\n'.join(good), directory, BASE)
                    # Replay refuses a manifest stripped of the marker, even re-signed.
                    bad = copy.deepcopy(manifest); bad.pop('thunk_policy')
                    self.assertFalse(valid(self.lines(f, selector, manifest=bad)))
                    # A re-signed manifest with float facts still fails the exact replay.
                    bad = copy.deepcopy(manifest); bad['dependencies'][0][2] = float(bad['dependencies'][0][2])
                    self.assertFalse(valid(self.lines(f, selector, manifest=bad)))
                    # Relabelling across selectors and to the thunk-free families fails.
                    other = FRAMED if selector == PLAIN else PLAIN
                    for schema in (thunks.SCHEMAS[other], evidence.SWITCH_MULTIPLE_DATA_SCHEMA,
                                   evidence.SWITCH_U16_SCALAR_SCHEMA, evidence.SWITCH_POOL_U16_SCALAR_SCHEMA,
                                   pool_switch_frame.SCHEMA, evidence.SWITCH_FUNCTION_U16_SCALAR_SCHEMA,
                                   evidence.SWITCH_FUNCTION_FRAME_U16_SCALAR_SCHEMA):
                        self.assertFalse(valid(self.lines(f, selector, schema=schema)), schema)
                    with self.assertRaises(ValueError):
                        thunks.selector_for_report('\n'.join(self.lines(f, selector) + [
                            f'* verification: `{thunks.SCHEMAS[other]}`']))
                    # Mixed profile lines and a missing or extra frame line fail.
                    self.assertFalse(valid(good + ['* function addresses: unknown']))
                    self.assertFalse(valid(good[:-1] if selector == FRAMED else
                                           good + [f'* stack frame: {evidence.STACK_SUMMARY}']))
                    fingerprint.return_value = 'b' * 64
                    self.assertFalse(valid(good))
                # kit #393: a load-bearing store premise is stated once, as the manifest records it.
                premised = build(tail=(('ldr', 3, 'object'), ('h', 0x681D), ('h', 0x2180), ('label', 'store'),
                                       ('h', 0x6019), ('label', 'reload'), ('h', 0x682C), ('h', 0x0524),
                                       ('h', 0x3415), ('h', 0x601C)), scalar='scalar_policy' in manifest,
                                 frame=selector == FRAMED)
                if selector == PLAIN and 'scalar_policy' not in manifest:
                    p_body, p_labels, p_manifest = premised
                    with patch.object(evidence, 'mapping_snapshot', return_value=entries), \
                            patch.object(evidence, 'data_snapshot', return_value=self.objects), \
                            patch.object(evidence, 'source_fingerprint', return_value=self.source), \
                            patch.object(evidence, 'report_rom_path', return_value=str(rom)):
                        # A premise line in a report whose manifest needs none fails.
                        line = thunks.premise_lines(BASE, {'store_premises': [[p_labels['reload'],
                                                                               [p_labels['store']]]]})[0]
                        self.assertTrue(evidence.switch_report_matches(good, directory, BASE, data_profile=True))
                        self.assertFalse(evidence.switch_report_matches(good + [line], directory, BASE,
                                                                        data_profile=True))
                    p_manifest = dict(p_manifest, store_premises=thunks.premise_manifest(
                        ((p_labels['reload'], (p_labels['store'],)),)))
                    line = thunks.premise_lines(BASE, p_manifest)[0]
                    rom.write_bytes(rom_image(p_body))
                    with patch.object(evidence, 'mapping_snapshot', return_value=mapping(p_body)), \
                            patch.object(evidence, 'data_snapshot', return_value=self.objects), \
                            patch.object(evidence, 'source_fingerprint', return_value=self.source), \
                            patch.object(evidence, 'report_rom_path', return_value=str(rom)):
                        def replays(lines):
                            return evidence.switch_report_matches(lines, directory, BASE, data_profile=True)
                        stated = self.lines(premised, selector, manifest=p_manifest, extra=[line])
                        self.assertTrue(replays(stated))
                        self.assertFalse(replays(self.lines(premised, selector, manifest=p_manifest)))  # missing
                        self.assertFalse(replays(stated + [line]))  # twice
                        self.assertFalse(replays(self.lines(premised, selector, manifest=p_manifest,
                                                            extra=[line.replace('0x08', '0x09', 1)])))
                        self.assertFalse(replays(self.lines(premised, selector, extra=[line])))  # unrecorded
                        self.assertFalse(replays(self.lines(premised, selector)))  # neither: the walk refuses
                # Thunk-free reports never recover a thunk selector.
                self.assertIsNone(thunks.selector_for_report(
                    f'* verification: `{evidence.SWITCH_U16_SCALAR_SCHEMA}`'))


# Case 1 stores 0x12345678, a literal word no immediate builds: a wide scalar word (switch_wide_scalars).
WIDE = SOURCE.replace('data_02000100 = 0;', 'data_02000100 = (void *)0x12345678;')
# Case 3 stores 0x1234 as well, so the wide word sits beside a u16 scalar word.
WIDE_BESIDE = WIDE.replace('*state = 1;', 'data_02000100 = (void *)0x1234;\n        *state = 1;')


def issue(test, source, objects, entries, selector, *, link, rom_words):
    """Compile `source`, lay it into a ROM beside the `entries` stubs and the `rom_words`, and write its
    report with match.main() under `selector`; returns (root, report text). The environment stays patched
    until the test ends."""
    scratch = Path(os.environ.get('FFTA_TEST_SCRATCH', ROOT / 'build'))
    scratch.mkdir(parents=True, exist_ok=True)
    directory = tempfile.TemporaryDirectory(prefix='switch_wide_', dir=scratch)
    test.addCleanup(directory.cleanup)
    root = Path(directory.name)
    for name in ('src', 'include', 'config', 'symbols'):
        (root / name).mkdir()
    environment = {key: value for key, value in os.environ.items() if key != 'FFTA_ROM'}
    environment.update(TMPDIR=str(root), PYTHONDONTWRITEBYTECODE='1')
    test.enterContext(patch.dict(os.environ, environment, clear=True))
    (root / 'src/08000000.c').write_text(source)
    (root / 'config/data_symbols.json').write_bytes(objects)
    rom = bytearray(max(address + 4 - BASE for address, _ in rom_words))
    for address, words in rom_words:
        struct.pack_into('<HH', rom, address - BASE, *words)
    args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                              objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
    runner = match.Runner(match.DEFAULT_CC, root=root, timeout=120)
    with runner.workspace() as workspace:
        _, _, original = match.compile_object(runner, workspace, args, root, BASE, 'src/08000000.c')
        symbol, _ = match.function_record(original, 'func_08000000', BASE, True)
        spans = [(BASE, symbol['size']), *entries]
        functions = json.dumps([{'rom': f'0x{start:08X}', 'end': f'0x{start + size:08X}', 'mode': 'thumb'}
                                for start, size in spans]).encode()
        (root / 'config/functions.json').write_bytes(functions)
        (root / 'symbols/functions.txt').write_text(''.join(
            f'{start:08X} {start + size:08X} {size} 1 return\n' for start, size in spans))
        body, _, _ = match.link_calls(runner, workspace, args, original, BASE, functions, len(rom), bytes(rom),
                                      objects, {}, {}, allow_switch_data=True, **link)
    rom[:len(body)] = body
    (root / 'baserom.bin').write_bytes(rom)
    output = io.StringIO()
    with patch.object(sys, 'argv', ['match.py', '--root', str(root), '0x08000000',
                                    '--switch-data-profile', selector]), \
            patch.object(match, 'ROOT', match.ROOT), contextlib.redirect_stdout(output):
        test.assertEqual(match.main(), 0, output.getvalue())
    return root, (root / 'docs/match/08000000.md').read_text()


def check_wide_report(test, root, report, schema, u16_words):
    """An issued `schema` report binds 0x12345678 as its one wide word beside `u16_words` u16 words, prints
    the wide-scalar premise once and replays; with that line removed it does not."""
    lines, line, prefix = report.splitlines(), wide_scalars.report_line(), '* switch manifest: `'
    manifest = json.loads(next(text for text in lines if text.startswith(prefix))[len(prefix):-1])
    test.assertIn(f'* verification: `{schema}`', lines)
    test.assertEqual(manifest['wide_scalar_policy'], wide_scalars.POLICY)
    test.assertEqual([value for _, value in manifest['wide_scalars']], [0x12345678])
    test.assertEqual(len(manifest['scalars']), u16_words)
    test.assertEqual(lines.count(line), 1, report)
    test.assertTrue(evidence.report_matches(report, root, BASE))
    test.assertTrue(evidence.switch_report_matches(lines, root, BASE, data_profile=True))
    test.assertFalse(evidence.switch_report_matches([text for text in lines if text != line], root, BASE,
                                                    data_profile=True))
    test.assertFalse(evidence.report_matches(report.replace(line + '\n', ''), root, BASE))


class ThunkWideScalarTests(unittest.TestCase):
    """Wide scalar words (switch_wide_scalars) under the thunk selectors."""

    def test_issued_reports_print_the_premise_and_replay(self):
        objects = json.dumps({'data_02000100': '0x02000100', 'data_02000200': '0x02000200'}).encode()
        for name, source, u16_words in (('beside u16 words', WIDE_BESIDE, 1), ('without u16 words', WIDE, 0)):
            with self.subTest(name):
                root, report = issue(self, source, objects, [(BASE + 0x400, 2), (BASE + 0x410, 2)], PLAIN,
                                     link={'switch_thunks': PLAIN}, rom_words=[(THUNK_R2, (0x4710, 0x46C0))])
                check_wide_report(self, root, report, thunks.SCHEMAS[PLAIN], u16_words)

    def test_a_wide_word_is_a_constant_to_the_thunk_target_walk(self):
        def wide(fixture):
            return dict(fixture[2], scalars=[], wide_scalar_policy=wide_scalars.POLICY,
                        wide_scalars=fixture[2]['scalars'])
        # 0x80000100 names nothing, and as a plain value it binds without a u16 word in both frame variants.
        for frame in (False, True):
            with self.subTest(frame=frame):
                f = build(scalar=True, scalar_value=0x80000100, frame=frame)
                verify(f, wide(f))
        # Shifted right by four it is 0x08000010, inside the caller; copied, it is still no loaded callback.
        for name, half, message in (('lsrs r2, r3, #4', 0x091A, 'local code address'),
                                    ('adds r2, r3, #0', 0x1C1A, 'constant-derived')):
            for frame in (False, True):
                f = build(post=(('ldr', 0, 'object'), ('h', half)), scalar=True, scalar_value=0x80000100,
                          frame=frame)
                with self.subTest(name, frame=frame), self.assertRaisesRegex(ValueError, message):
                    verify(f, wide(f))


class RomMirrorFoldTests(unittest.TestCase):
    """The store model folds the ROM windows through rom_mirror, except where a byte is not fixed."""
    GPIO = range(0xC4, 0xCA)
    SAMPLES = (0, 0xC2, 0xC3, 0xCA, 0xCB, 0x1234, 0x142244, 0xFFFFFF, 0x1000000, 0x10000C4, 0x1FFFFFF)

    def test_the_rom_windows_fold_as_rom_mirror_does(self):
        import rom_mirror
        for window in (0x08000000, 0x0A000000, 0x0C000000):
            for offset in self.SAMPLES:
                if window + offset >= 0x0D000000:
                    continue
                with self.subTest(address=hex(window + offset)):
                    self.assertEqual(thunks.canonical(window + offset), rom_mirror.canonical(window + offset))
                    self.assertEqual(thunks.canonical(window + offset), 0x08000000 + offset)
                    self.assertTrue(thunks.rom(thunks.canonical(window + offset)))
                    self.assertEqual(thunks.canonical(0x100000000 + window + offset), 0x08000000 + offset)

    def test_the_rom_fold_is_rom_mirrors_own(self):
        import rom_mirror
        folded = object()
        with patch.object(rom_mirror, 'canonical', return_value=folded) as fold:
            for address in (0x08000010, 0x0A000010, 0x0BFFFFFF, 0x0C000010, 0x0CFFFFFF):
                with self.subTest(address=hex(address)):
                    self.assertIs(thunks.canonical(address), folded)
                    fold.assert_called_with(address)
            # RAM and video mirrors are this module's own, and an unfixed byte is never folded.
            fold.reset_mock()
            self.assertEqual(thunks.canonical(0x02042000), 0x02002000)
            self.assertIsNone(thunks.canonical(0x0D000010))
            self.assertIsNone(thunks.canonical(0x0A0000C4))
            self.assertIsNone(thunks.canonical(0x0E000000))
            fold.assert_not_called()

    def test_the_0x0D_window_and_the_gpio_port_stay_unfixed_where_rom_mirror_folds_them(self):
        # The one place the two differ: rom_mirror classes a literal word and folds every mirror;
        # the store model names a byte and keeps these unfixed. Neither side may change alone.
        import rom_mirror
        for address in (0x0D000000, 0x0D000010, 0x0D142244, 0x0DFFFF00, 0x0DFFFFFF):
            with self.subTest(address=hex(address)):
                self.assertIsNone(thunks.canonical(address))
                self.assertEqual(rom_mirror.canonical(address), address - 0x04000000)
                self.assertTrue(thunks.rom(rom_mirror.canonical(address)))
        for window in (0x08000000, 0x0A000000, 0x0C000000):
            for offset in self.GPIO:
                with self.subTest(address=hex(window + offset)):
                    self.assertIsNone(thunks.canonical(window + offset))
                    self.assertEqual(rom_mirror.canonical(window + offset), 0x08000000 + offset)

    def test_a_possible_code_address_is_any_word_in_the_rom_or_its_mirrors(self):
        import rom_mirror
        self.assertEqual((thunks.ROM_LOW, thunks.ROM_HIGH), (0x08000000, 0x0E000000))
        self.assertEqual(thunks.ROM_HIGH, rom_mirror.MIRRORS[1])
        for value in (0x08000000, 0x09FFFFFF, 0x0A000000, 0x0C000000, 0x0D000000, 0x0DFFFFFF):
            with self.subTest(value=hex(value)):
                self.assertTrue(thunks.ROM_LOW <= value < thunks.ROM_HIGH)
                self.assertTrue(thunks.rom(rom_mirror.canonical(value)))
        for value in (0x07FFFFFF, 0x0E000000):
            with self.subTest(value=hex(value)):
                self.assertFalse(thunks.ROM_LOW <= value < thunks.ROM_HIGH)
                self.assertFalse(thunks.rom(rom_mirror.canonical(value)))
        # Only wait state 0 is a canonical ROM byte: a mirror address is folded before the test.
        self.assertTrue(thunks.rom(0x08000000) and thunks.rom(0x09FFFFFF))
        self.assertFalse(thunks.rom(0x07FFFFFF) or thunks.rom(0x0A000000) or thunks.rom(0x0D000000)
                         or thunks.rom(None))

    def test_a_constant_in_any_rom_window_cannot_be_stored(self):
        # r3 = &g_right; r1 = window << 24; str r1, [r3]. A constant in the ROM or in either mirror,
        # the 0x0D window included, may be a code address; one below or above them is a number.
        obj = ('ldr', 3, 'object')
        for window in (0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D):
            with self.subTest(window=hex(window)), \
                    self.assertRaisesRegex(ValueError, 'a local code address cannot be stored'):
                verify(build(tail=(obj, ('h', 0x2100 | window), ('h', 0x0609), ('h', 0x6019))))
        for window in (0x07, 0x0E):
            with self.subTest(window=hex(window)):
                verify(build(tail=(obj, ('h', 0x2100 | window), ('h', 0x0609), ('h', 0x6019))))


if __name__ == '__main__':
    unittest.main()
