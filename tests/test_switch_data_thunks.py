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
import function_thunk_profile as function_thunk
import switch_data_thunks as thunks
import switch_pool_outgoing_frame as pool_switch_frame

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
        variants = {
            'fresh literal reload': parts(),
            'rewrite of the base to itself': parts(between=(('h', 0x3300),)),
            'writeback store': parts(first=(('h', 0xC302),), reload=(('ldr', 4, 'object'),)),
            'copy of the base': parts(reload=(('h', 0x1C1C),)),
        }
        for label, fixture in variants.items():
            with self.subTest(label), self.assertRaisesRegex(ValueError, 'constant-derived'):
                leaf(build(**fixture), switch_thunks=PLAIN)
        # The dirty flag survives a call, which could copy the memory.
        bl = (('bl', CALLEE),)
        with self.assertRaisesRegex(ValueError, 'constant-derived'):
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
                'constant stored and loaded back': (
                    dict(post=(('ldr', 3, 'object'), ('h', 0x2180), ('h', 0x6019), ('h', 0x681A), ('h', 0x0512))),
                    'constant-derived'),
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
        # The joined state stays MIXED, but the exact value arriving there is a change.
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
                    self.assertEqual(rebuild.saved_profile_arguments('\n'.join(good), directory, BASE),
                                     ['--switch-data-profile', selector])
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
                # Thunk-free reports never recover a thunk selector.
                self.assertIsNone(thunks.selector_for_report(
                    f'* verification: `{evidence.SWITCH_U16_SCALAR_SCHEMA}`'))


if __name__ == '__main__':
    unittest.main()
