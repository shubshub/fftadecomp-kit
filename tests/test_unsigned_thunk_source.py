"""Synthetic source-admission boundaries for unsigned-divmod-thunks-v1.

No original ROM or compiler is needed.  Only the separately tested native
UDIV/UMOD/zero closure is replaced at its dependency boundary; the caller
CFG, frame, divisors, real thunk identity, ELF relocation and link surface,
source namespace, report fingerprint and freshness checks all execute here.
"""
import ast
import copy
import hashlib
import io
import json
import os
from contextlib import contextmanager, redirect_stdout
from pathlib import Path
import struct
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE/'tools'))
import match
import match_evidence as evidence
import function_thunk_profile as thunks
import owner_admission_profile as owner
import owner_graph_profile as graph
import umod_r1_thunk_profile as umod48
import unsigned_divmod_thunk_inventory as inventory
import unsigned_thunk_profile as profile

A = match.ROM_BASE + 0x10000
CALLEE = match.ROM_BASE + 0x11000
OBJECT, TABLE, HARDWARE = 0x02001000, 0x02001100, 0x06013900
NAME = f'func_{A:08X}'
UDIV, UMOD, ZERO = inventory.OPERATIONS['__udivsi3'], inventory.OPERATIONS['__umodsi3'], 0x0814274C
R2 = thunks.ALIASES['_call_via_r2']
TARGETS = {'udiv': UDIV, 'umod': UMOD, 'thunk': R2, 'call': CALLEE}
ALIASES = {UDIV: '__udivsi3', UMOD: '__umodsi3', R2: '_call_via_r2', CALLEE: f'func_{CALLEE:08X}'}
CLEAN = 'typedef void (*Fill)(void *, unsigned);\nextern const Fill table[];\n' \
        'void func_08010000(unsigned *value) { table[0](value, *value / 10u % 3u); }\n'


def sha(value):
    return hashlib.sha256(value).hexdigest()


def bl(site, target):
    delta = target-site-4
    return struct.pack('<HH', 0xF000 | ((delta >> 12) & 0x7ff), 0xF800 | ((delta >> 1) & 0x7ff))


class UnsignedThunkSourceTests(unittest.TestCase):
    def setUp(self):
        closure = patch.object(inventory.divmod, 'runtime_closure', return_value=(
            [['synthetic already-authenticated runtime closure']], [['synthetic own-frame closure']]))
        self.closure = closure.start()
        self.addCleanup(closure.stop)
        self.fixture()

    def fixture(self, *, quotient=0x210A, remainder=0x2103, middle=(), suffix=None, include=('udiv', 'umod', 'thunk')):
        sequence = [0xB510, 0x1C04, ('literal', 2, OBJECT), 0x6810, quotient, 'udiv', remainder, 'umod',
                    ('literal', 2, TABLE), 0x6812, *middle, 0x1C20, 'thunk',
                    ('literal', 1, HARDWARE), 0x1C20, 'call',
                    *(suffix if suffix is not None else [0xBC10, 0xBC01, 0x4700])]
        sequence = [value for value in sequence if value not in ('udiv', 'umod', 'thunk') or value in include]
        body, calls, loads = bytearray(), {}, []
        for value in sequence:
            site = A+len(body)
            if type(value) is tuple:
                loads.append((len(body), value[1], value[2]))
                body += b'\0\0'
            elif value in TARGETS:
                calls[site] = TARGETS[value]
                body += bl(site, TARGETS[value])
            else:
                body += struct.pack('<H', value)
        while len(body) % 4:
            body += b'\0\0'
        self.words = {}
        for offset, register, word in loads:
            self.words[len(body)] = word
            struct.pack_into('<H', body, offset, 0x4800 | (register << 8) | ((len(body)-((offset+4) & ~3))//4))
            body += struct.pack('<I', word)
        self.body, self.calls = bytes(body), calls
        self.literals = {offset: (name, value) for offset, value in self.words.items()
                         for name in [{OBJECT: 'synthetic_object', TABLE: 'synthetic_table'}.get(value)] if name}
        self.rows = [dict(rom=f'0x{A:08X}', end=f'0x{A+len(body):08X}', mode='thumb', instrs=0),
            dict(rom=f'0x{CALLEE:08X}', end=f'0x{CALLEE+4:08X}', mode='thumb', instrs=2),
            dict(rom=f'0x{R2:08X}', end=f'0x{R2+4:08X}', mode='thumb', instrs=2),
            dict(rom=f'0x{UDIV:08X}', end=f'0x{UMOD:08X}', mode='thumb', instrs=60),
            dict(rom=f'0x{UMOD:08X}', end='0x08142BE8', mode='thumb', instrs=95),
            dict(rom=f'0x{ZERO:08X}', end=f'0x{ZERO+2:08X}', mode='thumb', instrs=1)]
        self.rows[0]['instrs'] = owner.refine(self.body, A, json.dumps(self.rows).encode())['instrs']
        self.mapping = (json.dumps(self.rows, indent=2)+'\n').encode()
        self.index = ''.join(f'{int(row["rom"], 16):08X} {int(row["end"], 16):08X} '
            f'{int(row["end"], 16)-int(row["rom"], 16)} {row["instrs"]} return\n' for row in self.rows).encode()
        image = bytearray(0x142BE8)
        image[A-match.ROM_BASE:A-match.ROM_BASE+len(body)] = body
        struct.pack_into('<HH', image, R2-match.ROM_BASE, 0x4700+(2 << 3), 0x46C0)
        self.rom = bytes(image)
        self.objects = json.dumps({'synthetic_object': f'0x{OBJECT:08X}',
                                   'synthetic_table': f'0x{TABLE:08X}'}).encode()
        instructions, *_ = graph.graph(self.body, A, owner.refine(self.body, A, self.mapping))
        self.manifest = thunks.make_manifest(self.calls, {}, self.literals, A, self.rom, self.objects,
            [instructions[site] for site in sorted(instructions)], selector=profile.SELECTOR)

    def verify(self, **changes):
        values = dict(data=self.body, address=A, rom=self.rom, mapping=self.mapping,
                      index=self.index, objects=self.objects, manifest=self.manifest)
        values.update(changes)
        return thunks.verify(**values)

    def images(self):
        original = bytearray(self.body)
        records = []
        symbols = [dict(name=NAME, value=1, size=len(original), type=2, bind=1, section=1)]
        names = {}
        for site, target in sorted(self.calls.items()):
            name = ALIASES[target]
            if name not in names:
                symbols.append(dict(name=name, value=0, size=0, type=2 if name.startswith('func_') else 0,
                                    bind=1, section=0))
                names[name] = len(symbols)-1
            records.append(struct.pack('<II', site-A, (names[name] << 8) | 10))
            original[site-A:site-A+4] = bl(site, site)
        for offset, (name, _) in sorted(self.literals.items()):
            symbols.append(dict(name=name, value=0, size=0, type=0, bind=1, section=0))
            records.append(struct.pack('<II', offset, ((len(symbols)-1) << 8) | 2))
            struct.pack_into('<I', original, offset, 0)
        relocation = b''.join(records)
        section = (0, 1, 6, 0, 0, len(original), 0, 0, 4, 0)
        rel = (0, 9, 0, 0, 0, len(relocation), 3, 1, 4, 8)
        image = dict(type=1, text=bytes(original), text_index=1,
            sections=[(0,)*10, section, rel, (0,)*10],
            section_data=[b'', bytes(original), relocation, b''], symbols=symbols,
            symbol_tables={3: symbols}, relocations=[2])
        linked = copy.deepcopy(image)
        linked.update(type=2, text=self.body, relocations=[])
        linked['sections'][1] = (*section[:3], A, *section[4:])
        linked['symbols'][0]['value'] = A | 1
        objects = {name: value for name, value in self.literals.values()}
        for symbol in linked['symbols'][1:]:
            if symbol['name'] in objects:
                symbol.update(section=0xfff1, type=1, value=objects[symbol['name']])
            else:
                target = next(target for target, name in ALIASES.items() if name == symbol['name'])
                symbol.update(section=0xfff1, type=2, value=target | 1)
        return image, linked

    def link_kwargs(self, **changes):
        values = dict(function_thunks=True, udivsi3_bindings={site: '__udivsi3' for site, t in self.calls.items() if t == UDIV},
                      umodsi3_bindings={site: '__umodsi3' for site, t in self.calls.items() if t == UMOD},
                      unsigned_thunk_profile=profile.SELECTOR)
        values.update(changes)
        return values

    def targets(self):
        return {**{ALIASES[target]: target for target in self.calls.values()},
                **{name: value for name, value in self.literals.values()}}

    @contextmanager
    def identities(self):
        with patch.object(match, 'verify_udivsi3_identity') as quotient, \
                patch.object(match.umodsi3, 'verify_identity') as remainder:
            yield quotient, remainder

    # Positive composition -------------------------------------------------

    def test_synthetic_complete_frame_divisors_thunk_ordinary_call_and_typed_pool(self):
        instructions = self.verify()
        self.assertEqual(len(instructions), self.rows[0]['instrs'])
        self.assertEqual(self.closure.call_count, 1)
        self.assertFalse(self.manifest['frame'])
        self.assertEqual([name for _, name in self.manifest['unsigned_runtime']], ['__udivsi3', '__umodsi3'])
        self.assertEqual([name for _, name in self.manifest['thunks']], ['_call_via_r2'])
        self.assertEqual([name for _, name in self.manifest['calls']], [f'func_{CALLEE:08X}'])
        self.assertEqual(self.manifest['numeric_hardware_words'],
                         [[offset, HARDWARE] for offset, value in self.words.items() if value == HARDWARE])
        self.assertEqual(sorted(name for _, name, _ in self.manifest['data']), ['synthetic_object', 'synthetic_table'])
        proof, _ = profile.prove(self.body, A, self.rom, self.mapping, self.index, self.calls)
        self.assertEqual([value for _, value in proof['caller_divisors']], [10, 3])

    def test_either_runtime_family_alone_is_admitted(self):
        for family in ('udiv', 'umod'):
            self.fixture(include=(family, 'thunk'))
            with self.subTest(family=family):
                self.verify()

    def test_original_typed_ELF_bindings_and_exact_linked_surface(self):
        original, linked = self.images()
        with self.identities() as (quotient, remainder):
            calls, functions, literals = thunks.original_bindings(original, A, self.mapping, self.rom,
                                                                  self.objects, selector=profile.SELECTOR)
        quotient.assert_called_with(self.rom, self.mapping)
        remainder.assert_called_with(self.rom, self.mapping)
        self.assertEqual((calls, functions, literals), (self.calls, {}, self.literals))
        result = match.linked_function_bytes(original, linked, NAME, A, calls, self.targets(), literals, {}, {},
                                             **self.link_kwargs())
        self.assertEqual(result, self.body)
        for location in (0, len(self.body)-1):
            bad = copy.deepcopy(linked)
            data = bytearray(bad['text'])
            data[location] ^= 1
            bad['text'] = bytes(data)
            with self.subTest(location=location), self.assertRaises(ValueError):
                match.linked_function_bytes(original, bad, NAME, A, calls, self.targets(), literals, {}, {},
                                            **self.link_kwargs())

    # Refusals ---------------------------------------------------------------

    def test_existing_paths_still_refuse_the_composition(self):
        original, linked = self.images()
        with self.identities():
            for selector in (thunks.SELECTOR, umod48.SELECTOR):
                with self.subTest(selector=selector), self.assertRaises(ValueError):
                    thunks.original_bindings(original, A, self.mapping, self.rom, self.objects, selector=selector)
            with self.assertRaises(ValueError):
                match.call_bindings(original, NAME, A, self.mapping, len(self.rom), self.rom, self.objects, {}, {},
                                    udivsi3_bindings={}, umodsi3_bindings={})
            with self.assertRaises(ValueError):
                match.linked_function_bytes(original, linked, NAME, A, self.calls, self.targets(), self.literals,
                                            {}, {}, **self.link_kwargs(unsigned_thunk_profile=None))

    def test_missing_dynamic_or_zero_divisor_is_not_admitted(self):
        # adds r1, r4, #0 is an entry value, not a constant; movs r1, #0 is zero.
        for field, value in (('quotient', 0x1C21), ('remainder', 0x1C21), ('quotient', 0x2100), ('remainder', 0x2100)):
            self.fixture(**{field: value})
            with self.subTest(field=field, value=value), self.assertRaises(ValueError):
                self.verify()

    def test_runtime_and_thunk_calls_are_both_required(self):
        for include in (('udiv', 'umod'), ('thunk',)):
            self.fixture(include=include)
            with self.subTest(include=include), self.assertRaises(ValueError):
                self.verify()

    def test_allocations_SP_exports_entry_words_block_transfers_and_cycles_refuse(self):
        for instruction in (0xB081, 0x4668, 0x9803, 0x9000, 0xC810):
            with self.subTest(instruction=instruction), self.assertRaises(ValueError):
                self.fixture(middle=(instruction,))
                self.verify()
        for suffix in ([0xBC01, 0x4700], [0x2800, 0xD0FE, 0xBC10, 0xBC01, 0x4700]):
            with self.subTest(suffix=suffix), self.assertRaises(ValueError):
                self.fixture(suffix=suffix)
                self.verify()

    def test_thunk_target_with_stack_provenance_refuses(self):
        # mov r2, sp; adds r2, #4 (an SP export, then a stack-derived target).
        for middle in ((0x466A,), (0x466A, 0x3204)):
            with self.subTest(middle=middle), self.assertRaises(ValueError):
                self.fixture(middle=middle)
                self.verify()

    def test_untyped_RAM_ROM_or_reserved_address_words_refuse(self):
        for drop in ('synthetic_object', 'synthetic_table'):
            bad = copy.deepcopy(self.manifest)
            bad['data'] = [record for record in bad['data'] if record[1] != drop]
            with self.subTest(drop=drop), self.assertRaises(ValueError):
                self.verify(manifest=bad)
        hardware = next(offset for offset, value in self.words.items() if value == HARDWARE)
        for value in (A, UDIV, R2, 0x09000000):
            data = bytearray(self.body)
            struct.pack_into('<I', data, hardware, value)
            rom = bytearray(self.rom)
            rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)] = data
            with self.subTest(value=value), self.assertRaises(ValueError):
                self.verify(data=bytes(data), rom=bytes(rom))

    def test_tampered_manifests_refuse(self):
        def changed(**fields):
            bad = copy.deepcopy(self.manifest)
            bad.update(fields)
            return bad
        thunk, runtime, call = self.manifest['thunks'], self.manifest['unsigned_runtime'], self.manifest['calls']
        variants = [
            changed(thunks=[]), changed(thunks=thunk*2), changed(thunks=[[thunk[0][0]+2, thunk[0][1]]]),
            changed(thunks=[[thunk[0][0], '_call_via_r3']]),
            changed(unsigned_runtime=[]), changed(unsigned_runtime=runtime[:1]),
            changed(unsigned_runtime=[[runtime[0][0], '__umodsi3'], [runtime[1][0], '__udivsi3']]),
            changed(unsigned_runtime=[[runtime[0][0], '__divsi3'], runtime[1]]),
            changed(calls=[]), changed(calls=[[call[0][0], 'func_08011004']]),
            changed(calls=[*call, [thunk[0][0], '_call_via_r2']]),
            changed(functions=[[0, 'func_08011000']]), changed(numeric_hardware_words=[]),
            changed(numeric_hardware_words=[[self.manifest['numeric_hardware_words'][0][0], HARDWARE+4]]),
            changed(dependencies=[]), changed(frame=True), changed(selector=umod48.SELECTOR),
            changed(abi='other'), changed(runtime='other'),
            changed(producer_source_sha256={**self.manifest['producer_source_sha256'], 'match.py': '0'*64}),
            {key: value for key, value in self.manifest.items() if key != 'numeric_hardware_words'},
            {**self.manifest, 'divisors': []},
        ]
        for number, bad in enumerate(variants):
            with self.subTest(number=number), self.assertRaises(ValueError):
                self.verify(manifest=bad)

    def test_changed_thunk_identity_maps_indices_and_objects_refuse(self):
        rom = bytearray(self.rom)
        rom[R2-match.ROM_BASE] ^= 1
        with self.assertRaises(ValueError):
            self.verify(rom=bytes(rom))
        rows = copy.deepcopy(self.rows)
        rows[0]['instrs'] -= 1
        with self.assertRaises(ValueError):
            self.verify(mapping=json.dumps(rows).encode())
        lines = self.index.decode().splitlines()
        first = lines[0].split()
        first[3] = str(int(first[3])-1)
        lines[0] = ' '.join(first)
        with self.assertRaises(ValueError):
            self.verify(index=('\n'.join(lines)+'\n').encode())
        with self.assertRaises(ValueError):
            self.verify(objects=json.dumps({'synthetic_object': '0x02001004', 'synthetic_table': f'0x{TABLE:08X}'}).encode())

    def test_explicit_link_context_and_bindings_refuse_other_composition(self):
        original, _ = self.images()
        for changes in ({'unsigned_thunk_profile': True}, {'unsigned_thunk_profile': thunks.SELECTOR},
                        {'function_thunks': False}, {'allow_switch_data': True}, {'modsi3_bindings': {}},
                        {'divsi3_bindings': {}}, {'thunk_pool_words': 0}, {'umodsi3_bindings': None},
                        {'udivsi3_bindings': None}, {'umod_r1_profile': umod48.SELECTOR},
                        {'unsigned_runtime_profile': 'unsigned-divmod-ten-v1'}):
            with self.subTest(changes=changes), self.identities(), self.assertRaises(ValueError):
                match.call_bindings(original, NAME, A, self.mapping, len(self.rom), self.rom, self.objects,
                                    {}, {}, **self.link_kwargs(**changes))
        quotient, remainder = self.link_kwargs()['udivsi3_bindings'], self.link_kwargs()['umodsi3_bindings']
        for functions, switches in (({0: ('func_08011000', 0x08011001)}, {}), ({}, {0: 4})):
            with self.subTest(functions=functions, switches=switches), self.assertRaises(ValueError):
                profile.check_link_context(profile.SELECTOR, True, 5, functions, switches, {}, {},
                                           (False,)*4, (None,)*8)
        targets = self.targets()
        for mutated in ({**targets, 'func_08011004': 0x08011004}, {**targets, '__udivsi3': UDIV+2},
                        {**targets, '_call_via_r2': thunks.ALIASES['_call_via_r3']},
                        {**targets, f'func_{CALLEE:08X}': CALLEE+2}):
            with self.subTest(targets=sorted(mutated)), self.assertRaises(ValueError):
                profile.check_link_bindings(self.calls, mutated, self.literals, {}, {}, quotient, remainder)
        for q, r in (({}, remainder), (quotient, {}), (remainder, quotient), (quotient, {**remainder, **quotient})):
            with self.subTest(q=q, r=r), self.assertRaises(ValueError):
                profile.check_link_bindings(self.calls, targets, self.literals, {}, {}, q, r)
        profile.check_link_bindings(self.calls, targets, self.literals, {}, {}, quotient, remainder)

    def test_explicit_runtime_aliases_and_noncanonical_thunk_names_refuse(self):
        original, _ = self.images()
        for old, new in (('__udivsi3', 'func_08142AB0'), ('__umodsi3', 'func_08142B28'),
                         ('_call_via_r2', 'func_08142250')):
            bad = copy.deepcopy(original)
            next(symbol for symbol in bad['symbols'] if symbol['name'] == old)['name'] = new
            with self.subTest(name=new), self.identities(), self.assertRaises(ValueError):
                thunks.original_bindings(bad, A, self.mapping, self.rom, self.objects, selector=profile.SELECTOR)

    def test_forged_sources_naming_reserved_identifiers_or_asm_labels_refuse(self):
        profile.namespace(CLEAN)
        for source in (
                'extern unsigned __udivsi3(unsigned, unsigned);\nunsigned f(unsigned x) { return __udivsi3(x, 10); }\n',
                'extern unsigned __umodsi3(unsigned, unsigned);\nunsigned f(unsigned x) { return __umodsi3(x, 10); }\n',
                'extern void _call_via_r2(void);\nvoid f(void) { _call_via_r2(); }\n',
                'extern void forged(void) __asm("_call_via_r2");\nvoid f(void) { forged(); }\n',
                'extern unsigned q(unsigned, unsigned) __asm("__udivsi3");\nunsigned f(unsigned x) { return q(x, 10); }\n',
                'extern unsigned q(unsigned, unsigned) __asm("__umodsi3");\nunsigned f(unsigned x) { return q(x, 10); }\n',
                'extern void forged(void) __asm("_call_" "via_r2");\nvoid f(void) { forged(); }\n',
                'extern void forged(void) __asm__("label");\nvoid f(void) { forged(); }\n',
                'extern void forged(void) asm("label");\nvoid f(void) { forged(); }\n',
                'extern unsigned __divsi3(int, int);\n', 'extern unsigned __modsi3(int, int);\n',
                CLEAN + '\0'):
            with self.subTest(source=source), self.assertRaises(ValueError):
                profile.namespace(source)

    def test_alias_and_weak_attributes_refuse_in_any_spelling(self):
        for source in (CLEAN + 'unsigned weak, alias;\n',
                       CLEAN + 'extern void g(void) __attribute__((noreturn));\n'):
            profile.namespace(source)
        for source in (
                'extern unsigned my_div(unsigned, unsigned) __attribute__((__alias__("__udiv" "si3")));\n'
                'unsigned f(unsigned x) { return (unsigned short)my_div(x, 10u); }\n',
                'extern unsigned my_mod(unsigned, unsigned) __attribute ((alias ("__umod" "si3")));\n',
                'extern void forged(void) __attribute((__alias__("_call_" "via_r3")));\nvoid f(void) { forged(); }\n',
                'extern void forged(void) __attribute__((_alias("_call_" "via_r2")));\n',
                'extern unsigned my_div(unsigned, unsigned) __attribute__((weak));\n',
                'extern unsigned my_div(unsigned, unsigned) __attribute__((noreturn, __weak__));\n',
                'extern unsigned my_div(unsigned, unsigned) __attribute((_weak_));\n'):
            with self.subTest(source=source), self.assertRaises(ValueError):
                profile.namespace(source)

    def test_compiler_assembly_and_object_cannot_alias_or_export(self):
        original, _ = self.images()
        clean = f'\t.code\t16\n\t.globl\t{NAME}\n\t.thumb_func\n{NAME}:\n\tbl\t__udivsi3\n'
        profile.compiled(clean, original, A)
        for line in ('\t.thumb_set my_div,__udivsi3', '\t.thumb_set forged,_call_via_r3',
                     '\t.set my_div,__udivsi3', '\t.equ my_div,0x08142AB1', '\t.equiv my_div,__umodsi3',
                     '\t.eqv my_div,__udivsi3', '\t.weak my_div', '\t.weakref my_div,__udivsi3',
                     'label: .set my_div,__udivsi3'):
            with self.subTest(line=line), self.assertRaises(ValueError):
                profile.compiled(clean + line + '\n', original, A)
        for extra in (dict(name='my_div', value=0x51, size=4, type=2, bind=1, section=1),
                      dict(name='my_div', value=0x08142AB1, size=0, type=2, bind=1, section=0xfff1),
                      dict(name='my_div', value=0x51, size=4, type=2, bind=2, section=1)):
            bad = copy.deepcopy(original)
            bad['symbols'].append(extra)
            with self.subTest(symbol=extra), self.assertRaises(ValueError):
                profile.compiled(clean, bad, A)
        bad = copy.deepcopy(original)
        bad['symbols'][0]['bind'] = 0
        with self.assertRaises(ValueError):
            profile.compiled(clean, bad, A)

    def test_source_replay_applies_the_namespace_before_linking(self):
        class Runner:
            def __init__(self, text, assembly=f'\t.globl\t{NAME}\n{NAME}:\n'):
                self.text, self.assembly = text, assembly
            def read_binary(self, path):
                if path.endswith('/f.i'):
                    return self.text.encode()
                if path.endswith('/f.s'):
                    return self.assembly.encode()
                raise AssertionError('unexpected read')
        original, _ = self.images()
        args = match.argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                                        objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        forged = 'extern void forged(void) __asm("_call_via_r2");\n'
        with patch.object(match, 'link_calls') as link:
            for selector in (profile.SELECTOR,):
                with self.subTest(selector=selector), self.assertRaises(ValueError):
                    thunks.object_bytes(Runner(forged), '/w', args, original, A, self.mapping, self.rom,
                                        self.objects, selector=selector)
            link.assert_not_called()
        literals = self.literals
        # The C spelling is irrelevant to the assembly and object checks.  An
        # otherwise admissible link is mocked, so only those checks can refuse.
        exported = copy.deepcopy(original)
        exported['symbols'].append(dict(name='my_div', value=0x51, size=4, type=2, bind=1, section=1))
        with patch.object(match, 'link_calls', return_value=(self.body, self.calls, literals)) as link, \
                patch.object(thunks, 'original_bindings', return_value=(self.calls, {}, literals)):
            for assembly, image in ((f'\t.globl\tmy_div\n\t.thumb_set my_div,__udivsi3\n\t.globl\t{NAME}\n', original),
                                    (f'\t.globl\tforged\n\t.thumb_set forged,_call_via_r3\n\t.globl\t{NAME}\n', original),
                                    (f'\t.globl\t{NAME}\n{NAME}:\n', exported)):
                with self.subTest(assembly=assembly), self.assertRaises(ValueError):
                    thunks.object_bytes(Runner(CLEAN, assembly), '/w', args, image, A, self.mapping,
                                        self.rom, self.objects, selector=profile.SELECTOR)
            link.assert_not_called()
            self.assertEqual(thunks.object_bytes(Runner(CLEAN), '/w', args, original, A, self.mapping, self.rom,
                                                 self.objects, selector=profile.SELECTOR),
                             (self.body, self.calls, {}, literals))
        with patch.object(match, 'link_calls', return_value=(self.body, self.calls, literals)) as link, self.identities():
            result = thunks.object_bytes(Runner(CLEAN), '/w', args, original, A, self.mapping, self.rom,
                                         self.objects, selector=profile.SELECTOR)
        self.assertEqual(result, (self.body, self.calls, {}, literals))
        self.assertEqual(link.call_args.kwargs['unsigned_thunk_profile'], profile.SELECTOR)
        self.assertEqual(link.call_args.kwargs['udivsi3_bindings'], {})
        self.assertEqual(link.call_args.kwargs['umodsi3_bindings'], {})
        self.assertIsNone(link.call_args.kwargs['umod_r1_profile'])

    # Reports ----------------------------------------------------------------

    def test_closed_schema_and_report_selector_extraction(self):
        report = f'* verification: `{profile.SCHEMA}`\n* function-address thunks: {profile.SELECTOR}\n'
        self.assertEqual(thunks.selector_for_report(report), profile.SELECTOR)
        self.assertEqual(thunks.selector_from_manifest(self.manifest), profile.SELECTOR)
        for extra in ('* unsigned division: synthetic\n', '* function-address thunks: canonical-thunks-v1\n',
                      '* signed remainder: synthetic\n'):
            with self.subTest(extra=extra), self.assertRaises(ValueError):
                thunks.selector_for_report(report+extra)
        for schema in (umod48.SCHEMA, thunks.SCHEMA):
            with self.subTest(schema=schema), self.assertRaises(ValueError):
                thunks.selector_for_report(report.replace(profile.SCHEMA, schema))

    def test_CLI_exposes_only_the_explicit_selector(self):
        with patch.object(sys, 'argv', ['match.py', '--help']), redirect_stdout(io.StringIO()) as output, \
                self.assertRaises(SystemExit) as result:
            match.main()
        self.assertEqual(result.exception.code, 0)
        self.assertIn(profile.SELECTOR, output.getvalue())
        status = ast.parse((HERE/'tools/status.py').read_text())
        self.assertTrue(any(isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and
                            node.func.attr == 'selector_for_report' and isinstance(node.func.value, ast.Name) and
                            node.func.value.id == 'function_thunk' for node in ast.walk(status)))

    def report_root(self):
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH', HERE/'build'))
        scratch.mkdir(parents=True, exist_ok=True)
        temporary = tempfile.TemporaryDirectory(prefix='unsigned_thunk_source_', dir=scratch)
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name)
        for directory in ('src', 'include', 'config', 'symbols', 'docs/match'):
            (root/directory).mkdir(parents=True)
        (root/f'src/{A:08X}.c').write_text(CLEAN)
        (root/'include/context.h').write_text('struct Synthetic;\n')
        (root/'config/functions.json').write_bytes(self.mapping)
        (root/'config/data_symbols.json').write_bytes(self.objects)
        (root/'symbols/functions.txt').write_bytes(self.index)
        rom_path = root/'synthetic-image.bin'
        rom_path.write_bytes(self.rom)
        return root, rom_path

    def report(self, root, manifest=None):
        manifest = self.manifest if manifest is None else manifest
        source = evidence.source_fingerprint(root, A)
        proof = thunks.fingerprint(A, self.body, manifest, source, self.mapping, self.index, self.objects, self.rom)
        return '\n'.join([f'* verification: `{profile.SCHEMA}`', f'* function-address thunks: {profile.SELECTOR}',
            f'* control flow: {thunks.CONTROL_FLOW}', f'* compiler: `{match.DEFAULT_CC} {match.DEFAULT_FLAGS}`',
            f'* source SHA-256: `{source}`', f'* mapping SHA-256: `{sha(self.mapping)}`',
            f'* function index SHA-256: `{sha(self.index)}`', f'* data symbols SHA-256: `{sha(self.objects)}`',
            f'* ROM SHA-256: `{sha(self.rom)}`', '* verified extent: complete ELF function symbol, including literal pools',
            '* relocations: none', '* source plausibility: plausible', '* hand-asm allow list: not listed',
            f'* source: `src/{A:08X}.c`', f'* compiled : `{self.body.hex()}`',
            f'* function-address-thunk manifest: `{thunks.manifest_text(manifest)}`',
            f'* function-address-thunk sha256: `{proof}`', f'* ROM bytes: `{self.body.hex()}` ({len(self.body)} bytes)',
            f'**MATCH - byte identical** - {len(self.body)}/{len(self.body)} bytes'])+'\n'

    def test_report_acceptance_requires_fresh_inputs_and_rejects_tampering(self):
        root, rom_path = self.report_root()
        report = self.report(root)
        with patch.object(evidence, 'report_rom_path', return_value=rom_path), \
                patch.object(thunks, 'verify_source', return_value=True) as source:
            self.assertTrue(thunks.report_matches(report, root, A))
            self.assertTrue(evidence.report_matches(report, root, A))
            source.reset_mock()
            for path in (root/'config/functions.json', root/'symbols/functions.txt', root/'config/data_symbols.json',
                         root/'include/context.h', root/f'src/{A:08X}.c'):
                before = path.read_bytes()
                path.write_bytes(before+b' ')
                with self.subTest(path=path.name):
                    self.assertFalse(thunks.report_matches(report, root, A))
                path.write_bytes(before)
            source.assert_not_called()
            tampered = [
                report.replace(f'* function-address thunks: {profile.SELECTOR}', f'* function-address thunks: {umod48.SELECTOR}'),
                report.replace(profile.SCHEMA, umod48.SCHEMA),
                report.replace('"_call_via_r2"', '"_call_via_r3"'),
                report.replace('"__umodsi3"', '"__udivsi3"'),
                report.replace(f'{len(self.body)}/{len(self.body)} bytes', f'{len(self.body)-1}/{len(self.body)} bytes'),
                report.replace('* source plausibility: plausible', '* source plausibility: implausible'),
                report + '* unsigned division: synthetic\n',
                self.report(root, {**self.manifest, 'numeric_hardware_words': []}),
                self.report(root, {**self.manifest, 'unsigned_runtime': self.manifest['unsigned_runtime'][:1]}),
            ]
            fingerprint = report.split('* function-address-thunk sha256: `')[1][:64]
            tampered.append(report.replace(fingerprint, '0'*64))
            for number, bad in enumerate(tampered):
                with self.subTest(number=number):
                    self.assertNotEqual(bad, report)
                    self.assertFalse(thunks.report_matches(bad, root, A))
            with patch.object(thunks, 'verify_source', side_effect=ValueError('fresh C/ELF differs')):
                self.assertFalse(thunks.report_matches(report, root, A))


if __name__ == '__main__':
    unittest.main()
