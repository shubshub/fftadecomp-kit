"""Synthetic fixed-frame boundaries for unsigned-divmod-thunks-frame-v1.

The fixtures follow 0802BEB0 (an incoming fifth argument spilled to one local
word) and 0802C624 (one local word, no incoming word).  No ROM or compiler is
needed.  Only the separately tested native UDIV/UMOD/zero closure is replaced
at its dependency boundary; the caller CFG, the unchanged prove_frame policy,
divisors, thunk identity, manifest frame evidence and report replay all run.
"""
import copy
import hashlib
import json
import os
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
import unsigned_divmod_thunk_inventory as inventory
import unsigned_thunk_profile as profile

A = match.ROM_BASE + 0x10000
CALLEE = match.ROM_BASE + 0x11000
OBJECT, TABLE, HARDWARE = 0x02001000, 0x02001100, 0x06013900
NAME = f'func_{A:08X}'
UDIV, UMOD, ZERO = inventory.OPERATIONS['__udivsi3'], inventory.OPERATIONS['__umodsi3'], 0x0814274C
R2 = thunks.ALIASES['_call_via_r2']
TARGETS = {'udiv': UDIV, 'umod': UMOD, 'thunk': R2, 'call': CALLEE}
CLEAN = 'typedef void (*Fill)(void *, unsigned);\nextern const Fill table[];\n' \
        'void func_08010000(unsigned *value) { table[0](value, *value / 10u % 3u); }\n'
# push {r4, lr}; sub sp, #4; ldr r3, [sp, #12] (entry word0); str r3, [sp]
ENTRY_WORD = (0xB510, 0xB081, 0x9B03, 0x9300)
# push {r4, lr}; sub sp, #4; str r2, [sp]  (0802C624: a local word only)
LOCAL_ONLY = (0xB510, 0xB081, 0x9200)
# ldr r2, [sp]; str r2, [sp]: reload the local, then pass it as outgoing word0
OUTGOING = (0x9A00, 0x9200)
# add sp, #4; pop {r4}; pop {r0}; bx r0
EPILOGUE = (0xB001, 0xBC10, 0xBC01, 0x4700)


def sha(value):
    return hashlib.sha256(value).hexdigest()


def bl(site, target):
    delta = target-site-4
    return struct.pack('<HH', 0xF000 | ((delta >> 12) & 0x7ff), 0xF800 | ((delta >> 1) & 0x7ff))


class UnsignedThunkFrameSourceTests(unittest.TestCase):
    def setUp(self):
        closure = patch.object(inventory.divmod, 'runtime_closure', return_value=(
            [['synthetic already-authenticated runtime closure']], [['synthetic own-frame closure']]))
        self.closure = closure.start()
        self.addCleanup(closure.stop)
        self.fixture()

    def fixture(self, *, prologue=ENTRY_WORD, middle=(), before_call=OUTGOING, epilogue=EPILOGUE,
                selector=profile.FRAME_SELECTOR):
        sequence = [*prologue, 0x1C04, ('literal', 2, OBJECT), 0x6810, 0x210A, 'udiv', 0x2103, 'umod',
                    ('literal', 2, TABLE), 0x6812, *middle, 0x1C20, 'thunk',
                    ('literal', 1, HARDWARE), *before_call, 0x1C20, 'call', *epilogue]
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
        self.proof, instructions = profile.prove(self.body, A, self.rom, self.mapping, self.index, self.calls,
                                                 selector=selector)
        self.manifest = thunks.make_manifest(self.calls, {}, self.literals, A, self.rom, self.objects,
            instructions, selector=selector,
            frame_proof=self.proof if selector == profile.FRAME_SELECTOR else None)

    def verify(self, **changes):
        values = dict(data=self.body, address=A, rom=self.rom, mapping=self.mapping,
                      index=self.index, objects=self.objects, manifest=self.manifest)
        values.update(changes)
        return thunks.verify(**values)

    def refuses(self, message=None, **fixture):
        """The framed inventory refuses this body before any manifest exists."""
        with self.assertRaises(ValueError) as caught:
            self.fixture(**fixture)
        if message is not None:
            self.assertIn(message, str(caught.exception))

    # Positive shapes ------------------------------------------------------

    def test_entry_word_spilled_to_a_local_like_0802BEB0(self):
        instructions = self.verify()
        self.assertEqual(len(instructions), self.rows[0]['instrs'])
        self.assertTrue(self.manifest['frame'])
        self.assertEqual(self.manifest['selector'], profile.FRAME_SELECTOR)
        evidence_record = self.manifest['stack_frame']
        self.assertEqual(evidence_record['schema'], profile.FRAME_EVIDENCE)
        self.assertEqual([value for _, value in evidence_record['stack_adjustments']], [-4, 4])
        self.assertEqual([row[1:] for row in evidence_record['stack_words']],
                         [['ldr', 12], ['str', 0], ['ldr', 0], ['str', 0]])
        frame = evidence_record['frame']
        self.assertEqual(frame['maximum_frame_bytes'], 12)
        self.assertEqual(frame['entry_stack']['words'], [0])
        self.assertEqual([read[1:3] for read in frame['entry_stack']['reads']], [[0, 4]])
        self.assertEqual(self.proof['schema'], inventory.FRAME_SCHEMA)
        self.assertEqual([value for _, value in self.proof['caller_divisors']], [10, 3])
        self.assertIn('readonly_entry_stack_profile.py', self.manifest['producer_source_sha256'])

    def test_local_word_without_entry_words_like_0802C624(self):
        self.fixture(prologue=LOCAL_ONLY, before_call=())
        self.verify()
        self.assertNotIn('entry_stack', self.manifest['stack_frame']['frame'])
        self.assertIsNone(self.manifest['stack_frame']['entry_stack_contract'])
        self.assertEqual([row[1:] for row in self.manifest['stack_frame']['stack_words']], [['str', 0]])

    def test_two_incoming_words_use_the_existing_contiguous_contract(self):
        # ldr r2, [sp, #16] reads entry word1 as well as word0.
        self.fixture(prologue=(*ENTRY_WORD, 0x9A04))
        self.verify()
        entry = self.manifest['stack_frame']['frame']['entry_stack']
        self.assertEqual(entry['words'], [0, 1])
        self.assertEqual(entry['schema'], 'thumb-readonly-entry-stack-words-v1')

    def test_entry_word_without_locals(self):
        # push {r4, lr}; ldr r3, [sp, #8]: an incoming word read in a saved-only frame.
        self.fixture(prologue=(0xB510, 0x9B02), before_call=(), epilogue=EPILOGUE[1:])
        self.verify()
        self.assertEqual(self.manifest['stack_frame']['stack_adjustments'], [])

    # Refusals ---------------------------------------------------------------

    def test_saved_only_selector_still_refuses_frames_and_frame_selector_needs_one(self):
        self.refuses('saved-only frame excludes locals', selector=profile.SELECTOR)
        self.refuses('requires an allocated local or incoming word', prologue=(0xB510,), before_call=(),
                     epilogue=EPILOGUE[1:])

    def test_dynamic_SP_refuses(self):
        # add sp, r5; mov sp, r4
        for middle in ((0x44AD,), (0x46A5,)):
            with self.subTest(middle=middle):
                self.refuses(middle=middle)

    def test_out_of_frame_accesses_refuse(self):
        for prologue, message in (
                # str r3, [sp, #12]: a write to the incoming word
                ((0xB510, 0xB081, 0x9303), 'entry stack permits only exact direct aligned 2-byte Thumb LDR words'),
                # ldr r3, [sp, #16]: word1 without word0
                ((0xB510, 0xB081, 0x9B04), 'incoming words exceed the existing read-only contracts'),
                # ldr r3, [sp, #36]: word6, beyond the six-word contract
                ((*ENTRY_WORD, 0x9A04, 0x9A05, 0x9A06, 0x9A07, 0x9A08, 0x9B09),
                 'incoming words exceed the existing read-only contracts'),
                # str r3, [sp, #4]: overwrites the saved r4 slot
                ((0xB510, 0xB081, 0x9301), 'overwrites a saved register')):
            with self.subTest(prologue=prologue):
                self.refuses(message, prologue=prologue)
        # A missing release leaves SP unbalanced at the return.
        self.refuses('pop leaves the established saved frame', epilogue=EPILOGUE[1:])

    def test_SP_escapes_refuse(self):
        # add r0, sp, #0; mov r0, sp; mov r2, sp (a stack-derived thunk target); stmia/ldmia
        for middle in ((0xA800,), (0x4668,), (0x466A,), (0xC810,)):
            with self.subTest(middle=middle):
                self.refuses(middle=middle)
        # str r2, [sp] holding an SP-derived value is refused at materialization.
        self.refuses(before_call=(0x466A, 0x9200))

    def test_divisors_stay_proved(self):
        # Replace movs r1, #10 with ldr r1, [sp]: a local word is not a constant divisor.
        site = next(site for site, target in sorted(self.calls.items()) if target == UDIV)-2-A
        data = bytearray(self.body)
        struct.pack_into('<H', data, site, 0x9900)
        rom = bytearray(self.rom)
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)] = data
        with self.assertRaisesRegex(ValueError, 'constant in r1'):
            profile.prove(bytes(data), A, bytes(rom), self.mapping, self.index, self.calls,
                          selector=profile.FRAME_SELECTOR)

    def test_reached_literal_naming_the_callers_own_bytes_refuses_after_composition(self):
        # Refused upstream as an untyped ROM word; the own-span rule after the
        # composed proof is reached by substituting its result at that boundary.
        hardware = next(offset for offset, value in self.words.items() if value == HARDWARE)

        def own(value):
            data = bytearray(self.body)
            struct.pack_into('<I', data, hardware, value)
            rom = bytearray(self.rom)
            rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)] = data
            return bytes(data), bytes(rom)
        instructions = self.verify()
        with patch.object(profile, 'verify', return_value=instructions) as composed:
            self.assertIs(self.verify(), instructions)
            composed.assert_called_once()
            for value in (A+8, A+9):
                data, rom = own(value)
                with self.subTest(value=value), self.assertRaisesRegex(ValueError, "caller's own bytes"):
                    self.verify(data=data, rom=rom)
        for value in (A+8, A+9):
            data, rom = own(value)
            with self.subTest(value=value), self.assertRaisesRegex(ValueError, 'typed provenance'):
                self.verify(data=data, rom=rom)

    def test_tampered_frame_records_refuse(self):
        def changed(update):
            bad = copy.deepcopy(self.manifest)
            update(bad['stack_frame'])
            return bad
        variants = [
            changed(lambda record: record['frame'].update(maximum_frame_bytes=16)),
            changed(lambda record: record['frame']['entry_stack'].update(reads=[])),
            changed(lambda record: record['frame']['entry_stack'].update(words=[0, 1])),
            changed(lambda record: record['frame'].pop('entry_stack')),
            changed(lambda record: record['frame'].update(returns=[])),
            changed(lambda record: record.update(stack_adjustments=[])),
            changed(lambda record: record.update(stack_words=record['stack_words'][:-1])),
            changed(lambda record: record['stack_words'][0].__setitem__(2, 16)),
            changed(lambda record: record.update(schema='other')),
            changed(lambda record: record.update(entry_stack_contract=None)),
            changed(lambda record: record.update(caller_frame_policy='saved-only')),
            changed(lambda record: record.update(extra=True)),
            {key: value for key, value in self.manifest.items() if key != 'stack_frame'},
            {**self.manifest, 'frame': False},
            {**self.manifest, 'selector': profile.SELECTOR},
            {**self.manifest, 'producer_source_sha256': profile.producer_sources()},
        ]
        for number, bad in enumerate(variants):
            with self.subTest(number=number), self.assertRaises(ValueError):
                self.verify(manifest=bad)
        # A saved-only v1 manifest cannot acquire frame evidence or the framed selector.
        self.fixture(prologue=(0xB510,), before_call=(), epilogue=EPILOGUE[1:], selector=profile.SELECTOR)
        self.verify()
        for bad in ({**self.manifest, 'selector': profile.FRAME_SELECTOR},
                    {**self.manifest, 'stack_frame': {'schema': profile.FRAME_EVIDENCE}}):
            with self.subTest(bad=sorted(bad)), self.assertRaises(ValueError):
                self.verify(manifest=bad)

    def test_frame_evidence_is_bound_only_to_the_framed_selector(self):
        _, instructions = profile.prove(self.body, A, self.rom, self.mapping, self.index, self.calls,
                                        selector=profile.FRAME_SELECTOR)
        for selector, frame_proof in ((profile.FRAME_SELECTOR, None), (profile.SELECTOR, self.proof),
                                      (thunks.SELECTOR, self.proof)):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                thunks.make_manifest(self.calls, {}, self.literals, A, self.rom, self.objects, instructions,
                                     selector=selector, frame_proof=frame_proof)
        with self.assertRaises(ValueError):
            profile.frame_evidence({**self.proof, 'selector': inventory.SELECTOR})
        with self.assertRaises(ValueError):
            profile.prove(self.body, A, self.rom, self.mapping, self.index, self.calls, selector=thunks.SELECTOR)

    def test_link_context_accepts_both_unsigned_selectors_only(self):
        for selector in profile.SELECTORS:
            profile.check_link_context(selector, True, 5, {}, {}, {}, {}, (False,)*4, (None,)*8)
        for selector in (thunks.SELECTOR, 'unsigned-divmod-thunks-frame-v2', None):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                profile.check_link_context(selector, True, 5, {}, {}, {}, {}, (False,)*4, (None,)*8)

    def test_source_and_assembly_forgery_guards_run_before_linking(self):
        class Runner:
            def __init__(self, text, assembly=f'\t.globl\t{NAME}\n{NAME}:\n'):
                self.text, self.assembly = text, assembly
            def read_binary(self, path):
                return (self.text if path.endswith('/f.i') else self.assembly).encode()
        original = dict(symbols=[dict(name=NAME, value=1, size=len(self.body), type=2, bind=1, section=1)])
        args = match.argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                                        objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        with patch.object(match, 'link_calls') as link:
            for runner in (Runner('extern void forged(void) __asm("_call_via_r2");\n'),
                           Runner('extern unsigned d(unsigned, unsigned) __attribute__((__alias__("__udiv" "si3")));\n'),
                           Runner(CLEAN, f'\t.thumb_set my_div,__udivsi3\n\t.globl\t{NAME}\n')):
                with self.subTest(text=runner.text, assembly=runner.assembly), self.assertRaises(ValueError):
                    thunks.object_bytes(runner, '/w', args, original, A, self.mapping, self.rom,
                                        self.objects, selector=profile.FRAME_SELECTOR)
            link.assert_not_called()

    # Reports ----------------------------------------------------------------

    def test_schema_and_selector_relabels_refuse(self):
        report = f'* verification: `{profile.FRAME_SCHEMA}`\n* function-address thunks: {profile.FRAME_SELECTOR}\n'
        self.assertEqual(thunks.selector_for_report(report), profile.FRAME_SELECTOR)
        self.assertEqual(thunks.selector_from_manifest(self.manifest), profile.FRAME_SELECTOR)
        for bad in (report.replace(profile.FRAME_SCHEMA, profile.SCHEMA),
                    report.replace(f': {profile.FRAME_SELECTOR}', f': {profile.SELECTOR}'),
                    report + '* unsigned division: synthetic\n'):
            with self.subTest(bad=bad), self.assertRaises(ValueError):
                thunks.selector_for_report(bad)

    def report_root(self):
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH', HERE/'build'))
        scratch.mkdir(parents=True, exist_ok=True)
        temporary = tempfile.TemporaryDirectory(prefix='unsigned_thunk_frame_', dir=scratch)
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

    def report(self, root, manifest=None, schema=profile.FRAME_SCHEMA, selector=profile.FRAME_SELECTOR):
        manifest = self.manifest if manifest is None else manifest
        source = evidence.source_fingerprint(root, A)
        proof = thunks.fingerprint(A, self.body, manifest, source, self.mapping, self.index, self.objects, self.rom)
        return '\n'.join([f'* verification: `{schema}`', f'* function-address thunks: {selector}',
            f'* control flow: {thunks.CONTROL_FLOW}', f'* compiler: `{match.DEFAULT_CC} {match.DEFAULT_FLAGS}`',
            *([f'* stack frame: {evidence.STACK_SUMMARY}'] if manifest.get('frame') else []),
            f'* source SHA-256: `{source}`', f'* mapping SHA-256: `{sha(self.mapping)}`',
            f'* function index SHA-256: `{sha(self.index)}`', f'* data symbols SHA-256: `{sha(self.objects)}`',
            f'* ROM SHA-256: `{sha(self.rom)}`', '* verified extent: complete ELF function symbol, including literal pools',
            '* relocations: none', '* source plausibility: plausible', '* hand-asm allow list: not listed',
            f'* source: `src/{A:08X}.c`', f'* compiled : `{self.body.hex()}`',
            f'* function-address-thunk manifest: `{thunks.manifest_text(manifest)}`',
            f'* function-address-thunk sha256: `{proof}`', f'* ROM bytes: `{self.body.hex()}` ({len(self.body)} bytes)',
            f'**MATCH - byte identical** - {len(self.body)}/{len(self.body)} bytes'])+'\n'

    def test_report_replays_frame_evidence_and_rejects_tampering(self):
        root, rom_path = self.report_root()
        report = self.report(root)
        with patch.object(evidence, 'report_rom_path', return_value=rom_path), \
                patch.object(thunks, 'verify_source', return_value=True):
            self.assertTrue(thunks.report_matches(report, root, A))
            self.assertTrue(evidence.report_matches(report, root, A))
            record = copy.deepcopy(self.manifest)
            record['stack_frame']['frame']['maximum_frame_bytes'] += 4
            tampered = [
                report.replace(profile.FRAME_SCHEMA, profile.SCHEMA),
                report.replace(f'* function-address thunks: {profile.FRAME_SELECTOR}',
                               f'* function-address thunks: {profile.SELECTOR}'),
                self.report(root, schema=profile.SCHEMA, selector=profile.SELECTOR),
                self.report(root, {**self.manifest, 'selector': profile.SELECTOR},
                            schema=profile.SCHEMA, selector=profile.SELECTOR),
                self.report(root, record),
                self.report(root, {key: value for key, value in self.manifest.items() if key != 'stack_frame'}),
                report.replace('"stack_adjustments":[[', '"stack_adjustments":[[0,0],['),
                report.replace(f'* stack frame: {evidence.STACK_SUMMARY}\n', ''),
            ]
            for number, bad in enumerate(tampered):
                with self.subTest(number=number):
                    self.assertNotEqual(bad, report)
                    self.assertFalse(thunks.report_matches(bad, root, A))


if __name__ == '__main__':
    unittest.main()
