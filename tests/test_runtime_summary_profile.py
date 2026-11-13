"""Canonical division runtimes as proved leaf summaries inside bounded-buffer walks."""
import copy
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import named_data_buffer_profile as buffers
import owner_admission_profile as owner
import runtime_summary_profile as summary

A, B, C = 0x08010000, 0x08010100, 0x08010200
DIV, MOD, UDIV, UMOD, ZERO = 0x081426B8, 0x08142950, 0x08142AB0, 0x08142B28, 0x0814274C
RUNTIME_ROWS = ((DIV, 0x0814274A, 72), (ZERO, 0x0814274E, 1), (MOD, 0x08142A1E, 102),
                (UDIV, 0x08142B28, 59), (UMOD, 0x08142BE8, 95))
EPILOGUE = 'add sp, #8\npop {r4}\npop {r0}\nbx r0'
WRITER = 'movs r1, #0\nstr r1, [r0]\nbx lr'


class RuntimeSummaryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        selected = os.environ.get('FFTA_ROM')
        if not selected or not Path(selected).is_file():
            raise unittest.SkipTest('FFTA_ROM must reference the approved ROM')
        approved = Path(selected).read_bytes()
        if hashlib.sha256(approved).hexdigest() != \
                '43fc8204c6dceee58828aebc7af0c72eb807e99f35ad641c8bb0a4fa8b6edc19':
            raise unittest.SkipTest('FFTA_ROM is not the approved ROM')
        cls.runtime = approved[DIV - match.ROM_BASE:UMOD + 0xC0 - match.ROM_BASE]

    def setUp(self):
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH', tempfile.gettempdir()))
        scratch.mkdir(parents=True, exist_ok=True)
        self.temporary = tempfile.TemporaryDirectory(prefix='runtime_summary_', dir=scratch)
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)

    def fixture(self, caller, callee=WRITER, child='bx lr', *, names=None,
                selector=summary.SELECTOR, patch=None):
        assembly = self.root/'fixture.s'
        assembly.write_text('.syntax unified\n.arch armv4t\n.thumb\n.text\n'
            '.global caller, caller_end, callee, callee_end, child, child_end\n'
            + ''.join(f'.thumb_set rt_{address:08X}, 0x{address | 1:08X}\n'
                      for address in (DIV, MOD, UDIV, UMOD, ZERO, MOD + 2)) +
            f'caller:\n{caller}\ncaller_end:\n.org 0x100\n'
            f'callee:\n{callee}\ncallee_end:\n.org 0x200\nchild:\n{child}\nchild_end:\n')
        for command in (
            ['arm-none-eabi-as', '-mthumb-interwork', str(assembly), '-o', str(self.root/'f.o')],
            ['arm-none-eabi-ld', '-Ttext=0x08010000', '-e', 'caller', str(self.root/'f.o'), '-o', str(self.root/'f.elf')],
            ['arm-none-eabi-objcopy', '-O', 'binary', '--only-section=.text', str(self.root/'f.elf'), str(self.root/'f.bin')],
        ):
            subprocess.run(command, check=True, capture_output=True)
        image = match.elf_image((self.root/'f.elf').read_bytes())
        symbols = {symbol['name']: symbol['value'] for symbol in image['symbols']}
        binary = (self.root/'f.bin').read_bytes()
        rom = bytearray(UMOD + 0xC0 - match.ROM_BASE)
        rom[A - match.ROM_BASE:A - match.ROM_BASE + len(binary)] = binary
        rom[DIV - match.ROM_BASE:UMOD + 0xC0 - match.ROM_BASE] = self.runtime
        if patch is not None:
            address, value = patch
            rom[address - match.ROM_BASE:address - match.ROM_BASE + len(value)] = value
        rows = [dict(rom=f'0x{symbols[name]:08X}', end=f'0x{symbols[name + "_end"]:08X}',
                     mode='thumb', instrs=0) for name in ('caller', 'callee', 'child')]
        rows += [dict(rom=f'0x{start:08X}', end=f'0x{end:08X}', mode='thumb', instrs=count)
                 for start, end, count in RUNTIME_ROWS]
        body = binary[:symbols['caller_end'] - A]
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        calls = []
        for item in decoder.disasm(body, A):
            if item.mnemonic == 'bl':
                target = item.operands[0].imm
                name = (names or {}).get(target, summary.FAMILY.get(target, f'func_{target:08X}'))
                calls.append([item.address - A, name])
        return dict(data=body, address=A, rom=bytes(rom),
                    mapping=json.dumps(rows).encode(),
                    index=''.join(f'{int(r["rom"], 16):08X} {int(r["end"], 16):08X} '
                                  f'{int(r["end"], 16) - int(r["rom"], 16)} {r["instrs"]} return\n'
                                  for r in rows).encode(),
                    objects=b'{}\n', bindings=dict(calls=calls, data=[], functions=[], switches=[]),
                    selector=selector)

    @staticmethod
    def owner_body(middle='mov r3, sp', runtime=MOD):
        # A local word to an ordinary writer (whose R0 still aliases it on
        # return), then a runtime call with the buffer alias in saved R4, scalar
        # operands and, by default, a dead copy left in scratch R3.
        return ('push {r4, lr}\nsub sp, #8\nmov r0, sp\nbl callee\nmov r4, sp\nmovs r0, #7\nmovs r1, #3\n' + middle +
                f'\nbl rt_{runtime:08X}\nldr r0, [r4]\n' + EPILOGUE)

    def test_every_canonical_entry_is_summarised_with_bound_closure(self):
        for runtime in (DIV, MOD, UDIV, UMOD):
            with self.subTest(runtime=hex(runtime)):
                manifest, _ = owner.verify(**self.fixture(self.owner_body('', runtime)))
                self.assertEqual(manifest['profile'], summary.SCHEMA)
                proof = manifest['proof']
                self.assertEqual(proof['calls'], [[6, f'func_{B:08X}']])
                self.assertEqual(proof['runtime_calls'], [[16, summary.FAMILY[runtime]]])
                record = proof['buffers']['runtime_summaries']
                self.assertEqual(record['schema'], summary.SUMMARY_SCHEMA)
                self.assertEqual(record['families'], [summary.FAMILY[runtime]])
                self.assertEqual({row['address'] for row in record['components']}, {runtime, ZERO})
                for row in record['components']:
                    raw = self.runtime[row['address'] - DIV:row['end'] - DIV]
                    self.assertEqual(row['body_sha256'], hashlib.sha256(raw).hexdigest())
                    self.assertEqual(row['restores'], 'r4-r11,sp,entry-lr')
                self.assertEqual(record['observations'], [])  # no alias reached the call
                entry = next(row for row in record['components'] if row['address'] == runtime)
                self.assertEqual(entry['scratch_overwritten_on_every_return'], [3] if runtime == MOD else [])
                self.assertIs(record['numeric_equivalence_claim'], False)
                self.assertIs(record['termination_claim'], False)
                self.assertIn('no numeric quotient', record['contract'])

    def test_addressed_spelling_is_bound_and_a_wrong_name_is_refused(self):
        f = self.fixture(self.owner_body(), names={MOD: f'func_{MOD:08X}'})
        manifest, _ = owner.verify(**f)
        self.assertEqual(manifest['proof']['runtime_calls'], [[18, f'func_{MOD:08X}']])
        for wrong in ('__divsi3', '__umodsi3', f'func_{DIV:08X}', 'func_08142952'):
            with self.subTest(wrong=wrong), self.assertRaisesRegex(ValueError, 'does not bind its exact entry'):
                owner.verify(**self.fixture(self.owner_body(), names={MOD: wrong}))

    def test_stack_pointer_operand_or_link_alias_is_refused(self):
        for setup in ('mov r0, sp', 'mov r1, sp', 'add r1, sp, #4'):
            with self.subTest(setup=setup), self.assertRaisesRegex(ValueError, 'R0, R1 or LR'):
                owner.verify(**self.fixture(self.owner_body(setup)))
        f = self.fixture(self.owner_body())
        proof = summary.RuntimeSummaryBufferProof(f['rom'], f['mapping'], f['index'], f['objects'])
        stack = [(False, False, True)] * 2
        for register in (match.ARM_REG_R0, match.ARM_REG_R1, match.ARM_REG_LR):
            with self.subTest(register=register), self.assertRaisesRegex(ValueError, 'R0, R1 or LR'):
                proof.check_arguments(MOD, {register: -8}, stack, {}, frozenset(), site=A)

    def test_scratch_pointer_survives_unless_overwritten_on_every_return(self):
        # A pointer left in R2/R3/R12 is still there after the zero-divisor
        # (and UMOD early-return) paths; a later store through it must not be
        # admitted as an external access.
        for runtime in (DIV, MOD, UDIV, UMOD):
            for register in ('r2', 'r3', 'ip'):
                use = 'mov r2, ip' if register == 'ip' else f'adds r2, {register}, #0'
                setup = (f'mov {register}, sp' if register != 'ip' else 'mov r2, sp\nmov ip, r2\nmovs r2, #0')
                body = ('push {r4, lr}\nsub sp, #8\nmov r0, sp\nbl callee\nmov r4, sp\nmovs r0, #7\nmovs r1, #0\n'
                        f'{setup}\nbl rt_{runtime:08X}\n{use}\nmovs r1, #0\nstr r1, [r2, #0x40]\n'
                        'ldr r0, [r4]\n' + EPILOGUE)
                with self.subTest(runtime=hex(runtime), register=register):
                    if runtime == MOD and register == 'r3':
                        # Proved overwritten on every return: the alias is discarded and
                        # the later store goes through an unknown scalar, as after any call.
                        manifest, _ = owner.verify(**self.fixture(body))
                        observation, = manifest['proof']['buffers']['runtime_summaries']['observations']
                        self.assertEqual(observation['discarded_scratch_aliases'], [[3, -16]])
                    else:
                        with self.assertRaisesRegex(ValueError, 'may return unchanged'):
                            owner.verify(**self.fixture(body))

    def test_callee_runtime_call_and_its_pointer_operand(self):
        callee = ('push {r4, lr}\nadds r4, r0, #0\nmovs r0, #9\nmovs r1, #2\nbl rt_%08X\n'
                  'strb r0, [r4]\npop {r4}\npop {r1}\nbx r1')
        caller = 'push {r4, lr}\nsub sp, #8\nmov r0, sp\nbl callee\n' + EPILOGUE
        manifest, _ = owner.verify(**self.fixture(caller, callee % MOD))
        record = manifest['proof']['buffers']['runtime_summaries']
        self.assertEqual(record['sites'], [[B + 8, '__modsi3']])
        self.assertEqual(manifest['proof']['runtime_calls'], [])
        leaked = callee.replace('movs r0, #9', 'adds r0, r4, #0') % DIV
        with self.assertRaisesRegex(ValueError, 'buffer callee 0x08010100: runtime summary refuses'):
            owner.verify(**self.fixture(caller, leaked))
        # The existing selector keeps refusing a runtime inside an inspected callee.
        with self.assertRaisesRegex(ValueError, 'signed remainder requires numeric proof'):
            owner.verify(**self.fixture(caller, callee % MOD, selector=buffers.SELECTOR))

    def test_quotient_is_never_a_known_index(self):
        tail = 'mov r1, sp\nstrb r0, [r1, r0]\nmovs r1, #0\nadd sp, #8\npop {r4}\npop {r0}\nbx r0'
        start = 'push {r4, lr}\nsub sp, #8\nmov r0, sp\nbl callee\nmovs r0, #1\n'
        # control: without the call the proven constant index 1 is in bounds
        owner.verify(**self.fixture(start + tail, selector=buffers.DATAFREE_SELECTOR))
        with self.assertRaisesRegex(ValueError, 'index is not a known constant'):
            owner.verify(**self.fixture(start + 'movs r1, #3\nbl rt_{:08X}\n'.format(DIV) + tail))
        with self.assertRaisesRegex(ValueError, 'not a known scalar constant'):
            owner.verify(**self.fixture(start + 'movs r1, #3\nbl rt_{:08X}\nadds r1, r0, #0\nmov r0, sp\n'
                                        'bl callee\n'.format(UDIV) + EPILOGUE, 'strb r1, [r0, r1]\nbx lr'))

    def test_altered_runtime_bytes_or_spans_are_refused(self):
        caller = self.owner_body()
        for address, value in ((MOD + 0x10, b'\x00\x00'), (ZERO, b'\x70\x47'), (MOD + 0xCA, b'\x00\x60')):
            with self.subTest(address=hex(address)), self.assertRaisesRegex(ValueError, 'identity differs'):
                owner.verify(**self.fixture(caller, patch=(address, value)))
        f = self.fixture(caller)
        rows = json.loads(f['mapping'])
        for kind in ('end', 'drop-zero', 'mode'):
            changed = copy.deepcopy(rows)
            row = next(r for r in changed if r['rom'] == f'0x{MOD:08X}')
            if kind == 'end':
                row['end'] = '0x08142A20'
            elif kind == 'drop-zero':
                changed = [r for r in changed if r['rom'] != f'0x{ZERO:08X}']
            else:
                row['mode'] = 'arm'
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                owner.verify(**dict(f, mapping=json.dumps(changed).encode()))

    def test_only_exact_entries_are_summarised(self):
        for target in (MOD + 2, ZERO):
            with self.subTest(target=hex(target)), self.assertRaises(ValueError):
                owner.verify(**self.fixture(self.owner_body(runtime=target)))

    def test_summary_contexts_are_narrow(self):
        f = self.fixture(self.owner_body())
        proof = summary.RuntimeSummaryBufferProof(f['rom'], f['mapping'], f['index'], f['objects'])
        stack = [(False, False, True)] * 2
        with self.assertRaisesRegex(ValueError, 'word-provenance'):
            proof.check_arguments(MOD, {}, stack, {}, frozenset(), site=A, words={-8: 1})
        with self.assertRaisesRegex(ValueError, 'R4-R11'):
            proof.check_arguments(MOD, {}, stack, {}, frozenset(), site=A, watched=(match.ARM_REG_R2,))
        with self.assertRaisesRegex(ValueError, 'actual direct call site'):
            proof.check_arguments(MOD, {}, stack, {}, frozenset(), site=None)
        with self.assertRaisesRegex(ValueError, 'may return unchanged'):
            proof.check_arguments(MOD, {match.ARM_REG_R12: -4}, stack, {}, frozenset(), site=A)
        with self.assertRaisesRegex(ValueError, 'may return unchanged'):
            proof.check_arguments(DIV, {match.ARM_REG_R3: -8}, stack, {}, frozenset(), site=A)
        result = proof.check_arguments(MOD, {match.ARM_REG_R3: -8}, stack,
                                       {0: -8}, frozenset({-8}), site=A, watched=(match.ARM_REG_R0 + 4,))
        self.assertEqual(result, {})
        self.assertEqual(proof.callee_clobbers[MOD], frozenset())
        calls = {A + 6: B, A + 18: MOD}
        foreign = summary.RuntimeSummaryBufferProof(f['rom'], f['mapping'], f['index'], f['objects'])
        for context in (dict(divsi3_context=(f['rom'], f['mapping'], {}, {})),
                        dict(ignored_leaf_alias_proof=object()),
                        dict(switch_relocations={}), dict(acyclic_state_budget=16),
                        dict(typed_switch_outgoing_frame=object()), dict(finite_small_copy_context=object()),
                        dict(buffer_proof=None), dict(buffer_proof=buffers.NamedDataBufferProof(
                            f['rom'], f['mapping'], f['index'], f['objects'])),
                        dict(buffer_proof=foreign)):
            with self.subTest(context=sorted(context)), self.assertRaisesRegex(ValueError, 'runtime summar'):
                match.verify_leaf_instructions(f['data'], A, True, calls,
                    **{'buffer_proof': proof, **context}, runtime_summaries=proof.runtime_summaries)

    def test_scratch_inputs_must_be_written_before_read(self):
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        for source, accepted in (('movs r2, #0\nadds r0, r2, #0\nbx lr', {2}),
                                 ('cmp r1, #0\nbeq 1f\nmovs r3, #1\n1:\nmovs r2, #1\nbx lr', {2}),
                                 ('adds r0, r2, #0\nbx lr', None),
                                 ('mov r0, ip\nbx lr', None),
                                 ('cmp r1, #0\nbeq 1f\nmovs r3, #1\n1:\nadds r0, r3, #0\nbx lr', None),
                                 ('push {r4}\nmovs r4, #1\nadds r0, r4, #0\npop {r4}\nbx lr', set()),
                                 ('adds r0, r4, #0\nbx lr', 'caller'),
                                 ('mov r0, sp\nbx lr', 'caller'),
                                 ('mov r2, lr\nbx lr', 'caller'),
                                 ('push {r4}\nmovs r4, #1\npop {r4}\nadds r0, r4, #0\nbx lr', 'caller'),
                                 ('push {r4, lr}\npop {r4, r5}\nadds r0, r4, #0\nadds r0, r5, #0\nbx lr', 'caller'),
                                 ('push {r0}\npop {r4}\nadds r0, r4, #0\nbx lr', set()),
                                 ('bkpt #1\nbx lr', 'transfer')):
            (self.root/'s.s').write_text('.syntax unified\n.thumb\n' + source + '\n')
            subprocess.run(['arm-none-eabi-as', str(self.root/'s.s'), '-o', str(self.root/'s.o')],
                           check=True, capture_output=True)
            subprocess.run(['arm-none-eabi-objcopy', '-O', 'binary', '--only-section=.text',
                            str(self.root/'s.o'), str(self.root/'s.bin')], check=True, capture_output=True)
            decoded = list(decoder.disasm((self.root/'s.bin').read_bytes(), A))
            with self.subTest(source=source):
                if accepted == 'caller':
                    with self.assertRaisesRegex(ValueError, 'frame protocol'):
                        summary.scratch_inputs(decoded, A)
                elif accepted == 'transfer':
                    with self.assertRaises(ValueError):
                        summary.scratch_inputs(decoded, A)
                elif accepted is not None:
                    self.assertEqual({r - match.ARM_REG_R0 for r in summary.scratch_inputs(decoded, A)}, accepted)
                else:
                    with self.assertRaisesRegex(ValueError, 'before writing'):
                        summary.scratch_inputs(decoded, A)

    def test_existing_selectors_keep_refusing_runtimes(self):
        f = self.fixture(self.owner_body())
        for selector in (buffers.SELECTOR, buffers.DATAFREE_SELECTOR, owner.ACYCLIC_SELECTOR,
                         summary.FAST_FILL_SELECTOR):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                owner.verify(**dict(f, selector=selector))

    def test_report_markers(self):
        for selector, schema in summary.SCHEMAS.items():
            marker = f'* verification: `{schema}`\n'
            self.assertEqual(owner.selector_for_report(marker), selector)
            for malformed in (marker * 2, marker + f'* verification: `{buffers.SCHEMA}`\n'):
                with self.subTest(selector=selector), self.assertRaises(ValueError):
                    owner.selected(malformed)


if __name__ == '__main__':
    unittest.main()
