"""R6 thunk selection and original-object boundaries, using synthetic code only."""
import argparse
import copy
import report_fixtures
import hashlib
from pathlib import Path
import struct
import sys
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
from test_static_callback_r6_frame import A, W, L, C, CASE, bl, fixture as r7_fixture
import match
import match_evidence
import owner_admission_profile as owner
import static_callback_r6_frame_profile as policy
import static_callback_target_preservation_profile as r7
import function_thunk_profile as thunk

THUNK = thunk.ALIASES['_call_via_r6']


def fixture(*, loop=False, **changes):
    # R6 holds the callback and R5 the local payload. Both are saved/restored.
    worker = bytes.fromhex('70b50e1c151c291c') + bl(W+8, THUNK)
    worker += bytes.fromhex('002800d0f9e770bc01bc0047' if loop else '70bc01bc0047')
    values = r7_fixture(worker=worker, **changes)
    values['selector'] = policy.TARGET_SELECTOR
    return values


def result():
    values = fixture()
    manifest, instructions = owner.verify(**values)
    return (values['data'], manifest, 'synthetic-source', values['mapping'],
            values['index'], values['objects'], values['rom'], len(instructions),
            b'synthetic original ELF identity')


def original_image(values):
    text = bytearray(values['data'])
    symbols = [dict(name=f'func_{A:08X}', value=1, size=len(text), type=2, bind=1, section=1)]
    relocations = []
    for kind, binding in (('calls', 10), ('functions', 2)):
        for offset, name in values['bindings'][kind]:
            names = [symbol['name'] for symbol in symbols]
            if name not in names:
                symbols.append(dict(name=name, value=0, size=0, type=0, bind=1, section=0))
            number = [symbol['name'] for symbol in symbols].index(name)
            text[offset:offset+4] = bl(A+offset, A+offset) if binding == 10 else b'\0'*4
            relocations.extend((offset, (number << 8) | binding))
    raw = struct.pack('<'+'I'*len(relocations), *relocations)
    sections = [(0,)*10, (0,1,6,0,0,len(text),0,0,4,0), (0,2,0,0,0,0,0,0,4,16),
                (0,9,0,0,0,len(raw),2,1,4,8)]
    return dict(type=1, sections=sections, text_index=1, text=bytes(text), symbols=symbols,
                relocations=[3], symbol_tables={2:symbols}, section_data=[b'',bytes(text),b'',raw])


class TargetTests(unittest.TestCase):
    def test_explicit_r6_target_replays_effects_and_restores_ordinary_frames(self):
        manifest, instructions = owner.verify(**fixture())
        self.assertTrue(instructions)
        self.assertEqual(manifest['profile'], policy.TARGET_SCHEMA)
        evidence = manifest['proof']['buffers']['r6_restoration']
        self.assertEqual(evidence['policy']['selector'], policy.TARGET_SELECTOR)
        self.assertIn('canonical R6', evidence['policy']['callbacks'])
        self.assertNotIn('r7_observations', evidence)
        self.assertEqual({row['target'] for row in evidence['observations']}, {W, L})
        self.assertEqual(len(evidence['observations']), 3)
        self.assertTrue(all(row['value'] == C+1 for row in evidence['observations']))
        for row in evidence['callback_observations']:
            self.assertEqual((row['thunk'], row['register'], row['value']),
                             (THUNK, policy.REGISTER, C+1))
        worker = next(row for row in evidence['observations'] if row['target'] == W)
        self.assertEqual(worker['calls'][0]['certificate']['address'], C)
        self.assertEqual(worker['calls'][0]['target'], THUNK)

    def test_loop_has_fresh_complete_effects_without_a_scalar_or_termination_claim(self):
        manifest, _ = owner.verify(**fixture(loop=True))
        evidence = manifest['proof']['buffers']['r6_restoration']
        self.assertEqual(len([row for row in evidence['observations'] if row['target'] == W]), 2)
        self.assertEqual(evidence['policy']['returning'], 'conditional compatible normal return only')

    def test_old_and_new_target_selection_cannot_be_interchanged(self):
        values = fixture(); values['selector'] = policy.SELECTOR
        with self.assertRaises(ValueError): owner.verify(**values)
        values = r7_fixture(); values['selector'] = policy.TARGET_SELECTOR
        with self.assertRaises(ValueError): owner.verify(**values)
        self.assertIn('canonical R7', policy.policy_manifest()['callbacks'])
        self.assertEqual(policy.policy_manifest()['selector'], policy.SELECTOR)

    def test_saved_register_corruption_and_unbalanced_sp_are_refused(self):
        for register in range(4, 8):
            body = struct.pack('<H', 0x2000 | (register << 8)) + bytes.fromhex('01220a6000207047')
            with self.subTest(register=register), self.assertRaises(ValueError):
                owner.verify(**fixture(callback=body))
        for body in ('804601220a6000207047', '81b001220a6000207047'):
            with self.subTest(body=body), self.assertRaises(ValueError):
                owner.verify(**fixture(callback=bytes.fromhex(body)))

    def test_bounds_escape_and_unpreserved_nested_calls_stay_rejected(self):
        for body, message in (('01228a6000207047', 'outside allocated'),
                              ('016000207047', 'pointer use or escape')):
            with self.subTest(body=body), self.assertRaisesRegex(ValueError, message):
                owner.verify(**fixture(callback=bytes.fromhex(body)))
        body = bytes.fromhex('00b5') + bl(C+2, L) + bytes.fromhex('01bc0047')
        with self.assertRaises(ValueError):
            owner.verify(**fixture(callback=body, leaf=bytes.fromhex('00247047')))

    def test_framed_callback_replays_nested_effects_and_saved_register_restoration(self):
        body = bytes.fromhex('10b50c1c') + bl(C+4, L)
        body += bytes.fromhex('211c01220a60002010bc02bc0847')
        manifest, _ = owner.verify(**fixture(callback=body))
        evidence = manifest['proof']['buffers']['r6_restoration']
        worker = next(row for row in evidence['observations'] if row['target'] == W)
        callback = worker['calls'][0]['certificate']
        self.assertEqual(callback['address'], C)
        self.assertEqual(callback['calls'][0]['target'], L)
        self.assertEqual(callback['frame']['external_calls'], 'complete-native-callee-preservation-v1')
        # The exact target and replay guard remain unwritten even with a frame.
        for write in ('0026', '8346'):
            damaged = body[:4]+bytes.fromhex(write)+bl(C+6,L)+body[8:]
            with self.subTest(write=write), self.assertRaises(ValueError):
                owner.verify(**fixture(callback=damaged))

    def test_balanced_private_stack_frame_is_replayed_instead_of_assumed_leaf(self):
        body = bytes.fromhex('81b001220a6001b000207047')
        manifest, _ = owner.verify(**fixture(callback=body))
        evidence = manifest['proof']['buffers']['r6_restoration']
        self.assertTrue(evidence['callback_observations'])

    def test_return_scratch_requires_an_unobserving_complete_consumer(self):
        worker = bytes.fromhex('70b50e1c151c002802d0291c') + bl(W+12,THUNK)
        worker += bytes.fromhex('70bc01bc0047')
        values = r7_fixture(worker=worker); values['selector'] = policy.TARGET_SELECTOR
        body = bytearray(values['data']); offset = values['bindings']['calls'][0][0]+4
        body[offset:offset+2] = bytes.fromhex('0022')
        rom = bytearray(values['rom']); rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)] = body
        values.update(data=bytes(body), rom=bytes(rom))
        manifest, _ = owner.verify(**values)
        evidence = manifest['proof']['buffers']['r6_restoration']
        self.assertEqual(evidence['policy']['normal_return_scratch']['registers'], [2,3])
        self.assertTrue(evidence['normal_return_scratch'])
        self.assertTrue(all(row['consumer'] == A for row in evidence['normal_return_scratch']))
        # The continuation's real R2 use must reject projection, even though the
        # selector separately states a compatible normal-return ABI premise.
        body = bytearray(values['data'])
        body[offset:offset+2] = bytes.fromhex('111c')
        rom = bytearray(values['rom']); rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)] = body
        with self.assertRaisesRegex(ValueError, 'observes projected return scratch'):
            owner.verify(**dict(values, data=bytes(body), rom=bytes(rom)))

    def test_actual_r0_and_r1_local_pointer_returns_are_never_projected(self):
        for register in (0,1):
            # Copy the payload held in R5 into a real result register after the
            # callback; no normal-return scratch premise covers these results.
            worker = bytes.fromhex('70b50e1c151c291c') + bl(W+8,THUNK)
            worker += struct.pack('<H',0x1c28 | register) + bytes.fromhex('70bc01bc0047')
            values = r7_fixture(worker=worker); values['selector'] = policy.TARGET_SELECTOR
            # Preserve the real result register through the root's epilogue.
            # Its return address is popped into R3, outside the result pair.
            body = bytearray(values['data']); offset = values['bindings']['calls'][-1][0]+4
            body[offset:offset+2] = bytes.fromhex('0022')
            self.assertEqual(body[offset+6:offset+10], bytes.fromhex('01bc0047'))
            body[offset+6:offset+10] = bytes.fromhex('08bc1847')
            rom = bytearray(values['rom']); rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)] = body
            values.update(data=bytes(body), rom=bytes(rom))
            with self.subTest(register=register), self.assertRaises(ValueError):
                owner.verify(**values)

    def test_ordinary_saved_slots_return_guard_and_restore_stay_required(self):
        for body in ('70b50020009070bc01bc0047', '00267047', '83467047', '0047'):
            with self.subTest(body=body), self.assertRaises(ValueError):
                owner.verify(**fixture(leaf=bytes.fromhex(body)))

    def test_exact_thunk_bytes_and_typed_callback_binding_remain_required(self):
        values = fixture()
        for name in ('calls', 'functions'):
            bindings = copy.deepcopy(values['bindings']); bindings[name] = []
            with self.subTest(name=name), self.assertRaises(ValueError):
                owner.verify(**dict(values, bindings=bindings))
        rom = bytearray(values['rom']); rom[THUNK-match.ROM_BASE] ^= 8
        with self.assertRaises(ValueError): owner.verify(**dict(values, rom=bytes(rom)))

    def test_copied_reused_or_changed_ordinary_receipts_do_not_restore_constants(self):
        values = fixture()
        for mutation in ('copy', 'reuse', 'aliases', 'site', 'target', 'value'):
            proof = policy.R6FrameCallbackProof(values['rom'], values['mapping'], values['index'],
                                                values['objects'], policy=policy.TARGET_SELECTOR)
            constants = {policy.REGISTER: C+1}
            receipt = proof.check_arguments(L, {}, [(False,False,True)], {}, frozenset(),
                                             constants=constants, site=A)
            finish = dict(site=A, target=L)
            if mutation == 'copy': receipt = dict(receipt)
            elif mutation == 'aliases': receipt[match.ARM_REG_R0] = -4
            elif mutation == 'site': finish['site'] += 2
            elif mutation == 'target': finish['target'] = W
            elif mutation == 'value': constants[policy.REGISTER] = C+3
            if mutation in ('aliases', 'site', 'target', 'value'):
                with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                    proof.finish_call_constants(constants, receipt, **finish)
            else:
                proof.finish_call_constants(constants, receipt, **finish)
                if mutation == 'reuse': proof.finish_call_constants(constants, receipt, **finish)
                self.assertNotIn(policy.REGISTER, constants)

    def test_explicit_policy_and_closed_native_type_are_required(self):
        values = fixture()
        class Other(policy.R6FrameCallbackProof): pass
        proof = Other(values['rom'], values['mapping'], values['index'], values['objects'],
                      policy=policy.TARGET_SELECTOR)
        self.assertFalse(match._ordinary_call_replay(proof))
        with self.assertRaises(ValueError): policy.policy_manifest('unknown')

    def test_report_and_cli_select_exact_new_policy_and_bind_producer_bytes(self):
        argv = ['match.py', '--root', str(CASE/'scratch'), '--owner-runtime-profile',
                policy.TARGET_SELECTOR, f'0x{A:08X}']
        with patch.object(sys, 'argv', argv), patch.object(owner, 'issue', return_value=19) as issue:
            self.assertEqual(match.main(), 19)
        self.assertEqual(issue.call_args.args[2].owner_runtime_profile, policy.TARGET_SELECTOR)
        r = result(); report = owner.render(A, r)
        report_fixtures.rom_image(self, r[6])
        self.assertEqual(owner.selector_for_report(report), policy.TARGET_SELECTOR)
        self.assertIn('* owner runtime: '+policy.TARGET_SELECTOR, report)
        with patch.object(owner, 'build', return_value=r) as build:
            self.assertTrue(match_evidence.report_matches(report_fixtures.carried(report, CASE/'scratch', A), CASE/'scratch', A))
        self.assertEqual(build.call_args.kwargs, dict(expected=r[1], selector=policy.TARGET_SELECTOR))
        pins = r[1]['proof']['buffers']['r6_restoration']['policy']['source_sha256']
        for filename, digest in pins.items():
            self.assertEqual(digest, hashlib.sha256((CASE/'tools'/filename).read_bytes()).hexdigest())
        for extra in (f'* verification: `{policy.SCHEMA}`\n', f'* verification: `{r7.SCHEMA}`\n'):
            with self.assertRaises(ValueError): owner.selected(report+extra)

    def test_tampered_manifest_and_missing_original_identity_are_rejected(self):
        r = result()
        for mutation in ('policy', 'observations', 'effects', 'source', 'body'):
            manifest = copy.deepcopy(r[1]); evidence = manifest['proof']['buffers']
            if mutation == 'policy': evidence['r6_restoration']['policy']['selector'] = policy.SELECTOR
            elif mutation == 'observations': evidence['r6_restoration']['callback_observations'] = []
            elif mutation == 'effects': evidence['callbacks'] = []
            elif mutation == 'source': evidence['r6_restoration']['policy']['source_sha256']['match.py'] = '0'*64
            else: evidence['dependencies'][0]['body_sha256'] = '0'*64
            with self.subTest(mutation=mutation), self.assertRaisesRegex(ValueError, 'manifest differs'):
                owner.verify(**fixture(), manifest=manifest)
        with self.assertRaisesRegex(ValueError, 'original ELF identity'):
            owner.fingerprint(A, *r[:7])

    def test_original_et_rel_relocations_remain_the_typed_identity_authority(self):
        values = fixture(); image = original_image(values)
        bindings, targets = owner.original_bindings(image, A, values['rom'], values['mapping'],
                                                   values['objects'], selector=policy.TARGET_SELECTOR)
        self.assertEqual(bindings, values['bindings'])
        self.assertEqual(targets[f'func_{C:08X}'], (C,False))
        offset = values['bindings']['functions'][0][0]
        for mutation in ('addend', 'symbol_kind', 'extra_function', 'relocation_kind'):
            changed = copy.deepcopy(image)
            if mutation == 'addend': changed['text'] = changed['text'][:offset]+struct.pack('<I', 4)
            elif mutation == 'symbol_kind': changed['symbols'][-1]['type'] = 1
            elif mutation == 'extra_function': changed['symbols'].append(dict(changed['symbols'][0], name='extra'))
            else:
                raw = bytearray(changed['section_data'][3]); struct.pack_into('<I', raw, len(raw)-4, (3<<8)|3)
                changed['section_data'][3] = bytes(raw)
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                owner.original_bindings(changed, A, values['rom'], values['mapping'],
                                        values['objects'], selector=policy.TARGET_SELECTOR)

    def test_linked_function_must_match_full_text_and_original_relocation_sites(self):
        values = fixture(); original = original_image(values); linked = copy.deepcopy(original)
        linked.update(type=2, text=values['data'], relocations=[])
        linked['symbols'][0]['value'] = A+1
        section = list(linked['sections'][1]); section[3] = A; linked['sections'][1] = tuple(section)
        args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                                  objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        class Runner:
            def read_binary(self, path): return b'' if path.endswith('/f.i') else b'synthetic linked ELF'
            def write_text(self, path, text): pass
            def sh(self, command): pass
        with patch.object(match, 'elf_image', return_value=linked):
            body, bindings = owner.object_bytes(Runner(), 'synthetic', args, original, A,
                values['rom'], values['mapping'], values['objects'], selector=policy.TARGET_SELECTOR)
        self.assertEqual((body,bindings), (values['data'],values['bindings']))
        for mutation in ('text', 'call', 'size', 'relocation'):
            changed = copy.deepcopy(linked)
            if mutation == 'text': changed['text'] = b'\0\0'+changed['text'][2:]
            elif mutation == 'call':
                site = values['bindings']['calls'][0][0]
                changed['text'] = changed['text'][:site]+bl(A+site,C)+changed['text'][site+4:]
            elif mutation == 'size': changed['symbols'][0]['size'] -= 2
            else: changed['relocations'] = [3]
            with self.subTest(mutation=mutation), patch.object(match, 'elf_image', return_value=changed), self.assertRaises(ValueError):
                owner.object_bytes(Runner(), 'synthetic', args, original, A, values['rom'],
                    values['mapping'], values['objects'], selector=policy.TARGET_SELECTOR)

    def test_mixed_runtime_profiles_refuse_before_any_compilation(self):
        args = argparse.Namespace(owner_runtime_profile=policy.TARGET_SELECTOR, mode='thumb',
            control_flow_profile='ordinary', software_double_profile=None, software_double_remainder_profile=None,
            function_address_profile=None, switch_profile=None, label='', wsl='Ubuntu', wsl_path=match.DEFAULT_WSL_PATH,
            signed_quotient_profile='other', signed_runtime_profile=None, addressed_signed_runtime_profile=None,
            switch_data_profile=None)
        with patch.object(owner, 'build') as build, self.assertRaises(ValueError):
            owner.issue(CASE/'scratch', A, args)
        build.assert_not_called()


if __name__ == '__main__': unittest.main(verbosity=2)
