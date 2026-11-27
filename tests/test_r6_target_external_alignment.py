"""Explicit external alignment composed with complete R6 callback effect replay."""
import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import struct
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path[:0] = [str(Path(__file__).resolve().parent),
               str(Path(__file__).resolve().parents[1] / 'tools')]
from test_static_callback_r6_target import fixture, A, W, C, CASE, bl
import match
import report_fixtures
import match_evidence
import owner_admission_profile as owner
import static_callback_r6_frame_profile as policy


def aligned_fixture(**changes):
    worker = changes.pop('worker', None)
    if worker is None:
        values = fixture(**changes)
    else:
        from test_static_callback_r6_target import r7_fixture
        values = r7_fixture(worker=worker, **changes)
    # Move the actual return after the typed callback word. The original return
    # becomes a direct local branch, so every new halfword has a reached role.
    original = values['data']
    literal = values['bindings']['functions'][0][0]
    epilogue = bytes.fromhex('50bc01bc0047')
    site = original.index(epilogue)
    body = bytearray(original[:site] + b'\0\0')
    if len(body) % 4:
        body.extend(b'\0\0')
    new_literal = len(body)
    body.extend(original[literal:literal+4])
    destination = len(body)
    body.extend(epilogue)
    struct.pack_into('<H', body, site, 0xe000 | (((destination-site-4)//2) & 0x7ff))
    struct.pack_into('<H', body, 4, 0x4e00 | ((A+new_literal-((A+8) & ~3))//4))
    values['bindings']['functions'][0][0] = new_literal
    body = bytes(body)
    rows = json.loads(values['mapping'])
    row = next(row for row in rows if int(row['rom'], 16) == A)
    row['end'] = f'0x{A+len(body):08X}'
    rom = bytearray(values['rom'])
    rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)] = body
    lines = values['index'].decode().splitlines()
    for number, line in enumerate(lines):
        fields = line.split()
        if int(fields[0], 16) == A:
            fields[1:3] = [f'{A+len(body):08X}', str(len(body))]
            lines[number] = ' '.join(fields)
    values.update(data=body, rom=bytes(rom), mapping=json.dumps(rows).encode(),
                  index=('\n'.join(lines)+'\n').encode(),
                  selector=policy.ALIGNED_TARGET_SELECTOR)
    return values


def fixed_args():
    return argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP,
        assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY,
        linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)


class AlignmentTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        scratch = Path(os.environ['FFTA_TEST_SCRATCH'])
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix='r6_alignment_', dir=scratch)
        cls.root = Path(cls.temporary.name)
        cls.values = aligned_fixture()
        assert len(cls.values['data']) % 4 == 2
        text = bytearray(cls.values['data'])
        directives = []
        for kind, relocation in (('calls', 'R_ARM_THM_CALL'), ('functions', 'R_ARM_ABS32')):
            for offset, name in cls.values['bindings'][kind]:
                text[offset:offset+4] = bl(A+offset, A+offset) if kind == 'calls' else b'\0'*4
                directives.append(f'.reloc func_{A:08X}+{offset}, {relocation}, {name}')
        source = '\n'.join(['.syntax unified', '.thumb', '.balign 4',
            f'.global func_{A:08X}', f'.type func_{A:08X}, %function', '.thumb_func',
            f'func_{A:08X}:',
            *[f'.inst.n 0x{int.from_bytes(text[offset:offset+2], "little"):04x}'
              for offset in range(0, len(text), 2)],
            f'.size func_{A:08X}, .-func_{A:08X}', *directives, '.balign 4', ''])
        assembly = cls.root/'owner.s'
        assembly.write_text(source)
        assembled = subprocess.run([match.DEFAULT_AS, '-mthumb-interwork', str(assembly),
            '-o', str(cls.root/'owner.o')], text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        if assembled.returncode:
            raise RuntimeError(assembled.stdout)
        cls.original = (cls.root/'owner.o').read_bytes()
        cls.image = match.elf_image(cls.original)
        cls.runner = match.Runner(match.DEFAULT_CC, root=cls.root, timeout=120)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def bindings(self, image=None, selector=policy.ALIGNED_TARGET_SELECTOR):
        values = self.values
        return owner.original_bindings(image or self.image, A, values['rom'],
            values['mapping'], values['objects'], selector=selector, index=values['index'])

    def test_actual_original_link_preserves_external_tail_and_complete_func(self):
        before = copy.deepcopy(self.image)
        bindings, _ = self.bindings()
        self.assertEqual(bindings, self.values['bindings'])
        with self.runner.workspace() as workspace:
            Path(workspace+'/f.o').write_bytes(self.original)
            self.runner.write_text(workspace+'/f.i', '')
            body, actual = owner.object_bytes(self.runner, workspace, fixed_args(),
                self.image, A, self.values['rom'], self.values['mapping'], self.values['objects'],
                selector=policy.ALIGNED_TARGET_SELECTOR, index=self.values['index'])
            linked = match.elf_image(self.runner.read_binary(workspace+'/f.elf'))
        self.assertEqual(body, self.values['data'])
        self.assertEqual(actual, bindings)
        self.assertEqual(linked['text'], body+b'\xc0\x46')
        self.assertEqual(self.image, before)

    def test_external_envelope_rejects_changed_tail_alignment_ownership_and_extent(self):
        for kind in ('tail', 'section_alignment', 'tail_owner', 'foreign_func', 'missing', 'size'):
            image = copy.deepcopy(self.image)
            if kind == 'tail': image['text'] = image['text'][:-2]+b'\0\0'
            elif kind == 'section_alignment':
                section = list(image['sections'][image['text_index']]); section[8] = 2
                image['sections'][image['text_index']] = tuple(section)
            elif kind in ('tail_owner', 'foreign_func'):
                image['symbols'].append(dict(name='other', type=0 if kind=='tail_owner' else 2,
                    section=image['text_index'], value=len(image['text'])-2, size=2, bind=1))
            elif kind == 'missing': image['text'] = image['text'][:-2]
            else: image['symbols'][next(i for i,symbol in enumerate(image['symbols'])
                if symbol['name']==f'func_{A:08X}')]['size'] += 2
            with self.subTest(kind=kind), self.assertRaises(ValueError): self.bindings(image)

    def test_old_r6_selectors_still_refuse_external_alignment(self):
        for selector in (policy.SELECTOR, policy.TARGET_SELECTOR):
            with self.subTest(selector=selector), self.assertRaisesRegex(ValueError, 'sole complete'):
                self.bindings(selector=selector)

    def test_relocation_into_external_tail_is_not_function_evidence(self):
        image = copy.deepcopy(self.image)
        relocation = image['relocations'][0]
        raw = bytearray(image['section_data'][relocation])
        struct.pack_into('<I', raw, 0, len(self.values['data'])-2)
        image['section_data'][relocation] = bytes(raw)
        with self.assertRaisesRegex(ValueError, 'invalid, unsupported or overlapping'):
            self.bindings(image)

    def test_fresh_r6_callback_replay_and_alignment_manifest_are_bound(self):
        manifest, instructions = owner.verify(**self.values)
        self.assertEqual(manifest['profile'], policy.ALIGNED_TARGET_SCHEMA)
        evidence = manifest['proof']['buffers']['r6_restoration']
        self.assertTrue(instructions)
        self.assertTrue(evidence['callback_observations'])
        self.assertIn('normal_return_scratch', evidence)
        self.assertNotIn('r7_observations', evidence)
        self.assertEqual(evidence['policy']['selector'], policy.ALIGNED_TARGET_SELECTOR)
        self.assertEqual(evidence['policy']['terminal_alignment']['producer_sha256'],
            hashlib.sha256((CASE/'tools/addressed_signed_runtime_profile.py').read_bytes()).hexdigest())
        changed = copy.deepcopy(manifest)
        changed['proof']['buffers']['r6_restoration']['policy']['terminal_alignment']['producer_sha256'] = '0'*64
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            owner.verify(**self.values, manifest=changed)

    def test_alignment_does_not_admit_callback_oob_or_register_corruption(self):
        for callback in (bytes.fromhex('01228a6000207047'), bytes.fromhex('002601220a6000207047')):
            with self.subTest(callback=callback.hex()), self.assertRaises(ValueError):
                owner.verify(**aligned_fixture(callback=callback))

    def test_cli_report_fingerprint_and_mixed_schema_refuse_downgrades(self):
        manifest, instructions = owner.verify(**self.values)
        result = (self.values['data'], manifest, 'synthetic source', self.values['mapping'],
            self.values['index'], self.values['objects'], self.values['rom'], len(instructions), self.original)
        report = owner.render(A, result)
        report_fixtures.rom_image(self, self.values['rom'])
        self.assertEqual(owner.selector_for_report(report), policy.ALIGNED_TARGET_SELECTOR)
        with patch.object(owner, 'build', return_value=result) as build:
            self.assertTrue(match_evidence.report_matches(report_fixtures.carried(report, self.root, A), self.root, A))
        self.assertEqual(build.call_args.kwargs['selector'], policy.ALIGNED_TARGET_SELECTOR)
        for schema in (policy.SCHEMA, policy.TARGET_SCHEMA):
            with self.subTest(schema=schema), self.assertRaises(ValueError):
                owner.selected(report+f'* verification: `{schema}`\n')
        with patch.object(sys, 'argv', ['match.py','--root',str(self.root),
                '--owner-runtime-profile',policy.ALIGNED_TARGET_SELECTOR,f'0x{A:08X}']), \
                patch.object(owner, 'issue', return_value=17) as issue:
            self.assertEqual(match.main(),17)
        self.assertEqual(issue.call_args.args[2].owner_runtime_profile,policy.ALIGNED_TARGET_SELECTOR)
        args = (A,*result[:7])
        with self.assertRaisesRegex(ValueError,'original ELF'):
            owner.fingerprint(*args)
        self.assertNotEqual(owner.fingerprint(*args,original_elf=self.original),
                            owner.fingerprint(*args,original_elf=self.original+b'changed'))


if __name__ == '__main__': unittest.main(verbosity=2)
