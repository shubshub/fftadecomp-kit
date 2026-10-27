"""Exact inert error-halting paths compose with canonical binary64 calls."""
import copy
import io
from contextlib import redirect_stdout
import json
from pathlib import Path
import struct
import sys
import unittest
from unittest.mock import patch
import test_software_double_profile as fixture

BASE, match, profile = fixture.BASE, fixture.match, fixture.profile
SOURCE = '''double func_08000000(int count, double value)
{
    if (count <= 2)
        for (;;)
            ;
    return value + 1.0;
}
'''


class SoftwareDoubleSpinTests(unittest.TestCase):
    setUpClass = classmethod(fixture.SoftwareDoubleTests.setUpClass.__func__)
    setUp = fixture.SoftwareDoubleTests.setUp
    indexes = fixture.SoftwareDoubleTests.indexes
    patched_rom = fixture.SoftwareDoubleTests.patched_rom

    def fixture(self, source=SOURCE, spin=True):
        (self.root/'src/08000000.c').write_text(source)
        runner = match.Runner(match.DEFAULT_CC, root=self.root, timeout=120)
        with runner.workspace() as workspace:
            _, _, self.original = match.compile_object(
                runner, workspace, self.args, self.root, BASE, 'src/08000000.c')
            symbol, _ = match.function_record(self.original, 'func_08000000', BASE, True)
            self.indexes(symbol['size'], 1)
            self.body, self.calls, self.bindings = profile.object_bytes(
                runner, workspace, self.args, self.original, BASE, self.mapping,
                self.runtime_rom, self.index)
        rom = bytearray(self.runtime_rom); rom[:len(self.body)] = self.body
        self.rom = bytes(rom)
        self.context = {} if spin else None
        self.instructions = match.verify_leaf_instructions(
            self.body, BASE, True, self.calls,
            double_context=(self.rom, self.mapping, self.index, self.bindings),
            inert_spin_context=self.context)
        self.indexes(len(self.body), len(self.instructions))
        (self.root/'config/functions.json').write_bytes(self.mapping)
        (self.root/'symbols/functions.txt').write_bytes(self.index)
        self.manifest = profile.make_manifest(self.calls, BASE, self.bindings,
            self.instructions, spins=self.context['spins'] if spin else None)

    def verify(self, manifest=None, **kwargs):
        return profile.verify(self.body, BASE, kwargs.get('rom', self.rom),
            kwargs.get('mapping', self.mapping), kwargs.get('index', self.index),
            self.manifest if manifest is None else manifest)

    def native_report(self):
        opening, reading = self.patched_rom()
        with opening, reading, patch.object(sys, 'argv', ['match.py','--root',str(self.root),
                '--software-double-profile',profile.SELECTOR,'0x08000000']), \
                patch.object(match, 'ROOT', match.ROOT), redirect_stdout(io.StringIO()):
            self.assertEqual(match.main(), 0)
        return (self.root/'docs/match/08000000.md').read_text()

    def test_natural_error_halt_original_elf_and_report_replay(self):
        self.fixture()
        self.assertEqual(set(self.bindings.values()), {'__adddf3'})
        self.assertEqual(len(self.context['spins']), 1)
        self.assertEqual(self.manifest['inert_spin'], {
            'schema': profile.INERT_SPIN_SCHEMA, 'spins': self.context['spins']})
        self.assertEqual(len(self.verify()),len(self.instructions))
        self.assertEqual({s['name'] for s in self.original['symbols'] if not s['section'] and s['name']},
                         {'__adddf3'})
        report=self.native_report()
        self.assertIn('* control flow: '+match.inert_spin.CONTROL_FLOW,report)
        self.assertTrue(profile.selected(report))
        self.assertFalse(match.inert_spin.selected(report))
        opening, reading = self.patched_rom()
        with opening, reading:
            self.assertTrue(profile.report_matches(report,self.root,BASE))
            self.assertFalse(profile.report_matches(report.replace(match.inert_spin.CONTROL_FLOW,
                                          'closed leaf CFG'),self.root,BASE))
            path=self.root/'src/08000000.c'
            path.write_text(SOURCE.replace('<= 2','<= 3'))
            self.assertFalse(profile.report_matches(report,self.root,BASE))

    def test_manifest_must_pin_exact_policy_and_every_offset(self):
        self.fixture()
        for kind in ('missing','empty','schema','offset','float','duplicate','extra'):
            manifest=copy.deepcopy(self.manifest)
            if kind=='missing': del manifest['inert_spin']
            elif kind=='empty': manifest['inert_spin']['spins']=[]
            elif kind=='schema': manifest['inert_spin']['schema']='other'
            elif kind=='offset': manifest['inert_spin']['spins'][0]+=2
            elif kind=='float': manifest['inert_spin']['spins'][0]=float(self.context['spins'][0])
            elif kind=='duplicate': manifest['inert_spin']['spins']*=2
            else: manifest['inert_spin']['extra']=True
            with self.subTest(kind=kind),self.assertRaises(ValueError): self.verify(manifest)

    def test_non_self_branch_body_count_and_unproved_call_reject(self):
        self.fixture()
        for word in (0xD0FE, 0xE7FD, 0x4770):
            changed=bytearray(self.body);struct.pack_into('<H',changed,self.context['spins'][0],word)
            rom=bytearray(self.rom);rom[:len(changed)]=changed
            with self.subTest(word=word),self.assertRaises(ValueError):
                profile.verify(bytes(changed),BASE,bytes(rom),self.mapping,self.index,self.manifest)
        entries=json.loads(self.mapping);entries[0]['instrs']+=1
        with self.assertRaisesRegex(ValueError,'count'):
            self.verify(mapping=json.dumps(entries).encode())
        bindings=dict(self.bindings);bindings[next(iter(bindings))]='__subdf3'
        with self.assertRaises(ValueError):
            match.verify_leaf_instructions(self.body,BASE,True,self.calls,
                double_context=(self.rom,self.mapping,self.index,bindings),inert_spin_context={})
        with self.assertRaisesRegex(ValueError,'arithmetic runtimes'):
            match.verify_leaf_instructions(self.body,BASE,True,self.calls,inert_spin_context={})
        with self.assertRaisesRegex(ValueError,'no path to a verified return'):
            match.verify_leaf_instructions(self.body,BASE,True,self.calls,
                double_context=(self.rom,self.mapping,self.index,self.bindings))

    def test_no_spin_report_stays_ordinary_and_stale_or_mixed_marker_rejects(self):
        self.fixture('double func_08000000(int count,double value) { return value+1.0; }\n',False)
        self.assertNotIn('inert_spin',self.manifest)
        self.verify()
        report=self.native_report()
        self.assertNotIn(profile.INERT_SPIN_SCHEMA,report)
        opening,reading=self.patched_rom()
        with opening,reading:
            self.assertTrue(profile.report_matches(report,self.root,BASE))
            self.assertFalse(profile.report_matches(report+'\n* inert spins: forged',self.root,BASE))
        with self.assertRaisesRegex(ValueError,'requires a reachable nonreturning'):
            match.verify_leaf_instructions(self.body,BASE,True,self.calls,
                double_context=(self.rom,self.mapping,self.index,self.bindings),inert_spin_context={})


if __name__=='__main__': unittest.main()
