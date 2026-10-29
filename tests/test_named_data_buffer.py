"""Named data and finite buffer effects retain original ELF and fresh replay."""
import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import shutil
import struct
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import match_evidence
import named_data_buffer_profile as buffers
import owner_admission_profile as owner

A, B, SWITCH = 0x08010000, 0x08011000, 0x080C8570
SOURCE = '''extern unsigned int data_02000000[2];
extern void func_08011000(unsigned char *bytes);
extern unsigned int func_080C8570(unsigned char a, unsigned char b,
                                unsigned char c, unsigned char *bytes);
unsigned int func_08010000(unsigned int value)
{
    unsigned char bytes[4];
    bytes[0] = value;
    func_08011000(bytes);
    return data_02000000[1] + func_080C8570(value, 2, 3, bytes) + bytes[0];
}
'''
LEAF = '''void func_08011000(unsigned char *bytes)
{
    bytes[0] += 3;
}
'''


def fixture(root, approved_rom):
    """Natural synthetic C caller/leaf, plus one exact original read-only callee."""
    root = Path(root)
    for name in ('src', 'include', 'config', 'symbols', 'build', 'original-elf'):
        (root / name).mkdir(parents=True, exist_ok=True)
    if hashlib.sha256(approved_rom).hexdigest() != \
            '43fc8204c6dceee58828aebc7af0c72eb807e99f35ad641c8bb0a4fa8b6edc19':
        raise ValueError('fixture requires the exact approved original ROM')
    args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP,
        assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD,
        flags=match.DEFAULT_FLAGS)
    (root/'src/08010000.c').write_text(SOURCE)
    dependency = root/'src/08011000.c'
    dependency.write_text(LEAF)
    (root/'original-elf/08011000.c').write_text(LEAF)
    objects = b'{"data_02000000":"0x02000000"}\n'
    switch = approved_rom[SWITCH-match.ROM_BASE:SWITCH-match.ROM_BASE+1204]
    rom = bytearray(SWITCH-match.ROM_BASE+len(switch))
    rom[SWITCH-match.ROM_BASE:] = switch
    runner = match.Runner(match.DEFAULT_CC, 'Ubuntu', match.DEFAULT_WSL_PATH,
                          root=root, timeout=120)
    with runner.workspace() as workspace:
        leaf_object, leaf, _ = match.compile_object(runner, workspace, args, root, B,
                                                   'src/08011000.c')
        (root/'original-elf/08011000.o').write_bytes(leaf_object)
        dependency.unlink()
        original, body, image = match.compile_object(runner, workspace, args, root, A,
                                                     'src/08010000.c')
        (root/'original-elf/08010000.o').write_bytes(original)
        rows = [{'rom': f'0x{address:08X}', 'end': f'0x{address+size:08X}',
                 'mode': 'thumb', 'instrs': 0} for address,size in
                ((A,len(body)), (B,len(leaf)), (SWITCH,len(switch)))]
        mapping = json.dumps(rows).encode()
        data, bindings = owner.object_bytes(runner,workspace,args,image,A,bytes(rom),mapping,objects,
                                            selector=buffers.SELECTOR)
    rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)] = data
    rom[B-match.ROM_BASE:B-match.ROM_BASE+len(leaf)] = leaf
    rows[0]['instrs'] = owner.refine(data,A,mapping)['instrs']
    rows[1]['instrs'] = owner.refine(leaf,B,mapping)['instrs']
    rows[2]['instrs'] = 501
    mapping = json.dumps(rows, indent=2).encode()
    index = ''.join(f'{int(row["rom"],16):08X} {int(row["end"],16):08X} '
                    f'{int(row["end"],16)-int(row["rom"],16)} {row["instrs"]} return\n'
                    for row in rows).encode()
    (root/'config/functions.json').write_bytes(mapping)
    (root/'config/data_symbols.json').write_bytes(objects)
    (root/'symbols/functions.txt').write_bytes(index)
    (root/'baserom.bin').write_bytes(rom)
    return data, bindings, original


class SelectionTests(unittest.TestCase):
    def test_explicit_separate_schema_and_mixed_refusal(self):
        marker = f'* verification: `{buffers.SCHEMA}`\n'
        self.assertEqual(owner.selector_for_report(marker), buffers.SELECTOR)
        self.assertFalse(owner.selected('* verification: `ordinary`\n'))
        for report in (marker*2, marker+'* buffer calls: legacy\n',
                       marker+f'* verification: `{owner.ACYCLIC_SCHEMA}`\n'):
            with self.subTest(report=report), self.assertRaises(ValueError):
                owner.selected(report)


@unittest.skipUnless(os.environ.get('FFTA_NAMED_BUFFER_TEST_ROM') and
                     Path(os.path.expandvars(match.DEFAULT_CC)).is_file() and
                     shutil.which('arm-none-eabi-ld'), 'approved ROM and fixed compiler required')
class NativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        scratch = Path(os.environ.get('TMPDIR', Path.cwd()/'build/tests'))
        scratch.mkdir(parents=True,exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix='named_buffer_',dir=scratch)
        cls.root = Path(cls.temporary.name)
        cls.data,cls.bindings,cls.original = fixture(cls.root,
            Path(os.environ['FFTA_NAMED_BUFFER_TEST_ROM']).read_bytes())
        cls.environment = patch.dict(os.environ,FFTA_ROM=str(cls.root/'baserom.bin'))
        cls.environment.start()
        cls.result = owner.build(cls.root,A,selector=buffers.SELECTOR)
        cls.report = owner.render(A,cls.result)

    @classmethod
    def tearDownClass(cls):
        cls.environment.stop()
        cls.temporary.cleanup()

    def replay(self,**changes):
        result = self.result
        values = dict(data=result[0],address=A,rom=result[6],mapping=result[3],index=result[4],
                      objects=result[5],manifest=result[1],selector=buffers.SELECTOR)
        values.update(changes)
        return owner.verify(**values)

    def test_natural_c_original_elf_and_exact_switch_dependency(self):
        self.assertEqual(self.result[8],self.original)
        self.assertEqual(match.elf_image(self.original)['type'],1)
        proof = self.result[1]['proof']['buffers']['dependencies']
        self.assertEqual({row['address'] for row in proof},{B,SWITCH})
        switch = next(row for row in proof if row['address']==SWITCH)
        self.assertEqual(switch['structure']['instructions'],501)
        self.assertEqual(switch['structure']['switch']['bound'],47)
        self.assertNotIn('body',switch)
        self.assertTrue(self.replay())

    def test_default_and_both_old_buffer_versions_still_refuse(self):
        calls = {A+offset:int(name[5:],16) for offset,name in self.bindings['calls']}
        for stack in (False,True):
            proof = match.BufferCallProof(self.result[6],self.result[3],stack_arguments=stack)
            reason = 'program-counter write' if stack else 'pointer escapes through a return register'
            with self.subTest(stack=stack), self.assertRaisesRegex(ValueError,reason):
                match.verify_leaf_instructions(self.data,A,True,calls,buffer_proof=proof)
        with self.assertRaises(ValueError):
            self.replay(selector=owner.ACYCLIC_SELECTOR)

    def test_fresh_report_and_original_elf_fingerprint(self):
        self.assertTrue(match_evidence.report_matches(self.report,self.root,A))
        self.assertIn(hashlib.sha256(self.original).hexdigest(),self.report)
        changed = self.report.replace('"original_elf_sha256":"','"original_elf_sha256":"0')
        self.assertFalse(match_evidence.report_matches(changed,self.root,A))

    def test_stale_source_and_objects_refused(self):
        for filename in ('src/08010000.c','config/data_symbols.json','symbols/functions.txt'):
            path = self.root/filename
            original = path.read_bytes()
            try:
                path.write_bytes(original+b'\n')
                self.assertFalse(match_evidence.report_matches(self.report,self.root,A))
            finally:
                path.write_bytes(original)

    def test_every_typed_binding_and_dependency_identity_required(self):
        for key in ('data','calls'):
            manifest = copy.deepcopy(self.result[1])
            manifest['bindings'][key].pop()
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.replay(manifest=manifest)
        manifest = copy.deepcopy(self.result[1])
        manifest['proof']['buffers']['dependencies'][0]['body_sha256'] = '0'*64
        with self.assertRaises(ValueError):
            self.replay(manifest=manifest)

    def test_switch_table_guard_and_saved_control_writes_refused(self):
        # Change original dependency bytes and image together, so rejection
        # must come from structure/effects rather than a stale ROM comparison.
        for offset,replacement in ((0x1a,b'\x2e\x2d'),
                (0x30,struct.pack('<I',SWITCH+0x2c)),
                (0x10,b'\x00\x90')):
            rom = bytearray(self.result[6])
            start = SWITCH-match.ROM_BASE+offset
            rom[start:start+len(replacement)] = replacement
            with self.subTest(offset=offset), self.assertRaises(ValueError):
                self.replay(rom=bytes(rom),manifest=None,bindings=self.bindings)

    def test_incoming_pointer_preserved_into_any_case_is_still_bounded(self):
        rom = bytearray(self.result[6])
        position = SWITCH-match.ROM_BASE+0x14
        self.assertEqual(rom[position:position+2],b'\x0b\x18')
        rom[position:position+2] = b'\x1b\x1c'  # retain incoming r3 instead of overwriting it
        with self.assertRaisesRegex(ValueError,'outside allocated local words|pointer use or escape'):
            self.replay(rom=bytes(rom),manifest=None,bindings=self.bindings)

    def test_missing_or_ambiguous_maps_and_malformed_elf_refused(self):
        rows = json.loads(self.result[3])
        for changed in (rows[:-1],rows+[dict(rows[-1])]):
            with self.assertRaises(ValueError):
                self.replay(mapping=json.dumps(changed).encode())
        malformed = copy.deepcopy(rows)
        malformed[0]['instrs'] = 'not a count'
        with self.assertRaisesRegex(ValueError,'instruction-count annotation'):
            self.replay(mapping=json.dumps(malformed).encode())
        with self.assertRaisesRegex(ValueError,'instruction-count annotation'):
            self.replay(index=self.result[4].replace(b' 501 return',b' bad return'))
        duplicate = self.result[3].replace(b'"instrs":',b'"instrs": 0, "instrs":',1)
        with self.assertRaisesRegex(ValueError,'duplicate named-data buffer mapping key'):
            self.replay(mapping=duplicate)
        image = match.elf_image(self.original)
        image['type'] = 2
        with self.assertRaisesRegex(ValueError,'original relocatable ELF'):
            owner.original_bindings(image,A,self.result[6],self.result[3],self.result[5],
                                    selector=buffers.SELECTOR)


if __name__ == '__main__':
    unittest.main(verbosity=2)
