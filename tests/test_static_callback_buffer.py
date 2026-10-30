"""Natural fixed-compiler callback fixtures and source-bound fresh replay."""
import argparse
import copy
import json
import os
from pathlib import Path
import shutil
import struct
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import match_evidence
import function_thunk_profile as thunk
import owner_admission_profile as owner
import static_callback_buffer_profile as buffers

A, B, C, D = 0x08010000, 0x08011000, 0x08012000, 0x08013000
SOURCE = '''extern void func_08011000(unsigned char *, void (*)(unsigned char *));
extern void func_08012000(unsigned char *);
unsigned int func_08010000(unsigned int value)
{
    unsigned char bytes[4];
    bytes[0] = value;
    func_08011000(bytes, func_08012000);
    return bytes[0];
}
'''
WORKER = '''void func_08011000(unsigned char *bytes, void (*callback)(unsigned char *))
{
    callback(bytes);
}
'''
LEAF = '''void func_08012000(unsigned char *bytes)
{
    bytes[0] += 1;
}
'''
BAD = '''void func_08013000(unsigned char *bytes)
{
    bytes[8] = 1;
}
'''


def fixture(root, source=SOURCE, worker=WORKER, leaf=LEAF):
    root = Path(root)
    for name in ('src', 'include', 'config', 'symbols', 'build', 'original-elf'):
        (root/name).mkdir(parents=True, exist_ok=True)
    args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP,
        assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD,
        flags=match.DEFAULT_FLAGS)
    sources = {A: source, B: worker, C: leaf, D: BAD}
    raw, images, sizes = {}, {}, {}
    runner = match.Runner(match.DEFAULT_CC, 'Ubuntu', match.DEFAULT_WSL_PATH, root=root, timeout=120)
    rom = bytearray(thunk.END-match.ROM_BASE)
    # Generic compiler-runtime instructions, unrelated to any extracted game body.
    for register in range(13):
        struct.pack_into('<HH', rom, thunk.START-match.ROM_BASE+4*register,
                         0x4700+(register<<3), 0x46c0)
    with runner.workspace() as workspace:
        for address, text in sources.items():
            path = root/f'src/{address:08X}.c'; path.write_text(text)
            raw[address], body, images[address] = match.compile_object(runner, workspace, args,
                root, address, path.relative_to(root).as_posix())
            (root/f'original-elf/{address:08X}.o').write_bytes(raw[address])
            (root/f'original-elf/{address:08X}.c').write_text(text)
            sizes[address] = match.function_record(images[address],f'func_{address:08X}',address,True)[0]['size']
            path.unlink()
        rows = [{'rom':f'0x{address:08X}', 'end':f'0x{address+size:08X}',
                 'mode':'thumb', 'instrs':0} for address,size in sizes.items()]
        rows += [{'rom':f'0x{address:08X}', 'end':f'0x{address+2:08X}',
                  'mode':'thumb', 'instrs':1} for address in thunk.ALIASES.values()]
        mapping = json.dumps(rows).encode()
        for address in (C,D,B,A):
            # Recompile in its own pristine workspace to retain exact preprocessing.
            path = root/f'src/{address:08X}.c'; path.write_text(sources[address])
            original, _, image = match.compile_object(runner, workspace, args, root, address,
                                                      path.relative_to(root).as_posix())
            if address == B:
                body, _, _, _ = thunk.object_bytes(runner, workspace, args, image, address,
                                                   mapping, bytes(rom), b'{}')
            elif address in (C,D):
                body = image["text"]
            else:
                body, bindings = owner.object_bytes(runner, workspace, args, image, address,
                    bytes(rom), mapping, b'{}', selector=buffers.SELECTOR)
            body = body[:sizes[address]]
            rom[address-match.ROM_BASE:address-match.ROM_BASE+len(body)] = body
            if address != A: path.unlink()
    for row in rows[:4]:
        address,end = int(row['rom'],16),int(row['end'],16)
        row['instrs'] = owner.refine(bytes(rom[address-match.ROM_BASE:end-match.ROM_BASE]),
                                      address,mapping)['instrs']
    mapping = json.dumps(rows,indent=2).encode()
    index = ''.join(f'{int(row["rom"],16):08X} {int(row["end"],16):08X} '
                    f'{int(row["end"],16)-int(row["rom"],16)} {row["instrs"]} return\n'
                    for row in rows).encode()
    for name, data in (('config/functions.json',mapping), ('symbols/functions.txt',index),
                       ('config/data_symbols.json',b'{}'), ('baserom.bin',bytes(rom))):
        (root/name).write_bytes(data)
    return bytes(rom[A-match.ROM_BASE:A-match.ROM_BASE+sizes[A]]), bindings, raw[A]


class SelectionTests(unittest.TestCase):
    def test_isolated_versioned_schema(self):
        marker = f'* verification: `{buffers.SCHEMA}`\n'
        self.assertEqual(owner.selector_for_report(marker), buffers.SELECTOR)
        for report in (marker*2, marker+'* buffer calls: legacy\n',
                       marker+f'* verification: `{owner.named_buffer.SCHEMA}`\n'):
            with self.assertRaises(ValueError): owner.selected(report)


@unittest.skipUnless(Path(os.path.expandvars(match.DEFAULT_CC)).is_file() and
                     shutil.which('arm-none-eabi-ld'), 'fixed original compiler required')
class NativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        scratch=Path(os.environ.get('TMPDIR',Path.cwd()/'build/tests')); scratch.mkdir(parents=True,exist_ok=True)
        cls.temporary=tempfile.TemporaryDirectory(prefix='static_callback_',dir=scratch)
        cls.root=Path(cls.temporary.name)
        cls.data,cls.bindings,cls.original=fixture(cls.root)
        cls.environment=patch.dict(os.environ,FFTA_ROM=str(cls.root/'baserom.bin'))
        cls.environment.start()
        cls.result=owner.build(cls.root,A,selector=buffers.SELECTOR)
        cls.report=owner.render(A,cls.result)

    @classmethod
    def tearDownClass(cls):
        cls.environment.stop();cls.temporary.cleanup()

    def replay(self, **changes):
        r=self.result
        values=dict(data=r[0],address=A,rom=r[6],mapping=r[3],index=r[4],objects=r[5],
                    manifest=r[1],selector=buffers.SELECTOR)
        values.update(changes)
        return owner.verify(**values)

    def proof(self, **changes):
        r=self.result
        values=dict(rom=r[6],mapping=r[3],index=r[4],objects=r[5]);values.update(changes)
        return buffers.StaticCallbackBufferProof(**values)

    def test_natural_c_original_elf_and_actual_callback_effects(self):
        self.assertEqual(self.original,self.result[8])
        self.assertEqual(match.elf_image(self.original)['type'],1)
        evidence=self.result[1]['proof']['buffers']
        self.assertEqual({row['address'] for row in evidence['dependencies']},
                         {B,C,evidence['callbacks'][0]['thunk']})
        self.assertEqual({row['target'] for row in evidence['callbacks']},{C})
        self.assertTrue(self.replay())

    def test_old_selectors_and_default_remain_refused(self):
        for selector in (owner.ACYCLIC_SELECTOR,owner.named_buffer.SELECTOR):
            with self.subTest(selector=selector),self.assertRaises(ValueError):
                self.replay(selector=selector,manifest=None,bindings=self.bindings)
        with self.assertRaises(ValueError):
            match.verify_leaf_instructions(self.data,A,True,
                {A+offset:int(name[5:],16) for offset,name in self.bindings['calls']})

    def test_two_contexts_same_owner_cannot_reuse_safe_callback_effects(self):
        proof=self.proof();stack=[(False,False,True)]
        args={match.ARM_REG_R0:-4}
        proof.check_arguments(B,args,stack,{},frozenset(),constants={match.ARM_REG_R1:C+1})
        with self.assertRaisesRegex(ValueError,'outside allocated local words'):
            proof.check_arguments(B,args,stack,{},frozenset(),constants={match.ARM_REG_R1:D+1})
        self.assertEqual({row['target'] for row in proof.observations()},{C,D})

    def test_unknown_even_changed_thunk_and_overwritten_target_refused(self):
        args={match.ARM_REG_R0:-4};stack=[(False,False,True)]
        for facts in ({},{match.ARM_REG_R1:C},{match.ARM_REG_R1:C+3}):
            with self.subTest(facts=facts),self.assertRaises(ValueError):
                self.proof().check_arguments(B,args,stack,{},frozenset(),constants=facts)
        rom=bytearray(self.result[6]);address=self.result[1]['proof']['buffers']['callbacks'][0]['thunk']
        rom[address-match.ROM_BASE]^=8
        with self.assertRaisesRegex(ValueError,'thunk identity'):
            self.replay(rom=bytes(rom),manifest=None,bindings=self.bindings)

    def test_call_fact_loss_and_context_budget_refuse(self):
        proof=self.proof();facts={match.ARM_REG_R0+6:C+1}
        proof.clear_extra_call_constants(facts);self.assertEqual(facts,{})
        args={match.ARM_REG_R0:-4};stack=[(False,False,True)]
        address=self.result[1]['proof']['buffers']['callbacks'][0]['thunk']
        with self.assertRaisesRegex(ValueError,'not an exact Thumb'):
            proof.check_arguments(address,args,stack,{},frozenset(),constants=facts)
        with patch.object(buffers,'MAX_CONTEXTS',0),self.assertRaisesRegex(ValueError,'context budget'):
            self.proof().check_arguments(B,args,stack,{},frozenset(),constants={match.ARM_REG_R1:C+1})

    def test_actual_conditional_join_and_post_call_register_target_refuse(self):
        workers = (
            '''extern void func_08013000(unsigned char *);
void func_08011000(unsigned char *bytes, void (*callback)(unsigned char *))
{
    if (bytes[0]) callback = func_08013000;
    callback(bytes);
}
''',
            '''void func_08011000(unsigned char *bytes, void (*callback)(unsigned char *))
{
    callback(bytes);
    callback(bytes);
}
''')
        for number,worker in enumerate(workers):
            root=self.root/f'negative-{number}'
            _,bindings,_=fixture(root,worker=worker)
            rom=(root/'baserom.bin').read_bytes()
            mapping=(root/'config/functions.json').read_bytes()
            index=(root/'symbols/functions.txt').read_bytes()
            data=rom[A-match.ROM_BASE:int(json.loads(mapping)[0]['end'],16)-match.ROM_BASE]
            with self.subTest(number=number),self.assertRaisesRegex(ValueError,
                    'not an exact Thumb|outside allocated local words'):
                owner.verify(data,A,rom,mapping,index,b'{}',bindings=bindings,selector=buffers.SELECTOR)

    def test_protected_descriptor_and_saved_control_bounds_remain_refused(self):
        args={match.ARM_REG_R0:-4};facts={match.ARM_REG_R1:C+1}
        with self.assertRaisesRegex(ValueError,'pointer-bearing argument slot'):
            self.proof().check_arguments(B,args,[(False,False,True)],{},frozenset({-4}),constants=facts)
        with self.assertRaisesRegex(ValueError,'outside allocated local words'):
            self.proof().check_arguments(B,args,[(True,True,False)],{},frozenset(),constants=facts)

    def test_every_callback_context_and_dependency_fingerprint_required(self):
        for field in ('target','constants','stack'):
            manifest=copy.deepcopy(self.result[1]);row=manifest['proof']['buffers']['callbacks'][0]
            row[field]=0 if field=='target' else []
            with self.subTest(field=field),self.assertRaisesRegex(ValueError,'fresh native replay'):
                self.replay(manifest=manifest)
        manifest=copy.deepcopy(self.result[1]);manifest['proof']['buffers']['dependencies'][0]['body_sha256']='0'*64
        with self.assertRaises(ValueError):self.replay(manifest=manifest)

    def test_malformed_ambiguous_and_missing_metadata_refused(self):
        rows=json.loads(self.result[3])
        for changed in (rows+[dict(rows[1])], [row for row in rows if int(row['rom'],16)!=C]):
            with self.assertRaises(ValueError):self.replay(mapping=json.dumps(changed).encode())
        image=match.elf_image(self.original);image['type']=2
        with self.assertRaisesRegex(ValueError,'original relocatable ELF'):
            owner.original_bindings(image,A,self.result[6],self.result[3],self.result[5],selector=buffers.SELECTOR)

    def test_fresh_source_report_and_original_elf_identity(self):
        self.assertTrue(match_evidence.report_matches(self.report,self.root,A))
        altered=self.report.replace('"original_elf_sha256":"','"original_elf_sha256":"0')
        self.assertFalse(match_evidence.report_matches(altered,self.root,A))
        for name in ('src/08010000.c','config/functions.json','symbols/functions.txt','config/data_symbols.json'):
            path=self.root/name;raw=path.read_bytes()
            try:
                path.write_bytes(raw+b'\n')
                self.assertFalse(match_evidence.report_matches(self.report,self.root,A))
            finally:path.write_bytes(raw)


if __name__=='__main__':unittest.main(verbosity=2)
