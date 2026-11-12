"""Real fixed-O0 compiler, explicit orphan discard, complete native replay."""
import copy
import json
import os
from pathlib import Path
import struct
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import match
import match_evidence
import owner_admission_profile as owner
import status
import compiler_orphan_constants_native_profile as native
from test_compiler_orphan_constants_prerequisite import SOURCE,OBJECTS,A

B=0x08002000


class NativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary=tempfile.TemporaryDirectory()
        cls.root=root=Path(cls.temporary.name)
        for folder in ('src','include','config','symbols','build'):(root/folder).mkdir()
        (root/'src/08001000.c').write_text(SOURCE)
        cls.runner=match.Runner(match.DEFAULT_CC,'Ubuntu',match.DEFAULT_WSL_PATH,root=root)
        cls.context=cls.runner.workspace();cls.workspace=cls.context.__enter__()
        cls.original,body,cls.image=match.compile_object(cls.runner,cls.workspace,native.configuration(),root,A,'src/08001000.c')
        cls.rows=[dict(rom=f'0x{address:08X}',end=f'0x{address+size:08X}',mode='thumb',instrs=count)
            for address,size,count in ((A,len(body),0),(B,2,1))]
        cls.mapping=json.dumps(cls.rows).encode()
        cls.objects=OBJECTS
        rom=bytes(B-match.ROM_BASE)+b'\x70\x47'
        cls.data,cls.bindings,cls.transport=native.object_bytes(cls.runner,cls.workspace,native.configuration(),
            cls.original,A,cls.mapping,rom,cls.objects,selector=native.SELECTOR)
        rom=bytearray(rom);rom[A-match.ROM_BASE:A-match.ROM_BASE+len(cls.data)]=cls.data
        cls.rom=bytes(rom)
        cls.rows[0]['instrs']=owner.refine(cls.data,A,cls.mapping)['instrs']
        cls.mapping=json.dumps(cls.rows).encode()
        cls.index=''.join(f'{int(row["rom"],16):08X} {int(row["end"],16):08X} '
            f'{int(row["end"],16)-int(row["rom"],16)} {row["instrs"]} bx\n' for row in cls.rows).encode()
        (root/'config/functions.json').write_bytes(cls.mapping)
        (root/'config/data_symbols.json').write_bytes(cls.objects)
        (root/'symbols/functions.txt').write_bytes(cls.index)
        (root/'baserom.bin').write_bytes(cls.rom)
        cls.env=patch.dict(os.environ,FFTA_ROM=str(root/'baserom.bin'));cls.env.start()
        cls.result=native.build(root,A,capture_dir=root/'capture')
        cls.report=native.render(A,cls.result)

    @classmethod
    def tearDownClass(cls):
        cls.env.stop();cls.context.__exit__(None,None,None);cls.temporary.cleanup()

    def test_authentic_complete_native_path(self):
        data,manifest=self.result
        self.assertEqual(data,self.data)
        self.assertEqual(manifest['transport']['original_elf_sha256'],native.sha(self.original))
        self.assertEqual((self.root/'capture/compiler/f.o').read_bytes(),self.original)
        self.assertEqual(native.sha((self.root/'capture/compiler/f.elf').read_bytes()),
            manifest['transport']['linked_elf_sha256'])
        self.assertEqual((self.root/'capture/source/src/08001000.c').read_text(),SOURCE)
        self.assertIn(native.FLAGS,(self.root/'capture/commands.txt').read_text())
        self.assertTrue(any(native.FLAGS in command for command in manifest['invocations']))
        self.assertEqual(manifest['transport']['excluded_bytes'],8)
        self.assertEqual(manifest['transport']['excluded_ROM_credit'],0)
        self.assertEqual(manifest['native']['profile'],owner.ACYCLIC_SCHEMA)
        self.assertTrue(native.report_matches(self.report,self.root,A))
        self.assertTrue(match_evidence.report_matches(self.report,self.root,A))

    def test_legacy_original_binding_and_linker_policies_stay_strict(self):
        with self.assertRaisesRegex(ValueError,'unexpected nonempty allocated section'):
            match.call_bindings(self.image,'func_08001000',A,self.mapping,len(self.rom),self.rom,self.objects)
        with self.assertRaisesRegex(ValueError,'unexpected nonempty allocated section'):
            owner.original_bindings(self.image,A,self.rom,self.mapping,self.objects,index=self.index,selector=owner.ACYCLIC_SELECTOR)
        with self.assertRaises(ValueError):native.build(self.root,A,args=native.argparse.Namespace(
            **dict(vars(native.configuration()),flags=match.DEFAULT_FLAGS)))

    def test_wrong_policy_selector_and_actual_object(self):
        for changes in (dict(policy='GC'),dict(selector='ordinary'),dict(original_elf=self.original+b'x')):
            values=dict(runner=self.runner,workspace=self.workspace,args=native.configuration(),
                original_elf=self.original,address=A,mapping=self.mapping,rom=self.rom,
                objects=self.objects,selector=native.SELECTOR)
            values.update(changes)
            with self.subTest(changes=list(changes)),self.assertRaises(ValueError):native.object_bytes(**values)

    def test_missing_wrong_target_and_index_refuse(self):
        for path,changed in (('config/functions.json',json.dumps(self.rows[:1]).encode()),
                            ('symbols/functions.txt',self.index.replace(b' 1 bx',b' 2 bx')),
                            ('config/data_symbols.json',OBJECTS.replace(b'03002000',b'03002008'))):
            file=self.root/path;original=file.read_bytes()
            try:
                file.write_bytes(changed)
                self.assertFalse(native.report_matches(self.report,self.root,A))
            finally:file.write_bytes(original)

    def test_report_source_policy_runtime_ELF_and_bytes_staleness(self):
        for key in ('source_sha256','environment','transport','native'):
            manifest=copy.deepcopy(self.result[1]);manifest[key]='stale'
            with self.subTest(key=key),self.assertRaises(ValueError):native.build(self.root,A,expected=manifest)
        for name in ('src/08001000.c','config/functions.json','symbols/functions.txt','config/data_symbols.json'):
            file=self.root/name;original=file.read_bytes()
            try:
                file.write_bytes(original+b'\n')
                self.assertFalse(match_evidence.report_matches(self.report,self.root,A))
            finally:file.write_bytes(original)
        self.assertFalse(match_evidence.report_matches(self.report+'* verification: `ordinary`\n',self.root,A))

    def test_actual_cli_no_write_and_report_selection(self):
        self.assertTrue(owner.selected(self.report))
        self.assertEqual(owner.selector_for_report(self.report),native.SELECTOR)
        self.assertEqual(match_evidence.compiler_flags(self.report),native.FLAGS)
        command=[sys.executable,str(Path(match.__file__)), '--root',str(self.root),f'{A:08X}',
            '--owner-runtime-profile',native.SELECTOR,'--flags='+native.FLAGS,'--no-write']
        result=match._run_replay_process(command,self.root,120)
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        self.assertIn('verdict MATCH - byte identical',result.stdout.splitlines())
        self.assertEqual(status.matcher_extent(result.stdout),len(self.data))
        self.assertEqual(status.report_extent(self.report),len(self.data))
        self.assertFalse((self.root/'docs/match/08001000.md').exists())

    def test_actual_orphan_export_reference_and_addend_mutations_refuse(self):
        header=struct.unpack_from('<HHIIIIIHHHHHH',self.original,16)
        names=self.image['section_data'][header[12]]
        sections={names[row[0]:names.index(b'\0',row[0])].decode():i
            for i,row in enumerate(self.image['sections'])}
        table=next(iter(self.image['symbol_tables']))
        symbols=self.image['symbol_tables'][table]
        orphan=sections['.rodata']
        mapped=next(i for i,row in enumerate(symbols) if row['section']==orphan and row['type']==0)
        section_symbol=next(i for i,row in enumerate(symbols) if row['section']==orphan and row['type']==3)
        cases=[]
        raw=bytearray(self.original);raw[self.image['sections'][orphan][4]]^=1;cases.append(bytes(raw))
        raw=bytearray(self.original);raw[self.image['sections'][table][4]+16*mapped+12]=0x10;cases.append(bytes(raw))
        raw=bytearray(self.original)
        offset=self.image['sections'][sections['.rel.text']][4]
        struct.pack_into('<I',raw,offset+4,(section_symbol<<8)|2);cases.append(bytes(raw))
        read=self.runner.read_binary
        for original in cases:
            def changed(path):
                return original if path.endswith('/f.o') else read(path)
            with self.subTest(hash=native.sha(original)),patch.object(self.runner,'read_binary',side_effect=changed),self.assertRaises(ValueError):
                native.object_bytes(self.runner,self.workspace,native.configuration(),original,A,
                    self.mapping,self.rom,self.objects,selector=native.SELECTOR)

    def test_linked_call_target_mismatch_refuses(self):
        read=self.runner.read_binary
        site=self.bindings['calls'][0][0]
        def changed(path):
            raw=read(path)
            if path.endswith('/f.elf'):
                image=match.elf_image(raw);raw=bytearray(raw)
                offset=image['sections'][image['text_index']][4]+site
                raw[offset+2]^=1
                return bytes(raw)
            return raw
        with patch.object(self.runner,'read_binary',side_effect=changed),self.assertRaises(ValueError):
            native.object_bytes(self.runner,self.workspace,native.configuration(),self.original,A,
                self.mapping,self.rom,self.objects,selector=native.SELECTOR)

    def test_changed_linked_unrelocated_bytes_refuse(self):
        read=self.runner.read_binary
        def changed(path):
            raw=read(path)
            if path.endswith('/f.elf'):
                image=match.elf_image(raw);raw=bytearray(raw)
                raw[image['sections'][image['text_index']][4]]^=1
                return bytes(raw)
            return raw
        with patch.object(self.runner,'read_binary',side_effect=changed),self.assertRaises(ValueError):
            native.object_bytes(self.runner,self.workspace,native.configuration(),self.original,A,
                self.mapping,self.rom,self.objects,selector=native.SELECTOR)


if __name__=='__main__':unittest.main()
