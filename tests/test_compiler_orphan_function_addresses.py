"""Actual fixed-O0 compiler callback duplicates and hostile typed identities."""
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
import owner_admission_profile as owner
import compiler_orphan_constants_prerequisite as prerequisite
import compiler_orphan_constants_native_profile as native

A=0x08001000
B=0x08002000
SOURCE='''extern void func_08002000(void);
void (*func_08001000(void))(void)
{
    void (*callback)(void) = func_08002000;
    return callback;
}
'''


class FunctionAddressTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary=tempfile.TemporaryDirectory()
        cls.root=root=Path(cls.temporary.name)
        for name in ('src','include','config','symbols','build'):(root/name).mkdir()
        (root/'src/08001000.c').write_text(SOURCE)
        cls.runner=match.Runner(match.DEFAULT_CC,'Ubuntu',match.DEFAULT_WSL_PATH,root=root)
        cls.context=cls.runner.workspace();cls.workspace=cls.context.__enter__()
        cls.original,body,cls.image=match.compile_object(cls.runner,cls.workspace,native.configuration(),root,A,'src/08001000.c')
        cls.preprocessed=cls.runner.read_binary(cls.workspace+'/f.i')
        cls.rows=[dict(rom=f'0x{start:08X}',end=f'0x{start+size:08X}',mode='thumb',instrs=count)
            for start,size,count in ((A,len(body),0),(B,2,1))]
        cls.rows[0]['instrs']=owner.refine(body,A,json.dumps(cls.rows).encode())['instrs']
        cls.mapping=json.dumps(cls.rows).encode()
        cls.index=''.join(f'{int(row["rom"],16):08X} {int(row["end"],16):08X} '
            f'{int(row["end"],16)-int(row["rom"],16)} {row["instrs"]} bx\n' for row in cls.rows).encode()
        cls.rom=bytes(B-match.ROM_BASE)+b'\x70\x47'
        cls.data,cls.bindings,cls.transport=cls.link()
        rom=bytearray(cls.rom);rom[A-match.ROM_BASE:A-match.ROM_BASE+len(cls.data)]=cls.data
        cls.rom=bytes(rom)
        for name,raw in (('config/functions.json',cls.mapping),('symbols/functions.txt',cls.index),
                         ('config/data_symbols.json',b'{}'),('baserom.bin',cls.rom)):
            (root/name).write_bytes(raw)
        cls.environment=patch.dict(os.environ,FFTA_ROM=str(root/'baserom.bin'));cls.environment.start()
        cls.data,cls.manifest=native.build(root,A,capture_dir=root/'capture')

    @classmethod
    def tearDownClass(cls):
        cls.environment.stop();cls.context.__exit__(None,None,None);cls.temporary.cleanup()

    @classmethod
    def link(cls,**changes):
        values=dict(runner=cls.runner,workspace=cls.workspace,args=native.configuration(),
            original_elf=cls.original,address=A,mapping=cls.mapping,index=cls.index,
            rom=cls.rom,objects=b'{}',selector=native.SELECTOR)
        values.update(changes)
        return native.object_bytes(**values)

    def inventory(self,**changes):
        values=dict(original_elf=self.original,address=A,objects=b'{}',preprocessed_source=self.preprocessed,
            mapping=self.mapping,index=self.index,rom=self.rom,selector=prerequisite.SELECTOR)
        values.update(changes)
        return prerequisite.verify(**values)

    def test_actual_callback_duplicate_native_and_fresh_replay(self):
        self.assertFalse(self.bindings['calls'])
        self.assertFalse(self.bindings['data'])
        self.assertEqual(len(self.bindings['functions']),1)
        site,name=self.bindings['functions'][0]
        self.assertEqual((name,struct.unpack_from('<I',self.data,site)[0]),('func_08002000',B|1))
        proof=self.manifest['transport']['prerequisite']
        self.assertEqual(proof['function_addresses']['names'],['func_08002000'])
        self.assertEqual([row['address'] for row in proof['function_addresses']['spans']],[A,B])
        self.assertFalse(proof['function_addresses']['callback_body_semantics_proved'])
        self.assertEqual((self.root/'capture/compiler/f.o').read_bytes(),self.original)
        self.assertEqual(native.build(self.root,A,expected=self.manifest)[0],self.data)
        self.assertTrue(native.report_matches(native.render(A,(self.data,self.manifest)),self.root,A))

    def test_dual_index_missing_duplicate_mode_alignment_overlap_and_coverage(self):
        cases=[]
        for position in (0,1):
            cases.append(dict(mapping=json.dumps(self.rows[:position]+self.rows[position+1:]).encode()))
            cases.append(dict(mapping=json.dumps(self.rows+[self.rows[position]]).encode()))
            cases.append(dict(index=b'\n'.join(self.index.splitlines()[:position]+self.index.splitlines()[position+1:])))
            cases.append(dict(index=self.index+self.index.splitlines()[position]+b'\n'))
            for key,value in (('mode','arm'),('rom',f'0x{(A,B)[position]+1:08X}'),('end',f'0x{(A,B)[position]+1:08X}')):
                rows=copy.deepcopy(self.rows);rows[position][key]=value
                cases.append(dict(mapping=json.dumps(rows).encode()))
        rows=copy.deepcopy(self.rows);rows.append(dict(rom=f'0x{B-2:08X}',end=f'0x{B+2:08X}',mode='thumb',instrs=1))
        cases += [dict(mapping=json.dumps(rows).encode()),dict(index=self.index+f'{B-2:08X} {B+2:08X} 4 1 bx\n'.encode()),
                  dict(index=None),dict(mapping=None),dict(rom=None),dict(objects=b'{"func_08002000":"0x08002000"}')]
        for changes in cases:
            with self.subTest(changes=changes),self.assertRaises((ValueError,TypeError)):
                self.inventory(**changes)

    def test_actual_original_function_addends_and_literal_reference_refuse(self):
        for section_id in self.image['relocations']:
            section=self.image['sections'][section_id]
            if section[7] not in (self.image['text_index'],self.transport['prerequisite']['orphan_section']['index']):continue
            payload=self.image['section_data'][section_id]
            for position in range(0,len(payload),8):
                site,info=struct.unpack_from('<II',payload,position)
                if info&255 != 2:continue
                for addend in (1,4,0xffffffff):
                    raw=bytearray(self.original)
                    struct.pack_into('<I',raw,self.image['sections'][section[7]][4]+site,addend)
                    with self.subTest(section=section[7],addend=addend),self.assertRaises(ValueError):
                        self.inventory(original_elf=bytes(raw))
        raw=bytearray(self.original)
        # Change the reached PC-relative literal load into a two-byte NOP.
        site=self.inventory()['duplicate_words'][0]['original_literals'][0]['load_sites'][0]
        struct.pack_into('<H',raw,self.image['sections'][self.image['text_index']][4]+site,0x46c0)
        with self.assertRaises(ValueError):self.inventory(original_elf=bytes(raw))

    def test_original_callback_symbol_type_and_relocation_width_refuse(self):
        table=next(iter(self.image['symbol_tables']))
        number=next(i for i,row in enumerate(self.image['symbol_tables'][table])
                    if row['name']=='func_08002000')
        for delta,fmt,value in ((12,'B',0x11),(4,'I',1),(8,'I',4),(13,'B',1)):
            raw=bytearray(self.original)
            struct.pack_into('<'+fmt,raw,self.image['sections'][table][4]+16*number+delta,value)
            with self.subTest(delta=delta),self.assertRaises(ValueError):self.inventory(original_elf=bytes(raw))
        for section_id in self.image['relocations']:
            section=self.image['sections'][section_id]
            for delta in (1,2):
                raw=bytearray(self.original)
                offset=section[4]
                site,info=struct.unpack_from('<II',raw,offset)
                struct.pack_into('<I',raw,offset,site+delta)
                with self.subTest(section=section_id,delta=delta),self.assertRaises(ValueError):
                    self.inventory(original_elf=bytes(raw))

    def test_stale_manifest_and_callback_ROM_are_bound(self):
        proof=self.inventory()
        for changes in (dict(index=self.index+b'\n'),dict(mapping=self.mapping+b'\n'),
                        dict(rom=self.rom[:-1]+b'\0')):
            with self.subTest(changes=list(changes)),self.assertRaises(ValueError):self.inventory(manifest=proof,**changes)
        changed=copy.deepcopy(self.manifest)
        changed['indexed_spans'][-1]['body_sha256']='stale'
        with self.assertRaises(ValueError):native.build(self.root,A,expected=changed)

    def test_linked_function_word_and_unrelocated_bytes_refuse(self):
        read=self.runner.read_binary
        for site in (0,self.bindings['functions'][0][0]):
            def changed(path):
                raw=read(path)
                if path.endswith('/f.elf'):
                    image=match.elf_image(raw);raw=bytearray(raw)
                    raw[image['sections'][image['text_index']][4]+site]^=1
                    return bytes(raw)
                return raw
            with self.subTest(site=site),patch.object(self.runner,'read_binary',side_effect=changed),self.assertRaises(ValueError):self.link()


if __name__=='__main__':unittest.main()
