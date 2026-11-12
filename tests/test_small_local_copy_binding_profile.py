"""Actual compiler/linker, CLI/report replay and hostile binding boundaries."""
import argparse
import copy
import json
import os
from pathlib import Path
import struct
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode=True
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import match
import match_evidence
import owner_admission_profile as owner
import small_local_copy_binding_profile as binding
from test_small_local_copy_caller_profile import fixture

A,H,S=0x08000200,0x08000400,0x08000800
SOURCE='''extern unsigned short source_bytes[];
extern void *memcpy(void *,const void *,unsigned int);
struct Row { unsigned short i; unsigned short value; unsigned int g; unsigned short e,f; };
unsigned int func_08000200(struct Row *output, unsigned int input) {
 unsigned short local[4]; unsigned short *cursor; int i;
 memcpy(local,source_bytes,8); cursor=local;
 for(i=0;i<=3;i++) { output->i=i; output->value=*cursor; cursor++; output++; }
 output->g = (output->g + input) * (output->e + output->f) + output->i * output->value;
 return 4;
}
'''


class BindingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary=tempfile.TemporaryDirectory();cls.root=Path(cls.temporary.name)
        for name in ('src','include','config','symbols','build'):(cls.root/name).mkdir()
        (cls.root/'src/08000200.c').write_text(SOURCE)
        cls.args=argparse.Namespace(cc=match.DEFAULT_CC,cpp=match.DEFAULT_CPP,
            assembler=match.DEFAULT_AS,objcopy=match.DEFAULT_OBJCOPY,linker=match.DEFAULT_LD,flags=match.DEFAULT_FLAGS)
        cls.runner=match.Runner(match.DEFAULT_CC,'Ubuntu',match.DEFAULT_WSL_PATH,root=cls.root)
        cls.workspace_context=cls.runner.workspace();cls.workspace=cls.workspace_context.__enter__()
        cls.raw,body,cls.image=match.compile_object(cls.runner,cls.workspace,cls.args,cls.root,A,'src/08000200.c')
        env=fixture(source=S);data=bytearray(body)
        for section_id in cls.image['relocations']:
            section=cls.image['sections'][section_id];symbols=cls.image['symbol_tables'][section[6]]
            raw=cls.image['section_data'][section_id]
            for pos in range(0,len(raw),8):
                site,info=struct.unpack_from('<II',raw,pos);name=symbols[info>>8]['name']
                if info&255==10:
                    assert name=='memcpy'
                    delta=H-A-site-4
                    struct.pack_into('<HH',data,site,0xF000|((delta>>12)&2047),0xF800|((delta>>1)&2047))
                elif info&255==2:
                    assert name=='source_bytes';struct.pack_into('<I',data,site,S)
                else:raise AssertionError(info)
        cls.data=bytes(data);rom=bytearray(env['rom']);rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)]=data
        cls.rom=bytes(rom);rows=json.loads(env['mapping']);rows[0].update(end=f'0x{A+len(data):08X}',instrs=0)
        cls.mapping=json.dumps(rows).encode();rows[0]['instrs']=owner.refine(cls.data,A,cls.mapping)['instrs']
        cls.mapping=json.dumps(rows).encode()
        cls.index=''.join(f'{int(row["rom"],16):08X} {int(row["end"],16):08X} '
            f'{int(row["end"],16)-int(row["rom"],16)} {row["instrs"]} bx\n' for row in rows).encode()
        cls.objects=json.dumps({'source_bytes':f'0x{S:08X}'}).encode()
        cls.bindings,cls.targets=cls.original()
        for name,value in (('config/functions.json',cls.mapping),('symbols/functions.txt',cls.index),
                           ('config/data_symbols.json',cls.objects),('baserom.bin',cls.rom)):
            (cls.root/name).write_bytes(value)

    @classmethod
    def tearDownClass(cls):
        cls.workspace_context.__exit__(None,None,None);cls.temporary.cleanup()

    @classmethod
    def original(cls,**changes):
        args=dict(image=cls.image,address=A,rom=cls.rom,mapping=cls.mapping,objects=cls.objects,
                  index=cls.index,selector=binding.SELECTOR);args.update(changes)
        return owner.original_bindings(**args)

    def verify(self,**changes):
        args=dict(data=self.data,address=A,rom=self.rom,mapping=self.mapping,index=self.index,
                  objects=self.objects,bindings=self.bindings,selector=binding.SELECTOR)
        args.update(changes);return owner.verify(**args)

    def test_actual_compiler_link_complete_native_and_manifest_replay(self):
        self.assertEqual(self.targets['memcpy'],(H,False))
        data,bindings=owner.object_bytes(self.runner,self.workspace,self.args,self.image,A,
            self.rom,self.mapping,self.objects,selector=binding.SELECTOR,index=self.index)
        self.assertEqual(data,self.data);self.assertEqual(bindings,self.bindings)
        manifest,instructions=self.verify();self.verify(manifest=manifest)
        self.verify(manifest=manifest,bindings=None)
        self.assertEqual(manifest['profile'],binding.SCHEMA)
        self.assertEqual(manifest['proof']['finite_small_copy']['loop']['iterations'],4)
        self.assertEqual(manifest['proof']['source_correspondence']['point'],S)
        self.assertEqual(len(instructions),manifest['proof']['instructions'])
        self.assertFalse(manifest['proof']['physical_access_proved'])

    def test_native_cli_and_fresh_report_replay(self):
        with patch.dict(os.environ,FFTA_ROM=str(self.root/'baserom.bin')):
            result=owner.build(self.root,A,selector=binding.SELECTOR)
            report=owner.render(A,result)
            self.assertEqual(owner.selector_for_report(report),binding.SELECTOR)
            self.assertIn('* control flow: '+binding.CONTROL_FLOW,report)
            self.assertTrue(match_evidence.report_matches(report,self.root,A))
            command=[sys.executable,str(Path(match.__file__)),hex(A),'--root',str(self.root),
                     '--owner-runtime-profile',binding.SELECTOR,'--no-write']
            process=subprocess.run(command,capture_output=True,text=True,timeout=120)
            self.assertEqual(process.returncode,0,process.stdout+process.stderr)
            self.assertIn('MATCH',process.stdout)

    def test_stale_source_mapping_index_objects_rom_reports(self):
        with patch.dict(os.environ,FFTA_ROM=str(self.root/'baserom.bin')):
            report=owner.render(A,owner.build(self.root,A,selector=binding.SELECTOR))
            for name in ('src/08000200.c','config/functions.json','symbols/functions.txt','config/data_symbols.json','baserom.bin'):
                path=self.root/name;raw=path.read_bytes()
                try:
                    path.write_bytes(raw+b'\n')
                    with self.subTest(name=name):self.assertFalse(match_evidence.report_matches(report,self.root,A))
                finally:path.write_bytes(raw)

    def test_old_selector_and_mixed_report_refused(self):
        with self.assertRaises(ValueError):self.original(selector='named-data-buffer-v1')
        with self.assertRaisesRegex(ValueError,'genuine original ELF'):
            owner.preflight(self.data,A,self.rom,self.mapping,self.index,self.objects,selector=binding.SELECTOR)
        with patch.dict(os.environ,FFTA_ROM=str(self.root/'baserom.bin')):
            report=owner.render(A,owner.build(self.root,A,selector=binding.SELECTOR))
        for changed in (report+'* buffer calls: legacy\n',report+'* verification: `elf-symbol-thumb-named-data-buffer-calls-v1`\n'):
            with self.assertRaises(ValueError):owner.selector_for_report(changed)

    def test_wrong_memcpy_symbol_type_binding_and_identity(self):
        for field,value in (('name','memmove'),('type',1),('bind',2),('value',1),('size',4),('section',1)):
            image=copy.deepcopy(self.image)
            for row in image['symbols']:
                if row['name']=='memcpy':row[field]=value
            with self.subTest(field=field),self.assertRaises(ValueError):self.original(image=image)
        image=copy.deepcopy(self.image);image['symbols'].append(copy.deepcopy(next(row for row in image['symbols'] if row['name']=='memcpy')))
        with self.assertRaises(ValueError):self.original(image=image)

    def test_wrong_helper_count_complete_extent_and_source(self):
        rom=bytearray(self.rom);rom[H-match.ROM_BASE+20]^=1
        with self.assertRaises(ValueError):self.original(rom=bytes(rom))
        for old,new in ((b'98 49',b'98 48'),(f'{H+98:08X}'.encode(),f'{H+96:08X}'.encode())):
            with self.subTest(old=old),self.assertRaises(ValueError):self.original(index=self.index.replace(old,new))
        for value in (S+2,0x03002000):
            with self.subTest(source=value),self.assertRaises(ValueError):
                self.original(objects=json.dumps({'source_bytes':f'0x{value:08X}'}).encode())
        decoder=match.Cs(match.CS_ARCH_ARM,match.CS_MODE_THUMB);decoder.detail=True
        site=next(item.address-A for item in decoder.disasm(self.data,A)
            if item.mnemonic=='movs' and item.op_str=='r2, #8')
        data=bytearray(self.data);data[site]=10
        rom=bytearray(self.rom);rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)]=data
        with self.assertRaises(ValueError):self.verify(data=bytes(data),rom=bytes(rom))

    def test_original_relocation_addend_kind_overlap_and_missing(self):
        number=self.image['relocations'][0];raw=self.image['section_data'][number]
        for change in ('call-addend','source-addend','kind','overlap','missing'):
            image=copy.deepcopy(self.image);relocations=bytearray(raw)
            if change.endswith('addend'):
                site=self.bindings['calls'][0][0] if change=='call-addend' else self.bindings['data'][0][0]
                text=bytearray(image['text']);text[site]^=1;image['text']=bytes(text)
            elif change=='kind':
                site,info=struct.unpack_from('<II',relocations);struct.pack_into('<I',relocations,4,(info&~255)|99)
            elif change=='overlap':relocations[8:16]=relocations[:8]
            else:
                image['relocations']=[]
            image['section_data'][number]=bytes(relocations)
            with self.subTest(change=change),self.assertRaises(ValueError):self.original(image=image)

    def test_original_allocated_section_and_second_function_refused(self):
        image=copy.deepcopy(self.image)
        # A real additional allocated section cannot be hidden by the selector.
        section=list(image['sections'][image['text_index']]);section[2]|=2;section[5]=4
        image['sections'].append(tuple(section));image['section_data'].append(bytes(4))
        with self.assertRaises(ValueError):self.original(image=image)
        image=copy.deepcopy(self.image);symbol=copy.deepcopy(next(row for row in image['symbols'] if row['name']=='func_08000200'))
        symbol['name']='other_function';image['symbols'].append(symbol)
        with self.assertRaises(ValueError):self.original(image=image)

    def test_original_mode_owner_overlap_and_helper_identity_counts(self):
        image=copy.deepcopy(self.image)
        for row in image['symbols']:
            if row['name']=='func_08000200':row['value']&=~1
        with self.assertRaises(ValueError):self.original(image=image)
        rows=json.loads(self.mapping)
        for changed in (rows+[dict(rows[1])],
                        [dict(row,mode='arm') if int(row['rom'],16)==H else row for row in rows],
                        [dict(row,instrs=48) if int(row['rom'],16)==H else row for row in rows],
                        rows+[dict(rom=f'0x{A+2:08X}',end=f'0x{A+4:08X}',mode='thumb',instrs=1)]):
            with self.subTest(mapping=changed),self.assertRaises(ValueError):
                self.original(mapping=json.dumps(changed).encode())

    def test_changed_linked_unrelocated_bytes_refused(self):
        read=self.runner.read_binary
        def changed(path):
            raw=read(path)
            if path.endswith('/f.elf'):
                image=match.elf_image(raw);raw=bytearray(raw);raw[image['sections'][image['text_index']][4]]^=1
                return bytes(raw)
            return raw
        with patch.object(self.runner,'read_binary',side_effect=changed),self.assertRaises(ValueError):
            owner.object_bytes(self.runner,self.workspace,self.args,self.image,A,self.rom,self.mapping,
                self.objects,selector=binding.SELECTOR,index=self.index)

    def test_linked_symbol_thumb_object_type_and_identity_refused(self):
        read=self.runner.read_binary
        for name,field in (('memcpy','type'),('memcpy','thumb'),('source_bytes','type')):
            def changed(path):
                raw=read(path)
                if not path.endswith('/f.elf'):return raw
                image=match.elf_image(raw);raw=bytearray(raw)
                table,position=next((table,position) for table,rows in image['symbol_tables'].items()
                    for position,row in enumerate(rows) if row['name']==name)
                offset=image['sections'][table][4]+16*position
                if field=='type':raw[offset+12]=(raw[offset+12]&0xF0)|(1 if name=='memcpy' else 2)
                else:
                    value=struct.unpack_from('<I',raw,offset+4)[0];struct.pack_into('<I',raw,offset+4,value&~1)
                return bytes(raw)
            with self.subTest(name=name,field=field),patch.object(self.runner,'read_binary',side_effect=changed),self.assertRaises(ValueError):
                owner.object_bytes(self.runner,self.workspace,self.args,self.image,A,self.rom,self.mapping,
                    self.objects,selector=binding.SELECTOR,index=self.index)

    def test_manifest_and_typed_source_binding_staleness(self):
        manifest,_=self.verify()
        for field in ('producer_sha256','source_correspondence','finite_small_copy'):
            stale=copy.deepcopy(manifest);stale['proof'][field]={}
            with self.subTest(field=field),self.assertRaises(ValueError):self.verify(manifest=stale)
        for key in ('calls','data'):
            bindings=copy.deepcopy(self.bindings);bindings[key].pop()
            with self.subTest(key=key),self.assertRaises(ValueError):self.verify(bindings=bindings)


if __name__=='__main__':unittest.main()
