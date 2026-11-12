"""Natural compiler output and hostile original-ELF mutations; no admission."""
import argparse
import copy
import json
from pathlib import Path
import struct
import sys
import tempfile
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import match
import compiler_orphan_constants_prerequisite as orphan

A=0x08001000
SOURCE='''extern void func_08002000(void);
extern unsigned int state_a;
extern unsigned int state_b;
unsigned int func_08001000(void)
{
    unsigned int *first = &state_a;
    unsigned int *second = &state_b;
    func_08002000();
    return *first + *second;
}
'''
OBJECTS=b'{"state_a":"0x03002000","state_b":"0x03002004"}'


class PrerequisiteTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary=tempfile.TemporaryDirectory()
        root=Path(cls.temporary.name)
        (root/'src').mkdir();(root/'include').mkdir()
        (root/'src/08001000.c').write_text(SOURCE)
        args=argparse.Namespace(cc=match.DEFAULT_CC,cpp=match.DEFAULT_CPP,
            assembler=match.DEFAULT_AS,objcopy=match.DEFAULT_OBJCOPY,
            linker=match.DEFAULT_LD,flags='-mthumb-interwork -O0')
        runner=match.Runner(match.DEFAULT_CC,'Ubuntu',match.DEFAULT_WSL_PATH,root=root)
        with runner.workspace() as workspace:
            cls.original,cls.text,cls.image=match.compile_object(runner,workspace,args,root,A,'src/08001000.c')
            cls.preprocessed=runner.read_binary(workspace+'/f.i')
        cls.sh_offset=struct.unpack_from('<I',cls.original,32)[0]
        names=cls.image['section_data'][struct.unpack_from('<H',cls.original,50)[0]]
        cls.sections={names[row[0]:names.index(b'\0',row[0])].decode():index
            for index,row in enumerate(cls.image['sections'])}

    @classmethod
    def tearDownClass(cls):cls.temporary.cleanup()

    def verify(self,**changes):
        values=dict(original_elf=self.original,address=A,objects=OBJECTS,
            preprocessed_source=self.preprocessed,selector=orphan.SELECTOR)
        values.update(changes)
        return orphan.verify(**values)

    def section_change(self,name,field,value):
        raw=bytearray(self.original)
        struct.pack_into('<I',raw,self.sh_offset+40*self.sections[name]+4*field,value)
        return bytes(raw)

    def word_change(self,name,offset,value):
        raw=bytearray(self.original)
        struct.pack_into('<I',raw,self.image['sections'][self.sections[name]][4]+offset,value)
        return bytes(raw)

    def symbol_change(self,name,field,value):
        table=next(iter(self.image['symbol_tables']))
        number=next(i for i,row in enumerate(self.image['symbol_tables'][table]) if row['name']==name)
        raw=bytearray(self.original)
        offset=self.image['sections'][table][4]+16*number
        formats={'name':(0,'I'),'value':(4,'I'),'size':(8,'I'),'info':(12,'B'),
                 'visibility':(13,'B'),'section':(14,'H')}
        delta,fmt=formats[field];struct.pack_into('<'+fmt,raw,offset+delta,value)
        return bytes(raw)

    def test_natural_compiler_object_and_fresh_inventory(self):
        proof=self.verify()
        self.assertEqual(proof['orphan_section']['bytes'],8)
        self.assertEqual({row['symbol'] for row in proof['duplicate_words']},{'state_a','state_b'})
        self.assertTrue(all(row['original_literals'][0]['load_sites'] for row in proof['duplicate_words']))
        self.assertFalse(proof['native_admission'])
        self.assertFalse(proof['source_ELF_provenance_proved'])
        self.assertFalse(proof['section_exclusion_performed'])
        self.assertFalse(proof['runtime_unreachability_proved'])
        self.assertFalse(proof['ABI_or_return_provenance_proved'])
        self.assertEqual(self.verify(manifest=proof),proof)
        self.assertEqual(match.elf_image(self.original)['text'],self.text)

    def test_legacy_gate_keeps_exact_failure(self):
        with self.assertRaisesRegex(ValueError,'^unexpected nonempty allocated section$'):
            match.allocated_text_only(self.image)
        with self.assertRaisesRegex(ValueError,'unresolved relocations'):
            match.function_bytes(self.original,self.text,'func_08001000',A,True)

    def test_explicit_selector_and_immutable_inputs(self):
        for change in (dict(selector=None),dict(selector='ordinary'),dict(original_elf=bytearray(self.original)),
                       dict(preprocessed_source='source'),dict(address=A+1)):
            with self.subTest(change=list(change)),self.assertRaises(ValueError):self.verify(**change)

    def test_writable_executable_TLS_merge_BSS_and_bad_extent(self):
        for field,value in ((2,3),(2,6),(2,0x402),(2,0x12),(1,8),(5,6),(5,68),(8,1),(3,0x03000000)):
            with self.subTest(field=field,value=value),self.assertRaises(ValueError):
                self.verify(original_elf=self.section_change('.rodata',field,value))

    def test_missing_partial_overlapping_or_foreign_relocations(self):
        ro=self.sections['.rel.rodata']
        offset=self.image['sections'][ro][4]
        site,info=struct.unpack_from('<II',self.original,offset)
        second_site,second_info=struct.unpack_from('<II',self.original,offset+8)
        for raw in (self.section_change('.rel.rodata',5,8),
                    self.section_change('.rel.rodata',1,4),
                    self.section_change('.rel.rodata',7,self.sections['.data']),
                    self.word_change('.rel.rodata',8,site),
                    self.word_change('.rel.rodata',0,2),
                    self.word_change('.rel.rodata',4,(info&~255)|10),
                    self.word_change('.rel.rodata',4,(info&~255)|99),
                    self.word_change('.rel.rodata',4,(999<<8)|2)):
            with self.subTest(raw_hash=orphan.sha(raw)),self.assertRaises(ValueError):self.verify(original_elf=raw)

    def test_exported_object_foreign_local_and_incoming_references(self):
        for field,value in (('info',0x10),('info',1),('size',4),('visibility',2),('value',2)):
            with self.subTest(field=field),self.assertRaises(ValueError):
                self.verify(original_elf=self.symbol_change('$d',field,value))
        ro_index=self.sections['.rodata']
        symbols=self.image['symbol_tables'][next(iter(self.image['symbol_tables']))]
        number=next(i for i,row in enumerate(symbols) if row['section']==ro_index)
        with self.assertRaisesRegex(ValueError,'incoming reference'):
            self.verify(original_elf=self.word_change('.rel.text',4,(number<<8)|2))

    def test_named_target_type_binding_value_and_unknown_map(self):
        for field,value in (('info',2),('info',0x20),('info',0x12),('value',1),('size',4),
                            ('section',self.sections['.text']),('visibility',2)):
            with self.subTest(field=field,value=value),self.assertRaises(ValueError):
                self.verify(original_elf=self.symbol_change('state_a',field,value))
        for objects in (b'{}',b'{"state_a":"0x03002000"}',b'{"state_a":"0x03002000","state_a":"0x03002000"}'):
            with self.subTest(objects=objects),self.assertRaises(ValueError):self.verify(objects=objects)

    def test_addend_and_referenced_literal_required(self):
        with self.assertRaisesRegex(ValueError,'identical authenticated'):
            self.verify(original_elf=self.word_change('.rodata',0,4))
        # Keep the text relocation, but remove the actual PC load by changing it
        # into a scalar instruction. The orphan must lose its witness.
        proof=self.verify()
        site=proof['duplicate_words'][0]['original_literals'][0]['load_sites'][0]
        raw=bytearray(self.original)
        offset=self.image['sections'][self.image['text_index']][4]+site
        struct.pack_into('<H',raw,offset,0x2000)
        with self.assertRaises(ValueError):self.verify(original_elf=bytes(raw))

    def test_call_relocation_and_unowned_text_are_not_ignored(self):
        row=self.image['sections'][self.sections['.rel.text']]
        calls=[struct.unpack_from('<II',self.original,row[4]+offset)
            for offset in range(0,row[5],8)
            if struct.unpack_from('<I',self.original,row[4]+offset+4)[0]&255 == 10]
        self.assertEqual(len(calls),1)
        site,_=calls[0]
        raw=bytearray(self.original)
        offset=self.image['sections'][self.image['text_index']][4]+site
        raw[offset+2]^=1
        with self.assertRaisesRegex(ValueError,'zero-addend BL'):self.verify(original_elf=bytes(raw))
        with self.assertRaises(ValueError):
            self.verify(original_elf=self.symbol_change('func_08002000','info',0x11))
        with self.assertRaises(ValueError):
            self.verify(original_elf=self.symbol_change('func_08001000','size',len(self.text)-4))

    def test_file_overlap_foreign_metadata_and_nonempty_BSS(self):
        for name,field,value in (('.rodata',4,self.image['sections'][self.image['text_index']][4]),
                                 ('.rodata',4,len(self.original)-2),
                                 ('.ARM.attributes',1,1),('.strtab',2,0x400),('.bss',5,4),
                                 ('.data',5,4)):
            with self.subTest(name=name,field=field),self.assertRaises(ValueError):
                self.verify(original_elf=self.section_change(name,field,value))

    def test_duplicate_identity_and_changed_unrelocated_text_stay_bound(self):
        table=next(iter(self.image['symbol_tables']))
        symbols=self.image['symbol_tables'][table]
        number=next(i for i,row in enumerate(symbols) if row['name']=='state_a')
        name_offset=struct.unpack_from('<I',self.original,self.image['sections'][table][4]+16*number)[0]
        with self.assertRaisesRegex(ValueError,'unique undefined'):
            self.verify(original_elf=self.symbol_change('state_b','name',name_offset))
        # An unrelated scalar instruction mutation can remain structurally valid,
        # but it must invalidate the full original-object fingerprint on replay.
        proof=self.verify()
        raw=bytearray(self.original)
        raw[self.image['sections'][self.image['text_index']][4]]^=1
        with self.assertRaises(ValueError):self.verify(original_elf=bytes(raw),manifest=proof)

    def test_changed_source_object_map_and_manifest_are_stale(self):
        proof=self.verify()
        for changes in (dict(preprocessed_source=self.preprocessed+b'\n'),
                        dict(objects=OBJECTS+b'\n')):
            with self.subTest(changes=list(changes)),self.assertRaisesRegex(ValueError,'manifest differs'):
                self.verify(manifest=proof,**changes)
        stale=copy.deepcopy(proof);stale['orphan_section']['sha256']='0'*64
        with self.assertRaisesRegex(ValueError,'manifest differs'):self.verify(manifest=stale)
        raw=bytearray(self.original)
        raw[self.image['sections'][self.sections['.rodata']][4]]^=1
        with self.assertRaises(ValueError):self.verify(original_elf=bytes(raw),manifest=proof)


if __name__=='__main__':unittest.main()
