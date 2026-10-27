"""Canonical binary64 + the existing exact guarded local word-table encoding."""
import copy
import io
from contextlib import redirect_stdout
import json
import struct
import sys
import unittest
from unittest.mock import patch
import test_software_double_profile as fixture

BASE, match, profile = fixture.BASE, fixture.match, fixture.profile
SOURCE = '''extern int func_08000200(int);
extern int state;
double func_08000000(unsigned selector, int value)
{
    double converted = (double)value;
    switch (selector) {
    case 0: return converted + 1.0;
    case 1: return converted - 2.0;
    case 2: return converted * 3.0;
    case 3: return converted / 4.0;
    case 4: return (double)func_08000200(value);
    case 5: return converted + (double)state;
    case 6: return converted * 7.0;
    default: return converted;
    }
}
'''

class SoftwareDoubleSwitchTests(unittest.TestCase):
    setUpClass = classmethod(fixture.SoftwareDoubleTests.setUpClass.__func__)
    setUp = fixture.SoftwareDoubleTests.setUp
    def indexes(self,size,count):
        fixture.SoftwareDoubleTests.indexes(self,size,count)
        entries=json.loads(self.mapping)
        entries.extend(dict(rom=f'0x{a:08X}',end=f'0x{z:08X}',mode='thumb',instrs=n)
                       for a,z,n,_ in profile.DIVISION_IDENTITIES)
        entries.append(dict(rom='0x08142950',end='0x08142A1E',mode='thumb',instrs=102))
        self.mapping=json.dumps(entries).encode()
        self.index=''.join(f"{int(e['rom'],16):08X} {int(e['end'],16):08X} "
            f"{int(e['end'],16)-int(e['rom'],16)} {e['instrs']} return\n" for e in entries).encode()
    patched_rom = fixture.SoftwareDoubleTests.patched_rom

    def fixture(self, source=SOURCE, *, remainder_target=False):
        (self.root/'src/08000000.c').write_text(source)
        self.data_mapping=json.dumps({'state':'0x02000000'}).encode()
        self.words,self.literals={},{}
        runner=match.Runner(match.DEFAULT_CC,root=self.root,timeout=120)
        with runner.workspace() as workspace:
            _,_,self.original=match.compile_object(runner,workspace,self.args,self.root,BASE,'src/08000000.c')
            symbol,_=match.function_record(self.original,'func_08000000',BASE,True)
            self.indexes(symbol['size'],1)
            self.body,self.calls,self.bindings=profile.object_bytes(runner,workspace,self.args,
                self.original,BASE,self.mapping,self.runtime_rom,self.index,
                data_mapping=self.data_mapping,data_relocations=self.literals,switch_relocations=self.words)
        rom=bytearray(self.runtime_rom);rom[:len(self.body)]=self.body;self.rom=bytes(rom)
        self.instructions=match.verify_leaf_instructions(self.body,BASE,True,self.calls,
            double_context=(self.rom,self.mapping,self.index,self.bindings)+((True,) if remainder_target else ()),switch_relocations=self.words)
        self.indexes(len(self.body),len(self.instructions))
        for name,contents in [('config/functions.json',self.mapping),('symbols/functions.txt',self.index),
                              ('config/data_symbols.json',self.data_mapping)]:
            (self.root/name).write_bytes(contents)
        self.manifest=profile.make_manifest(self.calls,BASE,self.bindings,self.instructions,
            literals=self.literals,data_mapping=self.data_mapping,switch=profile.switch_record(self.body,BASE,self.words),remainder_target=remainder_target)

    def verify(self,manifest=None,body=None,rom=None):
        return profile.verify(self.body if body is None else body,BASE,self.rom if rom is None else rom,
            self.mapping,self.index,self.manifest if manifest is None else manifest,data_mapping=self.data_mapping)

    def test_natural_original_elf_complete_partition_and_fresh_native_report(self):
        self.fixture();self.assertTrue(self.words);self.assertTrue(self.literals)
        self.assertEqual(len(self.verify()),len(self.instructions))
        descriptor=self.manifest['switch']['layout']
        self.assertEqual(descriptor['bound'],6)
        from switch_constants_profile import complete_partition
        complete_partition(self.body,BASE,self.instructions,descriptor)
        opening,reading=self.patched_rom()
        with opening,reading,patch.object(sys,'argv',['match.py','--root',str(self.root),
                '--software-double-profile',profile.SELECTOR,'0x08000000']),redirect_stdout(io.StringIO()):
            self.assertEqual(match.main(),0)
        report=(self.root/'docs/match/08000000.md').read_text()
        opening,reading=self.patched_rom()
        with opening,reading:
            self.assertTrue(profile.report_matches(report,self.root,BASE))
            path=self.root/'src/08000000.c';path.write_text(SOURCE.replace('7.0','8.0'))
            self.assertFalse(profile.report_matches(report,self.root,BASE))

    def test_switch_dynamic_division_and_bounded_remainder_keep_typed_context(self):
        source=SOURCE.replace('case 4: return (double)func_08000200(value);',
            'case 4: return converted + (double)(value / func_08000200(value));').replace(
            'case 5: return converted + (double)state;',
            'case 5: return converted + (double)((short)value % 101) + (double)state;')
        self.fixture(source)
        self.assertIn('signed_division',self.manifest)
        self.assertIn('remainder',self.manifest)
        self.assertIn('switch',self.manifest)
        self.assertEqual(self.manifest['remainder']['dividend'],'signed16')
        self.verify()
        opening,reading=self.patched_rom()
        with opening,reading,patch.object(sys,'argv',['match.py','--root',str(self.root),
                '--software-double-profile',profile.SELECTOR,'0x08000000']),redirect_stdout(io.StringIO()):
            self.assertEqual(match.main(),0)
        for unsafe in (source.replace('(short)value % 101','value % 101'),
                       source.replace('(short)value % 101','(short)value % func_08000200(value)')):
            with self.subTest(source=unsafe),self.assertRaisesRegex(ValueError,'signed16 r0 and nonzero r1'):
                self.fixture(unsafe)

    def test_explicit_target_remainder_composes_without_widening_default_numeric_policy(self):
        source=SOURCE.replace('case 5: return converted + (double)state;',
            'case 5: return converted + (double)(value % func_08000200(value)) + (double)state;')
        with self.assertRaisesRegex(ValueError,'signed16 r0 and nonzero r1'):
            self.fixture(source)
        self.fixture(source,remainder_target=True)
        self.assertIn('target_remainder',self.manifest)
        self.assertNotIn('remainder',self.manifest)
        self.verify()
        opening,reading=self.patched_rom()
        with opening,reading,patch.object(sys,'argv',['match.py','--root',str(self.root),
                '--software-double-profile',profile.SELECTOR,'--software-double-remainder-profile',
                profile.REMAINDER_TARGET_SELECTOR,'0x08000000']),redirect_stdout(io.StringIO()):
            self.assertEqual(match.main(),0)
        report=(self.root/'docs/match/08000000.md').read_text()
        opening,reading=self.patched_rom()
        with opening,reading:self.assertTrue(profile.report_matches(report,self.root,BASE))

    def test_manifest_requires_exact_guard_bounds_and_unique_integer_local_words(self):
        self.fixture()
        for kind in ('missing','schema','bound','target','float','bool','descriptor_float','descriptor_bool','duplicate','extra'):
            manifest=copy.deepcopy(self.manifest);record=manifest['switch']
            if kind=='missing':del manifest['switch']
            elif kind=='schema':record['schema']='other'
            elif kind=='bound':record['layout']['bound']+=1
            elif kind=='target':record['layout']['relocations'][1][1]+=2
            elif kind=='float':record['layout']['relocations'][0][0]=float(record['layout']['literal'])
            elif kind=='bool':record['layout']['relocations'][0][0]=False
            elif kind=='descriptor_float':record['layout']['bound']=float(record['layout']['bound'])
            elif kind=='descriptor_bool':record['layout']['bound']=True
            elif kind=='duplicate':record['layout']['relocations'].append(record['layout']['relocations'][0])
            else:record['extra']=True
            with self.subTest(kind=kind),self.assertRaises(ValueError):self.verify(manifest)

    def test_original_elf_switch_requires_fresh_collection_and_section_identity(self):
        self.fixture();runner=match.Runner(match.DEFAULT_CC,root=self.root,timeout=120)
        with runner.workspace() as workspace:
            with self.assertRaisesRegex(ValueError,'original-ELF provenance'):
                profile.object_bytes(runner,workspace,self.args,self.original,BASE,self.mapping,
                    self.runtime_rom,self.index,data_mapping=self.data_mapping,data_relocations={})
            with self.assertRaisesRegex(ValueError,'empty collection'):
                profile.object_bytes(runner,workspace,self.args,self.original,BASE,self.mapping,
                    self.runtime_rom,self.index,data_mapping=self.data_mapping,data_relocations={},switch_relocations={0:0})
            changed=copy.deepcopy(self.original)
            section=next(s for s in changed['symbols'] if s['type']==3 and s['section']==changed['text_index'])
            section['value']=2
            for symbols in changed['symbol_tables'].values():
                for item in symbols:
                    if item['type']==3 and item['section']==changed['text_index']:item['value']=2
            with self.assertRaises(ValueError):
                profile.object_bytes(runner,workspace,self.args,changed,BASE,self.mapping,
                    self.runtime_rom,self.index,data_mapping=self.data_mapping,data_relocations={},switch_relocations={})

    def test_changed_guard_table_code_and_unowned_tail_reject(self):
        self.fixture();layout=self.manifest['switch']['layout']
        for offset,value in [(layout['comparison'],0x2807),(layout['guard'],0xD3FF),
                             (layout['dispatch']+8,0x4680),(layout['table'],BASE+layout['dispatch']+2)]:
            changed=bytearray(self.body)
            struct.pack_into('<I' if offset==layout['table'] else '<H',changed,offset,value)
            rom=bytearray(self.rom);rom[:len(changed)]=changed
            with self.subTest(offset=offset),self.assertRaises(ValueError):self.verify(body=bytes(changed),rom=bytes(rom))
        from switch_constants_profile import complete_partition
        with self.assertRaisesRegex(ValueError,'unowned'):
            complete_partition(self.body+b'\0\0',BASE,self.instructions,layout)
        with self.assertRaises(ValueError):
            match.verify_leaf_instructions(self.body,BASE,True,self.calls,switch_relocations=self.words)

if __name__=='__main__':unittest.main()
