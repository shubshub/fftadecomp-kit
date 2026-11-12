"""Authentic compiler ELF identity and complete native replay boundary tests."""
import argparse
import copy
import json
import os
from pathlib import Path
import struct
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'tools'))
import match
import match_evidence
import named_data_buffer_copy_binding_profile as adapter
import named_data_buffer_profile as buffers
import owner_admission_profile as owner
from test_local_shadow_halfword_matrix import fixture as helper_fixture

A, H, S = 0x08000200, 0x08000400, 0x03002000
SOURCE = '''struct Copy { unsigned int words[20]; };
extern struct Copy shadow_state;
extern void func_08000600(unsigned char *bytes);
unsigned int func_08000200(unsigned int a, unsigned int b, char *destination)
{
    unsigned char bytes[4];
    *(struct Copy *)(destination + 100) = shadow_state;
    bytes[0] = a;
    func_08000600(bytes);
    return bytes[0];
}
'''


class NativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory()
        root = cls.root = Path(cls.temporary.name)
        (root/'src').mkdir()
        (root/'include').mkdir()
        (root/'src/08000200.c').write_text(SOURCE)
        cls.args = argparse.Namespace(cc=match.DEFAULT_CC,cpp=match.DEFAULT_CPP,
            assembler=match.DEFAULT_AS,objcopy=match.DEFAULT_OBJCOPY,
            linker=match.DEFAULT_LD,flags=match.DEFAULT_FLAGS)
        cls.runner = match.Runner(match.DEFAULT_CC,'Ubuntu',match.DEFAULT_WSL_PATH,root=root)
        cls.workspace_context = cls.runner.workspace()
        cls.workspace = cls.workspace_context.__enter__()
        (root/'src/08000600.c').write_text('void func_08000600(unsigned char *bytes) { bytes[0] += 3; }')
        _, leaf, _ = match.compile_object(cls.runner,cls.workspace,cls.args,root,0x08000600,'src/08000600.c')
        cls.raw, body, cls.image = match.compile_object(cls.runner,cls.workspace,cls.args,root,A,'src/08000200.c')
        env = helper_fixture()
        cls.objects = env['objects']
        rows = json.loads(env['mapping'])
        rows[0].update(end=f'0x{A+len(body):08X}',instrs=0)
        rows.append(dict(rom='0x08000600',end=f'0x{0x08000600+len(leaf):08X}',mode='thumb',instrs=0))
        cls.mapping = json.dumps(rows).encode()
        # Derive synthetic linked ROM solely from this genuine compiler object's
        # relocation sites. Production authentication never uses these guesses.
        data = bytearray(body)
        for section_id in cls.image['relocations']:
            section = cls.image['sections'][section_id]
            symbols = cls.image['symbol_tables'][section[6]]
            raw = cls.image['section_data'][section_id]
            for pos in range(0,len(raw),8):
                site, info = struct.unpack_from('<II',raw,pos)
                symbol = symbols[info>>8]
                if info&255 == 10:
                    target = H if symbol['name']=='memcpy' else 0x08000600
                    delta = target-(A+site)-4
                    struct.pack_into('<HH',data,site,0xF000|((delta>>12)&2047),0xF800|((delta>>1)&2047))
                elif info&255 == 2:
                    struct.pack_into('<I',data,site,S)
                else:
                    raise AssertionError(info)
        cls.data = bytes(data)
        cls.rom = bytearray(env['rom'])
        cls.rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)] = data
        cls.rom.extend(bytes(max(0,0x08000600-match.ROM_BASE+len(leaf)-len(cls.rom))))
        cls.rom[0x08000600-match.ROM_BASE:0x08000600-match.ROM_BASE+len(leaf)]=leaf
        cls.rom = bytes(cls.rom)
        rows[0]['instrs'] = owner.refine(cls.data,A,cls.mapping)['instrs']
        rows[2]['instrs'] = owner.refine(leaf,0x08000600,cls.mapping)['instrs']
        cls.mapping = json.dumps(rows).encode()
        cls.index = ''.join(f'{int(row["rom"],16):08X} {int(row["end"],16):08X} '
            f'{int(row["end"],16)-int(row["rom"],16)} {row["instrs"]} bx\n' for row in rows).encode()
        cls.bindings, cls.targets = cls.original()

    @classmethod
    def tearDownClass(cls):
        cls.workspace_context.__exit__(None,None,None)
        cls.temporary.cleanup()

    @classmethod
    def original(cls, **changes):
        values = dict(image=cls.image,address=A,rom=cls.rom,mapping=cls.mapping,
            objects=cls.objects,index=cls.index,selector=adapter.SELECTOR)
        values.update(changes)
        return owner.original_bindings(**values)

    def verify(self, **changes):
        values=dict(data=self.data,address=A,rom=self.rom,mapping=self.mapping,
            index=self.index,objects=self.objects,bindings=self.bindings,selector=adapter.SELECTOR)
        values.update(changes)
        return owner.verify(**values)

    def test_authentic_compiler_original_link_and_native_replay(self):
        self.assertEqual(self.targets['memcpy'],(H,False))
        data, bindings = owner.object_bytes(self.runner,self.workspace,self.args,self.image,A,
            self.rom,self.mapping,self.objects,selector=adapter.SELECTOR,index=self.index)
        self.assertEqual(data,self.data)
        self.assertEqual(bindings,self.bindings)
        manifest, instructions = self.verify()
        self.assertTrue(instructions)
        self.assertEqual(manifest['profile'],adapter.SCHEMA)
        self.verify(manifest=manifest)
        boundary=manifest['proof']['compiler_copy_identity']
        for name in ('physical_access_proved','object_extent_proved','nonaliasing_proved',
                     'C_compatibility_proved','termination_proved'):
            self.assertFalse(boundary[name])

    def test_old_selector_remains_strict(self):
        with self.assertRaises(ValueError):
            self.original(selector=buffers.SELECTOR)

    def test_symbol_mutations(self):
        for field,value in (('name','memmove'),('name',f'func_{H:08X}'),('type',1),
                            ('bind',2),('value',1),('size',4),('section',1)):
            image=copy.deepcopy(self.image)
            for row in image['symbols']:
                if row['name']=='memcpy':row[field]=value
            with self.subTest(field=field,value=value),self.assertRaises(ValueError):
                self.original(image=image)
        image=copy.deepcopy(self.image)
        image['symbols'].append(copy.deepcopy(next(r for r in image['symbols'] if r['name']=='memcpy')))
        with self.assertRaises(ValueError):self.original(image=image)

    def test_stale_manifest(self):
        manifest,_=self.verify()
        for field in ('contract','producer_sha256'):
            stale=copy.deepcopy(manifest)
            stale['proof']['compiler_copy_identity'][field]='stale'
            with self.subTest(field=field),self.assertRaises(ValueError):self.verify(manifest=stale)

    def test_relocation_site_addend_kind_overlap_and_unresolved(self):
        section_id=self.image['relocations'][0]
        original=self.image['section_data'][section_id]
        sites=[struct.unpack_from('<II',original,pos) for pos in range(0,len(original),8)]
        copy_site=next(site for site,name in self.bindings['calls'] if name=='memcpy')
        position=next(pos for pos in range(0,len(original),8)
            if struct.unpack_from('<I',original,pos)[0]==copy_site)
        for change in ('site','kind','overlap','addend','unresolved'):
            image=copy.deepcopy(self.image)
            reloc=bytearray(original)
            site,info=struct.unpack_from('<II',reloc,position)
            if change=='site':struct.pack_into('<I',reloc,position,site+2)
            elif change=='kind':struct.pack_into('<I',reloc,position+4,(info&~255)|99)
            elif change=='overlap':reloc[8:16]=reloc[:8]
            elif change=='addend':
                text=bytearray(image['text']);text[site+2]^=1;image['text']=bytes(text)
            else:
                image['symbols'].append(dict(name='unresolved',section=0,value=0,bind=1,type=0,size=0))
            image['section_data'][section_id]=bytes(reloc)
            with self.subTest(change=change),self.assertRaises(ValueError):self.original(image=image)

    def test_count_site_bindings_and_complete_suffix(self):
        for role in ('calls','data'):
            binding=copy.deepcopy(self.bindings);binding[role].pop()
            with self.subTest(role=role),self.assertRaises(ValueError):self.verify(bindings=binding)
        data=bytearray(self.data)
        # Decoder reads the actual compiler instruction, never a guessed offset.
        decoder=match.Cs(match.CS_ARCH_ARM,match.CS_MODE_THUMB);decoder.detail=True
        count=next(i.address-A for i in decoder.disasm(self.data,A)
            if i.mnemonic=='movs' and i.op_str in ('r2, #0x50','r2, #80'))
        data[count]=79
        rom=bytearray(self.rom);rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)]=data
        with self.assertRaises(ValueError):self.verify(data=bytes(data),rom=bytes(rom))
        # Prefix proof alone cannot admit a changed unbalanced native suffix.
        site=next(site for site,name in self.bindings['calls'] if name=='memcpy')
        data=bytearray(self.data);data[site+4:site+6]=b'\x01\xb0'
        rom=bytearray(self.rom);rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)]=data
        with self.assertRaises(ValueError):self.verify(data=bytes(data),rom=bytes(rom))

    def test_changed_unrelocated_linked_bytes_refused(self):
        read=self.runner.read_binary
        def changed(path):
            raw=read(path)
            if path.endswith('/f.elf'):
                image=match.elf_image(raw)
                raw=bytearray(raw);raw[image['sections'][image['text_index']][4]]^=1
                return bytes(raw)
            return raw
        with patch.object(self.runner,'read_binary',side_effect=changed),self.assertRaises(ValueError):
            owner.object_bytes(self.runner,self.workspace,self.args,self.image,A,self.rom,
                self.mapping,self.objects,selector=adapter.SELECTOR,index=self.index)

    def test_report_fresh_and_stale_replay(self):
        for folder in ('config','symbols','build'):(self.root/folder).mkdir(exist_ok=True)
        (self.root/'config/functions.json').write_bytes(self.mapping)
        (self.root/'config/data_symbols.json').write_bytes(self.objects)
        (self.root/'symbols/functions.txt').write_bytes(self.index)
        (self.root/'baserom.bin').write_bytes(self.rom)
        with patch.dict(os.environ,FFTA_ROM=str(self.root/'baserom.bin')):
            result=owner.build(self.root,A,selector=adapter.SELECTOR)
            report=owner.render(A,result)
            self.assertEqual(owner.selector_for_report(report),adapter.SELECTOR)
            self.assertIn('* control flow: '+adapter.CONTROL_FLOW,report)
            self.assertTrue(match_evidence.report_matches(report,self.root,A))
            for name in ('src/08000200.c','config/functions.json','symbols/functions.txt','config/data_symbols.json'):
                path=self.root/name;raw=path.read_bytes()
                try:
                    path.write_bytes(raw+b'\n')
                    self.assertFalse(match_evidence.report_matches(report,self.root,A))
                finally:path.write_bytes(raw)
        for malformed in (report+f'* verification: `{buffers.SCHEMA}`\n',report+'* buffer calls: legacy\n'):
            with self.assertRaises(ValueError):owner.selector_for_report(malformed)

    def test_changed_data_addend_and_helper_ownership(self):
        image=copy.deepcopy(self.image)
        site=self.bindings['data'][0][0]
        text=bytearray(image['text']);struct.pack_into('<I',text,site,4);image['text']=bytes(text)
        bindings,_=self.original(image=image)
        with self.assertRaises(ValueError):self.verify(bindings=bindings)
        rows=json.loads(self.mapping)
        for changed in (rows+[dict(rows[1])],
                        [dict(row,instrs=48) if int(row['rom'],16)==H else row for row in rows],
                        rows+[dict(rom=f'0x{H+2:08X}',end=f'0x{H+4:08X}',mode='thumb',instrs=1)]):
            with self.subTest(mapping=changed),self.assertRaises(ValueError):
                self.original(mapping=json.dumps(changed).encode())

    def test_helper_and_index_mutations(self):
        rom=bytearray(self.rom);rom[H-match.ROM_BASE+20]^=1
        with self.assertRaises(ValueError):self.original(rom=bytes(rom))
        for old,new in ((b'98 49',b'98 48'),(f'{H+98:08X}'.encode(),f'{H+96:08X}'.encode())):
            with self.subTest(old=old),self.assertRaises(ValueError):
                self.original(index=self.index.replace(old,new))


if __name__=='__main__':unittest.main()
