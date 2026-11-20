"""Native shop category bounds, original symbol roles and rejection of stale inputs."""
import copy
import json
import os
from pathlib import Path
import struct
import sys
import tempfile
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import match
import match_evidence
import owner_admission_profile as owner
import shop_categories as shop


@unittest.skipUnless(os.getenv('FFTA_SHOP_CATEGORY_ROOT'), 'requires USA ROM and shop display C')
class ShopCategories(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_SHOP_CATEGORY_ROOT']).resolve()
        cls.raw,cls.manifest,_,cls.mapping,cls.index,cls.objects,cls.rom,_,elf = owner.build(
            cls.root,shop.OWNER,selector=shop.buffers.SELECTOR)
        cls.image = match.elf_image(elf)

    def test_original_elf_and_uncredited_preflight(self):
        self.assertEqual(self.raw,self.rom[0x6ed30:0x6ee98])
        original = self.manifest['bindings']
        self.assertEqual(original,shop.BINDINGS)
        targets = {f'func_{addr:08X}':(addr,False) for addr in shop.CALLS.values()}
        targets.update({name:(addr,True) for name,addr in shop.OBJECTS.items()})
        shop.check_original(self.image,original,targets)
        for group,row,field,value in [('calls',1,1,'func_080CC9F0'),('data',0,0,0x38),
                                      ('data',1,2,32),('data',3,1,'data_08393B40')]:
            bad = copy.deepcopy(original)
            bad[group][row][field] = value
            with self.subTest(change=(group,row,field)),self.assertRaises(ValueError):
                shop.check_original(self.image,bad,targets)
        with self.assertRaises(ValueError):
            shop.check_original(self.image,original,targets | {'g_table_0851D180':(shop.ITEMS,False)})
        for name, field, value in [('g_table_0851D180','size',32),('func_080CBD34','bind',0)]:
            image = copy.deepcopy(self.image)
            symbol = next(row for row in image['symbols'] if row['name'] == name)
            symbol[field] = value
            with self.subTest(symbol=name,field=field),self.assertRaises(ValueError):
                owner.original_bindings(image,shop.OWNER,self.rom,self.mapping,self.objects,
                                        selector=shop.buffers.SELECTOR,index=self.index)
        with self.assertRaisesRegex(ValueError,'original compiler ELF'):
            owner.preflight(self.raw,shop.OWNER,self.rom,self.mapping,self.index,self.objects,selector=shop.buffers.SELECTOR)

    def test_source_report_and_count_replay(self):
        path = Path('src/0806ED30.c')
        source = (self.root/path).read_text()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root/'include').mkdir()
            (root/'src').mkdir()
            (root/'include/ffta.h').write_bytes((self.root/'include/ffta.h').read_bytes())
            for old,new in [('present[6]','present[5]'),('entries[6]','entries[7]'),
                            ('u8 table)','u16 table)'),('g_table_0851D180[i].flags','g_table_0851D180[1].flags')]:
                self.assertIn(old,source)
                (root/path).write_text(source.replace(old,new))
                with self.assertRaises(ValueError):
                    shop.check_source(root)
        report = (self.root/'docs/match/0806ED30.md').read_text()
        self.assertTrue(match_evidence.report_matches(report,self.root,shop.OWNER))
        for old,new in [('"local":[-44,-38]','"local":[-44,-36]'),('"possible_count":[0,30]','"possible_count":[0,31]'),
                        (shop.buffers.SHOP_CATEGORY_CONTROL_FLOW,shop.buffers.CONTROL_FLOW)]:
            self.assertIn(old,report)
            self.assertFalse(match_evidence.report_matches(report.replace(old,new),self.root,shop.OWNER))
        rows = json.loads(self.mapping)
        item = next(row for row in rows if int(row['rom'],16) == shop.OWNER)
        self.assertEqual(item['instrs'],161)
        item['instrs'] = 180
        old_index = self.index.replace(b'0806ED30 0806EE98   360 161',b'0806ED30 0806EE98   360 180')
        self.assertNotEqual(self.index,old_index)
        opts = dict(bindings=shop.BINDINGS,selector=shop.buffers.SELECTOR)
        owner.verify(self.raw,shop.OWNER,self.rom,self.mapping,self.index,self.objects,**opts)
        for mapping,index in [(json.dumps(rows).encode(),old_index),(self.mapping,old_index),
                              (self.mapping,self.index.replace(b'080CECF4 080CED2C    56  25',b'080CECF4 080CED2C    56  28'))]:
            with self.assertRaises(ValueError):
                owner.verify(self.raw,shop.OWNER,self.rom,mapping,index,self.objects,**opts)

    def test_mutated_switch_and_category_record(self):
        for pc,check in [(0x080CA7D8,shop.classifier),(0x080CA7E4,shop.classifier),
                         (0x080CBD3E,shop.classifier),(0x080CBDB4,shop.classifier),
                         (0x080CCD0C,shop.supplemental_lookup),(0x080CCD24,shop.supplemental_lookup),
                         (0x080CECFE,shop.supplemental_lookup),(0x080CC9F6,shop.supplemental_lookup)]:
            changed = bytearray(self.rom)
            changed[pc-shop.BASE] ^= 1
            with self.subTest(pc=hex(pc)),self.assertRaises(ValueError):
                check(changed)
        bad = bytearray(self.rom)
        item = shop.ITEMS-shop.BASE+32*361
        # Force a mask-eligible regular item down the classifier's real 255 exit.
        bad[item+8] = bad[item+11] = 0
        bad[item+12] = 16
        self.assertEqual(shop.category(bad,361),255)
        with self.assertRaisesRegex(ValueError,'regular item'):
            shop.bounds(bad)
        bad = bytearray(self.rom)
        struct.pack_into('<H',bad,shop.SUPPLEMENTAL[0]-shop.BASE+4,65535)
        with self.assertRaisesRegex(ValueError,'outside the reviewed'):
            shop.bounds(bad)

    def test_mutated_frame_caller_and_dependencies(self):
        md = match.Cs(match.CS_ARCH_ARM,match.CS_MODE_THUMB)
        for pc in (0x0806ED3A,0x0806ED42,0x0806ED94,0x0806ED9C,0x0806EDC4,0x0806EDD2,
                   0x0806EE02,0x0806EE14,0x0806EE28,0x0806EE3E,0x0806EE56,0x0806EE74,0x0806EE80):
            changed = bytearray(self.raw)
            changed[pc-shop.OWNER] ^= 1
            instructions = {i.address:i for i in md.disasm(bytes(changed),shop.OWNER)}
            with self.subTest(pc=hex(pc)),self.assertRaises(ValueError):
                shop.owner_frame(instructions)
        bad = bytearray(self.rom)
        bad[shop.CALL_SITE-shop.BASE] ^= 1
        self.assertEqual(shop.direct_sites(bad,shop.OWNER),[])
        opts = dict(bindings=shop.BINDINGS,selector=shop.buffers.SELECTOR)
        objs = json.loads(self.objects)
        objs['g_table_0851D180'] = '0x0851D1A0'
        with self.assertRaises(ValueError):
            owner.verify(self.raw,shop.OWNER,self.rom,self.mapping,self.index,json.dumps(objs).encode(),**opts)

    def machine(self):
        from unicorn import Uc,UC_ARCH_ARM,UC_MODE_THUMB,UC_PROT_READ,UC_PROT_EXEC
        from unicorn import arm_const as reg
        from test_bg_affine_rows import NativeAffineRows
        cpu = Uc(UC_ARCH_ARM,UC_MODE_THUMB)
        for addr,size in ((shop.BASE,len(self.rom)),(0x02000000,0x40000),(0x03000000,0x8000)):
            cpu.mem_map(addr,size)
        cpu.mem_write(shop.BASE,self.rom)
        cpu.mem_protect(shop.BASE,len(self.rom),UC_PROT_READ|UC_PROT_EXEC)
        def call(addr,*args):
            regs = range(reg.UC_ARM_REG_R4,reg.UC_ARM_REG_R11+1)
            for r in regs:
                cpu.reg_write(r,0x69370000+r)
            value = NativeAffineRows.call(self,cpu,addr,*args)
            self.assertEqual([cpu.reg_read(r) for r in regs],[0x69370000+r for r in regs])
            return value
        return cpu,call

    def test_all_native_selectors_and_classifier_results(self):
        _,call = self.machine()
        for item in range(1,376):
            self.assertEqual(call(shop.CATEGORY,item),shop.category(self.rom,item))
        for selector in range(256):
            for i in range(31):
                expected = 0
                if 2 <= selector <= 6 and i:
                    offset = shop.SUPPLEMENTAL[selector-2]-shop.BASE+4+2*(i-1)
                    expected = struct.unpack_from('<H',self.rom,offset)[0]
                self.assertEqual(call(shop.QUERY,selector,i),expected)

    def test_native_owner_all_rank_table_prefixes_and_caller_stack(self):
        from unicorn import UC_HOOK_CODE
        from unicorn import arm_const as reg
        cpu,call = self.machine()
        entry_sp = 0x03007F00
        local = entry_sp-44
        state = entry_sp+24
        seen = {}
        def traced(machine,pc,width,context):
            if pc in (0x0806EDC8,0x0806EE18):
                seen['stores'].append(machine.reg_read(reg.UC_ARM_REG_R1)-local)
            elif pc == 0x0806ED6C:
                seen['fallback'] += 1
        for pc in (0x0806EDC8,0x0806EE18,0x0806ED6C):
            cpu.hook_add(UC_HOOK_CODE,traced,begin=pc,end=pc)
        for level,mask in ((9,16),(10,32),(20,64)):
            cpu.mem_write(shop.STATE+0x1f6c,struct.pack('<H',level))
            normal = [shop.category(self.rom,i) for i in range(1,362)
                      if self.rom[shop.ITEMS-shop.BASE+32*i+12]&mask]
            for count in range(31):
                for slot in range(30):
                    cpu.mem_write(shop.FLAGS+12*slot+1,bytes([3 if slot<count else slot%3]))
                for selector in (0,2,3,4,5,6):
                    cpu.mem_write(state-1,b'\xa5'*10)
                    seen.update(stores=[],fallback=0)
                    call(shop.OWNER,state,selector)
                    extra = []
                    if selector:
                        offset = shop.SUPPLEMENTAL[selector-2]-shop.BASE+4
                        ids = struct.unpack_from('<'+'H'*count,self.rom,offset)
                        extra = [shop.category(self.rom,item) for item in ids if item]
                    self.assertEqual(seen['stores'],normal+extra)
                    self.assertEqual(seen['fallback'],int(5 not in extra))
                    self.assertEqual(bytes(cpu.mem_read(state-1,10)),b'\xa5\xa5'+bytes(range(6))+b'\x06\xa5')


if __name__ == '__main__':
    unittest.main()
