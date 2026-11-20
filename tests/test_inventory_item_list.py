import json
import os
from pathlib import Path
import struct
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import inventory_item_list as items
import owner_admission_profile as admission
from match_evidence import report_matches

SELECTOR = items.named.ITEM_LIST_SELECTOR


@unittest.skipUnless(os.getenv('FFTA_ITEM_LIST_ROOT'), 'requires the USA ROM, item-list source and agbcc')
class InventoryItemListTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_ITEM_LIST_ROOT']).resolve()
        cls.result = admission.build(cls.root, items.OWNER, selector=SELECTOR)
        cls.body, _, _, cls.mapping, cls.index, cls.objects, cls.rom, _, cls.elf = cls.result

    def test_saved_report_and_original_elf(self):
        self.assertEqual(self.body, self.rom[0x8CBDC:0x8D0C4])
        original, _ = admission.original_bindings(items.match.elf_image(self.elf), items.OWNER,
            self.rom, self.mapping, self.objects, selector=SELECTOR, index=self.index)
        self.assertEqual(original, items.bindings())
        report = admission.render(items.OWNER, self.result)
        self.assertTrue(report_matches(report, self.root, items.OWNER))
        changed = report.replace('"maximum_rows":252', '"maximum_rows":256')
        self.assertNotEqual(changed, report)
        self.assertFalse(report_matches(changed, self.root, items.OWNER))

    def test_bindings_owner_and_index(self):
        def verify(body=self.body, mapping=self.mapping, index=self.index, bindings=None, address=items.OWNER):
            admission.verify(body,address,self.rom,mapping,index,self.objects,
                             bindings=items.bindings() if bindings is None else bindings,selector=SELECTOR)
        binding = items.bindings()
        binding['data'][1][1] = 'g_table_08526680'
        for offset in (0xCC68-0xCBDC,0xD084-0xCBDC,0xD094-0xCBDC):
            with self.subTest(offset=offset), self.assertRaises(ValueError):
                wrong = bytearray(self.body)
                wrong[offset] ^= 1
                verify(bytes(wrong))
        with self.assertRaises(ValueError):
            verify(bindings=binding)
        with self.assertRaises(ValueError):
            verify(address=0x0808D0C4)
        index = self.index.replace(b'0808CBDC 0808D0C4  1256 564',b'0808CBDC 0808D0C4  1256 628')
        self.assertNotEqual(index,self.index)
        with self.assertRaises(ValueError):
            verify(index=index)

    def test_native_providers_and_category_bounds(self):
        self.assertEqual(items.bound_groups(self.rom,self.objects),[23,51,252,12,23,14])
        for site in (0x0808D762,0x0808EFA2,0x080711D4,0x08071234,0x080CA956):
            with self.subTest(site=site), self.assertRaises(ValueError):
                changed = bytearray(self.rom)
                changed[site-0x08000000] ^= 1
                items.providers(bytes(changed),self.mapping,self.index)
        # Exercise the actual census, independently of the outer ROM fingerprint.
        changed = bytearray(self.rom)
        changed[items.DEFINITIONS-0x08000000+32+8] = 0
        with self.assertRaises(ValueError):
            items.bound_groups(bytes(changed),self.objects)
        wrong = json.loads(self.objects)
        wrong['g_table_08520080'] = '0x08520060'
        with self.assertRaises(ValueError):
            items.bound_groups(self.rom,json.dumps(wrong).encode())

    def test_source_and_header(self):
        paths = ('include/ffta.h','src/0808CBDC.c')
        with tempfile.TemporaryDirectory(dir=self.root/'build') as directory:
            tree = Path(directory)
            for path in paths:
                (tree/path).parent.mkdir(exist_ok=True)
                (tree/path).write_bytes((self.root/path).read_bytes())
            for path,old,new in ((paths[1],'items[256]','items[252]'),
                                 (paths[1],'u16 slot;','u8 slot;'),
                                 (paths[1],'ItemRow storage[256]','ItemRow storage[14]'),
                                 (paths[1],'i < second_count','i < count'),
                                 (paths[0],'unsigned short u16','signed short u16')):
                with self.subTest(old=old):
                    target = tree/path
                    original = target.read_text()
                    self.assertIn(old,original)
                    target.write_text(original.replace(old,new))
                    with self.assertRaises(ValueError):
                        items.check_source(tree)
                    target.write_text(original)

    def call(self, cpu, address, *arguments):
        from test_bg_affine_rows import NativeAffineRows
        return NativeAffineRows.call(self,cpu,address,*arguments)

    def test_real_scene_inventory_updates_and_rows(self):
        from unicorn.arm_const import UC_ARM_REG_PC
        from test_packed_transfer_task import TransferTaskTests
        cpu = TransferTaskTests.cpu(self)
        self.call(cpu,0x080227E8)
        cpu.emu_start(0x08024643,0x08024654,count=500000)
        self.assertEqual(cpu.reg_read(UC_ARM_REG_PC),0x08024654)
        self.call(cpu,0x0807109C,0)
        word = lambda address: int.from_bytes(cpu.mem_read(address,4),'little')
        scene = word(items.SCENE)
        pane = word(scene+0x2D50)
        self.assertEqual(pane,scene+items.PANE)
        self.assertEqual(word(scene+0x2E1C),scene+items.NEXT_PANE)
        self.assertTrue(0x020159D0 <= word(0x03002778) <= scene < scene+0x7240 <= 0x02040000)
        self.assertEqual(self.call(cpu,0x0808EF90,6),0)
        # Native insert and equipped-count updates maintain a unique slot for every ID.
        ids = sorted(range(1,376),key=lambda x:(x*251)%379)
        for identifier in ids:
            self.assertEqual(self.call(cpu,0x080CA900,identifier,1+identifier%4),0)
            if identifier%3 == 0:
                self.call(cpu,0x080CAB24,identifier,1)
        self.assertEqual(self.call(cpu,0x0808EF90,6),1)
        groups = ((21,24),(24,27),(1,20),(20,21),(27,30),(30,31))
        def verify_rows(category):
            catalog = self.rom[0x51D180:0x520080]
            inventory = bytes(cpu.mem_read(items.INVENTORY,375*4))
            first, end = groups[min(category,5)]
            banks = [[],[]]
            for i, (identifier,quantity,equipped) in enumerate(struct.iter_unpack('<HBB',inventory)):
                if first <= catalog[32*identifier+8] < end and quantity:
                    banks[i>=361].append((identifier,quantity,equipped,i if i<361 else i-361))
            initial = bytearray(b'\xa5'*(items.NEXT_PANE-items.PANE))
            cpu.mem_write(pane-4,b'LEFT'+bytes(initial)+b'RGHT')
            expected = bytearray(initial)
            accepted = banks[0]+banks[1]
            struct.pack_into('<II',expected,0,len(accepted),0x08526680)
            struct.pack_into('<4BH',expected,12,0,0,22,11,0x229)
            expected[18] = 0
            struct.pack_into('<HBBI',expected,20,0,16,0,pane+items.HEADER)
            for row,(identifier,quantity,equipped,slot) in enumerate(accepted):
                offset = items.HEADER+row*items.ROW
                name,description = struct.unpack_from('<HH',catalog,32*identifier)
                struct.pack_into('<HHH',expected,offset,row,0,identifier)
                struct.pack_into('<IHBBB',expected,offset+8,name,description,
                                 255 if category == 5 else equipped,quantity,
                                 0 if row<len(banks[0]) else 1 if row<len(banks[1]) else 2)
                struct.pack_into('<H',expected,offset+18,slot)
            self.assertEqual(self.call(cpu,items.OWNER,category,pane),len(accepted))
            self.assertEqual(bytes(cpu.mem_read(pane-4,8+len(initial))),b'LEFT'+bytes(expected)+b'RGHT')
            return len(accepted)
        self.assertEqual([verify_rows(k) for k in range(6)],[23,51,252,12,23,14])
        self.assertEqual(verify_rows(65535),14)
        self.assertEqual(self.call(cpu,0x080CA9E8,ids[0],99),0)
        verify_rows(2)
        # Safe unique IDs distributed across noncanonical banks exercise tag 2;
        # the ordinary adder creates no mixed-category bank for the original catalog.
        category_ids = [i for i in ids if 21 <= self.rom[0x51d188+32*i] < 24]
        cpu.mem_write(items.INVENTORY,bytes(375*4))
        for i,identifier in zip((0,361,363,374),category_ids):
            cpu.mem_write(items.INVENTORY+4*i,struct.pack('<HBB',identifier,3,1))
        self.assertEqual(verify_rows(0),4)


if __name__ == '__main__':
    unittest.main()
