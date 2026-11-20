from collections import Counter
import os
from pathlib import Path
import struct
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import item_ability_names as names
import owner_admission_profile as admission


@unittest.skipUnless(os.getenv('FFTA_ITEM_ABILITY_NAMES_ROOT'), 'requires the USA ROM, menu source and agbcc')
class ItemAbilityNames(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_ITEM_ABILITY_NAMES_ROOT']).resolve()
        cls.result = admission.build(cls.root,names.OWNER,selector=names.SELECTOR)
        cls.body,_,_,cls.mapping,cls.index,cls.objects,cls.rom,_,cls.elf = cls.result

    def test_original_compiler_roles_and_saved_report(self):
        from match_evidence import report_matches
        actual, targets = admission.original_bindings(names.match.elf_image(self.elf),names.OWNER,self.rom,
            self.mapping,self.objects,selector=names.SELECTOR,index=self.index)
        self.assertEqual(actual,names.bindings())
        self.assertEqual(targets['func_0806FFAC'],(names.DRAW,False))
        self.assertEqual(targets['g_table_085567F0'],(names.ABILITY_NAMES,True))
        self.assertEqual(self.body,self.rom[0x6fabc:0x6fb50])
        report = admission.render(names.OWNER,self.result)
        self.assertTrue(report_matches(report,self.root,names.OWNER))
        self.assertIn('"aligned_zero_words":7',report)
        self.assertFalse(report_matches(report.replace('"aligned_zero_words":7','"aligned_zero_words":8'),
                                        self.root,names.OWNER))

    def test_item_environment_drift(self):
        original = self.result[1]['proof']['environment']
        changed = dict(original, toolchain=[])
        for stage, fingerprints in (
                ('proof', (original, changed, original)),
                ('completion', (original, original, changed))):
            with self.subTest(stage=stage), patch.object(
                    names, 'environment_fingerprint', side_effect=fingerprints):
                with self.assertRaisesRegex(ValueError, 'changed during compilation'):
                    admission.build(self.root, names.OWNER, selector=names.SELECTOR)

    def test_changed_owner_provider_tables_and_bindings(self):
        for site in (0x0806FAF6,0x0806FB22,0x080C8DD8,0x080C8DF0,0x080CA814,0x080CD48C,
                     0x0836D4B8,0x08068B06,0x0806A5F4,0x0806F896,0x0806F93C,0x0806FFC0,0x08526CD8):
            with self.subTest(site=hex(site)):
                rom = bytearray(self.rom)
                rom[site-names.BASE] ^= 1
                with self.assertRaises(ValueError):
                    admission.verify(self.body,names.OWNER,bytes(rom),self.mapping,self.index,self.objects,
                                     bindings=names.bindings(),selector=names.SELECTOR)
        roles = names.bindings()
        roles['data'][0][1] = 'g_table_085567F0'
        with self.assertRaises(ValueError):
            admission.verify(self.body,names.OWNER,self.rom,self.mapping,self.index,self.objects,
                             bindings=roles,selector=names.SELECTOR)
        with self.assertRaisesRegex(ValueError,'original compiler ELF'):
            admission.preflight(self.body,names.OWNER,self.rom,self.mapping,self.index,self.objects,selector=names.SELECTOR)

    def test_private_source_extent(self):
        with tempfile.TemporaryDirectory(dir=self.root/'build') as directory:
            tree = Path(directory)
            (tree/'src').mkdir()
            (tree/'include').mkdir()
            (tree/'include/ffta.h').write_bytes((self.root/'include/ffta.h').read_bytes())
            source = (self.root/'src/0806FABC.c').read_text()
            for old,new in (('entries[3]','entries[2]'),('u16 id;','u32 id;'),('u8 sources[4];','u8 sources[5];'),
                            ('u16 first_tile;','u8 first_tile;')):
                self.assertIn(old,source)
                (tree/'src/0806FABC.c').write_text(source.replace(old,new))
                with self.assertRaisesRegex(ValueError,'declarations'):
                    names.check_source(tree)

    def test_table_limits_and_invalid_inputs(self):
        starts = (*names.words(self.rom,names.ROWS,24), names.ROWS_END)
        with self.assertRaises(ValueError):
            names.item_rows(self.rom,376,starts)
        # Both malformed records would read or write beyond the finite native objects;
        # exercise the table proof separately, without executing either invalid read/store.
        rom = bytearray(self.rom)
        ordinary = next(i for i in range(376) if rom[names.ITEMS-names.BASE+32*i+8] != 27)
        at = names.GRANTS-names.BASE+20*rom[names.ITEMS-names.BASE+32*ordinary+29]
        rom[at:at+10] = bytes((4,0,1,0,1,0,1,0,1,0))
        with self.assertRaisesRegex(ValueError,'private output'):
            names.item_rows(rom,ordinary,starts)
        rom[at:at+6] = bytes((2,0,7,0,1,0))
        with self.assertRaisesRegex(ValueError,'group exceeds'):
            names.item_rows(rom,ordinary,starts)
        switched = bytearray(self.rom)
        switched[0xC8DEC:0xC8DF0] = struct.pack('<I',0x080C8E60)
        with self.assertRaisesRegex(ValueError,'grouping switch'):
            names.collector_cfg(switched)

    def call(self,cpu,address,*args):
        from test_bg_affine_rows import NativeAffineRows
        return NativeAffineRows.call(self,cpu,address,*args)

    def segment(self,cpu,start,end):
        from unicorn.arm_const import UC_ARM_REG_PC
        cpu.emu_start(start|1,end,count=1800000)
        self.assertEqual(cpu.reg_read(UC_ARM_REG_PC),end)

    def native(self):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_INTR
        from unicorn.arm_const import UC_ARM_REG_PC, UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2
        cpu = Uc(UC_ARCH_ARM,UC_MODE_THUMB)
        for base,size in ((names.BASE,len(self.rom)),(0x02000000,0x40000),(0x03000000,0x8000),
                          (0x04000000,0x1000),(0x05000000,0x1000),(0x06000000,0x18000)):
            cpu.mem_map(base,size)
        cpu.mem_write(names.BASE,self.rom)
        clear_calls = []
        def bios(machine, interrupt, context):
            pc = machine.reg_read(UC_ARM_REG_PC)
            src,dst,ctl = (machine.reg_read(r) for r in (UC_ARM_REG_R0,UC_ARM_REG_R1,UC_ARM_REG_R2))
            self.assertIn(pc,(0x0814186A,0x0814186E))
            count = ctl & 0x1FFFFF
            if not count:
                return
            width = 4 if pc == 0x0814186A or ctl & (1<<26) else 2
            filling = ctl & (1<<24)
            if pc == 0x0814186A:
                self.assertEqual(count%8,0)
                clear_calls.append((dst,ctl))
            data = bytes(machine.mem_read(src,width if filling else width*count))
            machine.mem_write(dst,data*count if filling else data)
        cpu.hook_add(UC_HOOK_INTR,bios)
        self.call(cpu,0x08002768)
        self.assertEqual(cpu.mem_read(0x03005E78,176),self.rom[0xA38A2C:0xA38ADC])
        return cpu,clear_calls

    def test_native_all_items_original_scene_renderer_and_installed_list(self):
        from unicorn import UC_HOOK_CODE
        from unicorn.arm_const import UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3, UC_ARM_REG_R4, UC_ARM_REG_SP
        cpu,clears = self.native()
        word = lambda at: int.from_bytes(cpu.mem_read(at,4),'little')
        self.call(cpu,0x080227E8)
        # Run the original case-0 root allocation, publication and whole-record clear.
        self.segment(cpu,0x08068B00,0x08068B16)
        parent = word(names.SCENE)
        self.assertTrue(0x020159D0 <= parent < parent+0x9C08 <= 0x02040000)
        menu,drawing = parent+0x1A88,parent+0x39F4
        cpu.mem_write(names.GRAPHICS+0x10,struct.pack('<I',0x06000000))
        # The actual outer constructor computes the tile from VRAM and installs both
        # the text context and window dimensions before calling the owner.
        cpu.reg_write(UC_ARM_REG_R4,parent)
        cpu.reg_write(UC_ARM_REG_SP,0x03007C00)
        self.segment(cpu,0x0806A5C4,0x0806F89A)
        self.assertEqual(bytes(cpu.mem_read(menu+0x1A,2)),bytes((13,18)))
        self.assertEqual(int.from_bytes(cpu.mem_read(menu+0x50,2),'little'),0x580)
        self.assertEqual(word(menu+0x7C),drawing)
        cpu.mem_write(menu,b'\x01')
        renders,outputs = [],[]
        def observe(machine,pc,size,context):
            sp = machine.reg_read(UC_ARM_REG_SP)
            if pc == 0x08015110:
                renders.append(tuple(machine.reg_read(r) for r in
                                     (UC_ARM_REG_R0,UC_ARM_REG_R1,UC_ARM_REG_R2,UC_ARM_REG_R3))+(word(sp),))
            elif pc == names.COLLECT:
                outputs.append(machine.reg_read(UC_ARM_REG_R1))
            else:
                self.assertEqual(outputs[-1],sp)
                outputs.append((machine.reg_read(UC_ARM_REG_R0),bytes(machine.mem_read(sp,28))))
        for pc in (0x08015110,names.COLLECT,0x0806FAFA):
            cpu.hook_add(UC_HOOK_CODE,observe,begin=pc,end=pc)
        cpu.ctl_flush_tb()
        histogram = Counter()
        starts = (*names.words(self.rom,names.ROWS,24), names.ROWS_END)
        first,step,extent = 0x0600B000,26*32,24*32
        last = first+3*step+extent
        for item in range(376):
            item_name,out,abilities = names.item_rows(self.rom,item,starts)
            cpu.mem_write(first-4,b'LEFT'+b'\xA5'*(last-first)+b'RGHT')
            cpu.mem_write(parent+0x44EC,struct.pack('<H',item))
            cpu.mem_write(menu+6,b'\xFF\xFF')
            clears.clear()
            renders.clear()
            outputs.clear()
            cpu.reg_write(UC_ARM_REG_R4,names.SCENE)
            cpu.reg_write(UC_ARM_REG_SP,0x03007C00)
            start = 0x0806B1D6 if item % 2 == 0 else 0x0806D262
            self.segment(cpu,start,0x0806F940)
            pointers = (item_name,*abilities)
            self.assertEqual(renders,[(drawing,first+i*step,ptr,5,1) for i,ptr in enumerate(pointers)],(item,clears,outputs))
            self.assertEqual(clears,[(first+i*step,0x010000C0) for i in range(len(pointers))])
            if out is None:
                self.assertEqual(outputs,[])
            else:
                self.assertEqual(len(outputs),2)
                self.assertEqual(outputs[1],(len(abilities),out))
            self.assertEqual(cpu.mem_read(first-4,4),b'LEFT')
            self.assertEqual(cpu.mem_read(last,4),b'RGHT')
            for i in range(3):
                self.assertEqual(cpu.mem_read(first+i*step+extent,step-extent),b'\xA5'*(step-extent))
            if item == 135:
                from hashlib import sha256
                print('RASTER',sha256(cpu.mem_read(first,last-first)).hexdigest())
            histogram['bypass' if out is None else str(len(abilities))] += 1
        self.assertEqual(histogram,{'bypass':10,'0':150,'1':96,'2':82,'3':38})
        self.segment(cpu,0x08068BE4,0x08068BF4)
        self.assertEqual(word(names.SCENE),0)
