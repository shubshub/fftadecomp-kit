import os
from pathlib import Path
import struct
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import ability_list_pane as pane
import owner_admission_profile as admission


@unittest.skipUnless(os.getenv('FFTA_ABILITY_PANE_ROOT'), 'requires the USA ROM, ability pane source and agbcc')
class AbilityListPaneTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_ABILITY_PANE_ROOT']).resolve()
        cls.result = admission.build(cls.root,pane.OWNER,selector=pane.named.ABILITY_RANGE_SELECTOR)
        cls.body, _, _, cls.mapping, cls.index, cls.objects, cls.rom, _, cls.elf = cls.result

    def test_saved_report_and_original_roles(self):
        from match_evidence import report_matches
        original, targets = admission.original_bindings(pane.match.elf_image(self.elf),pane.OWNER,
            self.rom,self.mapping,self.objects,selector=pane.named.ABILITY_RANGE_SELECTOR,index=self.index)
        self.assertEqual(original,pane.bindings())
        self.assertEqual(targets['func_080CD480'],(pane.LOOKUP,False))
        self.assertEqual(self.body,self.rom[0x7B928:0x7BA3C])
        report = admission.render(pane.OWNER,self.result)
        self.assertTrue(report_matches(report,self.root,pane.OWNER))
        self.assertIn('"maximum_iterations":26',report)
        self.assertFalse(report_matches(report.replace('"maximum_iterations":26','"maximum_iterations":27'),
                                        self.root,pane.OWNER))

    def test_native_table_extents_and_returning_query_domain(self):
        limits = pane.limits(self.rom,self.objects)
        self.assertEqual((limits['jobs'],limits['maximum_last'],limits['maximum_iterations']), (116,141,26))
        self.assertEqual(limits['returning_job_pairs']+limits['repeating_job_pairs'],116*116)
        self.assertGreater(limits['repeating_job_pairs'],0)
        cpu = self.cpu()
        caps = [self.call(cpu,0x080C9ED8,race) for race in range(1,24)]
        self.assertEqual(caps,limits['unit_ability_counts'][1:])
        self.assertEqual((caps[21],limits['row_entries'][22]),(11,17))
        self.assertTrue(all(cap <= width for cap,width in zip(caps,limits['row_entries'][1:])))

    def test_original_owner_helpers_allocator_and_caller_mutations(self):
        for site in (0x0807B978,0x0807B9BE,0x0807B9EC,0x0807BA38,0x080CCF24,0x080CD48C,0x080C92FE,
                     0x080C8A0E,0x080711DE,0x080706F0,0x0807C8B0,0x0807D302,0x08071264,0x0851BA88):
            with self.subTest(site=hex(site)):
                mutated = bytearray(self.rom)
                mutated[site-0x08000000] ^= 1
                with self.assertRaises(ValueError):
                    admission.verify(self.body,pane.OWNER,bytes(mutated),self.mapping,self.index,self.objects,
                                     bindings=pane.bindings(),selector=pane.named.ABILITY_RANGE_SELECTOR)
        bindings = pane.bindings()
        bindings['data'][0][2] = 4
        with self.assertRaises(ValueError):
            admission.verify(self.body,pane.OWNER,self.rom,self.mapping,self.index,self.objects,
                             bindings=bindings,selector=pane.named.ABILITY_RANGE_SELECTOR)

    def test_source_frame_and_record_extent(self):
        with tempfile.TemporaryDirectory(dir=self.root/'build') as directory:
            tree = Path(directory)
            (tree/'src').mkdir()
            (tree/'include').mkdir()
            (tree/'include/ffta.h').write_bytes((self.root/'include/ffta.h').read_bytes())
            path = Path('src/0807B928.c')
            src = (self.root/path).read_text()
            for old,new in (('indices[256]','indices[255]'),('entries[0x8E]','entries[0x8D]'),
                            ('ability_points[0x8E]','ability_points[0x90]'),('u32 name;','u16 name;')):
                self.assertIn(old,src)
                (tree/path).write_text(src.replace(old,new))
                with self.assertRaisesRegex(ValueError,'pane declarations'):
                    pane.check_source(tree)

    def call(self,cpu,address,*args):
        from test_bg_affine_rows import NativeAffineRows
        return NativeAffineRows.call(self,cpu,address,*args)

    def cpu(self):
        from test_packed_transfer_task import TransferTaskTests
        return TransferTaskTests.cpu(self)

    def segment(self,cpu,start,end):
        from unicorn.arm_const import UC_ARM_REG_PC
        cpu.emu_start(start|1,end,count=500000)
        self.assertEqual(cpu.reg_read(UC_ARM_REG_PC),end)

    def test_original_allocation_and_callers(self):
        from unicorn import UC_HOOK_CODE,UC_HOOK_MEM_WRITE
        from unicorn.arm_const import UC_ARM_REG_R0,UC_ARM_REG_R1,UC_ARM_REG_R4,UC_ARM_REG_R5,UC_ARM_REG_R7,UC_ARM_REG_SP

        cpu = self.cpu()
        word = lambda address: int.from_bytes(cpu.mem_read(address,4),'little')
        self.call(cpu,0x080227E8)
        self.segment(cpu,0x08024642,0x08024654)
        arena = word(0x03002778)
        self.assertTrue(0x020159D0 <= arena < arena+0xC600 <= 0x02040000)
        self.assertEqual(word(0x03000E54),0xC600)
        self.call(cpu,0x0807109C,0)
        scene = word(pane.SCENE)
        output = word(scene+0x2E1C)
        self.assertTrue(arena <= scene < scene+pane.SCENE_SIZE <= arena+0xC600)
        self.assertEqual(output,scene+pane.PANE)

        # Select an active record with the original optional roster filter, then
        # use the original cursor-clamp, pointer publication and scene-side load.
        unit = 0x02000080
        cpu.mem_write(unit+4,b'\x01')
        cpu.mem_write(0x020020E4,b'\x80')
        # Previous menu's live allocation and one valid cursor selection.
        self.call(cpu,0x08064EF8,0,0x02012000)
        previous = word(0x0200F454)
        self.assertEqual(self.call(cpu,0x08067FFC,previous+0x424),1)
        task = self.call(cpu,0x08064FA0,7)
        context = task+24
        cpu.mem_write(context+0x68,struct.pack('<HH',1,0))
        cpu.reg_write(UC_ARM_REG_R7,context)
        self.segment(cpu,0x08065486,0x080654AA)
        self.assertEqual(word(0x030027F4),unit)
        self.segment(cpu,0x080706E4,0x080706F2)
        self.assertEqual(word(scene+0x1D0C),unit)
        index_writes, first_last, outputs = [], [], []
        def index_write(machine,access,address,width,value,context):
            from unicorn.arm_const import UC_ARM_REG_PC
            if machine.reg_read(UC_ARM_REG_PC) == 0x0807B9BE:
                index_writes.append((address,width,value))
        cpu.hook_add(UC_HOOK_MEM_WRITE,index_write)
        def observe(machine,address,width,context):
            sp = machine.reg_read(UC_ARM_REG_SP)
            if address == 0x0807B984:
                first_last.append(tuple(machine.mem_read(sp+512,2)))
            if address == pane.OWNER:
                outputs.append(machine.reg_read(UC_ARM_REG_R1))
        for at in (pane.OWNER,0x0807B984):
            cpu.hook_add(UC_HOOK_CODE,observe,begin=at,end=at)

        def row(race,index):
            table = int.from_bytes(self.rom[0x51BA84+4*race:0x51BA88+4*race],'little')-0x08000000
            return self.rom[table+index*8:table+(index+1)*8]

        # first/last and the output row to scan are independently known from the USA tables.
        for n,(mode,job,race,entity,override,source_row,first,last) in enumerate((
                (1,2,1,2,0,1,1,11),(2,2,1,3,0,1,12,22),(3,2,1,3,0,0,1,15),
                (1,2,1,3,1,0,1,15),(1,77,1,2,0,1,141,141),(0,2,1,2,0,0,0,0))):
            with self.subTest(mode=mode,job=job,override=override):
                record = bytearray(0x108)
                record[4:9] = bytes((1,job,race,job,entity))
                record[0x35] = override
                for i in range(first,last+1):
                    record[0x40+i] = 0 if i % 4 == 0 else 0x80+i%100
                cpu.mem_write(unit,bytes(record))
                cpu.mem_write(scene+0xBF9,bytes([mode]))
                cpu.mem_write(scene+0x1131,b'\x01')
                # Initialize only the used pane prefix; retain per-row and boundary canaries.
                initial = bytearray(b'\xA5'*(pane.HEADER+pane.POINTS*pane.ROW+4))
                cpu.mem_write(output-4,b'LEFT'+bytes(initial))
                index_writes.clear()
                start,stop,register = ((0x0807C89A,0x0807C8B4,UC_ARM_REG_R5) if n%2==0 else
                                       (0x0807D2EC,0x0807D306,UC_ARM_REG_R4))
                cpu.reg_write(register,pane.SCENE)
                cpu.reg_write(UC_ARM_REG_SP,0x03007F00)
                self.segment(cpu,start,stop)
                accepted = [i for i in range(first,last+1) if record[0x40+i] and row(source_row,i)[6]]
                self.assertEqual((first_last[-1],outputs[-1]),((first,last),mode))
                self.assertEqual((word(output),cpu.reg_read(UC_ARM_REG_R0)),(len(accepted),len(accepted)))
                self.assertEqual(index_writes,[(0x03007F00-32-0x20C+2*j,2,i) for j,i in enumerate(accepted)])
                expected=initial
                struct.pack_into('<II',expected,0,len(accepted),0x085567F0)
                expected[12:16]=bytes([0,0,20,13])
                struct.pack_into('<H',expected,16,0x1A7)
                expected[18]=0
                struct.pack_into('<HBBI',expected,20,0,16,0,output+pane.HEADER)
                struct.pack_into('<H',expected,pane.HEADER+12,0)
                for j,i in enumerate(accepted):
                    offset=pane.HEADER+j*pane.ROW
                    name,desc=struct.unpack_from('<HH',row(source_row,i))
                    struct.pack_into('<HH',expected,offset,j,0)
                    struct.pack_into('<IHBBB',expected,offset+8,name,desc,record[0x40+i],row(race,i)[7],row(race,i)[6])
                self.assertEqual(cpu.mem_read(output-4,len(expected)+4),b'LEFT'+bytes(expected))

        # This destructor frees the scene. Its global retains the expired address.
        released=[]
        cpu.hook_add(UC_HOOK_CODE,lambda m,a,w,c:released.append(m.reg_read(UC_ARM_REG_R1)),
                     begin=0x08007170,end=0x08007170)
        self.call(cpu,0x08071234,0)
        self.assertIn(scene,released)
