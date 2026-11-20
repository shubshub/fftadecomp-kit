"""Native callback dispatch, ROM table copy and the recorded menu-choice premise."""
import os
import json
from pathlib import Path
import struct
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import match_evidence
import menu_mode_dispatcher as menu
import owner_admission_profile as owner
import rom_table_copy_profile as rom_copy
import stack_index_precondition_profile as index


@unittest.skipUnless(os.environ.get('FFTA_MENU_MODE_ROOT'), 'requires the indexed game, ROM and 0807DDB8 source')
class MenuModes(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_MENU_MODE_ROOT']).resolve()
        cls.built = owner.build(cls.root, menu.OWNER, selector=index.SELECTOR)
        cls.raw, cls.manifest, _, cls.mapping, cls.index, cls.objects, cls.rom, _, cls.elf = cls.built

    def test_full_report_and_runtime_premise(self):
        self.assertEqual(self.raw, self.rom[menu.OWNER-menu.BASE:menu.END-menu.BASE])
        proof = self.manifest['proof']
        self.assertEqual(proof['instructions'], 434)
        self.assertEqual((proof['partition']['code_bytes'],proof['partition']['literal_and_table_bytes'],
                          proof['partition']['alignment_bytes']),(930,356,6))
        bound = proof['buffers']['stack_index_preconditions']
        row, = bound['preconditions']
        self.assertEqual((row['site'],row['bound'],row['array_entry_sp'],row['premise_proved']),
                         (menu.CHOICE,4,[-24,-20],False))
        for entry in ({},{menu.OWNER:{**bound['accepted'],'rows':[]}}):
            with self.assertRaises(index.PremiseRefusal):
                index.accept(bound, menu.OWNER, entry)
        report = (self.root/'docs/match/0807DDB8.md').read_text()
        self.assertTrue(match_evidence.report_matches(report,self.root,menu.OWNER))
        changed = report.replace('"premise_proved":false','"premise_proved":true')
        self.assertNotEqual(report,changed)
        self.assertFalse(match_evidence.report_matches(changed,self.root,menu.OWNER))

    def test_original_object_roles_and_initializer(self):
        image = match.elf_image(self.elf)
        rodata, initializer, _ = rom_copy.rodata_section(image)
        self.assertEqual(initializer,menu.MODE_BYTES)
        for section, symbol in ((rodata,None),(image['text_index'],None),(0,'func_0807C7E8'),(0,'data_0200F239'),(0,'memcpy')):
            t, n = next((t,n) for t, rows in image['symbol_tables'].items() for n,s in enumerate(rows)
                        if s['section'] == section and (s['name'] == symbol if symbol else s['type'] == 3))
            for delta in (8,13):
                changed = bytearray(self.elf)
                changed[image['sections'][t][4]+16*n+delta] ^= 1
                with self.subTest(section=section,symbol=symbol,delta=delta), self.assertRaises(ValueError):
                    owner.original_bindings(match.elf_image(bytes(changed)),menu.OWNER,self.rom,self.mapping,
                                            self.objects,selector=index.SELECTOR,index=self.index)
        changed = bytearray(self.elf)
        changed[image['sections'][rodata][4]+3] ^= 1
        with self.assertRaises(ValueError):
            rom_copy.rodata_binding(match.elf_image(bytes(changed)),menu.OWNER,self.rom)

    def test_original_caller_and_menu_writers(self):
        for pc in (0x080792DA,0x080069F4,0x080704B8,0x08070588,0x08006AF8,
                   0x08076F6E,0x080765FA,0x08076FCA,0x08077068,0x08085324,0x08085356,0x0807DF70):
            changed = bytearray(self.rom)
            changed[pc-menu.BASE] ^= 1
            with self.subTest(pc=pc), self.assertRaises(ValueError):
                menu.original_callers(changed,self.mapping,self.index)

    def test_halfword_span_is_not_an_instruction_count(self):
        # These two stale rows previously agreed on 1292 / 2, counting every
        # literal, switch slot, padding halfword and second half of each BL.
        entries = json.loads(self.mapping)
        next(row for row in entries if row['rom'] == f'0x{menu.OWNER:08X}')['instrs'] = 646
        old_index = self.index.replace(b'0807DDB8 0807E2C4  1292 434',b'0807DDB8 0807E2C4  1292 646')
        self.assertNotEqual(old_index,self.index)
        rodata = rom_copy.rodata_binding(match.elf_image(self.elf),menu.OWNER,self.rom)
        with self.assertRaisesRegex(ValueError,'indexed counts'):
            owner.verify(self.raw,menu.OWNER,self.rom,json.dumps(entries).encode(),old_index,self.objects,
                         bindings=self.manifest['bindings'],selector=index.SELECTOR,rodata=rodata,
                         premises=(self.root/'config/stack_index_premises.json').read_bytes())

    def test_native_states_and_four_live_choices(self):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_CODE
        from unicorn.arm_const import (UC_ARM_REG_PC, UC_ARM_REG_LR, UC_ARM_REG_SP, UC_ARM_REG_R0,
                                       UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3, UC_ARM_REG_R4)
        mem, record, context = 0x02004000,0x02009800,0x02009A00
        flag, sp, end = 0x03000EC3,0x03007500,menu.BASE
        callee_saved = tuple(range(UC_ARM_REG_R4,UC_ARM_REG_R4+8))
        seeds = [0x170000+i for i in range(8)]
        targets = {int(name[5:],16) for _,name in self.manifest['bindings']['calls'] if name != 'memcpy'}
        cpu = Uc(UC_ARCH_ARM,UC_MODE_THUMB)
        cpu.mem_map(menu.BASE,len(self.rom))
        cpu.mem_write(menu.BASE,self.rom)
        cpu.mem_map(0x02000000,0x40000)
        cpu.mem_map(0x03000000,0x8000)
        def word(addr,value):
            cpu.mem_write(addr,struct.pack('<I',value))
        word(0x03002818,mem)
        word(0x03002738,0x03000910)
        word(0x0300273C,0x03000EC0)
        word(mem+0x1D0C,record)
        word(mem+0x2D50,context)
        cpu.mem_write(record+6,bytes([12]))
        events = []
        def ordinary(machine,pc,size,user):
            regs = tuple(machine.reg_read(r) for r in (UC_ARM_REG_R0,UC_ARM_REG_R1,UC_ARM_REG_R2,UC_ARM_REG_R3))
            events.append((pc,regs))
            # Keep the original registration writer and compiler memcpy executable.
            if pc == 0x08006AF8:
                return
            result = {0x0807D96C:0xCAFE1234,0x0808B8E4:0x0200B000}.get(pc,0)
            machine.reg_write(UC_ARM_REG_R0,result)
            machine.reg_write(UC_ARM_REG_PC,machine.reg_read(UC_ARM_REG_LR))
        for pc in targets:
            cpu.hook_add(UC_HOOK_CODE,ordinary,begin=pc,end=pc)
        def run(state):
            events.clear()
            cpu.mem_write(sp-24,bytes(4))
            cpu.mem_write(flag,bytes([state]))
            cpu.reg_write(UC_ARM_REG_R0,3)
            cpu.reg_write(UC_ARM_REG_R1,flag)
            cpu.reg_write(UC_ARM_REG_SP,sp)
            cpu.reg_write(UC_ARM_REG_LR,end|1)
            for reg,value in zip(callee_saved,seeds):
                cpu.reg_write(reg,value)
            cpu.emu_start(menu.OWNER|1,end,count=1800)
            self.assertEqual(cpu.reg_read(UC_ARM_REG_PC),end)
            self.assertEqual(cpu.reg_read(UC_ARM_REG_SP),sp)
            self.assertEqual([cpu.reg_read(r) for r in callee_saved],seeds)
            self.assertEqual(cpu.mem_read(sp-24,4),menu.MODE_BYTES)
            return cpu.mem_read(flag,1)[0]
        for choice,mode in enumerate(menu.MODE_BYTES):
            # Run the native menu store which produces this choice.
            pc = (0x08076F64,0x080765F0,0x08076FC0,0x0807705E)[choice]
            cpu.emu_start(pc|1,pc+12,count=6)
            self.assertEqual(cpu.mem_read(mem+0x561,1),bytes([choice]))
            self.assertEqual(run(0),9)
            self.assertEqual(cpu.mem_read(mem+0xC1F,1),bytes([choice]))
            self.assertEqual([r[:3] for pc,r in events if pc == 0x0807D96C],[(mode,12,context)])
            self.assertEqual([r for pc,r in events if pc == 0x0808B8E4],[(5,1,0,y) for y in range(2,12,2)])
            self.assertEqual(cpu.mem_read(0x0200F237,3),bytes([7,3,0x34]))
        for mode,destination in ((1,0x0807C7E9),(5,0x0807D241)):
            cpu.mem_write(mem+0x1131,bytes([mode]))
            self.assertEqual(run(8),16)
            self.assertEqual(cpu.mem_read(0x03000910+7*4,4),struct.pack('<I',destination))
            self.assertEqual(cpu.mem_read(0x03000EC7,1),bytes([2]))
        for state in (1,2,3,5,6,12,13,14,15,18,19,255):
            self.assertEqual(run(state),state)
            self.assertEqual(events,[])
        self.assertEqual(run(4),7)
        self.assertEqual(run(7),7)
        self.assertEqual(run(9),7)
        self.assertEqual(run(10),7)
        self.assertEqual(run(11),11)
        self.assertEqual(run(16),16)
        self.assertEqual(run(17),18)
        # Dispatch an original state-17 callback through the real scheduler.
        cpu.reg_write(UC_ARM_REG_SP,sp)
        cpu.emu_start(0x080704AF,0x080704BC,count=400)
        cpu.emu_start(0x080792D5,0x080792DE,count=100)
        self.assertEqual(cpu.mem_read(0x0300091C,4),struct.pack('<I',menu.OWNER|1))
        self.assertEqual(cpu.mem_read(flag,1),bytes([0]))
        cpu.mem_write(flag,bytes([17]))
        received = []
        def callback(machine,pc,size,user):
            received.append((machine.reg_read(UC_ARM_REG_R0),machine.reg_read(UC_ARM_REG_R1)))
        cpu.hook_add(UC_HOOK_CODE,callback,begin=menu.OWNER,end=menu.OWNER)
        cpu.emu_start(0x08070585,0x0807058C,count=1000)
        self.assertEqual(received,[(3,flag)])
        self.assertEqual(cpu.mem_read(flag,1),bytes([18]))
        self.assertEqual(cpu.reg_read(UC_ARM_REG_SP),sp)
