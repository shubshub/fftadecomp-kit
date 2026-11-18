"""Finite original history-list construction, including every twelve-record filter."""
import copy
import os
from pathlib import Path
import struct
import sys
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import history_unit_list as builder


class NativeBuilder(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import match
        from inert_spin_profile import index_snapshot
        from rompath import rom_path
        root = os.environ.get('FFTA_HISTORY_BUILDER_FIXTURE')
        if not root:
            raise unittest.SkipTest('requires FFTA_HISTORY_BUILDER_FIXTURE with USA ROM and reviewed source')
        cls.root = Path(root)
        cls.rom = Path(rom_path(root)).read_bytes()
        cls.mapping,cls.index = match.mapping_snapshot(root),index_snapshot(root)
        cls.objects = match.data_snapshot(root)
        cls.bindings = dict(calls=builder.CALLS,data=builder.DATA,functions=[],switches=[])

    def prove(self, rom, bindings, mapping=None, index=None, objects=None):
        import owner_admission_profile as admission
        import finite_local_word_loop_profile as finite
        base = builder.history.BASE
        data = rom[builder.OWNER-base:builder.END-base]
        return admission.verify(data,builder.OWNER,rom,self.mapping if mapping is None else mapping,
            self.index if index is None else index,self.objects if objects is None else objects,
            selector=finite.SELECTOR,bindings=bindings)

    def test_exact_input_provenance_and_counterexamples(self):
        import json
        self.prove(self.rom,self.bindings)
        for pc in (0x080C687C,0x080C6882,0x080C68A0,0x080C68C0,0x080C68D2,0x080C62EE,0x080C62F4,
                   0x080C62F6,0x080C63E6,0x08124CC2,0x08125742,0x0836D4B8,0x08007164,0x080C68E4):
            changed = bytearray(self.rom)
            changed[pc-builder.history.BASE] ^= 1
            with self.subTest(pc=pc),self.assertRaises(ValueError):
                self.prove(bytes(changed),self.bindings)
        changes = [('calls',0,1,'_call_via_r3'),('calls',1,0,102),('data',0,0,54),('data',1,2,4)]
        for field,row,col,value in changes:
            changed = copy.deepcopy(self.bindings)
            changed[field][row][col] = value
            with self.assertRaises(ValueError):
                self.prove(self.rom,changed)
        rows = json.loads(self.mapping)
        next(row for row in rows if int(row['rom'],16)==builder.OWNER)['instrs'] += 1
        with self.assertRaises(ValueError):
            self.prove(self.rom,self.bindings,mapping=json.dumps(rows).encode())
        for count,mask in ((13,0),(-1,0),(1,2)):
            with self.assertRaises(ValueError):
                builder.selection(count,mask)

    def test_original_all_4096_active_masks_and_saved_frame(self):
        from unicorn import Uc,UC_ARCH_ARM,UC_MODE_THUMB
        from unicorn.arm_const import (UC_ARM_REG_R0,UC_ARM_REG_R1,UC_ARM_REG_R5,UC_ARM_REG_SP,
                                      UC_ARM_REG_LR,UC_ARM_REG_PC)
        machine = Uc(UC_ARCH_ARM,UC_MODE_THUMB)
        machine.mem_map(builder.history.BASE,(len(self.rom)+4095)&~4095)
        machine.mem_write(builder.history.BASE,self.rom)
        machine.mem_map(0x02000000,0x40000)
        machine.mem_map(0x03000000,0x8000)
        machine.mem_write(builder.FLAG,b'\x08')
        sp = 0x03007DA0
        for mask in range(1<<12):
            for i in range(12):
                machine.mem_write(builder.UNITS+i*0x108+4,bytes((0xA5 if mask&(1<<i) else 0,)))
            machine.mem_write(sp-68,bytes([0xCD])*72)
            machine.reg_write(UC_ARM_REG_R0,builder.UNITS)
            machine.reg_write(UC_ARM_REG_R1,12)
            machine.reg_write(UC_ARM_REG_SP,sp)
            machine.reg_write(UC_ARM_REG_LR,0x03007FF1)
            machine.emu_start(builder.OWNER|1,0x080C68BE,count=128)
            self.assertEqual(machine.reg_read(UC_ARM_REG_PC),0x080C68BE)
            cursor = machine.reg_read(UC_ARM_REG_SP)
            self.assertEqual(cursor,sp-64)
            selected = builder.selection(12,mask)
            self.assertEqual(machine.reg_read(UC_ARM_REG_R5),len(selected))
            words = b''.join(struct.pack('<I',address) for offset,address in selected)
            self.assertEqual(machine.mem_read(cursor,48),words+bytes([0xCD])*(48-len(words)))
            self.assertEqual(machine.mem_read(cursor-4,4),bytes([0xCD])*4)
            self.assertEqual(machine.mem_read(sp-4,4),struct.pack('<I',0x03007FF1))
            self.assertEqual(machine.mem_read(sp,4),bytes([0xCD])*4)

    def test_native_receipts_and_malformed_original_evidence(self):
        from match_evidence import report_matches
        for address in (builder.OWNER,0x08124BB4,0x081256D4):
            report = (self.root/'docs/match'/f'{address:08X}.md').read_text()
            self.assertTrue(report_matches(report,self.root,address))
        report = (self.root/'docs/match/080C6858.md').read_text()
        for key in ('* ROM bytes:','* compiled :','* owner runtime evidence:'):
            line = next(line for line in report.splitlines() if line.startswith(key))
            for value in (line[:-2],line+'\n'+line):
                with self.subTest(key=key):
                    self.assertFalse(report_matches(report.replace(line,value),self.root,builder.OWNER))
