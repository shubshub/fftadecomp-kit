"""Indexed scroll-wave loads, caller provenance and conditional field bounds."""
import copy
import os
from pathlib import Path
import struct
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match_evidence
import owner_admission_profile as owner
import scroll_wave_table_index as wave
import stack_index_precondition_profile as index


@unittest.skipUnless(os.environ.get('FFTA_SCROLL_WAVE_ROOT'), 'requires the scroll-wave ROM and source')
class ScrollWave(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_SCROLL_WAVE_ROOT']).resolve()
        cls.built = owner.build(cls.root, wave.OWNER, selector=index.SELECTOR)
        cls.raw, cls.manifest, _, cls.mapping, cls.index, _, cls.rom, _, _ = cls.built

    def test_owner_replay_and_bound(self):
        self.assertEqual(self.raw, self.rom[0xD8E00:0xD916E])
        proof = self.manifest['proof']['buffers']
        bounds = proof['stack_index_preconditions']['preconditions']
        self.assertEqual([(r['site'], r['bound']) for r in bounds],
                         [(pc, 8) for pc in (0x080D8ED2, 0x080D8EDC, 0x080D8EEE, *wave.READS)])
        self.assertEqual([r['site'] for r in bounds if 'one_based_iteration' in r['expression']], list(wave.READS))
        self.assertFalse(proof['scroll_wave_producers']['dynamic_layer_premise_proved'])
        report = (self.root/'docs/match/080D8E00.md').read_text()
        self.assertTrue(match_evidence.report_matches(report, self.root, wave.OWNER))
        stale = report.replace('"dynamic_layer_premise_proved":false', '"dynamic_layer_premise_proved":true')
        self.assertNotEqual(report, stale)
        self.assertFalse(match_evidence.report_matches(stale, self.root, wave.OWNER))
        with self.assertRaises(index.PremiseRefusal):
            index.accept({**proof['stack_index_preconditions'], 'accepted': None}, wave.OWNER, {})

    def test_original_elf_dependency_metadata(self):
        import match
        original = self.built[-1]
        image = match.elf_image(original)
        for name in ('func_0800D95C', 'data_08149AD4'):
            table, ordinal = next((table, i) for table, symbols in image['symbol_tables'].items()
                                  for i, symbol in enumerate(symbols) if symbol['name'] == name)
            start = image['sections'][table][4] + 16 * ordinal
            for field, wrong in ((8, 4), (12, 0x12 if name.startswith('func_') else 0x11), (13, 2)):
                with self.subTest(name=name, field=field):
                    changed = bytearray(original)
                    changed[start + field] = wrong
                    with self.assertRaises(ValueError):
                        owner.original_bindings(match.elf_image(bytes(changed)), wave.OWNER, self.rom,
                                                self.mapping, self.built[5], selector=index.SELECTOR, index=self.index)

    def test_changed_native_loop_and_side_entry(self):
        changed = bytearray(self.raw)
        changed[0xF4] = 2
        analysis = wave.ScrollWaveAnalysis(changed, wave.OWNER, (), (), {})
        with self.assertRaisesRegex(index.Refusal, 'parallel counters'):
            analysis.bind(analysis.syntactic_sites())
        changed = bytearray(self.raw)
        # The early default exit at +0x26 now jumps directly to a table read.
        offset = (wave.READS[0] - (wave.OWNER + 0x26 + 4)) // 2
        struct.pack_into('<H', changed, 0x26, 0xE000 | offset)
        analysis = wave.ScrollWaveAnalysis(changed, wave.OWNER, (), (), {})
        with self.assertRaisesRegex(index.Refusal, 'edge enters'):
            analysis.bind(analysis.syntactic_sites())

    def test_rejects_changed_caller_map_and_table(self):
        bindings = self.manifest['bindings']
        for address in (0x080E8E14, 0x080EA442, 0x0801E612, 0x0801D396, 0x08149AF4, 0x080D97D0):
            with self.subTest(address=address):
                changed = bytearray(self.rom)
                changed[address - 0x08000000] ^= 1
                with self.assertRaises(ValueError):
                    wave.producers(bytes(changed), self.mapping, self.index, bindings)
        changed = copy.deepcopy(bindings)
        changed['data'][1][1] = 'data_08149AD4'
        with self.assertRaisesRegex(ValueError, 'bindings'):
            wave.producers(self.rom, self.mapping, self.index, changed)

    def test_native_four_channel_index_and_live_map_premise(self):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_CODE
        from unicorn.arm_const import (UC_ARM_REG_PC, UC_ARM_REG_SP, UC_ARM_REG_LR, UC_ARM_REG_R0,
                                      UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R4)
        base, stack, cmd, state = 0x08000000, 0x03007C00, 0x02001000, 0x02002000
        cpu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        cpu.mem_map(base, len(self.rom))
        cpu.mem_write(base, self.rom)
        cpu.mem_map(0x03000000, 0x8000)
        cpu.mem_map(0x02000000, 0x10000)
        rows = []

        def watch(machine, pc, size, user):
            if pc in wave.READS:
                address = machine.reg_read(UC_ARM_REG_R4)
                rows.append((pc, (address - (stack - 88)) // 4))
                if rows[-1][1] >= 8:
                    machine.emu_stop()
            else:
                machine.reg_write(UC_ARM_REG_R0, 0x02003000)
                machine.reg_write(UC_ARM_REG_PC, machine.reg_read(UC_ARM_REG_LR))
        for pc in (*wave.READS, 0x0800CE08, 0x0800D95C):
            cpu.hook_add(UC_HOOK_CODE, watch, begin=pc, end=pc)
        # Follow the real layer producer and the native min branch up to registration.
        for first, second in ((1, 0), (2, 3), (3, 2), (3, 3)):
            cpu.mem_write(0x02007F40, bytes([first, second]))
            cpu.mem_write(cmd, struct.pack('<H', 0x100))
            cpu.mem_write(state, b'\x01\x00' + b'\x00' * 0x16A)
            cpu.reg_write(UC_ARM_REG_SP, stack)
            cpu.reg_write(UC_ARM_REG_R1, cmd)
            cpu.reg_write(UC_ARM_REG_R2, state)
            cpu.reg_write(UC_ARM_REG_LR, base | 1)
            cpu.emu_start(0x080EA3E9, wave.SPAWNER)
            bg = cpu.reg_read(UC_ARM_REG_R1)
            self.assertEqual((cpu.reg_read(UC_ARM_REG_R0), bg, cpu.reg_read(UC_ARM_REG_R2)),
                             (2, min(first, second), 0))
            rows.clear()
            cpu.mem_write(state, bytes(0x16C))
            cpu.mem_write(state + 8, bytes([2, bg, 0, 4]))
            cpu.mem_write(cmd, struct.pack('<H', 0x100))
            cpu.reg_write(UC_ARM_REG_SP, stack)
            cpu.reg_write(UC_ARM_REG_R1, cmd)
            cpu.reg_write(UC_ARM_REG_R2, state)
            cpu.reg_write(UC_ARM_REG_LR, base | 1)
            cpu.emu_start(wave.OWNER | 1, base, count=2000)
            if bg == 3:
                self.assertEqual(rows[-1], (wave.READS[0], 8))
            else:
                expected = [(pc, bg*2+i) for i in range(1, 4) for pc in wave.READS]
                self.assertEqual(rows, expected)
                self.assertEqual(cpu.reg_read(UC_ARM_REG_PC), base)
