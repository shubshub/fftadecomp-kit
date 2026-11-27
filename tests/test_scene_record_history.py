"""Run the placed menu queue and verify its original calls, data, and ELF bindings."""
from collections import Counter
from itertools import combinations
import os
from pathlib import Path
import struct
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import finite_local_word_loop_profile as finite
import match
import standing_premise
import match_evidence
import owner_admission_profile as admission
import scene_record_history as scene


@unittest.skipUnless(os.environ.get('FFTA_SCENE_HISTORY_ROOT'), 'requires the USA ROM and reviewed sources')
class SceneHistory(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_SCENE_HISTORY_ROOT'])
        cls.result = admission.build(cls.root, scene.OWNER, selector=finite.SELECTOR)
        cls.data, cls.manifest, _, cls.mapping, cls.index, cls.objects, cls.rom, _, cls.elf = cls.result

    def test_original_elf_and_replayed_reports(self):
        expected = dict(calls=scene.CALLS, data=scene.DATA, functions=[], switches=[])
        self.assertEqual(self.manifest['bindings'], expected)
        self.assertEqual(self.data, self.rom[scene.OWNER-scene.BASE:scene.END-scene.BASE])
        image = match.elf_image(self.elf)

        def bindings(image):
            return admission.original_bindings(image, scene.OWNER, self.rom, self.mapping, self.objects,
                                              selector=finite.SELECTOR, index=self.index)

        actual, targets = bindings(image)
        self.assertEqual(actual, expected)
        self.assertEqual(targets, {'_call_via_r2': (0x0814224C, False),
                                   'func_08099CDC': (scene.QUERY, False),
                                   'func_08133BC4': (scene.PREDICATE, False),
                                   'g_callbacks_0836D4B8': (scene.boot.POINTER, True)})
        for name in targets:
            original = match.elf_image(self.elf)
            table, symbols = next(iter(original['symbol_tables'].items()))
            n = next(i for i, symbol in enumerate(symbols) if symbol['name'] == name)
            section = bytearray(original['section_data'][table])
            section[16*n+13] = 2
            original['section_data'][table] = bytes(section)
            with self.subTest(hidden=name), self.assertRaises(ValueError):
                bindings(original)
        for address in (scene.OWNER, scene.QUERY, 0x080C7554):
            report = (self.root/'docs/match'/f'{address:08X}.md').read_text()
            self.assertTrue(match_evidence.report_matches(report, self.root, address))
        report = (self.root/'docs/match/080C68EC.md').read_text()
        self.assertEqual(standing_premise.strip(report, self.root, scene.OWNER), admission.render(scene.OWNER, self.result))
        self.assertFalse(match_evidence.report_matches(
            report.replace('"list_bound_proved_from_ROM":false', '"list_bound_proved_from_ROM":true'),
            self.root, scene.OWNER))

    def test_original_menu_and_placed_queue(self):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_INTR, UC_HOOK_CODE
        from unicorn.arm_const import (UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R4,
                                       UC_ARM_REG_R6, UC_ARM_REG_R11, UC_ARM_REG_PC, UC_ARM_REG_LR,
                                       UC_ARM_REG_SP)

        machine = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        machine.mem_map(scene.BASE, len(self.rom))
        machine.mem_map(0x02000000, 0x40000)
        machine.mem_map(0x03000000, 0x8000)
        machine.mem_write(scene.BASE, self.rom)
        sp, stop = 0x03007DA0, 0x03007FF0
        bios_calls = []

        def cpuset(cpu, _, __):
            self.assertEqual(cpu.reg_read(UC_ARM_REG_PC), 0x0814186E)
            source, dest, control = (cpu.reg_read(r) for r in (UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2))
            bios_calls.append((source, dest, control))
            width = 4 if control & (1 << 26) else 2
            count = control & 0x1FFFFF
            fill = bool(control & (1 << 24))
            payload = bytes(cpu.mem_read(source, width if fill else width*count))
            cpu.mem_write(dest, payload*count if fill else payload)

        machine.hook_add(UC_HOOK_INTR, cpuset)
        machine.reg_write(UC_ARM_REG_SP, sp)
        machine.reg_write(UC_ARM_REG_LR, stop | 1)
        machine.emu_start(0x08002769, stop, count=1000)
        self.assertEqual(machine.reg_read(UC_ARM_REG_PC), stop)
        self.assertEqual([(dest, control) for _, dest, control in bios_calls], [
            (0x02000000, 0x0500FF00), (0x03000000, 0x01003E00), (scene.boot.DESTINATION, 88)])
        self.assertEqual(bios_calls[-1][0], scene.boot.IMAGE)
        self.assertEqual(machine.mem_read(scene.boot.DESTINATION, 176),
                         self.rom[scene.boot.IMAGE-scene.BASE:scene.boot.IMAGE-scene.BASE+176])

        # The original call site uses [r6] for the owner and r6+0xb8 for the menu state.
        parent = 0x02018000
        state = parent + 0xB8
        owner, queue, objects = 0x02010000, 0x02011000, 0x02012000
        secondary = 0x02002FC4
        machine.mem_write(parent, struct.pack('<I', owner))
        machine.mem_write(owner+16, struct.pack('<I', queue))
        saved = {r: 0x10101010 + r for r in range(UC_ARM_REG_R4, UC_ARM_REG_R11+1)}
        saved[UC_ARM_REG_R6] = parent

        entries, collector, visits, steps = [], [], [], Counter()
        def entered(cpu, pc, _, __):
            steps[pc] += 1
            if pc == scene.QUERY:
                self.assertEqual(cpu.reg_read(UC_ARM_REG_R0), owner)
                entries.append(cpu.reg_read(UC_ARM_REG_R1))
            elif pc == 0x0809AC20:
                collector.append(cpu.reg_read(UC_ARM_REG_R0))
            elif pc == scene.PREDICATE:
                visits.append(cpu.reg_read(UC_ARM_REG_R0))

        for pc in (0x080C7554, scene.OWNER, scene.boot.DESTINATION, scene.QUERY,
                   0x080C7CC0, 0x0809ABE8, 0x080C7B74, 0x0809AC20,
                   0x0814224C, 0x0814225C, scene.PREDICATE, scene.MEMBERSHIP):
            machine.hook_add(UC_HOOK_CODE, entered, begin=pc, end=pc)

        def run(records):
            n = len(records)
            nodes = [queue+32+16*((5*i) % 13) for i in range(n)]
            items = [objects+0x84*i for i in range(n)]
            machine.mem_write(queue+4, struct.pack('<I', nodes[0] if n else 0))
            for i, (node, item, record) in enumerate(zip(nodes, items, records)):
                machine.mem_write(node, struct.pack('<III', item, nodes[i-1] if i else 0,
                                                    nodes[i+1] if i+1 < n else 0))
                machine.mem_write(item, struct.pack('<I', record))
            placed = machine.mem_read(owner, objects + 13*0x84 - owner)
            machine.mem_write(state-4, bytes([0xCD])*204)
            machine.mem_write(sp-128, bytes([0xA5])*132)
            for r, val in saved.items():
                machine.reg_write(r, val)
            machine.reg_write(UC_ARM_REG_SP, sp)
            entries.clear()
            collector.clear()
            visits.clear()
            steps.clear()

            machine.emu_start(0x080BA5ED, 0x080BA5F6, count=14000)
            self.assertEqual(machine.reg_read(UC_ARM_REG_PC), 0x080BA5F6)
            self.assertEqual(machine.reg_read(UC_ARM_REG_SP), sp)
            self.assertEqual({r: machine.reg_read(r) for r in saved}, saved)
            self.assertEqual(machine.mem_read(sp, 4), bytes([0xA5])*4)
            self.assertEqual(entries, [sp-4-76])
            self.assertEqual(collector, items)
            self.assertEqual(machine.mem_read(entries[0], 52), struct.pack(f'<{n}I', *items)+bytes([0xA5])*(52-4*n))
            self.assertEqual(machine.mem_read(owner, len(placed)), placed)

            primary = {scene.SCENE+0x108*i for i in range(24)}
            selected = [r for r in records if r in primary][:2]
            examined = next((i+1 for i in range(n) if sum(r in primary for r in records[:i+1]) == 2), n)
            self.assertEqual(visits, records[:examined])
            self.assertEqual(steps, Counter({0x080C7554: 1, scene.OWNER: 1, scene.boot.DESTINATION: 1,
                scene.QUERY: 1, 0x080C7CC0: 1, 0x0809ABE8: n, 0x080C7B74: n, 0x0809AC20: n,
                0x0814224C: 1+n, 0x0814225C: n, scene.PREDICATE: examined, scene.MEMBERSHIP: examined}))
            expected = bytearray(196)
            struct.pack_into('<I', expected, 0x60, owner)
            struct.pack_into(f'<{len(selected)}I', expected, 0x64, *selected)
            expected[0x79] = len(selected)
            struct.pack_into('<6H', expected, 0x7C, 0, 4, 18, 5, 8, 2)
            self.assertEqual(machine.mem_read(state-4, 204), bytes([0xCD])*4 + expected + bytes([0xCD])*4)

        # Each possible pair of retained positions defines one observable path.
        for n in range(14):
            for kept in range(min(2, n)+1):
                for chosen in combinations(range(n), kept):
                    with self.subTest(n=n, selected=chosen):
                        run([scene.SCENE+0x108*((3*i+n) % 24) if i in chosen
                             else secondary+0x108*(i % 12) for i in range(n)])
        run([scene.SCENE + 23*0x108] * 13)
