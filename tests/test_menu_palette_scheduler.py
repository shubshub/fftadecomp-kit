"""Real ROM constructor, installed copy, scheduler phase zero and original ELF."""
import copy
import os
from pathlib import Path
import struct
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

TOOLS = Path(__file__).resolve().parents[1] / 'tools'
sys.path.insert(0, str(TOOLS))
import match
import match_evidence
import menu_palette_scheduler as menu
import owner_admission_profile as owner
import owner_graph_profile as graph
from conditional_local_buffer_profile import ConditionalLocalBufferProof


@unittest.skipUnless(os.environ.get('FFTA_MENU_PALETTE_ROOT'), 'needs the indexed ROM and recovered C')
class MenuPaletteScheduler(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        root = Path(os.environ['FFTA_MENU_PALETTE_ROOT']).resolve()
        temp = tempfile.TemporaryDirectory()
        cls.addClassCleanup(temp.cleanup)
        cls.game = Path(temp.name)
        for name in ('include', 'config', 'symbols', 'baserom.bin'):
            (cls.game/name).symlink_to(root/name)
        (cls.game/'src').mkdir()
        cls.source = cls.game/'src/080253B0.c'
        cls.source.write_bytes((root/'src/080253B0.c').read_bytes())
        cls.rom = (root/'baserom.bin').read_bytes()
        cls.mapping = match_evidence.mapping_snapshot(root)
        cls.index = owner.index_snapshot(root)
        cls.objects = match_evidence.data_snapshot(root)
        check_linked = menu.check_linked
        def capture(image, targets):
            check_linked(image, targets)
            cls.linked, cls.targets = image, targets
        with patch.object(menu, 'check_linked', side_effect=capture):
            cls.data, cls.manifest, *_, raw = owner.build(cls.game, menu.OWNER, selector=menu.SELECTOR)
        cls.original = match.elf_image(raw)
        cls.ins, cls.edges, _, cls.calls, _ = graph.graph(
            cls.data, menu.OWNER, owner.refine(cls.data, menu.OWNER, cls.mapping))

    def test_selectors_and_saved_replay(self):
        def issue(*args):
            return subprocess.run([sys.executable, str(TOOLS/'match.py'), '--root', str(self.game),
                                   '080253B0', *args], capture_output=True, text=True)
        self.assertNotEqual(issue().returncode, 0)
        for selector in ('conditional-scheduler-call-site-summaries-v1',
                         'conditional-scheduler-call-site-summaries-v2', 'conditional-scheduler-zero-descriptor-v1'):
            with self.subTest(selector=selector):
                self.assertNotEqual(issue('--owner-runtime-profile', selector).returncode, 0)
        result = issue('--owner-runtime-profile', menu.SELECTOR)
        self.assertEqual(result.returncode, 0, result.stderr)
        report = (self.game/'docs/match/080253B0.md').read_text()
        replay = lambda value: match_evidence.report_matches(value, str(self.game), menu.OWNER)
        self.assertTrue(replay(report))
        self.assertIn('124/124 bytes', report)
        for field in ('"caller_initialized":[]', '"copied_descriptor_reads":[[0,2],[20,2]]',
                      '"installed_identity_proved":false', '"palette_bytes":["f526","0f26"]'):
            self.assertIn(field, report)
            self.assertFalse(replay(report.replace(field, '"unverified":true')))
        src = self.source.read_text()
        try:
            self.source.write_text(src.replace('descriptor.argument = mode - 1;', 'descriptor.argument = mode + 1;'))
            self.assertFalse(replay(report))
            self.assertNotEqual(issue('--owner-runtime-profile', menu.SELECTOR).returncode, 0)
        finally:
            self.source.write_text(src)

    def test_owner_image_install_copy_and_phase_mutations(self):
        for pc in (menu.OWNER+0x16, menu.OWNER+0x1E, menu.OWNER+0x22, menu.OWNER+0x30, menu.OWNER+0x38,
                   menu.OWNER+0x44, menu.OWNER+0x50, menu.OWNER+0x52, menu.OWNER+0x74, menu.OWNER+0x78,
                   0x08002796, menu.POINTER, 0x08A38A9C, 0x0841A0F8, 0x0841ABF8,
                   0x0801D882, menu.GETTER+0x18, 0x080059F2, 0x08005A02, 0x08005A08, menu.THUNK,
                   0x08029028, 0x08028E58, 0x08005BF8):
            rom = bytearray(self.rom)
            rom[pc-match.ROM_BASE] ^= 1
            proof = ConditionalLocalBufferProof(bytes(rom), self.mapping, self.index, self.objects,
                                               policy=menu.SELECTOR)
            with self.subTest(pc=hex(pc)), self.assertRaises(ValueError):
                menu.bind(proof, self.data, menu.OWNER, self.ins, self.edges, self.calls)
        edges = dict(self.edges)
        edges[menu.OWNER+0x18] = (menu.OWNER+0x3A, menu.OWNER+0x1A)
        proof = ConditionalLocalBufferProof(self.rom, self.mapping, self.index, self.objects, policy=menu.SELECTOR)
        with self.assertRaises(ValueError):
            menu.bind(proof, self.data, menu.OWNER, self.ins, edges, self.calls)
        with self.assertRaises(ValueError):
            menu.bind(proof, self.data, menu.OWNER+2, self.ins, self.edges, self.calls)

    def test_original_object_roles_and_rel_addends(self):
        def bind(image):
            return owner.original_bindings(image, menu.OWNER, self.rom, self.mapping, self.objects,
                                           selector=menu.SELECTOR, index=self.index)
        self.assertEqual(bind(self.original)[0], menu.BINDINGS)
        for mutation in ('rel-type', 'callback-name', 'literal-addend', 'call-addend', 'visibility', 'size'):
            image = copy.deepcopy(self.original)
            section, = image['relocations']
            table = image['sections'][section][6]
            symbols = image['symbol_tables'][table]
            if mutation in ('rel-type', 'callback-name'):
                raw = bytearray(image['section_data'][section])
                for at in range(0, len(raw), 8):
                    site, info = struct.unpack_from('<II', raw, at)
                    if site == 0x30:
                        idx = next(i for i, r in enumerate(symbols) if r['name'] == 'func_08028DE0')
                        struct.pack_into('<I', raw, at+4, idx << 8 | 2 if mutation == 'callback-name'
                                         else (info & ~255) | 10)
                image['section_data'][section] = bytes(raw)
            elif mutation in ('literal-addend', 'call-addend'):
                raw = bytearray(image['text'])
                raw[0x70 if mutation == 'literal-addend' else 0x52] ^= 1
                image['text'] = bytes(raw)
            else:
                n = next(i for i, r in enumerate(symbols) if r['name'] == 'data_0836D4BC')
                if mutation == 'visibility':
                    raw = bytearray(image['section_data'][table])
                    raw[n*16+13] = 2
                    image['section_data'][table] = bytes(raw)
                else:
                    symbols[n]['size'] = 4
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                bind(image)

    def test_actual_linked_object_symbol_classes(self):
        for field, value in (('type', 2), ('section', 1), ('value', menu.DEST+2), ('size', 1), ('visibility', 2)):
            image = copy.deepcopy(self.linked)
            table, symbols = next((t, rows) for t, rows in image['symbol_tables'].items()
                                  if any(row['name'] == 'data_030039F8' for row in rows))
            n = next(i for i, row in enumerate(symbols) if row['name'] == 'data_030039F8')
            if field == 'visibility':
                raw = bytearray(image['section_data'][table])
                raw[n*16+13] = value
                image['section_data'][table] = bytes(raw)
            else:
                symbols[n][field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                owner.small_copy_binding.check_linked(image, menu.OWNER, self.targets)
                menu.check_linked(image, self.targets)

    def test_native_installed_copy_and_synchronous_callbacks(self):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_CODE, UC_HOOK_MEM_READ, UC_HOOK_MEM_WRITE, UC_MEM_READ, UC_MEM_WRITE
        from unicorn.arm_const import UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3, UC_ARM_REG_SP, UC_ARM_REG_LR, UC_ARM_REG_PC

        for mode, selector, poison, with_parent in ((17, 0, 0xA5, False), (17, 2, 0x5A, True),
                (0, 0, 0x5A, True), (1, 2, 0xA5, False), (255, 1, 0x77, False), (16, 3, 0xBB, True)):
            with self.subTest(mode=mode, selector=selector, parent=with_parent):
                uc = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
                uc.mem_map(match.ROM_BASE, len(self.rom))
                uc.mem_write(match.ROM_BASE, self.rom)
                uc.mem_map(0x02000000, 0x40000)
                uc.mem_map(0x03000000, 0x8000)
                uc.mem_write(0x03005E78, self.rom[0xA38A2C:0xA38ADC])
                stack, stop = 0x03007000, 0x03007C00
                state = 0x02020000
                word = lambda point: struct.unpack('<I', uc.mem_read(point, 4))[0]
                def call(point, r0, r1):
                    uc.reg_write(UC_ARM_REG_SP, stack)
                    uc.reg_write(UC_ARM_REG_LR, stop | 1)
                    uc.reg_write(UC_ARM_REG_R0, r0)
                    uc.reg_write(UC_ARM_REG_R1, r1)
                    uc.emu_start(point | 1, stop, count=20000)
                    self.assertEqual(uc.reg_read(UC_ARM_REG_PC), stop)
                    self.assertEqual(uc.reg_read(UC_ARM_REG_SP), stack)
                    return uc.reg_read(UC_ARM_REG_R0)
                manager = call(0x08005C14, 0x02010000, 0x4000)
                self.assertTrue(0x02010000 <= manager < 0x02014000)
                uc.mem_write(0x0200F438, struct.pack('<I', state))
                uc.mem_write(state+32, struct.pack('<I', manager))
                seen, desc_reads, transfers = {}, [], []
                def code(emu, pc, size, _):
                    if pc == menu.SCHEDULER:
                        src = emu.reg_read(UC_ARM_REG_R3)
                        seen.update(original_desc=bytes(emu.mem_read(src, 28)), scheduler_parent=word(stack-52))
                        self.assertEqual(src, stack-48)
                        self.assertEqual(emu.reg_read(UC_ARM_REG_R2), 164)
                    if pc in (menu.SPECIAL, menu.NORMAL):
                        desc = emu.reg_read(UC_ARM_REG_R1)
                        seen.update(callback=pc, task=emu.reg_read(UC_ARM_REG_R0),
                                    payload=emu.reg_read(UC_ARM_REG_R2), desc=desc,
                                    copied=bytes(emu.mem_read(desc, 28)))
                    if pc == 0x03005EE8:
                        seen['copy'] = [emu.reg_read(reg) for reg in (UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2)]
                def memory(emu, access, addr, size, value, _):
                    pc = emu.reg_read(UC_ARM_REG_PC)
                    if (menu.NORMAL <= pc < 0x08029188 and 'desc' in seen
                        and seen['desc'] <= addr < seen['desc']+28):
                        desc_reads.append((addr-seen['desc'], size, access))
                    if 0x03005EE8 <= pc < 0x03005F26 and (addr < stack-0x1000 or addr >= match.ROM_BASE):
                        transfers.append((access, addr, size))
                uc.hook_add(UC_HOOK_CODE, code)
                uc.hook_add(UC_HOOK_MEM_READ | UC_HOOK_MEM_WRITE, memory)
                parent = 0
                if with_parent:
                    call(menu.OWNER, 17, 0)
                    parent = seen['task']
                seen.clear()
                desc_reads.clear()
                transfers.clear()
                uc.mem_write(state+0x480, bytes(6))
                uc.mem_write(0x02002FC2, bytes([selector]))
                uc.mem_write(0x02008168, bytes([selector & 1]))
                uc.mem_write(stack-0x300, bytes([poison])*0x300)
                uc.mem_write(menu.DEST-1, bytes([0xCC])*4)
                call(menu.OWNER, mode, parent)
                self.assertEqual(seen['scheduler_parent'], parent)
                expected = bytearray([poison])*28
                if mode != 17:
                    struct.pack_into('<H', expected, 20, (mode-1)&65535)
                self.assertEqual(seen['original_desc'], expected)
                expected[:2] = b'\0\0'
                self.assertEqual(seen['copied'], expected)
                task = seen['task']
                self.assertEqual(seen['payload'], task+24)
                self.assertEqual(word(task+12), parent)
                self.assertEqual(uc.mem_read(state, 2), b'\0\0')
                self.assertEqual(uc.mem_read(state+4, 1), bytes([mode]))
                if mode == 17:
                    self.assertEqual(seen['callback'], menu.SPECIAL)
                    self.assertNotIn('copy', seen)
                    self.assertEqual(desc_reads, [(0, 2, UC_MEM_READ)])
                    self.assertEqual(uc.mem_read(state+0x480, 6), bytes(range(1, 7)))
                    self.assertEqual(uc.mem_read(menu.DEST-1, 4), b'\xCC'*4)
                else:
                    source = menu.PALETTES[selector == 2]+12*32+24
                    self.assertEqual(seen['callback'], menu.NORMAL)
                    self.assertEqual(desc_reads, [(0, 2, UC_MEM_READ), (20, 2, UC_MEM_READ)])
                    self.assertEqual(seen['copy'], [menu.DEST, source, 2])
                    self.assertEqual(transfers, [(UC_MEM_READ, source, 1), (UC_MEM_WRITE, menu.DEST, 1),
                                                 (UC_MEM_READ, source+1, 1), (UC_MEM_WRITE, menu.DEST+1, 1)])
                    self.assertEqual(uc.mem_read(menu.DEST-1, 4), b'\xCC'+bytes(uc.mem_read(source, 2))+b'\xCC')
                    self.assertEqual(word(task+24), task)
                    self.assertEqual(word(task+28), parent)
                    self.assertEqual(uc.mem_read(task+32, 1), bytes([(mode-1)&255]))
