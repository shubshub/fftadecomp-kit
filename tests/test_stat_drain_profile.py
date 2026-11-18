"""ROM-backed arithmetic, original ELF role checks, and fresh report replay."""
import copy
import json
import os
from pathlib import Path
import struct
import subprocess
import sys
import tempfile
import unittest

TOOLS = Path(__file__).resolve().parents[1] / 'tools'
sys.path.insert(0, str(TOOLS))
import match
import match_evidence
import owner_admission_profile as owner
import signed_divmod_profile as driver
import stat_drain_profile as drain


@unittest.skipUnless(os.environ.get('FFTA_STAT_DRAIN_ROOT'), 'set FFTA_STAT_DRAIN_ROOT to the recovered USA game')
class StatDrainTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        game = Path(os.environ['FFTA_STAT_DRAIN_ROOT']).resolve()
        work = tempfile.TemporaryDirectory()
        cls.addClassCleanup(work.cleanup)
        cls.game = Path(work.name)
        for path in ('config', 'include', 'symbols', 'baserom.bin'):
            (cls.game/path).symlink_to(game/path)
        (cls.game/'src').mkdir()
        cls.src = cls.game/'src/08128C3C.c'
        cls.src.write_bytes((game/'src/08128C3C.c').read_bytes())
        cls.rom = (cls.game/'baserom.bin').read_bytes()
        cls.mapping = match_evidence.mapping_snapshot(cls.game)
        cls.objects = match_evidence.data_snapshot(cls.game)
        cls.index = owner.index_snapshot(cls.game)
        cls.result = driver.build(cls.game, drain.ADDRESS, selector=drain.SELECTOR)
        cls.bindings = cls.result['manifest']['bindings']

    def test_native_cli_fresh_replay_and_manual_runtime_rejection(self):
        cmd = [sys.executable, str(TOOLS/'match.py'), '--root', str(self.game), '08128C3C']
        def run(*extra):
            return subprocess.run([*cmd, *extra], capture_output=True, text=True)
        self.assertNotEqual(run().returncode, 0)
        args = ('--signed-runtime-profile', drain.SELECTOR)
        for extra in (('--control-flow-profile', 'mixed-return-inert-spin-v1'),
                      ('--owner-runtime-profile', 'numeric-data-switch-source-v1')):
            refused = run(*args, *extra)
            self.assertNotEqual(refused.returncode, 0)
            self.assertIn('isolated ordinary Thumb selector', refused.stderr)
        good = run(*args)
        self.assertEqual(good.returncode, 0, good.stderr)
        report = (self.game/'docs/match/08128C3C.md').read_text()
        replay = lambda r: match_evidence.report_matches(r, str(self.game), drain.ADDRESS)
        self.assertTrue(replay(report))
        self.assertIn('514/514 bytes', report)
        self.assertEqual(self.result['instructions'], 226)
        for old, new in [('"index_mask":7', '"index_mask":15'), ('"signed_numerator":10', '"signed_numerator":1'),
                         ('514/514 bytes', '516/516 bytes')]:
            self.assertIn(old, report)
            self.assertFalse(replay(report.replace(old, new)))
        original = self.src.read_text()
        try:
            self.src.write_text('unsigned __udivsi3(unsigned, unsigned);\n' + original.replace(
                'func_080C92F0(unit, 0x17) / divisor', '__udivsi3(func_080C92F0(unit, 0x17), divisor)'))
            self.assertFalse(replay(report))
            failed = run(*args)
            self.assertNotEqual(failed.returncode, 0)
            self.assertIn('reserved for compiler emission', failed.stderr)
        finally:
            self.src.write_text(original)

    def test_original_elf_relocation_roles_addends_symbol_types_and_padding(self):
        src = match.elf_image(self.result['original_elf'])
        def check(image):
            return owner.original_bindings(image, drain.ADDRESS, self.rom, self.mapping,
                    self.objects, selector=drain.SELECTOR, index=self.index)
        self.assertEqual(check(src), (self.bindings, drain.TARGETS))
        for change in ('type', 'table-addend', 'switch-addend', 'external-pad', 'data-as-call',
                       'manual-div', 'hidden', 'call-type', 'symbol-size', 'call-addend'):
            image = copy.deepcopy(src)
            text = bytearray(image['text'])
            table, symbols = next(iter(image['symbol_tables'].items()))
            rel = image['relocations'][0]
            if change == 'type':
                image['type'] = 2
            elif change in ('table-addend', 'switch-addend', 'external-pad', 'call-addend'):
                text[{'table-addend': 0x28, 'switch-addend': 0x30, 'external-pad': 514,
                      'call-addend': 0x56}[change]] ^= 1
                image['text'] = bytes(text)
            elif change == 'data-as-call':
                data = bytearray(image['section_data'][rel])
                data[4] = 10
                image['section_data'][rel] = bytes(data)
            else:
                idx = next(i for i, sym in enumerate(symbols) if sym['name'] == '__divsi3')
                if change == 'hidden':
                    data = bytearray(image['section_data'][table])
                    data[idx*16+13] = 2
                    image['section_data'][table] = bytes(data)
                elif change == 'manual-div':
                    symbols[idx]['name'] = 'func_081426B8'
                elif change == 'call-type':
                    symbols[idx]['type'] = 2
                else:
                    symbols[idx]['size'] = 4
            with self.subTest(change=change), self.assertRaises(ValueError):
                check(image)

    def test_changed_input_width_table_switch_getter_and_runtime(self):
        def check(rom, address=drain.ADDRESS):
            data = rom[drain.ADDRESS-drain.BASE:drain.END-drain.BASE]
            return drain.prove(data, address, rom, self.mapping, self.index, self.objects, self.bindings)
        with self.assertRaises(ValueError):
            check(self.rom, drain.ADDRESS+2)
        for location, replacement in [
                (0x08128C4A, b'\x40\x78'), (0x08128C4C, b'\x00\x07'), (0x08128C4E, b'\x00\x0f'),
                (0x08128C52, b'\x04\x88'), (0x08128C64, struct.pack('<I', drain.TABLE+1)),
                (drain.TABLE+3, b'\x00'), (drain.TABLE+7, b'\x13'),
                (0x08128C54, b'\x07\x2a'), (0x08128C6C, struct.pack('<I', 0x08128C8A)),
                (0x08128C90, b'\x29\x1c'), (0x08128DF4, b'\x09\x20'),
                (0x080C9308, b'\x04\x24'), (0x080C8A1E, b'\x60\xbc'),
                (drain.DIV+2, b'\xc0\x46'), (drain.UDIV+2, b'\xc0\x46')]:
            rom = bytearray(self.rom)
            where = location-drain.BASE
            self.assertNotEqual(rom[where:where+len(replacement)], replacement)
            rom[where:where+len(replacement)] = replacement
            with self.subTest(address=hex(location)), self.assertRaises(ValueError):
                check(bytes(rom))
        objects = json.loads(self.objects)
        objects[drain.NAME] = '0x083A8261'
        with self.assertRaises(ValueError):
            drain.prove(self.result['body'], drain.ADDRESS, self.rom, self.mapping, self.index,
                        json.dumps(objects).encode(), self.bindings)

    def test_real_owner_getter_and_divisions_all_key_bytes(self):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_CODE
        from unicorn import arm_const as arm
        cpu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        cpu.mem_map(drain.BASE, len(self.rom))
        cpu.mem_write(drain.BASE, self.rom)
        state, unit, key, sp, stop = 0x02000100, 0x02000200, 0x02000400, 0x02001800, 0x02001F00
        cpu.mem_map(0x02000000, 0x2000)
        cpu.mem_write(state+8, struct.pack('<II', unit, key))
        saved_regs = [getattr(arm, f'UC_ARM_REG_R{i}') for i in range(4, 12)]
        saved = [0xC0A00004+i for i in range(8)]
        observed = []
        def entry(uc, address, size, _):
            observed.append((address, uc.reg_read(arm.UC_ARM_REG_R0), uc.reg_read(arm.UC_ARM_REG_R1)))
        for site in (drain.DIV, drain.UDIV):
            cpu.hook_add(UC_HOOK_CODE, entry, begin=site, end=site)
        kinds = (0, 1, 2, 3, 4, 5, 6, 7)
        for key_byte in range(256):
            record_id = 0 if key_byte & 8 else 2
            record_base = 0x521A14 + 52*record_id
            record = self.rom[record_base:record_base+52]
            # Both sample records terminate immediately through their own data.
            self.assertEqual(record[5], 0)
            stats = [record[23], record[24], record[26] | (record[27]&15)<<8,
                     (record[27]>>4) | record[28]<<4, record[29] | (record[30]&15)<<8,
                     (record[30]>>4) | record[31]<<4, 10]
            for kind in kinds:
                data = bytearray(0x104)
                data[5] = record_id
                bound = (0, 1, 2, 12, 100, 256, 65535, 0x8000)[key_byte//32]
                special = (-120, 0, 10, 11, 15, 21, 100, 32767)[key_byte//32]
                fields = (0x1A, 0x1E, 0x20, 0x22, 0x24, 0x26)
                for field in fields:
                    struct.pack_into('<H', data, field, bound)
                struct.pack_into('<H', data, 0x18, 250)
                struct.pack_into('<H', data, 0x1C, 250)
                struct.pack_into('<h', data, 0xD2, special)
                cpu.mem_write(unit, bytes(data))
                cpu.mem_write(key+2, bytes([key_byte]))
                for reg, value in zip(saved_regs, saved):
                    cpu.reg_write(reg, value)
                cpu.reg_write(arm.UC_ARM_REG_LR, stop | 1)
                cpu.reg_write(arm.UC_ARM_REG_SP, sp)
                cpu.reg_write(arm.UC_ARM_REG_R0, state)
                cpu.reg_write(arm.UC_ARM_REG_R1, 0xABCD0000 | kind)
                observed.clear()
                cpu.emu_start(drain.ADDRESS | 1, stop, count=2000)
                divisor = drain.VALUES[key_byte & 7]
                amount = 0
                if kind < 7:
                    self.assertEqual(observed, [(drain.DIV if kind == 6 else drain.UDIV,
                                                stats[kind], divisor)])
                    amount = max(1, min(10 if kind == 6 else 99, stats[kind]//divisor))
                    if kind == 6:
                        amount = min(special-10, amount)
                        struct.pack_into('<h', data, 0xD2, special-amount)
                    else:
                        amount = min(bound-1, amount)
                        value = bound-amount
                        struct.pack_into('<H', data, fields[kind], value)
                        if kind < 2:
                            struct.pack_into('<H', data, fields[kind]-2, min(250, value))
                else:
                    self.assertEqual(observed, [])
                self.assertEqual(cpu.reg_read(arm.UC_ARM_REG_PC), stop)
                self.assertEqual(cpu.reg_read(arm.UC_ARM_REG_R0), amount & 255)
                self.assertEqual(cpu.reg_read(arm.UC_ARM_REG_SP), sp)
                self.assertEqual([cpu.reg_read(r) for r in saved_regs], saved)
                self.assertEqual(cpu.mem_read(unit, len(data)), data)
