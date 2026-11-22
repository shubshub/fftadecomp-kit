"""Replay the menu callback and execute its original installer, both dispatch paths and local outputs."""
import json
import os
from pathlib import Path
import struct
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import data_buffer_profile
import local_long_branch_profile as local
import match
import match_evidence
import menu_list_frame as menu
import owner_admission_profile as owner
import owner_graph_profile as graph

from test_battle_action_value import battle_environment


@unittest.skipUnless(os.getenv('FFTA_MENU_LIST_FRAME_ROOT'), 'requires USA ROM and recovered menu callback')
class MenuListTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_MENU_LIST_FRAME_ROOT']).resolve()
        cls.rom = (cls.root / 'baserom.bin').read_bytes()
        cls.data = cls.rom[menu.ADDRESS-match.ROM_BASE:menu.END-match.ROM_BASE]
        cls.mapping = (cls.root / 'config/functions.json').read_bytes()
        cls.objects = (cls.root / 'config/data_symbols.json').read_bytes()
        cls.index = (cls.root / 'symbols/functions.txt').read_bytes()
        cls.report = (cls.root / 'docs/match/08052870.md').read_text()

    def forge(self, edit):
        """The saved report with its data buffer manifest edited in place and the data buffer proof
        SHA-256 recomputed over the edit, so only the replay's own comparison can refuse it."""
        lines = self.report.splitlines()

        def field(prefix):
            (line,) = [row for row in lines if row.startswith(prefix)]
            return line, line[len(prefix):]

        def quoted(prefix):
            return field(prefix)[1][1:-1]

        manifest_line, raw = field(data_buffer_profile.MANIFEST_FIELD)
        proof_line, _ = field(data_buffer_profile.PROOF_FIELD)
        manifest = json.loads(raw[1:-1])
        edit(manifest)
        compiled = bytes.fromhex(field('* compiled : ')[1].split('`')[1])
        digest = data_buffer_profile.fingerprint(
            quoted('* verification: '), menu.ADDRESS, compiled, manifest, quoted('* source SHA-256: '),
            match_evidence.mapping_snapshot(self.root), match_evidence.data_snapshot(self.root),
            quoted('* buffer proof SHA-256: '))
        return self.report.replace(
            manifest_line, data_buffer_profile.MANIFEST_FIELD + '`' + data_buffer_profile.manifest_text(manifest) + '`'
        ).replace(proof_line, data_buffer_profile.PROOF_FIELD + '`' + digest + '`')

    def test_saved_report_exact_calls_and_complete_local_frame(self):
        self.assertTrue(match_evidence.report_matches(self.report, self.root, menu.ADDRESS))
        payload = next(row for row in self.report.splitlines() if row.startswith('* data buffer manifest:'))
        # The field is the text between the first and the last backtick; the replay line quotes its schema.
        evidence = json.loads(payload.split('`', 1)[1].rsplit('`', 1)[0])
        self.assertEqual([len(evidence[key]) for key in ('calls', 'data', 'functions')], [74, 30, 3])
        frame = evidence['restoring_menu_frame']['frame']
        self.assertEqual((frame['maximum_frame_bytes'], frame['returns']), (64, [0x08053092]))
        # The re-walk replays the byte-output callee and trusts R4 across 080CCA20, a pinned leaf
        # that finish checks; the report says both.
        replay = ['* buffer loop replay: `bounded-loop-replay-v2` callee 0x08053568 sites none writes '
                  'sp+28:1 sp+29:1; proved none; trusted 0x080CCA20:r4; pruned edges 0']
        self.assertEqual(evidence['restoring_menu_frame']['loop_replay_lines'], replay)
        self.assertEqual(evidence['restoring_menu_frame']['trusted_pinned_leaves'], [[0x080CCA20, [4]]])
        self.assertIn(0x080CCA20, menu.PINS)
        # Each forgery carries a recomputed proof SHA-256, so the replay comparison refuses it.
        self.assertEqual(self.forge(lambda manifest: None), self.report)
        for name, edit in (
                ('output offsets', lambda m: m['restoring_menu_frame'].update(output_offsets=[28, 30])),
                ('trusted', lambda m: m['restoring_menu_frame'].update(loop_replay_lines=[
                    line.replace('trusted 0x080CCA20:r4', 'trusted none') for line in replay])),
                ('replay dropped', lambda m: m['restoring_menu_frame'].update(loop_replay_lines=[])),
                ('pruned edges', lambda m: m['restoring_menu_frame'].update(loop_replay_lines=[
                    line.replace('pruned edges 0', 'pruned edges 1') for line in replay])),
                ('leaf dropped', lambda m: m['restoring_menu_frame'].update(trusted_pinned_leaves=[]))):
            with self.subTest(forged=name):
                forged = self.forge(edit)
                self.assertNotEqual(forged, self.report)
                self.assertFalse(match_evidence.report_matches(forged, self.root, menu.ADDRESS))

    def test_trusted_callee_must_be_a_pinned_leaf_that_keeps_the_register(self):
        r = lambda n: match.ARM_REG_R0 + n
        menu.require_pinned_leaf(self.rom, self.mapping, 0x080CCA20, {r(4)})
        for register in (0, 1, 2):
            with self.subTest(register=register), self.assertRaisesRegex(ValueError, 'writes a register'):
                menu.require_pinned_leaf(self.rom, self.mapping, 0x080CCA20, {r(register)})
        with self.assertRaisesRegex(ValueError, 'is not a pinned leaf'):
            menu.require_pinned_leaf(self.rom, self.mapping, menu.OUTPUT, {r(7)})
        offset = 0x080CCA22 - match.ROM_BASE
        changed = self.rom[:offset] + bytes([self.rom[offset] ^ 1]) + self.rom[offset+1:]
        with self.assertRaisesRegex(ValueError, 'differs from its pin'):
            menu.require_pinned_leaf(changed, self.mapping, 0x080CCA20, {r(4)})
        pins = {address: pin for address, pin in menu.PINS.items() if address != 0x080CCA20}
        with patch.object(menu, 'PINS', pins):
            with self.assertRaisesRegex(ValueError, 'unpinned callee 080CCA20'):
                menu.require_pinned_leaf(self.rom, self.mapping, 0x080CCA20, {r(4)})
            self.assertFalse(match_evidence.report_matches(self.report, self.root, menu.ADDRESS))

    def test_changed_rom_mapping_index_and_typed_bindings(self):
        def check(rom=self.rom, index=self.index, objects=self.objects, data_relocs=menu.OBJECTS,
                  callbacks=menu.FUNCTIONS, mapping=self.mapping):
            return menu.MenuListFrame(self.data, rom, mapping, index, objects, data_relocs, callbacks)

        check()
        for address in (*menu.PINS, menu.THUNK, 0x08422764, 0x0841CE18):
            with self.subTest(address=hex(address)), self.assertRaises(ValueError):
                offset = address - match.ROM_BASE
                changed = self.rom[:offset] + bytes([self.rom[offset] ^ 1]) + self.rom[offset+1:]
                check(rom=changed)
        wrong_index = self.index.replace(b'08052870 080530A0  2096 805', b'08052870 080530A0  2096 1044')
        self.assertNotEqual(wrong_index, self.index)
        rows = json.loads(self.mapping)
        next(row for row in rows if row['rom'] == '0x08052870')['instrs'] = 1044
        for args in (dict(index=wrong_index), dict(mapping=json.dumps(rows).encode(), index=wrong_index),
                     dict(objects=self.objects.replace(b'"0x08422764"', b'"0x08422768"')),
                     dict(callbacks={**menu.FUNCTIONS, 0x2E4: menu.FUNCTIONS[0x5B4]}),
                     dict(data_relocs={**menu.OBJECTS, 0x2F0: menu.OBJECTS[0x2F4]})):
            with self.subTest(field=list(args)), self.assertRaises(ValueError):
                check(**args)

    def test_independent_walk_rejects_under_restored_sp_and_exit_via_clobbered_lr(self):
        from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
        decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
        decoder.detail = True
        refinement = owner.refine(self.data, menu.ADDRESS, self.mapping)
        ins, edges, branches, calls, tables = graph.graph(self.data, menu.ADDRESS, refinement)
        self.assertEqual((len(ins), branches, len(calls), tables), (805, menu.MenuListFrame.BRANCHES, 74, {}))
        for site, target in branches.items():
            self.assertEqual(tuple(edges[site]), (target,))
        for site, code in ((0x08053084, b'\x07\xb0'), (0x08053092, b'\x70\x47')):
            with self.subTest(site=hex(site)), self.assertRaises(ValueError):
                altered = dict(ins)
                altered[site] = next(decoder.disasm(code, site))
                proof = match.BufferCallProof(self.rom, self.mapping, loop_replay=True)
                local.prove_frame(altered, edges, menu.ADDRESS, branches, calls,
                                  stack_aliases=True, buffer_proof=proof)

    def test_original_installer_dispatch_loop_animation_and_byte_output(self):
        from unicorn import UC_HOOK_CODE
        from unicorn import arm_const as reg
        cpu, call, write, _ = battle_environment(self)
        for loc, size in ((0x05000000, 0x1000), (0x06000000, 0x20000), (0x07000000, 0x1000)):
            cpu.mem_map(loc, size)
        for layer, buffer in ((0x030008B0, 0x0203C000), (0x03000990, 0x0203D000)):
            write(layer+12, 'B', 32)
            write(layer+16, 'II', 0x06008000, buffer)

        def read(loc, fmt='I'):
            return struct.unpack('<'+fmt, cpu.mem_read(loc, struct.calcsize('<'+fmt)))[0]

        events = {}

        def trace(machine, pc, size, user):
            events[pc] = tuple(machine.reg_read(r) for r in (
                reg.UC_ARM_REG_R0, reg.UC_ARM_REG_R1, reg.UC_ARM_REG_R2, reg.UC_ARM_REG_R3,
                reg.UC_ARM_REG_SP, reg.UC_ARM_REG_LR))

        for pc in (menu.REGISTER, menu.ADDRESS, *menu.MenuListFrame.BRANCHES, 0x08053084,
                   menu.OUTPUT, 0x08053C74, 0x0802B3A8):
            cpu.hook_add(UC_HOOK_CODE, trace, begin=pc, end=pc)
        call(0x08050F1C, 0, 0x0203B000)
        context = read(0x0200F428)
        runner = context + 0xCD8
        handlers, state = read(runner+8), read(runner+12)
        write(state, 'B', 254)
        call(menu.INSTALLER, 0, state)
        self.assertEqual(events[menu.REGISTER][:3], (runner, 0, menu.ADDRESS | 1))
        self.assertEqual((read(handlers), read(state, 'B')), (menu.ADDRESS | 1, 0))

        active_states = {0, 1, 20, 21, 22, 100, 101, 102, 103, 104, 200, 201, 220, 255}
        for phase in sorted(set(range(256)) - active_states):
            mode = phase % 2
            write(runner+5, 'B', mode)
            write(state, 'B', phase)
            events.clear()
            call(menu.RUNNER, runner, 1)
            args = events[menu.ADDRESS]
            self.assertEqual((args[:2], args[5], read(state, 'B')), ((0, state), (0x08006A39, 0x08006A6F)[mode], phase))
            self.assertIn(0x08053084, events)
            if phase in (2, 23):
                expected = (0x0805289A, 0x080528B0)[phase == 23]
                self.assertEqual(events.keys() & menu.MenuListFrame.BRANCHES.keys(), {expected})
                self.assertEqual(events[0x08053084][-1], (expected+4) | 1)

        write(0x02001F3C, 'H', 1)
        write(state, 'B', 0)
        for following in (20, 21):
            call(menu.RUNNER, runner, 1)
            self.assertEqual(read(state, 'B'), following)
        for _ in range(60):
            events.clear()
            call(menu.RUNNER, runner, 1)
            if read(state, 'B') != 21:
                break
        self.assertEqual(read(state, 'B'), 22)
        first, second, _, _, sp, _ = events[menu.OUTPUT]
        self.assertEqual((first, second), (sp+28, sp+29))
        self.assertEqual(events[0x08053C74][2:4], (0, 0))
        animation = context + 0x1D60
        self.assertEqual(events[0x0802B3A8][:4], (animation, 0x08422764, 0x0841CE18, 0))
        self.assertEqual((read(animation), read(animation+4), read(animation+8, 'H'), read(animation+12)),
                         (0x08422764, 0x0841CE18, 9, 0x0841CE22))
        write(state, 'B', 255)
        call(menu.RUNNER, runner, 1)
        self.assertEqual((read(handlers), read(state, 'B')), (menu.INSTALLER | 1, 0))

        # The production helper must touch exactly the two byte outputs, regardless of row count.
        items = [1, 85, 86, 170, 171] * 4
        write(0x02001F3C, '20H', *items)
        out = 0x03007604
        values = {1: self.rom[0x528F44], 85: self.rom[0x529484], 86: self.rom[0x528F44],
                  170: self.rom[0x529484], 171: self.rom[0x39475C]}
        for flags in ([0]*20, [1]+[2]*18+[1], [1]*20):
            cpu.mem_write(context+0x1D48, bytes(flags))
            cpu.mem_write(out-1, bytes.fromhex('aabbccdd'))
            call(menu.OUTPUT, out, out+1)
            active = [item for item, flag in zip(items, flags) if flag == 1]
            self.assertEqual(bytes(cpu.mem_read(out-1, 4)),
                             bytes((0xAA, len(active), sum(values[item] for item in active) & 255, 0xDD)))


if __name__ == '__main__':
    unittest.main()
