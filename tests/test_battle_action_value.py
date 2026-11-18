"""Battle actor values through both complete AI callers on a ROM-defined map."""
import copy
import os
from pathlib import Path
import struct
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import battle_action_value as battle
import unit_equipment_attribute as equip
import owner_admission_profile as owner
import match_evidence


def signed16(value):
    return (value + 0x8000) % 0x10000 - 0x8000


def lz77(memory, source):
    header = memory.mem_read(source, 4)
    if header[0] != 0x10:
        raise ValueError('expected original BIOS LZ77 resource')
    length = int.from_bytes(header[1:], 'little')
    output = bytearray()
    cursor = source + 4
    while len(output) < length:
        flags = memory.mem_read(cursor, 1)[0]
        cursor += 1
        for shift in reversed(range(8)):
            if len(output) == length:
                break
            if flags & (1 << shift):
                high, low = memory.mem_read(cursor, 2)
                cursor += 2
                distance = ((high & 15) << 8) + low + 1
                for _ in range(min(3 + (high >> 4), length - len(output))):
                    output.append(output[-distance])
            else:
                output.extend(memory.mem_read(cursor, 1))
                cursor += 1
    return bytes(output)


def battle_environment(test):
    from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_INTR, UC_PROT_READ, UC_PROT_EXEC
    from unicorn import arm_const as reg
    from test_bg_affine_rows import NativeAffineRows

    cpu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    for address, size in ((equip.BASE, len(test.rom)), (0x02000000, 0x40000),
                          (0x03000000, 0x8000), (0x04000000, 0x1000)):
        cpu.mem_map(address, size)
    cpu.mem_write(equip.BASE, test.rom)
    cpu.mem_protect(equip.BASE, len(test.rom), UC_PROT_READ | UC_PROT_EXEC)

    def bios(machine, _, context):
        pc = machine.reg_read(reg.UC_ARM_REG_PC)
        service, opcode = machine.mem_read(pc-2, 2)
        test.assertEqual(opcode, 0xdf)
        source, dest, control = (machine.reg_read(reg.UC_ARM_REG_R0+i) for i in range(3))
        if service == 0x11:
            data = lz77(machine, source)
        else:
            test.assertIn(service, (11, 12))
            count = control & 0x1fffff
            width = 4 if service == 12 or control & (1 << 26) else 2
            fill = bool(control & (1 << 24))
            data = bytes(machine.mem_read(source, width if fill else count*width))
            if fill:
                data *= count
        machine.mem_write(dest, data)

    def call(address, *args):
        saved = {r: 0x63120000+r for r in range(reg.UC_ARM_REG_R4, reg.UC_ARM_REG_R11+1)}
        for r, value in saved.items():
            cpu.reg_write(r, value)
        result = NativeAffineRows.call(test, cpu, address, *args)
        test.assertEqual({r: cpu.reg_read(r) for r in saved}, saved)
        return result

    def write(ptr, fmt, *args):
        cpu.mem_write(ptr, struct.pack('<'+fmt, *args))

    def allocate(count):
        ptr = call(0x08022840, count)
        test.assertTrue(0x02000000 <= ptr and ptr+count <= 0x02040000)
        cpu.mem_write(ptr, bytes(count))
        return ptr

    cpu.hook_add(UC_HOOK_INTR, bios)
    call(0x08002768)
    test.assertEqual(bytes(cpu.mem_read(0x03005E78, 176)), test.rom[0xA38A2C:0xA38ADC])
    call(0x080227E8)
    # Map 0. Original 0801A980 passes these three resource offsets to the loader.
    table = 0x08569104
    resources = [table + equip.word(test.rom, table+field) for field in (16, 4, 8)]
    call(0x08019D18, *resources, 32, 32)
    test.assertEqual(struct.unpack('<IBB', cpu.mem_read(0x02007F14, 6)), (0x02007CB0, 16, 16))

    return cpu, call, write, allocate


@unittest.skipUnless(os.getenv('FFTA_BATTLE_ACTION_ROOT'), 'requires USA ROM and recovered battle evaluator')
class BattleActionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_BATTLE_ACTION_ROOT']).resolve()
        cls.built = owner.build(cls.root, battle.OWNER, selector=equip.named.EQUIPMENT_SELECTOR)
        cls.rom = cls.built[6]

    def test_original_symbol_and_saved_condition(self):
        report = (self.root/'docs/match/080BDECC.md').read_text()
        self.assertTrue(match_evidence.report_matches(report, self.root, battle.OWNER))
        self.assertEqual(self.built[0], self.rom[0xBDECC:0xBDF9A])
        self.assertEqual(self.built[1]['bindings'], equip.bindings(battle.CALLS))
        for old, new in (('"local":[-36,-32]', '"local":[-36,-28]'), ('at most two', 'at most five')):
            changed = report.replace(old, new)
            self.assertNotEqual(changed, report)
            self.assertFalse(match_evidence.report_matches(changed, self.root, battle.OWNER))

    def test_original_thumb_symbol_roles(self):
        import match
        _, _, _, mapping, index, objects, rom, _, elf = self.built
        image = match.elf_image(elf)

        def repo_bindings(obj):
            return owner.original_bindings(obj, battle.OWNER, rom, mapping, objects,
                                          selector=equip.named.EQUIPMENT_SELECTOR, index=index)

        original, targets = repo_bindings(image)
        self.assertEqual(original, equip.bindings(battle.CALLS))
        self.assertEqual(targets, {f'func_{value:08X}': (value, False) for value in battle.CALLS.values()})
        for field, value in (('size', 4), ('bind', 2), ('type', 2)):
            changed = copy.deepcopy(image)
            symbol = next(s for s in changed['symbols'] if s['name'] == 'func_08130200')
            symbol[field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                repo_bindings(changed)

    def test_each_produced_count_and_action_path(self):
        rows = battle.selection_cases()
        self.assertEqual(len(rows), 32)
        for row in rows:
            count = row['mask'].bit_count()
            expected = [8] if count <= 1 or row['zero_action'] else [8, 10]
            self.assertEqual(row['read_offsets'], expected)
            self.assertEqual(row['fallback'], count == 0)

    def test_native_scene_units_and_both_callers(self):
        from unicorn import UC_HOOK_CODE
        from unicorn import arm_const as reg
        cpu, call, write, allocate = battle_environment(self)
        source, target = 0x02002FC4, 0x020030CC
        left, right = allocate(0x24), allocate(0x24)
        context, group, other = allocate(0x21C), allocate(0x290C), allocate(0x290C)
        positions, request, selected = allocate(1024), allocate(12), allocate(4)
        write(left, 'I', source)
        write(right, 'I', target)
        write(context, 'I', left)
        write(context+12, 'II', group, other)
        write(group, 'I', right)
        write(group+0x324, 'H', 1)    # One action record in the target entry.
        write(group+0x2908, 'H', 1)   # One entry in the first group.

        observed = {}
        def trace(machine, pc, size, context):
            args = tuple(machine.reg_read(reg.UC_ARM_REG_R0+i) for i in range(4))
            sp = machine.reg_read(reg.UC_ARM_REG_SP)
            on_stack = struct.unpack('<II', machine.mem_read(sp, 8))
            observed.setdefault(pc, []).append((args, sp, on_stack))

        for pc in (battle.OWNER, 0x080BE566, 0x080BE73C, 0x080BDEF0, 0x080BDF06, 0x080BDF0A,
                   0x080BDF14, 0x080BDF18, 0x080BDF54, 0x080BDF58, 0x080BDF8A):
            cpu.hook_add(UC_HOOK_CODE, trace, begin=pc, end=pc)

        target_definition = equip.GROUPS[2][1] + 48
        seen_counts, signs = set(), set()
        verified = 0
        for group_id, row, items, chosen in equip.scene_rows(self.rom):
            definition = equip.GROUPS[group_id][1] + 48*row
            for actor, record in ((source, definition), (target, target_definition)):
                call(0x080C9644, actor, record, 0)
            self.assertEqual(struct.unpack('<5H', cpu.mem_read(source+42, 10)), tuple(items))
            selected_items = [] if cpu.mem_read(source+0xE9, 1)[0] & 1 else sorted(chosen, reverse=True,
                key=lambda item: struct.unpack_from('<b', self.rom, equip.ITEMS-equip.BASE+32*item+16)[0])
            seen_counts.add(len(selected_items))
            for action in (0, 1, 2, 3):
                write(context+8, 'H', action)
                write(context+26, 'H', 0)
                write(group+4, 'H', action)
                write(group+16, 'h', 1)
                write(source+0xF6, 'BB', 6, 6)
                call(equip.WRAPPER, source, selected)
                write(request, 'IBBBBHH', source, 7, 6, 7, 6, action, int.from_bytes(cpu.mem_read(selected, 2), 'little'))
                count = call(0x080B4A1C, request, 0, 1, positions)
                self.assertTrue(0 < count <= 256)
                pos = next(positions+4*i for i in range(count) if cpu.mem_read(positions+4*i, 2) != bytes((6, 6)))
                coords = bytes(cpu.mem_read(pos, 2))
                self.assertEqual(call(0x0801CC7C, *coords), 1)
                cpu.mem_write(target+0xF6, coords)

                for caller, site, args in ((0x080BE494, 0x080BE566, (context, pos, 1)),
                                           (0x080BE5F4, 0x080BE73C, (context, 7, 6, *coords, positions))):
                    observed.clear()
                    result = call(caller, *args)
                    self.assertEqual(result, 1)
                    self.assertEqual(len(observed[site]), 1)
                    entry, entry_sp, _ = observed[battle.OWNER][0]
                    self.assertEqual(entry, (left, right, action, 0))
                    local_sp = entry_sp-44
                    self.assertEqual(observed[0x080BDEF0][0][0][0] & 255, 1)
                    adjust_args, _, adjust_stack = observed[0x080BDF06][0]
                    self.assertEqual((adjust_args, adjust_stack[0]), ((source, target, action, 1), 0))
                    collector_args = observed[0x080BDF14][0][0]
                    self.assertEqual(collector_args[:2], (source, local_sp+8))
                    self.assertEqual(observed[0x080BDF18][0][0][0], len(selected_items))
                    expected = (selected_items or [0])[:1 if not action else 2]
                    actual = observed[0x080BDF54]
                    self.assertEqual([args for args, _, _ in actual], [(source, target, action, item) for item in expected])
                    self.assertTrue(all(sp == local_sp and extra == (0, 2) for _, sp, extra in actual))
                    subtotal = 0
                    for regs, _, _ in observed[0x080BDF58]:
                        subtotal = signed16(subtotal + regs[0])
                    signs.add((subtotal > 0) - (subtotal < 0))
                    adjustment = signed16(observed[0x080BDF0A][0][0][0])
                    score = signed16(subtotal + (-adjustment if subtotal < 0 else adjustment))
                    self.assertEqual(observed[0x080BDF8A][0][0][0], score & 0xFFFFFFFF)
                    verified += 1
        self.assertEqual(verified, 336)
        self.assertEqual(seen_counts, {0, 1, 2})
        self.assertTrue({-1, 1} <= signs)
        # A defeated target fails the original basic-action eligibility predicate.
        write(target+0x18, 'H', 0)
        observed.clear()
        self.assertEqual(call(battle.OWNER, left, right, 0, 0), 0)
        self.assertEqual(observed[0x080BDEF0][0][0][0], 0)
        self.assertNotIn(0x080BDF14, observed)
