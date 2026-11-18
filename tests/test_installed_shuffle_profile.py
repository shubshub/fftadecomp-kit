"""Real Thumb overlap effects, exact owner obligations and original ELF replay."""

import copy
from contextlib import redirect_stdout
import io
import importlib.util
import json
import os
from pathlib import Path
import struct
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import installed_copy_effects as installed
import installed_shuffle_profile as shuffle
import match
import match_evidence
import signed_divmod_profile as driver
import status

ENTRY = 0x03005EE8


class CopyTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        path = Path(os.environ.get('FFTA_ROM', ''))
        if not path.is_file():
            raise unittest.SkipTest('FFTA_ROM must reference the approved ROM')
        with path.open('rb') as source:
            source.seek(0x08A38A9C - shuffle.BASE)
            cls.payload = source.read(62)
        if len(cls.payload) != 62:
            raise ValueError('approved ROM must supply the complete installed copy helper')

    def test_shared_memory_order_and_all_zero_cases(self):
        sizes = [0, 0, 0]
        for count in range(1, 9):
            for index in range(count):
                with self.subTest(count=count, index=index):
                    case = installed.verify_adjacent_table(self.payload, ENTRY, ENTRY, count, index)
                    rest = count - index - 1
                    sizes[min(rest, 2)] += 1
                    actual = list(range(8))
                    before = actual[:]
                    for offset in range(rest):
                        read, write = case['accesses'][2 * offset : 2 * offset + 2]
                        self.assertEqual(read, ['read', index + 1 + offset])
                        self.assertEqual(write, ['write', index + offset])
                        actual[write[1]] = actual[read[1]]
                    expected = before[:]
                    expected[index : count - 1] = before[index + 1 : count]
                    self.assertEqual(case['length'], rest)
                    self.assertEqual(len(case['accesses']), 2 * rest)
                    self.assertEqual(actual, expected)
        self.assertEqual(sizes, [8, 7, 21])

    def test_old_selector_preserves_disjoint_word_copy(self):
        proof = installed.verify_conditional(self.payload, ENTRY, ENTRY, 8, selector=installed.SELECTOR)
        self.assertEqual(len(proof['cases']), 16)
        self.assertIn(('source', 0, 4), proof['cases'][0]['reads'])
        self.assertTrue(any('physically disjoint' in p for p in proof['unproved_premises']))
        with self.assertRaises(ValueError):
            installed.verify_conditional(self.payload, ENTRY, ENTRY, 8, selector=shuffle.SELECTOR)

    def test_out_of_frame_indices_wrong_access_width_direction_and_order(self):
        for count, index in ((0, 0), (9, 0), (1, -1), (8, 8), (True, 0), (3, True)):
            with self.subTest(count=count, index=index), self.assertRaises(ValueError):
                installed.verify_adjacent_table(self.payload, ENTRY, ENTRY, count, index)
        for offset, value in ((0x2A, 0x7818), (0x2C, 0x7058), (0x2E, 0x3901), (0x1A, 0x46C0), (0x2A, 0x7018)):
            changed = bytearray(self.payload)
            struct.pack_into('<H', changed, offset, value)
            with self.subTest(offset=offset, value=value), self.assertRaises(ValueError):
                installed.verify_adjacent_table(bytes(changed), ENTRY, ENTRY, 8, 0)


SOURCE = """
typedef unsigned char u8;
typedef unsigned short u16;
typedef unsigned int u32;
typedef short s16;
typedef int s32;
typedef void (*BufferCopier)(void *, const void *, u32);
typedef struct { u8 unknown_00[12]; u8 order[9]; } Unit;
typedef struct {
    u8 unknown_00[8];
    Unit *unit;
    u8 unknown_0C[26];
    u16 flags;
} FlaggedObject;
extern BufferCopier data_0836D4BC[];
extern const u8 data_083A8C0C[];
extern u32 func_08002804(void);

void func_08132064(FlaggedObject *object)
{
    u8 table[8];
    u8 count;
    s32 i;

    if (object->flags & 0x10)
        return;
    data_0836D4BC[0](table, data_083A8C0C, 8);
    count = 8;
    for (i = 1; i <= 8 && count != 0; i++, count--) {
        s32 index = (s16)func_08002804() % count;
        s32 rest;
        object->unit->order[i] = table[index];
        rest = count - index - 1;
        if (rest != 0)
            data_0836D4BC[0](&table[index], &table[index + 1], rest);
    }
}
"""


class NativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        path = Path(os.environ.get('FFTA_ROM', ''))
        if not path.is_file():
            raise unittest.SkipTest('FFTA_ROM must reference the approved ROM')
        scratch = Path(
            os.environ.get('FFTA_TEST_SCRATCH', Path(__file__).resolve().parents[1] / 'build/tests')
        )
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix='action_shuffle_', dir=scratch)
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.root = root = Path(cls.temporary.name)
        for name in ('src', 'include', 'config', 'symbols'):
            (root / name).mkdir()
        (root / 'baserom.bin').symlink_to(path.resolve())
        cls.src = root / 'src/08132064.c'
        cls.src.write_text(SOURCE)
        spans = [
            (0x08002768, 0x080027B8, 26),
            (0x08002804, 0x08002824, 10),
            (0x08132064, 0x081320E8, 57),
            (0x0813388C, 0x08133970, 97),
            (0x0814186C, 0x08141870, 2),
            (0x08142248, 0x0814224A, 1),
            (0x08142250, 0x08142252, 1),
            (0x0814274C, 0x0814274E, 1),
            (0x08142950, 0x08142A1E, 102),
            (0x08A38A9C, 0x08A38ADA, 31),
        ]
        (root / 'config/functions.json').write_text(
            json.dumps(
                [dict(rom=f'0x{a:08X}', end=f'0x{e:08X}', instrs=n, mode='thumb') for a, e, n in spans]
            )
        )
        (root / 'symbols/functions.txt').write_text(
            ''.join(f'{a:08X} {e:08X} {e-a:5d} {n:3d} return\n' for a, e, n in spans)
        )
        (root / 'config/data_symbols.json').write_text(
            json.dumps(
                {
                    name: '0x' + name.split('_')[-1]
                    for name in (
                        'data_0836D4BC',
                        'data_083A8C0C',
                        'data_083A87B0',
                        'data_0200F3F0',
                        'g_state_030034B0',
                    )
                }
            )
        )
        cls.result = driver.build(root, shuffle.ADDRESS, selector=shuffle.SELECTOR)

    @unittest.skipUnless(importlib.util.find_spec('unicorn'), 'unicorn CPU oracle not installed')
    def test_real_owner_cpu_all_choices_and_aliased_unit(self):
        from unicorn import (
            Uc,
            UC_ARCH_ARM,
            UC_MODE_THUMB,
            UC_HOOK_CODE,
            UC_HOOK_MEM_READ,
            UC_HOOK_MEM_WRITE,
            UC_MEM_READ,
        )
        from unicorn import arm_const as arm

        rom = (self.root / 'baserom.bin').read_bytes()
        cpu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        for start, size in ((shuffle.BASE, 0x400000), (0x02000000, 0x1000), (0x03000000, 0x8000)):
            cpu.mem_map(start, size)
        for start, size in (
            (shuffle.ADDRESS, 132),
            (shuffle.RNG, 32),
            (shuffle.THUNK, 2),
            (shuffle.REMAINDER, 206),
            (0x0814274C, 2),
            (shuffle.POINTER, 4),
            (shuffle.TABLE, 8),
        ):
            cpu.mem_write(start, rom[start - shuffle.BASE : start - shuffle.BASE + size])
        cpu.mem_write(ENTRY, rom[0xA38A9C:0xA38ADA])
        sp, stop, obj = 0x03007000, 0x08000100, 0x02000100
        table = sp - 32
        regs = [getattr(arm, f'UC_ARM_REG_R{i}') for i in range(12)]
        runtime, copies = [], []

        def code(uc, pc, size, user):
            if pc == shuffle.ADDRESS + 0x36:
                runtime.append(uc.reg_read(regs[0]))
            if pc == ENTRY:
                copies.append(([uc.reg_read(regs[n]) for n in range(3)], []))

        def access(uc, kind, address, size, value, user):
            if ENTRY <= uc.reg_read(arm.UC_ARM_REG_PC) < ENTRY + 62 and table <= address < table + 8:
                copies[-1][1].append(('read' if kind == UC_MEM_READ else 'write', address, size))

        cpu.hook_add(UC_HOOK_CODE, code)
        cpu.hook_add(UC_HOOK_MEM_READ | UC_HOOK_MEM_WRITE, access)
        multiplier, increment = 0x41C64E6D, 0x3039
        inverse = pow(multiplier, -1, 2**32)
        observed = set()

        def run(seed, unit, flag):
            cpu.mem_write(obj + 8, struct.pack('<I', unit))
            cpu.mem_write(obj + 38, struct.pack('<H', flag))
            cpu.mem_write(table - 16, b'\xa5' * 64)
            if unit != table - 13:
                cpu.mem_write(unit + 13, b'\xcc' * 8)
            cpu.mem_write(0x030034B0, struct.pack('<I', seed))
            cpu.reg_write(arm.UC_ARM_REG_SP, sp)
            cpu.reg_write(arm.UC_ARM_REG_LR, stop | 1)
            cpu.reg_write(regs[0], obj)
            for n in range(4, 12):
                cpu.reg_write(regs[n], 0x12340 + n)
            runtime.clear()
            copies.clear()
            cpu.emu_start(shuffle.ADDRESS | 1, stop, count=4096)
            self.assertEqual(cpu.reg_read(arm.UC_ARM_REG_PC), stop)
            self.assertEqual(cpu.reg_read(arm.UC_ARM_REG_SP), sp)
            self.assertEqual([cpu.reg_read(r) for r in regs[4:]], list(range(0x12344, 0x1234C)))
            if flag:
                self.assertEqual((runtime, copies), ([], []))
                self.assertEqual(bytes(cpu.mem_read(unit + 13, 8)), b'\xcc' * 8)
            else:
                initial = rom[shuffle.TABLE - shuffle.BASE : shuffle.TABLE - shuffle.BASE + 8]
                memory = {table + n: b for n, b in enumerate(initial)}
                expected_calls = [([table, shuffle.TABLE, 8], [('write', table, 4), ('write', table + 4, 4)])]
                indices = []
                for count in range(8, 0, -1):
                    seed = (seed * multiplier + increment) & 0xFFFFFFFF
                    chosen = ((seed >> 16) & 0x7FFF) % count
                    indices.append(chosen)
                    observed.add((count, chosen))
                    memory[unit + 12 + (9 - count)] = memory[table + chosen]
                    length = count - chosen - 1
                    if length:
                        accesses = []
                        for n in range(chosen, count - 1):
                            accesses.extend([('read', table + n + 1, 1), ('write', table + n, 1)])
                            memory[table + n] = memory[table + n + 1]
                        expected_calls.append(([table + chosen, table + chosen + 1, length], accesses))
                self.assertEqual(runtime, indices)
                self.assertEqual(copies, expected_calls)
                self.assertEqual(
                    bytes(cpu.mem_read(unit + 13, 8)), bytes(memory[unit + 13 + n] for n in range(8))
                )
            self.assertEqual(struct.unpack('<I', cpu.mem_read(0x030034B0, 4))[0], seed)

        for count in range(1, 9):
            for chosen in range(count):
                # Invert the real LCG to arrange the requested remainder at this iteration.
                seed = chosen << 16
                for _ in range(9 - count):
                    seed = (seed - increment) * inverse & 0xFFFFFFFF
                run(seed, 0x02000200, 0)
        self.assertEqual(observed, {(n, k) for n in range(1, 9) for k in range(n)})
        run(0x12345678, table - 13, 0)  # Each unit output aliases one private table byte.
        run(0x87654321, 0x02000200, 0x10)

    def test_native_issue_replay_forged_report_and_addressed_source(self):
        options = [
            'match.py',
            '08132064',
            '--root',
            str(self.root),
            '--signed-runtime-profile',
            shuffle.SELECTOR,
        ]
        with patch.object(sys, 'argv', options), redirect_stdout(io.StringIO()):
            self.assertEqual(match.main(), 0)
        report = (self.root / 'docs/match/08132064.md').read_text()
        self.assertEqual(report, driver.render(self.result))
        self.assertEqual(self.result['instructions'], 57)
        self.assertEqual(len(self.result['body']), 132)
        self.assertEqual(self.result['manifest']['rng']['range'], [0, 32767])
        self.assertEqual(sum(x['called'] for x in self.result['manifest']['loop']), 28)
        self.assertFalse(self.result['manifest']['unconditional_permutation_proved'])
        self.assertTrue(match_evidence.report_matches(report, self.root, shuffle.ADDRESS))
        counts = status.collect(str(self.root), verify=True)
        self.assertEqual((counts[1], counts[3], counts[4]), (1, 132, []))
        forged = copy.deepcopy(self.result)
        forged['manifest']['unconditional_permutation_proved'] = True
        self.assertFalse(match_evidence.report_matches(driver.render(forged), self.root, shuffle.ADDRESS))
        with (
            patch.object(sys, 'argv', options + ['--switch-profile', 'two-constants-v2']),
            self.assertRaises(SystemExit),
        ):
            match.main()
        for replacement in (
            'func_08142950((s16)func_08002804(), count)',
            '__modsi3((s16)func_08002804(), count)',
        ):
            self.src.write_text(
                'extern int '
                + replacement.split('(')[0]
                + '(int, int);\n'
                + SOURCE.replace('(s16)func_08002804() % count', replacement)
            )
            try:
                self.assertFalse(match_evidence.report_matches(report, self.root, shuffle.ADDRESS))
                with self.assertRaises(ValueError):
                    driver.build(self.root, shuffle.ADDRESS, selector=shuffle.SELECTOR)
            finally:
                self.src.write_text(SOURCE)

    def test_forged_instruction_and_dependency_bytes_even_when_inputs_agree(self):
        root = self.root
        rom = (root / 'baserom.bin').read_bytes()
        mapping = (root / 'config/functions.json').read_bytes()
        index = (root / 'symbols/functions.txt').read_bytes()
        objects = (root / 'config/data_symbols.json').read_bytes()
        bindings = self.result['manifest']['bindings']
        # RNG sign, target index/destination, zero branch, source+1, count decrement,
        # frame release, installed Thumb pointer, slot pointer, remainder and veneer.
        for site in (
            0x08002814,
            0x081320A0,
            0x081320B0,
            0x081320B2,
            0x081320C4,
            0x081320D2,
            0x0836D4BC,
            0x083A8888,
            0x08142950,
            0x08142250,
            0x08002796,
        ):
            changed = bytearray(rom)
            changed[site - shuffle.BASE] ^= 1
            changed = bytes(changed)
            body = changed[0x132064:0x1320E8]
            with self.subTest(site=hex(site)), self.assertRaises(ValueError):
                shuffle.prove(body, shuffle.ADDRESS, changed, mapping, index, objects, bindings)
        bad = dict(bindings, calls=[*bindings['calls']])
        bad['calls'][2] = [0x32, 'func_08142950']
        with self.assertRaises(ValueError):
            shuffle.prove(self.result['body'], shuffle.ADDRESS, rom, mapping, index, objects, bad)

        addend = dict(bindings, data=[[0x7C, 'data_0836D4BC', 4], bindings['data'][1]])
        with self.assertRaises(ValueError):
            shuffle.prove(self.result['body'], shuffle.ADDRESS, rom, mapping, index, objects, addend)
        counts = index.replace(b'08132064 081320E8   132  57', b'08132064 081320E8   132  66')
        self.assertNotEqual(counts, index)
        with self.assertRaises(ValueError):
            shuffle.prove(self.result['body'], shuffle.ADDRESS, rom, mapping, counts, objects, bindings)
        remapped = objects.replace(b'0x030034B0', b'0x030034B4')
        with self.assertRaises(ValueError):
            shuffle.prove(self.result['body'], shuffle.ADDRESS, rom, mapping, index, remapped, bindings)
