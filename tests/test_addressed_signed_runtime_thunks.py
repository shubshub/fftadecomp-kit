"""Real agbcc: explicit signed runtimes composed with canonical _call_via_rN thunks.

Each caller is compiled by the fixed agbcc and linked by the selector's own
linker step.  The ROM is synthetic: the signed runtime spans are synthetic
bytes whose identity digests are patched in this process only, as in the
other addressed-runtime tests, and every thunk is the canonical `bx rN; nop`.
"""
import argparse
import copy
from contextlib import redirect_stdout
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import struct
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import report_fixtures
import match_evidence as evidence
import owner_admission_profile as owner
import owner_graph_profile as graph
import status
import addressed_signed_runtime_profile as profile

A, B = 0x08010000, 0x08011000
THUNKS, THUNKS_DATA = profile.THUNKS_SELECTOR, profile.THUNKS_DATA_SELECTOR
R2, R3 = (match.function_thunk.ALIASES[f'_call_via_r{n}'] for n in (2, 3))
OBJECTS = {'data_02001000': '0x02001000', 'data_02001004': '0x02001004', 'data_02001100': '0x02001100'}
TOOLS = Path(os.path.expandvars(match.DEFAULT_CC)).is_file() and all(
    shutil.which(tool) for tool in ('cpp', 'arm-none-eabi-as', 'arm-none-eabi-ld', 'arm-none-eabi-objcopy'))

# A callback read from a field of the incoming record, called through r2.
FIELD = '''typedef unsigned char u8;
typedef unsigned short u16;
typedef int s32;
typedef unsigned int u32;
typedef u8 (*RowPicker)(void *context, u16 line);
typedef struct {
    RowPicker pick;
    void *context;
    u16 *rows;
    u16 first;
    u8 count;
    u8 stride;
} Region;
s32 func_08142950(s32 numerator, s32 denominator);
void func_08011000(u16 *row, u32 control);

void func_08010000(Region *region, s32 start)
{
    u16 i;

    for (i = 0; i < 2; i++) {
        u16 line = func_08142950(region->first + start + i, region->count);
        u16 *row = region->rows + line * region->stride;

        func_08011000(row, region->stride);
        if (region->pick)
            row[0] = (row[0] & 0xFFF) | (CALL << 12);
    }
}
'''
CALLBACK = 'region->pick(region->context, line)'

# Two callback tables (r2 and r3 thunks), typed data and a body long
# enough that agbcc jumps with same-owner `bl` instructions.
TABLE = '''typedef unsigned char u8;
typedef int s32;
typedef unsigned int u32;
typedef void (*Clear)(void *destination, u32 size);
typedef void (*Copy)(void *destination, const void *source, u32 size);
typedef struct {
    s32 weight;
    s32 values[48];
} Record;
extern Clear data_02001000[];
extern Copy data_02001004[];
extern const u8 data_02001100[];
s32 func_08142950(s32 numerator, s32 denominator);

void func_08010000(Record *record, s32 count)
{
    s32 i;

    for (i = 0; i < count; i++) {
        if (func_08142950(i, 3) == 0) {
            data_02001000[0](record, sizeof(record->values));
            continue;
        }
%s
        data_02001004[0](record->values, data_02001100, func_08142950(count, i + 1));
    }
}
''' % '\n'.join(f'        record->values[{k % 48}] += {k & 7} + record->weight;' for k in range(240))


def bl(site, target):
    delta = target - site - 4
    return struct.pack('<HH', 0xF000 | ((delta >> 12) & 0x7FF), 0xF800 | ((delta >> 1) & 0x7FF))


def index_text(rows):
    return ''.join(f'{int(r["rom"], 16):08X} {int(r["end"], 16):08X} '
                   f'{int(r["end"], 16)-int(r["rom"], 16)} {r["instrs"]} return\n' for r in rows)


def assemble(items):
    """Halfwords, ('call', target), ('label', name) and ('beq'|'bne'|'b', name) as Thumb bytes."""
    labels, offset = {}, 0
    for item in items:
        if type(item) is tuple and item[0] == 'label':
            labels[item[1]] = offset
        else:
            offset += 4 if type(item) is tuple and item[0] == 'call' else 2
    body, calls = bytearray(), {}
    for item in items:
        site = A + len(body)
        if type(item) is int:
            body += struct.pack('<H', item)
        elif item[0] == 'call':
            calls[site] = item[1]
            body += bl(site, item[1])
        elif item[0] != 'label':
            delta = (labels[item[1]] - len(body) - 4) // 2
            opcode = 0xE000 | delta & 0x7FF if item[0] == 'b' else \
                {'beq': 0xD000, 'bne': 0xD100}[item[0]] | delta & 0xFF
            body += struct.pack('<H', opcode)
    return bytes(body), calls


def synthetic_rom():
    rom = bytearray(0x143000)
    rom[0x14274C:0x14274E] = bytes.fromhex('7047')
    rom[0x142742:0x142746] = bl(0x08142742, 0x0814274C)
    rom[0x142A16:0x142A1A] = bl(0x08142A16, 0x0814274C)
    for register in (2, 3):
        struct.pack_into('<HH', rom, match.function_thunk.ALIASES[f'_call_via_r{register}'] - match.ROM_BASE,
                         0x4700 | register << 3, 0x46C0)
    rom[B-match.ROM_BASE:B-match.ROM_BASE+2] = bytes.fromhex('7047')
    return rom


class TargetRuleTests(unittest.TestCase):
    """The target rule over small hand-encoded bodies; no compiler needed."""

    THUNK = {register: match.function_thunk.ALIASES[f'_call_via_r{register}'] for register in (0, 1, 2, 3, 12)}

    def loads(self, items):
        data, calls = assemble([0xB530, *items, 0xBC30, 0xBC01, 0x4700])   # push {r4, r5, lr} ... return
        rows = [dict(rom=f'0x{A:08X}', end=f'0x{A+len(data):08X}', mode='thumb', instrs=0),
                dict(rom=f'0x{B:08X}', end=f'0x{B+2:08X}', mode='thumb', instrs=1),
                *(dict(rom=f'0x{t:08X}', end=f'0x{t+2:08X}', mode='thumb', instrs=1) for t in self.THUNK.values())]
        instructions, edges, _, actual, _ = graph.graph(data, A, owner.refine(data, A, json.dumps(rows).encode()))
        self.assertEqual(actual, calls)
        return profile.thunk_target_loads(instructions, edges, actual, A)

    def refused(self, items):
        with self.assertRaisesRegex(ValueError, 'memory word load on every path'):
            self.loads(items)

    def test_a_join_needs_a_load_on_both_paths_in_either_order(self):
        # cmp r0, #0; beq; one side ldr r3, [r4], the other movs r3, #1; then the r3 thunk.
        for first, second in ((0x6823, 0x2301), (0x2301, 0x6823)):
            with self.subTest(fallthrough=hex(first)):
                self.refused([0x2800, ('beq', 'other'), first, ('b', 'call'), ('label', 'other'), second,
                              ('label', 'call'), ('call', R3)])
        (row,) = self.loads([0x2800, ('beq', 'other'), 0x6823, ('b', 'call'), ('label', 'other'), 0x6823,
                             ('label', 'call'), ('call', R3)])
        self.assertEqual(len(row[2]), 2, 'both loads reach the call')

    def test_a_loop_back_edge_brings_the_clobbered_target(self):
        # ldr r3, [r4]; top: bl _call_via_r3; subs r5, #1; bne top
        self.refused([0x6823, ('label', 'top'), ('call', R3), 0x3D01, ('bne', 'top')])
        self.loads([('label', 'top'), 0x6823, ('call', R3), 0x3D01, ('bne', 'top')])

    def test_every_call_clobbers_each_argument_register_target(self):
        for register in range(4):
            with self.subTest(register=register):
                self.loads([0x6820 | register, ('call', self.THUNK[register])])
                self.refused([0x6820 | register, ('call', B), ('call', self.THUNK[register])])
        # ldr r3, [r4]; ldr r2, [r5]; bl _call_via_r2; bl _call_via_r3: the first thunk call clobbers r3.
        self.refused([0x6823, 0x682A, ('call', R2), ('call', R3)])
        self.loads([0x682A, ('call', R2), 0x6823, ('call', R3)])

    def test_a_copy_of_a_loaded_register_is_not_a_load(self):
        self.refused([0x682C, 0x1C22, ('call', R2)])                   # ldr r4, [r5]; adds r2, r4, #0
        # A Thumb ldr cannot write r8-r12, so a high-register target is always a copy.
        self.refused([0x6823, 0x469C, ('call', self.THUNK[12])])       # ldr r3, [r4]; mov r12, r3


@unittest.skipUnless(TOOLS, 'fixed compiler and binutils required')
class SignedRuntimeThunkTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.rom = synthetic_rom()
        cls.patches = []
        for module in (profile.quotient, profile.remainder):
            ids = tuple((lo, hi, hashlib.sha256(cls.rom[lo-match.ROM_BASE:hi-match.ROM_BASE]).hexdigest())
                        for lo, hi, _ in module.IDENTITIES)
            cls.patches.append(patch.object(module, 'IDENTITIES', ids))
        for change in cls.patches:
            change.start()
        cls.scratch = tempfile.TemporaryDirectory(prefix='signed_thunks_')
        cls.args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
            objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        cls.field = cls.make_root('field', FIELD.replace('CALL', CALLBACK), THUNKS)
        cls.table = cls.make_root('table', TABLE, THUNKS_DATA)

    @classmethod
    def tearDownClass(cls):
        for change in reversed(cls.patches):
            change.stop()
        cls.scratch.cleanup()

    @classmethod
    def make_root(cls, name, source, selector):
        """Compile, link with the selector's own linker step, and place the bytes in a synthetic ROM."""
        root = Path(tempfile.mkdtemp(prefix=name + '_', dir=cls.scratch.name))
        for sub in ('src', 'include', 'build', 'config', 'symbols', 'docs/match'):
            (root/sub).mkdir(parents=True)
        (root/'src/08010000.c').write_text(source)
        objects = json.dumps(OBJECTS).encode()
        (root/'config/data_symbols.json').write_bytes(objects)
        rom = bytearray(cls.rom)
        runner = match.Runner(match.DEFAULT_CC, 'Ubuntu', match.DEFAULT_WSL_PATH, root=root, timeout=120)
        with runner.workspace() as workspace:
            _, _, image = match.compile_object(runner, workspace, cls.args, root, A, 'src/08010000.c')
            size = match.function_record(image, f'func_{A:08X}', A, True)[0]['size']
            rows = [dict(rom=f'0x{A:08X}', end=f'0x{A+size:08X}', mode='thumb', instrs=0),
                    dict(rom=f'0x{B:08X}', end=f'0x{B+2:08X}', mode='thumb', instrs=1),
                    *(dict(rom=f'0x{t:08X}', end=f'0x{t+2:08X}', mode='thumb', instrs=1) for t in (R2, R3)),
                    *(dict(rom=f'0x{lo:08X}', end=f'0x{hi:08X}', mode='thumb', instrs=(hi-lo)//2)
                      for lo, hi, _ in sorted(set(profile.quotient.IDENTITIES + profile.remainder.IDENTITIES)))]
            body = profile.object_bytes(runner, workspace, cls.args, image, A, bytes(rom),
                json.dumps(rows).encode(), selector=selector, data_mapping=objects)[0]
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)] = body
        rows[0]['instrs'] = owner.refine(body, A, json.dumps(rows).encode())['instrs']
        (root/'config/functions.json').write_text(json.dumps(rows))
        (root/'symbols/functions.txt').write_text(index_text(rows))
        (root/'baserom.bin').write_bytes(rom)
        return root

    def build(self, root, selector):
        with patch.dict(os.environ, FFTA_ROM=str(root/'baserom.bin')):
            return profile.build(root, A, selector=selector)

    def inputs(self, root, selector):
        """The fresh verify() inputs that build() derives for this root."""
        result = self.build(root, selector)
        mapping = (root/'config/functions.json').read_bytes()
        calls = {A+offset: (profile.OPERATIONS.get(name) or match.function_thunk.ALIASES.get(name)
                            or int(name[5:], 16)) for offset, name in result['manifest']['calls']}
        values = dict(data=result['body'], address=A, rom=(root/'baserom.bin').read_bytes(), mapping=mapping,
                      index=(root/'symbols/functions.txt').read_bytes(), calls=calls,
                      bindings={A+offset: name for offset, name in result['manifest']['calls']
                                if name in profile.OPERATIONS})
        if selector in profile.DATA_SELECTORS:
            values.update(data_mapping=(root/'config/data_symbols.json').read_bytes(),
                          data_bindings=result['manifest']['data_bindings'])
        return result, values

    def patched(self, values, offset, halfword):
        data = bytearray(values['data'])
        struct.pack_into('<H', data, offset, halfword)
        rom = bytearray(values['rom'])
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)] = data
        return dict(values, data=bytes(data), rom=bytes(rom))

    def copy_root(self, root):
        destination = Path(tempfile.mkdtemp(prefix='copy_', dir=self.scratch.name))
        shutil.copytree(root, destination, dirs_exist_ok=True)
        return destination

    # Positive compositions ---------------------------------------------

    def test_record_field_callback_cli_report_replay_and_status(self):
        root = self.copy_root(self.field)
        with patch.dict(os.environ, FFTA_ROM=str(root/'baserom.bin')), \
                patch.object(sys, 'argv', ['match.py', '--root', str(root),
                             '--addressed-signed-runtime-profile', THUNKS, f'0x{A:08X}']), \
                redirect_stdout(io.StringIO()) as output:
            self.assertEqual(match.main(), 0)
        self.assertIn('verdict MATCH - byte identical', output.getvalue())
        report = (root/'docs/match/08010000.md').read_text()
        self.assertEqual(profile.selector_for_report(report), THUNKS)
        self.assertIn('* canonical thunk callee ABI: ', report)
        manifest = json.loads(report.split('* addressed signed runtime evidence: `')[1].split('`')[0])['manifest']
        self.assertEqual(manifest['schema'], profile.THUNKS_SCHEMA)
        (site, alias, loads), = manifest['thunks']['sites']
        self.assertEqual(alias, '_call_via_r2')
        data = (root/'baserom.bin').read_bytes()[A-match.ROM_BASE:]
        load = struct.unpack_from('<H', data, loads[0])[0]
        self.assertEqual(load & 0xF807, 0x6802, 'the target is ldr r2, [rB, #imm]')
        self.assertEqual(manifest['thunks']['dependencies'][0][:3], ['_call_via_r2', R2, R2+4])
        self.assertEqual(manifest['thunks']['target_policy'], profile.THUNK_TARGET_POLICY)
        self.assertIsNone(manifest['local_long_branches'])
        self.assertIn([site, '_call_via_r2'], manifest['calls'])
        self.assertIn('unsigned_thunk_profile.py', manifest['producer_source_sha256'])
        with patch.dict(os.environ, FFTA_ROM=str(root/'baserom.bin')):
            self.assertTrue(evidence.report_matches(report, root, A))
            self.assertEqual(status.collect(str(root), verify=False)[1], 1)
            forged = report.replace(profile.THUNKS_SCHEMA, profile.R3_CALLBACK_SCHEMA)
            self.assertFalse(evidence.report_matches(forged, root, A))
            (root/'src/08010000.c').write_text(FIELD.replace('CALL', CALLBACK) + '\n')
            self.assertFalse(evidence.report_matches(report, root, A))

    def test_two_thunk_registers_typed_data_and_local_long_branches(self):
        result, values = self.inputs(self.table, THUNKS_DATA)
        manifest = result['manifest']
        self.assertEqual(manifest['schema'], profile.THUNKS_DATA_SCHEMA)
        self.assertEqual(sorted({alias for _, alias, _ in manifest['thunks']['sites']}),
                         ['_call_via_r2', '_call_via_r3'])
        self.assertEqual(sorted(name for _, name, _ in manifest['data_bindings']), sorted(OBJECTS))
        self.assertGreaterEqual(len(manifest['local_long_branches']['edges']), 1)
        self.assertEqual(manifest['frame']['schema'], 'thumb-same-owner-long-bl-restoring-frame-v1')
        self.assertEqual(profile.verify(**values, manifest=manifest, selector=THUNKS_DATA)[0], manifest)
        with patch.dict(os.environ, FFTA_ROM=str(self.table/'baserom.bin')):
            self.assertTrue(evidence.report_matches(report_fixtures.carried(profile.render(result), self.table, A), self.table, A))

    # Existing selectors keep their boundaries ---------------------------

    def test_existing_selectors_still_refuse_both_shapes(self):
        for root, selector in ((self.field, profile.SELECTOR), (self.field, profile.DATA_SELECTOR),
                               (self.field, profile.CALLBACK_SELECTOR), (self.field, profile.R3_CALLBACK_SELECTOR),
                               (self.field, THUNKS_DATA),
                               (self.table, profile.DATA_SELECTOR), (self.table, profile.R3_CALLBACK_SELECTOR),
                               (self.table, profile.CALLBACK_SELECTOR), (self.table, THUNKS)):
            with self.subTest(root=root.name, selector=selector), self.assertRaises(ValueError):
                self.build(root, selector)

    def test_local_long_branches_stay_closed_to_other_addressed_selectors(self):
        # The same long body without callbacks: only the far jumps remain new.
        source = TABLE.replace('data_02001000[0](record, sizeof(record->values));',
                               'record->weight = data_02001100[0];').replace(
            'data_02001004[0](record->values, data_02001100, func_08142950(count, i + 1));',
            'record->weight += func_08142950(count, i + 1) + data_02001100[1];')
        root = self.make_root('branches', source, profile.DATA_SELECTOR)
        mapping = (root/'config/functions.json').read_bytes()
        end = int(json.loads(mapping)[0]['end'], 16)
        data = (root/'baserom.bin').read_bytes()[A-match.ROM_BASE:end-match.ROM_BASE]
        instructions = graph.graph(data, A, owner.refine(data, A, mapping))[0]
        import local_long_branch_profile as frame
        self.assertTrue(frame.record(instructions.values(), A)['edges'])
        with self.assertRaisesRegex(ValueError, 'validated external direct Thumb BL'):
            self.build(root, profile.DATA_SELECTOR)
        with self.assertRaisesRegex(ValueError, 'actual compiler-emitted canonical thunk call'):
            self.build(root, THUNKS_DATA)

    # Thunk target and identity mutants -----------------------------------

    def test_target_must_be_a_memory_word_load_on_every_path(self):
        result, values = self.inputs(self.field, THUNKS)
        (site, _, (load,)), = result['manifest']['thunks']['sites']
        base = (struct.unpack_from('<H', values['data'], load)[0] >> 3) & 7
        pool = next(offset for offset in range(len(values['data'])-4, 0, -2) if (A+offset) % 4 == 0)
        literal = (pool - ((load + 4) & ~3)) // 4
        mutants = {'constant': 0x2201,                       # movs r2, #1
                   'literal': 0x4A00 | literal,              # ldr r2, [pc, #...]
                   'stack word': 0x9A00,                     # ldr r2, [sp]
                   'entry return': 0x4672,                   # mov r2, lr
                   'copy': 0x1C02 | base << 3,               # adds r2, rB, #0
                   'halfword': 0x8802 | base << 3,           # ldrh r2, [rB]
                   'byte': 0x7802 | base << 3}               # ldrb r2, [rB]
        for name, halfword in mutants.items():
            with self.subTest(mutant=name), self.assertRaises(ValueError):
                profile.verify(**self.patched(values, load, halfword), selector=THUNKS)
        # The load stays, but the target register is rewritten just before the call.
        self.assertLess(load, site - 2)
        with self.assertRaisesRegex(ValueError, 'memory word load on every path'):
            profile.verify(**self.patched(values, site - 2, 0x2201), selector=THUNKS)
        instructions, edges, _, calls, _ = graph.graph(values['data'], A, owner.refine(values['data'], A, values['mapping']))
        self.assertEqual(profile.thunk_target_loads(instructions, edges, calls, A)[0][2], [load])
        joined = dict(edges); joined[A] = (*edges[A], A+site)
        with self.assertRaisesRegex(ValueError, 'memory word load on every path'):
            profile.thunk_target_loads(instructions, joined, calls, A)
        between = next(address for address in sorted(instructions) if A+load < address < A+site)
        with self.assertRaisesRegex(ValueError, 'memory word load on every path'):
            profile.thunk_target_loads(instructions, edges, {**calls, between: B}, A)

    def test_thunk_body_owner_and_changed_bytes(self):
        _, values = self.inputs(self.field, THUNKS)
        changes = {'r3 body in the r2 slot': (R2, struct.pack('<HH', 0x4718, 0x46C0)),
                   'no padding': (R2, struct.pack('<HH', 0x4710, 0x0000)),
                   'remainder runtime byte': (profile.remainder.ADDRESS, b'\x01')}
        for name, (location, patch_bytes) in changes.items():
            rom = bytearray(values['rom']); rom[location-match.ROM_BASE:location-match.ROM_BASE+len(patch_bytes)] = patch_bytes
            with self.subTest(change=name), self.assertRaises(ValueError):
                profile.verify(**dict(values, rom=bytes(rom)), selector=THUNKS)
        rows = [row for row in json.loads(values['mapping']) if int(row['rom'], 16) != R2]
        with self.assertRaises(ValueError):
            profile.verify(**dict(values, mapping=json.dumps(rows).encode(), index=index_text(rows).encode()),
                           selector=THUNKS)
        # Still an indexed entry, so the CFG closes, but no longer the thunk's exact two-byte owner.
        rows = [dict(row, end=f'0x{R2+4:08X}', instrs=2) if int(row['rom'], 16) == R2 else row
                for row in json.loads(values['mapping'])]
        with self.assertRaisesRegex(ValueError, 'exact unique nonoverlapping Thumb span'):
            profile.verify(**dict(values, mapping=json.dumps(rows).encode(), index=index_text(rows).encode()),
                           selector=THUNKS)
        root = self.copy_root(self.field)
        rom = bytearray((root/'baserom.bin').read_bytes()); rom[A-match.ROM_BASE+6] ^= 1
        (root/'baserom.bin').write_bytes(rom)
        with self.assertRaises(ValueError):
            self.build(root, THUNKS)

    def test_every_thunk_owner_is_pinned_not_only_the_first(self):
        _, values = self.inputs(self.table, THUNKS_DATA)
        for register, target in (('r2', R2), ('r3', R3)):
            widened = [dict(row, end=f'0x{target+4:08X}', instrs=2) if int(row['rom'], 16) == target else row
                       for row in json.loads(values['mapping'])]
            removed = [row for row in json.loads(values['mapping']) if int(row['rom'], 16) != target]
            with self.subTest(widened=register), \
                    self.assertRaisesRegex(ValueError, 'exact unique nonoverlapping Thumb span'):
                profile.verify(**dict(values, mapping=json.dumps(widened).encode(),
                                      index=index_text(widened).encode()), selector=THUNKS_DATA)
            with self.subTest(removed=register), self.assertRaises(ValueError):
                profile.verify(**dict(values, mapping=json.dumps(removed).encode(),
                                      index=index_text(removed).encode()), selector=THUNKS_DATA)

    def test_a_different_runtime_is_refused(self):
        _, values = self.inputs(self.field, THUNKS)
        site = next(site for site, name in values['bindings'].items() if name == 'func_08142950')
        data = bytearray(values['data']); data[site-A:site-A+4] = bl(site, 0x08142B28)
        rom = bytearray(values['rom']); rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)] = data
        for bindings in ({**values['bindings'], site: 'func_08142B28'}, values['bindings']):
            with self.subTest(bindings=bindings[site]), self.assertRaises(ValueError):
                profile.verify(**dict(values, data=bytes(data), rom=bytes(rom),
                                      calls={**values['calls'], site: 0x08142B28}, bindings=bindings),
                               selector=THUNKS)
        with self.assertRaisesRegex(ValueError, 'canonical addressed function'):
            self.make_root('modulo', FIELD.replace('CALL', CALLBACK).replace(
                'func_08142950(region->first + start + i, region->count)',
                '(s32)(region->first + start + i) % region->count'), THUNKS)

    # Source mutants through the real compiler ---------------------------

    def test_stack_alias_reaching_a_callback_is_refused(self):
        root = self.make_root('alias', FIELD.replace('CALL', 'region->pick(&line, line)'), THUNKS)
        with self.assertRaisesRegex(ValueError, 'stack aliases cannot cross calls'):
            self.build(root, THUNKS)

    def test_reserved_spellings_and_missing_compositions(self):
        label = FIELD.replace('void func_08011000', 'extern u8 pick_row(void *, u16) __asm("_call_via_r2");\n'
                              'void func_08011000').replace('CALL', 'pick_row(region->context, line)')
        with self.assertRaisesRegex(ValueError, 'reserve runtime, call-via'):
            self.make_root('label', label, THUNKS)
        with self.assertRaisesRegex(ValueError, 'actual compiler-emitted canonical thunk call'):
            self.make_root('direct', FIELD.replace('CALL', 'line'), THUNKS)
        with self.assertRaisesRegex(ValueError, 'actual addressed calls'):
            self.make_root('plain', FIELD.replace('CALL', CALLBACK).replace(
                'func_08142950(region->first + start + i, region->count)', 'region->first + start + i'), THUNKS)

    def test_fresh_manifest_tampering_is_refused(self):
        result, values = self.inputs(self.table, THUNKS_DATA)
        manifest = result['manifest']
        for change in ('load', 'alias', 'dependency', 'policy', 'branch', 'producer'):
            bad = copy.deepcopy(manifest)
            if change == 'load': bad['thunks']['sites'][0][2] = [bad['thunks']['sites'][0][2][0] + 2]
            elif change == 'alias': bad['thunks']['sites'][0][1] = '_call_via_r1'
            elif change == 'dependency': bad['thunks']['dependencies'][0][3] = '0' * 64
            elif change == 'policy': bad['thunks']['target_policy'] = 'any-target'
            elif change == 'branch': bad['local_long_branches']['edges'][0][1] += 2
            else: bad['producer_source_sha256']['unsigned_thunk_profile.py'] = '0' * 64
            with self.subTest(change=change), self.assertRaises(ValueError):
                profile.verify(**values, manifest=bad, selector=THUNKS_DATA)


if __name__ == '__main__':
    unittest.main()
