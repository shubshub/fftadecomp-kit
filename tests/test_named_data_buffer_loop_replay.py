"""Bounded loop replay (#153) in the explicit named-data buffer proof.

`named-data-buffer-v1` constructs the exact `NamedDataBufferProof` with
`loop_replay=True`; every subclass keeps the join refusal. The proof's own
ledgers (`requested`, the dependency budget, and `records`, the manifest's
dependency list) are restored when a joined pass aborts, so a callee that only
an aborted pass inspected neither appears in the evidence nor consumes budget.
"""
import copy
import json
import os
from pathlib import Path
import shutil
import struct
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import match
import report_fixtures
import match_evidence
import named_data_buffer_profile as named
import owner_admission_profile as owner
from test_buffer_loop_replay import counted

BASE = match.ROM_BASE
RET = "add sp, #{frame}\npop {{r4}}\npop {{r0}}\nbx r0"
# The joined pass reaches `bl extra` (it explores both sides of `bne`) and then
# aborts at the loop head; the replay knows r5 is 0 or 1, so `bne` is always
# taken and `extra` is never reached.
PRUNED_EXTRA = ("push {r4, r5, r6, lr}\nadds r6, r1, #0\nmovs r1, #0\nmovs r5, #0\nloop:\n"
                "cmp r5, #5\nbne skip\nadds r1, r6, #0\nbl extra\nmovs r1, #0\nskip:\n"
                "strh r0, [r6]\nadds r6, #2\nadds r5, #1\ncmp r5, #1\nble loop\n"
                "pop {r4, r5, r6}\npop {r1}\nbx r1")
LEAF = "strh r0, [r1]\nmovs r1, #0\nbx lr"


def root(frame, *callees):
    calls = "".join(f"mov r1, sp\nmovs r0, #0\nbl {name}\n" for name in callees)
    return f"push {{r4, lr}}\nsub sp, #{frame}\n{calls}" + RET.format(frame=frame)


class AssemblyTests(unittest.TestCase):
    """The real `span`/`inspect` hooks over assembled ROM spans and both indexes."""

    def setUp(self):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="named_buffer_replay_", dir=scratch)
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)

    def assemble(self, functions):
        """functions: [(name, body)], the first is the root; each at a 0x100 boundary."""
        source = ".syntax unified\n.arch armv5t\n.thumb\n.text\n" + "".join(
            f".global {name}, {name}_end\n" for name, _ in functions) + "".join(
            f".org 0x{0x100 * index:x}\n{name}:\n{body}\n{name}_end:\n"
            for index, (name, body) in enumerate(functions))
        (self.root / "fixture.s").write_text(source)
        for command in (
            ["arm-none-eabi-as", "-mthumb-interwork", str(self.root / "fixture.s"),
             "-o", str(self.root / "fixture.o")],
            ["arm-none-eabi-ld", "-Ttext=0x08000000", "-e", functions[0][0],
             str(self.root / "fixture.o"), "-o", str(self.root / "fixture.elf")],
            ["arm-none-eabi-objcopy", "-O", "binary", "--only-section=.text",
             str(self.root / "fixture.elf"), str(self.root / "fixture.bin")],
        ):
            subprocess.run(command, check=True, capture_output=True)
        image = match.elf_image((self.root / "fixture.elf").read_bytes())
        symbols = {symbol["name"]: symbol["value"] for symbol in image["symbols"]}
        spans = [(symbols[name], symbols[name + "_end"]) for name, _ in functions]
        mapping = json.dumps([{"rom": f"0x{start:08X}", "end": f"0x{end:08X}", "mode": "thumb",
                               "instrs": 0} for start, end in spans]).encode()
        index = "".join(f"{start:08X} {end:08X} {end - start} 0 return\n"
                        for start, end in spans).encode()
        rom = (self.root / "fixture.bin").read_bytes()
        return rom, mapping, index, rom[:spans[0][1] - BASE]

    def run_proof(self, functions, proof_type=named.NamedDataBufferProof, budget=None, **options):
        rom, mapping, index, body = self.assemble(functions)
        proof = proof_type(rom, mapping, index, None, **options)
        if budget is not None:
            proof.dependency_budget = budget
        match.verify_leaf_instructions(body, BASE, True, buffer_proof=proof,
                                       call_resolver=proof.target)
        return proof

    def test_counted_loop_over_a_large_enough_local_is_replayed_and_recorded(self):
        proof = self.run_proof([("caller", root(8, "callee")), ("callee", counted(4)),
                                ("child", "bx lr")], loop_replay=True)
        self.assertEqual(set(proof.loop_replays), {BASE + 0x100})
        self.assertEqual(set(proof.records), {BASE + 0x100})
        self.assertEqual(proof.requested, set(proof.records))
        self.assertEqual(set(proof.dependencies), set(proof.records))
        record = proof.loop_replay_manifest()
        self.assertEqual(record["schema"], "bounded-loop-replay-v2")
        self.assertEqual(record["buffer_proof_sha256"], proof.fingerprint())
        self.assertEqual(record["lines"], proof.loop_replay_lines())
        self.assertIn("premise, not checked: named objects do not overlap any live stack", record["premise"])
        (line,) = record["lines"]
        self.assertRegex(line, r"^\* buffer loop replay: `bounded-loop-replay-v2` callee 0x08000100 "
                               r"sites 0x[0-9A-F]{8} writes sp\+0:2 sp\+2:2 sp\+4:2 sp\+6:2; "
                               r"proved none; trusted 0x08000200:r5; pruned edges \d+$")

    def test_too_small_local_refuses_at_the_exact_store(self):
        with self.assertRaisesRegex(ValueError, r"^buffer callee 0x08000100: bounded loop replay at "
                                    r"0x[0-9A-F]{8}: 2-byte strh at caller sp\+4: buffer access is "
                                    r"unaligned or outside allocated local words$"):
            self.run_proof([("caller", root(4, "callee")), ("callee", counted(4)),
                            ("child", "bx lr")], loop_replay=True)

    def test_without_the_constructor_argument_the_join_still_refuses(self):
        with self.assertRaisesRegex(ValueError, "inconsistent possible pointer offsets at control-flow join"):
            self.run_proof([("caller", root(8, "callee")), ("callee", counted(4)),
                            ("child", "bx lr")])

    def test_subclasses_do_not_replay(self):
        class Subclass(named.NamedDataBufferProof):
            pass
        functions = [("caller", root(8, "callee")), ("callee", counted(4)), ("child", "bx lr")]
        with self.assertRaisesRegex(ValueError, "inconsistent possible pointer offsets at control-flow join"):
            self.run_proof(functions, proof_type=Subclass, loop_replay=True)
        # Every loaded subclass, given the constructor argument, stays ineligible.
        import importlib
        for path in sorted((ROOT / "tools").glob("*.py")):
            importlib.import_module(path.stem)
        pending, classes = list(named.NamedDataBufferProof.__subclasses__()), set()
        while pending:
            cls = pending.pop()
            if cls not in classes:
                classes.add(cls)
                pending.extend(cls.__subclasses__())
        self.assertGreater(len(classes), 20)
        rom, mapping, index, _ = self.assemble(functions)
        for cls in sorted(classes, key=lambda cls: cls.__qualname__):
            with self.subTest(cls=cls.__qualname__):
                proof = cls.__new__(cls)
                named.NamedDataBufferProof.__init__(proof, rom, mapping, index, None, loop_replay=True)
                self.assertTrue(proof.loop_replay)
                self.assertFalse(proof.loop_replay_eligible())
        exact = named.NamedDataBufferProof(rom, mapping, index, None, loop_replay=True)
        self.assertTrue(exact.loop_replay_eligible())

    def test_an_aborted_joined_pass_leaves_no_ledger_entry(self):
        functions = [("caller", root(8, "callee", "after")), ("callee", PRUNED_EXTRA),
                     ("extra", "bx lr"), ("after", LEAF)]
        callee, extra, after = BASE + 0x100, BASE + 0x200, BASE + 0x300
        # Without the restore, the aborted pass's inspection of `extra` survives.
        with patch.object(named.NamedDataBufferProof, "_check_arguments",
                          match.BufferCallProof._check_arguments):
            leaked = self.run_proof(functions, loop_replay=True)
        self.assertIn(extra, leaked.records)
        self.assertIn(extra, leaked.requested)
        proof = self.run_proof(functions, loop_replay=True)
        self.assertEqual(set(proof.loop_replays), {callee})
        manifest = [proof.records[target] for target in sorted(proof.records)]
        self.assertEqual([row["address"] for row in manifest], [callee, after])
        self.assertEqual(proof.requested, {callee, after})
        self.assertEqual(set(proof.dependencies), {callee, after})
        # The budget is charged only for the final proof's callees.
        self.run_proof(functions, budget=2, loop_replay=True)
        with patch.object(named.NamedDataBufferProof, "_check_arguments",
                          match.BufferCallProof._check_arguments), \
                self.assertRaisesRegex(ValueError, "dependency budget exceeded"):
            self.run_proof(functions, budget=2, loop_replay=True)
        with self.assertRaisesRegex(ValueError, "dependency budget exceeded"):
            self.run_proof(functions, budget=1, loop_replay=True)

    def test_records_of_earlier_calls_survive_a_later_aborted_pass(self):
        # `after` is recorded first; the aborted pass of the second call must
        # restore to that state, not to an empty ledger.
        functions = [("caller", root(8, "after", "callee")), ("callee", PRUNED_EXTRA),
                     ("extra", "bx lr"), ("after", LEAF)]
        proof = self.run_proof(functions, loop_replay=True)
        self.assertEqual(set(proof.records), {BASE + 0x100, BASE + 0x300})
        self.assertEqual(proof.requested, set(proof.records))


class SelectionTests(unittest.TestCase):
    def test_only_the_named_schema_carries_exact_replay_lines(self):
        line = ('* buffer loop replay: `bounded-loop-replay-v2` callee 0x08000400 sites 0x08000208 '
                'writes sp+0:2; proved none; trusted none; pruned edges 1\n')
        marker = f'* verification: `{named.SCHEMA}`\n'
        self.assertTrue(owner.selected(marker + line))
        self.assertEqual(owner.selector_for_report(marker + line), named.SELECTOR)
        for report in (marker + ' ' + line, marker + '\t' + line, marker + line.replace('-v2', '-v1'),
                       marker + '* buffer loop replay: x\n', marker + line + '* buffer calls: legacy\n',
                       f'* verification: `{named.DATAFREE_SCHEMA}`\n' + line,
                       f'* verification: `{named.SCRATCH_SCHEMA}`\n' + line,
                       f'* verification: `{owner.ACYCLIC_SCHEMA}`\n' + line):
            with self.subTest(report=report), self.assertRaises(ValueError):
                owner.selected(report)


SOURCE = '''extern unsigned char data_02000000[4];
extern void func_08000400(unsigned short *out);
unsigned int func_08000200(unsigned int k)
{
    unsigned short entries[%d];
    func_08000400(entries);
    return entries[0] + data_02000000[k & 3];
}
'''
# `i == 5` never holds: the replay prunes the call to func_08000700, which the
# joined pass inspects (it receives `out`) before it aborts at the loop.
CALLEE = '''extern int func_08000600(int i);
extern void func_08000700(unsigned short *out);
void func_08000400(unsigned short *out)
{
    int i;
    for (i = 0; i < 4; i++) {
        if (i == 5)
            func_08000700(out);
        if (func_08000600(i))
            *out++ = i;
    }
}
'''
CHILD = 'int func_08000600(int i) { return i & 1; }\n'
EXTRA = 'void func_08000700(unsigned short *out) { }\n'
# The same caller with a callee whose stores need no replay.
STRAIGHT = 'void func_08000400(unsigned short *out) { out[0] = 1; out[3] = 2; }\n'
A, B, C, D = 0x08000200, 0x08000400, 0x08000600, 0x08000700


def native_fixture(root, entries, callee=CALLEE):
    """Natural C: a typed-data caller, a looping buffer callee, its scalar child and
    a buffer callee reached only on a path the replay prunes."""
    import argparse
    root = Path(root)
    for name in ('src', 'include', 'config', 'symbols', 'build'):
        (root / name).mkdir(parents=True, exist_ok=True)
    args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP,
        assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD,
        flags=match.DEFAULT_FLAGS)
    objects = b'{"data_02000000":"0x02000000"}\n'
    runner = match.Runner(match.DEFAULT_CC, 'Ubuntu', match.DEFAULT_WSL_PATH, root=root, timeout=120)
    rom = bytearray(D - match.ROM_BASE + 0x100)
    with runner.workspace() as workspace:
        bodies = {}
        for address, text in ((B, callee), (C, CHILD), (D, EXTRA)):
            path = root / f'src/{address:08X}.c'
            path.write_text(text)
            _, body, image = match.compile_object(runner, workspace, args, root, address,
                                                  f'src/{address:08X}.c')
            path.unlink()
            # The callee's only relocations are its two BLs.
            body = bytearray(body)
            for section_id in image['relocations']:
                section = image['sections'][section_id]
                for position in range(0, len(image['section_data'][section_id]), 8):
                    site, info = struct.unpack_from('<II', image['section_data'][section_id], position)
                    target = {'func_08000600': C, 'func_08000700': D}[
                        image['symbol_tables'][section[6]][info >> 8]['name']]
                    if info & 255 != 10:
                        raise AssertionError(info)
                    delta = target - (address + site) - 4
                    struct.pack_into('<HH', body, site, 0xF000 | ((delta >> 12) & 2047),
                                     0xF800 | ((delta >> 1) & 2047))
            # A trailing alignment NOP belongs to no function span.
            bodies[address] = bytes(body[:-2] if body.endswith(b'\xc0\x46') else body)
        (root / 'src/08000200.c').write_text(SOURCE % entries)
        _, body, image = match.compile_object(runner, workspace, args, root, A, 'src/08000200.c')
        rows = [{'rom': f'0x{address:08X}', 'end': f'0x{address + size:08X}', 'mode': 'thumb',
                 'instrs': 0} for address, size in ((A, len(body)), *(
                     (address, len(bodies[address])) for address in (B, C, D)))]
        mapping = json.dumps(rows).encode()
        for address, data in bodies.items():
            rom[address - match.ROM_BASE:address - match.ROM_BASE + len(data)] = data
        data, _ = owner.object_bytes(runner, workspace, args, image, A, bytes(rom), mapping, objects,
                                     selector=named.SELECTOR)
    rom[A - match.ROM_BASE:A - match.ROM_BASE + len(data)] = data
    for row, address, data in zip(rows, (A, B, C, D), (data, bodies[B], bodies[C], bodies[D])):
        row['instrs'] = owner.refine(data, address, mapping)['instrs']
    mapping = json.dumps(rows, indent=2).encode()
    index = ''.join(f'{int(row["rom"], 16):08X} {int(row["end"], 16):08X} '
                    f'{int(row["end"], 16) - int(row["rom"], 16)} {row["instrs"]} return\n'
                    for row in rows).encode()
    (root / 'config/functions.json').write_bytes(mapping)
    (root / 'config/data_symbols.json').write_bytes(objects)
    (root / 'symbols/functions.txt').write_bytes(index)
    (root / 'baserom.bin').write_bytes(bytes(rom))


@unittest.skipUnless(Path(os.path.expandvars(match.DEFAULT_CC)).is_file() and
                     shutil.which('arm-none-eabi-ld'), 'fixed compiler and ARM tools required')
class NativeTests(unittest.TestCase):
    """Typed data and a replayed buffer callee through the complete owner lifecycle."""

    @classmethod
    def setUpClass(cls):
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH', ROOT / 'build'))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix='named_buffer_replay_native_', dir=scratch)
        cls.root = Path(cls.temporary.name) / 'large'
        cls.small = Path(cls.temporary.name) / 'small'
        cls.straight = Path(cls.temporary.name) / 'straight'
        native_fixture(cls.root, 4)
        native_fixture(cls.small, 2)
        native_fixture(cls.straight, 4, STRAIGHT)
        cls.environment = patch.dict(os.environ, FFTA_ROM=str(cls.root / 'baserom.bin'))
        cls.environment.start()
        cls.result = owner.build(cls.root, A, selector=named.SELECTOR)
        cls.report = owner.render(A, cls.result)

    @classmethod
    def tearDownClass(cls):
        cls.environment.stop()
        cls.temporary.cleanup()

    def replay(self, **changes):
        result = self.result
        values = dict(data=result[0], address=A, rom=result[6], mapping=result[3], index=result[4],
                      objects=result[5], manifest=result[1], selector=named.SELECTOR)
        values.update(changes)
        return owner.verify(**values)

    def test_typed_data_caller_matches_with_a_replayed_callee(self):
        manifest = self.result[1]
        self.assertEqual(manifest['profile'], named.SCHEMA)
        self.assertEqual([row[1] for row in manifest['bindings']['data']], ['data_02000000'])
        buffers = manifest['proof']['buffers']
        self.assertEqual([row['address'] for row in buffers['dependencies']], [B])
        lines = [line for line in self.report.splitlines() if line.startswith('* buffer')]
        self.assertEqual(lines, buffers['loop_replay']['lines'])
        (line,) = lines
        self.assertRegex(line, r'^\* buffer loop replay: `bounded-loop-replay-v2` callee 0x08000400 '
                               r'sites 0x[0-9A-F]{8} writes sp\+0:2 sp\+2:2 sp\+4:2 sp\+6:2; '
                               r'proved none; trusted 0x08000600:r\d+; pruned edges \d+$')
        self.assertTrue(self.replay())
        self.assertTrue(match_evidence.report_matches(report_fixtures.carried(self.report, self.root, A), self.root, A))

    def test_a_callee_only_the_aborted_joined_pass_inspected_is_not_in_the_manifest(self):
        dependencies = [row['address'] for row in self.result[1]['proof']['buffers']['dependencies']]
        self.assertEqual(dependencies, [B])
        # Without the restore the pruned callee would be claimed as a dependency.
        with patch.object(named.NamedDataBufferProof, '_check_arguments',
                          match.BufferCallProof._check_arguments):
            leaked = owner.build(self.root, A, selector=named.SELECTOR)[1]
        self.assertEqual([row['address'] for row in leaked['proof']['buffers']['dependencies']], [B, D])

    def test_without_a_replay_the_report_has_no_record_and_no_line(self):
        with patch.dict(os.environ, FFTA_ROM=str(self.straight / 'baserom.bin')):
            result = owner.build(self.straight, A, selector=named.SELECTOR)
            report = owner.render(A, result)
            self.assertTrue(match_evidence.report_matches(report_fixtures.carried(report, self.straight, A), self.straight, A))
            buffers = result[1]['proof']['buffers']
            self.assertEqual([row['address'] for row in buffers['dependencies']], [B])
            self.assertNotIn('loop_replay', buffers)
            self.assertFalse([line for line in report.splitlines() if line.lstrip().startswith('* buffer')])
            self.assertNotIn('loop_replay', report)
            # A forged replay line on a report without a replay fails replay.
            (line,) = [line for line in self.report.splitlines() if line.startswith('* buffer loop replay')]
            evidence = next(row for row in report.splitlines() if row.startswith('* owner runtime evidence: '))
            self.assertFalse(report_fixtures.replay(
                report.replace(evidence, line + '\n' + evidence), self.straight, A))

    def test_too_small_local_refuses_at_the_exact_store(self):
        with patch.dict(os.environ, FFTA_ROM=str(self.small / 'baserom.bin')), \
                self.assertRaisesRegex(ValueError, r'buffer callee 0x08000400: bounded loop replay at '
                                       r'0x[0-9A-F]{8}: 2-byte strh at caller sp\+4: buffer access is '
                                       r'unaligned or outside allocated local words'):
            owner.build(self.small, A, selector=named.SELECTOR)

    def test_subclass_selectors_keep_the_join_refusal(self):
        import runtime_summary_profile as runtime_summary
        with self.assertRaisesRegex(ValueError, 'inconsistent possible pointer offsets at control-flow join'):
            owner.build(self.root, A, selector=runtime_summary.SELECTOR)

    def test_edited_replay_or_data_lines_fail_report_replay(self):
        (line,) = [line for line in self.report.splitlines() if line.startswith('* buffer loop replay')]
        evidence = next(line for line in self.report.splitlines()
                        if line.startswith('* owner runtime evidence: '))
        digest = self.result[1]['proof']['buffers']['loop_replay']['buffer_proof_sha256']
        edits = (self.report.replace(line + '\n', ''),
                 self.report.replace(line, line + '\n' + line),
                 self.report.replace(line, ' ' + line),
                 self.report.replace(line, line.replace('sp+6:2', 'sp+8:2')),
                 self.report.replace(line, line.replace('trusted 0x08000600', 'proved 0x08000600')),
                 self.report.replace(line, line + '\n* buffer calls: legacy'),
                 self.report.replace(evidence, evidence.replace(digest, '0' * 64)),
                 self.report.replace(evidence, evidence.replace('"data_02000000"', '"data_02000004"')),
                 self.report.replace(evidence, evidence.replace('"loop_replay":', '"loop_replay_":')))
        for edited in edits:
            with self.subTest(edit=edits.index(edited)):
                self.assertNotEqual(edited, self.report)
                self.assertFalse(report_fixtures.replay(edited, self.root, A))
        self.assertTrue(match_evidence.report_matches(report_fixtures.carried(self.report, self.root, A), self.root, A))

    def test_replay_record_is_required_and_exact(self):
        for change in ('drop', 'lines', 'premise'):
            manifest = copy.deepcopy(self.result[1])
            record = manifest['proof']['buffers']['loop_replay']
            if change == 'drop':
                del manifest['proof']['buffers']['loop_replay']
            elif change == 'lines':
                record['lines'] = []
            else:
                record['premise'] = 'none'
            with self.subTest(change=change), self.assertRaisesRegex(ValueError, 'differs from complete fresh'):
                self.replay(manifest=manifest)

    def test_misaligned_or_unreferenced_data_words_refuse(self):
        bindings = self.result[1]['bindings']
        (offset, name, addend), = bindings['data']
        self.assertEqual([row['address'] - A for row in self.result[1]['proof']['partition']['words']],
                         [offset])
        for moved, reason in ((offset + 2, 'bindings must be ordered complete words'),
                              (0, 'literal does not equal its binding')):
            changed = copy.deepcopy(bindings)
            changed['data'] = [[moved, name, addend]]
            with self.subTest(offset=moved), self.assertRaisesRegex(ValueError, reason):
                self.replay(manifest=None, bindings=changed)
        # A word holding the object address that no instruction loads, typed or
        # not, is not part of a complete owner.
        data = self.result[0] + struct.pack('<I', 0x02000000)
        rom = bytearray(self.result[6])
        rom[A - match.ROM_BASE + len(self.result[0]):A - match.ROM_BASE + len(data)] = data[-4:]
        rows = json.loads(self.result[3])
        rows[0]['end'] = f'0x{A + len(data):08X}'
        old = f'{A:08X} {A + len(self.result[0]):08X} {len(self.result[0])} '
        index = self.result[4].replace(old.encode(), f'{A:08X} {A + len(data):08X} {len(data)} '.encode())
        self.assertNotEqual(index, self.result[4])
        for extra in ([], [[len(self.result[0]), name, addend]]):
            changed = copy.deepcopy(bindings)
            changed['data'] += extra
            with self.subTest(typed=bool(extra)), self.assertRaisesRegex(
                    ValueError, 'unowned complete-owner bytes are not canonical literal alignment'):
                self.replay(data=data, rom=bytes(rom), mapping=json.dumps(rows).encode(), index=index,
                            manifest=None, bindings=changed)


if __name__ == "__main__":
    unittest.main(verbosity=2)
