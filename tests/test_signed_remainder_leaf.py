"""Compiler __modsi3 as a proved leaf call in the default buffer walk (signed_remainder_leaf_profile).

Natural C callers are compiled with the fixed agbcc and linked at 0x08000200
beside assembled callees; only the pinned __modsi3 and __div0 spans come from
the approved ROM.  match.py runs on the default path and report_matches
replays what it writes.
"""
from contextlib import redirect_stdout
import argparse
import hashlib
import io
import json
import os
from pathlib import Path
import re
import struct
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
sys.path.insert(0, str(ROOT / "tests"))
import match
import match_evidence as evidence
import data_buffer_profile as data_buffer
import modsi3_profile as modsi3
import owner_runtime_profile as owner
import owner_switch_buffer_profile as owner_switch
import signed_remainder_leaf_profile as leaf
# A module, not its classes: importing a TestCase class would make it run here again.
import test_data_buffer_calls as data_calls

BASE = match.ROM_BASE
A = data_calls.A
CALLEES = data_calls.CALLEES
APPROVED = "43fc8204c6dceee58828aebc7af0c72eb807e99f35ad641c8bb0a4fa8b6edc19"
ZERO = 0x0814274C
# The pinned division runtimes and their shared hook, as the index lists them (start, end, instructions).
RUNTIME_ROWS = ((0x081426B8, 0x0814274A, 72), (ZERO, 0x0814274E, 1), (modsi3.ADDRESS, 0x08142A1E, 102),
                (0x08142AB0, 0x08142B28, 59), (0x08142B28, 0x08142BE8, 95))
RUNTIME_SPAN = (0x081426B8, 0x08142BE8)
STORES = data_calls.STORES
# A buffer callee that itself takes a remainder: value % 9 into both halfwords of the buffer.
REMAINDER_CALLEE = ("push {r4, lr}\nadds r4, r1, #0\nmovs r1, #%d\nbl rt_modsi3\n"
                    "strh r0, [r4]\nstrh r0, [r4, #6]\npop {r4}\npop {r1}\nbx r1")
CALLEE_TAIL = "strh r0, [r4]\nstrh r0, [r4, #6]\npop {r4}\npop {r1}\nbx r1"
# The same callee with a copy of the caller's buffer pointer left in a scratch register at the call.
SCRATCH_CALLEE = "push {r4, lr}\nadds r4, r1, #0\n%s\nmovs r1, #9\nbl rt_modsi3\n" + CALLEE_TAIL
# A callee whose divisor is the literal -1 and whose dividend is unknown (INT_MIN % -1 is possible).
MINUS_ONE_CALLEE = "push {r4, lr}\nadds r4, r1, #0\nldr r1, =0xFFFFFFFF\nbl rt_modsi3\n" + CALLEE_TAIL + "\n.ltorg"
# A callee that divides by an unknown value with __udivsi3: only __modsi3 is summarised.
UDIV_CALLEE = "push {r4, lr}\nadds r4, r1, #0\nadds r1, r0, #0\nmovs r0, #100\nbl rt_udivsi3\n" + CALLEE_TAIL
# A callee that overwrites its buffer register unread (the dead-register rule admits the call
# without an inspection) and then takes an unprovable remainder.
DEAD_CALLEE = "push {r4, lr}\nadds r1, r0, #0\nbl rt_modsi3\npop {r4}\npop {r1}\nbx r1"
HEADER = ("typedef short s16;\ntypedef unsigned short u16;\ntypedef unsigned int u32;\n"
          "extern u16 data_02000000[];\n")
# The cluster's shape: a guarded jump table, a frame, a local handed to a callee, typed data and `%`.
SWITCH = HEADER + """extern void func_08000400(u16 value, u16 *out);
u32 func_08000200(u32 phase, int value)
{
    u16 buffer[4];

    switch (phase) {
    case 0:
        func_08000400(1, buffer);
        return buffer[0] + value %% 7;
    case 1:
        data_02000000[0] = 5;
        return 1;
    case 2:
        func_08000400(2, buffer);
        return buffer[3];
    case 3:
        return %(remainder)s;
    case 4:
        data_02000000[1] = 3;
        return 2;
    }
    return 0;
}
"""
# A runtime call thunk beside `%`, a local handed to a callee and typed data: the compiler-thunk
# route (kit #134) is tried first and refuses; the leaf retry follows.
THUNK = HEADER + """extern void func_08000400(u16 value, u16 *out);
int func_08000200(u16 value, void (*hook)(void), int number)
{
    u16 buffer[4];

    hook();
    func_08000400(value, buffer);
    data_02000000[0] = buffer[0];
    data_02000000[1] = buffer[3];
    return number % 41;
}
"""
# The same without typed data: the compiler-thunk route refuses for want of data, and the retry
# admits it under the plain stack buffer schema, whose replay does not recompile.
THUNK_NO_DATA = HEADER + """extern void func_08000400(u16 value, u16 *out);
int func_08000200(u16 value, void (*hook)(void), int number)
{
    u16 buffer[4];

    hook();
    func_08000400(value, buffer);
    return buffer[0] + buffer[3] + number % 41;
}
"""
# The isolated profile's own shape: admitted today, never retried.
ISOLATED = HEADER + "int func_08000200(int value)\n{\n    return (s16)value % 7;\n}\n"
# A frame and a local beside `%` with no table, thunk or literal: refused today by the
# isolated profile, not by the exclusion, so never retried.
FRAMED = HEADER + """extern void func_08000400(u16 value, u16 *out);
int func_08000200(u16 value)
{
    u16 buffer[4];

    func_08000400(value, buffer);
    return (s16)buffer[0] % 7;
}
"""


def approved_rom():
    selected = os.environ.get("FFTA_ROM")
    if not selected or not Path(selected).is_file():
        return None
    data = Path(selected).read_bytes()
    return data if hashlib.sha256(data).hexdigest() == APPROVED else None


def build(root, source, callees=(("func_08000400", STORES),), objects=data_calls.OBJECTS, runtime=None):
    """A complete tree as test_data_buffer_calls.build, plus the pinned division runtimes and thunks."""
    root = Path(root)
    for name in ("src", "include", "config", "symbols", "build"):
        (root / name).mkdir(parents=True, exist_ok=True)
    work = root / "build"
    names = [name for name, _ in callees]
    (work / "callees.s").write_text(
        ".syntax unified\n.arch armv4t\n.thumb\n.text\n"
        f".thumb_set rt_modsi3, 0x{modsi3.ADDRESS | 1:08X}\n"
        f".thumb_set rt_udivsi3, 0x{match.UDIVSI3_ADDRESS | 1:08X}\n" +
        "".join(f".global {name}, {name}_end\n" for name in names) +
        "".join(f".org 0x{0x100 * index:x}\n{name}:\n{body}\n{name}_end:\n"
                for index, (name, body) in enumerate(callees)))
    for command in (
            [match.DEFAULT_AS, "-mthumb-interwork", str(work / "callees.s"), "-o", str(work / "callees.o")],
            [match.DEFAULT_LD, f"-Ttext=0x{CALLEES:08X}", "-e", names[0], str(work / "callees.o"),
             "-o", str(work / "callees.elf")],
            [match.DEFAULT_OBJCOPY, "-O", "binary", "--only-section=.text", str(work / "callees.elf"),
             str(work / "callees.bin")]):
        subprocess.run(command, check=True, capture_output=True)
    image = match.elf_image((work / "callees.elf").read_bytes())
    symbols = {symbol["name"]: symbol["value"] for symbol in image["symbols"]}
    rom = bytearray(RUNTIME_SPAN[1] - BASE)
    code = (work / "callees.bin").read_bytes()
    rom[CALLEES - BASE:CALLEES - BASE + len(code)] = code
    rom[RUNTIME_SPAN[0] - BASE:] = runtime[RUNTIME_SPAN[0] - BASE:RUNTIME_SPAN[1] - BASE]
    for register in range(15):
        struct.pack_into("<HH", rom, match.RUNTIME_HELPERS[f"_call_via_r{register}"] - BASE,
                         0x4700 | register << 3, 0x46C0)
    entries = [{"rom": f"0x{symbols[name]:08X}", "end": f"0x{symbols[name + '_end']:08X}", "mode": "thumb"}
               for name in names]
    entries += [{"rom": f"0x{start:08X}", "end": f"0x{end:08X}", "mode": "thumb", "instrs": count}
                for start, end, count in RUNTIME_ROWS]
    # Each thunk is indexed as its one `bx rN`, as in the game's index.
    entries += [{"rom": f"0x{start:08X}", "end": f"0x{start + 2:08X}", "mode": "thumb", "instrs": 1}
                for start in sorted(match.RUNTIME_HELPERS.values())]
    counts = {int(entry["rom"], 16): entry.get("instrs", 0) for entry in entries}
    (root / "src/08000200.c").write_text(source)
    (root / "include/types.h").write_text("/* fixture */\n")
    (root / "config/data_symbols.json").write_bytes(json.dumps(objects).encode())
    args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                              objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
    runner = match.Runner(match.DEFAULT_CC, root=root, wsl_path=match.DEFAULT_WSL_PATH, timeout=120)
    with runner.workspace() as workspace:
        _, _, original = match.compile_object(runner, workspace, args, root, A, "src/08000200.c")
        symbol, _ = match.function_record(original, "func_08000200", A, True)
        entries.insert(0, {"rom": f"0x{A:08X}", "end": f"0x{A + symbol['size']:08X}", "mode": "thumb"})
        # Only the bytes are needed: link every undefined name at its address, whatever the binding
        # rules of the kit under test say about it.
        targets = {}
        for item in original["symbols"]:
            name = item["name"]
            if name and not item["section"]:
                targets[name] = (int(objects[name], 16) if name in objects else modsi3.ADDRESS
                                 if name in ("__modsi3", modsi3.ADDRESSED_NAME) else match.UDIVSI3_ADDRESS
                                 if name == "__udivsi3" else
                                 match.RUNTIME_HELPERS.get(name) or int(name[len("func_"):], 16))
        linked = match.link_typed_targets(runner, workspace, args, "func_08000200", A, targets,
                                          set(objects) & set(targets))
        symbol, offset = match.function_record(linked, "func_08000200", A, True)
        body = linked["text"][offset:offset + symbol["size"]]
    mapping = json.dumps(entries).encode()
    assert A + len(body) <= CALLEES
    rom[A - BASE:A - BASE + len(body)] = body
    (root / "config/functions.json").write_bytes(mapping)
    (root / "symbols/functions.txt").write_text("".join(
        f"{int(entry['rom'], 16):08X} {int(entry['end'], 16):08X} "
        f"{int(entry['end'], 16) - int(entry['rom'], 16)} {counts.get(int(entry['rom'], 16), 0)} return\n"
        for entry in entries))
    (root / "baserom.bin").write_bytes(bytes(rom))
    return root


def run(root, *options):
    """match.py in its own process: (exit status, stdout + stderr, report text or None)."""
    report = Path(root) / "docs/match/08000200.md"
    if report.exists() and "--check-report" not in options:
        report.unlink()
    environment = dict(os.environ, FFTA_ROM=str(Path(root) / "baserom.bin"), PYTHONDONTWRITEBYTECODE="1")
    result = subprocess.run([sys.executable, str(ROOT / "tools/match.py"), "--root", str(root), "0x08000200",
                             *options], capture_output=True, text=True, env=environment, timeout=600)
    return result.returncode, result.stdout + result.stderr, report.read_text() if report.exists() else None


def cli(root, *options):
    """match.main in this process (for patched policies): (exit status or message, stdout)."""
    output = io.StringIO()
    with patch.dict(os.environ, FFTA_ROM=str(Path(root) / "baserom.bin")), \
            patch.object(sys, "argv", ["match.py", "--root", str(root), "0x08000200", "--no-write", *options]), \
            patch.object(match, "ROOT", match.ROOT), redirect_stdout(output):
        try:
            code = match.main()
        except SystemExit as stop:
            code = stop.code
    return code, output.getvalue()


def leaf_lines(report):
    return [line for line in report.splitlines() if line.startswith(leaf.LINE)]


@unittest.skipUnless(data_calls.tools_present(), "fixed compiler and ARM tools required")
class SignedRemainderLeafTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.runtime = approved_rom()
        if cls.runtime is None:
            raise unittest.SkipTest("FFTA_ROM must reference the approved ROM")
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix="signed_remainder_leaf_", dir=scratch)
        cls.base = Path(cls.temporary.name)
        cls.admitted = cls.fixture("admitted", SWITCH % dict(remainder="value % 41"),
                                   (("func_08000400", REMAINDER_CALLEE % 9),))
        cls.code, cls.output, cls.report = run(cls.admitted)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    @classmethod
    def fixture(cls, name, source, callees=(("func_08000400", STORES),), **options):
        return build(cls.base / name, source, list(callees), runtime=cls.runtime, **options)

    def replays(self, report, root=None):
        root = root or self.admitted
        with patch.dict(os.environ, FFTA_ROM=str(root / "baserom.bin")):
            return evidence.report_matches(report, root, A)

    def assertRetryRefused(self, root, message):
        code, output, report = run(root)
        self.assertNotEqual(code, 0, output)
        self.assertIsNone(report)
        self.assertIn(leaf.EXCLUSION + leaf.RETRY, output)
        self.assertRegex(output, message)

    # The admitted shape.

    def test_the_cluster_shape_is_admitted_with_every_site_recorded(self):
        self.assertEqual(self.code, 0, self.output)
        self.assertIn("verdict MATCH - byte identical", self.output)
        self.assertNotIn(leaf.EXCLUSION, self.output)
        self.assertEqual(data_calls.verification(self.report), data_buffer.SCHEMA)
        self.assertEqual(len([line for line in self.report.splitlines()
                              if line.startswith(owner_switch.LINE)]), 1)
        head, *sites = leaf_lines(self.report)
        self.assertRegex(head, r"^\* buffer signed remainder: `thumb-compiler-modsi3-numeric-leaf-summary-v1` "
                               r"__modsi3 0x08142950 \(102 instructions, e29c5cee2bafd4fc\) and __div0 ")
        # Two sites in the owner (divisors 7 and 41) and one in the inspected callee (9).
        self.assertEqual([re.search(r"divisor (\d+) \(positive-signed32-constant-divisor\)", line)[1]
                          for line in sites], ["7", "41", "9"])
        self.assertTrue(sites[2].startswith(f"{leaf.LINE}call 0x{CALLEES + 6:08X} (0x{CALLEES:08X}+0x6): "))
        manifest = json.loads(re.search(r"\* data buffer manifest: `(.*)`", self.report)[1])
        self.assertEqual(sum(name == "__modsi3" for _, name in manifest["calls"]), 2)
        self.assertTrue(self.replays(self.report))

    def test_check_report_reproduces_the_saved_report(self):
        code, output, _ = run(self.admitted, "--check-report", "--no-write")
        self.assertEqual(code, 0, output)
        self.assertIn("report  identical to the saved docs/match/08000200.md", output)

    def test_the_fingerprint_binds_the_operand_records(self):
        rom = (self.admitted / "baserom.bin").read_bytes()
        mapping = (self.admitted / "config/functions.json").read_bytes()
        index = (self.admitted / "symbols/functions.txt").read_bytes()
        with leaf.activated():
            proof = match.BufferCallProof(rom, mapping, stack_arguments=True, loop_replay=True,
                                          bios_wrappers=True, copy_helper_index=index, switch_callee_index=index,
                                          dead_registers=True)
            summary = proof.runtime_summaries
            self.assertTrue(leaf.is_summaries(summary))
            before = proof.fingerprint()  # nothing summarised yet: no leaf evidence
            summary.sites[A + 2] = modsi3.ADDRESS
            summary.records[A + 2] = [A, 2, owner.POSITIVE_DIVISOR, 7]
            summary.prove(modsi3.ADDRESS)
            recorded = proof.fingerprint()
            self.assertNotEqual(recorded, before)
            summary.records[A + 2] = [A, 2, owner.POSITIVE_DIVISOR, 8]
            self.assertNotEqual(proof.fingerprint(), recorded)
            # The retry's admitted proof must have summarised every linked __modsi3 site of the owner.
            leaf.require_summarised(proof, {A + 2: modsi3.ADDRESS, A + 8: 0x08000400})
            for calls in ({A + 2: modsi3.ADDRESS, A + 6: modsi3.ADDRESS}, {A + 8: 0x08000400}):
                with self.subTest(calls=calls), self.assertRaisesRegex(ValueError, "every compiler __modsi3 call"):
                    leaf.require_summarised(proof, calls)
            with self.assertRaisesRegex(ValueError, "every compiler __modsi3 call"):
                leaf.require_summarised(match.BufferCallProof(rom, mapping), {A + 2: modsi3.ADDRESS})
            del summary.records[A + 2]
            with self.assertRaisesRegex(ValueError, "no numeric operand record"):
                proof.fingerprint()
            with self.assertRaisesRegex(ValueError, "no numeric operand record"):
                leaf.require_summarised(proof, {A + 2: modsi3.ADDRESS})
        # Outside the retry, and in any proof but the plain stack-argument one, there is no summary.
        self.assertIsNone(match.BufferCallProof(rom, mapping, stack_arguments=True,
                                                copy_helper_index=index).runtime_summaries)
        with leaf.activated():
            self.assertIsNone(match.BufferCallProof(rom, mapping, stack_arguments=True).runtime_summaries)
            self.assertIsNone(match.FunctionBufferCallProof(rom, mapping, stack_arguments=True)
                              .runtime_summaries)

    def test_tampered_removed_duplicated_or_indented_lines_fail_replay(self):
        lines = self.report.splitlines()
        at = next(i for i, line in enumerate(lines) if line.startswith(leaf.LINE + "call "))
        for change, edited in (
                ("divisor", lines[:at] + [lines[at].replace("divisor 7 ", "divisor 8 ")] + lines[at + 1:]),
                ("discards", lines[:at] + [re.sub(r"discarded: .*$", "discarded: r2=sp-8", lines[at])]
                 + lines[at + 1:]),
                ("removed", lines[:at] + lines[at + 1:]),
                ("duplicated", lines[:at + 1] + lines[at:]),
                ("indented", lines[:at] + ["  " + lines[at]] + lines[at + 1:]),
                ("every line removed", [line for line in lines if not line.startswith(leaf.LINE)])):
            with self.subTest(change=change):
                self.assertFalse(self.replays("\n".join(edited) + "\n"))

    def test_the_disabled_policy_keeps_the_plain_refusal_and_fails_replay(self):
        with patch.object(leaf.POLICY, "enabled", False):
            code, output = cli(self.admitted)
            self.assertEqual(code, f"compile failed:\n{leaf.EXCLUSION}")
            self.assertFalse(self.replays(self.report))
        self.assertTrue(self.replays(self.report))

    def test_the_leaf_lines_replay_only_under_the_plain_buffer_schemas(self):
        for schema in ("elf-symbol-thumb-modsi3-s16-v1", "elf-symbol-thumb-calls-v1"):
            with self.subTest(schema=schema):
                edited = self.report.replace(f"* verification: `{data_buffer.SCHEMA}`",
                                             f"* verification: `{schema}`")
                self.assertFalse(leaf.replayable(edited))
                self.assertFalse(self.replays(edited))

    # Refusals inside the retry.

    def test_an_owner_site_without_a_numeric_divisor_proof_refuses(self):
        # An unknown int divisor and an unknown int dividend: neither numeric record holds.
        root = self.fixture("unknown", SWITCH.replace("u32 phase, int value", "u32 phase, int value, int divisor")
                            % dict(remainder="value % divisor"))
        self.assertRetryRefused(root, "signed remainder requires proven signed16 r0 and nonzero r1")

    def test_a_divisor_that_can_be_zero_refuses(self):
        # A signed16 dividend, but the divisor is a loaded halfword that may be 0.
        root = self.fixture("zero", SWITCH % dict(remainder="(s16)value % data_02000000[2]"))
        self.assertRetryRefused(root, "signed remainder requires proven signed16 r0 and nonzero r1")

    def test_a_callee_site_needs_its_own_numeric_record(self):
        root = self.fixture("callee_zero", SWITCH % dict(remainder="value % 41"),
                            (("func_08000400", REMAINDER_CALLEE % 0),))
        self.assertRetryRefused(root, "signed remainder requires proven signed16 r0 and nonzero r1")

    def test_a_divisor_of_minus_one_refuses(self):
        root = self.fixture("minus_one", SWITCH % dict(remainder="value % 41"),
                            (("func_08000400", MINUS_ONE_CALLEE),))
        self.assertRetryRefused(root, "signed remainder requires proven signed16 r0 and nonzero r1")

    def test_another_runtime_in_an_inspected_callee_is_not_summarised(self):
        root = self.fixture("callee_udiv", SWITCH % dict(remainder="value % 41"), (("func_08000400", UDIV_CALLEE),))
        self.assertRetryRefused(root, "division runtime requires its versioned nonzero-divisor proof")

    def test_an_observed_site_without_a_record_refuses(self):
        # The callee's inspection reaches the remainder and is refused; the dead-register rule then
        # admits the call uninspected, but the observed site keeps needing its record.
        two = (SWITCH % dict(remainder="value % 41")).replace(
            "extern void func_08000400(u16 value, u16 *out);",
            "extern void func_08000400(u16 value, u16 *out);\nextern void func_08000500(u16 value, u16 *out);").replace(
            "func_08000400(2, buffer);", "func_08000500(2, buffer);")
        root = self.fixture("dead", two, (("func_08000400", STORES), ("func_08000500", DEAD_CALLEE)))
        self.assertRetryRefused(root, f"no numeric operand record: 0x{CALLEES + 0x104:08X}")

    def test_a_caller_pointer_in_r3_is_discarded_and_stated_but_r2_and_r12_refuse(self):
        root = self.fixture("scratch_r3", SWITCH % dict(remainder="value % 41"),
                            (("func_08000400", SCRATCH_CALLEE % "adds r3, r1, #0"),))
        code, output, report = run(root)
        self.assertEqual(code, 0, output)
        site, = [line for line in leaf_lines(report) if f"call 0x{CALLEES + 8:08X} " in line]
        self.assertRegex(site, r"divisor 9 \(positive-signed32-constant-divisor\); dead scratch discarded: r3=sp-\d+$")
        self.assertTrue(self.replays(report, root))
        for name, copy in (("r2", "adds r2, r1, #0"), ("r12", "mov r12, r1")):
            with self.subTest(register=name):
                root = self.fixture(f"scratch_{name}", SWITCH % dict(remainder="value % 41"),
                                    (("func_08000400", SCRATCH_CALLEE % copy),))
                self.assertRetryRefused(root, "scratch pointer the runtime may return unchanged")

    def test_a_local_pointer_operand_is_never_laundered_into_the_result(self):
        for name, remainder in (("dividend", "(int)buffer % 7"), ("divisor", "value % (int)buffer")):
            with self.subTest(operand=name):
                root = self.fixture(f"pointer_{name}", SWITCH % dict(remainder=remainder))
                self.assertRetryRefused(root, "local pointer in R0, R1 or LR")

    def test_explicit_runtime_identifiers_are_refused(self):
        explicit = SWITCH.replace("u32 func_08000200", "extern int __modsi3(int, int);\nu32 func_08000200")
        root = self.fixture("explicit", explicit % dict(remainder="__modsi3(value, 41)"))
        self.assertRetryRefused(root, "runtime identifiers cannot occur in preprocessed C")

    def test_other_runtimes_stay_refused_in_the_retry(self):
        root = self.fixture("udiv", SWITCH % dict(remainder="value % 41 + (u32)value / 10u"))
        self.assertRetryRefused(root, "signed remainder leaf summary excludes other runtimes and function literals")

    # Where the retry never runs.

    def test_an_admitted_isolated_remainder_is_not_retried(self):
        root = self.fixture("isolated", ISOLATED, objects={})
        with patch.object(leaf.Policy, "retry", side_effect=AssertionError("retried")):
            code, output = cli(root)
        self.assertEqual(code, 0, output)
        self.assertIn("verdict MATCH - byte identical", output)
        code, output, report = run(root)
        self.assertEqual(code, 0, output)
        self.assertEqual(data_calls.verification(report), modsi3.SCHEMA)
        self.assertEqual(leaf_lines(report), [])

    def test_another_refusal_is_not_retried(self):
        root = self.fixture("framed", FRAMED)
        with patch.object(leaf.Policy, "retry", side_effect=AssertionError("retried")):
            code, output = cli(root)
        self.assertIsInstance(code, str)
        self.assertNotIn(leaf.EXCLUSION, code)
        self.assertNotIn(leaf.RETRY, code)

    def test_a_labelled_run_is_not_retried(self):
        with patch.object(leaf.Policy, "retry", side_effect=AssertionError("retried")):
            code, output = cli(self.admitted, "--label", "probe")
        self.assertEqual(code, f"compile failed:\n{leaf.EXCLUSION}")

    def test_a_run_under_a_signed_quotient_selector_is_not_retried(self):
        with patch.object(leaf.Policy, "retry", side_effect=AssertionError("retried")):
            code, output = cli(self.admitted, "--signed-quotient-profile", match.divsi3.FRAMED_SELECTOR)
        self.assertEqual(code, f"compile failed:\n{leaf.EXCLUSION}")

    def test_the_addressed_spelling_is_not_retried(self):
        root = self.fixture("addressed", SWITCH % dict(remainder="value % 41"))
        # Only the refusal matters, and it comes before the bytes are compared with the ROM.
        addressed = SWITCH.replace("u32 func_08000200", "extern int func_08142950(int, int);\nu32 func_08000200")
        (root / "src/08000200.c").write_text((addressed % dict(remainder="func_08142950(value, 41)")).replace(
            "value % 7", "func_08142950(value, 7)"))
        with patch.object(leaf.Policy, "retry", side_effect=AssertionError("retried")):
            code, output = cli(root)
        self.assertEqual(code, f"compile failed:\n{leaf.EXCLUSION}")

    def test_the_retry_follows_a_refused_compiler_thunk_route(self):
        root = self.fixture("thunk", THUNK)
        routed = match.addressed_signed_runtime.COMPILER_THUNKS_POLICY
        with patch.object(routed, "issue", wraps=routed.issue) as issue:
            code, output = cli(root)
        self.assertEqual(code, 0, output)
        self.assertEqual(issue.call_count, 1)
        self.assertIn("verdict MATCH - byte identical", output)
        code, output, report = run(root)
        self.assertEqual(code, 0, output)
        self.assertEqual(data_calls.verification(report), data_buffer.SCHEMA)
        self.assertEqual(len(leaf_lines(report)), 2)
        self.assertTrue(self.replays(report, root))

    def test_without_typed_data_the_stack_buffer_schema_carries_and_replays_the_lines(self):
        root = self.fixture("thunk_no_data", THUNK_NO_DATA, objects={})
        code, output, report = run(root)
        self.assertEqual(code, 0, output)
        self.assertEqual(data_calls.verification(report), evidence.STACK_BUFFER_SCHEMA)
        head, site = leaf_lines(report)
        self.assertIn("divisor 41 (positive-signed32-constant-divisor)", site)
        self.assertTrue(self.replays(report, root))
        lines = report.splitlines()
        at = lines.index(site)
        self.assertFalse(self.replays("\n".join(lines[:at] + [site.replace("divisor 41", "divisor 40")]
                                                + lines[at + 1:]) + "\n", root))
        self.assertFalse(self.replays("\n".join(lines[:at] + lines[at + 1:]) + "\n", root))
        with patch.object(leaf.POLICY, "enabled", False):
            self.assertFalse(self.replays(report, root))
        code, output, _ = run(root, "--check-report", "--no-write")
        self.assertEqual(code, 0, output)
        self.assertIn("report  identical to the saved docs/match/08000200.md", output)

    def test_the_binding_and_link_take_only_compiler_modsi3(self):
        # Leaf mode binds no addressed spelling and no second runtime.
        self.assertFalse(leaf.active())
        with leaf.activated():
            self.assertTrue(leaf.active())
            with self.assertRaisesRegex(ValueError, "runtime identifiers"):
                leaf.namespace("int f(int a) { return __modsi3(a, 3); }")
            with self.assertRaisesRegex(ValueError, "runtime identifiers"):
                leaf.namespace("extern int func_08142950(int, int);")
            leaf.namespace('/* __modsi3 */ const char *s = "func_08142950";')
        self.assertFalse(leaf.active())



# A caller that needs both this retry and the default stack-index retry: a thunk beside `%`
# (the exclusion, then this retry) and a variably indexed private array (the stack-index retry
# inside it).  Neither rule alone admits it.
COMPOSED_TABLE = "".join(f"    table[{index}] = {value};\n" for index, value in enumerate((3, 1, 4, 1, 5, 9, 2, 6)))
COMPOSED = "typedef unsigned char u8;\n" + HEADER + """extern void func_08000400(u32 value);
u32 func_08000200(u32 value, void (*hook)(void), int number)
{
    u8 table[8];

    hook();
%s    func_08000400(value);
    return table[value & 7] + number %% 41;
}
""" % COMPOSED_TABLE


@unittest.skipUnless(data_calls.tools_present(), "fixed compiler and ARM tools required")
class ComposedWithStackIndexTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.runtime = approved_rom()
        if cls.runtime is None:
            raise unittest.SkipTest("FFTA_ROM must reference the approved ROM")
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix="leaf_composed_", dir=scratch)
        cls.base = Path(cls.temporary.name)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def replays(self, root, report):
        with patch.dict(os.environ, FFTA_ROM=str(root / "baserom.bin")):
            return evidence.report_matches(report, root, A)

    def test_a_stack_index_retry_inside_the_remainder_retry_states_both_in_order(self):
        import default_stack_index_profile as default_index
        root = build(self.base / "composed", COMPOSED, [("func_08000400", "bx lr")], objects={},
                     runtime=self.runtime)
        code, output, report = run(root)
        self.assertEqual(code, 0, output)
        self.assertEqual(data_calls.verification(report), evidence.STACK_BUFFER_SCHEMA)
        lines = report.splitlines()
        index = [line for line in lines if line.startswith("* buffer stack index")]
        remainder = [line for line in lines if line.startswith(leaf.LINE)]
        self.assertTrue(index)
        self.assertTrue(remainder)
        # The stack-index lines come first, then the remainder lines (BufferCallProof.loop_replay_lines).
        self.assertLess(max(lines.index(line) for line in index), min(lines.index(line) for line in remainder))
        self.assertTrue(self.replays(root, report))
        # Each rule is needed, and each block is bound.
        with patch.object(default_index.POLICY, "enabled", False):
            self.assertFalse(self.replays(root, report))
        with patch.object(leaf.POLICY, "enabled", False):
            self.assertFalse(self.replays(root, report))
        for prefix in ("* buffer stack index access", leaf.LINE + "call"):
            at = next(i for i, line in enumerate(lines) if line.startswith(prefix))
            self.assertFalse(self.replays(root, "\n".join(lines[:at] + lines[at + 1:]) + "\n"), prefix)
        # The blocks swapped do not replay: the fingerprint binds their order.
        rest = [line for line in lines if line not in index and line not in remainder]
        first = min(lines.index(line) for line in index + remainder)
        swapped = rest[:first] + remainder + index + rest[first:]
        self.assertFalse(self.replays(root, "\n".join(swapped) + "\n"))
        # The stack-index retry's second proof resolves calls as the first does: with it resolving
        # with ``target``, the summarised __modsi3 entry is a callee again and the report does not replay.
        original = match.BufferCallProof.resolve_call

        def by_target(proof, address):
            return proof.target(address) if proof.index_policy is not None else original(proof, address)
        with patch.object(match.BufferCallProof, "resolve_call", by_target):
            self.assertFalse(self.replays(root, report))
        code, output, _ = run(root, "--check-report", "--no-write")
        self.assertEqual(code, 0, output)
        self.assertIn("report  identical to the saved docs/match/08000200.md", output)

if __name__ == "__main__":
    unittest.main()
