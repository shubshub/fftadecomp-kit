"""Compiler __divsi3/__udivsi3/__umodsi3 as proved leaf calls in the default buffer walk.

The signed remainder leaf retry (signed_remainder_leaf_profile) widened to the other three
pinned word runtimes (``DIVISION``).  Natural C callers are compiled with the fixed agbcc and
linked beside assembled callees, as in test_signed_remainder_leaf; only the pinned runtime and
__div0 spans come from the approved ROM.
"""
import json
import os
from pathlib import Path
import re
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
import owner_runtime_profile as owner
import signed_remainder_leaf_profile as leaf
# Modules, not their classes: importing a TestCase class would make it run here again.
import test_data_buffer_calls as data_calls
import test_signed_remainder_leaf as base

A, CALLEES, STORES = base.A, base.CALLEES, base.STORES
HEADER = base.HEADER
# The cluster's shape (0x0802A6A0's): a guarded jump table, a frame, a local handed to a callee,
# typed data, and a quotient and a remainder by constants.
SIGNED = HEADER + """extern void func_08000400(u16 value, u16 *out);
u32 func_08000200(u32 phase, int value)
{
    u16 buffer[4];

    switch (phase) {
    case 0:
        func_08000400(1, buffer);
        return buffer[0] + value / 10;
    case 1:
        data_02000000[0] = 5;
        return 1;
    case 2:
        func_08000400(2, buffer);
        return buffer[3];
    case 3:
        return %(division)s;
    case 4:
        data_02000000[1] = 3;
        return 2;
    }
    return 0;
}
"""
# Unsigned: a quotient by 264 (MOV and LSL, as 0x08070A38's pointer difference) and a remainder by 40.
UNSIGNED = HEADER + """extern void func_08000400(u16 value, u16 *out);
u32 func_08000200(u32 phase, u32 value)
{
    u16 buffer[4];

    switch (phase) {
    case 0:
        func_08000400(1, buffer);
        return buffer[0] + value / 264;
    case 1:
        data_02000000[0] = 5;
        return 1;
    case 2:
        func_08000400(2, buffer);
        return buffer[3];
    case 3:
        return %(division)s;
    case 4:
        data_02000000[1] = 3;
        return 2;
    }
    return 0;
}
"""
# A buffer callee that takes a quotient: value / 9 into both halfwords of the buffer.
QUOTIENT_CALLEE = ("push {r4, lr}\nadds r4, r1, #0\nmovs r1, #%d\nbl rt_divsi3\n" + base.CALLEE_TAIL)
# The same with an unknown unsigned divisor (the caller's value), and with an interior target.
UMOD_CALLEE = "push {r4, lr}\nadds r4, r1, #0\nadds r1, r0, #0\nmovs r0, #100\nbl rt_umodsi3\n" + base.CALLEE_TAIL
UMOD_ZERO_CALLEE = "push {r4, lr}\nadds r4, r1, #0\nmovs r1, #0\nbl rt_umodsi3\n" + base.CALLEE_TAIL
MINUS_ONE_CALLEE = ("push {r4, lr}\nadds r4, r1, #0\nldr r1, =0xFFFFFFFF\nbl rt_divsi3\n" + base.CALLEE_TAIL +
                    "\n.ltorg")
INT_MIN_CALLEE = ("push {r4, lr}\nadds r4, r1, #0\nldr r1, =0x80000000\nbl rt_divsi3\n" + base.CALLEE_TAIL +
                  "\n.ltorg")
INTERIOR_CALLEE = "push {r4, lr}\nadds r4, r1, #0\nmovs r1, #9\nbl rt_divsi3 + 2\n" + base.CALLEE_TAIL
# A constant that does not reach the site on every path: clobbered by the summarised runtime itself, or
# set on one side of a branch only, with the caller's value on the other (0 itself, in the first).  The
# join is not the branch's own target, and the constant sits on the fallthrough in one and on the taken
# edge in the other, so in one of them it reaches the join first.
KILLED_CONSTANT_CALLEE = ("push {r4, lr}\nadds r4, r1, #0\nmovs r1, #10\nbl rt_udivsi3\nbl rt_udivsi3\n" +
                          base.CALLEE_TAIL)
ONE_PATH_CALLEE = ("push {r4, lr}\nadds r4, r1, #0\ncmp r0, #0\nbeq 1f\nmovs r1, #10\nb 2f\n1:\nadds r1, r0, #0\n"
                   "2:\nbl rt_udivsi3\n" + base.CALLEE_TAIL)
OTHER_PATH_CALLEE = ("push {r4, lr}\nadds r4, r1, #0\ncmp r0, #0\nbeq 1f\nadds r1, r0, #0\nb 2f\n1:\nmovs r1, #10\n"
                     "2:\nbl rt_udivsi3\n" + base.CALLEE_TAIL)


def division_lines(report):
    return [line for line in report.splitlines() if line.startswith(leaf.DIVISION_LINE)]


@unittest.skipUnless(data_calls.tools_present(), "fixed compiler and ARM tools required")
class DivisionLeafTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.runtime = base.approved_rom()
        if cls.runtime is None:
            raise unittest.SkipTest("FFTA_ROM must reference the approved ROM")
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix="division_leaf_", dir=scratch)
        cls.base = Path(cls.temporary.name)
        cls.signed = cls.fixture("signed", SIGNED % dict(division="value % 10"),
                                 (("func_08000400", QUOTIENT_CALLEE % 9),))
        cls.code, cls.output, cls.report = base.run(cls.signed)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    @classmethod
    def fixture(cls, name, source, callees=(("func_08000400", STORES),), **options):
        return base.build(cls.base / name, source, list(callees), runtime=cls.runtime, **options)

    def replays(self, report, root=None):
        root = root or self.signed
        with patch.dict(os.environ, FFTA_ROM=str(root / "baserom.bin")):
            return evidence.report_matches(report, root, A)

    def assertRetryRefused(self, root, exclusion, message):
        code, output, report = base.run(root)
        self.assertNotEqual(code, 0, output)
        self.assertIsNone(report)
        self.assertRegex(output, f"(?:{exclusion}){re.escape(leaf.DIVISION_RETRY)}")
        self.assertRegex(output, message)

    # Admitted shapes.

    def test_the_signed_cluster_shape_is_admitted_with_every_site_recorded(self):
        self.assertEqual(self.code, 0, self.output)
        self.assertIn("verdict MATCH - byte identical", self.output)
        self.assertEqual(data_calls.verification(self.report), data_buffer.SCHEMA)
        self.assertEqual(base.leaf_lines(self.report), [])
        head, *sites = division_lines(self.report)
        self.assertRegex(head, r"^\* buffer division runtime: `thumb-compiler-division-numeric-leaf-summary-v1` "
                               r"__divsi3 0x081426B8 \(\d+ instructions, 80b13b14c17b297e\), "
                               r"__modsi3 0x08142950 \(102 instructions, e29c5cee2bafd4fc\) and __div0 ")
        # The owner's quotient and remainder by 10, and the callee's quotient by 9.
        found = [re.search(r" (__\w+): divisor (\d+) \(positive-signed32-constant-divisor\)", line).groups()
                 for line in sites]
        self.assertEqual(sorted(found), sorted([("__divsi3", "10"), ("__modsi3", "10"), ("__divsi3", "9")]))
        self.assertTrue(any(line.startswith(f"{leaf.DIVISION_LINE}call 0x{CALLEES + 6:08X} (0x{CALLEES:08X}+0x6) "
                                            "__divsi3: ") for line in sites))
        manifest = json.loads(re.search(r"\* data buffer manifest: `(.*)`", self.report)[1])
        self.assertEqual(sorted(name for _, name in manifest["calls"] if name.startswith("__")),
                         ["__divsi3", "__modsi3"])
        self.assertTrue(self.replays(self.report))

    def test_check_report_reproduces_the_saved_report(self):
        code, output, _ = base.run(self.signed, "--check-report", "--no-write")
        self.assertEqual(code, 0, output)
        self.assertIn("report  identical to the saved docs/match/08000200.md", output)

    def test_unsigned_constants_through_mov_and_lsl_are_admitted(self):
        root = self.fixture("unsigned", UNSIGNED % dict(division="value % 40"))
        code, output, report = base.run(root)
        self.assertEqual(code, 0, output)
        sites = division_lines(report)[1:]
        found = sorted(re.search(r" (__\w+): divisor (\d+) \(nonzero-u32-constant-divisor\)", line).groups()
                       for line in sites)
        self.assertEqual(found, [("__udivsi3", "264"), ("__umodsi3", "40")])
        self.assertTrue(self.replays(report, root))

    def test_the_fingerprint_binds_the_operand_records(self):
        rom = (self.signed / "baserom.bin").read_bytes()
        mapping = (self.signed / "config/functions.json").read_bytes()
        index = (self.signed / "symbols/functions.txt").read_bytes()
        with leaf.activated():
            proof = match.BufferCallProof(rom, mapping, stack_arguments=True, loop_replay=True,
                                          bios_wrappers=True, copy_helper_index=index, switch_callee_index=index,
                                          dead_registers=True)
            summary = proof.runtime_summaries
            for entry in leaf.ENTRIES.values():
                self.assertTrue(summary.covers(entry))
            self.assertFalse(summary.covers(leaf.ENTRIES["__divsi3"] + 2))
            summary.sites[A + 2] = leaf.ENTRIES["__udivsi3"]
            summary.records[A + 2] = [A, 2, leaf.NONZERO_DIVISOR, 264]
            summary.prove(leaf.ENTRIES["__udivsi3"])
            recorded = proof.fingerprint()
            summary.records[A + 2] = [A, 2, leaf.NONZERO_DIVISOR, 265]
            self.assertNotEqual(proof.fingerprint(), recorded)
            self.assertIn("__udivsi3: divisor 265 (nonzero-u32-constant-divisor)", "\n".join(summary.lines()))
            summary.records[A + 2] = [A, 2, "an-unknown-kind", 264]
            with self.assertRaisesRegex(ValueError, "unknown kind"):
                summary.lines()
            del summary.records[A + 2]
            with self.assertRaisesRegex(ValueError, "no numeric operand record"):
                proof.fingerprint()
        with patch.object(leaf.DIVISION, "enabled", False), leaf.activated():
            proof = match.BufferCallProof(rom, mapping, stack_arguments=True, copy_helper_index=index)
            self.assertEqual([entry for entry in leaf.ENTRIES.values() if proof.runtime_summaries.covers(entry)],
                             [leaf.ADDRESS])

    def test_tampered_or_removed_lines_fail_replay(self):
        lines = self.report.splitlines()
        at = next(i for i, line in enumerate(lines) if line.startswith(leaf.DIVISION_LINE + "call "))
        for change, edited in (
                ("divisor", lines[:at] + [re.sub(r"divisor (\d+) ", lambda m: f"divisor {int(m[1]) + 1} ",
                                                 lines[at])] + lines[at + 1:]),
                ("runtime", lines[:at] + [lines[at].replace("__divsi3:", "__udivsi3:").replace(
                    "__modsi3:", "__umodsi3:")] + lines[at + 1:]),
                ("removed", lines[:at] + lines[at + 1:]),
                ("duplicated", lines[:at + 1] + lines[at:]),
                ("as remainder lines", [line.replace(leaf.DIVISION_LINE, leaf.LINE) for line in lines]),
                ("every line removed", [line for line in lines if not line.startswith(leaf.DIVISION_LINE)])):
            with self.subTest(change=change):
                self.assertFalse(self.replays("\n".join(edited) + "\n"))

    def test_the_disabled_policies_keep_the_plain_refusal_and_fail_replay(self):
        exclusion = "signed quotient excludes other runtime, literal, switch and thunk profiles"
        for policy in (leaf.DIVISION, leaf.POLICY):
            with self.subTest(policy=type(policy).__name__), patch.object(policy, "enabled", False):
                code, output = base.cli(self.signed)
                self.assertEqual(code, f"compile failed:\n{exclusion}")
                self.assertFalse(self.replays(self.report))
        self.assertTrue(self.replays(self.report))

    # Refusals inside the retry.

    def test_a_variable_signed_divisor_refuses(self):
        root = self.fixture("signed_variable",
                            SIGNED.replace("u32 phase, int value", "u32 phase, int value, int divisor")
                            % dict(division="value / divisor"))
        self.assertRetryRefused(root, "signed quotient excludes other runtime, literal, switch and thunk profiles",
                                "signed remainder requires proven signed16 r0 and nonzero r1")

    def test_a_signed16_dividend_needs_a_nonzero_divisor(self):
        root = self.fixture("signed_zero", SIGNED % dict(division="(s16)value / data_02000000[2]"))
        self.assertRetryRefused(root, "signed quotient excludes other runtime, literal, switch and thunk profiles",
                                "signed remainder requires proven signed16 r0 and nonzero r1")

    def test_a_variable_unsigned_divisor_refuses(self):
        root = self.fixture("unsigned_variable",
                            UNSIGNED.replace("u32 phase, u32 value", "u32 phase, u32 value, u32 divisor")
                            % dict(division="value % divisor"))
        self.assertRetryRefused(root, "(division evidence excludes literal, switch and thunk combinations|"
                                      "unsigned remainder excludes other runtime, switch, function and thunk "
                                      "profiles)",
                                "unsigned division leaf requires a CFG-proven nonzero constant in r1")

    def test_a_callee_site_needs_its_own_numeric_record(self):
        for name, callee, message in (
                ("callee_zero", QUOTIENT_CALLEE % 0, "signed remainder requires proven signed16 r0 and nonzero r1"),
                # -1 and INT_MIN as constants: neither is a positive signed32 divisor.
                ("callee_minus_one", MINUS_ONE_CALLEE, "signed remainder requires proven signed16 r0 and nonzero r1"),
                ("callee_int_min", INT_MIN_CALLEE, "signed remainder requires proven signed16 r0 and nonzero r1"),
                ("callee_umod", UMOD_CALLEE, "unsigned division leaf requires a CFG-proven nonzero constant"),
                ("callee_umod_zero", UMOD_ZERO_CALLEE, "unsigned division leaf requires a CFG-proven nonzero constant"),
                ("callee_killed_constant", KILLED_CONSTANT_CALLEE,
                 "unsigned division leaf requires a CFG-proven nonzero constant"),
                ("callee_one_path", ONE_PATH_CALLEE, "unsigned division leaf requires a CFG-proven nonzero constant"),
                ("callee_other_path", OTHER_PATH_CALLEE,
                 "unsigned division leaf requires a CFG-proven nonzero constant")):
            with self.subTest(callee=name):
                root = self.fixture(name, SIGNED % dict(division="value % 10"), (("func_08000400", callee),))
                self.assertRetryRefused(
                    root, "signed quotient excludes other runtime, literal, switch and thunk profiles", message)

    def test_an_interior_runtime_target_is_not_summarised(self):
        root = self.fixture("interior", SIGNED % dict(division="value % 10"), (("func_08000400", INTERIOR_CALLEE),))
        self.assertRetryRefused(root, "signed quotient excludes other runtime, literal, switch and thunk profiles",
                                "signed quotient requires its canonical positive-constant proof")

    def test_the_link_stage_refuses_an_interior_runtime_call_on_its_own(self):
        # call_bindings binds each summarised runtime at its pinned entry; the link check refuses a
        # call into a pinned runtime span anywhere else even if an earlier stage handed one over.
        bindings = match.call_bindings

        def interior(*args, **kwargs):
            calls, targets, data = bindings(*args, **kwargs)
            if leaf.active():
                calls = {site: target + 2 if target in leaf.entries() else target
                         for site, target in calls.items()}
            return calls, targets, data
        with patch.object(match, "call_bindings", interior):
            code, output = base.cli(self.signed)
        self.assertIn("linked signed remainder leaf bindings are incomplete or mixed", str(code))
        self.assertNotIn("verdict MATCH", output)

    def test_a_local_pointer_operand_is_never_laundered_into_the_result(self):
        for name, division in (("dividend", "(u32)buffer / 10u"), ("divisor", "(u32)value / (u32)buffer")):
            with self.subTest(operand=name):
                root = self.fixture(f"pointer_{name}", SIGNED % dict(division=division))
                self.assertRetryRefused(root, "signed quotient excludes other runtime, literal, switch and thunk "
                                              "profiles", "local pointer in R0, R1 or LR")

    def test_a_quotient_used_as_a_buffer_index_refuses(self):
        root = self.fixture("index", SIGNED % dict(division="buffer[(value & 0xFFF) / 1000]"))
        code, output, report = base.run(root)
        self.assertNotEqual(code, 0, output)
        self.assertIsNone(report)

    def test_explicit_runtime_identifiers_are_refused(self):
        explicit = SIGNED.replace("u32 func_08000200", "extern int __divsi3(int, int);\nu32 func_08000200")
        root = self.fixture("explicit", explicit % dict(division="value % 10"))
        self.assertRetryRefused(root, "signed quotient excludes other runtime, literal, switch and thunk profiles",
                                "division leaf summary requires compiler-emitted runtimes")

    def test_altered_runtime_bytes_refuse(self):
        rom = (self.signed / "baserom.bin").read_bytes()
        mapping = (self.signed / "config/functions.json").read_bytes()
        for name, entry in leaf.ENTRIES.items():
            with self.subTest(runtime=name):
                leaf.verify_identity(name, rom, mapping)
                altered = bytearray(rom)
                altered[entry + 0x10 - match.ROM_BASE] ^= 1
                with self.assertRaisesRegex(ValueError, "identity|differs|digest"):
                    leaf.verify_identity(name, bytes(altered), mapping)
        # End to end the plain path checks the identity first and keeps its refusal.
        runtime = bytearray(self.runtime)
        runtime[leaf.ENTRIES["__divsi3"] + 0x10 - match.ROM_BASE] ^= 1
        root = base.build(self.base / "altered", SIGNED % dict(division="value % 10"),
                          [("func_08000400", STORES)], runtime=bytes(runtime))
        code, output, report = base.run(root)
        self.assertNotEqual(code, 0, output)
        self.assertIsNone(report)
        self.assertIn("identity differs", output)

    # Where the retry never runs.

    def test_an_addressed_spelling_is_not_retried(self):
        root = self.fixture("addressed", SIGNED % dict(division="value % 10"))
        addressed = SIGNED.replace("u32 func_08000200", "extern int func_081426B8(int, int);\nu32 func_08000200")
        (root / "src/08000200.c").write_text((addressed % dict(division="value % 10")).replace(
            "value / 10", "func_081426B8(value, 10)"))
        with patch.object(leaf.Policy, "retry", side_effect=AssertionError("retried")):
            code, output = base.cli(root)
        self.assertIsInstance(code, str)
        self.assertNotIn(leaf.DIVISION_RETRY, code)

    def test_another_refusal_is_not_retried(self):
        with patch.object(leaf.Policy, "retry", side_effect=AssertionError("retried")):
            code, output = base.cli(self.signed, "--label", "probe")
        self.assertEqual(code, "compile failed:\nsigned quotient excludes other runtime, literal, switch and "
                               "thunk profiles")

    def test_the_trigger_is_the_exact_exclusion_text(self):
        args = match.argparse.Namespace(mode="thumb", control_flow_profile="ordinary", label="")
        original = {"symbols": [{"name": "__divsi3", "section": 0}]}
        with patch("library_units._selectors", return_value=()):
            for text, expected in ((leaf.DIVISION_EXCLUSIONS[0], True),
                                   ("buffer callee 0x08000400: " + leaf.DIVISION_EXCLUSIONS[0], False),
                                   (leaf.DIVISION_EXCLUSIONS[0] + ".", False),
                                   ("division runtime requires its canonical compiler alias", False)):
                with self.subTest(text=text):
                    self.assertEqual(leaf.POLICY.applies(args, None, original, ValueError(text)), expected)
            addressed = {"symbols": original["symbols"] + [{"name": "func_08142B28", "section": 0}]}
            self.assertFalse(leaf.POLICY.applies(args, None, addressed, ValueError(leaf.DIVISION_EXCLUSIONS[0])))
            with patch.object(leaf.DIVISION, "enabled", False):
                self.assertFalse(leaf.POLICY.applies(args, None, original, ValueError(leaf.DIVISION_EXCLUSIONS[0])))

    def test_the_namespace_and_names(self):
        with leaf.activated():
            for text in ("int f(int a) { return __udivsi3(a, 3); }", "extern int func_08142B28(int, int);"):
                with self.subTest(text=text), self.assertRaisesRegex(ValueError, "compiler-emitted runtimes"):
                    leaf.namespace(text)
            with self.assertRaisesRegex(ValueError, "compiler-emitted __modsi3"):
                leaf.namespace("extern int func_08142950(int, int);")
            leaf.namespace('/* __divsi3 */ const char *s = "func_081426B8";')
        with patch.object(leaf.DIVISION, "enabled", False):
            self.assertEqual(leaf.names(), {"__modsi3"})
            leaf.namespace("extern int __divsi3(int, int);")


if __name__ == "__main__":
    unittest.main()
