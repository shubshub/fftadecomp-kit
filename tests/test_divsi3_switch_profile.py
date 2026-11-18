"""Compiler __divsi3 beside one guarded local jump table (division_switch_profile.POLICY).

The callers are synthetic natural C compiled by the fixed agbcc; only the
pinned runtime spans come from the approved ROM, as in test_framed_divsi3_profile.
"""
import copy
import json
import os
from pathlib import Path
import re
import sys
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import test_framed_divsi3_profile as fixtures
import division_switch_profile as switches

match, evidence, profile, status = fixtures.match, fixtures.evidence, fixtures.profile, fixtures.status
BASE = fixtures.BASE
PLAIN = "signed quotient excludes other runtime, literal, switch and thunk profiles"

CASES = """    switch (kind) {
    case 0: return value / 6;
    case 1: return CALL;
    case 2: return value + 7;
    case 3: return value / 6 + 1;
    case 4: return value * 3;
    case 5: return value - 9;
    }
    return 0;
"""
# No frame: two-argument call.
FRAMELESS = ("extern int func_08000200(int, int);\nint func_08000000(int kind, int value)\n{\n" +
             CASES.replace("CALL", "func_08000200(value, 1)") + "}\n")
# A fifth argument forces a 4-byte outgoing frame.
FRAMED = ("extern int func_08000200(int, int, int, int, int);\nint func_08000000(int kind, int value)\n{\n" +
          CASES.replace("CALL", "func_08000200(value, 1, 2, 3, 4)") + "}\n")
# One division whose divisor joins two different constants from the cases.
JOINED = """extern int func_08000200(int, int);
int func_08000000(int kind, int value)
{
    int divisor = 1;
    switch (kind) {
    case 0: divisor = 6; break;
    case 1: divisor = 7; break;
    case 2: value += 7; divisor = 6; break;
    case 3: value = func_08000200(value, 1); divisor = 6; break;
    case 4: value *= 3; divisor = 6; break;
    case 5: value -= 9; divisor = 6; break;
    }
    return value / divisor;
}
"""


class QuotientSwitchTests(fixtures.FramedQuotientTests):
    """Reuses the framed fixture's root, ROM and CLI helpers; its own tests are not re-run."""

    def fixture(self, assembly=None, source=FRAMELESS):
        (self.root / "src/08000000.c").write_text(source)
        runner = match.Runner(match.DEFAULT_CC, root=self.root, timeout=120)
        with runner.workspace() as workspace:
            _, _, original = match.compile_object(runner, str(workspace), self.args, self.root, BASE,
                                                  "src/08000000.c")
            symbol, _ = match.function_record(original, fixtures.NAME, BASE, True)
            entries = [{"rom": f"0x{BASE:08X}", "end": f"0x{BASE + symbol['size']:08X}", "mode": "thumb"},
                       {"rom": f"0x{fixtures.CALLEE:08X}", "end": f"0x{fixtures.CALLEE + 2:08X}",
                        "mode": "thumb"}]
            entries += [{"rom": f"0x{start:08X}", "end": f"0x{end:08X}", "mode": "thumb"}
                        for start, end, _ in profile.IDENTITIES]
            self.mapping = json.dumps(entries).encode()
            self.bindings, self.switches = {}, {}
            self.body, self.calls, literals = match.link_calls(
                runner, str(workspace), self.args, original, BASE, self.mapping,
                len(self.runtime_rom), bytes(self.runtime_rom), divsi3_bindings=self.bindings,
                switch_relocations=self.switches)
            self.assertFalse(literals)
        rom = bytearray(self.runtime_rom)
        rom[:len(self.body)] = self.body
        self.rom = bytes(rom)
        (self.root / "config/functions.json").write_bytes(self.mapping)
        (self.root / "symbols/functions.txt").write_text(
            f"08000000 {BASE + len(self.body):08X} {len(self.body)} 0 return\n")

    def manifest(self, selector=None):
        observed = {}
        match.verify_leaf_instructions(self.body, BASE, True, self.calls,
            divsi3_context=(self.rom, self.mapping, self.bindings, observed),
            signed_quotient_profile=selector, switch_relocations=self.switches)
        return {"runtime": profile.RUNTIME,
                "calls": [[site - BASE, self.bindings.get(site, f"func_{target:08X}")]
                          for site, target in sorted(self.calls.items())],
                "divisors": [[site - BASE, divisor] for site, divisor in sorted(observed.items())],
                **({"frame": True} if selector else {}),
                "switch": match.switch_layout(self.body, BASE, self.switches)}

    def report(self):
        return (self.root / "docs/match/08000000.md").read_text()

    # Positive -----------------------------------------------------------

    def test_default_path_admits_a_frameless_switch_and_replays(self):
        self.fixture()
        self.assertTrue(self.switches)
        self.assertEqual(len(self.bindings), 2)
        code, _ = self.cli()
        self.assertEqual(code, 0)
        report = self.report()
        self.assertIn(f"* verification: `{profile.SWITCH_SCHEMA}`", report.splitlines())
        self.assertIn(f"* signed quotient: {profile.SWITCH_SUMMARY}", report.splitlines())
        self.assertFalse(any(line.startswith(("* switches", "* switch manifest")) for line in report.splitlines()))
        manifest = json.loads(report.split("* signed quotient manifest: `")[1].split("`")[0])
        self.assertEqual([divisor for _, divisor in manifest["divisors"]], [6, 6])
        self.assertEqual(manifest, self.manifest())
        with self.rom_reads():
            self.assertTrue(evidence.report_matches(report, self.root, BASE))
            self.assertEqual(status.collect(str(self.root), verify=False, quiet=True)[1], 1)
            bound = re.search(r'"bound":(\d+)', report)
            for name, changed in (
                    ("schema", report.replace(profile.SWITCH_SCHEMA, profile.SCHEMA)),
                    ("summary", report.replace(profile.SWITCH_SUMMARY, profile.SUMMARY)),
                    ("framed schema", report.replace(profile.SWITCH_SCHEMA, profile.FRAMED_SWITCH_SCHEMA)),
                    ("bound", report.replace(bound.group(0), f'"bound":{int(bound.group(1)) + 1}')),
                    ("switch lines", report + "\n* switches: forged")):
                with self.subTest(changed=name):
                    self.assertFalse(evidence.report_matches(changed, self.root, BASE))
            # The proof digest separates the switch schema from the plain one, and a
            # relabelling as the plain schema and summary still carries the switch.
            body = bytes.fromhex(report.split("* compiled : `")[1].split("`")[0])
            plain = profile.SCHEMA.encode("ascii")
            digest = __import__("hashlib").sha256()
            for payload in (plain, BASE.to_bytes(4, "little"), body, profile.manifest_text(manifest).encode("ascii")):
                digest.update(len(payload).to_bytes(8, "little")); digest.update(payload)
            proof = report.split("* signed quotient proof SHA-256: `")[1].split("`")[0]
            self.assertEqual(proof, profile.fingerprint(BASE, body, manifest))
            self.assertNotEqual(proof, digest.hexdigest(), "the switch schema separates the proof digest")
            relabelled = report.replace(profile.SWITCH_SCHEMA, profile.SCHEMA).replace(
                profile.SWITCH_SUMMARY, profile.SUMMARY)
            self.assertFalse(evidence.report_matches(relabelled, self.root, BASE))

    def test_framed_selector_admits_a_framed_switch_and_status_restores_it(self):
        self.fixture(source=FRAMED)
        with self.assertRaisesRegex(SystemExit, "fixed frames"):
            self.cli()
        code, _ = self.cli("--signed-quotient-profile", profile.FRAMED_SELECTOR)
        self.assertEqual(code, 0)
        report = self.report()
        self.assertIn(f"* verification: `{profile.FRAMED_SWITCH_SCHEMA}`", report.splitlines())
        self.assertIn(f"* signed quotient: {profile.FRAMED_SWITCH_SUMMARY}", report.splitlines())
        manifest = json.loads(report.split("* signed quotient manifest: `")[1].split("`")[0])
        self.assertEqual(manifest, self.manifest(profile.FRAMED_SELECTOR))
        with self.rom_reads():
            self.assertTrue(evidence.report_matches(report, self.root, BASE))
            commands = []
            original_run = fixtures.subprocess.run
            def run(command, *args, **kwargs):
                if len(command) > 1 and str(command[1]).endswith("/match.py"):
                    commands.append(command)
                    code, stdout = self.cli(*command[5:])
                    return fixtures.subprocess.CompletedProcess(command, code, stdout, "")
                return original_run(command, *args, **kwargs)
            with patch.object(status.subprocess, "run", run):
                self.assertEqual(status.collect(str(self.root), verify=True, quiet=True)[1], 1)
            self.assertEqual(len(commands), 1)
            self.assertIn(profile.FRAMED_SELECTOR, commands[0])
            self.assertFalse(evidence.report_matches(
                report.replace(profile.FRAMED_SWITCH_SCHEMA, profile.FRAMED_SCHEMA), self.root, BASE))

    # Boundaries --------------------------------------------------------------

    def test_disabled_policy_restores_every_refusal(self):
        self.fixture()
        manifest = self.manifest()
        with patch.object(switches.POLICY, "enabled", False):
            with self.assertRaisesRegex(SystemExit, re.escape(PLAIN)):
                self.cli()
            with self.assertRaisesRegex(ValueError, "isolated direct-call profile"):
                self.manifest()
            with self.assertRaisesRegex(ValueError, "invalid signed quotient manifest"):
                match.verify_divsi3(self.body, BASE, self.rom, self.mapping, manifest)
        self.assertFalse((self.root / "docs/match/08000000.md").exists())
        match.verify_divsi3(self.body, BASE, self.rom, self.mapping, manifest)

    def test_a_divisor_joined_across_cases_is_refused(self):
        self.fixture(source=JOINED)
        self.assertTrue(self.switches)
        with self.assertRaisesRegex(ValueError, "CFG-proven positive signed32"):
            self.manifest()
        with self.assertRaisesRegex(SystemExit, "CFG-proven positive signed32"):
            self.cli()

    def test_switch_descriptor_and_relocations_are_checked(self):
        self.fixture()
        manifest = self.manifest()
        self.assertEqual(match.verify_divsi3(self.body, BASE, self.rom, self.mapping, manifest)[0].address, BASE)
        changes = {
            "bound": lambda m: m["switch"].__setitem__("bound", m["switch"]["bound"] + 1),
            "dropped relocation": lambda m: m["switch"]["relocations"].pop(),
            "no relocations": lambda m: m["switch"].__setitem__("relocations", []),
            "case target": lambda m: m["switch"]["relocations"][0].__setitem__(
                1, m["switch"]["relocations"][1][1]),
            "not a dict": lambda m: m.__setitem__("switch", []),
            "string offset": lambda m: m["switch"]["relocations"][0].__setitem__(0, "0"),
            "non-pair record": lambda m: m["switch"]["relocations"].append(5),
            "frame without selector": lambda m: m.__setitem__("frame", True),
        }
        for name, change in changes.items():
            changed = copy.deepcopy(manifest)
            change(changed)
            with self.subTest(change=name), self.assertRaises(ValueError):
                match.verify_divsi3(self.body, BASE, self.rom, self.mapping, changed)
        stripped = {key: value for key, value in manifest.items() if key != "switch"}
        with self.assertRaises(ValueError):
            match.verify_divsi3(self.body, BASE, self.rom, self.mapping, stripped)
        self.assertNotEqual(profile.fingerprint(BASE, self.body, manifest),
                            profile.fingerprint(BASE, self.body, stripped))

    def test_source_replay_compares_the_fresh_switch_relocations(self):
        self.fixture()
        manifest = self.manifest()
        digest = evidence.source_fingerprint(self.root, BASE)
        def replay(candidate):
            with self.rom_reads():
                return match.verify_divsi3_source(self.root, BASE, self.body, self.rom, self.mapping,
                                                  digest, candidate)
        self.assertEqual(replay(manifest)[0].address, BASE)
        moved = copy.deepcopy(manifest)
        moved["switch"]["relocations"][0][1] += 2
        stripped = {key: value for key, value in manifest.items() if key != "switch"}
        for name, candidate in (("moved addend", moved), ("no switch", stripped)):
            with self.subTest(candidate=name), \
                    self.assertRaisesRegex(ValueError, "fresh canonical ELF provenance"):
                replay(candidate)

    def test_other_compositions_stay_refused(self):
        literal = FRAMELESS.replace("extern int func_08000200(int, int);",
                                    "extern int func_08000200(int, int);\nextern int data_02001000;").replace(
            "case 2: return value + 7;", "case 2: return value + data_02001000;")
        (self.root / "config").mkdir(exist_ok=True)
        (self.root / "config/data_symbols.json").write_text('{"data_02001000": "0x02001000"}')
        self.fixture()
        (self.root / "src/08000000.c").write_text(literal)
        with self.assertRaisesRegex(SystemExit, re.escape(PLAIN)):
            self.cli()
        remainder = FRAMELESS.replace("value - 9", "value % 9")
        (self.root / "src/08000000.c").write_text(remainder)
        with self.assertRaises(SystemExit) as raised:
            self.cli()
        self.assertNotIn("MATCH", str(raised.exception))


for name in [name for name in vars(fixtures.FramedQuotientTests) if name.startswith("test_")]:
    setattr(QuotientSwitchTests, name, None)


if __name__ == "__main__":
    unittest.main()
