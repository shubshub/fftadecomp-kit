"""Mixed-return inert spins: optional typed named data and terminal tails."""

import argparse
from contextlib import redirect_stdout
import hashlib
import io
import json
import os
from pathlib import Path
import struct
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import match
import match_evidence as evidence
import inert_spin_profile as profile

A, B = 0x08010000, 0x08020000
OBJECTS = {"data_03000100": "0x03000100"}
TAIL_SOURCE = """extern unsigned char data_03000100[];
extern int func_08020000(int);

int func_08010000(int value)
{
    if (value == 15) {
        data_03000100[0] = 0xA3;
        data_03000100[1] = 0x5D;
        for (;;)
            ;
    }
    return func_08020000(value) + data_03000100[2];
}
"""
ADDEND_SOURCE = """extern int data_03000100[];
extern int data_03000200[];
extern int func_08020000(int *);

int func_08010000(int value)
{
    if (value == 15)
        for (;;)
            ;
    return func_08020000(&data_03000100[4]) + func_08020000(&data_03000200[-1]);
}
"""
PARAMETER_SOURCE = """int func_08010000(unsigned char *state, int value)
{
    if (value == 15) {
        state[0] = 0xA3;
        state[1] = 0x5D;
        for (;;)
            ;
    }
    return state[2] + value;
}
"""
FUNCTION_SOURCE = """extern int func_08020000(int);
typedef int (*Handler)(int);

Handler func_08010000(int value)
{
    if (value == 15)
        for (;;)
            ;
    return func_08020000;
}
"""
PLAIN_SOURCE = """extern int func_08020000(int);

int func_08010000(int value)
{
    if (value == 15)
        for (;;)
            ;
    return func_08020000(value);
}
"""
# cmp r0,#15; beq 6; bx lr; movs r1,#0xA3; strb r1,[r2]; b .
TAIL = [0x280F, 0xD000, 0x4770, 0x21A3, 0x7011, 0xE7FE]
# cmp r0,#15; beq 6; bx lr; ldr r1,[pc,#8]; movs r2,#0xA3; strb r2,[r1]; b .; nop;
# then two copies of the object address, only the first of which is loaded.
POOL = [0x280F, 0xD000, 0x4770, 0x4902, 0x22A3, 0x700A, 0xE7FE, 0x46C0]


def body(words, literals=()):
    return b"".join(struct.pack("<H", word) for word in words) + \
        b"".join(struct.pack("<I", word) for word in literals)


def bl(site, target):
    offset = target - (site + 4)
    return [0xF000 | (offset >> 12) & 0x7FF, 0xF800 | (offset >> 1) & 0x7FF]


def indexes(size):
    rows = [{"rom": f"0x{A:08X}", "end": f"0x{A + size:08X}", "mode": "thumb", "instrs": 1},
            {"rom": f"0x{B:08X}", "end": f"0x{B + 2:08X}", "mode": "thumb", "instrs": 1}]
    return json.dumps(rows).encode(), "".join(
        f"{int(r['rom'], 16):08X} {int(r['end'], 16):08X} "
        f"{int(r['end'], 16) - int(r['rom'], 16)} {r['instrs']} return\n" for r in rows).encode()


def image(data):
    rom = bytearray(B - match.ROM_BASE + 2)
    rom[A - match.ROM_BASE:A - match.ROM_BASE + len(data)] = data
    return bytes(rom)


class TerminalTailTests(unittest.TestCase):
    """The walker and the profile's manifest check, on exact Thumb encodings."""

    def walk(self, words, calls=None, context=None):
        return match.verify_leaf_instructions(body(words), A, True, calls or {},
                                              inert_spin_context={"tails": []} if context is None else context)

    def verify(self, data, manifest, objects=None):
        mapping, index = indexes(len(data))
        return profile.verify(data, A, image(data), mapping, index, manifest,
                              data_mapping=None if objects is None else json.dumps(objects).encode())

    def test_store_prefix_before_self_branch_is_a_terminal_tail(self):
        context = {"tails": []}
        self.walk(TAIL, context=context)
        self.assertEqual(context, {"spins": [10], "tails": [6, 8]})
        manifest = {"calls": [], "frame": False, "spins": [10], "tails": [6, 8]}
        self.assertEqual(len(self.verify(body(TAIL), manifest)), 6)
        self.assertEqual(profile.summary(manifest), profile.TAIL_SUMMARY)

    def test_tails_are_opt_in_and_bound_by_the_manifest(self):
        # The software-double record and the old manifest keep the self-branch-only rule.
        with self.assertRaisesRegex(ValueError, "must itself be an inert narrow self-branch"):
            self.walk(TAIL, context={})
        for context in ({"tails": [6]}, {"tails": ()}, {"spins": []}, {"tails": [], "spins": []}):
            with self.subTest(context=context), self.assertRaisesRegex(ValueError, "fresh isolated"):
                self.walk(TAIL, context=context)
        for tails in (None, [6], [8], [8, 6], [6, 8, 10], [6, 6, 8], [], [True, 8], [6.0, 8]):
            manifest = {"calls": [], "frame": False, "spins": [10]}
            if tails is not None:
                manifest["tails"] = tails
            with self.subTest(tails=tails), self.assertRaises(ValueError):
                self.verify(body(TAIL), manifest)
        spin = [0x280F, 0xD000, 0x4770, 0xE7FE]
        context = {"tails": []}
        self.walk(spin, context=context)
        self.assertEqual(context, {"spins": [6], "tails": []})
        self.verify(body(spin), {"calls": [], "frame": False, "spins": [6]})
        with self.assertRaises(ValueError):
            self.verify(body(spin), {"calls": [], "frame": False, "spins": [6], "tails": [6]})

    def test_branches_calls_stack_changes_and_indirect_transfers_in_a_tail_refuse(self):
        cases = {
            "conditional": (TAIL[:4] + [0xD0FF] + TAIL[5:], "straight-line"),
            "stack adjustment": (TAIL[:4] + [0xB081] + TAIL[5:], "straight-line"),
            "push": (TAIL[:4] + [0xB410] + TAIL[5:], "straight-line"),
            "register to sp": (TAIL[:4] + [0x468D] + TAIL[5:], None),
            "indirect": (TAIL[:4] + [0x4708] + TAIL[5:], None),
            "pc write": (TAIL[:4] + [0x468F] + TAIL[5:], None),
            "interrupt": (TAIL[:4] + [0xDF00] + TAIL[5:], None),
            "two-instruction cycle": (TAIL[:5] + [0xE7FD], "straight-line"),
            "forward branch": (TAIL[:4] + [0xE000, 0x46C0, 0xE7FE], "straight-line"),
        }
        for name, (words, message) in cases.items():
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, message or ""):
                self.walk(words)
        call = TAIL[:3] + bl(A + 6, B) + [0xE7FE]
        with self.assertRaisesRegex(ValueError, "straight-line"):
            self.walk(call, calls={A + 6: B})
        # ldr r1,[pc,#4]; add sp,r1 with the literal -8: a literal stack adjustment.
        literal = TAIL[:3] + [0x4901, 0x448D, 0xE7FE]
        with self.assertRaisesRegex(ValueError, "straight-line"):
            match.verify_leaf_instructions(body(literal, (0xFFFFFFF8,)), A, True, {},
                                           inert_spin_context={"tails": []})

    def test_a_function_without_a_return_is_still_refused(self):
        with self.assertRaisesRegex(ValueError, "no verified return"):
            self.walk([0x21A3, 0x7011, 0xE7FE])
        with self.assertRaisesRegex(ValueError, "no verified return"):
            self.walk([0xE7FE])

    def test_typed_data_record_binds_aligned_loaded_mapped_words(self):
        data = body(POOL, (0x03000100, 0x03000100))
        manifest = {"calls": [], "data": [[16, "data_03000100", 0]], "frame": False,
                    "spins": [12], "tails": [6, 8, 10]}
        self.verify(data, manifest, OBJECTS)
        for addend in (-4, 16):
            changed = body(POOL, (0x03000100 + addend, 0x03000100))
            with self.subTest(addend=addend):
                self.verify(changed, dict(manifest, data=[[16, "data_03000100", addend]]), OBJECTS)
        refusals = {
            "not loaded": ([[20, "data_03000100", 0]], OBJECTS, "PC-relative"),
            "misaligned": ([[18, "data_03000100", 0]], OBJECTS, "aligned"),
            "unmapped": ([[16, "data_03000200", 0]], OBJECTS, "mapped"),
            "wrong addend": ([[16, "data_03000100", 4]], OBJECTS, "differs"),
            "duplicate": ([[16, "data_03000100", 0]] * 2, OBJECTS, "ordered"),
            "float addend": ([[16, "data_03000100", 0.0]], OBJECTS, "mapped"),
            "boolean offset": ([[True, "data_03000100", 0]], OBJECTS, "mapped"),
            "short": ([[16, "data_03000100"]], OBJECTS, "binding"),
            "empty": ([], OBJECTS, "manifest"),
            "no data map": ([[16, "data_03000100", 0]], None, "manifest"),
            "own function": ([[16, "data_self", 0]], {"data_self": f"0x{A:08X}"}, "own function"),
        }
        for name, (records, objects, message) in refusals.items():
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, message):
                self.verify(data, dict(manifest, data=records), objects)
        own = body(POOL, (A, A))
        with self.assertRaisesRegex(ValueError, "own function"):
            self.verify(own, dict(manifest, data=[[16, "data_self", 0]]), {"data_self": f"0x{A:08X}"})

    def test_reports_without_records_keep_their_digest(self):
        manifest = {"calls": [], "frame": False, "spins": [6]}
        arguments = (A, body([0x280F, 0xD000, 0x4770, 0xE7FE]), manifest, "0" * 64, b"[]", b"")
        self.assertEqual(profile.fingerprint(*arguments),
                         profile.fingerprint(*arguments, data_mapping=json.dumps(OBJECTS).encode()))
        digest = hashlib.sha256()
        for payload in (profile.SCHEMA.encode(), A.to_bytes(4, "little"), arguments[1],
                        profile.manifest_text(manifest).encode(), arguments[3].encode(),
                        hashlib.sha256(b"[]").hexdigest().encode(), hashlib.sha256(b"").hexdigest().encode(),
                        profile.compiler_text().encode()):
            digest.update(len(payload).to_bytes(8, "little"))
            digest.update(payload)
        self.assertEqual(profile.fingerprint(*arguments), digest.hexdigest())
        self.assertEqual(profile.summary(manifest), profile.SUMMARY)
        typed = dict(manifest, data=[[16, "data_03000100", 0]])
        with self.assertRaisesRegex(ValueError, "exact data mapping"):
            profile.fingerprint(*arguments[:2], typed, *arguments[3:])
        self.assertNotEqual(
            profile.fingerprint(*arguments[:2], typed, *arguments[3:], data_mapping=json.dumps(OBJECTS).encode()),
            profile.fingerprint(*arguments[:2], typed, *arguments[3:],
                                data_mapping=json.dumps(dict(OBJECTS, data_03000200="0x03000200")).encode()))


class CompiledInertSpinTests(unittest.TestCase):
    """Original-ELF provenance, the written report and its fresh replay."""

    def setUp(self):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", Path(__file__).resolve().parents[1] / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="inert_spin_", dir=scratch)
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        for name in ("src", "include", "config", "symbols"):
            (self.root / name).mkdir()
        environment = patch.dict(os.environ, {"TMPDIR": str(self.root), "PYTHONDONTWRITEBYTECODE": "1",
                                               "FFTA_ROM": str(self.root / "baserom.bin")})
        environment.start()
        self.addCleanup(environment.stop)
        self.args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                                       objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD,
                                       flags=match.DEFAULT_FLAGS)

    def fixture(self, source, objects=OBJECTS):
        (self.root / "src/08010000.c").write_text(source)
        (self.root / "config/data_symbols.json").write_text(json.dumps(objects, indent=2) + "\n")
        self.objects = (self.root / "config/data_symbols.json").read_bytes()
        runner = match.Runner(match.DEFAULT_CC, root=self.root, timeout=120)
        with runner.workspace() as workspace:
            _, _, self.original = match.compile_object(runner, workspace, self.args, self.root, A,
                                                       "src/08010000.c")
            symbol, _ = match.function_record(self.original, "func_08010000", A, True)
            self.mapping, self.index = indexes(symbol["size"])
            self.literals = {}
            self.body, self.calls = profile.object_bytes(
                runner, workspace, self.args, self.original, A, self.mapping, image(b""),
                data_mapping=self.objects, data_relocations=self.literals)
        self.rom = image(self.body)
        for name, data in (("baserom.bin", self.rom), ("config/functions.json", self.mapping),
                           ("symbols/functions.txt", self.index)):
            (self.root / name).write_bytes(data)

    def native_report(self):
        with patch.object(sys, "argv", ["match.py", "--root", str(self.root), "--control-flow-profile",
                                        profile.SELECTOR, "0x08010000"]), \
                patch.object(match, "ROOT", match.ROOT), redirect_stdout(io.StringIO()):
            self.assertEqual(match.main(), 0)
        return (self.root / "docs/match/08010000.md").read_text()

    def manifest(self, report):
        line = next(line for line in report.splitlines() if line.startswith("* inert spin manifest: "))
        return json.loads(line.split("`")[1])

    def replays(self, report):
        return evidence.report_matches(report, self.root, A)

    def test_data_with_terminal_tail_matches_and_report_binds_the_data_map(self):
        self.fixture(TAIL_SOURCE)
        report = self.native_report()
        manifest = self.manifest(report)
        self.assertEqual([record[1:] for record in manifest["data"]], [["data_03000100", 0]] * 2)
        self.assertEqual(set(manifest), {"calls", "data", "frame", "spins", "tails"})
        for offset in manifest["spins"]:
            self.assertEqual(self.body[offset:offset + 2], b"\xfe\xe7")
        self.assertEqual(manifest["tails"], list(range(manifest["tails"][0], manifest["spins"][0], 2)))
        self.assertIn(f"* data symbols SHA-256: `{hashlib.sha256(self.objects).hexdigest()}`", report)
        self.assertIn(f"* inert spins: {profile.TAIL_SUMMARY}", report)
        self.assertIn("**MATCH - byte identical**", report)
        self.assertTrue(self.replays(report))

        data_line = f"* data symbols SHA-256: `{hashlib.sha256(self.objects).hexdigest()}`"
        edits = {
            "dropped data line": report.replace(data_line + "\n", ""),
            "duplicated data line": report.replace(data_line, data_line + "\n" + data_line),
            "other data digest": report.replace(data_line, "* data symbols SHA-256: `" + "0" * 64 + "`"),
            "plain summary": report.replace(profile.TAIL_SUMMARY, profile.SUMMARY),
        }
        record = manifest["data"][0]
        for name, changed in (("addend", [record[0], record[1], 4]), ("offset", [record[0] + 4] + record[1:])):
            altered = dict(manifest, data=[changed] + manifest["data"][1:])
            text = report.replace(profile.manifest_text(manifest), profile.manifest_text(altered))
            proof = profile.fingerprint(A, self.body, altered, evidence.source_fingerprint(self.root, A),
                                        self.mapping, self.index, data_mapping=self.objects)
            old = profile.fingerprint(A, self.body, manifest, evidence.source_fingerprint(self.root, A),
                                      self.mapping, self.index, data_mapping=self.objects)
            edits[f"rehashed {name}"] = text.replace(old, proof)
        altered = dict(manifest, data=manifest["data"][:1])
        edits["rehashed dropped record"] = report.replace(profile.manifest_text(manifest),
                                                          profile.manifest_text(altered)).replace(
            profile.fingerprint(A, self.body, manifest, evidence.source_fingerprint(self.root, A),
                                self.mapping, self.index, data_mapping=self.objects),
            profile.fingerprint(A, self.body, altered, evidence.source_fingerprint(self.root, A),
                                self.mapping, self.index, data_mapping=self.objects))
        stripped = {key: value for key, value in manifest.items() if key != "tails"}
        edits["dropped tails"] = report.replace(profile.manifest_text(manifest), profile.manifest_text(stripped))
        for name, changed in edits.items():
            with self.subTest(name=name):
                self.assertNotEqual(changed, report)
                self.assertFalse(self.replays(changed))
        (self.root / "config/data_symbols.json").write_text(json.dumps(dict(OBJECTS, data_03000200="0x03000200")))
        self.assertFalse(self.replays(report))

    def test_signed_addends_match_and_replay(self):
        self.fixture(ADDEND_SOURCE, dict(OBJECTS, data_03000200="0x03000200"))
        self.assertEqual(sorted(self.literals.values()), [("data_03000100", 0x03000110),
                                                          ("data_03000200", 0x030001FC)])
        report = self.native_report()
        manifest = self.manifest(report)
        self.assertEqual(sorted(record[1:] for record in manifest["data"]),
                         [["data_03000100", 16], ["data_03000200", -4]])
        self.assertNotIn("tails", manifest)
        self.assertIn(f"* inert spins: {profile.SUMMARY}", report)
        self.assertTrue(self.replays(report))

    def test_unmapped_object_and_no_opt_in_refuse(self):
        self.fixture(PLAIN_SOURCE)
        (self.root / "src/08010000.c").write_text(TAIL_SOURCE)
        runner = match.Runner(match.DEFAULT_CC, root=self.root, timeout=120)
        with runner.workspace() as workspace:
            _, _, original = match.compile_object(runner, workspace, self.args, self.root, A, "src/08010000.c")
            symbol, _ = match.function_record(original, "func_08010000", A, True)
            mapping, _ = indexes(symbol["size"])
            for objects in (b"{}", json.dumps({"data_03000200": "0x03000200"}).encode(), None):
                with self.subTest(objects=objects), self.assertRaisesRegex(ValueError, "mapped global object"):
                    profile.object_bytes(runner, workspace, self.args, original, A, mapping, image(b""),
                                         data_mapping=objects, data_relocations={})
            with self.assertRaisesRegex(ValueError, "exclude non-call relocations"):
                profile.object_bytes(runner, workspace, self.args, original, A, mapping, image(b""),
                                     data_mapping=self.objects)
        (self.root / "src/08010000.c").write_text(FUNCTION_SOURCE)
        with runner.workspace() as workspace:
            _, _, original = match.compile_object(runner, workspace, self.args, self.root, A, "src/08010000.c")
            symbol, _ = match.function_record(original, "func_08010000", A, True)
            mapping, _ = indexes(symbol["size"])
            with self.assertRaisesRegex(ValueError, "exclude function-address relocations"):
                profile.object_bytes(runner, workspace, self.args, original, A, mapping, image(b""),
                                     data_mapping=self.objects, data_relocations={})

    def test_tail_without_data_and_plain_spin_keep_their_shapes(self):
        self.fixture(PARAMETER_SOURCE)
        report = self.native_report()
        manifest = self.manifest(report)
        self.assertEqual(set(manifest), {"calls", "frame", "spins", "tails"})
        self.assertNotIn("* data symbols", report)
        self.assertTrue(self.replays(report))
        forged = report.replace("* inert spins:", f"* data symbols SHA-256: `{hashlib.sha256(self.objects).hexdigest()}`"
                                "\n* inert spins:")
        self.assertFalse(self.replays(forged))
        self.fixture(PLAIN_SOURCE)
        report = self.native_report()
        manifest = self.manifest(report)
        self.assertEqual(set(manifest), {"calls", "frame", "spins"})
        self.assertIn(f"* inert spins: {profile.SUMMARY}", report)
        self.assertNotIn("* data symbols", report)
        self.assertTrue(self.replays(report))


if __name__ == "__main__":
    unittest.main()
