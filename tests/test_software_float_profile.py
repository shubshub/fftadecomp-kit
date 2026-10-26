"""Pinned software float: native compiler fixtures and fail-closed runtime evidence.

Only the locally approved ROM supplies runtime bodies in memory. No
ROM-derived body or disassembly is checked into the toolkit.
"""

import argparse
import builtins
import copy
from contextlib import redirect_stdout
import io
import hashlib
import struct
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import software_float_profile as profile
import match
import match_evidence as evidence

BASE = 0x08000000
SOURCE = """extern unsigned g_enabled;
extern void func_08000200(unsigned);
unsigned func_08000000(float volume, float factor)
{
    unsigned result = (unsigned)(volume * factor);
    if (g_enabled)
        func_08000200(result);
    return result;
}
"""


class SoftwareFloatTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        selected = os.environ.get("FFTA_ROM")
        if not selected or not Path(selected).is_file():
            raise unittest.SkipTest("FFTA_ROM must reference the approved ROM")
        cls.rom_path = Path(selected).resolve()
        cls.runtime_rom = cls.rom_path.read_bytes()
        if hashlib.sha256(cls.runtime_rom).hexdigest() != profile.ROM_SHA256:
            raise unittest.SkipTest("FFTA_ROM is not the approved image")

    def setUp(self):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="software_float_", dir=scratch)
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        for name in ("src", "include", "config", "symbols"):
            (self.root / name).mkdir()
        environment = patch.dict(os.environ, {"TMPDIR": str(self.root),
                                               "PYTHONDONTWRITEBYTECODE": "1"})
        environment.start()
        self.addCleanup(environment.stop)
        self.args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP,
                                       assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY,
                                       linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)

    def indexes(self, size, count):
        entries = [{"rom": f"0x{BASE:08X}", "end": f"0x{BASE + size:08X}",
                    "mode": "thumb", "instrs": count},
                   {"rom": "0x08000200", "end": "0x08000202", "mode": "thumb", "instrs": 1}]
        entries.extend({"rom": f"0x{a:08X}", "end": f"0x{b:08X}", "mode": "thumb", "instrs": n}
                       for a, b, n, _ in profile.IDENTITIES)
        self.mapping = json.dumps(entries).encode()
        self.index = "".join(f"{int(e['rom'], 16):08X} {int(e['end'], 16):08X} "
                             f"{int(e['end'], 16) - int(e['rom'], 16)} {e['instrs']} return\n"
                             for e in entries).encode()

    def fixture(self, source=SOURCE, assembly=None):
        # Synthetic callers alter only an in-memory image. The test policy
        # permits that image; native runtime hashes/CFG/ABI remain pinned.
        if getattr(self, "rom_policy", None) is not None:
            self.rom_policy.stop()
        (self.root / "src/08000000.c").write_text(source)
        runner = match.Runner(match.DEFAULT_CC, root=self.root, timeout=120)
        with runner.workspace() as workspace:
            if assembly is None:
                _, _, original = match.compile_object(
                    runner, workspace, self.args, self.root, BASE, "src/08000000.c")
            else:
                text = (".syntax unified\n.arch armv4t\n.thumb\n.text\n"
                        ".global func_08000000\n.type func_08000000, %function\n"
                        ".thumb_func\nfunc_08000000:\n" + assembly +
                        "\n.size func_08000000, . - func_08000000\n")
                path = Path(workspace) / "f.s"
                path.write_text(text)
                subprocess.run([self.args.assembler, "-mthumb-interwork", str(path),
                                "-o", str(Path(workspace) / "f.o")],
                               capture_output=True, check=True, timeout=120)
                original = match.elf_image((Path(workspace) / "f.o").read_bytes())
            symbol, _ = match.function_record(original, "func_08000000", BASE, True)
            self.indexes(symbol["size"], 1)
            self.objects = json.dumps({"g_enabled": "0x02000100"}).encode()
            self.bindings = {}
            self.body, self.calls, self.literals = match.link_calls(
                runner, workspace, self.args, original, BASE, self.mapping,
                len(self.runtime_rom), bytes(self.runtime_rom), data_mapping=self.objects,
                float_bindings=self.bindings, float_index=self.index)
            self.original = original
            self.linked = match.elf_image((Path(workspace) / "f.elf").read_bytes())
        rom = bytearray(self.runtime_rom)
        rom[:len(self.body)] = self.body
        self.rom = bytes(rom)
        self.rom_policy = patch.object(profile, "ROM_SHA256", hashlib.sha256(self.rom).hexdigest())
        self.rom_policy.start()
        self.addCleanup(self.rom_policy.stop)
        self.instructions = match.verify_leaf_instructions(
            self.body, BASE, True, self.calls,
            float_context=(self.rom, self.mapping, self.index, self.bindings))
        self.indexes(len(self.body), len(self.instructions))
        (self.root / "config/functions.json").write_bytes(self.mapping)
        (self.root / "symbols/functions.txt").write_bytes(self.index)
        (self.root / "config/data_symbols.json").write_bytes(self.objects)
        self.manifest = profile.make_manifest(self.calls, BASE, self.bindings, self.literals,
                                              self.objects, self.instructions)

    def verify(self, manifest=None):
        return profile.verify(self.body, BASE, self.rom, self.mapping, self.index, self.objects,
                              self.manifest if manifest is None else manifest)

    def patched_rom(self):
        original_open, original_read = builtins.open, Path.read_bytes
        def open_file(path, mode="r", *args, **kwargs):
            if mode == "rb" and Path(path).resolve() == self.rom_path:
                return io.BytesIO(self.rom)
            return original_open(path, mode, *args, **kwargs)
        def read(path):
            return self.rom if path.resolve() == self.rom_path else original_read(path)
        return patch.object(builtins, "open", open_file), patch.object(Path, "read_bytes", read)

    def native_report(self):
        opening, reading = self.patched_rom()
        with opening, reading, patch.object(sys, "argv", ["match.py", "--root", str(self.root),
                                                           "0x08000000"]), \
                patch.object(match, "ROOT", match.ROOT), redirect_stdout(io.StringIO()):
            self.assertEqual(match.main(), 0)
        return (self.root / "docs/match/08000000.md").read_text()

    def binding(self, original=None, **kwargs):
        return match.call_bindings(self.original if original is None else original,
                                   "func_08000000", BASE, self.mapping, len(self.rom), self.rom,
                                   data_mapping=self.objects, float_bindings={}, float_index=self.index,
                                   **kwargs)

    def test_native_helpers_data_ordinary_calls_and_scalar_frame(self):
        self.fixture()
        self.assertEqual(set(self.bindings.values()), set(profile.OPERATIONS))
        self.assertTrue(self.manifest["data"])
        self.assertIn(0x08000200, self.calls.values())
        self.assertEqual(len(self.verify()), len(self.instructions))
        with self.assertRaisesRegex(ValueError, "canonical runtime"):
            match.verify_leaf_instructions(self.body, BASE, True, self.calls)
        self.fixture(assembly="push {lr}\nsub sp, #4\nstr r0, [sp]\nbl __mulsf3\n"
                              "bl __fixunssfsi\nadd sp, #4\npop {r1}\nbx r1")
        self.assertTrue(self.manifest["frame"])
        self.verify()

    def test_complete_rom_runtime_and_unique_dual_ownership(self):
        self.fixture()
        proofs = profile.verify_identity(self.rom, self.mapping, self.index)
        self.assertEqual(set(proofs), {a for a, _, _, _ in profile.IDENTITIES})
        self.assertFalse(proofs[profile.OPERATIONS["__mulsf3"]]["writes"])
        changed = bytearray(self.rom); changed[-1] ^= 1
        with self.assertRaisesRegex(ValueError, "approved complete ROM"):
            profile.verify_identity(bytes(changed), self.mapping, self.index)
        changed = bytearray(self.rom); changed[profile.IDENTITIES[0][0] - BASE] ^= 1
        with patch.object(profile, "ROM_SHA256", hashlib.sha256(changed).hexdigest()), \
                self.assertRaisesRegex(ValueError, "runtime identity"):
            profile.verify_identity(bytes(changed), self.mapping, self.index)
        entries = json.loads(self.mapping)
        for change in ("duplicate", "overlap", "short", "arm", "count", "odd", "missing"):
            altered = copy.deepcopy(entries)
            if change == "duplicate": altered.append(copy.deepcopy(altered[2]))
            elif change == "overlap":
                altered.append({"rom": "0x081428AE", "end": "0x081428B0", "mode": "thumb", "instrs": 1})
            elif change == "short": altered[2]["end"] = "0x081428E0"
            elif change == "arm": altered[2]["mode"] = "arm"
            elif change == "count": altered[2]["instrs"] += 1
            elif change == "odd": altered[2]["rom"] = "0x081428AD"
            else: altered.pop(2)
            with self.subTest(change=change), self.assertRaises(ValueError):
                profile.verify_identity(self.rom, json.dumps(altered).encode(), self.index)
        for index in (self.index + self.index.splitlines()[2] + b"\n",
                      self.index.replace(b"081428E4 56 19", b"081428E0 52 19"),
                      self.index.replace(b"081428E4 56 19", b"081428E4 56 20")):
            with self.subTest(index=index[-100:]), self.assertRaises(ValueError):
                profile.verify_identity(self.rom, self.mapping, index)
        with self.assertRaises(ValueError):
            profile.verify_identity(self.rom[:100], self.mapping, self.index)

    def test_native_abi_rejects_unrestored_register_and_unbounded_write(self):
        self.fixture()
        proofs = profile.verify_identity(self.rom, self.mapping, self.index)
        from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
        start, end, count, _ = next(record for record in profile.IDENTITIES if record[0] == 0x08143A84)
        decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
        instructions = [i for a, b in proofs[start]["layout"]["code_ranges"]
                        for i in decoder.disasm(self.rom[int(a, 16) - BASE:int(b, 16) - BASE], int(a, 16))]
        for kind in ("restore", "write"):
            instruction = next(i for i in instructions if i.mnemonic == ("pop" if kind == "restore" else "str"))
            altered = bytearray(self.rom)
            position = instruction.address - BASE
            word = struct.unpack_from("<H", altered, position)[0]
            if kind == "restore": word ^= (1 << 4) | (1 << 5)
            else: word = (word & ~0x38) | (4 << 3)
            struct.pack_into("<H", altered, position, word)
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                profile.prove_runtime(bytes(altered), json.loads(self.mapping), start, end, count, {})

    def test_canonical_helper_names_symbols_addends_and_linked_bytes(self):
        self.fixture()
        for a, b, _, _ in profile.IDENTITIES:
            for target in (a, a | 1, a + 2, b - 2):
                with self.subTest(target=target), self.assertRaises(ValueError):
                    match.function_address_target(f"func_{target:08X}", json.loads(self.mapping),
                                                  BASE, len(self.body), len(self.rom))
                with self.subTest(target=target), self.assertRaises(ValueError):
                    match.parse_data_symbols(json.dumps({"object": f"0x{target:08X}"}).encode())
        for name in ("__mulsf3_alias", "func_08143CEC", "func_08143CEE", "func_08143CED"):
            altered = copy.deepcopy(self.original)
            for symbol in altered["symbols"]:
                if symbol["name"] == "__mulsf3": symbol["name"] = name
            with self.subTest(name=name), self.assertRaises(ValueError): self.binding(altered)
        for helper in profile.OPERATIONS:
            for key, value in (("section", 1), ("bind", 2), ("type", 1), ("value", 2)):
                altered = copy.deepcopy(self.original)
                for symbol in altered["symbols"]:
                    if symbol["name"] == helper: symbol[key] = value
                with self.subTest(helper=helper, key=key), self.assertRaises(ValueError): self.binding(altered)
        for helper in profile.OPERATIONS:
            with self.subTest(helper=helper), self.assertRaisesRegex(ValueError, "noncanonical addend"):
                self.fixture(assembly=f"push {{lr}}\nbl {helper}+2\npop {{r1}}\nbx r1")
        self.fixture()
        targets = dict(profile.OPERATIONS, g_enabled=0x02000100, func_08000200=0x08000200)
        altered = copy.deepcopy(self.linked)
        text = bytearray(altered["text"]); text[0] ^= 1; altered["text"] = bytes(text)
        with self.assertRaisesRegex(ValueError, "outside permitted relocations"):
            match.linked_function_bytes(self.original, altered, "func_08000000", BASE,
                                        self.calls, targets, self.literals, float_bindings=self.bindings)
        with self.assertRaises(ValueError):
            match.linked_function_bytes(self.original, self.linked, "func_08000000", BASE,
                                        self.calls, targets, self.literals)

    def test_complete_exact_caller_and_manifest(self):
        self.fixture()
        for key, value in (("frame", not self.manifest["frame"]), ("data", []), ("calls", []),
                           ("dependencies", []), ("abi", "generic"), ("semantics", "IEEE754")):
            altered = copy.deepcopy(self.manifest); altered[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError): self.verify(altered)
        for changed in (self.body[:-2], self.body + b"\0\0", bytes([self.body[0] ^ 1]) + self.body[1:]):
            with self.subTest(size=len(changed)), self.assertRaises(ValueError):
                profile.verify(changed, BASE, self.rom, self.mapping, self.index, self.objects, self.manifest)
        for context in ({}, (self.rom, self.mapping, self.index, {})):
            with self.assertRaises(ValueError):
                match.verify_leaf_instructions(self.body, BASE, True, self.calls, float_context=context)

    def test_profile_combinations_and_bad_return_fail_closed(self):
        self.fixture()
        for other in ("buffer_proof", "call_resolver", "switch_relocations", "switch_data_relocations",
                      "udivsi3_context", "modsi3_context", "divsi3_context", "umodsi3_context",
                      "ashldi3_context", "inert_spin_context", "double_context", "function_thunk_context"):
            with self.subTest(other=other), self.assertRaises(ValueError):
                match.verify_leaf_instructions(self.body, BASE, True, self.calls,
                    float_context=(self.rom, self.mapping, self.index, self.bindings), **{other: {}})
        for other in ("udivsi3_bindings", "modsi3_bindings", "divsi3_bindings", "umodsi3_bindings",
                      "ashldi3_bindings", "double_bindings", "function_relocations", "switch_relocations"):
            with self.subTest(other=other), self.assertRaises(ValueError):
                self.binding(**{other: {1: "unsupported"}})
        changed = copy.copy(self.args); changed.flags = "-mthumb-interwork -O1"
        with self.assertRaises(ValueError): profile.fixed_configuration(changed)
        for assembly in ("push {lr}\nsub sp, #4\nbl __mulsf3\npop {r1}\nbx r1",
                         "push {lr}\nbl __mulsf3\nbl __ashldi3\npop {r1}\nbx r1",
                         "push {lr}\nbl __mulsf3\nbl _call_via_r0\npop {r1}\nbx r1"):
            with self.subTest(assembly=assembly), self.assertRaises(ValueError): self.fixture(assembly=assembly)

    def test_native_report_rejects_stale_source_maps_rom_and_proof(self):
        self.fixture()
        report = self.native_report()
        self.assertIn(f"* verification: `{profile.SCHEMA}`", report)
        opening, reading = self.patched_rom()
        with opening, reading, redirect_stdout(io.StringIO()):
            self.assertTrue(evidence.report_matches(report, self.root, BASE))
            for changed in (report + "\n* ashldi3: forged", report + "\n* software double: forged",
                            report + "\n* software float: duplicate", report.replace("-O2", "-O1"),
                            report.replace(profile.SCHEMA, evidence.DATA_SCHEMA),
                            report.replace('"dependencies":[', '"dependencies":[],'),
                            report.replace("* software float proof SHA-256: `", "* software float proof SHA-256: `0")):
                with self.subTest(changed=changed[-100:]):
                    self.assertFalse(evidence.report_matches(changed, self.root, BASE))
            for name in ("symbols/functions.txt", "config/functions.json", "config/data_symbols.json"):
                path = self.root / name; original = path.read_bytes(); path.write_bytes(original + b"\n")
                with self.subTest(name=name): self.assertFalse(evidence.report_matches(report, self.root, BASE))
                path.write_bytes(original)
            original_rom = self.rom
            changed_rom = bytearray(original_rom); changed_rom[-1] ^= 1
            self.rom = bytes(changed_rom)
            self.assertFalse(evidence.report_matches(report, self.root, BASE))
            self.rom = original_rom
            source = self.root / "src/08000000.c"
            original_digest = evidence.source_fingerprint(self.root, BASE)
            source.write_text(source.read_text().replace("return result;", "return result + 1;"))
            new_digest = evidence.source_fingerprint(self.root, BASE)
            forged = report.replace(original_digest, new_digest).replace(
                profile.fingerprint(BASE, self.body, self.manifest, original_digest,
                                    self.mapping, self.index, self.objects, self.rom),
                profile.fingerprint(BASE, self.body, self.manifest, new_digest,
                                    self.mapping, self.index, self.objects, self.rom))
            self.assertFalse(evidence.report_matches(report, self.root, BASE))
            self.assertFalse(evidence.report_matches(forged, self.root, BASE))


if __name__ == "__main__":
    unittest.main()

