"""Synthetic ELF proofs for callbacks loaded from a caller's context.

Assembly fixtures exercise relocation and CFG checking, not C match credit.
"""

import argparse
import copy
import json
import os
from pathlib import Path
import struct
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import match
import function_thunk_profile as profile

BASE = match.ROM_BASE
NAME = "func_08000000"


class FunctionThunkContextTests(unittest.TestCase):
    def setUp(self):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="thunk_context_", dir=scratch)
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)

    def fixture(self, *, literal=False, restore=True, canonical=True):
        body = "push {lr}\nldr r2, [r1, #4]\n"
        if literal:
            body += "ldr r0, callback\n"
        body += "bl " + ("_call_via_r2" if canonical else "func_08000100") + "\n"
        body += "pop {r1}\nbx r1\n" if restore else "bx lr\n"
        if literal:
            body += ".balign 4\ncallback:\n.word func_08000200\n"
        assembly = (".syntax unified\n.arch armv4t\n.thumb\n.text\n"
                    f".global {NAME}\n.type {NAME}, %function\n.thumb_func\n"
                    f"{NAME}:\n{body}.size {NAME}, . - {NAME}\n")
        args = argparse.Namespace(assembler=match.DEFAULT_AS, linker=match.DEFAULT_LD,
                                  objcopy=match.DEFAULT_OBJCOPY)
        runner = match.Runner(match.DEFAULT_CC, root=self.root, timeout=120)
        rom = bytearray(profile.END - BASE)
        struct.pack_into("<HH", rom, profile.ALIASES["_call_via_r2"] - BASE,
                         0x4710, 0x46C0)
        with runner.workspace() as workspace:
            source = Path(workspace) / "f.s"
            source.write_text(assembly)
            obj = Path(workspace) / "f.o"
            subprocess.run([args.assembler, "-mthumb-interwork", str(source), "-o", str(obj)],
                           check=True, capture_output=True, timeout=120)
            self.original = match.elf_image(obj.read_bytes())
            symbol, _ = match.function_record(self.original, NAME, BASE, True)
            self.mapping = json.dumps([
                {"rom": f"0x{BASE:08X}", "end": f"0x{BASE + symbol['size']:08X}", "mode": "thumb"},
                {"rom": "0x08000100", "end": "0x08000102", "mode": "thumb"},
                {"rom": "0x08000200", "end": "0x08000202", "mode": "thumb"},
            ]).encode()
            self.index = f"{BASE:08X} {BASE + symbol['size']:08X} {symbol['size']}\n".encode()
            self.rom = bytes(rom)
            self.calls, self.functions, self.literals = profile.original_bindings(
                self.original, BASE, self.mapping, self.rom, None)
            functions = {}
            self.body, calls, literals = match.link_calls(
                runner, workspace, args, self.original, BASE, self.mapping, len(rom),
                self.rom, None, functions, function_thunks=True)
            self.assertEqual((calls, functions, literals),
                             (self.calls, self.functions, self.literals))
            self.assertEqual(len(self.body), symbol["size"])
        rom[:len(self.body)] = self.body
        self.rom = bytes(rom)
        instructions = match.verify_leaf_instructions(
            self.body, BASE, True, self.calls, function_thunk_context={}) if restore else []
        self.manifest = profile.make_manifest(
            self.calls, self.functions, self.literals, BASE, self.rom, None, instructions)

    def verify(self, *, manifest=None, rom=None):
        return profile.verify(self.body, BASE, self.rom if rom is None else rom,
                              self.mapping, self.index, None,
                              self.manifest if manifest is None else manifest)

    def test_context_callback_without_function_literal(self):
        self.fixture()
        self.assertEqual(self.functions, {})
        self.assertEqual(self.manifest["functions"], [])
        self.assertEqual(len(self.verify()), 5)

    def test_existing_typed_function_literal_still_supported(self):
        self.fixture(literal=True)
        self.assertTrue(self.functions)
        self.assertTrue(self.verify())

    def test_ordinary_function_address_profile_still_requires_literal(self):
        self.fixture()
        ordinary = {name: self.manifest[name] for name in ("calls", "functions", "data")}
        with self.assertRaisesRegex(ValueError, "invalid function-address manifest"):
            match.function_address_bindings(self.body, BASE, self.rom, self.mapping, None, ordinary)

    def test_no_canonical_call_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "require canonical calls"):
            self.fixture(canonical=False)

    def test_missing_duplicate_or_forged_thunk_evidence_is_rejected(self):
        self.fixture()
        for field, value in (("thunks", []), ("thunks", self.manifest["thunks"] * 2),
                             ("thunks", [[4, "_call_via_r3"]]), ("dependencies", []),
                             ("dependencies", [["_call_via_r2", 0, 4, "bad"]])):
            with self.subTest(field=field, value=value):
                manifest = copy.deepcopy(self.manifest)
                manifest[field] = value
                with self.assertRaises(ValueError):
                    self.verify(manifest=manifest)

    def test_runtime_bytes_must_be_the_exact_canonical_dependency(self):
        self.fixture()
        rom = bytearray(self.rom)
        rom[profile.ALIASES["_call_via_r2"] - BASE] ^= 1
        with self.assertRaisesRegex(ValueError, "thunk identity differs"):
            self.verify(rom=bytes(rom))

    def test_unbalanced_stack_is_rejected(self):
        self.fixture(restore=False)
        with self.assertRaises(ValueError):
            self.verify()


if __name__ == "__main__":
    unittest.main()
