"""Exercise profile/cache mechanics with synthetic assembled and linked ELF.

The report's C text is fingerprint-only and is not compiled. These fixtures do
not establish a canonical C-to-ELF match or any game-function match.
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
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import match
import match_evidence as evidence

BASE = match.ROM_BASE
NAME = "func_08000000"
DATA = "g_test_data"
TARGET = 0x02001000


class DataLiteralTests(unittest.TestCase):
    def setUp(self):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="data_literals_", dir=scratch)
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        environment = patch.dict(os.environ, {
            "TMPDIR": str(self.root), "FFTA_ROM": str(self.root / "baserom.bin"),
            "PYTHONDONTWRITEBYTECODE": "1"})
        environment.start()
        self.addCleanup(environment.stop)

    def fixture(self, middle=True, call=False, load=True, enter_pool=False,
                fallthrough=False, target=TARGET, addend=4):
        prefix = "push {lr}\n" if call else ""
        load_instruction = "ldr r0, pool" if load else "movs r0, #0"
        ending = "bl func_08000100\npop {r1}\nbx r1" if call else "bx lr"
        pool = f".balign 4\npool:\n.word {DATA} + ({addend})\n"
        if middle:
            skip = "movs r1, #0" if fallthrough else "b " + (
                "pool" if enter_pool else "continuation")
            body = f"{prefix}{load_instruction}\n{skip}\n{pool}continuation:\n{ending}\n"
        else:
            body = f"{prefix}{load_instruction}\n{ending}\n{pool}"
        assembly = (".syntax unified\n.arch armv4t\n.thumb\n.text\n"
                    f".global {NAME}\n.type {NAME}, %function\n.thumb_func\n"
                    f"{NAME}:\n{body}.size {NAME}, . - {NAME}\n"
                    f".type {DATA}, %object\n")
        args = argparse.Namespace(assembler=match.DEFAULT_AS, linker=match.DEFAULT_LD,
                                  objcopy=match.DEFAULT_OBJCOPY)
        runner = match.Runner(match.DEFAULT_CC, root=self.root, timeout=120)
        with runner.workspace() as workspace:
            assembly_path = Path(workspace) / "f.s"
            assembly_path.write_text(assembly)
            subprocess.run([args.assembler, "-mthumb-interwork", str(assembly_path),
                            "-o", str(Path(workspace) / "f.o")],
                           check=True, capture_output=True, timeout=120)
            self.original = match.elf_image((Path(workspace) / "f.o").read_bytes())
            symbol, _ = match.function_record(self.original, NAME, BASE, True)
            self.mapping = json.dumps([
                {"rom": f"0x{BASE:08X}", "end": f"0x{BASE + symbol['size']:08X}",
                 "mode": "thumb"},
                {"rom": "0x08000100", "end": "0x08000102", "mode": "thumb"},
            ]).encode()
            self.data_mapping = json.dumps({DATA: f"0x{target:08X}"}).encode()
            self.calls, self.targets, self.data_relocations = self.bindings()
            self.body, calls, relocations = match.link_calls(
                runner, workspace, args, self.original, BASE, self.mapping, 0x102,
                data_mapping=self.data_mapping)
            self.assertEqual(calls, self.calls)
            self.assertEqual(relocations, self.data_relocations)
            self.linked = match.elf_image((Path(workspace) / "f.elf").read_bytes())
        self.assertEqual(self.linked_body(), self.body)
        self.assertEqual(len(self.body), symbol["size"])
        self.assertFalse(self.linked["relocations"])

    def bindings(self, image=None, **changes):
        options = {"data_mapping": self.data_mapping}
        options.update(changes)
        return match.call_bindings(self.original if image is None else image,
                                   NAME, BASE, self.mapping, 0x102, **options)

    def linked_body(self, image=None):
        return match.linked_function_bytes(
            self.original, self.linked if image is None else image, NAME, BASE,
            self.calls, self.targets, self.data_relocations)

    def verified_instructions(self):
        instructions = match.verify_leaf_instructions(self.body, BASE, True, self.calls)
        match.verify_data_literals(instructions, BASE, self.data_relocations)
        return instructions

    def report(self, instructions):
        for directory in ("config", "src", "include"):
            (self.root / directory).mkdir(exist_ok=True)
        callee = ("extern unsigned char *func_08000100(unsigned char *data);\n"
                  if self.calls else "")
        expression = "func_08000100(g_test_data + 4)" if self.calls else "g_test_data + 4"
        (self.root / "src/08000000.c").write_text(
            "extern unsigned char g_test_data[];\n" + callee +
            "unsigned char *func_08000000(void)\n{\n    return " + expression + ";\n}\n")
        (self.root / "include/test.h").write_text("typedef unsigned char TestByte;\n")
        (self.root / "config/functions.json").write_bytes(self.mapping)
        (self.root / "config/data_symbols.json").write_bytes(self.data_mapping)
        (self.root / "baserom.bin").write_bytes(self.body.ljust(0x100, b"\0") + b"\x70\x47")
        framed = match.uses_stack_frame(instructions)
        schema = evidence.FRAMED_DATA_SCHEMA if framed else evidence.DATA_SCHEMA
        fields = [
            f"* verification: `{schema}`",
            f"* source SHA-256: `{evidence.source_fingerprint(self.root, BASE)}`",
            f"* mapping SHA-256: `{evidence.mapping_fingerprint(self.mapping)}`",
            f"* data symbols SHA-256: `{evidence.mapping_fingerprint(self.data_mapping)}`",
            "* control flow: " + (evidence.CALL_SUMMARY if self.calls else "closed leaf CFG"),
            "* verified extent: complete ELF function symbol, including literal pools",
            f"* ROM bytes: `{self.body.hex()}` ({len(self.body)} bytes)",
            f"* compiled : `{self.body.hex()}`",
            "* source plausibility: plausible", "* relocations: none",
            f"**MATCH - byte identical** - {len(self.body)}/{len(self.body)} bytes",
        ]
        if framed:
            fields.append(f"* stack frame: {evidence.STACK_SUMMARY}")
        return "\n".join(fields)

    def test_middle_trailing_and_direct_call_full_path(self):
        for middle, call in ((True, False), (False, False), (True, True)):
            with self.subTest(middle=middle, call=call):
                self.fixture(middle=middle, call=call)
                instructions = self.verified_instructions()
                self.assertEqual(len(self.data_relocations), 1)
                offset, binding = next(iter(self.data_relocations.items()))
                self.assertEqual(binding, (DATA, TARGET + 4))
                self.assertEqual(struct.unpack_from("<I", self.body, offset)[0], TARGET + 4)
                reached = {instruction.address + byte
                           for instruction in instructions for byte in range(instruction.size)}
                self.assertTrue(reached.isdisjoint(range(BASE + offset, BASE + offset + 4)))
                self.assertEqual(any(site >= BASE + offset + 4 for site in reached), middle)
                self.assertEqual(set(self.calls.values()), {BASE + 0x100} if call else set())
                self.assertTrue(evidence.report_matches(self.report(instructions), self.root, BASE))

    def test_signed_addend(self):
        self.fixture(addend=-4)
        self.verified_instructions()
        self.assertEqual(list(self.data_relocations.values()), [(DATA, TARGET - 4)])

    def test_pool_entry_or_fallthrough_rejected(self):
        for fallthrough in (False, True):
            with self.subTest(fallthrough=fallthrough):
                self.fixture(enter_pool=True, fallthrough=fallthrough, target=0x477046BC)
                with self.assertRaisesRegex(ValueError, "literal read overlaps reachable code"):
                    self.verified_instructions()

    def test_unconsumed_relocation_rejected(self):
        for middle in (False, True):
            with self.subTest(middle=middle):
                self.fixture(middle=middle, load=False)
                instructions = match.verify_leaf_instructions(self.body, BASE, True)
                with self.assertRaisesRegex(ValueError, "not a reachable.*literal-pool load"):
                    match.verify_data_literals(instructions, BASE, self.data_relocations)

    def test_missing_map_and_invalid_symbol_binding_rejected(self):
        self.fixture()
        for mapping in (None, b"{}"):
            with self.subTest(mapping=mapping), self.assertRaisesRegex(
                    ValueError, "data target must be an undefined mapped object"):
                self.bindings(data_mapping=mapping)
        for field, value in (("type", 2), ("type", 4), ("bind", 0), ("section", 0xFFF1)):
            image = copy.deepcopy(self.original)
            next(symbol for symbol in image["symbols"] if symbol["name"] == DATA)[field] = value
            with self.subTest(field=field, value=value), self.assertRaisesRegex(
                    ValueError, "data target must be an undefined mapped object"):
                self.bindings(image)

    def test_misaligned_incomplete_and_overlapping_relocations_rejected(self):
        self.fixture()
        section_index = self.original["relocations"][0]
        for offset in (6, 8):
            image = copy.deepcopy(self.original)
            relocation = bytearray(image["section_data"][section_index])
            struct.pack_into("<I", relocation, 0, offset)
            image["section_data"][section_index] = bytes(relocation)
            with self.subTest(offset=offset), self.assertRaisesRegex(
                    ValueError, "aligned complete literal word"):
                self.bindings(image)
        image = copy.deepcopy(self.original)
        image["section_data"][section_index] *= 2
        section = list(image["sections"][section_index])
        section[5] *= 2
        image["sections"][section_index] = section
        with self.assertRaisesRegex(ValueError, "overlapping data or call relocations"):
            self.bindings(image)

    def test_addend_overflow_and_self_reference_rejected(self):
        self.fixture()
        for target in (0xFFFFFFFF, BASE):
            with self.subTest(target=target), self.assertRaisesRegex(
                    ValueError, "overflows or references its own function"):
                self.bindings(data_mapping=json.dumps({DATA: f"0x{target:08X}"}).encode())

    def test_linked_symbol_and_word_mutations_rejected(self):
        self.fixture()
        for field, value in (("value", TARGET + 4), ("type", 2), ("section", 1)):
            image = copy.deepcopy(self.linked)
            next(symbol for symbol in image["symbols"] if symbol["name"] == DATA)[field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                self.linked_body(image)
        offset = next(iter(self.data_relocations))
        for value in (TARGET, TARGET + 8):
            image = copy.deepcopy(self.linked)
            data = bytearray(image["text"])
            struct.pack_into("<I", data, offset, value)
            image["text"] = bytes(data)
            with self.subTest(value=value), self.assertRaisesRegex(
                    ValueError, "mapped address and addend"):
                self.linked_body(image)

    def test_changes_outside_relocations_rejected(self):
        self.fixture(call=True)
        image = copy.deepcopy(self.linked)
        data = bytearray(image["text"])
        data[0] ^= 1
        image["text"] = bytes(data)
        with self.assertRaisesRegex(ValueError, "outside permitted relocations"):
            self.linked_body(image)

    def test_cached_report_binds_maps_source_headers_and_rom(self):
        self.fixture(call=True)
        report = self.report(self.verified_instructions())
        self.assertTrue(evidence.report_matches(report, self.root, BASE))
        for relative in ("config/data_symbols.json", "config/functions.json",
                         "src/08000000.c", "include/test.h", "baserom.bin"):
            path = self.root / relative
            original = path.read_bytes()
            if relative == "config/data_symbols.json":
                changed = json.dumps({DATA: f"0x{TARGET + 4:08X}"}).encode()
            elif relative == "baserom.bin":
                changed = bytes([original[0] ^ 1]) + original[1:]
            else:
                changed = original + b"\n"
            with self.subTest(path=relative):
                try:
                    path.write_bytes(changed)
                    self.assertFalse(evidence.report_matches(report, self.root, BASE))
                finally:
                    path.write_bytes(original)
                self.assertTrue(evidence.report_matches(report, self.root, BASE))


if __name__ == "__main__":
    unittest.main(verbosity=2)
