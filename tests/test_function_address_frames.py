"""Framed function-address proofs using synthetic assembled/linked fixtures.

The report source is fingerprint-only; these fixtures do not prove a C match.
"""

import argparse
import copy
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
import match
import match_evidence as evidence

BASE = match.ROM_BASE
NAME = "func_08000000"
CALLBACK = "func_08000200"


class FunctionAddressFrameTests(unittest.TestCase):
    def setUp(self):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="function_address_frames_", dir=scratch)
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        environment = patch.dict(os.environ, {
            "TMPDIR": str(self.root), "FFTA_ROM": str(self.root / "baserom.bin"),
            "PYTHONDONTWRITEBYTECODE": "1"})
        environment.start()
        self.addCleanup(environment.stop)

    def fixture(self, *, framed=True, call=True, access=None, restore=True, load=True):
        prefix = "push {lr}\n" if call else ""
        if framed:
            prefix += "sub sp, #8\n"
        if access is None:
            access = "str r1, [sp]\nldr r1, [sp]\n" if framed else ""
        callback_load = "ldr r0, callback_pool\n" if load else "movs r0, #0\n"
        body = prefix + "ldr r1, data_pool\n" + access + callback_load
        if call:
            body += "bl func_08000100\n"
        if framed and restore:
            body += "add sp, #8\n"
        body += "pop {r1}\nbx r1\n" if call else "bx lr\n"
        body += (".balign 4\ncallback_pool:\n.word " + CALLBACK +
                 "\ndata_pool:\n.word g_test_data\n")
        assembly = (".syntax unified\n.arch armv4t\n.thumb\n.text\n"
                    f".global {NAME}\n.type {NAME}, %function\n.thumb_func\n"
                    f"{NAME}:\n{body}.size {NAME}, . - {NAME}\n"
                    ".type g_test_data, %object\n")
        args = argparse.Namespace(assembler=match.DEFAULT_AS, linker=match.DEFAULT_LD,
                                  objcopy=match.DEFAULT_OBJCOPY)
        runner = match.Runner(match.DEFAULT_CC, root=self.root, timeout=120)
        with runner.workspace() as workspace:
            assembly_path = Path(workspace) / "f.s"
            assembly_path.write_text(assembly)
            object_path = Path(workspace) / "f.o"
            subprocess.run([args.assembler, "-mthumb-interwork", str(assembly_path),
                            "-o", str(object_path)], check=True, capture_output=True, timeout=120)
            original = match.elf_image(object_path.read_bytes())
            symbol, _ = match.function_record(original, NAME, BASE, True)
            self.mapping = json.dumps([
                {"rom": f"0x{BASE:08X}", "end": f"0x{BASE + symbol['size']:08X}",
                 "mode": "thumb"},
                {"rom": "0x08000100", "end": "0x08000102", "mode": "thumb"},
                {"rom": "0x08000200", "end": "0x08000202", "mode": "thumb"},
            ]).encode()
            self.objects = b'{"g_test_data":"0x02001000"}'
            functions = {}
            self.body, calls, objects = match.link_calls(
                runner, workspace, args, original, BASE, self.mapping, 0x202,
                data_mapping=self.objects, function_relocations=functions)
            self.assertFalse(match.elf_image((Path(workspace) / "f.elf").read_bytes())["relocations"])
            self.assertEqual(len(self.body), symbol["size"])
        self.manifest = {
            "calls": [[site - BASE, f"func_{target:08X}"] for site, target in sorted(calls.items())],
            "data": [[offset, name, value - 0x02001000]
                     for offset, (name, value) in sorted(objects.items())],
            "functions": [[offset, name] for offset, (name, _) in sorted(functions.items())],
        }
        self.rom = ((self.body.ljust(0x100, b"\0") + b"\x70\x47").ljust(0x200, b"\0") +
                    b"\x70\x47")

    def verify(self, manifest=None, mapping=None):
        return match.verify_function_addresses(
            self.body, BASE, self.rom, self.mapping if mapping is None else mapping,
            self.objects, self.manifest if manifest is None else manifest)

    def report(self, instructions):
        for directory in ("config", "src", "include"):
            (self.root / directory).mkdir(exist_ok=True)
        (self.root / "src/08000000.c").write_text(
            "extern void func_08000100(void (*callback)(void), unsigned char *data);\n"
            "extern void func_08000200(void);\nextern unsigned char g_test_data[];\n"
            "void func_08000000(void)\n{\n"
            "    func_08000100(func_08000200, g_test_data);\n}\n")
        (self.root / "config/functions.json").write_bytes(self.mapping)
        (self.root / "config/data_symbols.json").write_bytes(self.objects)
        (self.root / "baserom.bin").write_bytes(self.rom)
        framed = match.uses_stack_frame(instructions)
        schema = evidence.FRAMED_FUNCTION_ADDRESS_SCHEMA if framed else evidence.FUNCTION_ADDRESS_SCHEMA
        fields = [
            f"* verification: `{schema}`",
            f"* source SHA-256: `{evidence.source_fingerprint(self.root, BASE)}`",
            f"* mapping SHA-256: `{evidence.mapping_fingerprint(self.mapping)}`",
            f"* data symbols SHA-256: `{evidence.mapping_fingerprint(self.objects)}`",
            "* control flow: " + (evidence.CALL_SUMMARY if self.manifest["calls"] else "closed leaf CFG"),
            "* verified extent: complete ELF function symbol, including literal pools",
            f"* ROM bytes: `{self.body.hex()}` ({len(self.body)} bytes)",
            f"* compiled : `{self.body.hex()}`",
            "* source plausibility: plausible", "* relocations: none",
            f"* function addresses: {evidence.FUNCTION_ADDRESS_SUMMARY}",
            f"* function address manifest: `{evidence.function_address_manifest(self.manifest)}`",
            "* function address proof SHA-256: `" + evidence.function_address_fingerprint(
                BASE, self.body, self.manifest, framed=framed) + "`",
            f"**MATCH - byte identical** - {len(self.body)}/{len(self.body)} bytes",
        ]
        if framed:
            fields.append(f"* stack frame: {evidence.STACK_SUMMARY}")
        return "\n".join(fields)

    def test_fixed_frame_typed_literals_and_cached_report(self):
        for framed, call in ((True, True), (True, False), (False, True)):
            with self.subTest(framed=framed, call=call):
                self.fixture(framed=framed, call=call)
                instructions, _ = self.verify()
                self.assertEqual(match.uses_stack_frame(instructions), framed)
                report = self.report(instructions)
                self.assertTrue(evidence.report_matches(report, self.root, BASE))
                if framed:
                    for altered in (
                            report.replace(f"* stack frame: {evidence.STACK_SUMMARY}", ""),
                            report + f"\n* stack frame: {evidence.STACK_SUMMARY}",
                            report.replace(evidence.STACK_SUMMARY, "unverified frame"),
                            report.replace(evidence.FRAMED_FUNCTION_ADDRESS_SCHEMA,
                                           evidence.FUNCTION_ADDRESS_SCHEMA)):
                        self.assertFalse(evidence.report_matches(altered, self.root, BASE))
                else:
                    self.assertFalse(evidence.report_matches(
                        report + f"\n* stack frame: {evidence.STACK_SUMMARY}", self.root, BASE))

    def test_bounded_local_stack_alias(self):
        self.fixture(access="mov r2, sp\nstrb r1, [r2, #1]\nmovs r2, #0\n")
        instructions, _ = self.verify()
        self.assertTrue(evidence.report_matches(self.report(instructions), self.root, BASE))

    def test_unsafe_frames_still_rejected(self):
        cases = (
            ({"access": "mov sp, r1\n"}, "stack-pointer adjustment"),
            ({"access": "str r1, [sp, #12]\n"}, "outside the tracked frame"),
            ({"restore": False, "call": False}, "return does not balance the saved stack frame"),
            ({"access": "mov r2, sp\n"}, "stack aliases cannot cross calls"),
            ({"access": "cmp r1, #0\nbeq join\nsub sp, #4\njoin:\n"},
             "inconsistent saved stack depth|balance|no verified return"),
        )
        for options, error in cases:
            with self.subTest(options=options):
                self.fixture(**options)
                with self.assertRaisesRegex(ValueError, error):
                    self.verify()

    def test_function_literal_provenance_still_required(self):
        self.fixture()
        manifest = copy.deepcopy(self.manifest)
        manifest["functions"][0][1] = "func_08000100"
        with self.assertRaisesRegex(ValueError, "literal does not equal its binding"):
            self.verify(manifest=manifest)
        mapping = json.loads(self.mapping)
        mapping.append(copy.deepcopy(mapping[-1]))
        with self.assertRaisesRegex(ValueError, "unknown, ambiguous"):
            self.verify(mapping=json.dumps(mapping).encode())
        self.fixture(load=False)
        with self.assertRaisesRegex(ValueError, "not a reachable.*literal-pool load"):
            self.verify()


if __name__ == "__main__":
    unittest.main()
