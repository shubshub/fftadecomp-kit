"""Native binary64 callers require original-ELF provenance for named data."""

import argparse
import builtins
import copy
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
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import match
import match_evidence as evidence
import software_double_profile as profile
import software_float_profile as software_float

BASE = 0x08000000
SOURCE = """#include "objects.h"
extern int func_08000200(const int *);
double func_08000000(int value)
{
    return (double)(value + func_08000200(samples + 1));
}
"""


class SoftwareDoubleDataTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        selected = os.environ.get("FFTA_ROM")
        if not selected or not Path(selected).is_file():
            raise unittest.SkipTest("FFTA_ROM must reference the approved ROM")
        cls.rom_path = Path(selected).resolve()
        cls.runtime_rom = cls.rom_path.read_bytes()
        if hashlib.sha256(cls.runtime_rom).hexdigest() != software_float.ROM_SHA256:
            raise unittest.SkipTest("FFTA_ROM is not the approved image")

    def setUp(self):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="software_double_data_", dir=scratch)
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

    def fixture(self, source=SOURCE, object_address=0x02000000):
        (self.root / "src/08000000.c").write_text(source)
        (self.root / "include/objects.h").write_text("extern const int samples[];\n")
        self.data_mapping = json.dumps({"samples": f"0x{object_address:08X}"}).encode()
        (self.root / "config/data_symbols.json").write_bytes(self.data_mapping)
        runner = match.Runner(match.DEFAULT_CC, root=self.root, timeout=120)
        with runner.workspace() as workspace:
            _, _, self.original = match.compile_object(
                runner, workspace, self.args, self.root, BASE, "src/08000000.c")
            symbol, _ = match.function_record(self.original, "func_08000000", BASE, True)
            self.indexes(symbol["size"], 1)
            self.literals = {}
            self.body, self.calls, self.bindings = profile.object_bytes(
                runner, workspace, self.args, self.original, BASE, self.mapping,
                self.runtime_rom, self.index, data_mapping=self.data_mapping,
                data_relocations=self.literals)
            self.linked = match.elf_image((Path(workspace) / "f.elf").read_bytes())
        rom = bytearray(self.runtime_rom)
        rom[:len(self.body)] = self.body
        self.rom = bytes(rom)
        self.instructions = match.verify_leaf_instructions(
            self.body, BASE, True, self.calls,
            double_context=(self.rom, self.mapping, self.index, self.bindings))
        self.indexes(len(self.body), len(self.instructions))
        (self.root / "config/functions.json").write_bytes(self.mapping)
        (self.root / "symbols/functions.txt").write_bytes(self.index)
        self.manifest = profile.make_manifest(self.calls, BASE, self.bindings, self.instructions,
                                              literals=self.literals, data_mapping=self.data_mapping)

    def verify(self, manifest=None, **kwargs):
        return profile.verify(kwargs.pop("data", self.body), BASE,
                              kwargs.pop("rom", self.rom), kwargs.pop("mapping", self.mapping),
                              kwargs.pop("index", self.index), self.manifest if manifest is None else manifest,
                              data_mapping=kwargs.pop("data_mapping", self.data_mapping), **kwargs)

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
                "--software-double-profile", profile.SELECTOR, "0x08000000"]), \
                patch.object(match, "ROOT", match.ROOT), redirect_stdout(io.StringIO()):
            self.assertEqual(match.main(), 0)
        return (self.root / "docs/match/08000000.md").read_text()

    def test_native_named_ram_and_rom_objects_with_addend(self):
        for address in (0x02000000, 0x08394350):
            with self.subTest(address=address):
                self.fixture(object_address=address)
                self.assertEqual(len(self.literals), 1)
                offset = next(iter(self.literals))
                self.assertEqual(self.manifest["data"], [[offset, "samples", 4]])
                self.assertEqual(struct.unpack_from("<I", self.body, offset)[0], address + 4)
                self.assertEqual(len(self.verify()), len(self.instructions))
                self.assertEqual(set(self.bindings.values()), {"__floatsidf"})
                self.assertIn(0x08000200, self.calls.values())

    def test_missing_duplicate_unaligned_and_unreferenced_words_reject(self):
        self.fixture()
        offset = self.manifest["data"][0][0]
        for records in ([], self.manifest["data"] * 2, [[offset + 1, "samples", 4]],
                        [[len(self.body), "samples", 4]], [[offset, "unknown", 4]],
                        [[offset, "samples", True]], [[offset, "samples", 1 << 31]],
                        [[offset, "samples", 8]]):
            altered = copy.deepcopy(self.manifest); altered["data"] = records
            with self.subTest(records=records), self.assertRaises(ValueError):
                self.verify(altered)
        altered = dict(self.manifest); altered.pop("data")
        with self.assertRaisesRegex(ValueError, "exact mapped-data coverage"):
            self.verify(altered)
        with self.assertRaises(ValueError): self.verify(data_mapping=None)
        with self.assertRaises(ValueError): self.verify(data_mapping=b'{"samples":"0x02000004"}')
        # A matching numeric word elsewhere cannot establish a PC-relative read.
        with self.assertRaises(ValueError):
            match.verify_data_literals(self.instructions, BASE, {0: ("samples", 0x02000004)})

    def test_indexed_code_runtime_aliases_and_unsupported_memory_reject(self):
        self.fixture()
        offset = self.manifest["data"][0][0]
        for value in (0x08000200, 0x08000201, 0x0814383C, 0x0814383D,
                      0x01000000, 0xFFFFFFFF):
            body = bytearray(self.body); struct.pack_into("<I", body, offset, value)
            rom = bytearray(self.rom); rom[:len(body)] = body
            altered = copy.deepcopy(self.manifest); altered["data"][0][2] = 0
            objects = json.dumps({"samples": f"0x{value:08X}"}).encode()
            with self.subTest(value=value), self.assertRaises(ValueError):
                self.verify(altered, data=bytes(body), rom=bytes(rom), data_mapping=objects)
        # An otherwise supported ROM object plus an addend must not alias code.
        body = bytearray(self.body); struct.pack_into("<I", body, offset, 0x08000200)
        rom = bytearray(self.rom); rom[:len(body)] = body
        altered = copy.deepcopy(self.manifest); altered["data"][0][2] = 4
        with self.assertRaisesRegex(ValueError, "aliases indexed code"):
            self.verify(altered, data=bytes(body), rom=bytes(rom),
                        data_mapping=b'{"samples":"0x080001FC"}')
        altered = copy.deepcopy(self.manifest)
        altered["data"][0][2] = 0x02000004 - 0x08000200
        with self.assertRaisesRegex(ValueError, "aliases indexed code"):
            self.verify(altered, data_mapping=b'{"samples":"0x08000200"}')

    def test_original_elf_requires_undefined_global_object_and_capture(self):
        self.fixture()
        runner = match.Runner(match.DEFAULT_CC, root=self.root, timeout=120)
        for key, value in (("section", 1), ("bind", 0), ("type", 2), ("value", 4)):
            altered = copy.deepcopy(self.original)
            for item in altered["symbols"]:
                if item["name"] == "samples": item[key] = value
            with self.subTest(key=key), runner.workspace() as workspace, self.assertRaises(ValueError):
                profile.object_bytes(runner, workspace, self.args, altered, BASE, self.mapping,
                                     self.rom, self.index, data_mapping=self.data_mapping, data_relocations={})
        with runner.workspace() as workspace, self.assertRaisesRegex(ValueError, "explicit provenance capture"):
            profile.object_bytes(runner, workspace, self.args, self.original, BASE, self.mapping,
                                 self.rom, self.index, data_mapping=self.data_mapping)
        with runner.workspace() as workspace, self.assertRaises(ValueError):
            profile.object_bytes(runner, workspace, self.args, self.original, BASE, self.mapping,
                                 self.rom, self.index, data_mapping=b'{}', data_relocations={})
        with self.assertRaises(ValueError):
            match.call_bindings(self.original, "func_08000000", BASE, self.mapping,
                                len(self.rom), self.rom, self.data_mapping,
                                double_bindings={}, double_index=self.index)

    def test_linker_changes_and_incomplete_runtime_binding_reject(self):
        self.fixture()
        targets = {"samples": 0x02000000, "func_08000200": 0x08000200, "__floatsidf": 0x0814383C}
        for offset in (0, next(iter(self.literals))):
            altered = copy.deepcopy(self.linked)
            body = bytearray(altered["text"]); body[offset] ^= 1; altered["text"] = bytes(body)
            with self.subTest(offset=offset), self.assertRaises(ValueError):
                match.linked_function_bytes(self.original, altered, "func_08000000", BASE,
                    self.calls, targets, self.literals, double_bindings=self.bindings, allow_double_data=True)
        with self.assertRaises(ValueError):
            match.linked_function_bytes(self.original, self.linked, "func_08000000", BASE,
                self.calls, targets, self.literals, double_bindings={}, allow_double_data=True)

    def test_native_report_replay_and_stale_source_header_maps_reject(self):
        self.fixture()
        report = self.native_report()
        marker = f"* data symbols SHA-256: `{hashlib.sha256(self.data_mapping).hexdigest()}`"
        self.assertIn(marker, report)
        opening, reading = self.patched_rom()
        with opening, reading, redirect_stdout(io.StringIO()):
            self.assertTrue(evidence.report_matches(report, self.root, BASE))
            for changed in (report.replace(marker, ""), report + "\n" + marker,
                            report.replace(marker, marker + " trailing"), report + "\n* data symbols: forged",
                            report + "\n* software float: forged"):
                with self.subTest(marker=changed[-100:]):
                    self.assertFalse(evidence.report_matches(changed, self.root, BASE))
            for name in ("config/data_symbols.json", "config/functions.json", "symbols/functions.txt",
                         "src/08000000.c", "include/objects.h"):
                path = self.root / name; original = path.read_bytes()
                path.write_bytes(original + b"\n")
                with self.subTest(name=name):
                    self.assertFalse(evidence.report_matches(report, self.root, BASE))
                path.write_bytes(original)
            old_rom = self.rom
            changed = bytearray(old_rom); changed[-1] ^= 1; self.rom = bytes(changed)
            self.assertFalse(evidence.report_matches(report, self.root, BASE))
            self.rom = old_rom

    def test_rehashed_source_cannot_forge_original_elf_data_provenance(self):
        self.fixture()
        report = self.native_report()
        source = self.root / "src/08000000.c"
        old_digest = evidence.source_fingerprint(self.root, BASE)
        # Same compiled bytes, but numeric-address code has no object relocation.
        source.write_text(source.read_text().replace("samples + 1", "(const int *)0x02000004"))
        new_digest = evidence.source_fingerprint(self.root, BASE)
        old_proof = profile.fingerprint(BASE, self.body, self.manifest, old_digest,
                                       self.mapping, self.index, self.rom, data_mapping=self.data_mapping)
        new_proof = profile.fingerprint(BASE, self.body, self.manifest, new_digest,
                                       self.mapping, self.index, self.rom, data_mapping=self.data_mapping)
        forged = report.replace(old_digest, new_digest).replace(old_proof, new_proof)
        opening, reading = self.patched_rom()
        with opening, reading, redirect_stdout(io.StringIO()):
            self.assertFalse(evidence.report_matches(forged, self.root, BASE))

    def test_empty_data_manifest_and_fingerprint_remain_compatible(self):
        self.fixture(source="double func_08000000(int value) { return (double)value; }\n")
        self.assertFalse(self.literals)
        self.assertNotIn("data", self.manifest)
        digest = evidence.source_fingerprint(self.root, BASE)
        self.assertEqual(profile.fingerprint(BASE, self.body, self.manifest, digest,
                                            self.mapping, self.index, self.rom),
                         profile.fingerprint(BASE, self.body, self.manifest, digest,
                            self.mapping, self.index, self.rom, data_mapping=b'{}'))
        report = self.native_report()
        self.assertNotIn("* data symbols", report)
        opening, reading = self.patched_rom()
        with opening, reading, redirect_stdout(io.StringIO()):
            self.assertTrue(evidence.report_matches(report, self.root, BASE))
            self.assertFalse(evidence.report_matches(report + "\n* data symbols: forged", self.root, BASE))


if __name__ == "__main__":
    unittest.main()
