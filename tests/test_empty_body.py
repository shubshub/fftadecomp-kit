import argparse
import contextlib
import copy
import io
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
TOOLS = Path(__file__).resolve().parents[1] / "tools"
sys.path.insert(0, str(TOOLS))
import empty_body_profile as empty_body
import match
import match_evidence as evidence
import plausible
import push


class EmptyBodyTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", Path.cwd() / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix="empty_body_tests_", dir=scratch)
        cls.root = Path(cls.temporary.name)
        cls.address = 0x08000000
        for directory in ("src", "include", "config", "symbols", "docs/match"):
            (cls.root / directory).mkdir(parents=True, exist_ok=True)
        cls.source = cls.root / "src/08000000.c"
        cls.source_text = "void func_08000000(void)\n{\n}\n"
        cls.source.write_text(cls.source_text)
        cls.mapping = json.dumps([{"rom": "0x08000000", "end": "0x08000002",
                                   "mode": "thumb", "instrs": 1}]).encode()
        cls.index = b"08000000 08000002 2 1 return\n"
        cls.rom = bytes.fromhex("70470000")
        (cls.root / "config/functions.json").write_bytes(cls.mapping)
        (cls.root / "symbols/functions.txt").write_bytes(cls.index)
        (cls.root / "baserom.bin").write_bytes(cls.rom)
        cls.args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP,
            assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY,
            linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        runner = match.Runner(match.DEFAULT_CC, root=cls.root,
                              wsl_path=match.DEFAULT_WSL_PATH, timeout=120)
        with runner.workspace() as workspace:
            cls.object_data, cls.text_data, cls.image = match.compile_object(
                runner, workspace, cls.args, cls.root, cls.address, "src/08000000.c")
        result = cls.command("match.py", "--root", str(cls.root), "0x08000000")
        assert result.returncode == 0, result.stdout + result.stderr
        cls.report_path = cls.root / "docs/match/08000000.md"
        cls.report = cls.report_path.read_text()

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    @classmethod
    def command(cls, tool, *arguments, environment=None):
        return subprocess.run([sys.executable, str(TOOLS / tool), *arguments],
                              cwd=cls.root, capture_output=True, text=True, timeout=120,
                              env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1",
                                   **(environment or {})})

    @contextlib.contextmanager
    def changed(self, path, content):
        original = path.read_bytes() if path.exists() else None
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content.encode() if isinstance(content, str) else content)
        try:
            yield
        finally:
            if original is None:
                path.unlink()
            else:
                path.write_bytes(original)

    def object_check(self, object_data=None, text_data=None, **changes):
        values = dict(address=self.address, thumb=True, rom=self.rom,
                      mapping=self.mapping, index=self.index)
        values.update(changes)
        empty_body.verify_object(object_data or self.object_data,
                                 self.text_data if text_data is None else text_data, **values)

    def symbol_mutation(self, field, value):
        content = bytearray(self.object_data)
        symbol_section = next(section for section in self.image["sections"] if section[1] == 2)
        symbols = next(iter(self.image["symbol_tables"].values()))
        number = next(index for index, symbol in enumerate(symbols) if symbol["name"] == "func_08000000")
        offset, encoding = {"value": (4, "I"), "size": (8, "I"), "info": (12, "B"), "section": (14, "H")}[field]
        struct.pack_into("<" + encoding, content, symbol_section[4] + number * 16 + offset, value)
        return bytes(content)

    def test_positive_complete_function(self):
        self.object_check()
        self.assertEqual(self.text_data, bytes.fromhex("7047c046"))
        self.assertTrue(evidence.report_matches(self.report, self.root, self.address))
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertTrue(push.check_plausible(str(self.root)))
            self.assertTrue(push.check_reports(str(self.root)))

    def test_standalone_still_rejects_empty_body(self):
        result = self.command("plausible.py", "--json", str(self.source))
        self.assertEqual(result.returncode, 1)
        self.assertEqual([item["rule"] for item in json.loads(result.stdout)["findings"]], ["empty-body"])

    def test_comments_are_supported(self):
        with self.changed(self.source, "/* unused callback */\n" + self.source_text):
            result = self.command("match.py", "--root", str(self.root), "--no-write", "0x08000000")
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_only_canonical_empty_void_source(self):
        variants = ["int func_08000000(void) {}", "void func_08000000() {}",
                    "void func_08000000(int argument) {}", "static void func_08000000(void) {}",
                    "void func_08000001(void) {}", self.source_text + "void helper(void) {}",
                    "#define EMPTY\n" + self.source_text, "void func_08000000(void) { return; }"]
        for source in variants:
            with self.subTest(source=source), self.changed(self.source, source):
                with self.assertRaises(ValueError):
                    empty_body.source_path(self.root, self.address)

    def test_placeholder_comments_are_not_cleared(self):
        for marker in ("TODO", "FIXME", "UNIMPLEMENTED", "not implemented", "???"):
            with self.subTest(marker=marker), self.changed(self.source, f"/* {marker} */\n" + self.source_text):
                result = self.command("match.py", "--root", str(self.root), "--no-write", "0x08000000")
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("source  IMPLAUSIBLE", result.stdout)

    def test_other_findings_are_not_cleared(self):
        for source in ("volatile int value;\n" + self.source_text,
                       self.source_text + 'asm("nop");',
                       "#pragma GCC optimize(0)\n" + self.source_text,
                       self.source_text + "int UNIMPLEMENTED;",
                       "/* force the compiler */\n" + self.source_text):
            with self.subTest(source=source), self.changed(self.source, source):
                result = self.command("plausible.py", "--json", "--addr", "0x08000000", str(self.source))
                with self.assertRaises(ValueError):
                    empty_body.check_findings(result, self.root, self.address)

    def test_checker_failure_and_allow_entry_are_not_cleared(self):
        result = self.command("plausible.py", "--json", "--addr", "0x08000000", str(self.source))
        empty_body.check_findings(result, self.root, self.address)
        for exit_code in (0, 2, -9):
            with self.subTest(exit_code=exit_code), self.assertRaises(ValueError):
                empty_body.check_findings(subprocess.CompletedProcess([], exit_code, result.stdout), self.root, self.address)
        document = json.loads(result.stdout)
        document.update(hand_asm_allowed=True, allow_entry={"address": "0x08000000", "reason": "test"})
        with self.assertRaises(ValueError):
            empty_body.check_findings(subprocess.CompletedProcess([], 1, json.dumps(document)), self.root, self.address)

    def test_hand_asm_listing_does_not_make_match(self):
        allow = self.root / "allow.json"
        with self.changed(allow, json.dumps({"entries": [{"address": "0x08000000", "reason": "test"}]})):
            result = self.command("match.py", "--root", str(self.root), "--no-write", "0x08000000",
                                  environment={"FFTA_ASM_ALLOW": str(allow)})
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("HAND-ASM (sanctioned)", result.stdout)

    def test_elf_identity_negatives(self):
        for field, value in (("size", 0), ("size", 4), ("value", 0), ("value", 3),
                             ("info", 17), ("info", 34), ("section", 0)):
            with self.subTest(field=field, value=value), self.assertRaises(ValueError):
                self.object_check(self.symbol_mutation(field, value))
        with self.assertRaises(ValueError):
            self.object_check(text_data=bytes.fromhex("70470000"))
        with self.assertRaises(ValueError):
            self.object_check(thumb=False)

    def test_relocation_extra_section_and_function_rejected(self):
        for kind in ("relocation", "section", "function"):
            image = copy.deepcopy(self.image)
            if kind == "relocation":
                image["relocations"] = [1]
            elif kind == "section":
                image["sections"].append((0, 1, 2, 0, 0, 4, 0, 0, 4, 0))
            else:
                image["symbols"].append({**next(item for item in image["symbols"] if item["type"] == 2), "name": "extra"})
            with self.subTest(kind=kind), patch.object(match, "elf_image", return_value=image), self.assertRaises(ValueError):
                self.object_check()

    def test_opcode_and_extent_negatives(self):
        text_offset = self.image["sections"][self.image["text_index"]][4]
        for opcode in ("0047", "c046", "0020"):
            data = bytearray(self.object_data)
            altered = bytes.fromhex(opcode) + self.text_data[2:]
            data[text_offset:text_offset + len(altered)] = altered
            with self.subTest(opcode=opcode), self.assertRaises(ValueError):
                self.object_check(bytes(data), altered)
        for rom in (b"", bytes.fromhex("7046"), bytes.fromhex("70")):
            with self.subTest(rom=rom), self.assertRaises(ValueError):
                self.object_check(rom=rom)

    def test_index_mutations(self):
        entry = json.loads(self.mapping)[0]
        mappings = [[], [entry, entry], [{**entry, "mode": "arm"}], [{**entry, "end": "0x08000004"}],
                    [{**entry, "instrs": 2}], [{**entry, "rom": "0x08000001"}],
                    [entry, {"rom": "0x07FFFFFE", "end": "0x08000002", "mode": "thumb", "instrs": 2}]]
        for mapping in mappings:
            with self.subTest(mapping=mapping), self.assertRaises(ValueError):
                self.object_check(mapping=json.dumps(mapping).encode())
        for index in (b"", self.index * 2, b"08000000 08000004 4 2 return\n",
                      b"08000000 08000002 2 2 return\n", self.index + b"07FFFFFE 08000002 4 2 return\n"):
            with self.subTest(index=index), self.assertRaises(ValueError):
                self.object_check(index=index)

    def test_report_fields_are_strict(self):
        metadata = [line for line in self.report.splitlines() if line.startswith("* ")]
        for line in metadata:
            for variant in (self.report.replace(line + "\n", ""), self.report + line + "\n",
                            self.report.replace(line, " " + line), self.report.replace(line, line + " altered")):
                with self.subTest(line=line):
                    self.assertFalse(evidence.report_matches(variant, self.root, self.address))
        for extra in ("**NOT MATCHING - bytes differ** - 0/2 bytes", "**MATCH - byte identical** - 2/2 bytes",
                      "HAND-ASM", "IMPLAUSIBLE", "* stack frame: forged"):
            with self.subTest(extra=extra):
                self.assertFalse(evidence.report_matches(self.report + "\n" + extra, self.root, self.address))

    def test_legacy_schema_cannot_launder_empty_body(self):
        legacy = self.report.replace(empty_body.SCHEMA, evidence.SCHEMA)
        legacy = "\n".join(line for line in legacy.splitlines() if not line.startswith("* empty body:"))
        self.assertFalse(evidence.report_matches(legacy, self.root, self.address))
        with self.changed(self.report_path, legacy), contextlib.redirect_stdout(io.StringIO()):
            self.assertFalse(push.check_plausible(str(self.root)))

    def test_reports_bind_current_source_headers_indexes_and_rom(self):
        mutations = [(self.source, self.source_text + "\n"),
                     (self.root / "include/new.h", "typedef int Added;\n"),
                     (self.root / "config/functions.json", self.mapping + b"\n"),
                     (self.root / "symbols/functions.txt", self.index + b"\n"),
                     (self.root / "baserom.bin", bytes.fromhex("00470000")),
                     (self.root / "src/duplicate/08000000.c", self.source_text)]
        for path, content in mutations:
            with self.subTest(path=path), self.changed(path, content):
                self.assertFalse(evidence.report_matches(self.report, self.root, self.address))
                with contextlib.redirect_stdout(io.StringIO()):
                    self.assertFalse(push.check_plausible(str(self.root)))

    def test_push_does_not_clear_empty_header_or_other_findings(self):
        for text in ("void helper(void) {}", 'asm("nop");', "volatile int register_value;", "int UNIMPLEMENTED;"):
            with self.subTest(text=text), self.changed(self.root / "include/extra.h", text), \
                    contextlib.redirect_stdout(io.StringIO()):
                self.assertFalse(push.check_plausible(str(self.root)))

    def test_report_requires_fresh_compiler(self):
        with patch.object(match.Runner, "sh", side_effect=RuntimeError("compiler unavailable")):
            self.assertFalse(evidence.report_matches(self.report, self.root, self.address))

    def test_match_mismatch_and_wrong_extent_fail(self):
        with self.changed(self.root / "baserom.bin", bytes.fromhex("00207047")):
            result = self.command("match.py", "--root", str(self.root), "--no-write", "0x08000000")
            self.assertNotEqual(result.returncode, 0)
        with self.changed(self.root / "symbols/functions.txt", b"08000000 08000004 4 2 return\n"):
            result = self.command("match.py", "--root", str(self.root), "--no-write", "0x08000000")
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("shorter than the indexed span", result.stderr)


if __name__ == "__main__":
    unittest.main(verbosity=2)
