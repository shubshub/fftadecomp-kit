"""Original fixed-O2 C switch relocations under canonical-thunk source replay.

The state dispatcher is synthetic C; no game bytes or matching credit.
"""
import argparse
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
import function_thunk_profile as profile

BASE = match.ROM_BASE
NAME = "func_08000000"
SOURCE = """extern unsigned input_a, input_b, input_c, input_d, input_e;
struct Record { unsigned current, total, minimum, maximum; };
unsigned func_08000000(unsigned mode, struct Record *record, unsigned (*action)(unsigned))
{
    unsigned value = input_a + input_b + input_c + input_d + input_e;
    switch (mode) {
    case 0:
        value = action(value + record->current);
        record->total += value;
        record->current = value;
        record->minimum = value - 1;
        record->maximum = value + 1;
        break;
    case 1:
        value = action(value - record->current);
        record->current += value;
        record->total = value;
        record->minimum = value - 2;
        record->maximum = value + 2;
        break;
    case 2:
        value = action(value ^ record->current);
        record->total ^= value;
        record->current = value + 2;
        record->minimum = value - 3;
        record->maximum = value + 3;
        break;
    case 3:
        value = action(value | record->current);
        record->current |= value;
        record->total = value + 3;
        record->minimum = value - 4;
        record->maximum = value + 4;
        break;
    case 4:
        value = action(value & record->current);
        record->total &= value;
        record->current = value + 4;
        record->minimum = value - 5;
        record->maximum = value + 5;
        break;
    case 5:
        value = action(value * record->current);
        record->current *= value;
        record->total = value + 5;
        record->minimum = value - 6;
        record->maximum = value + 6;
        break;
    case 6:
        value = action(value + record->total);
        record->total = value + 6;
        record->current = value;
        record->minimum = value - 7;
        record->maximum = value + 7;
        break;
    default:
        value = record->current;
        break;
    }
    return value;
}
"""


class FunctionThunkSwitchElfTests(unittest.TestCase):
    def setUp(self):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="thunk_switch_elf_", dir=scratch)
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        for name in ("src", "include", "config", "symbols"):
            (self.root / name).mkdir()
        (self.root / "src/08000000.c").write_text(SOURCE)
        self.args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP,
            assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY,
            linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        self.runner = match.Runner(match.DEFAULT_CC, root=self.root, timeout=120)
        rom = bytearray(profile.END - BASE)
        for register in range(13):
            struct.pack_into("<HH", rom, profile.START + register * 4 - BASE,
                             0x4700 + register * 8, 0x46C0)
        self.rom = bytes(rom)
        self.objects = json.dumps({f"input_{name}": f"0x{0x02000000 + n * 4:08X}"
                                  for n, name in enumerate("abcde")}).encode()
        with self.runner.workspace() as workspace:
            self.original_raw, _, self.original = match.compile_object(self.runner, workspace,
                self.args, self.root, BASE, "src/08000000.c")
            self.size = match.function_record(self.original, NAME, BASE, True)[0]["size"]
            self.mapping = json.dumps([{"rom": "0x08000000", "end": f"0x{BASE + self.size:08X}",
                                        "mode": "thumb"}]).encode()
            self.words = {}
            self.calls, self.functions, self.literals = profile.original_bindings(
                self.original, BASE, self.mapping, self.rom, self.objects,
                switch_relocations=self.words)
            self.body, calls, functions, literals = profile.object_bytes(self.runner, workspace,
                self.args, self.original, BASE, self.mapping, self.rom, self.objects)
            self.assertEqual((calls, functions, literals),
                             (self.calls, self.functions, self.literals))
            self.assertEqual(self.original_raw, self.runner.read_binary(f"{workspace}/f.o"))
            self.linked = match.elf_image(self.runner.read_binary(f"{workspace}/f.elf"))
            self.original_hash = hashlib.sha256(self.original_raw).hexdigest()
            (self.root / "original.o").write_bytes(self.original_raw)
        rom[:self.size] = self.body
        self.rom = bytes(rom)
        self.instructions = match.verify_leaf_instructions(self.body, BASE, True, self.calls,
                                                           function_thunk_context={})
        self.index = f"08000000 {BASE + self.size:08X} {self.size} {len(self.instructions)} return\n".encode()
        self.manifest = profile.make_manifest(self.calls, self.functions, self.literals,
                                              BASE, self.rom, self.objects, self.instructions)
        for path, data in (("config/functions.json", self.mapping),
                           ("symbols/functions.txt", self.index),
                           ("config/data_symbols.json", self.objects),
                           ("synthetic.rom", self.rom)):
            (self.root / path).write_bytes(data)
        environment = patch.dict(os.environ, {"FFTA_ROM": str(self.root / "synthetic.rom"),
            "TMPDIR": str(self.root), "PYTHONDONTWRITEBYTECODE": "1"})
        environment.start()
        self.addCleanup(environment.stop)

    def bindings(self, image):
        return profile.original_bindings(image, BASE, self.mapping, self.rom, self.objects)

    def relocation_rows(self, image):
        for section_index in image["relocations"]:
            section = image["sections"][section_index]
            symbols = image["symbol_tables"][section[6]]
            for offset in range(0, section[5], 8):
                site, info = struct.unpack_from("<II", image["section_data"][section_index], offset)
                yield section_index, offset, site, info, symbols[info >> 8]

    def local_row(self, image):
        return next(row for row in self.relocation_rows(image) if row[4]["type"] == 3)

    def write_relocation(self, image, section, offset, site, info):
        data = bytearray(image["section_data"][section])
        struct.pack_into("<II", data, offset, site, info)
        image["section_data"][section] = bytes(data)

    def native_report(self):
        with patch.object(sys, "argv", ["match.py", "--root", str(self.root),
                "--function-address-profile", profile.SELECTOR, "0x08000000"]), \
                redirect_stdout(io.StringIO()):
            self.assertEqual(match.main(), 0)
        return (self.root / "docs/match/08000000.md").read_text()

    def test_fixed_o2_natural_source_full_symbol_original_elf_and_fresh_report_replay(self):
        self.assertEqual((self.size, len(self.instructions)), (316, 124))
        self.assertEqual((len(self.words), len(self.literals), len(self.calls)), (8, 5, 7))
        self.assertEqual(self.manifest["pool_switch"]["layout"]["bound"], 6)
        self.assertEqual(len(profile.verify(self.body, BASE, self.rom, self.mapping,
                         self.index, self.objects, self.manifest)), 124)
        report = self.native_report()
        self.assertTrue(profile.report_matches(report, self.root, BASE))
        self.assertEqual(hashlib.sha256((self.root / "original.o").read_bytes()).hexdigest(),
                         self.original_hash)
        (self.root / "src/08000000.c").write_text(SOURCE.replace("value - 7", "value - 8"))
        self.assertFalse(profile.report_matches(report, self.root, BASE))

    def test_default_legacy_linking_stays_closed(self):
        with self.assertRaises(ValueError):
            match.call_bindings(self.original, NAME, BASE, self.mapping, len(self.rom),
                                self.rom, self.objects, {})
        with self.assertRaises(ValueError):
            match.verify_leaf_instructions(self.body, BASE, True, self.calls)
        with self.assertRaises(ValueError):
            match.call_bindings(self.original, NAME, BASE, self.mapping, len(self.rom),
                                self.rom, self.objects, {}, {}, allow_switch_data=True)

    def test_fresh_source_replay_refuses_prelinked_words_without_original_local_relocations(self):
        from match_evidence import source_fingerprint
        compile_object = match.compile_object

        def prelinked_object(runner, workspace, *args, **kwargs):
            raw, _, image = compile_object(runner, workspace, *args, **kwargs)
            forged = bytearray(raw)
            text_offset = image["sections"][image["text_index"]][4]
            section_headers = struct.unpack_from("<I", raw, 32)[0]
            for section_index in image["relocations"]:
                section = image["sections"][section_index]
                retained = bytearray()
                for row_section, offset, site, info, symbol in self.relocation_rows(image):
                    if row_section != section_index:
                        continue
                    if info & 255 == 2 and symbol["type"] == 3:
                        addend = struct.unpack_from("<I", image["text"], site)[0]
                        struct.pack_into("<I", forged, text_offset + site, BASE + addend)
                    else:
                        retained += struct.pack("<II", site, info)
                forged[section[4]:section[4] + len(retained)] = retained
                struct.pack_into("<I", forged, section_headers + section_index * 40 + 20,
                                 len(retained))
            raw = bytes(forged)
            Path(workspace, "f.o").write_bytes(raw)
            image = match.elf_image(raw)
            return raw, image["text"], image

        with patch.object(match, "compile_object", side_effect=prelinked_object), \
                self.assertRaisesRegex(ValueError, "lacks exact original local relocations"):
            profile.verify_source(self.root, BASE, self.body, self.rom, self.mapping, self.index,
                self.objects, source_fingerprint(self.root, BASE), self.manifest)
        self.assertEqual(hashlib.sha256((self.root / "original.o").read_bytes()).hexdigest(),
                         self.original_hash)

    def test_foreign_named_nonlocal_nonzero_or_duplicate_section_symbol_is_rejected(self):
        for field, value in (("section", 0xFFF1), ("section", 0), ("type", 1),
                             ("bind", 1), ("name", "foreign"), ("value", 4)):
            image = copy.deepcopy(self.original)
            self.local_row(image)[4][field] = value
            with self.subTest(field=field, value=value), self.assertRaises(ValueError):
                self.bindings(image)
        image = copy.deepcopy(self.original)
        image["symbols"].append(copy.deepcopy(self.local_row(image)[4]))
        with self.assertRaises(ValueError):
            self.bindings(image)

    def test_only_local_text_abs32_and_thumb_call_relocations_are_allowed(self):
        for kind in (1, 3, 10, 28, 42):
            image = copy.deepcopy(self.original)
            section, offset, site, info, _ = self.local_row(image)
            self.write_relocation(image, section, offset, site, (info & ~255) | kind)
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                self.bindings(image)
        for field, value in ((1, 4), (7, 0), (9, 4)):
            image = copy.deepcopy(self.original)
            section = self.local_row(image)[0]
            altered = list(image["sections"][section]); altered[field] = value
            image["sections"][section] = tuple(altered)
            with self.subTest(section_field=field), self.assertRaises(ValueError):
                self.bindings(image)

    def test_odd_outside_owner_or_noninstruction_table_targets_fail(self):
        table = min(self.words) + 4
        for addend in (1, self.size, table, self.words[table] + 1):
            image = copy.deepcopy(self.original)
            body = bytearray(image["text"]); struct.pack_into("<I", body, table, addend)
            image["text"] = bytes(body)
            with self.subTest(addend=addend), self.assertRaises(ValueError):
                self.bindings(image)

    def test_extra_missing_duplicate_misaligned_or_code_relocations_fail(self):
        for change in ("missing", "duplicate", "unaligned", "code", "outside"):
            image = copy.deepcopy(self.original)
            section, offset, site, info, _ = self.local_row(image)
            if change == "missing":
                data = image["section_data"][section]
                image["section_data"][section] = data[:offset] + data[offset + 8:]
                fields = list(image["sections"][section]); fields[5] -= 8
                image["sections"][section] = tuple(fields)
            else:
                location = {"duplicate": site + 4, "unaligned": site + 2,
                            "code": 0, "outside": self.size}[change]
                self.write_relocation(image, section, offset, location, info)
            with self.subTest(change=change), self.assertRaises(ValueError):
                self.bindings(image)

    def test_linked_modifications_outside_exact_relocations_or_target_symbols_fail(self):
        _, targets, _ = match.call_bindings(self.original, NAME, BASE, self.mapping,
            len(self.rom), self.rom, self.objects, {}, {}, function_thunks=True)
        for change in ("instruction", "table", "section_symbol", "foreign_function", "veneer"):
            linked = copy.deepcopy(self.linked)
            if change in ("instruction", "table", "veneer"):
                data = bytearray(linked["text"])
                if change == "veneer":
                    data += b"\0\0"
                else:
                    data[0 if change == "instruction" else min(self.words)] ^= 1
                linked["text"] = bytes(data)
            elif change == "section_symbol":
                next(item for item in linked["symbols"] if item["type"] == 3 and
                     item["section"] == linked["text_index"])["value"] += 4
            else:
                linked["symbols"].append({"name": "foreign", "type": 2, "value": BASE + 1,
                                           "section": linked["text_index"], "bind": 1, "size": 2})
            with self.subTest(change=change), self.assertRaises(ValueError):
                match.linked_function_bytes(self.original, linked, NAME, BASE, self.calls,
                    targets, self.literals, self.functions, self.words, function_thunks=True)

    def test_guard_missing_pool_load_and_unbalanced_return_fail_after_linking(self):
        descriptor = self.manifest["pool_switch"]["layout"]
        for offset, word in ((descriptor["guard"], 0xDD00), (0, 0x46C0), (6, 0x46C0)):
            data = bytearray(self.body); struct.pack_into("<H", data, offset, word)
            with self.subTest(offset=offset), self.assertRaises(ValueError):
                match.verify_leaf_instructions(bytes(data), BASE, True, self.calls,
                                               function_thunk_context={"pool_switch": self.words})

    def test_exact_native_table_body_and_source_evidence_cannot_be_forged(self):
        for field in ("body_sha256", "table_sha256", "schema", "pool", "layout"):
            manifest = copy.deepcopy(self.manifest)
            manifest["pool_switch"][field] = [] if field in ("pool", "layout") else "forged"
            with self.subTest(field=field), self.assertRaises(ValueError):
                profile.verify(self.body, BASE, self.rom, self.mapping, self.index,
                               self.objects, manifest)
        report = self.native_report()
        for path in ("config/functions.json", "config/data_symbols.json", "symbols/functions.txt"):
            original = (self.root / path).read_bytes()
            (self.root / path).write_bytes(original + b" ")
            with self.subTest(path=path):
                self.assertFalse(profile.report_matches(report, self.root, BASE))
            (self.root / path).write_bytes(original)

    def test_explicit_thunk_names_and_nonfixed_compiler_configuration_remain_rejected(self):
        with self.assertRaises(ValueError):
            profile.namespace("extern void _call_via_r2(void);")
        args = copy.copy(self.args); args.flags = "-mthumb-interwork -O1"
        with self.assertRaises(ValueError):
            profile.fixed_configuration(args)


if __name__ == "__main__":
    unittest.main()
