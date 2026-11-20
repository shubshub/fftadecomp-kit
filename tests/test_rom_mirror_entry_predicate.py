"""rom_mirror.names_entry: the one function-entry check the switch inventories share.

A reached pool word is a function address when, with a ROM wait-state mirror
folded and the Thumb bit dropped, it equals the address of a function-index
row. The nine inventories that refuse such a word call this predicate, so the
fold cannot be left out of one of them.
"""
import ast
import hashlib
import os
from pathlib import Path
import re
import sys
import tempfile
import unittest
from unittest import mock

sys.dont_write_bytecode = True
TOOLS = Path(__file__).resolve().parents[1] / "tools"
sys.path.insert(0, str(TOOLS))
import rom_mirror

ENTRY, ARM_ENTRY = 0x08020000, 0x08030000
ENTRIES = [{"rom": f"0x{ENTRY:08X}", "end": f"0x{ENTRY + 8:08X}", "mode": "thumb"},
           {"rom": f"0x{ARM_ENTRY:08X}", "end": f"0x{ARM_ENTRY + 8:08X}", "mode": "arm"}]
WS1, WS2, SRAM = 0x02000000, 0x04000000, 0x06000000  # offsets of 0x0A, 0x0C and 0x0E from 0x08
INVENTORIES = ("non_sp_block_copy_inventory", "numeric_data_switch_native_profile",
               "one_constant_scalar_switch_inventory", "one_numeric_thunk_scalar_switch_inventory",
               "one_object_mixed_switch_inventory", "one_object_ordinary_acyclic_inventory",
               "one_object_ordinary_cycle_inventory", "one_object_thunk_switch_inventory",
               "one_object_zero_local_thunk_inventory")


class NamesEntryTests(unittest.TestCase):
    def test_the_canonical_entry_address_names_its_row(self):
        for value in (ENTRY, ARM_ENTRY):
            with self.subTest(value=hex(value)):
                self.assertTrue(rom_mirror.names_entry(value, ENTRIES))

    def test_the_thumb_bit_spelling_names_its_row(self):
        for value in (ENTRY | 1, ARM_ENTRY | 1):
            with self.subTest(value=hex(value)):
                self.assertTrue(rom_mirror.names_entry(value, ENTRIES))

    def test_each_mirror_spelling_names_its_row(self):
        for entry in (ENTRY, ARM_ENTRY):
            for value in (entry + WS1, (entry | 1) + WS1, entry + WS2, (entry | 1) + WS2):
                with self.subTest(value=hex(value)):
                    self.assertTrue(rom_mirror.names_entry(value, ENTRIES))

    def test_a_row_spelled_with_the_thumb_bit_is_the_same_entry(self):
        rows = [{"rom": f"0x{ENTRY | 1:08X}"}]
        for value in (ENTRY, ENTRY | 1, ENTRY + WS1, (ENTRY | 1) + WS2):
            with self.subTest(value=hex(value)):
                self.assertTrue(rom_mirror.names_entry(value, rows))

    def test_other_words_name_no_row(self):
        # Inside a function but not its entry, beside it, the SRAM bus, and bits no mirror folds.
        for value in (ENTRY + 2, ENTRY + 4, ENTRY - 2, ENTRY + 8, (ENTRY | 1) + SRAM, ENTRY + SRAM,
                      ENTRY - 0x08000000, ENTRY | 0x10000000, ENTRY | 0x80000000, 0, 0xFFFFFFFF):
            with self.subTest(value=hex(value)):
                self.assertFalse(rom_mirror.names_entry(value, ENTRIES))

    def test_an_empty_index_names_nothing(self):
        self.assertFalse(rom_mirror.names_entry(ENTRY, []))


class SingleCopyTests(unittest.TestCase):
    """The comparison is written once, in rom_mirror; no tool repeats it."""
    COPY = re.compile(r"\[\s*['\"]rom['\"]\s*\]\s*,\s*16\s*\)\s*&\s*~1\s*==\s*rom_mirror\.canonical\("
                      r"|rom_mirror\.canonical\([^()]*\)\s*&\s*~1\s*==\s*int\(")

    def test_no_tool_repeats_the_folded_entry_comparison(self):
        literal = "== rom_mirror.canonical(value) & ~1 for row in entries"
        for path in sorted(TOOLS.glob("*.py")):
            source = path.read_text()
            with self.subTest(tool=path.name):
                self.assertNotIn(literal, source)
                self.assertIsNone(self.COPY.search(source))

    def test_the_pattern_would_find_the_copied_line(self):
        self.assertIsNotNone(self.COPY.search(
            "any(int(row['rom'], 16) & ~1 == rom_mirror.canonical(value) & ~1 for row in entries)"))
        self.assertIsNotNone(self.COPY.search(
            'any(rom_mirror.canonical(value) & ~1 == int(row["rom"], 16) & ~1 for row in entries)'))

    def test_the_nine_inventories_call_the_predicate(self):
        for name in INVENTORIES:
            with self.subTest(tool=name):
                self.assertEqual((TOOLS / f"{name}.py").read_text().count(
                    "not word['switch_word'] and rom_mirror.names_entry(value, entries)"), 1)


class ProducerPinTests(unittest.TestCase):
    """Every record that pins a caller's source pins rom_mirror.py too, so a change to the check makes it stale."""

    def changed_rom_mirror(self):
        """Point rom_mirror at a copy of its source with one byte added, under the same file name."""
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", TOOLS.parent / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="rom_mirror_pin_", dir=scratch)
        self.addCleanup(directory.cleanup)
        copy = Path(directory.name) / "rom_mirror.py"
        copy.write_bytes(Path(rom_mirror.__file__).read_bytes() + b"\n")
        return mock.patch.object(rom_mirror, "__file__", str(copy))

    def assert_fingerprint_binds_rom_mirror(self, fingerprint, table, key):
        before = fingerprint()
        self.assertIn(key, before[table])
        self.assertEqual(before[table][key], hashlib.sha256(Path(rom_mirror.__file__).read_bytes()).hexdigest())
        with self.changed_rom_mirror():
            after = fingerprint()
        self.assertNotEqual(after[table][key], before[table][key])
        self.assertEqual({name: digest for name, digest in after[table].items() if name != key},
                         {name: digest for name, digest in before[table].items() if name != key})

    def test_the_multiple_switch_environment_binds_rom_mirror(self):
        import multiple_switch_native_profile as profile
        self.assert_fingerprint_binds_rom_mirror(profile.environment_fingerprint, "producers", "rom_mirror")

    def test_the_numeric_switch_producers_bind_rom_mirror(self):
        import numeric_data_switch_native_profile as profile
        self.assert_fingerprint_binds_rom_mirror(
            profile.environment_fingerprint, "numeric_switch_producers", "rom_mirror.py")

    def test_each_inventory_pins_rom_mirror_beside_its_own_source(self):
        # The modules tuple is hashed into the record's producer_source_sha256 with the inventory's own file.
        for name in INVENTORIES:
            if name == "numeric_data_switch_native_profile":
                continue
            tree = ast.parse((TOOLS / f"{name}.py").read_text())
            tuples = [node.value for node in ast.walk(tree) if isinstance(node, ast.Assign) and
                      [ast.unparse(target) for target in node.targets] == ["modules"]]
            with self.subTest(tool=name):
                self.assertEqual(len(tuples), 1)
                self.assertIn("rom_mirror", [ast.unparse(element) for element in tuples[0].elts])


if __name__ == "__main__":
    unittest.main()
