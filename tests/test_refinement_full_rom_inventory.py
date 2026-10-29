import contextlib
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import analyze


class FullRomInventoryTests(unittest.TestCase):
    address = analyze.CODE_END + 0x100
    rom_end = 0x09000000

    def entry(self, address=None, mode="thumb"):
        address = self.address if address is None else address
        return {"rom": f"0x{address:08X}", "mode": mode,
                "end": f"0x{address + 2:08X}"}

    def refine(self, encoded="7047", **options):
        address = options.pop("address", self.address)
        entries = options.pop("functions", [self.entry(address)])
        options.setdefault("rom_end", self.rom_end)
        options.setdefault("full_rom_inventory", True)
        result = analyze.refine_function(bytes.fromhex(encoded), address, entries, **options)
        self.assertFalse(result["complete"])
        self.assertFalse(result["inventory_complete"])
        return result

    def refused(self, **options):
        result = self.refine(**options)
        self.assertFalse(result["cfg_closed"], result)
        self.assertTrue(result["partial_reasons"], result)
        return result

    def test_late_thumb_entry_is_only_syntactically_closed(self):
        result = self.refine()
        self.assertTrue(result["cfg_closed"], result)
        self.assertTrue(result["full_rom_inventory"])
        self.assertEqual(result["candidate_extent"]["bytes"], 2)
        self.assertIn("no stack-safety proof", result["return_policy"])

    def test_default_still_refuses_late_entry(self):
        default = analyze.refine_function(b"\x70\x47", self.address,
                                          [self.entry()], rom_end=self.rom_end)
        self.assertEqual(default, self.refused(full_rom_inventory=False))
        self.assertEqual(default["partial_reasons"], ["invalid entry address"])
        self.assertNotIn("full_rom_inventory", default)
        _, issues = analyze.refinement_boundaries([self.entry()], self.rom_end)
        self.assertIn("outside code region", issues[self.address])

    def test_explicit_false_keeps_default_main_region_result(self):
        address = 0x08001000
        entries = [self.entry(address)]
        default = analyze.refine_function(b"\x70\x47", address, entries)
        self.assertEqual(default, analyze.refine_function(
            b"\x70\x47", address, entries, full_rom_inventory=False))

    def test_default_window_still_stops_at_code_ceiling(self):
        address = analyze.CODE_END - 2
        default = self.refused(encoded="c0467047", address=address,
                               full_rom_inventory=False)
        self.assertEqual(default["window"]["end"], f"0x{analyze.CODE_END:08X}")
        self.assertIn(f"control-flow boundary escape at 0x{analyze.CODE_END:08X}",
                      default["partial_reasons"])
        self.assertTrue(self.refine("c0467047", address=address)["cfg_closed"])

    def test_index_opt_in_accepts_late_start_only_in_original_rom(self):
        _, issues = analyze.refinement_boundaries(
            [self.entry()], self.rom_end, full_rom_inventory=True)
        self.assertEqual(issues, {})
        for address in (self.rom_end, 0x0A000100, 0x03000000):
            with self.subTest(address=address):
                _, issues = analyze.refinement_boundaries(
                    [self.entry(address)], 0x0C000000, full_rom_inventory=True)
                self.assertIn("outside code region", issues[address])
                if address >= self.rom_end:
                    self.assertIn("outside ROM", issues[address])

    def test_header_ram_odd_and_mirror_entries_are_refused(self):
        for address in (0x080000BE, 0x03005E78, self.address + 1,
                        0x09000000, 0x0A000100):
            with self.subTest(address=address):
                self.assertIn("invalid entry address",
                              self.refused(address=address)["partial_reasons"])
        self.assertTrue(self.refine(address=0x080000C0)["cfg_closed"])

    def test_arm_entry_and_alignment_are_still_refused(self):
        result = self.refused(functions=[self.entry(mode="arm")])
        self.assertEqual(result["partial_reasons"], ["unsupported ARM entry"])
        result = self.refused(address=self.address + 2,
                              functions=[self.entry(self.address + 2, "arm")])
        self.assertIn("unaligned start", result["partial_reasons"][0])

    def test_duplicate_entry_is_refused(self):
        result = self.refused(functions=[self.entry(), self.entry()])
        self.assertIn("duplicate start", result["partial_reasons"][0])

    def test_ambiguous_previous_and_next_neighbors_are_refused(self):
        for neighbor in (self.address - 2, self.address + 2):
            with self.subTest(neighbor=neighbor):
                result = self.refused(functions=[self.entry(), self.entry(neighbor),
                                                self.entry(neighbor)])
                self.assertIn(f"ambiguous neighboring start: duplicate start at 0x{neighbor:08X}",
                              result["partial_reasons"])
        result = self.refused(functions=[self.entry(), self.entry(self.address + 2, "unknown")])
        self.assertIn("ambiguous neighboring start: invalid mode", result["partial_reasons"][0])

    def test_valid_neighbor_and_byte_budget_still_bound_window(self):
        for options in ({"max_bytes": 2},
                        {"functions": [self.entry(), self.entry(self.address + 2)]}):
            with self.subTest(options=options):
                result = self.refused(encoded="c0467047", **options)
                self.assertEqual(result["instrs"], 1)
                self.assertEqual(result["window"]["end"], f"0x{self.address + 2:08X}")

    def test_instruction_budget_and_partial_reasons_are_preserved(self):
        result = self.refused(encoded="c0467047", max_instructions=1)
        self.assertEqual(result["instrs"], 1)
        self.assertIn(f"instruction budget exhausted at 0x{self.address + 2:08X}",
                      result["partial_reasons"])

    def test_actual_rom_end_and_truncated_entry_are_enforced(self):
        self.assertTrue(self.refine(rom_end=self.address + 2)["cfg_closed"])
        result = self.refused(encoded="c0467047", rom_end=self.address + 2)
        self.assertEqual(result["window"]["end"], f"0x{self.address + 2:08X}")
        for rom_end in (self.address, self.address + 1):
            with self.subTest(rom_end=rom_end):
                result = self.refused(rom_end=rom_end)
                self.assertIn("outside ROM", result["partial_reasons"][0])
                self.assertIsNone(result["window"])

    def test_original_rom_end_caps_oversized_input(self):
        result = self.refused(encoded="c0467047", address=self.rom_end - 2,
                              rom_end=self.rom_end + 0x100)
        self.assertEqual(result["window"]["end"], "0x09000000")
        self.assertEqual(result["instrs"], 1)
        self.assertTrue(self.refine(address=self.rom_end - 2)["cfg_closed"])

    def test_out_of_window_literal_is_never_read_or_owned(self):
        result = self.refused(encoded="0048704778563412", rom_end=self.address + 4)
        self.assertEqual(result["literal_ranges"], [])
        self.assertFalse(result["literal_reads"][0]["inside_window"])
        self.assertIn(f"literal outside window at 0x{self.address:08X}",
                      result["partial_reasons"])

    def test_opt_in_requires_boolean(self):
        for value in (1, "yes", None):
            with self.subTest(value=value):
                result = self.refused(full_rom_inventory=value)
                self.assertIn("full-ROM inventory opt-in must be Boolean",
                              result["partial_reasons"])
                with self.assertRaisesRegex(ValueError, "must be Boolean"):
                    analyze.refinement_boundaries([], self.rom_end, full_rom_inventory=value)

    def cli(self, address, encoded="7047", *, full_rom=True, file_end=None, entries=None):
        # Fixtures live beside this test, on the checkout's backing filesystem.
        with tempfile.TemporaryDirectory(dir=Path(__file__).resolve().parent) as directory:
            root = Path(directory)
            (root / "config").mkdir()
            index = root / "config/functions.json"
            index.write_text(json.dumps(entries or [self.entry(address)]))
            rom = root / "fixture.bin"
            data = bytes.fromhex(encoded)
            with rom.open("wb") as stream:
                stream.seek(address - analyze.ROM_BASE)
                stream.write(data)
                if file_end is not None:
                    stream.truncate(file_end - analyze.ROM_BASE)
            index_before = index.read_bytes()
            files_before = sorted(str(path.relative_to(root)) for path in root.rglob("*"))
            arguments = [str(rom), str(root), "--refine-address", hex(address)]
            if full_rom:
                arguments.append("--refine-full-rom-inventory")
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                exit_code = analyze.refinement_main(arguments)
            self.assertEqual(exit_code, 0, output.getvalue())
            self.assertEqual(index.read_bytes(), index_before)
            self.assertEqual(files_before,
                             sorted(str(path.relative_to(root)) for path in root.rglob("*")))
            result = json.loads(output.getvalue())
            self.assertFalse(result["inventory_complete"])
            return result

    def test_cli_opt_in_reads_late_entry_and_defaults_remain_rejected(self):
        result = self.cli(self.address)
        self.assertTrue(result["full_rom_inventory"])
        self.assertTrue(result["results"][0]["cfg_closed"])
        self.assertEqual(result["results"][0]["window"]["end"], f"0x{self.address + 2:08X}")
        default = self.cli(self.address, full_rom=False)
        self.assertNotIn("full_rom_inventory", default)
        self.assertEqual(default["results"][0]["partial_reasons"], ["invalid entry address"])

    def test_cli_short_rom_and_oversized_rom_stay_bounded(self):
        result = self.cli(self.address, "c0467047", file_end=self.address + 2)["results"][0]
        self.assertFalse(result["cfg_closed"])
        self.assertEqual(result["window"]["end"], f"0x{self.address + 2:08X}")
        result = self.cli(self.rom_end - 2, "c0467047",
                          file_end=self.rom_end + 0x100)["results"][0]
        self.assertFalse(result["cfg_closed"])
        self.assertEqual(result["window"]["end"], "0x09000000")
        result = self.cli(self.rom_end, file_end=self.rom_end + 2)["results"][0]
        self.assertIsNone(result["window"])
        self.assertIn("invalid entry address", result["partial_reasons"])


if __name__ == "__main__":
    unittest.main()
