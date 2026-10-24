from pathlib import Path
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import analyze


class RefinementLiteralTests(unittest.TestCase):
    address = 0x08001000

    def refine(self, encoded, **options):
        data = bytes.fromhex(encoded)
        entries = options.pop("functions", [{
            "rom": f"0x{self.address:08X}",
            "end": f"0x{self.address + len(data):08X}",
            "mode": "thumb", "instrs": 1,
        }])
        result = analyze.refine_function(data, self.address, entries, **options)
        self.assertEqual(result["profile"], "bounded-thumb-cfg-inventory-v1")
        self.assertFalse(result["complete"])
        self.assertFalse(result["inventory_complete"])
        return result

    def read(self, site, target, inside):
        return {"site": f"0x{self.address + site:08X}",
                "address": f"0x{self.address + target:08X}",
                "size": 4, "inside_window": inside}

    def test_inside_word_preserves_ranges(self):
        result = self.refine("0048704778563412")
        self.assertEqual(result["literal_reads"], [self.read(0, 4, True)])
        self.assertEqual(result["code_ranges"], [["0x08001000", "0x08001004"]])
        self.assertEqual(result["literal_ranges"], [["0x08001004", "0x08001008"]])
        self.assertEqual(result["candidate_extent"]["bytes"], 8)
        self.assertEqual(result["instrs"], 2)
        self.assertTrue(result["cfg_closed"])
        self.assertEqual(result["partial_reasons"], [])

    def test_external_word_is_only_a_dependency(self):
        result = self.refine("00487047")
        self.assertEqual(result["literal_reads"], [self.read(0, 4, False)])
        self.assertEqual(result["literal_ranges"], [])
        self.assertEqual(result["candidate_extent"]["bytes"], 4)
        self.assertFalse(result["cfg_closed"])
        self.assertEqual(result["partial_reasons"],
                         ["literal outside window at 0x08001000"])

    def test_target_beyond_rom_end_is_not_fetched(self):
        result = self.refine("ff487047", rom_end=self.address + 4)
        self.assertEqual(result["literal_reads"], [self.read(0, 0x400, False)])
        self.assertEqual(result["literal_ranges"], [])
        self.assertFalse(result["cfg_closed"])

    def test_repeated_word_keeps_distinct_sites(self):
        result = self.refine("014801497047000078563412")
        self.assertEqual(result["literal_reads"],
                         [self.read(0, 8, True), self.read(2, 8, True)])
        self.assertEqual(result["literal_ranges"], [["0x08001008", "0x0800100C"]])
        self.assertEqual(result["instrs"], 3)

    def test_branch_worklist_order_does_not_order_reads(self):
        result = self.refine("002801d0014800e00049704778563412")
        self.assertEqual(result["literal_reads"],
                         [self.read(4, 12, True), self.read(8, 12, True)])
        self.assertEqual(result["literal_ranges"], [["0x0800100C", "0x08001010"]])

    def test_no_load_and_invalid_entries_have_no_reads(self):
        self.assertEqual(self.refine("7047")["literal_reads"], [])
        self.assertEqual(self.refine("00487047", functions=[])["literal_reads"], [])
        self.assertEqual(self.refine("00487047", max_bytes=0)["literal_reads"], [])

    def test_budget_keeps_only_reached_loads(self):
        result = self.refine("014801497047000078563412", max_instructions=1)
        self.assertEqual(result["literal_reads"], [self.read(0, 8, True)])
        self.assertEqual(result["instrs"], 1)
        self.assertIn("instruction budget exhausted at 0x08001002", result["partial_reasons"])
        self.assertFalse(result["cfg_closed"])

    def test_full_word_must_fit_every_window_limit(self):
        encoded = "0048704778563412"
        cases = [
            {"max_bytes": 7},
            {"rom_end": self.address + 7},
            {"functions": [
                {"rom": "0x08001000", "end": "0x08001006", "mode": "thumb"},
                {"rom": "0x08001006", "end": "0x08001008", "mode": "thumb"},
            ]},
        ]
        for options in cases:
            with self.subTest(options=options):
                result = self.refine(encoded, **options)
                self.assertEqual(result["literal_reads"], [self.read(0, 4, False)])
                self.assertEqual(result["literal_ranges"], [])
                self.assertFalse(result["cfg_closed"])
        result = self.refine(encoded[:-2])
        self.assertEqual(result["literal_reads"], [self.read(0, 4, False)])

    def test_unreachable_load_is_not_recorded(self):
        self.assertEqual(self.refine("7047004878563412")["literal_reads"], [])


if __name__ == "__main__":
    unittest.main()
