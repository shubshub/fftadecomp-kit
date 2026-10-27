from pathlib import Path
import struct
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import analyze


class RefinementWordSwitchTests(unittest.TestCase):
    address = 0x08001000

    def fixture(self, kind="bhi", prefix=b""):
        # Two synthetic local cases and a default, all returning via BX LR.
        code = ("01280dd8800002494018006887460000" if kind == "bhi" else
                "012800d90ce080000149401800688746")
        base = self.address + len(prefix)
        return bytearray(prefix + bytes.fromhex(code) +
                         struct.pack("<III", base + 20, base + 28, base + 30) +
                         bytes.fromhex("704770477047"))

    def refine(self, data, **options):
        functions = options.pop("functions", [{"rom": f"0x{self.address:08X}",
                    "end": f"0x{self.address + len(data):08X}", "mode": "thumb"}])
        return analyze.refine_function(bytes(data), self.address, functions, **options)

    def refused(self, data, **options):
        result = self.refine(data, **options)
        self.assertFalse(result["cfg_closed"], result)
        self.assertTrue(result["partial_reasons"])
        return result

    def test_unsigned_high_guard_owns_every_table_word(self):
        result = self.refine(self.fixture())
        self.assertTrue(result["cfg_closed"], result)
        self.assertFalse(result["complete"])
        self.assertFalse(result["inventory_complete"])
        self.assertEqual(result["instrs"], 10)
        self.assertEqual(result["candidate_extent"]["bytes"], 34)
        self.assertEqual(result["literal_ranges"], [["0x08001010", "0x0800101C"]])
        self.assertEqual(result["gaps"], [["0x0800100E", "0x08001010"]])
        self.assertEqual(result["word_switches"][0]["bound"], 1)
        self.assertEqual(result["word_switches"][0]["schema"],
                         "bounded-guarded-word-switch-v1")
        self.assertEqual(result["literal_reads"], [{"site": "0x08001006",
                         "address": "0x08001010", "size": 4, "inside_window": True}])

    def test_unsigned_low_guard_and_default_branch(self):
        result = self.refine(self.fixture("bls"))
        self.assertTrue(result["cfg_closed"], result)
        self.assertEqual(result["instrs"], 11)
        self.assertEqual(result["word_switches"][0]["dispatch"], 6)

    def test_duplicate_cases_are_bounded(self):
        data = self.fixture()
        struct.pack_into("<I", data, 24, self.address + 28)
        result = self.refine(data)
        self.assertTrue(result["cfg_closed"], result)
        self.assertEqual(result["instrs"], 9)
        self.assertEqual(result["literal_ranges"], [["0x08001010", "0x0800101C"]])

    def test_missing_guard(self):
        data = self.fixture()
        data[0:2] = bytes.fromhex("0120")
        self.refused(data)

    def test_signed_guard(self):
        data = self.fixture()
        data[2:4] = bytes.fromhex("0ddc")
        self.refused(data)

    def test_guard_compares_different_register(self):
        data = self.fixture()
        data[0:2] = bytes.fromhex("012a")
        self.refused(data)

    def test_guard_bound_requires_complete_table(self):
        data = self.fixture()
        data[0:2] = bytes.fromhex("ff28")
        self.refused(data)

    def test_wrong_in_range_guard_destination(self):
        data = self.fixture("bls")
        data[2:4] = bytes.fromhex("01d9")
        self.refused(data)

    def test_wrong_pointer(self):
        data = self.fixture()
        struct.pack_into("<I", data, 16, self.address + 24)
        self.refused(data)

    def test_odd_outside_or_literal_case_target(self):
        for target in (self.address + 29, self.address - 2,
                       self.address + 34, self.address + 20):
            with self.subTest(target=target):
                data = self.fixture()
                struct.pack_into("<I", data, 20, target)
                self.refused(data)

    def test_default_outside_window(self):
        data = self.fixture("bls")
        data[4:6] = bytes.fromhex("ffe0")
        self.refused(data)

    def test_dispatch_register_mismatch(self):
        data = self.fixture()
        data[12:14] = bytes.fromhex("8f46")
        self.refused(data)

    def test_entry_path_cannot_bypass_guard(self):
        data = self.fixture(prefix=bytes.fromhex("002a01d0"))
        result = self.refused(data)
        self.assertIn("word-switch guard can be bypassed at 0x08001010",
                      result["partial_reasons"])

    def test_entry_path_cannot_enter_target_load_or_transfer(self):
        for branch in ("04d0", "05d0"):
            with self.subTest(branch=branch):
                self.refused(self.fixture(prefix=bytes.fromhex("002a" + branch)))

    def test_case_cannot_branch_back_into_lookup(self):
        data = self.fixture()
        data[28:30] = bytes.fromhex("f3e7")
        result = self.refused(data)
        self.assertTrue(any("guard can be bypassed" in reason
                            for reason in result["partial_reasons"]))

    def test_instruction_interior_case_still_refused(self):
        data = self.fixture()
        data[28:32] = bytes.fromhex("00f000f8")
        self.refused(data)

    def test_table_and_targets_respect_every_window_bound(self):
        for options in ({"max_bytes": 26}, {"rom_end": self.address + 26},
                        {"functions": [{"rom": f"0x{self.address:08X}",
                           "end": f"0x{self.address + 30:08X}", "mode": "thumb"},
                          {"rom": f"0x{self.address + 30:08X}",
                           "end": f"0x{self.address + 34:08X}", "mode": "thumb"}]}):
            with self.subTest(options=options):
                self.refused(self.fixture(), **options)

    def test_instruction_budget_is_preserved(self):
        result = self.refused(self.fixture(), max_instructions=7)
        self.assertTrue(any("instruction budget exhausted" in reason
                            for reason in result["partial_reasons"]))

    def test_ordinary_indirect_jump_is_still_unresolved(self):
        result = self.refused(bytes.fromhex("8746"))
        self.assertIn("unresolved jump at 0x08001000", result["partial_reasons"])


if __name__ == "__main__":
    unittest.main()
