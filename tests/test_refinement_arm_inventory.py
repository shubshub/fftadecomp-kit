import contextlib
import io
import json
from pathlib import Path
import struct
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import analyze


class ArmInventoryTests(unittest.TestCase):
    address = 0x08A40000
    rom_end = 0x09000000
    bx_lr = 0xE12FFF1E
    nop = 0xE1A00000

    def entry(self, address=None, mode="arm"):
        return {"rom": hex(self.address if address is None else address), "mode": mode,
                "end": "0x0FFFFFFF"}  # Provisional ends grant no ownership.

    def branch(self, site, target, *, call=False, condition=14):
        displacement = target - site - 8
        self.assertEqual(displacement % 4, 0)
        return condition << 28 | 0x0A000000 | int(call) << 24 | (displacement >> 2 & 0xFFFFFF)

    def refine(self, words=None, **options):
        options.setdefault("arm_inventory", True)
        options.setdefault("full_rom_inventory", True)
        options.setdefault("rom_end", self.rom_end)
        functions = options.pop("functions", [self.entry()])
        data = struct.pack("<" + "I" * len(words or [self.bx_lr]), *(words or [self.bx_lr]))
        result = analyze.refine_function(data, self.address, functions, **options)
        self.assertFalse(result["complete"])
        self.assertFalse(result["inventory_complete"])
        return result

    def partial(self, words=None, **options):
        result = self.refine(words, **options)
        self.assertFalse(result["cfg_closed"], result)
        self.assertTrue(result["partial_reasons"])
        return result

    def test_arm_is_explicit_and_default_remains_unsupported(self):
        result = self.partial(arm_inventory=False)
        self.assertEqual(result["partial_reasons"], ["unsupported ARM entry"])
        result = self.refine()
        self.assertEqual(result["profile"], "bounded-arm-cfg-inventory-v1")
        self.assertTrue(result["cfg_closed"])
        self.assertEqual(result["instrs"], 1)
        self.assertEqual(result["returns"], [f"0x{self.address:08X}"])

    def test_opt_ins_and_positive_integer_budgets_are_strict(self):
        for value in (1, None, "yes"):
            with self.subTest(value=value):
                self.assertIn("ARM inventory opt-in must be Boolean",
                              self.partial(arm_inventory=value)["partial_reasons"])
        for key in ("max_bytes", "max_instructions"):
            for value in (0, -1, True, 1.5, "4"):
                with self.subTest(key=key, value=value):
                    self.assertIn("budgets must be positive integers",
                                  self.partial(**{key: value})["partial_reasons"])
        self.assertIn("invalid entry address", self.partial(full_rom_inventory=False)["partial_reasons"])

    def test_syntactic_return_forms_and_conditional_continuation(self):
        for word in (self.bx_lr, 0xE1A0F00E, 0xE8BD8010):
            with self.subTest(word=hex(word)):
                self.assertTrue(self.refine([word])["cfg_closed"])
                conditional = word & 0x0FFFFFFF | 0x10000000
                self.assertTrue(self.refine([conditional, self.bx_lr])["cfg_closed"])
                self.partial([conditional])
        for word in (0xE1B0F00E, 0xE8FD8010, 0xE8BDA010, 0xE12FFF10, 0xE12FFF30, 0xFA000000):
            with self.subTest(word=hex(word)):
                self.partial([word])

    def test_both_conditional_branch_paths_are_required(self):
        branch = self.branch(self.address, self.address + 8, condition=1)
        self.assertTrue(self.refine([branch, self.bx_lr, self.bx_lr])["cfg_closed"])
        self.partial([branch, self.bx_lr, self.nop])
        # A bounded cycle is structural, with the return on another path.
        loop = self.branch(self.address, self.address, condition=1)
        self.assertTrue(self.refine([loop, self.bx_lr])["cfg_closed"])
        self.partial([self.branch(self.address, self.address)])

    def test_stm_writeback_accepts_only_defined_base_first_forms(self):
        # The real refusal at 0x0890ABEC is STMDBNE r4!, {r4,r5,r7,r10,r11}.
        for word in (0x19240CB0, 0xE92D6000, 0xE8A40030, 0xE9A40030,
                     0xE8240030, 0xE9240030, 0xE9240010):
            with self.subTest(word=hex(word)):
                result = self.refine([word, self.bx_lr])
                self.assertTrue(result["cfg_closed"], result)
                self.assertEqual(result["instrs"], 2)
                self.assertEqual(result["literal_reads"], [])
                self.assertEqual(result["returns"], [f"0x{self.address + 4:08X}"])
        # A syntactic save/restore shape still grants no stack or ABI proof.
        self.assertTrue(self.refine([0xE92D6000, 0xE8BD8001])["cfg_closed"])

    def test_stm_base_first_conditional_instruction_always_requires_fallthrough(self):
        for condition in (0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14):
            word = condition << 28 | 0x09240030
            with self.subTest(condition=condition):
                self.assertTrue(self.refine([word, self.bx_lr])["cfg_closed"])
                self.partial([word])
                self.partial([word, self.bx_lr], max_bytes=4)
                self.partial([word, self.bx_lr], max_instructions=1)
        self.partial([0xF9240030, self.bx_lr])

    def test_stm_base_first_keeps_pc_userbank_and_unpredictable_forms_partial(self):
        for word in (0xE9240031, 0xE92D4010 | 0x2000, 0xE8B40030, 0xE9340030,
                     0xE9640030, 0xE9248030, 0xE92F8000, 0xE9240000):
            with self.subTest(word=hex(word)):
                self.partial([word, self.bx_lr])
        # Base excluded from the list continues to use the existing rule.
        self.assertTrue(self.refine([0xE9240020, self.bx_lr])["cfg_closed"])
        self.assertTrue(self.refine([0xE8B40020, self.bx_lr])["cfg_closed"])

    def test_stm_base_first_does_not_widen_neighbors_or_literal_roles(self):
        self.partial([0x19240CB0, self.bx_lr],
                     functions=[self.entry(), self.entry(self.address + 4)])
        self.partial([0x19240CB0, self.bx_lr], rom_end=self.address + 4)
        # A load claiming the STM instruction word as a literal still conflicts.
        result = self.partial([0x19240CB0, 0xE51F000C, self.bx_lr])
        self.assertTrue(any("code/literal overlap" in reason for reason in result["partial_reasons"]))

    def test_branch_escapes_header_previous_next_rom_and_budget_are_partial(self):
        for target in (0x08000000, self.address - 4, self.address + 8, self.rom_end):
            with self.subTest(target=hex(target)):
                result = self.partial([self.branch(self.address, target), self.bx_lr])
                self.assertTrue(any("boundary escape" in reason for reason in result["partial_reasons"]))
        self.partial([self.nop, self.bx_lr], max_bytes=4)
        self.partial([self.nop, self.bx_lr], max_bytes=7)
        self.partial([self.nop, self.bx_lr], max_instructions=1)
        self.partial([self.nop, self.bx_lr], functions=[self.entry(), self.entry(self.address + 4)])
        self.partial([self.bx_lr], functions=[self.entry(), self.entry(self.address + 2, "thumb")])

    def test_actual_rom_end_and_original_image_limit_are_enforced(self):
        self.assertTrue(self.refine(rom_end=self.address + 4)["cfg_closed"])
        for rom_end in (self.address, self.address + 3):
            self.assertIsNone(self.partial(rom_end=rom_end)["window"])
        self.partial([self.nop, self.bx_lr], rom_end=self.address + 4)
        result = analyze.refine_function(struct.pack("<II", self.nop, self.bx_lr), self.rom_end - 4,
                                        [self.entry(self.rom_end - 4)], rom_end=self.rom_end + 4,
                                        full_rom_inventory=True, arm_inventory=True)
        self.assertEqual(result["window"]["end"], "0x09000000")
        self.assertFalse(result["cfg_closed"])

    def test_duplicate_unaligned_and_ambiguous_neighbors_fail_before_decode(self):
        cases = [[self.entry(), self.entry()], [self.entry(mode="unknown")],
                 [self.entry(), self.entry(self.address - 4), self.entry(self.address - 4)],
                 [self.entry(), self.entry(self.address + 4), self.entry(self.address + 4)],
                 [self.entry(), self.entry(self.address + 4, "unknown")]]
        for entries in cases:
            with self.subTest(entries=entries):
                self.assertEqual(self.partial(functions=entries)["instrs"], 0)
        result = analyze.refine_function(struct.pack("<I", self.bx_lr), self.address + 2,
                                        [self.entry(self.address + 2)], rom_end=self.rom_end,
                                        full_rom_inventory=True, arm_inventory=True)
        self.assertFalse(result["cfg_closed"])
        self.assertIn("unaligned start", result["partial_reasons"][0])

    def test_indexed_direct_arm_call_uses_continuation_only(self):
        target = self.address + 0x100
        call = self.branch(self.address, target, call=True)
        entries = [self.entry(), self.entry(target)]
        result = self.refine([call, self.bx_lr], functions=entries)
        self.assertTrue(result["cfg_closed"])
        self.assertEqual(result["instrs"], 2)
        self.assertEqual(result["calls"], [{"site": f"0x{self.address:08X}", "target": f"0x{target:08X}"}])
        for entries in ([self.entry()], [self.entry(), self.entry(target, "thumb")],
                        [self.entry(), self.entry(target), self.entry(target)],
                        [self.entry(), self.entry(target, "unknown")]):
            with self.subTest(entries=entries):
                self.partial([call, self.bx_lr], functions=entries)
        self.partial([self.branch(self.address, self.address + 4, call=True), self.bx_lr])
        outside = self.branch(self.address, self.rom_end, call=True)
        self.partial([outside, self.bx_lr], functions=[self.entry(), self.entry(self.rom_end)])

    def test_literals_are_bounded_owned_words_and_repeated_reads_remain_distinct(self):
        result = self.refine([0xE59F0000, self.bx_lr, 0x12345678])
        self.assertTrue(result["cfg_closed"])
        self.assertEqual(result["literal_ranges"], [[f"0x{self.address + 8:08X}", f"0x{self.address + 12:08X}"]])
        self.assertEqual(result["literal_reads"], [{"site": f"0x{self.address:08X}",
                         "address": f"0x{self.address + 8:08X}", "size": 4, "inside_window": True}])
        result = self.refine([0x159F0004, 0xE59F1000, self.bx_lr, 0x12345678])
        self.assertTrue(result["cfg_closed"])
        self.assertEqual(len(result["literal_reads"]), 2)
        self.assertEqual(len(result["literal_ranges"]), 1)
        # Negative displacement uses ARM's PC+8 without Thumb's PC rounding.
        result = self.refine([self.branch(self.address, self.address + 8), 0x12345678,
                              0xE51F000C, self.bx_lr])
        self.assertTrue(result["cfg_closed"])
        self.assertEqual(result["literal_reads"][0]["address"], f"0x{self.address + 4:08X}")

    def test_external_unaligned_and_boundary_cut_literals_never_gain_ownership(self):
        for word in (0xE59F0000, 0xE59F0001, 0xE51F000C):
            with self.subTest(word=hex(word)):
                result = self.partial([word, self.bx_lr])
                self.assertEqual(result["literal_ranges"], [])
                self.assertFalse(result["literal_reads"][0]["inside_window"])
        for options in ({"max_bytes": 11}, {"rom_end": self.address + 11},
                        {"functions": [self.entry(), self.entry(self.address + 8)]}):
            with self.subTest(options=options):
                result = self.partial([0xE59F0000, self.bx_lr, 0x12345678], **options)
                self.assertEqual(result["literal_ranges"], [])
                self.assertFalse(result["literal_reads"][0]["inside_window"])

    def test_code_and_literal_conflicts_are_rejected_in_both_discovery_orders(self):
        cases = [[0xE59F0000, self.nop, self.bx_lr],
                 [self.nop, 0xE51F000C, self.bx_lr],
                 [0xE59F0000, self.branch(self.address + 4, self.address + 8), self.bx_lr]]
        for words in cases:
            with self.subTest(words=words):
                result = self.partial(words)
                self.assertTrue(any("code/literal overlap" in reason for reason in result["partial_reasons"]))

    def test_unsupported_pc_register_system_and_new_architecture_forms_remain_partial(self):
        for word in (0xE1A0000F, 0xE080000F, 0xE59FF000, 0xE49F0004,
                     0xE79F0001, 0xE1DF00B0, 0xE3A0F001, 0xE8B08000,
                     0xEF000000, 0xE10F0000, 0xE16F0F10, 0xE3000001, 0xF57FF01F):
            with self.subTest(word=hex(word)):
                self.partial([word, self.bx_lr])
        for word in (0xE2800001, 0xE5910000, 0xE5810000, 0xE1D100B0,
                     0xE92D4010, 0xE0000192):
            with self.subTest(word=hex(word)):
                self.assertTrue(self.refine([word, self.bx_lr])["cfg_closed"])

    def test_thumb_results_are_identical_with_arm_opt_in(self):
        fixtures = ("7047", "0048704778563412", "002801d0014800e00049704778563412", "c0467047", "0047")
        for encoded in fixtures:
            for full_rom, address in ((False, 0x08001000), (True, self.address)):
                with self.subTest(encoded=encoded, full_rom=full_rom):
                    entries = [self.entry(address, "thumb")]
                    options = dict(rom_end=self.rom_end, full_rom_inventory=full_rom)
                    default = analyze.refine_function(bytes.fromhex(encoded), address, entries, **options)
                    enabled = analyze.refine_function(bytes.fromhex(encoded), address, entries,
                                                      arm_inventory=True, **options)
                    self.assertEqual(default, enabled)

    def test_cli_flag_is_read_only_and_arm_default_is_preserved(self):
        with tempfile.TemporaryDirectory(dir=Path(__file__).resolve().parent) as directory:
            root = Path(directory)
            (root / "config").mkdir()
            index = root / "config/functions.json"
            index.write_text(json.dumps([self.entry()]))
            rom = root / "fixture.bin"
            with rom.open("wb") as stream:
                stream.seek(self.address - analyze.ROM_BASE)
                stream.write(struct.pack("<I", self.bx_lr))
            before = index.read_bytes()
            files_before = sorted(path.relative_to(root) for path in root.rglob("*"))
            arguments = [str(rom), str(root), "--refine-address", hex(self.address),
                         "--refine-full-rom-inventory"]
            for enabled in (False, True):
                output = io.StringIO()
                with contextlib.redirect_stdout(output):
                    code = analyze.refinement_main(arguments + (["--refine-arm-inventory"] if enabled else []))
                self.assertEqual(code, 0)
                result = json.loads(output.getvalue())
                self.assertEqual(result["results"][0]["cfg_closed"], enabled)
                self.assertEqual(result.get("arm_inventory", False), enabled)
                self.assertFalse(result["inventory_complete"])
            self.assertEqual(index.read_bytes(), before)
            self.assertEqual(files_before, sorted(path.relative_to(root) for path in root.rglob("*")))


if __name__ == "__main__":
    unittest.main()
