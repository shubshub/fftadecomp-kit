"""tools/volatile_objects.json's reviewed-ram entries: ordinary RAM admitted case by case.

A user ruling may admit `volatile` on an ordinary RAM object for the functions it
lists, when the ROM shows reloads that only the qualifier explains.  The proof
admits such an object only in those functions, never through a caller, and
re-reads the review's evidence at every run: the function's pinned bytes, and
each listed reload as a load the non-volatile build drops, merges or moves.
"""
import os
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from hashlib import sha256

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import volatile_rom_proof as proof

try:
    import capstone
except ImportError:
    capstone = None

SYMBOLS = {"data_03000100": "0x03000100"}
FUNCTION = 0x08000400


def entry(rom=b"", start=FUNCTION, end=FUNCTION + 0x10, **changes):
    item = {"symbol": "data_03000100", "address": "0x03000100", "size": 2, "kind": proof.REVIEWED_KIND,
            "functions": [f"0x{FUNCTION:08X}"], "start": f"0x{start:08X}", "end": f"0x{end:08X}",
            "sha256": sha256(rom[start - proof.BASE:end - proof.BASE]).hexdigest(),
            "reloads": [["0x08000408", "0x08000402"]], "ruling": "a test ruling", "unproved": "no other writer",
            "reason": "a test"}
    item.update(changes)
    return item


class ObjectPremiseTests(unittest.TestCase):
    def premise(self, offset=0, width=2, entries=None, function=FUNCTION, base=proof.Base("symbol", "data_03000100")):
        return proof.object_premise(base, offset, width, False, SYMBOLS, [entry()] if entries is None else entries,
                                    b"", function=function)

    def test_the_listed_function_is_admitted_with_its_premise(self):
        text, extent = self.premise()
        self.assertEqual(extent, None)
        self.assertIn("data_03000100 is ordinary RAM admitted case by case for 08000400 by a reviewed "
                      "volatile_objects.json entry (a test ruling); unproved: no other writer", text)
        self.assertIn("08000400", self.premise(offset=1, width=1)[0])

    def test_any_other_function_or_a_caller_is_refused(self):
        for function in (None, 0x08000500):
            with self.subTest(function=function), self.assertRaisesRegex(proof.ProofError, "only in 08000400"):
                self.premise(function=function)

    def test_offsets_addresses_and_duplicates(self):
        for offset, width in ((None, 2), (2, 1), (1, 2), (-2, 2)):
            with self.subTest(offset=offset), self.assertRaisesRegex(proof.ProofError, "outside its listed"):
                self.premise(offset=offset, width=width)
        with self.assertRaisesRegex(proof.ProofError, "another address"):
            self.premise(entries=[entry(address="0x03000102")])
        with self.assertRaisesRegex(proof.ProofError, "another address"):
            self.premise(entries=[entry(), entry()])

    def test_without_the_entry_ordinary_ram_stays_refused(self):
        with self.assertRaisesRegex(proof.ProofError, "no hardware window"):
            self.premise(entries=[])
        with self.assertRaisesRegex(proof.ProofError, "no hardware window"):
            self.premise(entries=[entry(kind="shared")])


class EvidenceTests(unittest.TestCase):
    ROM = bytes(range(256)) * 16
    SITES = [(0x08000402, False, 2, "kept", "final"), (0x08000404, True, 2, "kept", "final"),
             (0x08000408, False, 2, "dropped", "cse"), (0x0800040C, True, 2, "kept", "final"),
             (0x080003FE, False, 2, "kept", "final"), (None, False, 2, "merged", "cse")]

    def evidence(self, item=None, address=FUNCTION, size=0x10, sites=None):
        return proof.reviewed_evidence(self.ROM, entry(self.ROM) if item is None else item, address, size,
                                       self.SITES if sites is None else sites)

    def test_the_listed_reloads_are_read_again(self):
        text = self.evidence()
        self.assertIn("reviewed reloads of data_03000100 that the non-volatile build drops or merges: "
                      "08000408 after 08000402", text)
        self.assertIn(entry(self.ROM)["sha256"], text)
        for category in ("merged", "moved"):
            sites = [self.SITES[0], (0x08000408, False, 2, category, "cse")]
            self.assertIn("08000408 after 08000402", self.evidence(sites=sites))
        # the reload may follow a store of the object
        self.assertIn("08000408 after 08000404", self.evidence(entry(self.ROM, reloads=[["0x08000408", "0x08000404"]])))

    def test_the_pinned_span_must_be_the_function_s(self):
        for address, size in ((0x08000402, 0x10), (FUNCTION, 0x12)):
            with self.subTest(address=address, size=size), \
                    self.assertRaisesRegex(proof.ProofError, "not this function's span"):
                self.evidence(address=address, size=size)
        with self.assertRaisesRegex(proof.ProofError, "changed"):
            self.evidence(entry(self.ROM, sha256="0" * 64))

    def test_a_reload_the_plain_build_keeps_is_no_evidence(self):
        for sites in ([self.SITES[0], (0x08000408, False, 2, "kept", "final")],
                      [self.SITES[0], (0x08000408, False, 2, "combined", "combine")],
                      [self.SITES[0], (0x08000408, True, 2, "dropped", "cse")],
                      [self.SITES[0], (0x08000408, False, 1, "dropped", "cse")],
                      [self.SITES[0]]):
            with self.subTest(sites=sites), \
                    self.assertRaisesRegex(proof.ProofError, "not a load the non-volatile build drops"):
                self.evidence(sites=sites)

    def test_the_reload_must_follow_an_earlier_access(self):
        # no access there, a later one, itself, and one outside the function
        for after in ("0x08000406", "0x0800040C", "0x08000408", "0x080003FE"):
            with self.subTest(after=after), self.assertRaisesRegex(proof.ProofError, "does not follow"):
                self.evidence(entry(self.ROM, reloads=[["0x08000408", after]]))
        with self.assertRaisesRegex(proof.ProofError, "lists no reload"):
            self.evidence(entry(self.ROM, reloads=[]))


class ShippedEntryTests(unittest.TestCase):
    def test_the_one_reviewed_entry(self):
        reviewed = [item for item in proof.load_objects() if item.get("kind") == proof.REVIEWED_KIND]
        self.assertEqual([(item["symbol"], item["functions"], item["start"], item["end"]) for item in reviewed],
                         [("data_030034D2", ["0x08003660"], "0x08003660", "0x08003888")])
        item, = reviewed
        self.assertEqual(item["reloads"], [["0x080037A6", "0x0800379E"], ["0x08003820", "0x080037E4"],
                                           ["0x0800382C", "0x08003820"]])
        self.assertTrue(item["ruling"] and item["unproved"] and item["reason"])
        rom = os.environ.get("FFTA_ROM")
        if rom and Path(rom).is_file():
            data = Path(rom).read_bytes()
            self.assertEqual(sha256(data[0x3660:0x3888]).hexdigest(), item["sha256"])


COMPILER = Path(os.path.expandvars(proof.CC)).is_file() and shutil.which("cpp") and shutil.which(proof.AS)
SOURCE = ("typedef unsigned short u16;\nextern volatile u16 data_03000100;\n"
          "extern void func_08000500(void);\n"
          "u16 func_08000400(void) { if (data_03000100 == 0xFFFF) return 1; if (data_03000100 == 0xFFFE) "
          "func_08000500(); return 0; }\n")


@unittest.skipUnless(COMPILER and capstone, "fixed compiler and capstone required")
class CompiledTests(unittest.TestCase):
    """the proof through agbcc, on a ROM built around the compiled function"""

    @classmethod
    def setUpClass(cls):
        cls.directory = tempfile.TemporaryDirectory()
        cls.root = Path(cls.directory.name)
        (cls.root / "src").mkdir()
        (cls.root / "include").mkdir()
        cls.relpath = f"src/{FUNCTION:08X}.c"
        (cls.root / cls.relpath).write_text(SOURCE)
        with tempfile.TemporaryDirectory(dir=cls.root) as work:
            unit = proof.Unit(cls.root, cls.relpath, SOURCE, [], work)
            text, start, cls.size, _ = unit.compile("probe", unit.real, f"func_{FUNCTION:08X}")["text"]
        rom = bytearray(b"\xff" * 0x1000)
        rom[FUNCTION - proof.BASE:FUNCTION - proof.BASE + cls.size] = text[start:start + cls.size]
        cls.rom = bytes(rom)
        # the halfword loads, read one halfword at a time so the literal pool does not stop the decoder
        decoder, body, cls.loads = proof.thumb_decoder(), text[start:start + cls.size], []
        at = 0
        while at < len(body):
            decoded = list(decoder.disasm(body[at:at + 4], FUNCTION + at, count=1))
            if decoded and decoded[0].mnemonic == "ldrh":
                cls.loads.append(FUNCTION + at)
            at += decoded[0].size if decoded else 2

    @classmethod
    def tearDownClass(cls):
        cls.directory.cleanup()

    def run_proof(self, **changes):
        first, second = self.loads
        changes = {"reloads": [[f"0x{second:08X}", f"0x{first:08X}"]], **changes}
        item = entry(self.rom, end=FUNCTION + self.size, **changes)
        return proof.prove(self.root, self.root, self.relpath, SOURCE, set(), SYMBOLS, [item], self.rom)

    def test_the_reviewed_object_is_admitted_with_its_evidence(self):
        self.assertEqual(len(self.loads), 2)
        (state, text), = [verdict for _, verdict in self.run_proof()]
        self.assertEqual(state, "admitted", text)
        self.assertIn("admitted case by case for 08000400", text)
        self.assertIn(f"{self.loads[1]:08X} after {self.loads[0]:08X}", text)
        self.assertIn("unproved: no other writer", text)

    def test_the_evidence_is_re_read(self):
        first, second = self.loads
        for changes, reason in (({"functions": ["0x08000500"]}, "only in 08000500"),
                                ({"reloads": [[f"0x{first:08X}", f"0x{FUNCTION:08X}"]]},
                                 "not a load the non-volatile build drops"),
                                ({"sha256": "0" * 64}, "changed"),
                                ({"kind": "shared"}, "no hardware window")):
            with self.subTest(changes=changes):
                (state, text), = [verdict for _, verdict in self.run_proof(**changes)]
                self.assertEqual(state, "refused")
                self.assertIn(reason, text)


if __name__ == "__main__":
    unittest.main()
