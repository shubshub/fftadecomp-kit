"""kit#165, R2: the operand read of `symbol.member |= ALL_ONES`.

For `g_control_flags_03000940.bldcnt_lo |= 0xff` agbcc keeps the volatile
operand read, folds the OR to 0xff, and then makes the bit-field store's own
read-modify-write read (08126118 0x081261DC: `ldrb r0, [r2]; ldrb r0, [r2];
movs r0, #0xff; strb r0, [r2]`).  The ROM cannot tell that first read from a
planted `(void)sym.m;`, so it is admitted only where the source has the
statement and a variant compile with that `|=` written `=` loses exactly that
load.
"""
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import match
import plausible
import volatile_semantics as semantics
import test_volatile_semantics as fixtures

SYMBOL = fixtures.SYMBOL
WINDOW = ("ldr\tr1, .L3", "add\tr1, r1, #60")
REAL = fixtures.assembly(*WINDOW, "ldrb\tr2, [r1]", "ldrb\tr2, [r1]", "mov\tr2, #255", "strb\tr2, [r1]", "bx\tlr")
VARIANT = fixtures.assembly(*WINDOW, "ldrb\tr2, [r1]", "mov\tr2, #255", "strb\tr2, [r1]", "bx\tlr")
STRIPPED = fixtures.assembly(*WINDOW, "mov\tr2, #255", "strb\tr2, [r1]", "bx\tlr")


def text(body):
    return fixtures.PREPROCESSED + fixtures.DECLARATION + "\nvoid func_08028C34(void) { " + body + " }\n"


class OperandReadTests(unittest.TestCase):
    def compare(self, body, real=REAL, variant=VARIANT, compiler=True):
        seen = []

        def compile_variant(rewrite):
            seen.append(rewrite(text(body)))
            return variant
        token = semantics.OPERAND_READ_COMPILE.set(compile_variant if compiler else None)
        try:
            return semantics._compare_compiles(real, STRIPPED, text(body), SYMBOL, fixtures.DECLARATION), seen
        finally:
            semantics.OPERAND_READ_COMPILE.reset(token)

    def refused(self, body, **options):
        with self.assertRaises(semantics.SemanticError) as caught:
            self.compare(body, **options)
        self.assertIn("not directly followed by a store", str(caught.exception))

    def test_the_operand_read_of_an_all_ones_or_is_admitted_and_recorded(self):
        for constant in ("0xFF", "0xff", "255", "0377", "0xFFu"):
            with self.subTest(constant=constant):
                results, seen = self.compare(SYMBOL + ".unknown_3C |= " + constant + ";")
                self.assertEqual(results[0][2], [3])
                self.assertEqual(seen, [text(SYMBOL + ".unknown_3C  = " + constant + ";")])
                line = semantics.record(SYMBOL, results)
                self.assertIn("all-ones `|=` operand reads (kit#165): instruction 3: `" + SYMBOL +
                              ".unknown_3C |=` at preprocessed line 4", line)

    def test_a_planted_read_is_refused(self):
        # the bytes are the same, but there is no `|=` to rewrite
        self.refused("(void)" + SYMBOL + ".unknown_3C; " + SYMBOL + ".unknown_3C = 0xFF;")
        # nor does a planted read beside a real `|=` pass: three loads
        planted = fixtures.assembly(*WINDOW, "ldrb\tr2, [r1]", "ldrb\tr2, [r1]", "ldrb\tr2, [r1]",
                                    "mov\tr2, #255", "strb\tr2, [r1]", "bx\tlr")
        self.refused("(void)" + SYMBOL + ".unknown_3C; " + SYMBOL + ".unknown_3C |= 0xFF;", real=planted)

    def test_other_constants_members_and_shapes_are_refused(self):
        self.refused(SYMBOL + ".unknown_3C |= 0x7F;")
        self.refused(SYMBOL + ".unknown_3D |= 0xFF;")
        self.refused("x = " + SYMBOL + ".unknown_3C |= 0xFF;")
        self.refused(SYMBOL + ".unknown_3C |= 0xFF;", compiler=False)

    def test_a_variant_that_changes_anything_else_is_refused(self):
        self.refused(SYMBOL + ".unknown_3C |= 0xFF;", variant=STRIPPED)
        self.refused(SYMBOL + ".unknown_3C |= 0xFF;", variant=REAL)
        moved = fixtures.assembly(*WINDOW, "ldrb\tr2, [r1]", "mov\tr2, #254", "strb\tr2, [r1]", "bx\tlr")
        self.refused(SYMBOL + ".unknown_3C |= 0xFF;", variant=moved)
        # the operand read taken out, and the literal pool changed: the variant must keep the pools
        pool = ".L3:\n\t.word\t" + SYMBOL + "\n"
        pooled = VARIANT.replace(pool, pool + ".L5:\n\t.word\t4660\n")
        self.assertNotEqual(pooled, VARIANT)
        self.refused(SYMBOL + ".unknown_3C |= 0xFF;", variant=pooled)

    def test_two_statements_may_not_claim_one_load(self):
        self.refused(SYMBOL + ".unknown_3C |= 0xFF; " + SYMBOL + ".unknown_3C |= 0xFF;")


class CompiledOperandReadTests(unittest.TestCase):
    """the variant compile through agbcc and match.py's own plumbing"""

    @classmethod
    def setUpClass(cls):
        cls.directory = tempfile.TemporaryDirectory()
        cls.root = Path(cls.directory.name)
        entry = plausible.volatile_allow_entries()[0]
        for name in ("config", "src", "include"):
            (cls.root / name).mkdir()
        (cls.root / "config" / "data_symbols.json").write_text(json.dumps({entry["symbol"]: entry["address"]}))
        (cls.root / entry["header"]).write_text(fixtures.HEADER.format(
            declaration=entry["declaration"].replace("; ", ";\n    ")))

    @classmethod
    def tearDownClass(cls):
        cls.directory.cleanup()

    def check(self, body):
        (self.root / "src" / "08028C34.c").write_text(
            '#include "control_flags.h"\nvoid func_08028C34(void)\n{\n' + body + "\n}\n")
        with mock.patch.dict(os.environ, FFTA_ROM=str(self.root / "baserom.bin")):
            return match.allowlisted_volatile_semantics(self.root, 0x08028C34)

    def test_an_all_ones_or_passes_and_a_planted_read_does_not(self):
        s = SYMBOL
        (line,) = self.check(f"{s}.bldcnt_lo |= 0xff; {s}.bldcnt_hi = 0;")
        self.assertIn("all-ones `|=` operand reads (kit#165)", line)
        with self.assertRaises(ValueError) as caught:
            self.check(f"(void){s}.bldcnt_lo; {s}.bldcnt_lo = 0xff; {s}.bldcnt_hi = 0;")
        self.assertIn("dead load", str(caught.exception))
        # a planted read beside a real `|=`: three loads, and the variant loses one
        with self.assertRaises(ValueError) as caught:
            self.check(f"(void){s}.bldcnt_lo; {s}.bldcnt_lo |= 0xff; {s}.bldcnt_hi = 0;")
        self.assertIn("dead load", str(caught.exception))


if __name__ == "__main__":
    unittest.main()
