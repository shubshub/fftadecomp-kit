"""A retried walk's DMA-fill recorder keeps the decomp's reviewed premise rows.

The default retries (the stack-index and closure-slot retries) start the plain walk's recorder afresh
in place, as `recorder.__init__(recorder.rom, ...)`.  Built as `__init__(rom)` alone, the reset dropped
`config/dma_fill_premises.json`, so an owner whose fill needs a reviewed row and whose walk needs one of
those retries lost the row in the retried walk.
"""
import ast
from pathlib import Path
import sys
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import dma_fill_profile as dma_fill


def in_place_resets(tree):
    """Every call `X.__init__(X.rom, ...)`: a recorder started afresh in place."""
    for node in ast.walk(tree):
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr == "__init__" \
                and node.args and isinstance(node.args[0], ast.Attribute) and node.args[0].attr == "rom" \
                and ast.unparse(node.args[0].value) == ast.unparse(node.func.value):
            yield node


class RetryResetTests(unittest.TestCase):
    def test_every_in_place_reset_keeps_the_premises(self):
        found = set()
        for path in sorted((ROOT / "tools").glob("*.py")):
            for call in in_place_resets(ast.parse(path.read_text())):
                owner = ast.unparse(call.func.value)
                found.add(path.name)
                with self.subTest(path=path.name, call=ast.unparse(call)):
                    self.assertEqual([ast.unparse(argument) for argument in call.args],
                                     [f"{owner}.rom", f"{owner}.premises"])
                    self.assertEqual(call.keywords, [])
        # The data-buffer proof's retries reset its one recorder in place; match.py builds one recorder per
        # walked proof (store_bound_premise_profile's composition), each with the premises (below).
        self.assertIn("data_buffer_profile.py", found)

    def test_every_recorder_is_built_with_the_premises(self):
        built = 0
        for path in sorted((ROOT / "tools").glob("*.py")):
            for node in ast.walk(ast.parse(path.read_text())):
                if isinstance(node, ast.Call) and ast.unparse(node.func) in ("dma_fill.Fills", "Fills"):
                    built += 1
                    with self.subTest(path=path.name, call=ast.unparse(node)):
                        self.assertEqual(len(node.args), 2)
                        self.assertIn("dma_fill_premise.snapshot(", ast.unparse(node.args[1]))
        self.assertGreaterEqual(built, 4)

    def test_a_reset_recorder_keeps_its_premises_and_forgets_its_walk(self):
        premises = b'{"0x0801AF08": {"review": "reviewed", "rows": []}}'
        fills = dma_fill.Fills(b"rom", premises)
        fills.observations["site"] = "seen"
        fills.records, fills.address = [], 0x0801AF08
        fills.__init__(fills.rom, fills.premises)
        self.assertEqual((fills.rom, fills.premises), (b"rom", premises))
        self.assertEqual((fills.observations, fills.records, fills.address), ({}, None, None))


if __name__ == "__main__":
    unittest.main()
