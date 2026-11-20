import json, os, sys, unittest
from types import SimpleNamespace
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import title_menu_style as title
from match_evidence import mapping_snapshot, data_snapshot
from inert_spin_profile import index_snapshot
import stack_index_precondition_profile as indexed


class TitleInput(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        location = os.environ.get("FFTA_TITLE_MENU_ROOT")
        if not location:
            raise unittest.SkipTest("requires the USA ROM and title menu source")
        root = Path(location)
        cls.root = root
        cls.rom = (root / "baserom.bin").read_bytes()
        cls.data = cls.rom[0x136A10:0x136DEC]
        cls.mapping = mapping_snapshot(root)
        cls.idx = index_snapshot(root)
        cls.obj = data_snapshot(root)
        cls.premises = {
            title.ADDRESS: dict(
                review="Both title selectors are in 0..2 at their indexed style writes.",
                rows=[
                    dict(
                        site=f"0x{pc:08X}",
                        expression="(u32)" + indexed.render(title.expression(read)),
                        bound=3,
                    )
                    for pc, (_, read) in title.STORES.items()
                ],
            )
        }

    def run_proof(self, **change):
        kw = dict(
            data=self.data,
            rom=self.rom,
            mapping=self.mapping,
            index=self.idx,
            objects=self.obj,
            reviewed=self.premises,
        )
        return title.prove(**(kw | change))

    def test_complete(self):
        proof = self.run_proof()
        self.assertEqual(proof["instructions"], 390)
        self.assertEqual(len(proof["runtime_sites"]), 2)
        self.assertEqual(len(proof["private_style_stores"]), 2)
        self.assertTrue(
            all(
                r["bound"] == 3 and r["premise_proved"] is False
                for r in proof["conditional_indices"]["preconditions"]
            )
        )

    def test_requires_review(self):
        with self.assertRaisesRegex(ValueError, "reviewed entry"):
            self.run_proof(reviewed={})

    def test_rejects_literal_rebinding(self):
        obj = json.loads(self.obj)
        obj["data_083A8CFE"] = "0x083A8D06"
        with self.assertRaisesRegex(ValueError, "title ROM object"):
            self.run_proof(objects=json.dumps(obj).encode())

    def test_rejects_different_bound(self):
        p = json.loads(json.dumps(self.premises[title.ADDRESS]))
        p["rows"][0]["bound"] = 4
        with self.assertRaisesRegex(ValueError, "reviewed entry"):
            self.run_proof(reviewed={title.ADDRESS: p})

    def test_missing_third_style_initialization(self):
        # Replace only the primary last-byte store. Test the actual range proof directly.
        raw = bytearray(self.data)
        raw[0x1C:0x1E] = bytes.fromhex("c046")
        refinement = title.owner.refine(bytes(raw), title.ADDRESS, self.mapping)
        ins, _, _, _, _ = title.graph.graph(bytes(raw), title.ADDRESS, refinement)
        policy = SimpleNamespace(
            spills=set(),
            returned={},
            accesses=set(),
            derivations={0x08136AB6, 0x08136C98},
        )
        with self.assertRaisesRegex(ValueError, "three style bytes"):
            title.check_arrays(bytes(raw), ins, policy)

    def test_unsigned_halfword_store_exceeds_array(self):
        raw = bytearray(self.data)
        raw[0xAC:0xAE] = bytes.fromhex("1080")
        refinement = title.owner.refine(bytes(raw), title.ADDRESS, self.mapping)
        ins, _, _, _, _ = title.graph.graph(bytes(raw), title.ADDRESS, refinement)
        policy = SimpleNamespace(
            spills=set(),
            returned={},
            accesses=set(),
            derivations={0x08136AB6, 0x08136C98},
        )
        with self.assertRaisesRegex(ValueError, "align|style store"):
            title.check_arrays(bytes(raw), ins, policy)

    def test_dual_index_count(self):
        idx = self.idx.replace(
            b"08136A10 08136DEC   988 390", b"08136A10 08136DEC   988 391"
        )
        self.assertNotEqual(idx, self.idx)
        with self.assertRaisesRegex(ValueError, "dual.index"):
            self.run_proof(index=idx)


if __name__ == "__main__":
    unittest.main()
