"""bios-fill-temporary-v1, rule 4: each fill's necessity, R's fills paired with the variant's by call order.

Removing a group's qualifiers must take the volatile store away from exactly the group's fills.  Fills
in disjoint scopes may share a slot in R and not in the variant (0x08023FD0: its first and fourth
fills share sp+0, and without the first fill's qualifier the fourth moves to sp+6), so the stores are
compared fill by fill, not slot by slot: the variant's BIOS calls pair with R's by call order, and the
pairing refuses unless the calls, their controls, destinations and sources' kinds agree.  Every other
fill keeps one volatile store of its width at any offset, and no volatile frame store of the variant
lies outside a fill.
"""
from pathlib import Path
import os
import re
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import bios_fill_temporary as fill
import volatile_rom_proof as proof
import test_bios_fill_carried as carried
import test_bios_fill_temporary as base

DEST = ("param", 0, None)


def call(control=0x01000100, slot=(18, -2), stores=(), **other):
    """a bios_calls() entry; stores: (insn index, width) of its block's volatile stores to its source"""
    return dict(dict(call=None, callee="func_0814186C", control=control, destination=DEST, slot=slot,
                     addressed=False, stores=[(index, (18, -2, width)) for index, width in stores]), **other)


# R: two fills, a copy from a frame buffer (no fill: no volatile store) and a copy from a non-frame source
REAL = [call(stores=((10, 2),)), call(control=0x01000800, stores=((20, 2),)),
        call(control=0x04000010, slot=(18, -16)), call(control=0x04000010, slot=None)]
FILLS = {0, 1}


def removal(calls, stores=None, reach=1):
    """paired_removal of R and a variant whose calls are calls; stores defaults to the calls' own stores"""
    stores = [index for one in calls for index, _ in one["stores"]] if stores is None else stores
    return fill.paired_removal(REAL, calls, FILLS, stores, reach, 7)


LOST = call()
KEPT = call(control=0x01000800, slot=(18, -6), stores=((21, 2),))


class PairingTests(unittest.TestCase):
    def test_the_group_s_fills_lose_their_store_and_the_others_keep_one_at_any_offset(self):
        self.assertEqual(removal([LOST, KEPT, REAL[2], REAL[3]]), {0})
        self.assertEqual(removal([LOST, call(control=0x01000800), REAL[2], REAL[3]], reach=2), {0, 1})
        # without its qualifier a word temporary is a local the expand pass has not placed yet (addressof)
        self.assertEqual(removal([dict(LOST, slot=None, addressed=True), KEPT, REAL[2], REAL[3]]), {0})

    def test_an_ambiguous_pairing_refuses(self):
        for label, calls, reason in (
                ("a different fill count", [LOST, KEPT, REAL[2], REAL[3], call(stores=((30, 2),))],
                 "makes 5 BIOS calls, not 4"),
                ("a reordered pair", [KEPT, LOST, REAL[2], REAL[3]], "BIOS call 1 has another control"),
                ("another BIOS call sequence", [dict(LOST, callee="func_08141868"), KEPT, REAL[2], REAL[3]],
                 "BIOS call 1 has another callee"),
                ("another destination", [dict(LOST, destination=("param", 0, 0x200)), KEPT, REAL[2], REAL[3]],
                 "BIOS call 1 has another destination"),
                ("a fill's source no local", [dict(LOST, slot=None), KEPT, REAL[2], REAL[3]],
                 "BIOS call 1, a fill, has no local as its source"),
                ("a frame copy's source no frame slot", [LOST, KEPT, dict(REAL[2], slot=None, addressed=True),
                                                         REAL[3]], "BIOS call 3 has no frame slot as its source"),
                ("a frame slot where R has none", [LOST, KEPT, REAL[2], dict(REAL[3], slot=(18, -8))],
                 "BIOS call 4 has a frame slot as its source")):
            with self.subTest(label=label), self.assertRaisesRegex(proof.ProofError, reason):
                removal(calls)

    def test_every_volatile_store_of_the_variant_is_a_kept_fill_s(self):
        for label, calls, stores, reason in (
                ("an extra unpaired fill", [LOST, KEPT, dict(REAL[2], stores=[(30, (18, -16, 2))]), REAL[3]], None,
                 "BIOS call 3, no fill, has a volatile store to its source"),
                ("a volatile store outside any fill", [LOST, KEPT, REAL[2], REAL[3]], [21, 40],
                 "a volatile frame store lies outside every fill"),
                ("a fill keeping two stores", [LOST, dict(KEPT, stores=[(21, (18, -6, 2)), (22, (18, -6, 2))]),
                                               REAL[2], REAL[3]], None,
                 "the fill of BIOS call 2 keeps other volatile stores"),
                ("a fill keeping a store of another width", [LOST, dict(KEPT, stores=[(21, (18, -6, 4))]), REAL[2],
                                                             REAL[3]], None,
                 "the fill of BIOS call 2 keeps other volatile stores"),
                ("no fill losing its store", [REAL[0], KEPT, REAL[2], REAL[3]], None,
                 "takes the volatile store of 0 fills, not of the 1 they reach")):
            with self.subTest(label=label), self.assertRaisesRegex(proof.ProofError, reason):
                removal(calls, stores)
        with self.assertRaisesRegex(proof.ProofError, "line 7 does not account for its volatile stores: removing "
                                                      "them takes the volatile store of 2 fills, not of the 1"):
            removal([LOST, call(control=0x01000800), REAL[2], REAL[3]])


class CallsTests(unittest.TestCase):
    """bios_calls() on expand RTL"""

    def test_each_call_keeps_its_own_block_s_stores_to_its_own_source(self):
        # fill 2's block also stores to another slot (sp-6), and fill 1's earlier block stored to the same slot
        other = (9, "insn (set (mem/v/f:HI (plus:SI (reg:SI 18 virtual-stack-vars) (const_int -6)) 0) "
                    "(const_int 0)) -1 (nil) (nil)")
        frame = "(plus:SI (reg:SI 18 virtual-stack-vars) (const_int -16))"
        rtl = base.function([base.ENTRY] + base.fill_insns(10) + [other] + base.fill_insns(20, dest=frame))
        calls = fill.bios_calls(rtl, proof.Resolver(rtl))
        self.assertEqual([(one["call"].uid, one["slot"], one["addressed"], one["control"], one["destination"],
                           [(rtl.insns[index].uid, key) for index, key in one["stores"]]) for one in calls],
                         [(16, (18, -2), False, 0x01000100, ("param", 0, 0), [(12, (18, -2, 2))]),
                          (26, (18, -2), False, 0x01000100, ("frame", 18, (18, -16)), [(22, (18, -2, 2))])])

    def test_a_word_temporary_without_its_qualifier_is_an_addressed_local(self):
        insns = [base.ENTRY, (10, "insn (set (reg:SI 30) (addressof:SI (reg/v:SI 33) 32)) -1 (nil) (nil)")] + \
            [(uid, text.replace("(reg:SI 110))", "(reg:SI 30))")) for uid, text in base.fill_insns(10, store=False)
             if uid != 10]
        rtl = base.function(insns)
        (one,) = fill.bios_calls(rtl, proof.Resolver(rtl))
        self.assertEqual((one["slot"], one["addressed"], one["stores"]), (None, True, []))


# 0x08023FD0's shape: fills 1 and 4 share sp+0 in disjoint scopes, 2 and 3 sp+2; each variant moves a fill
SHARED = """extern u32 func_08000500(u32);
extern void func_08000600(void *);
void func_08000200(u16 *dest, u32 flag)
{
    func_08000400(0);
    if (!func_08000500(flag)) {
        { volatile u16 fill = 0; func_0814186C((const void *)&fill, dest, 0x01000100); }
        { volatile u16 fill = 0; func_0814186C((const void *)&fill, dest + 0x100, 0x01000100); }
    }
    func_08000400(1);
    func_08000600(dest);
    { volatile u16 fill = 0; func_0814186C((const void *)&fill, dest + 0x200, 0x01000800); }
    { volatile u16 fill = 0; func_0814186C((const void *)&fill, dest + 0x300, 0x01000800); }
}
"""
# a copy (no fill) before the fills: R's BIOS calls and its fills are numbered apart
COPY_FIRST = SHARED.replace("u32 flag)", "u32 flag, const u16 *source)").replace(
    "    if (!func", "    func_0814186C(source, dest + 0x400, 0x00000010);\n    if (!func")


@unittest.skipUnless(carried.tools_present(), "fixed compiler, ARM tools and capstone required")
class CompiledTests(unittest.TestCase):
    def setUp(self):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", Path(__file__).resolve().parents[1] / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        self.directory = tempfile.TemporaryDirectory(prefix="bios_fill_pairing_", dir=scratch)
        self.addCleanup(self.directory.cleanup)

    def proved(self, body, admitted=frozenset()):
        directory = tempfile.mkdtemp(dir=self.directory.name)
        root = carried.tree(directory, body)
        return fill.prove(root, root, "src/08000200.c", carried.HEAD + body, set(admitted),
                          rom=(root / "baserom.bin").read_bytes())

    def check_shared(self, body):
        """each of the four groups owns its own fill, in order, at R's slot"""
        texts = [text for _, (state, text) in self.proved(body) if state == "admitted"]
        self.assertEqual(len(texts), 4, texts)
        for text, slot, control in zip(texts, (0, 2, 2, 0), ("0x01000100", "0x01000100", "0x01000800",
                                                            "0x01000800")):
            self.assertEqual(len(re.findall(r"[0-9A-F]{8} fills from sp\+", text)), 1, text)
            self.assertIn(f"fills from sp+{slot:#x} (address formed at", text)
            self.assertIn(f"control {control}, 2-byte units", text)
        sites = [int(re.search(r"([0-9A-F]{8}) fills from", text)[1], 16) for text in texts]
        self.assertEqual(sites, sorted(set(sites)), texts)

    def test_fills_sharing_a_slot_in_disjoint_scopes_each_own_their_fill(self):
        self.check_shared(SHARED)

    def test_each_group_s_record_names_its_own_fill_after_a_copy(self):
        self.check_shared(COPY_FIRST)

    def test_the_groups_own_every_fill_once(self):
        reason = "the fills do not account for every volatile frame store"
        # a group another exception admitted is no group here, and its fill is then nobody's
        second = fill.fill_groups(carried.HEAD + SHARED)[1]["offsets"]
        with self.assertRaisesRegex(proof.ProofError, reason):
            self.proved(SHARED, admitted=second)
        # a fill two groups' removals take (no compile does this; the pairing is replaced to show the check)
        with mock.patch.object(fill, "paired_removal", side_effect=[{0, 1}, {1}, {2}, {3}]), \
                self.assertRaisesRegex(proof.ProofError, reason):
            self.proved(SHARED)


@unittest.skipUnless(carried.tools_present(), "fixed compiler, ARM tools and capstone required")
class IssuanceTests(unittest.TestCase):
    """0x08023FD0's shape through match.py as a subprocess (`__main__`), then replayed as status.py --verify does"""

    def test_the_shared_slot_shape(self):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", Path(__file__).resolve().parents[1] / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        tools = Path(fill.__file__).parent
        with tempfile.TemporaryDirectory(prefix="bios_fill_pairing_", dir=scratch) as directory:
            root = carried.tree(directory, SHARED)
            environment = dict(os.environ, FFTA_ROM=str(root / "baserom.bin"), PYTHONDONTWRITEBYTECODE="1")
            result = subprocess.run([sys.executable, str(tools / "match.py"), "--root", str(root), "0x08000200"],
                                    capture_output=True, text=True, env=environment, timeout=900)
            output = result.stdout + result.stderr
            self.assertEqual(result.returncode, 0, output[-3000:])
            self.assertIn("MATCH - byte identical", output)
            report = (root / "docs/match/08000200.md").read_text()
            self.assertEqual(report.count("is the SDK's BIOS fill temporary (a block)"), 4, report[-4000:])
            replay = subprocess.run([sys.executable, "-c", carried.REPLAY, str(tools), str(root)],
                                    capture_output=True, text=True, env=environment, timeout=900)
            self.assertIn("replay True", replay.stdout, (replay.stdout + replay.stderr)[-3000:])


if __name__ == "__main__":
    unittest.main()
