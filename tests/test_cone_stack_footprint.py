"""The cone's two actual protected call sites and its outgoing cursor argument."""

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB

TOOLS = Path(__file__).resolve().parents[1] / "tools"
sys.path.insert(0, str(TOOLS))
import cone_stack_footprint as cone
import match_evidence
import named_data_buffer_profile as named


def decode(pc, halfword):
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    decoder.detail = True
    return next(decoder.disasm(halfword.to_bytes(2, "little"), pc))


class StructuralNegatives(unittest.TestCase):
    def test_reading_expired_r2_before_kill_is_rejected(self):
        pc = 0x080B49F4
        bad = decode(pc, 0x0010)  # movs r0,r2
        with self.assertRaisesRegex(ValueError, "expired R2 observed"):
            cone.false_continuation((b"", {pc: bad}, {pc: []}, {}), pc, 0)

    def test_returning_with_nonzero_stack_depth_is_rejected(self):
        pc = 0x080A0254
        sub = decode(pc, 0xB081)
        with self.assertRaisesRegex(ValueError, "unbalanced"):
            cone.stack_sites(pc, {pc: sub}, {pc: []}, {})


@unittest.skipUnless(
    os.environ.get("FFTA_CONE_ROOT"), "set FFTA_CONE_ROOT to a USA game root with the recovered cone C"
)
class NativeConeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.game = Path(os.environ["FFTA_CONE_ROOT"]).resolve()
        cls.rom = (cls.game / "baserom.bin").read_bytes()
        cls.mapping = (cls.game / "config/functions.json").read_bytes()
        cls.index = (cls.game / "symbols/functions.txt").read_bytes()
        cls.objects = (cls.game / "config/data_symbols.json").read_bytes()
        cls.entries = {int(r["rom"], 16): int(r["end"], 16) for r in json.loads(cls.mapping)}
        cls.proof = named.NamedDataBufferProof(cls.rom, cls.mapping, cls.index, cls.objects)
        cls.owners, cls.closure = cone.footprint(cls.proof, cls.entries)
        cls.owners[cone.ROOT] = cone.native_graph(cls.proof, cone.ROOT, cls.entries)

    def changed(self, at, halfword):
        data = bytearray(self.rom)
        i = at - 0x08000000
        data[i : i + 2] = halfword.to_bytes(2, "little")
        return named.NamedDataBufferProof(bytes(data), self.mapping, self.index, self.objects)

    def test_reads_and_forwarded_stack_words(self):
        self.assertEqual(len(self.closure), 29)
        self.assertEqual(sum(r["instructions"] for r in self.closure.values()), 2009)
        self.assertEqual(self.closure[cone.PREDICATE]["incoming"], [0, 4, 8, 12])
        for site, word in [(0x080A026A, 0x9E1C), (0x0809FF02, 0x9D1C)]:
            with self.subTest(address=hex(site)), self.assertRaisesRegex(ValueError, "incoming words"):
                cone.footprint(self.changed(site, word), self.entries)

    def test_scratch_consumer_uses_and_correlated_result(self):
        rows = cone.scratch_lifetime(self.proof, self.owners)["continuations"]
        self.assertEqual(len(rows), 8)
        self.assertEqual([r[2][-1] for r in rows if r[3] == "killed"], [0x080B49F4])
        cases = [
            (cone.ROOT, 0x080B49DA, 0x0015, "expired R2 observed"),
            (0x0809FEF0, 0x0809FFBE, 0x2001, "expired R2 observed"),
        ]
        for owner, site, word, error in cases:
            mixed = dict(self.owners)
            altered = self.changed(site, word)
            mixed[owner] = cone.native_graph(altered, owner, self.entries)
            with self.subTest(site=hex(site)), self.assertRaisesRegex(ValueError, error):
                cone.scratch_lifetime(altered, mixed)

    def test_root_call_and_store_refuse_escaped_aliases(self):
        proof = cone.ConeStackProof(self.rom, self.mapping, self.index, self.objects, policy=cone.SELECTOR)
        # Exercise the transfer after native authentication, mutating one input at a time.
        proof.certificate = {}
        stack = [(False, False, True)] * 26
        for aliases, slots in [({cone.ARM_REG_R2: -88}, {-52: -88}), ({}, {-104: -88}), ({}, {-52: -87})]:
            with self.assertRaisesRegex(ValueError, r"private SP\+52 spill"):
                proof.check_call(cone.PREDICATE, aliases, stack, slots, site=0x080B49B2)
        ins = self.owners[cone.ROOT][1][0x080B49D0]
        for off, aliases, ret in [
            (16, {}, set()),
            (12, {cone.ARM_REG_R2: -88}, set()),
            (12, {}, {cone.ARM_REG_R2}),
        ]:
            with self.assertRaisesRegex(ValueError, "writable formal"):
                proof.cursor_store(cone.ROOT, 0x080B49D0, off, ins, aliases, ret)

    def test_caller_cursor_word_and_resumed_use(self):
        native = self.owners[cone.ROOT]
        self.assertEqual(
            cone.outgoing_cursor(self.proof, self.entries, native)["updated_incoming_word"], 12
        )
        for site, word, error in [
            (0x080B4BF0, 0x9404, "argument stores"),
            (0x080B4C7A, 0x9D03, "observed before frame discard"),
        ]:
            with self.subTest(site=hex(site)), self.assertRaisesRegex(ValueError, error):
                cone.outgoing_cursor(self.changed(site, word), self.entries, native)
        altered = self.changed(0x080B49CE, 0x3208)
        with self.assertRaisesRegex(ValueError, "four-byte advancement"):
            cone.outgoing_cursor(altered, self.entries, cone.native_graph(altered, cone.ROOT, self.entries))

    def test_cursor_requires_both_real_mov_opcodes(self):
        for pc, encoding, operands in [
            (0x080B4A2A, 0x459A, "sl, r3"),
            (0x080B4A2A, 0x449A, "sl, r3"),
            (0x080B4BEE, 0x4554, "r4, sl"),
            (0x080B4BEE, 0x4454, "r4, sl"),
        ]:
            with self.subTest(site=hex(pc), encoding=hex(encoding)):
                substituted = decode(pc, encoding)
                self.assertEqual(substituted.op_str, operands)
                self.assertIn(substituted.mnemonic, ("cmp", "add"))
                with self.assertRaisesRegex(ValueError, "requires MOV"):
                    cone.outgoing_cursor(self.changed(pc, encoding), self.entries, self.owners[cone.ROOT])

    def test_cursor_initialization_dominates_and_uses_original_argument(self):
        # BEQ +0 at the preceding instruction leaves both a path through MOV and a bypass.
        for replacement, expected in [
            (0xD000, "bypasses required cursor definition"),
            (0x2300, "incoming output argument R3 is overwritten"),
        ]:
            with self.subTest(replacement=hex(replacement)), self.assertRaisesRegex(ValueError, expected):
                cone.outgoing_cursor(
                    self.changed(0x080B4A28, replacement), self.entries, self.owners[cone.ROOT]
                )

    def test_raw_call_pairs_and_thumb_pointers(self):
        site = 0x080B4BF2
        self.assertEqual(
            cone.raw_cursor_references(self.rom, site),
            {
                "raw_thumb_bl_sites": [site],
                "encoded_thumb_pointer_occurrences": 0,
                "rom_bytes": 0x1000000,
                "rom_sha256": cone.ROM_SHA256,
            },
        )
        image = bytearray(self.rom)
        extra = site + 4
        raw = bytes.fromhex("fff769fe")
        decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
        decoder.detail = True
        added = next(decoder.disasm(raw, extra))
        self.assertEqual((added.mnemonic, added.operands[0].imm), ("bl", cone.ROOT))
        index = extra - 0x08000000
        image[index : index + 4] = raw
        with self.assertRaisesRegex(ValueError, "raw Thumb BL reference"):
            cone.raw_cursor_references(image, site)
        image = bytearray(self.rom)
        image[0x1001:0x1005] = (cone.ROOT | 1).to_bytes(4, "little")
        with self.assertRaisesRegex(ValueError, "literal Thumb pointer"):
            cone.raw_cursor_references(image, site)

        with self.assertRaisesRegex(ValueError, "complete 16 MiB USA ROM"):
            cone.raw_cursor_references(self.rom[:-4], site)
        image = bytearray(self.rom)
        image[-1] ^= 1
        with self.assertRaisesRegex(ValueError, "approved USA ROM identity"):
            cone.raw_cursor_references(image, site)

    def test_native_cli_replay_and_evidence_integrity(self):
        with tempfile.TemporaryDirectory() as directory:
            game = Path(directory)
            for name in ("baserom.bin", "config", "include", "symbols"):
                (game / name).symlink_to(self.game / name, target_is_directory=(self.game / name).is_dir())
            (game / "src").mkdir()
            p = game / "src/080B48CC.c"
            p.write_bytes((self.game / "src" / p.name).read_bytes())
            command = [
                sys.executable,
                "-B",
                str(TOOLS / "match.py"),
                "--root",
                str(game),
                "080B48CC",
                "--owner-runtime-profile",
            ]
            refused = subprocess.run(command + [named.SELECTOR], capture_output=True, text=True)
            self.assertNotEqual(refused.returncode, 0)
            self.assertIn("return register", refused.stderr)
            hit = subprocess.run(command + [cone.SELECTOR], capture_output=True, text=True)
            self.assertEqual(hit.returncode, 0, hit.stderr)
            self.assertIn("336 bytes", hit.stdout)
            report = (game / "docs/match/080B48CC.md").read_text()
            replay = lambda text: match_evidence.report_matches(text, str(game), cone.ROOT)
            self.assertTrue(replay(report))
            for old, new in [
                ('"encoded_thumb_pointer_occurrences":0', '"encoded_thumb_pointer_occurrences":1'),
                ('"updated_incoming_word":12', '"updated_incoming_word":16'),
                ('"instructions":165', '"instructions":166'),
                (cone.SELECTOR, named.SELECTOR),
            ]:
                self.assertIn(old, report)
                self.assertFalse(replay(report.replace(old, new)))
            p.write_text(p.read_text().replace("depth * 2 + 1", "depth * 2 + 3"))
            self.assertFalse(replay(report))


if __name__ == "__main__":
    unittest.main()
