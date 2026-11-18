"""Incoming word ownership, Boolean dominance and full transfer-setup report replay."""
import json
import os
from pathlib import Path
import subprocess
import sys
import unittest

from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
from capstone.arm import ARM_REG_R1

TOOLS = Path(__file__).resolve().parents[1] / "tools"
sys.path.insert(0, str(TOOLS))
import analyze
import match
import match_evidence
import owner_graph_profile as graph
import transfer_mask_argument as transfer


def decode(words, start):
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    decoder.detail = True
    data = b"".join(word.to_bytes(2, "little") for word in words)
    ins = {item.address: item for item in decoder.disasm(data, start)}
    edges = {pc: [pc + 2] for pc in ins}
    return ins, edges


class SlotTests(unittest.TestCase):
    def test_outgoing_prefix_has_four_distinct_writes_and_no_side_entry(self):
        site = 0x1010
        ins, edges = decode([0x9000, 0x9001, 0x9002, 0x2101, 0x9103], site - 10)
        pred = transfer.predecessors(edges)
        self.assertEqual(transfer.outgoing(ins, pred, site)[12], site - 2)
        changed, _ = decode([0x9102], site - 2)
        with self.assertRaisesRegex(ValueError, "aligned scalar"):
            transfer.outgoing({**ins, **changed}, pred, site)
        pred[site - 2].add(0x1012)
        with self.assertRaisesRegex(ValueError, "ambiguous"):
            transfer.outgoing(ins, pred, site)

    def test_scalar_definition_must_be_zero_or_one(self):
        pc = 0x1000
        for value in (0, 1, 2):
            ins, edges = decode([0x2100 + value, 0x9103], pc)
            args = (ins, edges, transfer.predecessors(edges), pc, pc + 4, pc + 2)
            if value <= 1:
                self.assertEqual(transfer.argument_value(*args)["value"], value)
            else:
                with self.assertRaisesRegex(ValueError, "Boolean immediate"):
                    transfer.argument_value(*args)

    def test_store_rejects_wrong_slot_pointer_and_return_alias(self):
        store = transfer.STORE
        ins, _ = decode([0x9111], store)
        proof = object.__new__(transfer.MaskedArgumentProof)
        for offset, aliases, returns in ((8, {}, set()), (12, {ARM_REG_R1: -4}, set()), (12, {}, {ARM_REG_R1})):
            with self.assertRaisesRegex(ValueError, "non-pointer argument"):
                proof.store(transfer.ROOT, store, offset, ins[store], aliases, returns)

    def test_plain_frame_verifier_stays_strict(self):
        # Single STR into entry SP+12, followed by an ordinary Thumb return.
        with self.assertRaisesRegex(ValueError, "outside the tracked frame"):
            match.verify_leaf_instructions(bytes.fromhex("0391 7047"), 0x8000800, True,
                                           incoming_narrow_reads=True)


@unittest.skipUnless(os.environ.get("FFTA_TRANSFER_MASK_ROOT"), "set FFTA_TRANSFER_MASK_ROOT to the game fixture")
class NativeSlotTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ["FFTA_TRANSFER_MASK_ROOT"]).resolve()
        cls.rom = (cls.root / "baserom.bin").read_bytes()
        cls.mapping = (cls.root / "config/functions.json").read_bytes()
        cls.rows = json.loads(cls.mapping)
        cls.index = (cls.root / "symbols/functions.txt").read_bytes()

    def graph(self, address, size):
        offset = address - match.ROM_BASE
        data = self.rom[offset:offset + size]
        ref = analyze.refine_function(data, address, self.rows, max_bytes=size,
            max_instructions=size//2, rom_end=match.ROM_BASE + len(self.rom), same_owner_long_branches=True)
        ins, edges, _, _, _ = graph.graph(data, address, ref)
        return data, ins, edges

    def test_changed_mask_store_and_reload(self):
        data, ins, edges = self.graph(transfer.ROOT, 364)
        transfer.validate_mask(data, ins, edges)
        for site, encoding in ((transfer.STORE-6, 0x2003), (transfer.STORE, 0x9110), (transfer.STORE+10, 0x9B10)):
            mutated = bytearray(data)
            k = site - transfer.ROOT
            mutated[k:k+2] = encoding.to_bytes(2, "little")
            with self.assertRaisesRegex(ValueError, "same-word"):
                transfer.validate_mask(mutated, ins, edges)

    def test_taken_edge_must_dominate_zero_input(self):
        caller, site, store, branch = 0x0803D550, 0x0803D64E, 0x0803D646, 0x0803D580
        _, ins, edges = self.graph(caller, 720)
        args = (caller, site, store)
        accepted = transfer.argument_value(ins, edges, transfer.predecessors(edges), *args)
        self.assertEqual(accepted["zero_case_edge"], [branch, 0x0803D5AC])
        changed = {**edges, branch-2: [branch, 0x0803D5AC]}
        with self.assertRaisesRegex(ValueError, "bypasses the zero case"):
            transfer.argument_value(ins, changed, transfer.predecessors(changed), *args)

    def test_caller_rejects_short_allocation(self):
        caller = 0x0803D550
        changed = bytearray(self.rom)
        k = 0x0803D55A - match.ROM_BASE
        changed[k:k+2] = bytes.fromhex("83b0")  # SUB SP,#12 leaves word four outside the area.
        with self.assertRaisesRegex(ValueError, "dominating writable allocation"):
            transfer.caller_record(bytes(changed), self.mapping, self.index, self.rows,
                                   caller, transfer.CALLERS[caller])

    def test_inventory_rejects_added_thumb_pointer_or_direct_reference(self):
        for offset, addition in ((0x123457, (transfer.ROOT | 1).to_bytes(4, "little")),
                                 (transfer.ROOT-match.ROM_BASE, bytes.fromhex("fff7feff"))):
            changed = bytearray(self.rom)
            changed[offset:offset+4] = addition
            with self.assertRaisesRegex(ValueError, "reference set differs|unexpected address literal"):
                transfer.references(changed)

    def test_default_refusal_and_fresh_report(self):
        command = [sys.executable, str(TOOLS / "match.py"), "--root", str(self.root),
                   "--no-write", f"{transfer.ROOT:08X}"]
        ordinary = subprocess.run(command, capture_output=True, text=True)
        self.assertNotEqual(ordinary.returncode, 0)
        self.assertIn("outside the tracked frame", ordinary.stdout + ordinary.stderr)
        report = (self.root / "docs/match/08037C84.md").read_text()
        self.assertTrue(match_evidence.report_matches(report, self.root, transfer.ROOT))
        line = next(line for line in report.splitlines() if line.startswith("* owner runtime evidence: "))
        evidence = json.loads(line.split("`")[1])
        proof = evidence["manifest"]["proof"]["transfer_argument"]
        self.assertEqual([x["eighth_word"]["value"] for row in proof["callers"] for x in row["calls"]],
                         [0, 0, 1, 0, 1, 1, 1, 1, 0, 0])
        for field in ("* compiled :", "* ROM bytes:"):
            marker = next(line for line in report.splitlines() if line.startswith(field))
            self.assertFalse(match_evidence.report_matches(report.replace(marker, marker+"\n"+marker), self.root, transfer.ROOT))
