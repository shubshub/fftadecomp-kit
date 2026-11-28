"""Reviewed store bounds in a replayed callee loop (store_bound_premise_profile).

The fixtures are assembled Thumb owners and callees in the 0812E4F4 shape: the owner passes a u16[2]
at the top of its frame, and the callee stores one halfword per qualifying iteration of a five-pass
loop through an advancing pointer, so the bounded loop replay refuses the third store.  No game ROM
is needed.
"""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import match
import match_evidence as evidence
import store_bound_premise_profile as store_bound

BASE = match.ROM_BASE
CALLER = ("push {r4, lr}\nsub sp, #4\nadds r4, r0, #0\nmov r1, sp\nadds r0, r4, #0\nbl callee\n"
          "ldr r0, [sp]\nadd sp, #4\npop {r4}\npop {r1}\nbx r1")
# The 0812E4F4 loop: five passes over query(), one strh per nonzero result.
LOOP = """push {{r4, r5, r6, r7, lr}}
mov r7, sb
mov r6, r8
push {{r6, r7}}
mov sb, r0
adds r6, r1, #0
adds r5, r1, #0
movs r0, #0
strh r0, [r6]
strh r0, [r6, #2]
movs r7, #0
movs r0, #0
mov r8, r0
loop:
adds r1, r7, #0
mov r0, sb
bl query
adds r4, r0, #0
cmp r4, #0
beq skip
site:
strh r4, [r6]
adds r6, #2
movs r0, #1
add r8, r0
skip:
{extra}
adds r7, #1
cmp r7, #4
ble loop
mov r0, r8
pop {{r3, r4}}
mov r8, r3
mov sb, r4
pop {{r4, r5, r6, r7}}
pop {{r1}}
bx r1"""
QUERY = "movs r0, #1\nbx lr"
# The same loop behind an early return on an unknown query() result, so that one path of every call returns
# with no store.
EARLY = LOOP.replace("mov r8, r0\nloop:", "mov r8, r0\nmov r0, sb\nbl query\ncmp r0, #0\nbeq done\nloop:") \
    .replace("ble loop\nmov r0, r8", "ble loop\ndone:\nmov r0, r8")
# A store at every pass through a second advancing pointer.
EVERY_PASS = "site2:\nstrh r4, [r5]\nadds r5, #2"
# A store at every pass through a second advancing pointer, on a result of 1 only (a test the replay cannot
# decide), so that some paths store at most twice and return.
CONDITIONAL = "cmp r4, #1\nbne skip2\nsite2:\nstrh r4, [r5]\nadds r5, #2\nskip2:"
# A store at every pass; after the second (pass 1) the call may return on an unknown result, else the loop
# runs on.  The frame allows two, and the code one or two executions or more.
TWICE = ("site2:\nstrh r4, [r5]\nadds r5, #2\ncmp r7, #1\nbne stay\nmov r0, sb\nbl query\ncmp r0, #0\n"
         "beq done\nstay:")
DONE = LOOP.replace("ble loop\nmov r0, r8", "ble loop\ndone:\nmov r0, r8")
# An unknown choice sets r2 to 1 (arm A) or 2 (arm B) before the first store; after it only arm A may
# return, then `movs r2, #0` makes both arms' states equal, and every later pass stores.
# A callee prologue and epilogue for loops written out in full (as `LOOP` templates: braces doubled).
HEAD = ("push {{r4, r5, r6, r7, lr}}\nmov r7, sb\nmov r6, r8\npush {{r6, r7}}\nmov sb, r0\nadds r6, r1, #0\n"
        "adds r5, r1, #0\nmovs r0, #0\nstrh r0, [r6]\nstrh r0, [r6, #2]\nmovs r7, #0\n")
TAIL = "pop {{r3, r4}}\nmov r8, r3\nmov sb, r4\npop {{r4, r5, r6, r7}}\npop {{r1}}\nbx r1"
MERGED = HEAD + """movs r4, #5
adds r1, r7, #0
mov r0, sb
bl query
cmp r0, #0
CHOICE
site:
strh r4, [r6]
adds r6, #2
cmp r2, #1
bne z
adds r1, r7, #0
mov r0, sb
bl query
cmp r0, #0
beq done
z:
movs r2, #0
adds r7, #1
cmp r7, #4
ble site
done:
mov r0, r8
""" + TAIL
# On pass 0 a stored halfword is rewound (subs r6, #2), so the storing path (one store counted) and the
# skipping path (none) meet with equal registers and flags; on later passes every store advances.  The
# storing arm is the fall-through, or (swapped) the branch target.
COUNT_MERGE = HEAD + """loop:
adds r1, r7, #0
mov r0, sb
bl query
adds r4, r0, #0
cmp r4, #0
beq skip
site:
strh r4, [r6]
adds r6, #2
cmp r7, #0
bne next
subs r6, #2
b next
skip:
next:
adds r7, #1
cmp r7, #4
ble loop
mov r0, r8
""" + TAIL
COUNT_MERGE_SWAPPED = COUNT_MERGE.replace("beq skip\nsite:", "bne site\nb next\nsite:").replace(
    "subs r6, #2\nb next\nskip:\nnext:", "subs r6, #2\nnext:")
MERGED_A = MERGED.replace("CHOICE", "beq armB\narmA:\nmovs r2, #1\nb site\narmB:\nmovs r2, #2\nb site")
MERGED_B = MERGED.replace("CHOICE", "bne armA\narmB:\nmovs r2, #2\nb site\narmA:\nmovs r2, #1\nb site")
# The owner with a u16[6] (twelve bytes) instead of a u16[2].
CALLER12 = CALLER.replace("sub sp, #4", "sub sp, #12").replace("add sp, #4", "add sp, #12")


class StoreBoundTests(unittest.TestCase):
    def setUp(self):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="store_bound_", dir=scratch)
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        (self.root / "config").mkdir()
        environment = patch.dict(os.environ, {"FFTA_ROM": str(self.root / "baserom.bin")})
        environment.start()
        self.addCleanup(environment.stop)

    def build(self, extra="", caller=CALLER, query=QUERY, loop=LOOP):
        text = (".syntax unified\n.arch armv4t\n.thumb\n.text\n"
                ".global caller, caller_end, callee, callee_end, query, query_end, site, site2\n"
                f"caller:\n{caller}\n.align 2\n.ltorg\ncaller_end:\n.org 0x100\ncallee:\n"
                f"{loop.format(extra=extra)}\n.align 2\n.ltorg\ncallee_end:\n.org 0x200\nquery:\n{query}\nquery_end:\n")
        assembly = self.root / "fixture.s"
        assembly.write_text(text)
        for command in (
            ["arm-none-eabi-as", "-mthumb-interwork", str(assembly), "-o", str(self.root / "f.o")],
            ["arm-none-eabi-ld", "-Ttext=0x08000000", "-e", "caller", str(self.root / "f.o"),
             "-o", str(self.root / "f.elf")],
            ["arm-none-eabi-objcopy", "-O", "binary", "--only-section=.text",
             str(self.root / "f.elf"), str(self.root / "baserom.bin")],
        ):
            subprocess.run(command, check=True, capture_output=True)
        image = match.elf_image((self.root / "f.elf").read_bytes())
        self.symbols = {symbol["name"]: symbol["value"] for symbol in image["symbols"]}
        self.rom = (self.root / "baserom.bin").read_bytes()
        self.mapping = json.dumps([
            {"rom": f"0x{self.symbols[name]:08X}", "end": f"0x{self.symbols[name + '_end']:08X}", "mode": "thumb"}
            for name in ("caller", "callee", "query")]).encode()
        self.body = self.rom[:self.symbols["caller_end"] - BASE]
        self.callee, self.site = self.symbols["callee"], self.symbols["site"]
        return self.symbols

    def make_proof(self):
        return match.BufferCallProof(self.rom, self.mapping, stack_arguments=True, loop_replay=True,
                                     bios_wrappers=True, dead_registers=True)

    def run_walk(self, proof):
        return match.verify_leaf_instructions(self.body, BASE, True, buffer_proof=proof,
                                              call_resolver=proof.target, incoming_narrow_reads=True)

    def premises(self, rows, review="proved from the ROM: at most two qualifying results"):
        entry = {f"0x{BASE:08X}": {"review": review, "rows": [
            {"callee": f"0x{callee:08X}", "site": f"0x{site:08X}", "bound": bound} for callee, site, bound in rows]}}
        return json.dumps(entry).encode()

    def walk(self, premises=None, extra=""):
        self.build(extra)
        return store_bound.walk(self.make_proof, self.run_walk, self.body, BASE, None, premises)

    def trigger(self):
        return (f"buffer callee 0x{self.callee:08X}: bounded loop replay at 0x{self.site:08X}: 2-byte strh at "
                f"caller sp+4: buffer access is unaligned or outside allocated local words")

    # The plain walk ---------------------------------------------------------------------

    def test_the_plain_walk_refuses_the_third_store(self):
        self.build()
        with self.assertRaises(ValueError) as caught:
            self.run_walk(self.make_proof())
        self.assertEqual(str(caught.exception), self.trigger())
        self.assertEqual(store_bound.triggered(caught.exception), (self.callee, self.site))
        # The policy disabled: the trigger is raised unchanged.
        with patch.object(store_bound.POLICY, "enabled", False), self.assertRaises(ValueError) as caught:
            store_bound.walk(self.make_proof, self.run_walk, self.body, BASE, None,
                             self.premises([(self.callee, self.site, 2)]))
        self.assertEqual(str(caught.exception), self.trigger())

    # Admitted ---------------------------------------------------------------------------

    def test_a_reviewed_bound_admits_and_prunes_only_past_it(self):
        self.build()
        instructions, proof = self.walk(self.premises([(self.callee, self.site, 2)]))
        record = proof.store_bound_retry
        self.assertEqual(record["policy"], store_bound.NAME)
        self.assertEqual(record["trigger"], self.trigger())
        self.assertEqual(record["rows"], [{"callee": f"0x{self.callee:08X}", "site": f"0x{self.site:08X}",
                                           "bound": 2}])
        ((callee, site, call_site, pruned),) = record["pruned"]
        self.assertEqual((callee, site), (self.callee, self.site))
        self.assertTrue(BASE <= call_site < self.symbols["caller_end"])
        # A third store after two earlier ones, at passes 2, 3 and 4: one replayed state each (the replay
        # merges identical states, and r6, r7, r8 and the count agree on every path into each).
        self.assertEqual(pruned, 3)
        # The two permitted stores are the ordinary replayed writes, checked and recorded.
        ((_, _, _, _, _, writes),) = proof.loop_replays[self.callee]
        self.assertEqual(sorted(writes), [(0, 2), (2, 2)])
        lines = proof.loop_replay_lines()
        self.assertTrue(lines[0].startswith(f"* buffer loop replay: `bounded-loop-replay-v2` callee 0x{self.callee:08X}"))
        self.assertEqual(lines[1], f"* buffer store bound: `{store_bound.NAME}` after `{self.trigger()}`: "
                                   f"{store_bound.SUMMARY}")
        self.assertEqual(lines[2], f"* buffer store bound row: callee 0x{self.callee:08X} store 0x{self.site:08X} "
                                   f"executes at most 2 times per call (reached at 0x{call_site:08X}); {pruned} "
                                   f"replayed states past the bound end before the store and are not verified")
        self.assertTrue(lines[3].startswith(f"* buffer store bound premise: STORE premise: each bound above is the "
                                            f"reviewed entry 0x{BASE:08X} of {store_bound.PREMISES_PATH} "
                                            f"(canonical JSON SHA-256 `"))
        self.assertEqual(len(lines), 4)

    def test_a_smaller_proved_bound_is_accepted(self):
        self.build()
        _, proof = self.walk(self.premises([(self.callee, self.site, 1)]))
        ((_, _, _, pruned),) = proof.store_bound_retry["pruned"]
        self.assertEqual(pruned, 4)
        ((_, _, _, _, _, writes),) = proof.loop_replays[self.callee]
        self.assertEqual(sorted(writes), [(0, 2), (2, 2)])   # the producer's two zeroing stores

    def test_a_second_store_site_in_the_loop_stays_checked(self):
        # An unconditional in-frame store at a second site: never pruned, every execution checked.
        extra = "site2:\nstrh r4, [r5]"
        self.build(extra)
        _, proof = self.walk(self.premises([(self.callee, self.site, 2)]), extra=extra)
        self.assertEqual({(callee, site) for callee, site, _, _ in proof.store_bound_retry["pruned"]},
                         {(self.callee, self.site)})
        # A second site whose pointer advances on some passes leaves the frame at its third store whatever
        # the first site does: the first site's row does not cover it, and the entry that lacks a row for it
        # is refused with both rows printed.
        self.build(CONDITIONAL)
        site2 = self.symbols["site2"]
        with self.assertRaises(store_bound.StoreBoundRefusal) as caught:
            self.walk(self.premises([(self.callee, self.site, 2)]), extra=CONDITIONAL)
        self.assertIn("the entry lists other sites than the walk needs", str(caught.exception))
        self.assertEqual(caught.exception.entry[f"0x{BASE:08X}"]["rows"],
                         [{"callee": f"0x{self.callee:08X}", "site": f"0x{site:08X}", "bound": 2}
                          for site in sorted((self.site, site2))])
        # Bounding the second site above what the frame allows does not admit it.
        with self.assertRaisesRegex(store_bound.StoreBoundRefusal, r"\(a bound lets a store leave the allocated "):
            self.walk(self.premises(sorted([(self.callee, self.site, 2), (self.callee, site2, 3)])),
                      extra=CONDITIONAL)
        # A second site that advances on every pass leaves the frame on every path: no row can admit it, so
        # the plain refusal stands, with or without rows (test_rows_that_end_every_path_of_a_call_refuse).
        self.build(EVERY_PASS)
        site2 = self.symbols["site2"]
        for rows in ([(self.callee, self.site, 2)], [(self.callee, self.site, 2), (self.callee, site2, 2)]):
            with self.subTest(rows=len(rows)), self.assertRaises(ValueError) as caught:
                self.walk(self.premises(rows), extra=EVERY_PASS)
            self.assertNotIn("store-bound retry", str(caught.exception))
            self.assertIsNotNone(store_bound.triggered(caught.exception))

    # Refused entries ---------------------------------------------------------------------

    def test_a_missing_entry_refuses_and_prints_the_rows(self):
        with self.assertRaises(store_bound.StoreBoundRefusal) as caught:
            self.walk(None)
        message = str(caught.exception)
        self.assertTrue(message.startswith(self.trigger() + "; default store-bound retry: store bound: the replayed "
                                           f"stores of 0x{BASE:08X} need a reviewed entry in "
                                           f"{store_bound.PREMISES_PATH} that repeats these rows (none found)"))
        self.assertEqual(caught.exception.entry[f"0x{BASE:08X}"]["rows"],
                         [{"callee": f"0x{self.callee:08X}", "site": f"0x{self.site:08X}", "bound": 2}])
        self.assertIn(json.dumps(caught.exception.entry, indent=2), message)
        # Another owner's entry is not this owner's.
        other = json.dumps({"0x08000400": json.loads(self.premises([(self.callee, self.site, 2)]))[f"0x{BASE:08X}"]})
        with self.assertRaisesRegex(store_bound.StoreBoundRefusal, r"\(none found\)"):
            self.walk(other.encode())

    def test_a_differing_entry_refuses_and_prints_the_rows(self):
        self.build()
        cases = {
            "bound too large": ([(self.callee, self.site, 3)], "a bound lets a store leave the allocated local words"),
            "another site": ([(self.callee, self.callee + 1, 2)], "the entry lists other sites than the walk needs"),
            "another callee": ([(self.callee + 0x100, self.site, 2)], "the entry lists other sites than the walk needs"),
            "an extra row": ([(self.callee, self.site, 2), (self.callee, self.site + 1, 1)],
                             "the entry lists other sites than the walk needs"),
        }
        for name, (rows, reason) in cases.items():
            with self.subTest(case=name), self.assertRaises(store_bound.StoreBoundRefusal) as caught:
                self.walk(self.premises(rows))
            self.assertIn(f"({reason})", str(caught.exception))
            suggested = caught.exception.entry[f"0x{BASE:08X}"]["rows"]
            self.assertEqual(suggested, [{"callee": f"0x{self.callee:08X}", "site": f"0x{self.site:08X}",
                                          "bound": 2}])

    def test_a_row_site_that_is_not_a_store_refuses(self):
        self.build()
        not_a_store = self.site + 2                     # adds r6, #2
        with self.assertRaisesRegex(ValueError, rf"; default store-bound retry: buffer callee 0x{self.callee:08X}: "
                                                rf"bounded loop replay at 0x{not_a_store:08X}: store bound: the row site "
                                                rf"0x{not_a_store:08X} in 0x{self.callee:08X} is not a store"):
            self.walk(self.premises([(self.callee, self.site, 2), (self.callee, not_a_store, 1)]))

    def test_malformed_entries_refuse(self):
        self.build()
        good = json.loads(self.premises([(self.callee, self.site, 2)]))
        key = f"0x{BASE:08X}"
        cases = {
            "not JSON": b"{",
            "not an object": b"[]",
            "bad owner key": json.dumps({"8000000": good[key]}).encode(),
            "no review": json.dumps({key: {"rows": good[key]["rows"]}}).encode(),
            "empty review": json.dumps({key: dict(good[key], review=" ")}).encode(),
            "extra key": json.dumps({key: dict(good[key], proved=True)}).encode(),
            "no rows": json.dumps({key: dict(good[key], rows=[])}).encode(),
            "negative bound": json.dumps({key: dict(good[key], rows=[dict(good[key]["rows"][0], bound=-1)])}).encode(),
            "zero bound": json.dumps({key: dict(good[key], rows=[dict(good[key]["rows"][0], bound=0)])}).encode(),
            "text bound": json.dumps({key: dict(good[key], rows=[dict(good[key]["rows"][0], bound="2")])}).encode(),
            "lower-case site": json.dumps({key: dict(good[key], rows=[dict(good[key]["rows"][0],
                                                                           site=f"0x{self.site + 0x80:08x}")])}).encode(),
            "repeated row": json.dumps({key: dict(good[key], rows=good[key]["rows"] * 2)}).encode(),
            "unsorted rows": self.premises([(self.callee, self.site + 4, 1), (self.callee, self.site, 2)]),
        }
        for name, premises in cases.items():
            with self.subTest(case=name), self.assertRaisesRegex(ValueError, r"^store bound: "):
                store_bound.walk(self.make_proof, self.run_walk, self.body, BASE, None, premises)
        for name in ("negative bound", "zero bound", "text bound"):
            with self.subTest(case=name), self.assertRaisesRegex(
                    ValueError, rf"^store bound: a row of 0x{BASE:08X} is not \{{callee, site, bound >= 1\}}$"):
                store_bound.walk(self.make_proof, self.run_walk, self.body, BASE, None, cases[name])

    def test_repeated_keys_refuse(self):
        # JSON keeps the last of a repeated key silently, so a reader could see another entry, review or bound
        # than the walk would use: a repeat at any level refuses, whichever copy comes first.
        self.build()
        key = f"0x{BASE:08X}"
        one = json.loads(self.premises([(self.callee, self.site, 1)]))[key]
        two = json.loads(self.premises([(self.callee, self.site, 2)]))[key]
        row = json.dumps(two["rows"][0])
        cases = {
            "owner": '{"%s": %s, "%s": %s}' % (key, json.dumps(one), key, json.dumps(two)),
            "owner, other order": '{"%s": %s, "%s": %s}' % (key, json.dumps(two), key, json.dumps(one)),
            "another owner": '{"0x08000400": %s, "%s": %s, "0x08000400": %s}' % (
                json.dumps(one), key, json.dumps(two), json.dumps(two)),
            "review": '{"%s": {"review": "a", "review": %s, "rows": [%s]}}' % (key, json.dumps(two["review"]), row),
            "bound": '{"%s": {"review": %s, "rows": [%s]}}' % (key, json.dumps(two["review"]),
                                                               row.replace('"bound": 2', '"bound": 1, "bound": 2')),
        }
        for name, text in cases.items():
            with self.subTest(case=name):
                json.loads(text)                              # valid JSON: only the repeat is wrong
                with self.assertRaisesRegex(store_bound.DuplicateKey,
                                            rf"^store bound: {store_bound.PREMISES_PATH} repeats the key \""):
                    store_bound.walk(self.make_proof, self.run_walk, self.body, BASE, None, text.encode())
        # A report replay reading such a file refuses too.
        premises = self.premises([(self.callee, self.site, 2)])
        (self.root / store_bound.PREMISES_PATH).write_bytes(premises)
        _, proof = store_bound.walk(self.make_proof, self.run_walk, self.body, BASE, None, premises)
        self.assertTrue(self.accepted(self.report(proof)))
        (self.root / store_bound.PREMISES_PATH).write_text(cases["owner, other order"])
        self.assertFalse(self.accepted(self.report(proof)))

    def test_other_refusals_are_not_retried(self):
        # A callee store that leaves the frame outside any replay.
        caller = "push {r4, lr}\nsub sp, #4\nmov r0, sp\nbl query\nadd sp, #4\npop {r4}\npop {r1}\nbx r1"
        self.build(caller=caller, query="movs r1, #0\nstrh r1, [r0, #4]\nbx lr")
        with self.assertRaises(ValueError) as caught:
            store_bound.walk(self.make_proof, self.run_walk, self.body, BASE, None,
                             self.premises([(self.callee, self.site, 2)]))
        self.assertNotIn("store-bound retry", str(caught.exception))
        self.assertIsNone(store_bound.triggered(ValueError("bounded loop replay at 0x08000000: 2-byte strh at "
                                                           "caller sp+4: buffer access is unaligned or outside "
                                                           "allocated local words")))
        self.assertIsNone(store_bound.triggered(ValueError(self.trigger() + "; more")))

    # Evidence ----------------------------------------------------------------------------

    def report(self, proof, lines=None, fingerprint=None):
        from callee_saved_watch import premise_lines
        return [f"* compiled : `{self.body.hex()}`", f"* buffer calls: {evidence.STACK_BUFFER_SUMMARY}",
                f"* buffer proof SHA-256: `{fingerprint or proof.fingerprint()}`",
                *(proof.loop_replay_lines() + proof.bios_summary_lines() if lines is None else lines),
                *premise_lines(proof),
                f"**MATCH - byte identical** - {len(self.body)}/{len(self.body)} bytes"]

    def accepted(self, lines):
        return evidence.buffer_report_matches(lines, self.root, BASE, self.mapping, stack_arguments=True)

    def test_report_replay_binds_rows_entry_and_prunes(self):
        self.build()
        premises = self.premises([(self.callee, self.site, 2)])
        (self.root / store_bound.PREMISES_PATH).write_bytes(premises)
        _, proof = self.walk(premises)
        lines = proof.loop_replay_lines()
        self.assertTrue(self.accepted(self.report(proof)))
        replay, summary, row, premise = lines
        for name, edited in (("no row line", [replay, summary, premise]),
                             ("no premise line", [replay, summary, row]),
                             ("row edited", [replay, summary, row.replace("at most 2", "at most 3"), premise]),
                             ("row twice", [replay, summary, row, row, premise])):
            with self.subTest(edit=name):
                self.assertFalse(self.accepted(self.report(proof, lines=edited)))
        self.assertFalse(self.accepted(self.report(proof, fingerprint="0" * 64)))
        # The entry's review text is bound: an edited review changes the premise line and fingerprint.
        (self.root / store_bound.PREMISES_PATH).write_bytes(self.premises([(self.callee, self.site, 2)], review="other"))
        self.assertFalse(self.accepted(self.report(proof)))
        # Without the file the replay refuses (no entry), and with a smaller bound it differs.
        (self.root / store_bound.PREMISES_PATH).unlink()
        self.assertFalse(self.accepted(self.report(proof)))
        (self.root / store_bound.PREMISES_PATH).write_bytes(self.premises([(self.callee, self.site, 1)]))
        self.assertFalse(self.accepted(self.report(proof)))
        # Other owners' entries do not change the binding.
        table = json.loads(premises)
        table["0x08000400"] = table[f"0x{BASE:08X}"]
        (self.root / store_bound.PREMISES_PATH).write_text(json.dumps(table))
        self.assertTrue(self.accepted(self.report(proof)))

    def test_walks_without_the_retry_are_unchanged(self):
        # A loop whose stores stay in the frame: no trigger, no retry, no record, the same fingerprint.
        caller = CALLER.replace("sub sp, #4", "sub sp, #12").replace("add sp, #4", "add sp, #12")
        self.build(caller=caller)
        plain = self.make_proof()
        self.run_walk(plain)
        _, proof = store_bound.walk(self.make_proof, self.run_walk, self.body, BASE, None,
                                    self.premises([(self.callee, self.site, 2)]))
        self.assertIsNone(proof.store_bound_retry)
        self.assertIsNone(proof.store_bounds)
        self.assertEqual(proof.fingerprint(), plain.fingerprint())
        self.assertEqual(proof.loop_replay_lines(), plain.loop_replay_lines())

    def test_the_count_is_per_call(self):
        # Two calls of the same callee: each may store twice.
        caller = ("push {r4, lr}\nsub sp, #8\nadds r4, r0, #0\nmov r1, sp\nadds r0, r4, #0\nbl callee\n"
                  "add r1, sp, #4\nadds r0, r4, #0\nbl callee\nadd sp, #8\npop {r4}\npop {r1}\nbx r1")
        self.build(caller=caller)
        _, proof = store_bound.walk(self.make_proof, self.run_walk, self.body, BASE, None,
                                    self.premises([(self.callee, self.site, 2)]))
        calls = sorted(call for _, _, call, _ in proof.store_bound_retry["pruned"])
        self.assertEqual(len(calls), 2)
        ((_, _, _, _, _, first), (_, _, _, _, _, second)) = sorted(proof.loop_replays[self.callee])
        self.assertEqual(sorted(set(first) | set(second)), [(0, 2), (2, 2), (4, 2), (6, 2)])

    def test_the_fingerprint_binds_the_record(self):
        self.build()
        _, proof = self.walk(self.premises([(self.callee, self.site, 2)]))
        fingerprint = proof.fingerprint()
        record = proof.store_bound_retry
        for change in ("pruned", "rows", "entry_sha256"):
            with self.subTest(change=change):
                proof.store_bound_retry = dict(record, **{change: "edited"})
                self.assertNotEqual(proof.fingerprint(), fingerprint)
        proof.store_bound_retry = None
        self.assertNotEqual(proof.fingerprint(), fingerprint)
        proof.store_bound_retry = record
        self.assertEqual(proof.fingerprint(), fingerprint)

    def test_two_rows_whose_second_store_runs_every_pass_refuse(self):
        # The first site stores on a qualifying pass, the second on every one of the five passes: the frame
        # allows two of each, and any such bound ends every path at pass 2, so no path of the call would be
        # verified to its return.  The measure pass sees that, and the plain refusal stands.
        self.build(EVERY_PASS)
        site2 = self.symbols["site2"]
        with self.assertRaises(ValueError) as caught:
            self.walk(self.premises(sorted([(self.callee, self.site, 2), (self.callee, site2, 2)])),
                      extra=EVERY_PASS)
        self.assertNotIsInstance(caught.exception, store_bound.StoreBoundRefusal)
        self.assertEqual(store_bound.triggered(caught.exception)[0], self.callee)
        self.assertNotIn("store-bound retry", str(caught.exception))
        self.assertRegex(str(caught.exception.__cause__), rf"store bound: no replayed path of 0x{self.callee:08X} "
                                                          rf"\(called at 0x0800000[0-9A-F]\) returns")

    def test_two_rows_count_each_site_on_its_own(self):
        # The first site stores on a nonzero result, the second on a result of 1: two qualifying tests the
        # replay cannot decide, so both sites store on some passes and not on others, and some paths return.
        conditional = CONDITIONAL
        self.build(conditional)
        site2 = self.symbols["site2"]
        _, proof = self.walk(self.premises(sorted([(self.callee, self.site, 2), (self.callee, site2, 2)])),
                             extra=conditional)
        pruned = {site: count for _, site, _, count in proof.store_bound_retry["pruned"]}
        # The first site is cut at its third store, at passes 2, 3 and 4, after zero, one or two second-site
        # stores: nine replayed states.  The second site is cut at its third store at the same passes, after
        # zero, one or two first-site stores; whether the first site stored on this pass leaves r0 = 1 or the
        # unknown result, and it did only if its count is at least one, so five states a pass: fifteen.  A
        # count shared by the two sites would cut both earlier.
        self.assertEqual(pruned, {self.site: 9, site2: 15})

    def test_the_line_kinds_are_buffer_proof_lines_and_data_buffer_fields(self):
        import data_buffer_profile as data_buffer
        record = {"policy": store_bound.NAME, "address": BASE, "trigger": "t", "entry_sha256": "0" * 64,
                  "rows": [{"callee": "0x08000100", "site": "0x08000110", "bound": 2}],
                  "pruned": [[0x08000100, 0x08000110, 0x08000004, 3]]}
        lines = store_bound.lines(record)
        self.assertEqual(len(lines), 3)
        for line in lines:
            with self.subTest(line=line):
                self.assertTrue(line.startswith(evidence.BUFFER_LINES))
                self.assertIn(line.split(":", 1)[0], data_buffer.FIELDS)
        self.assertEqual(store_bound.lines(None), [])

    # Rows that would state reachability, not a count ---------------------------------------

    def test_a_store_outside_the_frame_at_its_first_execution_refuses(self):
        # An unconditional store eight bytes past the cursor leaves the u16[2] at its first execution: the
        # largest bound the frame allows would be 0, which says the store never runs.  The plain refusal
        # stands, with no entry printed, and an entry with a bound of 0 is malformed.
        extra = "site2:\nstrh r4, [r6, #8]"
        self.build(extra)
        site2 = self.symbols["site2"]
        with self.assertRaises(ValueError) as caught:
            self.walk(None, extra=extra)
        self.assertNotIsInstance(caught.exception, store_bound.StoreBoundRefusal)
        self.assertEqual(store_bound.triggered(caught.exception), (self.callee, site2))
        self.assertNotIn("store-bound retry", str(caught.exception))
        with self.assertRaisesRegex(ValueError, r"^store bound: a row of 0x08000000 is not \{callee, site, bound >= 1\}$"):
            self.walk(self.premises([(self.callee, site2, 0)]), extra=extra)
        with self.assertRaisesRegex(ValueError, "measures every row or bounds every row"):
            store_bound.StoreBounds(BASE, {(self.callee, site2): 0})

    def test_a_conditional_store_outside_the_frame_at_its_first_execution_refuses(self):
        # From the independent review: the store leaves the u16[2] at its first execution, but only on a result
        # of 1, so paths that skip it return and neither per-call check fires.  The frame bound of 0 alone keeps
        # the plain refusal, with or without an entry, and prints none.
        extra = "cmp r4, #1\nbne skip2\nsite2:\nstrh r4, [r6, #8]\nskip2:"
        self.build(extra)
        site2 = self.symbols["site2"]
        for premises in (None, self.premises([(self.callee, self.site, 2)])):
            with self.subTest(entry=premises is not None), self.assertRaises(ValueError) as caught:
                self.walk(premises, extra=extra)
            self.assertNotIsInstance(caught.exception, store_bound.StoreBoundRefusal)
            self.assertNotIn("store-bound retry", str(caught.exception))
            self.assertEqual(store_bound.triggered(caught.exception), (self.callee, site2))

    def test_rows_that_end_every_path_of_a_call_refuse(self):
        # The frame allows two stores at each site; the second site runs on all five passes, so every row
        # the frame allows ends every replayed path of the call: the premise is false by the code alone.  The
        # measure pass finds no path that returns, and the plain refusal stands, with no entry printed.
        self.build(EVERY_PASS)
        site2 = self.symbols["site2"]
        for premises in (None, self.premises([(self.callee, self.site, 2), (self.callee, site2, 2)])):
            with self.subTest(entry=premises is not None), self.assertRaises(ValueError) as caught:
                self.walk(premises, extra=EVERY_PASS)
            self.assertNotIsInstance(caught.exception, store_bound.StoreBoundRefusal)
            self.assertNotIn("store-bound retry", str(caught.exception))
            self.assertRegex(str(caught.exception.__cause__), rf"store bound: no replayed path of 0x{self.callee:08X} "
                                                              rf"\(called at 0x0800000[0-9A-F]\) returns and \d+ end at a "
                                                              rf"bound: the walk would verify the premise, not the call")
        # The frame allows two at the second site; a path may return after two, so 2 is admitted.  A bound of
        # 1 ends every path at pass 1, before the return: the reviewed entry is refused.
        self.build(TWICE, loop=DONE)
        site2 = self.symbols["site2"]
        rows = [(self.callee, self.site, 2), (self.callee, site2, 2)]
        _, proof = store_bound.walk(self.make_proof, self.run_walk, self.body, BASE, None, self.premises(rows))
        self.assertEqual({site for _, site, _, _ in proof.store_bound_retry["pruned"]}, {self.site, site2})
        with self.assertRaises(ValueError) as caught:
            store_bound.walk(self.make_proof, self.run_walk, self.body, BASE, None,
                             self.premises([(self.callee, self.site, 2), (self.callee, site2, 1)]))
        self.assertRegex(str(caught.exception),
                         rf"; default store-bound retry: buffer callee 0x{self.callee:08X}: bounded loop replay: "
                         rf"store bound: no replayed path of 0x{self.callee:08X} \(called at 0x0800000[0-9A-F]\) "
                         rf"returns and \d+ end at a bound: the walk would verify the premise, not the call$")

    def test_a_row_that_a_smaller_bound_makes_unreachable_refuses(self):
        # The second store runs only once the first has run twice, and only on a result of 1, so some paths
        # store it and return.  The frame allows each two; with both at 2 both rows prune.  A smaller proved
        # bound of 1 for the first store means the second never runs: its row prunes no path, and an entry
        # that states a premise the walk never uses is refused (without the row, the entry names other
        # sites than the walk needs).
        gated = "mov r0, r8\ncmp r0, #2\nblt skip2\ncmp r4, #1\nbne skip2\nsite2:\nstrh r4, [r5]\nadds r5, #2\nskip2:"
        self.build(gated)
        site2 = self.symbols["site2"]
        _, proof = store_bound.walk(self.make_proof, self.run_walk, self.body, BASE, None,
                                    self.premises([(self.callee, self.site, 2), (self.callee, site2, 2)]))
        self.assertEqual({site for _, site, _, _ in proof.store_bound_retry["pruned"]}, {self.site, site2})
        with self.assertRaises(ValueError) as caught:
            store_bound.walk(self.make_proof, self.run_walk, self.body, BASE, None,
                             self.premises([(self.callee, self.site, 1), (self.callee, site2, 2)]))
        self.assertRegex(str(caught.exception), rf"; default store-bound retry: store bound: the row 0x{site2:08X} in "
                                                rf"0x{self.callee:08X} prunes no path$")
        with self.assertRaises(store_bound.StoreBoundRefusal):
            store_bound.walk(self.make_proof, self.run_walk, self.body, BASE, None,
                             self.premises([(self.callee, self.site, 1)]))

    def test_a_forced_overrun_after_an_early_return_refuses(self):
        # The call may return at once on an unknown result, so some path returns; but once the second site
        # stores it stores on all five passes, through branches the replay follows both ways (the first
        # site's test), and its frame allows four.  The row would state that the loop never runs.
        # The measure pass sees it: the plain refusal stands, with or without the row the frame would allow.
        self.build("site2:\nstrh r4, [r5, #4]\nadds r5, #2", caller=CALLER12, loop=EARLY)
        site2 = self.symbols["site2"]
        for premises in (None, self.premises([(self.callee, site2, 4)]), self.premises([(self.callee, site2, 1)])):
            with self.subTest(entry=premises), self.assertRaises(ValueError) as caught:
                store_bound.walk(self.make_proof, self.run_walk, self.body, BASE, None, premises)
            self.assertNotIsInstance(caught.exception, store_bound.StoreBoundRefusal)
            self.assertEqual(store_bound.triggered(caught.exception), (self.callee, site2))
            self.assertRegex(str(caught.exception.__cause__),
                             rf"store bound: in 0x{self.callee:08X} \(called at 0x0800000[0-9A-F]\), once the store "
                             rf"at 0x{site2:08X} first runs no replayed continuation returns and some end at its bound: "
                             rf"the code itself runs the store more often than its row allows$")
        # Behind the early return, a second site that may return after its second store: the frame allows 2,
        # and 2 is admitted (a first store of the first site at pass 2 leads only to the second site's cut,
        # which is the second row's count).  A reviewed bound of 1 ends every continuation of the second
        # site's first store at its own bound at pass 1, while the early return still returns: the entry is
        # refused, naming that store only.
        self.build(TWICE, loop=EARLY)
        site2 = self.symbols["site2"]
        store_bound.walk(self.make_proof, self.run_walk, self.body, BASE, None,
                         self.premises([(self.callee, self.site, 2), (self.callee, site2, 2)]))
        with self.assertRaises(ValueError) as caught:
            store_bound.walk(self.make_proof, self.run_walk, self.body, BASE, None,
                             self.premises([(self.callee, self.site, 2), (self.callee, site2, 1)]))
        self.assertRegex(str(caught.exception),
                         rf"; default store-bound retry: buffer callee 0x{self.callee:08X}: bounded loop replay: "
                         rf"store bound: in 0x{self.callee:08X} \(called at 0x0800000[0-9A-F]\), once the store at "
                         rf"0x{site2:08X} first runs no replayed continuation returns and some end at its bound: "
                         rf"the code itself runs the store more often than its row allows$")

    def test_counts_do_not_merge_at_a_join(self):
        # From the independent review: the skipping path's third store reaches the saved register after two
        # earlier stores, the storing path's after three, so the frame allows 2.  A replay that merged the two
        # pass-0 paths on the higher count would measure 3 (or keep the larger count at a refusing store) and
        # never walk the lower-count continuation, admitting 3 with an unchecked store.  The stored value must
        # leave the frame-word facts equal on both arms (a known zero over the prologue's zero) for the two
        # states to be otherwise identical, so each order runs with and without that zero.
        zero = "movs r4, #0\nsite:\nstrh r4, [r6]"
        for name, loop in (("storing arm falls through", COUNT_MERGE), ("storing arm is the target", COUNT_MERGE_SWAPPED),
                           ("falls through, zero stored", COUNT_MERGE.replace("site:\nstrh r4, [r6]", zero)),
                           ("target, zero stored", COUNT_MERGE_SWAPPED.replace("site:\nstrh r4, [r6]", zero))):
            with self.subTest(order=name):
                self.build(loop=loop)
                with self.assertRaises(store_bound.StoreBoundRefusal) as caught:
                    store_bound.walk(self.make_proof, self.run_walk, self.body, BASE, None,
                                     self.premises([(self.callee, self.site, 3)]))
                self.assertIn("(a bound lets a store leave the allocated local words)", str(caught.exception))
                self.assertEqual(caught.exception.entry[f"0x{BASE:08X}"]["rows"][0]["bound"], 2)
                _, proof = store_bound.walk(self.make_proof, self.run_walk, self.body, BASE, None,
                                            self.premises([(self.callee, self.site, 2)]))
                self.assertEqual(proof.store_bound_retry["rows"][0]["bound"], 2)
                ((_, _, _, _, _, writes),) = proof.loop_replays[self.callee]
                self.assertEqual(sorted(writes), [(0, 2), (2, 2)])

    def test_a_forced_overrun_reached_through_a_merged_state_refuses(self):
        # From the independent review: arm B's first store leads only to the state arm A's continuation also
        # reaches, and from there every pass stores, past the two the frame allows; arm A may return.  Arm
        # B's overrun is reached through a state the replay may already have seen, so the graph must keep
        # edges into seen states.  Both exploration orders; the plain refusal stands, with or without a row.
        for name, loop in (("arm A first", MERGED_A), ("arm B first", MERGED_B)):
            self.build(loop=loop)
            for premises in (None, self.premises([(self.callee, self.site, 2)])):
                with self.subTest(order=name, entry=premises is not None), self.assertRaises(ValueError) as caught:
                    store_bound.walk(self.make_proof, self.run_walk, self.body, BASE, None, premises)
                self.assertNotIsInstance(caught.exception, store_bound.StoreBoundRefusal)
                self.assertEqual(store_bound.triggered(caught.exception), (self.callee, self.site))
                self.assertRegex(str(caught.exception.__cause__),
                                 rf"once the store at 0x{self.site:08X} first runs no replayed continuation returns")

    def test_a_bound_reached_only_after_a_later_execution_is_a_count(self):
        # The second site stores on every pass, and after its first store the call may return on an unknown
        # result; past that it stores on all five passes.  The code allows one execution or five, so a bound
        # of 4 (or 1) is a count the code allows, not a reachability premise, and is admitted; the paths it
        # ends start at the second execution.
        late = "site2:\nstrh r4, [r5, #4]\nadds r5, #2\ncmp r7, #0\nbne stay\nmov r0, sb\nbl query\ncmp r0, #0\n" \
               "beq done\nstay:"
        self.build(late, caller=CALLER12, loop=LOOP.replace("ble loop\nmov r0, r8", "ble loop\ndone:\nmov r0, r8"))
        site2 = self.symbols["site2"]
        for bound in (4, 1):
            with self.subTest(bound=bound):
                _, proof = store_bound.walk(self.make_proof, self.run_walk, self.body, BASE, None,
                                            self.premises([(self.callee, site2, bound)]))
                ((callee, site, _, pruned),) = proof.store_bound_retry["pruned"]
                self.assertEqual((callee, site), (self.callee, site2))
                self.assertGreater(pruned, 0)

    def test_a_first_execution_that_only_loops_forever_is_not_an_overrun(self):
        # A store at pass 0 is followed by a loop that has an exit but, with r7 = 0 known, never takes it
        # (the replay ends it where its state repeats): no continuation of that first execution returns, but
        # none ends at a bound either, so the row states nothing about it.  A first store on a later pass may
        # return or reach the bound.
        hang = LOOP.replace("add r8, r0\nskip:",
                            "add r8, r0\ncmp r7, #0\nbne go\nspin:\ncmp r7, #0\nbeq spin\ngo:\nskip:")
        self.build(loop=hang)
        _, proof = store_bound.walk(self.make_proof, self.run_walk, self.body, BASE, None,
                                    self.premises([(self.callee, self.site, 2)]))
        ((_, site, _, pruned),) = proof.store_bound_retry["pruned"]
        self.assertEqual(site, self.site)
        self.assertGreater(pruned, 0)

    def test_aborted_records_are_restored(self):
        self.build()
        proof = self.make_proof()
        proof.store_bounds = store_bound.StoreBounds(BASE, {(self.callee, self.site): 2})
        saved = proof._snapshot_ledgers()
        proof.store_bounds.pruned[(self.callee, self.site, BASE)] = 5
        proof._restore_ledgers(saved)
        self.assertEqual(proof.store_bounds.pruned, {})
        with self.assertRaisesRegex(ValueError, "measures every row or bounds every row"):
            store_bound.StoreBounds(BASE, {(self.callee, self.site): 2, (self.callee, self.site + 4): None})



# ---- native: match.py issues the reports, and replay checks them --------------------------------
NATIVE_LOOP = LOOP.format(extra="").replace("bl query", "bl func_08000500")
PLAIN_C = """typedef unsigned short u16;
extern int func_08000400(void *unit, u16 *out);
u16 func_08000200(void *unit)
{
    u16 entries[2];

    func_08000400(unit, entries);
    return entries[0] + entries[1];
}
"""
DATA_C = """typedef unsigned short u16;
extern u16 data_02000000[];
extern int func_08000400(void *unit, u16 *out);
void func_08000200(void *unit)
{
    u16 entries[2];

    func_08000400(unit, entries);
    data_02000000[0] = entries[0];
    data_02000000[1] = entries[1];
}
"""


def native_tools():
    return Path(os.path.expandvars(match.DEFAULT_CC)).is_file() and \
        all(shutil.which(tool) for tool in (match.DEFAULT_AS, match.DEFAULT_LD, match.DEFAULT_OBJCOPY))


@unittest.skipUnless(native_tools(), "fixed compiler and ARM tools required")
class StoreBoundNativeTests(unittest.TestCase):
    def setUp(self):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="store_bound_native_", dir=scratch)
        self.addCleanup(directory.cleanup)
        self.base = Path(directory.name)

    def tree(self, name, source):
        import test_data_buffer_calls as fixtures
        root = fixtures.build(self.base / name, source, [("func_08000400", NATIVE_LOOP),
                                                         ("func_08000500", QUERY)])
        rom = (root / "baserom.bin").read_bytes()
        loop = rom[fixtures.CALLEES - BASE:fixtures.CALLEES - BASE + 0x100]
        # The site is the loop's `strh r4, [r6]` (0x8034).
        (site,) = [offset for offset in range(0, len(loop) - 1, 2) if loop[offset:offset + 2] == bytes.fromhex("3480")]
        return root, fixtures, fixtures.CALLEES + site

    def entry(self, root, address, site, bound):
        (root / store_bound.PREMISES_PATH).write_text(json.dumps({f"0x{address:08X}": {
            "review": "fixture: at most two qualifying results",
            "rows": [{"callee": "0x08000400", "site": f"0x{site:08X}", "bound": bound}]}}))

    def issue(self, name, source, schema):
        root, fixtures, site = self.tree(name, source)
        code, output, report = fixtures.run(root)
        self.assertNotEqual(code, 0, output)
        self.assertIn("; default store-bound retry: store bound: the replayed stores of 0x08000200 need a reviewed "
                      f"entry in {store_bound.PREMISES_PATH} that repeats these rows (none found)", output)
        self.assertIn(f'"site": "0x{site:08X}",\n        "bound": 2', output)
        self.entry(root, fixtures.A, site, 2)
        code, output, report = fixtures.run(root)
        self.assertEqual(code, 0, output)
        self.assertEqual(fixtures.verification(report), schema)
        rows = [line for line in report.splitlines() if line.startswith("* buffer store bound row: ")]
        self.assertEqual(len(rows), 1)
        self.assertIn(f"store 0x{site:08X} executes at most 2 times per call", rows[0])
        with patch.dict(os.environ, FFTA_ROM=str(root / "baserom.bin")):
            self.assertTrue(evidence.report_matches(report, root, fixtures.A))
            self.entry(root, fixtures.A, site, 1)
            self.assertFalse(evidence.report_matches(report, root, fixtures.A))
            with patch.object(store_bound.POLICY, "enabled", False):
                self.entry(root, fixtures.A, site, 2)
                self.assertFalse(evidence.report_matches(report, root, fixtures.A))
            self.assertTrue(evidence.report_matches(report, root, fixtures.A))

    def test_the_plain_path_issues_and_replays(self):
        self.issue("plain", PLAIN_C, evidence.STACK_BUFFER_SCHEMA)

    # Rows that would state reachability, refused by match.py itself (it issues reports as __main__).

    def variant(self, name, loop, *stores):
        """The plain owner over ``loop``: (root, fixtures, address of each store encoding in ``stores``)."""
        import test_data_buffer_calls as fixtures
        root = fixtures.build(self.base / name, PLAIN_C, [("func_08000400", loop.replace("bl query", "bl func_08000500")),
                                                           ("func_08000500", QUERY)])
        rom = (root / "baserom.bin").read_bytes()
        code = rom[fixtures.CALLEES - BASE:fixtures.CALLEES - BASE + 0x100]
        sites = []
        for store in stores:
            (offset,) = [offset for offset in range(0, len(code) - 1, 2) if code[offset:offset + 2] == bytes.fromhex(store)]
            sites.append(fixtures.CALLEES + offset)
        return root, fixtures, sites

    def rows(self, root, owner, rows):
        (root / store_bound.PREMISES_PATH).write_text(json.dumps({f"0x{owner:08X}": {
            "review": "fixture", "rows": [{"callee": "0x08000400", "site": f"0x{site:08X}", "bound": bound}
                                          for site, bound in rows]}}))

    def plain_refusal(self, output, site):
        """The plain walk's refusal at ``site``, unchanged: no retry and no entry printed."""
        self.assertIn(f"bounded loop replay at 0x{site:08X}: 2-byte strh at caller sp+", output)
        self.assertNotIn("store-bound retry", output)
        self.assertNotIn('"bound"', output)

    def test_a_store_outside_the_frame_at_its_first_execution_refuses_end_to_end(self):
        # strh r4, [r6, #8] (0x8134) on every pass, outside the u16[2] at once.
        root, fixtures, (site,) = self.variant("zero", LOOP.format(extra="strh r4, [r6, #8]"), "3481")
        code, output, report = fixtures.run(root)
        self.assertNotEqual(code, 0, output)
        self.assertIsNone(report)
        self.plain_refusal(output, site)
        self.rows(root, fixtures.A, [(site, 0)])
        code, output, report = fixtures.run(root)
        self.assertNotEqual(code, 0, output)
        self.assertIsNone(report)
        self.assertIn(f"store bound: a row of 0x{fixtures.A:08X} is not {{callee, site, bound >= 1}}", output)

    def test_rows_that_end_every_path_of_a_call_refuse_end_to_end(self):
        # strh r4, [r5] (0x802C) on every one of the five passes; its frame allows two, so any row ends every
        # path: the plain refusal stands, with or without the rows.
        root, fixtures, (site, site2) = self.variant("every", LOOP.format(extra=EVERY_PASS), "3480", "2c80")
        for rows in (None, [(site, 2), (site2, 2)]):
            if rows:
                self.rows(root, fixtures.A, rows)
            code, output, report = fixtures.run(root)
            self.assertNotEqual(code, 0, output)
            self.assertIsNone(report)
            self.assertNotIn("store-bound retry", output)
        # The same store, but the call may return after its second execution: a bound of 2 is issued and
        # replays; a bound of 1 ends every path before that return and is refused.
        root, fixtures, (site, site2) = self.variant("twice", DONE.format(extra=TWICE), "3480", "2c80")
        self.rows(root, fixtures.A, [(site, 2), (site2, 2)])
        code, output, report = fixtures.run(root)
        self.assertEqual(code, 0, output)
        with patch.dict(os.environ, FFTA_ROM=str(root / "baserom.bin")):
            self.assertTrue(evidence.report_matches(report, root, fixtures.A))
            self.rows(root, fixtures.A, [(site, 2), (site2, 1)])
            self.assertFalse(evidence.report_matches(report, root, fixtures.A))
        code, output, report = fixtures.run(root)
        self.assertNotEqual(code, 0, output)
        self.assertIsNone(report)
        self.assertRegex(output, r"store bound: no replayed path of 0x08000400 \(called at 0x080002[0-9A-F]{2}\) "
                                 r"returns and \d+ end at a bound: the walk would verify the premise, not the call")

    def test_a_forced_overrun_after_an_early_return_refuses_end_to_end(self):
        root, fixtures, (site, site2) = self.variant("forced", EARLY.format(extra=EVERY_PASS), "3480", "2c80")
        self.rows(root, fixtures.A, [(site, 2), (site2, 2)])
        code, output, report = fixtures.run(root)
        self.assertNotEqual(code, 0, output)
        self.assertIsNone(report)
        self.assertNotIn("store-bound retry", output)
        root, fixtures, (site, site2) = self.variant("forced1", EARLY.format(extra=TWICE), "3480", "2c80")
        self.rows(root, fixtures.A, [(site, 2), (site2, 1)])
        code, output, report = fixtures.run(root)
        self.assertNotEqual(code, 0, output)
        self.assertIsNone(report)
        self.assertIn(f"once the store at 0x{site2:08X} first runs no replayed continuation returns and some end "
                      f"at its bound: the code itself runs the store more often than its row allows", output)

    def test_the_composed_data_buffer_proof_issues_and_replays(self):
        import data_buffer_profile as data_buffer
        self.issue("data", DATA_C, data_buffer.SCHEMA)


if __name__ == "__main__":
    unittest.main()
