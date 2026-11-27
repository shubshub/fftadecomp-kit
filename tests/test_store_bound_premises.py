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

    def build(self, extra="", caller=CALLER, query=QUERY):
        text = (".syntax unified\n.arch armv4t\n.thumb\n.text\n"
                ".global caller, caller_end, callee, callee_end, query, query_end, site, site2\n"
                f"caller:\n{caller}\n.align 2\n.ltorg\ncaller_end:\n.org 0x100\ncallee:\n"
                f"{LOOP.format(extra=extra)}\n.align 2\n.ltorg\ncallee_end:\n.org 0x200\nquery:\n{query}\nquery_end:\n")
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
        # A second site whose pointer advances on every pass leaves the frame at its third store whatever
        # the first site does: the first site's row does not cover it, the entry that lacks a row for it is
        # refused with both rows printed, and with both rows each site is pruned at its own bound.
        advancing = "site2:\nstrh r4, [r5]\nadds r5, #2"
        self.build(advancing)
        site2 = self.symbols["site2"]
        with self.assertRaises(store_bound.StoreBoundRefusal) as caught:
            self.walk(self.premises([(self.callee, self.site, 2)]), extra=advancing)
        self.assertIn("the entry lists other sites than the walk needs", str(caught.exception))
        self.assertEqual(caught.exception.entry[f"0x{BASE:08X}"]["rows"],
                         [{"callee": f"0x{self.callee:08X}", "site": f"0x{site:08X}", "bound": 2}
                          for site in sorted((self.site, site2))])
        _, proof = self.walk(self.premises(sorted([(self.callee, self.site, 2), (self.callee, site2, 2)])),
                             extra=advancing)
        self.assertEqual({(callee, site) for callee, site, _, _ in proof.store_bound_retry["pruned"]},
                         {(self.callee, self.site), (self.callee, site2)})
        # Bounding the first site alone below what the second needs does not admit the second.
        with self.assertRaises(store_bound.StoreBoundRefusal):
            self.walk(self.premises(sorted([(self.callee, self.site, 2), (self.callee, site2, 3)])),
                      extra=advancing)

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
            "text bound": json.dumps({key: dict(good[key], rows=[dict(good[key]["rows"][0], bound="2")])}).encode(),
            "lower-case site": json.dumps({key: dict(good[key], rows=[dict(good[key]["rows"][0],
                                                                           site=f"0x{self.site + 0x80:08x}")])}).encode(),
            "repeated row": json.dumps({key: dict(good[key], rows=good[key]["rows"] * 2)}).encode(),
            "unsorted rows": self.premises([(self.callee, self.site + 4, 1), (self.callee, self.site, 2)]),
        }
        for name, premises in cases.items():
            with self.subTest(case=name), self.assertRaisesRegex(ValueError, r"^store bound: "):
                store_bound.walk(self.make_proof, self.run_walk, self.body, BASE, None, premises)

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

    def test_two_rows_count_each_site_on_its_own(self):
        # The first site stores on a qualifying pass, the second on every pass: each is cut at its own count.
        advancing = "site2:\nstrh r4, [r5]\nadds r5, #2"
        self.build(advancing)
        site2 = self.symbols["site2"]
        _, proof = self.walk(self.premises(sorted([(self.callee, self.site, 2), (self.callee, site2, 2)])),
                             extra=advancing)
        pruned = {site: count for _, site, _, count in proof.store_bound_retry["pruned"]}
        # The first site is cut once: its third store, at pass 2 after stores at passes 0 and 1. The second
        # site is cut at pass 2 on every other path, after zero, one or two first-site stores, on the
        # skipping and on the storing branch (whose flags differ): five replayed states. A count shared by
        # the two sites would cut both earlier.
        self.assertEqual(pruned, {self.site: 1, site2: 5})

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

    def test_the_composed_data_buffer_proof_issues_and_replays(self):
        import data_buffer_profile as data_buffer
        self.issue("data", DATA_C, data_buffer.SCHEMA)


if __name__ == "__main__":
    unittest.main()
