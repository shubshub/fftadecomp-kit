"""A call target stored into a freshly allocated block and reloaded, under a reviewed entry (fresh_block_profile).

The fixture is the 0x08005954 shape, assembled and linked at 0x08000000: the owner hands a callee
its frame pointer and a function literal; the callee allocates a block, stores the callback into its
word 0, writes another object, reloads word 0 and calls it through `_call_via_r3` with the owner's
frame pointer.  No game ROM is needed.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import match
import fresh_block_profile as fresh
import call_via_target_profile as call_via

BASE = match.ROM_BASE
R3 = match.RUNTIME_HELPERS["_call_via_r3"]
REVIEW = "Reviewed: the list object is a live task, never the block just taken from the free list."

OWNER = ("push {lr}\nsub sp, #8\nmov r3, sp\nldr r1, =callback + 1\nbl creator\nadd sp, #8\npop {r0}\nbx r0\n"
         ".ltorg")
# The creator: the callback (r1) kept in r4, the owner's frame pointer (r3) in r5, a block from the
# allocator in r7, the callback stored into word 0 and reloaded for the call.
CREATOR = """push {{r4, r5, r7, lr}}
    adds r4, r1, #0
    adds r5, r3, #0
    ldr r0, =0x02000000
    movs r1, #16
alloc_call:
    bl allocator
    adds r7, r0, #0
store:
    str r4, [r7]
    {between}
reload:
    ldr r3, [r7]
    adds r0, r5, #0
    bl 0x{thunk:08X}
    pop {{r4, r5, r7}}
    pop {{r0}}
    bx r0
    .ltorg"""
BETWEEN = "ldr r0, =0x02001000\nother:\nstr r7, [r0, #8]"
# The 0x08005954 shape proper: the creator passes its OWN frame to the callback, so the call is checked
# in the creator's core walk, which starts from the owner's call-target facts (call_via_target_profile).
OWN_FRAME = CREATOR.replace("push {{r4, r5, r7, lr}}\n", "push {{r4, r5, r7, lr}}\n    sub sp, #8\n").replace(
    "    adds r0, r5, #0\n", "    mov r0, sp\n").replace("    pop {{r4, r5, r7}}\n", "    add sp, #8\n    pop {{r4, r5, r7}}\n")


@unittest.skipUnless(all(subprocess.run(["which", tool], capture_output=True).returncode == 0
                         for tool in ("arm-none-eabi-as", "arm-none-eabi-ld", "arm-none-eabi-objcopy")),
                     "ARM binutils required")
class FreshBlockTests(unittest.TestCase):
    def setUp(self):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="fresh_block_", dir=scratch)
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)

    def build(self, between=BETWEEN, callback="movs r1, #1\nstrh r1, [r0]\nbx lr", creator=None):
        creator = (creator or CREATOR).format(between=between, thunk=R3)
        functions = dict(owner=OWNER, creator=creator,
                         allocator="ldr r0, =0x02000100\nbx lr\n.ltorg", callback=callback)
        labels = [label for name in functions for label in (name, name + "_end")]
        labels += ["alloc_call", "store", "reload", "other"]
        text = ".syntax unified\n.arch armv4t\n.thumb\n.text\n.global " + ", ".join(labels) + "\n"
        for index, (name, body) in enumerate(functions.items()):
            text += f".org 0x{0x100 * index:x}\n{name}:\n{body}\n{name}_end:\n"
        if "other:" not in between:
            text += "other:\n"
        text += f".org 0x{R3 - BASE:x}\nbx r3\nnop\n"
        (self.root / "f.s").write_text(text)
        for command in (
                ["arm-none-eabi-as", "-mthumb-interwork", str(self.root / "f.s"), "-o", str(self.root / "f.o")],
                ["arm-none-eabi-ld", "-Ttext=0x08000000", "-e", "owner", str(self.root / "f.o"),
                 "-o", str(self.root / "f.elf")],
                ["arm-none-eabi-objcopy", "-O", "binary", "--only-section=.text", str(self.root / "f.elf"),
                 str(self.root / "f.bin")]):
            subprocess.run(command, check=True, capture_output=True)
        image = match.elf_image((self.root / "f.elf").read_bytes())
        self.symbols = {symbol["name"]: symbol["value"] for symbol in image["symbols"]}
        self.rom = (self.root / "f.bin").read_bytes()
        rows = [{"rom": f"0x{self.symbols[name]:08X}", "end": f"0x{self.symbols[name + '_end']:08X}",
                 "mode": "thumb"} for name in functions]
        rows.append({"rom": f"0x{R3:08X}", "end": f"0x{R3 + 2:08X}", "mode": "thumb"})
        self.mapping = json.dumps(rows).encode()

    def entry(self, **changes):
        row = {"allocator": f"0x{self.symbols['allocator']:08X}", "call": f"0x{self.symbols['alloc_call']:08X}",
               "base": "r7", "store": f"0x{self.symbols['store']:08X}", "reload": f"0x{self.symbols['reload']:08X}",
               "offset": 0, "writes": [f"0x{self.symbols['other']:08X}"]}
        row.update(changes)
        return {f"0x{self.symbols['creator']:08X}": {"review": REVIEW, "rows": [row]}}

    def prove(self, entries=None, *, kind=match.BufferCallProof):
        raw = None if entries is None else json.dumps(entries).encode()
        proof = kind(self.rom, self.mapping, stack_arguments=True, loop_replay=True, bios_wrappers=True,
                     dead_registers=True, call_via_targets=True, fresh_blocks=raw)
        body = self.rom[:self.symbols["owner_end"] - BASE]
        match.verify_leaf_instructions(body, BASE, True, buffer_proof=proof, call_resolver=proof.target,
                                       incoming_narrow_reads=True)
        return proof

    def refused(self, pattern, entries):
        with self.assertRaisesRegex(ValueError, pattern):
            self.prove(entries)

    # Admitted ------------------------------------------------------------------

    def test_the_reviewed_entry_forwards_the_stored_callback(self):
        self.build()
        proof = self.prove(self.entry())
        creator = self.symbols["creator"]
        self.assertEqual(proof.fresh_block_uses, {(creator, self.symbols["store"], self.symbols["reload"])})
        via = [line for line in call_via.lines(proof) if f"_call_via_r3 = 0x{self.symbols['callback'] + 1:08X}" in line]
        self.assertEqual(len(via), 1, call_via.lines(proof))
        line, = fresh.lines(proof)
        self.assertTrue(line.startswith(f"{fresh.FIELD}: `{fresh.SCHEMA}` 0x{creator:08X} row "), line)
        self.assertTrue(line.endswith(f"review: {REVIEW}"), line)
        self.assertIn(line, proof.loop_replay_lines())
        self.assertIn(self.symbols["callback"], proof.dependencies)

    def test_the_creators_own_frame_passed_to_the_callback(self):
        self.assertEqual([OWN_FRAME.count(text) for text in ("sub sp, #8", "mov r0, sp", "add sp, #8")], [1, 1, 1])
        self.build(creator=OWN_FRAME)
        proof = self.prove(self.entry())
        self.assertEqual(proof.fresh_block_uses,
                         {(self.symbols["creator"], self.symbols["store"], self.symbols["reload"])})
        self.assertIn(self.symbols["callback"], proof.dependencies)
        with self.assertRaises(ValueError):
            self.prove()

    def test_the_fingerprint_binds_the_review_and_the_row(self):
        self.build()
        bound = self.prove(self.entry()).fingerprint()
        entry = self.entry()
        (value,) = entry.values()
        value["review"] = REVIEW + " "
        self.assertNotEqual(self.prove(entry).fingerprint(), bound)
        self.assertEqual(self.prove(self.entry()).fingerprint(), bound)

    def test_a_store_through_the_base_elsewhere_is_checked_not_premised(self):
        self.build(between=BETWEEN + "\nstr r0, [r7, #4]\nstrh r0, [r7, #6]")
        self.prove(self.entry())

    def test_an_entry_must_match_its_own_function(self):
        self.build()
        entries = {f"0x{self.symbols['allocator']:08X}": self.entry()[f"0x{self.symbols['creator']:08X}"]}
        with self.assertRaises(ValueError):
            self.prove(entries)

    # Refused -------------------------------------------------------------------

    def test_without_an_entry_the_call_refuses_as_before(self):
        self.build()
        for entries in (None, {}):
            with self.subTest(entries=entries), self.assertRaises(ValueError) as caught:
                self.prove(entries)
            self.assertNotIn("fresh block", str(caught.exception))

    def test_an_entry_that_differs_from_the_bytes_refuses(self):
        self.build()
        symbols = self.symbols
        for changes, pattern in (
                (dict(store=f"0x{symbols['store'] + 2:08X}"), "not word accesses|is not an instruction"),
                (dict(reload=f"0x{symbols['reload'] - 2:08X}"), "not word accesses|reaches the reload|not an instruction"),
                (dict(offset=4), "not word accesses"),
                (dict(base="r5"), "not copied into the base"),
                (dict(allocator=f"0x{symbols['callback']:08X}"), "no call of the allocator"),
                (dict(writes=[]), "not the entry's"),
                (dict(writes=[f"0x{symbols['other']:08X}", f"0x{symbols['store']:08X}"]), "not the entry's")):
            with self.subTest(changes=changes):
                self.refused(pattern, self.entry(**changes))

    def test_the_window_between_store_and_reload_is_checked(self):
        for between, pattern in (
                (BETWEEN + "\nadds r7, #0", "base is written between"),
                (BETWEEN + "\nbl allocator", "call or transfer lies between"),
                (BETWEEN + "\nstr r0, [r7]", "may overwrite the stored word"),
                (BETWEEN + "\nstrb r0, [r7, #3]", "may overwrite the stored word"),
                (BETWEEN + "\nmovs r1, #0\nstr r0, [r7, r1]", "may overwrite the stored word"),
                (BETWEEN + "\nstmia r7!, {r0}", "base is written between|block store through the base")):
            with self.subTest(between=between):
                self.build(between=between)
                self.refused(pattern, self.entry())

    def test_a_path_around_the_store_refuses(self):
        # A branch from before the allocation straight to the reload.
        self.build()
        text = (self.root / "f.s").read_text().replace("alloc_call:\n", "cmp r1, #0\nbeq reload\nalloc_call:\n")
        (self.root / "f.s").write_text(text)
        self.build_from_text(text)
        self.refused("reaches the reload without the store", self.entry())

    def test_the_base_must_hold_the_allocator_result_at_the_store(self):
        # A write of the base between the copy and the store refuses; a call there is the ABI premise.
        for before, pattern in (("adds r7, #4", "base is written before the store"),
                                ("movs r7, #0", "base is written before the store")):
            with self.subTest(before=before):
                self.build()
                text = (self.root / "f.s").read_text().replace("store:\n", f"{before}\nstore:\n")
                (self.root / "f.s").write_text(text)
                self.build_from_text(text)
                self.refused(pattern, self.entry())

    def test_the_copy_is_reached_only_from_the_allocator_call(self):
        # A branch into the copy would put another R0 into the base.
        self.build()
        text = (self.root / "f.s").read_text().replace(
            "alloc_call:\n", "cmp r1, #0\nbeq join\nalloc_call:\n").replace(
            "    bl allocator\n    adds r7, r0, #0\n", "    bl allocator\njoin:\n    adds r7, r0, #0\n")
        self.assertEqual(text.count("join"), 2)
        (self.root / "f.s").write_text(text)
        self.build_from_text(text)
        self.refused("reached other than from the allocator call", self.entry())

    def test_a_store_or_reload_on_a_loop_refuses(self):
        # A path back to the store that misses the window writes the base unchecked; a loop through
        # the reload would forward the word a second time.
        for between, pattern in (
                (BETWEEN + "\ncmp r1, #0\nbeq reload\nadds r7, #4\nb store", "the store lies on a loop"),
                (BETWEEN, "the reload lies on a loop")):
            with self.subTest(pattern=pattern):
                self.build(between=between)
                if "reload lies" in pattern:
                    text = (self.root / "f.s").read_text().replace(
                        "    ldr r3, [r7]\n", "    ldr r3, [r7]\n    cmp r3, #0\n    beq reload\n")
                    (self.root / "f.s").write_text(text)
                    self.build_from_text(text)
                self.refused(pattern, self.entry())

    def test_a_far_jump_in_the_function_refuses(self):
        # agbcc's `bl` to a local label is a branch that never returns, not a call.
        self.build()
        text = (self.root / "f.s").read_text().replace("alloc_call:\n", "bl 1f\n1:\nalloc_call:\n")
        (self.root / "f.s").write_text(text)
        self.build_from_text(text)
        self.refused("a far jump at", self.entry())

    def test_a_store_of_a_value_with_no_fact_clears_the_word(self):
        # A walk can reach the store again with another value (a split join keeps states apart).
        self.build()
        proof = match.BufferCallProof(self.rom, self.mapping, stack_arguments=True, call_via_targets=True,
                                      fresh_blocks=json.dumps(self.entry()).encode())
        creator, store, reload = (self.symbols[name] for name in ("creator", "store", "reload"))
        ((_, (stored, _)),) = fresh.rows_for(proof, creator)
        at = lambda address: type("Instruction", (), {"address": address})()
        register = match.ARM_REG_R0 + stored
        constants = {register: call_via.CallTarget(self.symbols["callback"] + 1, {("pool", 0)})}
        fresh.extra_constant(proof, at(store), creator, constants)
        del constants[register]
        fresh.extra_constant(proof, at(store), creator, constants)
        self.assertIsNone(fresh.extra_constant(proof, at(reload), creator, constants))
        self.assertEqual(proof.fresh_block_uses, set())

    def build_from_text(self, text):
        for command in (
                ["arm-none-eabi-as", "-mthumb-interwork", str(self.root / "f.s"), "-o", str(self.root / "f.o")],
                ["arm-none-eabi-ld", "-Ttext=0x08000000", "-e", "owner", str(self.root / "f.o"),
                 "-o", str(self.root / "f.elf")],
                ["arm-none-eabi-objcopy", "-O", "binary", "--only-section=.text", str(self.root / "f.elf"),
                 str(self.root / "f.bin")]):
            subprocess.run(command, check=True, capture_output=True)
        image = match.elf_image((self.root / "f.elf").read_bytes())
        self.symbols = {symbol["name"]: symbol["value"] for symbol in image["symbols"]}
        self.rom = (self.root / "f.bin").read_bytes()
        rows = json.loads(self.mapping)
        names = ("owner", "creator", "allocator", "callback")
        for row, name in zip(rows, names):
            row["rom"], row["end"] = f"0x{self.symbols[name]:08X}", f"0x{self.symbols[name + '_end']:08X}"
        self.mapping = json.dumps(rows).encode()

    def test_malformed_entries_refuse(self):
        self.build()
        good = self.entry()
        (key, value), = good.items()
        cases = [b"not json", b"[]", json.dumps({"8005954": value}).encode(),
                 json.dumps({key: {"review": "", "rows": value["rows"]}}).encode(),
                 json.dumps({key: {"review": REVIEW, "rows": []}}).encode(),
                 json.dumps({key: dict(value, extra=1)}).encode(),
                 json.dumps({key: {"review": REVIEW, "rows": [dict(value["rows"][0], base="r3")]}}).encode(),
                 json.dumps({key: {"review": REVIEW, "rows": [dict(value["rows"][0], offset=2)]}}).encode(),
                 json.dumps({key: {"review": REVIEW, "rows": value["rows"] * 2}}).encode()]
        for raw in cases:
            with self.subTest(raw=raw[:60]), self.assertRaises(ValueError):
                fresh.parse(raw)

    def test_only_the_default_stack_argument_proofs_take_entries(self):
        self.build()
        raw = json.dumps(self.entry()).encode()

        class Other(match.BufferCallProof):
            pass
        for make in (lambda: Other(self.rom, self.mapping, stack_arguments=True, call_via_targets=True,
                                   fresh_blocks=raw),
                     lambda: match.BufferCallProof(self.rom, self.mapping, call_via_targets=True, fresh_blocks=raw),
                     # only where the proof takes call-via targets: A3 forwards their facts
                     lambda: match.BufferCallProof(self.rom, self.mapping, stack_arguments=True, fresh_blocks=raw)):
            with self.assertRaisesRegex(ValueError, "fresh block premises require"):
                make()
        self.assertIsNotNone(match.FunctionBufferCallProof(self.rom, self.mapping, stack_arguments=True,
                                                           call_via_targets=True, fresh_blocks=raw).fresh_block_entries)

    def test_an_aborted_pass_leaves_no_use(self):
        self.build()
        proof = match.BufferCallProof(self.rom, self.mapping, stack_arguments=True, call_via_targets=True,
                                      fresh_blocks=json.dumps(self.entry()).encode())
        saved = proof._snapshot_ledgers()
        proof.fresh_block_uses.add((1, 2, 3))
        proof._restore_ledgers(saved)
        self.assertEqual(proof.fresh_block_uses, set())

    # Mutants -------------------------------------------------------------------

    def test_without_the_forwarding_the_call_refuses(self):
        self.build()
        with patch.object(fresh, "extra_constant", lambda *args: None), self.assertRaises(ValueError):
            self.prove(self.entry())

    def test_without_the_window_check_a_clobbered_word_would_pass(self):
        self.build(between=BETWEEN + "\nstr r0, [r7]")
        with patch.object(fresh, "check", lambda proof, function, row: (4, 3)):
            self.prove(self.entry())      # the check is what refuses it


class WiringTests(unittest.TestCase):
    def test_every_default_stack_argument_construction_passes_the_entries(self):
        import ast
        found = set()
        for path in sorted((ROOT / "tools").glob("*.py")):
            tree = ast.parse(path.read_text())
            for function in ast.walk(tree):
                if not isinstance(function, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    continue
                for node in ast.walk(function):
                    if isinstance(node, ast.Call) and any(keyword.arg == "fresh_blocks" for keyword in node.keywords) \
                            and getattr(node.func, "attr", getattr(node.func, "id", None)) in (
                                "BufferCallProof", "FunctionBufferCallProof"):
                        found.add((path.name, function.name))
        # Exactly the default route's constructions that take call-via targets (call_via_target_profile).
        self.assertEqual(found, {("match.py", "main"), ("match.py", "verify_function_buffers"),
                                 ("match_evidence.py", "buffer_report_matches"),
                                 ("function_thunk_profile.py", "verify_source"),
                                 ("data_buffer_profile.py", "prove")})


    def test_entries_go_only_where_call_via_targets_do(self):
        # The constructor refuses entries on a proof without call-via targets, so each site passes them
        # under its own call_via_targets condition: a selector or library-unit route never meets it.
        import ast
        sites = []
        for path in sorted((ROOT / "tools").glob("*.py")):
            for node in ast.walk(ast.parse(path.read_text())):
                if not isinstance(node, ast.Call) or getattr(node.func, "attr", getattr(node.func, "id", None)) \
                        not in ("BufferCallProof", "FunctionBufferCallProof"):
                    continue
                keywords = {keyword.arg: keyword.value for keyword in node.keywords}
                if "fresh_blocks" not in keywords:
                    continue
                sites.append((path.name, node.lineno))
                targets, entries = keywords.get("call_via_targets"), keywords["fresh_blocks"]
                if isinstance(targets, ast.Constant) and targets.value is True:
                    continue
                with self.subTest(path=path.name, line=node.lineno):
                    self.assertIsInstance(entries, ast.IfExp)
                    self.assertEqual(ast.dump(entries.test), ast.dump(targets))
                    self.assertIsInstance(entries.orelse, ast.Constant)
                    self.assertIsNone(entries.orelse.value)
        self.assertEqual(len(sites), 6, sites)


class IssuingCopyTests(unittest.TestCase):
    def test_proofs_of_the_issuing_copy_of_match_take_the_rule(self):
        # match.py issues reports as __main__ loaded from its own file and replays them as the imported
        # match: proofs of both count (call_via_target_profile.kit_match).  Only the definitions are run.
        import types
        main = sys.modules["__main__"]
        copy = types.ModuleType("__main__")
        copy.__file__ = match.__file__
        source = Path(match.__file__).read_text().replace('if __name__ == "__main__":', "if False:")
        sys.modules["__main__"] = copy
        try:
            exec(compile(source, match.__file__, "exec"), copy.__dict__)
            for kind in ("BufferCallProof", "FunctionBufferCallProof"):
                with self.subTest(kind):
                    proof = getattr(copy, kind)(bytes(0x1000), "[]", stack_arguments=True, call_via_targets=True,
                                                fresh_blocks=b"{}")
                    self.assertTrue(fresh.applies(proof))
                    self.assertFalse(fresh.applies(getattr(copy, kind)(bytes(0x1000), "[]", stack_arguments=True)))
        finally:
            sys.modules["__main__"] = main

if __name__ == "__main__":
    unittest.main()
