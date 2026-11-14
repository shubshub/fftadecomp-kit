"""Synthetic, compiler-free coverage of u16-scalars-frame-v1.

The selector keeps the u16-scalars-v2 dispatch-identified pool and adds a
fixed Thumb frame of write-only outgoing call arguments.
"""

import copy
import json
import os
from pathlib import Path
import struct
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock

sys.dont_write_bytecode = True
TASK = Path(__file__).resolve().parents[1]
if os.environ.get("FFTA_TEST_SUPPORT_TOOLS"):
    sys.path.insert(0, os.environ["FFTA_TEST_SUPPORT_TOOLS"])
sys.path.insert(0, str(TASK / "tools"))
import match
import match_evidence as evidence
import switch_pool_outgoing_frame as frame
import typed_switch_outgoing_frame as typed_frame

assert Path(match.__file__).resolve() == TASK / "tools/match.py"
assert Path(evidence.__file__).resolve() == TASK / "tools/match_evidence.py"

BASE = 0x08000000
OBJECT = 0x02001000
CALLEE = BASE + 0x1000
THUNK = match.RUNTIME_HELPERS["_call_via_r3"]
SCALAR = 0x2FC1
SCHEMA = "elf-symbol-thumb-switch-data-u16-scalars-frame-v1"
V2_SCHEMA = "elf-symbol-thumb-switch-data-u16-scalars-v2"
POOL_POLICY = "dispatch-identified-table-pointer-v1"
STACK_POLICY = "write-only-outgoing-argument-words-v1"

PUSH_LR, POP_R1, BX_R1 = 0xB500, 0xBC02, 0x4708
STR_SP = 0x9000  # str r0,[sp,#4*n] | n
ARGUMENTS = ("str0", "str1", "call")


def sub_sp(words):
    return 0xB080 | words


def add_sp(words):
    return 0xB000 | words


def fixture(*, words=2, prologue=(), arguments=ARGUMENTS, case1=(), epilogue=None,
            release=None, target=CALLEE, push=PUSH_LR):
    """A guarded table whose pointer follows an object and a u16 scalar word.

    `words` is the `sub sp` allocation. Token lists hold halfwords, `strN`
    (`str r0,[sp,#4N]`), `call` (BL to `target`) and `bdone` (branch to the
    shared tail). `arguments` runs on every path before the release; `case1`
    is extra code in the second case only.
    """
    body, labels, fixups, calls = bytearray(), {}, [], []

    def half(value):
        body.extend(struct.pack("<H", value))

    def label(name):
        labels[name] = len(body)

    def emit(kind, name, register=0):
        fixups.append((len(body), kind, name, register))
        body.extend(bytes(4 if kind == "word" else 2))

    def tokens(items):
        for item in items:
            if item == "call":
                displacement = target - (BASE + len(body) + 4)
                calls.append([len(body), f"func_{target:08X}"])
                half(0xF000 | ((displacement >> 12) & 0x7FF))
                half(0xF800 | ((displacement >> 1) & 0x7FF))
            elif item == "bdone":
                emit("b", "done")
            elif isinstance(item, str) and item.startswith("str"):
                half(STR_SP | int(item[3:]))
            else:
                half(item)

    half(push)
    tokens(prologue)
    half(sub_sp(words))
    emit("ldr", "pool0", 2)
    emit("ldr", "pool1", 3)
    half(0x18C0)  # adds r0,r0,r3
    label("comparison")
    half(0x2801)  # cmp r0,#1
    label("guard")
    emit("bhi", "default")
    label("dispatch")
    half(0x0080)  # lsls r0,r0,#2
    emit("ldr", "pointer", 1)
    half(0x1840)  # adds r0,r0,r1
    half(0x6800)  # ldr r0,[r0]
    half(0x4687)  # mov pc,r0
    while len(body) % 4:
        half(0)
    label("pool0")
    body.extend(struct.pack("<I", OBJECT))
    label("pool1")
    body.extend(struct.pack("<I", SCALAR))
    label("pointer")
    emit("word", "table")
    label("table")
    emit("word", "case0")
    emit("word", "case1")
    label("case0")
    half(0x2001)  # movs r0,#1
    emit("b", "done")
    label("case1")
    half(0x2002)  # movs r0,#2
    tokens(case1)
    emit("b", "done")
    label("default")
    half(0x2000)  # movs r0,#0
    label("done")
    tokens(arguments)
    label("release")
    half(add_sp(words) if release is None else release)
    tokens((POP_R1, BX_R1) if epilogue is None else epilogue)
    while len(body) % 4:
        half(0)
    for offset, kind, name, register in fixups:
        destination = labels[name]
        if kind == "word":
            struct.pack_into("<I", body, offset, BASE + destination)
        elif kind == "ldr":
            distance = destination - ((offset + 4) & ~3)
            assert 0 <= distance <= 1020 and distance % 4 == 0
            struct.pack_into("<H", body, offset, 0x4800 | register << 8 | distance // 4)
        else:
            displacement = (destination - offset - 4) // 2
            struct.pack_into("<H", body, offset, (0xD800 | (displacement & 0xFF)) if kind == "bhi"
                             else (0xE000 | (displacement & 0x7FF)))
    relocations = [[labels["pointer"], labels["table"]],
                   [labels["table"], labels["case0"]],
                   [labels["table"] + 4, labels["case1"]]]
    descriptor = {name: labels[name] for name in (
        "comparison", "guard", "dispatch", "default", "table")}
    descriptor.update(literal=labels["pointer"], bound=1, relocations=relocations)
    manifest = {"calls": calls, "switch": descriptor,
                "data": [[labels["pool0"], "g_object", 0]],
                "data_policy": "complete-reachable-object-words-v1",
                "scalar_policy": "complete-reachable-u16-scalar-words-v1",
                "scalars": [[labels["pool1"], SCALAR]],
                "pool_policy": POOL_POLICY, "stack_policy": STACK_POLICY}
    mapping = [{"rom": f"0x{BASE:08X}", "end": f"0x{BASE + len(body):08X}", "mode": "thumb"},
               {"rom": f"0x{CALLEE:08X}", "end": f"0x{CALLEE + 2:08X}", "mode": "thumb"},
               {"rom": f"0x{THUNK:08X}", "end": f"0x{THUNK + 4:08X}", "mode": "thumb"}]
    return body, labels, manifest, mapping


def verify(body, manifest, mapping):
    rom = bytes(body).ljust(CALLEE - BASE, b"\0") + b"\x70\x47"
    rom = rom.ljust(THUNK - BASE, b"\0") + b"\x18\x47\xc0\x46"
    objects = json.dumps({"g_object": f"0x{OBJECT:08X}"}).encode()
    return match.verify_switches(bytes(body), BASE, rom, json.dumps(mapping).encode(),
                                 manifest, data_mapping=objects)


def relocations(manifest):
    return dict(map(tuple, manifest["switch"]["relocations"]))


def objects(manifest):
    return {offset: (name, OBJECT + addend) for offset, name, addend in manifest["data"]}


def leaf(body, manifest, calls, **kwargs):
    return match.verify_leaf_instructions(
        bytes(body), BASE, True, calls, switch_relocations=relocations(manifest),
        switch_data_relocations=objects(manifest), backward_switch_cases=True,
        switch_interposed_pool=True, **kwargs)


def straight(*items):
    """Run only the frame proof over straight-line code (`strN`, `call`, halfwords)."""
    from capstone import CS_ARCH_ARM, CS_MODE_THUMB, Cs
    body = bytearray()
    for item in items:
        if item == "call":
            body.extend(struct.pack("<HH", 0xF000, 0xF800))
        elif isinstance(item, str):
            body.extend(struct.pack("<H", STR_SP | int(item[3:])))
        else:
            body.extend(struct.pack("<H", item))
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    decoder.detail = True
    instructions = {item.address: item for item in decoder.disasm(bytes(body), BASE)}
    sites = sorted(instructions)
    edges = {site: [following] for site, following in zip(sites, sites[1:])}
    edges[sites[-1]] = []
    calls = {site: CALLEE for site in sites if instructions[site].size == 4}
    frame.verify_frame(instructions, edges, BASE, calls)


class AdmissionTests(unittest.TestCase):
    def test_outgoing_frame_with_interposed_pool_verifies(self):
        body, _, manifest, mapping = fixture()
        _, summary = verify(body, manifest, mapping)
        self.assertEqual(summary, match.CALL_SUMMARY)

    def test_calls_may_consume_prefixes_or_nothing(self):
        # A register-only call, a one-word call and a call that takes the
        # whole seven-word frame, each with its own freshly written words.
        arguments = ("call", "str0", "call", *(f"str{slot}" for slot in range(7)), "call")
        body, _, manifest, mapping = fixture(words=7, arguments=arguments)
        verify(body, manifest, mapping)

    def test_non_stack_block_copy_is_ordinary(self):
        copy_words = (0xC90C, 0xC00C)  # ldmia r1!,{r2,r3}; stmia r0!,{r2,r3}
        body, _, manifest, mapping = fixture(arguments=(*copy_words, *ARGUMENTS))
        verify(body, manifest, mapping)

    def test_loop_that_stores_and_calls(self):
        # str0; str1; bl; subs r1,#1; bne back to str0.
        body, _, manifest, mapping = fixture(arguments=(*ARGUMENTS, 0x3901, 0xD1F9))
        verify(body, manifest, mapping)

    def test_each_return_path_may_release(self):
        # The second case consumes the frame and returns through its own release.
        body, _, manifest, mapping = fixture(case1=(*ARGUMENTS, add_sp(2), POP_R1, BX_R1))
        verify(body, manifest, mapping)

    def test_call_after_the_whole_frame_call_is_register_only(self):
        body, _, manifest, mapping = fixture(arguments=(*ARGUMENTS, "call"))
        verify(body, manifest, mapping)

    def test_v2_still_refuses_the_frame(self):
        body, _, manifest, mapping = fixture()
        manifest.pop("stack_policy")
        with self.assertRaisesRegex(ValueError, "excludes fixed frames"):
            verify(body, manifest, mapping)


class AttackTests(unittest.TestCase):
    def refused(self, pattern=None, **kwargs):
        body, _, manifest, mapping = fixture(**kwargs)
        if pattern is None:
            with self.assertRaises(ValueError):
                verify(body, manifest, mapping)
        else:
            with self.assertRaisesRegex(ValueError, pattern):
                verify(body, manifest, mapping)

    def test_dynamic_stack_adjustment(self):
        self.refused(arguments=(0x449D, *ARGUMENTS))  # add sp,r3
        self.refused(arguments=(sub_sp(1), *ARGUMENTS, add_sp(1)))
        self.refused("one fixed allocation", arguments=(add_sp(1), sub_sp(1), *ARGUMENTS))

    def test_zero_stack_adjustment(self):
        for adjustment in (add_sp(0), sub_sp(0)):
            with self.subTest(adjustment=hex(adjustment)):
                self.refused(arguments=(adjustment, *ARGUMENTS))

    def test_second_release_on_one_path(self):
        # The ordinary stack tracker refuses this first; the frame proof
        # refuses it on its own as well.
        self.refused(case1=(add_sp(2), add_sp(2)))
        straight(sub_sp(1), "str0", "call", add_sp(1), 0x4770)  # bx lr
        with self.assertRaisesRegex(ValueError, "outside its allocation"):
            straight(sub_sp(1), "str0", "call", add_sp(1), add_sp(1), 0x4770)

    def test_unbalanced_return(self):
        self.refused(release=add_sp(1))
        self.refused(release=0x46C0)  # nop instead of the release
        # The second case returns without releasing the frame.
        self.refused(case1=(POP_R1, BX_R1))

    def test_stack_read_before_or_after_write(self):
        self.refused("must store", arguments=(0x9800, *ARGUMENTS))  # ldr r0,[sp]
        self.refused("must store", arguments=("str0", 0x9800, "str1", "call"))

    def test_stack_address_escape(self):
        for escape in (0xA800, 0xA901, 0x4668, 0x4468):  # add r0,sp,#0; add r1,sp,#4; mov r0,sp; add r0,sp
            with self.subTest(escape=hex(escape)):
                self.refused(arguments=(escape, *ARGUMENTS))

    def test_out_of_frame_access(self):
        # [sp,#8] is the saved r4 slot above the eight-byte frame.
        self.refused("must store", arguments=("str0", "str1", "str2", "call"),
                     push=0xB510, epilogue=(0xBC10, POP_R1, BX_R1))  # push {r4,lr}; pop {r4}
        # Before the allocation, [sp] is the saved r4 slot.
        self.refused("must store", prologue=("str0",),
                     push=0xB510, epilogue=(0xBC10, POP_R1, BX_R1))

    def test_runtime_call_thunk(self):
        self.refused(target=THUNK)
        body, _, manifest, _ = fixture(target=THUNK)
        calls = {BASE + offset: THUNK for offset, _ in manifest["calls"]}
        with self.assertRaisesRegex(ValueError, "runtime call thunks"):
            leaf(body, manifest, calls, switch_outgoing_stack=STACK_POLICY)

    def test_written_word_must_be_consumed(self):
        self.refused("no call consumes it", arguments=("call", "str0", "str1"))

    def test_arguments_must_be_a_prefix(self):
        self.refused("prefix", arguments=("str1", "call", "str0", "str1", "call"))

    def test_arguments_must_match_on_every_path(self):
        # Case 1 calls with no stack words; the shared call then sees two
        # different argument sets.
        self.refused("identically", arguments=("call",), case1=("str0", "str1"))
        self.refused("identically", arguments=("str0", "call"), case1=("str1",))

    def test_every_frame_word_is_consumed(self):
        self.refused("consumed by a call", arguments=("str0", "call"))
        self.refused("consumed by a call", arguments=())

    def test_frame_lifetime(self):
        self.refused("lifetime", prologue=("call",))
        self.refused("move inside", arguments=(0xB410, *ARGUMENTS, 0xBC10))  # push/pop {r4}

    def test_stack_block_transfer(self):
        self.refused(arguments=(0xE88D, 0x0003, *ARGUMENTS))  # stm.w sp,{r0,r1}


class StateLimitTests(unittest.TestCase):
    # Seven conditionally written words, then all seven unconditionally:
    # every path reaches the call with the whole frame, but the walk holds
    # up to 2**7 written sets at each site in between.
    ARGUMENTS = (*(token for slot in range(7) for token in (0xD000, f"str{slot}")),  # beq over the store
                 *(f"str{slot}" for slot in range(7)), "call")

    def test_branching_writes_verify_within_the_limit(self):
        body, _, manifest, mapping = fixture(words=7, arguments=self.ARGUMENTS)
        verify(body, manifest, mapping)

    def test_walk_beyond_the_limit_refuses(self):
        body, _, manifest, mapping = fixture(words=7, arguments=self.ARGUMENTS)
        with mock.patch.object(frame, "STATE_LIMIT", 64), \
                self.assertRaisesRegex(ValueError, "state limit"):
            verify(body, manifest, mapping)


class ManifestTests(unittest.TestCase):
    def test_policy_marker_is_exact_and_requires_the_pool(self):
        body, _, manifest, mapping = fixture()
        with self.assertRaisesRegex(ValueError, "canonical stack policy"):
            verify(body, dict(manifest, stack_policy="other-policy"), mapping)
        without_pool = copy.deepcopy(manifest)
        without_pool.pop("pool_policy")
        with self.assertRaisesRegex(ValueError, "canonical stack policy"):
            verify(body, without_pool, mapping)
        typed = dict(manifest, frame_policy=typed_frame.SELECTOR)
        with self.assertRaises(ValueError):
            verify(body, typed, mapping)

    def test_context_is_isolated(self):
        body, _, manifest, _ = fixture()
        calls = {BASE + offset: CALLEE for offset, _ in manifest["calls"]}
        with self.assertRaisesRegex(ValueError, "canonical stack policy"):
            leaf(body, manifest, calls, switch_outgoing_stack="other")
        with self.assertRaisesRegex(ValueError, "requires the interposed switch pool"):
            match.verify_leaf_instructions(
                bytes(body), BASE, True, calls, switch_relocations=relocations(manifest),
                switch_data_relocations=objects(manifest), backward_switch_cases=True,
                switch_outgoing_stack=STACK_POLICY)
        with self.assertRaisesRegex(ValueError, "isolated switch-data context"):
            leaf(body, manifest, calls, switch_outgoing_stack=STACK_POLICY,
                 typed_switch_outgoing_frame=typed_frame.SELECTOR)

    def test_selector_uses_the_isolated_fixed_configuration(self):
        args = SimpleNamespace(
            switch_data_profile=frame.SELECTOR,
            mode="thumb", control_flow_profile="ordinary", signed_quotient_profile=None,
            signed_runtime_profile=None, addressed_signed_runtime_profile=None,
            unsigned_runtime_profile=None, software_double_profile=None,
            software_double_remainder_profile=None, function_address_profile=None,
            switch_profile=None, owner_runtime_profile=None,
            cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
            objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        match.switch_u16_scalar_configuration(args)
        for field, value in (("switch_profile", "two-constants-frame-v1"),
                             ("function_address_profile", "canonical-thunks-v1")):
            with self.subTest(field=field), \
                    self.assertRaisesRegex(ValueError, "isolated explicit selector"):
                match.switch_u16_scalar_configuration(SimpleNamespace(**{**vars(args), field: value}))


class ReportTests(unittest.TestCase):
    def setUp(self):
        self.body, _, self.manifest, self.mapping = fixture()
        directory = tempfile.TemporaryDirectory(prefix="switch_pool_frame_",
                                                dir=os.environ.get("FFTA_TEST_SCRATCH"))
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        (self.root / "src").mkdir()
        (self.root / "include").mkdir()
        (self.root / "src/08000000.c").write_text("unsigned func_08000000(unsigned x);\n")
        self.source = evidence.source_fingerprint(self.root, BASE)
        self.functions = json.dumps(self.mapping).encode()
        self.objects = json.dumps({"g_object": f"0x{OBJECT:08X}"}).encode()
        self.rom_path = self.root / "synthetic-image.bin"
        rom = bytes(self.body).ljust(CALLEE - BASE, b"\0") + b"\x70\x47"
        self.rom_path.write_bytes(rom.ljust(THUNK - BASE, b"\0") + b"\x18\x47\xc0\x46")
        for name, value in (("mapping_snapshot", self.functions), ("data_snapshot", self.objects),
                            ("report_rom_path", str(self.rom_path))):
            patcher = mock.patch.object(evidence, name, return_value=value)
            patcher.start()
            self.addCleanup(patcher.stop)

    def report(self, manifest=None, fingerprint=None, *, schema=SCHEMA, summary=None,
               stack=True):
        manifest = self.manifest if manifest is None else manifest
        summary = frame.SUMMARY if summary is None else summary
        fingerprint = fingerprint or frame.fingerprint(BASE, self.body, manifest)
        lines = [f"* verification: `{schema}`",
                 f"* source SHA-256: `{self.source}`"]
        if stack:
            lines.append(f"* stack frame: {evidence.STACK_SUMMARY}")
        lines += [
            f"* mapping SHA-256: `{evidence.mapping_fingerprint(self.functions)}`",
            f"* control flow: {match.CALL_SUMMARY}",
            f"* data symbols SHA-256: `{evidence.mapping_fingerprint(self.objects)}`",
            f"* switches: {summary}",
            f"* switch manifest: `{evidence.switch_manifest(manifest)}`",
            f"* switch proof SHA-256: `{fingerprint}`",
            "* verified extent: complete ELF function symbol, including literal pools",
            "* relocations: none",
            f"* ROM bytes: `{self.body.hex()}` ({len(self.body)} bytes)",
            f"* compiled : `{self.body.hex()}`",
            "* source plausibility: plausible",
            f"**MATCH - byte identical** - {len(self.body)}/{len(self.body)} bytes"]
        return "\n".join(lines)

    def valid(self, report):
        return evidence.switch_report_matches(report.splitlines(), self.root, BASE, data_profile=True)

    def without(self, *fields):
        manifest = copy.deepcopy(self.manifest)
        for field in fields:
            manifest.pop(field)
        return manifest

    def test_report_revalidates(self):
        report = self.report()
        self.assertTrue(self.valid(report))
        with mock.patch.object(evidence.empty_body, "has_empty_body", return_value=False):
            self.assertTrue(evidence.report_matches(report, self.root, BASE))

    def test_tampered_reports_reject(self):
        report = self.report()
        v2 = evidence.switch_pool_u16_scalar_fingerprint(BASE, self.body, self.manifest)
        self.assertNotEqual(v2, frame.fingerprint(BASE, self.body, self.manifest))
        changed = copy.deepcopy(self.manifest)
        changed["calls"][0][0] += 2
        variants = [
            self.report(self.without("stack_policy")),
            self.report(dict(self.manifest, stack_policy="other-policy")),
            self.report(self.without("pool_policy")),
            self.report(changed),
            self.report(fingerprint=v2),
            self.report(stack=False),
            report.replace(frame.SUMMARY, evidence.SWITCH_POOL_U16_SCALAR_SUMMARY),
            report + f"\n* verification: `{SCHEMA}`",
            report + "\n* buffer calls: none",
        ]
        for index, variant in enumerate(variants):
            with self.subTest(index=index):
                self.assertFalse(self.valid(variant))

    def test_relabelled_reports_reject_both_ways(self):
        v2 = self.without("stack_policy")
        v1 = self.without("stack_policy", "pool_policy")
        typed = dict(self.without("stack_policy", "pool_policy", "scalar_policy", "scalars"),
                     frame_policy=typed_frame.SELECTOR)
        relabelled = {
            "frame as v2": self.report(
                v2, evidence.switch_pool_u16_scalar_fingerprint(BASE, self.body, v2),
                schema=V2_SCHEMA, summary=evidence.SWITCH_POOL_U16_SCALAR_SUMMARY, stack=False),
            "frame as v2 keeping marker": self.report(
                fingerprint=evidence.switch_pool_u16_scalar_fingerprint(BASE, self.body, self.manifest),
                schema=V2_SCHEMA, summary=evidence.SWITCH_POOL_U16_SCALAR_SUMMARY),
            "frame as v1": self.report(
                v1, evidence.switch_u16_scalar_fingerprint(BASE, self.body, v1),
                schema=evidence.SWITCH_U16_SCALAR_SCHEMA, summary=evidence.SWITCH_U16_SCALAR_SUMMARY,
                stack=False),
            "frame as typed outgoing": self.report(
                typed, typed_frame.fingerprint(BASE, self.body, typed),
                schema=typed_frame.SCHEMA, summary=typed_frame.SUMMARY),
            "v2 as frame": self.report(v2, frame.fingerprint(BASE, self.body, v2)),
            "v1 as frame": self.report(v1, frame.fingerprint(BASE, self.body, v1)),
            "typed outgoing as frame": self.report(typed, frame.fingerprint(BASE, self.body, typed)),
        }
        for name, report in relabelled.items():
            with self.subTest(name=name), \
                    mock.patch.object(evidence.empty_body, "has_empty_body", return_value=False):
                self.assertFalse(evidence.report_matches(report, self.root, BASE))

    def test_tampered_bytes_reject(self):
        altered = bytearray(self.rom_path.read_bytes())
        altered[len(self.body) - 1] ^= 1
        self.rom_path.write_bytes(altered)
        self.assertFalse(self.valid(self.report()))

    def test_rebuild_forwards_the_selector(self):
        import rebuild
        self.enterContext(mock.patch.object(evidence.empty_body, "has_empty_body", return_value=False))
        self.assertEqual(rebuild.saved_profile_arguments(self.report(), self.root, BASE),
                         ["--switch-data-profile", frame.SELECTOR])
        with self.assertRaisesRegex(ValueError, "invalid saved profile report"):
            rebuild.saved_profile_arguments(self.report(self.without("stack_policy")), self.root, BASE)
        self.assertIsNone(typed_frame.selector_for_report(self.report()))

    def test_status_forwards_the_selector(self):
        import status
        (self.root / "config").mkdir()
        (self.root / "config/functions.json").write_bytes(self.functions)
        (self.root / "config/data_symbols.json").write_bytes(self.objects)
        (self.root / "docs/match").mkdir(parents=True)
        (self.root / "docs/match/08000000.md").write_text(self.report())
        self.enterContext(mock.patch.object(evidence.empty_body, "has_empty_body", return_value=False))
        output = (f"extent    {len(self.body)} bytes (complete ELF symbol)\n"
                  "verdict MATCH - byte identical\n")

        def invoke(command, **kwargs):
            self.assertEqual(command.count("--switch-data-profile"), 1)
            self.assertEqual(command[command.index("--switch-data-profile") + 1], frame.SELECTOR)
            return subprocess.CompletedProcess(command, 0, output, "")
        with mock.patch.object(status.subprocess, "run", side_effect=invoke) as native:
            result = status.collect(str(self.root), True)
            self.assertEqual(result[1], 1)
            self.assertEqual(result[4], [])
            native.assert_called_once()


if __name__ == "__main__":
    unittest.main()
