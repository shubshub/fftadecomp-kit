"""Synthetic, compiler-free coverage of u16-scalars-fixed-frame-v1 and wide scalar words.

u16-scalars-fixed-frame-v1 keeps the u16-scalars-v1 fixed pool (the table
pointer is the word after the dispatch) and adds the u16-scalars-frame-v1
write-only outgoing-argument frame, without function literals or call thunks.
Separately, every u16 scalar switch policy binds an exact pool word of at
least 0x10000000 under `unmapped-bus-scalar-words-v1`.
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
sys.path.insert(0, str(TASK / "tests"))
import match
import match_evidence as evidence
import report_fixtures
import switch_pool_outgoing_frame as frame
import switch_wide_scalars as wide_scalars
import test_switch_pool_outgoing_frame as pool_tests

assert Path(match.__file__).resolve() == TASK / "tools/match.py"

BASE = 0x08000000
OBJECT = 0x02001000
CALLEE = BASE + 0x1000
THUNK = match.RUNTIME_HELPERS["_call_via_r3"]
SCALAR = 0x2FC1
HALF, ONE = 0x3F000000, 0x3F800000  # 0.5f and 1.0f, as in 080A7218
STACK_POLICY = "write-only-outgoing-argument-words-v1"
WIDE_POLICY = "unmapped-bus-scalar-words-v1"
ARGUMENTS = ("str0", "str1", "call")
FUNCTIONS_FRAME_SCHEMA = "elf-symbol-thumb-switch-data-u16-scalars-functions-frame-v1"


def fixture(*, words=2, framed=True, arguments=ARGUMENTS, case1=(), wide=(), scalar=True,
            pointer_reads=1, target=CALLEE):
    """A guarded two-case table on the fixed pool, with an optional outgoing frame.

    The prologue loads the object, the u16 scalar and each `wide` word; the
    pool sits after the epilogue. `arguments` runs on every path before the
    release, and `case1` only in the second case. `pointer_reads` above one
    adds a second read of the table pointer word to the prologue.
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
            elif isinstance(item, str) and item.startswith("str"):
                half(0x9000 | int(item[3:]))
            elif isinstance(item, tuple):
                emit(*item)
            else:
                half(item)

    half(0xB500)  # push {lr}
    if framed:
        half(0xB080 | words)
    for _ in range(pointer_reads - 1):
        emit("ldr", "pointer", 3)
    emit("ldr", "object", 2)
    if scalar:
        emit("ldr", "scalar", 3)
        half(0x18C0)  # adds r0,r0,r3
    for index in range(len(wide)):
        emit("ldr", f"wide{index}", 3)
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
    if framed:
        tokens(arguments)
        half(0xB000 | words)
    else:
        tokens(("call",))
    half(0xBC02)  # pop {r1}
    half(0x4708)  # bx r1
    while len(body) % 4:
        half(0)
    label("object")
    body.extend(struct.pack("<I", OBJECT))
    if scalar:
        label("scalar")
        body.extend(struct.pack("<I", SCALAR))
    for index, value in enumerate(wide):
        label(f"wide{index}")
        body.extend(struct.pack("<I", value))
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
    descriptor = {name: labels[name] for name in ("comparison", "guard", "dispatch", "default", "table")}
    descriptor.update(literal=labels["pointer"], bound=1, relocations=[
        [labels["pointer"], labels["table"]], [labels["table"], labels["case0"]],
        [labels["table"] + 4, labels["case1"]]])
    manifest = {"calls": calls, "switch": descriptor,
                "data": [[labels["object"], "g_object", 0]],
                "data_policy": "complete-reachable-object-words-v1",
                "scalar_policy": "complete-reachable-u16-scalar-words-v1",
                "scalars": [[labels["scalar"], SCALAR]] if scalar else []}
    if framed:
        manifest["stack_policy"] = STACK_POLICY
    if wide:
        manifest["wide_scalar_policy"] = WIDE_POLICY
        manifest["wide_scalars"] = [[labels[f"wide{index}"], value] for index, value in enumerate(wide)]
    mapping = [{"rom": f"0x{BASE:08X}", "end": f"0x{BASE + len(body):08X}", "mode": "thumb"},
               {"rom": f"0x{CALLEE:08X}", "end": f"0x{CALLEE + 2:08X}", "mode": "thumb"},
               {"rom": f"0x{THUNK:08X}", "end": f"0x{THUNK + 4:08X}", "mode": "thumb"}]
    return body, labels, manifest, mapping


def rom_image(body):
    rom = bytes(body).ljust(CALLEE - BASE, b"\0") + b"\x70\x47"
    return rom.ljust(THUNK - BASE, b"\0") + b"\x18\x47\xc0\x46"


def verify(body, manifest, mapping, objects=None):
    objects = {"g_object": f"0x{OBJECT:08X}"} if objects is None else objects
    return match.verify_switches(bytes(body), BASE, rom_image(body), json.dumps(mapping).encode(),
                                 manifest, data_mapping=json.dumps(objects).encode())


def without(manifest, *fields):
    manifest = copy.deepcopy(manifest)
    for field in fields:
        manifest.pop(field)
    return manifest


class FixedFrameTests(unittest.TestCase):
    def refused(self, pattern, **kwargs):
        body, _, manifest, mapping = fixture(**kwargs)
        with self.assertRaisesRegex(ValueError, pattern):
            verify(body, manifest, mapping)

    def test_fixed_pool_frame_verifies(self):
        body, _, manifest, mapping = fixture()
        _, summary = verify(body, manifest, mapping)
        self.assertEqual(summary, match.CALL_SUMMARY)
        self.assertEqual(frame.schema(manifest), frame.FIXED_SCHEMA)
        self.assertEqual(frame.summary(manifest), frame.FIXED_SUMMARY)
        # Prefix calls and a wider frame, as in the pool selector.
        arguments = ("call", "str0", "call", *(f"str{slot}" for slot in range(4)), "call")
        body, _, manifest, mapping = fixture(words=4, arguments=arguments)
        verify(body, manifest, mapping)

    def test_frameless_u16_scalars_v1_still_refuses_the_frame(self):
        body, _, manifest, mapping = fixture()
        with self.assertRaisesRegex(ValueError, "excludes fixed frames"):
            verify(body, without(manifest, "stack_policy"), mapping)
        # And the frame marker cannot be put on a frameless function.
        body, _, manifest, mapping = fixture(framed=False)
        verify(body, manifest, mapping)
        with self.assertRaisesRegex(ValueError, "one fixed allocation"):
            verify(body, dict(manifest, stack_policy=STACK_POLICY), mapping)

    def test_markers_are_exact(self):
        body, _, manifest, mapping = fixture()
        with self.assertRaisesRegex(ValueError, "canonical stack policy"):
            verify(body, dict(manifest, stack_policy="other-policy"), mapping)
        # Claiming the dispatch-identified pool for a fixed layout fails the layout.
        with self.assertRaises(ValueError):
            verify(body, dict(manifest, pool_policy="dispatch-identified-table-pointer-v1"), mapping)
        # The frame marker still needs the complete scalar data policy.
        with self.assertRaisesRegex(ValueError, "canonical stack policy"):
            verify(body, without(manifest, "scalar_policy", "scalars"), mapping)

    def test_frame_obligations_apply_on_the_fixed_pool(self):
        self.refused("must store", arguments=(0x9800, *ARGUMENTS))  # ldr r0,[sp]
        self.refused("no call consumes it", arguments=("call", "str0", "str1"))
        self.refused("consumed by a call", arguments=("str0", "call"))
        self.refused("identically", arguments=("str0", "call"), case1=("str1",))
        self.refused("stack-address|stack alias|unsupported", arguments=(0xA800, *ARGUMENTS))  # add r0,sp,#0

    def test_call_thunks_stay_refused(self):
        self.refused("runtime call thunks", target=THUNK)

    def test_table_pointer_is_read_only_by_the_dispatch(self):
        self.refused("read only by its dispatch load", pointer_reads=2)

    def test_literals_cannot_name_the_callers_bytes(self):
        body, labels, manifest, mapping = fixture()
        own = BASE + labels["case0"]
        struct.pack_into("<I", body, labels["object"], own)
        with self.assertRaisesRegex(ValueError, "own bytes|code entries|function spans|object"):
            verify(body, manifest, mapping, objects={"g_object": f"0x{own:08X}"})

    def test_leaf_context(self):
        body, labels, manifest, _ = fixture()
        calls = {BASE + offset: CALLEE for offset, _ in manifest["calls"]}
        options = dict(switch_relocations=dict(map(tuple, manifest["switch"]["relocations"])),
                       switch_data_relocations={labels["object"]: ("g_object", OBJECT)},
                       backward_switch_cases=True, switch_outgoing_stack=STACK_POLICY)
        match.verify_leaf_instructions(bytes(body), BASE, True, calls,
                                       switch_outgoing_stack_fixed_pool=True, **options)
        with self.assertRaisesRegex(ValueError, "requires the interposed switch pool"):
            match.verify_leaf_instructions(bytes(body), BASE, True, calls, **options)

    def test_selector_configuration(self):
        args = SimpleNamespace(
            switch_data_profile=frame.FIXED_SELECTOR,
            mode="thumb", control_flow_profile="ordinary", signed_quotient_profile=None,
            signed_runtime_profile=None, addressed_signed_runtime_profile=None,
            unsigned_runtime_profile=None, software_double_profile=None,
            software_double_remainder_profile=None, function_address_profile=None,
            switch_profile=None, owner_runtime_profile=None,
            cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
            objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        match.switch_u16_scalar_configuration(args)
        with self.assertRaisesRegex(ValueError, "isolated explicit selector"):
            match.switch_u16_scalar_configuration(
                SimpleNamespace(**{**vars(args), "switch_profile": "two-constants-frame-v1"}))


class WideScalarTests(unittest.TestCase):
    def test_wide_words_bind_beside_u16_scalars(self):
        for framed in (True, False):
            with self.subTest(framed=framed):
                body, _, manifest, mapping = fixture(framed=framed, wide=(HALF, ONE))
                verify(body, manifest, mapping)

    def test_wide_words_alone_bind(self):
        body, _, manifest, mapping = fixture(scalar=False, wide=(HALF,))
        verify(body, manifest, mapping)
        with self.assertRaisesRegex(ValueError, "nonempty"):
            verify(body, without(manifest, "wide_scalar_policy", "wide_scalars"), mapping)

    def test_bounds(self):
        for value in (0x10000000, 0xFFFFFFFF, 0x80000000):
            with self.subTest(value=hex(value)):
                body, _, manifest, mapping = fixture(wide=(value,))
                verify(body, manifest, mapping)
        for value in (0x0FFFFFFF, 0x08000001, 0x02001000, 0x04000000, 0x00010000):
            body, labels, manifest, mapping = fixture(wide=(value,))
            with self.subTest(value=hex(value)), \
                    self.assertRaisesRegex(ValueError, "outside the GBA bus"):
                verify(body, manifest, mapping)
            moved = dict(without(manifest, "wide_scalar_policy", "wide_scalars"),
                         scalars=[*manifest["scalars"], [labels["wide0"], value]])
            with self.subTest(value=hex(value), place="scalars"), self.assertRaises(ValueError):
                verify(body, moved, mapping)
        self.assertFalse(wide_scalars.admits(True))
        self.assertFalse(wide_scalars.admits(0x100000000))

    def test_records_split_and_the_u16_helper_still_refuses(self):
        body, labels, manifest, mapping = fixture(wide=(HALF,))
        instructions, _ = verify(body, manifest, mapping)
        objects = {labels["object"]: ("g_object", OBJECT)}
        self.assertEqual(match.switch_scalar_words(body, BASE, instructions, manifest["switch"], objects),
                         (manifest["scalars"], manifest["wide_scalars"]))
        with self.assertRaisesRegex(ValueError, "admits only u16"):
            match.switch_u16_scalar_records(body, BASE, instructions, manifest["switch"], objects)

    def test_manifest_tampering_rejects(self):
        body, labels, manifest, mapping = fixture(wide=(HALF, ONE))
        changed = copy.deepcopy(manifest)
        changed["wide_scalars"][0][1] = ONE
        variants = {
            "policy name": dict(manifest, wide_scalar_policy="other-policy"),
            "policy missing": without(manifest, "wide_scalar_policy"),
            "records missing": without(manifest, "wide_scalars"),
            "both missing": without(manifest, "wide_scalar_policy", "wide_scalars"),
            "empty records": dict(manifest, wide_scalars=[]),
            "value": changed,
            "order": dict(manifest, wide_scalars=manifest["wide_scalars"][::-1]),
            "duplicate": dict(manifest, wide_scalars=manifest["wide_scalars"][:1] * 2),
            "dropped": dict(manifest, wide_scalars=manifest["wide_scalars"][:1]),
            "u16 word as wide": dict(manifest, scalars=[], wide_scalars=[
                manifest["scalars"][0], *manifest["wide_scalars"]]),
            "malformed": dict(manifest, wide_scalars=[[labels["wide0"], HALF, 0]]),
            "bool value": dict(manifest, wide_scalars=[[labels["wide0"], True]]),
            "without scalar policy": without(manifest, "scalar_policy", "scalars"),
        }
        for name, variant in variants.items():
            with self.subTest(name=name), self.assertRaises(ValueError):
                verify(body, variant, mapping)
        # A wide marker on a manifest without wide words is refused too.
        body, _, plain, mapping = fixture()
        with self.assertRaises(ValueError):
            verify(body, dict(plain, wide_scalar_policy=WIDE_POLICY, wide_scalars=[]), mapping)

    def test_wide_records_need_the_scalar_policy(self):
        # An unreached wide-valued word after the pool: a data-only manifest cannot carry
        # wide records, even for a word no load reaches.
        body, _, manifest, mapping = fixture(framed=False, scalar=False)
        offset = len(body)
        body += struct.pack("<I", HALF)
        mapping[0]["end"] = f"0x{BASE + len(body):08X}"
        plain = without(manifest, "scalar_policy", "scalars")
        verify(body, plain, mapping)
        with self.assertRaisesRegex(ValueError, "invalid switch manifest"):
            verify(body, dict(plain, wide_scalar_policy=WIDE_POLICY, wide_scalars=[[offset, HALF]]), mapping)

    def test_premise_text(self):
        self.assertEqual(wide_scalars.report_line(),
                         "* switch wide scalar premise: each `wide_scalars` word is an exact number of at "
                         "least 0x10000000; GBATEK lists 10000000-FFFFFFFF as unused memory whose reads "
                         "return the prefetched opcode, so the word is no mapped address; the hard-coded value "
                         "of an address plus or minus a constant whose 32-bit sum is 0x10000000 or more (a ROM "
                         "object plus 0x08000000 is one), an expression agbcc would fold into one such word, is "
                         "assumed absent from the source")

    def test_interposed_pool_words_stay_objects_or_u16(self):
        body, labels, manifest, mapping = pool_tests.fixture()
        struct.pack_into("<I", body, labels["pool1"], HALF)
        manifest = dict(manifest, scalars=[], wide_scalar_policy=WIDE_POLICY,
                        wide_scalars=[[labels["pool1"], HALF]])
        with self.assertRaisesRegex(ValueError, "interposed switch pool words"):
            pool_tests.verify(body, manifest, mapping)


class ReportTests(unittest.TestCase):
    def setUp(self):
        self.body, _, self.manifest, self.mapping = fixture(wide=(HALF,))
        directory = tempfile.TemporaryDirectory(prefix="switch_fixed_frame_",
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
        self.rom_path.write_bytes(rom_image(self.body))
        for name, value in (("mapping_snapshot", self.functions), ("data_snapshot", self.objects),
                            ("report_rom_path", str(self.rom_path))):
            patcher = mock.patch.object(evidence, name, return_value=value)
            patcher.start()
            self.addCleanup(patcher.stop)
        self.enterContext(mock.patch.object(evidence.empty_body, "has_empty_body", return_value=False))

    def report(self, manifest=None, fingerprint=None, *, schema=frame.FIXED_SCHEMA, summary=None,
               stack=True, premise=None):
        manifest = self.manifest if manifest is None else manifest
        report = report_fixtures.switch_report(
            self.root, BASE, self.body, schema, manifest, summary=summary,
            fingerprint=fingerprint or frame.fingerprint(BASE, self.body, manifest), control_flow=match.CALL_SUMMARY)
        if not stack:
            report = report.replace(f"* stack frame: {evidence.STACK_SUMMARY}\n", "")
        if premise is not None:
            # replace the premise line the writer derives from the manifest with the given lines
            lines = [line for line in report.split("\n") if line != wide_scalars.report_line()]
            at = next(index for index, line in enumerate(lines) if line.startswith("* switch manifest: ")) + 1
            report = "\n".join(lines[:at] + list(premise) + lines[at:])
        return report

    def valid(self, report):
        return report_fixtures.replay(report, self.root, BASE)

    def test_report_revalidates(self):
        self.assertTrue(self.valid(self.report()))

    def test_premise_line_is_exact(self):
        line = wide_scalars.report_line()
        for name, premise in {"missing": [],
                              "duplicate": [line, line],
                              "altered": [line.replace("0x10000000", "0x08000000")],
                              "indented": ["  " + line],
                              "extra indented copy": [line, "  " + line]}.items():
            with self.subTest(name=name):
                self.assertFalse(self.valid(self.report(premise=premise)))
        # Not printed without wide words.
        body, _, plain, mapping = fixture()
        self.body, self.manifest = body, plain
        self.rom_path.write_bytes(rom_image(body))
        self.functions = json.dumps(mapping).encode()
        with mock.patch.object(evidence, "mapping_snapshot", return_value=self.functions):
            self.assertTrue(self.valid(self.report()))
            self.assertFalse(self.valid(self.report(premise=[line])))

    def test_tampered_reports_reject(self):
        changed = copy.deepcopy(self.manifest)
        changed["calls"][0][0] += 2
        variants = {
            "no stack policy": self.report(without(self.manifest, "stack_policy")),
            "no wide policy": self.report(without(self.manifest, "wide_scalar_policy", "wide_scalars")),
            "pool marker": self.report(dict(self.manifest, pool_policy="dispatch-identified-table-pointer-v1")),
            "calls": self.report(changed),
            "pool-schema fingerprint": self.report(fingerprint=frame.fingerprint(
                BASE, self.body, dict(self.manifest, pool_policy="dispatch-identified-table-pointer-v1"))),
            "no stack line": self.report(stack=False),
            "pool summary": self.report(summary=frame.SUMMARY),
            "second schema": self.report() + f"\n* verification: `{frame.FIXED_SCHEMA}`",
        }
        for name, report in variants.items():
            with self.subTest(name=name):
                self.assertFalse(self.valid(report))

    def test_relabelled_reports_reject_both_ways(self):
        v1 = without(self.manifest, "stack_policy")
        functions = dict(self.manifest, function_policy="canonical-function-literals-v1", functions=[])
        relabelled = {
            "as u16-scalars-v1": self.report(
                v1, evidence.switch_u16_scalar_fingerprint(BASE, self.body, v1),
                schema=evidence.SWITCH_U16_SCALAR_SCHEMA, summary=evidence.SWITCH_U16_SCALAR_SUMMARY,
                stack=False),
            "as u16-scalars-v1 keeping the marker": self.report(
                fingerprint=evidence.switch_u16_scalar_fingerprint(BASE, self.body, self.manifest),
                schema=evidence.SWITCH_U16_SCALAR_SCHEMA, summary=evidence.SWITCH_U16_SCALAR_SUMMARY),
            "as u16-scalars-frame-v1": self.report(schema=frame.SCHEMA, summary=frame.SUMMARY),
            "as functions-frame-v1": self.report(
                functions, evidence.switch_function_u16_scalar_fingerprint(BASE, self.body, functions),
                schema=FUNCTIONS_FRAME_SCHEMA, summary=evidence.SWITCH_FUNCTION_FRAME_U16_SCALAR_SUMMARY),
            "v1 as fixed frame": self.report(v1, frame.fingerprint(BASE, self.body, v1)),
        }
        for name, report in relabelled.items():
            with self.subTest(name=name):
                self.assertFalse(self.valid(report))
        self.assertNotEqual(frame.fingerprint(BASE, self.body, self.manifest),
                            evidence.switch_u16_scalar_fingerprint(BASE, self.body, self.manifest))
        # The fingerprint is domain-separated by the fixed schema itself.
        import hashlib
        digest = hashlib.sha256()
        for payload in (frame.FIXED_SCHEMA.encode("ascii"), BASE.to_bytes(4, "little"), bytes(self.body),
                        evidence.switch_manifest(self.manifest).encode("ascii")):
            digest.update(len(payload).to_bytes(8, "little"))
            digest.update(payload)
        self.assertEqual(frame.fingerprint(BASE, self.body, self.manifest), digest.hexdigest())
        self.assertEqual(frame.FIXED_SCHEMA, "elf-symbol-thumb-switch-data-u16-scalars-fixed-frame-v1")

    def test_tampered_bytes_reject(self):
        altered = bytearray(self.rom_path.read_bytes())
        altered[len(self.body) - 1] ^= 1
        self.rom_path.write_bytes(altered)
        self.assertFalse(self.valid(self.report()))

    def test_rebuild_and_status_forward_the_selector(self):
        import rebuild
        import status
        self.assertEqual(rebuild.saved_profile_arguments(report_fixtures.carried(self.report(), self.root, BASE), self.root, BASE),
                         ["--switch-data-profile", frame.FIXED_SELECTOR])
        (self.root / "config").mkdir()
        (self.root / "config/functions.json").write_bytes(self.functions)
        (self.root / "config/data_symbols.json").write_bytes(self.objects)
        (self.root / "docs/match").mkdir(parents=True)
        (self.root / "docs/match/08000000.md").write_text(self.report())
        output = (f"extent    {len(self.body)} bytes (complete ELF symbol)\n"
                  "verdict MATCH - byte identical\n")

        def invoke(command, **kwargs):
            self.assertEqual(command.count("--switch-data-profile"), 1)
            self.assertEqual(command[command.index("--switch-data-profile") + 1], frame.FIXED_SELECTOR)
            return subprocess.CompletedProcess(command, 0, output, "")
        with mock.patch.object(status.subprocess, "run", side_effect=invoke) as native:
            result = status.collect(str(self.root), True)
            self.assertEqual(result[1], 1)
            native.assert_called_once()


class WideScalarPremiseTests(unittest.TestCase):
    """The printed premise covers what `admits` takes, not only constants of 0x10000000 or more."""

    ROM_OBJECT, CONSTANT = 0x08200000, 0x08000000
    WORD = ROM_OBJECT + CONSTANT
    # the line reports carried before the premise named this case
    OLD_LINE = ("* switch wide scalar premise: each `wide_scalars` word is an exact number of at "
                "least 0x10000000; GBATEK lists 10000000-FFFFFFFF as unused memory whose reads "
                "return the prefetched opcode, so the word is no mapped address; an object address "
                "offset by 0x10000000 or more, which agbcc would fold into one such word, is assumed "
                "absent from the source")

    setUp = ReportTests.setUp
    report = ReportTests.report
    valid = ReportTests.valid

    def use(self, word):
        self.body, _, self.manifest, mapping = fixture(wide=(word,))
        self.assertEqual(json.dumps(mapping).encode(), self.functions)
        self.rom_path.write_bytes(rom_image(self.body))

    def switch_replay(self, report):
        return evidence.switch_report_matches(report.splitlines(), self.root, BASE, data_profile=True)

    def test_the_rule_takes_a_rom_object_plus_a_constant_below_its_bound(self):
        self.assertEqual(self.WORD, 0x10200000)
        self.assertLess(self.CONSTANT, wide_scalars.LOW)
        self.assertTrue(wide_scalars.admits(self.WORD))
        body, _, manifest, mapping = fixture(wide=(self.WORD,))
        verify(body, manifest, mapping)
        self.assertEqual([value for _, value in manifest["wide_scalars"]], [self.WORD])

    def test_the_premise_names_that_case(self):
        self.assertNotIn("offset by 0x10000000 or more", wide_scalars.PREMISE)
        self.assertIn("the hard-coded value of an address plus or minus a constant whose 32-bit sum is "
                      "0x10000000 or more (a ROM object plus 0x08000000 is one)", wide_scalars.PREMISE)
        self.assertIn(f"0x{wide_scalars.LOW:08X} or more (a ROM object plus 0x{self.CONSTANT:08X}",
                      wide_scalars.PREMISE)

    def test_the_word_reports_under_the_new_line_and_the_old_line_refuses(self):
        line = wide_scalars.report_line()
        self.assertTrue(self.OLD_LINE.startswith(wide_scalars.REPORT_PREFIX))
        self.assertNotEqual(self.OLD_LINE, line)
        for word in (self.WORD, HALF):
            with self.subTest(word=hex(word)):
                self.use(word)
                report = self.report()
                self.assertEqual(report.count(line + "\n"), 1)
                self.assertTrue(self.valid(report))
                self.assertTrue(self.switch_replay(report))
                for premise in ([self.OLD_LINE], [self.OLD_LINE, line], [line, self.OLD_LINE], [line, line]):
                    refused = self.report(premise=premise)
                    self.assertFalse(self.valid(refused))
                    # the premise check of the switch replay itself, apart from the whole-text comparison
                    self.assertFalse(self.switch_replay(refused))

    def test_the_line_refuses_in_a_report_without_the_policy(self):
        self.body, _, self.manifest, mapping = fixture()
        self.assertNotIn("wide_scalar_policy", self.manifest)
        self.functions = json.dumps(mapping).encode()
        self.rom_path.write_bytes(rom_image(self.body))
        with mock.patch.object(evidence, "mapping_snapshot", return_value=self.functions):
            self.assertTrue(self.switch_replay(self.report()))
            for premise in ([wide_scalars.report_line()], [self.OLD_LINE]):
                self.assertFalse(self.switch_replay(self.report(premise=premise)))


if __name__ == "__main__":
    unittest.main()
