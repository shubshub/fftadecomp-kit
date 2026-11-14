"""Synthetic, compiler-free coverage of dispatch-identified switch pools (u16-scalars-v2)."""

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

assert Path(match.__file__).resolve() == TASK / "tools/match.py"
assert Path(evidence.__file__).resolve() == TASK / "tools/match_evidence.py"

BASE = 0x08000000
OBJECT = 0x02001000
CALLEE = BASE + 0x1000
SCALAR = 0x2FC1
SCHEMA = "elf-symbol-thumb-switch-data-u16-scalars-v2"
POOL_POLICY = "dispatch-identified-table-pointer-v1"


def fixture(pool=("object", "scalar"), *, call=True, pointer_reader=False, scalar=SCALAR,
            late=False):
    """A guarded table whose pointer follows `pool` interposed literal words.

    `object` and `scalar` words are loaded before the guard (the scalar is the
    case bias); `unread` is a word no instruction loads. `late` adds an object
    and a scalar word after the code, read by the cases.
    """
    body, labels, fixups = bytearray(), {}, []

    def half(value):
        body.extend(struct.pack("<H", value))

    def label(name):
        labels[name] = len(body)

    def emit(kind, name, register=0):
        fixups.append((len(body), kind, name, register))
        body.extend(bytes(4 if kind == "word" else 2))

    if call:
        half(0xB500)  # push {lr}
    if pointer_reader:
        emit("ldr", "pointer", 1)
    for index, kind in enumerate(pool):
        if kind != "unread":
            emit("ldr", f"pool{index}", 3 if kind == "scalar" else 2)
    if "scalar" in pool:
        half(0x18C0)  # adds r0,r0,r3: numeric bias before the bound check
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
    for index, kind in enumerate(pool):
        label(f"pool{index}")
        body.extend(struct.pack("<I", OBJECT if kind == "object" else scalar))
    label("pointer")
    emit("word", "table")
    label("table")
    emit("word", "case0")
    emit("word", "case1")
    label("case0")
    if late:
        emit("ldr", "late_object", 1)
    half(0x2001)  # movs r0,#1
    label("skip0")
    emit("b", "done")
    label("case1")
    if late:
        emit("ldr", "late_scalar", 1)
    half(0x2002)  # movs r0,#2
    label("skip1")
    emit("b", "done")
    label("default")
    half(0x2000)  # movs r0,#0
    label("done")
    calls = []
    if call:
        displacement = CALLEE - (BASE + len(body) + 4)
        calls.append([len(body), "func_08001000"])
        half(0xF000 | ((displacement >> 12) & 0x7FF))
        half(0xF800 | ((displacement >> 1) & 0x7FF))
        half(0xBC02)  # pop {r1}
        half(0x4708)  # bx r1
    else:
        half(0x4770)  # bx lr
    while len(body) % 4:
        half(0)
    if late:
        label("late_object")
        body.extend(struct.pack("<I", OBJECT + 8))
        label("late_scalar")
        body.extend(struct.pack("<I", 0x444))
    for offset, kind, name, register in fixups:
        target = labels[name]
        if kind == "word":
            struct.pack_into("<I", body, offset, BASE + target)
        elif kind == "ldr":
            distance = target - ((offset + 4) & ~3)
            assert 0 <= distance <= 1020 and distance % 4 == 0
            struct.pack_into("<H", body, offset, 0x4800 | register << 8 | distance // 4)
        else:
            displacement = (target - offset - 4) // 2
            struct.pack_into("<H", body, offset, (0xD800 | (displacement & 0xFF)) if kind == "bhi"
                             else (0xE000 | (displacement & 0x7FF)))
    relocations = [[labels["pointer"], labels["table"]],
                   [labels["table"], labels["case0"]],
                   [labels["table"] + 4, labels["case1"]]]
    descriptor = {name: labels[name] for name in (
        "comparison", "guard", "dispatch", "default", "table")}
    descriptor.update(literal=labels["pointer"], bound=1, relocations=relocations)
    manifest = {"calls": calls, "switch": descriptor,
                "data": [[labels[f"pool{index}"], "g_object", 0]
                         for index, kind in enumerate(pool) if kind == "object"] +
                        ([[labels["late_object"], "g_object", 8]] if late else []),
                "data_policy": "complete-reachable-object-words-v1",
                "scalar_policy": "complete-reachable-u16-scalar-words-v1",
                "scalars": [[labels[f"pool{index}"], scalar]
                            for index, kind in enumerate(pool) if kind == "scalar"] +
                           ([[labels["late_scalar"], 0x444]] if late else []),
                "pool_policy": POOL_POLICY}
    mapping = [{"rom": f"0x{BASE:08X}", "end": f"0x{BASE + len(body):08X}", "mode": "thumb"},
               {"rom": f"0x{CALLEE:08X}", "end": f"0x{CALLEE + 2:08X}", "mode": "thumb"}]
    return body, labels, manifest, mapping


def verify(body, manifest, mapping, *, rom=None):
    if rom is None:
        rom = bytes(body).ljust(CALLEE - BASE, b"\0") + b"\x70\x47"
    objects = json.dumps({"g_object": f"0x{OBJECT:08X}"}).encode()
    return match.verify_switches(bytes(body), BASE, rom, json.dumps(mapping).encode(),
                                 manifest, data_mapping=objects)


def relocations(manifest):
    return dict(map(tuple, manifest["switch"]["relocations"]))


class LayoutTests(unittest.TestCase):
    def test_pointer_is_found_by_its_dispatch_load_for_any_pool_size(self):
        for pool in (("scalar",), ("object", "scalar"), ("object", "object", "scalar"),
                     ("object",) * 7):
            with self.subTest(pool=pool):
                body, _, manifest, _ = fixture(pool)
                self.assertEqual(match.switch_layout(bytes(body), BASE, relocations(manifest),
                                                     interposed_pool=True), manifest["switch"])

    def test_fixed_positions_still_refuse_interposed_numeric_words(self):
        body, labels, manifest, _ = fixture(("object", "scalar"))
        with self.assertRaisesRegex(ValueError, "five-op dispatch"):
            match.switch_layout(bytes(body), BASE, relocations(manifest))
        objects = {labels["pool0"]: ("g_object", OBJECT)}
        with self.assertRaisesRegex(ValueError, "five-op dispatch"):
            match.switch_layout(bytes(body), BASE, relocations(manifest), objects)

    def test_opt_in_is_boolean_and_isolated(self):
        body, _, manifest, _ = fixture()
        for kwargs in ({"interposed_pool": 1}, {"interposed_pool": True, "interposed_words": 5}):
            with self.subTest(kwargs=kwargs), self.assertRaises(ValueError):
                match.switch_layout(bytes(body), BASE, relocations(manifest), **kwargs)
        with self.assertRaisesRegex(ValueError, "isolated switch-data"):
            match.selected_switch_layout(bytes(body), BASE, relocations(manifest),
                                         allow_switch_constants=True, interposed_pool=True)
        with self.assertRaisesRegex(ValueError, "isolated switch-data"):
            match.check_switch_pool_opt_in(True, False)
        with self.assertRaisesRegex(ValueError, "isolated switch-data context"):
            match.verify_leaf_instructions(bytes(body), BASE, True, {},
                                           switch_relocations=relocations(manifest),
                                           switch_interposed_pool=True)

    def test_guard_alignment_and_table_remain_exact(self):
        body, labels, manifest, _ = fixture()
        changed = bytearray(body)
        struct.pack_into("<H", changed, labels["comparison"], 0x2802)  # cmp r0,#2
        with self.assertRaises(ValueError):
            match.switch_layout(bytes(changed), BASE, relocations(manifest), interposed_pool=True)
        changed = bytearray(body)
        alignment = labels["dispatch"] + 10
        self.assertLess(alignment, labels["pool0"])
        changed[alignment] = 1
        with self.assertRaises(ValueError):
            match.switch_layout(bytes(changed), BASE, relocations(manifest), interposed_pool=True)
        truncated = relocations(manifest)
        truncated.pop(labels["table"] + 4)
        with self.assertRaises(ValueError):
            match.switch_layout(bytes(body), BASE, truncated, interposed_pool=True)


class VerificationTests(unittest.TestCase):
    def test_numeric_bias_word_before_pointer(self):
        for call in (False, True):
            with self.subTest(call=call):
                body, _, manifest, mapping = fixture(("object", "scalar"), call=call)
                _, summary = verify(body, manifest, mapping)
                self.assertEqual(summary, match.CALL_SUMMARY if call else "closed leaf CFG")

    def test_objects_and_scalar_mixed_in_pool(self):
        body, labels, manifest, mapping = fixture(("object", "object", "scalar"), late=True)
        self.assertEqual(labels["pointer"] - labels["pool0"], 12)
        instructions, _ = verify(body, manifest, mapping)
        objects = {offset: (name, OBJECT + addend) for offset, name, addend in manifest["data"]}
        self.assertEqual(match.switch_u16_scalar_records(
            body, BASE, instructions, manifest["switch"], objects), manifest["scalars"])

    def test_v1_policy_still_refuses_the_same_bytes(self):
        body, _, manifest, mapping = fixture()
        manifest.pop("pool_policy")
        with self.assertRaisesRegex(ValueError, "five-op dispatch"):
            verify(body, manifest, mapping)

    def test_pool_policy_is_exact_and_requires_u16_scalar_policy(self):
        body, _, manifest, mapping = fixture()
        changed = dict(manifest, pool_policy="other-policy")
        with self.assertRaisesRegex(ValueError, "canonical policy marker"):
            verify(body, changed, mapping)
        changed = copy.deepcopy(manifest)
        for field in ("scalar_policy", "scalars"):
            changed.pop(field)
        with self.assertRaisesRegex(ValueError, "invalid switch manifest"):
            verify(body, changed, mapping)

    def test_every_interposed_word_must_be_bound(self):
        for field in ("data", "scalars"):
            with self.subTest(field=field):
                body, _, manifest, mapping = fixture(late=True)
                manifest[field].pop(0)
                with self.assertRaisesRegex(ValueError, "literal-word coverage|only u16"):
                    verify(body, manifest, mapping)

    def test_unread_interposed_word_is_refused(self):
        body, _, manifest, mapping = fixture(("object", "scalar", "unread"))
        with self.assertRaisesRegex(ValueError, "typed objects or u16 scalars"):
            verify(body, manifest, mapping)

    def test_interposed_word_cannot_claim_unbounded_numeric_category(self):
        body, _, manifest, mapping = fixture(scalar=0xFFFFFE93)
        with self.assertRaises(ValueError):
            verify(body, manifest, mapping)

    def test_table_pointer_has_no_other_reader(self):
        body, _, manifest, mapping = fixture(pointer_reader=True)
        with self.assertRaisesRegex(ValueError, "read only by its dispatch load"):
            verify(body, manifest, mapping)

    def test_zero_interposed_words_belong_to_v1(self):
        body, _, manifest, mapping = fixture((), late=True)
        with self.assertRaisesRegex(ValueError, "at least one interposed word"):
            verify(body, manifest, mapping)
        manifest.pop("pool_policy")
        verify(body, manifest, mapping)

    def test_control_flow_cannot_enter_the_pool(self):
        body, labels, manifest, mapping = fixture()
        displacement = (labels["pool1"] - labels["skip1"] - 4) // 2
        struct.pack_into("<H", body, labels["skip1"], 0xE000 | (displacement & 0x7FF))
        with self.assertRaises(ValueError):
            verify(body, manifest, mapping)

    def test_guard_cannot_be_rebound_or_bypassed(self):
        body, labels, manifest, mapping = fixture()
        changed = copy.deepcopy(manifest)
        changed["switch"]["comparison"] += 2
        with self.assertRaises(ValueError):
            verify(body, changed, mapping)
        changed = bytearray(body)
        displacement = (labels["dispatch"] - labels["skip0"] - 4) // 2
        struct.pack_into("<H", changed, labels["skip0"], 0xE000 | (displacement & 0x7FF))
        with self.assertRaises(ValueError):
            verify(changed, manifest, mapping)


class ConfigurationTests(unittest.TestCase):
    def test_v2_selector_uses_the_isolated_fixed_configuration(self):
        args = SimpleNamespace(
            switch_data_profile=evidence.SWITCH_POOL_U16_SCALAR_SELECTOR,
            mode="thumb", control_flow_profile="ordinary", signed_quotient_profile=None,
            signed_runtime_profile=None, addressed_signed_runtime_profile=None,
            unsigned_runtime_profile=None, software_double_profile=None,
            software_double_remainder_profile=None, function_address_profile=None,
            switch_profile=None, owner_runtime_profile=None,
            cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
            objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        match.switch_u16_scalar_configuration(args)
        args.switch_profile = "two-constants-frame-v1"
        with self.assertRaisesRegex(ValueError, "isolated explicit selector"):
            match.switch_u16_scalar_configuration(args)


class ReportTests(unittest.TestCase):
    def setUp(self):
        self.body, _, self.manifest, self.mapping = fixture(call=False)
        scratch = TASK / "build"
        scratch.mkdir(exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="switch_pool_u16_", dir=scratch)
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        (self.root / "src").mkdir()
        (self.root / "include").mkdir()
        (self.root / "src/08000000.c").write_text("unsigned func_08000000(unsigned x);\n")
        self.source = evidence.source_fingerprint(self.root, BASE)
        self.functions = json.dumps(self.mapping).encode()
        self.objects = json.dumps({"g_object": f"0x{OBJECT:08X}"}).encode()
        self.rom_path = self.root / "synthetic-image.bin"
        self.rom_path.write_bytes(self.body)
        for name, value in (("mapping_snapshot", self.functions), ("data_snapshot", self.objects),
                            ("report_rom_path", str(self.rom_path))):
            patcher = mock.patch.object(evidence, name, return_value=value)
            patcher.start()
            self.addCleanup(patcher.stop)

    def report(self, manifest=None, fingerprint=None):
        manifest = self.manifest if manifest is None else manifest
        fingerprint = fingerprint or evidence.switch_pool_u16_scalar_fingerprint(
            BASE, self.body, manifest)
        return "\n".join([
            f"* verification: `{SCHEMA}`",
            f"* source SHA-256: `{self.source}`",
            f"* mapping SHA-256: `{evidence.mapping_fingerprint(self.functions)}`",
            f"* data symbols SHA-256: `{evidence.mapping_fingerprint(self.objects)}`",
            f"* switches: {evidence.SWITCH_POOL_U16_SCALAR_SUMMARY}",
            "* source plausibility: plausible", "* relocations: none",
            "* verified extent: complete ELF function symbol, including literal pools",
            f"* compiled : `{self.body.hex()}`",
            f"* switch manifest: `{evidence.switch_manifest(manifest)}`",
            "* control flow: closed leaf CFG",
            f"* ROM bytes: `{self.body.hex()}` ({len(self.body)} bytes)",
            f"**MATCH - byte identical** - {len(self.body)}/{len(self.body)} bytes",
            f"* switch proof SHA-256: `{fingerprint}`"])

    def valid(self, report):
        return evidence.switch_report_matches(report.splitlines(), self.root, BASE, data_profile=True)

    def test_report_revalidates(self):
        report = self.report()
        self.assertTrue(self.valid(report))
        with mock.patch.object(evidence.empty_body, "has_empty_body", return_value=False):
            self.assertTrue(evidence.report_matches(report, self.root, BASE))

    def test_tampered_policy_schema_summary_and_fingerprint_reject(self):
        report = self.report()
        without = copy.deepcopy(self.manifest)
        without.pop("pool_policy")
        v1 = evidence.switch_u16_scalar_fingerprint(BASE, self.body, self.manifest)
        variants = [
            self.report(without),
            self.report(dict(self.manifest, pool_policy="other-policy")),
            report.replace(SCHEMA, evidence.SWITCH_U16_SCALAR_SCHEMA),
            report.replace(evidence.SWITCH_POOL_U16_SCALAR_SUMMARY, evidence.SWITCH_U16_SCALAR_SUMMARY),
            self.report(fingerprint=v1),
            report + f"\n* verification: `{SCHEMA}`",
            report + "\n* stack frame: 4 bytes",
        ]
        self.assertNotEqual(v1, evidence.switch_pool_u16_scalar_fingerprint(BASE, self.body, self.manifest))
        for index, variant in enumerate(variants):
            with self.subTest(index=index):
                self.assertFalse(self.valid(variant))

    def test_v1_report_cannot_be_relabelled_as_v2(self):
        v1 = copy.deepcopy(self.manifest)
        v1.pop("pool_policy")
        report = self.report(v1, evidence.switch_u16_scalar_fingerprint(BASE, self.body, v1)).replace(
            SCHEMA, evidence.SWITCH_U16_SCALAR_SCHEMA).replace(
            evidence.SWITCH_POOL_U16_SCALAR_SUMMARY, evidence.SWITCH_U16_SCALAR_SUMMARY)
        self.assertFalse(self.valid(report))

    def test_tampered_bytes_and_scalar_record_reject(self):
        changed = copy.deepcopy(self.manifest)
        changed["scalars"][0][1] ^= 1
        self.assertFalse(self.valid(self.report(changed)))
        altered = bytearray(self.body)
        altered[-1] ^= 1
        self.rom_path.write_bytes(altered)
        self.assertFalse(self.valid(self.report()))

    def test_rebuild_forwards_the_v2_selector(self):
        import rebuild
        self.enterContext(mock.patch.object(evidence.empty_body, "has_empty_body", return_value=False))
        self.assertEqual(rebuild.saved_profile_arguments(self.report(), self.root, BASE),
                         ["--switch-data-profile", evidence.SWITCH_POOL_U16_SCALAR_SELECTOR])
        with self.assertRaisesRegex(ValueError, "invalid saved profile report"):
            rebuild.saved_profile_arguments(
                self.report().replace(SCHEMA, evidence.SWITCH_U16_SCALAR_SCHEMA), self.root, BASE)
        v1 = copy.deepcopy(self.manifest)
        v1.pop("pool_policy")
        relabelled = self.report(v1, evidence.switch_u16_scalar_fingerprint(BASE, self.body, v1))
        with self.assertRaisesRegex(ValueError, "invalid saved profile report"):
            rebuild.saved_profile_arguments(relabelled, self.root, BASE)

    def test_status_forwards_the_v2_selector(self):
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
            self.assertEqual(command[command.index("--switch-data-profile") + 1],
                             evidence.SWITCH_POOL_U16_SCALAR_SELECTOR)
            return subprocess.CompletedProcess(command, 0, output, "")
        with mock.patch.object(status.subprocess, "run", side_effect=invoke) as native:
            result = status.collect(str(self.root), True)
            self.assertEqual(result[1], 1)
            self.assertEqual(result[4], [])
            native.assert_called_once()


if __name__ == "__main__":
    unittest.main()
