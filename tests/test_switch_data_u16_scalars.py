"""Synthetic, compiler-free coverage of explicitly selected u16 scalar pools."""

import copy
import hashlib
import json
import os
from pathlib import Path
import struct
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
POLICY = "complete-reachable-u16-scalar-words-v1"
SCHEMA = "elf-symbol-thumb-switch-data-u16-scalars-v1"


def fixture(*, call=True, two_scalars=False, interleaved_scalar=False):
    body, labels, fixups = bytearray(), {}, []

    def half(value):
        body.extend(struct.pack("<H", value))

    def label(name):
        labels[name] = len(body)

    def emit(kind, name, register=0):
        fixups.append((len(body), kind, name, register))
        body.extend(bytes(4 if kind == "word" else 2))

    def align():
        while len(body) % 4:
            half(0)

    if call:
        half(0xB500)  # push {lr}
    emit("ldr", "object0", 2)
    label("comparison")
    half(0x2801)
    label("guard")
    emit("bhi", "default")
    label("dispatch")
    half(0x0080)
    emit("ldr", "pointer", 1)
    half(0x1840)
    half(0x6800)
    half(0x4687)
    align()
    label("object0")
    body.extend(struct.pack("<I", OBJECT))
    label("pointer")
    emit("word", "table")
    label("table")
    emit("word", "case0")
    emit("word", "case1")
    for index in range(2):
        label(f"case{index}")
        if index == 0:
            emit("ldr", "object1", 1)
        else:
            half(0x1C11)  # adds r1,r2,#0: cached typed object
        emit("ldr", f"scalar{index if two_scalars else 0}")
        half(0x1809)  # adds r1,r1,r0: actual numeric member offset
        half(0x7808)  # ldrb r0,[r1]
        label(f"skip{index}")
        emit("b", "done")
        if index == 0:
            align()
            label("object1")
            body.extend(struct.pack("<I", OBJECT + 4))
            if interleaved_scalar:
                label("scalar0")
                body.extend(struct.pack("<I", 0x219E))
    label("default")
    half(0x2000)
    label("done")
    calls = []
    if call:
        displacement = CALLEE - (BASE + len(body) + 4)
        calls.append([len(body), "func_08001000"])
        half(0xF000 | ((displacement >> 12) & 0x7FF))
        half(0xF800 | ((displacement >> 1) & 0x7FF))
        half(0xBC02)
        half(0x4708)
    else:
        half(0x4770)
    align()
    for index in range(2 if two_scalars else 1):
        if f"scalar{index}" in labels:
            continue
        label(f"scalar{index}")
        body.extend(struct.pack("<I", 0x219E + index))
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
            halfword = (0xD800 | (displacement & 0xFF)) if kind == "bhi" else (
                0xE000 | (displacement & 0x7FF))
            struct.pack_into("<H", body, offset, halfword)
    relocations = [[labels["pointer"], labels["table"]],
                   [labels["table"], labels["case0"]],
                   [labels["table"] + 4, labels["case1"]]]
    descriptor = {name: labels[name] for name in (
        "comparison", "guard", "dispatch", "default", "table")}
    descriptor.update(literal=labels["pointer"], bound=1, relocations=relocations)
    manifest = {"calls": calls, "switch": descriptor,
                "data": [[labels["object0"], "g_object", 0],
                         [labels["object1"], "g_object", 4]],
                "data_policy": "complete-reachable-object-words-v1",
                "scalar_policy": POLICY,
                "scalars": [[labels[f"scalar{i}"], 0x219E + i]
                            for i in range(2 if two_scalars else 1)]}
    mapping = [{"rom": f"0x{BASE:08X}", "end": f"0x{BASE + len(body):08X}", "mode": "thumb"},
               {"rom": f"0x{CALLEE:08X}", "end": f"0x{CALLEE + 2:08X}", "mode": "thumb"}]
    return body, labels, manifest, mapping


def verify(body, manifest, mapping, *, rom=None, objects=None):
    if rom is None:
        rom = bytes(body).ljust(CALLEE - BASE, b"\0") + b"\x70\x47"
    objects = {"g_object": f"0x{OBJECT:08X}"} if objects is None else objects
    return match.verify_switches(bytes(body), BASE, rom, json.dumps(mapping).encode(),
                                 manifest, data_mapping=json.dumps(objects).encode())


class RegressionTests(unittest.TestCase):
    def test_explicit_u16_scalar_member_offset(self):
        body, _, manifest, mapping = fixture()
        _, summary = verify(body, manifest, mapping)
        self.assertEqual(summary, match.CALL_SUMMARY)

    def test_two_distinct_scalar_words_and_leaf_return(self):
        body, _, manifest, mapping = fixture(call=False, two_scalars=True)
        instructions, summary = verify(body, manifest, mapping)
        self.assertEqual(summary, "closed leaf CFG")
        objects = {offset: (name, OBJECT + addend)
                   for offset, name, addend in manifest["data"]}
        self.assertEqual(match.switch_u16_scalar_records(
            body, BASE, instructions, manifest["switch"], objects), manifest["scalars"])

    def test_scalar_word_between_forward_cases(self):
        body, labels, manifest, mapping = fixture(interleaved_scalar=True, two_scalars=True)
        self.assertLess(labels["case0"], labels["scalar0"])
        self.assertLess(labels["scalar0"], labels["case1"])
        _, summary = verify(body, manifest, mapping)
        self.assertEqual(summary, match.CALL_SUMMARY)

    def test_zero_and_u16_maximum_remain_literal_values(self):
        for value in (0, 0xFFFF):
            with self.subTest(value=value):
                body, _, manifest, mapping = fixture(call=False)
                offset = manifest["scalars"][0][0]
                struct.pack_into("<I", body, offset, value)
                manifest["scalars"][0][1] = value
                verify(body, manifest, mapping)

    def test_default_object_policy_still_rejects_extra_numeric_word(self):
        body, _, manifest, mapping = fixture()
        manifest.pop("scalar_policy")
        manifest.pop("scalars")
        with self.assertRaisesRegex(ValueError, "complete switch-data literal-word coverage"):
            verify(body, manifest, mapping)

    def test_policy_is_required_and_versioned(self):
        for field, value in (("scalar_policy", None), ("scalar_policy", "other-policy"),
                             ("data_policy", "other-policy"), ("extra", 0)):
            with self.subTest(field=field, value=value):
                body, _, manifest, mapping = fixture()
                if value is None:
                    manifest.pop(field)
                else:
                    manifest[field] = value
                with self.assertRaisesRegex(ValueError, "invalid switch manifest"):
                    verify(body, manifest, mapping)

    def test_scalar_manifest_must_be_finite_ordered_and_exact(self):
        mutations = [None, {}, [], [[True, 1]], [[-4, 1]], [[0, 1]], [[1, 1]],
                     [[0x10000, 1]], [[1.0, 1]], [["64", 1]], [[64]], [[64, 1, 2]]]
        body, _, manifest, mapping = fixture(two_scalars=True)
        mutations.extend([manifest["scalars"] * 2, manifest["scalars"][::-1],
                          manifest["scalars"][:1]])
        for records in mutations:
            with self.subTest(records=records):
                changed = copy.deepcopy(manifest)
                changed["scalars"] = records
                with self.assertRaises(ValueError):
                    verify(body, changed, mapping)

    def test_scalar_values_exclude_full_addresses_and_non_u16_values(self):
        for value in (True, -1, 0x10000, OBJECT, CALLEE, 1.5, "8606"):
            with self.subTest(value=value):
                body, _, manifest, mapping = fixture()
                offset = manifest["scalars"][0][0]
                if type(value) is int and 0 <= value <= 0xFFFFFFFF:
                    struct.pack_into("<I", body, offset, value)
                manifest["scalars"][0][1] = value
                with self.assertRaises(ValueError):
                    verify(body, manifest, mapping)

    def test_scalar_record_cannot_describe_an_unreached_trailing_word(self):
        body, _, manifest, mapping = fixture()
        manifest["scalars"].append([len(body), 3])
        body.extend(struct.pack("<I", 3))
        mapping[0]["end"] = f"0x{BASE + len(body):08X}"
        with self.assertRaises(ValueError):
            verify(body, manifest, mapping)

    def test_scalar_cannot_replace_object_table_code_or_call_binding(self):
        body, labels, manifest, mapping = fixture()
        for offset in (labels["object1"], labels["table"], labels["case0"],
                       manifest["calls"][0][0], labels["scalar0"] + 2):
            with self.subTest(offset=offset):
                changed = copy.deepcopy(manifest)
                changed["scalars"] = [[offset, 0]]
                with self.assertRaises(ValueError):
                    verify(body, changed, mapping)

    def test_declared_scalar_value_cannot_differ_from_full_word(self):
        body, _, manifest, mapping = fixture()
        manifest["scalars"][0][1] ^= 1
        with self.assertRaises(ValueError):
            verify(body, manifest, mapping)

    def test_branch_cannot_enter_referenced_scalar_word(self):
        body, labels, manifest, mapping = fixture()
        offset = labels["skip0"]
        displacement = (labels["scalar0"] - offset - 4) // 2
        struct.pack_into("<H", body, offset, 0xE000 | (displacement & 0x7FF))
        with self.assertRaises(ValueError):
            verify(body, manifest, mapping)

    def test_guard_and_table_cannot_be_rebound(self):
        body, labels, manifest, mapping = fixture()
        changed = bytearray(body)
        struct.pack_into("<H", changed, labels["comparison"], 0x2802)
        with self.assertRaises(ValueError):
            verify(changed, manifest, mapping)
        changed = copy.deepcopy(manifest)
        changed["switch"]["relocations"][1][1] = labels["scalar0"]
        with self.assertRaises(ValueError):
            verify(body, changed, mapping)

    def test_object_and_call_bindings_remain_required(self):
        for field in ("data", "calls"):
            with self.subTest(field=field):
                body, _, manifest, mapping = fixture()
                manifest[field].pop()
                with self.assertRaises(ValueError):
                    verify(body, manifest, mapping)
        body, _, manifest, mapping = fixture()
        with self.assertRaises(ValueError):
            verify(body, manifest, mapping, objects={"g_object": hex(OBJECT + 4)})

    def test_complete_rom_and_exact_thumb_span_remain_required(self):
        body, _, manifest, mapping = fixture()
        altered = bytearray(body)
        altered[-1] ^= 1
        with self.assertRaisesRegex(ValueError, "differs from the ROM"):
            verify(body, manifest, mapping, rom=altered)
        for change in ("short", "long", "arm", "duplicate"):
            with self.subTest(change=change):
                entries = copy.deepcopy(mapping)
                if change == "duplicate":
                    entries.append(entries[0].copy())
                elif change == "arm":
                    entries[0]["mode"] = "arm"
                else:
                    entries[0]["end"] = hex(BASE + len(body) + (-2 if change == "short" else 2))
                with self.assertRaisesRegex(ValueError, "exact mapped Thumb span"):
                    verify(body, manifest, entries)


class ConfigurationTests(unittest.TestCase):
    def args(self):
        return SimpleNamespace(
            switch_data_profile=evidence.SWITCH_U16_SCALAR_SELECTOR,
            mode="thumb", control_flow_profile="ordinary", signed_quotient_profile=None,
            signed_runtime_profile=None, addressed_signed_runtime_profile=None,
            software_double_profile=None, software_double_remainder_profile=None,
            function_address_profile=None, switch_profile=None, owner_runtime_profile=None,
            cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
            objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)

    def test_explicit_fixed_configuration(self):
        match.switch_u16_scalar_configuration(self.args())

    def test_no_selector_preserves_existing_configuration_path(self):
        args = self.args()
        args.switch_data_profile = None
        args.mode = "arm"
        match.switch_u16_scalar_configuration(args)

    def test_other_selectors_mode_flags_and_tools_are_rejected(self):
        for field in ("signed_quotient_profile", "signed_runtime_profile",
                      "addressed_signed_runtime_profile", "software_double_profile",
                      "software_double_remainder_profile", "function_address_profile",
                      "switch_profile", "owner_runtime_profile", "mode", "control_flow_profile",
                      "cc", "cpp", "assembler", "objcopy", "linker", "flags", "switch_data_profile"):
            with self.subTest(field=field):
                args = self.args()
                setattr(args, field, "other")
                with self.assertRaisesRegex(ValueError, "isolated explicit selector"):
                    match.switch_u16_scalar_configuration(args)


class ReportTests(unittest.TestCase):
    def setUp(self):
        self.body, _, self.manifest, self.mapping = fixture(call=False)
        scratch = TASK / "build"
        scratch.mkdir(exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="switch_u16_scalars_", dir=scratch)
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        (self.root / "src").mkdir()
        (self.root / "include").mkdir()
        (self.root / "src/08000000.c").write_text("unsigned func_08000000(unsigned x);\n")
        (self.root / "include/global.h").write_text("typedef unsigned int u32;\n")
        (self.root / "src/local.h").write_text("typedef unsigned char u8;\n")
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

    def report(self):
        return "\n".join([
            f"* verification: `{SCHEMA}`",
            f"* source SHA-256: `{self.source}`",
            f"* mapping SHA-256: `{evidence.mapping_fingerprint(self.functions)}`",
            f"* data symbols SHA-256: `{evidence.mapping_fingerprint(self.objects)}`",
            f"* switches: {evidence.SWITCH_U16_SCALAR_SUMMARY}",
            "* source plausibility: plausible", "* relocations: none",
            "* verified extent: complete ELF function symbol, including literal pools",
            f"* compiled : `{self.body.hex()}`",
            f"* switch manifest: `{evidence.switch_manifest(self.manifest)}`",
            "* control flow: closed leaf CFG",
            f"* ROM bytes: `{self.body.hex()}` ({len(self.body)} bytes)",
            f"**MATCH - byte identical** - {len(self.body)}/{len(self.body)} bytes",
            f"* switch proof SHA-256: `{evidence.switch_u16_scalar_fingerprint(BASE, self.body, self.manifest)}`"])

    def valid(self, report):
        return evidence.switch_report_matches(report.splitlines(), self.root, BASE, data_profile=True)

    def test_separate_schema_manifest_and_fingerprint_revalidate(self):
        report = self.report()
        self.assertTrue(self.valid(report))
        with mock.patch.object(evidence.empty_body, "has_empty_body", return_value=False):
            self.assertTrue(evidence.report_matches(report, self.root, BASE))

    def test_source_and_both_header_locations_are_bound(self):
        report = self.report()
        for name in ("src/08000000.c", "src/local.h", "include/global.h"):
            path = self.root / name
            original = path.read_bytes()
            path.write_bytes(original + b"\n")
            self.assertFalse(self.valid(report))
            path.write_bytes(original)

    def test_mapping_data_and_full_rom_are_bound(self):
        report = self.report()
        for name, value in (("mapping_snapshot", b"[]"), ("data_snapshot", b"{}")):
            with self.subTest(name=name), mock.patch.object(evidence, name, return_value=value):
                self.assertFalse(self.valid(report))
        changed = bytearray(self.body)
        changed[-1] ^= 1
        self.rom_path.write_bytes(changed)
        self.assertFalse(self.valid(report))

    def test_scalar_policy_and_record_must_survive_revalidation(self):
        for field in ("scalar_policy", "scalars", "data_policy"):
            with self.subTest(field=field):
                saved = self.manifest.pop(field)
                self.assertFalse(self.valid(self.report()))
                self.manifest[field] = saved

    def test_old_schema_or_fingerprint_cannot_claim_new_policy(self):
        report = self.report()
        for schema in (evidence.SWITCH_DATA_SCHEMA, evidence.SWITCH_MULTIPLE_DATA_SCHEMA):
            with self.subTest(schema=schema):
                self.assertFalse(self.valid(report.replace(SCHEMA, schema)))
        old = evidence.switch_multiple_data_fingerprint(BASE, self.body, self.manifest)
        new = evidence.switch_u16_scalar_fingerprint(BASE, self.body, self.manifest)
        self.assertNotEqual(old, new)
        self.assertFalse(self.valid(report.replace(new, old)))

    def test_fingerprint_binds_address_complete_bytes_and_scalar_manifest(self):
        original = evidence.switch_u16_scalar_fingerprint(BASE, self.body, self.manifest)
        changed = copy.deepcopy(self.manifest)
        changed["scalars"][0][1] ^= 1
        for address, body, manifest in ((BASE + 2, self.body, self.manifest),
                                        (BASE, self.body + b"\0", self.manifest),
                                        (BASE, self.body, changed)):
            self.assertNotEqual(original, evidence.switch_u16_scalar_fingerprint(address, body, manifest))

    def test_duplicate_markers_extra_profiles_and_noncanonical_manifest_rejected(self):
        report = self.report()
        for suffix in (f"\n* verification: `{SCHEMA}`", "\n* stack frame: 4 bytes",
                       "\n* function addresses: arbitrary"):
            with self.subTest(suffix=suffix):
                self.assertFalse(self.valid(report + suffix))
        self.assertFalse(self.valid(report.replace(evidence.switch_manifest(self.manifest),
                                                  json.dumps(self.manifest))))
        duplicate = evidence.switch_manifest(self.manifest).replace(
            '"scalar_policy":', '"scalar_policy":"other","scalar_policy":')
        self.assertFalse(self.valid(report.replace(evidence.switch_manifest(self.manifest), duplicate)))


if __name__ == "__main__":
    unittest.main()
