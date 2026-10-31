"""Synthetic, compiler-free checks for complete switch-data literal manifests."""

import copy
import hashlib
import json
from pathlib import Path
import struct
import sys
import tempfile
import unittest
from unittest import mock

sys.dont_write_bytecode = True
TASK = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(TASK / "tools"))
import match
import match_evidence as evidence

BASE = 0x08000000
OBJECT = 0x02001000
CALLEE = BASE + 0x1000
POLICY = "complete-reachable-object-words-v1"


def fixture(count=2, *, before=False, call=False, same_object=False):
    """Build N reachable cases with distinct literal words, optionally one before dispatch."""
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

    def object_word(index):
        label(f"object{index}")
        body.extend(struct.pack("<I", OBJECT if same_object else OBJECT + index * 4))

    if call:
        half(0xB500)  # push {lr}
    if before:
        emit("ldr", "object0", 2)
    label("comparison")
    half(0x2800 | (count - 1))
    label("guard")
    emit("bhi", "default")
    label("dispatch")
    half(0x0080)  # lsls r0,r0,#2
    emit("ldr", "pointer", 1)
    half(0x1840)  # adds r0,r0,r1
    half(0x6800)  # ldr r0,[r0]
    half(0x4687)  # mov pc,r0
    align()
    if before:
        object_word(0)
    label("pointer")
    emit("word", "table")
    label("table")
    for index in range(count):
        emit("word", f"case{index}")
    for index in range(count):
        label(f"case{index}")
        if before and index == 0:
            half(0x1C11)  # adds r1,r2,#0
        else:
            emit("ldr", f"object{index}", 1)
        half(0x7808)  # ldrb r0,[r1]
        label(f"skip{index}")
        emit("b", "done")
        if not (before and index == 0):
            align()
            object_word(index)
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
            assert kind != "bhi" or -128 <= displacement <= 127
            opcode = (0xD800 | (displacement & 0xFF)) if kind == "bhi" else (
                0xE000 | (displacement & 0x7FF))
            struct.pack_into("<H", body, offset, opcode)
    relocations = {labels["pointer"]: labels["table"]}
    relocations.update({labels["table"] + 4 * i: labels[f"case{i}"] for i in range(count)})
    descriptor = {name: labels[name] for name in (
        "comparison", "guard", "dispatch", "default", "table")}
    descriptor.update(literal=labels["pointer"], bound=count - 1,
                      relocations=[list(item) for item in relocations.items()])
    records = [[labels[f"object{i}"], "g_object", 0 if same_object else i * 4]
               for i in range(count)]
    records.sort()
    manifest = {"calls": calls, "data": records, "switch": descriptor, "data_policy": POLICY}
    mapping = [{"rom": f"0x{BASE:08X}", "end": f"0x{BASE + len(body):08X}", "mode": "thumb"},
               {"rom": f"0x{CALLEE:08X}", "end": f"0x{CALLEE + 2:08X}", "mode": "thumb"}]
    return body, labels, manifest, mapping


def verify(body, manifest, mapping, *, data_mapping=None, rom=None):
    objects = {"g_object": f"0x{OBJECT:08X}"} if data_mapping is None else data_mapping
    rom = bytes(body).ljust(CALLEE - BASE, b"\0") + b"\x70\x47" if rom is None else rom
    return match.verify_switches(bytes(body), BASE, rom, json.dumps(mapping).encode(),
                                 manifest, data_mapping=json.dumps(objects).encode())


class PositiveTests(unittest.TestCase):
    def test_multiple_referenced_words_and_same_object_repetitions(self):
        for count, same in ((2, False), (8, False), (9, True)):
            with self.subTest(count=count, same_object=same):
                body, labels, manifest, mapping = fixture(count, same_object=same)
                instructions, summary = verify(body, manifest, mapping)
                self.assertEqual(summary, "closed leaf CFG")
                reached = {item.address for item in instructions}
                self.assertTrue(all(BASE + labels[f"case{i}"] in reached for i in range(count)))

    def test_interposed_before_table_word_plus_other_words_and_direct_call(self):
        for call in (False, True):
            with self.subTest(call=call):
                body, labels, manifest, mapping = fixture(8, before=True, call=call)
                self.assertEqual(labels["object0"], labels["pointer"] - 4)
                _, summary = verify(body, manifest, mapping)
                self.assertEqual(summary, match.CALL_SUMMARY if call else "closed leaf CFG")

    def test_fingerprint_has_separate_domain_and_covers_every_record(self):
        body, _, manifest, _ = fixture(2)
        digest = evidence.switch_multiple_data_fingerprint(BASE, body, manifest)
        self.assertNotEqual(digest, evidence.switch_data_fingerprint(BASE, body, manifest))
        changed = copy.deepcopy(manifest)
        changed["data"][-1][-1] += 4
        self.assertNotEqual(digest, evidence.switch_multiple_data_fingerprint(BASE, body, changed))

    def test_distinct_named_objects_and_signed_addends(self):
        body, _, manifest, mapping = fixture(2)
        manifest["data"][1][1:] = ["g_second", 0]
        verify(body, manifest, mapping, data_mapping={
            "g_object": f"0x{OBJECT:08X}", "g_second": f"0x{OBJECT + 4:08X}"})
        body, _, manifest, mapping = fixture(2)
        for record in manifest["data"]:
            record[2] -= 4
        verify(body, manifest, mapping, data_mapping={"g_object": f"0x{OBJECT + 4:08X}"})


class NegativeTests(unittest.TestCase):
    def test_missing_record_including_reduction_to_one_rejected(self):
        for count in (2, 9):
            body, _, manifest, mapping = fixture(count)
            manifest["data"].pop()
            with self.subTest(count=count), self.assertRaisesRegex(ValueError, "complete.*literal.*coverage"):
                verify(body, manifest, mapping)

    def test_extra_unreferenced_word_rejected(self):
        body, _, manifest, mapping = fixture()
        while len(body) % 4:
            body.extend(bytes(2))
        manifest["data"].append([len(body), "g_object", 0])
        body.extend(struct.pack("<I", OBJECT))
        mapping[0]["end"] = f"0x{BASE + len(body):08X}"
        with self.assertRaisesRegex(ValueError, "not a reachable.*literal-pool load"):
            verify(body, manifest, mapping)

    def test_duplicate_and_unordered_records_rejected(self):
        body, _, manifest, mapping = fixture()
        for records in ([manifest["data"][0]] * 2, list(reversed(manifest["data"]))):
            changed = copy.deepcopy(manifest)
            changed["data"] = records
            with self.subTest(records=records), self.assertRaisesRegex(ValueError, "unique ordered"):
                verify(body, changed, mapping)

    def test_misaligned_incomplete_noninteger_and_overflow_rejected(self):
        body, labels, manifest, mapping = fixture()
        for offset in (labels["object0"] + 2, -4, len(body), True):
            changed = copy.deepcopy(manifest)
            changed["data"][0][0] = offset
            with self.subTest(offset=offset), self.assertRaises(ValueError):
                verify(body, changed, mapping)
        for addend in (True, 0x80000000, -0x80000001, 0x7FFFFFFF):
            changed = copy.deepcopy(manifest)
            changed["data"][-1][-1] = addend
            with self.subTest(addend=addend), self.assertRaises(ValueError):
                verify(body, changed, mapping, data_mapping={"g_object": "0xFFFFFFFF"})

    def test_reachable_reference_required_for_every_word(self):
        body, labels, manifest, mapping = fixture()
        struct.pack_into("<H", body, labels["case1"], 0x2100)
        with self.assertRaisesRegex(ValueError, "not a reachable.*literal-pool load"):
            verify(body, manifest, mapping)

    def test_table_code_and_call_overlap_rejected(self):
        body, labels, manifest, mapping = fixture()
        for offset in (labels["table"], labels["case0"]):
            changed = copy.deepcopy(manifest)
            changed["data"][0][0] = offset
            with self.subTest(offset=offset), self.assertRaises(ValueError):
                verify(body, changed, mapping)
        changed = copy.deepcopy(manifest)
        changed["calls"] = [[labels["object0"], "func_08001000"]]
        with self.assertRaisesRegex(ValueError, "overlapping switch manifest"):
            verify(body, changed, mapping)

    def test_branch_into_declared_word_rejected(self):
        body, labels, manifest, mapping = fixture()
        at = labels["skip0"]
        struct.pack_into("<H", body, at, 0xE000 | (((labels["object0"] - at - 4) // 2) & 0x7FF))
        with self.assertRaisesRegex(ValueError, "reachable code overlaps"):
            verify(body, manifest, mapping)

    def test_unknown_and_stale_binding_or_addend_rejected(self):
        body, _, manifest, mapping = fixture()
        for objects in ({}, {"g_other": f"0x{OBJECT:08X}"},
                        {"g_object": f"0x{OBJECT + 4:08X}"}):
            with self.subTest(objects=objects), self.assertRaises(ValueError):
                verify(body, manifest, mapping, data_mapping=objects)
        changed = copy.deepcopy(manifest)
        changed["data"][-1][-1] += 4
        with self.assertRaisesRegex(ValueError, "invalid interposed.*object word"):
            verify(body, changed, mapping)

    def test_numeric_literal_mixing_is_not_added(self):
        body, labels, manifest, mapping = fixture()
        manifest["data"].pop()
        struct.pack_into("<I", body, labels["object1"], 0x1234)
        with self.assertRaisesRegex(ValueError, "complete.*literal.*coverage"):
            verify(body, manifest, mapping)

    def test_policy_and_manifest_shape_required(self):
        body, _, manifest, mapping = fixture()
        for policy in (None, "unknown-policy", True):
            changed = copy.deepcopy(manifest)
            if policy is None:
                changed.pop("data_policy")
            else:
                changed["data_policy"] = policy
            with self.subTest(policy=policy), self.assertRaises(ValueError):
                verify(body, changed, mapping)

    def test_exact_rom_span_and_bound_unchanged(self):
        body, labels, manifest, mapping = fixture()
        changed = bytearray(body)
        changed[-1] ^= 1
        with self.assertRaisesRegex(ValueError, "differs from the ROM"):
            verify(body, manifest, mapping, rom=changed)
        mapping[0]["end"] = f"0x{BASE + len(body) - 2:08X}"
        with self.assertRaisesRegex(ValueError, "exact mapped Thumb span"):
            verify(body, manifest, mapping)
        body, labels, manifest, mapping = fixture()
        struct.pack_into("<H", body, labels["comparison"], 0x2802)
        with self.assertRaisesRegex(ValueError, "exact adjacent unsigned guard"):
            verify(body, manifest, mapping)


class ReportTests(unittest.TestCase):
    def setUp(self):
        self.body, _, self.manifest, self.mapping = fixture(2)
        self.source = hashlib.sha256(b"synthetic source/header identity").hexdigest()
        self.functions = json.dumps(self.mapping).encode()
        self.objects = json.dumps({"g_object": f"0x{OBJECT:08X}"}).encode()
        scratch = TASK / "build"
        scratch.mkdir(exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="switch_multiple_data_", dir=scratch)
        self.addCleanup(directory.cleanup)
        self.rom_path = Path(directory.name) / "synthetic-report-image.bin"
        self.rom_path.write_bytes(self.body)
        for name, value in (("mapping_snapshot", self.functions), ("data_snapshot", self.objects),
                            ("source_fingerprint", self.source), ("report_rom_path", str(self.rom_path))):
            patcher = mock.patch.object(evidence, name, return_value=value)
            patcher.start()
            self.addCleanup(patcher.stop)

    def report(self):
        return "\n".join([
            f"* verification: `{evidence.SWITCH_MULTIPLE_DATA_SCHEMA}`",
            f"* source SHA-256: `{self.source}`",
            f"* mapping SHA-256: `{evidence.mapping_fingerprint(self.functions)}`",
            f"* data symbols SHA-256: `{evidence.mapping_fingerprint(self.objects)}`",
            f"* switches: {evidence.SWITCH_MULTIPLE_DATA_SUMMARY}",
            "* source plausibility: plausible", "* relocations: none",
            "* verified extent: complete ELF function symbol, including literal pools",
            f"* compiled : `{self.body.hex()}`",
            f"* switch manifest: `{evidence.switch_manifest(self.manifest)}`",
            "* control flow: closed leaf CFG",
            f"* ROM bytes: `{self.body.hex()}` ({len(self.body)} bytes)",
            f"**MATCH - byte identical** - {len(self.body)}/{len(self.body)} bytes",
            f"* switch proof SHA-256: `{evidence.switch_multiple_data_fingerprint(BASE, self.body, self.manifest)}`",
        ])

    def test_v2_report_revalidation_and_v1_domain_rejected(self):
        report = self.report()
        self.assertTrue(evidence.switch_report_matches(report.splitlines(), TASK, BASE, data_profile=True))
        bad = report.replace(evidence.SWITCH_MULTIPLE_DATA_SCHEMA, evidence.SWITCH_DATA_SCHEMA)
        self.assertFalse(evidence.switch_report_matches(bad.splitlines(), TASK, BASE, data_profile=True))
        with mock.patch.object(evidence.empty_body, "has_empty_body", return_value=False):
            self.assertTrue(evidence.report_matches(report, TASK, BASE))

    def test_legacy_single_word_report_remains_valid(self):
        self.body, _, self.manifest, mapping = fixture(1)
        self.manifest.pop("data_policy")
        self.functions = json.dumps(mapping).encode()
        self.rom_path.write_bytes(self.body)
        report = self.report().replace(
            evidence.SWITCH_MULTIPLE_DATA_SCHEMA, evidence.SWITCH_DATA_SCHEMA).replace(
            evidence.SWITCH_MULTIPLE_DATA_SUMMARY, evidence.SWITCH_DATA_SUMMARY).replace(
            evidence.switch_multiple_data_fingerprint(BASE, self.body, self.manifest),
            evidence.switch_data_fingerprint(BASE, self.body, self.manifest))
        with mock.patch.object(evidence, "mapping_snapshot", return_value=self.functions):
            self.assertTrue(evidence.switch_report_matches(report.splitlines(), TASK, BASE, data_profile=True))

    def test_missing_policy_or_record_cannot_revalidate_v2_report(self):
        for change in ("policy", "record"):
            with self.subTest(change=change):
                saved = copy.deepcopy(self.manifest)
                if change == "policy":
                    self.manifest.pop("data_policy")
                else:
                    self.manifest["data"].pop()
                report = self.report()
                self.assertFalse(evidence.switch_report_matches(report.splitlines(), TASK, BASE, data_profile=True))
                self.manifest = saved

    def test_changed_source_mapping_and_byte_identities_rejected(self):
        report = self.report()
        for name, value in (("source_fingerprint", "stale-source"),
                            ("mapping_snapshot", b"[]"), ("data_snapshot", b"{}")):
            with self.subTest(provider=name), mock.patch.object(evidence, name, return_value=value):
                self.assertFalse(evidence.switch_report_matches(report.splitlines(), TASK, BASE, data_profile=True))
        changed = bytearray(self.body)
        changed[-1] ^= 1
        self.rom_path.write_bytes(changed)
        self.assertFalse(evidence.switch_report_matches(report.splitlines(), TASK, BASE, data_profile=True))


if __name__ == "__main__":
    unittest.main()
