"""Synthetic Thumb switch-data checks; no game bytes or compiler are used."""

import copy
import json
from pathlib import Path
import struct
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import match


BASE = 0x08000000
OBJECT = 0x02001000
CALLEE = 0x08001000


def fixture(before=False, call=False):
    """Build a two-case switch with one referenced, branch-skipped object word."""
    body = bytearray()
    labels, fixups = {}, []

    def half(value):
        body.extend(struct.pack("<H", value))

    def label(name):
        labels[name] = len(body)

    def instruction(kind, name, register=0):
        fixups.append((len(body), kind, name, register))
        half(0)

    def word(name):
        fixups.append((len(body), "word", name, 0))
        body.extend(bytes(4))

    def align():
        while len(body) % 4:
            half(0)

    if call:
        half(0xB500)  # push {lr}
    if before:
        instruction("ldr", "object", 2)
    label("comparison")
    half(0x2801)  # cmp r0, #1
    label("guard")
    instruction("bhi", "default")
    label("dispatch")
    half(0x0080)  # lsls r0, r0, #2
    instruction("ldr", "pointer", 1)
    half(0x1840)  # adds r0, r0, r1
    half(0x6800)  # ldr r0, [r0]
    half(0x4687)  # mov pc, r0
    align()
    if before:
        label("object")
        body.extend(struct.pack("<I", OBJECT))
    label("pointer")
    word("table")
    label("table")
    word("case0")
    word("case1")
    label("case0")
    if before:
        half(0x1C11)  # adds r1, r2, #0
    else:
        instruction("ldr", "object", 1)
    half(0x8808)  # ldrh r0, [r1]
    label("skip")
    instruction("b", "done")
    if not before:
        align()
        label("object")
        body.extend(struct.pack("<I", OBJECT))
    label("case1")
    half(0x2007)  # movs r0, #7
    instruction("b", "done")
    label("default")
    half(0x2000)  # movs r0, #0
    label("done")
    calls = []
    if call:
        offset = CALLEE - (BASE + len(body) + 4)
        calls.append([len(body), "func_08001000"])
        half(0xF000 | ((offset >> 12) & 0x7FF))
        half(0xF800 | ((offset >> 1) & 0x7FF))
        half(0xBC02)  # pop {r1}
        half(0x4708)  # bx r1
    else:
        half(0x4770)  # bx lr

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
            value = (0xD800 | displacement & 0xFF) if kind == "bhi" else (
                0xE000 | displacement & 0x7FF)
            struct.pack_into("<H", body, offset, value)

    relocations = {labels["pointer"]: labels["table"],
                   labels["table"]: labels["case0"],
                   labels["table"] + 4: labels["case1"]}
    descriptor = {name: labels[name] for name in (
        "comparison", "guard", "dispatch", "default", "table")}
    descriptor.update(literal=labels["pointer"], bound=1,
                      relocations=[list(item) for item in relocations.items()])
    manifest = {"calls": calls, "data": [[labels["object"], "g_object", 0]],
                "switch": descriptor}
    mapping = [{"rom": f"0x{BASE:08X}", "end": f"0x{BASE + len(body):08X}", "mode": "thumb"},
               {"rom": f"0x{CALLEE:08X}", "end": f"0x{CALLEE + 2:08X}", "mode": "thumb"}]
    return body, labels, manifest, mapping


class SwitchDataPlacementTests(unittest.TestCase):
    def verify(self, body, manifest, mapping, data_mapping=None, rom=None):
        if data_mapping is None:
            data_mapping = {"g_object": f"0x{OBJECT:08X}"}
        if rom is None:
            rom = bytes(body).ljust(CALLEE - BASE, b"\0") + b"\x70\x47"
        return match.verify_switches(bytes(body), BASE, rom, json.dumps(mapping).encode(),
                                     manifest, data_mapping=json.dumps(data_mapping).encode())

    def test_after_table_object(self):
        for call in (False, True):
            with self.subTest(call=call):
                body, labels, manifest, mapping = fixture(call=call)
                instructions, summary = self.verify(body, manifest, mapping)
                self.assertIn(BASE + labels["case0"], {item.address for item in instructions})
                self.assertGreater(labels["object"], labels["table"] + 7)
                self.assertEqual(summary, match.CALL_SUMMARY if call else "closed leaf CFG")

    def test_before_table_object_remains_supported(self):
        for call in (False, True):
            with self.subTest(call=call):
                body, labels, manifest, mapping = fixture(before=True, call=call)
                instructions, _ = self.verify(body, manifest, mapping)
                self.assertEqual(labels["object"], labels["pointer"] - 4)
                self.assertIn(BASE, {item.address for item in instructions})

    def test_unreferenced_object_rejected(self):
        body, labels, manifest, mapping = fixture()
        struct.pack_into("<H", body, labels["case0"], 0x2100)  # movs r1, #0
        with self.assertRaisesRegex(ValueError, "not a reachable.*literal-pool load"):
            self.verify(body, manifest, mapping)

    def test_branch_or_fallthrough_into_object_rejected(self):
        for fallthrough in (False, True):
            body, labels, manifest, mapping = fixture()
            offset = labels["skip"]
            instruction = 0x2200 if fallthrough else (
                0xE000 | ((labels["object"] - offset - 4) // 2) & 0x7FF)
            struct.pack_into("<H", body, offset, instruction)
            with self.subTest(fallthrough=fallthrough), self.assertRaisesRegex(
                    ValueError, "reachable code overlaps"):
                self.verify(body, manifest, mapping)

    def test_table_target_into_object_rejected(self):
        body, labels, manifest, mapping = fixture()
        struct.pack_into("<I", body, labels["table"], BASE + labels["object"])
        manifest["switch"]["relocations"][1][1] = labels["object"]
        with self.assertRaisesRegex(ValueError, "reachable code overlaps"):
            self.verify(body, manifest, mapping)

    def test_table_overlap_rejected(self):
        body, labels, manifest, mapping = fixture()
        manifest["data"][0][0] = labels["table"]
        value = struct.unpack_from("<I", body, labels["table"])[0]
        with self.assertRaisesRegex(ValueError, "invalid interposed switch-data object word"):
            self.verify(body, manifest, mapping, data_mapping={"g_object": f"0x{value:08X}"})

    def test_out_of_range_unaligned_and_noninteger_offsets_rejected(self):
        body, labels, manifest, mapping = fixture()
        for offset in (-4, len(body), len(body) + 4, labels["object"] + 2, True):
            changed = copy.deepcopy(manifest)
            changed["data"][0][0] = offset
            with self.subTest(offset=offset), self.assertRaises(ValueError):
                self.verify(body, changed, mapping)

    def test_mapping_and_object_value_must_agree(self):
        body, labels, manifest, mapping = fixture()
        for bindings in ({}, {"g_other": f"0x{OBJECT:08X}"},
                         {"g_object": f"0x{OBJECT + 4:08X}"}):
            with self.subTest(bindings=bindings), self.assertRaises(ValueError):
                self.verify(body, manifest, mapping, data_mapping=bindings)
        for field, value in ((1, "g_other"), (2, 4)):
            changed = copy.deepcopy(manifest)
            changed["data"][0][field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                self.verify(body, changed, mapping)

    def test_in_function_object_address_rejected(self):
        body, labels, manifest, mapping = fixture()
        value = BASE + labels["case0"]
        struct.pack_into("<I", body, labels["object"], value)
        with self.assertRaisesRegex(ValueError, "invalid interposed switch-data object word"):
            self.verify(body, manifest, mapping, data_mapping={"g_object": f"0x{value:08X}"})

    def test_multiple_bindings_including_seven_words_rejected(self):
        body, labels, manifest, mapping = fixture()
        for count in (2, 7):
            changed = copy.deepcopy(manifest)
            changed["data"] *= count
            with self.subTest(count=count), self.assertRaisesRegex(
                    ValueError, "one canonical object binding"):
                self.verify(body, changed, mapping)
            relocations = dict(manifest["switch"]["relocations"])
            data_relocations = {labels["object"] + 4 * index: ("g_object", OBJECT)
                                for index in range(count)}
            with self.subTest(layout_count=count), self.assertRaises(ValueError):
                match.switch_layout(bytes(body), BASE, relocations, data_relocations)

    def test_exact_unsigned_guard_required(self):
        body, labels, manifest, mapping = fixture()
        for offset, instruction in ((labels["comparison"], 0x2802),
                                    (labels["guard"], 0xD000)):
            changed = bytearray(body)
            struct.pack_into("<H", changed, offset, instruction)
            with self.subTest(offset=offset), self.assertRaisesRegex(
                    ValueError, "exact adjacent unsigned guard"):
                self.verify(changed, manifest, mapping)

    def test_table_targets_must_be_forward_even_and_local(self):
        body, labels, manifest, mapping = fixture()
        for target in (labels["table"], labels["case0"] + 1, len(body), -2):
            changed = bytearray(body)
            descriptor = copy.deepcopy(manifest)
            struct.pack_into("<I", changed, labels["table"], BASE + target)
            descriptor["switch"]["relocations"][1][1] = target
            with self.subTest(target=target), self.assertRaises(ValueError):
                self.verify(changed, descriptor, mapping)

    def test_exact_full_rom_and_unique_index_span_required(self):
        body, _, manifest, mapping = fixture()
        changed_rom = bytearray(body)
        changed_rom[-1] ^= 1
        with self.assertRaisesRegex(ValueError, "differs from the ROM"):
            self.verify(body, manifest, mapping, rom=bytes(changed_rom))
        for duplicate in (False, True):
            changed_mapping = copy.deepcopy(mapping)
            if duplicate:
                changed_mapping.append(changed_mapping[0].copy())
            else:
                changed_mapping[0]["end"] = f"0x{BASE + len(body) - 2:08X}"
            with self.subTest(duplicate=duplicate), self.assertRaisesRegex(
                    ValueError, "exact mapped Thumb span"):
                self.verify(body, manifest, changed_mapping)

    def test_direct_calls_require_unique_mapped_thumb_entries(self):
        body, _, manifest, mapping = fixture(call=True)
        for variant in ("missing", "duplicate", "arm"):
            changed_mapping = copy.deepcopy(mapping)
            if variant == "missing":
                changed_mapping.pop()
            elif variant == "duplicate":
                changed_mapping.append(changed_mapping[-1].copy())
            else:
                changed_mapping[-1]["mode"] = "arm"
            with self.subTest(variant=variant), self.assertRaisesRegex(
                    ValueError, "unknown, ambiguous, misaligned, or not Thumb"):
                self.verify(body, manifest, changed_mapping)


if __name__ == "__main__":
    unittest.main()
