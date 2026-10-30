"""Canonical public wide conversion and the exact authored runtime owner."""

import copy
import hashlib
import json
import struct
import unittest

import test_software_double_profile as fixture

BASE, match, profile = fixture.BASE, fixture.match, fixture.profile
SOURCE = """long long func_08000000(double value)
{
    if (value < 0) return -(unsigned long long)(-value);
    return (unsigned long long)value;
}
"""


class PublicUnsignedConversionTests(unittest.TestCase):
    setUpClass = classmethod(fixture.SoftwareDoubleTests.setUpClass.__func__)
    setUp = fixture.SoftwareDoubleTests.setUp
    indexes = fixture.SoftwareDoubleTests.indexes
    verify = fixture.SoftwareDoubleTests.verify
    binding = fixture.SoftwareDoubleTests.binding
    patched_rom = fixture.SoftwareDoubleTests.patched_rom
    native_report = fixture.SoftwareDoubleTests.native_report
    fixture = fixture.SoftwareDoubleTests.fixture

    def test_natural_public_helper_original_elf_and_fresh_report(self):
        self.fixture(SOURCE)
        expected = {"__ltdf2", "__fixunsdfdi", "__negdf2", "__negdi2"}
        self.assertEqual(set(self.bindings.values()), expected)
        self.assertEqual({s["name"] for s in self.original["symbols"]
                          if s["name"] and not s["section"]}, expected)
        self.assertEqual(list(self.bindings.values()).count("__fixunsdfdi"), 2)
        self.assertEqual(profile.OPERATIONS["__fixunsdfdi"], 0x0814278C)
        self.assertEqual(len(self.body), 58)
        self.assertEqual(len(self.verify()), len(self.instructions))
        report = self.native_report()
        opening, reading = self.patched_rom()
        with opening, reading:
            self.assertTrue(profile.report_matches(report, self.root, BASE))
            (self.root / "src/08000000.c").write_text(SOURCE.replace("return (unsigned long long)value;", "return 0;"))
            self.assertFalse(profile.report_matches(report, self.root, BASE))

    def test_exact_owner_has_full_identity_and_closed_restoring_abi(self):
        self.fixture(SOURCE)
        start, end, count, digest = profile.UNSIGNED_WIDE_OWNER
        body = self.rom[start-BASE:end-BASE]
        self.assertEqual((len(body), count), (214, 80))
        self.assertEqual(hashlib.sha256(body).hexdigest(), digest)
        entries, owner = profile.validate_span(body, start, self.rom, self.mapping, self.index)
        proof = profile.prove_unsigned_conversion_closure(self.rom, entries)[start]
        self.assertEqual(owner["instrs"], count)
        self.assertEqual(proof["layout"]["instrs"], count)
        self.assertTrue(proof["returns"])
        self.assertFalse(proof["writes"])
        self.assertFalse(proof["stack_reads"])
        calls = {site: target for site, target in profile.EDGES if start <= site < end}
        self.assertNotIn(start, calls.values())
        bindings = {site: next(name for name, address in profile.OPERATIONS.items() if address == target)
                    for site, target in calls.items()}
        instructions = match.verify_leaf_instructions(body, start, True, calls,
            double_context=(self.rom, self.mapping, self.index, bindings))
        self.assertEqual(len(instructions), count)
        manifest = profile.make_manifest(calls, start, bindings, instructions)
        self.assertEqual(len(profile.verify(body, start, self.rom, self.mapping, self.index, manifest)), count)

    def test_other_runtime_owners_and_interior_or_short_owners_stay_refused(self):
        self.fixture(SOURCE)
        start, end, _, _ = profile.UNSIGNED_WIDE_OWNER
        for a, b, _, _ in profile.IDENTITIES:
            if a == start:
                continue
            with self.subTest(owner=a), self.assertRaises(ValueError):
                profile.validate_span(self.rom[a-BASE:b-BASE], a, self.rom, self.mapping, self.index)
        for a, b in ((start+2, end), (start, end-2), (start, end+2)):
            with self.subTest(span=(a,b)), self.assertRaises(ValueError):
                profile.validate_span(self.rom[a-BASE:b-BASE], a, self.rom, self.mapping, self.index)

    def test_wrong_body_count_and_each_owner_index_are_refused(self):
        self.fixture(SOURCE)
        start, end, _, _ = profile.UNSIGNED_WIDE_OWNER
        body = self.rom[start-BASE:end-BASE]
        for position in (0, 26, len(body)-1):
            rom = bytearray(self.rom); rom[start-BASE+position] ^= 1
            with self.subTest(byte=position), self.assertRaises(ValueError):
                profile.validate_span(bytes(rom[start-BASE:end-BASE]), start, bytes(rom), self.mapping, self.index)
        entries = json.loads(self.mapping)
        for kind in ("old-count", "short", "mode", "duplicate", "overlap", "missing"):
            changed = copy.deepcopy(entries)
            row = next(e for e in changed if int(e["rom"],16) == start)
            if kind == "old-count": row["instrs"] = 107
            elif kind == "short": row["end"] = f"0x{end-2:08X}"
            elif kind == "mode": row["mode"] = "arm"
            elif kind == "duplicate": changed.append(copy.deepcopy(row))
            elif kind == "overlap": changed.append(dict(row, rom=f"0x{start+2:08X}"))
            else: changed.remove(row)
            with self.subTest(index=kind), self.assertRaises(ValueError):
                profile.validate_span(body, start, self.rom, json.dumps(changed).encode(), self.index)
        for index in (self.index.replace(f"{end:08X} 214 80".encode(), f"{end:08X} 214 107".encode()),
                      self.index + f"{start:08X} {end:08X} 214 80 return\n".encode()):
            self.assertNotEqual(index, self.index)
            with self.assertRaises(ValueError):
                profile.validate_span(body, start, self.rom, self.mapping, index)

    def test_public_helper_aliases_and_noncanonical_original_symbols_are_refused(self):
        self.fixture(SOURCE)
        for name in ("func_0814278C", "func_0814278D", "func_0814278E", "__fixunsdfdi_alias"):
            original = copy.deepcopy(self.original)
            next(s for s in original["symbols"] if s["name"] == "__fixunsdfdi")["name"] = name
            with self.subTest(alias=name), self.assertRaises(ValueError):
                self.binding(original)
        for key, value in (("section", 1), ("bind", 2), ("type", 1), ("value", 2)):
            original = copy.deepcopy(self.original)
            next(s for s in original["symbols"] if s["name"] == "__fixunsdfdi")[key] = value
            with self.subTest(symbol=key), self.assertRaises(ValueError):
                self.binding(original)
        with self.assertRaisesRegex(ValueError, "noncanonical addend"):
            self.fixture(assembly="push {lr}\nbl __fixunsdfdi+2\npop {r2}\nbx r2")

    def test_recursive_canonical_call_and_forged_link_are_refused(self):
        self.fixture(SOURCE)
        start, end, _, _ = profile.UNSIGNED_WIDE_OWNER
        original = copy.deepcopy(self.original)
        next(s for s in original["symbols"] if s["name"] == "func_08000000")["name"] = f"func_{start:08X}"
        with self.assertRaisesRegex(ValueError, "recursive or intra-function"):
            match.call_bindings(original, f"func_{start:08X}", start, self.mapping, len(self.rom), self.rom,
                                double_bindings={}, double_index=self.index)
        site = next(site for site, name in self.bindings.items() if name == "__fixunsdfdi")
        altered = copy.deepcopy(self.linked); raw = bytearray(altered["text"])
        wrong = start+2; displacement = wrong-site-4
        struct.pack_into("<HH", raw, site-BASE, 0xF000|((displacement>>12)&0x7FF),
                         0xF800|((displacement>>1)&0x7FF))
        altered["text"] = bytes(raw)
        next(s for s in altered["symbols"] if s["name"] == "__fixunsdfdi")["value"] = wrong|1
        targets = {name: profile.OPERATIONS[name] for name in self.bindings.values()}
        with self.assertRaises(ValueError):
            match.linked_function_bytes(self.original, altered, "func_08000000", BASE,
                                        self.calls, targets, {}, double_bindings=self.bindings)

    def test_stale_runtime_or_missing_owner_dependency_cannot_assert_public_support(self):
        self.fixture(SOURCE)
        for key, value in (("runtime", profile.RUNTIME.replace("fixunsdi-mod-s16-closure-v9", "mod-s16-closure-v8")),
                           ("dependencies", [row for row in self.manifest["dependencies"]
                                             if row[0] != profile.UNSIGNED_WIDE_OWNER[0]]),
                           ("calls", self.manifest["calls"][:-1])):
            manifest = copy.deepcopy(self.manifest); manifest[key] = value
            with self.subTest(proof=key), self.assertRaises(ValueError):
                self.verify(manifest)


if __name__ == "__main__":
    unittest.main()
