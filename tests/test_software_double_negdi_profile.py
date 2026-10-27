"""Original canonical integer-negation provenance in the binary64 profile."""

import copy
import json
import struct
import unittest

import test_software_double_profile as fixture

BASE, match, profile = fixture.BASE, fixture.match, fixture.profile
SOURCE = """long long func_08000000(double condition, long long value)
{
    return condition < 0.0 ? -value : value;
}
"""


class SoftwareDoubleNegationTests(unittest.TestCase):
    setUpClass = classmethod(fixture.SoftwareDoubleTests.setUpClass.__func__)
    setUp = fixture.SoftwareDoubleTests.setUp
    indexes = fixture.SoftwareDoubleTests.indexes
    verify = fixture.SoftwareDoubleTests.verify
    binding = fixture.SoftwareDoubleTests.binding
    patched_rom = fixture.SoftwareDoubleTests.patched_rom
    native_report = fixture.SoftwareDoubleTests.native_report
    fixture = fixture.SoftwareDoubleTests.fixture

    def test_natural_negation_original_elf_and_native_replay(self):
        self.fixture(SOURCE)
        expected = {"__ltdf2", "__negdi2"}
        self.assertEqual(set(self.bindings.values()), expected)
        self.assertEqual({s["name"] for s in self.original["symbols"]
                          if s["name"] and not s["section"]}, expected)
        self.assertEqual(profile.OPERATIONS["__negdi2"], 0x08142A94)
        self.assertEqual(len(self.verify()), len(self.instructions))
        with self.assertRaises(ValueError):
            match.verify_leaf_instructions(self.body, BASE, True, self.calls)
        report = self.native_report()
        opening, reading = self.patched_rom()
        with opening, reading:
            self.assertTrue(profile.report_matches(report, self.root, BASE))
            (self.root / "src/08000000.c").write_text(SOURCE.replace("-value", "value"))
            self.assertFalse(profile.report_matches(report, self.root, BASE))

    def test_negation_does_not_require_unproved_numeric_operand_bounds(self):
        # Unsigned two's-complement negation is also naturally emitted under
        # this canonical symbol; the profile preserves the pinned machine state.
        self.fixture("unsigned long long func_08000000(unsigned long long value) { return -value; }\n")
        self.assertEqual(set(self.bindings.values()), {"__negdi2"})
        self.assertEqual(set(self.calls.values()), {0x08142A94})
        self.assertEqual(len(self.verify()), len(self.instructions))

    def test_negation_original_symbol_alias_and_addend_refused(self):
        self.fixture(SOURCE)
        for name in ("func_08142A94", "func_08142A95", "__ucmpdi2", "__negdi2_alias"):
            original = copy.deepcopy(self.original)
            next(s for s in original["symbols"] if s["name"] == "__negdi2")["name"] = name
            with self.subTest(name=name), self.assertRaises(ValueError):
                self.binding(original)
        with self.assertRaisesRegex(ValueError, "noncanonical addend"):
            self.fixture(assembly="push {lr}\nbl __negdi2+2\npop {r2}\nbx r2")

    def test_negation_requires_original_undefined_global_function_symbol(self):
        self.fixture(SOURCE)
        for key, value in (("section", 1), ("bind", 2), ("type", 1), ("value", 2)):
            original = copy.deepcopy(self.original)
            next(s for s in original["symbols"] if s["name"] == "__negdi2")[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.binding(original)

    def test_negation_wrong_runtime_link_and_missing_binding_refused(self):
        self.fixture(SOURCE)
        site = next(site for site, name in self.bindings.items() if name == "__negdi2")
        targets = {name: profile.OPERATIONS[name] for name in self.bindings.values()}
        for wrong in (0x08142A20, 0x0814379C, 0x08142A96):
            altered = copy.deepcopy(self.linked)
            raw = bytearray(altered["text"])
            displacement = wrong - site - 4
            struct.pack_into("<HH", raw, site - BASE,
                             0xF000 | ((displacement >> 12) & 0x7FF),
                             0xF800 | ((displacement >> 1) & 0x7FF))
            altered["text"] = bytes(raw)
            next(s for s in altered["symbols"] if s["name"] == "__negdi2")["value"] = wrong | 1
            with self.subTest(wrong=wrong), self.assertRaises(ValueError):
                match.linked_function_bytes(self.original, altered, "func_08000000", BASE,
                    self.calls, targets, {}, double_bindings=self.bindings)
            calls = dict(self.calls); calls[site] = wrong
            with self.subTest(caller=wrong), self.assertRaises(ValueError):
                match.verify_leaf_instructions(bytes(raw), BASE, True, calls,
                    double_context=(self.rom, self.mapping, self.index, self.bindings))
        bindings = {site: name for site, name in self.bindings.items() if name != "__negdi2"}
        with self.assertRaises(ValueError):
            match.verify_leaf_instructions(self.body, BASE, True, self.calls,
                double_context=(self.rom, self.mapping, self.index, bindings))

    def test_complete_negation_identity_count_and_restore_refused_on_mutation(self):
        self.fixture(SOURCE)
        entries = json.loads(self.mapping)
        proofs = profile.prove_arithmetic_comparison_closure(self.rom, entries)
        proof = proofs[0x08142A94]
        self.assertFalse(proof["writes"])
        self.assertFalse(proof["stack_reads"])
        self.assertEqual(proof["layout"]["instrs"], 13)
        self.assertEqual(proof["layout"]["candidate_extent"]["end"], "0x08142AAE")
        changed = bytearray(self.rom); changed[0x08142AA8 - BASE] ^= 1
        with self.assertRaisesRegex(ValueError, "runtime identity"):
            profile.verify_identity(bytes(changed), self.mapping, self.index)
        with self.assertRaises(ValueError):
            profile.prove_arithmetic_comparison_closure(bytes(changed), entries)
        for change in ("count", "extent", "foreign"):
            altered = copy.deepcopy(entries)
            row = next(e for e in altered if e["rom"] == "0x08142A94")
            if change == "count": row["instrs"] = 12
            elif change == "extent": row["end"] = "0x08142AAC"
            else: altered.append({"rom": "0x08142AA8", "end": "0x08142AAE", "mode": "thumb", "instrs": 3})
            with self.subTest(change=change), self.assertRaises(ValueError):
                profile.verify_identity(self.rom, json.dumps(altered).encode(), self.index)

    def test_negation_saved_manifest_and_old_runtime_refused(self):
        self.fixture(SOURCE)
        for key, value in (("runtime", "agbcc-thumb-df-convert-add-sub-div-mul-lt-trunc-fix-mod-s16-closure-v6"),
                           ("calls", self.manifest["calls"][:-1]), ("dependencies", [])):
            manifest = copy.deepcopy(self.manifest); manifest[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.verify(manifest)


if __name__ == "__main__":
    unittest.main()
