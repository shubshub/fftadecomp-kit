"""Canonical unsigned word conversion, wide comparison and double negation."""

import copy
import json
import struct
import unittest

import test_software_double_profile as fixture

BASE, match, profile = fixture.BASE, fixture.match, fixture.profile
SOURCE = """typedef unsigned long long UDItype;
long long func_08000000(double value)
{
    double high;
    UDItype result;
    if (value < 0) return 0;
    high = value / ((UDItype)1 << 32);
    result = (unsigned int)high;
    result <<= 32;
    value -= (double)result;
    if (value < 0) result -= (unsigned int)(-value);
    else result += (unsigned int)value;
    return result;
}
"""
NEW_OPERATIONS = {"__fixunsdfsi": 0x08142864, "__cmpdi2": 0x0814435C,
                  "__negdf2": 0x08143930}


class SoftwareDoubleUnsignedTests(unittest.TestCase):
    setUpClass = classmethod(fixture.SoftwareDoubleTests.setUpClass.__func__)
    setUp = fixture.SoftwareDoubleTests.setUp
    indexes = fixture.SoftwareDoubleTests.indexes
    verify = fixture.SoftwareDoubleTests.verify
    binding = fixture.SoftwareDoubleTests.binding
    patched_rom = fixture.SoftwareDoubleTests.patched_rom
    native_report = fixture.SoftwareDoubleTests.native_report
    fixture = fixture.SoftwareDoubleTests.fixture

    def test_natural_complete_conversion_original_elf_and_fresh_report(self):
        self.fixture(SOURCE)
        expected = {"__ltdf2", "__muldf3", "__fixunsdfsi", "__cmpdi2",
                    "__floatdidf", "__adddf3", "__subdf3", "__negdf2"}
        self.assertEqual(set(self.bindings.values()), expected)
        self.assertEqual({s["name"] for s in self.original["symbols"]
                          if s["name"] and not s["section"]}, expected)
        self.assertEqual(len(self.body), 214)
        self.assertEqual(len(self.verify()), 80)
        with self.assertRaises(ValueError):
            match.verify_leaf_instructions(self.body, BASE, True, self.calls)
        report = self.native_report()
        opening, reading = self.patched_rom()
        with opening, reading:
            self.assertTrue(profile.report_matches(report, self.root, BASE))
            (self.root / "src/08000000.c").write_text(SOURCE.replace("return result;", "return 0;"))
            self.assertFalse(profile.report_matches(report, self.root, BASE))

    def test_word_conversion_and_negation_are_original_compiler_helpers(self):
        for source, names in (("unsigned int func_08000000(double v) { return (unsigned int)v; }", {"__fixunsdfsi"}),
                              ("double func_08000000(double v) { return -v; }", {"__negdf2"})):
            with self.subTest(source=source):
                self.fixture(source)
                self.assertEqual(set(self.bindings.values()), names)
                self.assertEqual(len(self.verify()), len(self.instructions))

    def test_alias_addend_and_nonundefined_symbol_refused(self):
        self.fixture(SOURCE)
        for canonical, target in NEW_OPERATIONS.items():
            self.assertEqual(profile.OPERATIONS[canonical], target)
            for alias in (f"func_{target:08X}", f"func_{target|1:08X}", canonical + "_alias", "__gedf2"):
                original = copy.deepcopy(self.original)
                next(s for s in original["symbols"] if s["name"] == canonical)["name"] = alias
                with self.subTest(canonical=canonical, alias=alias), self.assertRaises(ValueError):
                    self.binding(original)
            for key, value in (("section", 1), ("bind", 2), ("type", 1), ("value", 2)):
                original = copy.deepcopy(self.original)
                next(s for s in original["symbols"] if s["name"] == canonical)[key] = value
                with self.subTest(canonical=canonical, key=key), self.assertRaises(ValueError):
                    self.binding(original)
        for canonical in NEW_OPERATIONS:
            with self.subTest(canonical=canonical), self.assertRaisesRegex(ValueError, "noncanonical addend"):
                self.fixture(assembly=f"push {{lr}}\nbl {canonical}+2\npop {{r2}}\nbx r2")

    def test_wrong_link_and_missing_original_binding_refused(self):
        self.fixture(SOURCE)
        targets = {name: profile.OPERATIONS[name] for name in self.bindings.values()}
        for canonical, wrong in (("__fixunsdfsi", 0x081438BC), ("__cmpdi2", 0x08144378),
                                 ("__negdf2", 0x08142A94)):
            site = next(site for site, name in self.bindings.items() if name == canonical)
            altered = copy.deepcopy(self.linked)
            raw = bytearray(altered["text"])
            displacement = wrong - site - 4
            struct.pack_into("<HH", raw, site - BASE,
                             0xF000 | ((displacement >> 12) & 0x7FF),
                             0xF800 | ((displacement >> 1) & 0x7FF))
            altered["text"] = bytes(raw)
            next(s for s in altered["symbols"] if s["name"] == canonical)["value"] = wrong | 1
            with self.subTest(canonical=canonical), self.assertRaises(ValueError):
                match.linked_function_bytes(self.original, altered, "func_08000000", BASE,
                    self.calls, targets, {}, double_bindings=self.bindings)
            bindings = {a: name for a, name in self.bindings.items() if name != canonical}
            with self.subTest(missing=canonical), self.assertRaises(ValueError):
                match.verify_leaf_instructions(self.body, BASE, True, self.calls,
                    double_context=(self.rom, self.mapping, self.index, bindings))

    def test_identity_unique_dual_ownership_and_complete_pools(self):
        self.fixture(SOURCE)
        entries = json.loads(self.mapping)
        for start in (*NEW_OPERATIONS.values(), 0x0814374C):
            changed = bytearray(self.rom); changed[start - BASE] ^= 1
            with self.subTest(start=start), self.assertRaisesRegex(ValueError, "runtime identity"):
                profile.verify_identity(bytes(changed), self.mapping, self.index)
            for kind in ("count", "end", "mode", "duplicate", "missing", "overlap"):
                altered = copy.deepcopy(entries)
                row = next(e for e in altered if int(e["rom"], 16) == start)
                if kind == "count": row["instrs"] -= 1
                elif kind == "end": row["end"] = f"0x{int(row['end'], 16)-2:08X}"
                elif kind == "mode": row["mode"] = "arm"
                elif kind == "duplicate": altered.append(copy.deepcopy(row))
                elif kind == "missing": altered.remove(row)
                else: altered.append({"rom": f"0x{start+2:08X}", "end": row["end"], "mode": "thumb", "instrs": 1})
                with self.subTest(start=start, kind=kind), self.assertRaises(ValueError):
                    profile.verify_identity(self.rom, json.dumps(altered).encode(), self.index)
            index = self.index + f"{start:08X} {start+2:08X} 2 1 return\n".encode()
            with self.subTest(index=start), self.assertRaises(ValueError):
                profile.verify_identity(self.rom, self.mapping, index)
        changed = bytearray(self.rom); changed[0x081428A8 - BASE] ^= 1
        with self.assertRaisesRegex(ValueError, "runtime identity"):
            profile.verify_identity(bytes(changed), self.mapping, self.index)

    def test_complete_closure_abi_rejects_restore_frame_and_formal_write(self):
        self.fixture(SOURCE)
        from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
        decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
        entries = json.loads(self.mapping)
        proofs = profile.prove_unsigned_conversion_closure(self.rom, entries)
        self.assertEqual(set(proofs), set(profile.UNSIGNED_CONVERSION_CLOSURE))
        for start in (*NEW_OPERATIONS.values(), 0x0814374C, 0x081428E4):
            self.assertTrue(proofs[start]["returns"])
            self.assertFalse(proofs[start]["writes"])
        self.assertEqual(proofs[0x08142D34]["writes"], [(1, n, 4) for n in range(0, 20, 4)])
        for kind, start, mnemonic in (("restore", 0x0814374C, "pop"),
                                     ("frame", 0x08143930, "sub"),
                                     ("write", 0x08142D34, "str")):
            instructions = [i for a, b in proofs[start]["layout"]["code_ranges"]
                            for i in decoder.disasm(self.rom[int(a,16)-BASE:int(b,16)-BASE], int(a,16))]
            instruction = next(i for i in instructions if i.mnemonic == mnemonic)
            changed = bytearray(self.rom); position = instruction.address - BASE
            word = struct.unpack_from("<H", changed, position)[0]
            if kind == "restore": word ^= (1 << 4) | (1 << 5)
            elif kind == "frame": word += 1
            else: word = (word & ~0x7C0) | (5 << 6)
            struct.pack_into("<H", changed, position, word)
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                profile.prove_unsigned_conversion_closure(bytes(changed), entries)

    def test_old_proof_missing_dependencies_and_changed_call_refused(self):
        self.fixture(SOURCE)
        for key, value in (("runtime", "agbcc-thumb-df-convert-add-sub-div-mul-lt-trunc-fix-negdi-mod-s16-closure-v7"),
                           ("calls", self.manifest["calls"][:-1]), ("dependencies", [])):
            manifest = copy.deepcopy(self.manifest); manifest[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.verify(manifest)
        changed = bytearray(self.body); changed[0] ^= 1
        with self.assertRaises(ValueError):
            profile.verify(bytes(changed), BASE, self.rom, self.mapping, self.index, self.manifest)


if __name__ == "__main__":
    unittest.main()
