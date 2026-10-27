"""Canonical binary64 conversion closure, using only the local ROM in memory."""

import argparse
import builtins
import copy
from contextlib import redirect_stdout
import hashlib
import io
import json
import os
from pathlib import Path
import struct
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import match
import match_evidence as evidence
import software_double_profile as profile
import software_float_profile as software_float

BASE = 0x08000000
SOURCE = """extern float func_08000200(float);
float func_08000000(long long wide, int narrow)
{
    return func_08000200((float)(((double)wide - (double)narrow) / 100.0));
}
"""


class SoftwareDoubleTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        selected = os.environ.get("FFTA_ROM")
        if not selected or not Path(selected).is_file():
            raise unittest.SkipTest("FFTA_ROM must reference the approved ROM")
        cls.rom_path = Path(selected).resolve()
        cls.runtime_rom = cls.rom_path.read_bytes()
        if hashlib.sha256(cls.runtime_rom).hexdigest() != software_float.ROM_SHA256:
            raise unittest.SkipTest("FFTA_ROM is not the approved image")

    def setUp(self):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="software_double_", dir=scratch)
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        for name in ("src", "include", "config", "symbols"):
            (self.root / name).mkdir()
        environment = patch.dict(os.environ, {"TMPDIR": str(self.root),
                                               "PYTHONDONTWRITEBYTECODE": "1"})
        environment.start()
        self.addCleanup(environment.stop)
        self.args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP,
                                       assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY,
                                       linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)

    def indexes(self, size, count):
        entries = [{"rom": f"0x{BASE:08X}", "end": f"0x{BASE + size:08X}",
                    "mode": "thumb", "instrs": count},
                   {"rom": "0x08000200", "end": "0x08000202", "mode": "thumb", "instrs": 1}]
        entries.extend({"rom": f"0x{a:08X}", "end": f"0x{b:08X}", "mode": "thumb", "instrs": n}
                       for a, b, n, _ in profile.IDENTITIES)
        self.mapping = json.dumps(entries).encode()
        self.index = "".join(f"{int(e['rom'], 16):08X} {int(e['end'], 16):08X} "
                             f"{int(e['end'], 16) - int(e['rom'], 16)} {e['instrs']} return\n"
                             for e in entries).encode()

    def fixture(self, source=SOURCE, assembly=None):
        (self.root / "src/08000000.c").write_text(source)
        runner = match.Runner(match.DEFAULT_CC, root=self.root, timeout=120)
        with runner.workspace() as workspace:
            if assembly is None:
                _, _, original = match.compile_object(
                    runner, workspace, self.args, self.root, BASE, "src/08000000.c")
            else:
                text = (".syntax unified\n.arch armv4t\n.thumb\n.text\n"
                        ".global func_08000000\n.type func_08000000, %function\n"
                        ".thumb_func\nfunc_08000000:\n" + assembly +
                        "\n.size func_08000000, . - func_08000000\n")
                path = Path(workspace) / "f.s"
                path.write_text(text)
                subprocess.run([self.args.assembler, "-mthumb-interwork", str(path),
                                "-o", str(Path(workspace) / "f.o")],
                               capture_output=True, check=True, timeout=120)
                original = match.elf_image((Path(workspace) / "f.o").read_bytes())
            symbol, _ = match.function_record(original, "func_08000000", BASE, True)
            self.indexes(symbol["size"], 1)
            self.body, self.calls, self.bindings = profile.object_bytes(
                runner, workspace, self.args, original, BASE, self.mapping,
                self.runtime_rom, self.index)
            self.original = original
            self.linked = match.elf_image((Path(workspace) / "f.elf").read_bytes())
        rom = bytearray(self.runtime_rom)
        rom[:len(self.body)] = self.body
        self.rom = bytes(rom)
        self.instructions = match.verify_leaf_instructions(
            self.body, BASE, True, self.calls,
            double_context=(self.rom, self.mapping, self.index, self.bindings))
        self.indexes(len(self.body), len(self.instructions))
        (self.root / "config/functions.json").write_bytes(self.mapping)
        (self.root / "symbols/functions.txt").write_bytes(self.index)
        self.manifest = profile.make_manifest(self.calls, BASE, self.bindings, self.instructions)

    def verify(self, manifest=None):
        return profile.verify(self.body, BASE, self.rom, self.mapping, self.index,
                              self.manifest if manifest is None else manifest)

    def binding(self, original=None, **kwargs):
        return match.call_bindings(self.original if original is None else original,
                                   "func_08000000", BASE, self.mapping, len(self.rom), self.rom,
                                   double_bindings={}, double_index=self.index, **kwargs)

    def patched_rom(self):
        original_open, original_read = builtins.open, Path.read_bytes
        def open_file(path, mode="r", *args, **kwargs):
            if mode == "rb" and Path(path).resolve() == self.rom_path:
                return io.BytesIO(self.rom)
            return original_open(path, mode, *args, **kwargs)
        def read(path):
            return self.rom if path.resolve() == self.rom_path else original_read(path)
        return patch.object(builtins, "open", open_file), patch.object(Path, "read_bytes", read)

    def native_report(self):
        opening, reading = self.patched_rom()
        with opening, reading, patch.object(sys, "argv", ["match.py", "--root", str(self.root),
                "--software-double-profile", profile.SELECTOR, "0x08000000"]), \
                patch.object(match, "ROOT", match.ROOT), redirect_stdout(io.StringIO()):
            self.assertEqual(match.main(), 0)
        return (self.root / "docs/match/08000000.md").read_text()

    def test_native_all_five_operations_and_ordinary_call(self):
        self.fixture()
        self.assertEqual(set(self.bindings.values()), set(profile.OPERATIONS)-{"__adddf3", "__fixdfsi", "__muldf3", "__ltdf2", "__negdi2", "__fixunsdfsi", "__cmpdi2", "__negdf2", "__fixunsdfdi"})
        self.assertIn(0x08000200, self.calls.values())
        self.assertEqual(len(self.verify()), len(self.instructions))
        with self.assertRaises(ValueError):
            match.verify_leaf_instructions(self.body, BASE, True, self.calls)
        self.fixture(assembly="push {lr}\nsub sp, #4\nstr r0, [sp]\nbl __truncdfsf2\n"
                              "add sp, #4\npop {r1}\nbx r1")
        self.assertTrue(self.manifest["frame"])
        self.verify()

    def test_native_conversion_closure_and_output_footprint(self):
        self.fixture()
        entries, _ = profile.verify_identity(self.rom, self.mapping, self.index)
        proofs = profile.prove_truncation_closure(self.rom, entries)
        self.assertEqual(set(proofs), set(profile.TRUNCATION_CLOSURE))
        self.assertEqual(proofs[0x08142D34]["writes"], [(1, n, 4) for n in range(0, 20, 4)])
        for start in (0x08143980, 0x081439C8, 0x08144314):
            self.assertFalse(proofs[start]["writes"])
            self.assertTrue(proofs[start]["returns"])
        # Defaults refuse subword loads; enabling those alone still cannot
        # enlarge the original four-word output bound.
        with self.assertRaisesRegex(ValueError, "memory operation is unsupported"):
            software_float.prove_runtime(self.rom, entries, 0x08142D34, 0x08142E10, 97, {})
        with self.assertRaisesRegex(ValueError, "unbounded external write"):
            software_float.prove_runtime(self.rom, entries, 0x08142D34, 0x08142E10, 97, {},
                                         stack_load_widths=(1, 2, 4))

    def test_runtime_bodies_literal_edges_and_dual_ownership_fail_closed(self):
        self.fixture()
        for address in (0x08143980, 0x081439C4, 0x081439C8, 0x08144314):
            changed = bytearray(self.rom); changed[address - BASE] ^= 1
            with self.subTest(address=address), self.assertRaisesRegex(ValueError, "runtime identity"):
                profile.verify_identity(bytes(changed), self.mapping, self.index)
        entries = json.loads(self.mapping)
        position = next(i for i, row in enumerate(entries) if row["rom"] == "0x08143980")
        for change in ("duplicate", "foreign_literal", "short", "arm", "count", "odd", "missing"):
            altered = copy.deepcopy(entries)
            row = altered[position]
            if change == "duplicate": altered.append(copy.deepcopy(row))
            elif change == "foreign_literal":
                altered.append({"rom": "0x081439C4", "end": "0x081439C8", "mode": "thumb", "instrs": 2})
            elif change == "short": row["end"] = "0x081439C4"
            elif change == "arm": row["mode"] = "arm"
            elif change == "count": row["instrs"] = 34
            elif change == "odd": row["rom"] = "0x08143981"
            else: altered.pop(position)
            with self.subTest(change=change), self.assertRaises(ValueError):
                profile.verify_identity(self.rom, json.dumps(altered).encode(), self.index)
        for index in (self.index + b"081439C4 081439C8 4 2 return\n",
                      self.index.replace(b"081439C8 72 32", b"081439C4 68 32"),
                      self.index.replace(b"0814432C 24 11", b"0814432C 24 12")):
            with self.subTest(index=index[-100:]), self.assertRaises(ValueError):
                profile.verify_identity(self.rom, self.mapping, index)
        with patch.object(profile, "EDGES", profile.EDGES[:-1] + ((0x08144322, 0x081439CA),)), \
                self.assertRaisesRegex(ValueError, "dependency edge"):
            profile.verify_identity(self.rom, self.mapping, self.index)

    def test_native_abi_rejects_bad_restore_stack_and_write(self):
        self.fixture()
        from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
        decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
        proofs = profile.prove_truncation_closure(self.rom, json.loads(self.mapping))
        for kind, start, mnemonic in (("restore", 0x08143980, "pop"),
                                     ("frame", 0x08144314, "sub"),
                                     ("write", 0x08142D34, "str")):
            instructions = [i for a, b in proofs[start]["layout"]["code_ranges"]
                            for i in decoder.disasm(self.rom[int(a, 16) - BASE:int(b, 16) - BASE], int(a, 16))]
            instruction = next(i for i in instructions if i.mnemonic == mnemonic)
            changed = bytearray(self.rom)
            position = instruction.address - BASE
            word = struct.unpack_from("<H", changed, position)[0]
            if kind == "restore": word ^= (1 << 4) | (1 << 5)
            elif kind == "frame": word += 1
            else: word = (word & ~0x7C0) | (5 << 6)
            struct.pack_into("<H", changed, position, word)
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                profile.prove_truncation_closure(bytes(changed), json.loads(self.mapping))

    def test_reserved_spans_canonical_symbols_and_addends(self):
        self.fixture()
        for a, b, _, _ in profile.IDENTITIES:
            for target in (a, a | 1, a + 2, b - 2):
                with self.subTest(target=target), self.assertRaises(ValueError):
                    match.function_address_target(f"func_{target:08X}", json.loads(self.mapping),
                                                  BASE, len(self.body), len(self.rom))
                with self.subTest(target=target), self.assertRaises(ValueError):
                    match.parse_data_symbols(json.dumps({"object": f"0x{target:08X}"}).encode())
        for name in ("__truncdfsf2_alias", "func_08143980", "func_08143981", "func_08144314"):
            altered = copy.deepcopy(self.original)
            for symbol in altered["symbols"]:
                if symbol["name"] == "__truncdfsf2": symbol["name"] = name
            with self.subTest(name=name), self.assertRaises(ValueError): self.binding(altered)
        for key, value in (("section", 1), ("bind", 2), ("type", 1), ("value", 2)):
            altered = copy.deepcopy(self.original)
            for symbol in altered["symbols"]:
                if symbol["name"] == "__truncdfsf2": symbol[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError): self.binding(altered)
        with self.assertRaisesRegex(ValueError, "noncanonical addend"):
            self.fixture(assembly="push {lr}\nbl __truncdfsf2+2\npop {r1}\nbx r1")

    def test_typed_linking_rejects_changed_bytes_and_missing_binding(self):
        self.fixture()
        targets = {name: profile.OPERATIONS[name] for name in self.bindings.values()}
        targets["func_08000200"] = 0x08000200
        altered = copy.deepcopy(self.linked)
        text = bytearray(altered["text"]); text[0] ^= 1; altered["text"] = bytes(text)
        with self.assertRaisesRegex(ValueError, "outside permitted relocations"):
            match.linked_function_bytes(self.original, altered, "func_08000000", BASE,
                                        self.calls, targets, {}, double_bindings=self.bindings)
        with self.assertRaises(ValueError):
            match.linked_function_bytes(self.original, self.linked, "func_08000000", BASE,
                                        self.calls, targets, {})
        incomplete = {site: name for site, name in self.bindings.items() if name != "__truncdfsf2"}
        with self.assertRaisesRegex(ValueError, "incomplete or mixed"):
            match.linked_function_bytes(self.original, self.linked, "func_08000000", BASE,
                                        self.calls, targets, {}, double_bindings=incomplete)

    def test_complete_caller_manifest_and_old_runtime_ids_reject(self):
        self.fixture()
        for key, value in (("frame", not self.manifest["frame"]), ("calls", []), ("dependencies", []),
                           ("runtime", "agbcc-thumb-df-convert-sub-div-closure-v1"),
                           ("abi", "agbcc-thumb-df-mixed-integer-v1"), ("semantics", "IEEE754")):
            altered = copy.deepcopy(self.manifest); altered[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError): self.verify(altered)
        for changed in (self.body[:-2], self.body + b"\0\0", bytes([self.body[0] ^ 1]) + self.body[1:]):
            with self.subTest(size=len(changed)), self.assertRaises(ValueError):
                profile.verify(changed, BASE, self.rom, self.mapping, self.index, self.manifest)

    def test_mixed_profiles_and_data_relocations_still_reject(self):
        self.fixture()
        for other in ("buffer_proof", "call_resolver", "switch_relocations", "switch_data_relocations",
                      "udivsi3_context", "modsi3_context", "divsi3_context", "umodsi3_context",
                      "ashldi3_context", "inert_spin_context", "float_context", "function_thunk_context"):
            with self.subTest(other=other), self.assertRaises(ValueError):
                match.verify_leaf_instructions(self.body, BASE, True, self.calls,
                    double_context=(self.rom, self.mapping, self.index, self.bindings), **{other: {}})
        for other in ("udivsi3_bindings", "modsi3_bindings", "divsi3_bindings", "umodsi3_bindings",
                      "ashldi3_bindings", "float_bindings", "function_relocations", "switch_relocations"):
            with self.subTest(other=other), self.assertRaises(ValueError):
                self.binding(**{other: {1: "unsupported"}})
        with self.assertRaises(ValueError): self.binding(data_mapping=b'{}')
        changed = copy.copy(self.args); changed.flags = "-mthumb-interwork -O1"
        with self.assertRaises(ValueError): profile.fixed_configuration(changed)
        with self.assertRaises(ValueError):
            self.fixture(source="extern double object; float func_08000000(void) { return (float)object; }")

    def test_native_report_replay_and_stale_inputs_reject(self):
        self.fixture()
        report = self.native_report()
        self.assertIn(f"* verification: `{profile.SCHEMA}`", report)
        opening, reading = self.patched_rom()
        with opening, reading, redirect_stdout(io.StringIO()):
            self.assertTrue(evidence.report_matches(report, self.root, BASE))
            for changed in (report + "\n* software float: forged", report + "\n* function address: forged",
                            report + "\n* software double: duplicate", report.replace("-O2", "-O1"),
                            report.replace(profile.RUNTIME, "obsolete-runtime"),
                            report.replace('"dependencies":[', '"dependencies":[],'),
                            report.replace("* software double proof SHA-256: `", "* software double proof SHA-256: `0")):
                with self.subTest(changed=changed[-100:]):
                    self.assertFalse(evidence.report_matches(changed, self.root, BASE))
            for name in ("symbols/functions.txt", "config/functions.json"):
                path = self.root / name; original = path.read_bytes(); path.write_bytes(original + b"\n")
                with self.subTest(name=name): self.assertFalse(evidence.report_matches(report, self.root, BASE))
                path.write_bytes(original)
            original_rom = self.rom
            changed_rom = bytearray(original_rom); changed_rom[-1] ^= 1
            self.rom = bytes(changed_rom)
            self.assertFalse(evidence.report_matches(report, self.root, BASE))
            self.rom = original_rom
            source = self.root / "src/08000000.c"
            original_digest = evidence.source_fingerprint(self.root, BASE)
            source.write_text(source.read_text().replace("/ 100.0", "/ 101.0"))
            new_digest = evidence.source_fingerprint(self.root, BASE)
            forged = report.replace(original_digest, new_digest).replace(
                profile.fingerprint(BASE, self.body, self.manifest, original_digest,
                                    self.mapping, self.index, self.rom),
                profile.fingerprint(BASE, self.body, self.manifest, new_digest,
                                    self.mapping, self.index, self.rom))
            self.assertFalse(evidence.report_matches(report, self.root, BASE))
            self.assertFalse(evidence.report_matches(forged, self.root, BASE))


    def test_native_comparison_and_all_binary64_arithmetic_symbols(self):
        source = """double func_08000000(double a, double b)
{
    if (a < b) return (a - b) / (a * b);
    return a + b;
}
"""
        self.fixture(source)
        expected = {"__ltdf2", "__muldf3", "__subdf3", "__divdf3", "__adddf3"}
        self.assertEqual(set(self.bindings.values()), expected)
        self.assertEqual({row["name"] for row in self.original["symbols"]
                          if row["name"] and not row["section"]}, expected)
        self.assertEqual(len(self.verify()), len(self.instructions))
        report = self.native_report()
        opening, reading = self.patched_rom()
        with opening, reading:
            self.assertTrue(profile.report_matches(report, self.root, BASE))
            (self.root / "src/08000000.c").write_text(source.replace("a * b", "a + b"))
            self.assertFalse(profile.report_matches(report, self.root, BASE))

    def test_canonical_add_multiply_addresses_and_wrong_link_rejected(self):
        self.assertEqual(profile.OPERATIONS["__adddf3"], 0x08143080)
        self.assertEqual(profile.OPERATIONS["__muldf3"], 0x081430F0)
        for operator, name, target, wrong in (("+", "__adddf3", 0x08143080, 0x081430F0),
                                               ("*", "__muldf3", 0x081430F0, 0x08143080)):
            with self.subTest(operator=operator):
                self.fixture("double func_08000000(double a, double b) { return a " +
                             operator + " b; }\n")
                self.assertEqual(set(self.bindings.values()), {name})
                self.assertEqual(set(self.calls.values()), {target})
                site = next(iter(self.bindings))
                # A body linked to the other runtime is not a canonical caller,
                # even though both complete runtime identities are approved.
                displacement = wrong - site - 4
                words = (0xF000 | ((displacement >> 12) & 0x7FF),
                         0xF800 | ((displacement >> 1) & 0x7FF))
                altered = copy.deepcopy(self.linked)
                raw = bytearray(altered["text"])
                struct.pack_into("<HH", raw, site - BASE, *words)
                altered["text"] = bytes(raw)
                next(row for row in altered["symbols"] if row["name"] == name)["value"] = wrong | 1
                with self.assertRaises(ValueError):
                    match.linked_function_bytes(self.original, altered, "func_08000000", BASE,
                        self.calls, {name: target}, {}, double_bindings=self.bindings)
                wrong_calls = dict(self.calls); wrong_calls[site] = wrong
                with self.assertRaises(ValueError):
                    match.verify_leaf_instructions(bytes(raw), BASE, True, wrong_calls,
                        double_context=(self.rom, self.mapping, self.index, self.bindings))

    def test_native_arithmetic_comparison_closure_exact_output_contracts(self):
        self.fixture("double func_08000000(double a, double b) { return a*b; }\n")
        proofs = profile.prove_arithmetic_comparison_closure(self.rom, json.loads(self.mapping))
        self.assertEqual(set(proofs), set(profile.ARITHMETIC_COMPARISON_CLOSURE))
        for start, formal in ((0x08142D34, 1), (0x08142E10, 2)):
            self.assertEqual(proofs[start]["writes"], [(formal, n, 4) for n in range(0, 20, 4)])
        for start in (0x08143080, 0x081430B4, 0x0814339C, 0x0814379C):
            self.assertFalse(proofs[start]["writes"])
            self.assertTrue(proofs[start]["returns"])

    def test_comparison_runtime_identity_and_dual_index_ownership(self):
        self.fixture("int func_08000000(double a, double b) { return a<b; }\n")
        for address in (0x08143080, 0x08142E10, 0x08143528, 0x0814379C):
            changed = bytearray(self.rom); changed[address - BASE] ^= 1
            with self.subTest(address=address), self.assertRaisesRegex(ValueError, "runtime identity"):
                profile.verify_identity(bytes(changed), self.mapping, self.index)
        entries = json.loads(self.mapping)
        for kind in ("duplicate", "mode", "short", "count", "odd", "missing"):
            changed = copy.deepcopy(entries)
            row = next(row for row in changed if row["rom"] == "0x0814379C")
            if kind == "duplicate": changed.append(copy.deepcopy(row))
            elif kind == "mode": row["mode"] = "arm"
            elif kind == "short": row["end"] = "0x081437E8"
            elif kind == "count": row["instrs"] += 1
            elif kind == "odd": row["rom"] = "0x0814379D"
            else: changed.remove(row)
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                profile.verify_identity(self.rom, json.dumps(changed).encode(), self.index)
        changed = self.index.replace(b"081437EA 78 36", b"081437EA 78 37")
        self.assertNotEqual(changed, self.index)
        with self.assertRaises(ValueError): profile.verify_identity(self.rom, self.mapping, changed)

    def test_arithmetic_kernel_write_and_comparison_restore_are_proved(self):
        self.fixture("double func_08000000(double a, double b) { return a*b; }\n")
        from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
        decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
        entries = json.loads(self.mapping)
        proofs = profile.prove_arithmetic_comparison_closure(self.rom, entries)
        for start, kind in ((0x08142E10, "store"), (0x0814379C, "restore")):
            instructions = [i for a, b in proofs[start]["layout"]["code_ranges"]
                            for i in decoder.disasm(self.rom[int(a, 16)-BASE:int(b, 16)-BASE], int(a, 16))]
            if kind == "store":
                instruction = next(i for i in instructions if i.mnemonic == "str" and "#0x10]" in i.op_str)
                word = struct.unpack_from("<H", self.rom, instruction.address-BASE)[0]
                word = (word & ~0x7C0) | (5 << 6)  # Escape the five-word formal result.
            else:
                instruction = next(i for i in instructions if i.mnemonic == "pop" and "r4" in i.op_str)
                word = struct.unpack_from("<H", self.rom, instruction.address-BASE)[0] ^ ((1 << 4) | (1 << 5))
            changed = bytearray(self.rom); struct.pack_into("<H", changed, instruction.address-BASE, word)
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                profile.prove_arithmetic_comparison_closure(bytes(changed), entries)

    def test_shared_comparison_needs_exact_canonical_context(self):
        self.fixture("double func_08000000(double a, double b) { return a<b ? a*b : a+b; }\n")
        site = next(site for site, name in self.bindings.items() if name == "__ltdf2")
        for name in ("func_0814379C", "__gtdf2", "__ltdf2_alias"):
            altered = copy.deepcopy(self.original)
            next(row for row in altered["symbols"] if row["name"] == "__ltdf2")["name"] = name
            with self.subTest(name=name), self.assertRaises(ValueError): self.binding(altered)
        for name in ("__gtdf2", "func_0814379C"):
            bindings = dict(self.bindings)
            bindings[site] = name
            with self.subTest(name=name), self.assertRaises(ValueError):
                match.verify_leaf_instructions(self.body, BASE, True, self.calls,
                    double_context=(self.rom, self.mapping, self.index, bindings))
        with self.assertRaises(ValueError):
            match.verify_leaf_instructions(self.body, BASE, True, self.calls,
                double_context=(self.rom, self.mapping, self.index, self.bindings),
                float_context=(self.rom, self.mapping, self.index, {site: "__ltdf2"}))
        with self.assertRaises(ValueError): self.binding(float_bindings={})
        with self.assertRaises(ValueError):
            self.fixture("double func_08000000(float a, float b) { return (double)(a*b); }\n")

    def test_comparison_manifest_runtime_version_and_dependency_replay(self):
        self.fixture("double func_08000000(double a, double b) { return a<b ? a*b : a+b; }\n")
        for key, value in (("runtime", "agbcc-thumb-df-convert-add-sub-div-trunc-fix-mod-s16-closure-v5"),
                           ("dependencies", self.manifest["dependencies"][:-1]), ("calls", [])):
            manifest = copy.deepcopy(self.manifest); manifest[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError): self.verify(manifest)
        altered = copy.deepcopy(self.linked)
        body = bytearray(altered["text"]); body[0] ^= 1; altered["text"] = bytes(body)
        targets = {name: profile.OPERATIONS[name] for name in self.bindings.values()}
        with self.assertRaises(ValueError):
            match.linked_function_bytes(self.original, altered, "func_08000000", BASE,
                                        self.calls, targets, {}, double_bindings=self.bindings)


if __name__ == "__main__":
    unittest.main()
