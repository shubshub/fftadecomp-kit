"""Synthetic, compiler-free coverage of switch function literals (u16-scalars-functions-v1/v2)."""

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
CALLBACK = BASE + 0x1000
OTHER = BASE + 0x1010
V1 = "elf-symbol-thumb-switch-data-u16-scalars-functions-v1"
V2 = "elf-symbol-thumb-switch-data-u16-scalars-functions-v2"
POLICY = "canonical-function-literals-v1"


def fixture(pool=(), *, function=CALLBACK | 1, pointer_reader=False, branch_to_function=False):
    """A guarded table with a typed object, a u16 scalar and a function literal.

    `pool` lists object/scalar words interposed between the dispatch and the
    table pointer (empty is the fixed v1 shape). The cases read a late object,
    a late u16 scalar and a late function word, the function word as an
    ordinary register value (or, with `branch_to_function`, as a branch target).
    """
    body, labels, fixups = bytearray(), {}, []

    def half(value):
        body.extend(struct.pack("<H", value))

    def label(name):
        labels[name] = len(body)

    def emit(kind, name, register=0):
        fixups.append((len(body), kind, name, register))
        body.extend(bytes(4 if kind == "word" else 2))

    if pointer_reader:
        emit("ldr", "pointer", 1)
    for index, kind in enumerate(pool):
        emit("ldr", f"pool{index}", 3 if kind == "scalar" else 2)
    if "scalar" in pool:
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
    for index, kind in enumerate(pool):
        label(f"pool{index}")
        body.extend(struct.pack("<I", OBJECT if kind == "object" else
                                CALLBACK | 1 if kind == "function" else 0x2FC1))
    label("pointer")
    emit("word", "table")
    label("table")
    emit("word", "case0")
    emit("word", "case1")
    label("case0")
    emit("ldr", "late_object", 1)
    emit("ldr", "late_function", 0)
    if branch_to_function:
        half(0x4700)  # bx r0
    half(0x2001)  # movs r0,#1
    label("skip0")
    emit("b", "done")
    label("case1")
    emit("ldr", "late_scalar", 1)
    half(0x2002)  # movs r0,#2
    emit("b", "done")
    label("default")
    half(0x2000)  # movs r0,#0
    label("done")
    half(0x4770)  # bx lr
    while len(body) % 4:
        half(0)
    label("late_object")
    body.extend(struct.pack("<I", OBJECT + 8))
    label("late_scalar")
    body.extend(struct.pack("<I", 0x444))
    label("late_function")
    body.extend(struct.pack("<I", function))
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
    descriptor = {name: labels[name] for name in ("comparison", "guard", "dispatch", "default", "table")}
    descriptor.update(literal=labels["pointer"], bound=1, relocations=[
        [labels["pointer"], labels["table"]], [labels["table"], labels["case0"]],
        [labels["table"] + 4, labels["case1"]]])
    manifest = {"calls": [], "switch": descriptor,
                "data": [[labels[f"pool{index}"], "g_object", 0]
                         for index, kind in enumerate(pool) if kind == "object"] +
                        [[labels["late_object"], "g_object", 8]],
                "data_policy": "complete-reachable-object-words-v1",
                "scalar_policy": "complete-reachable-u16-scalar-words-v1",
                "scalars": [[labels[f"pool{index}"], 0x2FC1]
                            for index, kind in enumerate(pool) if kind == "scalar"] +
                           [[labels["late_scalar"], 0x444]],
                "function_policy": POLICY,
                "functions": [[labels[f"pool{index}"], f"func_{CALLBACK:08X}"]
                              for index, kind in enumerate(pool) if kind == "function"] +
                             [[labels["late_function"], f"func_{CALLBACK:08X}"]]}
    if pool:
        manifest["pool_policy"] = "dispatch-identified-table-pointer-v1"
    mapping = [{"rom": f"0x{BASE:08X}", "end": f"0x{BASE + len(body):08X}", "mode": "thumb"},
               {"rom": f"0x{CALLBACK:08X}", "end": f"0x{CALLBACK + 2:08X}", "mode": "thumb"},
               {"rom": f"0x{OTHER:08X}", "end": f"0x{OTHER + 2:08X}", "mode": "thumb"}]
    return body, labels, manifest, mapping


def image(body):
    rom = bytearray(bytes(body).ljust(OTHER - BASE + 2, b"\0"))
    struct.pack_into("<H", rom, CALLBACK - BASE, 0x4770)
    struct.pack_into("<H", rom, OTHER - BASE, 0x4770)
    return bytes(rom)


def verify(body, manifest, mapping, objects=None):
    objects = objects or {"g_object": f"0x{OBJECT:08X}"}
    return match.verify_switches(bytes(body), BASE, image(body), json.dumps(mapping).encode(),
                                 manifest, data_mapping=json.dumps(objects).encode())


class VerificationTests(unittest.TestCase):
    def test_both_pool_shapes_verify_with_a_function_literal(self):
        for pool in ((), ("object", "scalar")):
            with self.subTest(pool=pool):
                body, _, manifest, mapping = fixture(pool)
                _, summary = verify(body, manifest, mapping)
                self.assertEqual(summary, "closed leaf CFG")

    def test_existing_policies_still_refuse_the_function_word(self):
        for pool in ((), ("object", "scalar")):
            with self.subTest(pool=pool):
                body, _, manifest, mapping = fixture(pool)
                for field in ("function_policy", "functions"):
                    manifest.pop(field)
                with self.assertRaisesRegex(ValueError, "only u16"):
                    verify(body, manifest, mapping)

    def test_policy_marker_and_record_list_are_exact(self):
        body, _, manifest, mapping = fixture()
        with self.assertRaisesRegex(ValueError, "canonical policy marker"):
            verify(body, dict(manifest, function_policy="other-policy"), mapping)
        for field in ("function_policy", "functions"):
            changed = copy.deepcopy(manifest)
            changed.pop(field)
            with self.subTest(field=field), self.assertRaises(ValueError):
                verify(body, changed, mapping)
        with self.assertRaisesRegex(ValueError, "finite nonempty"):
            verify(body, dict(manifest, functions=[]), mapping)
        without_scalars = copy.deepcopy(manifest)
        for field in ("scalar_policy", "scalars"):
            without_scalars.pop(field)
        with self.assertRaisesRegex(ValueError, "invalid switch manifest"):
            verify(body, without_scalars, mapping)

    def test_function_word_must_equal_its_indexed_thumb_entry(self):
        body, labels, manifest, mapping = fixture()
        offset = labels["late_function"]
        for name, message in ((f"func_{OTHER:08X}", "does not equal its binding"),
                              ("func_08002000", "unknown, ambiguous"),
                              ("g_object", "canonical addressed function"),
                              (f"func_{BASE:08X}", "self or intra-function")):
            changed = copy.deepcopy(manifest)
            changed["functions"] = [[offset, name]]
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, message):
                verify(body, changed, mapping)
        # The word without its Thumb bit is not the canonical function value.
        body, _, manifest, mapping = fixture(function=CALLBACK)
        with self.assertRaisesRegex(ValueError, "does not equal its binding"):
            verify(body, manifest, mapping)

    def test_function_words_cannot_overlap_other_roles(self):
        body, labels, manifest, mapping = fixture(("object", "scalar"))
        for offset in (labels["pointer"], labels["table"], labels["pool0"], labels["pool1"],
                       labels["late_scalar"], labels["late_function"] + 2):
            changed = copy.deepcopy(manifest)
            changed["functions"] = sorted(changed["functions"] + [[offset, f"func_{CALLBACK:08X}"]])
            with self.subTest(offset=offset), self.assertRaisesRegex(ValueError, "nonoverlapping words"):
                verify(body, changed, mapping)

    def test_interposed_pool_words_still_exclude_function_literals(self):
        body, _, manifest, mapping = fixture(("function", "scalar"))
        with self.assertRaisesRegex(ValueError, "typed objects or u16 scalars"):
            verify(body, manifest, mapping)

    def test_data_cannot_launder_a_code_entry_or_the_callers_span(self):
        for value, message in ((CALLBACK, "cannot bind code entries or their own span"),
                               (CALLBACK | 1, "cannot bind code entries or their own span"),
                               (BASE + 4, "own span|object word")):
            body, labels, manifest, mapping = fixture()
            struct.pack_into("<I", body, labels["late_object"], value)
            objects = {"g_object": f"0x{value - 8:08X}"}
            with self.subTest(value=hex(value)), self.assertRaisesRegex(ValueError, message):
                verify(body, manifest, mapping, objects)

    def test_table_pointer_has_no_other_reader_in_either_shape(self):
        for pool in ((), ("object", "scalar")):
            with self.subTest(pool=pool):
                body, _, manifest, mapping = fixture(pool, pointer_reader=True)
                with self.assertRaisesRegex(ValueError, "read only by its dispatch load"):
                    verify(body, manifest, mapping)

    def test_function_literal_is_never_a_branch_target(self):
        body, _, manifest, mapping = fixture(branch_to_function=True)
        with self.assertRaisesRegex(ValueError, "indirect control flow"):
            verify(body, manifest, mapping)

    def test_unread_function_word_is_refused(self):
        body, labels, manifest, mapping = fixture()
        changed = copy.deepcopy(manifest)
        changed["functions"].append([labels["late_function"] + 4, f"func_{CALLBACK:08X}"])
        extended = bytes(body) + struct.pack("<I", CALLBACK | 1)
        mapping = copy.deepcopy(mapping)
        mapping[0]["end"] = f"0x{BASE + len(extended):08X}"
        with self.assertRaisesRegex(ValueError, "literal-word coverage"):
            verify(extended, changed, mapping)


class ConfigurationTests(unittest.TestCase):
    def test_opt_in_is_boolean_and_isolated(self):
        match.check_switch_function_opt_in(False, False, True, None, None)
        match.check_switch_function_opt_in(True, True, False, {}, {})
        for arguments in ((1, True, False, {}, {}), (True, False, False, {}, {}),
                          (True, True, True, {}, {}), (True, True, False, None, {}),
                          (True, True, False, {}, None)):
            with self.subTest(arguments=arguments), self.assertRaises(ValueError):
                match.check_switch_function_opt_in(*arguments)

    def test_selectors_use_the_isolated_fixed_configuration(self):
        for selector in (evidence.SWITCH_FUNCTION_U16_SCALAR_SELECTOR,
                         evidence.SWITCH_FUNCTION_POOL_U16_SCALAR_SELECTOR):
            args = SimpleNamespace(
                switch_data_profile=selector,
                mode="thumb", control_flow_profile="ordinary", signed_quotient_profile=None,
                signed_runtime_profile=None, addressed_signed_runtime_profile=None,
                unsigned_runtime_profile=None, software_double_profile=None,
                software_double_remainder_profile=None, function_address_profile=None,
                switch_profile=None, owner_runtime_profile=None,
                cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
            match.switch_u16_scalar_configuration(args)
            args.function_address_profile = "canonical-thunks-v1"
            with self.subTest(selector=selector), self.assertRaisesRegex(ValueError, "isolated explicit selector"):
                match.switch_u16_scalar_configuration(args)


class ReportTests(unittest.TestCase):
    def setUp(self):
        scratch = TASK / "build"
        scratch.mkdir(exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="switch_function_literals_", dir=scratch)
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        (self.root / "src").mkdir()
        (self.root / "include").mkdir()
        (self.root / "src/08000000.c").write_text("unsigned func_08000000(unsigned x);\n")
        self.source = evidence.source_fingerprint(self.root, BASE)
        self.objects = json.dumps({"g_object": f"0x{OBJECT:08X}"}).encode()
        self.rom_path = self.root / "synthetic-image.bin"
        self.use(())

    def use(self, pool):
        self.body, _, self.manifest, mapping = fixture(pool)
        self.functions = json.dumps(mapping).encode()
        self.rom_path.write_bytes(image(self.body))
        self.schema, self.summary = (V2, evidence.SWITCH_FUNCTION_POOL_U16_SCALAR_SUMMARY) if pool else \
            (V1, evidence.SWITCH_FUNCTION_U16_SCALAR_SUMMARY)
        for name, value in (("mapping_snapshot", self.functions), ("data_snapshot", self.objects),
                            ("report_rom_path", str(self.rom_path))):
            patcher = mock.patch.object(evidence, name, return_value=value)
            patcher.start()
            self.addCleanup(patcher.stop)

    def report(self, manifest=None, fingerprint=None):
        manifest = self.manifest if manifest is None else manifest
        fingerprint = fingerprint or evidence.switch_function_u16_scalar_fingerprint(BASE, self.body, manifest)
        return "\n".join([
            f"* verification: `{self.schema}`",
            f"* source SHA-256: `{self.source}`",
            f"* mapping SHA-256: `{evidence.mapping_fingerprint(self.functions)}`",
            f"* data symbols SHA-256: `{evidence.mapping_fingerprint(self.objects)}`",
            f"* switches: {self.summary}",
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

    def test_reports_revalidate_in_both_shapes(self):
        for pool in ((), ("object", "scalar")):
            with self.subTest(pool=pool):
                self.use(pool)
                report = self.report()
                self.assertTrue(self.valid(report))
                with mock.patch.object(evidence.empty_body, "has_empty_body", return_value=False):
                    self.assertTrue(evidence.report_matches(report, self.root, BASE))

    def test_tampered_policy_schema_summary_and_fingerprint_reject(self):
        report = self.report()
        without = copy.deepcopy(self.manifest)
        for field in ("function_policy", "functions"):
            without.pop(field)
        plain = evidence.switch_u16_scalar_fingerprint(BASE, self.body, self.manifest)
        variants = [
            self.report(without),
            self.report(dict(self.manifest, function_policy="other-policy")),
            report.replace(V1, evidence.SWITCH_U16_SCALAR_SCHEMA),
            report.replace(V1, V2),
            report.replace(self.summary, evidence.SWITCH_U16_SCALAR_SUMMARY),
            self.report(fingerprint=plain),
            report + f"\n* verification: `{V1}`",
            report + "\n* function addresses: x",
        ]
        self.assertNotEqual(plain, evidence.switch_function_u16_scalar_fingerprint(BASE, self.body, self.manifest))
        for index, variant in enumerate(variants):
            with self.subTest(index=index):
                self.assertFalse(self.valid(variant))

    def test_function_free_report_cannot_be_relabelled(self):
        plain = copy.deepcopy(self.manifest)
        for field in ("function_policy", "functions"):
            plain.pop(field)
        self.assertFalse(self.valid(self.report(
            plain, evidence.switch_function_u16_scalar_fingerprint(BASE, self.body, plain))))

    def test_tampered_bytes_and_function_record_reject(self):
        changed = copy.deepcopy(self.manifest)
        changed["functions"][0][1] = f"func_{OTHER:08X}"
        self.assertFalse(self.valid(self.report(changed)))
        altered = bytearray(image(self.body))
        altered[len(self.body) - 1] ^= 1
        self.rom_path.write_bytes(altered)
        self.assertFalse(self.valid(self.report()))

    def test_rebuild_forwards_both_selectors(self):
        import rebuild
        self.enterContext(mock.patch.object(evidence.empty_body, "has_empty_body", return_value=False))
        for pool, selector in (((), evidence.SWITCH_FUNCTION_U16_SCALAR_SELECTOR),
                               (("object", "scalar"), evidence.SWITCH_FUNCTION_POOL_U16_SCALAR_SELECTOR)):
            with self.subTest(selector=selector):
                self.use(pool)
                self.assertEqual(rebuild.saved_profile_arguments(self.report(), self.root, BASE),
                                 ["--switch-data-profile", selector])
                with self.assertRaisesRegex(ValueError, "invalid saved profile report"):
                    rebuild.saved_profile_arguments(
                        self.report().replace(self.schema, evidence.SWITCH_U16_SCALAR_SCHEMA), self.root, BASE)

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
            self.assertEqual(command[command.index("--switch-data-profile") + 1],
                             evidence.SWITCH_FUNCTION_U16_SCALAR_SELECTOR)
            return subprocess.CompletedProcess(command, 0, output, "")
        with mock.patch.object(status.subprocess, "run", side_effect=invoke) as native:
            result = status.collect(str(self.root), True)
            self.assertEqual(result[1], 1)
            self.assertEqual(result[4], [])
            native.assert_called_once()



SOURCE = """extern unsigned g_object;
extern void func_08001000(void);
extern unsigned func_08001010(void (*callback)(void), unsigned value);
unsigned func_08000000(unsigned mode)
{
    switch (mode) {
    case 0:
        return func_08001010(func_08001000, g_object);
    case 1:
        return g_object + 0x444;
    case 2:
        return func_08001010(0, 0x555);
    case 3:
        g_object = 3;
        break;
    case 4:
        g_object = 9;
        break;
    }
    return 0;
}
"""


class CompiledSourceTests(unittest.TestCase):
    """A fixed-O2 synthetic switch passing a function address: refused by
    default, admitted end to end by the explicit v1 selector."""

    def setUp(self):
        import argparse
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", TASK / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="switch_function_elf_", dir=scratch)
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        for name in ("src", "include", "config", "symbols", "docs/match"):
            (self.root / name).mkdir(parents=True)
        (self.root / "src/08000000.c").write_text(SOURCE)
        self.args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP,
            assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY,
            linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        self.runner = match.Runner(match.DEFAULT_CC, root=self.root, timeout=120)
        self.objects = json.dumps({"g_object": f"0x{OBJECT:08X}"}).encode()
        with self.runner.workspace() as workspace:
            _, _, self.original = match.compile_object(self.runner, workspace, self.args, self.root,
                                                       BASE, "src/08000000.c")
            size = match.function_record(self.original, "func_08000000", BASE, True)[0]["size"]
        self.mapping = json.dumps([
            {"rom": "0x08000000", "end": f"0x{BASE + size:08X}", "mode": "thumb"},
            {"rom": f"0x{CALLBACK:08X}", "end": f"0x{CALLBACK + 2:08X}", "mode": "thumb"},
            {"rom": f"0x{OTHER:08X}", "end": f"0x{OTHER + 2:08X}", "mode": "thumb"}]).encode()
        self.size = size

    def link(self, **options):
        functions, switches = {}, {}
        with self.runner.workspace() as workspace:
            match.compile_object(self.runner, workspace, self.args, self.root, BASE, "src/08000000.c")
            body, calls, data = match.link_calls(
                self.runner, workspace, self.args, self.original, BASE, self.mapping, 0x2000, b"",
                self.objects, functions, switches, allow_switch_data=True, **options)
        return body, calls, data, functions, switches

    def test_default_linking_refuses_and_selector_admits(self):
        with self.assertRaisesRegex(ValueError, "switch evidence excludes"):
            self.link()
        with self.assertRaisesRegex(ValueError, "isolated switch-data and function bindings"):
            self.link(switch_function_literals=True, function_thunks=True)
        body, calls, data, functions, switches = self.link(switch_function_literals=True)
        self.assertEqual({name for name, _ in functions.values()}, {f"func_{CALLBACK:08X}"})
        self.assertEqual(set(calls.values()), {OTHER})
        self.assertTrue(switches and data)
        rom = bytearray(0x2000)
        rom[:len(body)] = body
        for entry in (CALLBACK, OTHER):
            struct.pack_into("<H", rom, entry - BASE, 0x4770)
        for path, content in (("config/functions.json", self.mapping),
                              ("config/data_symbols.json", self.objects),
                              ("symbols/functions.txt",
                               f"08000000 {BASE + self.size:08X} {self.size} 1 return\n".encode()),
                              ("synthetic.rom", bytes(rom))):
            (self.root / path).write_bytes(content)
        from contextlib import redirect_stdout
        import io
        self.enterContext(mock.patch.dict(os.environ, {"FFTA_ROM": str(self.root / "synthetic.rom"),
                                                       "TMPDIR": str(self.root)}))
        for selector in (None, evidence.SWITCH_U16_SCALAR_SELECTOR):
            argv = ["match.py", "--root", str(self.root), "--no-write", "0x08000000"]
            if selector:
                argv[1:1] = ["--switch-data-profile", selector]
            with self.subTest(selector=selector), mock.patch.object(sys, "argv", argv), \
                    redirect_stdout(io.StringIO()), self.assertRaises(SystemExit):
                match.main()
        argv = ["match.py", "--root", str(self.root), "--switch-data-profile",
                evidence.SWITCH_FUNCTION_U16_SCALAR_SELECTOR, "0x08000000"]
        with mock.patch.object(sys, "argv", argv), redirect_stdout(io.StringIO()):
            self.assertEqual(match.main(), 0)
        report = (self.root / "docs/match/08000000.md").read_text()
        self.assertIn(f"* verification: `{V1}`", report.splitlines())
        self.assertTrue(evidence.report_matches(report, self.root, BASE))
        (self.root / "src/08000000.c").write_text(SOURCE.replace("0x555", "0x556"))
        self.assertFalse(evidence.report_matches(report, self.root, BASE))


if __name__ == "__main__":
    unittest.main()
