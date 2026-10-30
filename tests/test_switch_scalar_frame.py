import contextlib
import copy
from dataclasses import replace
import hashlib
import io
import json
import os
from pathlib import Path
import struct
import subprocess
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import match
import match_evidence
import rebuild
import status
import switch_constants_profile as profile
import switch_placement as placement
from test_switch_constants import SOURCE, fixed_args, assemble, fixture_assembly, ordinary_link
import test_switch_placement as placement_tests


def natural_source(repetitions):
    declarations = "\n".join(f"extern unsigned int func_{0x08001000 + index * 2:08X}("
        "unsigned int, unsigned int, unsigned int, unsigned int, unsigned int, unsigned int);"
        for index in range(6))
    source = declarations + "\nunsigned int func_08000000(unsigned int selector, unsigned int left, " \
        "unsigned int right, unsigned int fourth, unsigned int fifth, unsigned int sixth)\n{\n" \
        "    left &= 0xFF00FF00;\n    right &= 0x0F0F0F0F;\n    switch (selector) {\n"
    for selector in range(6):
        source += f"    case {selector}:\n"
        source += f"        left = func_{0x08001000 + selector * 2:08X}(left, right, selector, fourth, fifth, sixth);\n" * repetitions
        source += "        return left;\n"
    return source + "    default: return right;\n    }\n}\n"


def record(name, value):
    destination = os.environ.get("FFTA_SCALAR_FRAME_EVIDENCE")
    if destination:
        path = Path(destination)
        document = json.loads(path.read_text()) if path.exists() else {}
        document.setdefault(name, []).append(value)
        path.write_text(json.dumps(document, indent=2) + "\n")


class ScalarFrameTests(unittest.TestCase):
    policy = profile.FRAME_POLICY
    setUp = placement_tests.PlacementTests.setUp
    trusted_fixture = placement_tests.PlacementTests.trusted_fixture
    admit = placement_tests.PlacementTests.admit
    linked_capture_drift = placement_tests.PlacementTests.linked_capture_drift
    nonregular_capture = placement_tests.PlacementTests.nonregular_capture
    test_linked_capture_bytes_and_replacement_reject = placement_tests.PlacementTests.test_linked_capture_bytes_and_replacement_reject
    test_linked_capture_final_boundary_rejects = placement_tests.PlacementTests.test_linked_capture_final_boundary_rejects
    test_nonregular_initial_capture_rejects_without_fallback = placement_tests.PlacementTests.test_nonregular_initial_capture_rejects_without_fallback
    test_nonregular_final_capture_rejects_without_fallback = placement_tests.PlacementTests.test_nonregular_final_capture_rejects_without_fallback
    test_raw_assembly_stage_and_object_drift_reject = placement_tests.PlacementTests.test_raw_assembly_stage_and_object_drift_reject
    test_late_status_rebuild_and_external_prefix_exclusion = placement_tests.PlacementTests.test_late_status_rebuild_and_external_prefix_exclusion

    def prepare(self, address=0x08000000, repetitions=1):
        return placement_tests.PlacementTests.prepare(self, address, natural_source(repetitions), self.policy)

    def synthetic(self, address, **options):
        assembly = fixture_assembly(prefix="sub sp, #8", **options)
        assembly = assembly.replace("bl func_08001000\npop", "bl func_08001000\nadd sp, #8\npop") \
            if options.get("call") else assembly.replace("bx lr", "add sp, #8\nbx lr")
        assembly = assembly.replace("08000000", f"{address:08X}")
        if address % 4:
            assembly = assembly.replace(".thumb_func\n", ".balign 4, 0\n.space 2, 0\n.thumb_func\n", 1)
        original = assemble(self.root, assembly)
        image = match.elf_image(original)
        size = next(item["size"] for item in image["symbols"] if item["name"] == f"func_{address:08X}")
        mapping = json.dumps([{"rom": f"0x{address:08X}", "end": f"0x{address + size:08X}", "mode": "thumb"},
                              {"rom": "0x08001000", "end": "0x08001002", "mode": "thumb"}]).encode()
        return original, mapping

    test_identical_linked_bytes_raw_attacks_both_words_and_origins = placement_tests.PlacementTests.test_identical_linked_bytes_raw_attacks_both_words_and_origins
    test_raw_and_derived_relocation_coordinates_cannot_be_confused = placement_tests.PlacementTests.test_raw_and_derived_relocation_coordinates_cannot_be_confused
    test_original_and_linked_envelope_mutations = placement_tests.PlacementTests.test_original_and_linked_envelope_mutations

    def structural(self, assembly=None):
        if assembly is None:
            assembly = fixture_assembly(call=True, prefix="sub sp, #8\nstr r3, [sp]\nldr r3, [sp]")
            assembly = assembly.replace("bl func_08001000\npop", "bl func_08001000\nadd sp, #8\npop")
        original = assemble(self.root, assembly)
        linked, body = ordinary_link(self.root, original)
        image = match.elf_image(original)
        relocations = {}
        for section_index in image["relocations"]:
            section = image["sections"][section_index]
            for position in range(0, section[5], 8):
                site, info = struct.unpack_from("<II", image["section_data"][section_index], position)
                if info & 255 == 2:
                    relocations[site] = struct.unpack_from("<I", image["text"], site)[0]
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        calls = {instruction.address: instruction.operands[0].imm
                 for instruction in decoder.disasm(body, 0x08000000) if instruction.id == match.ARM_INS_BL}
        return assembly, body, calls, relocations

    def verify(self, fixture, **options):
        _, body, calls, relocations = fixture
        parameters = dict(switch_relocations=relocations, allow_switch_constants=True,
                          allow_switch_scalar_frame=True)
        parameters.update(options)
        return match.verify_leaf_instructions(body, 0x08000000, True, calls, **parameters)

    def test_policy_boolean_isolation_and_nonzero_allocation(self):
        fixture = self.structural()
        self.verify(fixture)
        for value in (None, 0, 1, "true", {}, []):
            with self.subTest(value=value), self.assertRaisesRegex(ValueError, "Boolean"):
                self.verify(fixture, allow_switch_scalar_frame=value)
        for options in ({"allow_switch_constants": False}, {"switch_relocations": None},
                        {"allow_switch_scalar_frame": False}):
            with self.subTest(options=options), self.assertRaises(ValueError):
                self.verify(fixture, **options)
        for name in ("buffer_proof", "call_resolver", "switch_data_relocations", "udivsi3_context",
                     "preloaded_switch", "modsi3_context", "divsi3_context", "double_context",
                     "function_thunk_context", "inert_spin_context"):
            with self.subTest(context=name), self.assertRaisesRegex(ValueError, "isolated"):
                self.verify(fixture, **{name: True if name == "preloaded_switch" else {}})
        for assembly in (fixture_assembly(), fixture_assembly(prefix="sub sp, #0")):
            with self.assertRaisesRegex(ValueError, "nonzero fixed allocation"):
                self.verify(self.structural(assembly))
        with self.assertRaises(ValueError):
            profile.checked_policy(replace(self.policy))
        with self.assertRaises(ValueError):
            profile.policy_for("two-constants-frame-v0")

    def test_fixed_frame_scalar_access_and_return_controls(self):
        initial, _, _, _ = self.structural()
        variants = {
            "dynamic": initial.replace("sub sp, #8", "mov sp, r0"),
            "wide": initial.replace(".arch armv4t", ".arch armv7-m").replace("sub sp, #8", "sub.w sp, sp, #8"),
            "conditional": initial.replace(".arch armv4t", ".arch armv7-m").replace("sub sp, #8", "it eq\nsubeq sp, #8"),
            "overfree": initial.replace("add sp, #8", "add sp, #16"),
            "outside": initial.replace("str r3, [sp]", "str r3, [sp, #12]"),
            "missing-pop": initial.replace("pop {r1}", "movs r1, #0"),
            "forged": initial.replace("bx r1", "bx r0"),
            "saved-slot": initial.replace("str r3, [sp]", "str r3, [sp, #8]"),
        }
        for name, assembly in variants.items():
            with self.subTest(name=name), self.assertRaises(ValueError) as error:
                self.verify(self.structural(assembly))
            record("structural_rejections", {"case": name, "reason": str(error.exception)})

    def test_alias_materialization_and_block_transfers_reject_even_dead(self):
        initial, _, _, _ = self.structural()
        for operation in ("mov r2, sp", "add r2, sp, #4", "movs r2, #4\nadd r2, sp",
                          "mov r2, sp\nstr r2, [sp]\nmovs r2, #0",
                          "mov r2, sp\nadd sp, #4\nsub sp, #4",
                          "mov r2, sp\nbl func_08001000", "ldmia r2!, {r3}", "stmia r2!, {r3}"):
            assembly = initial.replace("str r3, [sp]", operation + "\nmovs r2, #0\nstr r3, [sp]")
            with self.subTest(operation=operation), self.assertRaisesRegex(ValueError, "materialization|block transfers"):
                self.verify(self.structural(assembly))

    def test_graph_joins_backedges_and_call_return_provenance(self):
        initial, _, _, _ = self.structural()
        stable = initial.replace(".Ldone:\n", ".Ldone:\n.Lloop:\nsubs r3, #1\nbne .Lloop\n")
        self.verify(self.structural(stable))
        for case in (".Lcase0:\n", ".Lcase1:\n"):
            self.verify(self.structural(initial.replace(case, case + "mov r4, lr\n")))
            for operation in ("sub sp, #4", "str r3, [sp, #8]"):
                with self.subTest(case=case, operation=operation), self.assertRaises(ValueError) as error:
                    self.verify(self.structural(initial.replace(case, case + operation + "\n")))
                self.assertRegex(str(error.exception), "depth|balance|control flow")
                record("graph_rejections", {"case": case.strip(), "operation": operation, "reason": str(error.exception)})
        growing = initial.replace(".Ldone:\n", ".Ldone:\n.Lloop:\nsub sp, #4\ncmp r3, #0\nbne .Lloop\nadd sp, #4\n")
        with self.assertRaisesRegex(ValueError, "depth"):
            self.verify(self.structural(growing))
        local_return = initial.replace("str r3, [sp]", "mov r3, lr\nstr r3, [sp]")
        local_return = local_return.replace("bl func_08001000\nadd sp, #8\npop {r1}",
                                            "ldr r1, [sp]\nadd sp, #8\npop {r2}")
        self.verify(self.structural(local_return))
        with self.assertRaisesRegex(ValueError, "control flow"):
            self.verify(self.structural(local_return.replace("ldr r1, [sp]", "bl func_08001000\nldr r1, [sp]")))
        register_return = fixture_assembly(prefix="sub sp, #8\nmov r4, lr")
        register_return = register_return.replace("bx lr", "add sp, #8\nbx r4")
        self.verify(self.structural(register_return))
        for case in (".Lcase0:\n", ".Lcase1:\n"):
            harmless = register_return.replace(case, case + "movs r3, #0\n")
            self.verify(self.structural(harmless))
            with self.assertRaisesRegex(ValueError, "control flow"):
                self.verify(self.structural(register_return.replace(case, case + "movs r4, #0\n")))

    def test_guard_table_instruction_boundary_and_relocation_reachability(self):
        fixture = self.structural()
        initial, body, calls, relocations = fixture
        for old, new in (("cmp r0, #1", "cmp r0, #2"), ("bhi .Ldefault", "bgt .Ldefault"),
                         ("lsls r0, r0, #2", "lsls r0, r0, #1"),
                         ("lsls r0, r0, #2", "lsls r0, r2, #2"),
                         (".Ldefault:\nmovs r0, #0", ".Ldefault:\nmov pc, r0")):
            with self.subTest(change=new), self.assertRaises(ValueError):
                self.verify(self.structural(initial.replace(old, new)))
        descriptor = profile.layout(body, 0x08000000, relocations)
        with self.assertRaisesRegex(ValueError, "predecessor"):
            self.verify(self.structural(initial.replace(".Lcase0:\n", ".Lcase0:\nb .Ldispatch\n")))
        for target in (descriptor["literal"] - 8, descriptor["table"], next(iter(calls)) - 0x08000000 + 2):
            changed, wrong = bytearray(body), dict(relocations)
            site = descriptor["table"]
            wrong[site] = target
            struct.pack_into("<I", changed, site, 0x08000000 + target)
            with self.subTest(case_target=target), self.assertRaises(ValueError):
                self.verify((initial, bytes(changed), calls, wrong))
        for target in (descriptor["dispatch"], descriptor["dispatch"] + 10, descriptor["literal"] - 8, descriptor["table"],
                       next(iter(calls)) - 0x08000000 + 2):
            changed = bytearray(body)
            struct.pack_into("<H", changed, 0, 0xE000 | ((target - 4) // 2 & 0x7FF))
            with self.subTest(target=target), self.assertRaises(ValueError):
                self.verify((initial, bytes(changed), calls, relocations))
        unreachable = initial.replace(".size func_08000000", "bl func_08001000\n.size func_08000000")
        with self.assertRaisesRegex(ValueError, "not all reachable"):
            self.verify(self.structural(unreachable))

    def test_excluded_function_object_and_runtime_compositions(self):
        for expression in ("func_08001000", "g_external"):
            assembly = fixture_assembly(prefix="sub sp, #8").replace("bx lr", "add sp, #8\nbx lr")
            assembly = assembly.replace(".word 0xFF00FF00", ".word " + expression)
            original = assemble(self.root, assembly)
            image = match.elf_image(original)
            with self.subTest(expression=expression), self.assertRaisesRegex(ValueError, "unique unnamed"):
                profile._original_records(image, 0x08000000, b"[]", 8192)
        initial, _, _, _ = self.structural()
        with self.assertRaisesRegex(ValueError, "runtime call thunks"):
            self.verify(self.structural(initial.replace("func_08001000", "func_08142244")))

    def test_strict_frame_schema_fresh_replay_and_no_legacy_fallback(self):
        root, rom, _ = self.prepare()
        with self.trusted_fixture(root, rom):
            result = profile._build_from_source(root, 0x08000000, self.policy)
            report = profile.render_report(0x08000000, result, self.policy)
            self.assertTrue(match_evidence.report_matches(report, root, 0x08000000))
            manifest = json.loads(result.manifest_json)
            malformed = []
            for change in ("missing", "extra", "policy", "units", "bool", "offset", "order", "no-allocation", "access", "duplicate"):
                changed = copy.deepcopy(manifest)
                frame = changed["frame"]
                if change == "missing":
                    del changed["frame"]
                elif change == "extra":
                    frame["bounds"] = [0, 8]
                elif change == "policy":
                    frame["policy"] = "arbitrary-aliases"
                elif change == "units":
                    frame["adjustments"][0][1] //= 4
                elif change == "bool":
                    frame["accesses"][0][2] = True
                elif change == "offset":
                    frame["adjustments"][0][0] += 2
                elif change == "order":
                    frame["adjustments"].reverse()
                elif change == "no-allocation":
                    frame["adjustments"][0][1] = 0
                elif change == "access":
                    frame["accesses"][0][2] += 4
                elif change == "duplicate":
                    frame["accesses"].append(frame["accesses"][0])
                rewritten = replace(result, manifest_json=profile.canonical(changed))
                malformed.append((change, profile.render_report(0x08000000, rewritten, self.policy)))
            malformed += [
                ("missing-selector", report.replace(f"* switch constants: {self.policy.selector}\n", "")),
                ("duplicate-marker", report + f"* scalar frame: {profile.FRAME_SUMMARY}\n"),
                ("relabel-old", report.replace(self.policy.schema, profile.SCHEMA).replace(self.policy.selector, profile.SELECTOR)),
                ("unknown-schema", report.replace(self.policy.schema, self.policy.schema + "-future")),
                ("missing-frame-marker", report.replace(f"* scalar frame: {profile.FRAME_SUMMARY}\n", "")),
                ("duplicate-json", report.replace('"frame":{', '"frame":{},"frame":{')),
                ("orphan-frame", "# 0x08000000\n* scalar frame: " + profile.FRAME_SUMMARY + "\n**MATCH - byte identical** - 2/2 bytes\n"),
                ("diagnostic", report.replace("**MATCH - byte identical**", "**NOT MATCHING**")),
            ]
            for name, changed in malformed:
                with self.subTest(name=name), patch.object(match_evidence, "switch_report_matches") as fallback:
                    self.assertFalse(match_evidence.report_matches(changed, root, 0x08000000))
                    fallback.assert_not_called()
                record("schema_rejections", name)
            self.assertNotEqual(profile.fingerprint(0x08000000, result, self.policy),
                                profile.fingerprint(0x08000000, result))
            with self.assertRaisesRegex(ValueError, "fixed frames"):
                profile._build_from_source(root, 0x08000000)

    def test_input_binding_drift_and_failed_issuance_leave_no_outputs(self):
        root, rom, _ = self.prepare()
        (root / "include").mkdir()
        header = root / "include/scalar.h"
        header.write_text("typedef unsigned int scalar_word;\n")
        with self.trusted_fixture(root, rom):
            result = profile._build_from_source(root, 0x08000000, self.policy)
            report = profile.render_report(0x08000000, result, self.policy)
            for relative in ("src/08000000.c", "include/scalar.h", "config/functions.json", "symbols/functions.txt", "fixture.rom"):
                path = root / relative
                original = path.read_bytes()
                path.write_bytes(original + b"\n")
                with self.subTest(relative=relative):
                    self.assertFalse(match_evidence.report_matches(report, root, 0x08000000))
                path.write_bytes(original)
            resolve = profile._resolve_tools
            calls = 0

            def changed_tools():
                nonlocal calls
                calls += 1
                tools = resolve()
                return tools if calls == 1 else (*tools[:-1], (*tools[-1][:-1], "0" * 64))

            with patch.object(profile, "_resolve_tools", side_effect=changed_tools):
                self.assertFalse(match_evidence.report_matches(report, root, 0x08000000))
            snapshot = profile._checker_snapshot
            checks = 0

            def changed_checker():
                nonlocal checks
                checks += 1
                captured = snapshot()
                return captured if checks == 1 else (*captured[:-1], b"changed checker allowance")

            with patch.object(profile, "_checker_snapshot", side_effect=changed_checker):
                self.assertFalse(match_evidence.report_matches(report, root, 0x08000000))
            arguments = ["match.py", "--root", str(root), "--switch-profile", self.policy.selector,
                         "--emit", "build/failed.bin", "08000000"]
            for failure in (ValueError("bad original"), RuntimeError("tool failed"),
                            subprocess.TimeoutExpired("fixed tool", 120)):
                with self.subTest(failure=str(failure)), patch.object(sys, "argv", arguments), \
                        patch.object(profile, "_compile_object", side_effect=failure), \
                        patch.object(match, "compile_object", side_effect=AssertionError("legacy fallback")), \
                        contextlib.redirect_stdout(io.StringIO()) as output, self.assertRaises(SystemExit):
                    match.main()
                self.assertFalse((root / "build/failed.bin").exists())
                self.assertFalse((root / "docs/match/08000000.md").exists())
                self.assertNotIn("MATCH", output.getvalue())
                self.assertFalse(profile._active.get())
                self.assertEqual(list((root / "build").iterdir()), [])
            self.assertTrue(match_evidence.report_matches(report, root, 0x08000000))

    def test_public_unframed_and_legacy_framed_selections_reject(self):
        for framed, selector in ((False, self.policy.selector), (True, profile.SELECTOR)):
            root, rom, _ = self.prepare() if framed else placement_tests.PlacementTests.prepare(self, 0x08000000)
            arguments = ["match.py", "--root", str(root), "--switch-profile", selector,
                         "--emit", "build/rejected.bin", "08000000"]
            with self.trusted_fixture(root, rom), patch.object(sys, "argv", arguments), \
                    contextlib.redirect_stdout(io.StringIO()) as output, self.assertRaises(SystemExit):
                match.main()
            self.assertNotIn("MATCH", output.getvalue())
            self.assertFalse((root / "build/rejected.bin").exists())
            self.assertFalse((root / "docs/match/08000000.md").exists())
            self.assertEqual(list((root / "build").iterdir()), [])
            self.assertFalse(profile._active.get())

    def test_late_consumer_extent_and_selector_failures(self):
        address = 0x08150002
        root, rom, captured = self.prepare(address)
        tools = Path(match.__file__).resolve().parent
        launcher = ("import sys\n" + f"sys.path.insert(0, {str(tools)!r})\n"
                    "import match, switch_constants_profile as profile\n"
                    f"profile.ROM_SIZE = {len(rom)}\nprofile.ROM_SHA1 = {hashlib.sha1(rom).hexdigest()!r}\n"
                    "sys.exit(match.main())\n")
        run = subprocess.run
        changed = None
        records = []

        def invoke(command, **kwargs):
            self.assertEqual(command[:2], [sys.executable, str(tools / "match.py")])
            self.assertIn(self.policy.selector, command)
            completed = run([sys.executable, "-c", launcher, *command[2:]], timeout=120, **kwargs)
            self.assertEqual(completed.returncode, 0, completed.stdout + completed.stderr)
            if changed:
                completed.stdout = changed(completed.stdout)
            records.append({"command": command, "stdout": completed.stdout, "exit": completed.returncode})
            return completed

        arguments = ["match.py", "--root", str(root), "--switch-profile", self.policy.selector, f"{address:08X}"]
        report_path = root / f"docs/match/{address:08X}.md"
        with self.trusted_fixture(root, rom):
            with patch.object(sys, "argv", arguments), contextlib.redirect_stdout(io.StringIO()) as output:
                self.assertEqual(match.main(), 0)
            report = report_path.read_text()
            size = len(bytes.fromhex(captured["body"]))
            extent = f"extent    {size} bytes (complete ELF symbol; {profile.CONTROL_FLOW}; no relocations)"
            self.assertIn(extent, output.getvalue())
            for label, mutation in (
                    ("wrong", lambda text: text.replace(extent, extent.replace(str(size), str(size + 2), 1))),
                    ("missing", lambda text: text.replace(extent + "\n", "")),
                    ("duplicate", lambda text: text + extent + "\n")):
                changed = mutation
                with self.subTest(label=label), patch.object(status.subprocess, "run", side_effect=invoke):
                    result = status.collect(str(root), True, quiet=True)
                    self.assertEqual(result[5:], (0, 0))
                    self.assertTrue(result[4])
                    with contextlib.redirect_stdout(io.StringIO()), self.assertRaises(ValueError):
                        rebuild.compiled_rebuild(root, str(root / "build/rejected.bin"))
                self.assertFalse((root / "build/rejected.bin").exists())
            for bad in (report.replace(self.policy.selector, profile.SELECTOR),
                        report.replace(f"* switch constants: {self.policy.selector}\n", "")):
                report_path.write_text(bad)
                with patch.object(status.subprocess, "run", side_effect=AssertionError("malformed selector ran")):
                    self.assertTrue(status.collect(str(root), True, quiet=True)[4])
                    with self.assertRaises(ValueError):
                        rebuild.saved_profile_arguments(bad, root, address)
            report_path.write_text(report)
            self.assertEqual(list((root / "build").iterdir()), [])
        record("late_controls", {"address": address, "invocations": records, "report": report})

    def test_public_fifo_and_symlink_boundaries_at_both_origins(self):
        for address in (0x08000000, 0x08000002):
            root, rom, _ = self.prepare(address)
            arguments = ["match.py", "--root", str(root), "--switch-profile", self.policy.selector,
                         "--emit", "build/rejected.bin", f"{address:08X}"]
            with self.trusted_fixture(root, rom):
                report = profile.render_report(address, profile._build_from_source(root, address, self.policy), self.policy)
                for name in ("f.elf", "f.linked.bin"):
                    for boundary in (1, 2):
                        for kind in ("fifo", "symlink"):
                            snapshot = profile._artifact_snapshot
                            calls, replaced = 0, []

                            def substitute(path):
                                nonlocal calls
                                path = Path(path)
                                if path.name == name:
                                    calls += 1
                                    if calls == boundary:
                                        if kind == "symlink":
                                            target = path.with_suffix(path.suffix + ".target")
                                            path.rename(target)
                                            path.symlink_to(target)
                                        else:
                                            path.unlink()
                                            os.mkfifo(path)
                                        replaced.append(path)
                                return placement_tests.bounded_snapshot(snapshot, path)

                            with self.subTest(address=address, name=name, boundary=boundary, kind=kind), \
                                    patch.object(profile, "_artifact_snapshot", side_effect=substitute), \
                                    patch.object(match, "compile_object", side_effect=AssertionError("legacy compile")), \
                                    patch.object(match_evidence, "switch_report_matches", side_effect=AssertionError("legacy replay")), \
                                    patch.object(sys, "argv", arguments), contextlib.redirect_stdout(io.StringIO()) as output:
                                with self.assertRaises(SystemExit) as error:
                                    match.main()
                                calls = 0
                                self.assertFalse(match_evidence.report_matches(report, root, address))
                            self.assertEqual(len(replaced), 2)
                            self.assertTrue(all(not path.exists() and not path.is_symlink() for path in replaced))
                            self.assertFalse((root / f"docs/match/{address:08X}.md").exists())
                            self.assertFalse((root / "build/rejected.bin").exists())
                            self.assertEqual(list((root / "build").iterdir()), [])
                            self.assertFalse(profile._active.get())
                            self.assertNotIn("MATCH", output.getvalue())
                            record("nonregular", {"address": address, "artifact": name, "boundary": boundary,
                                "kind": kind, "issuance_rejection": str(error.exception), "replay_accepted": False,
                                "watchdog_fired": False, "report_or_output": False, "cleaned": True})

    def test_natural_full_issue_replay_both_origins_and_guard_classes(self):
        guards, dispatches = set(), set()
        for repetitions in (1, 8):
            for address in (0x08000000, 0x08000002):
                with self.subTest(repetitions=repetitions, address=address):
                    root, rom, captured = self.prepare(address, repetitions)
                    arguments = ["match.py", "--root", str(root), "--switch-profile",
                                 profile.FRAME_POLICY.selector, f"{address:08X}"]
                    with self.trusted_fixture(root, rom), patch.object(sys, "argv", arguments), \
                            contextlib.redirect_stdout(io.StringIO()) as output, \
                            patch.object(profile, "_compile_object", wraps=profile._compile_object) as compiled:
                        self.assertEqual(match.main(), 0)
                        report = (root / f"docs/match/{address:08X}.md").read_text()
                        self.assertTrue(match_evidence.report_matches(report, root, address))
                        self.assertEqual(compiled.call_count, 2)
                    manifest = json.loads(next(line.split("`", 2)[1] for line in report.splitlines()
                                               if line.startswith("* switch constants manifest:")))
                    frame = manifest["frame"]
                    self.assertEqual(frame["policy"], profile.FRAME_RULE)
                    self.assertTrue(any(delta < 0 for _, delta in frame["adjustments"]))
                    self.assertEqual({kind for _, kind, _ in frame["accesses"]}, {"ldr", "str"})
                    instructions = match.verify_leaf_instructions(bytes.fromhex(captured["body"]), address, True,
                        {address + site: int(name[5:], 16) for site, name in manifest["calls"]},
                        switch_relocations=dict(manifest["switch"]["relocations"]),
                        allow_switch_constants=True, allow_switch_scalar_frame=True)
                    depth = 0
                    incoming = []
                    for instruction in instructions:
                        if instruction.mnemonic == "push":
                            depth += 4 * len(instruction.operands)
                        adjustment = match.thumb_stack_adjustment(instruction)
                        if adjustment is not None:
                            depth -= 4 * adjustment
                        for operand in instruction.operands:
                            if instruction.mnemonic == "ldr" and operand.type == match.ARM_OP_MEM and \
                                    operand.mem.base == match.ARM_REG_SP and operand.mem.disp >= depth:
                                incoming.append([instruction.address - address, operand.mem.disp - depth])
                        if instruction.address - address == manifest["switch"]["comparison"]:
                            break
                    self.assertEqual({offset for _, offset in incoming}, {0, 4})
                    guards.add(manifest["switch"]["dispatch"] - manifest["switch"]["comparison"])
                    dispatches.add((address + manifest["switch"]["dispatch"]) % 4)
                    captured.update(report=report, incoming_arguments=incoming, stdout=output.getvalue(),
                                    fresh_compiles=compiled.call_count, repetitions=repetitions)
                    record("natural", captured)
        self.assertEqual(guards, {4, 6})
        self.assertEqual(dispatches, {0, 2})


if __name__ == "__main__":
    unittest.main()
