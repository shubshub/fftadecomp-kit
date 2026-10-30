import argparse
import json
import os
from pathlib import Path
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

BASE = match.ROM_BASE
CALLER = ("push {r4, lr}\nsub sp, #8\nmov r1, sp\nmovs r0, #0\n"
          "bl callee\nadd sp, #8\npop {r4}\npop {r0}\nbx r0")


class BufferIndexTests(unittest.TestCase):
    def setUp(self):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="buffer_index_", dir=scratch)
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        environment = patch.dict(os.environ, {
            "TMPDIR": str(self.root), "FFTA_ROM": str(self.root / "baserom.bin"),
            "PYTHONDONTWRITEBYTECODE": "1"})
        environment.start()
        self.addCleanup(environment.stop)

    def fixture(self, operation, caller=CALLER, child="bx lr", callee=None,
                stack_arguments=True, proof_type=match.BufferCallProof, arch="armv5t"):
        if callee is None:
            callee = ("push {r4, r5, lr}\nadds r4, r1, #0\nmovs r1, #0\n" +
                      operation + "\npop {r4, r5}\npop {r1}\nbx r1")
        assembly = self.root / "fixture.s"
        assembly.write_text(
            f".syntax unified\n.arch {arch}\n.thumb\n.text\n"
            ".global caller, caller_end, callee, callee_end, child, child_end\n"
            f"caller:\n{caller}\ncaller_end:\n.org 0x100\n"
            f"callee:\n{callee}\ncallee_end:\n.org 0x200\n"
            f"child:\n{child}\nchild_end:\n")
        for command in (
            ["arm-none-eabi-as", "-mthumb-interwork", str(assembly),
             "-o", str(self.root / "fixture.o")],
            ["arm-none-eabi-ld", "-Ttext=0x08000000", "-e", "caller",
             str(self.root / "fixture.o"), "-o", str(self.root / "fixture.elf")],
            ["arm-none-eabi-objcopy", "-O", "binary", "--only-section=.text",
             str(self.root / "fixture.elf"), str(self.root / "baserom.bin")],
        ):
            subprocess.run(command, check=True, capture_output=True)
        image = match.elf_image((self.root / "fixture.elf").read_bytes())
        symbols = {symbol["name"]: symbol["value"] for symbol in image["symbols"]}
        self.entries = [{"rom": f"0x{symbols[name]:08X}",
                         "end": f"0x{symbols[name + '_end']:08X}", "mode": "thumb"}
                        for name in ("caller", "callee", "child")]
        self.rom = (self.root / "baserom.bin").read_bytes()
        self.body = self.rom[:symbols["caller_end"] - BASE]
        proof = proof_type(self.rom, json.dumps(self.entries).encode(),
                           stack_arguments=stack_arguments)
        match.verify_leaf_instructions(self.body, BASE, True, buffer_proof=proof,
                                       call_resolver=proof.target)
        return proof

    def test_constant_index_widths_and_v1_rejection(self):
        for operation, offsets in (("ldrb", (1, 7)), ("ldrsb", (1, 7)),
                                   ("strb", (1, 7)), ("ldrh", (0, 2, 6)),
                                   ("ldrsh", (0, 2, 6)), ("strh", (0, 2, 6)),
                                   ("ldr", (0, 4)), ("str", (0, 4))):
            for offset in offsets:
                sequence = f"movs r2, #{offset}\n{operation} r0, [r4, r2]"
                with self.subTest(operation=operation, offset=offset):
                    proof = self.fixture(sequence)
                    self.assertEqual(set(proof.dependencies), {BASE + 0x100})
                    with self.assertRaisesRegex(ValueError, "unsupported buffer memory access"):
                        self.fixture(sequence, stack_arguments=False)

    def test_register_copy_and_actual_signed_load_shape(self):
        self.fixture("movs r2, #2\nmovs r3, r2\nldrsh r0, [r4, r3]")
        self.fixture("movs r5, r4\nmovs r4, #0\nldrsh r0, [r5, r4]")
        caller = ("push {r4, lr}\nsub sp, #12\nadd r1, sp, #8\nstr r1, [sp]\n"
                  "movs r1, #0\nbl callee\nadd sp, #12\npop {r4}\npop {r0}\nbx r0")
        self.fixture("ldr r4, [sp, #12]\nmovs r2, #0\nldrsh r0, [r4, r2]", caller=caller)

    def test_unknown_written_popped_and_arithmetic_indices_rejected(self):
        setups = ("", "movs r2, #2\nmovs r2, r3",
                  "movs r2, #2\nldr r2, [r3]", "movs r2, #2\nadds r2, #0",
                  "movs r2, #2\nsubs r2, #1", "movs r2, #1\nlsls r2, r2, #1",
                  "movs r2, #2\npush {r3}\npop {r2}",
                  "movs r2, #2\nldrsh r2, [r4, r2]")
        for setup in setups:
            with self.subTest(setup=setup), self.assertRaisesRegex(
                    ValueError, "buffer index is not a known scalar constant"):
                self.fixture(setup + "\nldrsh r0, [r4, r2]")

    def test_call_clobber_and_callee_saved_index(self):
        with self.assertRaisesRegex(ValueError, "buffer index is not a known scalar constant"):
            self.fixture("movs r2, #2\nbl child\nldrsh r0, [r4, r2]")
        self.fixture("movs r5, #2\nbl child\nldrsh r0, [r4, r5]")

    def test_nested_callee_must_establish_its_own_index(self):
        operation = "movs r1, r4\nmovs r2, #2\nbl child\nmovs r1, #0"
        with self.assertRaisesRegex(ValueError, "buffer index is not a known scalar constant"):
            self.fixture(operation, child="ldrsh r0, [r1, r2]\nbx lr")
        self.fixture(operation, child="movs r2, #2\nldrsh r0, [r1, r2]\nbx lr")

    def test_equal_join_and_stable_loop(self):
        self.fixture("cmp r0, #0\nbeq other\nmovs r2, #2\nb joined\n"
                     "other:\nmovs r2, #2\njoined:\nldrsh r0, [r4, r2]")
        self.fixture("movs r2, #2\nloop:\nldrsh r0, [r4, r2]\n"
                     "subs r3, #1\nbne loop")

    def test_different_or_missing_join_constant_rejected(self):
        for first, second in (("movs r2, #0", "movs r2, #2"),
                              ("", "movs r2, #2"), ("movs r2, #2", "")):
            with self.subTest(first=first, second=second), self.assertRaisesRegex(
                    ValueError, "buffer index is not a known scalar constant"):
                self.fixture(f"cmp r0, #0\nbeq other\n{first}\nb joined\n"
                             f"other:\n{second}\njoined:\nldrsh r0, [r4, r2]")

    def test_mixed_scalar_alias_join_rejected_in_both_orders(self):
        for first, second in (("movs r2, #2", "movs r2, r4"),
                              ("movs r2, r4", "movs r2, #2")):
            with self.subTest(first=first), self.assertRaisesRegex(
                    ValueError, "buffer index is not a known scalar constant"):
                self.fixture(f"cmp r0, #0\nbeq other\n{first}\nb joined\n"
                             f"other:\n{second}\njoined:\nldrsh r0, [r4, r2]")

    def test_changed_backedge_invalidates_previously_valid_access(self):
        for update in ("movs r2, #4", "movs r2, r3", "adds r2, #0"):
            with self.subTest(update=update), self.assertRaisesRegex(
                    ValueError, "buffer index is not a known scalar constant"):
                self.fixture("movs r2, #2\nloop:\nldrsh r0, [r4, r2]\n" +
                             update + "\ncmp r3, #0\nbne loop")
        self.fixture("loop:\nmovs r2, #2\nldrsh r0, [r4, r2]\n"
                     "adds r2, #0\ncmp r3, #0\nbne loop")

    def test_bounds_alignment_and_saved_slots(self):
        for operation, offset in (("ldrsh", 1), ("strh", 1), ("ldr", 2),
                                   ("str", 2), ("strb", 8), ("ldrb", 16),
                                   ("ldrsh", 8), ("str", 8)):
            with self.subTest(operation=operation, offset=offset), self.assertRaisesRegex(
                    ValueError, "unaligned or outside allocated local words"):
                self.fixture(f"movs r2, #{offset}\n{operation} r0, [r4, r2]")
        with self.assertRaisesRegex(ValueError, "unaligned or outside allocated local words"):
            self.fixture("subs r4, #1\nmovs r2, #0\nldrb r0, [r4, r2]")

    def test_pointer_slot_overlaps_rejected_for_all_widths(self):
        caller = ("push {r4, lr}\nsub sp, #12\nmov r1, sp\nstr r1, [sp, #4]\n"
                  "movs r0, #0\nbl callee\nadd sp, #12\npop {r4}\npop {r0}\nbx r0")
        for operation, offset in (("strb", 4), ("strb", 7), ("strh", 4),
                                   ("strh", 6), ("str", 4), ("ldrb", 7),
                                   ("ldrsh", 6), ("ldr", 4)):
            with self.subTest(operation=operation, offset=offset), self.assertRaisesRegex(
                    ValueError, "overlaps a pointer-bearing argument slot"):
                self.fixture(f"movs r2, #{offset}\n{operation} r0, [r4, r2]", caller=caller)

    def test_pointer_values_and_indices_do_not_gain_escape_permission(self):
        for operation in ("movs r2, #0\nstr r4, [r4, r2]",
                          "strb r0, [r2, r4]", "movs r2, r4\nstrb r0, [r4, r2]",
                          "str r4, [sp]", "push {r4}\npop {r4}", "mov lr, r4"):
            with self.subTest(operation=operation), self.assertRaises(ValueError):
                self.fixture(operation)

    def test_conflicting_alias_offsets_and_conditional_escape_still_rejected(self):
        with self.assertRaisesRegex(ValueError, "inconsistent possible pointer offsets"):
            self.fixture("cmp r0, #0\nbeq other\nmovs r3, r4\nb joined\n"
                         "other:\nadds r3, r4, #2\njoined:\nmovs r2, #0\n"
                         "ldrsh r0, [r3, r2]\nmovs r3, #0")
        caller = CALLER.replace("bl callee", "bl callee\nstr r2, [r3]")
        with self.assertRaisesRegex(ValueError, "alias use or escape"):
            self.fixture("cmp r0, #0\nbeq joined\nmovs r2, r4\njoined:", caller=caller)

    def test_wider_shifted_and_writeback_operations_rejected(self):
        for operation in ("movs r2, #0\nldr.w r0, [r4, r2, lsl #2]",
                          "ldr r0, [r4, #4]!"):
            with self.subTest(operation=operation), self.assertRaises(ValueError):
                self.fixture(operation, arch="armv7-m")

    def test_function_buffer_inheritance_preserves_runtime_exclusion(self):
        proof = self.fixture("movs r2, #2\nldrsh r0, [r4, r2]",
                             proof_type=match.FunctionBufferCallProof)
        with self.assertRaisesRegex(ValueError, "excludes runtime call thunks"):
            proof.target(match.RUNTIME_HELPERS["_call_via_r2"])

    def test_report_replays_and_binds_current_inputs(self):
        self.fixture("movs r2, #1\nstrb r0, [r4, r2]")
        for directory in ("config", "src", "include", "build", "symbols"):
            (self.root / directory).mkdir()
        source = self.root / "src/08000000.c"
        source.write_text("extern void func_08000100(unsigned value, unsigned char *buffer);\n"
                          "void func_08000000(void)\n{\n    unsigned char buffer[8];\n"
                          "    func_08000100(0, buffer);\n}\n")
        header = self.root / "include/test.h"
        header.write_text("typedef unsigned char TestByte;\n")
        mapping_path = self.root / "config/functions.json"
        args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP,
            assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY,
            linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        runner = match.Runner(match.DEFAULT_CC, root=self.root,
                              wsl_path=match.DEFAULT_WSL_PATH, timeout=120)
        with runner.workspace() as workspace:
            _, _, original = match.compile_object(
                runner, workspace, args, self.root, BASE, "src/08000000.c")
            symbol, _ = match.function_record(original, "func_08000000", BASE, True)
            self.entries[0]["end"] = f"0x{BASE + symbol['size']:08X}"
            self.body, _, _ = match.link_calls(
                runner, workspace, args, original, BASE,
                json.dumps(self.entries).encode(), len(self.rom), self.rom)
        self.assertLess(len(self.body), 0x100)
        self.rom = self.body.ljust(0x100, b"\0") + self.rom[0x100:]
        (self.root / "baserom.bin").write_bytes(self.rom)
        mapping_path.write_text(json.dumps(self.entries))
        (self.root / "symbols/functions.txt").write_text("".join(
            f"{int(entry['rom'], 16):08X} {int(entry['end'], 16):08X} "
            f"{int(entry['end'], 16) - int(entry['rom'], 16)} "
            f"{(int(entry['end'], 16) - int(entry['rom'], 16)) // 2} return\n"
            for entry in self.entries))
        proof = match.BufferCallProof(self.rom, json.dumps(self.entries).encode(),
                                      stack_arguments=True)
        match.verify_leaf_instructions(self.body, BASE, True, buffer_proof=proof,
                                       call_resolver=proof.target)
        report = "\n".join((
            f"* verification: `{evidence.STACK_BUFFER_SCHEMA}`",
            f"* source SHA-256: `{evidence.source_fingerprint(self.root, BASE)}`",
            f"* mapping SHA-256: `{evidence.mapping_fingerprint(evidence.mapping_snapshot(self.root))}`",
            f"* stack frame: {evidence.STACK_SUMMARY}",
            f"* control flow: {evidence.CALL_SUMMARY}",
            f"* buffer calls: {evidence.STACK_BUFFER_SUMMARY}",
            f"* buffer proof SHA-256: `{proof.fingerprint()}`",
            "* verified extent: complete ELF function symbol, including literal pools",
            f"* ROM bytes: `{self.body.hex()}` ({len(self.body)} bytes)",
            f"* compiled : `{self.body.hex()}`", "* source plausibility: plausible",
            "* relocations: none",
            f"**MATCH - byte identical** - {len(self.body)}/{len(self.body)} bytes",
        ))
        self.assertTrue(evidence.report_matches(report, self.root, BASE))
        old_report = report.replace(evidence.STACK_BUFFER_SCHEMA, evidence.BUFFER_SCHEMA).replace(
            evidence.STACK_BUFFER_SUMMARY, evidence.BUFFER_SUMMARY)
        self.assertFalse(evidence.report_matches(old_report, self.root, BASE))
        for path in (source, header, mapping_path):
            original = path.read_bytes()
            try:
                path.write_bytes(original + b"\n")
                self.assertFalse(evidence.report_matches(report, self.root, BASE), str(path))
            finally:
                path.write_bytes(original)
        changed = bytearray(self.rom)
        self.assertEqual(changed[0x106:0x108], bytes.fromhex("0122"))
        changed[0x106] = 8
        (self.root / "baserom.bin").write_bytes(changed)
        self.assertFalse(evidence.report_matches(report, self.root, BASE))


if __name__ == "__main__":
    unittest.main(verbosity=2)
