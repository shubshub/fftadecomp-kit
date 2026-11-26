"""The function-literal data-buffer proof takes the plain proof's default-walk summaries.

A caller with typed objects and a function literal is proved by data_buffer_profile's
FUNCTION_SCHEMA branch, whose FunctionBufferCallProof had no BIOS wrapper, copy-helper or
jump-table-callee summaries, so a local handed to func_081443FC or to the CpuSet wrapper refused
there although the same call is summarised on the plain path.  The fixtures are compiled C callers
linked at 0x08000200 beside the pinned helper and the indexed CpuSet wrapper.
"""
import argparse
import json
import os
from pathlib import Path
import struct
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
sys.path.insert(0, str(ROOT / "tests"))
import match
import match_evidence as evidence
import data_buffer_profile as data_buffer
# Modules, not their test classes: importing a TestCase class would run it here again.
import test_data_buffer_calls as data_calls
import test_copy_helper_summary as copy_tests

BASE = match.ROM_BASE
A = data_calls.A
HELPER = copy_tests.HELPER
CPUSET = 0x0814186C
ROM_SIZE = 0x150000
CALLEES = (("func_08000400", "bx lr"), ("func_08000500", "bx lr"))
HEADER = ("typedef unsigned short u16;\ntypedef unsigned int u32;\nextern u16 data_02000000[];\n"
          "extern void func_08000500(void);\nextern void func_08000400(void (*callback)(void));\n")
# A local filled by the pinned copy helper, and a function literal handed to func_08000400.
COPY = HEADER + """extern void func_081443FC(void *destination, const void *source, u32 size);
void func_08000200(void)
{
    u16 buffer[4];

    func_081443FC(buffer, data_02000000, 8);
    func_08000400(func_08000500);
    data_02000000[4] = buffer[0];
    data_02000000[5] = buffer[3];
}
"""
# The same local filled by CpuSet through its indexed wrapper (a 16-bit copy of four units); the
# next call's second argument overwrites the R1 the wrapper may leave the local in.
CPUSET_COPY = ("typedef unsigned short u16;\ntypedef unsigned int u32;\nextern u16 data_02000000[];\n"
               "extern void func_08000500(void);\n"
               "extern void func_08000400(void (*callback)(void), u32 zero);\n") + """extern void func_0814186C(const void *source, void *destination, u32 control);
void func_08000200(void)
{
    u16 buffer[4];

    func_0814186C(data_02000000, buffer, 4);
    func_08000400(func_08000500, 0);
    data_02000000[4] = buffer[0];
    data_02000000[5] = buffer[3];
}
"""
# The plain-path twin of COPY: no function literal, so the plain data-buffer proof.
PLAIN_COPY = COPY.replace("    func_08000400(func_08000500);\n", "")


def build(root, source, *, count=None):
    """A complete tree: the caller at A, two callees at 0x08000400/0x08000500, the pinned helper and
    the CpuSet wrapper at their ROM addresses, every one indexed in both indexes."""
    root = Path(root)
    for name in ("src", "include", "config", "symbols", "build"):
        (root / name).mkdir(parents=True, exist_ok=True)
    work = root / "build"
    names = [name for name, _ in CALLEES]
    (work / "callees.s").write_text(
        ".syntax unified\n.arch armv4t\n.thumb\n.text\n" +
        "".join(f".global {name}, {name}_end\n" for name in names) +
        "".join(f".org 0x{0x100 * index:x}\n{name}:\n{body}\n{name}_end:\n"
                for index, (name, body) in enumerate(CALLEES)))
    import subprocess
    for command in (
            [match.DEFAULT_AS, "-mthumb-interwork", str(work / "callees.s"), "-o", str(work / "callees.o")],
            [match.DEFAULT_LD, "-Ttext=0x08000400", "-e", names[0], str(work / "callees.o"),
             "-o", str(work / "callees.elf")],
            [match.DEFAULT_OBJCOPY, "-O", "binary", "--only-section=.text", str(work / "callees.elf"),
             str(work / "callees.bin")]):
        subprocess.run(command, check=True, capture_output=True)
    image = match.elf_image((work / "callees.elf").read_bytes())
    symbols = {symbol["name"]: symbol["value"] for symbol in image["symbols"]}
    rom = bytearray(ROM_SIZE)
    code = (work / "callees.bin").read_bytes()
    rom[0x400:0x400 + len(code)] = code
    rom[HELPER - BASE:HELPER - BASE + len(copy_tests.BODY)] = copy_tests.BODY
    struct.pack_into("<HH", rom, CPUSET - BASE, 0xDF0B, 0x4770)
    entries = [{"rom": f"0x{symbols[name]:08X}", "end": f"0x{symbols[name + '_end']:08X}", "mode": "thumb"}
               for name in names]
    entries += [{"rom": f"0x{CPUSET:08X}", "end": f"0x{CPUSET + 4:08X}", "mode": "thumb"},
                {"rom": f"0x{HELPER:08X}", "end": f"0x{HELPER + len(copy_tests.BODY):08X}", "mode": "thumb",
                 "instrs": 49}]
    if count is not None:
        source = source.replace(", 8);", f", {count});")
    (root / "src/08000200.c").write_text(source)
    (root / "include/types.h").write_text("/* fixture */\n")
    objects = json.dumps(data_calls.OBJECTS).encode()
    (root / "config/data_symbols.json").write_bytes(objects)
    args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                              objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
    runner = match.Runner(match.DEFAULT_CC, root=root, wsl_path=match.DEFAULT_WSL_PATH, timeout=120)
    with runner.workspace() as workspace:
        _, _, original = match.compile_object(runner, workspace, args, root, A, "src/08000200.c")
        symbol, _ = match.function_record(original, "func_08000200", A, True)
        entries.insert(0, {"rom": f"0x{A:08X}", "end": f"0x{A + symbol['size']:08X}", "mode": "thumb"})
        mapping = json.dumps(entries).encode()
        body, _, _ = match.link_calls(runner, workspace, args, original, A, mapping, len(rom), bytes(rom),
                                      objects, {})
    rom[A - BASE:A - BASE + len(body)] = body
    (root / "config/functions.json").write_bytes(mapping)
    (root / "symbols/functions.txt").write_text("".join(
        f"{int(entry['rom'], 16):08X} {int(entry['end'], 16):08X} "
        f"{int(entry['end'], 16) - int(entry['rom'], 16)} {entry.get('instrs', 0)} return\n"
        for entry in entries))
    (root / "baserom.bin").write_bytes(bytes(rom))
    return root


def lines(report, prefix):
    return [line for line in report.splitlines() if line.startswith(prefix)]


class ConstructorTests(unittest.TestCase):
    """The three summary guards admit the plain proof and the function-literal proof only."""

    def setUp(self):
        env = copy_tests.environment(copy_tests.owner())
        self.rom, self.mapping, self.index = env["rom"], env["mapping"], env["index"]

    def test_the_function_literal_proof_takes_every_summary(self):
        proof = match.FunctionBufferCallProof(self.rom, self.mapping, stack_arguments=True, loop_replay=True,
                                              bios_wrappers=True, copy_helper_index=self.index,
                                              switch_callee_index=self.index, dead_registers=True)
        self.assertIsNotNone(proof.bios_summaries)
        self.assertIsNotNone(proof.copy_summaries)
        self.assertIsNotNone(proof.switch_callees)

    def test_other_subclasses_still_refuse(self):
        class Other(match.BufferCallProof):
            pass

        class Further(match.FunctionBufferCallProof):
            pass

        for kind in (Other, Further):
            for options, message in ((dict(bios_wrappers=True), "BIOS wrapper summaries require"),
                                     (dict(copy_helper_index=self.index), "copy summaries require"),
                                     (dict(switch_callee_index=self.index), "switch callees require")):
                with self.subTest(kind=kind.__name__, message=message), \
                        self.assertRaisesRegex(ValueError, message):
                    kind(self.rom, self.mapping, stack_arguments=True, **options)

    def test_without_stack_arguments_the_copy_and_switch_summaries_refuse(self):
        for options, message in ((dict(copy_helper_index=self.index), "copy summaries require"),
                                 (dict(switch_callee_index=self.index), "switch callees require")):
            with self.subTest(message=message), self.assertRaisesRegex(ValueError, message):
                match.FunctionBufferCallProof(self.rom, self.mapping, **options)


@unittest.skipUnless(data_calls.tools_present(), "fixed compiler and ARM tools required")
class FunctionLiteralSummaryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix="function_literal_summaries_", dir=scratch)
        cls.base = Path(cls.temporary.name)
        cls.copy = build(cls.base / "copy", COPY)
        cls.copy_result = data_calls.run(cls.copy)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def replays(self, report, root):
        with patch.dict(os.environ, FFTA_ROM=str(root / "baserom.bin")):
            return evidence.report_matches(report, root, A)

    def test_a_copy_into_a_local_is_summarised_on_the_function_literal_path(self):
        code, output, report = self.copy_result
        self.assertEqual(code, 0, output)
        self.assertIn("verdict MATCH - byte identical", output)
        self.assertEqual(data_calls.verification(report), data_buffer.FUNCTION_SCHEMA)
        line, = lines(report, "* buffer copy summary:")
        self.assertRegex(line, r"^\* buffer copy summary: `pinned-copy-helper-summary-v1` 0x081443FC at "
                               r"0x080002[0-9A-F]{2}: count 8, destination sp\+0, source external; ")
        self.assertTrue(self.replays(report, self.copy))

    def test_an_edited_or_removed_summary_line_fails_replay(self):
        _, _, report = self.copy_result
        rows = report.splitlines()
        at = next(i for i, row in enumerate(rows) if row.startswith("* buffer copy summary:"))
        for name, edited in (("count", rows[:at] + [rows[at].replace("count 8", "count 4")] + rows[at + 1:]),
                             ("removed", rows[:at] + rows[at + 1:])):
            with self.subTest(name=name):
                self.assertFalse(self.replays("\n".join(edited) + "\n", self.copy))

    def test_the_plain_twin_keeps_its_schema(self):
        root = build(self.base / "plain", PLAIN_COPY)
        code, output, report = data_calls.run(root)
        self.assertEqual(code, 0, output)
        self.assertEqual(data_calls.verification(report), data_buffer.SCHEMA)
        self.assertEqual(len(lines(report, "* buffer copy summary:")), 1)

    def test_a_cpuset_copy_into_a_local_is_summarised_on_the_function_literal_path(self):
        root = build(self.base / "cpuset", CPUSET_COPY)
        code, output, report = data_calls.run(root)
        self.assertEqual(code, 0, output)
        self.assertEqual(data_calls.verification(report), data_buffer.FUNCTION_SCHEMA)
        self.assertTrue(lines(report, "* buffer BIOS summaries:"), report)
        self.assertTrue(self.replays(report, root))

    def test_a_copy_past_the_local_still_refuses(self):
        # 12 bytes into an 8-byte local: the summary's own destination check refuses
        root = build(self.base / "overrun", COPY, count=12)
        code, output, report = data_calls.run(root)
        self.assertNotEqual(code, 0, output)
        self.assertIsNone(report)
        self.assertIn("function-data-buffer proof:", output)

    def test_without_the_index_the_function_literal_proof_refuses_at_the_helper(self):
        # The proof the issuance path builds without an index has no copy summary.
        body, rom, mapping, objects, calls, literals, functions = self.linked(self.copy)
        with self.assertRaisesRegex(ValueError, "buffer callee 0x081443FC: unsupported buffer pointer use or escape"):
            data_buffer.prove(body, A, rom, mapping, objects, calls, literals, functions)
        index = (self.copy / "symbols/functions.txt").read_bytes()
        _, proof, schema, _ = data_buffer.prove(body, A, rom, mapping, objects, calls, literals, functions,
                                                index=index)
        self.assertEqual(schema, data_buffer.FUNCTION_SCHEMA)
        self.assertEqual([record["count"] for record in proof.copy_summaries.evidence()["observations"]], [8])

    def linked(self, root):
        args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                                  objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        rom = (root / "baserom.bin").read_bytes()
        mapping = (root / "config/functions.json").read_bytes()
        objects = (root / "config/data_symbols.json").read_bytes()
        runner = match.Runner(match.DEFAULT_CC, root=root, wsl_path=match.DEFAULT_WSL_PATH, timeout=120)
        with runner.workspace() as workspace:
            _, _, original = match.compile_object(runner, workspace, args, root, A, "src/08000200.c")
            functions = {}
            body, calls, literals = match.link_calls(runner, workspace, args, original, A, mapping,
                                                     len(rom), rom, objects, functions)
        return body, rom, mapping, objects, calls, literals, functions


if __name__ == "__main__":
    unittest.main()
