"""Typed named data beside the version-2 bounded buffer proof.

`elf-symbol-thumb-data-buffer-calls-v1` (plain direct-call path) and
`elf-symbol-thumb-function-data-buffer-calls-v1` (function-literal path) admit
a caller whose stack buffer reaches a callee while it also loads typed named
objects. Natural C callers are compiled with the fixed agbcc and
`-mthumb-interwork -O2`, linked at 0x08000200 beside assembled callees, and
run through `match.py`; the reports are replayed by `report_matches`.
"""
import argparse
import json
import os
from pathlib import Path
import shutil
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
import report_fixtures
import match_evidence as evidence
import data_buffer_profile as data_buffer
from test_buffer_loop_replay import counted

BASE = match.ROM_BASE
# After the cartridge header, where the complete owner graph may start.
A = 0x08000200
CALLEES = 0x08000400
CPUSET = 0x0814186C
OBJECTS = {"data_02000000": "0x02000000"}
STORES = "strh r0, [r1]\nstrh r0, [r1, #6]\nbx lr"
HEADER = ("typedef unsigned short u16;\ntypedef unsigned int u32;\n"
          "extern u16 data_02000000[];\n")
# The caller hands a four-halfword local to func_08000400(value, out).
PLAIN = HEADER + """extern void func_08000400(u16 value, u16 *out);
void func_08000200(u16 value)
{
    u16 buffer[%(size)d];

    func_08000400(value, buffer);
    data_02000000[0] = buffer[0];
    data_02000000[1] = buffer[%(last)d];
%(extra)s}
"""
# The same with a function literal handed to the callee in R2.
LITERAL = HEADER + """extern void func_08000500(void);
extern void func_08000400(u16 value, u16 *out, void (*callback)(void));
void func_08000200(u16 value)
{
    u16 buffer[4];

    func_08000400(value, buffer, func_08000500);
    data_02000000[0] = buffer[0];
    data_02000000[1] = buffer[3];
%(extra)s}
"""
# An indirect call through a parameter becomes a BL to _call_via_rN.
THUNK = HEADER + """extern void func_08000400(u16 value, u16 *out);
void func_08000200(u16 value, void (*hook)(void))
{
    u16 buffer[4];

    hook();
    func_08000400(value, buffer);
    data_02000000[0] = buffer[0];
    data_02000000[1] = buffer[3];
}
"""
# CpuSet through the indexed BIOS wrapper; no local alias reaches it.
CPUSET_CALL = HEADER + """extern void func_08000400(u16 value, u16 *out);
extern void func_0814186C(const void *source, void *destination, u32 control);
void func_08000200(u16 value)
{
    u16 buffer[4];

    func_08000400(value, buffer);
    data_02000000[0] = buffer[0];
    %(use)s
}
"""
DATA_ONLY = HEADER + """extern void func_08000400(u16 value, u16 *out);
void func_08000200(u16 value)
{
    func_08000400(value, data_02000000);
}
"""
BUFFER_ONLY = """typedef unsigned short u16;
extern void func_08000400(u16 value, u16 *out);
u16 func_08000200(u16 value)
{
    u16 buffer[4];

    func_08000400(value, buffer);
    return buffer[0] + buffer[3];
}
"""


def tools_present():
    return Path(os.path.expandvars(match.DEFAULT_CC)).is_file() and \
        all(shutil.which(tool) for tool in (match.DEFAULT_AS, match.DEFAULT_LD, match.DEFAULT_OBJCOPY))


def build(root, source, callees, objects=OBJECTS, large=False, function_literal_thunks=False):
    """A complete tree: the caller from `source`, assembled callees from 0x08000400.

    callees: [(name, assembly)], each 0x100 apart; `large` adds the CpuSet wrapper
    and the _call_via_rN thunks at their ROM addresses.
    """
    root = Path(root)
    for name in ("src", "include", "config", "symbols", "build"):
        (root / name).mkdir(parents=True, exist_ok=True)
    work = root / "build"
    names = [name for name, _ in callees]
    (work / "callees.s").write_text(
        ".syntax unified\n.arch armv4t\n.thumb\n.text\n" +
        "".join(f".global {name}, {name}_end\n" for name in names) +
        "".join(f".org 0x{0x100 * index:x}\n{name}:\n{body}\n{name}_end:\n"
                for index, (name, body) in enumerate(callees)))
    for command in (
            [match.DEFAULT_AS, "-mthumb-interwork", str(work / "callees.s"), "-o", str(work / "callees.o")],
            [match.DEFAULT_LD, f"-Ttext=0x{CALLEES:08X}", "-e", names[0], str(work / "callees.o"),
             "-o", str(work / "callees.elf")],
            [match.DEFAULT_OBJCOPY, "-O", "binary", "--only-section=.text", str(work / "callees.elf"),
             str(work / "callees.bin")]):
        subprocess.run(command, check=True, capture_output=True)
    image = match.elf_image((work / "callees.elf").read_bytes())
    symbols = {symbol["name"]: symbol["value"] for symbol in image["symbols"]}
    rom = bytearray(0x08142280 - BASE if large else 0x1000)
    code = (work / "callees.bin").read_bytes()
    rom[CALLEES - BASE:CALLEES - BASE + len(code)] = code
    entries = [{"rom": f"0x{symbols[name]:08X}", "end": f"0x{symbols[name + '_end']:08X}",
                "mode": "thumb"} for name in names]
    if large:
        struct.pack_into("<HH", rom, CPUSET - BASE, 0xDF0B, 0x4770)
        entries.append({"rom": f"0x{CPUSET:08X}", "end": f"0x{CPUSET + 4:08X}", "mode": "thumb"})
        for register in range(15):
            struct.pack_into("<HH", rom, match.RUNTIME_HELPERS[f"_call_via_r{register}"] - BASE,
                             0x4700 | register << 3, 0x46C0)
    (root / "src/08000200.c").write_text(source)
    (root / "include/types.h").write_text("/* fixture */\n")
    objects = json.dumps(objects).encode()
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
                                      objects, {}, function_literal_thunks=function_literal_thunks)
    assert A + len(body) <= CALLEES
    rom[A - BASE:A - BASE + len(body)] = body
    (root / "config/functions.json").write_bytes(mapping)
    (root / "symbols/functions.txt").write_text("".join(
        f"{int(entry['rom'], 16):08X} {int(entry['end'], 16):08X} "
        f"{int(entry['end'], 16) - int(entry['rom'], 16)} 0 return\n" for entry in entries))
    (root / "baserom.bin").write_bytes(bytes(rom))
    return root


def run(root):
    """match.py on the caller: (exit status, stdout + stderr, report text or None)."""
    report = Path(root) / "docs/match/08000200.md"
    if report.exists():
        report.unlink()
    environment = dict(os.environ, FFTA_ROM=str(Path(root) / "baserom.bin"), PYTHONDONTWRITEBYTECODE="1")
    result = subprocess.run([sys.executable, str(ROOT / "tools/match.py"), "--root", str(root), "0x08000200"],
                            capture_output=True, text=True, env=environment, timeout=600)
    return result.returncode, result.stdout + result.stderr, report.read_text() if report.exists() else None


def verification(report):
    (line,) = [line for line in report.splitlines() if line.startswith("* verification: ")]
    return line[len("* verification: `"):-1]


@unittest.skipUnless(tools_present(), "fixed compiler and ARM tools required")
class DataBufferNativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix="data_buffer_calls_", dir=scratch)
        cls.base = Path(cls.temporary.name)
        cls.plain = build(cls.base / "plain", PLAIN % dict(size=4, last=3, extra=""),
                          [("func_08000400", STORES)])
        cls.code, cls.output, cls.report = run(cls.plain)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def fixture(self, name, source, callees=(("func_08000400", STORES),), **options):
        return build(self.base / name, source, list(callees), **options)

    def replays(self, report, root=None):
        root = root or self.plain
        with patch.dict(os.environ, FFTA_ROM=str(root / "baserom.bin")):
            return report_fixtures.replay(report, root, A)

    def assertRefused(self, root, message):
        code, output, report = run(root)
        self.assertNotEqual(code, 0, output)
        self.assertIsNone(report)
        self.assertIn(message, output)

    # --- (a) the plain direct-call path ---

    def test_buffer_beside_typed_data_matches_and_replays(self):
        self.assertEqual(self.code, 0, self.output)
        self.assertIn("verdict MATCH - byte identical", self.output)
        self.assertEqual(verification(self.report), data_buffer.SCHEMA)
        lines = self.report.splitlines()
        self.assertIn(f"* buffer calls: {evidence.STACK_BUFFER_SUMMARY}", lines)
        self.assertIn(f"* stack frame: {evidence.STACK_SUMMARY}", lines)
        self.assertIn(data_buffer.CALLS_FIELD + data_buffer.SUMMARIES[data_buffer.SCHEMA], lines)
        (encoded,) = [line for line in lines if line.startswith(data_buffer.MANIFEST_FIELD)]
        manifest = json.loads(encoded[len(data_buffer.MANIFEST_FIELD) + 1:-1])
        self.assertEqual([row[1:] for row in manifest["data"]], [["data_02000000", 0]])
        self.assertEqual([row[1] for row in manifest["calls"]], ["func_08000400"])
        self.assertEqual(manifest["functions"], [])
        self.assertNotIn("numeric_hardware_words", manifest)
        self.assertFalse([line for line in lines if line.startswith("* buffer loop replay")])
        self.assertTrue(self.replays(self.report))

    def test_the_same_caller_without_data_or_without_a_buffer_keeps_its_schema(self):
        code, output, report = run(self.fixture("buffer_only", BUFFER_ONLY))
        self.assertEqual(code, 0, output)
        self.assertEqual(verification(report), evidence.STACK_BUFFER_SCHEMA)
        root = self.fixture("data_only", DATA_ONLY)
        code, output, report = run(root)
        self.assertEqual(code, 0, output)
        self.assertIn(verification(report), (evidence.DATA_SCHEMA, evidence.FRAMED_DATA_SCHEMA))
        # A data pointer handed to a callee is not a buffer: the composed proof has nothing to inspect.
        self.assertRaisesRegex(ValueError, "requires an inspected buffer call", self.prove, root)

    def test_report_replay_refuses_edited_fields_and_changed_inputs(self):
        report = self.report
        lines = report.splitlines()
        (manifest,) = [line for line in lines if line.startswith(data_buffer.MANIFEST_FIELD)]
        (digest,) = [line for line in lines if line.startswith(data_buffer.PROOF_FIELD)]
        (buffer_digest,) = [line for line in lines if line.startswith("* buffer proof SHA-256: ")]
        stack = f"* stack frame: {evidence.STACK_SUMMARY}"
        summary = data_buffer.CALLS_FIELD + data_buffer.SUMMARIES[data_buffer.SCHEMA]
        edits = {
            "data name": report.replace(manifest, manifest.replace('"data_02000000"', '"data_02000002"')),
            "data addend": report.replace(manifest, manifest.replace('"data_02000000",0', '"data_02000000",2')),
            "dropped manifest": report.replace(manifest + "\n", ""),
            "proof digest": report.replace(digest, digest[:-65] + "0" * 64 + "`"),
            "buffer digest": report.replace(buffer_digest, buffer_digest[:-65] + "0" * 64 + "`"),
            "premise": report.replace(summary, summary.replace("; " + data_buffer.PREMISE, "")),
            "stack frame": report.replace(stack + "\n", ""),
            "indented": report.replace(manifest, " " + manifest),
            "extra field": report.replace(manifest, manifest + "\n* function addresses: x"),
            "replay line": report.replace(manifest, manifest + "\n* buffer loop replay: `bounded-loop-replay-v2`"),
            "duplicate": report.replace(digest, digest + "\n" + digest),
        }
        for schema in (evidence.DATA_SCHEMA, evidence.FRAMED_DATA_SCHEMA, evidence.STACK_BUFFER_SCHEMA,
                       evidence.FUNCTION_BUFFER_SCHEMA, data_buffer.FUNCTION_SCHEMA):
            edits[schema] = report.replace(f"`{data_buffer.SCHEMA}`", f"`{schema}`")
        for field in ("* data symbols SHA-256: ", "* mapping SHA-256: ", "* source SHA-256: "):
            (line,) = [line for line in lines if line.startswith(field)]
            edits[field] = report.replace(line, line[:-65] + "0" * 64 + "`")
        # Forgeries that keep every digest consistent with the edited fields.
        manifest_text = manifest[len(data_buffer.MANIFEST_FIELD) + 1:-1]
        edits["consistent addend"] = self.forge(report, manifest_text.replace('"data_02000000",0',
                                                                              '"data_02000000",2'))
        edits["consistent hardware record"] = self.forge(report, manifest_text[:-1] + ',"numeric_hardware_words":'
            '{"contract":"x","schema":"reached-numeric-hardware-literals-v1","words":[]}}')
        edits["consistent schema"] = self.forge(report, manifest_text, data_buffer.FUNCTION_SCHEMA)
        # Every other bound field: the source path, toolchain, summaries, verdict and the canonical manifest.
        for old, new in (("* source: `src/08000200.c`", "* source: `src/x/08000200.c`"),
                         (f"* compiler: `{match.DEFAULT_CC} {match.DEFAULT_FLAGS}`",
                          f"* compiler: `{match.DEFAULT_CC} -mthumb-interwork -O1`"),
                         (f"* buffer calls: {evidence.STACK_BUFFER_SUMMARY}",
                          f"* buffer calls: {evidence.BUFFER_SUMMARY}"),
                         (f"* control flow: {evidence.CALL_SUMMARY}", "* control flow: closed leaf CFG"),
                         ("* source plausibility: plausible", "* source plausibility: IMPLAUSIBLE"),
                         ("* hand-asm allow list: not listed", "* hand-asm allow list: listed"),
                         ("**MATCH - byte identical**", "**NOT MATCHING - bytes differ**"),
                         (manifest, manifest.replace('],"data":', '], "data":'))):
            with self.subTest(field=old[:24]):
                self.assertIn(old, report)
            edits["field " + old[:24]] = report.replace(old, new)
        # Compiled and ROM bytes edited together, with the data-buffer digest recomputed to agree.
        (compiled,) = [line for line in lines if line.startswith("* compiled : ")]
        (rom_line,) = [line for line in lines if line.startswith("* ROM bytes: ")]
        body = bytes.fromhex(compiled[len("* compiled : `"):-1])
        flipped = body[:-1] + bytes([body[-1] ^ 1])
        edits["consistent bytes"] = self.forge(
            report.replace(compiled, f"* compiled : `{flipped.hex()}`").replace(
                rom_line, f"* ROM bytes: `{flipped.hex()}` ({len(flipped)} bytes)"), manifest_text)
        edits["ROM bytes only"] = report.replace(rom_line, f"* ROM bytes: `{flipped.hex()}` ({len(flipped)} bytes)")
        edits["verdict count"] = report.replace(f"**MATCH - byte identical** - {len(body)}/{len(body)} bytes",
                                                "**MATCH - byte identical** - 4/4 bytes")
        self.assertTrue(self.replays(self.forge(report, manifest_text)))
        # Without any data-buffer field the plain schemas refuse the data: it is not their evidence.
        stripped = "\n".join(line for line in lines if not line.startswith(data_buffer.MARKER))
        for schema in (evidence.DATA_SCHEMA, evidence.FRAMED_DATA_SCHEMA, evidence.STACK_BUFFER_SCHEMA):
            edits["stripped " + schema] = stripped.replace(f"`{data_buffer.SCHEMA}`", f"`{schema}`")
        for name, edited in edits.items():
            with self.subTest(edit=name):
                self.assertNotEqual(edited, report)
                self.assertFalse(self.replays(edited))
        self.assertTrue(self.replays(report))
        for path, change in ((self.plain / "config/data_symbols.json",
                              json.dumps(dict(OBJECTS, data_02000100="0x02000100")).encode()),
                             (self.plain / "src/08000200.c", None),
                             (self.plain / "config/functions.json", None)):
            original = path.read_bytes()
            try:
                path.write_bytes(change if change is not None else original + b"\n")
                with self.subTest(path=path.name):
                    self.assertFalse(self.replays(report))
            finally:
                path.write_bytes(original)
        self.assertTrue(self.replays(report))

    def forge(self, report, manifest, schema=data_buffer.SCHEMA):
        """The report with `manifest` and `schema`, every data-buffer digest recomputed to agree."""
        lines = report.splitlines()

        def field(prefix):
            (line,) = [line for line in lines if line.startswith(prefix)]
            return line[len(prefix):].strip("`")
        data = bytes.fromhex(field("* compiled : "))
        digest = data_buffer.fingerprint(
            schema, A, data, json.loads(manifest), field("* source SHA-256: "),
            (self.plain / "config/functions.json").read_bytes(),
            (self.plain / "config/data_symbols.json").read_bytes(), field("* buffer proof SHA-256: "))
        forged = [f"{data_buffer.MANIFEST_FIELD}`{manifest}`" if line.startswith(data_buffer.MANIFEST_FIELD) else
                  f"{data_buffer.PROOF_FIELD}`{digest}`" if line.startswith(data_buffer.PROOF_FIELD) else
                  data_buffer.CALLS_FIELD + data_buffer.SUMMARIES[schema] if line.startswith(data_buffer.CALLS_FIELD) else
                  f"* verification: `{schema}`" if line.startswith("* verification: ") else line
                  for line in lines]
        return "\n".join(forged) + "\n"

    def test_looping_callee_is_replayed_and_stated(self):
        callees = (("func_08000400", counted(4)), ("child", "bx lr"))
        root = self.fixture("loop", PLAIN % dict(size=4, last=3, extra=""), callees)
        code, output, report = run(root)
        self.assertEqual(code, 0, output)
        self.assertEqual(verification(report), data_buffer.SCHEMA)
        (line,) = [line for line in report.splitlines() if line.startswith("* buffer loop replay")]
        self.assertRegex(line, r"^\* buffer loop replay: `bounded-loop-replay-v2` callee 0x08000400 ")
        self.assertTrue(self.replays(report, root))
        self.assertFalse(self.replays(report.replace(line + "\n", ""), root))
        self.assertFalse(self.replays(report.replace(line, line + "\n" + line), root))
        small = self.fixture("loop_small", PLAIN % dict(size=2, last=1, extra=""), callees)
        self.assertRefused(small, "buffer access is unaligned or outside allocated local words")

    def test_store_outside_the_buffer_is_refused_beside_data(self):
        self.assertRefused(self.fixture("small", PLAIN % dict(size=2, last=1, extra="")),
                           "buffer access is unaligned or outside allocated local words")

    # --- typed coverage of reached address-domain words ---

    def test_untyped_ram_and_rom_words_are_refused(self):
        for name, extra in (("iwram", "    *(u16 *)0x03001000 = buffer[1];\n"),
                            ("ewram", "    *(u16 *)0x02001000 = buffer[1];\n"),
                            ("rom", "    data_02000000[2] = *(const u16 *)0x08000F00;\n")):
            with self.subTest(word=name):
                self.assertRefused(self.fixture(name, PLAIN % dict(size=4, last=3, extra=extra)),
                                   "data-buffer address literals require exact typed object/function coverage")

    def test_typed_words_outside_the_address_domain_are_refused(self):
        # As in the owner rule, every typed literal must also be a reached address-domain word.
        source = (PLAIN % dict(size=4, last=3, extra="    data_02000000[2] = data_0E000010[0];\n")).replace(
            "extern u16 data_02000000[];\n", "extern u16 data_02000000[];\nextern u16 data_0E000010[];\n")
        root = self.fixture("sram", source, objects=dict(OBJECTS, data_0E000010="0x0E000010"))
        self.assertRefused(root, "typed word 0x")
        self.assertRefused(root, "outside the address domain")

    # --- ROM wait-state mirrors (#377): 0x0A000000-0x0DFFFFFF is the same ROM ---

    def test_untyped_rom_mirror_words_are_refused_as_rom_words(self):
        for name, value in (("ws1", 0x0A000300), ("ws2", 0x0C000300), ("ws0", 0x08000300)):
            extra = f"    data_02000000[2] = *(const u16 *)0x{value:08X};\n"
            with self.subTest(word=name):
                self.assertRefused(self.fixture(name, PLAIN % dict(size=4, last=3, extra=extra)),
                                   f" = 0x{value:08X}")

    def test_sram_words_and_masks_beside_a_buffer_call_stay_numbers(self):
        for name, extra in (("sram", "    *(unsigned char *)0x0E000010 = buffer[3];\n"),
                            ("mask", "    *(u32 *)(data_02000000 + 4) = buffer[3] & 0x0FFFFFFF;\n")):
            with self.subTest(word=name):
                root = self.fixture(name, PLAIN % dict(size=4, last=3, extra=extra))
                code, output, report = run(root)
                self.assertEqual(code, 0, output)
                self.assertEqual(verification(report), data_buffer.SCHEMA)
                self.assertTrue(self.replays(report, root))

    def test_a_typed_object_spelled_through_a_mirror_is_refused(self):
        # An addend can carry a typed object word into a mirror: of other ROM bytes, or of the
        # caller's own (linking refuses that one, as for the caller's own wait-state-0 bytes).
        source = (PLAIN % dict(size=4, last=3, extra="    data_02000000[2] = *(u16 *)(data_06000000 + %s);\n")).replace(
            "extern u16 data_02000000[];\n", "extern u16 data_02000000[];\nextern char data_06000000[];\n")
        objects = dict(OBJECTS, data_06000000="0x06000000")
        root = self.fixture("typed_mirror", source % "0x04000300", objects=objects)
        self.assertRefused(root, "typed word 0x")
        self.assertRefused(root, "outside the address domain")
        for name, addend in (("typed_own_ws1", "0x04000200"), ("typed_own_ws2", "0x06000204")):
            with self.subTest(addend=addend), \
                    self.assertRaisesRegex(ValueError, "data relocation overflows or references its own function"):
                self.fixture(name, source % addend, objects=objects)

    def test_a_mirror_function_pointer_through_a_thunk_needs_function_provenance(self):
        source = HEADER + """extern void func_08000400(u16 value, u16 *out);
void func_08000200(u16 value)
{
    u16 buffer[4];
    void (*f)(u16, u16 *) = (void (*)(u16, u16 *))%s;

    func_08000400(value, buffer);
    f(value, 0);
    data_02000000[0] = buffer[0];
}
"""
        callees = (("func_08000400", STORES), ("func_08000500", "bx lr"))
        for pointer in ("0x0A000501", "0x0C000501", "0x08000501"):
            with self.subTest(pointer=pointer):
                root = self.fixture("pointer_" + pointer, source % pointer, callees, large=True)
                self.assertRefused(root, "code-entry thunk literals require canonical function provenance")
        # The named spelling keeps its own refusal: no data-buffer report takes a runtime thunk literal.
        named = (source % "func_08000500").replace(
            "extern void func_08000400", "extern void func_08000500(u16 value, u16 *out);\nextern void func_08000400")
        with self.assertRaisesRegex(match.Refusal, "function-address evidence does not support runtime call thunks"):
            self.fixture("pointer_named", named, callees, large=True)

    def test_untyped_hardware_numbers_are_recorded_and_bound(self):
        root = self.fixture("vram", PLAIN % dict(size=4, last=3, extra="    *(u16 *)0x06001000 = buffer[1];\n"))
        code, output, report = run(root)
        self.assertEqual(code, 0, output)
        self.assertEqual(verification(report), data_buffer.SCHEMA)
        (encoded,) = [line for line in report.splitlines() if line.startswith(data_buffer.MANIFEST_FIELD)]
        record = json.loads(encoded[len(data_buffer.MANIFEST_FIELD) + 1:-1])["numeric_hardware_words"]
        self.assertEqual(record["schema"], "reached-numeric-hardware-literals-v1")
        self.assertEqual([row[1] for row in record["words"]], [0x06001000])
        self.assertTrue(self.replays(report, root))
        self.assertFalse(self.replays(report.replace(str(0x06001000), str(0x06001004)), root))

    def test_a_cpuset_control_needs_typed_provenance_but_the_same_number_does_not(self):
        control = "func_0814186C(data_02000000, data_02000000 + 0x80, 0x05000040);"
        self.assertRefused(self.fixture("control", CPUSET_CALL % dict(use=control), large=True),
                           "data-buffer address literals require exact typed object/function coverage")
        number = "*(u32 *)(data_02000000 + 4) = 0x05000040;"
        root = self.fixture("number", CPUSET_CALL % dict(use=number), large=True)
        code, output, report = run(root)
        self.assertEqual(code, 0, output)
        (encoded,) = [line for line in report.splitlines() if line.startswith(data_buffer.MANIFEST_FIELD)]
        record = json.loads(encoded[len(data_buffer.MANIFEST_FIELD) + 1:-1])["numeric_hardware_words"]
        self.assertEqual([row[1] for row in record["words"]], [0x05000040])

    # --- the plain path's thunk rules ---

    def test_a_thunk_call_without_an_alias_stays_ordinary_and_binds_no_code_entry_as_data(self):
        root = self.fixture("thunk", THUNK, large=True)
        code, output, report = run(root)
        self.assertEqual(code, 0, output)
        self.assertEqual(verification(report), data_buffer.SCHEMA)
        self.assertRegex(report, r'"_call_via_r[0-9]+"')
        self.assertTrue(self.replays(report, root))
        # An object at an indexed code entry is refused once a thunk call is present
        # (linking refuses it too; this is the composed proof's own check, run on replay).
        entries = json.loads((root / "config/functions.json").read_bytes())
        entries.append({"rom": "0x02000000", "end": "0x02000004", "mode": "thumb"})
        with self.assertRaisesRegex(ValueError, "thunk callers cannot bind indexed function entries as data"):
            self.prove(root, mapping=json.dumps(entries).encode())

    def test_typed_hardware_objects_are_not_recorded_as_numbers(self):
        source = (PLAIN % dict(size=4, last=3, extra="    *(u16 *)0x06001000 = buffer[1];\n"
                                                    "    data_06002000[0] = buffer[2];\n")).replace(
            "extern u16 data_02000000[];\n", "extern u16 data_02000000[];\nextern u16 data_06002000[];\n")
        root = self.fixture("typed_vram", source, objects=dict(OBJECTS, data_06002000="0x06002000"))
        code, output, report = run(root)
        self.assertEqual(code, 0, output)
        (encoded,) = [line for line in report.splitlines() if line.startswith(data_buffer.MANIFEST_FIELD)]
        manifest = json.loads(encoded[len(data_buffer.MANIFEST_FIELD) + 1:-1])
        self.assertIn("data_06002000", [row[1] for row in manifest["data"]])
        self.assertEqual([row[1] for row in manifest["numeric_hardware_words"]["words"]], [0x06001000])

    def test_numeric_hardware_requires_the_reached_owner_graph(self):
        import owner_graph_profile
        root = self.fixture("vram_graph", PLAIN % dict(size=4, last=3,
                                                       extra="    *(u16 *)0x06001000 = buffer[1];\n"))
        self.assertEqual(self.prove(root)[2], data_buffer.SCHEMA)
        graph = owner_graph_profile.graph

        def partial(*arguments, **options):
            instructions, *rest = graph(*arguments, **options)
            last = max(instructions)
            return ({site: item for site, item in instructions.items() if site != last}, *rest)
        with patch.object(owner_graph_profile, "graph", partial), \
                self.assertRaisesRegex(ValueError, "exact complete owner graph"):
            self.prove(root)

    def test_replay_reruns_the_plausibility_check(self):
        root = self.fixture("pragma", PLAIN % dict(size=4, last=3, extra=""))
        code, output, report = run(root)
        self.assertEqual(code, 0, output)
        self.assertTrue(self.replays(report, root))
        # The same bytes from a source the checker refuses; every bound digest made to agree.
        path = root / "src/08000200.c"
        path.write_text('#pragma GCC optimize ("O2")\n' + path.read_text())
        digest = evidence.source_fingerprint(root, A)
        (line,) = [line for line in report.splitlines() if line.startswith("* source SHA-256: ")]
        edited = report.replace(line, f"* source SHA-256: `{digest}`")
        (manifest,) = [line for line in report.splitlines() if line.startswith(data_buffer.MANIFEST_FIELD)]
        lines = edited.splitlines()
        (buffer_digest,) = [line for line in lines if line.startswith("* buffer proof SHA-256: ")]
        (compiled,) = [line for line in lines if line.startswith("* compiled : ")]
        fingerprint = data_buffer.fingerprint(
            data_buffer.SCHEMA, A, bytes.fromhex(compiled[len("* compiled : `"):-1]),
            json.loads(manifest[len(data_buffer.MANIFEST_FIELD) + 1:-1]), digest,
            (root / "config/functions.json").read_bytes(), (root / "config/data_symbols.json").read_bytes(),
            buffer_digest[len("* buffer proof SHA-256: `"):-1])
        edited = "\n".join(f"{data_buffer.PROOF_FIELD}`{fingerprint}`" if line.startswith(data_buffer.PROOF_FIELD)
                           else line for line in lines) + "\n"
        output = run(root)[1]
        self.assertIn("bytes   identical", output)
        self.assertIn("source  IMPLAUSIBLE", output)
        self.assertFalse(self.replays(edited, root))

    # --- (b) the function-literal path ---

    def test_function_literal_path_walks_runtime_thunks_in_dependencies(self):
        # The callee drops every alias before calling the callback through _call_via_r2; the
        # thunks are indexed, as in the ROM.  The function-buffer exclusion refused it until
        # call_via_target_profile's T1: the call passes no frame address, so it is an ordinary
        # call as on the plain path, and the exclusion returns only with T1's policy off.
        callee = ("push {lr}\nstrh r0, [r1]\nstrh r0, [r1, #6]\nmovs r0, #0\nmovs r1, #0\n"
                  f"bl 0x{match.RUNTIME_HELPERS['_call_via_r2']:08X}\npop {{r0}}\nbx r0")
        root = self.fixture("literal_thunk", LITERAL % dict(extra=""),
                            (("func_08000400", callee), ("func_08000500", "bx lr")), large=True)
        entries = json.loads((root / "config/functions.json").read_bytes())
        for value in sorted(match.RUNTIME_HELPERS.values()):
            entries.append({"rom": f"0x{value:08X}", "end": f"0x{value + 2:08X}", "mode": "thumb"})
        (root / "config/functions.json").write_text(json.dumps(entries))
        (root / "symbols/functions.txt").write_text("".join(
            f"{int(entry['rom'], 16):08X} {int(entry['end'], 16):08X} "
            f"{int(entry['end'], 16) - int(entry['rom'], 16)} 0 return\n" for entry in entries))
        code, output, report = run(root)
        self.assertEqual(code, 0, output)
        self.assertEqual(verification(report), data_buffer.FUNCTION_SCHEMA)
        self.assertTrue(self.replays(report, root))
        import call_via_target_profile as call_via
        body, rom, mapping, objects, calls, literals, functions = self.linked(root)
        with patch.object(call_via.POLICY, "enabled", False), self.assertRaisesRegex(
                ValueError, "function-buffer evidence excludes runtime call thunks in inspected dependencies"):
            data_buffer.prove(body, A, rom, mapping, objects, calls, literals, functions)

    def test_function_literal_beside_buffer_and_typed_data(self):
        root = self.fixture("literal", LITERAL % dict(extra=""),
                            (("func_08000400", STORES), ("func_08000500", "bx lr")))
        code, output, report = run(root)
        self.assertEqual(code, 0, output)
        self.assertEqual(verification(report), data_buffer.FUNCTION_SCHEMA)
        (encoded,) = [line for line in report.splitlines() if line.startswith(data_buffer.MANIFEST_FIELD)]
        manifest = json.loads(encoded[len(data_buffer.MANIFEST_FIELD) + 1:-1])
        self.assertEqual([row[1] for row in manifest["functions"]], ["func_08000500"])
        self.assertEqual([row[1] for row in manifest["data"]], ["data_02000000"])
        self.assertFalse([line for line in report.splitlines() if line.startswith("* function address")])
        self.assertTrue(self.replays(report, root))
        self.assertFalse(self.replays(report.replace(f"`{data_buffer.FUNCTION_SCHEMA}`",
                                                     f"`{data_buffer.SCHEMA}`"), root))
        self.assertFalse(self.replays(report.replace(f"`{data_buffer.FUNCTION_SCHEMA}`",
                                                     f"`{evidence.FUNCTION_BUFFER_SCHEMA}`"), root))
        untyped = self.fixture("literal_iwram", LITERAL % dict(extra="    *(u16 *)0x03001000 = buffer[1];\n"),
                               (("func_08000400", STORES), ("func_08000500", "bx lr")))
        self.assertRefused(untyped, "function-data-buffer proof: data-buffer address literals require "
                                    "exact typed object/function coverage")

    # --- the composed proof on linked bytes ---

    def linked(self, root):
        args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                                  objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD,
                                  flags=match.DEFAULT_FLAGS)
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

    def prove(self, root, **changes):
        body, rom, mapping, objects, calls, literals, functions = self.linked(root)
        values = dict(data=body, address=A, rom=rom, mapping=mapping, objects=objects, calls=calls,
                      data_relocations=literals, function_relocations=functions)
        values.update(changes)
        return data_buffer.prove(**values)

    def test_object_words_must_be_complete_reached_bindings(self):
        body, rom, mapping, objects, calls, literals, _ = self.linked(self.plain)
        (offset, (name, value)), = literals.items()
        self.assertEqual(self.prove(self.plain)[2], data_buffer.SCHEMA)
        for moved, reason in ((offset + 2, "bindings must be ordered complete words|misaligned"),
                              (0, "literal does not equal its binding")):
            with self.subTest(offset=moved), self.assertRaisesRegex(ValueError, reason):
                self.prove(self.plain, data_relocations={moved: (name, value)})
        with self.assertRaisesRegex(ValueError, "requires typed named object relocations"):
            self.prove(self.plain, data_relocations={})
        with self.assertRaisesRegex(ValueError, "not in the data symbol map"):
            self.prove(self.plain, objects=b'{"data_02000004": "0x02000004"}')
        # A word equal to the object address that no instruction loads.
        extended = body + struct.pack("<I", value)
        self.assertEqual((A + len(body)) % 4, 0)
        rom = bytearray(rom)
        rom[A - BASE:A - BASE + len(extended)] = extended
        entries = json.loads(mapping)
        entries[0]["end"] = f"0x{A + len(extended):08X}"
        with self.assertRaisesRegex(ValueError, "not a reachable PC-relative literal-pool load"):
            self.prove(self.plain, data=extended, rom=bytes(rom), mapping=json.dumps(entries).encode(),
                       data_relocations={offset: (name, value), len(body): (name, value)})
        # The caller span must be the complete mapped span, overlapping no other indexed span.
        with self.assertRaisesRegex(ValueError, "exact complete mapped span|exact mapped Thumb span"):
            self.prove(self.plain, data=body[:-4])
        entries = json.loads(mapping)
        entries.append({"rom": f"0x{A + 4:08X}", "end": f"0x{A + 8:08X}", "mode": "thumb"})
        with self.assertRaisesRegex(ValueError, "overlaps another span"):
            self.prove(self.plain, mapping=json.dumps(entries).encode())


class DataBufferScanTests(unittest.TestCase):
    def test_selection_and_field_whitelist(self):
        self.assertTrue(data_buffer.selected(f"* verification: `{data_buffer.SCHEMA}`"))
        self.assertTrue(data_buffer.selected(f"* verification: `{data_buffer.FUNCTION_SCHEMA}`"))
        self.assertTrue(data_buffer.selected("  * data buffer manifest: `{}`"))
        self.assertFalse(data_buffer.selected(f"* verification: `{evidence.STACK_BUFFER_SCHEMA}`"))
        self.assertNotIn(data_buffer.SCHEMA, data_buffer.FUNCTION_SCHEMA)
        self.assertEqual(len(set(data_buffer.FIELDS)), len(data_buffer.FIELDS))
        import owner_admission_profile as owner
        self.assertEqual(data_buffer.HARDWARE_WINDOW, owner.NUMERIC_HARDWARE)
        # Other schemas never route here, and a report carrying these fields never reaches them.
        self.assertFalse(report_fixtures.replay(
            f"* verification: `{evidence.STACK_BUFFER_SCHEMA}`\n* data buffer calls: x\n"
            "**MATCH - byte identical** - 4/4 bytes", ROOT, A))


if __name__ == "__main__":
    unittest.main(verbosity=2)
