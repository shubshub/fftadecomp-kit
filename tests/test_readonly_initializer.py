"""Compiler read-only initialisers bound on the default path (readonly_initializer_profile).

Natural C callers with a constant local initialiser are compiled with the fixed agbcc and
`-mthumb-interwork -O2`, linked at 0x08000200 with their `.rodata` at TABLE, beside an assembled callee and the
pinned copy helper, and run through match.py on the default path; the reports are replayed by report_matches.
The refusals change one input (a ROM byte, a literal word, the helper, the source) and name the guard.
"""
import argparse
import hashlib
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
sys.path.insert(0, str(ROOT / "tests"))
import match
import match_evidence as evidence
import data_buffer_profile as data_buffer
import readonly_initializer_profile as readonly
import rom_table_copy_profile as rom_copy
import test_data_buffer_calls as data_calls
from test_copy_helper_summary import BODY, HELPER, ROM_SIZE

A, CALLEES, BASE = data_calls.A, data_calls.CALLEES, match.ROM_BASE
TABLE = 0x08001000
OBJECTS = data_calls.OBJECTS
HEADER = data_calls.HEADER
WORD_STORES = "str r0, [r1]\nstr r0, [r1, #4]\nbx lr"

# 08105930's shape: a u16[4] initialiser, which agbcc copies with the compiler's memcpy, handed to a callee.
COPIED = HEADER + """extern void func_08000400(u16 value, u16 *out);
void func_08000200(u16 value)
{
    u16 ticks[4] = {58, 82, 270, 270};

    func_08000400(value, ticks);
    data_02000000[0] = ticks[0];
    data_02000000[1] = ticks[3];
}
"""
# A two-word initialiser, which agbcc copies inline with word loads and stores (0811BB08's shape; a
# three-word one is an ldm/stm block copy, whose stm through a local alias the buffer walk refuses).
WORDS = HEADER + """extern void func_08000400(u32 value, u32 *out);
void func_08000200(u32 value)
{
    u32 steps[2] = {0x11223344, 0x55667788};

    func_08000400(value, steps);
    data_02000000[0] = steps[0];
    data_02000000[1] = steps[1];
}
"""
# Two initialisers: two owner literal words into one section.
TWO = HEADER + """extern void func_08000400(u16 value, u16 *out);
void func_08000200(u16 value)
{
    u16 ticks[4] = {58, 82, 270, 270};
    u16 marks[4] = {1, 2, 3, 4};

    func_08000400(value, ticks);
    func_08000400(value, marks);
    data_02000000[0] = ticks[0];
    data_02000000[1] = marks[3];
}
"""
# A packed struct assignment: agbcc copies it with the compiler's memcpy and emits no `.rodata`
# (0x0800620C's 16-byte records, 0x08005EF8's 12-byte ones).
STRUCT_COPY = """typedef unsigned char u8;
typedef unsigned short u16;
typedef unsigned int u32;
typedef struct __attribute__((packed)) Record {
    u32 first;
    u16 second;
    u8 third;
    u8 fourth;
} Record;
extern Record data_02000000[];
extern void func_08000400(u16 value, Record *out);
void func_08000200(u16 value)
{
    Record copy;

    copy = data_02000000[1];
    func_08000400(value, &copy);
    data_02000000[0].second = copy.second;
}
"""
# The struct copy's callee writes two halfwords and leaves no frame address in R1 at its return.
STRUCT_STORES = "strh r0, [r1]\nstrh r0, [r1, #6]\nmovs r1, #0\nbx lr"
# No typed object: the plain stack-buffer route, which carries no binding.
PLAIN = """typedef unsigned short u16;
extern void func_08000400(u16 value, u16 *out);
u16 func_08000200(u16 value)
{
    u16 ticks[4] = {58, 82, 270, 270};

    func_08000400(value, ticks);
    return ticks[0] + ticks[3];
}
"""
# A pointer initialiser: its `.rodata` carries relocations.
POINTERS = HEADER + """extern void func_08000400(u16 value, u16 **out);
void func_08000200(u16 value)
{
    u16 *targets[4] = {data_02000000, data_02000000 + 4, data_02000000 + 8, data_02000000 + 12};

    func_08000400(value, targets);
}
"""
# A static local: a second allocated section.
STATIC = HEADER + """extern void func_08000400(u16 value, u16 *out);
void func_08000200(u16 value)
{
    static u16 count;
    u16 ticks[4] = {58, 82, 270, 270};

    func_08000400(value + count++, ticks);
    data_02000000[0] = ticks[0];
}
"""


def arguments():
    return argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                              objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)


def compiled(root, workspace, runner):
    _, _, original = match.compile_object(runner, workspace, arguments(), root, A, "src/08000200.c")
    return original


def targets_of(original):
    """Every undefined symbol of the caller, at the address the ROM fixture gives it."""
    objects = {name: int(value, 16) for name, value in OBJECTS.items()}
    targets = {}
    for item in original["symbols"]:
        if item["name"] and not item["section"]:
            name = item["name"]
            targets[name] = HELPER if name == "memcpy" else objects[name] if name in objects else int(name[5:], 16)
    return targets


def build(root, source, callee=data_calls.STORES, table=TABLE):
    """A complete tree: the caller and its `.rodata` (at `table`), the callee, the pinned helper."""
    root = Path(root)
    for name in ("src", "include", "config", "symbols", "build"):
        (root / name).mkdir(parents=True, exist_ok=True)
    work = root / "build"
    (work / "callee.s").write_text(".syntax unified\n.arch armv4t\n.thumb\n.text\n"
                                   ".global func_08000400, func_08000400_end\n"
                                   f"func_08000400:\n{callee}\nfunc_08000400_end:\n")
    for command in (
            [match.DEFAULT_AS, "-mthumb-interwork", str(work / "callee.s"), "-o", str(work / "callee.o")],
            [match.DEFAULT_LD, f"-Ttext=0x{CALLEES:08X}", "-e", "func_08000400", str(work / "callee.o"),
             "-o", str(work / "callee.elf")],
            [match.DEFAULT_OBJCOPY, "-O", "binary", "--only-section=.text", str(work / "callee.elf"),
             str(work / "callee.bin")]):
        subprocess.run(command, check=True, capture_output=True)
    code = (work / "callee.bin").read_bytes()
    rom = bytearray(ROM_SIZE)
    rom[CALLEES - BASE:CALLEES - BASE + len(code)] = code
    rom[HELPER - BASE:HELPER - BASE + len(BODY)] = BODY
    (root / "src/08000200.c").write_text(source)
    (root / "include/types.h").write_text("/* fixture */\n")
    (root / "config/data_symbols.json").write_text(json.dumps(OBJECTS))
    runner = match.Runner(match.DEFAULT_CC, root=root, wsl_path=match.DEFAULT_WSL_PATH, timeout=120)
    with runner.workspace() as workspace:
        original = compiled(root, workspace, runner)
        symbol, _ = match.function_record(original, "func_08000200", A, True)
        section = rom_copy.rodata_section(original)
        targets = targets_of(original)
        linked = match.link_typed_targets(runner, workspace, arguments(), "func_08000200", A, targets,
                                          set(OBJECTS) & set(targets), readonly_initializer={"base": table})
    body = linked["text"][:symbol["size"]]
    rom[A - BASE:A - BASE + len(body)] = body
    if section is not None:
        rom[table - BASE:table - BASE + len(section[1])] = section[1]
    rows = [(A, len(body), 0), (CALLEES, len(code), 0), (HELPER, len(BODY), 49)]
    (root / "config/functions.json").write_text(json.dumps(
        [dict(rom=f"0x{a:08X}", end=f"0x{a + n:08X}", mode="thumb", **({"instrs": c} if c else {}))
         for a, n, c in rows]))
    (root / "symbols/functions.txt").write_text("".join(f"{a:08X} {a + n:08X} {n} {c} return\n" for a, n, c in rows))
    (root / "baserom.bin").write_bytes(bytes(rom))
    return root


def sites(root):
    """The owner's literal words into `.rodata`: [[offset, addend]] from a fresh compile."""
    runner = match.Runner(match.DEFAULT_CC, root=root, wsl_path=match.DEFAULT_WSL_PATH, timeout=120)
    with runner.workspace() as workspace:
        original = compiled(root, workspace, runner)
    found = []
    for number in original["relocations"]:
        table = original["sections"][number]
        symbols = original["symbol_tables"][table[6]]
        for position in range(0, table[5], 8):
            offset, info = struct.unpack_from("<II", original["section_data"][number], position)
            target = symbols[info >> 8]
            if info & 255 == 2 and target["type"] == 3 and \
                    original["section_names"][target["section"]] == ".rodata":
                found.append([offset, struct.unpack_from("<I", original["text"], offset)[0]])
    return sorted(found)


def patch_rom(root, changes):
    path = Path(root) / "baserom.bin"
    rom = bytearray(path.read_bytes())
    for address, raw in changes.items():
        rom[address - BASE:address - BASE + len(raw)] = raw
    path.write_bytes(bytes(rom))


def manifest(report):
    line = next(line for line in report.splitlines() if line.startswith(data_buffer.MANIFEST_FIELD))
    return json.loads(line[len(data_buffer.MANIFEST_FIELD) + 1:-1])


class UnitTests(unittest.TestCase):
    def test_only_an_empty_collection_opts_in(self):
        self.assertFalse(readonly.opted_in(None))
        self.assertTrue(readonly.opted_in({}))
        for value in ({"base": 1}, [], ()):
            with self.subTest(value=value), self.assertRaisesRegex(ValueError, "requires an empty collection"):
                readonly.opted_in(value)

    def test_a_site_must_be_a_complete_aligned_unshared_literal_word(self):
        rodata = (5, b"\x01\x02\x03\x04\x05\x06\x07\x08", 4)
        symbol = dict(section=5, type=3, bind=0, value=0, name="")
        image = dict(text=struct.pack("<4I", 0, 4, 0, 9))
        self.assertIsNone(readonly.site(None, symbol, image, 4, 16, A, set()))
        self.assertIsNone(readonly.site(rodata, dict(symbol, section=6), image, 4, 16, A, set()))
        self.assertEqual(readonly.site(rodata, symbol, image, 4, 16, A, set()), 4)
        for name, relocation, size, occupied, edited, message in (
                ("misaligned", 2, 16, set(), symbol, "aligned complete literal word"),
                ("past the function", 12, 14, set(), symbol, "aligned complete literal word"),
                ("shared", 4, 16, {5}, symbol, "overlapping"),
                ("named symbol", 4, 16, set(), dict(symbol, name="table"), "local section symbol"),
                ("global symbol", 4, 16, set(), dict(symbol, bind=1), "local section symbol"),
                ("addend outside", 12, 16, set(), symbol, "addend outside")):
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, message):
                readonly.site(rodata, edited, image, relocation, size, A, set(occupied))

    def test_the_report_line_prints_base_size_and_digest(self):
        line = readonly.report_line(dict(base=TABLE, size=8, sha256="ab" * 32, sites=[[44, 0], [48, 8]]))
        self.assertEqual(line, "* read-only initialiser: `.rodata` 8 bytes at 0x08001000, SHA-256 `" + "ab" * 32 +
                         "`, addressed by the owner's literal words at +0x2C, +0x30 (+8); accesses through "
                         "the literal (reads, writes, calls, escapes) get a named object's treatment, extent "
                         "not walked")


@unittest.skipUnless(data_calls.tools_present(), "fixed compiler and ARM tools required")
class NativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix="readonly_initializer_", dir=scratch)
        cls.base = Path(cls.temporary.name)
        cls.copied = build(cls.base / "copied", COPIED)
        cls.code, cls.output, cls.report = data_calls.run(cls.copied)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def replays(self, report, root):
        with patch.dict(os.environ, FFTA_ROM=str(Path(root) / "baserom.bin")):
            return evidence.report_matches(report, root, A)

    def refused(self, root, message):
        code, output, report = data_calls.run(root)
        self.assertNotEqual(code, 0, output)
        self.assertIsNone(report)
        self.assertRegex(output, message)

    def section_bytes(self, root):
        runner = match.Runner(match.DEFAULT_CC, root=root, wsl_path=match.DEFAULT_WSL_PATH, timeout=120)
        with runner.workspace() as workspace:
            return rom_copy.rodata_section(compiled(root, workspace, runner))[1]

    def test_memcpy_initialiser_is_admitted_with_its_binding(self):
        self.assertEqual(self.code, 0, self.output)
        self.assertIn("verdict MATCH - byte identical", self.output)
        self.assertEqual(data_calls.verification(self.report), data_buffer.SCHEMA)
        raw = self.section_bytes(self.copied)
        self.assertEqual(raw, struct.pack("<4H", 58, 82, 270, 270))
        record = manifest(self.report)[readonly.MANIFEST_KEY]
        self.assertEqual(record, dict(base=TABLE, size=8, sha256=hashlib.sha256(raw).hexdigest(),
                                      sites=sites(self.copied)))
        self.assertIn(f"func_{HELPER:08X}", [name for _, name in manifest(self.report)["calls"]])
        line, = [line for line in self.report.splitlines() if line.startswith(readonly.LINE)]
        self.assertEqual(line, readonly.report_line(record))
        self.assertIn(f"8 bytes at 0x{TABLE:08X}, SHA-256 `{record['sha256']}`", line)
        self.assertTrue(any(line.startswith("* buffer copy summary:") for line in self.report.splitlines()))
        self.assertTrue(self.replays(self.report, self.copied))

    def test_inline_initialiser_is_admitted_with_its_binding(self):
        root = build(self.base / "words", WORDS, WORD_STORES)
        code, output, report = data_calls.run(root)
        self.assertEqual(code, 0, output)
        record = manifest(report)[readonly.MANIFEST_KEY]
        self.assertEqual((record["base"], record["size"]), (TABLE, 8))
        self.assertNotIn(f"func_{HELPER:08X}", [name for _, name in manifest(report)["calls"]])
        self.assertTrue(self.replays(report, root))

    def test_tampered_or_stale_reports_fail_to_replay(self):
        lines = self.report.splitlines()
        record = manifest(self.report)[readonly.MANIFEST_KEY]
        at = next(index for index, line in enumerate(lines) if line.startswith(readonly.LINE))
        edits = {
            "line base": lines[:at] + [lines[at].replace(f"0x{TABLE:08X}", f"0x{TABLE + 4:08X}")] + lines[at + 1:],
            "line removed": lines[:at] + lines[at + 1:],
            "line duplicated": lines[:at + 1] + lines[at:],
            "manifest base": [line.replace(f'"base":{TABLE}', f'"base":{TABLE + 4}') for line in lines],
            "manifest digest": [line.replace(record["sha256"], "0" * 64) for line in lines],
        }
        for name, edited in edits.items():
            with self.subTest(name=name):
                self.assertNotEqual(edited, lines)
                self.assertFalse(self.replays("\n".join(edited) + "\n", self.copied))
        with self.subTest(name="ROM initialiser byte"):
            saved = (self.copied / "baserom.bin").read_bytes()
            try:
                patch_rom(self.copied, {TABLE + 1: bytes([saved[TABLE - BASE + 1] ^ 1])})
                self.assertFalse(self.replays(self.report, self.copied))
            finally:
                (self.copied / "baserom.bin").write_bytes(saved)

    def test_a_differing_rom_byte_refuses(self):
        root = build(self.base / "byte", COPIED)
        rom = (root / "baserom.bin").read_bytes()
        patch_rom(root, {TABLE + 3: bytes([rom[TABLE - BASE + 3] ^ 0x10])})
        self.refused(root, "ROM table bytes differ from the compiler initialiser bytes")

    def test_one_disagreeing_literal_word_refuses(self):
        root = build(self.base / "two", TWO)
        found = sites(root)
        self.assertEqual(len(found), 2, found)
        code, output, report = data_calls.run(root)
        self.assertEqual(code, 0, output)
        self.assertEqual(manifest(report)[readonly.MANIFEST_KEY]["sites"], found)
        (offset, addend), _ = found
        patch_rom(root, {A + offset: struct.pack("<I", TABLE + addend + 4)})
        self.refused(root, "owner literals disagree on the initialiser address")

    def test_a_base_outside_the_rom_image_refuses(self):
        root = build(self.base / "where", COPIED)
        (offset, addend), = sites(root)
        saved = (root / "baserom.bin").read_bytes()
        for name, base in (("EWRAM", 0x02000000), ("IWRAM", 0x03000000), ("ROM mirror", 0x0A000000 + TABLE - BASE),
                           ("crossing the ROM end", BASE + ROM_SIZE - 4), ("inside the owner", A),
                           ("misaligned", TABLE + 1)):
            with self.subTest(name=name):
                (root / "baserom.bin").write_bytes(saved)
                patch_rom(root, {A + offset: struct.pack("<I", base + addend)})
                self.refused(root, "initialiser address is misaligned, outside ROM or inside the owner")

    def test_a_changed_copy_helper_refuses_the_memcpy_binding(self):
        root = build(self.base / "helper", COPIED)
        rom = (root / "baserom.bin").read_bytes()
        patch_rom(root, {HELPER + 40: bytes([rom[HELPER - BASE + 40] ^ 1])})
        self.refused(root, "compiler memcpy requires the canonical pinned copy helper at 0x081443FC")

    def test_a_struct_copy_binds_memcpy_without_an_initialiser(self):
        root = build(self.base / "struct", STRUCT_COPY, STRUCT_STORES)
        runner = match.Runner(match.DEFAULT_CC, root=root, wsl_path=match.DEFAULT_WSL_PATH, timeout=120)
        with runner.workspace() as workspace:
            original = compiled(root, workspace, runner)
        self.assertIsNone(rom_copy.rodata_section(original))
        self.assertIn("memcpy", [item["name"] for item in original["symbols"] if not item["section"]])
        code, output, report = data_calls.run(root)
        self.assertEqual(code, 0, output)
        self.assertIn("verdict MATCH - byte identical", output)
        self.assertEqual(data_calls.verification(report), data_buffer.SCHEMA)
        found = manifest(report)
        self.assertNotIn(readonly.MANIFEST_KEY, found)
        self.assertIn(f"func_{HELPER:08X}", [name for _, name in found["calls"]])
        self.assertFalse(any(line.startswith(readonly.LINE) for line in report.splitlines()))
        self.assertTrue(self.replays(report, root))
        rom = (root / "baserom.bin").read_bytes()
        patch_rom(root, {HELPER + 40: bytes([rom[HELPER - BASE + 40] ^ 1])})
        self.assertFalse(self.replays(report, root))
        self.refused(root, "compiler memcpy requires the canonical pinned copy helper at 0x081443FC")

    def test_pointer_initialisers_and_second_sections_refuse(self):
        for name, source, message in (
                ("pointers", POINTERS, "read-only initialiser carries relocations"),
                ("static", STATIC, "unexpected nonempty allocated section")):
            with self.subTest(name=name):
                root = Path(self.base / name)
                for folder in ("src", "include", "config", "symbols", "build"):
                    (root / folder).mkdir(parents=True, exist_ok=True)
                for path in ("config/data_symbols.json", "config/functions.json", "symbols/functions.txt",
                             "baserom.bin", "include/types.h"):
                    (root / path).write_bytes((self.copied / path).read_bytes())
                (root / "src/08000200.c").write_text(source)
                self.refused(root, message)

    def test_the_plain_route_carries_no_binding_and_refuses(self):
        root = build(self.base / "plain", PLAIN)
        self.refused(root, "a read-only initialiser is admitted only with data-buffer evidence")

    def test_a_route_that_does_not_opt_in_keeps_the_text_only_refusal(self):
        runner = match.Runner(match.DEFAULT_CC, root=self.copied, wsl_path=match.DEFAULT_WSL_PATH, timeout=120)
        rom = (self.copied / "baserom.bin").read_bytes()
        mapping = (self.copied / "config/functions.json").read_bytes()
        objects = (self.copied / "config/data_symbols.json").read_bytes()
        with runner.workspace() as workspace:
            original = compiled(self.copied, workspace, runner)
            with self.assertRaisesRegex(ValueError, "unexpected nonempty allocated section"):
                match.link_calls(runner, workspace, arguments(), original, A, mapping, len(rom), rom, objects, {})
            binding = {}
            body, calls, _ = match.link_calls(runner, workspace, arguments(), original, A, mapping, len(rom), rom,
                                              objects, {}, readonly_initializer=binding)
        self.assertEqual(body, rom[A - BASE:A - BASE + len(body)])
        self.assertEqual(binding["base"], TABLE)
        self.assertIn(HELPER, calls.values())

    def test_the_linked_check_needs_the_bound_placement_and_words(self):
        runner = match.Runner(match.DEFAULT_CC, root=self.copied, wsl_path=match.DEFAULT_WSL_PATH, timeout=120)
        rom = (self.copied / "baserom.bin").read_bytes()
        record = manifest(self.report)[readonly.MANIFEST_KEY]
        with runner.workspace() as workspace:
            original = compiled(self.copied, workspace, runner)
            targets = targets_of(original)
            data_names = set(OBJECTS) & set(targets)
            linked = match.link_typed_targets(runner, workspace, arguments(), "func_08000200", A, targets,
                                              data_names, readonly_initializer=record)
            moved = match.link_typed_targets(runner, workspace, arguments(), "func_08000200", A, targets,
                                             data_names, readonly_initializer=dict(record, base=TABLE + 8))
        words = set()
        readonly.check_linked(linked, record, rom, words)
        self.assertEqual(words, {offset + n for offset, _ in record["sites"] for n in range(4)})
        with self.assertRaisesRegex(ValueError, "linked read-only section differs from the bound initialiser"):
            readonly.check_linked(moved, record, rom, set())
        shifted = dict(record, sites=[[offset, addend + 2] for offset, addend in record["sites"]])
        with self.assertRaisesRegex(ValueError, "linked read-only initialiser word does not equal its bound address"):
            readonly.check_linked(linked, shifted, rom, set())

    def test_the_data_proof_types_only_reached_words_holding_the_bound_address(self):
        rom = (self.copied / "baserom.bin").read_bytes()
        mapping = (self.copied / "config/functions.json").read_bytes()
        objects = (self.copied / "config/data_symbols.json").read_bytes()
        index = (self.copied / "symbols/functions.txt").read_bytes()
        data = bytes.fromhex(next(line for line in self.report.splitlines()
                                  if line.startswith("* compiled : "))[len("* compiled : `"):-1])
        found = manifest(self.report)
        calls = {A + offset: int(name[5:], 16) for offset, name in found["calls"]}
        symbols = match.parse_data_symbols(objects)
        literals = {offset: (name, symbols[name] + delta) for offset, name, delta in found["data"]}
        record = found[readonly.MANIFEST_KEY]
        _, _, schema, proved = data_buffer.prove(data, A, rom, mapping, objects, calls, literals, index=index,
                                                 readonly_initializer=record)
        self.assertEqual((schema, proved), (data_buffer.SCHEMA, found))
        with self.assertRaisesRegex(ValueError, "untyped word"):
            data_buffer.prove(data, A, rom, mapping, objects, calls, literals, index=index)
        (offset, addend), = record["sites"]
        for name, edited in (("other address", dict(record, base=TABLE + 4)),
                             ("unreached word", dict(record, sites=[[offset + 4, addend]]))):
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, "not a reached word holding"):
                data_buffer.prove(data, A, rom, mapping, objects, calls, literals, index=index,
                                  readonly_initializer=edited)


if __name__ == "__main__":
    unittest.main()
