"""The control-block volatile rules of kit #375 and #165, issued by match.py as a subprocess.

match.py writes a report as `__main__`, a second copy of the module beside the
`import match` the profiles and the in-process tests use.  Each rule here runs
once through that path on a synthetic tree whose ROM is built from the compile,
and the report must say MATCH and carry the rule's record:

- U: a whole-object copy of the block through a void pointer;
- R1: a spill reload inside a read-modify-write window;
- N and R4: `bldy_lo--; if (bldy_lo == 0)`;
- P: one typed pointer to the block;
- T: a typed copy saved by the compiler's memcpy under the copy80 route, issued and then replayed
  through match_evidence.report_matches (status.py --verify's owner pre-check);
- R2: `bldcnt_lo |= 0xff`;
- Z: a reviewed ordinary-RAM object (a tools copy with a test entry).
"""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
sys.path.insert(0, str(ROOT / "tests"))
import plausible
import test_data_buffer_calls as calls
import test_volatile_semantics as fixtures

SYMBOL = "g_control_flags_03000940"
OBJECTS = {SYMBOL: "0x03000940"}
PROLOGUE = '#include "control_flags.h"\ntypedef unsigned int u32;\n'


SPILL = r'''

typedef struct {
    u32 unknown_00;
    u32 unknown_04;
    u32 unknown_08;
    u8 unknown_0C;
    u8 unknown_0D;
    u8 unknown_0E[2];
    void *tiles;
    void *map;
} Layer;

typedef void (*Initializer)(void *destination, u32 size);

extern u8 *data_0200F3B0;
extern u16 data_03003860[0x200];
extern Layer data_03000E60;
extern Layer data_03000990;
extern Layer data_030008B0;
extern u8 data_06008000[];
extern u8 data_06007000[];
extern u8 data_06004C00[];
extern u8 data_06005800[];
extern u8 data_06005000[];
extern Initializer const g_callbacks_0836D4B8[];

extern void func_08000A00(const void *source, void *destination, u32 control);
extern void func_08000B00(void *, u16);
extern void func_08000C00(void *destination, u32 size,
                          Initializer callback);

void func_08000200(void)
{
    u32 zero;
    Initializer const *callbacks;

    zero = 0;
    func_08000A00(&zero, (void *)0x06000000, 0x01006000);

    g_control_flags_03000940.bg0hofs = 0;
    g_control_flags_03000940.bg0vofs = g_control_flags_03000940.bg0hofs;
    g_control_flags_03000940.bg1hofs = 0;
    g_control_flags_03000940.bg1vofs = g_control_flags_03000940.bg1hofs;
    g_control_flags_03000940.bg2hofs = 0;
    g_control_flags_03000940.bg2vofs = g_control_flags_03000940.bg2hofs;
    g_control_flags_03000940.bg3hofs = 0;
    g_control_flags_03000940.bg3vofs = g_control_flags_03000940.bg3hofs;
    g_control_flags_03000940.bg0cnt = 0x8E8A;
    g_control_flags_03000940.bg3cnt = 0x0B01;
    g_control_flags_03000940.bg2cnt = 0x0A00;
    g_control_flags_03000940.bldcnt_lo = 0x40;
    g_control_flags_03000940.bldcnt_hi = 0x29;
    g_control_flags_03000940.bldalpha_lo = 0x10;
    g_control_flags_03000940.bldalpha_hi = 0;
    g_control_flags_03000940.bldy_lo = 0x10;
    g_control_flags_03000940.winout_lo = 0x3C;
    g_control_flags_03000940.winout_hi = 0;
    g_control_flags_03000940.winin_lo = 0x37;
    g_control_flags_03000940.winin_hi = 0;
    g_control_flags_03000940.win0h_hi = 0;
    g_control_flags_03000940.win0h_lo = 0;
    g_control_flags_03000940.win0v_hi = 0;
    g_control_flags_03000940.win0v_lo = 0;
    g_control_flags_03000940.win1h_lo = 0;
    g_control_flags_03000940.win1h_hi = 0;
    g_control_flags_03000940.win1v_lo = 0;
    g_control_flags_03000940.win1v_hi = 0;
    g_control_flags_03000940.display = 0x1940;

    data_03000E60.tiles = data_06008000;
    data_03000E60.map = data_06007000;
    data_03000E60.unknown_08 = 0;
    data_03000E60.unknown_04 = 0;
    data_03000E60.unknown_0C = 0x20;
    data_03000E60.unknown_0D = 0x40;
    data_03000990.tiles = data_06004C00;
    data_03000990.map = data_06005800;
    data_03000990.unknown_08 = 0;
    data_03000990.unknown_04 = 0;
    data_03000990.unknown_0D = 0x20;
    data_03000990.unknown_0C = 0x20;
    data_030008B0.tiles = (void *)0x06000000;
    data_030008B0.map = data_06005000;
    data_030008B0.unknown_08 = 0;
    data_030008B0.unknown_04 = 0;
    data_030008B0.unknown_0D = 0x20;
    data_030008B0.unknown_0C = 0x20;
    *(u16 *)(data_0200F3B0 + 0x8DD6) = 0;

    func_08000B00(data_06004C00, 1);
    callbacks = g_callbacks_0836D4B8;
    func_08000C00(data_03000E60.map, 0x800, callbacks[0]);
    func_08000C00(data_030008B0.map, 0x800, callbacks[0]);
    func_08000C00(data_03000990.map, 0x800, callbacks[0]);
}
'''
SPILL_OBJECTS = dict(OBJECTS, data_0200F3B0="0x0200F3B0", data_03003860="0x03003860", data_03000E60="0x03000E60",
                     data_03000990="0x03000990", data_030008B0="0x030008B0", data_06008000="0x06008000",
                     data_06007000="0x06007000", data_06004C00="0x06004C00", data_06005800="0x06005800",
                     data_06005000="0x06005000", g_callbacks_0836D4B8="0x02000300")


def tree(root, source, callees=(("func_08000400", "bx lr"),), objects=OBJECTS, callee_base=None):
    """calls.build() with the allowlisted header in place first (callees from callee_base, if given)"""
    root = Path(root)
    if callee_base is not None:
        saved = calls.CALLEES
        calls.CALLEES = callee_base
        try:
            return tree(root, source, callees, objects)
        finally:
            calls.CALLEES = saved
    (root / "include").mkdir(parents=True, exist_ok=True)
    entry = plausible.volatile_allow_entries()[0]
    (root / entry["header"]).write_text(fixtures.HEADER.format(declaration=entry["declaration"].replace("; ", ";\n    ")))
    return calls.build(root, PROLOGUE + source, list(callees), objects=objects)


COPY80 = "named-data-buffer-compiler-copy80-binding-v1"
TYPED_COPY = PROLOGUE + """typedef struct { unsigned char unknown_00[0x64]; __typeof__(""" + SYMBOL + """) control; } State;
extern void func_08000600(unsigned char *bytes);
unsigned int func_08000200(unsigned int a, unsigned int b, State *state)
{
    unsigned char bytes[4];

    state->control = """ + SYMBOL + """;
    bytes[0] = a;
    func_08000600(bytes);
    return bytes[0] + state->control.bldcnt_lo;
}
"""


def copy80_tree(root, source=TYPED_COPY):
    """the copy80 route's tree: the canonical copy helper at 0x08000400 (the kit's own fixture),
    the function, which calls the compiler's memcpy, and a compiled leaf at 0x08000600"""
    import argparse
    import struct
    import match
    import owner_admission_profile as owner
    from test_local_shadow_halfword_matrix import fixture as helper_fixture
    root = Path(root)
    for name in ("src", "include", "config", "symbols", "build"):
        (root / name).mkdir(parents=True, exist_ok=True)
    entry = plausible.volatile_allow_entries()[0]
    (root / entry["header"]).write_text(fixtures.HEADER.format(declaration=entry["declaration"].replace("; ", ";\n    ")))
    (root / "src/08000200.c").write_text(source)
    (root / "src/08000600.c").write_text("void func_08000600(unsigned char *bytes) { bytes[0] += 3; }\n")
    args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                              objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
    runner = match.Runner(match.DEFAULT_CC, "Ubuntu", match.DEFAULT_WSL_PATH, root=root)
    with runner.workspace() as workspace:
        _, leaf, _ = match.compile_object(runner, workspace, args, root, 0x08000600, "src/08000600.c")
        _, body, image = match.compile_object(runner, workspace, args, root, 0x08000200, "src/08000200.c")
    environment = helper_fixture()
    rows = json.loads(environment["mapping"])
    rows[0].update(end=f"0x{0x08000200 + len(body):08X}", instrs=0)
    rows.append(dict(rom="0x08000600", end=f"0x{0x08000600 + len(leaf):08X}", mode="thumb", instrs=0))
    mapping = json.dumps(rows).encode()
    # the linked bytes from the object's own relocations: memcpy to the helper, the leaf, the block's address
    data = bytearray(body)
    for section_id in image["relocations"]:
        section = image["sections"][section_id]
        symbols = image["symbol_tables"][section[6]]
        raw = image["section_data"][section_id]
        for position in range(0, len(raw), 8):
            site, info = struct.unpack_from("<II", raw, position)
            symbol = symbols[info >> 8]
            if info & 255 == 10:
                target = environment["helper"] if symbol["name"] == "memcpy" else 0x08000600
                delta = target - (0x08000200 + site) - 4
                struct.pack_into("<HH", data, site, 0xF000 | ((delta >> 12) & 2047), 0xF800 | ((delta >> 1) & 2047))
            elif info & 255 == 2:
                struct.pack_into("<I", data, site, int(OBJECTS[symbol["name"]], 16))
            else:
                raise AssertionError(info)
    rom = bytearray(environment["rom"])
    rom[0x08000200 - 0x08000000:0x08000200 - 0x08000000 + len(data)] = data
    rom.extend(bytes(max(0, 0x08000600 - 0x08000000 + len(leaf) - len(rom))))
    rom[0x08000600 - 0x08000000:0x08000600 - 0x08000000 + len(leaf)] = leaf
    rows[0]["instrs"] = owner.refine(bytes(data), 0x08000200, mapping)["instrs"]
    rows[2]["instrs"] = owner.refine(leaf, 0x08000600, mapping)["instrs"]
    mapping = json.dumps(rows).encode()
    (root / "config/functions.json").write_bytes(mapping)
    (root / "config/data_symbols.json").write_text(json.dumps(OBJECTS))
    (root / "symbols/functions.txt").write_text("".join(
        f"{int(row['rom'], 16):08X} {int(row['end'], 16):08X} {int(row['end'], 16) - int(row['rom'], 16)} "
        f"{row['instrs']} bx\n" for row in rows))
    (root / "baserom.bin").write_bytes(bytes(rom))
    return root


def issued(test, root, *options, tools=None):
    """match.py as a subprocess: the report, which must say MATCH"""
    report = Path(root) / "docs/match/08000200.md"
    if report.exists():
        report.unlink()
    script = Path(tools or ROOT / "tools") / "match.py"
    environment = dict(os.environ, FFTA_ROM=str(Path(root) / "baserom.bin"), PYTHONDONTWRITEBYTECODE="1")
    result = subprocess.run([sys.executable, str(script), "--root", str(root), "0x08000200", *options],
                            capture_output=True, text=True, env=environment, timeout=900)
    output = result.stdout + result.stderr
    test.assertEqual(result.returncode, 0, output[-3000:])
    test.assertIn("MATCH - byte identical", output)
    test.assertTrue(report.exists(), output[-2000:])
    return report.read_text()


REPLAY = """import sys
from pathlib import Path
sys.path.insert(0, sys.argv[1])
import match_evidence
root = Path(sys.argv[2])
print("replay", match_evidence.report_matches((root / "docs/match/08000200.md").read_text(), root, 0x08000200))
"""


def replayed(test, root, tools=None):
    """match_evidence.report_matches on the saved report, in a fresh interpreter, as status.py --verify's
    owner pre-check runs it: True or False"""
    environment = dict(os.environ, FFTA_ROM=str(Path(root) / "baserom.bin"), PYTHONDONTWRITEBYTECODE="1")
    result = subprocess.run([sys.executable, "-c", REPLAY, str(Path(tools or ROOT / "tools")), str(root)],
                            capture_output=True, text=True, env=environment, timeout=900)
    output = result.stdout + result.stderr
    test.assertEqual(result.returncode, 0, output[-3000:])
    verdicts = [line for line in result.stdout.splitlines() if line.startswith("replay ")]
    test.assertEqual(len(verdicts), 1, output[-3000:])
    return verdicts[0] == "replay True"


@unittest.skipUnless(calls.tools_present(), "fixed compiler and ARM tools required")
class IssuanceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix="volatile_issuance_", dir=scratch)
        cls.base = Path(cls.temporary.name)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def test_u_whole_object_copy(self):
        root = tree(self.base / "u", "extern void *func_08000400(void *destination, const void *source, u32 size);\n"
                    "void func_08000200(void *saved)\n{\n"
                    "    func_08000400(saved, &" + SYMBOL + ", sizeof " + SYMBOL + ");\n"
                    "    " + SYMBOL + ".bldcnt_lo = 0;\n}\n")
        report = issued(self, root)
        self.assertIn("whole-object arguments (kit#375): `&" + SYMBOL + "` (+0x0) as the void-pointer argument 2 of "
                      "func_08000400 at instruction ", report)
        self.assertIn("with the object's size 0x50 in argument 3; what the callee does with them is not checked",
                      report)

    def test_r1_spill_reload(self):
        # 0813F22C's tail: the zero it stores to the scroll members is spilled across the fill and
        # reloaded inside the read-modify-write window (`ldr r3, [sp, #k]` before the strh)
        root = tree(self.base / "r1", SPILL, callees=tuple((f"func_0800{n}00", "bx lr") for n in "ABC"),
                    objects=SPILL_OBJECTS, callee_base=0x08000A00)
        report = issued(self, root)
        self.assertIn("read-modify-write windows holding a spill reload (kit#165) at [", report)

    def test_n_and_r4_increment_test(self):
        # 08057578's `bldy_lo++; if (bldy_lo == 9)`: the stripped compile narrows the sum by
        # `lsl #24; lsr #24` (rule N) where the real one re-reads the member (rule R4)
        root = tree(self.base / "r4", "extern void func_08000400(void);\nvoid func_08000200(void)\n{\n"
                    "    " + SYMBOL + ".bldy_lo++;\n    if (" + SYMBOL + ".bldy_lo == 9)\n"
                    "        func_08000400();\n}\n")
        report = issued(self, root)
        self.assertIn("stored-value test re-reads (kit#375) at [", report)
        self.assertIn("stored-value test lists) under premise: ", report)

    def test_p_typed_pointer(self):
        root = tree(self.base / "p", "extern void *func_08000400(void *destination, const void *source, u32 size);\n"
                    "void func_08000200(void *saved)\n{\n"
                    "    __typeof__(" + SYMBOL + ") *control;\n\n"
                    "    control = &" + SYMBOL + ";\n    func_08000400(saved, control, 0x50);\n"
                    "    control->display |= 0xC00;\n}\n")
        report = issued(self, root)
        self.assertIn("as the void-pointer argument 2 of func_08000400", report)

    def test_t_typed_copy_under_copy80(self):
        root = copy80_tree(self.base / "t")
        report = issued(self, root, "--owner-runtime-profile", COPY80)
        self.assertIn("typed copies (kit#375): `" + SYMBOL + "` saved to ", report)
        self.assertIn("bound to func_08000400 by " + COPY80 + "; premise: the copy at", report)
        # the saved report replays: the replay takes the copy80 route too, so memcpy is typed as at issuance
        self.assertTrue(replayed(self, root))

    def test_z_reviewed_ram(self):
        # a tools copy whose volatile_objects.json holds a reviewed entry for this fixture's function
        import hashlib
        import volatile_rom_proof as proof
        source = ("extern volatile u16 data_03000100;\nextern void func_08000400(void);\n"
                  "void func_08000200(void)\n{\n    if (data_03000100 == 0xFFFF)\n        return;\n"
                  "    if (data_03000100 == 0xFFFE)\n        func_08000400();\n}\n")
        root = tree(self.base / "z", source, objects=dict(OBJECTS, data_03000100="0x03000100"))
        start, end = [int(word, 16) for word in (root / "symbols/functions.txt").read_text().split()[:2]]
        rom = (root / "baserom.bin").read_bytes()
        decoder, loads, at = proof.thumb_decoder(), [], start
        while at < end:
            decoded = list(decoder.disasm(rom[at - 0x08000000:at - 0x08000000 + 4], at, count=1))
            if decoded and decoded[0].mnemonic == "ldrh":
                loads.append(at)
            at += decoded[0].size if decoded else 2
        self.assertEqual(len(loads), 2, loads)
        kit = self.base / "z-kit"
        shutil.copytree(ROOT / "tools", kit / "tools", ignore=shutil.ignore_patterns("__pycache__"))
        for name in ROOT.glob("*.json"):
            shutil.copy(name, kit / name.name)
        objects = json.loads((kit / "tools/volatile_objects.json").read_text())
        objects["entries"].append({
            "symbol": "data_03000100", "address": "0x03000100", "size": 2, "kind": "reviewed-ram",
            "functions": ["0x08000200"], "start": f"0x{start:08X}", "end": f"0x{end:08X}",
            "sha256": hashlib.sha256(rom[start - 0x08000000:end - 0x08000000]).hexdigest(),
            "reloads": [[f"0x{loads[1]:08X}", f"0x{loads[0]:08X}"]], "ruling": "a test ruling",
            "unproved": "no other writer", "reason": "a test entry"})
        (kit / "tools/volatile_objects.json").write_text(json.dumps(objects, indent=2) + "\n")
        report = issued(self, root, tools=kit / "tools")
        self.assertIn("data_03000100 is ordinary RAM admitted case by case for 08000200 by a reviewed "
                      "volatile_objects.json entry (a test ruling); unproved: no other writer", report)
        self.assertIn(f"reviewed reloads of data_03000100 that the non-volatile build drops or merges: "
                      f"{loads[1]:08X} after {loads[0]:08X}", report)
        # and the shipped tools, which list no such entry, refuse it
        result = subprocess.run([sys.executable, str(ROOT / "tools/match.py"), "--root", str(root), "--no-write",
                                 "0x08000200"], capture_output=True, text=True, timeout=900,
                                env=dict(os.environ, FFTA_ROM=str(root / "baserom.bin"), PYTHONDONTWRITEBYTECODE="1"))
        self.assertNotIn("MATCH - byte identical", result.stdout)

    def test_r2_all_ones_or(self):
        root = tree(self.base / "r2", "void func_08000200(void)\n{\n    " + SYMBOL + ".bldcnt_lo |= 0xff;\n"
                    "    " + SYMBOL + ".bldcnt_hi = 0;\n}\n", callees=(("func_08000400", "bx lr"),))
        report = issued(self, root)
        self.assertIn("all-ones `|=` operand reads (kit#165): instruction ", report)


if __name__ == "__main__":
    unittest.main()
