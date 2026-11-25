"""The SDK's BIOS fill temporary (tools/bios_fill_temporary.py, kit issue 164)."""
from collections import Counter
import os
from pathlib import Path
import shutil
import struct
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import bios_fill_temporary as fill
import plausible
import volatile_rom_proof as proof

try:
    import capstone
except ImportError:
    capstone = None

CPUSET = "extern void func_0814186C(const void *source, void *destination, unsigned int control);\n"
FASTSET = "extern void func_08141868(const void *source, void *destination, unsigned int control);\n"
TYPES = "typedef unsigned char u8;\ntypedef unsigned short u16;\ntypedef unsigned int u32;\n"
BLOCK = "void func_08000400(u16 *dest) {\n    {\n        volatile u16 tmp = 0;\n" \
        "        func_0814186C((const void *)&tmp, dest, 0x01000100);\n    }\n}\n"
MACRO = ("#define CpuFill16(value, dest, size)                \\\n"
         "{                                                   \\\n"
         "    volatile u16 tmp = (volatile u16)(value);       \\\n"
         "    func_0814186C((void *)&tmp, (dest),             \\\n"
         "        0x01000000 | ((size) / (16 / 8) & 0x1FFFFF)); \\\n"
         "}\n"
         "void func_08000400(u16 *dest) { CpuFill16(0, dest, 0x40); CpuFill16(0, dest + 0x20, 0x40); }\n")
FAST = ("#define CpuFastFill(value, dest, size)              \\\n"
        "{                                                   \\\n"
        "    volatile u32 tmp = (volatile u32)(value);       \\\n"
        "    func_08141868((void *)&tmp, (dest),             \\\n"
        "        0x01000000 | ((size) / (32 / 8) & 0x1FFFFF)); \\\n"
        "}\n"
        "extern void func_08001000(u32 *out);\n"
        "void func_08000400(u32 *dest) {\n    u32 out;\n    func_08001000(&out);\n"
        "    CpuFastFill(0, dest, 0x80);\n    CpuFastFill(out, dest + 0x40, 0x20);\n}\n")


def groups(source):
    return [(g["kind"], g["name"], g["type"], g["temporary"], [source[o:o + 8] for o in g["offsets"]],
             g["line"]) for g in fill.fill_groups(source)]


class SourceTests(unittest.TestCase):
    def test_an_open_block_is_one_group(self):
        source = TYPES + CPUSET + BLOCK
        self.assertEqual(groups(source), [("block", None, "u16", "tmp", ["volatile"], 7)])
        for cast in ("(void *)&tmp", "&tmp"):
            with self.subTest(cast=cast):
                self.assertEqual(len(fill.fill_groups(source.replace("(const void *)&tmp", cast))), 1)
        word = source.replace("volatile u16 tmp = 0", "volatile u32 tmp = 0").replace("0x01000100", "0x05000040")
        self.assertEqual(groups(word)[0][2], "u32")

    def test_a_macro_body_is_one_group_with_both_tokens(self):
        source = TYPES + CPUSET + MACRO
        (found,) = fill.fill_groups(source)
        self.assertEqual((found["kind"], found["name"], found["temporary"]), ("macro", "CpuFill16", "tmp"))
        self.assertEqual([source[o:o + 8] for o in found["offsets"]], ["volatile", "volatile"])
        self.assertEqual(found["line"], 7)

    def test_a_cpufastset_fill_takes_a_word(self):
        (found,) = fill.fill_groups(TYPES + FASTSET + FAST)
        self.assertEqual((found["kind"], found["name"], found["type"], found["callee"]),
                         ("macro", "CpuFastFill", "u32", "func_08141868"))
        block = TYPES + CPUSET + BLOCK
        self.assertEqual(fill.fill_groups(block)[0]["callee"], "func_0814186C")
        word = block.replace("volatile u16 tmp = 0", "volatile u32 tmp = 0").replace(
            "func_0814186C((const", "func_08141868((const")
        (found,) = fill.fill_groups(word)
        self.assertEqual((found["type"], found["callee"]), ("u32", "func_08141868"))
        # CpuFastSet reads words only: a halfword temporary is no fill of it
        self.assertEqual(fill.fill_groups(word.replace("volatile u32 tmp", "volatile u16 tmp")), [])

    def test_shapes_that_are_no_fill(self):
        source = TYPES + CPUSET + BLOCK
        for label, old, new in (
                ("a statement after the call", "0x01000100);\n", "0x01000100);\n        *dest = tmp;\n"),
                ("the temporary read in the value", "tmp = 0;", "tmp = 0 + 0 * sizeof(tmp);"),
                ("the temporary passed without &", "(const void *)&tmp", "(const void *)tmp"),
                ("another callee", "func_0814186C((const", "func_08141868((const"),
                ("a byte temporary", "volatile u16 tmp", "volatile u8 tmp"),
                ("a static temporary", "volatile u16 tmp", "static volatile u16 tmp"),
                ("a pointer temporary", "volatile u16 tmp = 0", "volatile u16 *tmp = 0"),
                ("two declarators", "volatile u16 tmp = 0;", "volatile u16 tmp = 0, other = 0;"),
                ("the address in the destination", "dest, 0x01000100", "(u16 *)&tmp, 0x01000100")):
            with self.subTest(label=label):
                self.assertEqual(fill.fill_groups(source.replace(old, new)), [])
        macro = TYPES + CPUSET + MACRO
        for label, old, new in (
                ("a macro with another statement", "0x1FFFFF)); \\\n}", "0x1FFFFF)); (dest)[0] = 1; \\\n}"),
                ("a macro defined twice", "void func_08000400", "#undef CpuFill16\nvoid func_08000400"),
                ("an object-like macro", "#define CpuFill16(value, dest, size)", "#define CpuFill16")):
            with self.subTest(label=label):
                self.assertEqual(fill.fill_groups(macro.replace(old, new)), [])
        # a token a splice splits is not read
        split = macro.replace("volatile u16 tmp = (volatile u16)", "vola\\\ntile u16 tmp = (volatile u16)")
        self.assertEqual(fill.fill_groups(split), [])

    def test_joined_offsets_map_back(self):
        source = TYPES + CPUSET + MACRO
        joined, back = fill.joined_view(source)
        self.assertEqual(joined, plausible.join_splices(source))
        self.assertTrue(all(source[back[j]] == joined[j] for j in range(len(joined))))


def dump(name, insns):
    lines = [f"\n;; Function {name}\n"]
    for index, (uid, rest) in enumerate(insns):
        before = insns[index - 1][0] if index else 0
        after = insns[index + 1][0] if index + 1 < len(insns) else 0
        kind, _, body = rest.partition(" ")
        lines.append(f"({kind} {uid} {before} {after} {body})\n")
    return "\n".join(lines)


def function(insns, name="func_08000400"):
    return proof.Function(proof.parse_dump(dump(name, insns))[name])


def fill_insns(uid, offset=-2, control=0x01000100, mode="HI", store=True, frame_r0=True, dest="(reg/v:SI 22)",
               callee="func_0814186C"):
    """the expand RTL of one fill: the slot's address, the value, the volatile store and the BIOS call"""
    address = f"(plus:SI (reg:SI 18 virtual-stack-vars) (const_int {offset}))"
    out = [(uid, f"insn (set (reg:SI {uid + 100}) {address}) -1 (nil) (nil)"),
           (uid + 1, f"insn (set (reg:{mode} {uid + 101}) (const_int 0)) -1 (nil) (nil)")]
    if store:
        out.append((uid + 2, f"insn (set (mem/v/f:{mode} (reg:SI {uid + 100}) 0) (reg:{mode} {uid + 101})) "
                             "-1 (nil) (nil)"))
    source = f"(reg:SI {uid + 100})" if frame_r0 else '(symbol_ref:SI ("data_03000040"))'
    out += [(uid + 3, f"insn (set (reg:SI 0 r0) {source}) -1 (nil) (nil)"),
            (uid + 4, f"insn (set (reg:SI 1 r1) {dest}) -1 (nil) (nil)"),
            (uid + 5, f"insn (set (reg:SI 2 r2) (const_int {control})) -1 (nil) (nil)"),
            (uid + 6, f'call_insn (call (mem:SI (symbol_ref:SI ("{callee}")) 0) (const_int 0)) -1 (nil) '
                      '(nil) (expr_list (use (reg:SI 0 r0)) (nil))')]
    return out


ENTRY = (2, "insn (set (reg/v:SI 22) (reg:SI 0 r0)) -1 (nil) (nil)")


class RtlTests(unittest.TestCase):
    def test_a_fill_is_read_off_its_block(self):
        (found,) = fill.fills(function([ENTRY] + fill_insns(10)))
        self.assertEqual((found["slot"], found["width"], found["control"], found["call"].uid),
                         ((18, -2), 2, 0x01000100, 16))
        word = fill.fills(function([ENTRY] + fill_insns(10, offset=-4, control=0x05000040, mode="SI")))
        self.assertEqual(word[0]["width"], 4)

    def test_two_blocks_may_share_a_slot(self):
        insns = [ENTRY] + fill_insns(10, offset=-4) + [(30, 'code_label 31 ""')] + fill_insns(40, offset=-4)
        self.assertEqual([f["slot"] for f in fill.fills(function(insns))], [(18, -4), (18, -4)])

    def test_the_destination_must_miss_the_temporary(self):
        def frame(register, offset):
            return f"(plus:SI (reg:SI {register} virtual) (const_int {offset}))"
        # the slot is [-2, 0); four halfwords from -10 end at -2, five reach it
        below = fill.fills(function([ENTRY] + fill_insns(10, control=0x01000004, dest=frame(18, -10))))
        self.assertEqual(below[0]["slot"], (18, -2))
        for label, dest, control, reason in (
                ("the temporary itself", frame(18, -2), 0x01000100, "passes r1 an address that reaches"),
                ("an address inside it", frame(18, -1), 0x01000001, "passes r1 an address that reaches"),
                ("a fill that runs into it", frame(18, -10), 0x01000005, "passes r1 an address that reaches"),
                ("another frame register", frame(17, 0), 0x01000100, "passes r1 a frame address the proof cannot")):
            with self.subTest(label=label), self.assertRaisesRegex(proof.ProofError, reason):
                fill.fills(function([ENTRY] + fill_insns(10, control=control, dest=dest)))
        # r3, which CpuSet does not read, may hold another frame address but none in the slot
        for offset, reason in ((-4, None), (-2, "passes r3 an address that reaches")):
            insns = fill_insns(10)
            insns.insert(5, (30, f"insn (set (reg:SI 3 r3) {frame(18, offset)}) -1 (nil) (nil)"))
            with self.subTest(r3=offset):
                if reason is None:
                    self.assertEqual(len(fill.fills(function([ENTRY] + insns))), 1)
                else:
                    with self.assertRaisesRegex(proof.ProofError, reason):
                        fill.fills(function([ENTRY] + insns))

    def test_a_cpufastset_fill(self):
        fast = dict(offset=-4, mode="SI", callee="func_08141868")
        (found,) = fill.fills(function([ENTRY] + fill_insns(10, control=0x01000008, **fast)))
        self.assertEqual((found["slot"], found["width"], found["control"], found["callee"], found["store_uid"]),
                         ((18, -4), 4, 0x01000008, "func_08141868", 12))
        frame = "(plus:SI (reg:SI 18 virtual) (const_int -32))"
        # one word from -32 ends at -28 for CpuSet; CpuFastSet writes eight, to 0, over the slot at -4
        word = dict(offset=-4, mode="SI", dest=frame)
        self.assertEqual(len(fill.fills(function([ENTRY] + fill_insns(10, control=0x05000001, **word)))), 1)
        for label, insns, reason in (
                ("a halfword temporary", fill_insns(10, control=0x01000008, callee="func_08141868"),
                 "passes CpuFastSet a 2-byte temporary"),
                ("a unit bit", fill_insns(10, control=0x05000008, **fast), "a bit outside 0-20 and 24"),
                ("a bit above the count", fill_insns(10, control=0x01200008, **fast), "a bit outside 0-20 and 24"),
                ("no fixed-source bit", fill_insns(10, control=0x00000008, **fast), "without bit 24"),
                ("eight words over the slot", fill_insns(10, control=0x01000001, dest=frame, **fast),
                 "passes r1 an address that reaches")):
            with self.subTest(label=label), self.assertRaisesRegex(proof.ProofError, reason):
                fill.fills(function([ENTRY] + insns))
        self.assertEqual(fill.filled(0x01000001, 4, "func_08141868"), 32)
        self.assertEqual(fill.filled(0x01000009, 4, "func_08141868"), 64)
        self.assertEqual(fill.filled(0x01000009, 4), 36)

    def test_a_removal_keeps_only_stores_the_function_makes(self):
        a, b, moved = (18, -2, 2), (18, -4, 2), (18, -6, 2)
        self.assertEqual(fill.account([a, b], Counter([b]), 1, 5), Counter([a]))
        for label, left, reach in (("a store moved", Counter([b, moved]), 1),
                                   ("too few removed", Counter([a, b]), 1),
                                   ("too many removed", Counter(), 1)):
            with self.subTest(label=label), self.assertRaisesRegex(proof.ProofError, "line 5 does not account"):
                fill.account([a, b], left, reach, 5)

    def test_a_value_read_from_the_frame_is_no_frame_address(self):
        # a fifth argument, read from the incoming arguments and compared: its value addresses no slot
        argument = [(3, "insn (set (reg:SI 23) (mem/f:SI (reg:SI 17 virtual-incoming-args) 0)) -1 (nil) (nil)"),
                    (4, "insn (set (reg:SI 24) (plus:SI (reg:SI 23) (const_int 1))) -1 (nil) (nil)"),
                    (5, "insn (set (cc0) (compare (reg:SI 24) (reg/v:SI 22))) -1 (nil) (nil)")]
        (found,) = fill.fills(function([ENTRY] + argument + fill_insns(10)))
        self.assertEqual(found["slot"], (18, -2))

    def test_refusals(self):
        later_load = (30, "insn (set (reg:SI 60) (zero_extend:SI (mem/f:HI (plus:SI (reg:SI 18 virtual-stack-vars) "
                          "(const_int -2)) 0))) -1 (nil) (nil)")
        passed_before = [(5, "insn (set (reg:SI 0 r0) (plus:SI (reg:SI 18 virtual-stack-vars) (const_int -2))) "
                             "-1 (nil) (nil)"),
                         (6, 'call_insn (call (mem:SI (symbol_ref:SI ("func_08001000")) 0) (const_int 0)) -1 (nil) '
                             '(nil) (expr_list (use (reg:SI 0 r0)) (nil))')]
        unknown = (30, "insn (set (mem:SI (plus:SI (reg:SI 18 virtual-stack-vars) (reg/v:SI 22)) 0) "
                       "(const_int 0)) -1 (nil) (nil)")
        read_inside = (9, "insn (set (reg:SI 61) (zero_extend:SI (mem/v/f:HI (reg:SI 110) 0))) -1 (nil) (nil)")
        escape = (9, 'insn (set (mem:SI (symbol_ref:SI ("data_03000040")) 0) (reg:SI 110)) -1 (nil) (nil)')
        for label, insns, reason in (
                ("no fixed-source bit", [ENTRY] + fill_insns(10, control=0x00000100), "without bit 24"),
                ("word units for a halfword", [ENTRY] + fill_insns(10, control=0x05000100), "bit 26"),
                ("halfword units for a word", [ENTRY] + fill_insns(10, mode="SI", offset=-4), "bit 26"),
                ("r0 not the stack", [ENTRY] + fill_insns(10, frame_r0=False), "no fill"),
                ("the temporary read after the call", [ENTRY] + fill_insns(10) + [later_load], "outside its block"),
                ("the address passed elsewhere before the store", [ENTRY] + passed_before + fill_insns(10),
                 "outside its block"),
                ("a frame reference with no constant offset", [ENTRY] + fill_insns(10) + [unknown],
                 "no constant offset"),
                ("the temporary read in its block", [ENTRY] + fill_insns(10)[:3] + [read_inside] + fill_insns(10)[3:],
                 "beside its store"),
                ("the address stored to memory in its block",
                 [ENTRY] + fill_insns(10)[:3] + [escape] + fill_insns(10)[3:], "beside its store")):
            with self.subTest(label=label), self.assertRaisesRegex(proof.ProofError, reason):
                fill.fills(function(insns))
        # a CpuSet call whose source is no frame slot is no fill, and no volatile store makes it one
        copy = [ENTRY, (10, "insn (set (reg:SI 0 r0) (reg/v:SI 22)) -1 (nil) (nil)"),
                (11, "insn (set (reg:SI 2 r2) (const_int 64)) -1 (nil) (nil)"),
                (12, 'call_insn (call (mem:SI (symbol_ref:SI ("func_0814186C")) 0) (const_int 0)) -1 (nil) (nil) '
                     '(expr_list (use (reg:SI 0 r0)) (nil))')]
        self.assertEqual(fill.fills(function(copy)), [])


def thumb(*halves):
    return struct.pack(f"<{len(halves)}H", *halves)


def encode_bl(at, target):
    offset = target - (at + 4)
    return struct.pack("<HH", 0xF000 | (offset >> 12) & 0x7FF, 0xF800 | (offset >> 1) & 0x7FF)


ADDRESS = 0x08000400


def window(items, uid=7, labels=(), control=0x01000100):
    """(rom, compiled, fill) for a function at ADDRESS whose code is items: halfwords, ("bl", target); each
    LDR_R2 loads `control` from a literal pool after the code"""
    rom = bytearray(b"\xff" * 0x150000)
    rom[0x14186C:0x141870] = fill.CPUSET_BYTES
    code, offsets, site = bytearray(), [], None
    for item in items:
        offsets.append(len(code))
        if isinstance(item, tuple):
            site = len(code)
            code += encode_bl(ADDRESS + len(code), item[1])
        else:
            code += thumb(item)
    pool = len(code) + 3 & ~3
    code += bytes(pool - len(code)) + struct.pack("<I", control)
    for item, at in zip(items, offsets):
        if item == LDR_R2:
            code[at:at + 2] = thumb(LDR_R2 | (pool - (at + 4 & ~3)) // 4)
    code = bytes(code)
    rom[ADDRESS - fill.BASE:ADDRESS - fill.BASE + len(code)] = code
    compiled = {"text": (code, 0, len(code), []), "layout": (offsets, set(labels)), "uids": {uid: [(site, "bl")]}}
    return bytes(rom), compiled, {"call": proof.Insn(["call_insn", str(uid), "0", "0", ["call"]], 0), "width": 2,
                                  "control": control}


ADD_R1_SP_38, MOVS_R0_0, STRH_R0_R1 = 0xA90E, 0x2000, 0x8008
LDR_R1, LDR_R2, ADD_R0_SP_38 = 0x4900, 0x4A00, 0xA80E


@unittest.skipUnless(capstone, "capstone required")
class RomTests(unittest.TestCase):
    def test_the_rom_s_fill_shapes(self):
        # 0804AB2C: the slot's address in r1, the zero stored through it, r0 formed again for the call
        rom, compiled, one = window([ADD_R1_SP_38, MOVS_R0_0, STRH_R0_R1, LDR_R1, LDR_R2, ADD_R0_SP_38,
                                     ("bl", 0x0814186C)])
        self.assertEqual(fill.rom_fill(rom, ADDRESS, compiled, one), (ADDRESS + 12, 0x38, ADDRESS))
        # 0804ABE2: mov r0, sp; adds r0, #0x3a; movs r1, #0; strh r1, [r0]
        rom, compiled, one = window([0x4668, 0x303A, 0x2100, 0x8001, 0x1C29, LDR_R2, ("bl", 0x0814186C)])
        self.assertEqual(fill.rom_fill(rom, ADDRESS, compiled, one)[1], 0x3A)
        # 0813F43C: after sub sp, the window starts at mov r0, sp
        rom, compiled, one = window([0xB081, 0x4668, 0x2500, 0x8005, LDR_R1, LDR_R2, ("bl", 0x0814186C)])
        self.assertEqual(fill.rom_fill(rom, ADDRESS, compiled, one)[1], 0)
        # 0804BFDC: a word is stored at sp before r0 is formed (str r0, [sp]; mov r0, sp)
        rom, compiled, one = window([0x9000, 0x4668, 0x1C29, LDR_R2, ("bl", 0x0814186C)])
        one.update(width=4)
        self.assertEqual(fill.rom_fill(rom, ADDRESS, compiled, one), (ADDRESS + 8, 0, ADDRESS + 2))

    def test_r1_must_miss_the_slot(self):
        # the slot is sp+0x38; r1 = sp+0x30 with four halfwords ends at it, five reach it, sp+0x38 is it
        shape = [ADD_R1_SP_38, MOVS_R0_0, STRH_R0_R1, 0xA90C, ADD_R0_SP_38, LDR_R2, ("bl", 0x0814186C)]
        rom, compiled, one = window(shape, control=0x01000004)
        self.assertEqual(fill.rom_fill(rom, ADDRESS, compiled, one)[1], 0x38)
        for label, items, control, reason in (
                ("a fill that runs into it", shape, 0x01000005, "passes r1 sp\\+0x30, which reaches"),
                ("the slot itself", [ADD_R1_SP_38, MOVS_R0_0, STRH_R0_R1, ADD_R0_SP_38, LDR_R2, ("bl", 0x0814186C)],
                 0x01000100, "passes r1 sp\\+0x38, which reaches"),
                ("r3 in the slot", [ADD_R1_SP_38, MOVS_R0_0, STRH_R0_R1, LDR_R1, 0xAB0E, ADD_R0_SP_38, LDR_R2,
                                    ("bl", 0x0814186C)], 0x01000100, "passes r3 sp\\+0x38, which reaches")):
            with self.subTest(label=label):
                rom, compiled, one = window(items, control=control)
                with self.assertRaisesRegex(proof.ProofError, reason):
                    fill.rom_fill(rom, ADDRESS, compiled, one)

    def test_a_cpufastset_fill_in_the_rom(self):
        # 0801A176: movs r0, #0; str r0, [sp]; ldr r1, [sp, #0xc]; ldr r2, =0x010013F8; mov r0, sp; bl CpuFastSet
        fast = dict(width=4, callee="func_08141868")
        items = [MOVS_R0_0, 0x9000, 0x9903, LDR_R2, 0x4668, ("bl", 0x08141868)]
        rom, compiled, one = window(items, control=0x010013F8)
        one.update(fast)
        self.assertEqual(fill.rom_fill(rom, ADDRESS, compiled, one), (ADDRESS + 10, 0, ADDRESS + 8))
        rom, compiled, one = window(items[:-1] + [("bl", 0x0814186C)], control=0x010013F8)
        one.update(fast)
        with self.assertRaisesRegex(proof.ProofError, "does not reach 08141868"):
            fill.rom_fill(rom, ADDRESS, compiled, one)
        # the slot is sp+0x1c and r1 is sp: one word misses it, CpuFastSet's run of eight reaches it
        items = [MOVS_R0_0, 0x9007, 0xA900, LDR_R2, 0xA807]
        rom, compiled, one = window(items + [("bl", 0x0814186C)], control=0x05000001)
        one.update(width=4)
        self.assertEqual(fill.rom_fill(rom, ADDRESS, compiled, one)[1], 0x1C)
        rom, compiled, one = window(items + [("bl", 0x08141868)], control=0x01000001)
        one.update(fast)
        with self.assertRaisesRegex(proof.ProofError, "passes r1 sp\\+0x0, which reaches"):
            fill.rom_fill(rom, ADDRESS, compiled, one)

    def test_r2_set_in_the_line_must_be_the_control_word(self):
        shape = [ADD_R1_SP_38, MOVS_R0_0, STRH_R0_R1, LDR_R1, LDR_R2, ADD_R0_SP_38, ("bl", 0x0814186C)]
        rom, compiled, one = window(shape, control=0x01000040)
        self.assertEqual(fill.rom_fill(rom, ADDRESS, compiled, one)[1], 0x38)
        # an immediate shifted into place: movs r2, #0x81; lsls r2, r2, #17; adds r2, #0x20
        built = shape[:4] + [0x2281, 0x0452, 0x3220] + shape[5:]
        rom, compiled, one = window(built, control=0x01020020)
        self.assertEqual(fill.rom_fill(rom, ADDRESS, compiled, one)[1], 0x38)
        # agbcc may keep the constant in a callee-saved register across calls (adds r2, r6, #0): the line does not
        # show it, and the control word is the RTL's (fills)
        rom, compiled, one = window(shape[:4] + [0x1C32] + shape[5:], control=0x01000040)
        self.assertEqual(fill.rom_fill(rom, ADDRESS, compiled, one)[1], 0x38)
        # a literal that a load then replaces (ldr r2, [sp, #8]) is no longer what r2 holds
        rom, compiled, one = window(shape[:5] + [0x9A02] + shape[5:], control=0x01000040)
        one.update(control=0x01000080)
        self.assertEqual(fill.rom_fill(rom, ADDRESS, compiled, one)[1], 0x38)
        for label, items, control, reason in (
                ("another literal", shape, 0x01000080, "r2 holds 0x01000040 at the BL"),
                ("another immediate", built, 0x01020000, "r2 holds 0x01020020 at the BL")):
            with self.subTest(label=label):
                rom, compiled, one = window(items, control=0x01000040 if items is shape else 0x01020020)
                one.update(control=control)
                with self.assertRaisesRegex(proof.ProofError, reason):
                    fill.rom_fill(rom, ADDRESS, compiled, one)

    def test_rom_refusals(self):
        for label, items, reason, extra in (
                ("a word stored for a halfword temporary",
                 [MOVS_R0_0, 0x900E, ADD_R0_SP_38, LDR_R1, LDR_R2, ("bl", 0x0814186C)], "with 2 bytes", {}),
                ("r0 no stack address", [ADD_R1_SP_38, MOVS_R0_0, STRH_R0_R1, LDR_R1, 0x4800, LDR_R2,
                                         ("bl", 0x0814186C)], "r0 holds no stack address", {}),
                ("a second access to the slot", [ADD_R1_SP_38, MOVS_R0_0, STRH_R0_R1, 0x880A, ADD_R0_SP_38,
                                                 LDR_R2, ("bl", 0x0814186C)], "not stored exactly once", {}),
                ("another callee", [ADD_R1_SP_38, MOVS_R0_0, STRH_R0_R1, ADD_R0_SP_38, LDR_R2,
                                    ("bl", 0x08141868)], "does not reach", {}),
                ("the address formed before another call", [ADD_R1_SP_38, ("bl", 0x08001000), MOVS_R0_0,
                                                            STRH_R0_R1, 0x1C08, LDR_R2, ("bl", 0x0814186C)],
                 "r0 holds no stack address", {})):
            with self.subTest(label=label):
                rom, compiled, one = window(items)
                one.update(extra)
                with self.assertRaisesRegex(proof.ProofError, reason):
                    fill.rom_fill(rom, ADDRESS, compiled, one)


class IdentityTests(unittest.TestCase):
    def test_cpuset_must_be_the_bios_call_in_the_rom(self):
        for label, source, bios, reason in (
                ("CpuSet", TYPES + CPUSET + BLOCK, (0x14186C, fill.CPUFASTSET_BYTES), "swi 0x0B"),
                ("CpuFastSet", TYPES + FASTSET + FAST, (0x141868, fill.CPUSET_BYTES), "swi 0x0C")):
            with self.subTest(label=label), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                (root / "src").mkdir()
                (root / "src" / "08000400.c").write_text(source)
                rom = bytearray(b"\xff" * 0x150000)
                rom[bios[0]:bios[0] + 4] = bios[1]
                with self.assertRaisesRegex(proof.ProofError, reason):
                    fill.prove(root, root, "src/08000400.c", source, set(), rom=bytes(rom))


@unittest.skipUnless(shutil.which("cpp"), "cpp required")
class CensusTests(unittest.TestCase):
    def test_a_macro_token_reaches_the_unit_once_per_use(self):
        source = TYPES + CPUSET + MACRO
        (found,) = fill.fill_groups(source)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "src").mkdir()
            (root / "src" / "08000400.c").write_text(source)
            with tempfile.TemporaryDirectory(dir=root) as work:
                unit = proof.Unit(root, "src/08000400.c", source, found["offsets"], work,
                                  repeated=frozenset(found["offsets"]))
                self.assertEqual(unit.reaches, [2, 2])
            with tempfile.TemporaryDirectory(dir=root) as work, \
                    self.assertRaisesRegex(proof.ProofError, "exactly once"):
                proof.Unit(root, "src/08000400.c", source, found["offsets"], work)


COMPILER = Path(os.path.expandvars(proof.CC)).is_file() and shutil.which("cpp") and shutil.which(proof.AS)


@unittest.skipUnless(COMPILER and capstone, "fixed compiler and capstone required")
class CompiledTests(unittest.TestCase):
    """the rule through agbcc, on a ROM built around each compiled function"""

    def run_fill(self, body, head=CPUSET):
        source = TYPES + head + body
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "src").mkdir()
            (root / "include").mkdir()
            (root / "src" / "08000400.c").write_text(source)
            with tempfile.TemporaryDirectory(dir=root) as work:
                unit = proof.Unit(root, "src/08000400.c", source, [], work)
                text, start, size, relocations = unit.compile("probe", unit.real, "func_08000400")["text"]
            rom = bytearray(b"\xff" * 0x150000)
            rom[0x14186C:0x141870] = fill.CPUSET_BYTES
            rom[0x141868:0x14186C] = fill.CPUFASTSET_BYTES
            rom[ADDRESS - fill.BASE:ADDRESS - fill.BASE + size] = text[start:start + size]
            for at, kind, name in relocations:
                if kind == 10:
                    site = ADDRESS + at - start
                    target = {"func_0814186C": 0x0814186C, "func_08141868": 0x08141868}.get(name, 0x08001000)
                    rom[site - fill.BASE:site - fill.BASE + 4] = encode_bl(site, target)
            return fill.prove(root, root, "src/08000400.c", source, set(), rom=bytes(rom))

    def states(self, body, head=CPUSET):
        return [state for _, (state, _) in self.run_fill(body, head)]

    def test_the_sdk_block_and_macro_are_admitted(self):
        two = ("void func_08000400(u16 *dest) {\n    {\n        volatile u16 tmp = 0;\n"
               "        func_0814186C((const void *)&tmp, dest, 0x01000100);\n    }\n"
               "    {\n        volatile u16 tmp = 0;\n"
               "        func_0814186C((const void *)&tmp, dest + 0x100, 0x01000100);\n    }\n}\n")
        result = self.run_fill(two)
        self.assertEqual([state for _, (state, _) in result], ["admitted", "admitted"], result)
        self.assertIn("is the SDK's BIOS fill temporary (a block)", result[0][1][1])
        self.assertIn("0814186C is `swi 0x0B; bx lr` in the ROM", result[0][1][1])
        macro = self.run_fill(MACRO)
        self.assertEqual([state for _, (state, _) in macro], ["admitted", "admitted"], macro)
        self.assertIn("(macro CpuFill16, used 2 times)", macro[0][1][1])
        # a fifth argument comes from the stack, and comparing it does not hide the fill
        fifth = ("void func_08000400(u16 *dest, int a, int b, int c, int n) {\n    if (n > 0) {\n"
                 "        volatile u16 tmp = 0;\n        func_0814186C((const void *)&tmp, dest, 0x01000100);\n"
                 "    }\n}\n")
        self.assertEqual(self.states(fifth), ["admitted"])

    def test_the_sdk_fast_fill_is_admitted(self):
        result = self.run_fill(FAST, FASTSET)
        self.assertEqual([state for _, (state, _) in result], ["admitted", "admitted"], result)
        text = result[0][1][1]
        self.assertIn("(macro CpuFastFill, used 2 times)", text)
        self.assertIn("control 0x01000020, 4-byte units", text)
        self.assertIn("08141868 is `swi 0x0C; bx lr` in the ROM", text)
        self.assertNotIn("0814186C", text)
        local = "extern void func_08001000(u32 *out);\nvoid func_08000400(u32 *dest) {\n    u32 out;\n" \
                "    func_08001000(&out);\n"
        block = local + ("    {\n        volatile u32 fill = out;\n\n"
                         "        func_08141868((const void *)&fill, dest, 0x01000400);\n    }\n}\n")
        self.assertEqual(self.states(block, FASTSET), ["admitted"])

    def test_a_fast_fill_the_rom_does_not_show_refuses(self):
        for control, reason in (("0x00000020", "without bit 24"), ("0x05000020", "a bit outside 0-20 and 24")):
            with self.subTest(control=control), self.assertRaisesRegex(proof.ProofError, reason):
                self.run_fill(FAST.replace("0x01000000 |", f"{control} |"), FASTSET)

    def test_a_qualifier_that_changes_nothing_refuses(self):
        # the second arm's temporary compiles alike without its qualifier: the ROM does not show it
        arms = ("void func_08000400(int c, u16 *a, u16 *b) {\n    if (c) {\n        volatile u16 tmp = 0;\n"
                "        func_0814186C((const void *)&tmp, a, 0x01000100);\n    } else {\n"
                "        volatile u16 tmp = 0;\n        func_0814186C((const void *)&tmp, b, 0x01000080);\n    }\n}\n")
        with self.assertRaisesRegex(proof.ProofError, "line 10 does not change the code"):
            self.run_fill(arms)

    def test_a_macro_argument_that_names_the_temporary_refuses(self):
        head = MACRO.split("void func_08000400")[0]
        for dest in ("&tmp", "(u16 *)&tmp + 0"):
            with self.subTest(dest=dest), \
                    self.assertRaisesRegex(proof.ProofError, "passes r1 an address that reaches"):
                self.run_fill(head + f"void func_08000400(u16 *dest) {{ CpuFill16(0, {dest}, 0x40); }}\n")

    def test_a_removal_that_moves_another_fill_refuses(self):
        # without the word's qualifier the halfword fill moves from sp+4 to sp+0, a store the function does not make
        word = ("void func_08000400(u16 *dest) {\n    {\n        volatile u32 tmp = 0;\n"
                "        func_0814186C((const void *)&tmp, dest, 0x05000010);\n    }\n"
                "    {\n        volatile u16 tmp = 0;\n"
                "        func_0814186C((const void *)&tmp, dest + 0x40, 0x01000010);\n    }\n}\n")
        with self.assertRaisesRegex(proof.ProofError, "line 7 does not account for its volatile stores"):
            self.run_fill(word)

    def test_a_fill_the_rom_does_not_show_refuses(self):
        with self.assertRaisesRegex(proof.ProofError, "without bit 24"):
            self.run_fill(BLOCK.replace("0x01000100", "0x00000100"))
        with self.assertRaisesRegex(proof.ProofError, "bit 26"):
            self.run_fill(BLOCK.replace("0x01000100", "0x05000100"))

    def test_what_is_no_fill_is_not_considered(self):
        for label, body in (
                ("the temporary read after the call", BLOCK.replace(
                    "0x01000100);\n", "0x01000100);\n        dest[1] = tmp;\n")),
                ("a volatile object that is no stack temporary", "extern volatile u16 data_03000040;\n"
                 "void func_08000400(u16 *dest) { func_0814186C((const void *)&data_03000040, dest, 0x01000100); }\n"),
                ("another callee", BLOCK.replace("func_0814186C((const", "func_08141868((const").replace(
                    "void func_08000400(u16", "extern void func_08141868(const void *, void *, unsigned int);\n"
                    "void func_08000400(u16"))):
            with self.subTest(label=label):
                self.assertIsNone(self.run_fill(body))


if __name__ == "__main__":
    unittest.main()
