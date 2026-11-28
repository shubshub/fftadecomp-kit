"""The SDK's BIOS fill temporary (tools/bios_fill_temporary.py, kit issue 164)."""
from collections import Counter
import os
from pathlib import Path
import shutil
import struct
import sys
import tempfile
import unittest
import unittest.mock

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


def block_move(uid, offset, label=False):
    """the RTL of a 12-byte structure copy into the frame at offset (movstrsi): the destination pointer, then
    one parallel that copies three words through it and advances it; label puts a branch target between them"""
    words = "".join(f"            (set (mem:SI (plus:SI (reg:SI 100) (const_int {k})) 0)\n"
                    f"                (mem:SI (plus:SI (reg:SI 101) (const_int {k})) 0))\n" for k in (4, 8))
    out = [(uid, f"insn (set (reg:SI 100) (plus:SI (reg:SI 18 virtual-stack-vars) (const_int {offset}))) "
                 "-1 (nil) (nil)"),
           (uid + 1, "insn (set (reg:SI 101) (reg/v:SI 22)) -1 (nil) (nil)")]
    if label:
        out.append((uid + 2, 'code_label 99 ""'))
    out.append((uid + 3, "insn (parallel[ \n            (set (mem:SI (reg:SI 100) 0)\n"
                         "                (mem:SI (reg:SI 101) 0))\n" + words +
                         "            (set (reg:SI 100) (plus:SI (reg:SI 100) (const_int 12)))\n"
                         "            (set (reg:SI 101) (plus:SI (reg:SI 101) (const_int 12)))\n"
                         "            (clobber (scratch:SI))\n            (clobber (scratch:SI))\n"
                         "            (clobber (scratch:SI))\n        ] ) -1 (nil)\n    (nil)"))
    return out


class RtlTests(unittest.TestCase):
    def test_a_function_naming_the_static_chain_is_nested(self):
        chained = (3, "insn (set (reg:SI 70) (reg:SI 9 r9)) -1 (nil) (nil)")
        noted = (3, "insn (set (reg:SI 70) (reg:SI 71)) -1 (nil) (expr_list:REG_EQUAL (reg:SI 9 r9) (nil))")
        others = [(3, "insn (set (reg:SI 70) (reg:SI 8 r8)) -1 (nil) (nil)"),
                  (4, "insn (set (reg:SI 79) (reg:SI 90)) -1 (nil) (nil)")]
        rtl = {"func_08000400": function([ENTRY] + fill_insns(10)), "peek": function([ENTRY, chained], "peek"),
               "twice": function([ENTRY, noted], "twice"), "plain": function([ENTRY] + others, "plain")}
        self.assertEqual(fill.nested_functions(rtl), ["peek", "twice"])
        self.assertEqual(fill.nested_functions({"func_08000400": rtl["func_08000400"]}), [])

    def test_a_fill_is_read_off_its_block(self):
        (found,) = fill.fills(function([ENTRY] + fill_insns(10)))
        self.assertEqual((found["slot"], found["width"], found["control"], found["call"].uid, found["value"]),
                         ((18, -2), 2, 0x01000100, 16, 0))
        other = [(k, i.replace("(const_int 0)", "(const_int -1)")) for k, i in fill_insns(10)]
        self.assertEqual(fill.fills(function([ENTRY] + other))[0]["value"], 0xFFFF)
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

    def test_a_block_move_is_placed_by_its_pointers_reaching_definitions(self):
        # 08081FB0: a structure copy into the frame advances its own pointers, so each has two definitions;
        # read where the copy reads them, the destination is the one before it, and after it that plus 12
        label = (29, 'code_label 98 ""')
        fn = function([ENTRY] + block_move(3, -16) + [label] + fill_insns(10))
        touches = fill.frame_touches(fn, proof.Resolver(fn))
        self.assertEqual(Counter((offset, width, what) for _, _, offset, width, what, _ in touches if offset != -2),
                         Counter([(-16, None, "address"), (-16, 4, "store"), (-12, 4, "store"), (-8, 4, "store"),
                                  (-4, None, "address")]))
        (found,) = fill.fills(fn)
        self.assertEqual(found["slot"], (18, -2))
        # the pointer moved on by 2 after the copy reaches the slot: forming it is placed, and refused
        onward = [(19, "insn (set (reg:SI 100) (plus:SI (reg:SI 100) (const_int 2))) -1 (nil) (nil)"),
                  (20, "insn (set (mem:HI (reg:SI 100) 0) (const_int 0)) -1 (nil) (nil)")]
        for label_, insns, reason in (
                ("a store the pointer reaches the slot with", [ENTRY] + block_move(3, -16) + onward + [label] +
                 fill_insns(10), "UID 19 uses the fill temporary's slot outside its block \\(address\\)"),
                ("a copy over the slot", [ENTRY] + block_move(3, -8) + [label] + fill_insns(10),
                 "UID 6 uses the fill temporary's slot outside its block"),
                ("a branch target between the pointer and the copy",
                 [ENTRY] + block_move(3, -16, label=True) + [label] + fill_insns(10), "no constant offset"),
                ("the advanced pointer as the destination", [ENTRY] + block_move(3, -16) +
                 fill_insns(10, control=0x01000002, dest="(reg:SI 100)"), "passes r1 an address that reaches")):
            with self.subTest(label=label_), self.assertRaisesRegex(proof.ProofError, reason):
                fill.fills(function(insns))

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
MOV_R0_SP, ADDS_R0_3A, MOVS_R1_0, STRH_R1_R0, ADDS_R0_R1, ADDS_R1_R7 = 0x4668, 0x303A, 0x2100, 0x8001, 0x1C08, 0x1C39


def assemble(items, control):
    """(code, offsets) of items: halfwords, ("bl", target), ("b", "beq" or "far", the index of the item it reaches;
    "far" is agbcc's far-jump BL), ("word", a data word); each LDR_R2 loads `control` from a literal pool after the
    code"""
    offsets, at = [], 0
    for item in items:
        offsets.append(at)
        at += 4 if isinstance(item, tuple) and item[0] in ("bl", "far", "word") else 2
    code = bytearray()
    for item, at in zip(items, offsets):
        if isinstance(item, tuple) and item[0] == "bl":
            code += encode_bl(ADDRESS + at, item[1])
        elif isinstance(item, tuple) and item[0] == "far":
            code += encode_bl(ADDRESS + at, ADDRESS + offsets[item[1]])
        elif isinstance(item, tuple) and item[0] == "word":
            code += struct.pack("<I", item[1])
        elif isinstance(item, tuple):
            step = (offsets[item[1]] - (at + 4)) // 2
            code += thumb(0xE000 | step & 0x7FF if item[0] == "b" else 0xD000 | step & 0xFF)
        else:
            code += thumb(item)
    pool = len(code) + 3 & ~3
    code += bytes(pool - len(code)) + struct.pack("<I", control)
    for item, at in zip(items, offsets):
        if item == LDR_R2:
            code[at:at + 2] = thumb(LDR_R2 | (pool - (at + 4 & ~3)) // 4)
    return bytes(code), offsets


def shared(items, labels, uids, control=0x01000160):
    """(rom, compiled) for a function at ADDRESS whose code is items (see assemble), with branch targets at the
    items whose indices are labels and uids {insn uid: [(item index, instruction text)]}"""
    code, offsets = assemble(items, control)
    rom = bytearray(b"\xff" * 0x150000)
    rom[ADDRESS - fill.BASE:ADDRESS - fill.BASE + len(code)] = code
    instructions = [at for at, item in zip(offsets, items) if not (isinstance(item, tuple) and item[0] == "word")]
    compiled = {"text": (code, 0, len(code), []), "layout": (instructions, {offsets[k] for k in labels}),
                "far": {at for at, item in zip(offsets, items) if isinstance(item, tuple) and item[0] == "far"},
                "uids": {uid: [(offsets[k], text) for k, text in sites] for uid, sites in uids.items()}}
    return bytes(rom), compiled


def one_fill(uid, store_uid, block, width=2, control=0x01000160, value=0):
    return {"call": proof.Insn(["call_insn", str(uid), "0", "0", ["call"]], 0), "width": width, "control": control,
            "store_uid": store_uid, "block": list(block), "value": value}


def shifted(uids, at, by):
    """uids with every item index from `at` on moved by `by`"""
    return {uid: [(k + by if k >= at else k, text) for k, text in sites] for uid, sites in uids.items()}


# 0804A8AE-0804A936: two arms end in the same fill from their own slots, sp+0x38 and sp+0x3a; cross-jumping kept
# the second arm's tail (r1, r2, the BL) and ends the first arm with a branch into it.  The first arm's block is
# insns 557-584 (the call, 584, is gone), the second's 753-778; 618, 1134 and 1245 are insns later passes made.
ARMS = [("bl", 0x08001000), ADD_R1_SP_38, MOVS_R0_0, STRH_R0_R1, ADDS_R0_R1, ("b", 11),
        ("bl", 0x08001000), MOV_R0_SP, ADDS_R0_3A, MOVS_R1_0, STRH_R1_R0,
        ADDS_R1_R7, LDR_R2, ("bl", 0x0814186C)]
ARM_UIDS = {559: [(1, "add\tr1, sp, #56")], 561: [(2, "movs\tr0, #0")], 562: [(3, "strh\tr0, [r1]")],
            578: [(4, "adds\tr0, r1, #0")], 618: [(5, "b\t.L58")], 1134: [(7, "mov\tr0, sp")],
            754: [(8, "adds\tr0, #58")], 756: [(9, "movs\tr1, #0")], 757: [(10, "strh\tr1, [r0]")],
            774: [(11, "adds\tr1, r7, #0")], 1245: [(12, "ldr\tr2, .L61")], 778: [(13, "bl\tfunc_0814186C")]}
FIRST, SECOND = (584, 562, range(557, 585)), (778, 757, range(753, 779))
# a two-arm fill as agbcc compiles it when the arms store alike: cross-jumping took the store too (movs r1, #0;
# strh r1, [r0]), so each arm forms its slot's address and branches or falls into the one shared store
MERGED = [("bl", 0x08001000), ADD_R0_SP_38, ("b", 6), ("bl", 0x08001000), MOV_R0_SP, ADDS_R0_3A,
          MOVS_R1_0, STRH_R1_R0, ADDS_R1_R7, LDR_R2, ("bl", 0x0814186C)]
MERGED_UIDS = {28: [(1, "add\tr0, sp, #56")], 50: [(2, "b\t.L4")], 107: [(4, "mov\tr0, sp")],
               62: [(5, "adds\tr0, #58")], 64: [(6, "movs\tr1, #0")], 65: [(7, "strh\tr1, [r0]")],
               72: [(8, "adds\tr1, r7, #0")], 76: [(10, "bl\tfunc_0814186C")]}


@unittest.skipUnless(capstone, "capstone required")
class RomTests(unittest.TestCase):
    def test_the_rom_s_fill_shapes(self):
        # 0804AB2C: the slot's address in r1, the zero stored through it, r0 formed again for the call
        rom, compiled, one = window([ADD_R1_SP_38, MOVS_R0_0, STRH_R0_R1, LDR_R1, LDR_R2, ADD_R0_SP_38,
                                     ("bl", 0x0814186C)])
        self.assertEqual(fill.rom_fill(rom, ADDRESS, compiled, one), (ADDRESS + 12, 0x38, ADDRESS, ()))
        # 0804ABE2: mov r0, sp; adds r0, #0x3a; movs r1, #0; strh r1, [r0]
        rom, compiled, one = window([0x4668, 0x303A, 0x2100, 0x8001, 0x1C29, LDR_R2, ("bl", 0x0814186C)])
        self.assertEqual(fill.rom_fill(rom, ADDRESS, compiled, one)[1], 0x3A)
        # 0813F43C: after sub sp, the window starts at mov r0, sp
        rom, compiled, one = window([0xB081, 0x4668, 0x2500, 0x8005, LDR_R1, LDR_R2, ("bl", 0x0814186C)])
        self.assertEqual(fill.rom_fill(rom, ADDRESS, compiled, one)[1], 0)
        # 0804BFDC: a word is stored at sp before r0 is formed (str r0, [sp]; mov r0, sp)
        rom, compiled, one = window([0x9000, 0x4668, 0x1C29, LDR_R2, ("bl", 0x0814186C)])
        one.update(width=4)
        self.assertEqual(fill.rom_fill(rom, ADDRESS, compiled, one), (ADDRESS + 8, 0, ADDRESS + 2, ()))

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

    def test_a_register_offset_from_a_stack_address_refuses(self):
        # `strh r0, [r1, r2]` with r1 = sp+0x38 writes sp+0x38+r2, an address the path does not know; it was read
        # as a store to sp+0x38 (the base at displacement 0)
        strh_r0_r1_r2, ldrh_r3_r1_r2, add_r2_sp_38, strh_r0_r4_r2 = 0x5288, 0x5A8B, 0xAA0E, 0x52A0
        tail = [ADDS_R1_R7, LDR_R2, ADD_R0_SP_38, ("bl", 0x0814186C)]
        for label, items in (("the fill's store", [ADD_R1_SP_38, MOVS_R0_0, strh_r0_r1_r2] + tail),
                             ("a load", [ADD_R1_SP_38, MOVS_R0_0, STRH_R0_R1, ldrh_r3_r1_r2] + tail),
                             ("the index", [ADD_R1_SP_38, MOVS_R0_0, STRH_R0_R1, add_r2_sp_38, strh_r0_r4_r2] + tail)):
            with self.subTest(label=label):
                rom, compiled, one = window(items)
                with self.assertRaisesRegex(proof.ProofError, "indexes the stack by a register inside the fill"):
                    fill.rom_fill(rom, ADDRESS, compiled, one)
        # an immediate offset from a stack address is placed: `strh r0, [r1, #2]` writes sp+0x3a, beside the slot
        rom, compiled, one = window([ADD_R1_SP_38, MOVS_R0_0, STRH_R0_R1, 0x8048] + tail)
        self.assertEqual(fill.rom_fill(rom, ADDRESS, compiled, one)[1], 0x38)

    def test_r3_may_hold_the_slot_only_as_the_base_of_its_store_into_cpuset(self):
        # 0810ECD8-0810ECEA: the slot's address copied to r3 (`mov r3, sl`) to store through, then into CpuSet,
        # which reads r0-r2 only: r3 is left holding the slot's address
        add_r3_sp_38, strh_r0_r3, str_r0_r3, adds_r3_1 = 0xAB0E, 0x8018, 0x6018, 0x3301
        shape = [add_r3_sp_38, MOVS_R0_0, strh_r0_r3, ADDS_R1_R7, LDR_R2, ADD_R0_SP_38, ("bl", 0x0814186C)]
        rom, compiled, one = window(shape)
        self.assertEqual(fill.rom_fill(rom, ADDRESS, compiled, one), (ADDRESS + 12, 0x38, ADDRESS, ()))
        # the record states the premise the admission rests on; a fill with no r3 in its slot states none
        self.assertEqual(one["r3"], [f"r3 holds sp+0x38 at the BL as the base of the store at {ADDRESS + 4:08X}; "
                                     "BIOS premise: CpuSet (swi 0x0B) reads only r0-r2 (GBATEK), so nothing reads r3"])
        rom, compiled, plain = window([ADD_R1_SP_38, MOVS_R0_0, STRH_R0_R1, LDR_R1, LDR_R2, ADD_R0_SP_38,
                                       ("bl", 0x0814186C)])
        fill.rom_fill(rom, ADDRESS, compiled, plain)
        self.assertEqual(plain["r3"], [])
        rom, compiled, one = window(shape)
        # a callee that reads r3: the ROM's 0814186C is `ldrh r0, [r3]; bx lr`, no SWI
        reads = bytearray(rom)
        reads[0x14186C:0x141870] = thumb(0x8818, 0x4770)
        with self.assertRaisesRegex(proof.ProofError, "passes r3 sp\\+0x38, which reaches"):
            fill.rom_fill(bytes(reads), ADDRESS, compiled, one)
        # CpuFastSet, which the relaxation does not cover
        fast = [add_r3_sp_38, MOVS_R0_0, str_r0_r3, ADDS_R1_R7, LDR_R2, ADD_R0_SP_38, ("bl", 0x08141868)]
        rom, compiled, one = window(fast, control=0x01000008)
        one.update(width=4, callee="func_08141868")
        with self.assertRaisesRegex(proof.ProofError, "passes r3 sp\\+0x38, which reaches"):
            fill.rom_fill(rom[:0x141868] + fill.CPUFASTSET_BYTES + rom[0x14186C:], ADDRESS, compiled, one)
        for label, items, reason in (
                ("a second store", shape[:3] + [strh_r0_r3] + shape[3:], "is not stored exactly once"),
                ("a different base", [ADD_R1_SP_38, MOVS_R0_0, STRH_R0_R1, add_r3_sp_38] + shape[3:],
                 "passes r3 sp\\+0x38, which reaches"),
                ("r3 moved inside the slot after the store", shape[:3] + [adds_r3_1] + shape[3:],
                 "passes r3 sp\\+0x39, which reaches"),
                ("r1 in the slot as well", shape[:3] + [ADD_R1_SP_38] + shape[4:],
                 "passes r1 sp\\+0x38, which reaches"),
                ("a register offset from r3", [add_r3_sp_38, MOVS_R0_0, 0x5258] + shape[3:],
                 "indexes the stack by a register inside the fill"),
                ("r3 as the stored value, not the base", [ADD_R1_SP_38, add_r3_sp_38, 0x800B] + shape[3:],
                 "passes r3 sp\\+0x38, which reaches")):
            with self.subTest(label=label):
                rom, compiled, one = window(items)
                with self.assertRaisesRegex(proof.ProofError, reason):
                    fill.rom_fill(rom, ADDRESS, compiled, one)

    def test_a_cpufastset_fill_in_the_rom(self):
        # 0801A176: movs r0, #0; str r0, [sp]; ldr r1, [sp, #0xc]; ldr r2, =0x010013F8; mov r0, sp; bl CpuFastSet
        fast = dict(width=4, callee="func_08141868")
        items = [MOVS_R0_0, 0x9000, 0x9903, LDR_R2, 0x4668, ("bl", 0x08141868)]
        rom, compiled, one = window(items, control=0x010013F8)
        one.update(fast)
        self.assertEqual(fill.rom_fill(rom, ADDRESS, compiled, one), (ADDRESS + 10, 0, ADDRESS + 8, ()))
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

    def test_a_bl_two_fills_share_is_read_on_every_path(self):
        rom, compiled = shared(ARMS, {11}, ARM_UIDS)
        first, second = one_fill(*FIRST), one_fill(*SECOND)
        both = [first, second]
        self.assertEqual(fill.rom_fill(rom, ADDRESS, compiled, first, both),
                         (ADDRESS + 0x1E, 0x38, ADDRESS + 4, ((ADDRESS + 0x1A, ADDRESS + 0xC),)))
        self.assertEqual(fill.rom_fill(rom, ADDRESS, compiled, second, both),
                         (ADDRESS + 0x1E, 0x3A, ADDRESS + 0x14, ((ADDRESS + 0x1A, ADDRESS + 0x18),)))
        # the store shared as well: each path still stores its own slot once
        rom, compiled = shared(MERGED, {6}, MERGED_UIDS)
        first, second = one_fill(45, 43, range(26, 46)), one_fill(76, 65, range(60, 77))
        self.assertEqual(fill.rom_fill(rom, ADDRESS, compiled, first, [first, second]),
                         (ADDRESS + 0x18, 0x38, ADDRESS + 4, ((ADDRESS + 0x10, ADDRESS + 6),)))
        self.assertEqual(fill.rom_fill(rom, ADDRESS, compiled, second, [first, second]),
                         (ADDRESS + 0x18, 0x3A, ADDRESS + 0xE, ((ADDRESS + 0x10, ADDRESS + 0xE),)))
        # the first arm reaches the tail by agbcc's far jump, a BL into the function
        rom, compiled = shared(ARMS[:5] + [("far", 11)] + ARMS[6:], {11}, ARM_UIDS)
        first, second = one_fill(*FIRST), one_fill(*SECOND)
        self.assertEqual(fill.rom_fill(rom, ADDRESS, compiled, first, [first, second]),
                         (ADDRESS + 0x20, 0x38, ADDRESS + 4, ((ADDRESS + 0x1C, ADDRESS + 0xC),)))
        self.assertEqual(fill.rom_fill(rom, ADDRESS, compiled, second, [first, second])[1], 0x3A)
        # one fill whose line starts at a branch target that only its own block falls into
        alone = ARMS[6:]
        sites = shifted({k: v for k, v in ARM_UIDS.items() if v[0][0] >= 6}, 0, -6)
        rom, compiled = shared(alone, {5}, sites)
        one = one_fill(*SECOND)
        self.assertEqual(fill.rom_fill(rom, ADDRESS, compiled, one, [one]),
                         (ADDRESS + 0x10, 0x3A, ADDRESS + 6, ((ADDRESS + 0xC, ADDRESS + 0xA),)))
        # a second way in that stores nothing: the path from the beq shows no fill
        rom, compiled = shared([alone[0], ("beq", 6)] + alone[1:], {6}, shifted(sites, 1, 1))
        with self.assertRaisesRegex(proof.ProofError, "r0 holds no stack address at the BL at 08000412"):
            fill.rom_fill(rom, ADDRESS, compiled, one, [one])

    def test_shared_bl_refusals(self):
        first, second = one_fill(*FIRST), one_fill(*SECOND)
        uids = {k: v for k, v in ARM_UIDS.items() if k not in (559, 561, 562, 578)}
        conditional = ARMS[:5] + [("beq", 12), ("b", 12)] + ARMS[6:]
        for label, items, labels, sites, fills, reason in (
                ("a path without its own store", ARMS[:3] + [0x46C0] + ARMS[4:], {11}, ARM_UIDS, None,
                 "sp\\+0x38 of the fill at 0800041E is not stored exactly once"),
                ("a path whose store is no fill's", ARMS, {11}, {**uids, 563: [(3, "strh\tr0, [r1]")],
                                                                 578: [(4, "adds\tr0, r1, #0")]}, None,
                 "stores its slot sp\\+0x38 at 08000408, which is no fill's store"),
                ("a path from no fill's block", ARMS, {11}, {**uids, 580: [(11, "adds\tr1, r7, #0")]}, None,
                 "from 08000404 comes from no fill's block"),
                ("a path from two fills' blocks", ARMS, {11}, {**ARM_UIDS, 755: [(1, "add\tr1, sp, #56")]}, None,
                 "from 08000404 comes from more than one fill's block"),
                ("a block the code no longer holds", ARMS, {11}, uids, None,
                 "UID 584 is not one BL, and its block reaches none"),
                ("a temporary of another width", ARMS, {11}, ARM_UIDS, [one_fill(*FIRST, width=4), second],
                 "differ in their call or temporary"),
                ("another control word", ARMS, {11}, ARM_UIDS, [one_fill(*FIRST, control=0x01000180), second],
                 "r2 holds 0x01000160 at the BL at 0800041E, not the fill's control word 0x01000180"),
                ("a computed jump", ARMS + [0x4687], {11}, ARM_UIDS, None, "jumps where the ROM does not say"),
                ("a BL into the function the listing does not mark a far jump", ARMS + [("bl", ADDRESS + 0x1A)],
                 {11}, ARM_UIDS, None, "08000422 jumps where the ROM does not say"),
                ("a far jump to no branch target", ARMS + [("far", 9)], {11}, ARM_UIDS, None,
                 "08000422 is marked a far jump but reaches no branch target of the function"),
                # 0x08000400 calling itself in the arm whose tail cross-jumping kept: the call returns into the
                # target, and the CpuSet BL then runs with r0 = its result and no store
                ("a recursive call falling into the target", ARMS[:5] + [("b", 7), ("bl", ADDRESS)] + ARMS[11:],
                 {7}, {**{k: v for k, v in ARM_UIDS.items() if v[0][0] < 6}, 778: [(9, "bl\tfunc_0814186C")]},
                 [first], "r0 holds no stack address at the BL at 08000416"),
                ("an insn before the target that does not fall into it",
                 ARMS[:5] + [("b", 12)] + ARMS[6:11] + [("word", 0)] + ARMS[11:], {12}, shifted(ARM_UIDS, 11, 1),
                 None, "08000418 does not fall through to the branch target at 0800041E"),
                ("a far jump in that stores nothing", ARMS + [("far", 11)], {11}, ARM_UIDS, None,
                 "r0 holds no stack address at the BL at 0800041E"),
                ("a conditional branch in that stores nothing", ARMS + [("beq", 11)], {11}, ARM_UIDS, None,
                 "r0 holds no stack address at the BL at 0800041E"),
                ("the target's address in a literal", ARMS + [0x46C0, ("word", ADDRESS + 0x1B)], {11}, ARM_UIDS, None,
                 "the address of the branch target at 0800041A is taken"),
                ("the target's address formed in the code", [0xA006] + ARMS[:5] + [("b", 12)] + ARMS[6:], {12},
                 shifted(ARM_UIDS, 0, 1), None, "the address of the branch target at 0800041C is taken"),
                ("another value stored", ARMS, {11}, ARM_UIDS, [one_fill(*FIRST, value=1), second],
                 "the store at 08000408 writes 0x0 to the slot sp\\+0x38, not the fill's value 0x1"),
                ("a block that leaves by a conditional branch", conditional, {12}, shifted(ARM_UIDS, 5, 1), None,
                 "UID 584 is not one BL, and its block reaches none in a straight line"),
                ("a call between the store and the target",
                 ARMS[:5] + [("b", 12)] + ARMS[6:11] + [("bl", 0x08001000)] + ARMS[11:], {12},
                 shifted(ARM_UIDS, 11, 1), None, "r0 holds no stack address at the BL at 08000422"),
                ("a fill sharing the BL with no path", ARMS, {11}, {**ARM_UIDS, 395: [(11, "adds\tr1, r7, #0")]},
                 [first, second, one_fill(400, 399, range(390, 401))],
                 "UID 400 reaches the BL at 0800041E by no path of its own"),
                ("a fill reaching the BL from two slots", ARMS + [0xA90F, MOVS_R0_0, STRH_R0_R1, ADDS_R0_R1, ("b", 11)],
                 {11}, {**ARM_UIDS, 570: [(14, "add\tr1, sp, #60")], 571: [(16, "strh\tr0, [r1]")],
                        562: [(3, "strh\tr0, [r1]"), (16, "strh\tr0, [r1]")]}, None,
                 "UID 584 reaches the BL at 0800041E by paths with different slots")):
            with self.subTest(label=label):
                rom, compiled = shared(items, labels, sites)
                both = fills or [first, second]
                with self.assertRaisesRegex(proof.ProofError, reason):
                    for one in both:
                        fill.rom_fill(rom, ADDRESS, compiled, one, both)

    def test_far_jumps_are_read_off_the_listing(self):
        # agbcc marks its long branch `@far jump`, or `@ far jump`; a BL to a function is a call, marked or not
        listing = ("  18 0008 01F034F8 \t\tbl\t.L3\t@far jump\n"
                   "  31 0010 FFF7FEFF \t\tbl\t.L9\t@ far jump\n"
                   "  40 0014 FFF7FEFF \t\tbl\t.L9\n"
                   "  52 0018 FFF7FEFF \t\tbl\tfunc_08000400\t@ 33\tcall_value\n"
                   "  60 001c FFF7FEFF \t\tbl\tfunc_08000400\t@far jump\n")
        self.assertEqual(fill.far_jumps(listing), {0x8, 0x10})

    def test_paths_are_bounded(self):
        first, second = one_fill(*FIRST), one_fill(*SECOND)
        rom, compiled = shared(ARMS, {11}, ARM_UIDS)
        for name, value, reason in (("MAX_PATHS", 1, "more than 1 paths reach the BL at 0800041E"),
                                    ("MAX_WINDOW", 6, "a path into the BL at 0800041E is longer than 6")):
            with self.subTest(name=name), unittest.mock.patch.object(fill, name, value), \
                    self.assertRaisesRegex(proof.ProofError, reason):
                fill.rom_fill(rom, ADDRESS, compiled, first, [first, second])

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

    def test_a_fill_beside_a_structure_copy_is_admitted(self):
        # 08081FB0: the copy into a frame structure is a block move, whose pointers have two definitions each
        copy = ("struct S { u32 a, b, c; };\nextern void func_08001000(u32 *out);\n"
                "extern void func_08001004(struct S *s, u32 out);\n"
                "void func_08000400(u32 *dest, struct S *src)\n{\n    u32 out;\n\n"
                "    func_08001000(&out);\n    {\n        volatile u32 fill = 0;\n\n"
                "        func_08141868((const void *)&fill, dest, 0x01000008);\n    }\n"
                "    {\n        struct S copy;\n\n        copy = *src;\n        func_08001004(&copy, out);\n    }\n}\n")
        self.assertEqual(self.states(copy, FASTSET), ["admitted"])

    def test_a_fast_fill_the_rom_does_not_show_refuses(self):
        for control, reason in (("0x00000020", "without bit 24"), ("0x05000020", "a bit outside 0-20 and 24")):
            with self.subTest(control=control), self.assertRaisesRegex(proof.ProofError, reason):
                self.run_fill(FAST.replace("0x01000000 |", f"{control} |"), FASTSET)

    def test_fills_that_share_a_bl_are_admitted(self):
        # the arms' tails are alike from the store on, so cross-jumping leaves the first arm's slot address and a
        # branch into the second arm's store and BL
        arms = MACRO.split("void func_08000400")[0] + (
            "extern void func_08001000(void);\nextern void func_08001004(void);\n"
            "extern void func_08001008(u16 *dest);\nextern void func_0800100C(void);\n"
            "extern void func_08001010(void);\n"
            "void func_08000400(int c, u16 *dest)\n{\n    if (c == 1) {\n        func_08001000();\n"
            "        CpuFill16(0, dest, 0x2C0);\n        func_08001008(dest);\n    } else if (c == 2) {\n"
            "        func_08001004();\n        CpuFill16(0, dest, 0x2C0);\n        func_08001008(dest);\n"
            "    } else {\n        func_0800100C();\n    }\n    func_08001010();\n}\n")
        result = self.run_fill(arms)
        self.assertEqual([state for _, (state, _) in result], ["admitted", "admitted"], result)
        text = result[0][1][1]
        self.assertIn("(macro CpuFill16, used 2 times)", text)
        self.assertIn("08000426 fills from sp+0x0 (address formed at 0800040E, joining at 0800041E from 08000410, "
                      "control 0x01000160", text)
        self.assertIn("08000426 fills from sp+0x2 (address formed at 0800041C, joining at 0800041E from 0800041C, "
                      "control 0x01000160", text)

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

    def test_a_removal_that_moves_another_fill_is_accounted(self):
        # without the word's qualifier the halfword fill moves from sp+4 to sp+0, keeping its volatile store: the
        # fills pair by call order, so the word's group accounts for exactly its own fill.  The proof then reaches
        # the halfword's group, whose qualifier changes nothing (the store stays, its address escapes)
        word = ("void func_08000400(u16 *dest) {\n    {\n        volatile u32 tmp = 0;\n"
                "        func_0814186C((const void *)&tmp, dest, 0x05000010);\n    }\n"
                "    {\n        volatile u16 tmp = 0;\n"
                "        func_0814186C((const void *)&tmp, dest + 0x40, 0x01000010);\n    }\n}\n")
        with self.assertRaisesRegex(proof.ProofError, "removing the qualifiers of the fill at line 11 does not change "
                                                      "the code"):
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

    def test_a_unit_holding_a_nested_function_is_refused(self):
        # a nested function reads the containing frame through the static chain, where the frame analysis
        # cannot see it; inlined or never called, it is still in the unit's expand RTL
        block = ("    {\n        volatile u16 tmp = 0;\n"
                 "        func_0814186C((const void *)&tmp, dest, 0x01000100);\n    }\n")
        for label, inner in (
                ("a nested function reading the frame", "u8 later[2];\n        u8 peek(u32 i) { return later[i]; }\n"
                 "        dest[1] = peek(mode);"),
                ("an inline one", "u8 later[2];\n        inline u8 peek(u32 i) { return later[i]; }\n"
                 "        dest[1] = peek(mode);"),
                ("one never called", "u8 later[2];\n        u8 peek(u32 i) { return later[i]; }\n"
                 "        dest[1] = mode;"),
                ("one that reads no frame", "u32 twice(u32 i) { return i * 2; }\n        dest[1] = twice(mode);")):
            body = ("void func_08000400(u16 *dest, u32 mode)\n{\n" + block + "    {\n        " + inner +
                    "\n    }\n}\n")
            with self.subTest(label), self.assertRaisesRegex(proof.ProofError,
                                                             "the unit names the static chain register r9"):
                self.run_fill(body)
        # a file-scope helper is no nested function
        helper = "static u32 twice(u32 i) { return i * 2; }\n"
        unit = helper + BLOCK.replace("    }\n}\n", "    }\n    dest[1] = twice(dest[2]);\n}\n")
        self.assertEqual(self.states(unit), ["admitted"])


if __name__ == "__main__":
    unittest.main()
