import contextlib
import io
import json
import os
from pathlib import Path
import shlex
import shutil
import struct
import sys
import tempfile
import unittest
from hashlib import sha256
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import plausible
import volatile_rom_proof as proof

try:
    import capstone
except ImportError:
    capstone = None


def dump(function, insns):
    """an agbcc-shaped RTL dump of one function: insns are (uid, text after the links)"""
    lines = [f"\n;; Function {function}\n"]
    for index, (uid, rest) in enumerate(insns):
        before = insns[index - 1][0] if index else 0
        after = insns[index + 1][0] if index + 1 < len(insns) else 0
        kind, _, body = rest.partition(" ")
        lines.append(f"({kind} {uid} {before} {after} {body})\n")
    return "\n".join(lines)


def function(insns, name="func_08000400"):
    return proof.Function(proof.parse_dump(dump(name, insns))[name])


LOAD = 'insn (set (reg:SI 30) (mem/s/v:HI (reg/v:SI 22) 0)) -1 (nil) (nil)'
STORE = 'insn (set (mem/s/v:HI (reg/v:SI 22) 0) (reg:SI 23)) -1 (nil) (nil)'
ENTRY = 'insn (set (reg/v:SI 22) (reg:SI 0 r0)) -1 (nil) (nil)'


class DumpTests(unittest.TestCase):
    def test_forms_flags_and_commentary(self):
        text = dump("func_08000400", [(1, 'note "" NOTE_INSN_DELETED'), (2, ENTRY), (3, LOAD),
                                       (4, 'insn/i ' + STORE[5:])])
        text += ("\nInsn 84: giv reg 57 src reg 43 add (mult:SI (reg:SI 51)\n    (const_int 65536))\n"
                 "Loop from 65 to 530: 122 real insns.\n")
        fn = proof.Function(proof.parse_dump(text)["func_08000400"])
        self.assertEqual([i.uid for i in fn.insns], [1, 2, 3, 4])
        self.assertTrue(fn.insns[0].deleted)
        self.assertEqual([(i.uid, s) for i, _, s in fn.mems()], [(3, False), (4, True)])
        self.assertEqual(fn.users, [22])

    def test_a_missed_insn_breaks_the_chain(self):
        text = dump("func_08000400", [(2, ENTRY), (3, LOAD), (4, STORE)])
        broken = text.replace("(insn 3 2 4", " (insn 3 2 4")
        with self.assertRaisesRegex(proof.ProofError, "chain is broken"):
            proof.Function(proof.parse_dump(broken)["func_08000400"])

    def test_store_through_a_bit_field_and_call_targets(self):
        pattern = proof.parse_dump(dump("f", [(2, 'insn (set (zero_extract:SI (mem/v:QI (reg:SI 22) 0) '
                                                   '(const_int 4) (const_int 0)) (reg:SI 23)) -1 (nil) (nil)'),
                                              (3, 'call_insn (set (reg:SI 0 r0) (call (mem:SI (symbol_ref:SI '
                                                   '("func_X")) 0) (const_int 0))) -1 (nil) (nil) (nil)')]))["f"]
        fn = proof.Function(pattern)
        self.assertEqual([(i.uid, s, proof.rtl_mode(m)) for i, m, s in fn.mems()], [(2, True, "QI")])


class ResolverTests(unittest.TestCase):
    def address(self, insns, uid):
        fn = function(insns)
        insn = fn.by_uid[uid]
        mem = [m for m, _ in proof.walk_mems(insn.pattern, [])][0]
        return proof.Resolver(fn).address(insn, mem)

    POOL = ('insn (set (reg:SI 23) (mem/u:SI (symbol_ref:SI ("*.LC0")) 0)) -1 (nil) '
            '(expr_list:REG_EQUAL (symbol_ref:SI ("data_03000030")) (nil))')

    def test_constant_pool_symbol_and_offset(self):
        base, offset = self.address([(2, self.POOL), (3, 'insn (set (reg:SI 24) (mem/s/v:HI (plus:SI '
                                                          '(reg:SI 23) (const_int 4)) 0)) -1 (nil) (nil)')], 3)
        self.assertEqual((base, offset), (proof.Base("symbol", "data_03000030"), 4))

    def test_induction_variable_keeps_its_base(self):
        insns = [(2, self.POOL), (3, 'insn (set (reg/v:SI 25) (reg:SI 23)) -1 (nil) (nil)'),
                 (4, 'code_label 9 ""'),
                 (5, 'insn (set (mem/s/v:HI (reg/v:SI 25) 0) (reg:SI 26)) -1 (nil) (nil)'),
                 (6, 'insn (set (reg/v:SI 25) (plus:SI (reg/v:SI 25) (const_int 8))) -1 (nil) (nil)')]
        self.assertEqual(self.address(insns, 5), (proof.Base("symbol", "data_03000030"), None))

    def test_scaled_loaded_index_is_an_integer_but_a_loaded_word_is_not(self):
        index = ('insn (set (reg:SI 27) (mem:SI (symbol_ref:SI ("data_03000020")) 0)) -1 (nil) (nil)')
        scaled = [(2, self.POOL), (3, index),
                  (4, 'insn (set (reg:SI 28) (plus:SI (reg:SI 23) (mult:SI (reg:SI 27) (const_int 8)))) '
                      '-1 (nil) (nil)'),
                  (5, 'insn (set (mem/s/v:HI (reg:SI 28) 0) (reg:SI 26)) -1 (nil) (nil)')]
        self.assertEqual(self.address(scaled, 5), (proof.Base("symbol", "data_03000030"), None))
        plain = [scaled[0], scaled[1], (4, 'insn (set (reg:SI 28) (plus:SI (reg:SI 23) (reg:SI 27))) '
                                           '-1 (nil) (nil)'), scaled[3]]
        self.assertEqual(self.address(plain, 5)[0].kind, "unknown")
        parameter = [(1, 'insn (set (reg:SI 27) (reg:SI 1 r1)) -1 (nil) (nil)')] + scaled[:1] + scaled[2:]
        self.assertEqual(self.address(parameter, 5), (proof.Base("symbol", "data_03000030"), None))

    def test_parameters_results_frames_and_constants(self):
        self.assertEqual(self.address([(2, ENTRY), (3, LOAD)], 3)[0], proof.Base("param", 0))
        call = ('call_insn (set (reg:SI 0 r0) (call (mem:SI (symbol_ref:SI ("func_0800C614")) 0) '
                '(const_int 0))) -1 (nil) (nil) (nil)')
        result = [(2, call), (3, 'insn (set (reg/v:SI 22) (reg:SI 0 r0)) -1 (nil) (nil)'), (4, LOAD)]
        self.assertEqual(self.address(result, 4)[0], proof.Base("ret", "func_0800C614"))
        frame = [(2, 'insn (set (mem/v:HI (plus:SI (reg:SI 18) (const_int -2)) 0) (reg:SI 23)) -1 (nil) (nil)')]
        self.assertEqual(self.address(frame, 2)[0].kind, "frame")
        stack = [(2, 'insn (set (reg/v:SI 22) (mem/f:SI (plus:SI (reg:SI 17) (const_int 8)) 0)) -1 (nil) (nil)'),
                 (3, LOAD)]
        self.assertEqual(self.address(stack, 3)[0], proof.Base("param", 6))
        constant = [(2, 'insn (set (reg:SI 22) (const_int 67108868)) -1 (nil) (nil)'),
                    (3, 'insn (set (mem/v:HI (reg:SI 22) 0) (reg:SI 23)) -1 (nil) (nil)')]
        self.assertEqual(self.address(constant, 3), (proof.Base("fixed", 0x04000004), 0))

    def test_pointer_arithmetic_that_could_name_another_object_refuses(self):
        other = self.POOL.replace("*.LC0", "*.LC1").replace("data_03000030", "data_02000000").replace("23", "24")
        for expression in ("(minus:SI (reg:SI 24) (reg:SI 23))", "(mult:SI (reg:SI 24) (const_int 2))",
                           "(zero_extend:SI (subreg:HI (reg:SI 24) 0))", "(reg:SI 0 r0)"):
            with self.subTest(expression=expression):
                insns = [(2, self.POOL), (3, other),
                         (4, f'insn (set (reg:SI 28) (plus:SI (reg:SI 23) {expression})) -1 (nil) (nil)'),
                         (5, 'insn (set (mem/s/v:HI (reg:SI 28) 0) (reg:SI 26)) -1 (nil) (nil)')]
                self.assertEqual(self.address(insns, 5)[0].kind, "unknown")

    def test_a_narrowed_constant_loses_its_value(self):
        # (u32)(u16)0x04000004 + 0x03000000 is 0x03000004, not 0x07000004
        insns = [(2, 'insn (set (reg/v:SI 22) (const_int 67108868)) -1 (nil) (nil)'),
                 (3, 'insn (set (reg:SI 23) (zero_extend:SI (subreg:HI (reg/v:SI 22) 0))) -1 (nil) (nil)'),
                 (4, 'insn (set (reg:SI 24) (plus:SI (reg:SI 23) (const_int 50331648))) -1 (nil) (nil)'),
                 (5, 'insn (set (reg:SI 30) (mem/v:HI (reg:SI 24) 0)) -1 (nil) (nil)')]
        self.assertEqual(self.address(insns, 5), (proof.Base("fixed", 0x03000000), None))
        for head in ("sign_extend:SI", "truncate:HI"):
            narrowed = [insns[0], (3, insns[1][1].replace("zero_extend:SI", head))] + insns[2:]
            with self.subTest(head=head):
                self.assertEqual(self.address(narrowed, 5)[1], None)

    def test_two_integers_join_to_no_value(self):
        insns = [(2, 'insn (set (reg/v:SI 22) (const_int 67108868)) -1 (nil) (nil)'),
                 (3, 'code_label 9 ""'),
                 (4, 'insn (set (reg/v:SI 22) (const_int 50335744)) -1 (nil) (nil)'),
                 (5, 'insn (set (reg:SI 30) (mem/v:HI (reg/v:SI 22) 0)) -1 (nil) (nil)')]
        self.assertEqual(self.address(insns, 5)[0].kind, "unknown")

    def test_a_reassigned_argument_register_is_no_parameter(self):
        insns = [(2, 'insn (set (reg:SI 0 r0) (const_int 67108868)) -1 (nil) (nil)'),
                 (3, 'insn (set (reg/v:SI 22) (reg:SI 0 r0)) -1 (nil) (nil)'), (4, LOAD)]
        self.assertEqual(self.address(insns, 4)[0].kind, "unknown")

    def test_a_partial_definition_is_unknown(self):
        for target in ("(zero_extract:SI (reg/v:SI 22) (const_int 8) (const_int 24))",
                       "(strict_low_part (subreg:HI (reg/v:SI 22) 0))", "(subreg:HI (reg/v:SI 22) 0)"):
            insns = [(2, 'insn (set (reg/v:SI 22) (const_int 67108864)) -1 (nil) (nil)'),
                     (3, f'insn (set {target} (const_int 3)) -1 (nil) (nil)'), (4, LOAD)]
            with self.subTest(target=target):
                self.assertEqual(self.address(insns, 4)[0].kind, "unknown")

    def test_a_set_through_a_subreg_narrows(self):
        # a promoted variable's subreg and a paradoxical subreg define the whole register, narrowed
        index = ('insn (set (reg:SI 27) (mem:SI (symbol_ref:SI ("data_03000020")) 0)) -1 (nil) (nil)')
        for target in ("(subreg/s/u:HI (reg/v:SI 28) 0)", "(subreg/s:HI (reg/v:SI 28) 0)"):
            insns = [(2, ResolverTests.POOL), (3, index), (4, f'insn (set {target} (reg:SI 27)) -1 (nil) (nil)'),
                     (5, 'insn (set (reg:SI 29) (plus:SI (reg:SI 23) (reg/v:SI 28))) -1 (nil) (nil)'),
                     (6, 'insn (set (mem/s/v:HI (reg:SI 29) 0) (reg:SI 26)) -1 (nil) (nil)')]
            with self.subTest(target=target):
                self.assertEqual(self.address(insns, 6), (proof.Base("symbol", "data_03000030"), None))
        # a narrower subreg of a variable that is not promoted leaves the rest of the register as it was
        partial = [(2, ResolverTests.POOL), (3, index),
                   (4, 'insn (set (subreg:HI (reg/v:SI 28) 0) (reg:SI 27)) -1 (nil) (nil)'),
                   (5, 'insn (set (reg:SI 29) (plus:SI (reg:SI 23) (reg/v:SI 28))) -1 (nil) (nil)'),
                   (6, 'insn (set (mem/s/v:HI (reg:SI 29) 0) (reg:SI 26)) -1 (nil) (nil)')]
        self.assertEqual(self.address(partial, 6)[0].kind, "unknown")
        constant = [(2, 'insn (set (subreg:SI (reg:HI 28) 0) (const_int 67108868)) -1 (nil) (nil)'),
                    (3, 'insn (set (reg:SI 29) (zero_extend:SI (reg:HI 28))) -1 (nil) (nil)'),
                    (4, 'insn (set (reg:SI 30) (mem/v:HI (reg:SI 29) 0)) -1 (nil) (nil)')]
        self.assertEqual(self.address(constant, 4)[0].kind, "unknown")
        fn = function([(2, 'insn (set (subreg:SI (reg:HI 28) 0) (reg:SI 27)) -1 (nil) (nil)')])
        self.assertEqual(fn.defs[28][0][1], ["truncate:HI", ["reg:SI", "27"]])
        # a note's value is the subreg's, not the register's
        noted = [(2, 'insn (set (subreg/s/u:HI (reg/v:SI 28) 0) (reg:SI 27)) -1 (nil) '
                     '(expr_list:REG_EQUAL (const_int 67108868) (nil))'),
                 (3, 'insn (set (reg:SI 30) (mem/v:HI (reg/v:SI 28) 0)) -1 (nil) (nil)')]
        self.assertEqual(self.address(noted, 3)[0].kind, "unknown")

    def test_printing_has_no_depth_cap(self):
        chain = [(2, 'insn (set (reg:SI 22) (reg:SI 1 r1)) -1 (nil) (nil)')]
        for k in range(1, 40):
            chain.append((2 + k, f'insn (set (reg:SI {22 + k}) (plus:SI (reg:SI {21 + k}) (const_int {k}))) '
                                 '-1 (nil) (nil)'))
        fn = function(chain)
        printed = fn.name(["reg:SI", "61"])
        self.assertNotIn("T*", printed)
        self.assertEqual(printed.count("plus"), 39)
        deep = [(2, 'insn (set (reg:SI 22) (reg:SI 1 r1)) -1 (nil) (nil)')] + [
            (2 + k, f'insn (set (reg:SI {22 + k}) (neg:SI (reg:SI {21 + k}))) -1 (nil) (nil)') for k in range(1, 400)]
        with self.assertRaisesRegex(proof.ProofError, "too deep to print"):
            function(deep).name(["reg:SI", str(22 + 399)])
        cycle = function([(2, 'insn (set (reg:SI 22) (plus:SI (reg:SI 22) (const_int 1))) -1 (nil) (nil)')])
        with self.assertRaisesRegex(proof.ProofError, "defined through itself"):
            cycle.name(["reg:SI", "22"])

    def test_conflicting_bases_refuse(self):
        other = self.POOL.replace("*.LC0", "*.LC1").replace("data_03000030", "data_02000000").replace("23", "24")
        insns = [(2, self.POOL), (3, other), (4, 'insn (set (reg/v:SI 25) (reg:SI 23)) -1 (nil) (nil)'),
                 (5, 'insn (set (reg/v:SI 25) (reg:SI 24)) -1 (nil) (nil)'),
                 (6, 'insn (set (mem/s/v:HI (reg/v:SI 25) 0) (reg:SI 26)) -1 (nil) (nil)')]
        self.assertEqual(self.address(insns, 6)[0].kind, "unknown")
        self.assertEqual(self.address(insns[:3] + insns[4:], 6)[0], proof.Base("symbol", "data_03000030"))

    def test_a_variable_step_from_a_constant_has_no_offset(self):
        insns = [(2, 'insn (set (reg/v:SI 22) (const_int 134217728)) -1 (nil) (nil)'),
                 (3, 'insn (set (reg:SI 30) (mem/v:HI (reg/v:SI 22) 0)) -1 (nil) (nil)'),
                 (4, 'insn (set (reg/v:SI 22) (plus:SI (reg/v:SI 22) (reg:SI 29))) -1 (nil) (nil)'),
                 (5, 'insn (set (reg:SI 29) (ashift:SI (reg:SI 31) (const_int 1))) -1 (nil) (nil)'),
                 (6, 'insn (set (reg:SI 31) (zero_extend:SI (mem:HI (reg:SI 0 r0) 0))) -1 (nil) (nil)')]
        self.assertEqual(self.address(insns, 3), (proof.Base("fixed", 0x08000000), None))


class ClaimTests(unittest.TestCase):
    def test_an_access_that_prints_like_another_reference_is_ambiguous(self):
        mine = (7, False, "HI", "[(plus T* T*)]", True, 0)
        other = (5, False, "HI", "[(plus T* T*)]", True, 0)
        third = (9, False, "HI", "[V1]", False, 0)
        self.assertTrue(proof.ambiguous([other, mine, third], [(mine, None)]))
        self.assertFalse(proof.ambiguous([mine, third], [(mine, None)]))
        self.assertFalse(proof.ambiguous([other, mine], [(mine, None), (other, None)]))
        self.assertTrue(proof.ambiguous([mine, (7, False, "HI", "[(plus T* T*)]", True, 1)], [(mine, None)]))

    def test_two_tokens_claiming_one_access_are_both_refused(self):
        verdicts = [("admitted", "a", {(7, 0)}), ("admitted", "b", {(7, 0), (8, 0)}), ("admitted", "c", {(9, 0)}),
                    ("refused", "why", set())]
        self.assertEqual(proof.settle(verdicts), [
            ("refused", "another qualifier claims the same access"),
            ("refused", "another qualifier claims the same access"), ("admitted", "c"), ("refused", "why")])


class FateTests(unittest.TestCase):
    def dumps(self, stages):
        return {name: function(insns) for name, insns in stages.items()}

    def test_each_pass_names_the_fate(self):
        start = [(2, ENTRY), (3, LOAD), (4, STORE)]
        deleted = [(2, ENTRY), (3, 'note "" NOTE_INSN_DELETED'), (4, STORE)]
        rewritten = [(2, ENTRY), (3, 'insn (set (reg:SI 30) (reg:SI 23)) -1 (nil) (nil)'), (4, STORE)]
        cases = {"cse": ("dropped", deleted), "flow": ("dropped", deleted), "combine": ("combined", deleted),
                 "greg": ("other", deleted), "gcse": ("merged", rewritten), "jump2": ("dropped", deleted)}
        for stage, (expected, after) in cases.items():
            with self.subTest(stage=stage):
                stages = {"rtl": start}
                for name in proof.PASSES[1:]:
                    stages[name] = after if proof.PASSES.index(name) >= proof.PASSES.index(stage) else start
                self.assertEqual(proof.fate(self.dumps(stages), 3, False, "HI", {2, 4}), (expected, stage))
        kept = {name: start for name in proof.PASSES}
        self.assertEqual(proof.fate(self.dumps(kept), 3, False, "HI", {2, 3, 4}), ("kept", "final"))
        self.assertEqual(proof.fate(self.dumps(kept), 3, False, "HI", {2, 4}), ("other", "final"))

    def test_a_deleted_reread_is_merged_and_a_dead_read_dropped(self):
        reread = [(2, ENTRY), (5, LOAD.replace("30", "31")), (3, LOAD), (4, STORE)]
        gone = [(2, ENTRY), (5, LOAD.replace("30", "31")), (3, 'note "" NOTE_INSN_DELETED'), (4, STORE)]
        stages = {"rtl": reread, **{name: gone for name in proof.PASSES[1:]}}
        self.assertEqual(proof.fate(self.dumps(stages), 3, False, "HI", set()), ("dropped", "jump"))
        stages = {"rtl": reread, "jump": reread, **{name: gone for name in proof.PASSES[2:]}}
        self.assertEqual(proof.fate(self.dumps(stages), 3, False, "HI", set()), ("merged", "cse"))
        label = [(2, ENTRY), (5, LOAD.replace("30", "31")), (6, 'code_label 9 ""'), (3, LOAD), (4, STORE)]
        stages = {"rtl": label, "jump": label, **{name: [i if i[0] != 3 else (3, 'note "" NOTE_INSN_DELETED')
                                                        for i in label] for name in proof.PASSES[2:]}}
        self.assertEqual(proof.fate(self.dumps(stages), 3, False, "HI", set()), ("dropped", "cse"))

    def test_loop_moves_or_drops(self):
        start = [(2, ENTRY), (3, LOAD), (4, STORE)]
        moved = [(2, ENTRY), (9, LOAD.replace("30", "40")), (3, 'note "" NOTE_INSN_DELETED'), (4, STORE)]
        stages = {name: start for name in proof.PASSES[:proof.PASSES.index("loop")]}
        stages.update({name: moved for name in proof.PASSES[proof.PASSES.index("loop"):]})
        self.assertEqual(proof.fate(self.dumps(stages), 3, False, "HI", set()), ("moved", "loop"))
        dropped = [(2, ENTRY), (3, 'note "" NOTE_INSN_DELETED'), (4, STORE)]
        stages.update({name: dropped for name in proof.PASSES[proof.PASSES.index("loop"):]})
        self.assertEqual(proof.fate(self.dumps(stages), 3, False, "HI", set()), ("dropped", "loop"))


def dma_code(object_word=0x03000030, control_high=0x84, register_offset=0, extra=b"", control_offset=8):
    """Thumb code at 0x08000100: r6 = object, r2 = DMA0SAD, str r6, [r2, #off]; r1 = high << 24; str r1, [r2, #8]"""
    code = struct.pack("<HHHHHH", 0x4E02, 0x4A03, 0x6016 | (register_offset // 4) << 6,
                       0x2100 | control_high, 0x0609, 0x6011 | (control_offset // 4) << 6)
    return extra + code, struct.pack("<II", object_word, 0x040000B0)


def rom_with(code, pool, size=0x1000):
    rom = bytearray(b"\xff" * size)
    rom[0x100:0x100 + len(code)] = code
    rom[0x100 + len(code):0x100 + len(code) + len(pool)] = pool
    return rom


def entry_for(code, **changes):
    entry = {"symbol": "data_03000030", "address": "0x03000030", "size": 2048, "kind": "dma-source",
             "start": "0x08000100", "end": f"{0x08000100 + len(code):#010x}", "sha256": sha256(code).hexdigest()}
    entry.update(changes)
    return entry


@unittest.skipUnless(capstone, "capstone required")
class EvidenceTests(unittest.TestCase):
    def test_dma_source_is_read_off_the_code(self):
        code, pool = dma_code()
        premise = proof.dma_evidence(bytes(rom_with(code, pool)), entry_for(code))
        self.assertIn("data_03000030 is a DMA0 source", premise)
        self.assertIn("08000104 stores it to DMA0SAD", premise)

    def test_refusals(self):
        code, pool = dma_code()
        rom = bytes(rom_with(code, pool))
        variants = {
            "changed": (rom, entry_for(code, sha256="0" * 64)),
            "no enable bit": (bytes(rom_with(*dma_code(control_high=0x04))), entry_for(dma_code(control_high=0x04)[0])),
            "another object": (bytes(rom_with(*dma_code(object_word=0x03001000))), entry_for(code)),
            "destination, not source": (bytes(rom_with(*dma_code(register_offset=4))),
                                        entry_for(dma_code(register_offset=4)[0])),
            "a target kind": (rom, entry_for(code, kind="dma-target")),
            "the enable stored to another register": (bytes(rom_with(*dma_code(control_offset=4))),
                                                      entry_for(dma_code(control_offset=4)[0])),
            "an unread kind": (rom, entry_for(code, kind="irq-shared")),
        }
        for label, (data, entry) in variants.items():
            with self.subTest(label=label), self.assertRaises(proof.ProofError):
                proof.dma_evidence(data, entry)
        backward = struct.pack("<H", 0xE7FE)    # b . (a backward branch)
        code2, pool2 = dma_code(extra=backward)
        with self.assertRaises(proof.ProofError):
            proof.dma_evidence(bytes(rom_with(code2, pool2)), entry_for(code2))


def encode_bl(at, target):
    offset = target - (at + 4)
    return struct.pack("<HH", 0xF000 | (offset >> 12) & 0x7FF, 0xF800 | (offset >> 1) & 0x7FF)


GETTER = 0x080D9B08


def getter_rom(at=GETTER, size=0x100000, first=None, second=None, task_data=None, payload=None):
    """a ROM holding a scanline payload getter at `at` and the two bodies it calls"""
    first = proof.TASK_DATA if first is None else first
    second = proof.PAYLOAD if second is None else second
    rom = bytearray(b"\xff" * size)
    body = struct.pack("<H", 0xB500) + encode_bl(at + 2, first) + struct.pack("<H", 0x6840) + \
        encode_bl(at + 8, second) + struct.pack("<HH", 0xBC02, 0x4708)
    rom[at - proof.BASE:at - proof.BASE + 16] = body
    for where, halves in ((proof.TASK_DATA, task_data or proof.TASK_DATA_BODY),
                          (proof.PAYLOAD, payload or proof.PAYLOAD_BODY)):
        rom[where - proof.BASE:where - proof.BASE + 2 * len(halves)] = struct.pack(f"<{len(halves)}H", *halves)
    return rom


def getter_entry(rom, at=GETTER, **changes):
    entry = {"symbol": f"func_{at:08X}", "address": f"{at:#010x}", "kind": proof.GETTER_KIND,
             "start": f"{at:#010x}", "end": f"{at + 16:#010x}",
             "sha256": sha256(bytes(rom[at - proof.BASE:at - proof.BASE + 16])).hexdigest()}
    entry.update(changes)
    return entry


def no_pipeline(rom):
    """stands for bg_affine_rows.scanline_pipeline, which needs the USA ROM"""


class GetterTests(unittest.TestCase):
    def test_bl_decoding(self):
        rom = bytearray(0x100)
        rom[0x10:0x14] = encode_bl(0x08000010, 0x08000400)
        rom[0x20:0x24] = encode_bl(0x08000020, 0x07FFF000)
        self.assertEqual(proof.decode_bl(rom, 0x08000010), 0x08000400)
        self.assertEqual(proof.decode_bl(rom, 0x08000020), 0x07FFF000)
        self.assertIsNone(proof.decode_bl(rom, 0x08000012))
        self.assertIsNone(proof.decode_bl(rom, 0x080000FE))
        compiled = (b"", 0x40, 0x20, [(0x48, 10, "func_X"), (0x50, 2, "func_X"), (0x60, 10, "func_Y")])
        rom[0x08:0x0C] = encode_bl(0x08000008, 0x08001000)
        self.assertEqual(proof.call_targets(compiled, 0x08000000, rom), {"func_X": {0x08001000}})

    def test_the_getter_is_read_off_its_code(self):
        rom = getter_rom()
        premise = proof.getter_evidence(bytes(rom), getter_entry(rom), no_pipeline)
        self.assertIn("func_080D9B08 returns a scanline task's payload", premise)
        self.assertIn("0800C614(*(u32 *)(08005BFC(task) + 4))", premise)

    def test_getter_refusals(self):
        rom = getter_rom()
        moved = bytearray(rom)
        moved[GETTER - proof.BASE + 14:GETTER - proof.BASE + 16] = struct.pack("<H", 0x4700)    # bx r0
        def failing(rom):
            raise ValueError("changed manager")
        variants = {
            "changed": (rom, getter_entry(rom, sha256="0" * 64), no_pipeline),
            "a range that is not the getter": (rom, getter_entry(rom, end=f"{GETTER + 18:#010x}", sha256=sha256(
                bytes(rom[GETTER - proof.BASE:GETTER - proof.BASE + 18])).hexdigest()), no_pipeline),
            "a range away from the address": (rom, getter_entry(rom, address=f"{GETTER + 2:#010x}"), no_pipeline),
            "another first callee": (getter_rom(first=proof.TASK_DATA + 4), None, no_pipeline),
            "another second callee": (getter_rom(second=proof.PAYLOAD + 4), None, no_pipeline),
            "another task data offset": (getter_rom(task_data=(0x301C, 0x4770)), None, no_pipeline),
            "a payload getter that reads another field": (getter_rom(payload=proof.PAYLOAD_BODY[:6] + (0x698A,) +
                                                                     proof.PAYLOAD_BODY[7:]), None, no_pipeline),
            "another return": (moved, None, no_pipeline),
            "the pipeline": (rom, getter_entry(rom), failing),
            "a ROM too short": (rom[:0xC000], getter_entry(rom), no_pipeline),
        }
        for label, (data, entry, pipeline) in variants.items():
            with self.subTest(label=label), self.assertRaises(proof.ProofError):
                proof.getter_evidence(bytes(data), entry or getter_entry(data), pipeline)

    def test_a_call_result_is_admitted_only_from_a_listed_getter_the_rom_calls(self):
        rom = bytes(getter_rom())
        entry = getter_entry(rom)
        name = entry["symbol"]
        task = {name: [(proof.Base("param", 0), 0)]}
        text, extent = proof.object_premise(proof.Base("ret", name), None, 1, False, {}, [entry], rom,
                                            calls={name: {GETTER}}, pipeline=no_pipeline, tasks=task)
        self.assertIn("returns a scanline task's payload", text)
        self.assertIn("argument (parameter r0) is a task whose data word +4 holds a scanline task", extent)
        for argument, reason in ((proof.Base("int", 0x03001000), "a constant"), (proof.Base("fixed", 0x03001000),
                                 "a constant"), (proof.Base("symbol", "data_03000030"), "the data symbol"),
                                 (proof.Base("frame", 18), "a local"), (proof.Base("ret", name), "a scanline payload"),
                                 (proof.Base("unknown"), "an unresolved value")):
            with self.subTest(argument=argument), self.assertRaisesRegex(proof.ProofError, reason):
                proof.object_premise(proof.Base("ret", name), 0, 1, False, {}, [entry], rom, calls={name: {GETTER}},
                                     pipeline=no_pipeline, tasks={name: [(proof.Base("param", 1), 0), (argument, 0)]})
        for argument, shown in ((proof.Base("word"), "a word loaded from memory"),
                                (proof.Base("ret", "func_080D9A24"), "the result of func_080D9A24"),
                                (proof.Base("param", 5), "stack parameter 1")):
            self.assertIn(f"argument ({shown})", proof.object_premise(
                proof.Base("ret", name), 0, 1, False, {}, [entry], rom, calls={name: {GETTER}}, pipeline=no_pipeline,
                tasks={name: [(argument, 0)]})[1])
        with self.assertRaisesRegex(proof.ProofError, "cannot be read"):
            proof.object_premise(proof.Base("ret", name), 0, 1, False, {}, [entry], rom, calls={name: {GETTER}},
                                 pipeline=no_pipeline, tasks={})
        self.assertIn("returns a scanline task's payload", proof.object_premise(
            proof.Base("ret", name), 0, 1, False, {}, [entry], rom, calls={name: {GETTER}}, pipeline=no_pipeline,
            tasks=task)[0])
        with self.assertRaisesRegex(proof.ProofError, "before the payload"):
            proof.object_premise(proof.Base("ret", name), -2, 1, False, {}, [entry], rom, calls={name: {GETTER}},
                                 pipeline=no_pipeline, tasks=task)
        for calls, reason in (({name: {GETTER + 16}}, "reaches"), ({name: {GETTER, None}}, "reaches"),
                              ({}, "reaches")):
            with self.subTest(calls=calls), self.assertRaisesRegex(proof.ProofError, reason):
                proof.object_premise(proof.Base("ret", name), 0, 1, False, {}, [entry], rom, calls=calls,
                                     pipeline=no_pipeline, tasks=task)
        for entries, reason in (([], "call result"), ([dict(entry, kind="dma-source")], "call result"),
                                ([entry, entry], "more than once")):
            with self.subTest(entries=len(entries)), self.assertRaisesRegex(proof.ProofError, reason):
                proof.object_premise(proof.Base("ret", name), 0, 1, False, {}, entries, rom, calls={name: {GETTER}},
                                     pipeline=no_pipeline)
        # a getter entry vouches for no data symbol of the same name
        with self.assertRaisesRegex(proof.ProofError, "does not size"):
            proof.object_premise(proof.Base("symbol", name), None, 1, False, {name: "0x03000000"}, [entry], rom)

    def test_a_call_s_argument_is_read_in_its_block(self):
        call = (9, 'call_insn (set (reg:SI 0 r0) (call (mem:SI (symbol_ref:SI ("func_080D9B08")) 0) '
                   '(const_int 0))) -1 (nil) (nil) (expr_list (use (reg:SI 0 r0)) (nil))')
        entry = (2, 'insn (set (reg/v:SI 22) (reg:SI 0 r0)) -1 (nil) (nil)')
        argument = (3, 'insn (set (reg:SI 0 r0) (reg/v:SI 22)) -1 (nil) (nil)')
        self.assertEqual(proof.call_arguments(function([entry, argument, call]), "func_080D9B08"),
                         [(proof.Base("param", 0), 0)])
        pool = [(2, 'insn (set (reg:SI 30) (mem/u:SI (symbol_ref/u:SI ("*.LC0")) 0)) -1 (nil) (nil)'),
                (3, 'insn (set (reg:SI 0 r0) (reg:SI 30)) -1 (nil) (nil)'), call]
        self.assertEqual(proof.call_arguments(function(pool), "func_080D9B08"), [(proof.Base("int"), None)])
        for label, insns in (("a label", [entry, argument, (4, 'code_label 7 ""'), call]),
                             ("a call", [entry, argument, (4, call[1].replace("func_080D9B08", "func_X")), call]),
                             ("no setting", [call])):
            with self.subTest(label=label), self.assertRaisesRegex(proof.ProofError, "not set"):
                proof.call_arguments(function(insns), "func_080D9B08")

    def test_a_getter_s_argument_is_taken_only_as_a_plain_value(self):
        call = (9, 'call_insn (set (reg:SI 0 r0) (call (mem:SI (symbol_ref:SI ("func_080D9B08")) 0) '
                   '(const_int 0))) -1 (nil) (nil) (expr_list (use (reg:SI 0 r0)) (nil))')
        other = (5, 'call_insn (set (reg:SI 0 r0) (call (mem:SI (symbol_ref:SI ("func_08000900")) 0) '
                    '(const_int 0))) -1 (nil) (nil) (expr_list (use (reg:SI 0 r0)) (nil))')
        entry = (2, 'insn (set (reg/v:SI 22) (reg:SI 0 r0)) -1 (nil) (nil)')
        second = (3, 'insn (set (reg/v:SI 23) (reg:SI 1 r1)) -1 (nil) (nil)')

        def argument(*insns):
            (result,) = proof.call_arguments(function(list(insns)), "func_080D9B08")
            return result

        def to_r0(uid, source):
            return (uid, f'insn (set (reg:SI 0 r0) {source}) -1 (nil) (nil)')

        # plain: a parameter's copy, a full word loaded from memory, another call's result
        self.assertEqual(argument(entry, to_r0(8, "(reg/v:SI 22)"), call), (proof.Base("param", 0), 0))
        loaded = (4, 'insn (set (reg:SI 30) (mem:SI (plus:SI (reg/v:SI 22) (const_int 4)) 0)) -1 (nil) (nil)')
        self.assertEqual(argument(entry, loaded, to_r0(8, "(reg:SI 30)"), call)[0].kind, "word")
        result = (6, 'insn (set (reg:SI 31) (reg:SI 0 r0)) -1 (nil) (nil)')
        self.assertEqual(argument(other, result, to_r0(8, "(reg:SI 31)"), call)[0], proof.Base("ret", "func_08000900"))
        # not plain: arithmetic on a parameter, a value set on two paths, a narrower load
        for label, insns, what in (
                ("a constant plus a parameter",
                 (entry, second, (4, 'insn (set (reg:SI 30) (plus:SI (reg/v:SI 23) (const_int 50335744))) -1 (nil) '
                                     '(nil)'), to_r0(8, "(reg:SI 30)"), call), "a computed value (plus)"),
                ("a join", (entry, second, (4, 'insn (set (reg:SI 30) (reg/v:SI 22)) -1 (nil) (nil)'),
                            (5, 'insn (set (reg:SI 30) (const_int 50335744)) -1 (nil) (nil)'),
                            to_r0(8, "(reg:SI 30)"), call), "a value set in more than one place")):
            with self.subTest(label=label):
                base, offset = argument(*insns)
                self.assertEqual((base, offset), (proof.Base("computed", what), None))
                with self.assertRaisesRegex(proof.ProofError, "only a parameter, a call result or a word"):
                    proof.task_argument(base, {"func_080D9B08"})
        halfword = (4, 'insn (set (reg:SI 30) (zero_extend:SI (mem:HI (reg/v:SI 22) 0))) -1 (nil) (nil)')
        self.assertEqual(argument(entry, halfword, to_r0(8, "(reg:SI 30)"), call)[0].kind, "int")

    def test_listed_getters_have_the_shape_the_rule_reads(self):
        getters = [entry for entry in proof.load_objects() if entry["kind"] == proof.GETTER_KIND]
        self.assertEqual({entry["symbol"] for entry in getters}, {"func_080D9B08", "func_080DABB4"})
        for entry in getters:
            at = int(entry["address"], 16)
            with self.subTest(getter=entry["symbol"]):
                self.assertEqual(proof.getter_evidence(bytes(getter_rom(at)), entry, no_pipeline).split(":")[0],
                                 f"{entry['symbol']} returns a scanline task's payload")


class ObjectTests(unittest.TestCase):
    symbols = {"REG_DISPCNT": "0x04000000", "data_03000030": "0x03000030", "rom_data": "0x08100000"}

    def premise(self, base, offset, width=2, stores=False, entries=(), rom=b""):
        return proof.object_premise(base, offset, width, stores, self.symbols, list(entries), rom)

    def test_windows_and_their_edges(self):
        self.assertIn("I/O registers at 0x040003fe", self.premise(proof.Base("fixed", 0x04000000), 0x3FE)[0])
        self.assertIn("OAM", self.premise(proof.Base("fixed", 0x07000000), 8)[0])
        self.assertIn("VRAM", self.premise(proof.Base("fixed", 0x06017FFC), 0, 4)[0])
        for base, offset, width in ((0x04000000, 0x3FF, 2), (0x06018000, 0, 2), (0x03000000, 0, 1),
                                    (0x02000000, 0, 4), (0x0E010000, 0, 1)):
            with self.subTest(address=hex(base + offset)), self.assertRaises(proof.ProofError):
                self.premise(proof.Base("fixed", base), offset, width)
        self.assertIn("(REG_DISPCNT) at 0x04000000", self.premise(proof.Base("symbol", "REG_DISPCNT"), 0)[0])

    def test_cartridge_bus_needs_a_store(self):
        self.assertIn("cartridge bus", self.premise(proof.Base("fixed", 0x08000000), 0, stores=True)[0])
        with self.assertRaisesRegex(proof.ProofError, "never writes"):
            self.premise(proof.Base("fixed", 0x08000000), 0)
        with self.assertRaisesRegex(proof.ProofError, "never writes"):
            self.premise(proof.Base("symbol", "rom_data"), 0)

    def test_unbounded_and_untraced_bases(self):
        for base, offset, reason in ((proof.Base("fixed", 0x04000000), None, "nothing bounds it"),
                                     (proof.Base("symbol", "REG_DISPCNT"), None, "does not size"),
                                     (proof.Base("symbol", "unmapped"), 0, "not mapped"),
                                     (proof.Base("param", 0), None, "parameter"),
                                     (proof.Base("ret", "func_0800C614"), 0, "call result"),
                                     (proof.Base("frame", 18), None, "local"),
                                     (proof.Base("unknown"), None, "unresolved")):
            with self.subTest(base=base), self.assertRaisesRegex(proof.ProofError, reason):
                self.premise(base, offset)
        typed = lambda base: "the payload" if base == proof.Base("param", 3) else None
        self.assertEqual(proof.object_premise(proof.Base("param", 3), None, 1, False, {}, [], b"", typed),
                         ("the payload", None))
        with self.assertRaises(proof.ProofError):
            proof.object_premise(proof.Base("param", 2), None, 1, False, {}, [], b"", typed)

    @unittest.skipUnless(capstone, "capstone required")
    def test_listed_object(self):
        code, pool = dma_code()
        rom = bytes(rom_with(code, pool))
        entry = entry_for(code)
        text, extent = self.premise(proof.Base("symbol", "data_03000030"), None, entries=[entry], rom=rom)
        self.assertIn("DMA0 source", text)
        self.assertIn("variable offsets stay inside data_03000030's 2048 bytes", extent)
        self.assertEqual(self.premise(proof.Base("symbol", "data_03000030"), 2046, entries=[entry], rom=rom)[1], None)
        with self.assertRaisesRegex(proof.ProofError, "outside its listed"):
            self.premise(proof.Base("symbol", "data_03000030"), 2047, entries=[entry], rom=rom)
        with self.assertRaisesRegex(proof.ProofError, "another address"):
            self.premise(proof.Base("symbol", "data_03000030"), 0, entries=[dict(entry, address="0x03000040")],
                         rom=rom)


class SourceTests(unittest.TestCase):
    def test_candidates(self):
        text = ("/* volatile */\n#define V volatile\nvolatile u16 *r;\nstatic volatile u8 x;\n")
        self.assertIsNone(proof.candidate_offsets(text, set()))
        text = "/* volatile */\nvolatile u16 *r;\nstatic volatile u8 x;\n"
        offsets = proof.candidate_offsets(text, set())
        self.assertEqual([text[o:o + 8] for o in offsets], ["volatile", "volatile"])
        self.assertEqual(proof.candidate_offsets(text, {offsets[0]}), offsets[1:])
        self.assertIsNone(proof.candidate_offsets("__volatile__ int x;", set()))

    def test_unsupported_spellings(self):
        for text in ("a \\\n b", "??=", "%:define", "<: :>", "<% %>", "x\0", "x\r\n"):
            self.assertTrue(proof.unsupported_text(text), text)
        self.assertFalse(proof.unsupported_text("volatile u16 *r = (u16 *)0x04000000; /* a < b */"))

    def census(self, marked):
        """Unit's census with cpp replaced: marked(text) is what the marked copy preprocesses to"""
        source = "volatile int x;\n"
        with tempfile.TemporaryDirectory() as root, tempfile.TemporaryDirectory() as work:
            (Path(root) / "src").mkdir()
            (Path(root) / "src" / "08000400.c").write_text(source)

            def run(command, cwd):
                text = (Path(cwd) / "src" / "08000400.c").read_text()
                text = text if Path(cwd).resolve() == Path(root).resolve() else marked(text)
                Path(shlex.split(command)[-1]).write_text('# 1 "src/08000400.c"\n' + text)
                return ""
            with mock.patch.object(proof, "run", run):
                return proof.Unit(root, "src/08000400.c", source, [0], work)

    def test_the_census_holds_the_variants_exact(self):
        self.assertEqual(self.census(lambda text: text).real, '# 1 "src/08000400.c"\nvolatile int x;\n')
        with self.assertRaisesRegex(proof.ProofError, "changes when only its candidate qualifiers are renamed"):
            self.census(lambda text: text + "int y;\n")
        with self.assertRaisesRegex(proof.ProofError, "does not reach the unit exactly once"):
            self.census(lambda text: "volatile int x;\n")
        with self.assertRaisesRegex(proof.ProofError, "does not reach the unit exactly once"):
            self.census(lambda text: text + text)

    def test_more_candidates_than_the_limit_refuse(self):
        text = "".join(f"volatile int x{k};\n" for k in range(proof.MAX_CANDIDATES + 1))
        with self.assertRaisesRegex(proof.ProofError, "more than 8 candidate"):
            proof.prove("/nonexistent", "/nonexistent", "src/08000400.c", text, set(), {}, [], b"")

    def test_only_an_addressed_source_is_proved(self):
        for relpath in ("include/08000400.h", "src/08000400.h", "src/func.c", None):
            with self.subTest(relpath=relpath):
                self.assertIsNone(proof.prove("/nonexistent", "/nonexistent", relpath, "volatile int x;\n", set(),
                                              {}, [], b""))

    def test_the_allow_list_is_an_exception_before_the_proof(self):
        entry, = plausible.volatile_allow_entries()
        declaration = entry["declaration"] + "\n"
        offsets = plausible.exempt_qualifiers(declaration, entry["header"], {entry["symbol"]: entry["address"]},
                                              None, None, None)
        self.assertEqual(offsets, {k for k in range(len(declaration)) if declaration.startswith("volatile", k)})

    def test_listing_and_rom_access(self):
        listing = ("  15              \t@ 0x0000\n"
                   "  16 000a 89B0     \t\tadd\tsp, sp, #-36\t@ 986\taddsi3/7\t[length = 2]\n"
                   "  17 000c 1888     \t\tmov\tr1, #24\t@ 977\t*extendhisi2_insn\t[length = 4]\n"
                   "  18 000e 795E     \t\tldrsh\tr3, [r7, r1]\n"
                   "  19              \t.L3:\n"
                   "  20 0010 0880     \t\tstrh\tr0, [r1]\t@ 12\t*movhi_insn/2\t[length = 2]\n")
        uids = proof.listing_uids(listing)
        self.assertEqual(uids[986], [(0x0A, "add\tsp, sp, #-36")])
        # a label ends an insn's lines: what follows it untagged is no part of the insn before
        labelled = listing.replace("  20 0010 0880     \t\tstrh\tr0, [r1]\t@ 12\t*movhi_insn/2\t[length = 2]\n",
                                   "  20 0010 0880     \t\tstrh\tr0, [r1]\n")
        self.assertEqual([at for at, _ in proof.listing_uids(labelled)[977]], [0x0C, 0x0E])
        self.assertEqual([at for at, _ in uids[977]], [0x0C, 0x0E])
        self.assertEqual([at for at, _ in uids[12]], [0x10])
        rom = bytearray(b"\0" * 0x40)
        rom[0x10:0x16] = struct.pack("<HHH", 0x8808, 0x7008, 0x6808)   # ldrh, strb, ldr
        self.assertEqual(proof.rom_access(rom, 0x08000010, 2, False, 2), 0x08000010)
        self.assertEqual(proof.rom_access(rom, 0x08000010, 4, True, 1), 0x08000012)
        self.assertIsNone(proof.rom_access(rom, 0x08000010, 6, True, 2))

    def test_cli_ignores_a_qualifier_outside_the_code(self):
        # as record() and plausible.py: no candidate, even in a unit the proof never reads
        source = "/* volatile */\n#define F(x) \\\n    (x)\nint func_08000400(void) { return 0; }\n"
        with tempfile.TemporaryDirectory() as root:
            (Path(root) / "src").mkdir()
            (Path(root) / "src" / "08000400.c").write_text(source)
            output = io.StringIO()
            with mock.patch.object(sys, "argv", ["volatile_rom_proof.py", "--root", root, "0x08000400"]), \
                    contextlib.redirect_stdout(output):
                self.assertEqual(proof.main(), 0)
            self.assertEqual(output.getvalue(), "no candidate qualifier\n")
            self.assertIsNone(proof.record(root, 0x08000400))

    def test_pinned_toolchain_is_match_py_s(self):
        import match
        self.assertEqual((proof.CC, proof.FLAGS, proof.AS), (match.DEFAULT_CC, match.DEFAULT_FLAGS, match.DEFAULT_AS))

    def test_registry_is_well_formed(self):
        entries = proof.load_objects()
        self.assertTrue(entries)
        keys = {"symbol", "address", "kind", "start", "end", "sha256", "reason"}
        for entry in entries:
            self.assertIn(entry["kind"], proof.DMA_KINDS + (proof.GETTER_KIND, proof.ALLOCATOR_KIND))
            self.assertEqual(set(entry), keys | ({"size"} if entry["kind"] in proof.DMA_KINDS else set()))


class PlausibleHookTests(unittest.TestCase):
    source = "typedef unsigned short u16;\nvoid func_08000400(void) { volatile u16 *r = (u16 *)0x04000004; (void)*r; }\n"

    def check(self, proved):
        original = proof.qualifier_offsets
        proof.qualifier_offsets = lambda text, *args: proved(text)
        try:
            return [rule for _, rule, _, _ in plausible.check_text(
                self.source, relpath="src/08000400.c", tree="/nonexistent", project="/nonexistent")]
        finally:
            proof.qualifier_offsets = original

    def test_only_proved_offsets_are_exempt(self):
        self.assertEqual(self.check(lambda text: {text.index("volatile")}), [])
        self.assertEqual(self.check(lambda text: set()), ["volatile"])
        self.assertEqual([rule for _, rule, _, _ in plausible.check_text(self.source)], ["volatile"])

    def test_a_proof_that_cannot_run_admits_nothing(self):
        self.assertEqual([rule for _, rule, _, _ in plausible.check_text(
            self.source, relpath="src/08000400.c", tree="/nonexistent", project="/nonexistent")], ["volatile"])

    def test_other_exceptions_are_not_candidates(self):
        seen = []
        original = proof.qualifier_offsets
        proof.qualifier_offsets = lambda text, tree, project, relpath, admitted, symbols: seen.append(admitted) or set()
        try:
            source = "/* plausible: I/O */\n*(volatile u16 *)0x04000000 = v;\n"
            plausible.check_text(source, relpath="src/08000400.c", tree="/x", project="/x")
        finally:
            proof.qualifier_offsets = original
        self.assertEqual(seen, [{source.index("volatile")}])

    def test_record_is_carried(self):
        original = proof.record
        proof.record = lambda root, address: "* allowlisted volatile ROM proof: x" if address == 0x08000400 else None
        try:
            with tempfile.TemporaryDirectory() as root:
                (Path(root) / "src").mkdir()
                self.assertEqual(plausible.allowlisted_volatile_uses(root, 0x08000400),
                                 ["* allowlisted volatile ROM proof: x"])
                self.assertEqual(plausible.allowlisted_volatile_uses(root, 0x08000402), [])
        finally:
            proof.record = original


def thumb(*halves):
    return struct.pack(f"<{len(halves)}H", *halves)


class CallerScanTests(unittest.TestCase):
    """the reference scan, the listing layout, the index and the callback flow, without a compiler"""

    def test_references_are_calls_branches_and_address_words(self):
        rom = bytearray(b"\xff" * 0x2000)
        rom[0x100:0x104] = encode_bl(0x08000100, 0x08000400)
        rom[0x600:0x604] = encode_bl(0x08000600, 0x08000400)
        rom[0x404:0x408] = encode_bl(0x08000404, 0x08000400)          # inside the function: still a call
        rom[0x3F0:0x3F2] = thumb(0xE000 | ((0x08000400 - 0x080003F4) >> 1))   # b func
        rom[0x40E:0x410] = thumb(0xE000 | ((0x08000400 - 0x08000412) >> 1) & 0x7FF)  # inside: not a reference
        rom[0x700:0x704] = struct.pack("<I", 0x08000401)
        rom[0x803:0x807] = struct.pack("<I", 0x08000400)
        rom[0x900:0x904] = encode_bl(0x08000900, 0x08000404)                # a call of the body
        rom[0x430:0x432] = thumb(0xE000 | ((0x08000408 - 0x08000434) >> 1) & 0x7FF)   # a branch into the body
        rom[0xA01:0xA05] = struct.pack("<I", 0x0800041F)                    # a word holding a body address
        proof._BL_INDEX.clear()
        calls, inside, words = proof.rom_references(bytes(rom), 0x08000400, 0x08000420)
        self.assertEqual(calls, [0x08000100, 0x08000404, 0x08000600])
        self.assertEqual(inside, [(0x080003F0, 0x08000400), (0x08000430, 0x08000408), (0x08000803, 0x08000400),
                                  (0x08000900, 0x08000404), (0x08000A01, 0x0800041F)])
        self.assertEqual(words, [0x08000700])

    def test_every_pc_relative_load_of_a_word_is_found(self):
        rom = bytearray(b"\xff" * 0x3000)
        rom[0x100:0x102] = thumb(0x4800 | (0x08000110 - 0x08000104) // 4)    # ldr r0, [pc, #12]
        rom[0x10E:0x110] = thumb(0x4900)                                       # ldr r1, [pc, #0] reads 08000110
        rom[0x200:0x204] = struct.pack("<I", 0xE51F0000 | (0x08000208 - 0x08000110))   # ARM ldr r0, [pc, #-0xF8]
        rom[0x40:0x44] = struct.pack("<I", 0xE59F0000 | (0x08000110 - 0x08000048))     # ARM ldr r0, [pc, #0xC8]
        self.assertEqual(proof.pc_loads(bytes(rom), 0x08000110), [0x08000040, 0x08000100, 0x0800010E, 0x08000200])

    def test_listing_layout_and_index(self):
        listing = ("   9              \tfunc_08000400:\n"
                   "  10 0000 00B5     \t\tpush\t{lr}\n"
                   "  11              \t@ 0x0002\n"
                   "  12 0002 0148     \t\tldr\tr0, .L3\t@ 6\t*movsi_insn/6\t[length = 2]\n"
                   "  13              \t.L2:\n"
                   "  14 0004 0047     \t\tbx\tr0\n"
                   "  15 0006 C046     \t\t.align\t2, 0\n"
                   "  16              \t.L3:\n"
                   "  17 0008 01040008 \t\t.word\tfunc_08000400\n")
        self.assertEqual(proof.listing_layout(listing), ([0, 2, 4], {0, 4, 8}))
        with tempfile.TemporaryDirectory() as root:
            with self.assertRaisesRegex(proof.ProofError, "no function index"):
                proof.function_index(root)
            (Path(root) / "symbols").mkdir()
            (Path(root) / "symbols" / "functions.txt").write_text(
                "# FFTA - discovered functions (addr end size instrs)\n08000400 08000420    32  16 return\n")
            self.assertEqual(proof.function_index(root), [(0x08000400, 0x08000420)])

    def callers(self, rom, address=0x08000800, entries=()):
        return proof.Callers("/nonexistent", "/nonexistent", address, address + 0x40, bytes(rom), {}, list(entries),
                             no_pipeline, "/nonexistent")

    def flow(self, *halves, labels=(), at=0x08000100):
        """follow the pc-relative load that is the first halfword, through a straight line ending in a BL"""
        rom = bytearray(b"\xff" * 0x1000)
        rom[at - proof.BASE:at - proof.BASE + 2 * len(halves)] = thumb(*halves)
        instructions = [2 * k for k in range(len(halves))]
        return self.callers(rom).follow(instructions, set(labels), 0, at, 0, at, halves[0] >> 8 & 7)

    def call(self, after):
        """the halfwords of a BL to the allocator after `after` halfwords at 0x08000100"""
        return struct.unpack("<HH", encode_bl(0x08000100 + 2 * after, ALLOCATOR))

    def test_a_callback_load_must_reach_r0_of_a_call(self):
        site = (0x08000106, ALLOCATOR)
        self.assertEqual(self.flow(0x4801, 0x2104, 0x2202, *self.call(3)), site)                # ldr r0 directly
        self.assertEqual(self.flow(0x4B01, 0x1C18, 0x2304, *self.call(3)), site)                # adds r0, r3, #0
        self.assertEqual(self.flow(0x4B01, 0x0018, 0x2300, *self.call(3)), site)                # movs r0, r3
        self.assertEqual(self.flow(0x4B01, 0x1C18, 0x438A, 0x2300, *self.call(4))[1], ALLOCATOR)  # bics r2, r1
        for label, halves, labels, reason in (
                ("a branch target between", (0x4801, 0x2104, 0x2202, *self.call(3)), {4}, "branch target"),
                ("a spill", (0x4B01, 0x9300, 0x1C18, 0x2300, *self.call(4)), (), "otherwise"),
                ("a callee-saved copy", (0x4B01, 0x4698, 0x1C18, 0x2300, *self.call(4)), (), "not exactly r0"),
                ("a second argument", (0x4B01, 0x1C19, 0x2000, 0x2300, *self.call(4)), (), "not exactly r0"),
                ("a value kept in a fourth argument", (0x4B01, 0x1C18, 0x2104, *self.call(3)), (), "not exactly r0"),
                ("an exchange", (0x4B01, 0x4718, *self.call(2)), (), "control leaves"),
                ("a return", (0x4801, 0xBD00, *self.call(2)), (), "control leaves"),
                ("an interrupt", (0x4801, 0xDF0B, *self.call(2)), (), "control leaves"),
                ("a conditional branch", (0x4801, 0xD000, *self.call(2)), (), "control leaves"),
                ("overwritten", (0x4B01, 0x2300, *self.call(2)), (), "overwritten"),
                ("no call", (0x4801, 0x2104), (), "reaches no call")):
            with self.subTest(label=label), self.assertRaisesRegex(proof.ProofError, reason):
                self.flow(*halves, labels=labels)

    def argument(self, insns, uid=9, offset=6, callee="func_08000800"):
        """argument r0 at the call insn `uid`, listed at `offset`, of a caller whose expand dump is `insns`"""
        callers = self.callers(b"\xff" * 0x1000)
        callers.compiled[0x08000100] = {"dumps": {"rtl": {"func_08000100": function(insns, "func_08000100")}},
                                        "text": (b"", 0, 0x20, []), "uids": {uid: [(offset, "bl")]}}
        return callers.argument(0x08000100, 0x08000106, 0)

    CALL = ('call_insn (set (reg:SI 0 r0) (call (mem:SI (symbol_ref:SI ("{}")) 0) (const_int 0))) -1 (nil) (nil) '
            '(expr_list (use (reg:SI 0 r0)) (nil))')

    def test_every_call_in_the_source_reaches_its_own_bl(self):
        call = (9, self.CALL.format("func_08000800"))
        other = (12, self.CALL.format("func_08000800"))

        def reach(insns, uids, sites):
            callers = self.callers(b"\xff" * 0x1000)
            callers.compiled[0x08000100] = {"dumps": {"rtl": {"func_08000100": function(insns, "func_08000100")}},
                                            "text": (b"", 0, 0x20, []), "uids": uids}
            callers.calls_reach_code(0x08000100, set(sites))

        reach([call], {9: [(6, "bl")]}, {0x08000106})
        reach([call, other], {9: [(6, "bl")], 12: [(0x10, "bl")]}, {0x08000106, 0x08000110})
        for label, insns, uids, sites, reason in (
                ("a call listed at another instruction", [call], {9: [(8, "bl")]}, {0x08000106}, "reaches none"),
                ("a call listed nowhere", [call], {}, {0x08000106}, "reaches none"),
                ("two calls merged into one BL", [call, other], {9: [(6, "bl")]}, {0x08000106}, "reaches none"),
                ("two calls listed at one BL", [call, other], {9: [(6, "bl")], 12: [(6, "bl")]},
                 {0x08000106, 0x08000110}, "pair one to one"),
                ("a BL no call lists", [call], {9: [(6, "bl")]}, {0x08000106, 0x08000110}, "pair one to one")):
            with self.subTest(label=label), self.assertRaisesRegex(proof.ProofError, reason):
                reach(insns, uids, sites)

    def test_an_argument_is_read_in_the_call_s_block(self):
        setting = (2, 'insn (set (reg:SI 0 r0) (const_int 67108928)) -1 (nil) (nil)')
        call = (9, self.CALL.format("func_08000800"))
        self.assertEqual(self.argument([setting, call]), (proof.Base("fixed", 0x04000040), 0))
        # a narrowed constant is no address in a caller either
        narrowed = [(1, 'insn (set (reg:SI 30) (const_int 67108928)) -1 (nil) (nil)'),
                    (2, 'insn (set (reg:SI 0 r0) (zero_extend:SI (subreg:HI (reg:SI 30) 0))) -1 (nil) (nil)'), call]
        self.assertEqual(self.argument(narrowed)[0].kind, "unknown")
        noted = [(2, 'insn (set (subreg/s/u:HI (reg:SI 0 r0) 0) (reg:SI 27)) -1 (nil) '
                     '(expr_list:REG_EQUAL (const_int 67108928) (nil))'), call]
        self.assertEqual(self.argument(noted)[0].kind, "unknown")
        for label, insns, kwargs, reason in (
                ("across a label", [setting, (3, 'code_label 7 ""'), call], {}, "sets no r0 in the block"),
                ("across a call", [setting, (3, self.CALL.format("func_X")), call], {}, "sets no r0 in the block"),
                ("another callee", [setting, (9, self.CALL.format("func_X"))], {}, "does not name"),
                ("not listed there", [setting, call], {"offset": 8}, "not one call insn")):
            with self.subTest(label=label), self.assertRaisesRegex(proof.ProofError, reason):
                self.argument(insns, **kwargs)

    def registrar(self, *halves, relocated="func_08000800", word=0x08000110, entries=None):
        """the registration of func_08000800 by synthetic code at 08000100 whose literal is at `word`"""
        rom = bytearray(b"\xff" * 0x10000)
        rom[0x100:0x100 + 2 * len(halves)] = thumb(*halves)
        rom[word - proof.BASE:word - proof.BASE + 4] = struct.pack("<I", 0x08000801)
        callers = self.callers(rom, entries=[{"kind": proof.ALLOCATOR_KIND, "address": f"{ALLOCATOR:#010x}"}]
                               if entries is None else entries)
        callers.compiled[0x08000100] = {"text": (b"", 0, 0x14, [(word - 0x08000100, 2, relocated)]),
                                        "layout": ([2 * k for k in range(len(halves))], {0})}
        return callers.registration(0x08000100, word)

    def bl(self, at):
        return struct.unpack("<HH", encode_bl(at, ALLOCATOR))

    def test_a_registration_is_one_literal_load_to_one_allocator_call(self):
        once = (0x4803, *self.bl(0x08000102), 0x4770, 0x46C0)       # ldr r0, =func; bl alloc; bx lr
        site, entry = self.registrar(*once)
        self.assertEqual((site, entry["address"]), (0x08000102, f"{ALLOCATOR:#010x}"))
        for label, kwargs, halves, reason in (
                ("another literal", {"relocated": "func_08000900"}, once, "no literal of func_08000800"),
                ("an adr", {}, (0xA000, 0x4803, *self.bl(0x08000104), 0x4770), "forms a pc-relative address"),
                ("two calls", {}, (0x4803, *self.bl(0x08000102), 0x4802, *self.bl(0x08000108), 0x4770),
                 "passes the function to 2 calls"),
                ("no allocator", {"entries": []}, once, "no listed scanline callback allocator"),
                ("no load", {}, (0x4770, 0x46C0), "no instruction of func_08000100 loads")):
            with self.subTest(label=label), self.assertRaisesRegex(proof.ProofError, reason):
                self.registrar(*halves, **kwargs)

    def test_another_load_of_the_registration_word_refuses(self):
        rom_halves = (0x4803, *self.bl(0x08000102), 0x4770, 0x46C0)
        original = proof.pc_loads
        with mock.patch.object(proof, "pc_loads", lambda rom, word: original(rom, word) + [0x080000F0]):
            with self.assertRaisesRegex(proof.ProofError, "load at 080000F0 reads the word"):
                self.registrar(*rom_halves)

    def test_too_many_references_refuse(self):
        rom = bytearray(b"\xff" * 0x10000)
        for k in range(proof.MAX_CALLERS + 1):
            site = 0x08001000 + 8 * k
            rom[site - proof.BASE:site - proof.BASE + 4] = encode_bl(site, 0x08000800)
        proof._BL_INDEX.clear()
        with self.assertRaisesRegex(proof.ProofError, "more than 16 references"):
            self.callers(rom).scan()

    def test_stack_parameters_and_late_code(self):
        with self.assertRaisesRegex(proof.ProofError, "stack parameter 0: callers pass it on the stack"):
            self.callers(b"\xff" * 0x1000).premise(4, 0, 1, False)
        with self.assertRaisesRegex(proof.ProofError, "overlay map"):
            self.callers(b"\xff" * 0x1000, address=proof.CODE_END).premise(0, 0, 1, False)
        with self.assertRaisesRegex(proof.ProofError, "overlay map"):
            self.callers(b"\xff" * 0x1000, address=proof.CODE_END + 0x400).premise(5, 0, 1, False)

    @unittest.skipUnless(capstone, "capstone required")
    def test_allocator_evidence(self):
        rom = bytearray(b"\xff" * 0x10000)
        entry = {"symbol": "func_0800C3CC", "address": "0x0800C3CC", "kind": proof.ALLOCATOR_KIND,
                 "start": "0x0800C3CC", "end": "0x0800C4B4", "sha256": sha256(b"\xff" * 0xE8).hexdigest()}
        self.assertIn("stores its r0 as a new scanline task's callback", proof.allocator_evidence(rom, entry,
                                                                                               no_pipeline))
        def failing(rom):
            raise ValueError("changed manager")
        for label, changed, pipeline in (("changed", dict(entry, sha256="0" * 64), no_pipeline),
                                         ("moved", dict(entry, address="0x0800C3D0"), no_pipeline),
                                         ("too long", dict(entry, end="0x0800C6CC"), no_pipeline),
                                         ("the pipeline", entry, failing)):
            with self.subTest(label=label), self.assertRaises(proof.ProofError):
                proof.allocator_evidence(rom, changed, pipeline)

    def test_code_end_is_the_index_s(self):
        import analyze
        import status
        self.assertEqual(proof.CODE_END, analyze.CODE_END)
        self.assertEqual(proof.CODE_END, status.CODE_END)



COMPILER = Path(os.path.expandvars(proof.CC)).is_file() and shutil.which("cpp") and shutil.which(proof.AS)
ADDRESS = 0x08000400
TYPES = "typedef unsigned char u8;\ntypedef unsigned short u16;\n"


@unittest.skipUnless(COMPILER and capstone, "fixed compiler and capstone required")
class CompiledTests(unittest.TestCase):
    """the proof through agbcc, on a ROM built around each compiled function"""

    def run_proof(self, body, symbols=None, entries=(), spliced=True, calls=None):
        """calls maps a callee symbol to the address the ROM's BL reaches at each of its calls"""
        source = TYPES + body
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "src").mkdir()
            (root / "include").mkdir()
            (root / "src" / f"{ADDRESS:08X}.c").write_text(source)
            relpath = f"src/{ADDRESS:08X}.c"
            with tempfile.TemporaryDirectory(dir=root) as work:
                unit = proof.Unit(root, relpath, source, [], work)
                text, start, size, relocations = unit.compile("probe", unit.real, f"func_{ADDRESS:08X}")["text"]
            code, pool = dma_code()
            rom = getter_rom() if calls else rom_with(code, pool, 0x2000)
            if calls:
                rom[0x100:0x100 + len(code) + len(pool)] = code + pool
            if spliced:
                rom[ADDRESS - proof.BASE:ADDRESS - proof.BASE + size] = text[start:start + size]
                for at, kind, name in relocations if calls else ():
                    if kind == 10 and name in calls:
                        site = ADDRESS + at - start
                        rom[site - proof.BASE:site - proof.BASE + 4] = encode_bl(site, calls[name])
            listed = [entry_for(code)] if entries == "listed" else \
                [getter_entry(rom)] if entries == "getter" else list(entries)
            return proof.prove(root, root, relpath, source, set(), symbols or {}, listed, bytes(rom),
                               **({"pipeline": no_pipeline} if calls else {}))

    def verdicts(self, *args, **kwargs):
        return [state for _, (state, _) in self.run_proof(*args, **kwargs)]

    SHARED = ("typedef volatile struct { u16 a : 16; u16 b : 16; } Entry;\nextern Entry data_03000030[];\n"
              "void func_08000400(int i, u16 v) { data_03000030[i].a = v; data_03000030[i].b = v; }\n")

    def test_listed_dma_source_is_admitted(self):
        result = self.run_proof(self.SHARED, {"data_03000030": "0x03000030"}, "listed")
        (state, text), = [verdict for _, verdict in result]
        self.assertEqual(state, "admitted", text)
        self.assertIn("DMA0 source", text)
        self.assertIn("load dropped", text)
        self.assertIn("variable offsets stay inside data_03000030's 2048 bytes (assumed: the proof does not bound "
                      "them)", text)

    def test_unlisted_ram_and_unmatched_rom_are_refused(self):
        refused = self.run_proof(self.SHARED, {"data_03000030": "0x03000030"})
        self.assertIn("does not size", refused[0][1][1])
        constant = self.SHARED.replace("[i]", "[0]")
        refused = self.run_proof(constant, {"data_03000030": "0x03000030"})
        self.assertIn("no hardware window", refused[0][1][1])
        refused = self.run_proof(self.SHARED, {"data_03000030": "0x03000030"}, "listed", spliced=False)
        self.assertIn("not the ROM's", refused[0][1][1])

    def test_parameters_and_locals_are_refused(self):
        param = ("typedef volatile struct { u16 a : 16; } Entry;\n"
                 "void func_08000400(Entry *p, u16 v) { p->a = v; }\n")
        self.assertIn("parameter", self.run_proof(param)[0][1][1])
        local = "u16 func_08000400(u16 v) { volatile u16 t = v; return t; }\n"
        self.assertIn("local or frame", self.run_proof(local)[0][1][1])
        self.assertEqual(proof.align([(1, True, "HI", "a", True, 0)], []), [((1, True, "HI", "a", True, 0), None)])
        for ours, plain in (([(1, True, "HI", "a", False, 0)], []), ([], [(1, True, "HI", "a", False, 0)]),
                            ([(1, True, "HI", "a", False, 0)], [(1, True, "HI", "a", True, 0)])):
            with self.subTest(ours=ours, plain=plain), self.assertRaises(proof.ProofError):
                proof.align(ours, plain)

    def test_hardware_windows(self):
        dead_read = "void func_08000400(void) { volatile u16 *r = (u16 *)0x04000004; (void)*r; }\n"
        result = self.run_proof(dead_read)
        self.assertEqual(result[0][1][0], "admitted", result)
        self.assertIn("I/O registers at 0x04000004", result[0][1][1])
        plain_store = "void func_08000400(u16 v) { volatile u16 *r = (u16 *)0x04000004; *r = v; }\n"
        self.assertIn("none of its accesses (kept)", self.run_proof(plain_store)[0][1][1])
        narrowed = "u16 func_08000400(void) { return *(volatile u16 *)0x0E000000 & 0xFF; }\n"
        (state, reason), = [verdict for _, verdict in self.run_proof(narrowed)]
        self.assertEqual(state, "refused")
        self.assertIn("none of its accesses (combined in combine)", reason)

    def test_cartridge_bus(self):
        command = ("u16 func_08000400(void) { volatile u16 *f = (u16 *)0x08000000; *f = 0x90; return *f; }\n")
        result = self.run_proof(command)
        self.assertEqual(result[0][1][0], "admitted", result)
        self.assertIn("written by this function", result[0][1][1])
        self.assertIn("load merged", result[0][1][1])
        read = ("u16 func_08000400(void) { volatile u16 *f = (u16 *)0x08000000; u16 a = *f; return *f + a; }\n")
        self.assertIn("never writes", self.run_proof(read)[0][1][1])

    def test_dump_flags_must_not_change_the_code(self):
        source = TYPES + "void func_08000400(void) { (void)*(volatile u16 *)0x04000004; }\n"
        original = proof.elf_function
        seen = []

        def changed(data, name):
            text, start, size, relocations = original(data, name)
            seen.append(1)
            return (text, start, size + 2 * (len(seen) % 2 == 0), relocations)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "src").mkdir()
            (root / "src" / f"{ADDRESS:08X}.c").write_text(source)
            with tempfile.TemporaryDirectory(dir=root) as work, mock.patch.object(proof, "elf_function", changed):
                unit = proof.Unit(root, f"src/{ADDRESS:08X}.c", source, [], work)
                with self.assertRaisesRegex(proof.ProofError, "-da -dp changed"):
                    unit.compile("probe", unit.real, f"func_{ADDRESS:08X}")

    def test_another_function_with_a_volatile_reference_refuses(self):
        helper = ("static void __attribute__((noinline)) h(void) { (void)*(volatile u16 *)0x03001000; }\n"
                  "void func_08000400(void) { (void)*(volatile u16 *)0x04000004; h(); }\n")
        result = self.run_proof(helper)
        self.assertEqual([state for _, (state, _) in result], ["refused", "refused"], result)
        self.assertIn("holds a volatile reference too", result[1][1][1])

    def test_an_access_the_real_build_does_not_emit_is_no_evidence(self):
        # the plain build drops the unreachable read at expand, but the ROM cannot show that
        dead = ("void func_08000400(u16 v) { volatile u16 *r = (u16 *)0x04000004; int z = 0; "
                "if (z) (void)*r; *r = v; }\n")
        (state, reason), = [verdict for _, verdict in self.run_proof(dead)]
        self.assertEqual(state, "refused")
        self.assertIn("none of its accesses (not emitted, kept)", reason)

    def test_an_unemitted_store_writes_nothing(self):
        for body in ("int z = 0; if (z) *f = 0x90; (void)*f; return 0;", "(void)*f; return 0; *f = 0x90;"):
            source = f"u16 func_08000400(void) {{ volatile u16 *f = (u16 *)0x08001234; {body} }}\n"
            with self.subTest(body=body):
                (state, reason), = [verdict for _, verdict in self.run_proof(source)]
                self.assertEqual(state, "refused", reason)
                self.assertIn("never writes", reason)

    def test_a_narrowed_constant_is_no_address(self):
        for body in ("(void)*(volatile u16 *)((u32)(u16)a + 0x03000000);", "(void)*(volatile u16 *)(u32)(u16)a;",
                     "u8 b = a; (void)*(volatile u16 *)((u32)b + 0x03001000);"):
            source = f"typedef unsigned int u32;\nvoid func_08000400(void) {{ u32 a = 0x04000004; {body} }}\n"
            with self.subTest(body=body):
                (state, reason), = [verdict for _, verdict in self.run_proof(source)]
                self.assertEqual(state, "refused", reason)

    DEEP = ("typedef unsigned int u32;\nextern u16 data_03000030[];\n"
            "void func_08000400(int c) {\n"
            "    int a1 = c ^ 1, a2 = c ^ 2, a3 = c ^ 3, a4 = c ^ 4, a5 = c ^ 5, a6 = c ^ 6, a7 = c ^ 7, a8 = c ^ 8, "
            "a9 = c ^ 9, a10 = c ^ 10, a11 = c ^ 11, a12 = c ^ 12, a13 = c ^ 13, a14 = c ^ 14;\n"
            "    volatile u16 *q = data_03000030 + (c & 7);\n"
            "    volatile u16 *r = (u16 *)0x03001000;\n"
            "    (void)*(r + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 + a11 + a12 + a13 + a14);\n"
            "    (void)*(q + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 + a11 + a12 + a13 + a14);\n}\n")

    def test_deep_addresses_keep_their_own_object(self):
        # two deep addresses used to print alike, and the RAM token was given the listed object's access
        integers = self.DEEP.replace("volatile u16 *q = data_03000030 + (c & 7);",
                                     "u32 q = (u32)(data_03000030 + (c & 7));").replace(
            "volatile u16 *r = (u16 *)0x03001000;", "u32 r = 0x03001000;").replace(
            "(void)*(r + ", "(void)*(volatile u16 *)(r + ").replace("(void)*(q + ", "(void)*(volatile u16 *)(q + ")
        for label, source in (("pointers", self.DEEP), ("integers", integers)):
            with self.subTest(label=label):
                full = TYPES + source
                result = self.run_proof(source, {"data_03000030": "0x03000030"}, "listed")
                ram = 0
                for offset, (state, text) in result:
                    line = full.splitlines()[full.count("\n", 0, offset)]
                    if "*r = " in line or "(r + " in line:
                        ram += 1
                        self.assertEqual(state, "refused", text)
                    elif state == "admitted":
                        self.assertIn("data_03000030 is a DMA0 source", text)
                self.assertEqual(ram, 1)

    def test_a_reference_printing_like_another_is_ambiguous(self):
        # both conditional addresses print `T*`: the pairing could give the listed token the RAM read
        source = ("extern volatile u16 data_03000030[];\nvoid func_08000400(int c) {\n"
                  "    (void)*(volatile u16 *)(c ? 0x03001000 : 0x03001002);\n"
                  "    (void)*(c ? &data_03000030[1] : &data_03000030[2]);\n}\n")
        result = self.run_proof(source, {"data_03000030": "0x03000030"}, "listed")
        self.assertEqual([state for _, (state, _) in result], ["refused", "refused"], result)
        self.assertIn("ambiguous", result[1][1][1])

    def test_a_kept_access_that_changes_no_code_is_refused_first(self):
        same = "u16 func_08000400(void) { return *(volatile u16 *)0x04000004; }\n"
        self.assertIn("removing it does not change the code", self.run_proof(same)[0][1][1])

    PAYLOAD = ("typedef volatile struct { u16 a : 16; u16 b : 16; } Entry;\nextern Entry *func_080D9B08(void *task);\n"
               "void func_08000400(void *task, int i, u16 v) { Entry *e = func_080D9B08(task); e[i].a = v; "
               "e[i].b = v; }\n")

    def test_a_listed_getter_s_payload_is_admitted(self):
        result = self.run_proof(self.PAYLOAD, entries="getter", calls={"func_080D9B08": GETTER})
        (state, text), = [verdict for _, verdict in result]
        self.assertEqual(state, "admitted", text)
        self.assertIn("func_080D9B08 returns a scanline task's payload", text)
        self.assertIn("premise: func_080D9B08's argument (parameter r0) is a task whose data word +4 holds a "
                      "scanline task", text)
        self.assertIn("load dropped", text)

    def test_a_getter_s_payload_needs_the_listed_call(self):
        refused = self.run_proof(self.PAYLOAD, entries="getter", calls={"func_080D9B08": GETTER + 16})
        self.assertIn("not every call of func_080D9B08", refused[0][1][1])
        refused = self.run_proof(self.PAYLOAD, calls={"func_080D9B08": GETTER})
        self.assertIn("a call result", refused[0][1][1])
        other = self.PAYLOAD.replace("func_080D9B08", "func_080D9B18")
        refused = self.run_proof(other, entries="getter", calls={"func_080D9B18": GETTER})
        self.assertIn("a call result", refused[0][1][1])

    def test_a_getter_s_argument_must_be_able_to_be_a_task(self):
        for task, reason in (("(void *)0x03001000", "a constant"), ("func_080D9B08(task)", "a scanline payload"),
                             ("&local", "no task"), ("data_03000040", "a constant"),
                             ("(void *)func_08000400", "a constant"),
                             ("(void *)(0x03001000 + i)", "a computed value"),
                             ("i ? task : (void *)0x03001000", "more than one place")):
            source = self.PAYLOAD.replace("Entry *e = func_080D9B08(task);",
                                          f"int local; Entry *e = func_080D9B08({task});").replace(
                "extern Entry *func_080D9B08(void *task);", "extern Entry *func_080D9B08(void *task);\n"
                "extern u8 data_03000040[];")
            with self.subTest(task=task):
                refused = self.run_proof(source, {"data_03000040": "0x03000040"}, entries="getter",
                                         calls={"func_080D9B08": GETTER})
                self.assertEqual(refused[0][1][0], "refused", refused)
                self.assertIn(reason, refused[0][1][1])
        loaded = self.PAYLOAD.replace("void *task, int i", "void **task, int i").replace("func_080D9B08(task)",
                                                                                        "func_080D9B08(*task)")
        result = self.run_proof(loaded, entries="getter", calls={"func_080D9B08": GETTER})
        self.assertEqual(result[0][1][0], "admitted", result)
        self.assertIn("argument (a word loaded from memory)", result[0][1][1])

    def test_each_qualifier_is_proved_on_its_own(self):
        both = ("u16 func_08000400(u16 v) { volatile u16 *f = (volatile u16 *)0x08000000; *f = 0x90; return *f; }\n")
        self.assertEqual(self.verdicts(both), ["admitted", "refused"])

    def test_plausible_admits_only_with_the_rom(self):
        # the tree's own baserom.bin, not a ROM the environment names
        self.enterContext(mock.patch.dict(os.environ))
        os.environ.pop("FFTA_ROM", None)
        source = TYPES + "void func_08000400(void) { volatile u16 *r = (u16 *)0x04000004; (void)*r; }\n"
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in ("src", "include", "config"):
                (root / name).mkdir()
            (root / "config" / "data_symbols.json").write_text("{}")
            path = root / "src" / f"{ADDRESS:08X}.c"
            path.write_text(source)
            self.assertEqual([rule for _, rule, _, _ in plausible.check_file(path)], ["volatile"])
            with tempfile.TemporaryDirectory(dir=root) as work:
                unit = proof.Unit(root, path.relative_to(root).as_posix(), source, [], work)
                text, start, size, _ = unit.compile("probe", unit.real, f"func_{ADDRESS:08X}")["text"]
            rom = bytearray(b"\xff" * 0x2000)
            rom[ADDRESS - proof.BASE:ADDRESS - proof.BASE + size] = text[start:start + size]
            (root / "baserom.bin").write_bytes(bytes(rom))
            proof._CACHE.clear()
            self.assertEqual(plausible.check_file(path), [])
            line = proof.record(root, ADDRESS)
            self.assertTrue(line.startswith(proof.RECORD + " `volatile-rom-proof-v1`"), line)
            self.assertIn("I/O registers at 0x04000004", line)
            self.assertEqual(plausible.allowlisted_volatile_uses(root, ADDRESS), [line])

    def test_plausible_and_the_record_keep_a_refused_token_out(self):
        # one token admitted, one refused: no mock between plausible.py and the proof
        self.enterContext(mock.patch.dict(os.environ))
        os.environ.pop("FFTA_ROM", None)
        source = TYPES + ("void func_08000400(u16 v) { volatile u16 *r = (u16 *)0x04000004; (void)*r; "
                          "*(volatile u16 *)0x04000008 = v; }\n")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in ("src", "include", "config"):
                (root / name).mkdir()
            (root / "config" / "data_symbols.json").write_text("{}")
            path = root / "src" / f"{ADDRESS:08X}.c"
            path.write_text(source)
            with tempfile.TemporaryDirectory(dir=root) as work:
                unit = proof.Unit(root, path.relative_to(root).as_posix(), source, [], work)
                text, start, size, _ = unit.compile("probe", unit.real, f"func_{ADDRESS:08X}")["text"]
            rom = bytearray(b"\xff" * 0x2000)
            rom[ADDRESS - proof.BASE:ADDRESS - proof.BASE + size] = text[start:start + size]
            (root / "baserom.bin").write_bytes(bytes(rom))
            proof._CACHE.clear()
            findings = plausible.check_file(path)
            self.assertEqual([rule for _, rule, _, _ in findings], ["volatile"])
            line = proof.record(root, ADDRESS)
            self.assertEqual(line.count(" | "), 0, line)
            self.assertIn("I/O registers at 0x04000004", line)
            self.assertNotIn("0x04000008", line)

    def test_a_cached_proof_follows_every_file_its_unit_reads(self):
        self.enterContext(mock.patch.dict(os.environ))
        os.environ.pop("FFTA_ROM", None)
        source = TYPES + '#include "port.inc"\nvoid func_08000400(void) { volatile u16 *r = (u16 *)PORT; (void)*r; }\n'
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in ("src", "include", "config"):
                (root / name).mkdir()
            (root / "config" / "data_symbols.json").write_text("{}")
            (root / "include" / "port.inc").write_text("#define PORT 0x04000004\n")
            path = root / "src" / f"{ADDRESS:08X}.c"
            path.write_text(source)
            with tempfile.TemporaryDirectory(dir=root) as work:
                unit = proof.Unit(root, path.relative_to(root).as_posix(), source, [], work)
                text, start, size, _ = unit.compile("probe", unit.real, f"func_{ADDRESS:08X}")["text"]
            rom = bytearray(b"\xff" * 0x2000)
            rom[ADDRESS - proof.BASE:ADDRESS - proof.BASE + size] = text[start:start + size]
            (root / "baserom.bin").write_bytes(bytes(rom))
            proof._CACHE.clear()
            relpath = path.relative_to(root).as_posix()
            self.assertEqual(len(proof.qualifier_offsets(source, root, root, relpath, set(), {})), 1)
            (root / "include" / "port.inc").write_text("#define PORT 0x02000004\n")
            self.assertEqual(proof.qualifier_offsets(source, root, root, relpath, set(), {}), set())


ALLOCATOR = 0x0800C3CC


@unittest.skipUnless(COMPILER and capstone, "fixed compiler and capstone required")
class CallerTests(unittest.TestCase):
    """caller tracing through agbcc: the addressed function and its callers compiled into a synthetic ROM"""

    CALLEE = ("typedef volatile struct { u16 a : 16; u16 b : 16; } Entry;\n"
              "void func_08000400(Entry *e, u16 v) { e->a = v; e->b = v; }\n")
    CALLER = ("extern void func_08000400(void *e, u16 v);\n"
              "void func_08000800(u16 v) { func_08000400((void *)0x04000040, v); }\n")
    EDGES = ("typedef struct __attribute__((packed)) { volatile u8 right : 8; volatile u8 left : 8; } Edges;\n"
             "void func_08000400(void *state, Edges *e) { e->left = 1; e->right = 2; }\n")
    REGISTRAR = ("extern void *func_0800C3CC(void (*callback)(void *, void *), u32 size, u32 type, u16 *destination);\n"
                 "extern void func_08000400(void *state, void *e);\n"
                 "void *func_08000800(void) { return func_0800C3CC(func_08000400, 4, 2, (u16 *)0x04000040); }\n")

    def build(self, root, sources, size=0x100000):
        """compile each source, splice it at its address, link its calls and function words; index them all"""
        rom = bytearray(b"\xff" * size)
        rows = []
        for address, body in sources.items():
            source = TYPES + "typedef unsigned int u32;\n" + body
            relpath = f"src/{address:08X}.c"
            (root / relpath).write_text(source)
            with tempfile.TemporaryDirectory(dir=root) as work:
                unit = proof.Unit(root, relpath, source, [], work)
                text, start, length, relocations = unit.compile("probe", unit.real, f"func_{address:08X}")["text"]
            rom[address - proof.BASE:address - proof.BASE + length] = text[start:start + length]
            for at, kind, name in relocations:
                site = address + at - start
                if kind == 10 and name.startswith("func_"):
                    rom[site - proof.BASE:site - proof.BASE + 4] = encode_bl(site, int(name[5:], 16))
                elif kind == 2 and name.startswith("func_"):
                    rom[site - proof.BASE:site - proof.BASE + 4] = struct.pack("<I", int(name[5:], 16) | 1)
            rows.append(f"{address:08X} {address + length:08X} {length:5d} 0 return")
        (root / "symbols").mkdir(exist_ok=True)
        (root / "symbols" / "functions.txt").write_text("# index\n" + "\n".join(sorted(rows)) + "\n")
        allocator = bytes(range(256))[:0xE8]
        rom[ALLOCATOR - proof.BASE:ALLOCATOR - proof.BASE + 0xE8] = allocator
        self.allocator = {"symbol": "func_0800C3CC", "address": f"{ALLOCATOR:#010x}", "kind": proof.ALLOCATOR_KIND,
                          "start": f"{ALLOCATOR:#010x}", "end": f"{ALLOCATOR + 0xE8:#010x}",
                          "sha256": sha256(allocator).hexdigest()}
        return rom

    def trace(self, sources, edit=None, entries=None, address=ADDRESS, size=0x100000):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in ("src", "include"):
                (root / name).mkdir()
            rom = self.build(root, sources, size)
            if edit:
                edit(root, rom)
            relpath = f"src/{address:08X}.c"
            text = (root / relpath).read_text()
            listed = [self.allocator] if entries is None else entries(self.allocator)
            proof._BL_INDEX.clear()
            return proof.prove(root, root, relpath, text, set(), {}, listed, bytes(rom), pipeline=no_pipeline)

    def test_a_parameter_every_caller_fills_with_hardware_is_admitted(self):
        result = self.trace({ADDRESS: self.CALLEE, 0x08000800: self.CALLER})
        (state, text), = [verdict for _, verdict in result]
        self.assertEqual(state, "admitted", text)
        self.assertIn("r0 of func_08000400, traced to the references a scan of the ROM finds (1 BL to its start, 0 "
                      "words holding its Thumb address", text)
        self.assertIn("no address of it is formed by arithmetic", text)
        self.assertIn("in func_08000800 passes I/O registers at 0x04000040", text)
        self.assertIn("premise: the code runs where it lies below 0x08150000", text)
        self.assertIn("load dropped", text)

    def test_every_caller_must_pass_an_object(self):
        two = {ADDRESS: self.CALLEE, 0x08000800: self.CALLER,
               0x08000C00: self.CALLER.replace("func_08000800", "func_08000C00").replace("0x04000040", "0x02000040")}
        self.assertIn("in no hardware window", self.trace(two)[0][1][1])
        own = {ADDRESS: self.CALLEE, 0x08000800: "extern void func_08000400(void *e, u16 v);\n"
                                                  "void func_08000800(void *e, u16 v) { func_08000400(e, v); }\n"}
        self.assertIn("own parameter", self.trace(own)[0][1][1])

    def test_a_traced_cartridge_address_needs_a_store_the_rom_holds(self):
        callee = ("void func_08000400(volatile u16 *f) { int z = 0; if (z) *f = 0x90; (void)*f; }\n")
        caller = ("extern void func_08000400(volatile u16 *f);\n"
                  "void func_08000800(void) { func_08000400((volatile u16 *)0x08001234); }\n")
        refused = self.trace({ADDRESS: callee, 0x08000800: caller})
        self.assertIn("never writes", refused[0][1][1])

    def test_unexplained_references_refuse(self):
        sources = {ADDRESS: self.CALLEE, 0x08000800: self.CALLER}

        def stray_word(root, rom):
            rom[0x9000:0x9004] = struct.pack("<I", ADDRESS | 1)

        def branch(root, rom):
            rom[0x3F0:0x3F2] = struct.pack("<H", 0xE000 | ((ADDRESS - 0x080003F4) >> 1))

        def branch_into_the_body(root, rom):
            rom[0x3F0:0x3F2] = struct.pack("<H", 0xE000 | ((ADDRESS + 4 - 0x080003F4) >> 1))

        def call_of_the_body(root, rom):
            rom[0x9000:0x9004] = encode_bl(0x08009000, ADDRESS + 4)

        def word_of_the_body(root, rom):
            rom[0x9000:0x9004] = struct.pack("<I", ADDRESS + 5)

        def unmatched(root, rom):
            (root / "src" / "08000800.c").unlink()

        def wrong(root, rom):
            rom[0x800:0x802] = b"\x00\x00"

        def another_callee(root, rom):
            caller = root / "src" / "08000800.c"
            caller.write_text(caller.read_text().replace("func_08000400", "func_08000500"))

        def overlapping(root, rom):
            index = root / "symbols" / "functions.txt"
            index.write_text(index.read_text() + "08000800 08000A00   512 256 return\n")

        for edit, reason in ((stray_word, "08009000 lies in 0 indexed functions"),
                             (branch, "080003F0 reaches or holds 08000400 inside the function"),
                             (branch_into_the_body, "080003F0 reaches or holds 08000404"),
                             (call_of_the_body, "08009000 reaches or holds 08000404"),
                             (word_of_the_body, "08009000 reaches or holds 08000405"), (unmatched, "no matched source"),
                             (wrong, "does not match the ROM"), (overlapping, "lies in 2 indexed functions"),
                             (another_callee, "is no call of func_08000400 in func_08000800's source")):
            with self.subTest(edit=edit.__name__):
                self.assertIn(reason, self.trace(sources, edit)[0][1][1])
        self.assertIn("no call of the function", self.trace({ADDRESS: self.CALLEE})[0][1][1])
        recursive = {ADDRESS: self.CALLEE.replace("e->b = v; }", "e->b = v; if (v) func_08000400("
                                                  "(Entry *)0x04000040, v - 1); }"),
                     0x08000800: self.CALLER}
        self.assertIn("lies in the function itself", self.trace(recursive)[0][1][1])

    def test_calls_a_later_pass_merged_refuse(self):
        # jump2 cross-jumps these calls into one BL: tracing that BL would read one argument for all of them
        for label, body in (
                ("a switch", "switch (c) { case 1: func_08000400((void *)0x04000040, v); break; "
                             "case 2: func_08000400((void *)0x04000044, v); break; "
                             "default: func_08000400((void *)0x03001000, v); }"),
                ("two branches", "if (c) func_08000400((void *)0x04000040, v); "
                                 "else func_08000400((void *)0x03001000, v);"),
                ("two branches swapped", "if (c) func_08000400((void *)0x03001000, v); "
                                         "else func_08000400((void *)0x04000040, v);")):
            caller = ("extern void func_08000400(void *e, u16 v);\n"
                      f"void func_08000800(int c, u16 v) {{ {body} }}\n")
            with self.subTest(label=label):
                (state, reason), = [verdict for _, verdict in self.trace({ADDRESS: self.CALLEE, 0x08000800: caller})]
                self.assertEqual(state, "refused", reason)

    def test_late_code_and_late_callers(self):
        late = proof.CODE_END + 0x400
        refused = self.trace({late: self.CALLEE.replace("func_08000400", f"func_{late:08X}"),
                              0x08000800: self.CALLER.replace("func_08000400", f"func_{late:08X}")},
                             address=late, size=0x160000)
        self.assertIn("overlay map", refused[0][1][1])
        refused = self.trace({ADDRESS: self.CALLEE,
                              late: self.CALLER.replace("func_08000800", f"func_{late:08X}")}, size=0x160000)
        self.assertIn("lies in late code", refused[0][1][1])

    def test_a_registered_scanline_callback_is_admitted(self):
        result = self.trace({ADDRESS: self.EDGES, 0x08000800: self.REGISTRAR})
        self.assertEqual([state for _, (state, _) in result], ["admitted", "admitted"], result)
        text = result[0][1][1]
        self.assertIn("(0 BL to its start, 1 words holding its Thumb address, each read only by its owner's pc-relative "
                      "loads; no branch, BL or word reaching inside it): it is a scanline callback, whose r1 is the "
                      "task's back bank", text)
        self.assertIn("registered by func_08000800 (word 080008", text)
        self.assertIn("a scanline task's callback is called only by the scanline manager 0800C4B4", text)
        payload = self.EDGES.replace("void *state, Edges *e", "Edges *e, void *state")
        result = self.trace({ADDRESS: payload, 0x08000800: self.REGISTRAR})
        self.assertIn("whose r0 is the task's payload (or 0)", result[0][1][1])
        before = self.EDGES.replace("e->left = 1; e->right = 2;", "e[-1].left = 1; e[-1].right = 2;")
        self.assertIn("lies before the object", self.trace({ADDRESS: before, 0x08000800: self.REGISTRAR})[0][1][1])
        third = self.EDGES.replace("void *state, Edges *e", "void *state, void *bank, Edges *e")
        refused = self.trace({ADDRESS: third, 0x08000800: self.REGISTRAR})
        self.assertIn("passes its callbacks no r2", refused[0][1][1])

    def test_a_registration_word_read_by_other_code_refuses(self):
        def foreign(root, rom):
            text = bytes(rom[0x800:0x900])
            word = 0x08000800 + text.index(struct.pack("<I", ADDRESS | 1))
            rom[0x780:0x784] = struct.pack("<HH", 0x4800 | (word - 0x08000784) // 4, 0x4700)   # ldr r0, =func; bx r0
            index = root / "symbols" / "functions.txt"
            index.write_text(index.read_text() + "08000780 08000784     4   2 return\n")
        refused = self.trace({ADDRESS: self.EDGES, 0x08000800: self.REGISTRAR}, foreign)
        self.assertIn("the pc-relative load at 08000780 reads the word", refused[0][1][1])

    def test_a_callback_registration_must_be_the_only_use(self):
        stored = self.REGISTRAR.replace("void *func_08000800(void) {",
                                        "extern void (*g_callback)(void *, void *);\n"
                                        "void *func_08000800(void) { g_callback = func_08000400;")
        self.assertIn("otherwise", self.trace({ADDRESS: self.EDGES, 0x08000800: stored})[0][1][1])
        second = ("extern void *func_0800C3CC(u32 size, void (*callback)(void *, void *));\n"
                  "extern void func_08000400(void *state, void *e);\n"
                  "void *func_08000800(void) { return func_0800C3CC(4, func_08000400); }\n")
        self.assertIn("not exactly r0", self.trace({ADDRESS: self.EDGES, 0x08000800: second})[0][1][1])
        for entries in (lambda allocator: [], lambda allocator: [dict(allocator, kind="dma-source")]):
            refused = self.trace({ADDRESS: self.EDGES, 0x08000800: self.REGISTRAR}, entries=entries)
            self.assertIn("no listed scanline callback allocator", refused[0][1][1])

    def test_a_cached_proof_follows_its_callers(self):
        self.enterContext(mock.patch.dict(os.environ))
        os.environ.pop("FFTA_ROM", None)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in ("src", "include", "config"):
                (root / name).mkdir()
            (root / "config" / "data_symbols.json").write_text("{}")
            rom = self.build(root, {ADDRESS: self.CALLEE, 0x08000800: self.CALLER})
            (root / "baserom.bin").write_bytes(bytes(rom))
            relpath = f"src/{ADDRESS:08X}.c"
            text = (root / relpath).read_text()
            proof._CACHE.clear()
            self.assertEqual(len(proof.qualifier_offsets(text, root, root, relpath, set(), {})), 1)
            caller = root / "src" / "08000800.c"
            caller.write_text(caller.read_text().replace("(void *)0x04000040", "(void *)0x02000040"))
            self.assertEqual(proof.qualifier_offsets(text, root, root, relpath, set(), {}), set())



@unittest.skipUnless(os.getenv("FFTA_WINDOW_SCANLINE_ROOT") and COMPILER and capstone,
                     "requires the USA ROM, the reviewed sources and native agbcc")
class WindowScanlineInstanceTests(unittest.TestCase):
    """window_scanline's seven writers pass the general proof once its caller-path evidence vouches for the payload"""

    def test_seven_writers(self):
        import window_scanline as window
        from rompath import rom_path
        root = Path(os.environ["FFTA_WINDOW_SCANLINE_ROOT"]).resolve()
        rom = Path(rom_path(root)).read_bytes()
        symbols = plausible.data_symbols_of(root)
        for address in window.OWNER_SHAPES:
            with self.subTest(address=hex(address)):
                path, = (root / "src").rglob(f"{address:08X}.c")
                relpath, text = path.relative_to(root).as_posix(), path.read_text()
                admitted = plausible.exempt_qualifiers(text, relpath, symbols, root, root,
                                                       plausible.include_closure(root, path))
                self.assertEqual(len(admitted), 2)
                # production never proves what window_scanline admits
                self.assertIsNone(proof.prove(root, root, relpath, text, admitted, symbols, rom=rom))

                def payload(base, address=address):
                    window.provider_evidence(rom, address)
                    return "the WINxH payload (window_scanline provider and caller-path evidence)"
                result = proof.prove(root, root, relpath, text, set(), symbols, rom=rom, typed=payload)
                self.assertEqual([state for _, (state, _) in result], ["admitted", "admitted"], result)
                if address == window.SHIFTED_ELLIPSE:
                    # its rows come from func_080DABB4, a listed scanline payload getter: no typed evidence
                    result = proof.prove(root, root, relpath, text, set(), symbols, rom=rom)
                    self.assertEqual([state for _, (state, _) in result], ["admitted", "admitted"], result)
                    self.assertIn("func_080DABB4 returns a scanline task's payload", result[0][1][1])


if __name__ == "__main__":
    unittest.main()
