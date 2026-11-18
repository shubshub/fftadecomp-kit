"""Stores into the owner's own pushed words are refused (kit #246).

`push` words hold callee-saved registers and the return address; only `sub sp`
words are allocated locals. A store through a tracked stack alias (STR, STRH,
STRB, STMIA) or a direct `str Rt, [sp, #imm]` must land in a word that is an
allocated local on every incoming path. Synthetic Thumb owners and callees are
assembled with the ARM binutils and walked as match.py's default owner path
walks them; no ROM is read.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import match

A = 0x08010000              # owner
CALLEE = 0x08010100         # first callee; each further callee is 0x100 higher
SAVED = "stack-alias store overlaps a saved register or return-address word"
DIRECT = "stack-frame store overlaps a saved register or return-address word"
# push {r4, lr}; sub sp, #8: sp+0 and sp+4 are locals, sp+8 the saved R4, sp+12 the saved LR.
PROLOGUE = "push {r4, lr}\nsub sp, #8\n"
EPILOGUE = "\nadd sp, #8\npop {r4}\npop {r1}\nbx r1"


def tools_present():
    return all(subprocess.run(["which", tool], capture_output=True).returncode == 0
               for tool in (match.DEFAULT_AS, match.DEFAULT_LD, match.DEFAULT_OBJCOPY))


@unittest.skipUnless(tools_present(), "ARM binutils required")
class SavedWordStoreTests(unittest.TestCase):
    def setUp(self):
        scratch = os.environ.get("FFTA_TEST_SCRATCH")
        if scratch:
            Path(scratch).mkdir(parents=True, exist_ok=True)
        self.temporary = tempfile.TemporaryDirectory(prefix="saved_word_stores_", dir=scratch)
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)

    def build(self, caller, callees=()):
        """Assemble the owner at A and each callee 0x100 apart from CALLEE."""
        names = ["caller"] + [f"callee{index}" for index in range(len(callees))]
        bodies = [caller] + list(callees)
        assembly = self.root / "fixture.s"
        assembly.write_text(".syntax unified\n.arch armv4t\n.thumb\n.text\n" +
                            "".join(f".global {name}, {name}_end\n" for name in names) +
                            "".join(f".org 0x{0x100 * index:x}\n{name}:\n{body}\n{name}_end:\n"
                                    for index, (name, body) in enumerate(zip(names, bodies))))
        for command in (
                [match.DEFAULT_AS, "-mthumb-interwork", str(assembly), "-o", str(self.root / "f.o")],
                [match.DEFAULT_LD, f"-Ttext=0x{A:08X}", "-e", "caller", str(self.root / "f.o"),
                 "-o", str(self.root / "f.elf")],
                [match.DEFAULT_OBJCOPY, "-O", "binary", "--only-section=.text",
                 str(self.root / "f.elf"), str(self.root / "f.bin")]):
            subprocess.run(command, check=True, capture_output=True)
        image = match.elf_image((self.root / "f.elf").read_bytes())
        symbols = {row["name"]: row["value"] for row in image["symbols"]}
        binary = (self.root / "f.bin").read_bytes()
        rom = bytes(A - match.ROM_BASE) + binary
        rows = [{"rom": f"0x{symbols[name]:08X}", "end": f"0x{symbols[name + '_end']:08X}",
                 "mode": "thumb"} for name in names]
        data = binary[:symbols["caller_end"] - A]
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        calls = {item.address: item.operands[0].imm for item in decoder.disasm(data, A)
                 if item.mnemonic == "bl"}
        return data, calls, rom, json.dumps(rows).encode()

    def verify(self, caller, callees=()):
        """match.py's default owner path: the v1 walk, then the stack-argument (v2) retry."""
        data, calls, rom, mapping = self.build(caller, callees)
        proof = match.BufferCallProof(rom, mapping if calls else None, loop_replay=True)
        try:
            match.verify_leaf_instructions(data, A, True, calls, buffer_proof=proof,
                                           incoming_narrow_reads=True)
        except ValueError:
            if not calls:
                raise
            proof = match.BufferCallProof(rom, mapping, stack_arguments=True, loop_replay=True)
            match.verify_leaf_instructions(data, A, True, calls, buffer_proof=proof,
                                           incoming_narrow_reads=True)
        return proof

    def refused(self, message, caller, callees=()):
        with self.assertRaisesRegex(ValueError, message):
            self.verify(caller, callees)

    def test_alias_stores_over_the_saved_r4_word(self):
        for store in ("add r3, sp, #8\nstr r0, [r3]",
                      "mov r3, sp\nstr r0, [r3, #8]",
                      "mov r3, sp\nstrh r0, [r3, #8]",
                      "mov r3, sp\nstrh r0, [r3, #10]",
                      "mov r3, sp\nstrb r0, [r3, #8]",
                      "mov r3, sp\nstrb r0, [r3, #9]",
                      "mov r3, sp\nstrb r0, [r3, #10]",
                      "mov r3, sp\nstrb r0, [r3, #11]",
                      "mov r3, sp\nmovs r2, #8\nstr r0, [r3, r2]",
                      "mov r3, sp\nmovs r2, #11\nstrb r0, [r3, r2]",
                      "mov r3, sp\nadds r3, #8\nstm r3!, {r0}",
                      "mov r3, sp\nadds r3, #4\nstm r3!, {r0, r1}"):
            with self.subTest(store=store):
                self.refused(SAVED, PROLOGUE + store + "\nmovs r3, #0" + EPILOGUE)

    def test_direct_stores_over_pushed_words(self):
        for store in ("str r0, [sp, #8]", "str r0, [sp, #12]", "mov r0, lr\nstr r0, [sp, #12]"):
            with self.subTest(store=store):
                self.refused(DIRECT, PROLOGUE + store + EPILOGUE)

    def test_every_saved_register_and_the_return_word(self):
        # push {r4-r7, lr}; sub sp, #8: R4-R7 at sp+8..sp+20, LR at sp+24.
        frame = "push {r4, r5, r6, r7, lr}\nsub sp, #8\n%s\nadd sp, #8\npop {r4, r5, r6, r7}\npop {r1}\nbx r1"
        for offset in (8, 12, 16, 20, 24):
            with self.subTest(offset=offset):
                self.refused(SAVED, frame % f"add r3, sp, #{offset}\nstr r0, [r3]\nmovs r3, #0")
                self.refused(DIRECT, frame % f"str r0, [sp, #{offset}]")

    def test_high_register_saved_through_a_low_one(self):
        # push {r7, lr}; mov r7, r8; push {r7}: sp+8 holds R8.
        self.refused(SAVED, "push {r7, lr}\nmov r7, r8\npush {r7}\nsub sp, #8\n"
                            "add r3, sp, #8\nstr r0, [r3]\nmovs r3, #0\nadd sp, #8\n"
                            "pop {r3}\nmov r8, r3\npop {r7}\npop {r1}\nbx r1")

    def test_entry_return_copies_are_refused_too(self):
        # Writing the entry LR itself, over the saved R4 or back over the saved LR.
        for offset in (8, 12):
            with self.subTest(offset=offset):
                self.refused(SAVED, PROLOGUE + f"mov r2, lr\nadd r3, sp, #{offset}\nstr r2, [r3]\n"
                                               "movs r3, #0" + EPILOGUE)

    def test_pushed_argument_words_fail_closed(self):
        # A varargs-style spill: the pushed R0-R3 words are not allocated locals either.
        frame = "push {r0, r1, r2, r3}\npush {lr}\nadd r3, sp, #8\n%s\npop {r3}\nadd sp, #16\nbx r3"
        self.refused(SAVED, frame % "str r0, [r3]")
        self.verify(frame % "ldr r0, [r3]")

    def test_allocated_local_words_still_take_stores(self):
        for store in ("add r3, sp, #4\nstr r0, [r3]",
                      "mov r3, sp\nstr r0, [r3]",
                      "mov r3, sp\nstrh r0, [r3, #6]",
                      "mov r3, sp\nstrb r0, [r3, #7]",
                      "mov r3, sp\nmovs r2, #7\nstrb r0, [r3, r2]",
                      "mov r3, sp\nstm r3!, {r0, r1}",
                      "str r0, [sp]",
                      "str r0, [sp, #4]",
                      "mov r0, lr\nstr r0, [sp, #4]\nldr r1, [sp, #4]"):
            with self.subTest(store=store):
                self.verify(PROLOGUE + store + "\nmovs r3, #0" + EPILOGUE)

    def test_return_address_spilled_to_a_local_word(self):
        # The entry LR in the local word sp+4 survives only while nothing else is stored there:
        # the return through it is still proved, and any later store there still loses it.
        frame = ("push {r4, lr}\nsub sp, #8\nmov r0, lr\nstr r0, [sp, #4]\n%s\nldr r2, [sp, #4]\n"
                 "add sp, #8\npop {r4}\nadd sp, #4\nbx r2")
        self.verify(frame % "")
        for store in ("str r1, [sp, #4]",
                      "mov r3, sp\nstr r1, [r3, #4]\nmovs r3, #0",
                      "mov r3, sp\nstrh r1, [r3, #4]\nmovs r3, #0",
                      "mov r3, sp\nstrb r1, [r3, #7]\nmovs r3, #0"):
            with self.subTest(store=store):
                self.refused("non-leaf indirect control flow requires linked CFG verification", frame % store)

    def test_reads_of_pushed_words_are_unchanged(self):
        for load in ("ldr r0, [sp, #8]", "ldr r0, [sp, #12]",
                     "add r3, sp, #8\nldr r0, [r3]\nmovs r3, #0",
                     "mov r3, sp\nldrh r0, [r3, #10]\nmovs r3, #0",
                     "add r3, sp, #12\nldm r3!, {r0}\nmovs r3, #0"):
            with self.subTest(load=load):
                self.verify(PROLOGUE + load + EPILOGUE)

    def test_incoming_words_keep_their_refusals(self):
        self.refused("stack-alias access is unaligned or outside the tracked frame",
                     PROLOGUE + "add r3, sp, #16\nstr r0, [r3]\nmovs r3, #0" + EPILOGUE)
        self.refused("stack-frame write is outside the tracked frame",
                     PROLOGUE + "str r0, [sp, #16]" + EPILOGUE)

    def test_word_pushed_on_one_path_and_allocated_on_another(self):
        # The word at the joined SP is a saved R1 on one path and a local on the other.
        # Both branch orders, so that the store is also walked under the joined state
        # (pushed AND allocated: neither saved nor local) and not only on the pushed path.
        frame = ("cmp r0, #0\nbeq second\n%s\nb joined\nsecond:\n%s\njoined:\n%s\n"
                 "add sp, #4\nbx lr")
        alias = "mov r3, sp\nstr r0, [r3]\nmovs r3, #0"
        for first, second in (("push {r1}", "sub sp, #4"), ("sub sp, #4", "push {r1}")):
            with self.subTest(first=first):
                self.refused(SAVED, frame % (first, second, alias))
                self.refused(DIRECT, frame % (first, second, "str r0, [sp]"))
        self.verify(frame % ("sub sp, #4", "sub sp, #4", alias))
        self.verify(frame % ("sub sp, #4", "sub sp, #4", "str r0, [sp]"))

    def test_pointer_word_stores_keep_the_buffer_rule(self):
        # A stack pointer stored over a pushed word is refused by the version-2 pointer-word
        # rule (BufferCallProof.access), as before; the scalar check does not replace it.
        owner = PROLOGUE + "mov r1, sp\n%s\nmov r0, sp\nbl callee0\nmovs r0, #0\nmovs r1, #0" + EPILOGUE
        self.refused("buffer access is unaligned or outside allocated local words",
                     owner % "str r1, [sp, #8]", ["movs r1, #0\nstrh r1, [r0]\nbx lr"])
        self.verify(owner % "str r1, [sp, #4]", ["movs r1, #0\nstrh r1, [r0]\nbx lr"])

    def test_aliases_returned_by_an_inspected_callee(self):
        # The callee hands the caller's sp (R3) back in R0-R3 or R12.
        owner = PROLOGUE + "mov r3, sp\nbl callee0\n%s\nadd sp, #8\npop {r4}\npop {r0}\nbx r0"
        routes = [(f"adds r{n}, r3, #0\n" + ("movs r3, #0\n" if n != 3 else "") + "bx lr", f"r{n}", "")
                  for n in range(4)]
        routes.append(("mov ip, r3\nmovs r3, #0\nbx lr", "r0", "mov r0, ip\n"))
        for callee, register, take in routes:
            for offset, outcome in ((4, None), (8, SAVED), (10, SAVED), (12, SAVED)):
                store = "strh" if offset % 4 else "str"
                value = "r1" if register == "r2" else "r2"
                after = f"{take}{store} {value}, [{register}, #{offset}]\nmovs {register}, #0"
                with self.subTest(callee=callee, offset=offset):
                    if outcome is None:
                        proof = self.verify(owner % after, [callee])
                        self.assertEqual(sorted(proof.dependencies), [CALLEE])
                    else:
                        self.refused(outcome, owner % after, [callee])

    def test_inspected_callee_stores(self):
        owner = PROLOGUE + "%s\nbl callee0\nmovs r0, #0" + EPILOGUE
        # Into the caller's saved R4 through its buffer argument: refused by the callee rule, as before.
        self.refused("buffer access is unaligned or outside allocated local words",
                     owner % "add r0, sp, #4", ["movs r1, #0\nstr r1, [r0, #4]\nbx lr"])
        self.verify(owner % "mov r0, sp", ["movs r1, #0\nstr r1, [r0, #4]\nbx lr"])
        # Into its own saved R4: the inspected callee's own walk refuses it.
        own = "push {r4, lr}\nmov r2, sp\n%s\nmovs r2, #0\nstrh r1, [r0]\npop {r4}\npop {r1}\nbx r1"
        self.refused(f"buffer callee 0x{CALLEE:08X}: {SAVED}", owner % "mov r0, sp",
                     [own % "str r1, [r2]"])
        self.refused(f"buffer callee 0x{CALLEE:08X}: {DIRECT}", owner % "mov r0, sp",
                     [own % "str r1, [sp]"])
        # Its own allocated local: admitted.
        local = ("push {r4, lr}\nsub sp, #4\nmov r2, sp\nstr r1, [r2]\nmovs r2, #0\nstrh r1, [r0]\n"
                 "add sp, #4\npop {r4}\npop {r1}\nbx r1")
        self.verify(owner % "mov r0, sp", [local])

    def test_store_helper_keeps_the_frame_facts_on_refusal(self):
        stack = [(False, True, False), (True, True, False), (False, False, True)]
        slots = {-4: -4}
        for offset, width in ((-12, 4), (-10, 2), (-9, 1), (-8, 4)):
            with self.subTest(offset=offset, width=width):
                with self.assertRaisesRegex(ValueError, SAVED):
                    match.stack_alias_store(stack, slots, {}, {match.ARM_REG_R0}, offset, width,
                                            match.ARM_REG_R0)
                self.assertEqual(stack, [(False, True, False), (True, True, False), (False, False, True)])
                self.assertEqual(slots, {-4: -4})
        match.stack_alias_store(stack, slots, {}, {match.ARM_REG_R0}, -4, 4, match.ARM_REG_R0)
        self.assertEqual(stack[2], (True, False, True))
        self.assertEqual(slots, {})


@unittest.skipUnless(tools_present(), "ARM binutils required")
class NaturalSourceTests(unittest.TestCase):
    """One past the end of a local array, compiled with the fixed agbcc, through match.py."""

    SOURCE = """typedef unsigned short u16;
extern void func_08000400(u16 value, u16 *out);
u16 func_08000200(u16 value)
{
    u16 buffer[4];

    func_08000400(value, buffer);
    buffer[%d] = value;
    return buffer[0];
}
"""

    def test_one_past_the_end_store_is_refused_and_the_last_element_matches(self):
        import test_data_buffer_calls as data_calls
        if not data_calls.tools_present():
            self.skipTest("fixed compiler and ARM tools required")
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="saved_word_source_", dir=scratch) as base:
            for index, expected in ((3, None), (4, SAVED), (5, SAVED), (6, SAVED)):
                with self.subTest(index=index):
                    root = data_calls.build(Path(base) / str(index), self.SOURCE % index,
                                            [("func_08000400", data_calls.STORES)])
                    code, output, report = data_calls.run(root)
                    if expected is None:
                        self.assertEqual(code, 0, output)
                        self.assertIn("verdict MATCH - byte identical", output)
                    else:
                        self.assertNotEqual(code, 0, output)
                        self.assertIsNone(report)
                        self.assertIn(expected, output)


if __name__ == "__main__":
    unittest.main()
