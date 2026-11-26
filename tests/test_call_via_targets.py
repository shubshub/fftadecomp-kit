"""Call-via thunks beside function literals (T1) and exact call-via targets (T2).

Natural C callers are compiled with the fixed agbcc and `-mthumb-interwork -O2` and linked at
0x08000200 beside assembled callees (test_data_buffer_calls.build), with agbcc's `_call_via_rN`
thunks at their ROM addresses; match.py runs on the default path and the reports are replayed.
"""
import json
import os
import re
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
import call_via_target_profile as call_via
from test_data_buffer_calls import A, BASE, HEADER, LITERAL, STORES, build, run, tools_present, verification

R2 = match.RUNTIME_HELPERS["_call_via_r2"]
R5 = match.RUNTIME_HELPERS["_call_via_r5"]
R0T = match.RUNTIME_HELPERS["_call_via_r0"]
R1T = match.RUNTIME_HELPERS["_call_via_r1"]
R3T = match.RUNTIME_HELPERS["_call_via_r3"]
CALLBACK = 0x08000500
# The callee hands its caller's buffer to the callback it was given in R2.
DIRECT = f"push {{lr}}\nadds r0, r1, #0\nbl 0x{R2:08X}\npop {{r0}}\nbx r0"
# The same twice through R5, which the callback must preserve across the first call.
LOOP = (f"push {{r4, r5, lr}}\nadds r4, r1, #0\nadds r5, r2, #0\nadds r0, r4, #0\nbl 0x{R5:08X}\n"
        f"adds r0, r4, #0\nbl 0x{R5:08X}\npop {{r4, r5}}\npop {{r0}}\nbx r0")
# The fact crosses the first call in R5 and is used from R2 after a copy: the crossing still counts.
COPY = (f"push {{r4, r5, lr}}\nadds r4, r1, #0\nadds r5, r2, #0\nadds r0, r4, #0\nbl 0x{R5:08X}\n"
        f"adds r0, r4, #0\nadds r2, r5, #0\nbl 0x{R2:08X}\npop {{r4, r5}}\npop {{r0}}\nbx r0")
# The callee passes its own frame to the callback, with no caller address left in R0-R3: only the
# callee's core walk sees the call, so only a fact seeded at that walk's entry resolves it.
CORE = (f"push {{lr}}\nsub sp, #8\nstrh r0, [r1]\nstrh r0, [r1, #6]\nmovs r1, #0\nmov r0, sp\n"
        f"bl 0x{R2:08X}\nadd sp, #8\npop {{r0}}\nbx r0")
# A plain owner (no function literal, no typed data): the default plain stack-argument route.
BUFFER_ONLY = """typedef unsigned short u16;
extern void func_08000400(u16 value, u16 *out);
u16 func_08000200(u16 value)
{
    u16 buffer[4];

    func_08000400(value, buffer);
    return buffer[0] + buffer[3];
}
"""
# The same owner also calls a hook (a thunk) beside its buffer call.
HOOK_ONLY = """typedef unsigned short u16;
extern void func_08000400(u16 value, u16 *out);
u16 func_08000200(u16 value, void (*hook)(void))
{
    u16 buffer[4];

    hook();
    func_08000400(value, buffer);
    return buffer[0] + buffer[3];
}
"""
# The callee hands the buffer to a callback it loads from its own pool.
POOL_CALLBACK = (f"push {{lr}}\nadds r0, r1, #0\nldr r2, 1f\nbl 0x{R2:08X}\npop {{r0}}\nbx r0\n"
                 ".align 2\n1: .word 0x08000501")
# The target is read from the buffer: no exact value.
MEMORY = f"push {{lr}}\nldr r2, [r1]\nadds r0, r1, #0\nbl 0x{R2:08X}\npop {{r0}}\nbx r0"
INSIDE = "movs r1, #0\nstrh r1, [r0]\nstrh r1, [r0, #6]\nbx lr"
OUTSIDE = "movs r1, #0\nstrh r1, [r0, #8]\nbx lr"
CLOBBER = "movs r5, #1\nmovs r1, #0\nstrh r1, [r0]\nbx lr"
# The caller itself also calls through a parameter (T1 at the owner's own link).
HOOK = HEADER + """extern void func_08000500(void);
extern void func_08000400(u16 value, u16 *out, void (*callback)(void));
void func_08000200(u16 value, void (*hook)(void))
{
    u16 buffer[4];

    hook();
    func_08000400(value, buffer, func_08000500);
    data_02000000[0] = buffer[0];
    data_02000000[1] = buffer[3];
}
"""


# No typed data: the function-buffer proof (verify_function_buffers), not the data-buffer one.
HOOK_PLAIN = """typedef unsigned short u16;
extern void func_08000500(void);
extern void func_08000400(u16 value, u16 *out, void (*callback)(void));
u16 func_08000200(u16 value, void (*hook)(void))
{
    u16 buffer[4];

    hook();
    func_08000400(value, buffer, func_08000500);
    return buffer[0] + buffer[3];
}
"""
# The literal caller without typed data: the function-buffer proof, which match.py walks in its own module.
LITERAL_PLAIN = """typedef unsigned short u16;
extern void func_08000500(void);
extern void func_08000400(u16 value, u16 *out, void (*callback)(void));
u16 func_08000200(u16 value)
{
    u16 buffer[4];

    func_08000400(value, buffer, func_08000500);
    return buffer[0] + buffer[3];
}
"""
# The owner's callback lives in a local whose address func_08000400 is given; func_08000400 rewrites
# it with FAR (an ordinary store), so the literal the local first held is stale at the call.
STALE = """typedef unsigned short u16;
extern void func_08000500(u16 *out);
extern void func_08000400(void (**slot)(u16 *));
u16 func_08000200(void)
{
    u16 buffer[4];
    void (*callback)(u16 *) = func_08000500;

    func_08000400(&callback);
    callback(buffer);
    return buffer[0] + buffer[3];
}
"""
REWRITE = "ldr r1, 1f\nstr r1, [r0]\nbx lr\n.align 2\n1: .word 0x08000701"
# The same with the address also handed over in a register copy, which the callee writes through.
STALE_COPY = """typedef unsigned short u16;
extern void func_08000500(u16 *out);
extern void func_08000400(void (**slot)(u16 *), void (**copy)(u16 *));
u16 func_08000200(void)
{
    u16 buffer[4];
    void (*callback)(u16 *) = func_08000500;
    void (**slot)(u16 *) = &callback;

    func_08000400(slot, slot);
    callback(buffer);
    return buffer[0] + buffer[3];
}
"""
REWRITE_COPY = "ldr r2, 1f\nstr r2, [r1]\nbx lr\n.align 2\n1: .word 0x08000701"
# The owner hands func_08000400 its buffer and the callback literal (rv-T F13).
TWO = """typedef unsigned short u16;
extern void func_08000500(u16 *out);
extern void func_08000400(u16 *out, void (*callback)(u16 *));
u16 func_08000200(void)
{
    u16 buffer[4];

    func_08000400(buffer, func_08000500);
    return buffer[0] + buffer[3];
}
"""
# func_08000400 keeps the callback fact in R4 across a crossed call, then calls it with the buffer.
# The crossed call goes through a value reloaded from a frame word whose address func_08000700 was
# given (and rewrote): BENIGN 0x08000601 is stale, CLOBBER 0x08000801 sets R4 to FAR at run time.
CROSS_HEAD = ("push {r4, r5, lr}\nsub sp, #8\nadds r5, r0, #0\nadds r4, r1, #0\nldr r0, 1f\n"
              "str r0, [sp, #4]\nadd r0, sp, #4\nbl 0x08000700\n")
CROSS_TAIL = (f"adds r1, r4, #0\nadds r0, r5, #0\nbl 0x{R1T:08X}\nadd sp, #8\npop {{r4, r5}}\npop {{r0}}\n"
              "bx r0\n.align 2\n1: .word 0x08000601")
STALE_THUNK = CROSS_HEAD + f"ldr r3, [sp, #4]\nmovs r0, #0\nbl 0x{R3T:08X}\n" + CROSS_TAIL
# The direct twin: the stale value is the argument of a walked helper that calls through it.
STALE_ARGUMENT = CROSS_HEAD + "ldr r0, [sp, #4]\nbl 0x08000A00\n" + CROSS_TAIL
# An honest crossing: the crossed thunk's register holds a literal the caller loaded itself.
KNOWN_THUNK = (CROSS_HEAD + "ldr r3, 2f\nmovs r0, #0\nbl 0x%08X\n" % R3T +
               CROSS_TAIL + "\n2: .word %s")
REWRITE_SLOT = "ldr r1, 1f\nstr r1, [r0]\nbx lr\n.align 2\n1: .word 0x08000801"
CLOBBER_R4 = "ldr r4, 1f\nbx lr\n.align 2\n1: .word 0x08000901"
CALLS_ARGUMENT = f"push {{lr}}\nbl 0x{R0T:08X}\npop {{r0}}\nbx r0"
# Writes far outside any owner local: what runs if the stale literal were trusted.
FAR = "movs r1, #0\nstrh r1, [r0, #16]\nbx lr"
# A numeric code pointer beside the thunk call: no canonical function provenance.
NUMERIC_PLAIN = """typedef unsigned short u16;
extern void func_08000500(void);
extern void func_08000400(u16 value, u16 *out, void (*callback)(void));
u16 func_08000200(u16 value)
{
    u16 buffer[4];
    void (*f)(u16, u16 *) = (void (*)(u16, u16 *))0x08000501;

    func_08000400(value, buffer, func_08000500);
    f(value, 0);
    return buffer[0] + buffer[3];
}
"""


def index_thunks(root):
    """The thunks are indexed two-byte spans, as in the ROM."""
    entries = json.loads((root / "config/functions.json").read_bytes())
    for value in sorted(match.RUNTIME_HELPERS.values()):
        entries.append({"rom": f"0x{value:08X}", "end": f"0x{value + 2:08X}", "mode": "thumb"})
    (root / "config/functions.json").write_text(json.dumps(entries))
    (root / "symbols/functions.txt").write_text("".join(
        f"{int(entry['rom'], 16):08X} {int(entry['end'], 16):08X} "
        f"{int(entry['end'], 16) - int(entry['rom'], 16)} 0 return\n" for entry in entries))
    return root


class FactTests(unittest.TestCase):
    def test_call_target_equality_and_join(self):
        first = call_via.CallTarget(0x08000501, {("pool", 1)})
        second = call_via.CallTarget(0x08000501, {("pool", 2)}, {(5, 6, 4)})
        self.assertEqual(first, 0x08000501)
        self.assertNotEqual(first, second)
        joined = call_via.join(first, second)
        self.assertEqual((int(joined), joined.origins, joined.crossed),
                         (0x08000501, {("pool", 1), ("pool", 2)}, {(5, 6, 4)}))
        self.assertIsNone(call_via.join(first, call_via.CallTarget(0x08000601)))
        self.assertIsNone(call_via.join(first, 0x08000501))
        self.assertIsNone(call_via.join(first, None))
        self.assertEqual(call_via.join(7, 7), 7)
        self.assertIsNone(call_via.join(7, 8))

    def test_entry_requires_an_odd_unique_indexed_thumb_entry(self):
        class Proof:
            rom = bytes(0x200000)
            entries = [{"rom": "0x08000500", "end": "0x08000504", "mode": "thumb"},
                       {"rom": "0x08000600", "end": "0x08000604", "mode": "arm"}]
        self.assertEqual(call_via.entry(Proof, 0x08000501), 0x08000500)
        for value in (0x08000500, 0x08000503, 0x08000601, R2 | 1, "0x08000501"):
            with self.subTest(value=value):
                self.assertIsNone(call_via.entry(Proof, value))

    def test_proofs_are_checked_against_their_own_match_module(self):
        # match.py issues reports as __main__ and replays them as the imported match: both copies count.
        import importlib.util
        spec = importlib.util.spec_from_file_location("match_issuing_copy", match.__file__)
        copy = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = copy
        try:
            spec.loader.exec_module(copy)
            rom, mapping = bytes(0x1000), "[]"
            for kind in ("BufferCallProof", "FunctionBufferCallProof"):
                with self.subTest(kind):
                    proof = getattr(copy, kind)(rom, mapping, stack_arguments=True, call_via_targets=True)
                    # A loaded copy is not one of the two entries that count (rv-T F11).
                    self.assertIs(call_via.kit_match(proof), match)
                    self.assertFalse(call_via.active(proof))
        finally:
            del sys.modules[spec.name]
        # A copy run as __main__ from match.py's own file, as match.py runs when it issues a report, counts.
        # (Its entry point is not run here: only its definitions are loaded.)
        import types
        main = sys.modules["__main__"]
        copy = types.ModuleType("__main__")
        copy.__file__ = match.__file__
        source = Path(match.__file__).read_text().replace('if __name__ == "__main__":', "if False:")
        sys.modules["__main__"] = copy
        try:
            exec(compile(source, match.__file__, "exec"), copy.__dict__)
            for kind in ("BufferCallProof", "FunctionBufferCallProof"):
                with self.subTest(kind):
                    proof = getattr(copy, kind)(rom, mapping, stack_arguments=True, call_via_targets=True)
                    self.assertIs(call_via.kit_match(proof), copy)
                    self.assertTrue(call_via.active(proof))
            # A subclass is not one of the two proofs, in either copy.
            derived = type("Derived", (copy.BufferCallProof,), {})
            self.assertFalse(call_via.active(derived(rom, mapping, stack_arguments=True, call_via_targets=True)))
        finally:
            sys.modules["__main__"] = main
        # A module that states match.py's file without being either entry does not count (rv-T F11).
        forged = types.ModuleType("call_via_forged")
        forged.__file__ = match.__file__
        exec("import match\nclass BufferCallProof(match.BufferCallProof):\n    pass\n"
             "class FunctionBufferCallProof(match.FunctionBufferCallProof):\n    pass\n", forged.__dict__)
        sys.modules["call_via_forged"] = forged
        try:
            proof = forged.BufferCallProof(bytes(0x1000), "[]", stack_arguments=True, call_via_targets=True)
            self.assertIs(call_via.kit_match(proof), match)
            self.assertFalse(call_via.active(proof))
        finally:
            del sys.modules["call_via_forged"]

        class FunctionBufferCallProof(match.FunctionBufferCallProof):
            pass
        # A class of the same name in another module is not the proof's class.
        self.assertIs(call_via.kit_match(FunctionBufferCallProof(bytes(0x1000), "[]", stack_arguments=True)), match)
        self.assertFalse(call_via.active(FunctionBufferCallProof(bytes(0x1000), "[]", stack_arguments=True,
                                                                 call_via_targets=True)))

    def test_only_default_route_proofs_opt_in(self):
        # An exact proof a selector route builds (owner runtime, addressed runtime, menu list, ...) does not
        # get the rule: only the default route's constructors and their replays pass call_via_targets=True.
        rom, mapping = bytes(0x1000), "[]"
        for kind in (match.BufferCallProof, match.FunctionBufferCallProof):
            with self.subTest(kind.__name__):
                self.assertFalse(call_via.active(kind(rom, mapping, stack_arguments=True)))
                self.assertTrue(call_via.active(kind(rom, mapping, stack_arguments=True, call_via_targets=True)))
        import ast
        sites = set()
        for path in sorted((ROOT / "tools").glob("*.py")):
            tree = ast.parse(path.read_text())
            for function in ast.walk(tree):
                if isinstance(function, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    for node in ast.walk(function):
                        if isinstance(node, ast.Call) and any(keyword.arg == "call_via_targets"
                                                              for keyword in node.keywords):
                            sites.add((path.name, function.name))
        self.assertEqual(sites, {("match.py", "verify_function_buffers"), ("match.py", "main"),
                                 ("data_buffer_profile.py", "prove"), ("match_evidence.py", "buffer_report_matches"),
                                 ("function_thunk_profile.py", "verify_source")})

    def test_entry_facts_are_call_targets_in_argument_registers(self):
        rom, mapping = bytes(0x1000), "[]"
        proof = match.FunctionBufferCallProof(rom, mapping, stack_arguments=True, call_via_targets=True)
        fact = call_via.CallTarget(0x08000501, {("pool", 1)})
        self.assertEqual(call_via.check_entry(proof, {match.ARM_REG_R0 + 2: fact}), ((match.ARM_REG_R0 + 2, fact),))
        self.assertEqual(call_via.check_entry(None, {}), ())
        self.assertEqual(call_via.entry_facts(proof, {match.ARM_REG_R0 + 2: fact, match.ARM_REG_R0 + 5: fact,
                                                      match.ARM_REG_R0 + 1: 7}),
                         {"entry_constants": {match.ARM_REG_R0 + 2: fact}})
        self.assertEqual(call_via.entry_facts(proof, {match.ARM_REG_R0 + 1: 7}), {})
        self.assertEqual(call_via.entry_facts(type("Derived", (match.BufferCallProof,), {})(
            rom, mapping, stack_arguments=True, call_via_targets=True), {match.ARM_REG_R0 + 2: fact}), {})
        self.assertEqual(call_via.entry_facts(match.FunctionBufferCallProof(rom, mapping, stack_arguments=True),
                                              {match.ARM_REG_R0 + 2: fact}), {})
        for name, (walk, entry) in {
                "plain value": (proof, {match.ARM_REG_R0 + 2: 0x08000501}),
                "callee-saved register": (proof, {match.ARM_REG_R0 + 4: fact}),
                "no proof": (None, {match.ARM_REG_R0 + 2: fact}),
                "other proof": (type("Derived", (match.BufferCallProof,), {})(
                    rom, mapping, stack_arguments=True, call_via_targets=True), {match.ARM_REG_R0 + 2: fact}),
                "not opted in": (match.FunctionBufferCallProof(rom, mapping, stack_arguments=True),
                                 {match.ARM_REG_R0 + 2: fact})}.items():
            with self.subTest(name), self.assertRaisesRegex(ValueError, "entry call-target facts require"):
                call_via.check_entry(walk, entry)
        with patch.object(call_via.TARGETS, "enabled", False), self.assertRaises(ValueError):
            call_via.check_entry(proof, {match.ARM_REG_R0 + 2: fact})

    def assemble(self, asm):
        """(code, site) of an assembled function at 0x08000400 (label ``site:`` marks the site)."""
        import shutil, subprocess
        if not all(shutil.which(tool) for tool in (match.DEFAULT_AS, match.DEFAULT_LD, match.DEFAULT_OBJCOPY)):
            self.skipTest("ARM tools required")
        with tempfile.TemporaryDirectory() as work:
            work = Path(work)
            (work / "f.s").write_text(".syntax unified\n.arch armv4t\n.thumb\n.text\n.global f\nf:\n" + asm + "\n")
            subprocess.run([match.DEFAULT_AS, str(work / "f.s"), "-o", str(work / "f.o")], check=True)
            subprocess.run([match.DEFAULT_LD, "-Ttext=0x08000400", "-e", "f", str(work / "f.o"), "-o",
                            str(work / "f.elf")], check=True)
            subprocess.run([match.DEFAULT_OBJCOPY, "-O", "binary", "--only-section=.text", str(work / "f.elf"),
                            str(work / "f.bin")], check=True)
            code = (work / "f.bin").read_bytes()
            listing = subprocess.run([match.DEFAULT_OBJCOPY.replace("objcopy", "nm"), str(work / "f.elf")],
                                     capture_output=True, text=True).stdout
        site = next(int(line.split()[0], 16) for line in listing.splitlines() if line.endswith(" site"))
        return code, site

    def strict(self, asm, data=b""):
        """strict_known over an assembled function at 0x08000400 (label ``site:`` marks the site)."""
        code, site = self.assemble(asm)
        rom = bytearray(0x1000)
        rom[0x400:0x400 + len(code)] = code
        rom[0x800:0x800 + len(data)] = data
        proof = type("Proof", (), {})()
        proof.rom = bytes(rom)
        return call_via.strict_known(proof, (0x08000400, 0x08000400 + len(code)), site)

    def test_strict_values_come_from_literals_rom_words_and_registers_only(self):
        pool = "bx lr\n.align 2\n1: .word 0x08000501\n2: .word 0x08000800"
        self.assertEqual(self.strict("ldr r1, 1f\nadds r2, r1, #0\nsite: mov r8, r8\n" + pool).get(2), 0x08000501)
        rom_word = struct.pack("<II", 0, 0x03005E79)
        self.assertEqual(self.strict("ldr r0, 2f\nldr r1, [r0, #4]\nsite: mov r8, r8\n" + pool,
                                     rom_word).get(1), 0x03005E79)
        # A word read from RAM, or unaligned, is not a value: only ROM is read-only.
        for word, offset in (("0x03000000", 0), ("0x08000800", 2)):
            with self.subTest(word=word, offset=offset):
                self.assertIsNone(self.strict(f"ldr r0, 3f\nmovs r2, #{offset}\nldr r1, [r0, r2]\nsite: mov r8, r8\nbx lr\n"
                                              f".align 2\n3: .word {word}", rom_word).get(1))
        # No register value crosses a call, callee-saved or not.
        self.assertIsNone(self.strict("push {r4, lr}\nldr r4, 1f\nbl 0x08000700\nsite: mov r8, r8\n"
                                      "pop {r4}\npop {r0}\nbx r0\n.align 2\n1: .word 0x08000501").get(4))
        # A literal stored to a frame word and reloaded after a call given that word's address (rv-T F12),
        # or with no call at all: frame words are never value sources.
        for between in ("add r0, sp, #4\nbl 0x08000700\n", "add r2, sp, #4\nadds r0, r2, #0\nbl 0x08000700\n", ""):
            with self.subTest(between=between):
                known = self.strict("push {lr}\nsub sp, #8\nldr r0, 1f\nstr r0, [sp, #4]\n" + between +
                                    "ldr r1, [sp, #4]\nsite: mov r0, sp\nadd sp, #8\npop {r0}\nbx r0\n"
                                    ".align 2\n1: .word 0x08000501")
                self.assertIsNone(known.get(1))

    def test_strict_values_join_every_path_or_give_none(self):
        pool = ".align 2\n1: .word 0x08000501\n2: .word 0x08000601"
        same = "cmp r0, #0\nbeq 3f\nldr r1, 1f\nb site\n3: ldr r1, 1f\nsite: mov r8, r8\nbx lr\n"
        self.assertEqual(self.strict(same + pool).get(1), 0x08000501)
        differ = "cmp r0, #0\nbeq 3f\nldr r1, 1f\nb site\n3: ldr r1, 2f\nsite: mov r8, r8\nbx lr\n"
        self.assertIsNone(self.strict(differ + pool).get(1))
        # Control flow it cannot follow exactly gives nothing anywhere.
        self.assertEqual(self.strict("ldr r1, 1f\ncmp r0, #0\nbeq 3f\nmov pc, r2\n3:\nsite: mov r8, r8\nbx lr\n"
                                     ".align 2\n1: .word 0x08000501"), {})
        self.assertEqual(self.strict("ldr r1, 1f\ncmp r0, #0\nbeq site\nbx r2\nsite: mov r8, r8\nbx lr\n"
                                     ".align 2\n1: .word 0x08000501"), {})

    def test_checker_call_takes_the_given_values_instead_of_known_at(self):
        import callee_saved_watch
        rom = bytearray(R3T - match.ROM_BASE + 0x10)
        rom[0x500:0x502] = (0x4770).to_bytes(2, "little")             # bx lr
        rom[R3T - match.ROM_BASE:R3T - match.ROM_BASE + 4] = struct.pack("<HH", 0x4718, 0x46C0)   # bx r3; mov r8, r8
        self.assertTrue(match.thunk_is_call_via(bytes(rom), R3T, 3))
        entries = [{"rom": "0x08000400", "end": "0x08000404", "mode": "thumb"},
                   {"rom": "0x08000500", "end": "0x08000502", "mode": "thumb"}]
        checker = callee_saved_watch.Checker(bytes(rom), entries)
        with patch.object(checker, "known_at", side_effect=AssertionError("known_at used")):
            self.assertEqual(checker.call(0x08000500, {4}, caller=0x08000400, site=0x08000400, known={}), {})
        checker = callee_saved_watch.Checker(bytes(rom), entries)
        with patch.object(checker, "known_at", return_value={}) as known_at:
            checker.call(0x08000500, {4}, caller=0x08000400, site=0x08000400)
        known_at.assert_called_once_with(0x08000400, 0x08000400)
        # Through a thunk the given values decide the destination: unknown, so the standard premise.
        checker = callee_saved_watch.Checker(bytes(rom), entries)
        with patch.object(checker, "known_at", return_value={3: 0x08000501}):
            checker.call(R3T, {4}, caller=0x08000400, site=0x08000400, known={})
        self.assertEqual([record[0] for record in checker.premises], ["call"])

    def test_checker_call_without_known_is_unchanged(self):
        # known=None keeps known_at; giving known_at's own values is the same check, result for result.
        import callee_saved_watch
        for name, asm in (
                ("resolved", "push {r4, lr}\nldr r3, 1f\nsite: bl 0x%08X\npop {r4}\npop {r0}\nbx r0\n"
                             ".align 2\n1: .word 0x08000501" % R3T),
                ("unresolved", "push {r4, lr}\nadds r3, r0, #0\nsite: bl 0x%08X\npop {r4}\npop {r0}\nbx r0" % R3T)):
            with self.subTest(name):
                code, site = self.assemble(asm)
                rom = bytearray(R3T - match.ROM_BASE + 0x10)
                rom[0x400:0x400 + len(code)] = code
                rom[0x500:0x502] = (0x4770).to_bytes(2, "little")
                rom[R3T - match.ROM_BASE:R3T - match.ROM_BASE + 4] = struct.pack("<HH", 0x4718, 0x46C0)
                entries = [{"rom": "0x08000400", "end": f"0x{0x08000400 + len(code):08X}", "mode": "thumb"},
                           {"rom": "0x08000500", "end": "0x08000502", "mode": "thumb"}]
                plain, given = (callee_saved_watch.Checker(bytes(rom), entries) for _ in range(2))
                first = plain.call(R3T, {4}, caller=0x08000400, site=site)
                second = given.call(R3T, {4}, caller=0x08000400, site=site,
                                    known=given.known_at(0x08000400, site))
                self.assertEqual((first, plain.premises, plain.results), (second, given.premises, given.results))
                self.assertEqual(bool(plain.premises), name == "unresolved")

    def test_crossing_checks_use_strict_values_and_state_only_call_and_swi_premises(self):
        import callee_saved_watch
        rom, mapping = bytes(0x1000), json.dumps([{"rom": "0x08000400", "end": "0x08000420", "mode": "thumb"}])
        proof = match.FunctionBufferCallProof(rom, mapping, stack_arguments=True, call_via_targets=True)
        seen = []

        def call(checker, target, watched, constants=None, *, caller=None, site=None, known=None):
            seen.append((target, watched, caller, site, known))
            checker.premises.add(premise)
            return {}
        strict = {3: 0x08000601}
        with patch.object(callee_saved_watch.Checker, "call", call), \
                patch.object(call_via, "strict_known", return_value=strict):
            premise = ("call", 0x08000400, 0x08000410, (3,), None, (4,), (), False)
            self.assertEqual(call_via.crossing_premises(proof, (0x08000400, 0x08000420), 0x08000410, R3T, 4),
                             frozenset({premise}))
            self.assertEqual(seen, [(R3T, frozenset({4}), 0x08000400, 0x08000410, strict)])
            premise = ("escape", 0x08000400, 0x08000412, "a global", (8,), ())
            with self.assertRaisesRegex(ValueError, r"needs a premise this rule does not state \(escape\)"):
                call_via.crossing_premises(proof, (0x08000400, 0x08000420), 0x08000412, 0x08000500, 4)
        # Each crossing is checked on a checker of its own: the shared check records nothing.
        self.assertFalse(callee_saved_watch.premise_lines(proof))

    def test_cross_marks_only_callee_saved_facts(self):
        constants = {match.ARM_REG_R0 + 1: call_via.CallTarget(0x08000501),
                     match.ARM_REG_R0 + 5: call_via.CallTarget(0x08000501), match.ARM_REG_R0 + 6: 9}
        call_via.cross(constants, 0x08000404, CALLBACK)
        self.assertEqual(constants[match.ARM_REG_R0 + 5].crossed, {(0x08000404, CALLBACK, 5)})
        self.assertEqual(constants[match.ARM_REG_R0 + 1].crossed, frozenset())
        self.assertEqual(constants[match.ARM_REG_R0 + 6], 9)


@unittest.skipUnless(tools_present(), "fixed compiler and ARM tools required")
class CallViaNativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix="call_via_targets_", dir=scratch)
        cls.base = Path(cls.temporary.name)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def fixture(self, name, worker, callback=INSIDE, source=None):
        return index_thunks(build(self.base / name, source or LITERAL % dict(extra=""),
                                  [("func_08000400", worker), ("func_08000500", callback)], large=True))

    def replays(self, report, root):
        with patch.dict(os.environ, FFTA_ROM=str(root / "baserom.bin")):
            return evidence.report_matches(report, root, A)

    def admitted(self, root, schema=data_buffer.FUNCTION_SCHEMA):
        code, output, report = run(root)
        self.assertEqual(code, 0, output)
        self.assertEqual(verification(report), schema)
        self.assertTrue(self.replays(report, root))
        return report

    def refused(self, root, message):
        code, output, report = run(root)
        self.assertNotEqual(code, 0, output)
        self.assertIsNone(report)
        self.assertRegex(output, message)
        return output

    def targets(self, report):
        return [line for line in report.splitlines() if line.startswith(call_via.LINE)]

    def test_owner_literal_carried_into_a_callee_is_walked(self):
        root = self.fixture("direct", DIRECT)
        report = self.admitted(root)
        (line,) = self.targets(report)
        self.assertIn(f"in 0x08000400 _call_via_r2 = 0x{CALLBACK | 1:08X} -> 0x{CALLBACK:08X}", line)
        self.assertIn("(fact; origins pool 0x080002", line)
        # The line is bound: an altered or dropped line does not replay.
        self.assertFalse(self.replays(report.replace(f"-> 0x{CALLBACK:08X}", "-> 0x08000600"), root))
        self.assertFalse(self.replays(report.replace(line + "\n", ""), root))

    def test_walked_target_keeps_every_buffer_bound(self):
        self.refused(self.fixture("outside", DIRECT, OUTSIDE), "outside allocated local words")

    def test_fact_crossing_a_call_needs_a_preserving_callee(self):
        report = self.admitted(self.fixture("loop", LOOP))
        first, second = self.targets(report)
        self.assertTrue(all("_call_via_r5" in line for line in (first, second)))
        self.assertIn("crossed none", first)
        # The second call relies on R5 across the first, whose walked callee only leaves it alone.
        self.assertRegex(second, r"crossed 0x0800040[0-9A-F]->0x08000500:r5\)")
        self.refused(self.fixture("clobber", LOOP, CLOBBER),
                     r"buffer callee 0x08000400: callee 0x08000500: R5 does not hold its value at the return")

    def test_crossings_count_after_a_copy_into_an_argument_register(self):
        report = self.admitted(self.fixture("copy", COPY))
        first, second = self.targets(report)
        self.assertIn("_call_via_r5", first)
        self.assertIn("_call_via_r2", second)
        self.assertRegex(second, r"crossed 0x0800040[0-9A-F]->0x08000500:r5\)")
        self.refused(self.fixture("copy_clobber", COPY, CLOBBER),
                     r"buffer callee 0x08000400: callee 0x08000500: R5 does not hold its value at the return")

    def test_callee_core_walk_starts_with_the_caller_facts(self):
        report = self.admitted(self.fixture("core", CORE))
        (line,) = self.targets(report)
        self.assertIn(f"in 0x08000400 _call_via_r2 = 0x{CALLBACK | 1:08X} -> 0x{CALLBACK:08X} (fact; origins pool", line)
        # Only the seeded core walk resolves it.
        from test_data_buffer_calls import DataBufferNativeTests
        body, rom, mapping, objects, calls, literals, functions = DataBufferNativeTests.linked(
            self, self.fixture("core_unseeded", CORE))
        with patch.object(call_via, "entry_facts", return_value={}), self.assertRaisesRegex(
                ValueError, "non-leaf indirect control flow requires linked CFG verification"):
            data_buffer.prove(body, A, rom, mapping, objects, calls, literals, functions)
        # The resolved callback is walked with the callee's frame: its bounds still hold.
        self.refused(self.fixture("core_outside", CORE, OUTSIDE), "outside allocated local words")

    def test_f1_callback_rewritten_through_its_address_is_not_the_stale_literal(self):
        for name, source, rewrite in (("stale", STALE, REWRITE), ("stale_copy", STALE_COPY, REWRITE_COPY)):
            with self.subTest(name):
                root = index_thunks(build(self.base / name, source,
                                          [("func_08000400", rewrite), ("func_08000500", INSIDE),
                                           ("func_08000600", "bx lr"), ("func_08000700", FAR)],
                                          large=True, function_literal_thunks=True))
                code, output, report = run(root)
                self.assertNotEqual(code, 0, output)
                self.assertIsNone(report)
                self.assertNotIn("0x08000501 -> 0x08000500", output)

    def root_of(self, name):
        return self.base / name

    def crossing(self, name, worker):
        return index_thunks(build(self.base / name, TWO,
                                  [("func_08000400", worker), ("func_08000500", INSIDE), ("func_08000600", "bx lr"),
                                   ("func_08000700", REWRITE_SLOT), ("func_08000800", CLOBBER_R4),
                                   ("func_08000900", FAR), ("func_08000A00", CALLS_ARGUMENT)], large=True))

    def premises(self, report):
        return [line for line in report.splitlines() if line.startswith(call_via.PREMISE_LINE)]

    def shared_premises(self, report):
        return [line for line in report.splitlines() if line.startswith("* callee-saved premise")]

    def test_f13_crossed_call_through_a_stale_value_is_premised_not_proved(self):
        # The crossed call's destination (a thunk) or argument (a helper that calls through it) is a
        # value reloaded from an escaped frame word: unknown, so the call stands on the stated premise
        # and is never "proved" by walking the stale BENIGN.
        for name, worker, thunk, crossed in (("f13", STALE_THUNK, "_call_via_r3", R3T),
                                             ("f13_argument", STALE_ARGUMENT, "_call_via_r0", 0x08000A00)):
            with self.subTest(name):
                report = self.admitted(self.crossing(name, worker), evidence.FUNCTION_BUFFER_SCHEMA)
                (line,) = [line for line in self.targets(report) if "_call_via_r1" in line]
                self.assertRegex(line, rf"0x080004[0-9A-F]{{2}}->0x{crossed:08X}:r4\)")
                (premise,) = self.premises(report)
                self.assertIn(f"through {thunk} to an unknown address, with R4 holding the call-via target "
                              f"0x{CALLBACK | 1:08X}; {call_via.CROSSING_PREMISE}", premise)
                self.assertIn(f"relies on the crossed call at 0x080004", premise)
                # The call target (R4) is never stated as an owner stack address on the shared lines.  The
                # shared check may premise the same site for an owner address it watches (R5 holds the
                # buffer): that line is the #350 check's own, and correct once its known_at is strict.
                self.assertFalse([line for line in self.shared_premises(report)
                                  if re.search(r"with (R\d+,)*R4\b[^;]* depending on owner stack addresses", line)])
                # The premise line is bound: a dropped line does not replay.
                self.assertFalse(self.replays(report.replace(premise + "\n", ""), self.root_of(name)))

    def test_crossed_call_through_a_known_value_is_walked(self):
        report = self.admitted(self.crossing("known_benign", KNOWN_THUNK % "0x08000601"),
                               evidence.FUNCTION_BUFFER_SCHEMA)
        self.assertFalse(self.premises(report))
        self.assertFalse([premise for premise in self.shared_premises(report) if "_call_via_r3" in premise])
        self.refused(self.crossing("known_clobber", KNOWN_THUNK % "0x08000801"),
                     r"R4 does not hold its value at the return")

    def test_plain_stack_route_resolves_and_replays(self):
        # rv-T h10/h10c: the report's replay re-walks through function_thunk_profile.verify_source too.
        for name, source in (("plain", BUFFER_ONLY), ("plain_hook", HOOK_ONLY)):
            with self.subTest(name):
                root = index_thunks(build(self.base / name, source,
                                          [("func_08000400", POOL_CALLBACK), ("func_08000500", INSIDE)], large=True))
                report = self.admitted(root, evidence.STACK_BUFFER_SCHEMA)
                (line,) = self.targets(report)
                self.assertIn(f"_call_via_r2 = 0x{CALLBACK | 1:08X} -> 0x{CALLBACK:08X} (fact; origins pool", line)
                self.assertFalse(self.replays(report.replace(line + "\n", ""), root))

    def test_target_read_from_memory_stays_unresolved(self):
        self.refused(self.fixture("memory", MEMORY),
                     "non-leaf indirect control flow requires linked CFG verification")

    def test_owner_thunk_beside_function_literal_and_buffer(self):
        root = index_thunks(build(self.base / "hook", HOOK,
                                  [("func_08000400", STORES), ("func_08000500", "bx lr")], large=True,
                                  function_literal_thunks=True))
        report = self.admitted(root)
        (encoded,) = [line for line in report.splitlines() if line.startswith(data_buffer.MANIFEST_FIELD)]
        manifest = json.loads(encoded[len(data_buffer.MANIFEST_FIELD) + 1:-1])
        self.assertTrue(any(row[1].startswith("_call_via_r") for row in manifest["calls"]), manifest)
        self.assertEqual([row[1] for row in manifest["functions"]], ["func_08000500"])
        self.assertFalse(self.targets(report))
        # Without the default route the owner's own link keeps refusing function literals beside thunks.
        with self.assertRaisesRegex(match.Refusal, "function-address evidence does not support runtime call thunks"):
            build(self.base / "hook_selector", HOOK, [("func_08000400", STORES), ("func_08000500", "bx lr")],
                  large=True)

    def test_function_buffer_path_binds_thunks_by_their_bytes(self):
        root = index_thunks(build(self.base / "hook_plain", HOOK_PLAIN,
                                  [("func_08000400", STORES), ("func_08000500", "bx lr")], large=True,
                                  function_literal_thunks=True))
        code, output, report = run(root)
        self.assertEqual(code, 0, output)
        self.assertEqual(verification(report), evidence.FUNCTION_BUFFER_SCHEMA)
        self.assertTrue(self.replays(report, root))
        (encoded,) = [line for line in report.splitlines() if line.startswith("* function address manifest: ")]
        names = [row[1] for row in json.loads(encoded[len("* function address manifest: `"):-1])["calls"]]
        (thunk,) = [name for name in names if name.startswith("_call_via_r")]
        # A thunk whose bytes differ does not replay.
        rom = bytearray((root / "baserom.bin").read_bytes())
        address = match.RUNTIME_HELPERS[thunk] - BASE
        rom[address] ^= 8
        (root / "baserom.bin").write_bytes(bytes(rom))
        self.assertFalse(self.replays(report, root))

    def test_function_buffer_path_resolves_targets(self):
        root = self.fixture("direct_plain", DIRECT, source=LITERAL_PLAIN)
        code, output, report = run(root)
        self.assertEqual(code, 0, output)
        self.assertEqual(verification(report), evidence.FUNCTION_BUFFER_SCHEMA)
        (line,) = self.targets(report)
        self.assertIn(f"in 0x08000400 _call_via_r2 = 0x{CALLBACK | 1:08X} -> 0x{CALLBACK:08X}", line)
        self.assertTrue(self.replays(report, root))
        self.assertFalse(self.replays(report.replace(line + "\n", ""), root))

    def test_numeric_code_pointer_beside_a_thunk_refused(self):
        root = index_thunks(build(self.base / "numeric", NUMERIC_PLAIN,
                                  [("func_08000400", STORES), ("func_08000500", "bx lr")], large=True,
                                  function_literal_thunks=True))
        self.refused(root, "code-entry thunk literals require canonical function provenance")

    def test_resolution_is_part_of_the_buffer_fingerprint(self):
        root = self.fixture("fingerprint", DIRECT)
        from test_data_buffer_calls import DataBufferNativeTests
        body, rom, mapping, objects, calls, literals, functions = DataBufferNativeTests.linked(self, root)
        proof = data_buffer.prove(body, A, rom, mapping, objects, calls, literals, functions)[1]
        self.assertTrue(proof.call_via_records)
        bound = proof.fingerprint()
        proof.call_via_records.clear()
        self.assertNotEqual(proof.fingerprint(), bound)

    def test_default_route_only(self):
        import argparse
        base = dict(control_flow_profile="ordinary")
        self.assertTrue(match.default_call_route(argparse.Namespace(**base)))
        for name in ("owner_runtime_profile", "function_address_profile", "switch_data_profile",
                     "signed_quotient_profile", "unsigned_quotient_profile"):
            with self.subTest(name=name):
                self.assertFalse(match.default_call_route(argparse.Namespace(**base, **{name: "x"})))
        self.assertFalse(match.default_call_route(argparse.Namespace(control_flow_profile="other")))
        self.assertFalse(match.default_call_route(argparse.Namespace(**base), {"tool": "x"}))
        with patch.object(call_via.POLICY, "enabled", False), self.assertRaisesRegex(
                match.Refusal, "function-address evidence does not support runtime call thunks"):
            build(self.base / "hook_policy", HOOK, [("func_08000400", STORES), ("func_08000500", "bx lr")],
                  large=True, function_literal_thunks=True)

    def test_owner_walk_call_is_checked_as_its_target(self):
        root = self.fixture("owner_call", DIRECT)
        rom = (root / "baserom.bin").read_bytes()
        mapping = (root / "config/functions.json").read_bytes()
        proof = match.FunctionBufferCallProof(rom, mapping, stack_arguments=True, loop_replay=True,
                                              dead_registers=True, call_via_targets=True)
        stack = [(False, False, True)] * 2
        fact = call_via.CallTarget(CALLBACK | 1, {("pool", A + 0x40)})
        proof.check_call(R2, {match.ARM_REG_R0: -8}, stack, constants={match.ARM_REG_R0 + 2: fact}, site=A + 4)
        self.assertEqual([(record["site"], record["target"]) for record in proof.call_via_records.values()],
                         [(A + 4, CALLBACK)])
        self.assertIn(CALLBACK, proof.dependencies)
        with self.assertRaisesRegex(ValueError, "non-leaf indirect control flow"):
            match.FunctionBufferCallProof(rom, mapping, stack_arguments=True, call_via_targets=True).check_call(
                R2, {match.ARM_REG_R0: -8}, stack, constants={}, site=A + 4)
        # Not opted in (a selector route's exact proof): the fact is not used.
        with self.assertRaisesRegex(ValueError, "non-leaf indirect control flow"):
            match.FunctionBufferCallProof(rom, mapping, stack_arguments=True).check_call(
                R2, {match.ARM_REG_R0: -8}, stack, constants={match.ARM_REG_R0 + 2: fact}, site=A + 4)

    def test_targets_policy_off_leaves_the_thunk_unresolved(self):
        root = self.fixture("targets_policy", DIRECT)
        from test_data_buffer_calls import DataBufferNativeTests
        body, rom, mapping, objects, calls, literals, functions = DataBufferNativeTests.linked(self, root)
        with patch.object(call_via.TARGETS, "enabled", False), self.assertRaisesRegex(
                ValueError, "non-leaf indirect control flow requires linked CFG verification"):
            data_buffer.prove(body, A, rom, mapping, objects, calls, literals, functions)

    def test_policy_off_keeps_the_earlier_refusals(self):
        root = self.fixture("policy", DIRECT)
        from test_data_buffer_calls import DataBufferNativeTests
        linked = DataBufferNativeTests.linked(self, root)
        body, rom, mapping, objects, calls, literals, functions = linked
        values = dict(data=body, address=A, rom=rom, mapping=mapping, objects=objects, calls=calls,
                      data_relocations=literals, function_relocations=functions)
        self.assertEqual(data_buffer.prove(**values)[2], data_buffer.FUNCTION_SCHEMA)
        with patch.object(call_via.POLICY, "enabled", False):
            with self.assertRaisesRegex(ValueError, "excludes runtime call thunks in inspected dependencies"):
                data_buffer.prove(**values)
