"""A walked callee's released frame address in R2/R3 at its return (released_scratch_profile).

The 0x08006EC0 shape: a callee passes `mov r2, sp` to a further call that leaves R2 alone and
returns with R2 still holding an address of its own, now released, frame.  The default buffer walk
refused that return; the rule hands the register back to the walked caller as a marker that
refuses any use and is cleared by a write.  Fixtures are assembled Thumb functions linked at
0x08000000; no game ROM is needed.
"""
import os
from pathlib import Path
import json
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import match
import released_scratch_profile as released

BASE = match.ROM_BASE
OWNER = BASE
# X: takes the owner's buffer in r0, writes it, hands its own sp to Y in r2, returns with r2 = sp.
X = ("push {lr}\nsub sp, #8\nmovs r1, #1\nstrh r1, [r0]\nmov r2, sp\nmovs r0, #0\nbl func_Y\n"
     "add sp, #8\npop {r0}\nbx r0")
Y = "bx lr"
# Z: like X but takes nothing from the owner; X2 keeps the owner's buffer in r4 across Z, so the
# alias-path walk follows Z, and never touches r2 again: the release passes through X2's return.
Z = "push {lr}\nsub sp, #8\nmov r2, sp\nmovs r0, #0\nbl func_Y\nadd sp, #8\npop {r0}\nbx r0"
X2 = ("push {r4, lr}\nadds r4, r0, #0\nbl func_Z\nmovs r1, #2\nstrh r1, [r4]\npop {r4}\npop {r0}\nbx r0")
# X3: overwrites the owner's buffer pointer unread (the dead-register shape), releases r2 on the
# path the walk takes first and meets an SWI, which the walk refuses, on the other.
X3 = ("push {lr}\nsub sp, #8\nmovs r0, #0\ncmp r1, #0\nbeq 1f\nmov r2, sp\nadd sp, #8\npop {r0}\nbx r0\n"
      "1:\nsvc #0\nadd sp, #8\npop {r0}\nbx r0")
# Order (rule 6).  D releases r2 (its own frame, through Y) and is walked only when it is passed a
# stack address.  E writes through r0 + 8, which for r0 = D's released frame is E's own saved LR.
D = "push {lr}\nsub sp, #8\nmov r2, sp\nmovs r0, #0\nbl func_Y\nadd sp, #8\npop {r0}\nbx r0"
E = "push {lr}\nstr r1, [r0, #8]\npop {r0}\nbx r0"
# The owner calls D with nothing passed (not walked) and hands its r2 to E, then walks D.
D_LATER = ("push {r4, lr}\nsub sp, #8\nbl func_D\nadds r0, r2, #0\nmovs r1, #0\nbl func_E\n"
           "mov r0, sp\nbl func_D\nmovs r2, #0\nadd sp, #8\npop {r4}\npop {r1}\nbx r1")
# The same inside a walked callee's alias-path walk: the path taken first drops the owner's buffer,
# calls D unwalked and hands r2 to E; the other path passes the buffer to D, which is walked.
C_BRANCH = ("push {r4, lr}\ncmp r1, #0\nbeq 1f\nmovs r0, #0\nbl func_D\nadds r0, r2, #0\nmovs r1, #0\n"
            "bl func_E\nb 2f\n1:\nbl func_D\nmovs r2, #0\n2:\npop {r4}\npop {r0}\nbx r0")
# A walked callee that calls D unwalked, overwrites r2, then walks D with its own frame: its core
# walk meets the first call before D's record, its alias-path walk after it.
C_BOTH = ("push {lr}\nsub sp, #8\nmovs r1, #1\nstrh r1, [r0]\nmovs r0, #0\nbl func_D\nmovs r2, #0\n"
          "mov r0, sp\nbl func_D\nmovs r2, #0\nadd sp, #8\npop {r0}\nbx r0")


def owner(after, callee="func_X", frame=8):
    """push, a local frame, the call with the local in r0, `after`, and a balanced return."""
    return (f"push {{r4, lr}}\nsub sp, #{frame}\nmov r0, sp\nbl {callee}\n{after}\n"
            f"add sp, #{frame}\npop {{r4}}\npop {{r1}}\nbx r1")


@unittest.skipUnless(all(subprocess.run(["which", tool], capture_output=True).returncode == 0
                         for tool in ("arm-none-eabi-as", "arm-none-eabi-ld", "arm-none-eabi-objcopy")),
                     "ARM binutils required")
class ReleasedScratchTests(unittest.TestCase):
    def setUp(self):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="released_scratch_", dir=scratch)
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)

    def build(self, owner_body, **bodies):
        functions = dict(func_X=X, func_Y=Y, func_Z=Z, func_X2=X2, func_W="bx lr", func_X3=X3, func_D=D,
                         func_E=E, func_C_BRANCH=C_BRANCH, func_C_BOTH=C_BOTH)
        functions.update(bodies)
        labels = ["owner", "owner_end"] + [label for name in functions for label in (name, name + "_end")]
        text = (".syntax unified\n.arch armv4t\n.thumb\n.text\n.global " + ", ".join(labels) + "\n"
                f"owner:\n{owner_body}\n.align 2\n.ltorg\nowner_end:\n")
        for index, (name, body) in enumerate(functions.items()):
            text += f".org 0x{0x100 * (index + 1):x}\n{name}:\n{body}\n{name}_end:\n"
        (self.root / "f.s").write_text(text)
        for command in (
                ["arm-none-eabi-as", "-mthumb-interwork", str(self.root / "f.s"), "-o", str(self.root / "f.o")],
                ["arm-none-eabi-ld", "-Ttext=0x08000000", "-e", "owner", str(self.root / "f.o"),
                 "-o", str(self.root / "f.elf")],
                ["arm-none-eabi-objcopy", "-O", "binary", "--only-section=.text", str(self.root / "f.elf"),
                 str(self.root / "f.bin")]):
            subprocess.run(command, check=True, capture_output=True)
        image = match.elf_image((self.root / "f.elf").read_bytes())
        self.symbols = {symbol["name"]: symbol["value"] for symbol in image["symbols"]}
        rom = (self.root / "f.bin").read_bytes()
        entries = [{"rom": f"0x{self.symbols[name]:08X}", "end": f"0x{self.symbols[name + '_end']:08X}",
                    "mode": "thumb"} for name in ("owner", *functions)]
        self.rom, self.mapping = rom, json.dumps(entries).encode()
        self.body = rom[:self.symbols["owner_end"] - BASE]

    def walk(self, owner_body, **bodies):
        self.build(owner_body, **bodies)
        proof = match.BufferCallProof(self.rom, self.mapping, stack_arguments=True, loop_replay=True,
                                      bios_wrappers=True, dead_registers=True)
        match.verify_leaf_instructions(self.body, OWNER, True, buffer_proof=proof, call_resolver=proof.target,
                                       incoming_narrow_reads=True)
        return proof

    def refused(self, pattern, owner_body, **bodies):
        with self.assertRaisesRegex(ValueError, pattern):
            self.walk(owner_body, **bodies)

    def x(self, name="func_X"):
        return self.symbols[name]

    # Admitted ------------------------------------------------------------------

    def test_the_owner_overwrites_the_released_register(self):
        proof = self.walk(owner("movs r2, #0\nstrh r2, [r0]"))
        returns = [row for row in proof.released_scratch if row[0] == self.x()]
        self.assertEqual([(row[2], row[3]) for row in returns], [(2, -12)])
        self.assertEqual({row[2] for row in proof.released_kills}, {2})
        line, = released.lines(proof)
        self.assertTrue(line.startswith(f"* buffer released scratch: `{released.SCHEMA}` released "
                                        f"0x{self.x():08X} return 0x"), line)
        self.assertIn(line, proof.loop_replay_lines())

    def test_the_release_follows_two_returns(self):
        proof = self.walk(owner("movs r2, #0", callee="func_X2"))
        rows = sorted((row[0], row[2], row[3]) for row in proof.released_scratch)
        self.assertEqual(rows, sorted([(self.x("func_Z"), 2, -12), (self.x("func_X2"), 2, None)]))

    def test_a_proof_without_a_release_keeps_its_fingerprint(self):
        proof = self.walk(owner("movs r2, #0\nstrh r2, [r0]"))
        with_release = proof.fingerprint()
        proof.released_scratch.clear()
        proof.released_kills.clear()
        self.assertNotEqual(proof.fingerprint(), with_release)
        quiet = self.walk(owner("movs r2, #0\nstrh r2, [r0]"), func_X=X.replace("mov r2, sp", "movs r2, #0"))
        self.assertFalse(quiet.released_scratch)
        self.assertEqual(released.lines(quiet), [])

    # Refused -------------------------------------------------------------------

    def test_a_read_of_the_released_register_refuses(self):
        for use in ("adds r0, r2, #0", "strh r1, [r2]", "cmp r2, #0", "push {r2}\npop {r2}", "str r2, [sp]"):
            with self.subTest(use=use):
                self.refused("released callee frame address in r2 is read", owner(use))

    def test_a_call_with_the_released_register_live_refuses(self):
        self.refused("released callee frame address reaches a call in R0-R3", owner("bl func_W"))

    def test_the_owner_returning_it_refuses(self):
        self.refused(released.ESCAPE, owner("movs r0, #0"))

    def test_r0_and_r1_keep_the_refusal(self):
        for register, other in (("r0", "r1"), ("r1", "r0")):
            with self.subTest(register=register):
                body = X.replace("mov r2, sp\nmovs r0, #0", f"mov {register}, sp").replace(
                    "pop {r0}\nbx r0", f"pop {{{other}}}\nbx {other}")
                self.refused(released.ESCAPE, owner("movs r2, #0"), func_X=body)

    def test_a_caller_frame_address_keeps_the_refusal(self):
        # sp + 12 is X's incoming area (the owner's frame), not X's own released frame
        body = X.replace("mov r2, sp", "add r2, sp, #12")
        self.refused(f"{released.ESCAPE}|outside allocated local words", owner("movs r2, #0"), func_X=body)

    def test_a_release_on_one_path_is_released_after_the_join(self):
        # X releases r2 only when r1 is nonzero; the owner reads r2 after the join
        body = ("push {lr}\nsub sp, #8\nmovs r2, #0\ncmp r1, #0\nbeq 1f\nmov r2, sp\n1:\nmovs r0, #0\n"
                "bl func_Y\nadd sp, #8\npop {r0}\nbx r0")
        self.refused("released callee frame address in r2 is read", owner("adds r0, r2, #0"), func_X=body)
        self.walk(owner("movs r2, #0"), func_X=body)

    def test_a_refused_inspection_that_released_keeps_its_refusal(self):
        # Without a release, the refused inspection of X3 is the dead-register fallback's alias-free call.
        quiet = self.walk(owner("strh r1, [r2]", callee="func_X3"), func_X3=X3.replace("mov r2, sp", "movs r2, #0"))
        self.assertTrue(quiet.dead_registers.calls)
        self.assertFalse(quiet.released_scratch)
        # With one, the fallback would discard the record and drop the address: the refusal stays.
        for after in ("strh r1, [r2]", "movs r2, #0"):
            with self.subTest(after=after):
                self.refused("non-leaf calls and interrupts", owner(after, callee="func_X3"), func_X3=X3)
        with patch.object(released, "recorded_since", lambda proof, before: False):
            dropped = self.walk(owner("strh r1, [r2]", callee="func_X3"), func_X3=X3)
        self.assertTrue(dropped.dead_registers.calls)
        self.assertFalse(dropped.released_scratch)

    def test_a_release_recorded_after_an_unmarked_call_refuses(self):
        # The first call of D went without a marker because D's release was not recorded yet.
        self.refused(r"released callee frame address in r2: an earlier call to 0x[0-9A-F]{8} took no marker",
                     D_LATER)
        # In the other order the release is recorded first and the read of r2 refuses.
        self.refused("released callee frame address in r2 is read",
                     D_LATER.replace("bl func_D\nadds r0, r2, #0\nmovs r1, #0\nbl func_E\nmov r0, sp\nbl func_D\n",
                                     "mov r0, sp\nbl func_D\nmovs r2, #0\nbl func_D\nadds r0, r2, #0\nmovs r1, #0\nbl func_E\n"))

    def test_a_release_recorded_on_a_later_path_of_an_alias_walk_refuses(self):
        self.refused(r"an earlier call to 0x[0-9A-F]{8} took no marker", owner("movs r2, #0", callee="func_C_BRANCH"))

    def test_a_walked_callees_core_walk_is_checked_by_its_alias_walk(self):
        proof = self.walk(owner("movs r2, #0", callee="func_C_BOTH"))
        self.assertIn((self.x("func_D"), 2), {(row[0], row[2]) for row in proof.released_scratch})
        self.assertNotIn((self.x("func_D"), 2), proof.released_unmarked)
        # Without the exemption its core walk's first call would refuse the release it meets next;
        # the alias-path walk marks that call (D's release is recorded by then).
        self.refused("released callee frame address in r2 is read",
                     owner("movs r2, #0", callee="func_C_BOTH"),
                     func_C_BOTH=C_BOTH.replace("bl func_D\nmovs r2, #0\nmov r0, sp", "bl func_D\nadds r0, r2, #0\nmov r0, sp"))

    def test_an_aborted_pass_leaves_no_unmarked_call(self):
        self.build(owner("movs r2, #0"))
        proof = match.BufferCallProof(self.rom, self.mapping, stack_arguments=True)
        saved = proof._snapshot_ledgers()
        proof.released_unmarked.add((1, 2))
        proof._restore_ledgers(saved)
        self.assertEqual(proof.released_unmarked, set())

    def test_a_subclass_proof_keeps_the_refusal(self):
        self.build(owner("movs r2, #0"))

        class Other(match.BufferCallProof):
            pass
        proof = Other(self.rom, self.mapping, stack_arguments=True)
        with self.assertRaisesRegex(ValueError, released.ESCAPE):
            match.verify_leaf_instructions(self.body, OWNER, True, buffer_proof=proof, call_resolver=proof.target)

    # Mutants -------------------------------------------------------------------

    def test_without_the_rule_the_old_refusal_returns(self):
        with patch.object(released, "callee_return", lambda proof, address, site, aliases, **_: aliases):
            self.refused(released.ESCAPE, owner("movs r2, #0"))


class IssuingCopyTests(unittest.TestCase):
    def test_proofs_of_the_issuing_copy_of_match_take_the_rule(self):
        # match.py issues reports as __main__ loaded from its own file and replays them as the imported
        # match: proofs of both count (call_via_target_profile.kit_match).  Only the definitions are run.
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
                    self.assertTrue(released.applies(getattr(copy, kind)(bytes(0x1000), "[]", stack_arguments=True)))
                    self.assertFalse(released.applies(getattr(copy, kind)(bytes(0x1000), "[]")))
            derived = type("Derived", (copy.BufferCallProof,), {})
            self.assertFalse(released.applies(derived(bytes(0x1000), "[]", stack_arguments=True)))
        finally:
            sys.modules["__main__"] = main

if __name__ == "__main__":
    unittest.main()
