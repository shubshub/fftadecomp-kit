"""A frame address left in R12 (IP) at a return of a buffer walk (r12_exit_scratch_profile, kit #588).

The synthetic walks need only the assembler.  The subprocess tests compile C with the fixed compiler
and run match.py as issuance does (as __main__), then replay the report.  No game ROM is needed.
"""
import json
import os
from pathlib import Path
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
import r12_exit_scratch_profile as r12_exit
import return_scratch_profile as scratch

BASE = match.ROM_BASE
ESCAPE = scratch.ESCAPE
BINUTILS = all(subprocess.run(["which", tool], capture_output=True).returncode == 0
               for tool in ("arm-none-eabi-as", "arm-none-eabi-ld", "arm-none-eabi-objcopy"))

# A walked callee that copies its own frame address into IP and returns (the issue's func_X12).
X12 = ("push {lr}\nsub sp, #8\nmovs r1, #1\nstrh r1, [r0]\nmov r3, sp\nmov ip, r3\nmovs r3, #0\n"
       "add sp, #8\npop {r0}\nbx r0")
# E stores R1 at R0 + 8: with R0 = X12's released frame, that is E's own saved LR.
E = "push {lr}\nstr r1, [r0, #8]\npop {r0}\nbx r0"
OWNER = ("push {r4, lr}\nsub sp, #8\nmov r0, sp\nbl func_X12\nmov r0, ip\nmovs r1, #0\nbl func_E\n"
         "add sp, #8\npop {r4}\npop {r1}\nbx r1")


def frame(body):
    return f"push {{r4, lr}}\nsub sp, #8\n{body}\nadd sp, #8\npop {{r4}}\npop {{r1}}\nbx r1"


@unittest.skipUnless(BINUTILS, "ARM binutils required")
class WalkTests(unittest.TestCase):
    def setUp(self):
        scratch_dir = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch_dir.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="r12_exit_", dir=scratch_dir)
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)

    def build(self, owner, **functions):
        functions = dict(owner=owner, **functions)
        labels = [label for name in functions for label in (name, name + "_end")]
        text = ".syntax unified\n.arch armv4t\n.thumb\n.text\n.global " + ", ".join(labels) + "\n"
        for index, (name, body) in enumerate(functions.items()):
            text += f".org 0x{0x100 * index:x}\n{name}:\n{body}\n{name}_end:\n"
        (self.root / "f.s").write_text(text)
        for command in (
                ["arm-none-eabi-as", "-mthumb-interwork", str(self.root / "f.s"), "-o", str(self.root / "f.o")],
                ["arm-none-eabi-ld", "-Ttext=0x08000000", "-e", "owner", str(self.root / "f.o"),
                 "-o", str(self.root / "f.elf")],
                ["arm-none-eabi-objcopy", "-O", "binary", "--only-section=.text", str(self.root / "f.elf"),
                 str(self.root / "f.bin")]):
            subprocess.run(command, check=True, capture_output=True)
        self.symbols = {s["name"]: s["value"] for s in match.elf_image((self.root / "f.elf").read_bytes())["symbols"]}
        self.rom = (self.root / "f.bin").read_bytes()
        self.mapping = json.dumps([{"rom": f"0x{self.symbols[n]:08X}", "end": f"0x{self.symbols[n + '_end']:08X}",
                                    "mode": "thumb"} for n in functions]).encode()
        return self.rom[:self.symbols["owner_end"] - BASE]

    def proof(self, kind="v2", enabled=True):
        """The default path's proof (it keeps the ledger), or with `enabled` False a subclass, as a
        profile's proof that does not print the line is."""
        if kind == "v1":
            return match.BufferCallProof(self.rom, self.mapping, loop_replay=True, bios_wrappers=True)
        if enabled:
            return match.BufferCallProof(self.rom, self.mapping, stack_arguments=True, loop_replay=True,
                                         bios_wrappers=True, dead_registers=True)
        return type("Profile", (match.BufferCallProof,), {})(self.rom, self.mapping, stack_arguments=True)

    def walk(self, owner, *, kind="v2", enabled=True, ledger=None, **functions):
        body = self.build(owner, **functions)
        proof = None if kind is None else self.proof(kind, enabled)
        match.verify_leaf_instructions(body, BASE, True, buffer_proof=proof,
                                       call_resolver=proof.target if proof is not None else None,
                                       incoming_narrow_reads=enabled, return_scratch=ledger)
        return proof

    def returns(self):
        """The owner's final `bx r1`."""
        return self.symbols["owner_end"] - 2

    # A walked callee's return ------------------------------------------------------------------

    def test_a_walked_callees_frame_address_in_ip_refuses(self):
        # The issue's reproduction: the owner reads IP after the call and hands it to E.
        with self.assertRaisesRegex(ValueError, f"{ESCAPE}: r12 at a walked callee's return"):
            self.walk(OWNER, func_X12=X12, func_E=E)

    def test_it_refuses_whether_or_not_the_caller_reads_ip(self):
        owner = frame("mov r0, sp\nbl func_X12\nmovs r0, #0")
        with self.assertRaisesRegex(ValueError, f"{ESCAPE}: r12 at a walked callee's return"):
            self.walk(owner, func_X12=X12)

    def test_a_callee_that_leaves_zero_in_ip_is_admitted_unchanged(self):
        x12 = X12.replace("mov r3, sp\nmov ip, r3", "movs r3, #0\nmov ip, r3")
        proof = self.walk(OWNER, func_X12=x12, func_E=E)
        self.assertEqual((r12_exit.sites(proof), proof.exit_r12_lines()), ([], []))
        plain = self.walk(OWNER, enabled=False, func_X12=x12, func_E=E)
        self.assertEqual(proof.fingerprint(), plain.fingerprint())

    def test_a_nested_callees_frame_address_in_ip_refuses(self):
        outer = "push {lr}\nbl func_X12\nmovs r1, #0\nmov ip, r1\npop {r0}\nbx r0"
        owner = frame("mov r0, sp\nbl func_A\nmovs r0, #0")
        with self.assertRaisesRegex(ValueError, f"{ESCAPE}: r12 at a walked callee's return"):
            self.walk(owner, func_A=outer, func_X12=X12)

    def test_the_dead_register_fallback_keeps_the_refusal(self):
        # The callee writes r0 before reading it, so the dead-register rule would take the call as one
        # that receives no stack address; its inspection refused at its return, so the refusal stands.
        callee = ("push {lr}\nsub sp, #8\nmovs r0, #0\nmov r3, sp\nmov ip, r3\nmovs r3, #0\nadd sp, #8\n"
                  "pop {r1}\nbx r1")
        owner = frame("mov r0, sp\nbl func_D\nmovs r0, #0")
        with self.assertRaisesRegex(ValueError, f"{ESCAPE}: r12 at a walked callee's return"):
            self.walk(owner, func_D=callee)
        # The same callee without the address is the dead-register rule's alias-free call.
        self.walk(owner, func_D=callee.replace("mov r3, sp\nmov ip, r3", "movs r3, #0\nmov ip, r3"))

    def test_a_version_one_callee_refuses(self):
        owner = frame("mov r0, sp\nbl func_X12\nmovs r0, #0")
        with self.assertRaisesRegex(ValueError, f"{ESCAPE}: r12 at a return of a walk without a stack-argument"):
            self.walk(owner, kind="v1", func_X12=X12)

    # The root's own return ---------------------------------------------------------------------

    def test_the_roots_frame_address_in_ip_is_stated(self):
        proof = self.walk(frame("add r3, sp, #4\nmov ip, r3\nmovs r3, #0\nmovs r0, #0"))
        site = self.returns()
        self.assertEqual(r12_exit.sites(proof), [(site, -12)])
        self.assertEqual(proof.exit_r12_lines(), [
            f"* buffer exit scratch r12: `thumb-discarded-exit-scratch-r12-v1` {r12_exit.CONTRACT}; "
            f"`0x{site:08X} r12 -12`"])
        bound = proof.fingerprint()
        proof.r12_exit_scratch = {(site, -8)}
        self.assertNotEqual(proof.fingerprint(), bound)
        proof.r12_exit_scratch = set()
        self.assertNotEqual(proof.fingerprint(), bound)
        self.assertEqual(proof.exit_r12_lines(), [])

    def test_a_root_whose_report_does_not_state_it_refuses(self):
        with self.assertRaisesRegex(ValueError, f"{ESCAPE}: r12 at a root return whose report does not state"):
            self.walk(frame("add r3, sp, #4\nmov ip, r3\nmovs r3, #0\nmovs r0, #0"), enabled=False)

    def test_an_address_at_or_above_the_entry_sp_refuses(self):
        # After the frame is released, sp+0 and up is the caller's own stack: no premise covers it.
        with self.assertRaisesRegex(ValueError, "at or above the entry SP"):
            self.walk("mov ip, sp\nbx lr")

    def test_walks_without_a_stack_argument_proof_refuse(self):
        body = "sub sp, #8\nmov ip, sp\nmovs r0, #0\nadd sp, #8\nbx lr"
        for kind, ledger in (("v1", None), (None, None), (None, scratch.ReturnScratch())):
            with self.subTest(kind=kind, ledger=ledger is not None), \
                    self.assertRaisesRegex(ValueError, f"{ESCAPE}: r12 at a return of a walk without"):
                self.walk(body, kind=kind, ledger=ledger)

    def test_result_and_scratch_register_messages_are_unchanged(self):
        # R0-R3 are checked first, with their own messages; R12 only after them.
        with self.assertRaisesRegex(ValueError, f"^{ESCAPE}$"):
            self.walk(frame("mov r0, sp\nmov r3, sp\nmov ip, r3"))

    def test_only_the_default_paths_two_stack_argument_proofs_keep_the_ledger(self):
        self.build("bx lr")
        for kind, options, kept in ((match.BufferCallProof, dict(stack_arguments=True), True),
                                    (match.FunctionBufferCallProof, dict(stack_arguments=True), True),
                                    (match.BufferCallProof, {}, False),
                                    (type("Profile", (match.BufferCallProof,), {}), dict(stack_arguments=True), False)):
            with self.subTest(kind=kind.__name__, options=options):
                proof = kind(self.rom, self.mapping, **options)
                self.assertEqual(proof.r12_exit_scratch is not None, kept)
                self.assertIs(r12_exit.enable(proof), proof)
                self.assertEqual(proof.r12_exit_scratch, set())

    def test_the_check_needs_a_ledger_an_inactive_proof_and_a_negative_offset(self):
        class Stub:
            active = set()
            r12_exit_scratch = None
        aliases = {match.ARM_REG_R12: -4}
        with self.assertRaisesRegex(ValueError, "does not state"):
            r12_exit.check(aliases, BASE, Stub(), True)
        stub = r12_exit.enable(Stub())
        r12_exit.check(aliases, BASE, stub, True)
        self.assertEqual(r12_exit.sites(stub), [(BASE, -4)])
        stub.active = {BASE + 0x100}
        with self.assertRaisesRegex(ValueError, "walked callee"):
            r12_exit.check(aliases, BASE, stub, True)
        stub.active = set()
        for value in (0, 4, ("pointer", -4)):
            with self.subTest(value=value), self.assertRaisesRegex(ValueError, "at or above"):
                r12_exit.check({match.ARM_REG_R12: value}, BASE, stub, True)
        with self.assertRaisesRegex(ValueError, "without a stack-argument"):
            r12_exit.check(aliases, BASE, stub, False)
        r12_exit.check({match.ARM_REG_R0 + 3: -4}, BASE, None, False)     # not this rule's register


# The 0x080A9B00 shape from natural C: agbcc keeps &first_output in IP across the loops, so the
# root returns with its own frame address in IP.  func_08000400 writes the two outputs.
ROOT_C = """typedef unsigned char u8;
typedef signed short s16;
typedef unsigned short u16;
typedef signed int s32;

typedef struct {
    u8 unknown_00[0x2E];
    s16 inputs[3];
    u8 unknown_34[4];
    u16 value_38;
    u8 unknown_3A[4];
    s16 first_values[3];
    s16 second_values[3];
    u16 stored_values[3];
    s16 counters[3];
} Record;

extern void func_08000400(s16 first, s16 second, s16 third, s16 *first_output, s16 *second_output);

void func_08000200(Record *record)
{
    s16 first_output;
    s16 second_output;
    s32 i;

    func_08000400(record->inputs[0], record->inputs[1], record->inputs[2], &first_output, &second_output);
    for (i = 0; i < 3; i++) {
        if (record->counters[i] > 6)
            return;
        if (record->counters[i] > 0 &&
            record->first_values[i] == first_output &&
            record->second_values[i] == second_output)
            return;
    }
    for (i = 0; i < 3; i++) {
        if (record->counters[i] <= 0) {
            record->counters[i] = 8;
            record->first_values[i] = first_output;
            record->second_values[i] = second_output;
            record->stored_values[i] = record->value_38;
            return;
        }
    }
}
"""
OUTPUTS = "movs r0, #0\nstrh r0, [r3]\nldr r1, [sp]\nstrh r0, [r1]\nmovs r1, #0\nmovs r3, #0\nbx lr"
BUFFER_ONLY = """typedef unsigned short u16;
extern void func_08000400(u16 value, u16 *out);
u16 func_08000200(u16 value)
{
    u16 buffer[4];

    func_08000400(value, buffer);
    return buffer[0] + buffer[3];
}
"""
CALLEE_IP = ("push {lr}\nsub sp, #8\nmovs r0, #0\nstrh r0, [r1]\nmov r3, sp\nmov ip, r3\nmovs r3, #0\n"
             "add sp, #8\npop {r0}\nbx r0")

try:
    from test_data_buffer_calls import A, build as data_buffer_tree, run as run_match, tools_present
    import match_evidence
except ImportError:            # pragma: no cover - the sibling fixtures are part of the suite
    tools_present = lambda: False


@unittest.skipUnless(tools_present(), "fixed compiler and ARM tools required")
class SubprocessTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        scratch_dir = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch_dir.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix="r12_exit_sub_", dir=scratch_dir)
        cls.base = Path(cls.temporary.name)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def replays(self, text, root):
        with patch.dict(os.environ, FFTA_ROM=str(root / "baserom.bin")):
            return match_evidence.report_matches(text, root, A)

    def test_a_root_return_in_ip_is_stated_at_issuance_and_bound_in_replay(self):
        root = data_buffer_tree(self.base / "root", ROOT_C, [("func_08000400", OUTPUTS)])
        code, output, text = run_match(root)
        self.assertEqual(code, 0, output[-2000:])
        lines = [line for line in text.splitlines() if line.startswith(r12_exit.FIELD + ":")]
        self.assertEqual(len(lines), 1, text)
        self.assertIn(f"`{r12_exit.SCHEMA}` {r12_exit.CONTRACT}; `0x", lines[0])
        self.assertTrue(self.replays(text, root))
        self.assertFalse(self.replays(text.replace(lines[0] + "\n", ""), root))
        edited = lines[0].replace(" r12 -", " r12 -1")
        self.assertNotEqual(edited, lines[0])
        self.assertFalse(self.replays(text.replace(lines[0], edited), root))

    def test_a_data_buffer_root_return_in_ip_is_stated_and_bound(self):
        # The same root reading a typed data word: the data-buffer route (data_buffer_profile).
        source = ROOT_C.replace("extern void func_08000400", "extern u16 data_02000000[];\nextern void func_08000400")
        source = source.replace("record->stored_values[i] = record->value_38;",
                                "record->stored_values[i] = data_02000000[0];")
        root = data_buffer_tree(self.base / "data", source, [("func_08000400", OUTPUTS)])
        code, output, text = run_match(root)
        self.assertEqual(code, 0, output[-2000:])
        self.assertIn("* verification: `elf-symbol-thumb-data-buffer-calls-v1`", text)
        lines = [line for line in text.splitlines() if line.startswith(r12_exit.FIELD + ":")]
        self.assertEqual(len(lines), 1, text)
        self.assertTrue(self.replays(text, root))
        self.assertFalse(self.replays(text.replace(lines[0] + "\n", ""), root))

    def test_a_walked_callees_frame_address_in_ip_refuses_at_issuance(self):
        root = data_buffer_tree(self.base / "callee", BUFFER_ONLY, [("func_08000400", CALLEE_IP)])
        code, output, text = run_match(root)
        self.assertNotEqual(code, 0, output[-2000:])
        self.assertIn(f"{ESCAPE}: r12 at", output)
        # The control: the same callee leaving 0 in IP matches and states nothing.
        root = data_buffer_tree(self.base / "control", BUFFER_ONLY,
                                [("func_08000400", CALLEE_IP.replace("mov r3, sp\nmov ip, r3", "mov ip, r3"))])
        code, output, text = run_match(root)
        self.assertEqual(code, 0, output[-2000:])
        self.assertNotIn(r12_exit.FIELD, text)


CALLEE_C = """typedef signed short s16;
void func_08000400(s16 first, s16 second, s16 third, s16 *first_output, s16 *second_output)
{
    *first_output = first + third;
    *second_output = second;
}
"""


def owner_fixture(root):
    """ROOT_C at A and CALLEE_C at 0x08000400, linked as the complete-owner route links them, with
    the function index and the (empty) data map a complete-owner report binds."""
    import argparse
    import owner_admission_profile as owner
    import named_data_buffer_profile as named
    root = Path(root)
    for name in ("src", "include", "config", "symbols", "build"):
        (root / name).mkdir(parents=True, exist_ok=True)
    args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                              objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
    objects = b"{}\n"
    runner = match.Runner(match.DEFAULT_CC, root=root, wsl_path=match.DEFAULT_WSL_PATH, timeout=120)
    callee = BASE + 0x400
    rom = bytearray(callee - BASE + 0x100)
    with runner.workspace() as workspace:
        (root / "src/08000400.c").write_text(CALLEE_C)
        _, body, _ = match.compile_object(runner, workspace, args, root, callee, "src/08000400.c")
        (root / "src/08000400.c").unlink()
        body = bytes(body[:-2] if body.endswith(b"\xc0\x46") else body)
        rom[callee - BASE:callee - BASE + len(body)] = body
        (root / "src/08000200.c").write_text(ROOT_C)
        _, own, image = match.compile_object(runner, workspace, args, root, A, "src/08000200.c")
        rows = [{"rom": f"0x{A:08X}", "end": f"0x{A + len(own):08X}", "mode": "thumb", "instrs": 0},
                {"rom": f"0x{callee:08X}", "end": f"0x{callee + len(body):08X}", "mode": "thumb", "instrs": 0}]
        mapping = json.dumps(rows).encode()
        data, _ = owner.object_bytes(runner, workspace, args, image, A, bytes(rom), mapping, objects,
                                     selector=named.DATAFREE_SELECTOR)
    rom[A - BASE:A - BASE + len(data)] = data
    for row, address, code in zip(rows, (A, callee), (data, body)):
        row["instrs"] = owner.refine(code, address, mapping)["instrs"]
    mapping = json.dumps(rows, indent=2).encode()
    (root / "config/functions.json").write_bytes(mapping)
    (root / "config/data_symbols.json").write_bytes(objects)
    (root / "symbols/functions.txt").write_text("".join(
        f"{int(r['rom'], 16):08X} {int(r['end'], 16):08X} {int(r['end'], 16) - int(r['rom'], 16)} {r['instrs']} return\n"
        for r in rows))
    (root / "baserom.bin").write_bytes(bytes(rom))
    return root


@unittest.skipUnless(tools_present(), "fixed compiler and ARM tools required")
class OwnerRouteTests(unittest.TestCase):
    """The complete-owner route (owner_admission_profile): the root's R12 site is recorded in the
    owner manifest, printed on its own line, and the report replays only with it."""

    def test_the_owner_manifest_records_and_prints_the_root_return(self):
        import owner_admission_profile as owner
        import named_data_buffer_profile as named
        scratch_dir = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch_dir.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="r12_exit_owner_", dir=scratch_dir) as directory:
            root = owner_fixture(Path(directory) / "owner")
            with patch.dict(os.environ, FFTA_ROM=str(root / "baserom.bin")):
                result = owner.build(root, A, selector=named.DATAFREE_SELECTOR)
                report = owner.render(A, result)
                recorded = result[1]["proof"]["buffers"]["r12_exit_scratch"]
                self.assertEqual(len(recorded), 1)
                self.assertRegex(recorded[0], r"^\* buffer exit scratch r12: `thumb-discarded-exit-scratch-r12-v1` "
                                              r".*; `0x[0-9A-F]{8} r12 -\d+`$")
                self.assertEqual([line for line in report.splitlines() if line.startswith(r12_exit.FIELD)], recorded)
                self.assertTrue(match_evidence.report_matches(report, root, A))
                self.assertFalse(match_evidence.report_matches(report.replace(recorded[0] + "\n", ""), root, A))
                edited = recorded[0].replace(" r12 -", " r12 -1")
                self.assertFalse(match_evidence.report_matches(report.replace(recorded[0], edited), root, A))


if __name__ == "__main__":
    unittest.main()
