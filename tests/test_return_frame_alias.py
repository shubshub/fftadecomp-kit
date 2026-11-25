"""A frame address in a return register, in walks without a stack-argument proof (kit #538).

Synthetic walks need only the assembler; the native tests compile C with the
fixed compiler and run match.py on the default path. No game ROM is needed.
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
import match_evidence as evidence
import plain_report_fields
import return_scratch_profile as scratch

BASE = match.ROM_BASE
CALLEE = BASE + 0x100
ESCAPE = "local stack pointer escapes through a return register"
R0 = match.ARM_REG_R0


class ReturnCheckTests(unittest.TestCase):
    """The return check of the walks without a stack-argument proof, on assembled bodies."""

    def setUp(self):
        scratch_dir = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch_dir.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="return_frame_alias_", dir=scratch_dir)
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)

    def build(self, caller, callee="bx lr"):
        text = (".syntax unified\n.arch armv4t\n.thumb\n.text\n.global caller, caller_end, callee, callee_end\n"
                f"caller:\n{caller}\n.align 2\ncaller_end:\n.org 0x100\ncallee:\n{callee}\ncallee_end:\n")
        (self.root / "f.s").write_text(text)
        for command in (
                ["arm-none-eabi-as", "-mthumb-interwork", str(self.root / "f.s"), "-o", str(self.root / "f.o")],
                ["arm-none-eabi-ld", "-Ttext=0x08000000", "-e", "caller", str(self.root / "f.o"),
                 "-o", str(self.root / "f.elf")],
                ["arm-none-eabi-objcopy", "-O", "binary", "--only-section=.text", str(self.root / "f.elf"),
                 str(self.root / "rom.bin")]):
            subprocess.run(command, check=True, capture_output=True)
        image = match.elf_image((self.root / "f.elf").read_bytes())
        symbols = {symbol["name"]: symbol["value"] for symbol in image["symbols"]}
        self.rom = (self.root / "rom.bin").read_bytes()
        self.mapping = json.dumps([{"rom": f"0x{symbols[name]:08X}", "end": f"0x{symbols[name + '_end']:08X}",
                                    "mode": "thumb"} for name in ("caller", "callee")]).encode()
        return self.rom[:symbols["caller_end"] - BASE]

    def walk(self, caller, *, ledger=None, callee="bx lr", proof=None):
        body = self.build(caller, callee)
        if proof == "v1":
            proof = match.BufferCallProof(self.rom, self.mapping, loop_replay=True, bios_wrappers=True)
        elif proof == "v2":
            proof = match.BufferCallProof(self.rom, self.mapping, stack_arguments=True, loop_replay=True)
        elif proof == "v2-dead":
            proof = match.BufferCallProof(self.rom, self.mapping, stack_arguments=True, loop_replay=True,
                                          dead_registers=True)
        return match.verify_leaf_instructions(body, BASE, True, buffer_proof=proof,
                                              call_resolver=proof.target if proof is not None else None,
                                              return_scratch=ledger)

    @staticmethod
    def frame(body, registers="r4"):
        return f"push {{{registers}, lr}}\nsub sp, #8\n{body}\nadd sp, #8\npop {{{registers}}}\npop {{r1}}\nbx r1"

    def test_an_acyclic_owner_walk_records_r2_scratch_in_its_ledger(self):
        # The 0809C9E8 shape: the exact-path (acyclic) walk of a restoring owner returns with a dead frame
        # address in R2. Without a ledger it refuses; with one it is admitted and the site is recorded.
        body = self.build(self.frame("add r2, sp, #4\nmovs r0, #0\nstrh r0, [r2]"))
        walk = lambda ledger: match.verify_leaf_instructions(body, BASE, True, acyclic_state_budget=64,
                                                             return_scratch=ledger)
        with self.assertRaisesRegex(ValueError, ESCAPE):
            walk(None)
        ledger = scratch.ReturnScratch()
        walk(ledger)
        (site, register, offset), = ledger.sites
        self.assertEqual((register, offset), (2, -12))
        self.assertEqual(scratch.manifest(ledger), {
            "schema": "thumb-discarded-exit-scratch-v1", "registers": [2, 3],
            "contract": "r2/r3 are discarded scratch at external returns; no result values are returned through them",
            "residual_aliases": [[site, 2, -12, True]], "native_nonescape_proof": False})

    def test_every_return_form_is_checked(self):
        for name, body in (("pop {pc}", "push {lr}\nsub sp, #8\nmov r0, sp\nadd sp, #8\npop {pc}"),
                           ("pop {r4, pc}", "push {r4, lr}\nsub sp, #8\nmov r0, sp\nadd sp, #8\npop {r4, pc}"),
                           ("mov pc, lr", "sub sp, #8\nmov r0, sp\nadd sp, #8\nmov pc, lr"),
                           ("bx through r3", "sub sp, #8\nmov r0, sp\nadd sp, #8\nmov r3, lr\nbx r3")):
            with self.subTest(form=name), self.assertRaisesRegex(ValueError, ESCAPE):
                self.walk(body)

    def test_exact_path_state_walks_check_their_returns(self):
        # The acyclic (exact path state) walk: a frame address on one path only reaches the return without a
        # join to refuse it, so the return check is the one that must.
        def walk(body, ledger=None):
            return match.verify_leaf_instructions(self.build(body), BASE, True, acyclic_state_budget=64,
                                                  return_scratch=ledger)
        r0 = "sub sp, #8\nmovs r0, #0\ncmp r1, #0\nbeq 1f\nmov r0, sp\n1:\nadd sp, #8\nbx lr"
        r3 = "sub sp, #8\nmovs r3, #0\ncmp r1, #0\nbeq 1f\nmov r3, sp\n1:\nmovs r0, #0\nadd sp, #8\nbx lr"
        for ledger in (None, scratch.ReturnScratch()):
            with self.subTest(ledger=ledger is not None), self.assertRaisesRegex(ValueError, ESCAPE):
                walk(r0, ledger)
        with self.assertRaisesRegex(ValueError, ESCAPE):
            walk(r3)
        ledger = scratch.ReturnScratch()
        walk(r3, ledger)
        self.assertEqual([(register, offset) for _, register, offset in ledger.sites], [(3, -8)])

    def test_a_dead_register_call_keeps_a_callee_frame_return_refused(self):
        # The callee writes r0 before reading it, so the dead-register rule would take the call as one that
        # receives no stack address; but its inspection refused because it returns its own frame in r0.
        callee = "sub sp, #4\nmov r0, sp\nadd sp, #4\nbx lr"
        with self.assertRaisesRegex(ValueError, ESCAPE):
            self.walk(self.frame("mov r0, sp\nbl callee\nmovs r0, #0"), callee=callee, proof="v2-dead")

    def test_result_registers_refuse_with_or_without_the_ledger(self):
        for register in ("r0", "r1"):
            for ledger in (None, scratch.ReturnScratch()):
                with self.subTest(register=register, ledger=ledger is not None):
                    with self.assertRaisesRegex(ValueError, ESCAPE):
                        self.walk(f"sub sp, #8\nmov {register}, sp\nadd sp, #8\nbx lr", ledger=ledger)

    def test_scratch_registers_need_the_ledger_and_are_recorded(self):
        for register in (2, 3):
            body = f"sub sp, #8\nadd r{register}, sp, #4\nmovs r0, #0\nadd sp, #8\nbx lr"
            with self.subTest(register=register):
                with self.assertRaisesRegex(ValueError, ESCAPE):
                    self.walk(body)
                ledger = scratch.ReturnScratch()
                self.walk(body, ledger=ledger)
                self.assertEqual(ledger.sites, {(BASE + 8, register, -4)})
                self.assertEqual(ledger.report_lines(), [
                    scratch.PREMISE, f"* stack frame exit scratch: `0x{BASE + 8:08X} r{register} -4`"])

    def test_ip_keeps_its_exemption_and_unaliased_returns_record_nothing(self):
        ledger = scratch.ReturnScratch()
        self.walk("sub sp, #8\nmov ip, sp\nmovs r0, #0\nadd sp, #8\nbx lr", ledger=ledger)
        self.walk("sub sp, #8\nmov r3, sp\nmovs r3, #0\nadd sp, #8\nbx lr", ledger=ledger)
        self.assertEqual((ledger.sites, ledger.report_lines()), (set(), []))

    def test_an_address_into_the_callers_frame_refuses_even_in_r3(self):
        # sp+8 after the frame is released is the caller's stack: no premise covers it.
        with self.assertRaisesRegex(ValueError, ESCAPE):
            scratch.ReturnScratch().admit(BASE, {3: 0})
        with self.assertRaisesRegex(ValueError, ESCAPE):
            scratch.ReturnScratch().admit(BASE, {3: 4})

    def test_a_version_one_callee_that_returns_its_own_frame_refuses(self):
        owner = self.frame("mov r0, sp\nbl callee\nmovs r0, #0")
        for callee in ("sub sp, #4\nmov r0, sp\nadd sp, #4\nbx lr",
                       "sub sp, #4\nmov r2, sp\nmovs r0, #0\nadd sp, #4\nbx lr"):
            with self.subTest(callee=callee), self.assertRaisesRegex(ValueError, ESCAPE):
                self.walk(owner, callee=callee, proof="v1")
        # The same callee without the leftover is an ordinary inspected callee.
        self.walk(owner, callee="sub sp, #4\nmovs r0, #0\nadd sp, #4\nbx lr", proof="v1")

    def test_the_ledger_belongs_to_root_walks_without_stack_arguments(self):
        with self.assertRaisesRegex(ValueError, "return scratch requires a root walk"):
            self.walk("bx lr", ledger=scratch.ReturnScratch(), proof="v2")
        with self.assertRaisesRegex(ValueError, "return scratch requires a root walk"):
            self.walk("bx lr", ledger=object())

    def test_report_fields_allow_the_lines_only_on_plain_framed_schemas(self):
        lines = [scratch.PREMISE, "* stack frame exit scratch: `0x08000208 r3 -4`"]
        for schema in (evidence.FRAMED_SCHEMA, evidence.FRAMED_LINKED_SCHEMA, evidence.FRAMED_DATA_SCHEMA):
            self.assertIn(scratch.MARKER, plain_report_fields.layout(schema)[2])
        for schema in (evidence.SCHEMA, evidence.LINKED_SCHEMA, evidence.DATA_SCHEMA, evidence.BUFFER_SCHEMA,
                       evidence.STACK_BUFFER_SCHEMA):
            self.assertNotIn(scratch.MARKER, plain_report_fields.layout(schema)[2])
        self.assertEqual(scratch.report_fields(["* stack frame: x", *lines, "* other: y"]), lines)


SOURCES = {
    # The issue's first fixture: a leaf returning its own array.
    "leaf": """typedef unsigned short u16;
u16 *func_08000200(u16 value)
{
    u16 buf[4];
    buf[0] = value;
    buf[1] = value + 1;
    return buf;
}
""",
    # The issue's second fixture: the same after a call, so no alias crosses it.
    "after_call": """typedef unsigned short u16;
extern void func_08000400(u16 value, u16 *out);
u16 *func_08000200(u16 value)
{
    u16 buf[4];
    func_08000400(value, 0);
    buf[0] = value;
    buf[1] = value + 1;
    return buf;
}
""",
    # The composition one level down: F (func_08000400) returns its own expired frame, the owner passes it
    # on to G; one more buffer call keeps the owner's buffer evidence.
    "dead_register_composition": """extern unsigned *func_08000400(unsigned *ignored);
extern void func_08000500(unsigned *p, unsigned v);
extern void func_08000600(unsigned *out);
void func_08000200(unsigned v)
{
    unsigned local[1];
    unsigned other[1];
    func_08000600(other);
    local[0] = v + other[0];
    func_08000500(func_08000400(local), v);
}
""",
    # A version-1 buffer owner that leaves a local's address in R2 at its return: no premise on a buffer schema.
    "buffer_owner_r2_scratch": """typedef short s16;
extern void func_08000400(s16 *p);
static inline void put(s16 a, s16 b, s16 *x, s16 *h, s16 *y)
{
    *x = a * 32 + 16;
    *h = 0;
    *y = b * 32 + 16;
}
void func_08000200(const signed char *tile, s16 *world)
{
    s16 height;
    s16 tmp;
    func_08000400(&tmp);
    put(tile[0], tile[1], &world[0], &height, &world[1]);
}
""",
    # A local whose address is left in R2 at the return, as in 0809C9E8 (restoring-owner-acyclic-v1).
    "r2_scratch": """typedef short s16;
static inline void put(s16 a, s16 *h, s16 *x)
{
    *x = a * 32 + 16;
    *h = 0;
}
void func_08000200(const signed char *tile, s16 *world)
{
    s16 height;
    put(tile[0], &height, &world[0]);
}
""",
    # A local whose address is left in R3 at the return, as in three merged reports.
    "r3_scratch": """typedef short s16;
static inline void put(s16 a, s16 b, s16 *x, s16 *h, s16 *y)
{
    *x = a * 32 + 16;
    *h = 0;
    *y = b * 32 + 16;
}
void func_08000200(const signed char *tile, s16 *world)
{
    s16 height;
    put(tile[0], tile[1], &world[0], &height, &world[1]);
}
""",
}
CALLEES = [("func_08000400", "bx lr")]
FIXTURE_CALLEES = {
    "dead_register_composition": [
        ("func_08000400", "sub sp, #4\nmovs r1, #0\nstr r1, [sp]\nmov r0, sp\nadd sp, #4\nbx lr"),
        ("func_08000500", "str r1, [r0]\nbx lr"),
        ("func_08000600", "movs r1, #0\nstr r1, [r0]\nmovs r0, #0\nbx lr")],
    "buffer_owner_r2_scratch": [("func_08000400", "movs r1, #0\nstr r1, [r0]\nmovs r0, #0\nbx lr")],
}


def tools_present():
    import shutil
    return Path(os.path.expandvars(match.DEFAULT_CC)).is_file() and \
        all(shutil.which(tool) for tool in (match.DEFAULT_AS, match.DEFAULT_LD, match.DEFAULT_OBJCOPY))


@unittest.skipUnless(tools_present(), "fixed compiler and ARM tools required")
class ReturnFrameAliasNativeTests(unittest.TestCase):
    """agbcc-compiled owners through match.py's default path, and their reports' replay."""

    def setUp(self):
        scratch_dir = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch_dir.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="return_frame_alias_native_", dir=scratch_dir)
        self.addCleanup(directory.cleanup)
        self.base = Path(directory.name)

    def run_fixture(self, name):
        import test_data_buffer_calls as data_calls
        build = data_calls.build
        callees = FIXTURE_CALLEES.get(name, CALLEES)
        if name not in ("after_call", *FIXTURE_CALLEES):
            def unlinked(runner, workspace, args, original, address, *rest, **options):
                symbol, offset = match.function_record(original, f"func_{address:08X}", address, True)
                return original["text"][offset:offset + symbol["size"]], {}, {}
            with patch.object(match, "link_calls", unlinked):
                root = build(self.base / name, SOURCES[name], callees)
        else:
            root = build(self.base / name, SOURCES[name], callees)
        return (root, *data_calls.run(root))

    def test_a_returned_own_frame_address_is_refused(self):
        for name in ("leaf", "after_call"):
            with self.subTest(fixture=name):
                _, code, output, report = self.run_fixture(name)
                self.assertNotEqual(code, 0, output)
                self.assertIsNone(report)
                self.assertIn(ESCAPE, output)

    def test_an_r3_scratch_leftover_states_the_premise_and_replays(self):
        root, code, output, report = self.run_fixture("r3_scratch")
        self.assertEqual(code, 0, output)
        lines = report.splitlines()
        self.assertIn(f"* verification: `{evidence.FRAMED_SCHEMA}`", lines)
        start = lines.index(f"* stack frame: {evidence.STACK_SUMMARY}")
        premise, sites = lines[start + 1:start + 3]
        self.assertEqual(premise, "* stack frame exit scratch premise: `thumb-discarded-exit-scratch-v1` r2/r3 are "
                                  "discarded scratch at external returns; no result values are returned through them")
        self.assertRegex(sites, r"^\* stack frame exit scratch: `0x0800[0-9A-F]{4} r3 -[0-9]+`$")
        with patch.dict(os.environ, FFTA_ROM=str(root / "baserom.bin")):
            self.assertTrue(evidence.report_matches(report, root, 0x08000200))
            for edited in (report.replace(premise + "\n", "").replace(sites + "\n", ""),
                           report.replace(sites + "\n", ""),
                           report.replace(premise + "\n", ""),
                           report.replace(" r3 ", " r2 "),
                           report.replace(sites, sites.replace("`0x", "`0x1")),
                           report.replace(sites + "\n", sites + "\n" + sites + "\n"),
                           report.replace(evidence.FRAMED_SCHEMA, evidence.SCHEMA)):
                with self.subTest(edited=edited[:0]):
                    self.assertNotEqual(edited, report)
                    self.assertFalse(evidence.report_matches(edited, root, 0x08000200))


    def test_a_dead_register_call_never_hands_on_a_returned_frame(self):
        # Kit main admits the owner: the plain walk did not look at F's return, and the dead-register rule took
        # F's refused inspection as a call that receives no stack address.
        _, code, output, report = self.run_fixture("dead_register_composition")
        self.assertNotEqual(code, 0, output)
        self.assertIsNone(report)
        self.assertIn(ESCAPE, output)

    def test_a_buffer_owner_with_r2_scratch_is_refused(self):
        # The premise lines belong to the plain framed schemas only; a buffer report cannot state them.
        _, code, output, report = self.run_fixture("buffer_owner_r2_scratch")
        self.assertNotEqual(code, 0, output)
        self.assertIsNone(report)
        self.assertIn(ESCAPE, output)

    def test_an_acyclic_owner_records_r2_scratch_in_its_evidence_and_replays(self):
        import owner_admission_profile as owner
        root, code, output, report = self.run_fixture("r2_scratch")
        self.assertEqual(code, 0, output)
        self.assertIn("* stack frame exit scratch: `0x", report)
        # The restoring owner binds each row's reachable instruction count.
        rom = (root / "baserom.bin").read_bytes()
        rows = json.loads((root / "config/functions.json").read_text())
        mapping = json.dumps(rows).encode()
        for row in rows:
            start, end = int(row["rom"], 16), int(row["end"], 16)
            row["instrs"] = owner.refine(rom[start - BASE:end - BASE], start, mapping)["instrs"]
        (root / "config/functions.json").write_text(json.dumps(rows))
        (root / "symbols/functions.txt").write_text("".join(
            f"{int(row['rom'], 16):08X} {int(row['end'], 16):08X} {int(row['end'], 16) - int(row['rom'], 16)} "
            f"{row['instrs']} return\n" for row in rows))
        environment = dict(os.environ, FFTA_ROM=str(root / "baserom.bin"), PYTHONDONTWRITEBYTECODE="1")
        run = subprocess.run([sys.executable, str(ROOT / "tools/match.py"), "--root", str(root), "0x08000200",
                              "--owner-runtime-profile", owner.ACYCLIC_SELECTOR],
                             capture_output=True, text=True, env=environment, timeout=600)
        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
        report = (root / "docs/match/08000200.md").read_text()
        self.assertIn(f"* owner runtime: {owner.ACYCLIC_SELECTOR}", report.splitlines())
        (line,) = [line for line in report.splitlines() if line.startswith("* owner runtime evidence: `")]
        manifest = json.loads(line[len("* owner runtime evidence: `"):-1])["manifest"]
        record = manifest["proof"]["discarded_exit_scratch"]
        self.assertEqual({key: record[key] for key in ("schema", "registers", "contract")},
                         {"schema": "thumb-discarded-exit-scratch-v1", "registers": [2, 3],
                          "contract": "r2/r3 are discarded scratch at external returns; no result values are "
                                      "returned through them"})
        # The rows have the frame proof's shape: (site, register, entry-SP offset, live).
        ((site, register, offset, live),) = record["residual_aliases"]
        self.assertEqual((register, live, record["native_nonescape_proof"]), (2, True, False))
        self.assertLess(offset, 0)
        with patch.dict(os.environ, FFTA_ROM=str(root / "baserom.bin")):
            self.assertTrue(evidence.report_matches(report, root, 0x08000200))
            # The rebuilt proof must carry the record, so a report without it does not replay.
            stripped = json.loads(line[len("* owner runtime evidence: `"):-1])
            del stripped["manifest"]["proof"]["discarded_exit_scratch"]
            edited = report.replace(line, "* owner runtime evidence: `" + owner.text(stripped) + "`")
            self.assertNotEqual(edited, report)
            self.assertFalse(evidence.report_matches(edited, root, 0x08000200))


COMPOSITION = {
    # C forwards F's result to G; G writes v through it and calls H. On kit main all four matched, and
    # under emulation G's own saved return address sits at the word F returned, so G returned to v.
    0x08000000: """extern unsigned *func_08000100(void);
extern void func_08000200(unsigned *p, unsigned v);
void func_08000000(unsigned v)
{
    func_08000200(func_08000100(), v);
}
""",
    0x08000100: """unsigned *func_08000100(void)
{
    unsigned buf[1];
    buf[0] = 0;
    return buf;
}
""",
    0x08000200: """extern unsigned func_08000300(unsigned x);
void func_08000200(unsigned *p, unsigned v)
{
    *p = v;
    func_08000300(v);
}
""",
    0x08000300: """unsigned func_08000300(unsigned x)
{
    return x + 1;
}
""",
}


@unittest.skipUnless(tools_present(), "fixed compiler and ARM tools required")
class CompositionNativeTests(unittest.TestCase):
    """The issue's composition: only F, which returns its own frame address, is refused now."""

    def setUp(self):
        scratch_dir = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch_dir.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="return_frame_alias_composition_", dir=scratch_dir)
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)

    def build(self, sources=COMPOSITION, self_calls=()):
        import argparse
        root = self.root
        for name in ("src", "include", "config", "symbols", "build", "docs/match"):
            (root / name).mkdir(parents=True, exist_ok=True)
        (root / "config/data_symbols.json").write_text("{}\n")
        for address, text in sources.items():
            (root / f"src/{address:08X}.c").write_text(text)
        args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                                  objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        runner = match.Runner(match.DEFAULT_CC, root=root, wsl_path=match.DEFAULT_WSL_PATH, timeout=120)
        compiled, sizes = {}, {}
        for address in sources:
            with runner.workspace() as workspace:
                object_data, text, original = match.compile_object(runner, workspace, args, root, address,
                                                                   f"src/{address:08X}.c")
                symbol, _ = match.function_record(original, f"func_{address:08X}", address, True)
            compiled[address], sizes[address] = (object_data, text, original), symbol["size"]
        mapping = json.dumps([{"rom": f"0x{a:08X}", "end": f"0x{a + sizes[a]:08X}", "mode": "thumb"}
                              for a in sources]).encode()
        rom = bytearray(0x400)
        for _ in range(2):
            for address, (object_data, text, original) in compiled.items():
                if original["relocations"]:
                    with runner.workspace() as workspace:
                        match.compile_object(runner, workspace, args, root, address, f"src/{address:08X}.c")
                        body, _, _ = match.link_calls(runner, workspace, args, original, address, mapping,
                                                      len(rom), bytes(rom), allow_self_call=address in self_calls)
                else:
                    body = match.function_bytes(object_data, text, f"func_{address:08X}", address, True)
                rom[address - BASE:address - BASE + len(body)] = body
        (root / "baserom.bin").write_bytes(bytes(rom))
        (root / "config/functions.json").write_bytes(mapping + b"\n")
        (root / "symbols/functions.txt").write_text("".join(
            f"{a:08X} {a + sizes[a]:08X} {sizes[a]} {sizes[a] // 2} return\n" for a in sources))

    def test_only_the_function_returning_its_frame_is_refused(self):
        self.build()
        environment = dict(os.environ, FFTA_ROM=str(self.root / "baserom.bin"), PYTHONDONTWRITEBYTECODE="1")
        results = {}
        for address in COMPOSITION:
            run = subprocess.run([sys.executable, str(ROOT / "tools/match.py"), "--root", str(self.root),
                                  f"0x{address:08X}"], capture_output=True, text=True, env=environment, timeout=600)
            results[address] = (run.returncode, run.stdout + run.stderr)
        self.assertEqual({address: code for address, (code, _) in results.items()},
                         {0x08000000: 0, 0x08000100: 1, 0x08000200: 0, 0x08000300: 0})
        self.assertIn(ESCAPE, results[0x08000100][1])

    def test_a_self_call_returning_its_frame_is_refused(self):
        source = """unsigned *func_08000000(unsigned n)
{
    unsigned buf[1];
    buf[0] = n;
    if (n)
        func_08000000(n - 1);
    return buf;
}
"""
        self.build({0x08000000: source}, self_calls={0x08000000})
        run = subprocess.run([sys.executable, str(ROOT / "tools/match.py"), "--root", str(self.root), "0x08000000"],
                             capture_output=True, text=True, timeout=600,
                             env=dict(os.environ, FFTA_ROM=str(self.root / "baserom.bin")))
        self.assertNotEqual(run.returncode, 0, run.stdout)
        self.assertIn(ESCAPE, run.stdout + run.stderr)


if __name__ == "__main__":
    unittest.main()
