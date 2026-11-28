"""bios-fill-temporary-v1, rule 6: a fill slot's address carried in a callee-saved register.

agbcc may form the address of a fill's temporary once, keep it in r4-r11 across branches,
loops and calls, and copy it to r0 at the BL (0x08023FD0 keeps sp+2 in r6 across a branch and
nine calls; 0x0810EC04 forms sp+0x34 in r0 and moves it to sl before a loop of calls).  The
straight line before the BL then shows no access to the slot.  rom_fill takes the address from
such a register when every route into the line, walked backwards on the ROM's control-flow
graph, reaches a site whose own straight line makes it sp+K, with one K, before any other write
of it, any change of sp, a SWI or the function's entry; and every call the routes cross is
walked by kit #350's callee-saved check, which must find the register (and SP) returned unchanged
and no bit of it used.  The record names the register, the forming site, the calls and the
premises the check states.
"""
from pathlib import Path
import json
import re
import os
import struct
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import bios_fill_temporary as fill
import volatile_rom_proof as proof
import test_bios_fill_temporary as base

ADDRESS, thumb, shared, one_fill = base.ADDRESS, base.thumb, base.shared, base.one_fill
LDR_R1, LDR_R2 = base.LDR_R1, base.LDR_R2
MOV_R6_SP, ADDS_R6_2, ADDS_R6_4 = 0x466E, 0x3602, 0x3604
MOVS_R5_0, STRH_R5_R6, ADDS_R0_R6 = 0x2500, 0x8035, 0x1C30
SUB_SP_8, SWI_0B = 0xB082, 0xDF0B
STRH_R5_R0, LDMIA_R0_R6, PUSH_R7, POP_R7 = 0x8005, 0xC840, 0xB480, 0xBC80
CALLEE, CALLEE2 = 0x08001000, 0x08001100
CPUSET = ("bl", 0x0814186C)


def path(*before):
    """the fill's straight line after a call: `movs r5, #0; strh r5, [r6]; ldr r1; adds r0, r6, #0; ldr r2; bl`"""
    return list(before) + [MOVS_R5_0, STRH_R5_R6, LDR_R1, ADDS_R0_R6, LDR_R2, CPUSET]


def case(items, labels=()):
    """(rom, compiled, fill) of items; the fill's call is the last item, its store the STRH_R5_R6"""
    store, call = items.index(STRH_R5_R6), len(items) - 1
    uids = {65: [(store, "strh\tr5, [r6]")], 76: [(call, "bl\tfunc_0814186C")]}
    rom, compiled = shared(items, labels, uids, control=0x01000100)
    return rom, compiled, one_fill(76, 65, [65, 76], control=0x01000100)


class Stub:
    """a carrier whose callee-saved check admits every call, and remembers what it was asked"""

    def __init__(self, premises=()):
        self.asked, self.premises = [], list(premises)

    def check(self, number, sites):
        self.asked.append((number, list(sites)))
        return self.premises


SHAPE = [MOV_R6_SP, ADDS_R6_2, ("bl", CALLEE)] + path()


@unittest.skipUnless(base.capstone, "capstone required")
class RouteTests(unittest.TestCase):
    def test_a_slot_address_carried_across_a_call_is_read(self):
        rom, compiled, one = case(SHAPE)
        stub = Stub(["premise: a stated one"])
        self.assertEqual(fill.rom_fill(rom, ADDRESS, compiled, one, carrier=stub), (ADDRESS + 18, 2, ADDRESS + 2, ()))
        self.assertEqual(stub.asked, [(6, [ADDRESS + 4])])
        self.assertEqual(one["carried"], [f"sp+0x2 held in r6 from {ADDRESS + 2:08X} across the calls at "
                                          f"{ADDRESS + 4:08X}, each walked by the callee-saved check (it returns r6 "
                                          "unchanged and uses no bit of it); callee-saved premise: a stated one"])
        # without a carrier the line shows no slot, as before
        with self.assertRaisesRegex(proof.ProofError, "r0 holds no stack address"):
            fill.rom_fill(rom, ADDRESS, compiled, one)

    def test_a_loop_whose_body_keeps_the_register_is_crossed(self):
        # r6 formed before the loop; the loop calls and branches back; the fill follows it
        items = [MOV_R6_SP, ADDS_R6_2, ("bl", CALLEE), ("beq", 2)] + path()
        rom, compiled, one = case(items, labels={2})
        stub = Stub()
        self.assertEqual(fill.rom_fill(rom, ADDRESS, compiled, one, carrier=stub)[1], 2)
        self.assertEqual(stub.asked, [(6, [ADDRESS + 4])])

    def test_hostile_routes_refuse(self):
        reason = "r0 holds no stack address at the BL"
        for label, items, labels, why in (
                ("a write in the loop body", [MOV_R6_SP, ADDS_R6_2, ("bl", CALLEE), ADDS_R6_2, ("beq", 2)] + path(),
                 {2}, "writes r6 with no stack address"),
                ("two forming sites with different K",
                 [("beq", 4), MOV_R6_SP, ADDS_R6_2, ("b", 6), MOV_R6_SP, ADDS_R6_4, ("bl", CALLEE)] + path(), {4, 6},
                 "as different stack addresses: sp\\+0x2 at .*, sp\\+0x4 at"),
                ("an sp write on a route", [MOV_R6_SP, ADDS_R6_2, SUB_SP_8, ("bl", CALLEE)] + path(), (),
                 "changes sp on a route"),
                ("a SWI on a route", [MOV_R6_SP, ADDS_R6_2, SWI_0B, ("bl", CALLEE)] + path(), (), "is a SWI"),
                ("a block load writing it on a route", [MOV_R6_SP, ADDS_R6_2, LDMIA_R0_R6, ("bl", CALLEE)] + path(),
                 (), "writes r6 with no stack address"),
                ("a push and pop on a route", [MOV_R6_SP, ADDS_R6_2, PUSH_R7, POP_R7, ("bl", CALLEE)] + path(), (),
                 "changes sp on a route"),
                ("the entry without a forming site", path(), (), "reaches the function's entry"),
                ("a loop back to the entry", [("bl", CALLEE), ("beq", 0)] + path(), {0},
                 "reaches the function's entry"),
                ("a data word between the call and the line", SHAPE[:3] + [("word", 0)] + path(), (),
                 "does not fall through")):
            with self.subTest(label):
                rom, compiled, one = case(items, labels)
                with self.assertRaisesRegex(proof.ProofError, reason + ".*" + why):
                    fill.rom_fill(rom, ADDRESS, compiled, one, carrier=Stub())

    def test_a_register_offset_from_the_carried_register_refuses(self):
        # `strh r5, [r6, r7]` with r6 carried as sp+2 writes sp+2+r7, an address the path does not know
        items = [MOV_R6_SP, ADDS_R6_2, ("bl", CALLEE), MOVS_R5_0, 0x5200 | 7 << 6 | 6 << 3 | 5, LDR_R1, ADDS_R0_R6,
                 LDR_R2, CPUSET]
        uids = {65: [(4, "strh\tr5, [r6, r7]")], 76: [(8, "bl\tfunc_0814186C")]}
        rom, compiled = shared(items, (), uids, control=0x01000100)
        with self.assertRaisesRegex(proof.ProofError, "indexes the stack by a register inside the fill"):
            fill.rom_fill(rom, ADDRESS, compiled, one_fill(76, 65, [65, 76], control=0x01000100), carrier=Stub())

    def test_two_forming_sites_with_one_k_are_read(self):
        items = [("beq", 4), MOV_R6_SP, ADDS_R6_2, ("b", 6), MOV_R6_SP, ADDS_R6_2, ("bl", CALLEE)] + path()
        rom, compiled, one = case(items, labels={4, 6})
        self.assertEqual(fill.rom_fill(rom, ADDRESS, compiled, one, carrier=Stub())[1], 2)
        self.assertIn(f"held in r6 from {ADDRESS + 4:08X}, {ADDRESS + 10:08X} across", one["carried"][0])

    def test_a_refused_call_refuses(self):
        class Refusing(Stub):
            def check(self, number, sites):
                raise proof.ProofError("the walk refuses")
        rom, compiled, one = case(SHAPE)
        with self.assertRaisesRegex(proof.ProofError, "r0 holds no stack address .*r6: the walk refuses"):
            fill.rom_fill(rom, ADDRESS, compiled, one, carrier=Refusing())

    def test_the_walk_is_bounded(self):
        rom, compiled, one = case(SHAPE)
        with mock.patch.object(fill, "MAX_CARRY", 1), \
                self.assertRaisesRegex(proof.ProofError, "longer than 1 instructions"):
            fill.rom_fill(rom, ADDRESS, compiled, one, carrier=Stub())
        with mock.patch.object(fill, "MAX_CARRY_CALLS", 0), \
                self.assertRaisesRegex(proof.ProofError, "cross more than 0 calls"):
            fill.rom_fill(rom, ADDRESS, compiled, one, carrier=Stub())


@unittest.skipUnless(base.capstone, "capstone required")
class CarrierTests(unittest.TestCase):
    """the real callee-saved check (callee_saved_watch.Checker) on a callee the ROM holds"""

    def carrier(self, callee, items=SHAPE):
        """(rom, compiled, fill, Carrier) of items with each callee in the ROM and the index: callee is the
        halfwords at CALLEE, or {address: halfwords}"""
        callees = callee if isinstance(callee, dict) else {CALLEE: callee}
        rom, compiled, one = case(items)
        rom = bytearray(rom)
        code = compiled["text"][0]
        entries = [{"rom": f"0x{ADDRESS:08X}", "end": f"0x{ADDRESS + len(code):08X}", "mode": "thumb"}]
        for at, halves in sorted(callees.items()):
            rom[at - fill.BASE:at - fill.BASE + 2 * len(halves)] = thumb(*halves)
            entries.append({"rom": f"0x{at:08X}", "end": f"0x{at + 2 * len(halves):08X}", "mode": "thumb"})
        return bytes(rom), compiled, one, fill.Carrier(bytes(rom), entries, ADDRESS)

    def test_a_callee_that_keeps_the_register_is_admitted(self):
        rom, compiled, one, carrier = self.carrier([0x4770])                        # bx lr
        self.assertEqual(fill.rom_fill(rom, ADDRESS, compiled, one, carrier=carrier)[1], 2)
        self.assertNotIn("premise", one["carried"][0])

    def test_a_callee_that_clobbers_the_register_is_refused(self):
        for label, callee in (("overwrites it", [0x2600, 0x4770]),                   # movs r6, #0; bx lr
                              ("stores through it", [0x8030, 0x4770])):               # strh r0, [r6]; bx lr
            with self.subTest(label):
                rom, compiled, one, carrier = self.carrier(callee)
                with self.assertRaisesRegex(proof.ProofError, "r0 holds no stack address .*the callee-saved check "
                                                              f"refuses the call at {ADDRESS + 4:08X}"):
                    fill.rom_fill(rom, ADDRESS, compiled, one, carrier=carrier)

    def test_every_crossed_call_is_walked(self):
        # two calls between the forming and the line: the first overwrites r6, the second keeps it
        items = [MOV_R6_SP, ADDS_R6_2, ("bl", CALLEE), ("bl", CALLEE2)] + path()
        rom, compiled, one, carrier = self.carrier({CALLEE: [0x2600, 0x4770], CALLEE2: [0x4770]}, items)
        with self.assertRaisesRegex(proof.ProofError, "r0 holds no stack address .*the callee-saved check refuses "
                                                      f"the call at {ADDRESS + 4:08X}"):
            fill.rom_fill(rom, ADDRESS, compiled, one, carrier=carrier)

    def test_a_callee_handing_the_address_back_is_followed_into_the_caller(self):
        # adds r0, r6, #0; bx lr: the caller then stores through r0, a store to the slot the fill's line does not
        # show; the check's walk of the caller after the call (its continuation) is what sees it
        items = [MOV_R6_SP, ADDS_R6_2, ("bl", CALLEE), MOVS_R5_0, STRH_R5_R0] + path()[1:]
        rom, compiled, one, carrier = self.carrier([ADDS_R0_R6, 0x4770], items)
        with self.assertRaisesRegex(proof.ProofError, "r0 holds no stack address .*the callee-saved check refuses"):
            fill.rom_fill(rom, ADDRESS, compiled, one, carrier=carrier)


# Compiled shapes (agbcc), each one fill: the slot's address hoisted out of a loop of calls into
LOOP = """void func_08000200(u16 *dest, u32 n)
{
    u32 i;
    for (i = 0; i < n; i++) {
        func_08000400(i);
        { volatile u16 fill = 0; func_0814186C((const void *)&fill, dest + i * 0x100, 0x01000100); }
    }
}
"""
# a low register (r7, `mov r7, sp`); with more values live, a high one (sl, `mov sl, sp`)
HIGH = """void func_08000200(u16 *dest, u32 n, u32 *p, u32 *q)
{
    u32 i, a = p[0], b = p[1], c = q[0], d = q[1];
    for (i = 0; i < n; i++) {
        func_08000400(a + b);
        { volatile u16 fill = 0; func_0814186C((const void *)&fill, dest + i * 0x100, 0x01000100); }
        a += c; b += d; dest[i] = a ^ b;
    }
}
"""
# a five-argument call puts the slot at sp+4, which a high register takes in two steps (`add r1, sp, #4; mov sl, r1`)
TWO_STEP = """void func_08000200(u16 *dest, u32 n, u32 *p, u32 *q)
{
    u32 i, a = p[0], b = p[1], c = q[0], d = q[1];
    for (i = 0; i < n; i++) {
        func_08000700(1, 2, 3, 4, 5);
        { volatile u16 fill = 0; func_0814186C((const void *)&fill, dest + i * 0x100, 0x01000100); }
        a += c; b += d; dest[i] = a ^ b;
    }
}
"""
# with a value live across the five-argument call too, agbcc spills the address to the frame and reloads it after
# the call: a frame word across a call is no carried register, so the store is no access the line can place
SPILLED = """void func_08000200(u16 *dest, u32 n, u32 *p, u32 *q)
{
    u32 i, a = p[0], b = p[1], c = q[0], d = q[1];
    for (i = 0; i < n; i++) {
        func_08000700(a, b, c, d, i);
        { volatile u16 fill = 0; func_0814186C((const void *)&fill, dest + i * 0x100, 0x01000100); }
        a += c; b += d; dest[i] = a ^ b;
    }
}
"""
# 0810EC04: the slot's address formed before a loop of calls and kept in sb; after the loop, with r0 holding the value
# and r1 the literal it came from, agbcc copies sb to r3 to store through it (`mov r3, r9; strh r0, [r3]`) and
# leaves r3 holding the slot's address at the BL into CpuSet
STORE_BASE = """extern void func_08000600(void *);
typedef struct { u32 a, b; u16 current; } State;
typedef struct { u8 *status; u16 gradient[0xC0]; u16 backdrop[0xA0]; } Payload;
void func_08000200(Payload *payload)
{
    State red, green, blue;
    u16 i;
    func_08000600(&red);
    func_08000600(&green);
    func_08000600(&blue);
    for (i = 0; i < 0xC0; i++) {
        func_08000600(&red);
        func_08000600(&green);
        func_08000600(&blue);
        payload->gradient[i] = red.current | (green.current << 5) | (blue.current << 10);
    }
    { volatile u16 fill = 0x65C9; func_0814186C((const void *)&fill, payload->backdrop, 0x010000A0); }
    *payload->status = 0;
}
"""
HEAD = ("typedef unsigned char u8;\ntypedef unsigned short u16;\ntypedef unsigned int u32;\n"
        "extern void func_0814186C(const void *source, void *destination, u32 control);\n"
        "extern void func_08000400(u32);\nextern void func_08000700(u32, u32, u32, u32, u32);\n")
STUBS = [("func_08000400", "bx lr"), ("func_08000500", "bx lr"), ("func_08000600", "bx lr"),
         ("func_08000700", "bx lr")]


def tree(directory, body):
    import test_data_buffer_calls as calls
    return calls.build(Path(directory) / "tree", HEAD + body, STUBS, objects={}, large=True)


def assembly(root, body):
    with tempfile.TemporaryDirectory(dir=root) as work:
        unit = proof.Unit(root, "src/08000200.c", HEAD + body, [], work)
        unit.compile("probe", unit.real, "func_08000200")
        return (Path(work) / "probe" / "f.s").read_text()


def tools_present():
    import test_data_buffer_calls as calls
    return base.COMPILER and base.capstone and calls.tools_present()


@unittest.skipUnless(tools_present(), "fixed compiler, ARM tools and capstone required")
class CompiledTests(unittest.TestCase):
    def setUp(self):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", Path(__file__).resolve().parents[1] / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        self.directory = tempfile.TemporaryDirectory(prefix="bios_fill_carried_", dir=scratch)
        self.addCleanup(self.directory.cleanup)

    def proved(self, body):
        root = tree(self.directory.name, body)
        return root, fill.prove(root, root, "src/08000200.c", HEAD + body, set(),
                                rom=(root / "baserom.bin").read_bytes())

    def test_the_shapes_compile_as_described(self):
        for body, formed in ((LOOP, "\tmov\tr7, sp"), (HIGH, "\tmov\tsl, sp"), (TWO_STEP, "\tmov\tsl, r1")):
            with self.subTest(formed=formed), tempfile.TemporaryDirectory(dir=self.directory.name) as directory:
                root = tree(directory, body)
                text = assembly(root, body)
                self.assertIn(formed, text)
                if body is TWO_STEP:
                    self.assertIn("\tadd\tr1, sp, #4", text)

    def test_the_loop_shape_is_admitted_with_its_premise(self):
        _, result = self.proved(LOOP)
        (state, text), = {verdict for _, verdict in result}
        self.assertEqual(state, "admitted", text)
        self.assertRegex(text, r"fills from sp\+0x0 \(address formed at [0-9A-F]{8}, sp\+0x0 held in r7 from "
                               r"[0-9A-F]{8} across the calls at [0-9A-F]{8}, [0-9A-F]{8}, each walked by the "
                               r"callee-saved check")
        self.assertIn("callee-saved premise: SWI 0x0B (CpuSet) at 0x0814186C in 0x0814186C, with R7 depending on "
                      "owner stack addresses; unproved premise: the BIOS uses", text)

    def test_the_index_is_a_dependency_of_the_cached_proof(self):
        root, _ = self.proved(LOOP)
        with mock.patch.dict(os.environ, {"FFTA_ROM": str(root / "baserom.bin")}):
            result = fill.cached(root, root, "src/08000200.c", HEAD + LOOP, set())
            self.assertEqual({state for _, (state, _) in result}, {"admitted"})
            (root / "config/functions.json").unlink()
            self.assertIn("is not stored exactly once", fill.cached(root, root, "src/08000200.c", HEAD + LOOP, set()))

    def test_r3_left_holding_the_slot_as_its_store_s_base_is_admitted(self):
        root = tree(self.directory.name, STORE_BASE)
        code = [line.split("\t@")[0] for line in assembly(root, STORE_BASE).splitlines()
                if line.startswith("\t") and not line.startswith("\t.")]
        k = code.index("\tmov\tr3, r9")
        self.assertEqual((code[k + 1], code[k + 6], code[k + 7]),
                         ("\tstrh\tr0, [r3]", "\tmov\tr0, r9", "\tbl\tfunc_0814186C"))
        result = fill.prove(root, root, "src/08000200.c", HEAD + STORE_BASE, set(),
                            rom=(root / "baserom.bin").read_bytes())
        (state, text), = {verdict for _, verdict in result}
        self.assertEqual(state, "admitted", text)
        self.assertRegex(text, r"held in sb from [0-9A-F]{8} across the calls at")
        self.assertRegex(text, r"uses no bit of it\), r3 holds sp\+0x24 at the BL as the base of the store at "
                               r"[0-9A-F]{8}; BIOS premise: CpuSet \(swi 0x0B\) reads only r0-r2 \(GBATEK\), so "
                               r"nothing reads r3, control 0x010000a0")

    def test_a_spilled_address_is_not_carried(self):
        with self.assertRaisesRegex(proof.ProofError, "is not stored exactly once"):
            self.proved(SPILLED)

    def test_without_an_index_nothing_is_carried(self):
        root, _ = self.proved(LOOP)
        (root / "config/functions.json").unlink()
        with self.assertRaisesRegex(proof.ProofError, "is not stored exactly once"):
            fill.prove(root, root, "src/08000200.c", HEAD + LOOP, set(), rom=(root / "baserom.bin").read_bytes())


REPLAY = """import sys
from pathlib import Path
sys.path.insert(0, sys.argv[1])
import match_evidence
root = Path(sys.argv[2])
print("replay", match_evidence.report_matches((root / "docs/match/08000200.md").read_text(), root, 0x08000200))
"""


@unittest.skipUnless(tools_present(), "fixed compiler, ARM tools and capstone required")
class IssuanceTests(unittest.TestCase):
    """each shape through match.py as a subprocess (`__main__`), then replayed as status.py --verify does"""

    def issue_and_replay(self, body, register, tampers=()):
        """the issued report; each (old, new) of tampers, and another register for the carry, fails replay"""
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", Path(__file__).resolve().parents[1] / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        tools = Path(fill.__file__).parent
        with tempfile.TemporaryDirectory(prefix="bios_fill_carried_", dir=scratch) as directory:
            root = tree(directory, body)
            environment = dict(os.environ, FFTA_ROM=str(root / "baserom.bin"), PYTHONDONTWRITEBYTECODE="1")
            result = subprocess.run([sys.executable, str(tools / "match.py"), "--root", str(root), "0x08000200"],
                                    capture_output=True, text=True, env=environment, timeout=900)
            output = result.stdout + result.stderr
            self.assertEqual(result.returncode, 0, output[-3000:])
            self.assertIn("MATCH - byte identical", output)
            report = (root / "docs/match/08000200.md").read_text()
            self.assertRegex(report, rf"held in {register} from [0-9A-F]{{8}} across the calls at")
            replay = subprocess.run([sys.executable, "-c", REPLAY, str(tools), str(root)], capture_output=True,
                                    text=True, env=environment, timeout=900)
            self.assertEqual(replay.returncode, 0, (replay.stdout + replay.stderr)[-3000:])
            self.assertIn("replay True", replay.stdout, (replay.stdout + replay.stderr)[-3000:])
            # the record is recomputed: a report naming another register, or with another premise, does not replay
            other = "r4" if register != "r4" else "r5"
            for old, new in [(f"held in {register} from", f"held in {other} from")] + list(tampers):
                self.assertIn(old, report)
                (root / "docs/match/08000200.md").write_text(report.replace(old, new))
                tampered = subprocess.run([sys.executable, "-c", REPLAY, str(tools), str(root)], capture_output=True,
                                          text=True, env=environment, timeout=900)
                self.assertIn("replay False", tampered.stdout, (tampered.stdout + tampered.stderr)[-3000:])
            return report

    def test_the_loop_shape(self):
        self.issue_and_replay(LOOP, "r7")

    def test_the_high_register_shape(self):
        self.issue_and_replay(HIGH, "sl")

    def test_the_two_step_shape(self):
        self.issue_and_replay(TWO_STEP, "sl")

    def test_the_r3_store_base_shape(self):
        # 0x0810EC04's shape; match.py's frame proof admits r3 = sp+K at the CpuSet call only as a dead local
        # address (the BIOS wrapper summaries' non-argument register), and the fill's record states its premise
        premise = "BIOS premise: CpuSet (swi 0x0B) reads only r0-r2 (GBATEK), so nothing reads r3"
        report = self.issue_and_replay(STORE_BASE, "sb", [(premise, premise.replace("r0-r2", "r0-r3"))])
        self.assertRegex(report, r"r3 holds sp\+0x24 at the BL as the base of the store at [0-9A-F]{8}; "
                         + re.escape(premise))
        self.assertIn("* buffer BIOS non-argument register: r3 carried local", report)


if __name__ == "__main__":
    unittest.main()
