"""Forwarded buffer pointer slots on the default stack-argument proofs (no ROM, compiler or game C)."""
from pathlib import Path
import argparse
import json
import os
import sys
import tempfile
import unittest
import unittest.mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import test_dead_stack_registers as base
import match
import forwarded_slot_profile as forwarded
import copy_helper_summary_profile as copy_summary
import match_evidence as evidence
import test_dma_fill as dma_tests

OWNER, FWD, LEAF, OTHER = base.OWNER, base.P, base.C, base.G
R0, R1, R2 = base.R0, base.R1, base.R2

# FWD(r0, r1): push {lr}; sub sp,#4; str r1,[sp]; bl LEAF; add sp,#4; pop {r0}; bx r0 - passes its
# second argument, the owner's local, on as LEAF's fifth (stack) argument, as 0x080DBDC8 does.
FWD_CODE = [0xb500, 0xb081, 0x9100, LEAF, 0xb001, 0xbc01, 0x4700]
STORE = FWD + 4
# LEAF: ldr r1,[sp,#0]; movs r0,#0; strh r0,[r1]; movs r1,#0; bx lr - writes through its fifth argument.
LEAF_CODE = [0x9900, 0x2000, 0x8008, 0x2100, 0x4770]
OTHER_CODE = [0x4770]


def owner(after=()):
    """push {lr}; sub sp,#8; add r1,sp,#4; bl FWD; <after>; add sp,#8; pop {r0}; bx r0"""
    return [0xb500, 0xb082, 0xa901, FWD, *after, 0xb002, 0xbc01, 0x4700]


def bodies(after=(), leaf=LEAF_CODE, fwd=FWD_CODE):
    return {OWNER: owner(after), FWD: fwd, LEAF: leaf, OTHER: OTHER_CODE}


def walk(code, *, forward=True):
    rom, mapping = base.build(code)
    options = dict(stack_arguments=True, loop_replay=True, bios_wrappers=True, dead_registers=True)
    if forward:
        options['forward_slots'] = True
    proof = match.BufferCallProof(rom, mapping, **options)
    data = base.assemble(OWNER, code[OWNER])
    match.verify_leaf_instructions(data, OWNER, True, base.calls_of(OWNER, code[OWNER]), buffer_proof=proof)
    return proof


FIRST_CALL = OWNER + 6          # push, sub, add r1: the first bl
SECOND_CALL = OWNER + 10        # bl after the first bl


class DefaultForwardingTests(unittest.TestCase):
    def test_a_forwarded_output_pointer_is_tracked_and_released_to_the_owner(self):
        proof = walk(bodies())
        # The owner's sp+4 is entry_SP-8; FWD's slot is its entry_SP-8; released below the owner's SP
        # (entry_SP-12) at entry_SP-20.
        self.assertEqual(proof.forward_slot_records, {(FWD, STORE, -8, -8)})
        self.assertEqual(proof.forward_releases, {FIRST_CALL: {-20}})
        self.assertEqual(proof.forward_trusted_calls, set())
        lines = forwarded.lines(proof)
        self.assertEqual(lines, [
            f"{forwarded.SLOTS_FIELD}`{forwarded.SCHEMA}` inspected callees store owner frame pointers in their own "
            f"frames, tracked word by word: 0x{FWD:08X} store 0x{STORE:08X} word entry_SP-0x8 = owner "
            f"entry_SP-0x8; released inside callees at 0x{FWD + 10:08X} in 0x{FWD:08X}; released below the "
            f"owner's SP after call 0x{FIRST_CALL:08X}: entry_SP-0x14; trusted calls while released words exist: "
            f"none", forwarded.PREMISE_FIELD + forwarded.PREMISE])
        self.assertEqual(proof.loop_replay_lines()[-2:], lines)
        self.assertIsNotNone(forwarded.fingerprint_payload(proof))

    def test_the_records_are_bound_into_the_fingerprint(self):
        proof = walk(bodies())
        bound = proof.fingerprint()
        proof.forward_releases.clear()
        self.assertNotEqual(proof.fingerprint(), bound)
        proof.forward_slot_records.clear()
        unbound = proof.fingerprint()
        proof.forward_trusted_calls.add((OWNER, SECOND_CALL, OTHER))
        self.assertNotEqual(proof.fingerprint(), unbound)

    def test_replays_refuse_only_while_something_is_forwarded(self):
        rom, mapping = base.build(bodies())
        proof = match.BufferCallProof(rom, mapping, stack_arguments=True, forward_slots=True)
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        (store,) = list(decoder.disasm(bytes.fromhex('0091'), FWD + 4))   # str r1, [sp]
        by_address = {store.address: store}
        self.assertFalse(proof.forwarded_slot_step(FWD, store, {R1: -8}, {}, 1, by_address, True))
        with self.assertRaisesRegex(ValueError, 'exclude replay and frame-content profiles'):
            proof.forwarded_slot_step(FWD, store, {R1: -8, -4: -8}, {}, 1, by_address, True)
        with self.assertRaisesRegex(ValueError, 'exclude replay and frame-content profiles'):
            proof.forwarded_slot_step(FWD, store, {R1: -8, match.FORWARD_STALE_BASE - 8: -8}, {}, 1, by_address,
                                      True)

    def test_without_the_policy_the_store_refuses_and_nothing_is_bound(self):
        with self.assertRaisesRegex(ValueError, 'unsupported buffer pointer use or escape'):
            walk(bodies(), forward=False)
        proof = walk({OWNER: [0xb500, 0xbc01, 0x4700], FWD: FWD_CODE, LEAF: LEAF_CODE, OTHER: OTHER_CODE})
        self.assertEqual((forwarded.lines(proof), forwarded.fingerprint_payload(proof)), ([], None))

    def test_an_instance_flag_set_by_another_policy_is_not_the_default_rule(self):
        # the scheduler's v2 policy sets the instance flag with its own records and owner rules
        rom, mapping = base.build(bodies())
        proof = match.BufferCallProof(rom, mapping, stack_arguments=True)
        proof.forwarded_stack_arguments = True
        proof.forward_slot_records, proof.forward_trusted_calls = {(FWD, STORE, -8, -8)}, set()
        proof.forward_releases = {FIRST_CALL: {-20}}
        self.assertFalse(proof.default_forwarding)
        self.assertEqual((forwarded.lines(proof), forwarded.fingerprint_payload(proof)), ([], None))

    def test_the_opt_in_v2_class_keeps_its_own_records(self):
        class ForwardingClass(match.BufferCallProof):
            forwarded_stack_arguments = True
        rom, mapping = base.build(bodies())
        proof = ForwardingClass(rom, mapping, stack_arguments=True)
        proof.forward_slot_records = {(FWD, STORE, -8, -8)}
        proof.forward_releases, proof.forward_trusted_calls = {}, set()
        self.assertFalse(forwarded.observed(proof))

    def test_a_trusted_owner_call_while_a_word_is_released_states_the_premise(self):
        proof = walk(bodies(after=(OTHER,)))
        self.assertEqual(proof.forward_trusted_calls, {(OWNER, SECOND_CALL, OTHER)})
        lines = forwarded.lines(proof)
        self.assertEqual(lines[1], forwarded.PREMISE_FIELD + forwarded.PREMISE)
        self.assertIn(f"trusted calls while released words exist: 0x{SECOND_CALL:08X} to 0x{OTHER:08X}", lines[0])

    def test_a_release_a_callee_push_ends_still_states_the_premise(self):
        # FWD releases its slot (add sp,#4), calls OTHER with no stack pointer (trusted while the
        # owner pointer sits in the released word below its SP), then push {r4} writes the word, so no word
        # comes back to the owner.  The trusted call relied on the premise, so the report states it.
        fwd = [0xb500, 0xb081, 0x9100, LEAF, 0xb001, OTHER, 0xb410, 0xbc10, 0xbc01, 0x4700]
        proof = walk(bodies(fwd=fwd))
        self.assertEqual(proof.forward_releases, {})
        self.assertEqual(proof.forward_trusted_calls, {(FWD, FWD + 12, OTHER)})
        self.assertEqual(proof.forward_callee_releases, {(FWD, FWD + 10)})
        lines = forwarded.lines(proof)
        self.assertEqual(lines[1], forwarded.PREMISE_FIELD + forwarded.PREMISE)
        self.assertIn(f"released inside callees at 0x{FWD + 10:08X} in 0x{FWD:08X}; released below the owner's "
                      f"SP after none; trusted calls while released words exist: 0x{FWD + 12:08X} to "
                      f"0x{OTHER:08X}", lines[0])
        # Without the trusted call the release still relied on the premise (interrupt handlers) until the PUSH.
        proof = walk(bodies(fwd=[0xb500, 0xb081, 0x9100, LEAF, 0xb001, 0xb410, 0xbc10, 0xbc01, 0x4700]))
        self.assertEqual((proof.forward_releases, proof.forward_trusted_calls), ({}, set()))
        self.assertEqual(forwarded.lines(proof)[1], forwarded.PREMISE_FIELD + forwarded.PREMISE)
        payload = forwarded.fingerprint_payload(proof)
        proof.forward_callee_releases.clear()
        self.assertNotEqual(forwarded.fingerprint_payload(proof), payload)

    def test_split_records_name_forwarded_words_by_their_offsets(self):
        # A join may keep a released word or a live slot apart, as it does a register: the line names each.
        import split_join_profile as split_join
        self.assertEqual(split_join.FORWARD_STALE_BASE, match.FORWARD_STALE_BASE)
        (line,) = split_join.lines({(OWNER, OWNER + 8, match.FORWARD_STALE_BASE - 20, -8, -12),
                                    (OWNER, OWNER + 8, -8, -16, -20), (OWNER, OWNER + 8, R2, -4, -8)})
        self.assertIn(" keeps released word entry_SP-0x14 -8/-12, slot entry_SP-0x8 -16/-20, r2 -4/-8 apart ", line)

    def test_a_later_walked_call_inherits_the_released_word(self):
        proof = walk(bodies(after=(0xa901, FWD)))
        self.assertEqual(proof.forward_releases, {FIRST_CALL: {-20}, OWNER + 12: {-20}})
        self.assertEqual(proof.forward_trusted_calls, set())

    def test_an_inheriting_callee_that_reads_the_word_first_refuses(self):
        # FWD2: push {lr}; sub sp,#4; ldr r0,[sp]; ...: reads its re-covered, released entry_SP-8
        reader = [0xb500, 0xb081, 0x9800, 0x9100, LEAF, 0xb001, 0xbc01, 0x4700]
        code = bodies(after=(0xa901, OTHER + 0x100))
        code[OTHER + 0x100] = reader
        with self.assertRaisesRegex(ValueError, 'released forwarded pointer word before it is written'):
            walk(code)

    def test_the_owner_may_not_move_sp_down_over_a_released_word(self):
        with self.assertRaisesRegex(ValueError, 'the owner moves SP down after a callee released'):
            walk(bodies(after=(0xb082, 0xb002)))

    def test_an_owner_push_writes_the_released_words_it_covers(self):
        # push {r4, r5}: entry_SP-16 and -20; the released word ends, so the next call is not trusted
        proof = walk(bodies(after=(0xb430, 0xbc30, OTHER)))
        self.assertEqual(proof.forward_trusted_calls, set())
        # push {r4} covers entry_SP-16 only: the word at -20 stays and the call is trusted
        proof = walk(bodies(after=(0xb410, 0xbc10, OTHER)))
        self.assertEqual(proof.forward_trusted_calls, {(OWNER, OWNER + 14, OTHER)})

    def test_the_owner_returns_with_released_words_below_its_sp(self):
        self.assertEqual(walk(bodies()).forward_releases, {FIRST_CALL: {-20}})

    def test_a_callee_may_not_write_its_incoming_forwarded_word(self):
        # LEAF: movs r0,#0; str r0,[sp]; bx lr - would overwrite the slot FWD passed
        with self.assertRaisesRegex(ValueError, 'outside the tracked frame'):
            walk(bodies(leaf=[0x2000, 0x9000, 0x4770]))

    def test_a_forwarder_that_materialises_sp_refuses(self):
        # FWD: push {lr}; sub sp,#4; str r1,[sp]; mov r2,sp; bl LEAF; movs r2,#0; add sp,#4; pop {r0}; bx r0
        fwd = [0xb500, 0xb081, 0x9100, base.MOV_R2_SP, LEAF, base.MOVS_R2_0, 0xb001, 0xbc01, 0x4700]
        with self.assertRaisesRegex(ValueError, 'needs a callee with only immediate SP uses'):
            walk(bodies(fwd=fwd))

    def test_the_ledgers_of_a_replaced_inspection_are_restored(self):
        rom, mapping = base.build(bodies())
        proof = match.BufferCallProof(rom, mapping, stack_arguments=True, dead_registers=True, forward_slots=True)
        saved = proof._snapshot_ledgers()
        proof.forward_slot_records.add((FWD, STORE, -8, -8))
        proof.forward_trusted_calls.add((OWNER, FIRST_CALL, OTHER))
        proof.forward_releases[FIRST_CALL] = {-20}
        proof.forward_callee_releases.add((FWD, FWD + 10))
        proof._restore_ledgers(saved)
        self.assertEqual((proof.forward_slot_records, proof.forward_trusted_calls, proof.forward_releases,
                          proof.forward_callee_releases), (set(), set(), {}, set()))

    def test_construction_guards(self):
        rom, mapping = base.build(bodies())
        for options in (dict(forward_slots=True), dict(stack_arguments=True, forward_slots=1)):
            with self.subTest(options=options), self.assertRaisesRegex(ValueError, 'forwarded buffer slots require'):
                match.BufferCallProof(rom, mapping, **options)
        class Other(match.BufferCallProof):
            pass
        with self.assertRaisesRegex(ValueError, 'forwarded buffer slots require'):
            Other(rom, mapping, stack_arguments=True, forward_slots=True)


class ConstructionSiteTests(unittest.TestCase):
    def test_every_default_stack_argument_proof_and_its_replays_forward(self):
        import ast
        found = set()
        for path in sorted((Path(__file__).resolve().parents[1] / 'tools').glob('*.py')):
            for function in ast.walk(ast.parse(path.read_text())):
                if isinstance(function, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    for node in ast.walk(function):
                        if isinstance(node, ast.Call):
                            for keyword in node.keywords:
                                if keyword.arg == 'forward_slots':
                                    found.add((path.name, function.name, ast.unparse(keyword.value)))
        self.assertEqual(found, {
            ('match.py', 'verify_function_buffers', 'True'), ('match.py', 'main', 'True'),
            ('data_buffer_profile.py', 'prove', 'True'),
            ('match_evidence.py', 'buffer_report_matches', 'stack_arguments is True'),
            ('function_thunk_profile.py', 'verify_source', 'buffer_stack_arguments is True')})


class SummaryCompositionTests(unittest.TestCase):
    def test_the_pinned_copy_helper_uses_sp_only_by_push_and_pop(self):
        import test_copy_helper_summary as copy_tests
        self.assertTrue(copy_summary.helper_stack_plain(copy_tests.BODY))
        # ldr r0,[sp,#0] in a helper body is not
        self.assertFalse(copy_summary.helper_stack_plain(bytes.fromhex('00987047')))

    def test_the_copy_summary_hands_released_words_back(self):
        import test_copy_helper_summary as copy_tests
        proof, _ = copy_tests.prove(copy_tests.owner())
        stack = [(False, False, True)] * 2 + [(False, True, False)] * 2
        stale = match.FORWARD_STALE_BASE - 4
        with self.assertRaisesRegex(ValueError, 'reach only the default forwarding proofs'):
            proof.check_call(copy_tests.HELPER, {R0: -16}, stack, constants={R2: 4}, site=copy_tests.OWNER + 8,
                             released={stale: -12})
        proof.forwarded_stack_arguments = proof.default_forwarding = True
        proof.forward_slot_records, proof.forward_trusted_calls, proof.forward_releases = set(), set(), {}
        result = proof.check_call(copy_tests.HELPER, {R0: -16}, stack, constants={R2: 4}, site=copy_tests.OWNER + 8,
                                  released={stale: -12})
        self.assertEqual(result[stale], -12)
        self.assertEqual(result[R0], -16)
        # a helper that might read below SP refuses beside released words, and only then
        with unittest.mock.patch.object(copy_summary, 'helper_stack_plain', lambda body: False):
            with self.assertRaisesRegex(ValueError, 'must use SP only by PUSH and POP'):
                proof.check_call(copy_tests.HELPER, {R0: -16}, stack, constants={R2: 4},
                                 site=copy_tests.OWNER + 8, released={stale: -12})
            proof.check_call(copy_tests.HELPER, {R0: -16}, stack, constants={R2: 4}, site=copy_tests.OWNER + 8)

    def test_a_bios_summary_hands_released_words_back_and_is_trusted(self):
        import test_bios_wrapper_summaries as bios_tests
        case = bios_tests.BiosWrapperSummaryTests()
        case.setUp()
        self.addCleanup(case.doCleanups)
        case.build(bios_tests.fill())
        proof = match.BufferCallProof(case.rom, case.mapping, stack_arguments=True, bios_wrappers=True,
                                      forward_slots=True)
        stack = [(False, False, True)] * 2
        stale = match.FORWARD_STALE_BASE - 4
        result = proof.check_arguments(0x08141898, {stale: -8}, stack, {}, frozenset(), site=bios_tests.BASE)
        self.assertEqual(result, {stale: -8})
        self.assertEqual(proof.forward_trusted_calls, {(0, bios_tests.BASE, 0x08141898)})


A, WRAPPER, CALLEE = 0x08000200, 0x08000400, 0x08000500
# WRAPPER(r0): push {lr}; sub sp,#4; str r0,[sp]; movs r0,#0; movs r1,#0; movs r2,#0; movs r3,#0; bl CALLEE;
# add sp,#4; pop {r0}; bx r0 - passes its argument on as CALLEE's fifth (stack) argument.
WRAPPER_CODE = [0xb500, 0xb081, 0x9000, 0x2000, 0x2100, 0x2200, 0x2300, CALLEE, 0xb001, 0xbc01, 0x4700]
# CALLEE: ldr r1,[sp,#0]; movs r0,#7; strh r0,[r1]; movs r1,#0; bx lr
CALLEE_CODE = [0x9900, 0x2007, 0x8008, 0x2100, 0x4770]
NATIVE = """typedef short s16;
extern void func_08000400(s16 *out);
%(extern)s
s16 func_08000200(void)
{
    s16 value;

    func_08000400(&value);
    %(store)s
    return value;
}
"""


# The same wrapper, but after the call it releases its slot (add sp,#4), calls OTHER2 with no stack pointer
# (trusted while the pointer sits below its SP) and then pushes over the word: no word reaches the owner.
OTHER2 = 0x08000600
TRUSTING_CODE = [0xb500, 0xb081, 0x9000, 0x2000, 0x2100, 0x2200, 0x2300, CALLEE, 0xb001, OTHER2, 0xb410, 0xbc10,
                 0xbc01, 0x4700]


def build_native(root, text, objects, callees=((WRAPPER, WRAPPER_CODE), (CALLEE, CALLEE_CODE))):
    root = Path(root)
    for name in ("src", "include", "config", "symbols", "build"):
        (root / name).mkdir(parents=True, exist_ok=True)
    rom = bytearray(0x1000)
    spans = []
    for address, code in callees:
        raw = base.assemble(address, code)
        rom[address - match.ROM_BASE:address - match.ROM_BASE + len(raw)] = raw
        spans.append({"rom": f"0x{address:08X}", "end": f"0x{address + len(raw):08X}", "mode": "thumb"})
    (root / "src/08000200.c").write_text(text)
    data_symbols = json.dumps(objects).encode()
    (root / "config/data_symbols.json").write_bytes(data_symbols)
    args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                              objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
    runner = match.Runner(match.DEFAULT_CC, root=root, wsl_path=match.DEFAULT_WSL_PATH, timeout=120)
    with runner.workspace() as workspace:
        _, _, original = match.compile_object(runner, workspace, args, root, A, "src/08000200.c")
        symbol, _ = match.function_record(original, "func_08000200", A, True)
        entries = [{"rom": f"0x{A:08X}", "end": f"0x{A + symbol['size']:08X}", "mode": "thumb"}] + spans
        mapping = json.dumps(entries).encode()
        body, _, _ = match.link_calls(runner, workspace, args, original, A, mapping, len(rom), bytes(rom),
                                      data_symbols, {})
    rom[A - match.ROM_BASE:A - match.ROM_BASE + len(body)] = body
    (root / "config/functions.json").write_bytes(mapping)
    (root / "symbols/functions.txt").write_text("".join(
        f"{int(entry['rom'], 16):08X} {int(entry['end'], 16):08X} "
        f"{int(entry['end'], 16) - int(entry['rom'], 16)} 0 return\n" for entry in entries))
    (root / "baserom.bin").write_bytes(bytes(rom))
    return root


@unittest.skipUnless(dma_tests.tools_present(), "fixed compiler and ARM tools required")
class DefaultForwardingNativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", dma_tests.ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix="forwarded_slots_", dir=scratch)
        cls.base = Path(cls.temporary.name)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def replays(self, root, report):
        with unittest.mock.patch.dict(os.environ, FFTA_ROM=str(Path(root) / "baserom.bin")):
            return evidence.report_matches(report, root, A)

    def check(self, name, text, objects, schema, callees=((WRAPPER, WRAPPER_CODE), (CALLEE, CALLEE_CODE))):
        root = build_native(self.base / name, text, objects, callees)
        code, output, report = dma_tests.run(root)
        self.assertEqual(code, 0, output)
        self.assertIn("verdict MATCH - byte identical", output)
        lines = report.splitlines()
        self.assertIn(f"* verification: `{schema}`", lines)
        (stated,) = [line for line in lines if line.startswith(forwarded.SLOTS_FIELD)]
        self.assertIn(f"0x{WRAPPER:08X} store 0x{WRAPPER + 4:08X} word entry_SP-0x8 = owner", stated)
        self.assertTrue(self.replays(root, report))
        self.assertFalse(self.replays(root, report.replace(stated + "\n", "")))
        self.assertFalse(self.replays(root, report.replace(stated, stated.replace(
            f"store 0x{WRAPPER + 4:08X}", f"store 0x{WRAPPER + 6:08X}"))))
        code, output = dma_tests.check_report(root)
        self.assertEqual(code, 0, output)
        self.assertIn("report  identical to the saved", output)
        return report

    def test_a_wrapper_forwarding_the_owners_local_matches_and_replays(self):
        self.check("plain", NATIVE % dict(extern="", store=""), {}, evidence.STACK_BUFFER_SCHEMA)

    def test_a_wrapper_that_trusts_a_call_and_pushes_over_the_word_states_the_premise(self):
        # The same through match.py: the release ends inside the wrapper, and the premise is still stated.
        callees = ((WRAPPER, TRUSTING_CODE), (CALLEE, CALLEE_CODE), (OTHER2, [0x4770]))
        report = self.check("trusting", NATIVE % dict(extern="", store=""), {}, evidence.STACK_BUFFER_SCHEMA,
                            callees)
        premise = forwarded.PREMISE_FIELD + forwarded.PREMISE
        self.assertIn(premise, report.splitlines())
        (stated,) = [line for line in report.splitlines() if line.startswith(forwarded.SLOTS_FIELD)]
        self.assertIn(f"released inside callees at 0x{WRAPPER + 18:08X} in 0x{WRAPPER:08X}; released below the "
                      f"owner's SP after none; trusted calls while released words exist: 0x{WRAPPER + 20:08X} to "
                      f"0x{OTHER2:08X}", stated)
        root = self.base / "trusting"
        self.assertFalse(self.replays(root, report.replace(premise + "\n", "")))

    def test_the_same_beside_typed_data_uses_the_data_buffer_schema(self):
        import data_buffer_profile
        text = NATIVE % dict(extern="extern s16 data_03003860[];", store="data_03003860[0] = value;")
        self.check("data", text, {"data_03003860": "0x03003860"}, data_buffer_profile.SCHEMA)

if __name__ == '__main__':
    unittest.main()
