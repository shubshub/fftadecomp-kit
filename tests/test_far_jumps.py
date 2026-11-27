"""agbcc far jumps on the default path (far_jump_profile): the walk, its two proofs, the record."""
import ast
import glob
import os
import re
import runpy
import struct
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
sys.path.insert(0, str(ROOT / "tests"))
import match
import match_evidence as evidence
import closure_slot_profile as closure
import far_jump_profile as far_jump
import test_data_buffer_calls as data_buffer_tests
from test_data_buffer_calls import A, BUFFER_ONLY, LITERAL, build, run, tools_present

START = 0x08000200
# With no linked call, the old refusal of an in-function BL is the first of these.
REFUSED = "non-leaf calls and interrupts require linked CFG verification|call is not a validated external direct Thumb BL"


def half(*values):
    return b"".join(struct.pack("<H", value) for value in values)


def bl(site, target):
    """The canonical BL pair at ``site`` to ``target``."""
    value = ((target - (site + 4)) >> 1) & 0x3FFFFF
    return half(0xF000 | value >> 11, 0xF800 | value & 0x7FF)


def body(*parts):
    return b"".join(parts)


# 200 push {lr}; 202 cmp r0,#0; 204 beq 20a; 206 bl 20e (the far jump); 20a movs r0,#1; 20c b 20e;
# 20e pop {r1}; 210 bx r1
def jump(target=0x0800020E, tail=half(0xBC02, 0x4708)):
    return body(half(0xB500, 0x2800, 0xD001), bl(0x08000206, target), half(0x2001, 0xE7FF), tail)


def walk(code, calls=None, **context):
    return match.verify_leaf_instructions(code, START, True, dict(calls or {}), **context)


# Every kit function that computes Thumb successors (SuccessorSiteTests.scan), by how it treats a far
# jump.  AWARE: through far_jump_profile.successors / raw_successors.  SOURCE: the walks that decide
# the far jumps and keep their edges.  OWN_RULE: walks every same-function BL as a jump (or every BL
# target as reached) by its own check.  REFUSES: reaches a BL only to refuse, so a far jump can only
# make it refuse.  RUNTIME: walks only a pinned runtime or library body.  SELECTOR: belongs to an
# opt-in profile, a selector route or a proof class whose walks are never default walks, so it never
# meets a far jump the kit walked as such; the default routes are checked not to reach it.
AWARE, SOURCE, OWN_RULE, REFUSES, RUNTIME, SELECTOR = ("aware", "source", "own rule", "refuses", "runtime",
                                                      "selector")
SUCCESSOR_SITES = {
    # AWARE
    "closure_slot_profile.py:_cyclic_sites": AWARE,
    "far_jump_profile.py:raw_successors": AWARE,
    "far_jump_profile.py:successors": AWARE,
    "match.py:_check_arguments": AWARE,
    "protected_descriptor_word_profile.py:check_lifetime": AWARE,
    "stack_index_precondition_profile.py:successors": AWARE,
    # SOURCE
    "match.py:verify_leaf_instructions": SOURCE,
    "stack_index_frame_words_profile.py:step": SOURCE,
    "stack_index_precondition_profile.py:step": SOURCE,
    # OWN_RULE
    "callee_saved_watch.py:call": OWN_RULE,
    "callee_saved_watch.py:inline": OWN_RULE,
    "callee_saved_watch.py:one_walk": OWN_RULE,
    "owner_graph_profile.py:graph": OWN_RULE,
    "volatile_rom_proof.py:pool_halfword": OWN_RULE,
    # REFUSES
    "compiler_orphan_constants_prerequisite.py:reachable_literals": REFUSES,
    "dead_register.py:step": REFUSES,
    "dead_register.py:through_calls": REFUSES,
    "match.py:stack_alias_overwritten_before_use": REFUSES,
    # RUNTIME
    "libgcc_divdi3_bounds.py:branch": RUNTIME,
    "libgcc_divdi3_bounds.py:instruction": RUNTIME,
    "runtime_summary_profile.py:scratch_inputs": RUNTIME,
    "software_float_profile.py:prove_runtime": RUNTIME,
    # SELECTOR
    "action_coordinate_query.py:visit": SELECTOR,
    "affine_sequence_task.py:constructor": SELECTOR,
    "allocator_saved_flow.py:visit": SELECTOR,
    "conditional_registration_profile.py:_execute_caller_prefixes": SELECTOR,
    "conditional_registration_profile.py:_source_binding_agreement": SELECTOR,
    "cone_stack_footprint.py:native_graph": SELECTOR,
    "dead_argument_buffer_profile.py:step": SELECTOR,
    "descriptor_callee_constant_profile.py:complete_frame": SELECTOR,
    "descriptor_frame_shape_prerequisite.py:decode_partition": SELECTOR,
    "dynamic_division_buffer_profile.py:control_overwrites": SELECTOR,
    "entry_recursive_ordinary_call_profile.py:_edges": SELECTOR,
    "finite_small_local_copy_profile.py:__init__": SELECTOR,
    "formal_entry_word_halfword_effects.py:prove_origins": SELECTOR,
    "formal_r0_r1_named_leaf_inventory.py:prove_origins": SELECTOR,
    "halfword_channel_arithmetic.py:compose": SELECTOR,
    "incoming_scratch_overwrite_profile.py:step": SELECTOR,
    "inert_spin_profile.py:terminal_tails": SELECTOR,
    "inert_spin_readonly_entry_inventory.py:graph": SELECTOR,
    "item_ability_names.py:collector_cfg": SELECTOR,
    "iwram_installation_prerequisite.py:image_inventory": SELECTOR,
    "known_list_query_closure_profile.py:callback_effects": SELECTOR,
    "known_list_query_continuation_profile.py:query_prefix": SELECTOR,
    "known_query_callback_effects.py:decoded": SELECTOR,
    "known_query_stack_buffer_profile.py:execute": SELECTOR,
    "menu_ring_initializer.py:callback_site": SELECTOR,
    "mutable_stack_index_profile.py:successors": SELECTOR,
    "named_data_buffer_profile.py:check_arguments": SELECTOR,
    "named_data_buffer_profile.py:normal_return_aliases": SELECTOR,
    "narrowed_counter_loop_prerequisite.py:__init__": SELECTOR,
    "non_sp_block_copy_inventory.py:copy_pairs": SELECTOR,
    "ordinary_formal_stack_callee_inventory.py:prove_formal_origins": SELECTOR,
    "ordinary_second_formal_output_callees_inventory.py:prove_second_origins": SELECTOR,
    "ordinary_third_formal_output_callees_inventory.py:prove_local_origins": SELECTOR,
    "ordinary_two_output_callees_inventory.py:prove_named_origins": SELECTOR,
    "palette_value_composition.py:copy": SELECTOR,
    "party_effect_scheduler.py:entry_kill": SELECTOR,
    "scaled_polygon.py:edge_frame": SELECTOR,
    "scheduler_coordinate_common_state.py:derive": SELECTOR,
    "scheduler_descriptor_lifetime.py:bind_layout": SELECTOR,
    "scheduler_helper_common_state.py:_derive": SELECTOR,
    "scheduler_killed_alias_profile.py:overwrite": SELECTOR,
    "scheduler_projected_outputs_profile.py:pair_origins": SELECTOR,
    "scheduler_small_entry_state.py:derive": SELECTOR,
    "scheduler_zero40_state.py:derive": SELECTOR,
    "stat_drain_profile.py:prove": SELECTOR,
    "static_callback_r6_frame_profile.py:normal_return_aliases": SELECTOR,
    "three_halfword_output_buffer_profile.py:prove_leaf_origins": SELECTOR,
    "transfer_mask_argument.py:continuation": SELECTOR,
    "transfer_mask_argument.py:validate_mask": SELECTOR,
}
DEFAULT_ROUTE_KINDS = {AWARE, SOURCE, OWN_RULE, REFUSES, RUNTIME}
STEP_NAMES = {"site", "current", "position", "cursor", "node", "pc", "here", "at"}


def _is_step(node):
    """`x + item.size`, or `site + 2` / `site + 4`: a fall-through or next-instruction address."""
    if not (isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add)):
        return False
    if isinstance(node.right, ast.Attribute) and node.right.attr == "size" and \
            isinstance(node.left, (ast.Name, ast.Attribute)):
        return True
    return isinstance(node.right, ast.Constant) and node.right.value in (2, 4) and (
        isinstance(node.left, ast.Name) and node.left.id in STEP_NAMES or
        isinstance(node.left, ast.Attribute) and node.left.attr == "address")


def _own_nodes(function):
    pending = list(ast.iter_child_nodes(function))
    while pending:
        node = pending.pop()
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            continue
        yield node
        pending.extend(ast.iter_child_nodes(node))


def _computes_successors(function):
    """A function that builds a successor tuple or list, or queues one, from a next-instruction address."""
    for node in _own_nodes(function):
        if isinstance(node, (ast.Tuple, ast.List)) and any(_is_step(item) for item in node.elts):
            return True
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr in ("append", "extend") \
                and any(_is_step(argument) or isinstance(argument, (ast.Tuple, ast.List)) and
                        any(_is_step(item) for item in argument.elts) for argument in node.args):
            return True
    return False


def scan():
    """{"module:function"} of every kit function that computes successors."""
    found = set()
    for path in sorted(glob.glob(str(ROOT / "tools" / "*.py"))):
        tree = ast.parse(Path(path).read_text())
        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and _computes_successors(node):
                found.add(f"{Path(path).name}:{node.name}")
    return found


class SuccessorSiteTests(unittest.TestCase):
    def test_every_successor_site_is_classified(self):
        found = scan()
        self.assertEqual(sorted(found - SUCCESSOR_SITES.keys()), [],
                         "a new function computes Thumb successors: honour far jumps through "
                         "far_jump_profile.successors and classify it in SUCCESSOR_SITES")
        self.assertEqual(sorted(SUCCESSOR_SITES.keys() - found), [], "stale SUCCESSOR_SITES entries")

    def test_aware_sites_use_the_shared_rule(self):
        for name, kind in SUCCESSOR_SITES.items():
            module, function = name.split(":")
            if kind != AWARE or module == "far_jump_profile.py":
                continue
            with self.subTest(name):
                tree = ast.parse((ROOT / "tools" / module).read_text())
                (node,) = [node for node in ast.walk(tree)
                           if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.name == function]
                self.assertRegex(ast.unparse(node), r"far_jump\.(raw_)?successors\(")


class FarJumpWalkTests(unittest.TestCase):
    def test_a_far_jump_is_a_jump_and_is_recorded(self):
        instructions = walk(jump())
        self.assertEqual(far_jump.record(instructions, START), [[6, 14]])
        self.assertEqual(far_jump.report_line([[6, 14]]),
                         f"{far_jump.LINE}`{far_jump.SCHEMA}` {far_jump.SUMMARY}: +0x6->+0xE")
        # Nothing but the jump reaches its continuation: 0x20A is reached only from the beq.
        self.assertIn(0x0800020A, {item.address for item in instructions})

    def test_without_the_rule_the_pair_is_refused_as_before(self):
        with patch.object(far_jump.POLICY, "enabled", False):
            with self.assertRaisesRegex(ValueError, REFUSED):
                walk(jump())

    def test_a_selector_context_keeps_its_refusal(self):
        with self.assertRaisesRegex(ValueError, REFUSED):
            walk(jump(), acyclic_state_budget=64)

    def test_a_target_inside_an_instruction_refuses(self):
        # Into the second half of the pair itself.
        with self.assertRaisesRegex(ValueError, "invalid or truncated reachable instruction|enters the middle"):
            walk(jump(target=0x08000208))

    def test_a_target_on_a_pool_word_refuses(self):
        # 200 push {lr}; 202 ldr r0,[pc,#8] (the word at 20c); 204 bl 20c; 208 pop {r1}; 20a bx r1;
        # 20c the word, which decodes as pop {r1}; bx r1 when jumped into.
        code = body(half(0xB500, 0x4802), bl(0x08000204, 0x0800020C), half(0xBC02, 0x4708), half(0xBC02, 0x4708))
        with self.assertRaisesRegex(ValueError, "literal read overlaps reachable code"):
            walk(code)

    def test_a_target_at_the_entry_or_the_end_is_not_a_far_jump(self):
        for target in (START, START + len(jump())):
            with self.subTest(hex(target)):
                with self.assertRaisesRegex(ValueError, REFUSED):
                    walk(jump(target=target))

    def test_a_site_with_a_call_binding_stays_a_call(self):
        with self.assertRaisesRegex(ValueError, "call is not a validated external direct Thumb BL"):
            walk(jump(), calls={0x08000206: 0x0800020E})

    def test_the_continuation_in_lr_is_never_read(self):
        # 20e mov r0, lr: the walk finishes (r0 is a scalar), the dead-LR pass refuses.
        with self.assertRaisesRegex(ValueError, r"far jump: the continuation in LR is read at 0x0800020E"):
            walk(jump(tail=half(0x4670, 0xBC02, 0x4708)))
        # 20e push {lr} ... pop {r1}; pop {r2}; bx r2: the pushed word is the continuation.
        with self.assertRaisesRegex(ValueError, r"continuation in LR is read|not a validated|indirect"):
            walk(jump(tail=half(0xB500, 0xBC02, 0xBC04, 0x4710)))

    def test_the_continuation_in_lr_is_never_read_on_any_later_path(self):
        # rv-X1 M03/R33: 20e movs r0,#1; 210 mov r0, lr: the read is one instruction past the target.
        with self.assertRaisesRegex(ValueError, r"far jump: the continuation in LR is read at 0x08000210"):
            walk(jump(tail=half(0x2001, 0x4670, 0xBC02, 0x4708)))

    def test_an_instruction_that_reads_and_writes_lr_reads_it_first(self):
        # rv-X1 M14/R27: 20e add lr, r0 reads the continuation before it writes LR.
        with self.assertRaisesRegex(ValueError, r"far jump: the continuation in LR is read at 0x0800020E"):
            walk(jump(tail=half(0x4486, 0x4672, 0xBC02, 0x4708)))

    def test_an_lr_write_ends_the_continuation(self):
        # 20e mov lr, r2; 210 mov r0, lr; 212 pop {r1}; 214 bx r1: LR is rewritten before it is read.
        instructions = walk(jump(tail=half(0x4696, 0x4670, 0xBC02, 0x4708)))
        self.assertEqual(far_jump.record(instructions, START), [[6, 14]])

    def test_a_target_that_is_a_function_entry_refuses(self):
        # 20e movs r0,#0; 210 bx lr: a leaf inside the span returns through LR, the continuation.
        with self.assertRaisesRegex(ValueError, r"continuation in LR is read|indirect control flow"):
            walk(jump(tail=half(0x2000, 0x4770)))

    def test_an_unbalanced_frame_at_the_return_refuses(self):
        # 20e pop {r1}; 210 sub sp,#4; 212 bx r1: the entry LR, with a word left allocated.
        with self.assertRaisesRegex(ValueError, "return does not balance the saved stack frame"):
            walk(jump(tail=half(0xBC02, 0xB081, 0x4708)))

    def test_a_jump_keeps_every_register_but_lr(self):
        # 200 push {lr}; 202 movs r2,#5; 204 bl 20a; 208 movs r2,#6 (not reached); 20a cmp r2,#5;
        # 20c pop {r1}; 20e bx r1.  The walk reaches 20a only through the jump.
        code = body(half(0xB500, 0x2205), bl(0x08000204, 0x0800020A), half(0x2206, 0x2A05, 0xBC02, 0x4708))
        instructions = walk(code)
        self.assertNotIn(0x08000208, {item.address for item in instructions})
        self.assertEqual(far_jump.record(instructions, START), [[4, 10]])


class DefaultContextTests(unittest.TestCase):
    def test_only_default_parameters_and_proofs(self):
        rom, mapping = bytes(0x1000), "[]"
        base = {"data": b"", "address": START, "thumb": True}

        def default_walk(values):
            return far_jump.default_walk(dict.fromkeys(match.VERIFY_LEAF_PARAMETERS) | values,
                                         match.VERIFY_LEAF_PARAMETERS)
        self.assertTrue(default_walk(base))
        self.assertTrue(default_walk(dict(base, buffer_proof=match.BufferCallProof(rom, mapping))))
        self.assertTrue(default_walk(dict(base, buffer_proof=match.FunctionBufferCallProof(rom, mapping))))
        self.assertFalse(default_walk(dict(base, thumb=False)))
        self.assertFalse(default_walk(dict(base, menu_list_frame=object())))
        self.assertFalse(default_walk(dict(base, switch_relocations={})))

        class Selector(match.BufferCallProof):
            pass
        selector = Selector(rom, mapping)
        self.assertFalse(default_walk(dict(base, buffer_proof=selector)))
        # A callee walk resolves through the proof that inspects it.
        self.assertFalse(default_walk(dict(base, call_resolver=selector.resolve_call)))
        proof = match.BufferCallProof(rom, mapping)
        self.assertTrue(default_walk(dict(base, call_resolver=proof.resolve_call)))
        with patch.object(far_jump.POLICY, "enabled", False):
            self.assertFalse(default_walk(base))

    def test_every_other_parameter_is_a_selector_context(self):
        names = match.VERIFY_LEAF_PARAMETERS
        self.assertLessEqual(far_jump.PARAMETERS, names)
        self.assertIn("menu_list_frame", names - far_jump.PARAMETERS)
        self.assertIn("double_context", names - far_jump.PARAMETERS)


class RecordTests(unittest.TestCase):
    def test_callee_far_jumps_are_bound_into_the_fingerprint_and_ledgers(self):
        proof = match.BufferCallProof(bytes(0x1000), "[]")
        before = proof.fingerprint()
        self.assertEqual(far_jump.lines(proof), [])
        proof.far_jumps[0x08000400] = [[2, 8]]
        self.assertNotEqual(proof.fingerprint(), before)
        self.assertEqual(far_jump.lines(proof),
                         [f"{far_jump.BUFFER_LINE}`{far_jump.SCHEMA}` callee 0x08000400: +0x2->+0x8"])
        self.assertEqual(proof.loop_replay_lines()[-1:], far_jump.lines(proof))
        # An aborted inspection leaves no far-jump record.
        saved = proof._snapshot_ledgers()
        proof.far_jumps[0x08000500] = [[2, 6]]
        proof._restore_ledgers(saved)
        self.assertEqual(proof.far_jumps, {0x08000400: [[2, 8]]})

    def test_the_stack_index_analysis_follows_only_the_core_far_jumps(self):
        import stack_index_precondition_profile as analysis_profile
        # 200 push {lr}; 202 bl 0x08000400 (a call); 206 bl 20e (a far jump); 20a pop {r1}; 20c bx r1;
        # 20e movs r0,#1; 210 pop {r1}; 212 bx r1
        code = body(half(0xB500), bl(0x08000202, 0x08000400), bl(0x08000206, 0x0800020E),
                    half(0xBC02, 0x4708, 0x2001, 0xBC02, 0x4708))
        analysis = analysis_profile.Analysis(code, START, frozenset(), frozenset(), {})
        self.assertEqual(analysis.reaches([0x08000202]), {0x08000206, 0x0800020A, 0x0800020C})
        analysis.far_jumps = {0x08000206: 0x0800020E}
        self.assertEqual(analysis.reaches([0x08000202]), {0x08000206, 0x0800020E, 0x08000210, 0x08000212})
        evidence_ = analysis_profile.forwarding_evidence(
            analysis, {"releases": [[0x08000202, [4]]], "walked": set(), "slots": [], "trusted": []})
        self.assertEqual(evidence_["trusted_calls"], [])


# A hand-built ROM for the buffer proofs: the root at 0x08000200 and the callees each at its address.
def rom_with(root_code, callees):
    import json
    rom = bytearray(0x1000)
    rom[START - match.ROM_BASE:START - match.ROM_BASE + len(root_code)] = root_code
    entries = [{"rom": f"0x{START:08X}", "end": f"0x{START + len(root_code):08X}", "mode": "thumb"}]
    for address, code in callees:
        rom[address - match.ROM_BASE:address - match.ROM_BASE + len(code)] = code
        entries.append({"rom": f"0x{address:08X}", "end": f"0x{address + len(code):08X}", "mode": "thumb"})
    return bytes(rom), json.dumps(entries)


def stack_walk(root_code, calls, callees):
    """The root under the default stack-argument proof; returns (instructions, proof)."""
    rom, mapping = rom_with(root_code, callees)
    proof = match.BufferCallProof(rom, mapping, stack_arguments=True, loop_replay=True, bios_wrappers=True,
                                  dead_registers=True, forward_slots=True)
    instructions = match.verify_leaf_instructions(root_code, START, True, dict(calls), buffer_proof=proof,
                                                  incoming_narrow_reads=True)
    return instructions, proof


# rv-X1 C09: 200 push {lr}; 202 sub sp,#8; 204 mov r1,sp; 206 bl 400 (a buffer call); 20a mov r1,sp; 20c bl 214
# (the far jump, r1 = sp across it); 210 movs r0,#0; 212 nop; 214 bl 410 (gets r1 = sp); 218 movs r1,#0;
# 21a add sp,#8; 21c pop {r0}; 21e bx r0
ROOT_ALIAS_ACROSS = body(half(0xB500, 0xB082, 0x4669), bl(0x08000206, 0x08000400), half(0x4669),
                         bl(0x0800020C, 0x08000214), half(0x2000, 0x46C0), bl(0x08000214, 0x08000410),
                         half(0x2100, 0xB002, 0xBC01, 0x4700))
ROOT_ALIAS_CALLS = {0x08000206: 0x08000400, 0x08000214: 0x08000410}
STORES_RAW = half(0x8008, 0x80C8, 0x4770)            # strh r0,[r1]; strh r0,[r1,#6]; bx lr


class AliasAcrossFarJumpTests(unittest.TestCase):
    def test_a_frame_alias_crosses_the_jump_and_keeps_its_bounds(self):
        # rv-X1 M17: the jump changes no register but LR, so r1 = sp reaches the call at 214 and the
        # callee is walked with it: in bounds it is admitted and inspected ...
        instructions, proof = stack_walk(ROOT_ALIAS_ACROSS, ROOT_ALIAS_CALLS,
                                         [(0x08000400, STORES_RAW), (0x08000410, STORES_RAW)])
        self.assertEqual(far_jump.record(instructions, START), [[12, 20]])
        self.assertIn(0x08000410, proof.dependencies)
        # ... and a store past the frame through it refuses.
        with self.assertRaisesRegex(ValueError, "outside allocated local words|unaligned"):
            stack_walk(ROOT_ALIAS_ACROSS, ROOT_ALIAS_CALLS,
                       [(0x08000400, STORES_RAW), (0x08000410, half(0x8108, 0x4770))])


class LifetimeTests(unittest.TestCase):
    """K5 (closure_slot_profile.check_lifetime) over a walked root with a far jump (rv-X1 L01/L01b/L02)."""
    # 200 push {lr}; 202 sub sp,#8; 204 add sp,#8 (the release); 206 cmp r0,#0; 208 beq 20e; 20a the far jump
    # (or b 212; nop); 20e movs r0,#1; 210 b 216; 212 sub sp,#8 (an allocation after the release); 214 add sp,#8;
    # 216 pop {r1}; 218 bx r1
    HEAD = half(0xB500, 0xB082, 0xB002, 0x2800, 0xD001)
    TAIL = half(0x2001, 0xE001, 0xB082, 0xB002, 0xBC02, 0x4708)

    def lifetime(self, code):
        instructions = walk(code)
        closure.check_lifetime(None, code, START, instructions)
        return instructions

    def test_the_lifetime_check_follows_the_far_jump(self):
        for name, code in (("far", body(self.HEAD, bl(0x0800020A, 0x08000212), self.TAIL)),
                           ("near", body(self.HEAD, half(0xE002, 0x46C0), self.TAIL)),
                           # no beq: the continuation 20e is never walked, the target is
                           ("unreached", body(half(0xB500, 0xB082, 0xB002, 0x46C0, 0x46C0),
                                              bl(0x0800020A, 0x08000212), self.TAIL))):
            with self.subTest(name):
                with self.assertRaisesRegex(ValueError, "descriptor word lifetime excludes allocation after deallocation"):
                    self.lifetime(code)

    def test_a_far_jump_past_no_allocation_is_admitted(self):
        # 212 movs r3,#1 instead of the allocation.
        tail = half(0x2001, 0xE000, 0x2301, 0xBC02, 0x4708)
        instructions = self.lifetime(body(self.HEAD, bl(0x0800020A, 0x08000212), tail))
        self.assertEqual(far_jump.record(instructions, START), [[10, 18]])


class ClosureCycleTests(unittest.TestCase):
    def test_a_loop_closed_by_a_far_jump_is_a_cycle(self):
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        # 200 movs r0,#0; 202 adds r0,#1; 204 cmp r0,#3; 206 beq 20c; 208 bl 202 (the far jump back);
        # 20c bx lr
        code = body(half(0x2000, 0x3001, 0x2803, 0xD001), bl(0x08000208, 0x08000202), half(0x4770))
        items = list(decoder.disasm(code, START))
        # Unmarked, the BL is a call that returns: no loop.  The walk marks the far jump it takes.
        self.assertEqual(closure._cyclic_sites(items), set())
        far_jump.mark(items[4])
        self.assertEqual(closure._cyclic_sites(items), {0x08000202, 0x08000204, 0x08000206, 0x08000208})


# A root with a far jump needs a skip agbcc cannot reach with a B (2 KiB): 400 calls of 6 bytes.
FAR_CALLEES = 0x08001000


def far_owner(index=False, calls=400, data=False):
    steps = "".join("        func_08001100(1);\n" for _ in range(calls))
    store = "    buffer[i & 3] = value;\n" if index else ""
    result = ("    data_02000000[0] = buffer[0];\n    data_02000000[1] = buffer[3];\n" if data else
              "    return buffer[0] + buffer[3];\n")
    return (f"typedef unsigned short u16;\n"
            f"{'extern u16 data_02000000[];' + chr(10) if data else ''}"
            f"extern void func_08001000(u16 value, u16 *out);\n"
            f"extern void func_08001100(int step);\n"
            f"{'void' if data else 'u16'} func_08000200(u16 value{', u16 i' if index else ''})\n"
            f"{{\n    u16 buffer[4];\n\n{store}    if (value) {{\n{steps}    }}\n"
            f"    func_08001000(value, buffer);\n{result}}}\n")


STORES = "strh r0, [r1]\nstrh r0, [r1, #6]\nbx lr"
OUTSIDE = "strh r0, [r1, #8]\nbx lr"
# A callee with a far jump of its own (+2 -> +8), and the same reading the continuation.
CALLEE_FAR = "push {lr}\nbl 1f\nmovs r0, #9\n1: strh r0, [r1]\nstrh r0, [r1, #6]\npop {r0}\nbx r0"
CALLEE_LR = "push {lr}\nbl 1f\nmovs r0, #9\n1: mov r2, lr\nstrh r0, [r1]\nstrh r0, [r1, #6]\npop {r0}\nbx r0"
# rv-X1's K5 cases: the adapter releases its frame, then branches to a new allocation (6:) or past it.
K5_RELEASE = "sub sp, #8\nadd sp, #8\ncmp r0, #0\nbeq 5f\n"
K5_TAIL = "5: movs r3, #0\nb 7f\n6: sub sp, #8\nadd sp, #8\n7: "
K5_NO_REALLOCATION = "5: movs r3, #0\nb 7f\n6: movs r3, #1\n7: "
CALLEE_FAR_OUTSIDE = "push {lr}\nbl 1f\nmovs r0, #9\n1: strh r0, [r1, #8]\npop {r0}\nbx r0"


@unittest.skipUnless(tools_present(), "fixed compiler and ARM tools required")
class FarJumpNativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix="far_jumps_", dir=scratch)
        cls.base = Path(cls.temporary.name)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def far_root(self, name, index=False, callee=STORES, data=False):
        with patch.object(data_buffer_tests, "CALLEES", FAR_CALLEES):
            return build(self.base / name, far_owner(index, data=data),
                         [("func_08001000", callee), ("func_08001100", "bx lr")], large=True)

    def replays(self, report, root):
        with patch.dict(os.environ, FFTA_ROM=str(root / "baserom.bin")):
            return evidence.report_matches(report, root, A)

    def admitted(self, root):
        code, output, report = run(root)
        self.assertEqual(code, 0, output[-4000:])
        self.assertIsNotNone(report)
        self.assertTrue(self.replays(report, root))
        return report

    def refused(self, root, message):
        code, output, report = run(root)
        self.assertNotEqual(code, 0, output[-2000:])
        self.assertIsNone(report)
        self.assertRegex(output, message)
        return output

    def far_lines(self, report, prefix=far_jump.LINE):
        return [line for line in report.splitlines() if line.startswith(prefix)]

    def test_root_far_jump_is_admitted_stated_and_replayed(self):
        root = self.far_root("root")
        report = self.admitted(root)
        (line,) = self.far_lines(report)
        self.assertRegex(line, rf"^{re.escape(far_jump.LINE)}`{far_jump.SCHEMA}` .*: \+0x[0-9A-F]+->\+0x[0-9A-F]+$")
        self.assertEqual(data_buffer_tests.verification(report), evidence.STACK_BUFFER_SCHEMA)
        # The line is bound: dropped or edited, the replay refuses; without the rule it refuses too.
        self.assertFalse(self.replays(report.replace(line + "\n", ""), root))
        self.assertFalse(self.replays(report.replace(line, line[:-1] + "0"), root))
        with patch.object(far_jump.POLICY, "enabled", False):
            self.assertFalse(self.replays(report, root))

    def test_root_far_jump_on_the_data_buffer_route(self):
        root = self.far_root("data", data=True)
        report = self.admitted(root)
        (line,) = self.far_lines(report)
        self.assertIn("data-buffer", data_buffer_tests.verification(report))
        self.assertFalse(self.replays(report.replace(line + "\n", ""), root))
        with patch.object(far_jump.POLICY, "enabled", False):
            self.assertFalse(self.replays(report, root))

    def test_root_far_jump_keeps_the_buffer_bounds(self):
        self.refused(self.far_root("root_outside", callee=OUTSIDE), "outside allocated local words|unaligned")

    def test_root_far_jump_on_the_stack_index_retry(self):
        root = self.far_root("index", index=True)
        report = self.admitted(root)
        self.assertEqual(len(self.far_lines(report)), 1)
        self.assertIn("default-stack-index-retry-v1", report)
        # The analysis takes only the far jumps the core walked.
        import stack_index_precondition_profile as analysis
        original = analysis.prove_words

        def without(*arguments, **keywords):
            keywords["far_jumps"] = None
            return original(*arguments, **keywords)
        with patch.object(analysis, "prove_words", without):
            self.assertFalse(self.replays(report, root))

    def test_callee_far_jump_is_fingerprinted_and_stated(self):
        for name, source, callees in (
                ("plain", BUFFER_ONLY, [("func_08000400", CALLEE_FAR)]),
                ("literal", LITERAL % dict(extra=""), [("func_08000400", CALLEE_FAR), ("func_08000500", "bx lr")])):
            with self.subTest(name):
                root = build(self.base / f"callee_{name}", source, callees)
                report = self.admitted(root)
                self.assertFalse(self.far_lines(report))
                (line,) = self.far_lines(report, far_jump.BUFFER_LINE)
                self.assertEqual(line, f"{far_jump.BUFFER_LINE}`{far_jump.SCHEMA}` callee 0x08000400: +0x2->+0x8")
                self.assertFalse(self.replays(report.replace(line + "\n", ""), root))
                with patch.object(far_jump.POLICY, "enabled", False):
                    self.assertFalse(self.replays(report, root))

    def closure_root(self, name, before):
        import test_closure_slots as tcs
        from test_call_via_targets import index_thunks
        return index_thunks(build(self.base / name, tcs.OWNER, tcs.callees(adapter_body=tcs.adapter(before_reload=before)),
                                  large=True, function_literal_thunks=True))

    def test_closure_lifetime_follows_a_callee_far_jump(self):
        # rv-X1 K5: the adapter (walked in the closure-slot retry) releases its frame, then reaches a new
        # allocation through a far jump: the lifetime check must follow the jump as it follows a B.
        for name, jump in (("k5_far", "bl 6f"), ("k5_near", "b 6f")):
            with self.subTest(name):
                self.refused(self.closure_root(name, K5_RELEASE + jump + "\n" + K5_TAIL),
                             "descriptor word lifetime excludes allocation after deallocation")
        report = self.admitted(self.closure_root("k5_far_ok", K5_RELEASE + "bl 6f\n" + K5_NO_REALLOCATION))
        (line,) = self.far_lines(report, far_jump.BUFFER_LINE)
        self.assertTrue(line.startswith(f"{far_jump.BUFFER_LINE}`{far_jump.SCHEMA}` callee 0x08000500: "), line)

    def test_default_routes_reach_only_classified_successor_sites(self):
        """Issue and replay each default route with a far jump in process: every successor-computing
        function they run must be one that honours far jumps (SUCCESSOR_SITES, not SELECTOR)."""
        import test_data_buffer_calls as fixtures
        roots = {"root": self.far_root("route_root"), "index": self.far_root("route_index", index=True),
                 "data": self.far_root("route_data", data=True),
                 "callee": build(self.base / "route_callee", BUFFER_ONLY, [("func_08000400", CALLEE_FAR)]),
                 "literal": build(self.base / "route_literal", LITERAL % dict(extra=""),
                                  [("func_08000400", CALLEE_FAR), ("func_08000500", "bx lr")]),
                 "closure": self.closure_root("route_closure", K5_RELEASE + "bl 6f\n" + K5_NO_REALLOCATION),
                 "closure_refused": self.closure_root("route_closure_refused", K5_RELEASE + "bl 6f\n" + K5_TAIL)}
        tools = str(ROOT / "tools")
        reached = {}

        def profile(frame, event, argument):
            if event == "call" and frame.f_code.co_filename.startswith(tools):
                reached.setdefault(f"{Path(frame.f_code.co_filename).name}:{frame.f_code.co_name}", set()).add(route)
        for route, root in roots.items():
            report_path = root / "docs/match/08000200.md"
            with patch.dict(os.environ, FFTA_ROM=str(root / "baserom.bin")), \
                    patch.object(sys, "argv", ["match.py", "--root", str(root), "0x08000200"]):
                sys.setprofile(profile)
                try:
                    runpy.run_path(str(ROOT / "tools/match.py"), run_name="__main__")
                except SystemExit:
                    pass
                finally:
                    sys.setprofile(None)
                if report_path.exists():
                    report = report_path.read_text()
                    sys.setprofile(profile)
                    try:
                        replayed = evidence.report_matches(report, root, A)
                    finally:
                        sys.setprofile(None)
                    self.assertTrue(replayed, route)
                else:
                    self.assertEqual(route, "closure_refused")
        self.assertTrue(roots and fixtures.A == A)
        found = scan()
        sites = {name: sorted(routes) for name, routes in reached.items() if name in found}
        self.assertIn("protected_descriptor_word_profile.py:check_lifetime", sites)
        self.assertIn("match.py:_check_arguments", sites)
        self.assertEqual({name: routes for name, routes in sites.items()
                          if SUCCESSOR_SITES.get(name) not in DEFAULT_ROUTE_KINDS}, {})

    def test_callee_far_jump_keeps_its_proofs(self):
        self.refused(build(self.base / "callee_lr", BUFFER_ONLY, [("func_08000400", CALLEE_LR)]),
                     r"buffer callee 0x08000400: far jump: the continuation in LR is read at 0x08000408")
        self.refused(build(self.base / "callee_outside", BUFFER_ONLY, [("func_08000400", CALLEE_FAR_OUTSIDE)]),
                     r"buffer callee 0x08000400: .*(outside allocated local words|unaligned)")


if __name__ == "__main__":
    unittest.main()
