"""Stack-array callers of the pinned known list queries, refusals and a CPU oracle."""
import copy
import importlib.util
import json
from pathlib import Path
import struct
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import owner_admission_profile as owner
import known_query_stack_buffer_profile as stack
from test_nested_known_query import assemble

A, B, OTHER = 0x08010000, 0x08011000, 0x08099D60
Q = 0x08099CDC
ROM_SIZE = 0x150000

# push {r4-r6,lr}; sub sp,#52; mov r1,sp; bl Q; cmp r0,#0; ble done; mov r5,sp;
# adds r6,r0,#0; loop: ldr r0,[r5]; bl B; adds r5,#4; subs r6,#1; cmp r6,#0;
# bne loop; done: add sp,#52; pop {r4-r6}; pop {r0}; bx r0
CALLER = [0xb570, 0xb08d, 0x4669, Q, 0x2800, 0xdd08, 0x466d, 0x1c06,
          0x6828, B, 0x3504, 0x3e01, 0x2e00, 0xd1f8,
          0xb00d, 0xbc70, 0xbc01, 0x4700]


def pinned_bodies():
    bodies = {address: (17, stack.query_body(address)) for address in stack.QUERIES}
    bodies.update({address: (count, bytes.fromhex(code))
                   for address, (count, code) in stack.DEPENDENCIES.items()})
    return bodies


def fixture(tokens=CALLER, *, patch=None):
    raw = assemble(A, tokens)
    rom = bytearray(ROM_SIZE)
    rom[A-match.ROM_BASE:A-match.ROM_BASE+len(raw)] = raw
    rom[B-match.ROM_BASE:B-match.ROM_BASE+2] = bytes.fromhex('7047')
    rom[OTHER-match.ROM_BASE:OTHER-match.ROM_BASE+2] = bytes.fromhex('7047')
    spans = [(A, len(raw), 0), (B, 2, 1), (OTHER, 2, 1)]
    for address, (count, body) in pinned_bodies().items():
        rom[address-match.ROM_BASE:address-match.ROM_BASE+len(body)] = body
        spans.append((address, len(body), count))
    for address, padding in stack.THUNK_PADDING.items():
        rom[address+2-match.ROM_BASE:address+4-match.ROM_BASE] = bytes.fromhex(padding)
    if patch:
        for address, value in patch.items():
            rom[address-match.ROM_BASE] = value
    rows = [dict(rom=f'0x{a:08X}', end=f'0x{a+n:08X}', mode='thumb', instrs=count)
            for a, n, count in sorted(spans)]
    mapping = json.dumps(rows).encode()
    caller = next(r for r in rows if int(r['rom'], 16) == A)
    caller['instrs'] = owner.refine(raw, A, mapping)['instrs']
    mapping = json.dumps(rows).encode()
    import owner_graph_profile as graph
    _, _, _, calls, _ = graph.graph(raw, A, owner.refine(raw, A, mapping))
    return dict(data=raw, address=A, rom=bytes(rom), mapping=mapping,
        index=''.join(f'{int(r["rom"],16):08X} {int(r["end"],16):08X} '
                      f'{int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n' for r in rows).encode(),
        objects=b'{}',
        bindings=dict(calls=[[site-A, f'func_{target:08X}'] for site, target in sorted(calls.items())],
                      data=[], functions=[], switches=[]),
        selector=stack.SELECTOR)


def changed(index, token, tokens=CALLER):
    tokens = list(tokens); tokens[index] = token
    return fixture(tokens)


def straight(pre=(0x4669,), post=(), epilogue=(0xbc01, 0x4700), frame=0xb08d):
    """push {r4-r6,lr}; sub sp; <pre>; bl Q; <post>; add sp; pop {r4-r6}; <epilogue>."""
    return fixture([0xb570, frame, *pre, Q, *post, frame-0x80, 0xbc70, *epilogue])


class KnownQueryStackBufferTests(unittest.TestCase):
    def test_stack_array_caller_executes_every_premised_count(self):
        manifest, _ = owner.verify(**fixture())
        self.assertEqual(manifest['profile'], stack.SCHEMA)
        proof = manifest['proof']
        caller = proof['caller']
        self.assertEqual(caller['returned_counts'], list(range(14)))
        self.assertEqual(caller['query_calls'], [dict(site=A+6, target=Q, buffer_entry_SP_offset=-68,
                         buffer_words=13, caller_SP_offset=-68)])
        self.assertEqual(sorted({at for _, at in caller['local_reads']}), list(range(-68, -16, 4)))
        self.assertEqual(caller['uninitialized_private_reads'], 0)
        self.assertFalse(proof['list_bound_proved_from_ROM'])
        self.assertFalse(proof['termination_proved'])
        self.assertIn('at most 13 nodes', proof['explicit_conditions'][0])
        self.assertEqual(len(proof['query_contract']['identities']), 9)

    def test_each_pinned_query_is_admitted(self):
        for target in stack.QUERIES:
            tokens = list(CALLER); tokens[3] = target
            with self.subTest(target=hex(target)):
                manifest, _ = owner.verify(**fixture(tokens))
                self.assertEqual(manifest['proof']['caller']['query_calls'][0]['target'], target)

    def test_buffer_smaller_than_write_bound_refuses(self):
        tokens = list(CALLER); tokens[1] = 0xb08c; tokens[14] = 0xb00c
        with self.assertRaisesRegex(ValueError, 'smaller than the premised 13-word'):
            owner.verify(**fixture(tokens))

    def test_buffer_starting_inside_the_array_refuses(self):
        with self.assertRaisesRegex(ValueError, 'smaller than the premised 13-word'):
            owner.verify(**changed(2, 0xa901))  # add r1, sp, #4

    def test_read_beyond_returned_count_refuses(self):
        # A 14-word array keeps word 13 allocated, so only initialization refuses.
        tokens = list(CALLER); tokens[1] = 0xb08e; tokens[14] = 0xb00e
        tokens[7] = 0x1c46  # adds r6, r0, #1
        with self.assertRaisesRegex(ValueError, 'uninitialized'):
            owner.verify(**fixture(tokens))
        # With exactly 13 words, the first refused path is n = 13 reading word 13,
        # which is the saved R4 slot.
        with self.assertRaisesRegex(ValueError, 'outside allocated local words'):
            owner.verify(**changed(7, 0x1c46))

    def test_straight_line_caller_is_admitted(self):
        manifest, _ = owner.verify(**straight())
        self.assertEqual(manifest['proof']['caller']['returned_counts'], list(range(14)))

    def test_query_scratch_registers_are_undefined_afterwards(self):
        # The pinned collector leaves R2 = out+4n; for n = 13 that is the saved R4 slot.
        for post in ((0x2300, 0x6093),            # movs r3,#0; str r3,[r2,#8]
                     (0x6808,),                   # ldr r0,[r1]
                     (0x1c18,),                   # adds r0,r3,#0
                     (0x4660,),                   # mov r0,ip
                     (0x9100,)):                  # str r1,[sp]
            with self.subTest(post=[hex(x) for x in post]), \
                    self.assertRaisesRegex(ValueError, 'untracked register'):
                owner.verify(**straight(post=post))

    def test_direct_call_to_pinned_dependency_refuses(self):
        for target in (0x0809AC20, 0x080C7CC0):
            with self.subTest(target=hex(target)), \
                    self.assertRaisesRegex(ValueError, 'pinned query dependency'):
                owner.verify(**changed(9, target))

    def test_ordinary_call_stack_words_are_recorded(self):
        manifest, _ = owner.verify(**fixture())
        # The loop call at A+20 sees the initialized prefix of the buffer at SP.
        self.assertEqual(manifest['proof']['caller']['ordinary_call_initialized_words_at_SP'],
                         [[A+20, list(range(1, 14))]])

    def test_ordinary_call_scratch_registers_are_undefined_afterwards(self):
        tokens = list(CALLER); tokens[10] = 0x6809  # ldr r1,[r1] after bl B
        with self.assertRaisesRegex(ValueError, 'untracked register'):
            owner.verify(**fixture(tokens))

    def test_private_address_stored_to_local_or_external_refuses(self):
        with self.assertRaisesRegex(ValueError, 'stored to a local word'):
            owner.verify(**straight(post=(0x4668, 0x9001)))  # mov r0,sp; str r0,[sp,#4]
        with self.assertRaisesRegex(ValueError, 'stored to external memory'):
            # movs r1,#0x80; lsls r1,r1,#19; mov r0,sp; str r0,[r1]
            owner.verify(**straight(post=(0x2180, 0x04c9, 0x4668, 0x6008)))

    def test_misaligned_buffer_refuses(self):
        with self.assertRaisesRegex(ValueError, 'aligned private stack address'):
            owner.verify(**straight(pre=(0x4669, 0x3102)))  # mov r1,sp; adds r1,#2

    def test_private_address_in_other_query_arguments_refuses(self):
        for register, move in (('r0', 0x4668), ('r2', 0x466a), ('r3', 0x466b)):
            with self.subTest(register=register), \
                    self.assertRaisesRegex(ValueError, 'passed to a call'):
                owner.verify(**straight(pre=(0x4669, move)))

    def test_private_address_in_return_register_refuses(self):
        with self.assertRaisesRegex(ValueError, 'escapes through a return register'):
            # mov r0,sp before the frame release; pop {r1}; bx r1
            owner.verify(**straight(post=(0x4668,), epilogue=(0xbc02, 0x4708)))

    def test_subword_private_access_refuses(self):
        for post in ((0x466b, 0x8818),            # mov r3,sp; ldrh r0,[r3]
                     (0x466b, 0x2000, 0x7018)):   # mov r3,sp; movs r0,#0; strb r0,[r3]
            with self.subTest(post=[hex(x) for x in post]), \
                    self.assertRaisesRegex(ValueError, 'aligned word'):
                owner.verify(**straight(post=post))

    def test_state_budget_exhaustion_refuses(self):
        with patch.object(stack, 'MAX_STATES', 8), \
                self.assertRaisesRegex(ValueError, 'state budget exhausted'):
            owner.verify(**fixture())

    def test_saved_word_inside_the_buffer_window_refuses(self):
        # 13 local words, then push {r3} and pass the new SP: word 0 is the saved R3.
        tokens = [0xb570, 0xb08d, 0xb408, 0x4669, Q, 0xbc08, 0xb00d, 0xbc70, 0xbc01, 0x4700]
        with self.assertRaisesRegex(ValueError, 'smaller than the premised 13-word'):
            owner.verify(**fixture(tokens))

    def test_larger_array_is_admitted(self):
        tokens = list(CALLER); tokens[1] = 0xb08e; tokens[14] = 0xb00e
        manifest, _ = owner.verify(**fixture(tokens))
        self.assertEqual(manifest['proof']['caller']['query_calls'][0]['buffer_entry_SP_offset'], -72)

    def test_read_before_count_check_refuses(self):
        with self.assertRaisesRegex(ValueError, 'uninitialized'):
            owner.verify(**changed(4, 0x9c00))  # ldr r4, [sp] replaces cmp r0, #0

    def test_different_callee_refuses(self):
        with self.assertRaisesRegex(ValueError, 'outside the pinned query contract'):
            owner.verify(**changed(3, OTHER))

    def test_private_address_to_ordinary_call_refuses(self):
        with self.assertRaisesRegex(ValueError, 'passed to a call'):
            owner.verify(**changed(8, 0x1c28))  # adds r0, r5, #0

    def test_tampered_callee_rom_bytes_refuse(self):
        for address, (_, body) in sorted(pinned_bodies().items()):
            for offset in sorted({0, len(body)-1}):
                with self.subTest(address=hex(address), offset=offset), \
                        self.assertRaisesRegex(ValueError, 'pinned known-query dependency'):
                    original = body[offset]
                    owner.verify(**fixture(patch={address+offset: original ^ 1}))

    def test_owned_or_changed_thunk_padding_refuses(self):
        with self.assertRaisesRegex(ValueError, 'padding'):
            owner.verify(**fixture(patch={0x0814225E: 0}))

    def test_changed_dependency_extent_or_count_refuses(self):
        f = fixture(); rows = json.loads(f['mapping'])
        row = next(r for r in rows if int(r['rom'], 16) == 0x080C7CC0)
        row['instrs'] = 17
        f['mapping'] = json.dumps(rows).encode()
        f['index'] = f['index'].replace(b'080C7CC0 080C7CE2 34 16', b'080C7CC0 080C7CE2 34 17')
        with self.assertRaisesRegex(ValueError, 'pinned known-query dependency'):
            owner.verify(**f)

    def test_tampered_manifest_refuses(self):
        f = fixture(); manifest, _ = owner.verify(**f)
        edits = [
            ('caller', 'returned_counts', list(range(13))),
            ('caller', 'query_calls', []),
            ('query_contract', 'capacity_words', 12),
            ('query_contract', 'identities', []),
            (None, 'list_bound_proved_from_ROM', True),
            (None, 'explicit_conditions', []),
        ]
        for section, key, value in edits:
            bad = copy.deepcopy(manifest)
            (bad['proof'][section] if section else bad['proof'])[key] = value
            with self.subTest(key=key), self.assertRaisesRegex(ValueError, 'manifest differs'):
                owner.verify(**f, manifest=bad)
        manifest_again, _ = owner.verify(**f, manifest=manifest)
        self.assertEqual(manifest_again, manifest)

    def test_selector_routes_reports_and_stays_opt_in(self):
        report = f'# 0x{A:08X}\n\n* verification: `{stack.SCHEMA}`\n'
        self.assertTrue(owner.selected(report))
        self.assertEqual(owner.selector_for_report(report), stack.SELECTOR)
        with self.assertRaisesRegex(ValueError, 'buffer callee 0x08099CDC'):
            f = fixture()
            calls = {A+6: Q, A+20: B}
            proof = match.BufferCallProof(f['rom'], f['mapping'], stack_arguments=True)
            match.verify_leaf_instructions(f['data'], A, True, calls, buffer_proof=proof)


@unittest.skipUnless(importlib.util.find_spec('unicorn'), 'unicorn CPU oracle not installed')
class QueryContractOracle(unittest.TestCase):
    """Run the exact pinned query bytes on a CPU against the contract relation."""

    def run_query(self, target, nodes):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_MEM_WRITE, UC_HOOK_CODE
        from unicorn import arm_const as arm
        rom = fixture()['rom']
        cpu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        cpu.mem_map(0x08000000, ROM_SIZE); cpu.mem_write(0x08000000, rom)
        cpu.mem_map(0x02000000, 0x40000)
        owner_at, list_at, node_at = 0x02010000, 0x02010100, 0x02011000
        offset = stack.QUERIES[target][0]
        cpu.mem_write(owner_at+offset, struct.pack('<I', list_at))
        first = node_at if nodes else 0
        cpu.mem_write(list_at+4, struct.pack('<I', first))
        for k in range(nodes):
            at = node_at+16*k
            following = at+16 if k+1 < nodes else 0
            cpu.mem_write(at, struct.pack('<III', 0x03000000+k, 0, following))
        caller_sp, stop = 0x02030000, 0x08008000
        buffer = caller_sp
        cpu.mem_write(buffer, b'\xee' * 4 * 20)
        cpu.reg_write(arm.UC_ARM_REG_SP, caller_sp)
        cpu.reg_write(arm.UC_ARM_REG_R0, owner_at); cpu.reg_write(arm.UC_ARM_REG_R1, buffer)
        cpu.reg_write(arm.UC_ARM_REG_LR, stop | 1)
        cpu.reg_write(arm.UC_ARM_REG_R2, 0x2222); cpu.reg_write(arm.UC_ARM_REG_R3, 0x3333)
        cpu.reg_write(arm.UC_ARM_REG_R12, 0xcccc)
        saved = {getattr(arm, f'UC_ARM_REG_R{n}'): 0x1000+n for n in range(4, 12)}
        for register, value in saved.items():
            cpu.reg_write(register, value)
        writes, lowest = [], [caller_sp]

        everywhere = []

        def write(uc, access, at, size, value, user):
            everywhere.append((at, size))
            if at >= caller_sp:
                writes.append((at-buffer, size, value & 0xffffffff))

        def code(uc, pc, size, user):
            lowest[0] = min(lowest[0], uc.reg_read(arm.UC_ARM_REG_SP))
        cpu.hook_add(UC_HOOK_MEM_WRITE, write); cpu.hook_add(UC_HOOK_CODE, code)
        cpu.emu_start(target | 1, stop, count=4096)
        self.assertEqual(cpu.reg_read(arm.UC_ARM_REG_PC), stop)
        self.assertEqual(cpu.reg_read(arm.UC_ARM_REG_SP), caller_sp)
        for register, value in saved.items():
            self.assertEqual(cpu.reg_read(register), value)
        # Scratch results: R1 is the restored return, R3/R12 are untouched, and
        # R2 is the collector cursor out+4n (or the expired root closure when
        # n = 0). The profile therefore leaves R1-R3/R12/LR undefined.
        self.assertEqual(cpu.reg_read(arm.UC_ARM_REG_R1), stop | 1)
        self.assertEqual(cpu.reg_read(arm.UC_ARM_REG_R2),
                         buffer+4*nodes if nodes else caller_sp-12)
        self.assertEqual(cpu.reg_read(arm.UC_ARM_REG_R3), 0x3333)
        self.assertEqual(cpu.reg_read(arm.UC_ARM_REG_R12), 0xcccc)
        # Every store is in the query's own 44-byte frame below the caller SP
        # or in out[0..n-1].
        for at, size in everywhere:
            self.assertTrue(caller_sp-stack.QUERY_FRAME_BYTES <= at and at+size <= caller_sp or
                            buffer <= at and at+size <= buffer+4*nodes, hex(at))
        return cpu.reg_read(arm.UC_ARM_REG_R0), writes, caller_sp-lowest[0]

    def test_query_writes_exactly_the_returned_prefix(self):
        for target in stack.QUERIES:
            for nodes in range(stack.CAPACITY_WORDS+1):
                with self.subTest(target=hex(target), nodes=nodes):
                    count, writes, depth = self.run_query(target, nodes)
                    self.assertEqual(count, nodes)
                    self.assertEqual(writes, [(4*k, 4, 0x03000000+k) for k in range(nodes)])
                    self.assertLessEqual(depth, stack.QUERY_FRAME_BYTES)

    def test_fourteen_nodes_overrun_a_thirteen_word_array(self):
        # The ROM imposes no cap: this is why n <= 13 is an explicit premise.
        count, writes, _ = self.run_query(Q, 14)
        self.assertEqual(count, 14)
        self.assertIn((52, 4, 0x0300000D), writes)


if __name__ == '__main__':
    unittest.main()
