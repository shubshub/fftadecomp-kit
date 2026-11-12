"""All-path manager provenance with independent raw branch execution."""
from pathlib import Path
import json
import struct
import subprocess
import sys
import unittest
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import owner_admission_profile as owner
import scheduler_entry_profile as entry
import scheduler_manager_offset_profile as previous
import scheduler_manager_paths_profile as profile
from test_scheduler_entry import bound
from test_scheduler_manager_offset import caller as straight
from test_scheduler_predicates import A, half, bl

POINT = 0x02004000


def caller(*, poison=None, skip=False, diamond=False, frame=8, descriptor=1,
           parent=0x9200, extra=()):
    words = [0xB500, 0xB080 + frame, 0xAB00 + descriptor]
    literals = []

    def literal():
        literals.append(len(words))
        words.append(0x4800)

    if diamond:
        literal()
    words.extend([0x2900, 0])  # cmp r1,#0; beq right
    conditional = len(words) - 1
    if not diamond:
        literal()
    words.extend([0x6800, 0x6880] if not diamond else [0x6800])
    branch = len(words)
    words.append(0)
    right = len(words)
    if not diamond:
        literal()
    if not skip:
        words.append(0x6800)
    if not diamond:
        words.append(0x68C0 if poison is None else poison)
    elif poison is not None:
        words.append(poison)
    join = len(words)
    if diamond:
        words.append(0x6880)
    words.extend([0x2200, parent, 0x2228, *extra])
    site = A + len(words)*2
    words[conditional] = 0xD000 | (right - conditional - 2) & 255
    words[branch] = 0xE000 | (join - branch - 2) & 2047
    data = half(*words) + bl(site, entry.DIRECT) + half(0xB000 + frame, 0xBC02, 0x4708)
    data += bytes((-len(data)) % 4)
    offsets = []
    for i, location in enumerate(literals):
        offset = len(data)
        offsets.append(offset)
        instruction = 0x4800 | ((A + offset - ((A + location*2 + 4) & ~3)) // 4)
        data = data[:location*2] + half(instruction) + data[location*2+2:]
        data += struct.pack('<I', POINT + i*4)
    return data, {site: entry.DIRECT}, offsets


def verified(**kwargs):
    data, calls, offsets = caller(**kwargs)
    proof = bound(data, calls, policy=profile.SELECTOR)
    match.verify_leaf_instructions(data, A, True, calls, buffer_proof=proof)
    return proof, data, calls, offsets


def raw(data, memory, argument):
    """Small independent decoder; no Capstone, CFG or profile helpers."""
    regs = [0] * 16
    regs[1], regs[13] = argument, 0x03007F00
    pc, equal, reads = 0, False, []
    for _ in range(128):
        word = int.from_bytes(data[pc:pc+2], 'little')
        if word & 0xF800 == 0xF000:
            return regs, reads, A + pc
        next_pc = pc + 2
        if word == 0xB500:
            regs[13] -= 4
        elif word & 0xFF80 == 0xB080:
            regs[13] -= (word & 127)*4
        elif word & 0xF800 == 0xA800:
            regs[(word >> 8) & 7] = regs[13] + (word & 255)*4
        elif word & 0xF800 == 0x4800:
            location = ((A + pc + 4) & ~3) + (word & 255)*4
            regs[(word >> 8) & 7] = int.from_bytes(data[location-A:location-A+4], 'little')
        elif word & 0xF800 == 0x6800:
            destination, base = word & 7, (word >> 3) & 7
            location = regs[base] + ((word >> 6) & 31)*4
            reads.append((A + pc, location))
            regs[destination] = memory[location]
        elif word & 0xF800 == 0x2800:
            equal = regs[(word >> 8) & 7] == (word & 255)
        elif word & 0xFF00 == 0xD000:
            if equal:
                displacement = word & 255
                next_pc = pc + 4 + (displacement if displacement < 128 else displacement-256)*2
        elif word & 0xF800 == 0xE000:
            displacement = word & 2047
            next_pc = pc + 4 + (displacement if displacement < 1024 else displacement-2048)*2
        elif word & 0xF800 == 0x2000:
            regs[(word >> 8) & 7] = word & 255
        elif word & 0xF800 == 0x9000:
            memory[regs[13] + (word & 255)*4] = regs[(word >> 8) & 7]
        else:
            raise AssertionError(hex(word))
        pc = next_pc
    raise AssertionError('raw fixture execution budget')


class ManagerPathsTests(unittest.TestCase):
    def test_branch_and_diamond_all_paths_agree_with_raw_execution(self):
        for diamond in (False, True):
            proof, data, calls, offsets = verified(diamond=diamond)
            report = proof.contract_manifest()
            self.assertEqual(report['entry']['entry_to_call_paths'], 2)
            self.assertEqual(len(report['entry']['manager_paths']), 2)
            for argument in (0, 1):
                memory = {POINT: 0x02005000, POINT+4: 0x02006000,
                          0x02005008: 0x02007000, 0x0200600C: 0x02008000}
                regs, reads, site = raw(data, memory, argument)
                expected = 0x02007000 if diamond or argument else 0x02008000
                self.assertEqual(regs[0], expected)
                self.assertEqual(site, next(iter(calls)))
                chain = next(chain for chain in report['entry']['manager_paths']
                             if chain['pointer_load_site'] == reads[0][0])
                self.assertEqual(chain['dereference_site'], reads[1][0])
                self.assertEqual(chain['field_offset'], 8 if diamond or argument else 12)
            self.assertEqual(report['schema'], profile.SCHEMA)
            self.assertFalse(report['manager_memory_access_proved'])
            self.assertFalse(report['manager_values_equal_across_paths_proved'])
            for phrase in ('ordered loads', 'without address wraparound', 'both storage words',
                           'ambient original R9', 'initialization is not checked'):
                self.assertIn(phrase, ' '.join(report['assumptions']))

    def test_straight_line_register_changes_remain_supported(self):
        for registers in ((0, 0), (1, 2), (4, 5)):
            data, calls, _ = straight(literal_reg=registers[0], pointer_reg=registers[1])
            proof = bound(data, calls, policy=profile.SELECTOR)
            match.verify_leaf_instructions(data, A, True, calls, buffer_proof=proof)
            self.assertEqual(len(proof.contract_manifest()['entry']['manager_paths']), 1)

    def test_previous_selector_still_rejects_join(self):
        data, calls, _ = caller()
        with self.assertRaisesRegex(ValueError, 'straight-line'):
            bound(data, calls, policy=previous.SELECTOR)

    def test_every_poisoned_path_is_rejected(self):
        for poison in (0x2000, 0x7800, 0x8800, 0x5800, 0x6888):
            with self.subTest(poison=poison), self.assertRaises(ValueError):
                verified(poison=poison)
        with self.assertRaises(ValueError):
            verified(skip=True)

    def test_overwrites_and_calls_are_rejected(self):
        for extra in ((0x2000,), (0xF000, 0xF800)):
            with self.subTest(extra=extra), self.assertRaises(ValueError):
                verified(extra=extra)

    def test_uninitialized_registers_are_rejected(self):
        for options in ({'before_pointer': (0x2100,)}, {'before_final': (0x2200,)},
                        {'last': 0x6888}, {'before_call': (0x2000,)}):
            data, calls, _ = straight(**options)
            with self.subTest(options=options), self.assertRaises(ValueError):
                bound(data, calls, policy=profile.SELECTOR)

    def test_every_literal_needs_unique_zero_addend_binding(self):
        proof, _, _, offsets = verified()
        report = proof.contract_manifest()
        rows = [[offset, 'data_' + format(POINT + i*4, '08X'), 0]
                for i, offset in enumerate(offsets)]
        profile.check_bindings(report, {'data': rows})
        for bad in (rows[:-1], rows + [rows[0]], [[offsets[0], 'data_02004000', 4], rows[1]],
                    [[offsets[0]+4, 'data_02004000', 0], rows[1]]):
            with self.subTest(rows=bad), self.assertRaises(ValueError):
                profile.check_bindings(report, {'data': bad})

    def test_forged_literal_identity_is_rejected_by_typed_owner_binding(self):
        proof, data, _, offsets = verified()
        rows = [[offset, 'data_' + format(POINT + i*4, '08X'), 0]
                for i, offset in enumerate(offsets)]
        mapping = json.dumps([dict(rom=hex(A), end=hex(A+len(data)), mode='thumb')]).encode()
        rom = bytes(A-match.ROM_BASE) + data
        objects = json.dumps({'data_02004000': '0x%08X' % POINT,
                              'data_02004004': '0x%08X' % (POINT+4),
                              'data_02004008': '0x%08X' % (POINT+8)}).encode()
        manifest = dict(calls=[], data=rows, functions=[])
        match.function_address_bindings(data, A, rom, mapping, objects, manifest,
                                        allow_empty_functions=True)
        for name in ('data_02004008', 'data_0200400C'):
            bad = dict(manifest, data=[rows[0], [offsets[1], name, 0]])
            # The shape-only path contract and the typed byte binding are both
            # required by owner.verify; shape alone cannot authenticate identity.
            profile.check_bindings(proof.contract_manifest(), bad)
            with self.subTest(name=name), self.assertRaises(ValueError):
                match.function_address_bindings(data, A, rom, mapping, objects, bad,
                                                allow_empty_functions=True)

    def test_frames_descriptor_and_parent_remain_checked(self):
        for options in ({'frame': 7}, {'descriptor': 0}, {'parent': 0x9300},
                        {'extra': (0x1C19,)}):
            with self.subTest(options=options), self.assertRaises(ValueError):
                verified(**options)

    def test_dependency_identity_and_only_one_pinned_call(self):
        data, calls, _ = caller()
        with self.assertRaisesRegex(ValueError, 'dependency identity'):
            bound(data, calls, policy=profile.SELECTOR, pins={entry.DIRECT: (206, '0'*64)})
        for calls in ({}, {A: entry.POOL}, {A: entry.DIRECT, A+4: entry.DIRECT}):
            with self.assertRaises(ValueError):
                profile.bind(b'', A, {}, {}, calls)

    def test_cycle_missing_entry_and_budgets_fail_closed(self):
        data, calls, _ = caller()
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        # A tiny caller using actual decoded nodes, but adversarial CFG inputs.
        nodes = {instruction.address: instruction for instruction in decoder.disasm(data[:10], A)}
        site = max(nodes)
        edges = {A: [A+2], A+2: [A+4], A+4: [site], site: []}
        cyclic = {**edges, A+4: [A+2, site]}
        missing = {**edges, A: []}
        for graph in (cyclic, missing):
            with self.assertRaises(ValueError):
                profile.bind(data, A, nodes, graph, {site: entry.DIRECT})
        with mock.patch.object(profile, 'MAX_STEPS', 1), self.assertRaisesRegex(ValueError, 'budget'):
            bound(data, calls, policy=profile.SELECTOR)
        with mock.patch.object(profile, 'MAX_PATHS', 1), self.assertRaisesRegex(ValueError, 'budget'):
            bound(data, calls, policy=profile.SELECTOR)
        with mock.patch.object(profile, 'MAX_DEPTH', 1), self.assertRaisesRegex(ValueError, 'budget'):
            bound(data, calls, policy=profile.SELECTOR)

    def test_selector_registered_in_owner_and_cli(self):
        self.assertIn(profile.SELECTOR, owner.named_buffer.SELECTORS)
        self.assertEqual(owner.selector_for_report('* verification: `' + profile.SCHEMA + '`'), profile.SELECTOR)
        run = subprocess.run([sys.executable, '-B', str(Path(match.__file__)),
                              '--owner-runtime-profile', profile.SELECTOR, '--help'], capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stderr)


if __name__ == '__main__':
    unittest.main()
