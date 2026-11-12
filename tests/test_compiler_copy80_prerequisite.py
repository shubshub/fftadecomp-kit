import json
from pathlib import Path
import struct
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import compiler_copy80_prerequisite as copy80
from test_local_shadow_halfword_matrix import fixture


def helper_inputs():
    env = fixture()
    return env['helper'], env['rom'], env['mapping'], env['index']


def raw_helper(body, source_bytes, destination=0x02001000, source=0x03000940):
    """Independent raw Thumb execution for the exact helper's aligned path."""
    regs = [0x13570000 + i for i in range(16)]
    regs[0], regs[1], regs[2], regs[13], regs[14] = destination, source, 80, 0x03007000, 0x08012345
    initial = regs[:]
    memory = {source+i: value for i, value in enumerate(source_bytes)}
    memory.update({destination+i: 0xA5 for i in range(-4, 84)})
    writes, trace = [], []
    pc, zero, carry, negative, overflow = 0, False, False, False, False

    def read(address):
        return sum(memory[address+i] << (8*i) for i in range(4))

    def write(address, value):
        for i in range(4):
            memory[address+i] = (value >> (8*i)) & 255
            writes.append(address+i)

    for _ in range(128):
        trace.append(pc)
        word = struct.unpack_from('<H', body, pc)[0]
        following = pc + 2
        if word == 0xB530:
            regs[13] -= 12
            for i, register in enumerate((4, 5, 14)):
                write(regs[13]+4*i, regs[register])
        elif word in (0xBC30, 0xBC02):
            for register in ((4, 5) if word == 0xBC30 else (1,)):
                regs[register] = read(regs[13])
                regs[13] += 4
        elif word == 0x4708:
            assert regs[1] == initial[14]
            return regs, initial, memory, writes, trace, dict(N=negative, Z=zero, C=carry, V=overflow)
        elif word & 0xFE00 == 0x1C00:
            regs[word & 7] = regs[(word >> 3) & 7]
            negative, zero = bool(regs[word & 7] & 0x80000000), regs[word & 7] == 0
            carry, overflow = False, False
        elif word & 0xF800 == 0x2000:
            regs[(word >> 8) & 7] = word & 255
        elif word & 0xFFC0 in (0x4000, 0x4300):
            d, s = word & 7, (word >> 3) & 7
            regs[d] = regs[d] & regs[s] if word & 0xFFC0 == 0x4000 else regs[d] | regs[s]
        elif word & 0xF800 == 0x2800:
            left, right = regs[(word >> 8) & 7], word & 255
            zero, carry = left == right, left >= right
        elif word & 0xFFC0 == 0x4280:
            left, right = regs[word & 7], regs[(word >> 3) & 7]
            zero, carry = left == right, left >= right
        elif word & 0xF800 == 0x3800:
            r = (word >> 8) & 7
            regs[r] = (regs[r] - (word & 255)) & 0xFFFFFFFF
        elif word & 0xFFC0 == 0x4240:
            regs[word & 7] = -regs[(word >> 3) & 7] & 0xFFFFFFFF
        elif word & 0xF000 == 0xD000:
            condition = (word >> 8) & 15
            take = {0: zero, 1: not zero, 8: carry and not zero, 9: not carry or zero}[condition]
            delta = word & 255
            if take:
                following = pc + 4 + 2*(delta if delta < 128 else delta-256)
        elif word in (0xCB01, 0xC101):
            if word == 0xCB01:
                regs[0] = read(regs[3])
                regs[3] += 4
            else:
                write(regs[1], regs[0])
                regs[1] += 4
        else:
            raise AssertionError(f'Unexpected helper opcode {word:04X} at {pc}')
        pc = following
    raise AssertionError('Helper execution exceeded instruction bound')


class Copy80Tests(unittest.TestCase):
    def test_complete_helper_identity(self):
        result = copy80.verify_helper(*helper_inputs())
        self.assertEqual(result['instructions'], 49)
        self.assertEqual(result['partition']['code_bytes'], 98)
        self.assertFalse(result['source_or_ELF_admission'])
        self.assertFalse(result['caller_arguments_proved'])

    def test_changed_helper_byte_refused(self):
        address, rom, mapping, index = helper_inputs()
        changed = bytearray(rom)
        changed[address-0x08000000+42] ^= 1
        with self.assertRaises(ValueError):
            copy80.verify_helper(address, bytes(changed), mapping, index)

    def test_both_counts_required(self):
        address, rom, mapping, index = helper_inputs()
        rows = json.loads(mapping)
        rows[1]['instrs'] = 48
        with self.assertRaises(ValueError):
            copy80.verify_helper(address, rom, json.dumps(rows).encode(), index)
        with self.assertRaises(ValueError):
            copy80.verify_helper(address, rom, mapping, index.replace(b'98 49', b'98 48'))

    def test_wrong_extent_and_duplicate_owner_refused(self):
        address, rom, mapping, index = helper_inputs()
        rows = json.loads(mapping)
        for changed in (rows + [rows[1]], [rows[0], dict(rows[1], end=f'0x{address+96:08X}')]):
            with self.assertRaises(ValueError):
                copy80.verify_helper(address, rom, json.dumps(changed).encode(), index)

    def test_relocated_helper_identity(self):
        env = fixture(helper=0x08000800)
        result = copy80.verify_helper(env['helper'], env['rom'], env['mapping'], env['index'])
        self.assertEqual(result['helper'], 0x08000800)

    def test_malformed_inputs_refused(self):
        address, rom, mapping, index = helper_inputs()
        with self.assertRaises(ValueError):
            copy80.verify_helper(address, None, mapping, index)
        with self.assertRaises(ValueError):
            copy80.verify_helper(True, rom, mapping, index)
        with self.assertRaises(ValueError):
            copy80.verify_helper(address, rom, mapping.replace(b'"instrs": 49', b'"instrs": 49, "instrs": 49'), index)

    def test_opaque_bytes_remain_opaque(self):
        values = tuple(f'unknown_{i}' for i in range(80))
        result = copy80.relation(values)
        self.assertEqual(result['destination_bytes'], list(values))
        self.assertEqual(result['copy_words'], 20)
        self.assertEqual(len(result['copy_writes']), 80)
        self.assertEqual(result['final_registers']['r2'], 0xFFFFFFFF)
        self.assertFalse(result['physical_access_proved'])

    def test_raw_opcodes_agree_on_complete_copy_and_saves(self):
        address, rom, _, _ = helper_inputs()
        body = rom[address-0x08000000:address-0x08000000+98]
        for values in (bytes(range(80)), bytes([0xFF])*80, bytes((i*37+19) & 255 for i in range(80))):
            relation = copy80.relation(values)
            regs, initial, memory, writes, trace, flags = raw_helper(body, values)
            self.assertEqual(bytes(memory[initial[0]+i] for i in range(80)), bytes(relation['destination_bytes']))
            self.assertEqual([regs[i] for i in (0, 4, 5, 13)], [initial[i] for i in (0, 4, 5, 13)])
            self.assertEqual(regs[1], initial[14])
            self.assertEqual(regs[2], 0xFFFFFFFF)
            self.assertEqual(regs[3], initial[1]+80)
            self.assertEqual(trace, relation['helper_instruction_offsets'])
            self.assertEqual(set(writes), set(range(initial[0], initial[0]+80)) | set(range(initial[13]-12, initial[13])))
            self.assertTrue(all(memory[initial[0]+i] == 0xA5 for i in (*range(-4, 0), *range(80, 84))))
            self.assertEqual(bytes(memory[initial[1]+i] for i in range(80)), values)
            self.assertEqual(flags, dict(N=False, Z=False, C=False, V=False))

    def test_final_flags_for_zero_and_high_destination(self):
        address, rom, _, _ = helper_inputs()
        body = rom[address-0x08000000:address-0x08000000+98]
        for destination in (0, 0x80000000):
            *_, flags = raw_helper(body, bytes(80), destination=destination)
            self.assertEqual(flags, dict(N=bool(destination & 0x80000000),
                Z=destination == 0, C=False, V=False))

    def test_exact_byte_domain(self):
        for values in (bytes(79), bytes(81), tuple([True]*80), tuple([256]*80), tuple([None]*80)):
            with self.assertRaises(ValueError):
                copy80.relation(values)

    def domain(self, **changes):
        values = dict(entry_sp=0x03007000, source=0x03000940, destination=0x02001064,
                      caller_frame_bytes=60, caller_code=(0x08125A5C, 908), helper_code=(0x081443FC, 98))
        values.update(changes)
        return copy80.concrete_domain(**values)

    def test_domain_is_conditions_not_permission(self):
        result = self.domain()
        self.assertEqual(result['combined_frame'], [0x03007000-72, 0x03007000])
        self.assertFalse(result['physical_access_granted'])
        self.assertFalse(result['caller_arguments_proved'])

    def test_bad_numeric_domains_refused(self):
        for changes in ({'entry_sp': 8}, {'entry_sp': 0x03007002}, {'source': 0x03000941},
                        {'destination': 0xFFFFFFF0}, {'destination': 0x03000944},
                        {'source': 0xFFFFFFB0}, {'destination': 0xFFFFFFB0},
                        {'source': 0x03006FC0}, {'destination': 0x03006FB8},
                        {'destination': 0x081443FC}, {'source': 0x08125A5C},
                        {'caller_frame_bytes': -4}, {'caller_frame_bytes': True},
                        {'caller_code': (0xFFFFFFFC, 8)}, {'helper_code': (0x081443FC, 96)}):
            with self.subTest(changes=changes), self.assertRaises(ValueError):
                self.domain(**changes)


if __name__ == '__main__':
    unittest.main()
