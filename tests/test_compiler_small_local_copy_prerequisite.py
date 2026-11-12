import copy
import json
from pathlib import Path
import struct
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import compiler_small_local_copy_prerequisite as small
from test_local_shadow_halfword_matrix import fixture


def raw_run(body, values, destination=0x03007001, source=0x02001001):
    """Independent concrete decoding; no production paths or transitions used."""
    regs = [0x13570000+i for i in range(16)]
    regs[0], regs[1], regs[2], regs[13], regs[14] = destination, source, len(values), 0x03007000, 0x08012345
    initial = regs[:]
    memory = {source+i: value for i, value in enumerate(values)}
    memory.update({destination+i: 0xA5 for i in range(-1, len(values)+1)})
    reads, writes, trace = [], [], []
    pc, zero, carry, negative, overflow = 0, False, False, False, False

    def read(address, size):
        raw = [memory[address+i] for i in range(size)]
        reads.append([address, size, raw])
        return sum(value << (8*i) for i, value in enumerate(raw))

    def write(address, value, size):
        for i in range(size):
            memory[address+i] = (value >> (8*i)) & 255
            writes.append([address+i, memory[address+i]])

    for _ in range(256):
        trace.append(pc)
        word = struct.unpack_from('<H', body, pc)[0]
        following = pc+2
        if word == 0xB530:
            regs[13] -= 12
            for i, register in enumerate((4, 5, 14)):
                write(regs[13]+4*i, regs[register], 4)
        elif word in (0xBC30, 0xBC02):
            for register in ((4, 5) if word == 0xBC30 else (1,)):
                regs[register] = read(regs[13], 4)
                regs[13] += 4
        elif word == 0x4708:
            if regs[1] != initial[14]:
                raise AssertionError('return provenance differs')
            return regs, initial, memory, reads, writes, trace, (negative, zero, carry, overflow)
        elif word & 0xFE00 == 0x1C00:
            regs[word & 7] = regs[(word >> 3) & 7]
            negative, zero = bool(regs[word & 7] & 0x80000000), regs[word & 7] == 0
            carry, overflow = False, False
        elif word & 0xF800 == 0x2000:
            regs[(word >> 8) & 7] = word & 255
        elif word & 0xF800 == 0x2800:
            left, right = regs[(word >> 8) & 7], word & 255
            zero, carry = left == right, left >= right
        elif word & 0xFFC0 == 0x4280:
            left, right = regs[word & 7], regs[(word >> 3) & 7]
            zero, carry = left == right, left >= right
        elif word & 0xF800 in (0x3000, 0x3800):
            register = (word >> 8) & 7
            delta = (word & 255) * (1 if word & 0xF800 == 0x3000 else -1)
            regs[register] = (regs[register]+delta) & 0xFFFFFFFF
        elif word & 0xFFC0 == 0x4240:
            regs[word & 7] = -regs[(word >> 3) & 7] & 0xFFFFFFFF
        elif word & 0xF000 == 0xD000:
            condition, delta = (word >> 8) & 15, word & 255
            take = {0: zero, 1: not zero, 9: not carry or zero}[condition]
            if take:
                following = pc+4+2*(delta if delta < 128 else delta-256)
        elif word & 0xF800 in (0x7000, 0x7800):
            address = regs[(word >> 3) & 7]+((word >> 6) & 31)
            if word & 0xF800 == 0x7800:
                regs[word & 7] = read(address, 1)
            else:
                write(address, regs[word & 7], 1)
        else:
            raise AssertionError(f'Unexpected opcode {word:04X} at {pc}')
        pc = following
    raise AssertionError('raw execution exceeded bound')


class SmallCopyTests(unittest.TestCase):
    def prove(self, count=8, env=None, **kwargs):
        env = fixture() if env is None else env
        return small.verify_helper(env['helper'], env['rom'], env['mapping'], env['index'],
            count=count, selector=small.SELECTOR, **kwargs)

    def test_raw_opcodes_all_counts_values_and_unaligned_byte_addresses(self):
        env = fixture()
        body = env['rom'][env['helper']-0x08000000:env['helper']-0x08000000+98]
        for count in small.COUNTS:
            for values in (bytes(range(count)), bytes([255])*count,
                           bytes((i*37+19) & 255 for i in range(count))):
                for destination in (0x03007001, 0, 0x80000000):
                    with self.subTest(count=count, destination=destination, values=values):
                        proof = small.relation(values)
                        regs, initial, memory, reads, writes, trace, flags = raw_run(body, values, destination)
                        self.assertEqual([memory[destination+i] for i in range(count)], proof['destination_bytes'])
                        self.assertEqual(trace, proof['helper_instruction_offsets'])
                        source = initial[1]
                        self.assertEqual([[a-source, n, v] for a, n, v in reads if source <= a < source+count],
                                         proof['copy_reads'])
                        self.assertEqual([[a-destination, v] for a, v in writes if destination <= a < destination+count],
                                         proof['copy_writes'])
                        self.assertEqual(set(a for a, _ in writes),
                            set(range(destination, destination+count)) | set(range(initial[13]-12, initial[13])))
                        self.assertEqual([regs[i] for i in (0, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14)],
                                         [initial[i] for i in (0, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14)])
                        self.assertEqual(regs[1:4], [initial[14], 0xFFFFFFFF, source+count])
                        self.assertEqual(flags, (bool(destination & 0x80000000), destination == 0, False, False))
                        self.assertEqual(bytes(memory[source+i] for i in range(count)), values)
                        self.assertEqual((memory[destination-1], memory[destination+count]), (0xA5, 0xA5))

    def test_authenticated_counts_and_manifest_replay(self):
        for count in small.COUNTS:
            result = self.prove(count)
            self.assertEqual(self.prove(count, manifest=json.loads(json.dumps(result))), result)
            self.assertEqual(result['instructions'], 49)
            self.assertEqual(result['relation']['byte_iterations'], count)
            self.assertEqual(result['relation']['copy_words'], 0)
            self.assertIn('compiler_small_local_copy_prerequisite.py', result['producer_sha256'])
            for key in ('source_or_ELF_admission', 'actual_copy_invocation_proved', 'caller_arguments_proved'):
                self.assertFalse(result[key])

    def test_opaque_values_and_invalid_sources(self):
        values = tuple(f'unknown{i}' for i in range(10))
        self.assertEqual(small.relation(values)['destination_bytes'], list(values))
        for values in (bytes(3), [0]*4, (True, 0), (0, 256), (0, ''), (None, 0)):
            with self.subTest(values=values), self.assertRaises(ValueError):
                small.relation(values)

    def test_unsupported_count_and_policy(self):
        for count in (True, 0, 1, 3, 15, 16, 80, 8.0):
            with self.subTest(count=count), self.assertRaises(ValueError):
                self.prove(count)
        env = fixture()
        with self.assertRaises(ValueError):
            small.verify_helper(env['helper'], env['rom'], env['mapping'], env['index'], count=8, selector='ordinary')

    def test_wrong_helper_bytes_including_unexecuted_path(self):
        for offset in (20, 76, 78, 84, 94, 96):
            env = fixture(); raw = bytearray(env['rom'])
            raw[env['helper']-0x08000000+offset] ^= 1
            env['rom'] = bytes(raw)
            with self.subTest(offset=offset), self.assertRaises(ValueError):
                self.prove(env=env)

    def test_wrong_indexes_and_duplicate_owner(self):
        for kind in ('count', 'extent', 'duplicate', 'text'):
            env = fixture(); rows = json.loads(env['mapping'])
            if kind == 'count': rows[1]['instrs'] = 48
            elif kind == 'extent': rows[1]['end'] = f"0x{env['helper']+96:08X}"
            elif kind == 'duplicate': rows.append(rows[1])
            else: env['index'] = env['index'].replace(b'98 49', b'98 48')
            env['mapping'] = json.dumps(rows).encode()
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                self.prove(env=env)

    def test_stale_results_producers_and_inputs(self):
        result = self.prove()
        for key in ('producer_sha256', 'input_pins', 'relation', 'conditions'):
            changed = copy.deepcopy(result); changed[key] = {}
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.prove(manifest=changed)
        env = fixture(); raw = bytearray(env['rom']); raw[0] ^= 1; env['rom'] = bytes(raw)
        with self.assertRaises(ValueError): self.prove(env=env, manifest=result)
        with self.assertRaises(ValueError): self.prove(10, manifest=result)

    def domain(self, **changes):
        args = dict(count=8, helper_sp=0x03007000, source=0x02001001,
            destination=0x03007001, destination_window=(0x03007000, 16),
            caller_code=(0x08001000, 128), helper_code=(0x08000400, 98))
        args.update(changes)
        return small.concrete_domain(**args)

    def test_caller_local_window_is_supplied_not_authenticated(self):
        result = self.domain()
        self.assertEqual(result['regions']['helper_frame'], (0x03007000-12, 12))
        self.assertFalse(result['caller_window_authenticated'])
        self.assertFalse(result['physical_access_granted'])

    def test_bad_domains_and_protected_saves(self):
        for changes in ({'helper_sp': 0x03007002}, {'helper_sp': 8}, {'source': True},
                {'source': 0xFFFFFFFC}, {'source': 0x03007003}, {'source': 0x03006FF8},
                {'source': 0x08001000}, {'source': 0x08000401},
                {'destination': 0x03006FFC, 'destination_window': (0x03006FFC, 16)},
                {'destination_window': (0x03007002, 16)}, {'destination_window': (0x03007000, 8)},
                {'destination_window': (0xFFFFFFFC, 16)}, {'helper_code': (0x08000400, 96)},
                {'caller_code': (0x08000402, 128)}, {'caller_code': (0x08001001, 128)},
                {'destination': 0xFFFFFFFC, 'destination_window': (0xFFFFFFF0, 16)}):
            with self.subTest(changes=changes), self.assertRaises(ValueError): self.domain(**changes)


if __name__ == '__main__':
    unittest.main()
