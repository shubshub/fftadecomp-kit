"""An opaque store cannot erase a pointer obligation before its reload."""
import json
from pathlib import Path
import struct
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import descriptor_output_alias_profile as profile
import owner_admission_profile as owner

A, H = 0x08000100, 0x08000200


def fixture(helper):
    """One exact Thumb caller passes its second allocated word in R0."""
    delta = H - (A + 6) - 4
    call = struct.pack('<HH', 0xf000 | ((delta >> 12) & 0x7ff),
                       0xf800 | ((delta >> 1) & 0x7ff))
    root = bytes.fromhex('00b582b001a8') + call + bytes.fromhex('019802b002bc0847')
    bodies = {A: root, H: helper}
    rom = bytearray(0x400)
    rows = []
    for address, body in bodies.items():
        rom[address-match.ROM_BASE:address-match.ROM_BASE+len(body)] = body
        rows.append(dict(rom=f'0x{address:08X}', end=f'0x{address+len(body):08X}',
                         mode='thumb', instrs=0))
    mapping = json.dumps(rows).encode()
    for row in rows:
        address = int(row['rom'], 16)
        row['instrs'] = owner.refine(bodies[address], address, mapping)['instrs']
    mapping = json.dumps(rows).encode()
    index = ''.join(f'{int(r["rom"],16):08X} {int(r["end"],16):08X} '
                    f'{int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n'
                    for r in rows).encode()
    return root, bytes(rom), mapping, index


class PointerFactLossTests(unittest.TestCase):
    def test_unknown_store_cannot_forget_spilled_output_pointer(self):
        # push; allocate; spill R0; opaque STR; reload R2; write output;
        # deallocate and return with the pointer still in R2.
        helper = bytes.fromhex('10b581b000901a60009a01211160002001b010bc02bc0847')
        data, rom, mapping, index = fixture(helper)
        proof = profile.DescriptorOutputAliasProof(rom, mapping, index, b'{}')
        with self.assertRaisesRegex(ValueError, 'unknown store.*pointer'):
            match.verify_leaf_instructions(data, A, True, {A+6:H}, buffer_proof=proof)

    def test_partial_bounded_store_cannot_forget_spilled_pointer(self):
        for store in ('1970', '1980'):  # STRB/STRH R1,[R3], R3 = SP
            helper = bytes.fromhex('10b581b000906b460121' + store +
                                   '0023009a1160002001b010bc02bc0847')
            data, rom, mapping, index = fixture(helper)
            proof = profile.DescriptorOutputAliasProof(rom, mapping, index, b'{}')
            with self.subTest(store=store), self.assertRaisesRegex(ValueError, 'partial.*pointer'):
                match.verify_leaf_instructions(data, A, True, {A+6:H}, buffer_proof=proof)

    def test_unaligned_word_store_cannot_forget_pointer(self):
        helper = bytes.fromhex('10b582b000906b460133012119600023009a1160002002b010bc02bc0847')
        data, rom, mapping, index = fixture(helper)
        proof = profile.DescriptorOutputAliasProof(rom, mapping, index, b'{}')
        with self.assertRaisesRegex(ValueError, 'partial.*pointer'):
            match.verify_leaf_instructions(data, A, True, {A+6:H}, buffer_proof=proof)

    def test_unrelated_bounded_byte_store_remains_allowed(self):
        helper = bytes.fromhex('10b582b000906b46012119710020002302b010bc02bc0847')
        data, rom, mapping, index = fixture(helper)
        proof = profile.DescriptorOutputAliasProof(rom, mapping, index, b'{}')
        self.assertTrue(match.verify_leaf_instructions(data, A, True, {A+6:H}, buffer_proof=proof))

    def test_complete_aligned_scalar_overwrite_remains_allowed(self):
        helper = bytes.fromhex('10b581b000906b46012119600023009a1160002001b010bc02bc0847')
        data, rom, mapping, index = fixture(helper)
        proof = profile.DescriptorOutputAliasProof(rom, mapping, index, b'{}')
        self.assertTrue(match.verify_leaf_instructions(data, A, True, {A+6:H}, buffer_proof=proof))

    def test_unknown_indexed_store_cannot_forget_pointer(self):
        # STR R1,[R3,R2], with R3 = SP and unknown R2.
        helper = bytes.fromhex('10b581b000906b4699500023009a1160002001b010bc02bc0847')
        data, rom, mapping, index = fixture(helper)
        proof = profile.DescriptorOutputAliasProof(rom, mapping, index, b'{}')
        with self.assertRaisesRegex(ValueError, 'unknown store.*pointer'):
            match.verify_leaf_instructions(data, A, True, {A+6:H}, buffer_proof=proof)

    def test_unknown_store_without_pointer_word_keeps_scalar_behavior(self):
        helper = bytes.fromhex('10b500211a600160002010bc02bc0847')
        data, rom, mapping, index = fixture(helper)
        proof = profile.DescriptorOutputAliasProof(rom, mapping, index, b'{}')
        self.assertTrue(match.verify_leaf_instructions(data, A, True, {A+6:H}, buffer_proof=proof))


if __name__ == '__main__':
    unittest.main()
