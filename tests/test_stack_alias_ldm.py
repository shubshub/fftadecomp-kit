"""Synthetic Thumb CFGs for one exact stack-alias LDM word and writeback."""
import struct
import unittest
from types import SimpleNamespace

import match
from capstone.arm_const import ARM_CC_NE, ARM_REG_R8
from protected_descriptor_word_profile import ProtectedDescriptorWordProof

BASE = 0x08000000
R0, R1, R2, R3 = (match.ARM_REG_R0 + number for number in range(4))


def body(*words):
    return struct.pack('<' + 'H' * len(words), *words)


class RecordingWordProof(ProtectedDescriptorWordProof):
    """Observe a real caller transfer, then refuse instead of inventing effects."""

    def __init__(self):
        super().__init__(b'', b'[]', b'', b'{}')
        self.observed = None

    def check_call(self, address, aliases, stack, slots=None, **context):
        self.observed = (address, dict(aliases), dict(context['constants']))
        raise ValueError('synthetic call context captured without admission')


class StackAliasLdmTests(unittest.TestCase):
    def frame(self, middle, words=4, result=0x4708):
        # push{r4,r5,lr}; subsp; middle; addsp; pop{r4,r5}; pop{r1}; bxr1.
        return body(0xB530, 0xB080 | words, *middle,
                    0xB000 | words, 0xBC30, 0xBC02, result)

    def verify(self, code, proof=None, calls=None):
        return match.verify_leaf_instructions(code, BASE, True, calls,
                                             buffer_proof=proof)

    def instruction(self, encoded=0xC901):
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        return next(decoder.disasm(body(encoded), BASE))

    def test_exact_transfer_and_following_writeback_access(self):
        # Store the entry return, then an ordinary scalar. LDM must load the
        # return and advance r1 to the scalar, which replaces that provenance.
        code = self.frame([0x4670, 0x9000, 0x2007, 0x9001, 0x4669,
                           0xC900 | 1, 0x6808], result=0x4700)
        with self.assertRaisesRegex(ValueError, 'verified return|indirect control flow'):
            self.verify(code)
        instructions = self.verify(self.frame([0x2007, 0x9000, 0x4669,
                                               0xC901, 0x680A]))
        self.assertEqual(sum(item.mnemonic == 'ldm' for item in instructions), 1)

    def test_loaded_entry_return_is_preserved(self):
        self.verify(self.frame([0x4670, 0x9000, 0x4669, 0xC901], result=0x4700))
        # The saved LR is also an aligned in-frame word, with existing return
        # provenance; LDM must not manufacture this fact for other saved words.
        self.verify(self.frame([0xA903, 0xC901], words=1, result=0x4700))

    def test_scalar_load_kills_old_alias_and_return_facts(self):
        self.verify(self.frame([0x2007, 0x9000, 0x4669, 0x4668, 0xC901, 0x6010]))
        with self.assertRaisesRegex(ValueError, 'verified return|indirect control flow'):
            self.verify(self.frame([0x2007, 0x9000, 0x4670, 0x4669, 0xC901], result=0x4700))
        with self.assertRaisesRegex(ValueError, 'verified return|indirect control flow'):
            self.verify(self.frame([0x9003, 0xA903, 0xC901], words=1, result=0x4700))

    def test_misalignment_and_post_writeback_bounds_stay_rejected(self):
        with self.assertRaisesRegex(ValueError, 'unaligned'):
            self.verify(self.frame([0x4669, 0x3101, 0xC901]))
        with self.assertRaisesRegex(ValueError, 'outside the tracked frame'):
            self.verify(self.frame([0x4669, 0x3118, 0xC901, 0x680A]))
        for offset in (-32, -3, 0):
            with self.subTest(offset=offset), self.assertRaisesRegex(ValueError, 'unaligned|outside'):
                match.thumb_stack_alias_ldm(self.instruction(), {R1: offset}, 7)

    def test_loaded_pointer_word_cannot_escape_to_store_or_direct_call(self):
        # The existing non-word buffer route records this exact pointer slot.
        proof = match.BufferCallProof(b'', b'[]', stack_arguments=True)
        middle = [0x4668, 0x9000, 0x2000, 0x4669, 0xC901]
        with self.assertRaisesRegex(ValueError, 'stack-alias use or escape'):
            self.verify(self.frame(middle + [0x6010]), proof)
        # A synthetic direct BL targets0x08000100. No ROM or helper is read:
        # the captured alias must reach the existing target-identity refusal.
        with self.assertRaisesRegex(ValueError, 'unique aligned Thumb ROM code'):
            self.verify(self.frame(middle + [0xF000, 0xF877]), proof,
                        {BASE + 14: BASE + 0x100})

    def test_descriptor_pointer_word_is_restored_and_escape_refused(self):
        proof = RecordingWordProof()
        with self.assertRaisesRegex(ValueError, 'stack-alias use or escape'):
            self.verify(self.frame([0x4668, 0x9000, 0x2000, 0x4669,
                                    0xC901, 0x6010]), proof)

    def test_loaded_code_pointer_constant_reaches_real_call_state(self):
        # The aligned literal is an invented synthetic fixture value, not a
        # ROM-derived body. Protected word provenance must survive the LDM.
        middle = [0x4A05, 0x9200, 0x2200, 0x4669, 0xC904, 0xF000, 0xF877]
        code = self.frame(middle) + body(0, 0x0101, 0x0800)
        proof = RecordingWordProof()
        with self.assertRaisesRegex(ValueError, 'synthetic call context captured'):
            self.verify(code, proof, {BASE + 14: BASE + 0x100})
        self.assertEqual(proof.observed[2][R2], 0x08000101)

    def test_unknown_descriptor_word_fact_is_not_erased(self):
        proof = RecordingWordProof()
        # A partial write destroys the exact stored pointer fact. Reloading
        # the protected pointer slot must refuse instead of yielding a scalar.
        with self.assertRaisesRegex(ValueError, 'partial access|descriptor reload'):
            self.verify(self.frame([0x4668, 0x9000, 0x2100, 0x466A,
                                    0x7011, 0x4669, 0xC901]), proof)

    def test_lost_descriptor_word_fact_refuses_at_ldm(self):
        # An unknown destination write clears exact word facts without deleting
        # the separately protected pointer slot. LDM cannot turn it into scalar.
        with self.assertRaisesRegex(ValueError, 'descriptor LDM reload lacks'):
            self.verify(self.frame([0x4668, 0x9000, 0x2000, 0x601A,
                                    0x4669, 0xC901]), RecordingWordProof())

    def test_loaded_stack_pointer_cannot_escape_through_result(self):
        with self.assertRaisesRegex(ValueError, 'local stack pointer escapes'):
            self.verify(self.frame([0x4668, 0x9000, 0x2000, 0x4669,
                                    0xC901]), RecordingWordProof())

    def test_exact_encoding_and_unpredictable_forms_are_closed(self):
        instruction = self.instruction()
        self.assertEqual(match.thumb_stack_alias_ldm(instruction, {R1: -28}, 7),
                         (R1, -28, R0))
        self.assertIsNone(match.thumb_stack_alias_ldm(instruction, {}, 7))
        attributes = {name: getattr(instruction, name) for name in
                      ('mnemonic', 'operands', 'bytes', 'size', 'writeback', 'cc', 'regs_access')}
        mutations = [{'bytes': body(0xC901, 0)}, {'bytes': body(0xC900)},
                     {'bytes': body(0xC903)}, {'bytes': body(0xC902)},
                     {'bytes': body(0xCA01)}, {'bytes': body(0xC101)},
                     {'size': 4}, {'writeback': False}, {'cc': ARM_CC_NE},
                     {'mnemonic': 'ldmdb'},
                     {'regs_access': lambda: ([R1], [R0])},
                     {'regs_access': lambda: ([], [R1, R0])}]
        for mutation in mutations:
            with self.subTest(mutation=mutation), self.assertRaisesRegex(ValueError, 'LDM encoding'):
                match.thumb_stack_alias_ldm(SimpleNamespace(**{**attributes, **mutation}), {R1: -28}, 7)
        # An empty Thumb register list is not a decoded instruction. The raw
        # forged-encoding case above separately exercises the recognizer guard.
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        self.assertEqual(list(decoder.disasm(body(0xC900), BASE)), [])
        for encoded in (0xC903, 0xC902):
            with self.subTest(encoded=encoded), self.assertRaisesRegex(ValueError, 'LDM encoding'):
                match.thumb_stack_alias_ldm(self.instruction(encoded), {R1: -28}, 7)
        for name in ('shift', 'subtracted', 'reg'):
            operands = [SimpleNamespace(type=o.type, reg=o.reg,
                shift=SimpleNamespace(type=o.shift.type, value=o.shift.value),
                subtracted=o.subtracted) for o in attributes['operands']]
            if name == 'shift':
                operands[1].shift.value = 1
            elif name == 'reg':
                operands[1].reg = ARM_REG_R8
            else:
                operands[1].subtracted = True
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, 'LDM encoding'):
                match.thumb_stack_alias_ldm(SimpleNamespace(**{**attributes, 'operands': operands}), {R1: -28}, 7)
        for base in (match.ARM_REG_SP, match.ARM_REG_LR, match.ARM_REG_PC):
            operands = [SimpleNamespace(type=o.type, reg=o.reg,
                shift=SimpleNamespace(type=o.shift.type, value=o.shift.value),
                subtracted=o.subtracted) for o in attributes['operands']]
            operands[0].reg = base
            with self.subTest(base=base), self.assertRaisesRegex(ValueError, 'LDM encoding'):
                match.thumb_stack_alias_ldm(SimpleNamespace(**{**attributes, 'operands': operands}), {base: -28}, 7)

    def test_live_writeback_join_remains_rejected(self):
        # cmp r2,0; beq join; one arm advances r1; join reads r1.
        code = self.frame([0x4669, 0x2A00, 0xD000, 0xC901, 0x6808])
        with self.assertRaisesRegex(ValueError, 'inconsistent stack aliases'):
            self.verify(code)

    def test_live_r8_loop_remains_an_independent_refusal(self):
        # movr8,sp; loop:movr1,r8; r8=r1+4; r1-=4; ldmr1!,{r0};
        # scalarcounter--; bne loop. Immediate r8 use excludes the dead fix.
        code = self.frame([0x46E8, 0x4641, 0x3104, 0x4688, 0x3904,
                           0xC901, 0x3A01, 0xD1F8])
        with self.assertRaisesRegex(ValueError, 'inconsistent possible pointer offsets'):
            self.verify(code, match.BufferCallProof(b'', b'[]', stack_arguments=True))

    def test_existing_ldr_stm_and_ordinary_unknown_base_routes_remain(self):
        self.verify(self.frame([0x4669, 0xC101, 0x6808]))
        self.verify(self.frame([0xC901]))
        with self.assertRaisesRegex(ValueError, 'stack-alias use or escape'):
            self.verify(self.frame([0x4668, 0xC101]))


if __name__ == '__main__':
    unittest.main(verbosity=2)
