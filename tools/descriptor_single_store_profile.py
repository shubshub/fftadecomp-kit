"""One exact Thumb STMIA word with bounded stack provenance and writeback."""
import json

import match
import descriptor_output_alias_profile as output

SELECTOR = 'descriptor-single-store-v1'
SCHEMA = 'elf-symbol-thumb-descriptor-single-store-v1'
CONTROL_FLOW = 'complete Thumb owner with exact single-word stack STMIA and mandatory context/frame replay'
MAX_DEPENDENCIES = output.MAX_DEPENDENCIES
MAX_STACK_BYTES = output.MAX_STACK_BYTES


class _SingleStoreEffects:
    single_word_stores = True
    structural_stores = False

    def apply_single_store(self, instruction, aliases, constants, stack, words, *,
                           pointer_slots=None, root_frame=None, context=None):
        if not instruction.mnemonic.startswith('stm'):
            return False
        encoded = int.from_bytes(instruction.bytes, 'little')
        base = match.ARM_REG_R0 + ((encoded >> 8) & 7)
        stored = tuple(match.ARM_REG_R0 + bit for bit in range(8) if encoded & (1 << bit))
        operands = instruction.operands
        read, written = instruction.regs_access()
        if instruction.size != 2 or len(instruction.bytes) != 2 or encoded & 0xF800 != 0xC000 or \
                instruction.mnemonic != 'stm' or not instruction.writeback or \
                instruction.cc not in (match.ARM_CC_AL,match.ARM_CC_INVALID) or len(stored) != 1 or \
                base in stored or tuple(operand.reg for operand in operands) != (base,*stored) or \
                any(operand.type != match.ARM_OP_REG or operand.shift.type or operand.shift.value or
                    operand.subtracted for operand in operands) or set(read) != {base,*stored} or set(written) != {base}:
            raise ValueError('single-word STM requires one exact low register and excludes base-in-list')
        if base not in aliases:
            if not self.structural_stores:
                raise ValueError('single-word STM lacks an exact live stack base')
            # Structural frame inspection exports no memory or pointer identity.
            words.clear()
            if pointer_slots is not None:
                pointer_slots.clear()
            constants.pop(base,None)
            return True
        # Reuse the native encoding, exact bounds and writeback recognizer. The
        # stored pointer, if present, receives the existing full-word proof below.
        _, offset, registers = match.thumb_stack_alias_stm(instruction,{base:aliases[base]},len(stack))
        self.access(offset,4,stack)
        source = registers[0]
        value = None
        if source in aliases:
            self.access(aliases[source],1,stack)
            value = ('pointer',aliases[source])
        elif source in constants:
            value = ('constant',constants[source])
        before = {'aliases':[list(pair) for pair in sorted(aliases.items())],
                  'constants':[list(pair) for pair in sorted(constants.items())],
                  'words':[[slot,list(fact)] for slot,fact in sorted(words.items())]}
        for slot in tuple(words):
            if offset < slot+4 and offset+4 > slot:
                del words[slot]
        if value is not None:
            words[offset] = value
        if pointer_slots is not None:
            pointer_slots.pop(offset,None)
            if value is not None and value[0]=='pointer':
                pointer_slots[offset] = value[1]
        slot = (offset+4*len(stack))//4
        stack[slot] = (False,stack[slot][1],stack[slot][2])
        aliases[base] = offset+4
        constants.pop(base,None)
        if not self.structural_stores:
            row = {'site':instruction.address,'base_register':base,'source_register':source,
                'offset':offset,'writeback':offset+4,'stored_value':None if value is None else list(value),
                'root_frame':root_frame,'stack':[list(word) for word in stack], 'before':before,
                'after_words':[[slot,list(fact)] for slot,fact in sorted(words.items())],
                'context':context}
            self.single_stores[json.dumps(row,sort_keys=True)] = row
        return True


class _SingleStoreStructuralFrame(_SingleStoreEffects,output._StructuralFrameProof):
    structural_stores = True


class DescriptorSingleStoreProof(_SingleStoreEffects,output.DescriptorOutputAliasProof):
    structural_frame_type = _SingleStoreStructuralFrame

    def __init__(self,*args):
        super().__init__(*args)
        self.single_stores = {}

    def store_observations(self):
        return [self.single_stores[key] for key in sorted(self.single_stores)]
