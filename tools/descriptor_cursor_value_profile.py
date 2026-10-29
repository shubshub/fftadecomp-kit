"""Exact stack cursor values carry no permission to access the pointed-to word."""
import json

import match
import descriptor_callee_constant_profile as constant

SELECTOR = 'descriptor-cursor-value-v1'
SCHEMA = 'elf-symbol-thumb-descriptor-cursor-value-v1'
CONTROL_FLOW = 'complete Thumb owner with exact bounded cursor values and independent memory access proofs'
MAX_DEPENDENCIES = constant.MAX_DEPENDENCIES
MAX_STACK_BYTES = constant.MAX_STACK_BYTES
MAX_PATH_STATES = constant.MAX_PATH_STATES


class _CursorValues:
    def validate_pointer_value(self, offset, stack):
        # The exact entry-SP-relative address may denote a saved slot or the
        # frame's upper boundary. This is only a bounded value, not an object
        # extent or permission to read or write. Popped-frame values still fail.
        if type(offset) is not int or len(stack)*4 > MAX_STACK_BYTES or not -4*len(stack) <= offset <= 0:
            raise ValueError('cursor value leaves the exact bounded live stack extent')

    def word_memory(self, instruction, aliases, constants, stack, words, sp_offset, protected, **kwargs):
        # The native caller engine also handles saved-register loads. An alias
        # recovered as a cursor must never use that path to access saved words.
        widths = {'ldr':4, 'str':4, 'ldrb':1, 'strb':1, 'ldrh':2, 'strh':2,
                  'ldrsb':1, 'ldrsh':2}
        width = widths.get(instruction.mnemonic)
        for operand in instruction.operands:
            if operand.type == match.ARM_OP_MEM and operand.mem.base in aliases and width is not None:
                memory = operand.mem
                if not memory.index or memory.index in constants:
                    offset = aliases[memory.base]+memory.disp+(constants[memory.index] if memory.index else 0)
                    self.access(offset,width,stack)
        return super().word_memory(instruction,aliases,constants,stack,words,sp_offset,protected,**kwargs)


class _CursorStructuralFrame(_CursorValues, constant.DescriptorCalleeConstantProof.structural_frame_type):
    pass


class DescriptorCursorValueProof(_CursorValues, constant.DescriptorCalleeConstantProof):
    structural_frame_type = _CursorStructuralFrame

    def __init__(self, *args):
        super().__init__(*args)
        self.cursor_values = {}

    def word_memory(self, instruction, aliases, constants, stack, words, sp_offset, protected, **kwargs):
        before = tuple(sorted(words.items()))
        result = super().word_memory(instruction,aliases,constants,stack,words,sp_offset,protected,**kwargs)
        loaded,_,_,stored = result
        register = instruction.operands[0].reg if instruction.operands and \
            instruction.operands[0].type == match.ARM_OP_REG else None
        value = aliases[register] if stored else loaded[1] if loaded is not None else None
        if value is not None:
            try:
                self.access(value,1,stack)
                local = True
            except ValueError:
                local = False
            row = {'site':instruction.address, 'operation':'store' if stored else 'reload',
                'register':register, 'value':value, 'pointee_is_local':local,
                'sp_offset':sp_offset, 'root_frame':kwargs.get('root_frame'),
                'aliases':sorted(aliases.items()), 'constants':sorted(constants.items()),
                'stack':list(stack), 'before_words':before, 'after_words':sorted(words.items()),
                'protected':sorted(protected)}
            self.cursor_values[json.dumps(row,sort_keys=True)] = row
        return result

    def cursor_observations(self):
        return {'schema':'exact-stack-cursor-values-v1',
                'access':'every actual memory access independently requires allocated local words',
                'transfers':[self.cursor_values[key] for key in sorted(self.cursor_values)]}
