"""Exact register-carried callbacks, replayed with existing bounded buffer effects."""
import hashlib
import json
import struct

import match
import function_thunk_profile as thunk
import named_data_buffer_profile as named

SELECTOR = 'static-callback-buffer-v1'
SCHEMA = 'elf-symbol-thumb-static-callback-buffer-v1'
CONTROL_FLOW = 'complete Thumb owner with exact register callback targets and ROM-proved bounded buffer effects'
MAX_DEPENDENCIES = 10
MAX_CONTEXTS = 128


class StaticCallbackBufferProof(named.NamedDataBufferProof):
    dependency_budget = MAX_DEPENDENCIES

    def __init__(self, rom, mapping, index, objects):
        super().__init__(rom, mapping, index, objects)
        self.contexts = set()
        self.callbacks = {}

    def argument_constants(self, constants):
        return dict(constants)

    def clear_extra_call_constants(self, constants):
        # The ordinary frame proof does not establish preservation of arbitrary
        # register values. Even callee-saved target facts die at every call.
        constants.clear()

    def extra_constant(self, instruction, data, address, constants):
        operands = instruction.operands
        if instruction.size != 2 or instruction.cc not in (match.ARM_CC_AL, match.ARM_CC_INVALID):
            return None
        if instruction.mnemonic == 'ldr' and len(operands) == 2 and \
                operands[0].type == match.ARM_OP_REG and operands[1].type == match.ARM_OP_MEM and \
                operands[1].mem.base == match.ARM_REG_PC and not operands[1].mem.index:
            offset = ((instruction.address + 4) & ~3) + operands[1].mem.disp - address
            if offset < 0 or offset + 4 > len(data) or (address + offset) % 4:
                raise ValueError('static callback literal is not a complete aligned owner word')
            return struct.unpack_from('<I', data, offset)[0]
        if instruction.mnemonic in ('add', 'adds') and len(operands) == 3 and \
                operands[0].type == match.ARM_OP_REG and operands[1].type == match.ARM_OP_REG and \
                operands[2].type == match.ARM_OP_IMM and operands[2].imm == 0:
            return constants.get(operands[1].reg)
        return None

    def check_arguments(self, address, arguments, stack, incoming, protected, *, constants=None, site=None):
        if not arguments and not incoming:
            return {}
        constants = constants or {}
        context = (address, tuple(sorted(arguments.items())), tuple(stack),
                   tuple(sorted(incoming.items())), tuple(sorted(protected)),
                   tuple(sorted(constants.items())), site)
        self.contexts.add(context)
        if len(self.contexts) > MAX_CONTEXTS:
            raise ValueError('static callback context budget exceeded')
        reverse = {value: name for name, value in thunk.ALIASES.items()}
        if address not in reverse:
            return super().check_arguments(address, arguments, stack, incoming, protected,
                                           constants=constants, site=site)
        name = reverse[address]
        canonical = thunk.dependencies([name], self.rom)[0]
        data = self.span(address)
        if len(data) != 2 or data != self.rom[address-match.ROM_BASE:address-match.ROM_BASE+2]:
            raise ValueError('static callback thunk requires its exact two-byte owner')
        register = match.ARM_REG_R0 + (address - thunk.START) // 4
        value = constants.get(register)
        if register in arguments or value is None or value % 2 != 1:
            raise ValueError('static callback target register is not an exact Thumb function pointer')
        target = match.function_address_target(f'func_{value & ~1:08X}', self.entries,
                                               address, len(data), len(self.rom))
        if target in reverse:
            raise ValueError('static callback target cannot be another indirect thunk')
        self.dependencies[address] = data
        self.records[address] = {'address': address, 'end': address+len(data), 'bytes': len(data),
            'body_sha256': hashlib.sha256(data).hexdigest(), **self.identities,
            'structure': {'kind': 'existing-canonical-call-via-register-v1',
                          'canonical_dependency': canonical}}
        # No cached effects: every target/alias/constant context replays the body.
        self.callbacks[context] = {'site': site, 'thunk': address, 'register': register,
            'target': target, 'arguments': [list(pair) for pair in sorted(arguments.items())],
            'incoming': [list(pair) for pair in sorted(incoming.items())],
            'protected': sorted(protected), 'stack': [list(word) for word in stack],
            'constants': [list(pair) for pair in sorted(constants.items())]}
        return super().check_arguments(target, arguments, stack, incoming, protected,
                                       constants=constants, site=site)

    def observations(self):
        return sorted(self.callbacks.values(), key=lambda row: json.dumps(row, sort_keys=True))
