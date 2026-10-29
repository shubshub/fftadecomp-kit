"""Exact live stack words within the existing buffer and canonical-call engine."""
import json

import match
import static_callback_buffer_profile as callback

SELECTOR = 'protected-descriptor-word-v1'
SCHEMA = 'elf-symbol-thumb-protected-descriptor-word-v1'
CONTROL_FLOW = 'complete Thumb owner with exact live descriptor words and bounded callback buffer effects'
MAX_DEPENDENCIES = 12
MAX_CONTEXTS = callback.MAX_CONTEXTS


class WordResult(dict):
    def __init__(self, aliases, words):
        super().__init__(aliases)
        self.words = tuple(sorted(words.items()))


class ProtectedDescriptorWordProof(callback.StaticCallbackBufferProof):
    word_provenance = True
    dependency_budget = MAX_DEPENDENCIES

    def __init__(self, *args):
        super().__init__(*args)
        self.word_reads = {}

    def word_context(self, words, frame_base, root_frame, watched=()):
        return dict(words=dict(words), frame_base=frame_base, root_frame=root_frame, watched=tuple(sorted(watched)))

    def word_result(self, aliases, words):
        return WordResult(aliases, words)

    def prune_words(self, words, stack):
        for slot, (kind, value) in tuple(words.items()):
            try:
                self.access(slot, 4, stack)
                if kind == 'pointer':
                    self.access(value, 1, stack)
            except ValueError:
                del words[slot]

    def check_lifetime(self, data, address, instructions, finite=None):
        """No allocation after deallocation, including through CFG back edges."""
        by_address = {item.address: item for item in instructions}
        pending, seen = [(address, False)], set()
        while pending:
            site, shrunk = pending.pop()
            if (site, shrunk) in seen:
                continue
            seen.add((site, shrunk))
            item = by_address[site]
            regs = [operand.reg for operand in item.operands if operand.type == match.ARM_OP_REG]
            adjustment = match.thumb_stack_adjustment(item)
            if adjustment is None:
                adjustment = match.thumb_literal_stack_adjustment(item, data, address)
            grows = item.mnemonic == 'push' or adjustment is not None and adjustment < 0
            if grows and shrunk:
                raise ValueError('descriptor word lifetime excludes allocation after deallocation')
            shrunk |= item.mnemonic == 'pop' or adjustment is not None and adjustment > 0
            if finite and site in finite:
                successors = finite[site]
            elif item.mnemonic == 'bx' or item.mnemonic == 'pop' and match.ARM_REG_PC in regs or \
                    item.mnemonic == 'mov' and regs and regs[0] == match.ARM_REG_PC:
                successors = ()
            elif item.id == match.ARM_INS_B:
                successors = (item.operands[0].imm,)
                if item.cc not in (match.ARM_CC_AL, match.ARM_CC_INVALID):
                    successors += (site+item.size,)
            else:
                successors = (site+item.size,)
            pending.extend((target, shrunk) for target in successors)

    def inspect(self, address, data):
        instructions, finite = super().inspect(address, data)
        self.check_lifetime(data, address, instructions, finite)
        return instructions, finite

    def word_memory(self, instruction, aliases, constants, stack, words, sp_offset, protected, *, root_frame=None):
        """Only exact full-word accesses can restore existing word provenance."""
        operands = instruction.operands
        if instruction.mnemonic.startswith(('stm', 'swp', 'vstr')):
            words.clear()
            raise ValueError('descriptor effects require a proved bounded base for block writes')
        memories = [operand for operand in operands if operand.type == match.ARM_OP_MEM]
        if not memories:
            return None, None, False, False
        memory = memories[0].mem
        reading = instruction.mnemonic.startswith('ldr')
        writing = instruction.mnemonic.startswith('str')
        if memory.base == match.ARM_REG_PC and reading:
            return None, None, False, False
        widths = {'ldr':4, 'str':4, 'ldrb':1, 'strb':1, 'ldrh':2, 'strh':2,
                  'ldrsb':1, 'ldrsh':2}
        width = widths.get(instruction.mnemonic)
        base = sp_offset if memory.base == match.ARM_REG_SP else aliases.get(memory.base)
        if base is None or width is None or len(memories) != 1:
            if not reading:
                words.clear()
            return None, None, False, False
        if memory.index and memory.index not in constants:
            if writing:
                words.clear()
            return None, None, False, False
        offset = base + memory.disp + (constants[memory.index] if memory.index else 0)
        overlapping = {slot for slot in words.keys() | set(protected)
                       if offset < slot+4 and offset+width > slot}
        if reading:
            if not overlapping:
                return None, None, False, False
            if width != 4 or offset % 4 or overlapping != {offset} or \
                    instruction.size != 2 or instruction.cc not in (match.ARM_CC_AL,match.ARM_CC_INVALID) or \
                    instruction.mnemonic != 'ldr' or instruction.writeback or \
                    memory.index or len(operands) != 2 or operands[0].type != match.ARM_OP_REG:
                raise ValueError('descriptor reload requires one exact aligned full word')
            self.access(offset, 4, stack)
            value = words.get(offset)
            if value is None:
                raise ValueError('descriptor reload lacks an exact surviving word value')
            kind, number = value
            if kind == 'pointer':
                self.access(number, 1, stack)
            key = (instruction.address, offset, value, tuple(sorted(words.items())), sp_offset,
                   tuple(stack), tuple(sorted(aliases.items())), tuple(sorted(constants.items())),
                   tuple(sorted(protected)), root_frame)
            self.word_reads[key] = {'site':instruction.address, 'offset':offset,
                'kind':kind, 'value':number, 'sp_offset':sp_offset,
                'words':[[slot,list(fact)] for slot,fact in sorted(words.items())],
                'frame':[list(word) for word in stack], 'root_frame':root_frame}
            return ((operands[0].reg, number) if kind == 'pointer' else None,
                    number if kind == 'constant' else None, True, False)
        for slot in overlapping:
            words.pop(slot, None)
        if not writing:
            words.clear()
            return None, None, False, False
        register = operands[0].reg if operands and operands[0].type == match.ARM_OP_REG else None
        if width != 4 or offset % 4 or instruction.writeback or memory.index:
            return None, None, False, False
        try:
            self.access(offset, 4, stack)
        except ValueError:
            return None, None, False, False
        if register in aliases:
            self.access(aliases[register], 1, stack)
            words[offset] = ('pointer', aliases[register])
            return None, None, False, True
        if register in constants:
            words[offset] = ('constant', constants[register])
        return None, None, False, False

    def word_observations(self):
        return sorted(self.word_reads.values(), key=lambda row: json.dumps(row, sort_keys=True))
