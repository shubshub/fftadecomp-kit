"""Exact callee-local stack origins in the existing descriptor buffer replay."""
import hashlib
import json

import match
import owner_graph_profile as graph
import protected_descriptor_word_profile as descriptor
import watched_switch_preservation_profile as watched

SELECTOR = 'descriptor-output-alias-v1'
SCHEMA = 'elf-symbol-thumb-descriptor-output-alias-v1'
CONTROL_FLOW = 'complete Thumb owner with context-replayed callee stack origins and exact live descriptor words'
MAX_DEPENDENCIES = 14
MAX_STACK_BYTES = 4096


class _StructuralFrameProof(descriptor.ProtectedDescriptorWordProof):
    """Native local frame proof only; no call effect or identity is exported."""

    def check_call(self, address, aliases, stack, slots=None, **kwargs):
        # The independent actual-context engine must inspect effects afterwards.
        # In this structural pass calls destroy all scalar/pointer word facts.
        return descriptor.WordResult({}, {})


class DescriptorOutputAliasProof(watched.WatchedSwitchPreservationProof):
    callee_frames = True
    dependency_budget = MAX_DEPENDENCIES

    def __init__(self, *args):
        super().__init__(*args)
        self.frame_aliases = {}
        self.native_frames = {}

    def inspect(self, address, data):
        import owner_admission_profile as owner
        refinement = owner.refine(data, address, self.mapping)
        if refinement['word_switches'] or any(
                match.preloaded_switch_encoding(data, address, literal) is not None
                for literal in range((-address) % 4, len(data)-3, 4)):
            return super().inspect(address, data)
        instructions, _, branches, _, words = graph.graph(data, address, refinement)
        if branches or words:
            raise ValueError('descriptor callee frame excludes local BL and unproved switch words')
        partition = graph.partition(data, address, refinement, instructions, words)
        verified = list(instructions.values())
        self.check_lifetime(data, address, verified)
        self.records[address] = {'address':address, 'end':address+len(data), 'bytes':len(data),
            'body_sha256':hashlib.sha256(data).hexdigest(), **self.identities,
            'structure':{'kind':'complete-closed-CFG-before-actual-effects-and-native-frame-v1',
                'instructions':len(verified), 'partition':partition}}
        return verified, {}

    def complete_frame(self, address, data, instructions):
        # A context cannot export effects until the independent complete native
        # frame/return proof passes. Failed prefixes remain diagnostic evidence.
        kind = self.records[address]['structure']['kind']
        if kind == 'complete-closed-CFG-before-actual-effects-and-native-frame-v1':
            structural = _StructuralFrameProof(self.rom, self.mapping, self.index, self.objects)
            verified = match.verify_leaf_instructions(data, address, True,
                buffer_proof=structural, call_resolver=self.target)
            if {item.address for item in instructions} != {item.address for item in verified}:
                raise ValueError('descriptor callee frame differs from complete native CFG')
        self.native_frames[address] = self.native_frames.get(address, 0) + 1

    def word_memory(self, instruction, aliases, constants, stack, words, sp_offset, protected, **kwargs):
        if instruction.mnemonic.startswith('stm') and instruction.operands and \
                instruction.operands[0].type == match.ARM_OP_REG and \
                instruction.operands[0].reg in aliases:
            raise ValueError('descriptor output base is known; append block-write and iteration bounds remain unproved')
        return super().word_memory(instruction, aliases, constants, stack, words,
                                   sp_offset, protected, **kwargs)

    def observe_frame_alias(self, address, site, assignment, stack, words, frame_base,
                            root_frame, watched_registers, arguments, incoming, protected, constants):
        row = {'address':address, 'site':site, 'register':assignment[0], 'offset':assignment[1],
            'frame_base':frame_base, 'root_frame':root_frame, 'stack':[list(word) for word in stack],
            'words':[[slot,list(value)] for slot,value in sorted(words.items())],
            'watched':sorted(watched_registers), 'arguments':[list(pair) for pair in sorted(arguments.items())],
            'incoming':[list(pair) for pair in sorted(incoming.items())], 'protected':sorted(protected),
            'constants':[list(pair) for pair in sorted(constants.items())]}
        self.frame_aliases[json.dumps(row,sort_keys=True)] = row

    def frame_observations(self):
        return [self.frame_aliases[key] for key in sorted(self.frame_aliases)]

    def native_frame_observations(self):
        return [{'address':address,'replays':count} for address,count in sorted(self.native_frames.items())]
