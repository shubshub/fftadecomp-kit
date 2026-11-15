"""Private, default-off two-local-word helper effect prerequisite.

This is not an owner-admission selector. The existing native frame and alias
engine remains authoritative, including expired scratch aliases at return.
Only the bound callback can allocate a frame; its one bound helper has its
complete five-instruction effects independently decoded and checked.
"""
import hashlib
import json
from pathlib import Path

import match
import descriptor_output_alias_profile as frame
import protected_descriptor_word_profile as descriptor

SCHEMA = 'callback-local-two-word-output-frame-prerequisite-v1'
_HASHES = ('rom_sha256', 'mapping_sha256', 'index_sha256', 'objects_sha256',
           'callback_sha256', 'helper_sha256')
_KEYS = {'schema', 'callback', 'helper', 'call_site', 'local_bytes', *_HASHES}
_ENGINE_FILES = ('match.py', 'armv4t.py', 'descriptor_output_alias_profile.py',
                 'protected_descriptor_word_profile.py', 'named_data_buffer_profile.py',
                 'static_callback_buffer_profile.py', 'watched_switch_preservation_profile.py')


def sha(data):
    return hashlib.sha256(data).hexdigest()


class CallbackLocalTwoOutputProof(frame.DescriptorOutputAliasProof):
    """Replay one explicit callback frame and two exact ordered word stores.

    Loaded words remain unknown scalars. In particular, source/output aliasing
    does not license combining or reordering the observed loads and stores.
    The helper's unchanged R1/R2 aliases are retained, not erased by its void
    source prototype or by a generic caller-clobbered register assumption.
    """

    def __init__(self, rom, mapping, index, objects, *, policy=None):
        if type(policy) is not dict or set(policy) != _KEYS or policy.get('schema') != SCHEMA:
            raise ValueError('exact explicit local-output prerequisite policy required')
        for key in ('callback', 'helper', 'call_site'):
            if type(policy[key]) is not int or policy[key] % 2:
                raise ValueError('local-output policy requires aligned integer code identities')
        if type(policy['local_bytes']) is not int or policy['local_bytes'] != 8:
            raise ValueError('local-output prerequisite requires exactly two local words')
        for key in _HASHES:
            value = policy[key]
            if type(value) is not str or len(value) != 64 or any(c not in '0123456789abcdef' for c in value):
                raise ValueError('local-output policy requires exact lowercase SHA256 bindings')
        for key, value in zip(_HASHES[:4], (rom, mapping, index, objects)):
            if not isinstance(value, bytes) or sha(value) != policy[key]:
                raise ValueError('stale local-output input binding: ' + key)
        super().__init__(rom, mapping, index, objects)
        self.policy = json.dumps(policy, sort_keys=True, separators=(',', ':'))
        self.callback, self.helper, self.call_site = (policy[key] for key in ('callback', 'helper', 'call_site'))
        if self.callback == self.helper:
            raise ValueError('callback and output helper require distinct owners')
        self.effect_rows = []
        self.output_reads = []
        self._context = None
        self.completed = False
        for label, address in (('callback', self.callback), ('helper', self.helper)):
            if sha(self.span(address)) != policy[label + '_sha256']:
                raise ValueError('stale local-output complete ' + label + ' body')

    def inspect(self, address, data):
        if address != self.callback:
            raise ValueError('local-output frame is restricted to its bound callback')
        instructions, finite = super().inspect(address, data)
        calls = [item for item in instructions if match.CS_GRP_CALL in item.groups]
        if len(calls) != 1 or calls[0].address != self.call_site or \
                calls[0].operands[0].imm != self.helper:
            raise ValueError('callback requires its one exact direct output-helper site')
        # This prerequisite opens the actual 8B-local/12B-save frame only.
        # Other descriptor frame classes and ordinary buffer selectors are unchanged.
        ordered = sorted(instructions, key=lambda item: item.address)
        if len(ordered) < 3 or ordered[0].bytes != bytes.fromhex('30b5') or \
                ordered[1].bytes != bytes.fromhex('82b0'):
            raise ValueError('callback requires the bounded two-word local frame prologue')
        allocations = [(item.address, match.thumb_stack_adjustment(item)) for item in ordered
                       if match.thumb_stack_adjustment(item) is not None]
        if allocations != [(address + 2, -2), (next((item.address for item in ordered
                if item.bytes == bytes.fromhex('02b0')), -1), 2)] or \
                sum(item.mnemonic == 'push' for item in ordered) != 1:
            raise ValueError('callback excludes additional or reused local allocations')
        return instructions, finite

    def _helper_instructions(self):
        data = self.span(self.helper)
        instructions = match.verify_leaf_instructions(data, self.helper, True)
        if len(data) != 10 or len(instructions) != 5 or \
                [item.address for item in instructions] != list(range(self.helper, self.helper + 10, 2)):
            raise ValueError('two-output helper requires its complete five narrow instructions')
        r0, r1, r2, r3 = (match.ARM_REG_R0 + n for n in range(4))
        expected = (('ldr', r3, r0, 4), ('str', r3, r1, 0),
                    ('ldr', r0, r0, 0), ('str', r0, r2, 0))
        for item, (mnemonic, register, base, displacement) in zip(instructions, expected):
            operands = item.operands
            if item.size != 2 or item.mnemonic != mnemonic or item.writeback or \
                    len(operands) != 2 or operands[0].type != match.ARM_OP_REG or \
                    operands[0].reg != register or operands[1].type != match.ARM_OP_MEM or \
                    operands[1].mem.base != base or operands[1].mem.index or \
                    operands[1].mem.disp != displacement or operands[1].shift.type or \
                    item.cc not in (match.ARM_CC_AL, match.ARM_CC_INVALID):
                raise ValueError('two-output helper differs from ordered scalar-load/word-store effects')
            read, written = item.regs_access()
            if set(read) != ({base} if mnemonic == 'ldr' else {base, register}) or \
                    set(written) != ({register} if mnemonic == 'ldr' else set()):
                raise ValueError('two-output helper has unrecognized register effects')
        tail = instructions[-1]
        if tail.bytes != bytes.fromhex('7047') or set(tail.regs_access()[0]) != {match.ARM_REG_LR}:
            raise ValueError('two-output helper requires its verified entry-LR return')
        self.dependencies[self.helper] = data
        return data

    def _output_call(self, arguments, stack, incoming, protected, *, site, words,
                     frame_base, root_frame, watched, constants):
        if self._context is None or site != self.call_site:
            raise ValueError('two-output helper lacks its active callback call-site context')
        origin, outer_words, context_address = self._context
        if frame_base != origin - 20 or len(stack) != outer_words + 5 or \
                frame_base != -4 * len(stack):
            raise ValueError('two-output helper differs from the exact live callback frame')
        r1, r2 = match.ARM_REG_R1, match.ARM_REG_R2
        if arguments != {r1: frame_base, r2: frame_base + 4} or incoming:
            raise ValueError('two-output helper requires separate callback-local R1/R2 words')
        for offset in arguments.values():
            self.access(offset, 4, stack)
            if any(offset < slot + 4 and offset + 4 > slot for slot in protected):
                raise ValueError('local output overlaps a protected pointer word')
        if set(watched) & {match.ARM_REG_R0, match.ARM_REG_R3}:
            raise ValueError('two-output helper clobbers a watched alias')
        data = self._helper_instructions()
        updated = dict(words)
        for offset in arguments.values():
            for slot in tuple(updated):
                if offset < slot + 4 and offset + 4 > slot:
                    del updated[slot]
            # The site identifies an initialization event, never a numeric value.
            updated[offset] = ('local-output', site)
        self.effect_rows.append({'site': site, 'helper': self.helper,
            'helper_sha256': sha(data), 'context': context_address,
            'ordered_effects': [['read', 'source', 4, 4], ['write', 'R1', 0, 4],
                                ['read', 'source', 0, 4], ['write', 'R2', 0, 4]],
            'outputs': [[r1, frame_base], [r2, frame_base + 4]],
            'frame_base': frame_base, 'root_frame': root_frame,
            'stack': [list(slot) for slot in stack],
            'preserved_aliases': [list(pair) for pair in sorted(arguments.items())],
            'numeric_facts': []})
        return descriptor.WordResult(arguments, updated)

    def check_arguments(self, address, arguments, stack, incoming, protected, *,
                        constants=None, site=None, words=None, frame_base=None,
                        root_frame=None, watched=()):
        if address == self.helper:
            return self._output_call(arguments, stack, incoming, protected, site=site,
                words=words or {}, frame_base=frame_base, root_frame=root_frame,
                watched=watched, constants=constants or {})
        if address != self.callback or self._context is not None:
            raise ValueError('local-output prerequisite excludes other or recursive callback owners')
        if set(arguments) != {match.ARM_REG_R1} or incoming or frame_base != -4 * len(stack):
            raise ValueError('callback requires one explicit live context pointer and no incoming slots')
        for offset in (arguments[match.ARM_REG_R1], arguments[match.ARM_REG_R1] + 4):
            self.access(offset, 4, stack)
        for kind, value in (words or {}).values():
            if kind not in ('constant', 'pointer') or type(value) is not int:
                raise ValueError('callback input word facts cannot forge local output initialization')
        self._context = (frame_base, len(stack), arguments[match.ARM_REG_R1])
        self.completed = False
        try:
            result = super().check_arguments(address, arguments, stack, incoming, protected,
                constants=constants, site=site, words=words, frame_base=frame_base,
                root_frame=root_frame, watched=watched)
            self.completed = True
            return result
        finally:
            self._context = None

    def word_memory(self, instruction, aliases, constants, stack, words, sp_offset,
                    protected, *, root_frame=None):
        if self._context is not None and instruction.mnemonic.startswith('str') and \
                instruction.operands and instruction.operands[0].type == match.ARM_OP_REG:
            value = aliases.get(instruction.operands[0].reg)
            local = self._context[0] - 20
            if value is not None and local <= value < local + 8:
                raise ValueError('callback-local output pointer cannot be stored or escape')
        if self._context is not None and instruction.mnemonic.startswith('ldr'):
            for operand in instruction.operands:
                if operand.type != match.ARM_OP_MEM:
                    continue
                memory = operand.mem
                base = sp_offset if memory.base == match.ARM_REG_SP else aliases.get(memory.base)
                if base is None:
                    continue
                offset = base + memory.disp
                local = self._context[0] - 20
                if local <= offset < local + 8:
                    if memory.index or instruction.mnemonic != 'ldr' or offset % 4 or \
                            instruction.size != 2 or instruction.writeback:
                        raise ValueError('local output reads require exact aligned full words')
                    self.access(offset, 4, stack)
                    value = words.get(offset)
                    if value is None:
                        raise ValueError('callback reads an uninitialized local output word')
                    if value[0] == 'local-output':
                        self.output_reads.append({'site': instruction.address, 'offset': offset,
                            'producer': value[1], 'numeric_facts': []})
                        return None, None, True, False
        return super().word_memory(instruction, aliases, constants, stack, words,
                                   sp_offset, protected, root_frame=root_frame)

    def manifest(self):
        if not self.completed or self.callback not in self.native_frames:
            raise ValueError('local-output effects lack a completed native callback frame')
        engine = Path(match.__file__).resolve().parent
        return {'schema': SCHEMA, 'policy': json.loads(self.policy),
            'implementation_sha256': sha(Path(__file__).read_bytes()),
            'engine_sources': {name: sha((engine / name).read_bytes()) for name in _ENGINE_FILES},
            'dependencies': [{'address': address, 'bytes': len(data), 'body_sha256': sha(data)}
                             for address, data in sorted(self.dependencies.items())],
            'ordered_output_effects': list(self.effect_rows), 'local_scalar_reads': list(self.output_reads),
            'frame_aliases': self.frame_observations(), 'native_frames': self.native_frame_observations(),
            'claim': 'private frame/effect prerequisite only; no owner, ELF, callback-target or root admission'}
