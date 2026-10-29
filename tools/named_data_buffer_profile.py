"""Explicit named-data buffer composition with exact read-only switch callees."""
import hashlib
import json
import struct

import match
import owner_graph_profile as graph
from inert_spin_profile import validate_span

SELECTOR = 'named-data-buffer-v1'
SCHEMA = 'elf-symbol-thumb-named-data-buffer-calls-v1'
CONTROL_FLOW = 'complete Thumb owner with typed data literals and ROM-proved bounded buffer callees'
MAX_DEPENDENCIES = 8
MAX_BYTES = 4096


def validate_owner(data, address, rom, mapping, index):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError('duplicate named-data buffer mapping key')
            result[key] = value
        return result
    json.loads(mapping, object_pairs_hook=unique)
    entries = validate_span(data, address, rom, mapping, index)
    entry = next(row for row in entries if int(row['rom'], 16) == address)
    fields = next(line.split() for line in index.decode().splitlines()
                  if line.split() and not line.lstrip().startswith('#') and
                  int(line.split()[0], 16) == address)
    # Legacy counts include literal words in some rows. They remain bounded
    # numeric annotations; the complete native CFG establishes the real count.
    if type(entry.get('instrs')) is not int or not 0 <= entry['instrs'] <= len(data)//2 or \
            len(fields) < 4 or not fields[3].isdigit() or not 0 <= int(fields[3]) <= len(data)//2:
        raise ValueError('malformed named-data buffer instruction-count annotation')


class NamedDataBufferProof(match.BufferCallProof):
    """Keep existing alias rules; add only an independently proved finite dispatch."""

    dependency_budget = MAX_DEPENDENCIES

    def __init__(self, rom, mapping, index, objects):
        super().__init__(rom, mapping, stack_arguments=True)
        self.mapping, self.index, self.objects = mapping, index, objects
        self.requested = set()
        self.records = {}
        self.identities = {'rom_sha256': hashlib.sha256(rom).hexdigest(),
                           'mapping_sha256': hashlib.sha256(mapping).hexdigest(),
                           'index_sha256': hashlib.sha256(index).hexdigest(),
                           'objects_sha256': None if objects is None else hashlib.sha256(objects).hexdigest()}

    def span(self, address):
        if address not in self.requested and len(self.requested) >= self.dependency_budget:
            raise ValueError('named-data buffer dependency budget exceeded')
        self.requested.add(address)
        entry = self.target(address)
        if not 0 < int(entry['end'], 16) - address <= MAX_BYTES:
            raise ValueError('named-data buffer dependency exceeds bounded owner size')
        data = super().span(address)
        validate_owner(data, address, self.rom, self.mapping, self.index)
        return data

    def inspect(self, address, data):
        candidates = []
        for literal in range((-address) % 4, len(data) - 3, 4):
            encoding = match.preloaded_switch_encoding(data, address, literal)
            if encoding is not None:
                candidates.append((literal, encoding[-1]))
        if len(candidates) > 1:
            raise ValueError('ambiguous preloaded buffer switch')
        transfers = {}
        if candidates:
            literal, bound = candidates[0]
            end = literal + 4 * (bound + 2)
            if end > len(data):
                raise ValueError('preloaded buffer switch leaves complete owner')
            words = {offset: struct.unpack_from('<I', data, offset)[0] - address
                     for offset in range(literal, end, 4)}
            # This is a ROM-checked literal role, not an invented named object.
            # The existing complete read-only CFG proof and the alias replay
            # independently establish effects; literal identity grants no alias fact.
            value = struct.unpack_from('<I', data, literal - 4)[0]
            object_word = {literal - 4: ('ROM-checked literal word', value)}
            switch = match.preloaded_switch_layout(data, address, words, object_word)
            instructions = match.verify_leaf_instructions(data, address, True,
                switch_relocations=words, switch_data_relocations=object_word,
                preloaded_switch=True)
            transfers[address + switch['transfer']] = tuple(sorted(
                {address + target for offset, target in words.items() if offset != literal}))
            structure = {'kind': 'existing-complete-read-only-preloaded-switch-v1',
                         'switch': switch, 'instructions': len(instructions),
                         'object_word_sha256': hashlib.sha256(data[literal-4:literal]).hexdigest()}
        else:
            instructions, transfers = super().inspect(address, data)
            import owner_admission_profile as owner
            refinement = owner.refine(data, address, self.mapping)
            ins, _, branches, calls, words = graph.graph(data, address, refinement)
            if branches or words or set(ins) != {item.address for item in instructions}:
                raise ValueError('buffer dependency differs from complete ordinary CFG')
            structure = {'kind': 'complete-ordinary-buffer-owner-v1',
                         'instructions': len(instructions),
                         'partition': graph.partition(data, address, refinement, ins, words)}
        self.records[address] = {
            'address': address, 'end': address + len(data), 'bytes': len(data),
            'body_sha256': hashlib.sha256(data).hexdigest(), 'structure': structure,
            **self.identities}
        return instructions, transfers
