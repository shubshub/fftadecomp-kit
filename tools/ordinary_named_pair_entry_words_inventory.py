"""Default-off C918/E6F0 output pair with four read-only incoming ABI words."""
import argparse
import json
from pathlib import Path

from capstone.arm import ARM_REG_R0, ARM_REG_R1, ARM_REG_R12, ARM_REG_LR
import ordinary_named_output_leaf_only_inventory as leaf
import formal_r0_r1_named_leaf_inventory as output
import readonly_entry_stack_words_profile as entry

parent, named = leaf.parent, leaf.named
FIRST = leaf.LEAF
SELECTOR = 'ordinary-named-pair-entry-words-inventory-v1'
SCHEMA = 'thumb-ordinary-named-pair-entry-words-inventory-v1'
sha, text = named.sha, named.text


def entry_policy():
    return {'schema': entry.SCHEMA, 'words': [0, 1, 2, 3]}


def validate_entry(policy):
    entry.validate(policy)
    if policy != entry_policy():
        raise ValueError('named pair requires exactly four explicit incoming words')


class R0R1LocalOutputProof:
    """Discharge the freshly observed formal halfwords into live caller locals."""
    def __init__(self, data, rom, mapping, index, data_mapping, sites, policy):
        address = output.IDENTITY[0]
        if type(sites) is not dict or len(sites) != 1 or any(
                type(site) is not int or site % 2 or type(target) is not int or target != address
                for site, target in sites.items()):
            raise ValueError('r0/r1 local output requires one exact marked call site')
        self._record, _ = output.verify(data, address, rom, mapping, index, data_mapping,
            selector=output.SELECTOR, readonly_named_buffer_policy=policy,
            formal_output_policy=output.output_policy())
        self.sites = dict(sites)
        self._sites = text(sorted(sites.items()))
        self._seal = sha(text(self._record).encode())
        self._observations = {}

    def validate_calls(self, calls):
        if type(calls) is not dict or text(sorted(self.sites.items())) != self._sites or any(
                calls.get(site) != target for site, target in self.sites.items()) or \
                sha(text(self._record).encode()) != self._seal or \
                self._record['effects']['writes'] != output.output_policy()['writes']:
            raise ValueError('r0/r1 local output differs from its fresh body/site/effect proof')

    def check_call(self, site, target, aliases, stack, pointer_slots):
        self.validate_calls({site: target})
        clobbered = {*range(ARM_REG_R0, ARM_REG_R0+4), ARM_REG_R12, ARM_REG_LR}
        if self.sites.get(site) != target or type(stack) is not list or not stack or \
                set(aliases) & clobbered != {ARM_REG_R0, ARM_REG_R1}:
            raise ValueError('r0/r1 output requires exactly its two local argument pointers')
        base = -4*len(stack)
        writes = []
        for formal, offset, width in self._record['effects']['writes']:
            values = aliases[ARM_REG_R0+formal]
            if type(values) is not frozenset or len(values) != 1:
                raise ValueError('r0/r1 output needs one all-path local pointer origin')
            origin, live = next(iter(values))
            if type(origin) is not int or live is not True:
                raise ValueError('r0/r1 output pointer has missing or expired lifetime')
            position = origin+offset-base
            if (origin+offset) % width or position < 8 or origin+offset+width > 0 or any(
                    stack[number][0] != 'local'
                    for number in range(position//4, (position+width-1)//4+1)):
                raise ValueError('r0/r1 output leaves aligned live locals or overlaps outgoing/saved words')
            writes.append((origin+offset, width))
        if max(writes[0][0], writes[1][0]) < min(start+width for start, width in writes):
            raise ValueError('r0/r1 actual halfword domains overlap')
        self._observations[site] = {'site': site, 'target': target,
            'caller_SP_entry_offset': base,
            'argument_entry_SP_offsets': [[formal, writes[formal][0]] for formal in (0, 1)],
            'writes_entry_SP_offsets': [list(row) for row in writes],
            'callee_stack_separation': 'fresh zero-byte frame; formal writes in caller locals above outgoing words',
            'physical_nonalias_claim': False}
        return writes

    def fingerprint(self):
        self.validate_calls(self.sites)
        if set(self._observations) != set(self.sites):
            raise ValueError('r0/r1 output proof did not cover every marked call')
        return {'schema': output.SCHEMA, 'native_leaf': json.loads(text(self._record)),
                'calls': [self._observations[site] for site in sorted(self._observations)]}


class NamedPairEntryWordsProof:
    """Closed pair of independently fresh body, effects and frame proofs."""
    def __init__(self, rom, mapping, index, data_mapping, calls, first_policy, second_policy):
        bodies = {identity[0]: output.second.exact_body(identity, rom, mapping, index)
                  for identity in (FIRST, output.IDENTITY)}
        first_sites = {site: target for site, target in calls.items() if target == FIRST[0]}
        second_sites = {site: target for site, target in calls.items() if target == output.IDENTITY[0]}
        if len(first_sites) != 1 or len(second_sites) != 1:
            raise ValueError('named pair requires exactly one actual call to each leaf')
        self._first = named.NamedReadonlyFormalLeafProof(bodies[FIRST[0]], FIRST[0], rom,
            mapping, index, data_mapping, first_sites, first_policy)
        self._second = R0R1LocalOutputProof(bodies[output.IDENTITY[0]], rom, mapping,
            index, data_mapping, second_sites, second_policy)
        self.sites = first_sites | second_sites
        self._sites = text(sorted(self.sites.items()))

    def validate_calls(self, calls):
        if type(self._first) is not named.NamedReadonlyFormalLeafProof or \
                type(self._second) is not R0R1LocalOutputProof or \
                text(sorted(self.sites.items())) != self._sites or \
                set(self.sites) != set(self._first.sites) | set(self._second.sites):
            raise ValueError('named pair differs from its exact fresh children or sites')
        self._first.validate_calls(calls)
        self._second.validate_calls(calls)

    def check_call(self, site, target, aliases, stack, pointer_slots):
        self.validate_calls(self.sites)
        if self.sites.get(site) != target:
            raise ValueError('unmarked named pair call or target')
        child = self._first if site in self._first.sites else self._second
        return child.check_call(site, target, aliases, stack, pointer_slots)

    def fingerprint(self):
        self.validate_calls(self.sites)
        return {'schema': SCHEMA, 'callees': [self._first.fingerprint(), self._second.fingerprint()],
            'store_events': 7, 'unique_write_footprints_per_callee': [3, 2],
            'written_abstract_word_facts': 'existing frame invalidates every overlapping local scalar/alias-slot fact',
            'physical_nonalias_claim': False}


def bind_calls(calls, mapping, address, size, rom_size):
    bound = leaf.bind_calls(calls, mapping, address, size, rom_size)
    if list(calls.values()).count(output.IDENTITY[0]) != 1:
        raise ValueError('named pair requires one actual r0/r1 leaf call')
    return bound


def verify(data, address, rom, mapping, index, data_mapping, calls, bindings, *, selector,
           readonly_named_buffer_policy=None, readonly_second_named_buffer_policy=None,
           readonly_entry_words_policy=None, manifest=None):
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('named pair requires its explicit default-off selector')
    validate_entry(readonly_entry_words_policy)
    named.validate_named_policy(readonly_named_buffer_policy, data_mapping)
    output.second.validate_second_policy(readonly_second_named_buffer_policy, data_mapping)
    instructions, edges, actual_calls, partition = parent.complete(data, address, rom, mapping, index)
    if type(calls) is not dict or calls != actual_calls or type(bindings) is not dict or \
            bindings != bind_calls(calls, mapping, address, len(data), len(rom)):
        raise ValueError('named pair bindings differ from every actual reached call')
    if any(start < address+len(data) and end > address for start, end, _, _ in (FIRST, output.IDENTITY)):
        raise ValueError('named pair helper overlaps caller')
    proof = NamedPairEntryWordsProof(rom, mapping, index, data_mapping, calls,
        readonly_named_buffer_policy, readonly_second_named_buffer_policy)
    restored = parent.frame.prove_frame(instructions, edges, address, {}, calls,
        stack_aliases=True, local_alias_slot_policy=parent.slots.SELECTOR,
        formal_stack_callee_proof=proof, entry_stack_policy=readonly_entry_words_policy,
        formal_stack_entry_words_policy=SELECTOR, zero_index_profile=parent.zero_index.SELECTOR)
    modules = (leaf, named, output, output.second, parent, parent.analyze, parent.match,
        parent.thunks, parent.owner, parent.graph, parent.operations, parent.indices, parent.frame,
        parent.slots, parent.incoming, parent.zero_index, entry)
    sources = {Path(module.__file__).name: sha(Path(module.__file__).read_bytes()) for module in modules}
    sources[Path(__file__).name] = sha(Path(__file__).read_bytes())
    observed = {'schema': SCHEMA, 'selector': SELECTOR, 'inventory_only': True,
        'address': address, 'end': address+len(data), 'instructions': len(instructions),
        'body_sha256': sha(data), 'ROM_sha256': sha(rom), 'mapping_sha256': sha(mapping),
        'index_sha256': sha(index), 'data_mapping_sha256': sha(data_mapping),
        'calls': [[site, target, bindings[site]] for site, target in sorted(calls.items())],
        'partition': partition, 'frame': restored,
        'readonly_named_buffer_policy': json.loads(text(readonly_named_buffer_policy)),
        'named_read_premise': named.READ_PREMISE,
        'readonly_second_named_buffer_policy': json.loads(text(readonly_second_named_buffer_policy)),
        'second_named_read_premise': output.PREMISE,
        'readonly_entry_words_policy': json.loads(text(readonly_entry_words_policy)),
        'entry_words_premise': entry.CONTRACT,
        'component_accounting': {'fresh_helper_workflows': 2, 'fresh_helper_frames': 2,
            'fresh_caller_frames': 1, 'helper_store_events': [5, 2], 'unique_write_footprints': [3, 2]},
        'ordinary_call_premise': 'conditional: every other ordinary callee returns and obeys the existing r4-r11/SP preserving direct-call ABI; its body and memory effects are not proved',
        'output_call_premise': 'actual initialized outgoing words0/4 and arg3 discharge C918 writes; r0/r1 discharge E6F0 writes; every observed halfword is in distinct live local domains above outgoing words and outside saved slots',
        'named_loaded_values': 'unknown scalars; no numeric or return facts',
        'complete_native_structural_proof': True, 'complete_argument_effect_proof': True,
        'source_or_ELF_admission': False, 'arithmetic_C_equivalence': False,
        'numeric_input_preconditions': [], 'numeric_return_facts': [],
        'physical_memory_claim': False, 'memory_safety_claim': False, 'nonescape_claim': False,
        'universal_termination_claim': False, 'producer_source_sha256': sources}
    if manifest is not None and text(manifest) != text(observed):
        raise ValueError('named pair manifest differs from the fresh native proof')
    return observed, [instructions[site] for site in sorted(instructions)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile', required=True, choices=(SELECTOR,))
    for name in ('rom', 'mapping', 'index', 'data-mapping'):
        parser.add_argument('--'+name, required=True, type=Path)
    for name in ('readonly-named-buffer-policy', 'readonly-second-named-buffer-policy', 'readonly-entry-words-policy'):
        parser.add_argument('--'+name, required=True, type=json.loads)
    parser.add_argument('address', type=lambda value: int(value, 16))
    args = parser.parse_args()
    rom, mapping, index, data_mapping = (args.rom.read_bytes(), args.mapping.read_bytes(),
        args.index.read_bytes(), args.data_mapping.read_bytes())
    rows = [row for row in json.loads(mapping) if int(row['rom'], 16) == args.address]
    if len(rows) != 1:
        raise ValueError('named pair requires one exact caller row')
    data = rom[args.address-parent.match.ROM_BASE:int(rows[0]['end'], 16)-parent.match.ROM_BASE]
    _, _, calls, _ = parent.complete(data, args.address, rom, mapping, index)
    bindings = bind_calls(calls, mapping, args.address, len(data), len(rom))
    result, _ = verify(data, args.address, rom, mapping, index, data_mapping, calls, bindings,
        selector=args.profile, readonly_named_buffer_policy=args.readonly_named_buffer_policy,
        readonly_second_named_buffer_policy=args.readonly_second_named_buffer_policy,
        readonly_entry_words_policy=args.readonly_entry_words_policy)
    print(text(result))


if __name__ == '__main__':
    main()
