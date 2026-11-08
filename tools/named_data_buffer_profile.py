"""Explicit named-data buffer composition with exact read-only switch callees."""
import hashlib
import json
import struct

import match
import owner_graph_profile as graph
from inert_spin_profile import validate_span

SELECTOR = 'named-data-buffer-v1'
SCHEMA = 'elf-symbol-thumb-named-data-buffer-calls-v1'
DATAFREE_SELECTOR = 'bounded-buffer-datafree-caller-v1'
DATAFREE_SCHEMA = 'elf-symbol-thumb-bounded-buffer-datafree-caller-v1'
DATAFREE_CONTROL_FLOW = 'complete data-free Thumb caller with unchanged bounded ordinary-buffer effects'
SCRATCH_SELECTOR = 'bounded-buffer-discarded-return-scratch-v1'
SCRATCH_SCHEMA = 'elf-symbol-thumb-bounded-buffer-discarded-return-scratch-v1'
SCRATCH_CONTROL_FLOW = 'bounded buffer calls with exact unobserved R2/R3 normal-return scratch'
BIOS_SQRT_SELECTOR = 'bounded-buffer-bios-sqrt-scratch-v1'
BIOS_SQRT_SCHEMA = 'elf-symbol-thumb-bounded-buffer-bios-sqrt-scratch-v1'
BIOS_SQRT_CONTROL_FLOW = 'bounded buffer calls with an exact scalar BIOS Sqrt wrapper and killed return scratch'
BIOS_FILL_SELECTOR = 'bounded-buffer-bios-fill-source-v1'
BIOS_FILL_SCHEMA = 'elf-symbol-thumb-bounded-buffer-bios-fill-source-v1'
BIOS_FILL_CONTROL_FLOW = 'complete named-data owner with exact conditional BIOS CpuSet local-source bounds'
FAST_FILL_SELECTOR = 'bounded-buffer-bios-fast-fill-source-v1'
FAST_FILL_SCHEMA = 'elf-symbol-thumb-bounded-buffer-bios-fast-fill-source-v1'
FAST_FILL_CONTROL_FLOW = 'complete data-free Thumb owner with exact conditional BIOS CpuFastSet local-word source bounds'
GUARDED_SWITCH_SELECTOR = 'bounded-buffer-guarded-switch-v1'
GUARDED_SWITCH_SCHEMA = 'elf-symbol-thumb-bounded-buffer-guarded-switch-v1'
GUARDED_SWITCH_CONTROL_FLOW = 'bounded buffer calls with an exact unsigned-guarded local word switch'
NESTED_OUTPUT_SELECTOR = 'bounded-buffer-nested-halfword-output-v1'
NESTED_OUTPUT_SCHEMA = 'elf-symbol-thumb-bounded-buffer-nested-halfword-output-v1'
NESTED_OUTPUT_CONTROL_FLOW = 'bounded buffer calls with native nested formal halfword outputs and retained entry aliases'
THUNK_SELECTOR = 'bounded-buffer-conditional-thunks-v1'
THUNK_SCHEMA = 'elf-symbol-thumb-bounded-buffer-conditional-thunks-v1'
THUNK_CONTROL_FLOW = 'complete named-data owner with typed function words, bounded buffer callees and conditional canonical indirect-call ABI'
THUNK_SCRATCH_SELECTOR = 'bounded-buffer-conditional-thunks-discarded-scratch-v1'
THUNK_SCRATCH_SCHEMA = 'elf-symbol-thumb-bounded-buffer-conditional-thunks-discarded-scratch-v1'
THUNK_SCRATCH_CONTROL_FLOW = 'bounded buffer outputs with proven unobserved R2/R3 returns and conditional canonical indirect-call ABI'
THUNK_PARTIAL_SELECTOR = 'bounded-buffer-conditional-thunks-selective-scratch-v1'
THUNK_PARTIAL_SCHEMA = 'elf-symbol-thumb-bounded-buffer-conditional-thunks-selective-scratch-v1'
THUNK_PARTIAL_CONTROL_FLOW = 'conditional canonical thunks with individually proved dead scratch and retained live pointer aliases'
THUNK_SELECTORS = (THUNK_SELECTOR, THUNK_SCRATCH_SELECTOR, THUNK_PARTIAL_SELECTOR)
THUNK_SCHEMAS = {THUNK_SELECTOR: THUNK_SCHEMA, THUNK_SCRATCH_SELECTOR: THUNK_SCRATCH_SCHEMA, THUNK_PARTIAL_SELECTOR: THUNK_PARTIAL_SCHEMA}
GUARDED_ALIAS_SELECTOR = 'bounded-buffer-guarded-callee-aliases-v1'
GUARDED_ALIAS_SCHEMA = 'elf-symbol-thumb-bounded-buffer-guarded-callee-aliases-v1'
GUARDED_ALIAS_CONTROL_FLOW = 'complete ordinary Thumb owner with guarded bounded-buffer callees and every native return alias retained'
GUARDED_ALIAS_MAX_DEPENDENCIES = 32
ROOT_SWITCH_SELECTOR = 'bounded-buffer-root-guarded-switch-v1'
ROOT_SWITCH_SCHEMA = 'elf-symbol-thumb-bounded-buffer-root-guarded-switch-v1'
ROOT_SWITCH_CONTROL_FLOW = 'complete guarded-switch owner with unchanged bounded ordinary-buffer alias checks'
BIOS_DIV_GUARDED_SELECTOR = 'bounded-buffer-guarded-bios-division-v1'
BIOS_DIV_GUARDED_SCHEMA = 'elf-symbol-thumb-bounded-buffer-guarded-bios-division-v1'
NAMED_THREE_OUTPUT_SELECTOR = 'bounded-buffer-named-three-halfword-output-v1'
NAMED_THREE_OUTPUT_SCHEMA = 'elf-symbol-thumb-bounded-buffer-named-three-halfword-output-v1'
THREE_OUTPUT_SELECTOR = 'bounded-buffer-three-halfword-output-v1'
THREE_OUTPUT_SCHEMA = 'elf-symbol-thumb-bounded-buffer-three-halfword-output-v1'
DYNAMIC_DIV_SELECTOR = 'bounded-buffer-three-output-dynamic-division-v1'
DYNAMIC_DIV_SCHEMA = 'elf-symbol-thumb-bounded-buffer-three-output-dynamic-division-v1'
NESTED_QUERY_SELECTOR = 'conditional-nested-known-query-continuation-v1'
NESTED_QUERY_SCHEMA = 'elf-symbol-thumb-conditional-nested-known-query-continuation-v1'
QUERY_CONTINUATION_SELECTOR = 'conditional-known-list-query-continuation-v1'
QUERY_CONTINUATION_SCHEMA = 'elf-symbol-thumb-conditional-known-list-query-continuation-v1'
KNOWN_LIST_QUERY_SELECTOR = 'conditional-known-list-query-closure-v1'
KNOWN_LIST_QUERY_SCHEMA = 'elf-symbol-thumb-conditional-known-list-query-closure-v1'
KNOWN_QUERY_SELECTOR = 'conditional-known-query-native-closure-v1'
KNOWN_QUERY_SCHEMA = 'elf-symbol-thumb-conditional-known-query-native-closure-v1'
TREE_CALLBACK_SELECTOR = 'conditional-two-word-tree-callback-closure-v1'
TREE_CALLBACK_SCHEMA = 'elf-symbol-thumb-conditional-two-word-tree-callback-closure-v1'
CALLBACK_CLOSURE_SELECTOR = 'conditional-two-word-callback-closure-v1'
CALLBACK_CLOSURE_SCHEMA = 'elf-symbol-thumb-conditional-two-word-callback-closure-v1'
DIRECT_OUTPUT_SELECTOR = 'bounded-buffer-direct-halfword-output-v1'
DIRECT_OUTPUT_SCHEMA = 'elf-symbol-thumb-bounded-buffer-direct-halfword-output-v1'
FINITE_LOOP_SELECTOR = 'conditional-finite-local-word-loops-v1'
SPILLED_LOOP_SELECTOR = 'conditional-finite-spilled-scalar-loops-v1'
FINITE_LOOP_SCHEMA = 'elf-symbol-thumb-conditional-finite-local-word-loops-v1'
SPILLED_LOOP_SCHEMA = 'elf-symbol-thumb-conditional-finite-spilled-scalar-loops-v1'
LOCAL_CALL_SELECTORS = ('conditional-scheduler-descriptor-calls-v1', 'conditional-local-state-iterator-v1')
LOCAL_CALL_SCHEMAS = tuple('elf-symbol-thumb-'+value for value in LOCAL_CALL_SELECTORS)
SELECTORS = (*LOCAL_CALL_SELECTORS, NAMED_THREE_OUTPUT_SELECTOR, SPILLED_LOOP_SELECTOR, FINITE_LOOP_SELECTOR, NESTED_QUERY_SELECTOR, QUERY_CONTINUATION_SELECTOR, THUNK_PARTIAL_SELECTOR, THUNK_SCRATCH_SELECTOR, THUNK_SELECTOR, KNOWN_LIST_QUERY_SELECTOR, KNOWN_QUERY_SELECTOR, TREE_CALLBACK_SELECTOR, CALLBACK_CLOSURE_SELECTOR, DIRECT_OUTPUT_SELECTOR, DYNAMIC_DIV_SELECTOR, THREE_OUTPUT_SELECTOR, FAST_FILL_SELECTOR, BIOS_DIV_GUARDED_SELECTOR, SELECTOR, SCRATCH_SELECTOR, BIOS_SQRT_SELECTOR, BIOS_FILL_SELECTOR, GUARDED_SWITCH_SELECTOR, NESTED_OUTPUT_SELECTOR, ROOT_SWITCH_SELECTOR, GUARDED_ALIAS_SELECTOR, DATAFREE_SELECTOR)
SCHEMAS = (*LOCAL_CALL_SCHEMAS, NAMED_THREE_OUTPUT_SCHEMA, SPILLED_LOOP_SCHEMA, FINITE_LOOP_SCHEMA, NESTED_QUERY_SCHEMA, QUERY_CONTINUATION_SCHEMA, THUNK_PARTIAL_SCHEMA, THUNK_SCRATCH_SCHEMA, THUNK_SCHEMA, KNOWN_LIST_QUERY_SCHEMA, KNOWN_QUERY_SCHEMA, TREE_CALLBACK_SCHEMA, CALLBACK_CLOSURE_SCHEMA, DIRECT_OUTPUT_SCHEMA, DYNAMIC_DIV_SCHEMA, THREE_OUTPUT_SCHEMA, FAST_FILL_SCHEMA, BIOS_DIV_GUARDED_SCHEMA, SCHEMA, SCRATCH_SCHEMA, BIOS_SQRT_SCHEMA, BIOS_FILL_SCHEMA, GUARDED_SWITCH_SCHEMA, NESTED_OUTPUT_SCHEMA, ROOT_SWITCH_SCHEMA, GUARDED_ALIAS_SCHEMA, DATAFREE_SCHEMA)
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


class RootGuardedSwitchBufferProof(NamedDataBufferProof):
    """Authenticate root switch edges without changing buffer or escape rules."""

    def inspect(self, address, data):
        # Reuse only the existing complete instruction/edge inventory. Alias
        # effects are replayed on this object, without scratch projection.
        inspector = GuardedSwitchBufferProof(self.rom, self.mapping, self.index, self.objects)
        instructions, transfers = inspector.inspect(address, data)
        self.records[address] = inspector.records[address]
        if inspector._guarded_switches:
            self.__dict__.setdefault('_root_guarded_callees', {}).update(inspector._guarded_switches)
        return instructions, transfers

    def bind_root(self, data, address, calls, words):
        import owner_admission_profile as owner
        import owner_runtime_profile as operations
        if hasattr(self, '_root_switch'):
            raise ValueError('root switch buffer context is single use')
        validate_owner(data, address, self.rom, self.mapping, self.index)
        refinement = owner.refine(data, address, self.mapping)
        ins, edges, branches, actual_calls, actual_words = graph.graph(data, address, refinement)
        if branches or not calls or calls != actual_calls or words != actual_words or \
                len(refinement['word_switches']) != 1:
            raise ValueError('root buffer requires one exact guarded switch and ordinary calls')
        layout = match.switch_layout(data, address, words)
        operations.verify_operations(ins, edges, address, branches, calls, refinement)
        self._root_switch = (data, address, dict(calls), dict(words))
        self._root_switch_manifest = dict(schema=ROOT_SWITCH_SCHEMA,
            address=address, end=address+len(data), body_sha256=hashlib.sha256(data).hexdigest(),
            switch=layout, partition=graph.partition(data, address, refinement, ins, words),
            calls=[[site-address, target] for site, target in sorted(calls.items())],
            contract='Exact local guarded dispatch edges only. Ordinary buffer bounds, alias joins, '
                'pointer slots and return escape checks remain active. Every reached return restores '
                'R4-R11, SP and the entry return address under the conditional returning ordinary-call ABI. '
                'No initialization, physical readability, nonalias, arithmetic equivalence or termination theorem.',
            **self.identities)

    def root_manifest(self):
        if not hasattr(self, '_root_switch_manifest'):
            raise ValueError('root switch has not been authenticated')
        return dict(self._root_switch_manifest, guarded_callees=[
            record for _, record in sorted(getattr(self, '_root_guarded_callees', {}).items())])


def root_switch_context(proof, data, address, calls, words, data_words):
    if type(proof) is not RootGuardedSwitchBufferProof:
        return False
    if data_words is not None or not hasattr(proof, '_root_switch') or \
            proof._root_switch != (data, address, calls, words):
        raise ValueError('root buffer switch differs from authenticated complete context')
    return True


class ConditionalThunkBufferProof(NamedDataBufferProof):
    """Root-only canonical calls never receive tracked local or return pointers."""

    def bind_root(self, data, address, calls):
        import function_thunk_profile as thunk
        import owner_admission_profile as owner
        if hasattr(self, '_thunk_root'):
            raise ValueError('conditional thunk root context is single use')
        validate_owner(data, address, self.rom, self.mapping, self.index)
        refinement = owner.refine(data, address, self.mapping)
        ins, _, branches, actual_calls, words = graph.graph(data, address, refinement)
        selected = {site: target for site, target in calls.items() if thunk.reserved(target)}
        if branches or words or actual_calls != calls or not selected or any(
                target not in thunk.ALIASES.values() for target in selected.values()):
            raise ValueError('conditional thunks require exact complete root calls')
        self._thunk_root = (address, bytes(data), dict(selected))
        self._thunk_observations = {}
        self._thunk_partition = graph.partition(data, address, refinement, ins, words)
        self._thunk_dependencies = []
        for target in sorted(set(selected.values())):
            name = next(name for name, value in thunk.ALIASES.items() if value == target)
            dependency, = thunk.dependencies([name], self.rom)
            body = match.BufferCallProof.span(self, target)
            validate_owner(body, target, self.rom, self.mapping, self.index)
            if len(body) != 2 or any(int(row['rom'], 16) < target+4 and
                    int(row['end'], 16) > target+2 for row in self.entries):
                raise ValueError('canonical thunk requires its exact indexed BX and separate padding')
            self._thunk_dependencies.append(dependency)

    def check_indirect_target(self, address, aliases, returns, *, site):
        import function_thunk_profile as thunk
        if not thunk.reserved(address):
            return
        if not hasattr(self, '_thunk_root') or self._thunk_root[2].get(site) != address:
            raise ValueError('conditional thunk differs from the authenticated root call site')
        register = match.ARM_REG_R0 + (address-thunk.START)//4
        if register in aliases or register in returns:
            raise ValueError('indirect target carries tracked stack or return provenance')
        if set(returns) & (set(match.CALLER_CLOBBERED) - {match.ARM_REG_LR}):
            raise ValueError('conditional indirect argument carries saved-return provenance')

    def check_call(self, address, aliases, stack, slots=None, *, constants=None,
                   site=None, words=None):
        import function_thunk_profile as thunk
        if not thunk.reserved(address):
            return super().check_call(address, aliases, stack, slots,
                constants=constants, site=site, words=words)
        self.check_indirect_target(address, aliases, (), site=site)
        if slots or words or any(reg in aliases for reg in match.CALLER_CLOBBERED):
            raise ValueError('conditional indirect call excludes local argument aliases and pointer words')
        observation = dict(site=site, target=address,
            target_register=(address-thunk.START)//4,
            preserved_local_registers=[[reg-match.ARM_REG_R0, offset]
                                      for reg, offset in sorted(aliases.items())],
            local_argument_aliases=[], pointer_slots=[], pointer_words=[])
        if site in self._thunk_observations and self._thunk_observations[site] != observation:
            raise ValueError('conditional indirect local preservation context differs between paths')
        self._thunk_observations[site] = observation
        return {}

    def thunk_manifest(self):
        import function_thunk_profile as thunk
        from pathlib import Path
        if not hasattr(self, '_thunk_root') or set(self._thunk_observations) != set(self._thunk_root[2]):
            raise ValueError('conditional thunk policy requires every actual root indirect call')
        address, data, calls = self._thunk_root
        return dict(schema=THUNK_SCHEMA, runtime=thunk.RUNTIME, ABI=thunk.ABI,
            root=address, root_sha256=hashlib.sha256(data).hexdigest(),
            partition=self._thunk_partition,
            contract='conditional compatible returning indirect ARM ABI: target code and '
                'ordinary memory access remain premises; R4-R11 and SP preserved, '
                'caller-clobbered results carry no local or saved-return pointers; '
                'no tracked local pointer is passed in an argument, stack word or target; '
                'no callback body identity, memory effects, physical readability, '
                'initialization, nonalias, numerical or termination theorem',
            dependencies=self._thunk_dependencies,
            source_sha256={name:hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                for name in ('named_data_buffer_profile.py', 'function_thunk_profile.py',
                             'owner_admission_profile.py', 'owner_graph_profile.py',
                             'inert_spin_profile.py', 'analyze.py', 'match.py')},
            observations=[self._thunk_observations[site] for site in sorted(calls)])


def conditional_thunk_replay(proof):
    from conditional_local_buffer_profile import ConditionalLocalBufferProof
    from known_list_query_continuation_profile import KnownListQueryContinuationProof
    from nested_known_query_profile import NestedKnownQueryProof
    return type(proof) in (ConditionalLocalBufferProof, NestedKnownQueryProof, KnownListQueryContinuationProof, ConditionalThunkBufferProof, ConditionalThunkScratchBufferProof,
                           ConditionalThunkSelectiveScratchBufferProof)


class DiscardedReturnScratchProof(NamedDataBufferProof):
    """Project R2/R3 only after checking their complete actual continuation."""

    def __init__(self, rom, mapping, index, objects):
        super().__init__(rom, mapping, index, objects)
        self._consumers = []
        self._scratch_returns = {}

    def check_arguments(self, address, arguments, stack, incoming, protected,
                        *, constants=None, site=None, **context):
        self._consumers.append((address, site))
        try:
            return super().check_arguments(address, arguments, stack, incoming,
                protected, constants=constants, site=site, **context)
        finally:
            self._consumers.pop()

    def normal_return_aliases(self, address, site, aliases):
        scratch = {match.ARM_REG_R0 + 2, match.ARM_REG_R0 + 3}
        projected = {register: offset for register, offset in aliases.items()
                     if register in scratch}
        if not projected:
            return aliases
        if not self._consumers or self._consumers[-1][0] != address:
            raise ValueError('discarded return scratch requires its active exact callee')
        call_site = self._consumers[-1][1]
        if type(call_site) is not int:
            raise ValueError('discarded return scratch requires the actual consumer call site')
        owners = [row for row in self.entries
                  if int(row['rom'], 16) <= call_site < int(row['end'], 16)]
        if len(owners) != 1:
            raise ValueError('discarded return scratch requires one complete consumer')
        consumer = int(owners[0]['rom'], 16)
        data = match.BufferCallProof.span(self, consumer)
        if len(data) > MAX_BYTES:
            raise ValueError('discarded return scratch consumer exceeds bounded owner size')
        validate_owner(data, consumer, self.rom, self.mapping, self.index)
        import owner_admission_profile as owner
        refinement = owner.refine(data, consumer, self.mapping)
        ins, edges, branches, calls, words = graph.graph(data, consumer, refinement)
        if branches or words or calls.get(call_site) != address:
            raise ValueError('discarded return scratch differs from the exact ordinary consumer')
        pending = [(call_site + ins[call_site].size, frozenset(projected))]
        seen = set()
        while pending:
            current, live = pending.pop()
            if (current, live) in seen:
                continue
            seen.add((current, live))
            instruction = ins[current]
            read, written = instruction.regs_access()
            if set(read) & live or current in calls and live:
                raise ValueError('consumer observes discarded return scratch before a killing write')
            live -= set(written)
            pending.extend((target, live) for target in edges[current] if live)
        receipt = dict(address=address, site=site, consumer=consumer,
            call_site=call_site, call_target=address,
            consumer_sha256=hashlib.sha256(data).hexdigest(),
            partition=graph.partition(data, consumer, refinement, ins, words),
            projected=[[register-match.ARM_REG_R0, offset]
                       for register, offset in sorted(projected.items())],
            continuation_states=len(seen))
        self._scratch_returns[json.dumps(receipt, sort_keys=True)] = receipt
        return {register: offset for register, offset in aliases.items()
                if register not in scratch}

    def scratch_manifest(self):
        from local_long_branch_profile import DISCARDED_SCRATCH_SCHEMA, DISCARDED_SCRATCH_CONTRACT
        from pathlib import Path
        import importlib
        producers = ('named_data_buffer_profile', 'owner_admission_profile',
                     'owner_graph_profile', 'analyze', 'inert_spin_profile',
                     'local_long_branch_profile', 'match')
        return dict(schema=DISCARDED_SCRATCH_SCHEMA, registers=[2, 3],
            contract=DISCARDED_SCRATCH_CONTRACT +
                '; every actual consumer path leaves projected values unobserved until '
                'a killing write or normal return; existing bounded alias/effect proof '
                'unchanged; conditional compatible returning ABI only, no memory '
                'initialization, physical readability, nonalias or termination theorem',
            source_sha256={name+'.py': hashlib.sha256(
                Path(importlib.import_module(name).__file__).read_bytes()).hexdigest()
                for name in producers},
            observations=[self._scratch_returns[key] for key in sorted(self._scratch_returns)])


class ConditionalThunkScratchBufferProof(ConditionalThunkBufferProof, DiscardedReturnScratchProof):
    """Compose exact thunk checks with actual consumer scratch nonobservation."""


class ConditionalThunkSelectiveScratchBufferProof(ConditionalThunkScratchBufferProof):
    """Retain observed aliases for normal buffer replay; project only dead ones."""

    def normal_return_aliases(self, address, site, aliases):
        scratch = {match.ARM_REG_R0 + 2, match.ARM_REG_R0 + 3}
        projected = {register: offset for register, offset in aliases.items()
                     if register in scratch}
        if not projected:
            return aliases
        if not self._consumers or self._consumers[-1][0] != address:
            raise ValueError('discarded return scratch requires its active exact callee')
        call_site = self._consumers[-1][1]
        if type(call_site) is not int:
            raise ValueError('discarded return scratch requires the actual consumer call site')
        owners = [row for row in self.entries
                  if int(row['rom'], 16) <= call_site < int(row['end'], 16)]
        if len(owners) != 1:
            raise ValueError('discarded return scratch requires one complete consumer')
        consumer = int(owners[0]['rom'], 16)
        data = match.BufferCallProof.span(self, consumer)
        if len(data) > MAX_BYTES:
            raise ValueError('discarded return scratch consumer exceeds bounded owner size')
        validate_owner(data, consumer, self.rom, self.mapping, self.index)
        import owner_admission_profile as owner
        refinement = owner.refine(data, consumer, self.mapping)
        ins, edges, branches, calls, words = graph.graph(data, consumer, refinement)
        if branches or words or calls.get(call_site) != address:
            raise ValueError('discarded return scratch differs from the exact ordinary consumer')
        pending = [(call_site + ins[call_site].size, frozenset({register}))
                   for register in sorted(projected)]
        seen = set()
        observed = set()
        while pending:
            current, live = pending.pop()
            if (current, live) in seen:
                continue
            if len(seen) >= 4096:
                raise ValueError('selective scratch continuation state budget exceeded')
            seen.add((current, live))
            instruction = ins[current]
            read, written = instruction.regs_access()
            if set(read) & live or current in calls and live:
                observed.update(live)
                continue
            live -= set(written)
            pending.extend((target, live) for target in edges[current] if live)
        retained = {register: offset for register, offset in projected.items()
                    if register in observed}
        projected = {register: offset for register, offset in projected.items()
                     if register not in observed}
        receipt = dict(address=address, site=site, consumer=consumer,
            call_site=call_site, call_target=address,
            consumer_sha256=hashlib.sha256(data).hexdigest(),
            partition=graph.partition(data, consumer, refinement, ins, words),
            projected=[[register-match.ARM_REG_R0, offset]
                       for register, offset in sorted(projected.items())],
            retained=[[register-match.ARM_REG_R0, offset]
                      for register, offset in sorted(retained.items())],
            continuation_states=len(seen))
        self._scratch_returns[json.dumps(receipt, sort_keys=True)] = receipt
        return {register: offset for register, offset in aliases.items()
                if register not in projected}

    def scratch_manifest(self):
        manifest = super().scratch_manifest()
        manifest['selection'] = 'each R2/R3 independently; observed aliases remain tracked'
        manifest['contract'] += ('; observed R2/R3 aliases are retained unchanged for every '
            'ordinary buffer bound, nested call, indirect argument and root return check; '
            'root alias memory accesses are limited to allocated local words, excluding saves')
        return manifest


class GuardedSwitchBufferProof(DiscardedReturnScratchProof):
    """Compose the existing scalar switch CFG and bounded alias replay."""

    def __init__(self, rom, mapping, index, objects):
        super().__init__(rom, mapping, index, objects)
        self._guarded_switches = {}

    def inspect(self, address, data):
        import analyze
        refinement = analyze.refine_function(data, address, json.loads(self.mapping),
            max_bytes=len(data), max_instructions=len(data)//2, rom_end=0x09000000,
            same_owner_long_branches=True, two_constant_word_switch=True)
        switches = refinement['word_switches']
        if not switches:
            return super().inspect(address, data)
        if len(switches) != 1 or switches[0].get('interposed_words', 0) not in (0, 2):
            raise ValueError('buffer switch requires one guarded table with zero or two scalar words')
        two_constants = switches[0].get('interposed_words', 0) == 2
        ins, edges, branches, calls, words = graph.graph(
            data, address, refinement, two_constant_word_switch=two_constants)
        if branches:
            raise ValueError('buffer switch excludes local BL control')
        for destination in calls.values():
            match.function_address_target(f'func_{destination:08X}', self.entries,
                                          address, len(data), len(self.rom))
        # This first pass proves saved-register/SP/return provenance and the
        # exact guarded dispatch. The caller's existing alias replay below
        # independently checks every actual buffer access and nested call.
        instructions = match.verify_leaf_instructions(data, address, True, calls,
            switch_relocations=words, allow_switch_constants=two_constants)
        if set(ins) != {item.address for item in instructions}:
            raise ValueError('buffer switch differs from complete verified instructions')
        partition = graph.partition(data, address, refinement, ins, words)
        transfer = address + switches[0]['dispatch'] + 8
        structure = dict(kind='complete-guarded-buffer-switch-v1',
            switch=switches[0], instructions=len(instructions), partition=partition,
            transfer=transfer, successors=list(edges[transfer]),
            table_words_sha256=hashlib.sha256(b''.join(
                data[offset:offset+4] for offset in sorted(words))).hexdigest())
        self.records[address] = dict(address=address, end=address+len(data), bytes=len(data),
            body_sha256=hashlib.sha256(data).hexdigest(), structure=structure, **self.identities)
        self._guarded_switches[address] = self.records[address]
        return instructions, {transfer: edges[transfer]}

    def guarded_manifest(self):
        from pathlib import Path
        import importlib
        producers = ('named_data_buffer_profile', 'owner_admission_profile',
                     'owner_graph_profile', 'switch_constants_profile', 'analyze',
                     'inert_spin_profile', 'local_long_branch_profile', 'match')
        return dict(schema=GUARDED_SWITCH_SCHEMA,
            contract='one exact unsigned-guarded complete local Thumb word table per '
                'inspected buffer callee, zero or two reached scalar constants; '
                'existing bounded alias accesses, escapes and return provenance '
                'are checked on all actual finite successors; ordinary direct calls '
                'use only conditional compatible returning ABI summaries; no physical '
                'readability, initialization, nonalias, numerical or termination theorem',
            source_sha256={name+'.py': hashlib.sha256(
                Path(importlib.import_module(name).__file__).read_bytes()).hexdigest()
                for name in producers},
            observations=[self._guarded_switches[key] for key in sorted(self._guarded_switches)])


class BiosFillSourceProof(NamedDataBufferProof):
    """Compose the existing root-local source proof without widening callees."""

    def bind_root(self, data, address, calls):
        import bios_cpuset_fill_profile as bios
        if hasattr(self, '_root_fill'):
            raise ValueError('BIOS fill root context is single use')
        self._root_fill = bios.BiosFillProof(data, address, self.rom,
            self.mapping, self.index, calls)

    def check_call(self, address, aliases, stack, slots=None, *, constants=None,
                   site=None, words=None):
        import bios_cpuset_fill_profile as bios
        if address != bios.ADDRESS:
            return super().check_call(address, aliases, stack, slots,
                constants=constants, site=site, words=words)
        if not hasattr(self, '_root_fill') or slots or words or match.ARM_REG_LR in aliases:
            raise ValueError('BIOS fill requires its actual root call without pointer slots or words')
        arguments = {reg:offset for reg,offset in aliases.items()
                     if reg in match.CALLER_CLOBBERED}
        result = self._root_fill.check_call(site, arguments, stack)
        data = self.span(address)
        if data != bios.WRAPPER:
            raise ValueError('BIOS fill requires the exact complete indexed wrapper')
        self.dependencies[address] = data
        self.records[address] = dict(address=address, end=address+len(data), bytes=len(data),
            body_sha256=hashlib.sha256(data).hexdigest(), **self.identities,
            structure=dict(kind=BIOS_FILL_SCHEMA, instructions=2,
                wrapper_hex=data.hex(), conditional_ABI=bios.CONTRACT))
        return result

    def bios_manifest(self):
        import bios_cpuset_fill_profile as bios
        from pathlib import Path
        if not hasattr(self, '_root_fill') or not self._root_fill.observations:
            raise ValueError('BIOS fill source profile requires an actual checked local source')
        return dict(self._root_fill.manifest(), producer_sha256={
            Path(module.__file__).name:hashlib.sha256(Path(module.__file__).read_bytes()).hexdigest()
            for module in (bios, __import__(__name__))})


class BiosSqrtScratchProof(DiscardedReturnScratchProof):
    """An explicit conditional scalar ABI for one exact two-instruction wrapper."""

    wrapper_bytes = b'\x08\xdf\x70\x47'
    bios_contract = (
        'conditional compatible BIOS service 8 normal-return ABI: R0 is a scalar '
        'input and scalar result, no memory access or pointer result, R4-R11/SP '
        'are preserved; R1-R3 may be clobbered and must each be killed on every '
        'consumer path before any observation or normal return; no numerical '
        'Sqrt equivalence, BIOS implementation, physical memory, initialization, '
        'nonalias or termination theorem')

    def __init__(self, rom, mapping, index, objects):
        super().__init__(rom, mapping, index, objects)
        self._bios_calls = {}

    def check_arguments(self, address, arguments, stack, incoming, protected,
                        *, constants=None, site=None, **context):
        offset = address - match.ROM_BASE
        prefix = self.rom[offset:offset + 2] if offset >= 0 else b''
        if len(prefix) != 2 or prefix[1] != 0xdf:
            return super().check_arguments(address, arguments, stack, incoming,
                protected, constants=constants, site=site, **context)
        data = self.span(address)
        if data != self.wrapper_bytes:
            raise ValueError('BIOS Sqrt requires exact complete svc #8; bx lr wrapper')
        scratch = {match.ARM_REG_R0 + n for n in (1, 2, 3)}
        if set(arguments) - scratch:
            raise ValueError('BIOS Sqrt requires scalar R0 and excludes control-register aliases')
        if context.get('words'):
            raise ValueError('BIOS Sqrt excludes word-provenance composition')
        # The exact wrapper never reads SP or memory. Incoming pointer slots
        # remain untouched under this explicit memory-free BIOS ABI premise.
        for value in (*arguments.values(), *incoming.values()):
            self.validate_pointer_value(value, stack)
        if type(site) is not int:
            raise ValueError('BIOS Sqrt requires an actual direct consumer call site')
        owners = [row for row in self.entries
                  if int(row['rom'], 16) <= site < int(row['end'], 16)]
        if len(owners) != 1:
            raise ValueError('BIOS Sqrt requires one complete consumer')
        consumer = int(owners[0]['rom'], 16)
        consumer_data = match.BufferCallProof.span(self, consumer)
        if len(consumer_data) > MAX_BYTES:
            raise ValueError('BIOS Sqrt consumer exceeds bounded owner size')
        validate_owner(consumer_data, consumer, self.rom, self.mapping, self.index)
        import owner_admission_profile as owner
        refinement = owner.refine(consumer_data, consumer, self.mapping)
        ins, edges, branches, calls, words = graph.graph(consumer_data, consumer, refinement)
        if branches or words or calls.get(site) != address:
            raise ValueError('BIOS Sqrt differs from the exact ordinary consumer call')
        pending = [(site + ins[site].size, frozenset(scratch))]
        seen = set()
        while pending:
            current, live = pending.pop()
            if (current, live) in seen:
                continue
            if len(seen) >= 4096:
                raise ValueError('BIOS Sqrt continuation state budget exceeded')
            seen.add((current, live))
            instruction = ins[current]
            read, written = instruction.regs_access()
            if set(read) & live or current in calls and live:
                raise ValueError('consumer observes BIOS Sqrt scratch before a killing write')
            live -= set(written)
            if live and not edges[current]:
                raise ValueError('BIOS Sqrt scratch reaches normal return before a killing write')
            pending.extend((target, live) for target in edges[current] if live)
        self.dependencies[address] = data
        self.records[address] = dict(address=address, end=address + len(data),
            bytes=len(data), body_sha256=hashlib.sha256(data).hexdigest(),
            structure=dict(kind='exact-scalar-bios-sqrt-wrapper-v1', instructions=2,
                           bytes_hex=data.hex(), conditional_ABI=self.bios_contract),
            **self.identities)
        receipt = dict(address=address, call_site=site, consumer=consumer,
            consumer_sha256=hashlib.sha256(consumer_data).hexdigest(),
            partition=graph.partition(consumer_data, consumer, refinement, ins, words),
            incoming_aliases=[[r-match.ARM_REG_R0, v] for r, v in sorted(arguments.items())],
            untouched_incoming_slots=sorted(incoming.items()),
            protected_slots=sorted(protected),
            killed_registers=[1, 2, 3], continuation_states=len(seen))
        self._bios_calls[json.dumps(receipt, sort_keys=True)] = receipt
        return self.word_result({}, {})

    def bios_manifest(self):
        from pathlib import Path
        import importlib
        producers = ('named_data_buffer_profile', 'owner_admission_profile',
                     'owner_graph_profile', 'analyze', 'inert_spin_profile',
                     'local_long_branch_profile', 'match')
        return dict(schema='exact-scalar-bios-sqrt-conditional-abi-v1',
            wrapper_hex=self.wrapper_bytes.hex(), contract=self.bios_contract,
            source_sha256={name+'.py': hashlib.sha256(
                Path(importlib.import_module(name).__file__).read_bytes()).hexdigest()
                for name in producers},
            observations=[self._bios_calls[key] for key in sorted(self._bios_calls)])


class GuardedAliasBufferProof(NamedDataBufferProof):
    """Reuse guarded native CFG inventory and preserve ordinary return aliases."""

    dependency_budget = GUARDED_ALIAS_MAX_DEPENDENCIES

    def __init__(self, rom, mapping, index, objects):
        super().__init__(rom, mapping, index, objects)
        self._guarded_switches = {}
        self._entry_kills = {}

    def prefix_kills(self, address, registers):
        """Prove every incoming scratch value dies before any use or call.

        This proves only non-observation of the supplied incoming values.
        The subsequent ordinary call retains the existing conditional returning
        ABI boundary; no callee-local buffer or arbitrary-memory effect is proved.
        """
        scratch = {match.ARM_REG_R0 + 2, match.ARM_REG_R0 + 3}
        if not registers or set(registers) - scratch:
            return None
        data = self.span(address)
        validate_owner(data, address, self.rom, self.mapping, self.index)
        import owner_admission_profile as owner
        refinement = owner.refine(data, address, self.mapping)
        try:
            ins, edges, branches, calls, words = graph.graph(data, address, refinement)
        except ValueError:
            return None
        if branches or words:
            return None
        pending = [(address, frozenset(registers))]
        seen, frontier = set(), set()
        while pending:
            current, live = pending.pop()
            if (current, live) in seen:
                return None  # A cycle before all kills proves no finite prefix.
            if len(seen) >= 4096:
                return None
            seen.add((current, live))
            item = ins[current]
            read, written = item.regs_access()
            if item.size != 2 or current in calls or not edges[current] or set(read) & live or \
                    item.mnemonic not in ('push', 'sub', 'subs', 'add', 'adds',
                        'mov', 'movs', 'ldr', 'ldrh', 'ldrb', 'cmp', 'b', 'beq', 'bne',
                        'bhi', 'bls', 'bge', 'blt', 'bgt', 'ble', 'bhs', 'blo'):
                return None
            remaining = live - set(written)
            if remaining:
                pending.extend((target, remaining) for target in edges[current])
            else:
                frontier.add(current)
        if not frontier:
            return None
        return dict(address=address, end=address+len(data), bytes=len(data),
            body_sha256=hashlib.sha256(data).hexdigest(),
            incoming_registers=[r-match.ARM_REG_R0 for r in sorted(registers)],
            checked_states=[[site, [r-match.ARM_REG_R0 for r in sorted(live)]]
                            for site, live in sorted(seen)],
            killed_frontier=sorted(frontier),
            partition=graph.partition(data, address, refinement, ins, words),
            ordinary_call_boundary='conditional compatible returning ABI after '
                'every incoming scratch pointer is overwritten without a read; '
                'no callee-local or arbitrary-memory effect theorem',
            **self.identities)

    def check_arguments(self, address, arguments, stack, incoming, protected, *,
                        constants=None, site=None, **context):
        if arguments and not incoming and not context.get('words') and not context.get('watched'):
            for offset in arguments.values():
                self.validate_pointer_value(offset, stack)
            killed = self.prefix_kills(address, arguments)
            if killed is not None:
                self.dependencies[address] = self.span(address)
                self.records[address] = dict(killed, structure={'kind': 'incoming-scratch-prefix-overwrite-v1'})
                self._entry_kills[(address, tuple(sorted(arguments)))] = killed
                return self.word_result({}, {})
        return super().check_arguments(address, arguments, stack, incoming, protected,
            constants=constants, site=site, **context)

    def entry_kill_manifest(self):
        return dict(schema='exact-native-scratch-prefix-overwrite-v1',
            observations=[self._entry_kills[key] for key in sorted(self._entry_kills)])

    def inspect(self, address, data):
        # Inventory only; all effects replay on this ordinary alias proof.
        import analyze
        refinement = analyze.refine_function(data, address, json.loads(self.mapping),
            max_bytes=len(data), max_instructions=len(data)//2, rom_end=0x09000000,
            same_owner_long_branches=True, one_object_word_switch=True)
        switches = refinement['word_switches']
        if len(switches) == 1 and switches[0].get('interposed_words') == 1:
            ins, edges, branches, calls, words = graph.graph(data, address, refinement,
                one_object_word_switch=True)
            if branches:
                raise ValueError('one-word guarded buffer excludes local BL control')
            for destination in calls.values():
                match.function_address_target(f'func_{destination:08X}', self.entries,
                    address, len(data), len(self.rom))
            offset = switches[0]['literal'] - 4
            value = struct.unpack_from('<I', data, offset)[0]
            objects = {offset: ('ROM-checked interposed word', value)}
            instructions = match.verify_leaf_instructions(data, address, True, calls,
                switch_relocations=words, switch_data_relocations=objects)
            if set(ins) != {item.address for item in instructions}:
                raise ValueError('one-word guarded buffer differs from complete instructions')
            transfer = address + switches[0]['dispatch'] + 8
            structure = dict(kind='complete-guarded-buffer-switch-one-ROM-word-v1',
                switch=switches[0], instructions=len(instructions),
                partition=graph.partition(data, address, refinement, ins, words),
                transfer=transfer, successors=list(edges[transfer]),
                interposed_ROM_word=dict(offset=offset, value=value,
                    sha256=hashlib.sha256(data[offset:offset+4]).hexdigest()),
                table_words_sha256=hashlib.sha256(b''.join(
                    data[word:word+4] for word in sorted(words))).hexdigest())
            self.records[address] = dict(address=address, end=address+len(data),
                bytes=len(data), body_sha256=hashlib.sha256(data).hexdigest(),
                structure=structure, **self.identities)
            self._guarded_switches[address] = self.records[address]
            return instructions, {transfer: edges[transfer]}
        inspector = GuardedSwitchBufferProof(self.rom, self.mapping, self.index, self.objects)
        instructions, transfers = inspector.inspect(address, data)
        self.records[address] = inspector.records[address]
        self._guarded_switches.update(inspector._guarded_switches)
        return instructions, transfers

    def guarded_manifest(self):
        manifest = GuardedSwitchBufferProof.guarded_manifest(self)
        manifest['contract'] += '; ordinary-alias inventory additionally accepts one '
        manifest['contract'] += 'reached interposed ROM word under the existing exact '
        manifest['contract'] += 'one-object switch parser and complete byte partition; '
        manifest['contract'] += 'the word grants no extent, contents or alias premise'
        return manifest
