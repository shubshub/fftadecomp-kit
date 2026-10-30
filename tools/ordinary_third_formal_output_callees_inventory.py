"""Default-off ordinary caller composition with a helper-local byte buffer."""
import argparse
import json
from pathlib import Path

from capstone.arm import (ARM_OP_REG, ARM_OP_IMM, ARM_OP_MEM, ARM_REG_R0,
    ARM_REG_SP, ARM_REG_PC, ARM_REG_LR, ARM_REG_R12, ARM_CC_AL, ARM_CC_INVALID)
import ordinary_second_formal_output_callees_inventory as prior

parent, named = prior.parent, prior.named
SELECTOR = 'ordinary-third-formal-output-callees-inventory-v1'
SCHEMA = 'thumb-ordinary-third-formal-output-callees-inventory-v1'
HELPER_SCHEMA = 'thumb-local-byte-buffer-formal-output-leaf-v1'
POLICY_SCHEMA = 'thumb-third-output-readonly-named-bytes-v1'
FIRST = prior.FIRST
THIRD = (0x0801CDA4, 0x0801CE44, 77,
    'd902786b82e03cf9dbf8cbd45ec0c2b8c2a8f54fb5a2953fbf78b7ed11d7515e')
NAME, GLOBAL = 'data_02007F10', 0x02007F10
READS = [[offset, 1] for offset in (13, 15, 10, 12, 14, 11)]
WRITES = [[formal, 0, 2] for formal in (1, 2, 0, 1, 2)]
FORMAL_READS = [[1, 0, 2], [2, 0, 2]]
READ_PREMISE = ('conditional: the named bytes data_02007F10 at offsets 13/15/10/12/14/11 '
    'are initialized and readable at each reached load; values remain unknown; '
    'the helper performs no named writes; no physical nonalias claim')
sha, text = prior.sha, prior.text


def encoded_register(number):
    return ARM_REG_R0 + number if number < 13 else (ARM_REG_SP, ARM_REG_LR, ARM_REG_PC)[number - 13]


def third_named_policy():
    return dict(schema=POLICY_SCHEMA, symbol=NAME, reads=[list(row) for row in READS],
                readable=True, initialized=True)


def validate_policy(policy, data_mapping):
    if type(policy) is not dict or set(policy) != set(third_named_policy()) or \
            policy != third_named_policy() or type(policy['schema']) is not str or \
            type(policy['symbol']) is not str or type(policy['reads']) is not list or \
            any(type(row) is not list or any(type(value) is not int for value in row) for row in policy['reads']) or \
            policy['readable'] is not True or policy['initialized'] is not True or type(data_mapping) is not bytes:
        raise ValueError('third output requires its distinct exact typed named-byte premise')
    if parent.match.parse_data_symbols(data_mapping).get(NAME) != GLOBAL:
        raise ValueError('third output requires its exact existing named data binding')


def complete_third(data, address, rom, mapping, index):
    if any(type(value) is not bytes for value in (data, rom, mapping, index)) or type(address) is not int or \
            address != THIRD[0] or data != prior.exact_body(THIRD, rom, mapping, index):
        raise ValueError('third output requires its actual complete immutable mapped helper body')
    parent.owner.validate_span(data, address, rom, mapping, index)
    refinement = parent.owner.refine(data, address, mapping)
    instructions, edges, branches, calls, words = parent.graph.graph(data, address, refinement)
    if len(instructions) != THIRD[2] or branches or calls or words or refinement['word_switches']:
        raise ValueError('third output requires its complete call-free CFG')
    parent.operations.verify_operations(instructions, edges, address, branches, calls, refinement)
    partition = parent.graph.partition(data, address, refinement, instructions, words)
    if partition['code_bytes'] != 2 * THIRD[2] or partition['literal_and_table_bytes'] != 4 or \
            partition['alignment_bytes'] != 2 or partition['alignment'] != [[address + 2 * THIRD[2], address + 2 * THIRD[2] + 2]] or \
            len(partition['words']) != 1:
        raise ValueError('third output requires its exact code, zero alignment and literal partition')
    return instructions, edges, partition


def prove_local_origins(instructions, edges, address, data, partition, data_mapping, policy):
    """Track local byte initialization and formal origins separately from frame proof."""
    validate_policy(policy, data_mapping)
    ordered = sorted(instructions)
    if not ordered or ordered[0] != address or set(edges) != set(instructions):
        raise ValueError('third output requires its complete straight-line CFG')
    literal = partition['words'][0]
    if literal['value'] != GLOBAL or literal['switch_word'] or len(literal['load_sites']) != 1:
        raise ValueError('third output named literal ownership/value differs')
    origins = {ARM_REG_R0 + number: ('formal', number) for number in range(3)}
    constants, stack, initialized, formal_initialized = {}, [], set(), set()
    reads, writes, local_reads, local_writes, loads = [], [], [], [], []
    formal_reads = []

    def local(offset, width):
        position = offset + 4 * len(stack)
        if offset % width or position < 0 or offset + width > 0 or any(
                stack[slot] != 'local' for slot in range(position // 4, (position + width - 1) // 4 + 1)):
            raise ValueError('third output local access leaves live allocated bytes')

    def assign(register, origin=None, constant=None):
        origins.pop(register, None)
        constants.pop(register, None)
        if origin is not None:
            origins[register] = origin
        if constant is not None:
            constants[register] = constant

    for position, site in enumerate(ordered):
        item = instructions[site]
        raw = bytes(item.bytes)
        encoded = int.from_bytes(raw, 'little')
        ops = item.operands
        regs = tuple(op.reg for op in ops if op.type == ARM_OP_REG)
        expected = () if position == len(ordered) - 1 else (site + 2,)
        if item.size != 2 or len(raw) != 2 or item.cc not in (ARM_CC_AL, ARM_CC_INVALID) or \
                tuple(edges[site]) != expected or position + 1 < len(ordered) and ordered[position + 1] != site + 2:
            raise ValueError('third output requires exact straight-line narrow instructions')
        if item.mnemonic in ('push', 'pop'):
            push = item.mnemonic == 'push'
            actual = tuple(ARM_REG_R0 + number for number in range(8) if encoded & (1 << number)) + \
                (((ARM_REG_LR if push else ARM_REG_PC),) if encoded & 0x100 else ())
            if encoded & 0xFE00 != (0xB400 if push else 0xBC00) or regs != actual or \
                    push and any(reg in origins for reg in regs) or \
                    not push and (len(regs) > len(stack) or any(kind != 'saved' for kind in stack[:len(regs)])):
                raise ValueError('third output cannot spill pointer origins or forge saved-frame operations')
            if push:
                stack[:0] = ['saved'] * len(regs)
            else:
                del stack[:len(regs)]
                for register in regs:
                    assign(register)
        elif item.mnemonic in ('sub', 'add') and encoded & 0xFF00 == 0xB000:
            amount = 4 * (encoded & 0x7F)
            subtract = bool(encoded & 0x80)
            if not amount or len(ops) != 2 or ops[0].type != ARM_OP_REG or ops[0].reg != ARM_REG_SP or \
                    ops[1].type != ARM_OP_IMM or ops[1].imm != amount or item.mnemonic != ('sub' if subtract else 'add'):
                raise ValueError('third output stack adjustment differs from its exact encoding')
            if subtract:
                stack[:0] = ['local'] * (amount // 4)
            else:
                if amount // 4 > len(stack) or any(kind != 'local' for kind in stack[:amount // 4]):
                    raise ValueError('third output deallocation overlaps saved frame')
                del stack[:amount // 4]
                initialized = {offset for offset in initialized if offset >= -4 * len(stack)}
                for register, origin in list(origins.items()):
                    if origin[0] == 'local' and origin[1] < -4 * len(stack):
                        assign(register)
        elif item.mnemonic == 'ldr' and encoded & 0xF800 == 0x4800:
            destination = ARM_REG_R0 + ((encoded >> 8) & 7)
            target = ((site + 4) & ~3) + 4 * (encoded & 255)
            if len(ops) != 2 or ops[0].type != ARM_OP_REG or ops[0].reg != destination or \
                    ops[1].type != ARM_OP_MEM or ops[1].mem.base != ARM_REG_PC or ops[1].mem.index or \
                    ops[1].mem.disp != 4 * (encoded & 255) or target != literal['address'] or \
                    literal['load_sites'] != [site] or int.from_bytes(data[target-address:target-address+4], 'little') != GLOBAL:
                raise ValueError('third output requires the exact owned named-literal load')
            assign(destination, ('named', NAME))
            loads.append([site, target, NAME, GLOBAL, raw.hex()])
        elif item.mnemonic in ('ldrb', 'strb', 'ldrh', 'strh'):
            load = item.mnemonic.startswith('ldr')
            width = 1 if item.mnemonic.endswith('b') else 2
            opcode = {('ldrb'): 0x7800, ('strb'): 0x7000, ('ldrh'): 0x8800, ('strh'): 0x8000}[item.mnemonic]
            register, base = ARM_REG_R0 + (encoded & 7), ARM_REG_R0 + ((encoded >> 3) & 7)
            offset = width * ((encoded >> 6) & 31)
            if encoded & 0xF800 != opcode or len(ops) != 2 or ops[0].type != ARM_OP_REG or ops[0].reg != register or \
                    ops[1].type != ARM_OP_MEM or ops[1].mem.base != base or ops[1].mem.index or \
                    ops[1].mem.disp != offset or item.writeback or ops[1].subtracted or ops[1].shift.type or ops[1].shift.value:
                raise ValueError('third output requires exact immediate byte/halfword memory encodings')
            origin = origins.get(base)
            if origin is None:
                raise ValueError('third output memory access lacks an authenticated origin')
            if not load and register in origins:
                raise ValueError('third output cannot store a pointer origin')
            if origin[0] == 'named':
                if not load or width != 1 or [offset, width] not in READS:
                    raise ValueError('third output named access exceeds its readonly byte premise')
                reads.append([site, NAME, offset, width, GLOBAL + offset, raw.hex()])
            elif origin[0] == 'local':
                absolute = origin[1] + offset
                local(absolute, width)
                if width != 1:
                    raise ValueError('third output helper-local buffer is byte-only')
                if load:
                    if absolute not in initialized:
                        raise ValueError('third output local byte read precedes initialization')
                    local_reads.append([site, absolute, width, raw.hex()])
                else:
                    initialized.add(absolute)
                    local_writes.append([site, absolute, width, raw.hex()])
            elif origin[0] == 'formal':
                if width != 2 or offset:
                    raise ValueError('third output formal access differs from its exact halfword domain')
                formal = origin[1]
                if load:
                    if formal not in formal_initialized:
                        raise ValueError('third output formal read precedes its own proved write')
                    formal_reads.append([site, formal, offset, width, raw.hex()])
                else:
                    formal_initialized.add(formal)
                    writes.append([site, formal, offset, width, raw.hex()])
            else:
                raise ValueError('third output has an unsupported memory origin')
            if load:
                assign(register)
        elif item.mnemonic in ('mov', 'movs') and encoded & 0xFC00 == 0x4400 and (encoded >> 8) & 3 == 2:
            destination = encoded_register((encoded & 7) + ((encoded >> 4) & 8))
            source = encoded_register((encoded >> 3) & 15)
            if len(ops) != 2 or regs != (destination, source) or destination in (ARM_REG_SP, ARM_REG_PC, ARM_REG_LR) or \
                    source in (ARM_REG_PC, ARM_REG_LR):
                raise ValueError('third output copy cannot forge stack/control origins')
            origin = ('local', -4 * len(stack)) if source == ARM_REG_SP else origins.get(source)
            assign(destination, origin, constants.get(source))
        elif item.mnemonic in ('mov', 'movs') and encoded & 0xF800 == 0x2000:
            destination, value = ARM_REG_R0 + ((encoded >> 8) & 7), encoded & 255
            if len(ops) != 2 or regs != (destination,) or ops[1].type != ARM_OP_IMM or ops[1].imm != value:
                raise ValueError('third output constant differs from its exact immediate encoding')
            assign(destination, constant=value)
        elif item.mnemonic == 'add' and encoded & 0xF800 == 0xA800:
            destination, offset = ARM_REG_R0 + ((encoded >> 8) & 7), 4 * (encoded & 255)
            if len(ops) != 3 or regs != (destination, ARM_REG_SP) or ops[2].type != ARM_OP_IMM or ops[2].imm != offset:
                raise ValueError('third output SP-relative origin differs from its exact encoding')
            assign(destination, ('local', -4 * len(stack) + offset))
        elif item.mnemonic == 'add' and encoded & 0xFC00 == 0x4400 and (encoded >> 8) & 3 == 0:
            destination = encoded_register((encoded & 7) + ((encoded >> 4) & 8))
            source = encoded_register((encoded >> 3) & 15)
            if regs != (destination, ARM_REG_SP, destination) or source != ARM_REG_SP or \
                    destination not in constants or constants[destination] not in (1, 2, 3):
                raise ValueError('third output small SP alias lacks its exact initialized constant')
            assign(destination, ('local', -4 * len(stack) + constants[destination]))
        elif item.mnemonic == 'adds' and encoded & 0xF800 == 0x3000 and ARM_REG_R0 + ((encoded >> 8) & 7) in origins:
            destination, offset = ARM_REG_R0 + ((encoded >> 8) & 7), encoded & 255
            if len(ops) != 2 or regs != (destination,) or ops[1].type != ARM_OP_IMM or ops[1].imm != offset or \
                    origins[destination][0] != 'local':
                raise ValueError('third output pointer arithmetic requires a bounded local byte origin')
            absolute = origins[destination][1] + offset
            local(absolute, 1)
            assign(destination, ('local', absolute))
        elif item.mnemonic == 'bx':
            if position != len(ordered) - 1 or encoded & 0xFF87 != 0x4700 or not regs or regs[0] in origins:
                raise ValueError('third output requires its restored scalar entry-LR return')
        else:
            allowed = item.mnemonic in ('lsls', 'asrs', 'adds', 'subs') and encoded & 0xF800 in (
                0x0000, 0x1000, 0x1800, 0x3000, 0x3800)
            read, written = item.regs_access()
            if not allowed or any(register in origins for register in read) or set(written) & {ARM_REG_SP, ARM_REG_PC, ARM_REG_LR}:
                raise ValueError('third output has unsupported pointer/scalar operation')
            for register in written:
                assign(register)
    if stack or [[row[2], row[3]] for row in reads] != READS or [row[1:4] for row in writes] != WRITES or \
            [row[1:4] for row in formal_reads] != FORMAL_READS or len(loads) != 1:
        raise ValueError('third output observed frame/reads/writes differ from the exact effect policy')
    return dict(schema=HELPER_SCHEMA, reads=[], writes=[[formal, 0, 2] for formal in range(3)],
        store_events=writes, store_event_count=len(writes), unique_write_footprints=3,
        formal_reads_after_own_writes=formal_reads, local_byte_reads=local_reads, local_byte_writes=local_writes,
        named_reads=reads, typed_literal_loads=loads, readonly_named_buffer_policy=policy,
        named_loaded_values='unknown scalars', named_read_premise=READ_PREMISE,
        return_argument_facts=[], physical_nonalias_claim=False)


class LocalByteOutputLeafProof:
    def __init__(self, data, address, rom, mapping, index, data_mapping, sites, policy):
        if type(sites) is not dict or len(sites) != 1 or any(type(site) is not int or site % 2 or \
                type(target) is not int or target != address for site, target in sites.items()):
            raise ValueError('third output proof requires its one exact call site')
        instructions, edges, partition = complete_third(data, address, rom, mapping, index)
        effects = prove_local_origins(instructions, edges, address, data, partition, data_mapping, policy)
        restored = parent.frame.prove_frame(instructions, edges, address, {}, {}, stack_aliases=True,
                                             local_alias_slot_policy=parent.slots.SELECTOR)
        self.sites = dict(sites)
        self._sites = text(sorted(sites.items()))
        self._observations = {}
        self._record = dict(schema=HELPER_SCHEMA, address=address, end=address + len(data),
            instructions=len(instructions), body_sha256=sha(data), ROM_sha256=sha(rom),
            mapping_sha256=sha(mapping), index_sha256=sha(index), data_mapping_sha256=sha(data_mapping),
            partition=partition, effects=effects, frame=restored)
        self._seal = sha(text(self._record).encode())

    def validate_calls(self, calls):
        if text(sorted(self.sites.items())) != self._sites or any(calls.get(site) != target for site, target in self.sites.items()) or \
                sha(text(self._record).encode()) != self._seal:
            raise ValueError('third output descriptor differs from its fresh native body/effect proof')

    def check_call(self, site, target, aliases, stack, pointer_slots):
        self.validate_calls({site: target})
        if self.sites.get(site) != target or type(stack) is not list or not stack:
            raise ValueError('unmarked third output call or missing live caller frame')
        required = {ARM_REG_R0 + number for number in range(3)}
        if set(aliases) & {*range(ARM_REG_R0, ARM_REG_R0 + 4), ARM_REG_R12, ARM_REG_LR} != required:
            raise ValueError('third output requires exactly arg0/arg1/arg2 live local pointers')
        base = -4 * len(stack)
        writes, occupied = [], set()
        for formal in range(3):
            values = aliases[ARM_REG_R0 + formal]
            if type(values) is not frozenset or len(values) != 1:
                raise ValueError('third output requires one all-path local origin per formal')
            origin, live = next(iter(values))
            position = origin - base if type(origin) is int else -1
            if type(origin) is not int or live is not True or origin % 2 or position < 8 or origin + 2 > 0 or any(
                    stack[number][0] != 'local' for number in range(position // 4, (position + 1) // 4 + 1)):
                raise ValueError('third output leaves aligned live locals or overlaps outgoing/saved words')
            domain = set(range(origin, origin + 2))
            if occupied & domain:
                raise ValueError('third output formal halfword domains overlap')
            occupied |= domain
            writes.append((origin, 2))
        self._observations[site] = dict(site=site, target=target, caller_SP_entry_offset=base,
            writes_entry_SP_offsets=[list(row) for row in writes], physical_nonalias_claim=False,
            separation='fresh helper locals and saved frame below call SP; formal accesses in caller locals above outgoing words')
        return writes

    def fingerprint(self):
        self.validate_calls(self.sites)
        if set(self._observations) != set(self.sites):
            raise ValueError('third output proof did not cover every marked call')
        return dict(schema=HELPER_SCHEMA, native_leaf=json.loads(text(self._record)),
                    calls=[self._observations[site] for site in sorted(self._observations)])


class ThirdFormalOutputCalleesProof:
    def __init__(self, first_data, third_data, rom, mapping, index, data_mapping, calls, first_policy, third_policy):
        if first_data != prior.exact_body(FIRST, rom, mapping, index) or third_data != prior.exact_body(THIRD, rom, mapping, index):
            raise ValueError('third-output pair requires both actual canonical mapped helper bodies')
        first_sites = {site: target for site, target in calls.items() if target == FIRST[0]}
        third_sites = {site: target for site, target in calls.items() if target == THIRD[0]}
        if len(first_sites) != 1 or len(third_sites) != 1:
            raise ValueError('third-output pair requires exactly one call to each fresh helper')
        self._first = named.NamedReadonlyFormalLeafProof(first_data, FIRST[0], rom, mapping, index,
                                                        data_mapping, first_sites, first_policy)
        self._third = LocalByteOutputLeafProof(third_data, THIRD[0], rom, mapping, index,
                                               data_mapping, third_sites, third_policy)
        self.sites = first_sites | third_sites
        self._sites = text(sorted(self.sites.items()))

    def validate_calls(self, calls):
        if type(self._first) is not named.NamedReadonlyFormalLeafProof or type(self._third) is not LocalByteOutputLeafProof or \
                text(sorted(self.sites.items())) != self._sites or set(self.sites) != set(self._first.sites) | set(self._third.sites):
            raise ValueError('third-output pair differs from its exact fresh children')
        self._first.validate_calls(calls)
        self._third.validate_calls(calls)

    def check_call(self, site, target, aliases, stack, pointer_slots):
        self.validate_calls(self.sites)
        if self.sites.get(site) != target:
            raise ValueError('unmarked third-output pair call or target')
        child = self._first if site in self._first.sites else self._third
        return child.check_call(site, target, aliases, stack, pointer_slots)

    def fingerprint(self):
        self.validate_calls(self.sites)
        return dict(schema=SCHEMA, callees=[self._first.fingerprint(), self._third.fingerprint()],
                    physical_nonalias_claim=False)


def bind_calls(calls, mapping, address, size, rom_size):
    bound = prior.leaf.bind_calls(calls, mapping, address, size, rom_size)
    if list(calls.values()).count(THIRD[0]) != 1:
        raise ValueError('third-output inventory requires one actual local-byte helper call')
    return bound


def verify(data, address, rom, mapping, index, data_mapping, calls, bindings, *, selector,
           readonly_named_buffer_policy=None, readonly_third_named_buffer_policy=None, manifest=None):
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('third-output inventory requires its explicit default-off selector')
    named.validate_named_policy(readonly_named_buffer_policy, data_mapping)
    validate_policy(readonly_third_named_buffer_policy, data_mapping)
    instructions, edges, actual_calls, partition = parent.complete(data, address, rom, mapping, index)
    if type(calls) is not dict or calls != actual_calls or type(bindings) is not dict or \
            bindings != bind_calls(calls, mapping, address, len(data), len(rom)):
        raise ValueError('third-output bindings differ from all actual reached calls')
    bodies = {}
    for identity in (FIRST, THIRD):
        start, end, _, _ = identity
        if start < address + len(data) and end > address:
            raise ValueError('third-output helper overlaps caller')
        bodies[start] = prior.exact_body(identity, rom, mapping, index)
    proof = ThirdFormalOutputCalleesProof(bodies[FIRST[0]], bodies[THIRD[0]], rom, mapping, index, data_mapping,
        calls, readonly_named_buffer_policy, readonly_third_named_buffer_policy)
    restored = parent.frame.prove_frame(instructions, edges, address, {}, calls, stack_aliases=True,
        local_alias_slot_policy=parent.slots.SELECTOR, zero_index_profile=parent.zero_index.SELECTOR,
        formal_stack_callee_proof=proof)
    modules = (prior, prior.leaf, named, parent, parent.analyze, parent.match, parent.thunks, parent.owner,
               parent.graph, parent.operations, parent.indices, parent.frame, parent.slots, parent.zero_index, parent.incoming)
    source = {Path(module.__file__).name: sha(Path(module.__file__).read_bytes()) for module in modules}
    source[Path(__file__).name] = sha(Path(__file__).read_bytes())
    observed = dict(schema=SCHEMA, selector=SELECTOR, inventory_only=True, address=address, end=address + len(data),
        instructions=len(instructions), body_sha256=sha(data), ROM_sha256=sha(rom), mapping_sha256=sha(mapping),
        index_sha256=sha(index), data_mapping_sha256=sha(data_mapping), partition=partition, frame=restored,
        calls=[[site, target, bindings[site]] for site, target in sorted(calls.items())],
        readonly_named_buffer_policy=readonly_named_buffer_policy, readonly_third_named_buffer_policy=readonly_third_named_buffer_policy,
        named_loaded_values='unknown scalars', named_read_premises=[named.READ_PREMISE, READ_PREMISE],
        ordinary_call_premise='conditional: every other ordinary callee returns and obeys the existing r4-r11/SP preserving ABI; its body and memory effects remain unproved',
        complete_native_structural_proof=True, complete_argument_effect_proof=True, producer_source_sha256=source,
        numeric_input_preconditions=[], numeric_return_facts=[], source_or_ELF_admission=False,
        arithmetic_C_equivalence=False, physical_memory_claim=False, memory_safety_claim=False,
        nonescape_claim=False, universal_termination_claim=False)
    if manifest is not None and text(manifest) != text(observed):
        raise ValueError('third-output manifest differs from fresh native proof')
    return observed, [instructions[site] for site in sorted(instructions)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile', required=True, choices=(SELECTOR,))
    for name in ('rom', 'mapping', 'index', 'data-mapping'):
        parser.add_argument('--' + name, required=True, type=Path)
    parser.add_argument('--readonly-named-buffer-policy', required=True, type=json.loads)
    parser.add_argument('--readonly-third-named-buffer-policy', required=True, type=json.loads)
    parser.add_argument('address', type=lambda value: int(value, 16))
    args = parser.parse_args()
    rom, mapping, index, data_mapping = (args.rom.read_bytes(), args.mapping.read_bytes(),
                                       args.index.read_bytes(), args.data_mapping.read_bytes())
    rows = [row for row in json.loads(mapping) if int(row['rom'], 16) == args.address]
    if len(rows) != 1:
        raise ValueError('third-output inventory requires one exact caller row')
    data = rom[args.address-parent.match.ROM_BASE:int(rows[0]['end'], 16)-parent.match.ROM_BASE]
    _, _, calls, _ = parent.complete(data, args.address, rom, mapping, index)
    bindings = bind_calls(calls, mapping, args.address, len(data), len(rom))
    result, _ = verify(data, args.address, rom, mapping, index, data_mapping, calls, bindings,
        selector=args.profile, readonly_named_buffer_policy=args.readonly_named_buffer_policy,
        readonly_third_named_buffer_policy=args.readonly_third_named_buffer_policy)
    print(text(result))


if __name__ == '__main__':
    main()
