"""Explicit ordinary-call inventory with one freshly proved formal-stack output leaf."""
import argparse
import hashlib
import json
from pathlib import Path

from capstone.arm import (ARM_OP_REG, ARM_OP_IMM, ARM_OP_MEM, ARM_REG_R0,
    ARM_REG_R3, ARM_REG_R12, ARM_REG_SP, ARM_REG_LR, ARM_REG_PC,
    ARM_CC_AL, ARM_CC_INVALID)

import analyze
import match
import function_thunk_profile as thunks
import owner_admission_profile as owner
import owner_graph_profile as graph
import owner_runtime_profile as operations
import software_double_profile as indices
import local_long_branch_profile as frame
import local_alias_slot_profile as slots
import zero_index_stack_profile as zero_index
import readonly_entry_stack_words_profile as incoming

SELECTOR = 'ordinary-formal-stack-callee-inventory-v1'
SCHEMA = 'thumb-ordinary-formal-stack-callee-inventory-v1'
EFFECT_SCHEMA = 'thumb-formal-stack-output-leaf-v1'
LEAF = (0x0801CA78, 0x0801CA98, 16,
    'dbde99fd245e7c42708043685bb3836d3d84a6baa034ba92cb9fdd062ac9a273')
NOOP = (0x080A880C, 0x080A880E, 1,
    'c7dfbb7d02759eacb64dbc916c1bb6f21eabaff1c1032ea5c9176abf7fd28df8')
EFFECTS = [[3, 0, 2], [4, 0, 2], [5, 0, 2]]
ENTRY_POLICY = {'schema': incoming.SCHEMA, 'words': [0, 1]}


def sha(value):
    return hashlib.sha256(value).hexdigest()


def text(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def complete(data, address, rom, mapping, index):
    if any(type(value) is not bytes for value in (data, rom, mapping, index)) or type(address) is not int:
        raise ValueError('formal stack inventory requires exact immutable typed inputs')
    owner.validate_span(data, address, rom, mapping, index)
    entries, rows = indices.indices(mapping, index)
    record = indices.span_record(address, address + len(data), entries, rows, rom)
    refinement = owner.refine(data, address, mapping)
    instructions, edges, branches, calls, words = graph.graph(data, address, refinement)
    if record['instrs'] != len(instructions):
        raise ValueError('formal stack inventory requires exact complete dual-index instruction counts')
    if branches or words or refinement['word_switches'] or any(
            item.mnemonic.startswith(('ldm', 'stm')) for item in instructions.values()):
        raise ValueError('formal stack inventory excludes local BL, switches and block transfers')
    operations.verify_operations(instructions, edges, address, branches, calls, refinement)
    partition = graph.partition(data, address, refinement, instructions, words)
    if partition['words']:
        raise ValueError('formal stack inventory excludes materialized literal addresses')
    return instructions, edges, calls, partition


def prove_formal_origins(instructions, edges, address):
    """Exact straight-line leaf transfer; incoming words become pointer formals only here.

    Native frame restoration and the read-only incoming-word contract are proved
    separately. No memory-loaded scalar, arithmetic result or return gains an origin.
    """
    ordered = sorted(instructions)
    if not ordered or ordered[0] != address or set(edges) != set(instructions):
        raise ValueError('formal leaf requires its complete exact CFG')
    origins = {ARM_REG_R3: 3}
    depth, reads, writes, transfers = 0, [], [], []
    for position, site in enumerate(ordered):
        item = instructions[site]
        raw = bytes(item.bytes)
        encoded = int.from_bytes(raw, 'little')
        operands = item.operands
        regs = tuple(op.reg for op in operands if op.type == ARM_OP_REG)
        expected = () if position == len(ordered)-1 else (site+2,)
        if item.size != 2 or len(raw) != 2 or item.cc not in (ARM_CC_AL, ARM_CC_INVALID) or \
                tuple(edges[site]) != expected or position+1 < len(ordered) and ordered[position+1] != site+2:
            raise ValueError('formal leaf requires exact straight-line narrow CFG and final return')
        if item.mnemonic == 'push':
            actual = tuple(ARM_REG_R0+n for n in range(8) if encoded & (1 << n)) + \
                ((ARM_REG_LR,) if encoded & 0x100 else ())
            if encoded & 0xFE00 != 0xB400 or regs != actual or any(reg in origins for reg in regs):
                raise ValueError('formal leaf cannot spill pointer formals or forge push operands')
            depth += len(regs)
        elif item.mnemonic == 'pop':
            actual = tuple(ARM_REG_R0+n for n in range(8) if encoded & (1 << n)) + \
                ((ARM_REG_PC,) if encoded & 0x100 else ())
            if encoded & 0xFE00 != 0xBC00 or regs != actual or len(regs) > depth:
                raise ValueError('formal leaf pop differs from its established frame')
            depth -= len(regs)
            for register in regs:
                origins.pop(register, None)
        elif item.mnemonic == 'ldr':
            offset = incoming.read_word(item, depth, ENTRY_POLICY)
            register = ARM_REG_R0 + ((encoded >> 8) & 7)
            origins[register] = 4 + offset//4
            reads.append([site, offset, 4, register-ARM_REG_R0, raw.hex()])
            transfers.append([site, register-ARM_REG_R0, 4+offset//4, 0])
        elif item.mnemonic == 'strh':
            source, base = ARM_REG_R0+(encoded & 7), ARM_REG_R0+((encoded >> 3) & 7)
            if encoded & 0xF800 != 0x8000 or (encoded >> 6) & 31 or \
                    len(operands) != 2 or operands[0].type != ARM_OP_REG or operands[0].reg != source or \
                    operands[1].type != ARM_OP_MEM or operands[1].mem.base != base or \
                    operands[1].mem.index or operands[1].mem.disp or item.writeback or \
                    operands[1].subtracted or operands[1].shift.type or operands[1].shift.value or \
                    base not in origins or source in origins:
                raise ValueError('formal leaf requires exact halfword writes through proved formals')
            writes.append([origins[base], 0, 2])
        elif item.mnemonic in ('mov', 'movs') and encoded & 0xFC00 == 0x4400 and (encoded >> 8) & 3 == 2:
            destination = ARM_REG_R0 + (encoded & 7) + ((encoded >> 4) & 8)
            source = ARM_REG_R0 + ((encoded >> 3) & 15)
            if len(operands) != 2 or regs != (destination, source) or \
                    any(reg in (ARM_REG_SP, ARM_REG_PC, ARM_REG_LR) for reg in regs):
                raise ValueError('formal leaf copy cannot materialize control or stack origins')
            origin = origins.get(source)
            origins.pop(destination, None)
            if origin is not None:
                origins[destination] = origin
        elif item.mnemonic == 'bx':
            if position != len(ordered)-1 or encoded & 0xFF87 != 0x4700 or regs[0] in origins:
                raise ValueError('formal leaf requires its checked entry-LR return without pointer result facts')
        else:
            # The concrete leaf needs only immediate LSL/ASR and ADD. Every
            # arithmetic write destroys origin; pointer arithmetic is refused.
            allowed = (encoded & 0xF800 in (0x0000, 0x1000, 0x3000) and
                       item.mnemonic in ('lsls', 'asrs', 'adds'))
            read, written = item.regs_access()
            if not allowed or any(register in origins for register in read) or \
                    set(written) & {ARM_REG_SP, ARM_REG_PC, ARM_REG_LR}:
                raise ValueError('formal leaf has unsupported pointer, scalar or memory operation')
            for register in written:
                origins.pop(register, None)
    incoming.validate_reads((row[1] for row in reads), ENTRY_POLICY)
    if depth or sorted(writes) != EFFECTS or len(writes) != 3 or \
            any(register in origins for register in (ARM_REG_R0, ARM_REG_R0+1, ARM_REG_R12, ARM_REG_LR)):
        raise ValueError('formal leaf observed effects or scalar return origins differ')
    return {'schema': EFFECT_SCHEMA, 'reads': [], 'writes': sorted(writes),
        'incoming_pointer_word_reads': reads, 'observed_origin_transfers': transfers,
        'formal_domain': 'arg3 and entry-SP words0/4 as pointer formals4/5; other scalar values unknown',
        'incoming_pointer_contract': 'two readable initialized aligned outgoing caller words contain the authenticated local pointers',
        'allowed_effects': EFFECTS, 'return_argument_facts': []}


class FormalStackCalleeProof:
    """Fresh source-bound leaf proof, consumed only by the explicit frame hook."""
    def __init__(self, data, address, rom, mapping, index, sites):
        if type(sites) is not dict or not sites or any(type(site) is not int or site % 2 or
                type(target) is not int or target != address for site, target in sites.items()):
            raise ValueError('formal leaf requires exact marked call sites and target')
        instructions, edges, calls, partition = complete(data, address, rom, mapping, index)
        if calls:
            raise ValueError('formal output leaf cannot contain nested calls')
        effects = prove_formal_origins(instructions, edges, address)
        restored = frame.prove_frame(instructions, edges, address, {}, {}, entry_stack_policy=ENTRY_POLICY)
        self.sites = dict(sites)
        self._sites = text(sorted(sites.items()))
        self._record = {'schema': EFFECT_SCHEMA, 'address': address, 'end': address+len(data),
            'instructions': len(instructions), 'body_sha256': sha(data), 'ROM_sha256': sha(rom),
            'mapping_sha256': sha(mapping), 'index_sha256': sha(index),
            'native_edges': [[site, list(targets)] for site, targets in sorted(edges.items())],
            'effects': effects, 'frame': restored, 'partition': partition}
        self._seal = sha(text(self._record).encode())
        self._observations = {}

    def validate_calls(self, calls):
        if type(calls) is not dict or text(sorted(self.sites.items())) != self._sites or \
                any(calls.get(site) != target for site, target in self.sites.items()) or \
                sha(text(self._record).encode()) != self._seal or \
                self._record['effects']['writes'] != EFFECTS:
            raise ValueError('formal stack descriptor differs from its fresh body/site/effect proof')

    def check_call(self, site, target, aliases, stack, pointer_slots):
        self.validate_calls({site: target} if len(self.sites) == 1 else self.sites)
        if self.sites.get(site) != target or type(stack) is not list or not stack:
            raise ValueError('unmarked formal stack call or absent caller frame')
        clobbered = {*range(ARM_REG_R0, ARM_REG_R0+4), ARM_REG_R12, ARM_REG_LR}
        if set(aliases) & clobbered != {ARM_REG_R3}:
            raise ValueError('formal stack call requires exactly arg3 local pointer and scalar other arguments')
        def local(offset, width):
            position = offset + 4*len(stack)
            if type(offset) is not int or offset % width or position < 0 or offset+width > 0 or \
                    any(stack[number][0] != 'local' for number in
                        range(position//4, (position+width-1)//4+1)):
                raise ValueError('formal stack effect leaves aligned live local words or overlaps saved slots')
        def exact(values):
            if type(values) is not frozenset or len(values) != 1:
                raise ValueError('formal stack pointer requires one all-path live local origin')
            offset, live = next(iter(values))
            if type(offset) is not int or live is not True:
                raise ValueError('formal stack pointer has missing or expired local origin')
            return offset
        base = -4*len(stack)
        pointers = {3: exact(aliases[ARM_REG_R3])}
        outgoing = []
        for formal, displacement in ((4, 0), (5, 4)):
            offset = base+displacement
            local(offset, 4)
            pointers[formal] = exact(pointer_slots.get(offset))
            outgoing.append([displacement, 4, pointers[formal]])
        writes = [(pointers[formal]+offset, width) for formal, offset, width in self._record['effects']['writes']]
        owned = set()
        for offset, width in writes:
            local(offset, width)
            touched = set(range(offset, offset+width))
            if touched & owned or touched & set(range(base, base+8)):
                raise ValueError('formal stack output overlaps another output or outgoing argument words')
            owned.update(touched)
        self._observations[site] = {'site': site, 'target': target,
            'arg3_entry_SP_offset': pointers[3], 'outgoing_words': outgoing,
            'writes_entry_SP_offsets': [list(row) for row in writes],
            'caller_SP_entry_offset': base,
            'frame_memory_separation': 'callee uses its own saved frame below call SP; proved output accesses lie in caller allocated local bytes at or above call SP',
            'physical_nonalias_claim': False}
        return writes

    def fingerprint(self):
        self.validate_calls(self.sites)
        if set(self._observations) != set(self.sites):
            raise ValueError('formal stack proof did not cover every marked actual call')
        return {'schema': EFFECT_SCHEMA, 'native_leaf': json.loads(text(self._record)),
            'calls': [self._observations[site] for site in sorted(self._observations)],
            'written_abstract_word_facts': 'invalidated for every overlapping actual effect byte',
            'partial_pointer_slot_writes': 'retain unknown/possible-pointer taint; never fabricate a scalar'}


def bind_calls(calls, mapping, address, size, rom_size):
    if type(calls) is not dict or not calls or type(mapping) is not bytes or \
            any(type(value) is not int for value in (address, size, rom_size)) or \
            address % 2 or size <= 0 or not match.ROM_BASE <= address < address+size <= match.ROM_BASE+rom_size:
        raise ValueError('formal stack inventory requires exact ordinary call inputs')
    entries = json.loads(mapping)
    bound = {}
    for site, target in sorted(calls.items()):
        if type(site) is not int or type(target) is not int or site % 2 or not address <= site <= address+size-4 or thunks.reserved(target):
            raise ValueError('formal stack inventory excludes thunks and malformed call boundaries')
        name = f'func_{target:08X}'
        actual = match.function_address_target(name, entries, address, size, rom_size)
        rows = [row for row in entries if int(row['rom'], 16) == actual]
        end = int(rows[0]['end'], 16)
        if not actual < end <= match.ROM_BASE+rom_size or actual < address+size and end > address or any(
                row is not rows[0] and int(row['rom'], 16) < end and int(row['end'], 16) > actual for row in entries):
            raise ValueError('formal stack ordinary target requires unique nonoverlapping complete ownership')
        bound[site] = name
    if list(calls.values()).count(LEAF[0]) != 1 or list(calls.values()).count(NOOP[0]) != 1:
        raise ValueError('formal stack inventory requires exactly one output leaf and one exact noop call')
    return bound


def verify(data, address, rom, mapping, index, calls, bindings, *, selector, manifest=None):
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('formal stack inventory requires its explicit default-off selector')
    instructions, edges, actual_calls, partition = complete(data, address, rom, mapping, index)
    if type(calls) is not dict or calls != actual_calls or type(bindings) is not dict or \
            bindings != bind_calls(calls, mapping, address, len(data), len(rom)):
        raise ValueError('formal stack inventory bindings differ from all actual reached calls')
    entries, rows = indices.indices(mapping, index)
    bodies = {}
    for identity in (LEAF, NOOP):
        start, end, count, digest = identity
        record = indices.span_record(start, end, entries, rows, rom)
        body = rom[start-match.ROM_BASE:end-match.ROM_BASE]
        if record['instrs'] != count or sha(body) != digest or start < address+len(data) and end > address:
            raise ValueError('formal stack callee complete body identity/count differs')
        bodies[start] = body
    leaf_sites = {site: target for site, target in calls.items() if target == LEAF[0]}
    leaf = FormalStackCalleeProof(bodies[LEAF[0]], LEAF[0], rom, mapping, index, leaf_sites)
    noop_instructions, noop_edges, noop_calls, noop_partition = complete(bodies[NOOP[0]], NOOP[0], rom, mapping, index)
    if bodies[NOOP[0]] != b'\x70\x47' or noop_calls:
        raise ValueError('exact noop requires its sole complete BX LR')
    noop_frame = frame.prove_frame(noop_instructions, noop_edges, NOOP[0], {}, {})
    restored = frame.prove_frame(instructions, edges, address, {}, calls,
        stack_aliases=True, local_alias_slot_policy=slots.SELECTOR,
        zero_index_profile=zero_index.SELECTOR, formal_stack_callee_proof=leaf)
    modules = (analyze, match, thunks, owner, graph, operations, indices, frame, slots, zero_index, incoming)
    source_pins = {Path(module.__file__).name: sha(Path(module.__file__).read_bytes()) for module in modules}
    source_pins[Path(__file__).name] = sha(Path(__file__).read_bytes())
    observed = {'schema': SCHEMA, 'selector': SELECTOR, 'inventory_only': True,
        'address': address, 'end': address+len(data), 'instructions': len(instructions),
        'body_sha256': sha(data), 'ROM_sha256': sha(rom), 'mapping_sha256': sha(mapping), 'index_sha256': sha(index),
        'calls': [[site, target, bindings[site]] for site, target in sorted(calls.items())],
        'frame': restored, 'partition': partition,
        'exact_noop': {'address': NOOP[0], 'body_sha256': NOOP[3],
            'call_sites': [site for site, target in calls.items() if target == NOOP[0]],
            'frame': noop_frame, 'partition': noop_partition},
        'component_accounting': {'fresh_formal_leaf_workflows': 1, 'fresh_noop_workflows': 1,
            'fresh_leaf_frames': 1, 'fresh_noop_frames': 1, 'fresh_caller_frames': 1},
        'ordinary_call_premise': 'conditional: every other ordinary callee returns and obeys the existing r4-r11/SP preserving direct-call ABI; its body and memory effects are not proved',
        'output_call_premise': 'entry-SP words0/4 carry the proved live local pointers; actual arg3/formals4/5 halfword writes are discharged into caller abstract locals',
        'complete_native_structural_proof': True, 'source_or_ELF_admission': False,
        'numeric_input_preconditions': [], 'numeric_return_facts': [], 'arithmetic_C_equivalence': False,
        'physical_memory_claim': False, 'memory_safety_claim': False, 'nonescape_claim': False,
        'universal_termination_claim': False,
        'claim': 'complete CFG/partition and reached-return abstract ABI restoration with source-bound formal output effects; ordinary calls remain conditional',
        'producer_source_sha256': source_pins}
    if manifest is not None and text(manifest) != text(observed):
        raise ValueError('formal stack inventory manifest differs from fresh native proof')
    return observed, [instructions[site] for site in sorted(instructions)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile', required=True, choices=(SELECTOR,))
    for name in ('rom', 'mapping', 'index'):
        parser.add_argument('--'+name, required=True, type=Path)
    parser.add_argument('address', type=lambda value: int(value, 16))
    args = parser.parse_args()
    rom, mapping, index = args.rom.read_bytes(), args.mapping.read_bytes(), args.index.read_bytes()
    selected = [row for row in json.loads(mapping) if int(row['rom'], 16) == args.address]
    if len(selected) != 1:
        raise ValueError('formal stack inventory requires one exact caller row')
    data = rom[args.address-match.ROM_BASE:int(selected[0]['end'], 16)-match.ROM_BASE]
    _, _, calls, _ = complete(data, args.address, rom, mapping, index)
    bindings = bind_calls(calls, mapping, args.address, len(data), len(rom))
    result, _ = verify(data, args.address, rom, mapping, index, calls, bindings, selector=args.profile)
    print(text(result))


if __name__ == '__main__':
    main()
