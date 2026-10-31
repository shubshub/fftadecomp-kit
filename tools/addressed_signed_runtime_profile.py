"""Explicit source admission for conditional addressed signed-runtime calls.

This authenticates the actual runtime entries and ordinary returning ARM ABI
boundary. It supplies no numeric division/remainder result or domain theorem.
"""
import argparse
from contextvars import ContextVar
import hashlib
import importlib
import json
import os
from pathlib import Path
import platform
import re
import shlex
import shutil
import struct
import subprocess
import sys
import tempfile

import divsi3_profile as quotient
import modsi3_profile as remainder

SELECTOR = 'addressed-signed-runtime-v1'
SCHEMA = 'elf-symbol-thumb-addressed-signed-runtime-v1'
READONLY_SELECTOR = 'addressed-signed-runtime-readonly-word0-v1'
READONLY_SCHEMA = 'elf-symbol-thumb-addressed-signed-runtime-readonly-word0-v1'
READONLY_TWO_SELECTOR = 'addressed-signed-runtime-readonly-two-words-v1'
READONLY_TWO_SCHEMA = 'elf-symbol-thumb-addressed-signed-runtime-readonly-two-words-v1'
DATA_SELECTOR = 'addressed-signed-runtime-data-v1'
DATA_SCHEMA = 'elf-symbol-thumb-addressed-signed-runtime-data-v1'
CALLBACK_SELECTOR = 'addressed-signed-runtime-r2-callback-data-v1'
CALLBACK_SCHEMA = 'elf-symbol-thumb-addressed-signed-runtime-r2-callback-data-v1'
R3_CALLBACK_SELECTOR = 'addressed-signed-runtime-r3-callback-data-v1'
R3_CALLBACK_SCHEMA = 'elf-symbol-thumb-addressed-signed-runtime-r3-callback-data-v1'
CALLBACK_SELECTORS = (CALLBACK_SELECTOR, R3_CALLBACK_SELECTOR)
DATA_SELECTORS = (DATA_SELECTOR, *CALLBACK_SELECTORS)
CALLBACK_ALIAS = '_call_via_r2'
CALLBACK_CONTRACT = ('conditional returning typed source callback via canonical r2; '
                     'r0/r1 are caller arguments, r2 is the target, not a third C formal; '
                     'no callback numeric, buffer, memory or termination equivalence facts')
R3_CALLBACK_CONTRACT = ('conditional returning typed source callback via canonical r3; '
                        'r0/r1/r2 are caller arguments, r3 is the target, not a fourth C formal; '
                        'no callback numeric, buffer, memory or termination equivalence facts')
DATA_CONTRACT = ('typed named ABS32 object identity only; no physical readability, '
                 'allocation, pointee type, memory safety or C semantic facts')
SCHEMAS = {SELECTOR: SCHEMA, READONLY_SELECTOR: READONLY_SCHEMA,
            READONLY_TWO_SELECTOR: READONLY_TWO_SCHEMA, DATA_SELECTOR: DATA_SCHEMA,
            CALLBACK_SELECTOR: CALLBACK_SCHEMA, R3_CALLBACK_SELECTOR: R3_CALLBACK_SCHEMA}
OPERATIONS = {'func_081426B8': quotient.ADDRESS, remainder.ADDRESSED_NAME: remainder.ADDRESS}
ABI = 'conditional returning ARM ABI; arbitrary incoming word patterns; no numeric return facts'
_replay = ContextVar('addressed_signed_runtime_replay', default=False)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def text(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def context_selector(context):
    if type(context) is tuple:
        if len(context) == 5:
            return SELECTOR
        if len(context) == 6 and context[5] == READONLY_SELECTOR:
            return READONLY_SELECTOR
        if len(context) == 6 and type(context[5]) is str and context[5] == READONLY_TWO_SELECTOR:
            return READONLY_TWO_SELECTOR
        if len(context) == 8 and type(context[5]) is str and context[5] in DATA_SELECTORS:
            return context[5]
    raise ValueError('addressed signed runtimes require an exact explicit context')


def object_value(name, addend, objects, entries, address, size):
    """The existing typed-data addend boundary, excluding code-as-data aliases."""
    import match
    if name not in objects or type(addend) is not int or not -0x80000000 <= addend <= 0x7FFFFFFF:
        raise ValueError('addressed data requires a mapped object and signed32 addend')
    base = objects[name]
    value = base + addend
    if not 0 <= value <= 0xFFFFFFFF or address <= value < address + size or \
            any(match.function_thunk.reserved(target) for target in (base, value)) or any(
            int(row['rom'], 16) <= (target & ~1) < int(row['end'], 16)
            for row in entries for target in (base, value)):
        raise ValueError('addressed data overflows or aliases indexed code')
    return value


def data_literals(data, address, rom, mapping, objects, records):
    import match
    if type(objects) is not bytes or type(records) is not list or not records:
        raise ValueError('addressed data requires an actual typed data snapshot and bindings')
    # Calls are authenticated separately by prepare; do not send reserved runtime
    # names through the ordinary function-address validator.
    calls, literals = match.function_address_bindings(data, address, rom, mapping, objects,
        {'calls': [], 'data': records, 'functions': []}, allow_empty_functions=True)
    parsed, entries = match.parse_data_symbols(objects), json.loads(mapping)
    for offset, name, addend in records:
        value = object_value(name, addend, parsed, entries, address, len(data))
        if literals[offset] != (name, value):
            raise ValueError('addressed data lost its typed object identity')
    if calls:
        raise ValueError('addressed data cannot introduce function bindings')
    return literals


def data_producer_fingerprint():
    """Pin the actual data admission, linker, CFG and source-replay producers."""
    import match
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    import local_long_branch_profile as frame
    modules = (match, owner, graph, frame, quotient, remainder, match.function_thunk,
               match.software_double, match.software_float, match.ashldi3, match.umodsi3)
    paths = {Path(module.__file__) for module in modules} | {Path(__file__)}
    paths.update(Path(importlib.import_module(name).__file__) for name in
                 ('match_evidence', 'inert_spin_profile', 'analyze', 'plausible'))
    return {path.name: sha(path.read_bytes()) for path in sorted(paths)}


def callback_alias(selector):
    return '_call_via_r3' if selector == R3_CALLBACK_SELECTOR else CALLBACK_ALIAS


def callback_dependencies(rom, mapping, index, selector=CALLBACK_SELECTOR):
    """Reuse canonical thunk identity, with its actual two-byte indexed owner."""
    import match
    import owner_admission_profile as owner
    alias = callback_alias(selector)
    target = match.function_thunk.ALIASES[alias]
    offset = target - match.ROM_BASE
    owner.validate_span(rom[offset:offset+2], target, rom, mapping, index)
    return match.function_thunk.dependencies([alias], rom)


def callback_r0_slot(instructions, edges, reverse, calls, site, address, bindings):
    """One closed R0 slot load, then two explicit register argument assignments."""
    import match
    chain, cursor = [], site
    for _ in range(4):
        if len(reverse[cursor]) != 1:
            return None
        previous = next(iter(reverse[cursor]))
        item = instructions[previous]
        if item.size != 2 or previous + item.size != cursor or \
                edges[previous] != (cursor,) or previous in calls:
            return None
        chain.append(item)
        cursor = previous
    literal_load, slot_load, arg0, arg1 = reversed(chain)

    def register(operand, value):
        return operand.type == match.ARM_OP_REG and operand.reg == value

    def memory(operand, base):
        return operand.type == match.ARM_OP_MEM and operand.mem.base == base and \
            not operand.mem.index and not operand.mem.disp

    operands = literal_load.operands
    if literal_load.mnemonic != 'ldr' or len(operands) != 2 or \
            not register(operands[0], match.ARM_REG_R0) or \
            operands[1].type != match.ARM_OP_MEM or \
            operands[1].mem.base != match.ARM_REG_PC or operands[1].mem.index:
        return None
    literal = ((literal_load.address + 4) & ~3) + operands[1].mem.disp - address
    if literal not in bindings or bindings[literal][1] != 0:
        return None
    operands = slot_load.operands
    if slot_load.mnemonic != 'ldr' or len(operands) != 2 or \
            not register(operands[0], match.ARM_REG_R2) or \
            not memory(operands[1], match.ARM_REG_R0):
        return None
    operands = arg0.operands
    if arg0.mnemonic != 'adds' or len(operands) != 3 or \
            not register(operands[0], match.ARM_REG_R0) or \
            operands[1].type != match.ARM_OP_REG or \
            arg0.reg_name(operands[1].reg) not in ('r4', 'r5', 'r6', 'r7') or \
            operands[2].type != match.ARM_OP_IMM or operands[2].imm != 0:
        return None
    source = arg0.reg_name(operands[1].reg)
    operands = arg1.operands
    if arg1.mnemonic != 'movs' or len(operands) != 2 or \
            not register(operands[0], match.ARM_REG_R1) or \
            operands[1].type != match.ARM_OP_IMM or not 0 <= operands[1].imm <= 255:
        return None
    return [site-address, literal_load.address-address, slot_load.address-address,
            literal, bindings[literal][0], dict(policy='r0-slot-zero-argument-setup-v1',
                base_register='r0', target_register='r2', slot_offset=0,
                argument_setup=[dict(offset=arg0.address-address, bytes=arg0.bytes.hex(),
                                     destination='r0', source=source),
                                dict(offset=arg1.address-address, bytes=arg1.bytes.hex(),
                                     destination='r1', immediate=operands[1].imm)])]


def callback_sites(instructions, edges, calls, address, records):
    """Require an unambiguous straight-line mapped slot-zero load into r2."""
    import match
    target = match.function_thunk.ALIASES[CALLBACK_ALIAS]
    reverse = {site: set() for site in instructions}
    for site, successors in edges.items():
        for successor in successors:
            reverse[successor].add(site)
    bindings = {offset: (name, addend) for offset, name, addend in records}
    result = []
    for site in sorted(site for site, value in calls.items() if value == target):
        cursor = site
        load = None
        for distance in range(8):
            predecessors = reverse[cursor]
            if len(predecessors) != 1:
                break
            previous = next(iter(predecessors))
            item = instructions[previous]
            if previous + item.size != cursor or edges[previous] != (cursor,) or previous in calls:
                break
            operands = item.operands
            if distance == 0:
                if item.mnemonic != 'ldr' or len(operands) != 2 or \
                        operands[0].type != match.ARM_OP_REG or operands[0].reg != match.ARM_REG_R2 or \
                        operands[1].type != match.ARM_OP_MEM or operands[1].mem.base != match.ARM_REG_R2 or \
                        operands[1].mem.index or operands[1].mem.disp:
                    break
                load = previous
            elif item.mnemonic == 'ldr' and len(operands) == 2 and \
                    operands[0].type == match.ARM_OP_REG and operands[0].reg == match.ARM_REG_R2 and \
                    operands[1].type == match.ARM_OP_MEM and operands[1].mem.base == match.ARM_REG_PC and \
                    not operands[1].mem.index:
                literal = ((previous + 4) & ~3) + operands[1].mem.disp - address
                if literal not in bindings or bindings[literal][1] != 0:
                    break
                result.append([site-address, previous-address, load-address,
                               literal, bindings[literal][0]])
                break
            elif match.ARM_REG_R2 in item.regs_access()[1]:
                break
            cursor = previous
        else:
            raise ValueError('r2 callback exceeds its bounded mapped-load chain')
        if not result or result[-1][0] != site-address:
            row = callback_r0_slot(instructions, edges, reverse, calls, site, address, bindings)
            if row is None:
                raise ValueError('r2 callback requires an unambiguous mapped slot-zero target load')
            result.append(row)
    if not result:
        raise ValueError('callback selector requires its actual canonical callback call')
    return result


def r3_callback_sites(instructions, edges, calls, address, records):
    """Two closed slot-zero producer shapes with three genuine argument inputs."""
    import match
    target = match.function_thunk.ALIASES['_call_via_r3']
    reverse = {site: set() for site in instructions}
    for site, successors in edges.items():
        for successor in successors:
            reverse[successor].add(site)
    bindings = {offset: (name, addend) for offset, name, addend in records}

    def register(operand, name):
        return operand.type == match.ARM_OP_REG and operand.reg == getattr(match, 'ARM_REG_' + name.upper())

    def immediate(operand):
        return operand.type == match.ARM_OP_IMM and 0 <= operand.imm <= 255

    def shape(chain):
        literal_load = chain[0]
        base = 'r0' if len(chain) == 5 else 'r2'
        ops = literal_load.operands
        if literal_load.mnemonic != 'ldr' or len(ops) != 2 or not register(ops[0], base) or \
                ops[1].type != match.ARM_OP_MEM or ops[1].mem.base != match.ARM_REG_PC or ops[1].mem.index:
            return None
        literal = ((literal_load.address + 4) & ~3) + ops[1].mem.disp - address
        if literal not in bindings or bindings[literal][1] != 0:
            return None
        source, slot, dest, size = (chain[1], chain[2], chain[3], chain[4]) if len(chain) == 5 else \
                                   (chain[3], chain[4], chain[1], chain[5])
        ops = source.operands
        if source.mnemonic != 'adds' or len(ops) != 3 or not register(ops[0], 'r1') or \
                ops[1].type != match.ARM_OP_REG or source.reg_name(ops[1].reg) not in ('r4','r5','r6','r7') or \
                not register(ops[2], 'r1'):
            return None
        ops = slot.operands
        if slot.mnemonic != 'ldr' or len(ops) != 2 or not register(ops[0], 'r3') or \
                ops[1].type != match.ARM_OP_MEM or slot.reg_name(ops[1].mem.base) != base or \
                ops[1].mem.index or ops[1].mem.disp:
            return None
        ops = dest.operands
        if dest.mnemonic != 'adds' or len(ops) != 3 or not register(ops[0], 'r0') or \
                ops[1].type != match.ARM_OP_REG or dest.reg_name(ops[1].reg) not in ('r4','r5','r6','r7') or \
                ops[2].type != match.ARM_OP_IMM or ops[2].imm != 0:
            return None
        destination = 0
        if len(chain) == 6:
            increment = chain[2]
            ops = increment.operands
            if increment.mnemonic != 'adds' or len(ops) != 2 or not register(ops[0], 'r0') or \
                    not immediate(ops[1]):
                return None
            destination = ops[1].imm
        ops = size.operands
        if size.mnemonic != 'movs' or len(ops) != 2 or not register(ops[0], 'r2') or not immediate(ops[1]):
            return None
        # Every instruction in the producer is bound. No call, branch join or
        # uninspected argument/target write can occur between these operations.
        return [literal_load.address-address, slot.address-address, literal, bindings[literal][0],
                dict(policy='r3-slot-zero-three-argument-setup-v1', base_register=base,
                     target_register='r3', slot_offset=0, destination_offset=destination,
                     producer_instructions=[dict(offset=item.address-address, bytes=item.bytes.hex())
                                            for item in chain],
                     argument_setup=[dict(offset=item.address-address, bytes=item.bytes.hex())
                                     for item in chain[1:] if item is not slot])]

    result = []
    for site in sorted(site for site, value in calls.items() if value == target):
        chain, cursor, row = [], site, None
        for _ in range(6):
            if len(reverse[cursor]) != 1:
                break
            previous = next(iter(reverse[cursor]))
            item = instructions[previous]
            if item.size != 2 or previous + 2 != cursor or edges[previous] != (cursor,) or previous in calls:
                break
            chain.insert(0, item)
            cursor = previous
            if len(chain) in (5, 6):
                row = shape(chain)
                if row is not None:
                    break
        if row is None:
            raise ValueError('r3 callback requires a bounded unambiguous mapped slot-zero three-argument producer')
        result.append([site-address, *row])
    if not result:
        raise ValueError('r3 callback selector requires an actual canonical callback call')
    return result


def prepare(data, address, calls, context):
    import match
    import owner_admission_profile as owner
    selector = context_selector(context)
    if type(context[3]) is not dict or not context[3] or \
            type(context[4]) is not dict or context[4]:
        raise ValueError('addressed signed runtimes require a fresh exact context')
    rom, mapping, index, bindings, _ = context[:5]
    entries = owner.validate_span(data, address, rom, mapping, index)
    if selector in DATA_SELECTORS:
        data_literals(data, address, rom, mapping, context[6], context[7])
    if selector in CALLBACK_SELECTORS:
        callback_dependencies(rom, mapping, index, selector)
        if match.function_thunk.ALIASES[callback_alias(selector)] not in calls.values():
            raise ValueError('callback selector requires its actual canonical callback call')
    if any(type(site) is not int or type(name) is not str or name not in OPERATIONS or
           calls.get(site) != OPERATIONS[name] for site, name in bindings.items()) or \
            set(bindings) != {site for site, target in calls.items() if target in OPERATIONS.values()}:
        raise ValueError('addressed signed runtimes require complete canonical addressed bindings')
    selected = []
    for module in (quotient, remainder):
        if module.ADDRESS not in {calls[site] for site in bindings}:
            continue
        module.verify_identity(rom, mapping)
        for lo, hi, digest in module.IDENTITIES:
            owner.validate_span(rom[lo-match.ROM_BASE:hi-match.ROM_BASE], lo, rom, mapping, index)
            selected.append([lo, hi, digest])
    for site, target in calls.items():
        if site not in bindings:
            if selector in CALLBACK_SELECTORS and target == match.function_thunk.ALIASES[callback_alias(selector)]:
                continue
            match.function_address_target(f'func_{target:08X}', entries, address, len(data), len(rom))
    return sorted({tuple(row) for row in selected})


def finish(data, address, calls, context, verified, dependencies):
    import match
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    import local_long_branch_profile as frame
    refinement = owner.refine(data, address, context[1])
    instructions, edges, branches, actual_calls, words = graph.graph(data, address, refinement)
    if branches or words or calls != actual_calls or \
            set(instructions) != {item.address for item in verified}:
        raise ValueError('addressed signed runtimes require the exact closed direct-call CFG')
    partition = graph.partition(data, address, refinement, instructions, words)
    selector = context_selector(context)
    if selector in DATA_SELECTORS:
        literals = data_literals(data, address, context[0], context[1], context[6], context[7])
        match.verify_data_literals(instructions.values(), address, literals)
        address_words = {row['address'] - address for row in partition['words']
                         if remainder.address_literal(row['value'])}
        if address_words != set(literals):
            raise ValueError('addressed data requires exact typed coverage of reached address words')
    elif any(remainder.address_literal(row['value']) for row in partition['words']):
        raise ValueError('addressed signed runtimes exclude address literals and data bindings')
    if selector in (READONLY_SELECTOR, READONLY_TWO_SELECTOR):
        if selector == READONLY_TWO_SELECTOR:
            import readonly_entry_stack_words_profile as incoming
            policy = {'schema': incoming.SCHEMA, 'words': [0, 1]}
        else:
            import readonly_entry_stack_profile as incoming
            policy = {'schema': incoming.SCHEMA, 'words': [0]}
        restored = frame.prove_frame(instructions, edges, address, {}, calls,
            entry_stack_policy=policy)
        if not restored['entry_stack']['reads']:
            raise ValueError('addressed readonly ABI requires actual checked incoming reads')
    else:
        restored = frame.prove_frame(instructions, edges, address, {}, calls)
    modules = (match, owner, graph, frame, quotient, remainder)
    if selector in (READONLY_SELECTOR, READONLY_TWO_SELECTOR):
        modules += (incoming,)
    pins = {Path(module.__file__).name: sha(Path(module.__file__).read_bytes()) for module in modules}
    pins[Path(__file__).name] = sha(Path(__file__).read_bytes())
    if selector in DATA_SELECTORS:
        pins = data_producer_fingerprint()
    context[4].update(schema=SCHEMAS[selector], calls=[
        [site-address, callback_alias(selector) if selector in CALLBACK_SELECTORS and
         target == match.function_thunk.ALIASES[callback_alias(selector)] else
         context[3].get(site, f'func_{target:08X}')]
        for site, target in sorted(calls.items())], dependencies=[list(row) for row in dependencies],
        runtime_ABI=ABI, runtime_numeric_return_facts=[], arithmetic_C_equivalence=False,
        original_formal_type_certainty=False,
        ordinary_calls='conditional returning r4-r11/SP preserving ABI only; no transitive callee proof',
        termination='every reached region has a checked return path; universal termination unproved',
        frame=restored, partition=partition, producer_source_sha256=pins)
    if selector in DATA_SELECTORS:
        context[4].update(data_bindings=[list(row) for row in context[7]],
            data_contract=DATA_CONTRACT)
    if selector in CALLBACK_SELECTORS:
        context[4]['callback'] = dict(
            contract=R3_CALLBACK_CONTRACT if selector == R3_CALLBACK_SELECTOR else CALLBACK_CONTRACT,
            sites=(r3_callback_sites if selector == R3_CALLBACK_SELECTOR else callback_sites)(
                instructions, edges, calls, address, context[7]),
            dependencies=callback_dependencies(context[0], context[1], context[2], selector),
            runtime=match.function_thunk.RUNTIME, abi=match.function_thunk.ABI)


def verify(data, address, rom, mapping, index, calls, bindings, manifest=None, *, selector=SELECTOR,
           data_mapping=None, data_bindings=None):
    import match
    if selector not in SCHEMAS:
        raise ValueError('unknown addressed signed runtime selector')
    observed = {}
    context = (rom, mapping, index, bindings, observed)
    if selector in (READONLY_SELECTOR, READONLY_TWO_SELECTOR):
        context += (selector,)
    elif selector in DATA_SELECTORS:
        context += (selector, data_mapping, data_bindings)
    if selector not in DATA_SELECTORS and (data_mapping is not None or data_bindings is not None):
        raise ValueError('typed data requires its separate explicit addressed selector')
    instructions = match.verify_leaf_instructions(data, address, True, calls,
        addressed_signed_runtime_context=context)
    if manifest is not None and text(manifest) != text(observed):
        raise ValueError('addressed signed runtime manifest differs from fresh native verification')
    return observed, instructions


def terminal_alignment(image, symbol):
    """Only the native assembler's two-byte, four-alignment Thumb NOP tail."""
    size = symbol['size']
    padding = image['text'][size:]
    if not padding:
        return
    section = image['sections'][image['text_index']]
    if size <= 0 or size % 4 != 2 or padding != b'\xc0\x46' or symbol['bind'] != 1 or \
            section[1] != 1 or section[2] != 6 or section[3] % 4 or section[4] % 4 or \
            section[5] != len(image['text']) or section[8] != 4 or \
            image['type'] == 1 and section[3] != 0:
        raise ValueError('addressed runtime text has noncanonical terminal alignment')
    for item in image['symbols']:
        if item is symbol or item['section'] != image['text_index']:
            continue
        offset = item['value'] - section[3]
        if not 0 <= offset < size or offset + item['size'] > size:
            raise ValueError('addressed runtime terminal alignment has a symbol owner')


def original_function(image, address):
    import match
    if image['type'] != 1:
        raise ValueError('addressed signed runtimes require original relocatable ELF')
    match.allocated_text_only(image)
    symbol, offset = match.function_record(image, f'func_{address:08X}', address, True)
    if offset or any(
            item is not symbol and item['type'] in (1, 2) and item['section'] or
            re.fullmatch(r'\$a(?:\..*)?', item['name']) for item in image['symbols']):
        raise ValueError('addressed signed runtimes require sole complete original Thumb text')
    terminal_alignment(image, symbol)
    return symbol


def original_bindings(image, address, rom, mapping, *, data_mapping=None, data_relocations=None,
                      selector=SELECTOR):
    """Canonical addressed calls, with separately requested typed original ABS32."""
    import match
    with_data = data_mapping is not None or data_relocations is not None
    if with_data and (type(data_mapping) is not bytes or type(data_relocations) is not dict or
                      data_relocations):
        raise ValueError('addressed data linking requires a snapshot and fresh empty binding collection')
    objects = match.parse_data_symbols(data_mapping) if with_data else {}
    if selector not in SCHEMAS or selector in CALLBACK_SELECTORS and not with_data:
        raise ValueError('callback linking requires its exact selector and typed data')
    symbol = original_function(image, address)
    entries = json.loads(mapping)
    calls, bindings, targets, occupied = {}, {}, {}, set()
    for section_index in image['relocations']:
        section = image['sections'][section_index]
        if section[1] != 9 or section[7] != image['text_index'] or section[9] != 8 or section[5] % 8:
            raise ValueError('addressed signed runtimes require canonical Thumb call REL sections')
        symbols = image['symbol_tables'].get(section[6])
        for position in range(0, section[5], 8):
            offset, info = struct.unpack_from('<II', image['section_data'][section_index], position)
            if info & 255 not in ((2, 10) if with_data else (10,)) or \
                    symbols is None or info >> 8 >= len(symbols) or offset % 2 or \
                    offset + 4 > symbol['size'] or occupied.intersection(range(offset, offset+4)):
                raise ValueError('addressed signed runtimes exclude data and irregular relocations')
            target_symbol = symbols[info >> 8]
            name = target_symbol['name']
            if info & 255 == 2:
                if (address + offset) % 4 or target_symbol['section'] or target_symbol['value'] or \
                        target_symbol['size'] or target_symbol['bind'] != 1 or \
                        target_symbol['type'] not in (0, 1) or \
                        sum(item['name'] == name for item in image['symbols']) != 1:
                    raise ValueError('addressed ABS32 requires an aligned unique undefined global object')
                addend = struct.unpack_from('<i', image['text'], offset)[0]
                object_value(name, addend, objects, entries, address, symbol['size'])
                data_relocations[offset] = (name, addend)
                targets[name] = objects[name]
                occupied.update(range(offset, offset+4))
                continue
            if target_symbol['section'] or target_symbol['value'] or target_symbol['bind'] != 1 or \
                    target_symbol['type'] not in (0, 2) or \
                    sum(item['name'] == name for item in image['symbols']) != 1:
                raise ValueError('addressed calls require unique undefined zero-valued global functions')
            target = OPERATIONS.get(name)
            if target is None:
                if selector in CALLBACK_SELECTORS and name == callback_alias(selector):
                    target = match.function_thunk.ALIASES[name]
                    match.function_thunk.dependencies([name], rom)
                else:
                    target = match.function_address_target(name, entries, address, symbol['size'], len(rom))
            else:
                bindings[address+offset] = name
            decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
            decoder.detail = True
            instruction = next(decoder.disasm(image['text'][offset:offset+4],address+offset),None)
            if instruction is None or instruction.id != match.ARM_INS_BL or instruction.size != 4 or \
                    len(instruction.operands) != 1 or instruction.operands[0].type != match.ARM_OP_IMM or \
                    instruction.operands[0].imm != address+offset:
                raise ValueError('addressed call relocation requires its canonical zero addend')
            calls[address+offset] = target
            targets[name] = target
            occupied.update(range(offset,offset+4))
    if not bindings or with_data and not data_relocations or any(
                           item['name'] and not item['section'] and item['name'] not in targets
                           for item in image['symbols']):
        raise ValueError('addressed runtime ELF requires actual addressed calls and no unresolved symbols')
    if selector in CALLBACK_SELECTORS and callback_alias(selector) not in targets:
        raise ValueError('callback ELF requires its actual compiler-emitted canonical call')
    return calls, bindings, targets


def linked_bytes(original, linked, address, calls, targets, *, data_relocations=None):
    import match
    if linked['type'] != 2 or linked['relocations']:
        raise ValueError('addressed runtime link requires executable ELF without relocations')
    match.allocated_text_only(linked)
    name = f'func_{address:08X}'
    before = original_function(original, address)
    after, offset = match.function_record(linked, name, address, True)
    if offset or after['value'] != address | 1 or after['size'] != before['size'] or \
            linked['sections'][linked['text_index']][3] != address or \
            len(linked['text']) != len(original['text']):
        raise ValueError('addressed runtime linker changed extent, mode, placement or text size')
    terminal_alignment(linked, after)
    if data_relocations is not None and (type(data_relocations) is not dict or not data_relocations):
        raise ValueError('addressed data linker requires actual original bindings')
    data_relocations = data_relocations or {}
    data_names = {record[0] for record in data_relocations.values()}
    functions = [item['name'] for item in linked['symbols'] if item['type'] == 2]
    objects = [item['name'] for item in linked['symbols'] if item['type'] == 1]
    expected_functions = {name} | (set(targets) - data_names)
    if len(functions) != len(expected_functions) or set(functions) != expected_functions or \
            len(objects) != len(data_names) or set(objects) != data_names or any(
            item['name'] and not item['section'] or
            re.fullmatch(r'\$a(?:\..*)?', item['name']) for item in linked['symbols']):
        raise ValueError('addressed runtime linker introduced objects, undefined symbols or veneers')
    for target_name, target in targets.items():
        symbols = [item for item in linked['symbols'] if item['name'] == target_name]
        kind = 1 if target_name in data_names else 2
        value = target if kind == 1 else target | 1
        if len(symbols) != 1 or symbols[0]['type'] != kind or symbols[0]['bind'] != 1 or \
                symbols[0]['section'] != 0xFFF1 or symbols[0]['value'] != value:
            raise ValueError('addressed runtime linked target lost its absolute Thumb identity')
    occupied = set()
    for site, target in calls.items():
        offset = site-address
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB); decoder.detail = True
        instruction = next(decoder.disasm(linked['text'][offset:offset+4],site),None)
        if instruction is None or instruction.id != match.ARM_INS_BL or instruction.size != 4 or \
                instruction.operands[0].imm != target:
            raise ValueError('addressed runtime linked BL target differs')
        occupied.update(range(offset,offset+4))
    for offset, (target_name, addend) in data_relocations.items():
        if type(offset) is not int or (address+offset) % 4 or not 0 <= offset <= before['size']-4 or \
                type(addend) is not int or not -0x80000000 <= addend <= 0x7FFFFFFF or \
                target_name not in targets or occupied.intersection(range(offset,offset+4)) or \
                struct.unpack_from('<i', original['text'], offset)[0] != addend or \
                not 0 <= targets[target_name]+addend <= 0xFFFFFFFF or \
                struct.unpack_from('<I', linked['text'], offset)[0] != targets[target_name]+addend:
            raise ValueError('addressed linked data differs from its original typed ABS32 addend')
        occupied.update(range(offset,offset+4))
    if any(index not in occupied and first != second for index, (first,second) in
           enumerate(zip(original['text'],linked['text']))):
        raise ValueError('addressed runtime linker changed bytes outside call relocations')
    return linked['text'][:after['size']]


def object_bytes(runner, workspace, args, original, address, rom, mapping, *,
                 selector=SELECTOR, data_mapping=None):
    import match
    from inert_spin_profile import fixed_configuration
    fixed_configuration(args)
    data = {} if selector in DATA_SELECTORS else None
    if selector in CALLBACK_SELECTORS:
        match.function_thunk.namespace(runner.read_binary(f'{workspace}/f.i').decode('utf-8'))
    calls, bindings, targets = original_bindings(original,address,rom,mapping,
        data_mapping=data_mapping if data is not None else None, data_relocations=data, selector=selector)
    data_names = {record[0] for record in (data or {}).values()}
    definitions = ['.syntax unified','.thumb']
    for name,target in sorted(targets.items()):
        if name in data_names:
            definitions += [f'.global {name}',f'.type {name}, %object',f'.set {name}, 0x{target:08X}']
        else:
            definitions += [f'.global {name}',f'.type {name}, %function',f'.thumb_set {name}, 0x{target|1:08X}']
    runner.write_text(f'{workspace}/f.known.s','\n'.join(definitions)+'\n')
    runner.write_text(f'{workspace}/f.ld',
        f'SECTIONS {{ .text 0x{address:08X} : {{ *(.text) *(.glue_7) *(.glue_7t) }} '
        '.data 0 : { *(.data) } .bss 0 : { *(.bss) } '
        '.ARM.attributes 0 : { *(.ARM.attributes) } '
        '.unexpected 0 : { *(.vfp11_veneer) *(.v4_bx) *(.iplt) *(.igot.plt) } '
        '.rel.iplt 0 : { *(.rel.iplt) } '
        'ASSERT(SIZEOF(.unexpected) == 0, "unexpected linker stubs") '
        'ASSERT(SIZEOF(.rel.iplt) == 0, "unexpected dynamic relocations") '
        '/DISCARD/ : { *(.comment) *(.note.GNU-stack) } }')
    quoted = shlex.quote(workspace)
    runner.sh(f'export TMPDIR={quoted}; {args.assembler} -mthumb-interwork {quoted}/f.known.s -o {quoted}/f.known.o')
    runner.sh(f'export TMPDIR={quoted}; {args.linker} --fatal-warnings --no-undefined --no-relax '
              f'--orphan-handling=error -T {quoted}/f.ld -e func_{address:08X} '
              f'{quoted}/f.o {quoted}/f.known.o -o {quoted}/f.elf')
    runner.sh(f'{args.objcopy} -O binary --only-section=.text {quoted}/f.elf {quoted}/f.linked.bin')
    linked = match.elf_image(runner.read_binary(f'{workspace}/f.elf'))
    if runner.read_binary(f'{workspace}/f.linked.bin') != linked['text']:
        raise ValueError('addressed runtime objcopy differs from linked ELF text')
    result = linked_bytes(original,linked,address,calls,targets,data_relocations=data),calls,bindings
    if data is not None:
        result += ([[offset,name,addend] for offset,(name,addend) in sorted(data.items())],)
    return result


def toolchain_fingerprint():
    import match
    commands = (match.DEFAULT_CC,match.DEFAULT_CPP,match.DEFAULT_AS,match.DEFAULT_OBJCOPY,match.DEFAULT_LD)
    return [[command,sha(Path(shutil.which(os.path.expandvars(command)) or
                              os.path.expandvars(command)).read_bytes())] for command in commands]


def runtime_fingerprint():
    import capstone
    return dict(system=platform.system(), kernel=platform.release(), machine=platform.machine(),
        python=platform.python_version(), python_sha256=sha(Path(sys.executable).read_bytes()),
        capstone=capstone.__version__, binding_sha256=sha(Path(capstone.__file__).read_bytes()),
        capstone_native_sha256=sha(Path(capstone._cs._name).read_bytes()))


def build(root, address, args=None, expected=None, *, selector=SELECTOR):
    import match
    from inert_spin_profile import fixed_configuration,index_snapshot
    from match_evidence import source_fingerprint,source_paths,mapping_snapshot,data_snapshot,report_rom_path
    root = Path(root)
    args = args or argparse.Namespace(cc=match.DEFAULT_CC,cpp=match.DEFAULT_CPP,assembler=match.DEFAULT_AS,
        objcopy=match.DEFAULT_OBJCOPY,linker=match.DEFAULT_LD,flags=match.DEFAULT_FLAGS)
    fixed_configuration(args)
    if selector not in SCHEMAS:
        raise ValueError('unknown addressed signed runtime selector')
    runtime = runtime_fingerprint() if selector in (READONLY_SELECTOR, READONLY_TWO_SELECTOR, *DATA_SELECTORS) else None
    producers = data_producer_fingerprint() if selector in DATA_SELECTORS else None
    source,mapping,index = source_fingerprint(root,address),mapping_snapshot(root),index_snapshot(root)
    objects,selected_rom = data_snapshot(root),report_rom_path(root)
    rom = Path(selected_rom).read_bytes(); tools = toolchain_fingerprint()
    candidates = list((root/'src').rglob(f'{address:08X}.c'))
    if len(candidates) != 1:
        raise ValueError('addressed signed runtime requires one uniquely addressed source')
    (root/'build').mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='addressed_signed_',dir=root/'build') as directory:
        captured = Path(directory)
        for path in source_paths(root,address):
            destination = captured/path.relative_to(root)
            destination.parent.mkdir(parents=True,exist_ok=True); destination.write_bytes(path.read_bytes())
        if source_fingerprint(captured,address) != source:
            raise ValueError('addressed signed runtime source capture differs')
        runner = match.Runner(match.DEFAULT_CC,'Ubuntu',match.DEFAULT_WSL_PATH,root=captured,timeout=120)
        with runner.workspace() as workspace:
            raw,_,original = match.compile_object(runner,workspace,args,captured,address,
                candidates[0].relative_to(root).as_posix())
            assembly = runner.read_binary(f'{workspace}/f.s')
            linked_result = object_bytes(runner,workspace,args,original,address,rom,mapping,
                selector=selector,data_mapping=objects)
            body,calls,bindings = linked_result[:3]
            data_options = (dict(data_mapping=objects,data_bindings=linked_result[3])
                            if selector in DATA_SELECTORS else {})
            manifest,instructions = verify(body,address,rom,mapping,index,calls,bindings,expected,
                                           selector=selector,**data_options)
            linked = runner.read_binary(f'{workspace}/f.elf')
        check = match._run_replay_process([sys.executable,str(Path(importlib.import_module('plausible').__file__)),
            '--quiet','--addr',f'0x{address:08X}','--json']+
            [str(path) for path in source_paths(captured,address)],captured,120)
        findings,allowed = match.plausibility_result(check,address)
        if findings or allowed or source_fingerprint(captured,address) != source:
            raise ValueError('addressed signed runtime source is implausible or changed')
    if source_fingerprint(root,address) != source or mapping_snapshot(root) != mapping or \
            index_snapshot(root) != index or data_snapshot(root) != objects or \
            report_rom_path(root) != selected_rom or Path(selected_rom).read_bytes() != rom or \
            toolchain_fingerprint() != tools or runtime is not None and runtime_fingerprint() != runtime or \
            producers is not None and (data_producer_fingerprint() != producers or
                manifest['producer_source_sha256'] != producers):
        raise ValueError('addressed signed runtime source, inputs or tools changed during verification')
    result = dict(address=address,body=body,manifest=manifest,source_sha256=source,
        mapping_sha256=sha(mapping),index_sha256=sha(index),objects_sha256=None if objects is None else sha(objects),
        rom_sha256=sha(rom),instructions=len(instructions),toolchain=tools,
        original_elf=raw,assembly=assembly,linked_elf=linked)
    if runtime is not None:
        result['runtime'] = runtime
    return result


def render(result):
    selector = next((key for key,value in SCHEMAS.items() if value == result['manifest']['schema']),None)
    if selector is None:
        raise ValueError('unknown addressed signed runtime manifest schema')
    premise = [] if selector not in (READONLY_SELECTOR, READONLY_TWO_SELECTOR) else [
        '* incoming stack ABI: ' + result['manifest']['frame']['entry_stack']['contract']]
    if selector in DATA_SELECTORS:
        premise = ['* named data binding: ' + result['manifest']['data_contract']]
    if selector in CALLBACK_SELECTORS:
        register = 'r3' if selector == R3_CALLBACK_SELECTOR else 'r2'
        premise.append(f'* mapped {register} callback ABI: ' + result['manifest']['callback']['contract'])
    evidence = {key:value for key,value in result.items() if key not in
                ('body','original_elf','assembly','linked_elf')}
    for key in ('body','original_elf','assembly','linked_elf'):
        evidence[key+'_sha256'] = sha(result[key])
    encoded = text(evidence)
    return '\n'.join([f'# 0x{result["address"]:08X}','',f'* verification: `{SCHEMAS[selector]}`',
        f'* addressed signed runtime: `{selector}`',f'* control flow: {ABI}',*premise,
        '* source plausibility: plausible',
        '* verified extent: complete original ELF function symbol including referenced literal pools',
        '* numeric division/remainder equivalence: unclaimed; original formal type certainty: unclaimed',
        f'* addressed signed runtime evidence: `{encoded}`',
        f'* addressed signed runtime proof SHA-256: `{sha(encoded.encode())}`',
        f'* compiled : `{result["body"].hex()}`',
        f'* ROM bytes: `{result["body"].hex()}` ({len(result["body"])} bytes)','',
        f'**MATCH - byte identical** - {len(result["body"])}/{len(result["body"])} bytes',''])


def selector_for_report(report):
    from inert_spin_profile import marker_text
    lines = report.splitlines()
    if not any(any(schema in line for schema in SCHEMAS.values()) or
               marker_text(line).startswith('* addressed signed runtime') for line in lines):
        return False
    for selector,schema in SCHEMAS.items():
        if [line for line in lines if marker_text(line).startswith('* verification:')] == [f'* verification: `{schema}`'] and \
                [line for line in lines if marker_text(line).startswith('* addressed signed runtime:')] == \
                [f'* addressed signed runtime: `{selector}`']:
            return selector
    raise ValueError('mixed or malformed addressed signed runtime report')


def selected(report):
    return bool(selector_for_report(report))


def report_matches(report, root, address):
    from match_evidence import source_fingerprint,mapping_snapshot,data_snapshot,report_rom_path,valid_match_verdict
    from inert_spin_profile import index_snapshot
    if _replay.get():
        return False
    token = _replay.set(True)
    try:
        selector = selector_for_report(report)
        if not selector or not valid_match_verdict(report):
            return False
        prefix = '* addressed signed runtime evidence: `'
        rows = [line for line in report.splitlines() if line.startswith(prefix)]
        if len(rows) != 1 or not rows[0].endswith('`'):
            return False
        def unique(pairs):
            result = {}
            for key,value in pairs:
                if key in result: raise ValueError('duplicate addressed signed runtime evidence key')
                result[key] = value
            return result
        encoded = rows[0][len(prefix):-1]; saved = json.loads(encoded,object_pairs_hook=unique)
        objects = data_snapshot(root)
        if text(saved) != encoded or saved['address'] != address or \
                saved['source_sha256'] != source_fingerprint(root,address) or \
                saved['mapping_sha256'] != sha(mapping_snapshot(root)) or \
                saved['index_sha256'] != sha(index_snapshot(root)) or \
                saved['objects_sha256'] != (None if objects is None else sha(objects)) or \
                saved['rom_sha256'] != sha(Path(report_rom_path(root)).read_bytes()) or \
                saved['toolchain'] != toolchain_fingerprint():
            return False
        if selector in (READONLY_SELECTOR, READONLY_TWO_SELECTOR, *DATA_SELECTORS) and saved['runtime'] != runtime_fingerprint():
            return False
        return render(build(root,address,expected=saved['manifest'],selector=selector)) == report
    except (OSError,ValueError,KeyError,TypeError,IndexError,RuntimeError,subprocess.SubprocessError):
        return False
    finally:
        _replay.reset(token)


def issue(root, address, args):
    import match
    if args.mode != 'thumb' or args.control_flow_profile != 'ordinary' or args.label or \
            args.wsl != 'Ubuntu' or args.wsl_path != match.DEFAULT_WSL_PATH or any(
                getattr(args,name) is not None for name in ('signed_runtime_profile','signed_quotient_profile',
                'software_double_profile','software_double_remainder_profile','function_address_profile',
                'switch_profile','owner_runtime_profile')):
        raise ValueError('addressed signed runtimes require their isolated explicit Thumb selector')
    result = build(root,address,args,selector=args.addressed_signed_runtime_profile)
    if args.emit:
        output = (Path(root)/args.emit).resolve()
        if (Path(root)/'build').resolve() not in output.parents or output.exists():
            raise ValueError('--emit requires a new file beneath build/')
        output.parent.mkdir(parents=True,exist_ok=True)
        with output.open('xb') as stream:stream.write(result['body'])
    if not args.no_write:
        report = Path(root)/'docs/match'/f'{address:08X}.md'
        report.parent.mkdir(parents=True,exist_ok=True); report.write_text(render(result))
    print(f'extent    {len(result["body"])} bytes (complete ELF symbol; conditional addressed runtime ABI)')
    print('verdict MATCH - byte identical')
    return 0
