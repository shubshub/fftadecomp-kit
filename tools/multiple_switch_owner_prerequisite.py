"""Explicit original-ELF prerequisite for bounded ordinary multi-switch owners.

This composes existing local-section relocation, guarded dispatch, complete CFG,
partition and strict frame checks. It is not compiler/source or native admission.
"""
import hashlib
import json
from pathlib import Path
import struct

import analyze
import framed_switch_inventory as ordinary
import local_long_branch_profile as frame
import match
import owner_admission_profile as owner
import owner_graph_profile as graph
import owner_runtime_profile as operations
from one_constant_scalar_switch_inventory import guard_predecessors
from software_double_profile import indices, span_record

SELECTOR = 'ordinary-multiple-switch-owner-prerequisite-v1'
MAX_BYTES = 4096
MAX_SWITCHES = 8


def _text(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def _sha(value):
    return hashlib.sha256(value).hexdigest()


def check_context(selector, relocations, contexts=(), flags=(), pool_words=5):
    if type(selector) is not str or selector != SELECTOR or type(relocations) is not dict or \
            any(value is not None for value in contexts) or \
            any(type(flag) is not bool or flag for flag in flags) or \
            type(pool_words) is not int or pool_words != 5:
        raise ValueError('multiple-switch prerequisite requires its isolated explicit context')


def check_backward_context(selector, flags=()):
    """Only the explicit multi-switch route may widen table target direction."""
    if selector is not None and (type(selector) is not str or selector != SELECTOR or
            any(type(flag) is not bool or flag for flag in flags)):
        raise ValueError('backward multiple-switch cases require isolated explicit qualification')
    return selector is not None


def layout(data, address, relocations, *, multiple_switch_profile=None):
    """Partition every original local word into a unique existing guarded table.

    Table lengths come from matching exact guard/dispatch bytes, never from a
    caller-provided split. Complete CFG, cross-table edges and frame are separate
    mandatory checks in verify(), after all actual BL relocations are applied.
    """
    if type(data) is not bytes or type(address) is not int or address % 2 or \
            not 2 <= len(data) <= MAX_BYTES or type(relocations) is not dict or \
            not 4 <= len(relocations) <= len(data)//4 or any(
                type(at) is not int or type(value) is not int for at, value in relocations.items()):
        raise ValueError('multiple-switch layout requires bounded immutable bytes and local words')
    backward = check_backward_context(multiple_switch_profile)
    remaining = dict(relocations)
    descriptors = []
    while remaining:
        if len(descriptors) == MAX_SWITCHES:
            raise ValueError('multiple-switch table budget exceeded')
        first = min(remaining)
        candidates = []
        for count in range(1, min(256, len(remaining)-1)+1):
            positions = range(first, first+4*(count+1), 4)
            if any(at not in remaining for at in positions):
                break
            words = {at: remaining[at] for at in positions}
            try:
                descriptor = match.switch_layout(data, address, words, allow_backward_cases=backward)
            except ValueError:
                continue
            candidates.append(descriptor)
        if len(candidates) != 1:
            raise ValueError('local relocation words have no unique complete guarded-table partition')
        descriptor = candidates[0]
        descriptors.append(descriptor)
        for at, _ in descriptor['relocations']:
            del remaining[at]
    if len(descriptors) < 2:
        raise ValueError('multiple-switch prerequisite requires at least two actual tables')
    return dict(selector=SELECTOR, switches=descriptors)


def _ordinary_original_calls(image, calls, address):
    # Existing generic call binding permits some nonzero addressed addends.
    # This closed prerequisite requires the genuine unique zero-addend identity.
    for section_no in image['relocations']:
        section = image['sections'][section_no]
        symbols = image['symbol_tables'][section[6]]
        raw = image['section_data'][section_no]
        for at in range(0, len(raw), 8):
            offset, info = struct.unpack_from('<II', raw, at)
            if info & 255 != 10:
                continue
            symbol = symbols[info >> 8]
            if symbol['section'] or symbol['value'] or symbol['size'] or \
                    symbol['bind'] != 1 or symbol['type'] not in (0, 2) or \
                    sum(row['name'] == symbol['name'] for row in image['symbols']) != 1 or \
                    image['text'][offset:offset+4] != bytes.fromhex('fff7feff') or \
                    calls.get(address+offset) != int(symbol['name'][5:], 16):
                raise ValueError('multiple-switch calls require genuine unique zero-addend function identities')


def verify(original_ELF, linked_ELF, address, rom, mapping, index, *, selector, manifest=None):
    if type(selector) is not str or selector != SELECTOR or type(address) is not int or \
            any(type(value) is not bytes for value in (original_ELF, linked_ELF, rom, mapping, index)):
        raise ValueError('multiple-switch prerequisite requires its explicit immutable original inputs')
    original, linked = match.elf_image(original_ELF), match.elf_image(linked_ELF)
    name = f'func_{address:08X}'
    symbol, _ = match.function_record(original, name, address, True)
    if not 2 <= symbol['size'] <= MAX_BYTES:
        raise ValueError('multiple-switch complete owner exceeds byte budget')
    relocations = {}
    calls, targets, objects = match.call_bindings(original, name, address, mapping,
        len(rom), rom_image=rom, switch_relocations=relocations, multiple_switch_profile=SELECTOR)
    if objects:
        raise ValueError('multiple-switch prerequisite excludes external object words')
    _ordinary_original_calls(original, calls, address)
    data = match.linked_function_bytes(original, linked, name, address, calls, targets,
        switch_relocations=relocations, multiple_switch_profile=SELECTOR)
    entries = owner.validate_span(data, address, rom, mapping, index)
    refinement = owner.refine(data, address, mapping, multiple_switch_profile=selector)
    instructions, edges, branches, actual_calls, words = graph.graph(data, address, refinement, multiple_switch_profile=selector)
    descriptor = layout(data, address, relocations, multiple_switch_profile=selector)
    if branches or calls != actual_calls or words != relocations or \
            len(refinement['word_switches']) != len(descriptor['switches']):
        raise ValueError('multiple-switch complete CFG differs from original relocations/calls')
    for actual, expected in zip(refinement['word_switches'], descriptor['switches']):
        if actual.get('interposed_words', 0) or any(actual.get(k) != v for k, v in expected.items()):
            raise ValueError('multiple-switch actual descriptors differ from local word ownership')
        guard_predecessors(instructions, edges, address, actual)
    indexed, rows = indices(mapping, index)
    span = span_record(address, address+len(data), indexed, rows, rom)
    if span['instrs'] != len(instructions):
        raise ValueError('multiple-switch dual-index instruction count differs from complete CFG')
    if calls:
        bindings = ordinary.bind_calls(calls, mapping, address, len(data), len(rom))
        for target in sorted(set(calls.values())):
            row = next(row for row in entries if int(row['rom'], 16) == target)
            span_record(target, int(row['end'], 16), indexed, rows, rom)
    else:
        bindings = {}
    degree = {site: 0 for site in instructions}
    for successors in edges.values():
        for target in successors:
            degree[target] += 1
    pending = [site for site in instructions if degree[site] == 0]
    visited = 0
    while pending:
        site = pending.pop(); visited += 1
        for target in edges[site]:
            degree[target] -= 1
            if degree[target] == 0:
                pending.append(target)
    if visited != len(instructions):
        raise ValueError('multiple-switch prerequisite excludes local CFG cycles')
    operations.verify_operations(instructions, edges, address, branches, calls, refinement)
    for item in instructions.values():
        adjustment = match.thumb_stack_adjustment(item)
        if item.size != (4 if item.mnemonic == 'bl' else 2) or \
                item.mnemonic.startswith(('ldm', 'stm')) or \
                item.mnemonic not in ('push', 'pop') and adjustment is None and any(
                    operand.type == match.ARM_OP_REG and operand.reg == match.ARM_REG_SP
                    for operand in item.operands):
            raise ValueError('multiple-switch excludes wide/block operations and stack address materialization')
    partition = graph.partition(data, address, refinement, instructions, words)
    scalar_words = []
    for word in partition['words']:
        if word['switch_word']:
            continue
        if not word['load_sites'] or not 0 <= word['value'] <= 0xffff:
            raise ValueError('multiple-switch extra literals must be actually reached u16 scalars')
        scalar_words.append(word)
    restored = frame.prove_frame(instructions, edges, address, {}, calls)
    modules = (analyze, ordinary, frame, match, owner, graph, operations)
    result = dict(schema=SELECTOR, selector=selector, address=address, bytes=len(data),
        instructions=len(instructions), switches=descriptor['switches'],
        backward_case_policy='explicit multi-switch cases; complete acyclic cross-table CFG',
        local_relocations=sorted(relocations.items()), scalar_words=scalar_words,
        calls=sorted(calls.items()), bindings=sorted(bindings.items()), frame=restored,
        partition=partition, cycles_present=False, original_ET_REL_sha256=_sha(original_ELF),
        linked_ELF_sha256=_sha(linked_ELF), body_sha256=_sha(data), ROM_sha256=_sha(rom),
        mapping_sha256=_sha(mapping), index_sha256=_sha(index),
        source_or_ELF_admission=False, native_admission=False, memory_safety_claim=False,
        arithmetic_C_equivalence=False, termination_claim=False,
        ordinary_callee_effects_proved=False, numeric_input_preconditions=[],
        ordinary_call_premise='Conditional ordinary returning-call ABI preserves r4-r11/SP; '
            'no actual callee effects, memory permission or callback identity is inferred.',
        claim='Complete original local-section typed-link and guarded multi-switch owner '
            'CFG/partition/frame prerequisite. Compiler/source admission requires parent integration.',
        producer_sha256={Path(m.__file__).name: _sha(Path(m.__file__).read_bytes()) for m in modules},
        self_sha256=_sha(Path(__file__).read_bytes()))
    if manifest is not None and _text(manifest) != _text(result):
        raise ValueError('multiple-switch manifest differs from fresh proof')
    return result
