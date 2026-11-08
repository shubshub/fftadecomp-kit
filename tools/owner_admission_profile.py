"""Explicit complete-owner composition with original-ELF and source replay.

Local BL control, guarded word switches, restoring stack aliases, canonical
indirect thunks and constant nonzero unsigned division share one closed CFG.
The selector grants no permission to alter the compiler or bypass source checks.
"""
import argparse
from contextvars import ContextVar
import hashlib
import json
from pathlib import Path
import re
import shlex
import struct
import subprocess
import sys
import tempfile

import analyze
import entry_recursive_ordinary_call_profile as entry
import mutable_three_call_native_profile as mutable_native
import multiple_switch_native_profile as multiple_native
import canonical_integer_native_profile as integer_native
import canonical_integer_three_words_native_profile as integer_three
import canonical_integer_six_words_native_profile as integer_words
import canonical_integer_two_words_native_profile as integer_two
import canonical_integer_private_locals_native_profile as integer_locals
import canonical_integer_scalar_data_native_profile as integer_data
import numeric_data_switch_native_profile as numeric_switch
import owner_graph_profile as graph
import owner_runtime_profile as runtime
import function_thunk_profile as thunk
import ignored_leaf_alias_profile as ignored_leaf
import named_data_buffer_profile as named_buffer
import conditional_local_buffer_profile as local_calls
import bios_fast_fill_source_profile as fast_fill
import nested_formal_output_buffer_profile as nested_output
import direct_halfword_output_buffer_profile as direct_output
import three_halfword_output_buffer_profile as three_output
import named_three_halfword_output_buffer_profile as named_three
import dynamic_division_buffer_profile as dynamic_div
import static_callback_buffer_profile as static_buffer
import static_callback_target_preservation_profile as r7_buffer
import static_callback_r6_frame_profile as r6_buffer
import word_result_callback_profile as word_buffer
import standalone_local_output_word_profile as resident_word
import local_rom_halfword_table_profile as rom_table
import local_shadow_matrix_native_profile as shadow_matrix
import protected_descriptor_word_profile as descriptor
import watched_switch_preservation_profile as watched_switch
import descriptor_output_alias_profile as output_alias
import descriptor_single_store_profile as single_store
import descriptor_disjunctive_alias_profile as disjunctive
import descriptor_callee_constant_profile as callee_constant
import descriptor_cursor_value_profile as cursor
import ordinary_formal_output_spill_profile as formal_spill
import two_word_callback_closure_profile as callback_closure
import tree_two_word_callback_closure_profile as tree_callback
import known_query_native_closure_profile as known_query
import known_list_query_closure_profile as list_query
import known_list_query_continuation_profile as query_cont
import nested_known_query_profile as nested_query
import finite_local_word_loop_profile as finite_loop
import finite_spilled_scalar_loop_profile as spilled_loop
import guarded_bios_division_profile as bios_div
from inert_spin_profile import fixed_configuration, index_snapshot, validate_span, marker_text

SCHEMA = 'elf-symbol-thumb-restoring-owner-runtime-v1'
SELECTOR = 'restoring-owner-runtime-v1'
ALIGNED_SELECTOR = 'restoring-owner-switch-aligned-v1'
ALIGNED_SCHEMA = 'elf-symbol-thumb-restoring-owner-switch-aligned-v1'
CYCLIC_SELECTOR = 'restoring-owner-switch-cycles-function-words-v1'
CYCLIC_SCHEMA = 'elf-symbol-thumb-restoring-owner-switch-cycles-function-words-v1'
THUNK_SWITCH_SELECTOR = 'restoring-owner-r3-thunk-switch-v1'
THUNK_SWITCH_SCHEMA = 'elf-symbol-thumb-restoring-owner-r3-thunk-switch-v1'
THUNK_SWITCH_CONTROL_FLOW = 'complete acyclic scalar-frame guarded switch with typed named data, exact canonical R3 thunks and conditional returning ordinary and indirect ABI; termination unproved'
DIRECT_SWITCH_SELECTOR = 'restoring-owner-scalar-switch-v1'
DIRECT_SWITCH_SCHEMA = 'elf-symbol-thumb-restoring-owner-scalar-switch-v1'
DIRECT_SWITCH_CONTROL_FLOW = 'complete scalar-frame guarded Thumb switch with exact ordinary calls and restored returns; termination unproved'
ENTRY_SWITCH_SELECTOR = 'restoring-owner-switch-entry-word-v1'
ENTRY_SWITCH_SCHEMA = 'elf-symbol-thumb-restoring-owner-switch-entry-word-v1'
ENTRY_DATA_SWITCH_SELECTOR = 'restoring-owner-switch-entry-two-words-data-v1'
ENTRY_DATA_SWITCH_SCHEMA = 'elf-symbol-thumb-restoring-owner-switch-entry-two-words-data-v1'
ENTRY_DATA_SWITCH_CONTROL_FLOW = 'complete guarded Thumb switch with two unknown readable incoming ABI words, typed named data and restored return frame; termination unproved'
ENTRY_SWITCH_CONTROL_FLOW = 'complete guarded Thumb switch with one unknown readable incoming ABI word and restored return frame; termination unproved'
CYCLIC_CONTROL_FLOW = 'complete restoring Thumb owner; guarded switch, local CFG cycles, exact ordinary calls and typed function words; partial correctness under conditional returning-call ABI'
ALIGNED_CONTROL_FLOW = 'complete acyclic restoring Thumb owner; guarded word switches, exact ordinary-call bindings and conditional returning-call ABI'
CONTROL_FLOW = 'complete restoring Thumb owner; local BL control, guarded switches, canonical thunks and constant unsigned division'
ACYCLIC_SELECTOR = 'restoring-owner-acyclic-v1'
ACYCLIC_SCHEMA = 'elf-symbol-thumb-acyclic-stack-alias-v1'
ACYCLIC_STATE_BUDGET = 4096
ACYCLIC_CONTROL_FLOW = 'complete acyclic Thumb owner; exact bounded path states and ordinary direct-call ABI summaries'
_replay = ContextVar('owner_runtime_replay', default=False)


def text(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def selected(report):
    verification = '\n'.join(line for line in report.splitlines()
                             if marker_text(line).startswith('* verification'))
    relevant = shadow_matrix.SCHEMA in verification or rom_table.SCHEMA in verification or numeric_switch.SCHEMA in verification or integer_three.SCHEMA in verification or integer_data.SCHEMA in verification or integer_locals.SCHEMA in verification or integer_two.SCHEMA in verification or integer_words.SCHEMA in verification or integer_native.SCHEMA in verification or multiple_native.SCHEMA in verification or mutable_native.SCHEMA in verification or resident_word.SCHEMA in verification or any(schema in verification for schema in r6_buffer.SCHEMAS) or entry.NATIVE_SCHEMA in verification or SCHEMA in verification or ALIGNED_SCHEMA in verification or CYCLIC_SCHEMA in verification or THUNK_SWITCH_SCHEMA in verification or DIRECT_SWITCH_SCHEMA in verification or ENTRY_DATA_SWITCH_SCHEMA in verification or ENTRY_SWITCH_SCHEMA in verification or ACYCLIC_SCHEMA in verification or ignored_leaf.SCHEMA in verification or any(schema in verification for schema in named_buffer.SCHEMAS) or static_buffer.SCHEMA in verification or word_buffer.SCHEMA in verification or r7_buffer.SCHEMA in verification or descriptor.SCHEMA in verification or watched_switch.SCHEMA in verification or output_alias.SCHEMA in verification or single_store.SCHEMA in verification or any(schema in verification for schema in disjunctive.PROFILES.values()) or any(schema in verification for schema in callee_constant.PROFILES.values()) or cursor.SCHEMA in verification or any(schema in verification for schema in formal_spill.SCHEMAS) or any(marker_text(line).startswith('* owner runtime')
                                      for line in report.splitlines())
    if not relevant:
        return False
    fields = [line for line in report.splitlines() if marker_text(line).startswith('* verification')]
    if fields not in ([f'* verification: `{numeric_switch.SCHEMA}`'], [f'* verification: `{integer_three.SCHEMA}`'], [f'* verification: `{integer_data.SCHEMA}`'], [f'* verification: `{integer_locals.SCHEMA}`'], [f'* verification: `{integer_two.SCHEMA}`'], [f'* verification: `{integer_words.SCHEMA}`'], [f'* verification: `{integer_native.SCHEMA}`'], [f'* verification: `{multiple_native.SCHEMA}`'], [f'* verification: `{SCHEMA}`'], [f'* verification: `{ALIGNED_SCHEMA}`'], [f'* verification: `{CYCLIC_SCHEMA}`'],
                      [f'* verification: `{THUNK_SWITCH_SCHEMA}`'], [f'* verification: `{DIRECT_SWITCH_SCHEMA}`'], [f'* verification: `{ENTRY_DATA_SWITCH_SCHEMA}`'], [f'* verification: `{ENTRY_SWITCH_SCHEMA}`'], [f'* verification: `{ACYCLIC_SCHEMA}`'],
                      [f'* verification: `{ignored_leaf.SCHEMA}`'],
                      *([f'* verification: `{schema}`'] for schema in local_calls.SCHEMAS.values()),
                      [f'* verification: `{named_buffer.SCHEMA}`'],
                      [f'* verification: `{named_buffer.DATAFREE_SCHEMA}`'],
                      [f'* verification: `{query_cont.SCHEMA}`'],
                      [f'* verification: `{nested_query.SCHEMA}`'],
                      [f'* verification: `{finite_loop.SCHEMA}`'], [f'* verification: `{spilled_loop.SCHEMA}`'],
                      [f'* verification: `{list_query.SCHEMA}`'],
                      [f'* verification: `{known_query.SCHEMA}`'],
                      [f'* verification: `{tree_callback.SCHEMA}`'],
                      [f'* verification: `{callback_closure.SCHEMA}`'],
                      [f'* verification: `{named_buffer.SCRATCH_SCHEMA}`'],
                      [f'* verification: `{named_buffer.BIOS_SQRT_SCHEMA}`'],
                      [f'* verification: `{named_buffer.THUNK_PARTIAL_SCHEMA}`'],
                      [f'* verification: `{named_buffer.THUNK_SCRATCH_SCHEMA}`'],
                      [f'* verification: `{named_buffer.THUNK_SCHEMA}`'],
                      [f'* verification: `{named_buffer.BIOS_FILL_SCHEMA}`'],
                      [f'* verification: `{named_buffer.FAST_FILL_SCHEMA}`'],
                      [f'* verification: `{named_buffer.GUARDED_SWITCH_SCHEMA}`'],
                      [f'* verification: `{named_buffer.GUARDED_ALIAS_SCHEMA}`'],
                      [f'* verification: `{bios_div.SCHEMA}`'],
                      [f'* verification: `{named_buffer.ROOT_SWITCH_SCHEMA}`'],
                      [f'* verification: `{nested_output.SCHEMA}`'],
                      [f'* verification: `{direct_output.SCHEMA}`'],
                      [f'* verification: `{dynamic_div.SCHEMA}`'],
                      [f'* verification: `{three_output.SCHEMA}`'], [f'* verification: `{named_three.SCHEMA}`'],
                      [f'* verification: `{static_buffer.SCHEMA}`'],
                      [f'* verification: `{r7_buffer.SCHEMA}`'],
                      *([f'* verification: `{schema}`'] for schema in r6_buffer.SCHEMAS),
                      [f'* verification: `{word_buffer.SCHEMA}`'],
                      [f'* verification: `{resident_word.SCHEMA}`'],
                      [f'* verification: `{rom_table.SCHEMA}`'],
                      [f'* verification: `{shadow_matrix.SCHEMA}`'],
                      [f'* verification: `{descriptor.SCHEMA}`'],
                      [f'* verification: `{watched_switch.SCHEMA}`'],
                      [f'* verification: `{output_alias.SCHEMA}`'],
                      [f'* verification: `{single_store.SCHEMA}`'],
                      *([f'* verification: `{schema}`'] for schema in disjunctive.PROFILES.values()),
                      *([f'* verification: `{schema}`'] for schema in callee_constant.PROFILES.values()),
                      [f'* verification: `{cursor.SCHEMA}`'],
                      [f'* verification: `{formal_spill.SCHEMA}`'],
                      [f'* verification: `{formal_spill.BIOS_SCHEMA}`'],
                      [f'* verification: `{entry.NATIVE_SCHEMA}`'],
                      [f'* verification: `{mutable_native.SCHEMA}`']) or any(marker_text(line).startswith((
            '* function-address', '* unsigned division', '* software double', '* software float',
            '* inert spin', '* switches', '* buffer calls', '* signed quotient', '* signed remainder'))
            for line in report.splitlines()):
        raise ValueError('mixed or malformed complete-owner profile')
    return True


def selector_for_report(report):
    if not selected(report):
        raise ValueError('not a complete-owner report')
    for policy, schema in local_calls.SCHEMAS.items():
        if f'* verification: `{schema}`' in report.splitlines():
            return policy
    if f'* verification: `{spilled_loop.SCHEMA}`' in report.splitlines():
        return spilled_loop.SELECTOR
    if f'* verification: `{finite_loop.SCHEMA}`' in report.splitlines():
        return finite_loop.SELECTOR
    if f'* verification: `{nested_query.SCHEMA}`' in report.splitlines():
        return nested_query.SELECTOR
    if f'* verification: `{query_cont.SCHEMA}`' in report.splitlines():
        return query_cont.SELECTOR
    if f'* verification: `{list_query.SCHEMA}`' in report.splitlines():
        return list_query.SELECTOR
    if f'* verification: `{known_query.SCHEMA}`' in report.splitlines():
        return known_query.SELECTOR
    if f'* verification: `{tree_callback.SCHEMA}`' in report.splitlines():
        return tree_callback.SELECTOR
    if f'* verification: `{callback_closure.SCHEMA}`' in report.splitlines():
        return callback_closure.SELECTOR
    if f'* verification: `{numeric_switch.SCHEMA}`' in report.splitlines():
        return numeric_switch.SELECTOR
    if f'* verification: `{integer_data.SCHEMA}`' in report.splitlines():
        return integer_data.SELECTOR
    if f'* verification: `{integer_locals.SCHEMA}`' in report.splitlines():
        return integer_locals.SELECTOR
    if f'* verification: `{integer_two.SCHEMA}`' in report.splitlines():
        return integer_two.SELECTOR
    if f'* verification: `{integer_words.SCHEMA}`' in report.splitlines():
        return integer_words.SELECTOR
    if f'* verification: `{integer_three.SCHEMA}`' in report.splitlines():
        return integer_three.SELECTOR
    if f'* verification: `{integer_native.SCHEMA}`' in report.splitlines():
        return integer_native.SELECTOR
    if f'* verification: `{multiple_native.SCHEMA}`' in report.splitlines():
        return multiple_native.SELECTOR
    if f'* verification: `{THUNK_SWITCH_SCHEMA}`' in report.splitlines():
        return THUNK_SWITCH_SELECTOR
    if f'* verification: `{DIRECT_SWITCH_SCHEMA}`' in report.splitlines():
        return DIRECT_SWITCH_SELECTOR
    if f'* verification: `{ENTRY_DATA_SWITCH_SCHEMA}`' in report.splitlines():
        return ENTRY_DATA_SWITCH_SELECTOR
    if f'* verification: `{ENTRY_SWITCH_SCHEMA}`' in report.splitlines():
        return ENTRY_SWITCH_SELECTOR
    if f'* verification: `{CYCLIC_SCHEMA}`' in report.splitlines():
        return CYCLIC_SELECTOR
    if f'* verification: `{ALIGNED_SCHEMA}`' in report.splitlines():
        return ALIGNED_SELECTOR
    if f'* verification: `{mutable_native.SCHEMA}`' in report.splitlines():
        return mutable_native.SELECTOR
    if f'* verification: `{shadow_matrix.SCHEMA}`' in report.splitlines():
        return shadow_matrix.SELECTOR
    if f'* verification: `{rom_table.SCHEMA}`' in report.splitlines():
        return rom_table.SELECTOR
    if f'* verification: `{resident_word.SCHEMA}`' in report.splitlines():
        return resident_word.SELECTOR
    if f'* verification: `{entry.NATIVE_SCHEMA}`' in report.splitlines():
        return entry.SELECTOR
    if f'* verification: `{formal_spill.BIOS_SCHEMA}`' in report.splitlines():
        return formal_spill.BIOS_SELECTOR
    if f'* verification: `{formal_spill.SCHEMA}`' in report.splitlines():
        return formal_spill.SELECTOR
    if f'* verification: `{ignored_leaf.SCHEMA}`' in report.splitlines():
        return ignored_leaf.SELECTOR
    if f'* verification: `{cursor.SCHEMA}`' in report.splitlines():
        return cursor.SELECTOR
    for selector, schema in callee_constant.PROFILES.items():
        if f'* verification: `{schema}`' in report.splitlines():
            return selector
    for selector, schema in disjunctive.PROFILES.items():
        if f'* verification: `{schema}`' in report.splitlines():
            return selector
    if f'* verification: `{single_store.SCHEMA}`' in report.splitlines():
        return single_store.SELECTOR
    if f'* verification: `{output_alias.SCHEMA}`' in report.splitlines():
        return output_alias.SELECTOR
    if f'* verification: `{watched_switch.SCHEMA}`' in report.splitlines():
        return watched_switch.SELECTOR
    if f'* verification: `{descriptor.SCHEMA}`' in report.splitlines():
        return descriptor.SELECTOR
    if f'* verification: `{word_buffer.SCHEMA}`' in report.splitlines():
        return word_buffer.SELECTOR
    for selector, (schema, _) in r6_buffer.PROFILES.items():
        if f'* verification: `{schema}`' in report.splitlines():
            return selector
    if f'* verification: `{r7_buffer.SCHEMA}`' in report.splitlines():
        return r7_buffer.SELECTOR
    if f'* verification: `{static_buffer.SCHEMA}`' in report.splitlines():
        return static_buffer.SELECTOR
    if f'* verification: `{dynamic_div.SCHEMA}`' in report.splitlines():
        return dynamic_div.SELECTOR
    if f'* verification: `{named_three.SCHEMA}`' in report.splitlines():
        return named_three.SELECTOR
    if f'* verification: `{three_output.SCHEMA}`' in report.splitlines():
        return three_output.SELECTOR
    if f'* verification: `{direct_output.SCHEMA}`' in report.splitlines():
        return direct_output.SELECTOR
    if f'* verification: `{nested_output.SCHEMA}`' in report.splitlines():
        return nested_output.SELECTOR
    if f'* verification: `{named_buffer.ROOT_SWITCH_SCHEMA}`' in report.splitlines():
        return named_buffer.ROOT_SWITCH_SELECTOR
    if f'* verification: `{bios_div.SCHEMA}`' in report.splitlines():
        return bios_div.SELECTOR
    if f'* verification: `{named_buffer.GUARDED_ALIAS_SCHEMA}`' in report.splitlines():
        return named_buffer.GUARDED_ALIAS_SELECTOR
    if f'* verification: `{named_buffer.GUARDED_SWITCH_SCHEMA}`' in report.splitlines():
        return named_buffer.GUARDED_SWITCH_SELECTOR
    if f'* verification: `{named_buffer.FAST_FILL_SCHEMA}`' in report.splitlines():
        return named_buffer.FAST_FILL_SELECTOR
    if f'* verification: `{named_buffer.THUNK_PARTIAL_SCHEMA}`' in report.splitlines():
        return named_buffer.THUNK_PARTIAL_SELECTOR
    if f'* verification: `{named_buffer.THUNK_SCRATCH_SCHEMA}`' in report.splitlines():
        return named_buffer.THUNK_SCRATCH_SELECTOR
    if f'* verification: `{named_buffer.THUNK_SCHEMA}`' in report.splitlines():
        return named_buffer.THUNK_SELECTOR
    if f'* verification: `{named_buffer.BIOS_FILL_SCHEMA}`' in report.splitlines():
        return named_buffer.BIOS_FILL_SELECTOR
    if f'* verification: `{named_buffer.BIOS_SQRT_SCHEMA}`' in report.splitlines():
        return named_buffer.BIOS_SQRT_SELECTOR
    if f'* verification: `{named_buffer.SCRATCH_SCHEMA}`' in report.splitlines():
        return named_buffer.SCRATCH_SELECTOR
    if f'* verification: `{named_buffer.SCHEMA}`' in report.splitlines():
        return named_buffer.SELECTOR
    if f'* verification: `{named_buffer.DATAFREE_SCHEMA}`' in report.splitlines():
        return named_buffer.DATAFREE_SELECTOR
    return ACYCLIC_SELECTOR if f'* verification: `{ACYCLIC_SCHEMA}`' in report.splitlines() else SELECTOR


def refine(data, address, mapping):
    return analyze.refine_function(data, address, json.loads(mapping), max_bytes=len(data),
            max_instructions=len(data)//2, rom_end=0x09000000, same_owner_long_branches=True)


def verify(data, address, rom, mapping, index, objects, manifest=None, *, bindings=None,
           selector=SELECTOR, source_fingerprint=None):
    """Replay complete structural/frame/runtime proof before typed provenance."""
    import match
    if selector == mutable_native.SELECTOR:
        return mutable_native.verify_owner(data,address,rom,mapping,index,objects,manifest,bindings)
    if selector == entry.SELECTOR:
        return entry.verify_owner(data,address,rom,mapping,index,objects,manifest,bindings)
    if selector not in (shadow_matrix.SELECTOR, rom_table.SELECTOR, resident_word.SELECTOR, SELECTOR, THUNK_SWITCH_SELECTOR, DIRECT_SWITCH_SELECTOR, ALIGNED_SELECTOR, CYCLIC_SELECTOR, ENTRY_DATA_SWITCH_SELECTOR, ENTRY_SWITCH_SELECTOR, ACYCLIC_SELECTOR, ignored_leaf.SELECTOR, *named_buffer.SELECTORS, static_buffer.SELECTOR, *r6_buffer.PROFILES, r7_buffer.SELECTOR, word_buffer.SELECTOR, descriptor.SELECTOR, watched_switch.SELECTOR, output_alias.SELECTOR, single_store.SELECTOR, *disjunctive.PROFILES, *callee_constant.PROFILES, cursor.SELECTOR, *formal_spill.SELECTORS):
        raise ValueError('unknown complete-owner selector')
    buffer_selector = selector in (resident_word.SELECTOR, *named_buffer.SELECTORS, static_buffer.SELECTOR, *r6_buffer.PROFILES, r7_buffer.SELECTOR, word_buffer.SELECTOR, descriptor.SELECTOR, watched_switch.SELECTOR, output_alias.SELECTOR, single_store.SELECTOR, *disjunctive.PROFILES, *callee_constant.PROFILES, cursor.SELECTOR, *formal_spill.SELECTORS)
    if buffer_selector and len(data) > named_buffer.MAX_BYTES:
        raise ValueError('named-data buffer caller exceeds bounded owner size')
    validate_span(data,address,rom,mapping,index)
    if buffer_selector:
        named_buffer.validate_owner(data,address,rom,mapping,index)
    refinement = refine(data,address,mapping)
    selected_rows=[line.split() for line in index.decode().splitlines()
                   if line.split() and line.split()[0]==f'{address:08X}']
    if not buffer_selector and (len(selected_rows)!=1 or len(selected_rows[0])<4 or int(selected_rows[0][3])!=refinement['instrs']):
        raise ValueError('complete-owner text reachable instruction count differs')
    ins, edges, branches, calls, words = graph.graph(data,address,refinement)
    if selector == shadow_matrix.SELECTOR:
        proof = shadow_matrix.prove(data,address,rom,mapping,index,objects,
            bindings=bindings,source_fingerprint=source_fingerprint)
    elif selector == rom_table.SELECTOR:
        proof = rom_table.prove(data,address,rom,mapping,index,objects,
            bindings=bindings,source_fingerprint=source_fingerprint)
    elif selector == resident_word.SELECTOR:
        proof = resident_word.prove(data,address,rom,mapping,index,objects,
            bindings=bindings,source_fingerprint=source_fingerprint)
    elif selector in (THUNK_SWITCH_SELECTOR,DIRECT_SWITCH_SELECTOR,ALIGNED_SELECTOR,CYCLIC_SELECTOR,ENTRY_SWITCH_SELECTOR,ENTRY_DATA_SWITCH_SELECTOR):
        import framed_switch_inventory as scalar_switch
        if bindings is None:
            raise ValueError('switch owner requires exact typed bindings')
        if selector == THUNK_SWITCH_SELECTOR:
            if not bindings['data'] or bindings['functions']:
                raise ValueError('scalar thunk switch requires named data and excludes function literals')
        elif selector == DIRECT_SWITCH_SELECTOR:
            if bindings['data'] or bindings['functions']:
                raise ValueError('scalar switch excludes named data and function literals')
        elif selector == ENTRY_DATA_SWITCH_SELECTOR:
            if not bindings['data'] or bindings['functions']:
                raise ValueError('two-word switch requires named data and excludes function literals')
        elif bindings['data'] or selector in (ALIGNED_SELECTOR, ENTRY_SWITCH_SELECTOR) and bindings['functions']:
            raise ValueError('aligned switch owner excludes data and function-pointer literals')
        native, verified = scalar_switch.verify(data,address,rom,mapping,index,calls,
            scalar_switch.bind_calls(calls, mapping, address, len(data), len(rom),
                allow_r3=selector == THUNK_SWITCH_SELECTOR),
            selector=scalar_switch.THUNK_SELECTOR if selector == THUNK_SWITCH_SELECTOR else scalar_switch.ENTRY_DATA_SELECTOR if selector == ENTRY_DATA_SWITCH_SELECTOR else scalar_switch.ENTRY_SELECTOR if selector == ENTRY_SWITCH_SELECTOR else scalar_switch.CYCLIC_SELECTOR if selector in (CYCLIC_SELECTOR, DIRECT_SWITCH_SELECTOR) else scalar_switch.SELECTOR)
        proof = dict(schema=THUNK_SWITCH_SCHEMA if selector == THUNK_SWITCH_SELECTOR else DIRECT_SWITCH_SCHEMA if selector == DIRECT_SWITCH_SELECTOR else ENTRY_DATA_SWITCH_SCHEMA if selector == ENTRY_DATA_SWITCH_SELECTOR else ENTRY_SWITCH_SCHEMA if selector == ENTRY_SWITCH_SELECTOR else CYCLIC_SCHEMA if selector == CYCLIC_SELECTOR else ALIGNED_SCHEMA,instructions=len(verified),
            calls=native['calls'],runtime_calls=native['runtime_calls'],partition=native['partition'],
            ordinary_switch_inventory=native)
        if set(ins) != {item.address for item in verified}:
            raise ValueError('aligned switch native instructions differ from complete owner CFG')
    elif selector == spilled_loop.SELECTOR:
        proof = spilled_loop.prove(data, address, rom, mapping, index, objects, bindings)
    elif selector == finite_loop.SELECTOR:
        proof = finite_loop.prove(data, address, rom, mapping, index, objects, bindings)
    elif selector == nested_query.SELECTOR:
        proof = nested_query.prove(data, address, rom, mapping, index, objects, bindings)
    elif selector == query_cont.SELECTOR:
        proof = query_cont.prove(data, address, rom, mapping, index, objects, bindings)
    elif selector == list_query.SELECTOR:
        if address not in list_query.ROOTS:
            raise ValueError('unsupported known-list query root')
        _, _, callback, encoded = list_query.ROOTS[address]
        expected = dict(calls=[[16, 'func_080C7CC0']], data=[],
                        functions=[[len(bytes.fromhex(encoded))-4, f'func_{callback:08X}']], switches=[])
        if type(bindings) is not dict or bindings != expected:
            raise ValueError('known-list query requires exact genuine typed bindings')
        proof = list_query.prove(data,address,rom,mapping,index,selector=selector)
    elif selector == known_query.SELECTOR:
        if type(bindings) is not dict or bindings != dict(
                calls=[[22, 'func_08099840']], data=[],
                functions=[[32, 'func_0809C9E8']], switches=[]):
            raise ValueError('known-query closure requires exact genuine typed bindings')
        proof = known_query.prove(data,address,rom,mapping,index,selector=selector)
    elif selector in (callback_closure.SELECTOR, tree_callback.SELECTOR):
        expected_calls = [[site-address,f'func_{target:08X}']for site,target in sorted(calls.items())]
        if type(bindings) is not dict or set(bindings) != {'calls','data','functions','switches'} or \
                len(data) != 28 or bindings['calls'] != expected_calls or \
                bindings['data'] or bindings['switches'] or \
                bindings['functions'] != [[24,f'func_{struct.unpack_from("<I",data,24)[0]&~1:08X}']]:
            raise ValueError('two-word closure requires exact typed bindings before effect proof')
        module = tree_callback if selector == tree_callback.SELECTOR else callback_closure
        proof = module.prove(data,address,rom,mapping,index,selector=selector)
    elif buffer_selector:
        module = named_three if selector == named_three.SELECTOR else direct_output if selector == direct_output.SELECTOR else dynamic_div if selector == dynamic_div.SELECTOR else three_output if selector == three_output.SELECTOR else bios_div if selector == bios_div.SELECTOR else nested_output if selector == nested_output.SELECTOR else r6_buffer if selector in r6_buffer.PROFILES else word_buffer if selector == word_buffer.SELECTOR else r7_buffer if selector == r7_buffer.SELECTOR else formal_spill if selector in formal_spill.SELECTORS else cursor if selector == cursor.SELECTOR else callee_constant if selector in callee_constant.PROFILES else disjunctive if selector in disjunctive.PROFILES else single_store if selector == single_store.SELECTOR else output_alias if selector == output_alias.SELECTOR else watched_switch if selector == watched_switch.SELECTOR else descriptor if selector == descriptor.SELECTOR else static_buffer if selector == static_buffer.SELECTOR else named_buffer
        if branches or words and selector != named_buffer.ROOT_SWITCH_SELECTOR:
            raise ValueError('named-data buffer caller excludes local BL and word switches')
        for destination in calls.values():
            if selector in (*named_buffer.THUNK_SELECTORS, *local_calls.SELECTORS) and destination in thunk.ALIASES.values():
                continue  # bind_root authenticates the indexed canonical BX and padding.
            match.function_address_target(f'func_{destination:08X}', json.loads(mapping),
                                          address, len(data), len(rom))
        buffers = (local_calls.ConditionalLocalBufferProof if selector in local_calls.SELECTORS else
                   named_three.NamedThreeOutputBufferProof if selector == named_three.SELECTOR else
                   direct_output.DirectOutputBufferProof if selector == direct_output.SELECTOR else
                   dynamic_div.DynamicDivisionBufferProof if selector == dynamic_div.SELECTOR else
                   three_output.ThreeOutputBufferProof if selector == three_output.SELECTOR else
                   named_buffer.RootGuardedSwitchBufferProof if selector == named_buffer.ROOT_SWITCH_SELECTOR else
                   nested_output.NestedOutputBufferProof if selector == nested_output.SELECTOR else
                   r6_buffer.R6FrameCallbackProof if selector in r6_buffer.PROFILES else
                   word_buffer.WordResultCallbackProof if selector == word_buffer.SELECTOR else
                   r7_buffer.StaticCallbackTargetPreservationProof if selector == r7_buffer.SELECTOR else
                   formal_spill.BiosRemainderSpillProof if selector == formal_spill.BIOS_SELECTOR else
                   formal_spill.FormalOutputSpillProof if selector == formal_spill.SELECTOR else
                   cursor.DescriptorCursorValueProof if selector == cursor.SELECTOR else
                   callee_constant.proof_type(selector) if selector in callee_constant.PROFILES else
                   disjunctive.BoundedRestoringScratchProof if selector == disjunctive.BOUNDED_SELECTOR else
                   disjunctive.RestoringCalleeDisjunctiveProof if selector == disjunctive.CALLEE_SELECTOR else
                   disjunctive.RestoringLeafDisjunctiveProof if selector == disjunctive.RESTORING_SELECTOR else
                   disjunctive.DescriptorDisjunctiveAliasProof if selector in disjunctive.PROFILES else
                   single_store.DescriptorSingleStoreProof if selector == single_store.SELECTOR else
                   output_alias.DescriptorOutputAliasProof if selector == output_alias.SELECTOR else
                   watched_switch.WatchedSwitchPreservationProof if selector == watched_switch.SELECTOR else
                   descriptor.ProtectedDescriptorWordProof if selector == descriptor.SELECTOR else
                   static_buffer.StaticCallbackBufferProof if selector == static_buffer.SELECTOR else
                   bios_div.GuardedBiosDivisionProof if selector == bios_div.SELECTOR else
                   named_buffer.GuardedAliasBufferProof if selector == named_buffer.GUARDED_ALIAS_SELECTOR else
                   named_buffer.GuardedSwitchBufferProof if selector == named_buffer.GUARDED_SWITCH_SELECTOR else
                   fast_fill.FastFillSourceProof if selector == named_buffer.FAST_FILL_SELECTOR else
                   named_buffer.ConditionalThunkSelectiveScratchBufferProof if selector == named_buffer.THUNK_PARTIAL_SELECTOR else
                   named_buffer.ConditionalThunkScratchBufferProof if selector == named_buffer.THUNK_SCRATCH_SELECTOR else
                   named_buffer.ConditionalThunkBufferProof if selector in named_buffer.THUNK_SELECTORS else
                   named_buffer.BiosFillSourceProof if selector == named_buffer.BIOS_FILL_SELECTOR else
                   named_buffer.BiosSqrtScratchProof if selector == named_buffer.BIOS_SQRT_SELECTOR else
                   named_buffer.DiscardedReturnScratchProof if selector == named_buffer.SCRATCH_SELECTOR else
                   named_buffer.NamedDataBufferProof)(rom, mapping, index, objects,
                       **({"policy": selector} if selector in local_calls.SELECTORS else {"root": address, "bindings": bindings if bindings is not None else (manifest or {}).get("bindings")}
                           if selector == word_buffer.SELECTOR else {"policy": selector}
                           if selector in r6_buffer.PROFILES else {"policy": r7_buffer.SELECTOR}
                           if selector == r7_buffer.SELECTOR else {}))
        if selector == disjunctive.BOUNDED_SELECTOR:
            buffers.bind_root(address,data)
        if selector == direct_output.SELECTOR:
            buffers.bind_root(address, data)
        if selector in (named_buffer.FAST_FILL_SELECTOR, named_buffer.BIOS_FILL_SELECTOR, *named_buffer.THUNK_SELECTORS, *local_calls.SELECTORS):
            buffers.bind_root(data, address, calls)
        if selector == named_buffer.ROOT_SWITCH_SELECTOR:
            buffers.bind_root(data, address, calls, words)
        if selector in (descriptor.SELECTOR, watched_switch.SELECTOR, output_alias.SELECTOR, single_store.SELECTOR, *disjunctive.PROFILES, *callee_constant.PROFILES, cursor.SELECTOR):
            buffers.check_lifetime(data, address, list(ins.values()))
        verified = match.verify_leaf_instructions(data, address, True, calls, buffer_proof=buffers,
            switch_relocations=words if selector == named_buffer.ROOT_SWITCH_SELECTOR else None)
        if not buffers.dependencies or set(ins) != {item.address for item in verified}:
            raise ValueError('named-data buffer profile requires exact inspected buffer calls')
        if selector in formal_spill.SELECTORS:
            if bindings is None or any(bindings.get(key) for key in ('data','functions','switches')):
                raise ValueError('formal output excludes data/callback/switch composition')
        if selector in (static_buffer.SELECTOR, *r6_buffer.PROFILES, r7_buffer.SELECTOR, word_buffer.SELECTOR, descriptor.SELECTOR) and not buffers.callbacks:
            raise ValueError('static callback profile requires an actual resolved buffer callback')
        proof = {'schema': local_calls.SCHEMAS[selector] if selector in local_calls.SELECTORS else callee_constant.PROFILES[selector] if selector in callee_constant.PROFILES else disjunctive.PROFILES[selector] if selector in disjunctive.PROFILES else named_buffer.DATAFREE_SCHEMA if selector == named_buffer.DATAFREE_SELECTOR else named_buffer.GUARDED_ALIAS_SCHEMA if selector == named_buffer.GUARDED_ALIAS_SELECTOR else formal_spill.BIOS_SCHEMA if selector == formal_spill.BIOS_SELECTOR else r6_buffer.PROFILES[selector][0] if selector in r6_buffer.PROFILES else named_buffer.GUARDED_SWITCH_SCHEMA if selector == named_buffer.GUARDED_SWITCH_SELECTOR else named_buffer.THUNK_SCHEMAS[selector] if selector in named_buffer.THUNK_SELECTORS else named_buffer.FAST_FILL_SCHEMA if selector == named_buffer.FAST_FILL_SELECTOR else named_buffer.BIOS_FILL_SCHEMA if selector == named_buffer.BIOS_FILL_SELECTOR else named_buffer.BIOS_SQRT_SCHEMA if selector == named_buffer.BIOS_SQRT_SELECTOR else named_buffer.SCRATCH_SCHEMA if selector == named_buffer.SCRATCH_SELECTOR else module.SCHEMA, 'instructions': len(verified),
                 'calls': [[site-address, next((name for name,value in thunk.ALIASES.items() if value == target), f'func_{target:08X}') if selector in (*named_buffer.THUNK_SELECTORS, *local_calls.SELECTORS) else f'func_{target:08X}'] for site,target in sorted(calls.items())],
                 'runtime_calls': [], 'partition': graph.partition(data,address,refinement,ins,words),
                 'buffers': {'dependency_budget': buffers.dependency_budget if selector in (named_buffer.GUARDED_ALIAS_SELECTOR, *r6_buffer.PROFILES) else module.MAX_DEPENDENCIES,
                    'owner_byte_budget': named_buffer.MAX_BYTES,
                    'dependencies': [buffers.records[target] for target in sorted(buffers.records)]}}
        if selector in local_calls.SELECTORS:
            proof['buffers']['conditional_local_calls'] = buffers.contract_manifest()
        if selector in named_buffer.THUNK_SELECTORS:
            proof['buffers']['conditional_thunks'] = buffers.thunk_manifest()
        if selector in (named_buffer.THUNK_SCRATCH_SELECTOR, named_buffer.THUNK_PARTIAL_SELECTOR):
            proof['buffers']['normal_return_scratch'] = buffers.scratch_manifest()
        if selector == dynamic_div.SELECTOR:
            proof['buffers']['dynamic_division'] = buffers.division_manifest()
        if selector in (named_three.SELECTOR, three_output.SELECTOR, dynamic_div.SELECTOR):
            proof['buffers']['three_halfword_outputs'] = buffers.nested_manifest()
            proof['buffers']['normal_return_scratch'] = buffers.scratch_manifest()
        if selector == direct_output.SELECTOR:
            proof['buffers']['direct_halfword_outputs'] = buffers.direct_manifest()
            proof['buffers']['normal_return_scratch'] = buffers.scratch_manifest()
        if selector == nested_output.SELECTOR:
            proof['buffers']['nested_halfword_outputs'] = buffers.nested_manifest()
            proof['buffers']['normal_return_scratch'] = buffers.scratch_manifest()
        if selector == named_buffer.ROOT_SWITCH_SELECTOR:
            from local_long_branch_profile import prove_frame
            proof['schema'] = named_buffer.ROOT_SWITCH_SCHEMA
            proof['buffers']['root_guarded_switch'] = buffers.root_manifest()
            proof['frame'] = prove_frame(ins, edges, address, {}, calls,
                stack_aliases=True, buffer_proof=buffers)
        if selector == named_buffer.SCRATCH_SELECTOR:
            scratch = buffers.scratch_manifest()
            if not scratch['observations']:
                raise ValueError('discarded return scratch requires actual checked projections')
            proof['buffers']['normal_return_scratch'] = scratch
        if selector in (named_buffer.GUARDED_SWITCH_SELECTOR, named_buffer.GUARDED_ALIAS_SELECTOR):
            guarded = buffers.guarded_manifest()
            if not guarded['observations']:
                raise ValueError('guarded buffer switch requires an actual inspected switch callee')
            proof['buffers']['guarded_switches'] = guarded
            if selector == named_buffer.GUARDED_ALIAS_SELECTOR:
                proof['buffers']['entry_scratch_overwrites'] = buffers.entry_kill_manifest()
            if selector == named_buffer.GUARDED_SWITCH_SELECTOR:
                proof['buffers']['normal_return_scratch'] = buffers.scratch_manifest()
        if selector == bios_div.SELECTOR:
            proof['buffers']['bios_division'] = buffers.bios_manifest()
            proof['buffers']['guarded_switches'] = buffers.guarded_manifest()
            proof['buffers']['entry_scratch_overwrites'] = buffers.entry_kill_manifest()
        if selector == named_buffer.FAST_FILL_SELECTOR:
            proof['buffers']['bios_fast_fill'] = buffers.bios_manifest()
        if selector == named_buffer.BIOS_FILL_SELECTOR:
            import bios_cpuset_fill_profile as fill
            proof['buffers']['bios_fill'] = buffers.bios_manifest()
            proof['bios_scalar_control_words'] = fill.scalar_control_words(ins, edges, calls, proof['partition'], address)
        if selector == named_buffer.BIOS_SQRT_SELECTOR:
            bios = buffers.bios_manifest()
            if not bios['observations']:
                raise ValueError('BIOS Sqrt profile requires an actual checked wrapper call')
            proof['buffers']['bios_sqrt'] = bios
            proof['buffers']['normal_return_scratch'] = buffers.scratch_manifest()
        if selector == r7_buffer.SELECTOR:
            observations = buffers.preservation_observations()
            if not observations:
                raise ValueError('unwritten-R7 profile requires actual authenticated callback preservation')
            proof['buffers']['r7_preservation'] = dict(
                policy=r7_buffer.policy_manifest(), observations=observations)
        if selector in r6_buffer.PROFILES:
            restorations = buffers.restoration_observations()
            callbacks = buffers.preservation_observations()
            if not restorations or not callbacks or not any(row['value'] is not None for row in restorations):
                raise ValueError('R6 selector requires actual frame restoration and callback effect replay')
            proof['buffers']['r6_restoration'] = dict(policy=r6_buffer.policy_manifest(selector),
                observations=restorations, **{'callback_observations' if selector in r6_buffer.TARGET_POLICIES else 'r7_observations': callbacks})
            if selector in r6_buffer.TARGET_POLICIES:
                proof['buffers']['r6_restoration']['normal_return_scratch'] = buffers.scratch_return_observations()
            if selector == r6_buffer.COMPACT_CLOSURE_SELECTOR:
                proof['buffers']['r6_restoration']['compact_dependency_closure'] = buffers.compact_dependency_closure()
        if selector == word_buffer.SELECTOR:
            proof['buffers']['word_result_callback'] = buffers.effect_manifest()
        if selector in formal_spill.SELECTORS:
            proof['buffers']['formal_output_spill'] = buffers.spill_manifest()
        if selector == formal_spill.BIOS_SELECTOR:
            proof['buffers']['bios_remainder'] = buffers.bios_manifest()
        if selector in (static_buffer.SELECTOR, *r6_buffer.PROFILES, r7_buffer.SELECTOR, word_buffer.SELECTOR, descriptor.SELECTOR, watched_switch.SELECTOR, output_alias.SELECTOR, single_store.SELECTOR, *disjunctive.PROFILES, *callee_constant.PROFILES, cursor.SELECTOR):
            proof['buffers'].update(context_budget=static_buffer.MAX_CONTEXTS,
                                    callbacks=buffers.observations())
        if selector in (output_alias.SELECTOR,single_store.SELECTOR,*disjunctive.PROFILES,*callee_constant.PROFILES, cursor.SELECTOR):
            if selector != disjunctive.BOUNDED_SELECTOR and (not buffers.frame_observations() or not any(
                    row['kind']=='pointer' for row in buffers.word_observations())):
                raise ValueError('descriptor output alias profile requires actual callee stack origin and pointer-word replay')
            proof['buffers'].update(frame_aliases=buffers.frame_observations(),
                native_frame_replays=buffers.native_frame_observations(),
                word_reads=buffers.word_observations(), switch_contexts=buffers.switch_observations(),
                stack_byte_budget=output_alias.MAX_STACK_BYTES,
                lifetime='exact live root and callee frames; allocation after deallocation refused')
        if selector in (single_store.SELECTOR, *disjunctive.PROFILES, *callee_constant.PROFILES, cursor.SELECTOR):
            if selector not in (disjunctive.BOUNDED_SELECTOR, callee_constant.RESTORING_SELECTOR) and not buffers.store_observations():
                raise ValueError('single-word store profile requires an actual bounded STMIA replay')
            proof['buffers']['single_word_stores'] = buffers.store_observations()
        if selector in (disjunctive.RESTORING_SELECTOR,disjunctive.CALLEE_SELECTOR,disjunctive.BOUNDED_SELECTOR,callee_constant.RESTORING_SELECTOR):
            proof['buffers']['restoring_leaf_aliases'] = buffers.restoring_leaf_manifest()
        if selector == callee_constant.RESTORING_SELECTOR:
            proof['buffers']['discarded_return_scratch'] = buffers.scratch_manifest()
        if selector == disjunctive.BOUNDED_SELECTOR:
            proof['buffers']['root_discarded_scratch'] = buffers.root_scratch_manifest()
        if selector in (*disjunctive.PROFILES,*callee_constant.PROFILES, cursor.SELECTOR):
            paths = buffers.alias_observations()
            if selector not in (disjunctive.BOUNDED_SELECTOR, callee_constant.RESTORING_SELECTOR) and not any(len({tuple(state['state'][0]) for state in row['states']
                            if state['site'] == site}) > 1
                       for row in paths for site in {state['site'] for state in row['states']}):
                raise ValueError('disjunctive alias profile requires an actual unequal alias join')
            proof['buffers'].update(alias_path_state_budget=disjunctive.MAX_PATH_STATES,
                alias_alternatives=paths, return_effects='every exact return alternative replays in its caller')
        if selector in (*callee_constant.PROFILES,cursor.SELECTOR):
            constants = buffers.constant_observations()
            if not constants['transfers']:
                raise ValueError('callee constant profile requires an actual native-proved constant transfer')
            proof['buffers']['callee_constants'] = constants
        if selector == cursor.SELECTOR:
            values = buffers.cursor_observations()
            if not any(not row['pointee_is_local'] for row in values['transfers']):
                raise ValueError('cursor value profile requires an actual transfer without pointee access permission')
            proof['buffers']['cursor_values'] = values
        if selector == watched_switch.SELECTOR:
            if not buffers.switch_observations():
                raise ValueError('watched switch profile requires an actual watched switch context')
            proof['buffers'].update(switch_contexts=buffers.switch_observations(),
                word_reads=buffers.word_observations(),
                lifetime='allocated root-frame words; allocation after deallocation refused')
        if selector == descriptor.SELECTOR:
            if not any(row['kind']=='pointer' for row in buffers.word_observations()):
                raise ValueError('descriptor profile requires an actual exact pointer-word reload')
            proof['buffers'].update(word_reads=buffers.word_observations(),
                lifetime='allocated root-frame words; allocation after deallocation refused')
    elif selector in (ACYCLIC_SELECTOR, ignored_leaf.SELECTOR):
        if branches or words:
            raise ValueError('acyclic owner excludes local BL and word switches')
        for destination in calls.values():
            match.function_address_target(f'func_{destination:08X}', json.loads(mapping),
                                          address, len(data), len(rom))
        aliases = None
        if selector == ignored_leaf.SELECTOR:
            entries = json.loads(mapping)
            row = next(row for row in entries if int(row['rom'], 16) == address)
            if type(row.get('instrs')) is not int or row['instrs'] != len(ins):
                raise ValueError('ignored leaf caller JSON reachable instruction count differs')
            aliases = ignored_leaf.IgnoredLeafAliasProof(rom,mapping,index,objects,address,len(data),calls)
        verified = match.verify_leaf_instructions(data,address,True,calls,
            acyclic_state_budget=ACYCLIC_STATE_BUDGET, ignored_leaf_alias_proof=aliases)
        if {item.address for item in verified} != set(ins):
            raise ValueError('acyclic native verification differs from complete owner CFG')
        proof = {'schema': ACYCLIC_SCHEMA, 'state_budget': ACYCLIC_STATE_BUDGET,
                 'instructions': len(verified), 'calls': [[site-address, f'func_{target:08X}']
                    for site,target in sorted(calls.items())], 'runtime_calls': [],
                 'partition': graph.partition(data,address,refinement,ins,words)}
        if aliases is not None:
            if not aliases.observations:
                raise ValueError('ignored leaf selector requires an actual discarded incoming alias')
            proof.update(schema=ignored_leaf.SCHEMA, ignored_leaf_aliases=aliases.manifest())
    else:
        proof = runtime.verify(data,address,rom,mapping,refinement)
    ordinary = {'calls':proof['calls'], 'data':[], 'functions':[]}
    if bindings is None:
        if manifest is None:
            raise ValueError('typed owner bindings are required')
        bindings = manifest.get('bindings')
    if type(bindings) is not dict or set(bindings) != {'calls','data','functions','switches'} or \
            bindings['calls'] != sorted(proof['calls'] + proof['runtime_calls']):
        raise ValueError('owner bindings do not cover every exact reached external call')
    ordinary.update(data=bindings['data'],functions=bindings['functions'])
    if selector == shadow_matrix.SELECTOR:
        # The closed original-binding adapter has authenticated memcpy to this
        # actual indexed helper. Existing literal validation uses its entry name.
        helper = proof['local_shadow_halfword_matrix']['helper']
        ordinary['calls'] = [[66, f'func_{helper:08X}']]
    if selector in (bios_div.SELECTOR, direct_output.SELECTOR, nested_output.SELECTOR, named_buffer.SCRATCH_SELECTOR, named_buffer.BIOS_SQRT_SELECTOR, named_buffer.BIOS_FILL_SELECTOR, named_buffer.GUARDED_SWITCH_SELECTOR, named_buffer.GUARDED_ALIAS_SELECTOR) and (bindings['functions'] or bindings['switches']):
        raise ValueError('discarded return scratch excludes callback literals and switches')
    if selector in (named_buffer.SELECTOR, named_buffer.BIOS_FILL_SELECTOR) and (not bindings['data'] or bindings['functions'] or bindings['switches']):
        raise ValueError('named-data buffers require actual named object relocations and exclude function literals')
    if selector in (named_buffer.FAST_FILL_SELECTOR, named_buffer.DATAFREE_SELECTOR) and any(bindings[key] for key in ('data', 'functions', 'switches')):
        raise ValueError('data-free caller excludes object, function and switch literals')
    if selector == named_buffer.ROOT_SWITCH_SELECTOR and (not bindings['data'] or
            bindings['functions'] or not bindings['switches']):
        raise ValueError('root buffer switch requires typed data and local switch words without function literals')
    if selector in named_buffer.THUNK_SELECTORS and (not bindings['data'] or bindings['switches']):
        raise ValueError('conditional buffer thunks require actual named data and exclude switches')
    if selector in (*local_calls.SELECTORS, *named_buffer.THUNK_SELECTORS, query_cont.SELECTOR, nested_query.SELECTOR, finite_loop.SELECTOR, spilled_loop.SELECTOR):
        # Indexed canonical bodies and exact call sites were authenticated above.
        ordinary['calls'] = [[site, name] for site, name in ordinary['calls']
                             if name not in thunk.ALIASES]
    _, literals = match.function_address_bindings(data,address,rom,mapping,objects,ordinary,
                                                 allow_empty_functions=True)
    if bindings['switches'] != [[offset, addend] for offset,addend in sorted(words.items())]:
        raise ValueError('owner local relocations do not equal guarded switch words')
    match.verify_data_literals(ins.values(),address,literals)
    functions = {offset:(name,struct.unpack_from('<I',data,offset)[0])
                 for offset,name in bindings['functions']}
    thunk.verify_literal_bindings(data,address,ins.values(),calls,mapping,functions)
    data_literals = ({offset:literals[offset] for offset,name,addend in bindings['data']}
                     if selector in (*local_calls.SELECTORS, *named_buffer.THUNK_SELECTORS, query_cont.SELECTOR, nested_query.SELECTOR, finite_loop.SELECTOR, spilled_loop.SELECTOR) else literals)
    thunk.verify_data_bindings(calls,data_literals,match.parse_data_symbols(objects),json.loads(mapping))
    # All actual address-domain PC words require typed object/function provenance.
    # Exact local switch words are proved separately; numerical scalars remain scalar.
    address_words = {row['address']-address for row in proof['partition']['words']
        if row['load_sites'] and not row['switch_word'] and
        (0x02000000 <= row['value'] < 0x04000000 or
         0x04000000 <= row['value'] < 0x08000000 or
         0x08000000 <= row['value'] < 0x09000000)}
    if selector == named_buffer.BIOS_FILL_SELECTOR:
        controls = {row[0] for row in proof['bios_scalar_control_words']}
        if controls & set(literals):
            raise ValueError('BIOS scalar control cannot also be a named object')
        address_words -= controls
    if address_words != set(literals):
        raise ValueError('owner address literals require exact typed object/function coverage')
    schema = local_calls.SCHEMAS[selector] if selector in local_calls.SELECTORS else spilled_loop.SCHEMA if selector == spilled_loop.SELECTOR else finite_loop.SCHEMA if selector == finite_loop.SELECTOR else nested_query.SCHEMA if selector == nested_query.SELECTOR else query_cont.SCHEMA if selector == query_cont.SELECTOR else list_query.SCHEMA if selector == list_query.SELECTOR else known_query.SCHEMA if selector == known_query.SELECTOR else tree_callback.SCHEMA if selector == tree_callback.SELECTOR else callback_closure.SCHEMA if selector == callback_closure.SELECTOR else THUNK_SWITCH_SCHEMA if selector == THUNK_SWITCH_SELECTOR else DIRECT_SWITCH_SCHEMA if selector == DIRECT_SWITCH_SELECTOR else ENTRY_DATA_SWITCH_SCHEMA if selector == ENTRY_DATA_SWITCH_SELECTOR else ENTRY_SWITCH_SCHEMA if selector == ENTRY_SWITCH_SELECTOR else \
        shadow_matrix.SCHEMA if selector == shadow_matrix.SELECTOR else \
        rom_table.SCHEMA if selector == rom_table.SELECTOR else \
        resident_word.SCHEMA if selector == resident_word.SELECTOR else \
        r6_buffer.PROFILES[selector][0] if selector in r6_buffer.PROFILES else \
        word_buffer.SCHEMA if selector == word_buffer.SELECTOR else \
        r7_buffer.SCHEMA if selector == r7_buffer.SELECTOR else \
        formal_spill.BIOS_SCHEMA if selector == formal_spill.BIOS_SELECTOR else \
        formal_spill.SCHEMA if selector == formal_spill.SELECTOR else \
        cursor.SCHEMA if selector == cursor.SELECTOR else \
        callee_constant.PROFILES[selector] if selector in callee_constant.PROFILES else \
        disjunctive.PROFILES[selector] if selector in disjunctive.PROFILES else \
        single_store.SCHEMA if selector == single_store.SELECTOR else \
        output_alias.SCHEMA if selector == output_alias.SELECTOR else \
        watched_switch.SCHEMA if selector == watched_switch.SELECTOR else \
        descriptor.SCHEMA if selector == descriptor.SELECTOR else \
        static_buffer.SCHEMA if selector == static_buffer.SELECTOR else \
        dynamic_div.SCHEMA if selector == dynamic_div.SELECTOR else \
        named_three.SCHEMA if selector == named_three.SELECTOR else three_output.SCHEMA if selector == three_output.SELECTOR else \
        direct_output.SCHEMA if selector == direct_output.SELECTOR else \
        nested_output.SCHEMA if selector == nested_output.SELECTOR else \
        named_buffer.DATAFREE_SCHEMA if selector == named_buffer.DATAFREE_SELECTOR else \
        named_buffer.ROOT_SWITCH_SCHEMA if selector == named_buffer.ROOT_SWITCH_SELECTOR else \
        bios_div.SCHEMA if selector == bios_div.SELECTOR else \
        named_buffer.GUARDED_ALIAS_SCHEMA if selector == named_buffer.GUARDED_ALIAS_SELECTOR else \
        named_buffer.GUARDED_SWITCH_SCHEMA if selector == named_buffer.GUARDED_SWITCH_SELECTOR else \
        named_buffer.THUNK_SCHEMAS[selector] if selector in named_buffer.THUNK_SELECTORS else named_buffer.FAST_FILL_SCHEMA if selector == named_buffer.FAST_FILL_SELECTOR else named_buffer.BIOS_FILL_SCHEMA if selector == named_buffer.BIOS_FILL_SELECTOR else named_buffer.BIOS_SQRT_SCHEMA if selector == named_buffer.BIOS_SQRT_SELECTOR else \
        named_buffer.SCRATCH_SCHEMA if selector == named_buffer.SCRATCH_SELECTOR else \
        named_buffer.SCHEMA if selector == named_buffer.SELECTOR else \
        ignored_leaf.SCHEMA if selector == ignored_leaf.SELECTOR else \
        ACYCLIC_SCHEMA if selector == ACYCLIC_SELECTOR else SCHEMA
    if selector in (ALIGNED_SELECTOR,CYCLIC_SELECTOR):
        if not words or proof['runtime_calls'] or bindings['data'] or selector == ALIGNED_SELECTOR and bindings['functions']:
            raise ValueError('aligned switch owner requires actual guarded local table and ordinary direct calls only')
        import addressed_signed_runtime_profile as alignment
        proof['terminal_alignment_policy'] = dict(
            schema='canonical-external-two-byte-thumb-nop-v1',
            scope='external assembler alignment only; complete sized FUNC remains unchanged',
            producer_sha256=sha(Path(alignment.__file__).read_bytes()))
        if selector == CYCLIC_SELECTOR:
            if not bindings['functions'] or not proof['ordinary_switch_inventory']['local_CFG_cycles']:
                raise ValueError('cyclic switch owner requires actual local CFG cycles and typed function words')
            proof['typed_function_words'] = bindings['functions']
        schema = CYCLIC_SCHEMA if selector == CYCLIC_SELECTOR else ALIGNED_SCHEMA
    observed={'profile':schema,
              'proof':proof,'bindings':bindings}
    if manifest is not None and text(observed)!=text(manifest):
        raise ValueError('owner manifest differs from complete fresh native replay')
    return observed, list(ins.values())



def preflight(data,address,rom,mapping,index,objects, *, selector=SELECTOR):
    """Inventory bindings derive only reached words and current named objects.

    This record has no source/ELF credit. Later compiler relocations must independently
    reconstruct the same calls, local tables and typed object/function words.
    """
    import match
    if selector == mutable_native.SELECTOR:
        raise ValueError('native admission requires original resident-owner ELF bindings')
    if selector == entry.SELECTOR:
        raise ValueError('entry native admission requires original resident-owner ELF bindings')
    if selector in (shadow_matrix.SELECTOR, rom_table.SELECTOR, resident_word.SELECTOR):
        raise ValueError('resident native admission requires original ELF and source bindings')
    refinement=refine(data,address,mapping)
    instructions,edges,branches,calls,words=graph.graph(data,address,refinement)
    partition=graph.partition(data,address,refinement,instructions,words)
    entries=json.loads(mapping);names=match.parse_data_symbols(objects)
    reverse={value:name for name,value in thunk.ALIASES.items()}
    bindings={'calls':[[site-address,reverse.get(target,'__udivsi3' if target==match.UDIVSI3_ADDRESS
                     else f'func_{target:08X}')]for site,target in sorted(calls.items())],
              'data':[],'functions':[],'switches':[[offset,value]for offset,value in sorted(words.items())]}
    for word in partition['words']:
        value=word['value'];offset=word['address']-address
        if not word['load_sites'] or word['switch_word'] or not 0x02000000<=value<0x09000000:
            continue
        owners=[row for row in entries if int(row['rom'],16)==value&~1]
        if owners:
            if value%2!=1 or len(owners)!=1:
                raise ValueError('literal code entry requires unambiguous typed Thumb function pointer')
            bindings['functions'].append([offset,f'func_{value&~1:08X}'])
        else:
            candidates=sorted(name for name,base in names.items() if base==value)
            if not candidates:
                raise ValueError(f'owner literal requires genuine named object proof at {value:08X}')
            bindings['data'].append([offset,candidates[0],0])
    observed,verified=verify(data,address,rom,mapping,index,objects,bindings=bindings,
                             selector=selector)
    return observed,verified,refinement


def original_bindings(image,address,rom,mapping,objects, *, selector=SELECTOR, index=None):
    """Validate every original relocation, with no rewriting of the input ELF."""
    import match
    if selector == integer_three.SELECTOR:
        selector = integer_native.SELECTOR
    if selector == entry.SELECTOR:
        return entry.original_bindings(image,address,rom,mapping,index)
    if selector == shadow_matrix.SELECTOR:
        return shadow_matrix.original_bindings(image,address,rom,mapping,index,objects)
    if image['type']!=1:
        raise ValueError('owner requires original relocatable ELF')
    match.allocated_text_only(image)
    symbol,offset=match.function_record(image,f'func_{address:08X}',address,True)
    size=symbol['size']
    if selector in (integer_native.SELECTOR, numeric_switch.SELECTOR):
        import addressed_signed_runtime_profile as alignment
        alignment.terminal_alignment(image,symbol)
    if selector in (ALIGNED_SELECTOR,CYCLIC_SELECTOR,*r6_buffer.ALIGNED_POLICIES):
        import addressed_signed_runtime_profile as alignment
        alignment.terminal_alignment(image,symbol)
        if len(image['text']) != size+2:
            raise ValueError('aligned owner requires actual external two-byte Thumb alignment')
    external_alignment=(selector in (numeric_switch.SELECTOR,integer_native.SELECTOR,*named_buffer.SELECTORS,ALIGNED_SELECTOR,CYCLIC_SELECTOR,*r6_buffer.ALIGNED_POLICIES) and size%4==2 and
                        len(image['text'])==size+2 and image['text'][size:]==b'\xc0\x46')
    if offset or (size!=len(image['text']) and not external_alignment) or any(
            item['type']==2 and item is not symbol and item['section'] or
            item['type']==1 and item['section'] or re.fullmatch(r'\$a(?:\..*)?',item['name'])
            for item in image['symbols']):
        raise ValueError('owner requires sole complete Thumb ELF function')
    entries=json.loads(mapping); names=match.parse_data_symbols(objects)
    result={'calls':[],'data':[],'functions':[],'switches':[]}; targets={}; occupied=set()
    decoder=match.Cs(match.CS_ARCH_ARM,match.CS_MODE_THUMB);decoder.detail=True
    for section_index in image['relocations']:
        section=image['sections'][section_index]
        if section[1]!=9 or section[7]!=image['text_index'] or section[9]!=8 or section[5]%8:
            raise ValueError('owner requires canonical .text REL relocations')
        symbols=image['symbol_tables'].get(section[6])
        for position in range(0,section[5],8):
            site,info=struct.unpack_from('<II',image['section_data'][section_index],position)
            kind=info&255
            if symbols is None or info>>8>=len(symbols) or kind not in (2,10) or \
                    site<0 or site+4>size or occupied.intersection(range(site,site+4)):
                raise ValueError('invalid, unsupported or overlapping owner relocation')
            occupied.update(range(site,site+4)); target=symbols[info>>8];name=target['name']
            if kind==2 and target['section']:
                if target['type']!=3 or target['section']!=image['text_index'] or \
                        target['value'] or target['bind'] or (address+site)%4:
                    raise ValueError('local owner relocation requires zero-valued .text section symbol')
                addend=struct.unpack_from('<I',image['text'],site)[0]
                result['switches'].append([site,addend]);continue
            if target['section'] or target['value'] or target['bind']!=1 or \
                    sum(item['name']==name for item in image['symbols'])!=1:
                raise ValueError('owner requires unique undefined zero-valued global symbols')
            if kind==10:
                instruction=next(decoder.disasm(image['text'][site:site+4],address+site),None)
                if site%2 or target['type'] not in (0,2) or instruction is None or \
                        instruction.id!=match.ARM_INS_BL or instruction.size!=4 or \
                        instruction.operands[0].imm!=address+site:
                    raise ValueError('owner call requires canonical Thumb BL zero addend')
                destination=(integer_native.scalar.OPERATIONS[name] if selector in (integer_native.SELECTOR, integer_two.SELECTOR, integer_words.SELECTOR, integer_locals.SELECTOR, integer_data.SELECTOR) and name in integer_native.scalar.OPERATIONS else
                    thunk.ALIASES[name] if name in thunk.ALIASES else
                    match.UDIVSI3_ADDRESS if name=='__udivsi3' else
                    match.function_address_target(name,entries,address,size,len(rom)))
                result['calls'].append([site,name]);targets[name]=(destination,False)
            else:
                if (address+site)%4:
                    raise ValueError('unaligned owner literal relocation')
                addend=struct.unpack_from('<i',image['text'],site)[0]
                if name.startswith('func_'):
                    if target['type'] not in (0,2) or addend:
                        raise ValueError('function pointer requires canonical zero addend')
                    destination=match.function_address_target(name,entries,address,size,len(rom))
                    result['functions'].append([site,name]);targets[name]=(destination,False)
                else:
                    if target['type'] not in (0,1) or name not in names:
                        raise ValueError('unmapped or non-object owner literal')
                    result['data'].append([site,name,addend]);targets[name]=(names[name],True)
    if any(item['name'] and not item['section'] and item['name'] not in targets
           for item in image['symbols']):
        raise ValueError('unresolved owner symbol outside exact binding roles')
    for records in result.values():records.sort()
    if selector == numeric_switch.SELECTOR:
        if result['functions'] or not all(result[role] for role in ('calls', 'data', 'switches')) or \
                any(addend for _, _, addend in result['data']) or any(
                    numeric_switch.reserved(value) for value, is_object in targets.values() if not is_object):
            raise ValueError('numeric switch requires ordinary calls, zero-addend data and local table words')
    elif selector in (integer_two.SELECTOR, integer_words.SELECTOR, integer_locals.SELECTOR, integer_data.SELECTOR):
        if any(result[role] for role in ('functions','switches')) or not result['data'] or \
                any(addend for _, _, addend in result['data']) or \
                not set(targets).intersection(integer_native.scalar.OPERATIONS) or set(targets).intersection(thunk.ALIASES):
            raise ValueError('six-word integer source requires canonical integer calls and zero-addend named objects')
    elif selector == integer_native.SELECTOR:
        if any(result[role] for role in ('data','functions','switches')) or \
                not set(targets).intersection(integer_native.scalar.OPERATIONS) or \
                set(targets).intersection(thunk.ALIASES):
            raise ValueError('canonical integer source requires call-only compiler integer identities')
    elif selector in (*local_calls.SELECTORS, query_cont.SELECTOR, nested_query.SELECTOR, finite_loop.SELECTOR, spilled_loop.SELECTOR):
        if any(match.is_udivsi3_address(destination) or thunk.reserved(destination) and name not in thunk.ALIASES
               for name, (destination, is_object) in targets.items() if not is_object):
            raise ValueError("known query continuation excludes unsupported compiler runtimes")
        thunk.dependencies([name for name in targets if name in thunk.ALIASES], rom)
    elif selector in named_buffer.THUNK_SELECTORS:
        if any(match.is_udivsi3_address(destination) or thunk.reserved(destination) and name not in thunk.ALIASES
               for name,(destination,is_object) in targets.items() if not is_object) or not any(
               name in thunk.ALIASES for name in targets):
            raise ValueError('conditional buffer thunks require canonical compiler call names without division')
        thunk.dependencies([name for name in targets if name in thunk.ALIASES], rom)
    elif selector == THUNK_SWITCH_SELECTOR:
        runtime_names = set(targets) & set(thunk.ALIASES)
        if runtime_names != {'_call_via_r3'} or '__udivsi3' in targets:
            raise ValueError('scalar thunk switch requires canonical R3 only, without arithmetic runtime')
    elif selector in (shadow_matrix.SELECTOR, rom_table.SELECTOR, multiple_native.SELECTOR, DIRECT_SWITCH_SELECTOR, ENTRY_DATA_SWITCH_SELECTOR, ENTRY_SWITCH_SELECTOR, ALIGNED_SELECTOR, CYCLIC_SELECTOR, mutable_native.SELECTOR, resident_word.SELECTOR, ACYCLIC_SELECTOR, ignored_leaf.SELECTOR, *named_buffer.SELECTORS, static_buffer.SELECTOR, *r6_buffer.PROFILES, r7_buffer.SELECTOR, word_buffer.SELECTOR, descriptor.SELECTOR, watched_switch.SELECTOR, output_alias.SELECTOR, single_store.SELECTOR, *disjunctive.PROFILES, *callee_constant.PROFILES, cursor.SELECTOR, *formal_spill.SELECTORS):
        if any(destination in thunk.ALIASES.values() or match.is_udivsi3_address(destination)
               for destination,is_object in targets.values() if not is_object):
            raise ValueError('acyclic owner excludes arithmetic runtimes and indirect thunks')
    elif selector != SELECTOR:
        raise ValueError('unknown complete-owner selector')
    elif '__udivsi3' not in targets or not any(name in thunk.ALIASES for name in targets):
        raise ValueError('owner profile requires actual compiler UDIV and indirect thunk calls')
    return result,targets


def object_bytes(runner,workspace,args,original,address,rom,mapping,objects, *, selector=SELECTOR, index=None):
    import match
    fixed_configuration(args)
    preprocessed=runner.read_binary(workspace+'/f.i').decode()
    thunk.namespace(preprocessed)
    from plausible import strip_comments_and_strings
    reserved = (r'\b(?:__divsi3|__modsi3|__udivsi3|__umodsi3)\b'
                if selector in (integer_three.SELECTOR, integer_native.SELECTOR, integer_two.SELECTOR, integer_words.SELECTOR, integer_locals.SELECTOR, integer_data.SELECTOR) else r'\b__udivsi3\b')
    if re.search(reserved,strip_comments_and_strings(preprocessed)):
        raise ValueError('division identifiers are reserved for compiler emission')
    bindings,targets=original_bindings(original,address,rom,mapping,objects,selector=selector,index=index)
    definitions=['.syntax unified','.thumb']
    for name,(value,is_object) in sorted(targets.items()):
        if selector == entry.SELECTOR and name == f'func_{address:08X}':
            continue  # Resident function is defined by f.o, never an absolute alias.
        definitions += [f'.global {name}',f'.type {name}, %'+('object' if is_object else 'function'),
                        f'.set {name}, 0x{value:08X}' if is_object else
                        f'.thumb_set {name}, 0x{value|1:08X}']
    runner.write_text(workspace+'/f.known.s','\n'.join(definitions)+'\n')
    runner.write_text(workspace+'/f.ld',f'SECTIONS {{ .text 0x{address:08X} : {{ *(.text) *(.glue_7) *(.glue_7t) }} '
        '.data 0 : { *(.data) } .bss 0 : { *(.bss) } .ARM.attributes 0 : { *(.ARM.attributes) } '
        '.unexpected 0 : { *(.vfp11_veneer) *(.v4_bx) *(.iplt) *(.igot.plt) } '
        '.rel.iplt 0 : { *(.rel.iplt) } ASSERT(SIZEOF(.unexpected)==0,"unexpected stubs") '
        'ASSERT(SIZEOF(.rel.iplt)==0,"unexpected relocations") /DISCARD/ : { *(.comment) *(.note.GNU-stack) } }')
    quoted=shlex.quote(workspace)
    runner.sh(f'{args.assembler} -mthumb-interwork {quoted}/f.known.s -o {quoted}/f.known.o')
    runner.sh(f'{args.linker} --fatal-warnings --no-undefined --no-relax --orphan-handling=error '
              f'-T {quoted}/f.ld -e func_{address:08X} {quoted}/f.o {quoted}/f.known.o -o {quoted}/f.elf')
    linked=match.elf_image(runner.read_binary(workspace+'/f.elf'))
    if selector == entry.SELECTOR:
        return entry.linked_bytes(original,linked,address,rom,mapping,index,bindings,targets),bindings
    match.allocated_text_only(linked)
    record,offset=match.function_record(linked,f'func_{address:08X}',address,True)
    original_record,_=match.function_record(original,f'func_{address:08X}',address,True)
    if selector in (ALIGNED_SELECTOR,CYCLIC_SELECTOR,*r6_buffer.ALIGNED_POLICIES):
        import addressed_signed_runtime_profile as alignment
        alignment.terminal_alignment(linked,record)
    if linked['type']!=2 or offset or linked['relocations'] or \
            record['size']!=original_record['size'] or len(linked['text'])!=len(original['text']):
        raise ValueError('linker altered complete owner extent or retained relocations')
    expected=bytearray(original['text']);decoder=match.Cs(match.CS_ARCH_ARM,match.CS_MODE_THUMB);decoder.detail=True
    for site,name in bindings['calls']:
        item=next(decoder.disasm(linked['text'][site:site+4],address+site),None)
        if item is None or item.id!=match.ARM_INS_BL or item.size!=4 or \
                item.operands[0].imm!=targets[name][0]:
            raise ValueError('linked canonical call target differs from original symbol binding')
        expected[site:site+4]=linked['text'][site:site+4]
    for site,addend in bindings['switches']:struct.pack_into('<I',expected,site,address+addend)
    for site,name,addend in bindings['data']:struct.pack_into('<I',expected,site,targets[name][0]+addend)
    for site,name in bindings['functions']:struct.pack_into('<I',expected,site,targets[name][0]|1)
    if bytes(expected)!=linked['text']:
        raise ValueError('linker changed bytes outside exact original relocations')
    return linked['text'][:record['size']],bindings


def fingerprint(address,data,manifest,source,mapping,index,objects,rom,original_elf=None):
    import match
    parts=[manifest['profile'].encode(),address.to_bytes(4,'little'),data,text(manifest).encode(),source.encode(),
           mapping,index,b'absent' if objects is None else objects,hashlib.sha256(rom).digest(),
           text([match.DEFAULT_CC,match.DEFAULT_CPP,match.DEFAULT_AS,match.DEFAULT_OBJCOPY,
                 match.DEFAULT_LD,match.DEFAULT_FLAGS]).encode()]
    if manifest['profile'] in (shadow_matrix.SCHEMA, rom_table.SCHEMA, numeric_switch.SCHEMA, integer_three.SCHEMA, integer_data.SCHEMA, integer_locals.SCHEMA, integer_two.SCHEMA, integer_words.SCHEMA, integer_native.SCHEMA, multiple_native.SCHEMA, THUNK_SWITCH_SCHEMA, DIRECT_SWITCH_SCHEMA, ENTRY_DATA_SWITCH_SCHEMA, ENTRY_SWITCH_SCHEMA, ALIGNED_SCHEMA, CYCLIC_SCHEMA, mutable_native.SCHEMA, resident_word.SCHEMA, entry.NATIVE_SCHEMA, *named_buffer.SCHEMAS, static_buffer.SCHEMA, *r6_buffer.SCHEMAS, r7_buffer.SCHEMA, word_buffer.SCHEMA, descriptor.SCHEMA, watched_switch.SCHEMA, output_alias.SCHEMA, single_store.SCHEMA, *disjunctive.PROFILES.values(), *callee_constant.PROFILES.values(), cursor.SCHEMA, *formal_spill.SCHEMAS):
        if not isinstance(original_elf, bytes):
            raise ValueError('named-data buffer evidence requires original ELF identity')
        parts.append(hashlib.sha256(original_elf).digest())
    return sha(b''.join(len(value).to_bytes(8,'little')+value for value in parts))


def build(root,address,args=None,expected=None, *, selector=SELECTOR):
    """Fresh fixed-toolchain compilation and complete original-ELF provenance."""
    import match
    from match_evidence import source_paths,source_fingerprint,mapping_snapshot,data_snapshot,report_rom_path
    root=Path(root)
    args=args or argparse.Namespace(cc=match.DEFAULT_CC,cpp=match.DEFAULT_CPP,assembler=match.DEFAULT_AS,
        objcopy=match.DEFAULT_OBJCOPY,linker=match.DEFAULT_LD,flags=match.DEFAULT_FLAGS)
    fixed_configuration(args)
    environment_reader = (known_query.environment_fingerprint if selector in local_calls.SELECTORS
        else integer_three.environment_fingerprint if selector == integer_three.SELECTOR
        else numeric_switch.environment_fingerprint if selector == numeric_switch.SELECTOR
        else integer_data.environment_fingerprint if selector == integer_data.SELECTOR
        else integer_locals.environment_fingerprint if selector == integer_locals.SELECTOR
        else integer_two.environment_fingerprint if selector == integer_two.SELECTOR
        else integer_words.environment_fingerprint if selector == integer_words.SELECTOR
        else integer_native.environment_fingerprint if selector == integer_native.SELECTOR
        else multiple_native.environment_fingerprint if selector == multiple_native.SELECTOR
        else mutable_native.environment_fingerprint if selector == mutable_native.SELECTOR
        else entry.environment_fingerprint if selector == entry.SELECTOR
        else known_query.environment_fingerprint if selector in (shadow_matrix.SELECTOR, rom_table.SELECTOR, known_query.SELECTOR)
        else list_query.environment_fingerprint if selector in (spilled_loop.SELECTOR, finite_loop.SELECTOR, nested_query.SELECTOR, query_cont.SELECTOR, list_query.SELECTOR) else None)
    environment=environment_reader() if environment_reader else None
    source=source_fingerprint(root,address);mapping=mapping_snapshot(root);index=index_snapshot(root)
    objects=data_snapshot(root);rom_path=report_rom_path(root);rom=Path(rom_path).read_bytes()
    candidates=list((root/'src').rglob(f'{address:08X}.c'))
    if len(candidates)!=1:raise ValueError('owner requires one unique source')
    (root/'build').mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='owner_replay_',dir=root/'build') as directory:
        capture=Path(directory)
        for path in source_paths(root,address):
            destination=capture/path.relative_to(root);destination.parent.mkdir(parents=True,exist_ok=True)
            destination.write_bytes(path.read_bytes())
        runner=match.Runner(match.DEFAULT_CC,'Ubuntu',match.DEFAULT_WSL_PATH,root=capture,timeout=120)
        with runner.workspace() as workspace:
            raw,_,original=match.compile_object(runner,workspace,args,capture,address,
                                               candidates[0].relative_to(root).as_posix())
            data,bindings=object_bytes(runner,workspace,args,original,address,rom,mapping,objects,
                                      selector=selector,index=index)
            if selector in (numeric_switch.SELECTOR, integer_two.SELECTOR, integer_words.SELECTOR, integer_locals.SELECTOR, integer_data.SELECTOR):
                native = numeric_switch if selector == numeric_switch.SELECTOR else integer_two if selector == integer_two.SELECTOR else integer_words if selector == integer_words.SELECTOR else integer_data if selector == integer_data.SELECTOR else integer_locals
                manifest,count=native.verify_original(raw,runner.read_binary(workspace+'/f.elf'),
                    address,rom,mapping,index,bindings,expected,objects=objects)
            elif selector in (integer_three.SELECTOR, integer_native.SELECTOR, multiple_native.SELECTOR):
                native = integer_three if selector == integer_three.SELECTOR else integer_native if selector == integer_native.SELECTOR else multiple_native
                manifest,count=native.verify_original(raw,runner.read_binary(workspace+'/f.elf'),
                    address,rom,mapping,index,bindings,expected)
            else:
                manifest,instructions=verify(data,address,rom,mapping,index,objects,expected,
                                             bindings=bindings,selector=selector,source_fingerprint=source)
                count=len(instructions)
        check=match._run_replay_process([sys.executable,str(Path(__file__).with_name('plausible.py')),
            '--quiet','--addr',f'0x{address:08X}','--json']+[str(p) for p in source_paths(capture,address)],capture,120)
        findings,allowed=match.plausibility_result(check,address)
        if findings or allowed or source_fingerprint(capture,address)!=source:
            raise ValueError('owner source is implausible or changed during captured compilation')
    if source_fingerprint(root,address)!=source or mapping_snapshot(root)!=mapping or \
            index_snapshot(root)!=index or data_snapshot(root)!=objects or \
            report_rom_path(root)!=rom_path or Path(rom_path).read_bytes()!=rom:
        raise ValueError('owner source, maps, headers or ROM changed during native verification')
    if environment is not None and environment != environment_reader():
        raise ValueError('entry admission producers, selected binaries or runtime changed during compilation')
    return data,manifest,source,mapping,index,objects,rom,count,raw


def render(address,result):
    import match
    data,manifest,source,mapping,index,objects,rom,count,original_elf=result
    numeric_switch_selected = manifest['profile'] == numeric_switch.SCHEMA
    integer_data_selected = manifest['profile'] == integer_data.SCHEMA
    integer_locals_selected = manifest['profile'] == integer_locals.SCHEMA
    integer_two_selected = manifest['profile'] == integer_two.SCHEMA
    integer_words_selected = manifest['profile'] == integer_words.SCHEMA
    integer_three_selected = manifest['profile'] == integer_three.SCHEMA
    integer_selected = manifest['profile'] == integer_native.SCHEMA
    multiple_selected = manifest['profile'] == multiple_native.SCHEMA
    mutable_selected = manifest['profile'] == mutable_native.SCHEMA
    recursive = manifest['profile'] == entry.NATIVE_SCHEMA
    shadow_matrix_selected = manifest['profile'] == shadow_matrix.SCHEMA
    rom_table_selected = manifest['profile'] == rom_table.SCHEMA
    resident_selected = manifest['profile'] == resident_word.SCHEMA
    word_selected = manifest['profile'] == word_buffer.SCHEMA
    r6_profile = next(((selector, flow) for selector, (schema, flow) in
                       r6_buffer.PROFILES.items() if schema == manifest['profile']), None)
    r6_selected = r6_profile is not None
    r7_selected = manifest['profile'] == r7_buffer.SCHEMA
    spilled = manifest['profile'] in formal_spill.SCHEMAS
    aligned = manifest['profile'] in (ALIGNED_SCHEMA,CYCLIC_SCHEMA)
    entry_switch = manifest['profile'] in (ENTRY_SWITCH_SCHEMA, ENTRY_DATA_SWITCH_SCHEMA)
    scalar_switch = manifest['profile'] in (THUNK_SWITCH_SCHEMA, DIRECT_SWITCH_SCHEMA)
    acyclic = manifest['profile'] == ACYCLIC_SCHEMA
    ignored = manifest['profile'] == ignored_leaf.SCHEMA
    cursor_value = manifest['profile'] == cursor.SCHEMA
    constant = manifest['profile'] in callee_constant.PROFILES.values()
    alternatives = manifest['profile'] in disjunctive.PROFILES.values()
    store = manifest['profile'] == single_store.SCHEMA
    output = manifest['profile'] == output_alias.SCHEMA
    switch = manifest['profile'] == watched_switch.SCHEMA
    words = manifest['profile'] == descriptor.SCHEMA
    static = manifest['profile'] == static_buffer.SCHEMA
    buffers = manifest['profile'] in (shadow_matrix.SCHEMA, rom_table.SCHEMA, resident_word.SCHEMA, *named_buffer.SCHEMAS, static_buffer.SCHEMA, *r6_buffer.SCHEMAS, r7_buffer.SCHEMA, word_buffer.SCHEMA, descriptor.SCHEMA, watched_switch.SCHEMA, output_alias.SCHEMA, single_store.SCHEMA, *disjunctive.PROFILES.values(), *callee_constant.PROFILES.values(), cursor.SCHEMA, *formal_spill.SCHEMAS)
    evidence={'address':address,'bytes':len(data),'instructions':count,'source_sha256':source,
        'mapping_sha256':sha(mapping),'index_sha256':sha(index),'objects_sha256':None if objects is None else sha(objects),
        'rom_sha256':sha(rom),'compiler':[match.DEFAULT_CC,match.DEFAULT_FLAGS],
        'manifest':manifest,'fingerprint':fingerprint(address,data,manifest,source,mapping,index,objects,rom,
                                                     original_elf if numeric_switch_selected or integer_three_selected or integer_data_selected or integer_locals_selected or integer_two_selected or integer_words_selected or integer_selected or multiple_selected or buffers or recursive or mutable_selected or aligned or entry_switch or scalar_switch else None)}
    if numeric_switch_selected or integer_three_selected or integer_data_selected or integer_locals_selected or integer_two_selected or integer_words_selected or integer_selected or multiple_selected or buffers or recursive or mutable_selected or aligned or entry_switch or scalar_switch:
        evidence['original_elf_sha256'] = sha(original_elf)
    return '\n'.join([f'# 0x{address:08X}','',f'* verification: `{manifest["profile"]}`',
        f'* owner runtime: {next(key for key, value in local_calls.SCHEMAS.items() if value == manifest["profile"]) if manifest["profile"] in local_calls.SCHEMAS.values() else spilled_loop.SELECTOR if manifest["profile"] == spilled_loop.SCHEMA else finite_loop.SELECTOR if manifest["profile"] == finite_loop.SCHEMA else nested_query.SELECTOR if manifest["profile"] == nested_query.SCHEMA else query_cont.SELECTOR if manifest["profile"] == query_cont.SCHEMA else list_query.SELECTOR if manifest["profile"] == list_query.SCHEMA else known_query.SELECTOR if manifest["profile"] == known_query.SCHEMA else tree_callback.SELECTOR if manifest["profile"] == tree_callback.SCHEMA else callback_closure.SELECTOR if manifest["profile"] == callback_closure.SCHEMA else numeric_switch.SELECTOR if numeric_switch_selected else integer_data.SELECTOR if integer_data_selected else integer_locals.SELECTOR if integer_locals_selected else integer_two.SELECTOR if integer_two_selected else integer_words.SELECTOR if integer_words_selected else integer_three.SELECTOR if integer_three_selected else integer_native.SELECTOR if integer_selected else multiple_native.SELECTOR if multiple_selected else THUNK_SWITCH_SELECTOR if manifest["profile"] == THUNK_SWITCH_SCHEMA else DIRECT_SWITCH_SELECTOR if manifest["profile"] == DIRECT_SWITCH_SCHEMA else ENTRY_DATA_SWITCH_SELECTOR if manifest["profile"] == ENTRY_DATA_SWITCH_SCHEMA else ENTRY_SWITCH_SELECTOR if entry_switch else CYCLIC_SELECTOR if manifest["profile"] == CYCLIC_SCHEMA else ALIGNED_SELECTOR if aligned else mutable_native.SELECTOR if mutable_selected else entry.SELECTOR if recursive else shadow_matrix.SELECTOR if shadow_matrix_selected else rom_table.SELECTOR if rom_table_selected else resident_word.SELECTOR if resident_selected else word_buffer.SELECTOR if word_selected else r6_profile[0] if r6_selected else r7_buffer.SELECTOR if r7_selected else formal_spill.BIOS_SELECTOR if manifest["profile"] == formal_spill.BIOS_SCHEMA else formal_spill.SELECTOR if spilled else cursor.SELECTOR if cursor_value else next(selector for selector,schema in callee_constant.PROFILES.items() if schema == manifest["profile"]) if constant else next(selector for selector, schema in disjunctive.PROFILES.items() if schema == manifest["profile"]) if alternatives else single_store.SELECTOR if store else output_alias.SELECTOR if output else watched_switch.SELECTOR if switch else descriptor.SELECTOR if words else static_buffer.SELECTOR if static else dynamic_div.SELECTOR if manifest["profile"] == dynamic_div.SCHEMA else named_three.SELECTOR if manifest["profile"] == named_three.SCHEMA else three_output.SELECTOR if manifest["profile"] == three_output.SCHEMA else direct_output.SELECTOR if manifest["profile"] == direct_output.SCHEMA else nested_output.SELECTOR if manifest["profile"] == nested_output.SCHEMA else named_buffer.ROOT_SWITCH_SELECTOR if manifest["profile"] == named_buffer.ROOT_SWITCH_SCHEMA else bios_div.SELECTOR if manifest["profile"] == bios_div.SCHEMA else named_buffer.GUARDED_ALIAS_SELECTOR if manifest["profile"] == named_buffer.GUARDED_ALIAS_SCHEMA else named_buffer.GUARDED_SWITCH_SELECTOR if manifest["profile"] == named_buffer.GUARDED_SWITCH_SCHEMA else named_buffer.THUNK_PARTIAL_SELECTOR if manifest["profile"] == named_buffer.THUNK_PARTIAL_SCHEMA else named_buffer.THUNK_SCRATCH_SELECTOR if manifest["profile"] == named_buffer.THUNK_SCRATCH_SCHEMA else named_buffer.THUNK_SELECTOR if manifest["profile"] == named_buffer.THUNK_SCHEMA else named_buffer.FAST_FILL_SELECTOR if manifest["profile"] == named_buffer.FAST_FILL_SCHEMA else named_buffer.BIOS_SQRT_SELECTOR if manifest["profile"] == named_buffer.BIOS_SQRT_SCHEMA else named_buffer.SCRATCH_SELECTOR if manifest["profile"] == named_buffer.SCRATCH_SCHEMA else named_buffer.DATAFREE_SELECTOR if manifest["profile"] == named_buffer.DATAFREE_SCHEMA else named_buffer.SELECTOR if buffers else ignored_leaf.SELECTOR if ignored else ACYCLIC_SELECTOR if acyclic else SELECTOR}',
        f'* control flow: {local_calls.CONTROL_FLOW if manifest["profile"] in local_calls.SCHEMAS.values() else spilled_loop.CONTROL_FLOW if manifest["profile"] == spilled_loop.SCHEMA else finite_loop.CONTROL_FLOW if manifest["profile"] == finite_loop.SCHEMA else nested_query.CONTROL_FLOW if manifest["profile"] == nested_query.SCHEMA else query_cont.CONTROL_FLOW if manifest["profile"] == query_cont.SCHEMA else list_query.CONTROL_FLOW if manifest["profile"] == list_query.SCHEMA else known_query.CONTROL_FLOW if manifest["profile"] == known_query.SCHEMA else tree_callback.CONTROL_FLOW if manifest["profile"] == tree_callback.SCHEMA else callback_closure.CONTROL_FLOW if manifest["profile"] == callback_closure.SCHEMA else numeric_switch.CONTROL_FLOW if numeric_switch_selected else integer_data.CONTROL_FLOW if integer_data_selected else integer_locals.CONTROL_FLOW if integer_locals_selected else integer_two.CONTROL_FLOW if integer_two_selected else integer_words.CONTROL_FLOW if integer_words_selected else integer_three.CONTROL_FLOW if integer_three_selected else integer_native.CONTROL_FLOW if integer_selected else multiple_native.CONTROL_FLOW if multiple_selected else THUNK_SWITCH_CONTROL_FLOW if manifest["profile"] == THUNK_SWITCH_SCHEMA else DIRECT_SWITCH_CONTROL_FLOW if manifest["profile"] == DIRECT_SWITCH_SCHEMA else ENTRY_DATA_SWITCH_CONTROL_FLOW if manifest["profile"] == ENTRY_DATA_SWITCH_SCHEMA else ENTRY_SWITCH_CONTROL_FLOW if entry_switch else CYCLIC_CONTROL_FLOW if manifest["profile"] == CYCLIC_SCHEMA else ALIGNED_CONTROL_FLOW if manifest["profile"] == ALIGNED_SCHEMA else mutable_native.CONTROL_FLOW if mutable_selected else entry.CONTROL_FLOW if recursive else shadow_matrix.CONTROL_FLOW if shadow_matrix_selected else rom_table.CONTROL_FLOW if rom_table_selected else resident_word.CONTROL_FLOW if resident_selected else word_buffer.CONTROL_FLOW if word_selected else r6_profile[1] if r6_selected else r7_buffer.CONTROL_FLOW if r7_selected else formal_spill.BIOS_CONTROL_FLOW if manifest["profile"] == formal_spill.BIOS_SCHEMA else formal_spill.CONTROL_FLOW if spilled else cursor.CONTROL_FLOW if cursor_value else callee_constant.control_flow(next(selector for selector,schema in callee_constant.PROFILES.items() if schema == manifest["profile"])) if constant else disjunctive.CONTROL_FLOW if alternatives else single_store.CONTROL_FLOW if store else output_alias.CONTROL_FLOW if output else watched_switch.CONTROL_FLOW if switch else descriptor.CONTROL_FLOW if words else static_buffer.CONTROL_FLOW if static else dynamic_div.CONTROL_FLOW if manifest["profile"] == dynamic_div.SCHEMA else named_three.CONTROL_FLOW if manifest["profile"] == named_three.SCHEMA else three_output.CONTROL_FLOW if manifest["profile"] == three_output.SCHEMA else direct_output.CONTROL_FLOW if manifest["profile"] == direct_output.SCHEMA else nested_output.CONTROL_FLOW if manifest["profile"] == nested_output.SCHEMA else named_buffer.ROOT_SWITCH_CONTROL_FLOW if manifest["profile"] == named_buffer.ROOT_SWITCH_SCHEMA else bios_div.CONTROL_FLOW if manifest["profile"] == bios_div.SCHEMA else named_buffer.GUARDED_ALIAS_CONTROL_FLOW if manifest["profile"] == named_buffer.GUARDED_ALIAS_SCHEMA else named_buffer.GUARDED_SWITCH_CONTROL_FLOW if manifest["profile"] == named_buffer.GUARDED_SWITCH_SCHEMA else named_buffer.THUNK_PARTIAL_CONTROL_FLOW if manifest["profile"] == named_buffer.THUNK_PARTIAL_SCHEMA else named_buffer.THUNK_SCRATCH_CONTROL_FLOW if manifest["profile"] == named_buffer.THUNK_SCRATCH_SCHEMA else named_buffer.THUNK_CONTROL_FLOW if manifest["profile"] == named_buffer.THUNK_SCHEMA else named_buffer.FAST_FILL_CONTROL_FLOW if manifest["profile"] == named_buffer.FAST_FILL_SCHEMA else named_buffer.BIOS_FILL_CONTROL_FLOW if manifest["profile"] == named_buffer.BIOS_FILL_SCHEMA else named_buffer.BIOS_SQRT_CONTROL_FLOW if manifest["profile"] == named_buffer.BIOS_SQRT_SCHEMA else named_buffer.SCRATCH_CONTROL_FLOW if manifest["profile"] == named_buffer.SCRATCH_SCHEMA else named_buffer.DATAFREE_CONTROL_FLOW if manifest["profile"] == named_buffer.DATAFREE_SCHEMA else named_buffer.CONTROL_FLOW if buffers else ignored_leaf.CONTROL_FLOW if ignored else ACYCLIC_CONTROL_FLOW if acyclic else CONTROL_FLOW}',
        '* verified extent: complete ELF function symbol, including literal pools',
        '* relocations: none','* source plausibility: plausible','* hand-asm allow list: not listed',
        f'* owner runtime evidence: `{text(evidence)}`',f'* compiled : `{data.hex()}`',
        f'* ROM bytes: `{data.hex()}` ({len(data)} bytes)','',
        f'**MATCH - byte identical** - {len(data)}/{len(data)} bytes',''])


def report_matches(report,root,address):
    if _replay.get():return False
    token=_replay.set(True)
    try:
        if not selected(report):return False
        lines=[line for line in report.splitlines() if line.startswith('* owner runtime evidence: `')]
        if len(lines)!=1:return False
        encoded=lines[0][len('* owner runtime evidence: `'):-1]
        def unique(pairs):
            result={}
            for key,value in pairs:
                if key in result:raise ValueError('duplicate owner evidence key')
                result[key]=value
            return result
        evidence=json.loads(encoded,object_pairs_hook=unique)
        if text(evidence)!=encoded:return False
        result=build(root,address,expected=evidence['manifest'],selector=selector_for_report(report))
        return render(address,result)==report
    except (OSError,ValueError,KeyError,TypeError,IndexError,RuntimeError,subprocess.SubprocessError):
        return False
    finally:_replay.reset(token)


def issue(root,address,args):
    import match
    if args.mode!='thumb' or args.control_flow_profile!='ordinary' or \
            args.software_double_profile or args.software_double_remainder_profile or \
            args.function_address_profile or args.switch_profile or args.label or \
            args.wsl!='Ubuntu' or args.wsl_path!=match.DEFAULT_WSL_PATH:
        raise ValueError('owner profile requires its isolated fixed Thumb selector')
    if args.owner_runtime_profile in (*r6_buffer.PROFILES, r7_buffer.SELECTOR, word_buffer.SELECTOR, resident_word.SELECTOR) and any(
            getattr(args, name, None) for name in ('signed_quotient_profile',
                'signed_runtime_profile', 'addressed_signed_runtime_profile',
                'switch_data_profile')):
        raise ValueError('unwritten-R7 selector excludes other profile policies')
    if args.owner_runtime_profile in (entry.SELECTOR, mutable_native.SELECTOR) and any(
            getattr(args, name, None) for name in ('signed_quotient_profile',
                'signed_runtime_profile', 'addressed_signed_runtime_profile',
                'switch_data_profile')):
        raise ValueError('entry selector excludes other profile policies')
    if args.owner_runtime_profile in (numeric_switch.SELECTOR, integer_three.SELECTOR, integer_data.SELECTOR, integer_locals.SELECTOR, integer_two.SELECTOR, integer_words.SELECTOR, integer_native.SELECTOR, multiple_native.SELECTOR) and any(
            getattr(args, name, None) for name in ('signed_quotient_profile',
                'signed_runtime_profile', 'unsigned_runtime_profile',
                'addressed_signed_runtime_profile', 'switch_data_profile')):
        raise ValueError('multiple-switch source selector excludes mixed runtime/data policies')
    if args.owner_runtime_profile in (nested_query.SELECTOR, query_cont.SELECTOR, shadow_matrix.SELECTOR, rom_table.SELECTOR,known_query.SELECTOR,list_query.SELECTOR) and any(
            getattr(args, name, None) for name in ('signed_quotient_profile',
                'signed_runtime_profile', 'unsigned_runtime_profile',
                'addressed_signed_runtime_profile', 'switch_data_profile')):
        raise ValueError('known-query closure excludes mixed runtime/data policies')
    result=build(root,address,args,selector=args.owner_runtime_profile)
    report=render(address,result)
    if args.emit:
        output=(Path(root)/args.emit).resolve()
        if (Path(root)/'build').resolve() not in output.parents or output.exists():
            raise ValueError('--emit requires a new file beneath build/')
        output.parent.mkdir(parents=True,exist_ok=True)
        with output.open('xb') as stream:stream.write(result[0])
    if not args.no_write:
        path=Path(root)/'docs/match'/f'{address:08X}.md';path.parent.mkdir(parents=True,exist_ok=True)
        path.write_text(report)
    control_flow = local_calls.CONTROL_FLOW if args.owner_runtime_profile in local_calls.SELECTORS else spilled_loop.CONTROL_FLOW if args.owner_runtime_profile == spilled_loop.SELECTOR else finite_loop.CONTROL_FLOW if args.owner_runtime_profile == finite_loop.SELECTOR else nested_query.CONTROL_FLOW if args.owner_runtime_profile == nested_query.SELECTOR else query_cont.CONTROL_FLOW if args.owner_runtime_profile == query_cont.SELECTOR else list_query.CONTROL_FLOW if args.owner_runtime_profile == list_query.SELECTOR else known_query.CONTROL_FLOW if args.owner_runtime_profile == known_query.SELECTOR else tree_callback.CONTROL_FLOW if args.owner_runtime_profile == tree_callback.SELECTOR else callback_closure.CONTROL_FLOW if args.owner_runtime_profile == callback_closure.SELECTOR else numeric_switch.CONTROL_FLOW if args.owner_runtime_profile == numeric_switch.SELECTOR else integer_data.CONTROL_FLOW if args.owner_runtime_profile == integer_data.SELECTOR else integer_locals.CONTROL_FLOW if args.owner_runtime_profile == integer_locals.SELECTOR else integer_two.CONTROL_FLOW if args.owner_runtime_profile == integer_two.SELECTOR else integer_words.CONTROL_FLOW if args.owner_runtime_profile == integer_words.SELECTOR else integer_three.CONTROL_FLOW if args.owner_runtime_profile == integer_three.SELECTOR else integer_native.CONTROL_FLOW if args.owner_runtime_profile == integer_native.SELECTOR else multiple_native.CONTROL_FLOW if args.owner_runtime_profile == multiple_native.SELECTOR else THUNK_SWITCH_CONTROL_FLOW if args.owner_runtime_profile == THUNK_SWITCH_SELECTOR else DIRECT_SWITCH_CONTROL_FLOW if args.owner_runtime_profile == DIRECT_SWITCH_SELECTOR else ENTRY_DATA_SWITCH_CONTROL_FLOW if args.owner_runtime_profile == ENTRY_DATA_SWITCH_SELECTOR else ENTRY_SWITCH_CONTROL_FLOW if args.owner_runtime_profile == ENTRY_SWITCH_SELECTOR else \
        CYCLIC_CONTROL_FLOW if args.owner_runtime_profile == CYCLIC_SELECTOR else \
        ALIGNED_CONTROL_FLOW if args.owner_runtime_profile == ALIGNED_SELECTOR else \
        mutable_native.CONTROL_FLOW if args.owner_runtime_profile == mutable_native.SELECTOR else \
        shadow_matrix.CONTROL_FLOW if args.owner_runtime_profile == shadow_matrix.SELECTOR else \
        rom_table.CONTROL_FLOW if args.owner_runtime_profile == rom_table.SELECTOR else \
        resident_word.CONTROL_FLOW if args.owner_runtime_profile == resident_word.SELECTOR else \
        entry.CONTROL_FLOW if args.owner_runtime_profile == entry.SELECTOR else \
        word_buffer.CONTROL_FLOW if args.owner_runtime_profile == word_buffer.SELECTOR else \
        r6_buffer.PROFILES[args.owner_runtime_profile][1] if args.owner_runtime_profile in r6_buffer.PROFILES else \
        r7_buffer.CONTROL_FLOW if args.owner_runtime_profile == r7_buffer.SELECTOR else \
        formal_spill.BIOS_CONTROL_FLOW if args.owner_runtime_profile == formal_spill.BIOS_SELECTOR else \
        cursor.CONTROL_FLOW if args.owner_runtime_profile == cursor.SELECTOR else \
        callee_constant.control_flow(args.owner_runtime_profile) if args.owner_runtime_profile in callee_constant.PROFILES else \
        disjunctive.CONTROL_FLOW if args.owner_runtime_profile == disjunctive.SELECTOR else \
        single_store.CONTROL_FLOW if args.owner_runtime_profile == single_store.SELECTOR else \
        output_alias.CONTROL_FLOW if args.owner_runtime_profile == output_alias.SELECTOR else \
        watched_switch.CONTROL_FLOW if args.owner_runtime_profile == watched_switch.SELECTOR else \
        descriptor.CONTROL_FLOW if args.owner_runtime_profile == descriptor.SELECTOR else \
        static_buffer.CONTROL_FLOW if args.owner_runtime_profile == static_buffer.SELECTOR else \
        dynamic_div.CONTROL_FLOW if args.owner_runtime_profile == dynamic_div.SELECTOR else \
        named_three.CONTROL_FLOW if args.owner_runtime_profile == named_three.SELECTOR else three_output.CONTROL_FLOW if args.owner_runtime_profile == three_output.SELECTOR else \
        direct_output.CONTROL_FLOW if args.owner_runtime_profile == direct_output.SELECTOR else \
        nested_output.CONTROL_FLOW if args.owner_runtime_profile == nested_output.SELECTOR else \
        named_buffer.DATAFREE_CONTROL_FLOW if args.owner_runtime_profile == named_buffer.DATAFREE_SELECTOR else \
        named_buffer.GUARDED_ALIAS_CONTROL_FLOW if args.owner_runtime_profile == named_buffer.GUARDED_ALIAS_SELECTOR else \
        named_buffer.GUARDED_SWITCH_CONTROL_FLOW if args.owner_runtime_profile == named_buffer.GUARDED_SWITCH_SELECTOR else \
        named_buffer.SCRATCH_CONTROL_FLOW if args.owner_runtime_profile == named_buffer.SCRATCH_SELECTOR else \
        named_buffer.THUNK_PARTIAL_CONTROL_FLOW if args.owner_runtime_profile == named_buffer.THUNK_PARTIAL_SELECTOR else named_buffer.THUNK_SCRATCH_CONTROL_FLOW if args.owner_runtime_profile == named_buffer.THUNK_SCRATCH_SELECTOR else named_buffer.THUNK_CONTROL_FLOW if args.owner_runtime_profile == named_buffer.THUNK_SELECTOR else named_buffer.FAST_FILL_CONTROL_FLOW if args.owner_runtime_profile == named_buffer.FAST_FILL_SELECTOR else named_buffer.BIOS_FILL_CONTROL_FLOW if args.owner_runtime_profile == named_buffer.BIOS_FILL_SELECTOR else named_buffer.CONTROL_FLOW if args.owner_runtime_profile == named_buffer.SELECTOR else \
        ignored_leaf.CONTROL_FLOW if args.owner_runtime_profile == ignored_leaf.SELECTOR else \
        ACYCLIC_CONTROL_FLOW if args.owner_runtime_profile == ACYCLIC_SELECTOR else CONTROL_FLOW
    print(f'extent    {len(result[0])} bytes (complete ELF symbol; {control_flow}; no relocations)')
    print('verdict MATCH - byte identical')
    return 0
