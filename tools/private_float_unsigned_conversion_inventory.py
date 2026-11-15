"""Compose the real comparison, signed conversion and selected-record float closures."""
import hashlib
import json
from pathlib import Path

import software_float_profile as runtime
import private_float_argument_effects_inventory as argument_base
import private_float_comparison_effects_inventory as comparison
import private_float_scalar_conversion_effects_inventory as scalar_conversion
import private_float_selected_record_inventory as selected_record

SELECTOR = 'private-float-unsigned-conversion-effects-inventory-v1'
SCHEMA = 'thumb-private-float-unsigned-conversion-effects-inventory-v1'
policy = argument_base.policy
CONTRACT = ('complete pinned comparison/signed-conversion/selected-record float closures; '
            'fixed RAM record readability is a conditional premise and loaded values remain unknown; '
            'no initialized contents, numeric conversion or IEEE/C definedness equivalence, '
            'physical memory, nonalias, nonescape or universal termination theorem')
HELPERS = tuple((name, next(record for record in runtime.IDENTITIES if record[0] == address), policy())
                for name, address in (('private-comparison', 0x0814413C),
                                      ('private-signed-conversion', 0x08144280),
                                      ('private-addition', 0x08143C84)))
ROOT_HELPERS = ('private-comparison', 'private-signed-conversion',
                'private-addition', 'private-signed-conversion')
COMPILER_ALIASES = {'__ltsf2': 'private-comparison',
                    '__fixsfsi': 'private-signed-conversion', '__addsf3': 'private-addition'}
DEPENDENCIES = (comparison, scalar_conversion, selected_record)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def text(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def verify(data, address, rom, mapping, index, *, selector, manifest=None):
    import match
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    import owner_runtime_profile as operations
    from software_double_profile import indices, span_record
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('private float conversion requires its explicit inventory-only selector')
    if any(type(value) is not bytes for value in (data, rom, mapping, index)) or type(address) is not int:
        raise ValueError('private float conversion requires exact immutable typed inputs')
    if sha(rom) != runtime.ROM_SHA256:
        raise ValueError('private float conversion requires the approved complete ROM identity')
    owner.validate_span(data, address, rom, mapping, index)
    entries, rows = indices(mapping, index)
    refinement = owner.refine(data, address, mapping)
    instructions, edges, branches, calls, words = graph.graph(data, address, refinement)
    expected = [next(record[0] for role, record, _ in HELPERS if role == name)
                for name in ROOT_HELPERS]
    if branches or words or [target for _, target in sorted(calls.items())] != expected:
        raise ValueError('private float conversion requires exactly comparison/conversion/addition/conversion calls')
    if span_record(address, address+len(data), entries, rows, rom)['instrs'] != len(instructions):
        raise ValueError('private float conversion complete dual-index count differs')
    operations.verify_operations(instructions, edges, address, branches, calls, refinement)
    partition = graph.partition(data, address, refinement, instructions, words)
    dependencies, helper_records = {}, []
    for (name, (start, end, count, digest), bounds), producer in zip(HELPERS, DEPENDENCIES):
        record = span_record(start, end, entries, rows, rom)
        body = rom[start-match.ROM_BASE:end-match.ROM_BASE]
        if record['instrs'] != count or sha(body) != digest or start < address+len(data) and end > address:
            raise ValueError('private float conversion helper complete body/count/ownership identity differs')
        inventory, decoded = producer.verify(body, start, rom, mapping, index, selector=producer.SELECTOR)
        proof = inventory['caller']
        if len(decoded) != count or inventory['address'] != start or inventory['end'] != end or \
                inventory['body_sha256'] != digest or inventory['mapping_sha256'] != sha(mapping) or \
                inventory['index_sha256'] != sha(index):
            raise ValueError('private float conversion dependency identity or context differs')
        dependencies[start] = proof
        helper_records.append(dict(name=name, address=start, end=end, instructions=count,
            body_sha256=digest, inventory=inventory, native_proof=proof))
    caller = runtime.prove_runtime(rom, entries, address, address+len(data), len(instructions),
        dependencies, call_edges=tuple(sorted(calls.items())), scalar_entries=(address,),
        argument_effect_policy=policy(), absolute_read_policy=selected_record.ABSOLUTE_POLICY)
    if caller['argument_effects']['reads'] or caller['writes'] or caller['stack_reads']:
        raise ValueError('private float conversion has undischarged external formal or incoming effects')
    if caller['native_edges'] != [[site, list(targets)] for site, targets in sorted(edges.items())]:
        raise ValueError('private float conversion native and complete CFG edges differ')
    if caller['absolute_reads']['reads'] != selected_record.ABSOLUTE_POLICY['reads']:
        raise ValueError('private float conversion must retain every conditional child absolute read')
    source_pins = {Path(module.__file__).name: sha(Path(module.__file__).read_bytes())
                   for module in (runtime, argument_base, comparison, scalar_conversion,
                                  selected_record, match, match.armv4t, owner, graph, operations)}
    source_pins[Path(__file__).name] = sha(Path(__file__).read_bytes())
    observed = dict(schema=SCHEMA, selector=SELECTOR, inventory_only=True,
        complete_native_structural_proof=True, complete_argument_effect_proof=True,
        address=address, end=address+len(data), instructions=len(instructions),
        body_sha256=sha(data), ROM_sha256=sha(rom), mapping_sha256=sha(mapping), index_sha256=sha(index),
        private_bindings=[[site, next(name for name, record, _ in HELPERS if record[0] == target)]
                          for site, target in sorted(calls.items())],
        helper_closure=helper_records, caller=caller, partition=partition,
        external_reads=caller['absolute_reads']['reads'],
        external_formal_reads=caller['argument_effects']['reads'], external_writes=caller['writes'],
        conditional_absolute_read_premise=caller['absolute_reads'],
        numeric_input_preconditions=[], numeric_return_facts=[], source_or_ELF_admission=False,
        arithmetic_C_equivalence=False, memory_safety_claim=False, physical_memory_claim=False,
        nonescape_claim=False, universal_termination_claim=False,
        claim='complete actual scalar closure and conditional fixed-record reads; all numeric results unknown',
        producer_source_sha256=source_pins)
    if manifest is not None and text(manifest) != text(observed):
        raise ValueError('private float conversion manifest differs from fresh native proof')
    return observed, [instructions[site] for site in sorted(instructions)]
