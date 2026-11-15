"""Explicit scalar division with initialized private bytes and discarded R2/R3."""
import hashlib
import json
from pathlib import Path

import dynamic_division_buffer_profile as dynamic
import software_float_profile as runtime

SELECTOR = 'private-scalar-division-byte-locals-inventory-v1'
SCHEMA = 'thumb-private-scalar-division-byte-locals-inventory-v1'
HELPERS = (('signed-division', dynamic.integer.canonical.DIVISION_IDENTITIES[0], None),)
ROOT_HELPER_SEQUENCES = (('signed-division', 'signed-division'),)
COMPILER_ALIASES = {'__divsi3': 'signed-division'}
CONTRACT = ('complete canonical signed division including the real zero hook; '
            'initialized byte/halfword/word accesses within live abstract locals; '
            'reached returns restore r4-r11/SP/control; residual local R2/R3 values '
            'require the explicit discarded-scratch return ABI; no numeric '
            'equivalence, physical memory, nonescape or termination theorem')


def verify(data, address, rom, mapping, index, *, selector, manifest=None):
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('scalar division locals require their explicit inventory selector')
    if any(type(value) is not bytes for value in (data, rom, mapping, index)) or type(address) is not int:
        raise ValueError('scalar division locals require immutable bytes and an integer address')
    if hashlib.sha256(rom).hexdigest() != runtime.ROM_SHA256:
        raise ValueError('scalar division locals require the approved complete ROM')
    owner.validate_span(data, address, rom, mapping, index)
    refinement = owner.refine(data, address, mapping)
    instructions, edges, branches, calls, words = graph.graph(data, address, refinement)
    if branches or words or list(target for _, target in sorted(calls.items())) != [dynamic.DIV, dynamic.DIV]:
        raise ValueError('scalar division locals require exactly two canonical direct division calls')
    proof = dynamic.prove(data, address, rom, mapping, index, selector=dynamic.SELECTOR)
    frame = proof['frame']
    if not frame['local_aliases']['accesses'] or not proof['residual_local_scratch']:
        raise ValueError('scalar division locals require actual private accesses and discarded scratch')
    if proof['external_memory_reads'] or proof['external_memory_writes'] or proof['incoming_stack_reads']:
        raise ValueError('scalar division locals cannot import external or incoming memory permission')
    producer = {Path(module.__file__).name: hashlib.sha256(Path(module.__file__).read_bytes()).hexdigest()
                for module in (dynamic, runtime, owner, graph, graph.armv4t)}
    producer[Path(__file__).name] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    observed = dict(schema=SCHEMA, selector=SELECTOR, inventory_only=True,
        private_bindings=[[site, 'signed-division'] for site in sorted(calls)],
        address=address, end=address+len(data), instructions=len(instructions),
        body_sha256=hashlib.sha256(data).hexdigest(), ROM_sha256=hashlib.sha256(rom).hexdigest(),
        mapping_sha256=hashlib.sha256(mapping).hexdigest(), index_sha256=hashlib.sha256(index).hexdigest(),
        partition=proof['partition'], native_closure=proof, contract=CONTRACT,
        discarded_exit_scratch_policy=dynamic.SCRATCH_POLICY,
        discarded_scratch_ABI_premise=dynamic.frame.DISCARDED_SCRATCH_CONTRACT,
        external_reads=[], external_writes=[], incoming_stack_reads=[],
        numeric_input_preconditions=[], numeric_return_facts=[],
        source_or_ELF_admission=False, arithmetic_C_equivalence=False,
        physical_memory_claim=False, native_nonescape_proof=False,
        universal_termination_claim=False, producer_source_sha256=producer)
    if manifest is not None and json.dumps(manifest, sort_keys=True) != json.dumps(observed, sort_keys=True):
        raise ValueError('scalar division locals manifest differs from fresh proof')
    return observed, [instructions[site] for site in sorted(instructions)]
