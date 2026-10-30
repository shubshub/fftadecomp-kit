"""Inventory-only exact UDIV/MOD closures with SHIFT-proven MOD dividends."""
import argparse
import json
from pathlib import Path

import zero_aware_remainder_inventory as remainder
import zero_aware_remainder_ordinary_inventory as ordinary
import zero_aware_remainder_shift_inventory as shift

SELECTOR = 'zero-aware-unsigned-quotient-shift-inventory-v1'
SCHEMA = 'thumb-canonical-zero-aware-unsigned-quotient-shift-inventory-v1'
UDIV = 0x08142AB0
OPERATIONS = {'__udivsi3': UDIV, '__modsi3': remainder.remainder.ADDRESS}
prove_operands = shift.prove_operands


def bind_calls(calls, mapping, address, size, rom_size):
    if type(calls) is not dict or not set(OPERATIONS.values()) <= set(calls.values()) or any(
            type(site) is not int or type(target) is not int or site % 2 or
            not address <= site <= address + size - 4 for site, target in calls.items()):
        raise ValueError('unsigned quotient inventory requires actual canonical UDIV and MOD calls')
    other = {site: target for site, target in calls.items() if target != UDIV}
    if any(target != remainder.remainder.ADDRESS for target in other.values()):
        bindings = ordinary.bind_calls(other, mapping, address, size, rom_size)
    else:
        bindings = {site: '__modsi3' for site in other}
    bindings.update((site, '__udivsi3') for site, target in calls.items() if target == UDIV)
    return dict(sorted(bindings.items()))


def prove_quotient_closure(rom, mapping, index):
    """Reuse the unchanged native interpreter, including the real zero hook."""
    import match
    from software_double_profile import indices, span_record
    from software_float_profile import prove_runtime
    match.verify_udivsi3_identity(rom, mapping)
    entries, rows = indices(mapping, index)
    zero = 0x0814274C
    for start, end, count in ((zero, 0x0814274E, 1), (UDIV, 0x08142B28, 59)):
        if span_record(start, end, entries, rows, rom)['instrs'] != count:
            raise ValueError('unsigned quotient runtime exact instruction count differs')
    proofs = {zero: prove_runtime(rom, entries, zero, 0x0814274E, 1, {},
        call_edges=(), scalar_entries=(zero,), allowed_writes=(), thumb_pc_returns=(zero,))}
    proofs[UDIV] = prove_runtime(rom, entries, UDIV, 0x08142B28, 59, proofs,
        call_edges=((0x08142B20, zero),), scalar_entries=(UDIV,), allowed_writes=(),
        thumb_pc_returns=(0x08142B1C, 0x08142B26))
    return proofs


def prepare(data, address, calls, context):
    import match
    if type(context) is not tuple or len(context) != 6 or context[5] != SELECTOR or \
            type(context[3]) is not dict or type(context[4]) is not dict or context[4]:
        raise ValueError('unsigned quotient inventory requires a fresh explicit context')
    rom, mapping, index, bindings, observed, _ = context
    if bindings != bind_calls(calls, mapping, address, len(data), len(rom)):
        raise ValueError('unsigned quotient bindings differ from every validated actual call')
    mod = {site: name for site, name in bindings.items() if name == '__modsi3'}
    remainder.prepare(data, address, {site: calls[site] for site in mod},
        (rom, mapping, index, mod, observed, remainder.SELECTOR))
    closure = prove_quotient_closure(rom, mapping, index)
    zero = 0x0814274C
    if set(closure) != {UDIV, zero} or any(
            proof['writes'] or proof['stack_reads'] for proof in closure.values()) or \
            closure[UDIV]['returns'] != [0x08142B1C, 0x08142B26]:
        raise ValueError('unsigned quotient requires both complete native runtime cases')
    existing = dict(observed['native_runtime_closure'])
    if existing[zero] != closure[zero]:
        raise ValueError('unsigned quotient and remainder zero-hook proofs differ')
    expected = ((UDIV, '0029'), (0x08142AB2, '34d0'), (0x08142B1E, '00b5'),
        (0x08142B20, 'fff714fe'), (zero, 'f746'), (0x08142B24, '0020'), (0x08142B26, '00bd'))
    for site, encoded in expected:
        raw = bytes.fromhex(encoded)
        if rom[site - match.ROM_BASE:site - match.ROM_BASE + len(raw)] != raw:
            raise ValueError('unsigned quotient exact entry-to-zero trace differs')
    mod_cases = observed['runtime_cases']
    existing.update(closure)
    ordinary_sites = [[site - address, name] for site, name in bindings.items()
                      if name not in OPERATIONS]
    observed.update(schema=SCHEMA, selector=SELECTOR,
        dependencies={'quotient': [list(row) for row in match.UDIVSI3_IDENTITIES],
            'remainder': [list(row) for row in remainder.remainder.IDENTITIES]},
        native_runtime_closure=[[site, proof] for site, proof in sorted(existing.items())],
        runtime_cases={'remainder': mod_cases, 'quotient': {
            'nonzero': {'component': 'exact canonical native UDIV closure',
                'operands': 'unrestricted target entry-register state'},
            'zero': {'guard': 'entry r1 == 0', 'return_r0': 0,
                'preserved': 'r4-r11,sp,entry-lr',
                'trace': [[site, remainder.sha(bytes.fromhex(encoded))] for site, encoded in expected]}}},
        dividend_policy='exact existing SHIFT signed16 r0 proof at every MOD site only',
        unsigned_quotient_operand_policy='entry-register state, no nonzero divisor premise',
        call_clobbers=['r0', 'r1', 'r2', 'r3', 'r12', 'lr', 'flags'],
        caller_facts='every call kills caller-saved facts; no quotient, remainder or flags result facts',
        ordinary_calls=ordinary_sites,
        ordinary_call_ABI=ordinary.ABI if ordinary_sites else None,
        ordinary_call_premise=('conditional: each ordinary callee returns and obeys the existing direct-call ABI'
            if ordinary_sites else None),
        external_call_policy='complete native canonical UDIV/MOD closures; conditional returning-call ABI at ordinary sites only')
    return mod


def finish(data, address, calls, context, verified):
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    import local_long_branch_profile as frame
    from capstone.arm_const import ARM_REG_R4, ARM_REG_R11
    refinement = owner.refine(data, address, context[1])
    instructions, edges, branches, actual_calls, words = graph.graph(data, address, refinement)
    if calls != actual_calls or branches or words or {i.address for i in verified} != set(instructions) or \
            context[3] != bind_calls(calls, context[1], address, len(data), len(context[0])):
        raise ValueError('unsigned quotient inventory requires its exact closed complete call CFG')
    # The existing structural ABI remains conditional at ordinary sites. When
    # no such site exists, every preserved-register premise has a native proof.
    preservation = {} if context[4]['ordinary_calls'] else {
        site: frozenset(range(ARM_REG_R4, ARM_REG_R11 + 1)) for site in calls}
    restored = frame.prove_frame(instructions, edges, address, {}, calls, stack_aliases=True,
        **({'call_preservation': preservation} if preservation else {}))
    context[4].update(frame=restored,
        partition=graph.partition(data, address, refinement, instructions, words),
        calls=[[site - address, name] for site, name in sorted(context[3].items())],
        runtime_calls=[[site - address, name] for site, name in sorted(context[3].items())
                       if name in OPERATIONS],
        body_sha256=remainder.sha(data), mapping_sha256=remainder.sha(context[1]),
        index_sha256=remainder.sha(context[2]), ROM_sha256=remainder.sha(context[0]),
        complete_native_proof=True)


def verify(data, address, rom, mapping, index, calls, bindings, *, selector, manifest=None):
    import match
    if selector != SELECTOR:
        raise ValueError('unsigned quotient requires its explicit inventory-only selector')
    observed = {}
    verified = match.verify_leaf_instructions(data, address, True, calls,
        zero_aware_unsigned_quotient_inventory_context=(rom, mapping, index, bindings, observed, selector))
    if manifest is not None and remainder.text(manifest) != remainder.text(observed):
        raise ValueError('unsigned quotient inventory manifest differs from fresh native proof')
    return observed, verified


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile', required=True, choices=(SELECTOR,))
    for name in ('rom', 'mapping', 'index'):
        parser.add_argument('--' + name, required=True, type=Path)
    parser.add_argument('address', type=lambda value: int(value, 16))
    args = parser.parse_args()
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    rom, mapping, index = args.rom.read_bytes(), args.mapping.read_bytes(), args.index.read_bytes()
    rows = [row for row in json.loads(mapping) if int(row['rom'], 16) == args.address]
    if len(rows) != 1:
        raise ValueError('inventory requires one exact mapped owner')
    data = rom[args.address - 0x08000000:int(rows[0]['end'], 16) - 0x08000000]
    refinement = owner.refine(data, args.address, mapping)
    _, _, _, calls, _ = graph.graph(data, args.address, refinement)
    bindings = bind_calls(calls, mapping, args.address, len(data), len(rom))
    manifest, _ = verify(data, args.address, rom, mapping, index, calls, bindings, selector=args.profile)
    print(remainder.text(manifest))


if __name__ == '__main__':
    main()
