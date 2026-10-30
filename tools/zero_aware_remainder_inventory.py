"""Inventory-only canonical MOD closure, including its actual zero return."""
import argparse
import hashlib
import json
from pathlib import Path
import struct

import modsi3_profile as remainder

SELECTOR = 'zero-aware-remainder-inventory-v1'
SCHEMA = 'thumb-canonical-zero-aware-remainder-inventory-v1'


def text(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def sha(data):
    return hashlib.sha256(data).hexdigest()


def prepare(data, address, calls, context):
    import owner_admission_profile as owner
    import software_double_profile as canonical
    if type(context) is not tuple or len(context) != 6 or context[5] != SELECTOR or \
            type(context[3]) is not dict or not context[3] or \
            type(context[4]) is not dict or context[4]:
        raise ValueError('zero-aware remainder requires a fresh explicit inventory context')
    rom, mapping, index, bindings, observed, _ = context
    owner.validate_span(data, address, rom, mapping, index)
    if set(bindings) != set(calls) or set(bindings.values()) != {'__modsi3'} or \
            any(target != remainder.ADDRESS for target in calls.values()):
        raise ValueError('zero-aware remainder inventory requires every call to be canonical MOD')
    remainder.verify_context(data, address, calls, (rom, mapping, bindings))
    # This existing complete native interpreter includes both real MOD returns,
    # its zero-hook dependency, every saved register and all reachable effects.
    closure = canonical.prove_remainder_closure(rom, mapping, index)
    if set(closure) != {remainder.ADDRESS, 0x0814274C} or any(
            proof['writes'] or proof['stack_reads'] for proof in closure.values()) or \
            set(closure[remainder.ADDRESS]['returns']) != {0x08142A12, 0x08142A1C}:
        raise ValueError('zero-aware remainder requires both complete native runtime cases')
    # Exact entry CMP/BEQ selects this zero path before the nonzero body saves
    # any registers. PUSH/BL/hook-return/MOVS/POP returns r0=0 and entry LR.
    expected = ((0x08142950, '0123'), (0x08142952, '0029'), (0x08142954, '5ed0'),
                (0x08142A14, '00b5'), (0x08142A16, 'fff799fe'),
                (0x0814274C, 'f746'), (0x08142A1A, '0020'), (0x08142A1C, '00bd'))
    for site, encoded in expected:
        raw = bytes.fromhex(encoded)
        if rom[site-0x08000000:site-0x08000000+len(raw)] != raw:
            raise ValueError('zero-aware remainder exact entry-to-zero trace differs')
    observed.update(schema=SCHEMA, selector=SELECTOR, inventory_only=True,
        source_or_ELF_admission=False, dependencies=[list(row) for row in remainder.IDENTITIES],
        native_runtime_closure=[[site, proof] for site, proof in sorted(closure.items())],
        runtime_cases={'nonzero': {'component': remainder.SCHEMA,
                                  'operands': ['signed16 r0', 'nonzero r1']},
                       'zero': {'guard': 'entry r1 == 0', 'return_r0': 0,
                                'maximum_frame_bytes': 4, 'preserved': 'r4-r11,sp,entry-lr',
                                'trace': [[site, sha(bytes.fromhex(encoded))]
                                          for site, encoded in expected]}},
        divisor_partition=['r1 == 0', 'r1 != 0'])


def prove_operands(data, address, instructions, edges, sites, observed):
    """Track exact mask constants and nonnegative signed16 facts on every path."""
    from capstone import CS_GRP_CALL
    from capstone.arm_const import (ARM_CC_AL, ARM_CC_INVALID, ARM_OP_REG, ARM_OP_IMM,
        ARM_REG_R0, ARM_REG_R3, ARM_REG_R12, ARM_REG_LR)
    clobbered = {*range(ARM_REG_R0, ARM_REG_R3+1), ARM_REG_R12, ARM_REG_LR}
    states, pending = {address: ({}, frozenset())}, [address]

    def mask(instruction, incoming):
        operands = instruction.operands
        if instruction.size != 2 or int.from_bytes(instruction.bytes, 'little') & 0xFFC0 != 0x4000 or \
                instruction.cc not in (ARM_CC_AL, ARM_CC_INVALID) or len(operands) != 2 or \
                any(op.type != ARM_OP_REG for op in operands):
            return None
        candidates = [(op.reg, incoming[op.reg]) for op in operands if op.reg in incoming and
                      0 <= incoming[op.reg][0] <= 0x7FFF]
        return min(candidates) if candidates else None

    while pending:
        site = pending.pop()
        instruction = instructions[site]
        incoming, bounded = states[site]
        constants, bounds = dict(incoming), set(bounded)
        if CS_GRP_CALL in instruction.groups:
            for reg in clobbered:
                constants.pop(reg, None); bounds.discard(reg)
        else:
            _, written = instruction.regs_access()
            for reg in written:
                constants.pop(reg, None); bounds.discard(reg)
            operands = instruction.operands
            if instruction.cc in (ARM_CC_AL, ARM_CC_INVALID) and instruction.size == 2 and \
                    operands and operands[0].type == ARM_OP_REG:
                destination, source, value = operands[0].reg, None, None
                if instruction.mnemonic in ('mov', 'movs') and len(operands) == 2:
                    if operands[1].type == ARM_OP_REG:
                        source = operands[1].reg
                    elif operands[1].type == ARM_OP_IMM:
                        value = (operands[1].imm & 0xFFFFFFFF, ('immediate', site-address))
                elif instruction.mnemonic in ('add', 'adds') and len(operands) == 3 and \
                        operands[1].type == ARM_OP_REG and operands[2].type == ARM_OP_IMM and \
                        operands[2].imm == 0:
                    source = operands[1].reg
                elif int.from_bytes(instruction.bytes, 'little') & 0xF800 == 0x4800:
                    word = ((site+4) & ~3) + ((int.from_bytes(instruction.bytes, 'little') & 0xFF) << 2)
                    if word % 4 or not address <= word <= address+len(data)-4:
                        raise ValueError('mask constant literal leaves the complete aligned owner')
                    raw = data[word-address:word-address+4]
                    value = (struct.unpack('<I', raw)[0], ('literal', word-address, sha(raw)))
                if source is not None:
                    value = incoming.get(source)
                    if source in bounded:
                        bounds.add(destination)
                if value is not None:
                    constants[destination] = value
                    if value[0] <= 0x7FFF:
                        bounds.add(destination)
                if mask(instruction, incoming) is not None:
                    bounds.add(destination)
        outgoing = (constants, frozenset(bounds))
        for successor in edges[site]:
            previous = states.get(successor)
            merged = outgoing if previous is None else (
                {reg: value for reg, value in previous[0].items() if constants.get(reg) == value},
                previous[1] & outgoing[1])
            if merged != previous:
                states[successor] = merged
                pending.append(successor)
    for site in sorted(sites):
        if ARM_REG_R0 not in states.get(site, ({}, ()))[1]:
            raise ValueError('zero-aware remainder requires signed16 r0 on every call path')
    masks = []
    for site, instruction in sorted(instructions.items()):
        selected = mask(instruction, states[site][0])
        if selected is not None:
            reg, (value, origin) = selected
            masks.append([site-address, instruction.reg_name(instruction.operands[0].reg),
                          instruction.reg_name(reg), value, origin])
    if not masks:
        raise ValueError('zero-aware remainder inventory requires an actual bounded AND mask')
    observed['mask_transfers'] = masks
    observed['operands'] = [[site-address, 'signed16 r0', 'zero-or-nonzero r1'] for site in sorted(sites)]


def finish(data, address, calls, context, verified):
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    import local_long_branch_profile as frame
    from capstone.arm_const import ARM_REG_R4, ARM_REG_R11
    refinement = owner.refine(data, address, context[1])
    instructions, edges, branches, actual_calls, words = graph.graph(data, address, refinement)
    if calls != actual_calls or branches or words or {i.address for i in verified} != set(instructions):
        raise ValueError('zero-aware remainder requires its exact closed direct-call inventory')
    partition = graph.partition(data, address, refinement, instructions, words)
    preserved = frozenset(range(ARM_REG_R4, ARM_REG_R11+1))
    restored = frame.prove_frame(instructions, edges, address, {}, calls, stack_aliases=True,
        call_preservation={site: preserved for site in calls})
    context[4].update(frame=restored, partition=partition,
        calls=[[site-address, '__modsi3'] for site in sorted(calls)],
        body_sha256=sha(data), mapping_sha256=sha(context[1]), index_sha256=sha(context[2]),
        ROM_sha256=sha(context[0]), complete_native_proof=True,
        external_call_policy='complete exact canonical runtime closure; no ordinary ABI premise')


def verify(data, address, rom, mapping, index, calls, bindings, *, selector, manifest=None):
    import match
    if selector != SELECTOR:
        raise ValueError('zero-aware remainder requires its explicit inventory-only selector')
    observed = {}
    verified = match.verify_leaf_instructions(data, address, True, calls,
        remainder_inventory_context=(rom, mapping, index, bindings, observed, selector))
    if manifest is not None and text(manifest) != text(observed):
        raise ValueError('zero-aware remainder inventory manifest differs from fresh native proof')
    return observed, verified


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile', required=True, choices=(SELECTOR,))
    parser.add_argument('--rom', required=True, type=Path)
    parser.add_argument('--mapping', required=True, type=Path)
    parser.add_argument('--index', required=True, type=Path)
    parser.add_argument('address', type=lambda value: int(value, 16))
    args = parser.parse_args()
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    rom, mapping, index = args.rom.read_bytes(), args.mapping.read_bytes(), args.index.read_bytes()
    rows = [row for row in json.loads(mapping) if int(row['rom'], 16) == args.address]
    if len(rows) != 1:
        raise ValueError('inventory requires one exact mapped owner')
    data = rom[args.address-0x08000000:int(rows[0]['end'], 16)-0x08000000]
    refinement = owner.refine(data, args.address, mapping)
    _, _, _, calls, _ = graph.graph(data, args.address, refinement)
    bindings = {site: '__modsi3' for site in calls}
    manifest, _ = verify(data, args.address, rom, mapping, index, calls, bindings, selector=args.profile)
    print(text(manifest))


if __name__ == '__main__':
    main()
