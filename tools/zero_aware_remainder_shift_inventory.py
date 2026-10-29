"""Exact immediate-shift signed16 bounds for mixed-call remainder inventory."""
import argparse
from pathlib import Path
import json

import zero_aware_remainder_ordinary_inventory as ordinary

SELECTOR = 'zero-aware-remainder-shift-inventory-v1'
SCHEMA = 'thumb-canonical-zero-aware-remainder-shift-inventory-v1'
bind_calls = ordinary.bind_calls


def prepare(data, address, calls, context):
    if type(context) is not tuple or len(context) != 6 or context[5] != SELECTOR:
        raise ValueError('shift remainder requires its explicit inventory context')
    runtime = ordinary.prepare(data,address,calls,context[:5]+(ordinary.SELECTOR,))
    context[4].update(schema=SCHEMA,selector=SELECTOR,
        dividend_policy='exact immediate ASR16..32 signed range or LSR17..32 unsigned range; no input assumptions')
    return runtime


def shift_bound(instruction):
    """Decode only unconditional two-byte Thumb immediate shifts, including #32."""
    from capstone.arm_const import ARM_CC_AL, ARM_CC_INVALID, ARM_OP_REG, ARM_OP_IMM, ARM_REG_R0
    operands = instruction.operands
    if instruction.size != 2 or instruction.cc not in (ARM_CC_AL,ARM_CC_INVALID) or \
            len(operands) != 3 or operands[0].type != ARM_OP_REG or \
            operands[1].type != ARM_OP_REG or operands[2].type != ARM_OP_IMM:
        return None
    encoded = int.from_bytes(instruction.bytes,'little')
    amount = (encoded >> 6) & 31 or 32
    operation = encoded & 0xF800
    if operands[0].reg != ARM_REG_R0+(encoded & 7) or \
            operands[1].reg != ARM_REG_R0+((encoded >> 3) & 7) or operands[2].imm != amount:
        return None
    if operation == 0x1000 and instruction.mnemonic == 'asrs' and 16 <= amount <= 32:
        magnitude = 1 << max(31-amount,0)
        return amount, -magnitude, magnitude-1
    if operation == 0x0800 and instruction.mnemonic == 'lsrs' and 17 <= amount <= 32:
        return amount, 0, (1 << (32-amount))-1
    return None


def prove_operands(data, address, instructions, edges, sites, observed):
    """Every reaching alternative retains a shift origin, or the fact is absent."""
    from capstone import CS_GRP_CALL
    from capstone.arm_const import (ARM_CC_AL,ARM_CC_INVALID,ARM_OP_REG,ARM_OP_IMM,
        ARM_REG_R0,ARM_REG_R3,ARM_REG_R12,ARM_REG_LR)
    if address not in instructions or set(edges) != set(instructions) or not sites or \
            set(sites)-set(instructions):
        raise ValueError('shift remainder requires its exact complete reached call CFG')
    clobbered = {*range(ARM_REG_R0,ARM_REG_R3+1),ARM_REG_R12,ARM_REG_LR}
    states,pending = {address:{}},[address]
    while pending:
        site = pending.pop()
        instruction = instructions[site]
        incoming = states[site]
        outgoing = dict(incoming)
        if CS_GRP_CALL in instruction.groups:
            for register in clobbered:outgoing.pop(register,None)
        else:
            _,written = instruction.regs_access()
            for register in written:outgoing.pop(register,None)
            operands = instruction.operands
            if instruction.cc in (ARM_CC_AL,ARM_CC_INVALID) and instruction.size == 2 and \
                    operands and operands[0].type == ARM_OP_REG:
                source = None
                if instruction.mnemonic in ('mov','movs') and len(operands) == 2 and operands[1].type == ARM_OP_REG:
                    source = operands[1].reg
                elif instruction.mnemonic in ('add','adds') and len(operands) == 3 and \
                        operands[1].type == ARM_OP_REG and operands[2].type == ARM_OP_IMM and operands[2].imm == 0:
                    source = operands[1].reg
                if source in incoming:
                    outgoing[operands[0].reg] = incoming[source]
                if shift_bound(instruction) is not None:
                    outgoing[operands[0].reg] = frozenset((site,))
        for successor in edges[site]:
            if successor not in instructions:
                raise ValueError('shift remainder CFG leaves exact reached instruction boundaries')
            previous = states.get(successor)
            merged = outgoing if previous is None else {
                register:origins | outgoing[register] for register,origins in previous.items()
                if register in outgoing}
            if previous != merged:
                states[successor] = merged
                pending.append(successor)
    if set(states) != set(instructions):
        raise ValueError('shift remainder facts do not cover the complete reached owner')
    transfers = []
    for site,instruction in sorted(instructions.items()):
        bound = shift_bound(instruction)
        if bound is not None:
            amount,minimum,maximum = bound
            transfers.append([site-address,instruction.mnemonic,
                instruction.reg_name(instruction.operands[0].reg),
                instruction.reg_name(instruction.operands[1].reg),amount,minimum,maximum,
                ordinary.pure.sha(instruction.bytes)])
    if not transfers:
        raise ValueError('shift remainder requires an actual exact bounded immediate shift')
    origins = []
    for site in sorted(sites):
        if ARM_REG_R0 not in states[site]:
            raise ValueError(f'shift remainder requires signed16 r0 on every call path at {site:08X}')
        origins.append([site-address,sorted(origin-address for origin in states[site][ARM_REG_R0])])
    observed.update(shift_transfers=transfers,operand_shift_origins=origins,
        operands=[[site-address,'signed16 r0','zero-or-nonzero r1'] for site in sorted(sites)])


def finish(data, address, calls, context, verified):
    ordinary.finish(data,address,calls,context,verified)


def verify(data, address, rom, mapping, index, calls, bindings, *, selector, manifest=None):
    import match
    if selector != SELECTOR:
        raise ValueError('shift remainder requires its explicit inventory-only selector')
    observed = {}
    verified = match.verify_leaf_instructions(data,address,True,calls,
        remainder_shift_inventory_context=(rom,mapping,index,bindings,observed,selector))
    if manifest is not None and ordinary.pure.text(manifest) != ordinary.pure.text(observed):
        raise ValueError('shift remainder inventory manifest differs from fresh native proof')
    return observed,verified


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile',required=True,choices=(SELECTOR,))
    parser.add_argument('--rom',required=True,type=Path)
    parser.add_argument('--mapping',required=True,type=Path)
    parser.add_argument('--index',required=True,type=Path)
    parser.add_argument('address',type=lambda value:int(value,16))
    args = parser.parse_args()
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    rom,mapping,index = args.rom.read_bytes(),args.mapping.read_bytes(),args.index.read_bytes()
    rows = [row for row in json.loads(mapping) if int(row['rom'],16) == args.address]
    if len(rows) != 1:raise ValueError('inventory requires one exact mapped owner')
    data = rom[args.address-0x08000000:int(rows[0]['end'],16)-0x08000000]
    refinement = owner.refine(data,args.address,mapping)
    _,_,_,calls,_ = graph.graph(data,args.address,refinement)
    bindings = bind_calls(calls,mapping,args.address,len(data),len(rom))
    manifest,_ = verify(data,args.address,rom,mapping,index,calls,bindings,selector=args.profile)
    print(ordinary.pure.text(manifest))


if __name__ == '__main__':
    main()
