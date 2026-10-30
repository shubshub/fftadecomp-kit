"""Exact load ranges and bounded immediate arithmetic for MOD inventory."""
import argparse
import json
from pathlib import Path

import zero_aware_remainder_ordinary_inventory as ordinary

SELECTOR = 'zero-aware-remainder-byte-range-inventory-v1'
SCHEMA = 'thumb-canonical-zero-aware-remainder-byte-range-inventory-v1'
MAX_UPDATES = 4096
bind_calls = ordinary.bind_calls


def prepare(data,address,calls,context):
    if type(context) is not tuple or len(context) != 6 or context[5] != SELECTOR:
        raise ValueError('byte-range remainder requires its explicit inventory context')
    runtime = ordinary.prepare(data,address,calls,context[:5]+(ordinary.SELECTOR,))
    context[4].update(schema=SCHEMA,selector=SELECTOR,
        dividend_policy='exact architectural LDRB/LDRSB/LDRSH and immediate ADD/SUB intervals contained in signed16',
        numeric_resource_policy='at most4096 changed proof states; exceeding this refuses, never bounds runtime iterations')
    return runtime


def load_range(instruction):
    """Authenticate the narrow Thumb encoding, registers and addressing form."""
    from capstone.arm_const import ARM_CC_AL,ARM_CC_INVALID,ARM_OP_REG,ARM_OP_MEM,ARM_REG_R0
    operands = instruction.operands
    if instruction.size != 2 or instruction.cc not in (ARM_CC_AL,ARM_CC_INVALID) or \
            len(operands) != 2 or operands[0].type != ARM_OP_REG or operands[1].type != ARM_OP_MEM:
        return None
    encoded = int.from_bytes(instruction.bytes,'little')
    memory = operands[1].mem
    if operands[0].reg != ARM_REG_R0+(encoded & 7) or \
            memory.base != ARM_REG_R0+((encoded >> 3) & 7):
        return None
    if encoded & 0xF800 == 0x7800:
        if instruction.mnemonic != 'ldrb' or memory.index or memory.disp != ((encoded >> 6) & 31):
            return None
        return 0,255
    kinds = {0x5C00:('ldrb',0,255),0x5600:('ldrsb',-128,127),0x5E00:('ldrsh',-32768,32767)}
    kind = kinds.get(encoded & 0xFE00)
    if kind is None or instruction.mnemonic != kind[0] or memory.disp or \
            memory.index != ARM_REG_R0+((encoded >> 6) & 7):
        return None
    return kind[1:]


def immediate_arithmetic(instruction):
    from capstone.arm_const import ARM_CC_AL,ARM_CC_INVALID,ARM_OP_REG,ARM_OP_IMM,ARM_REG_R0
    operands = instruction.operands
    if instruction.size != 2 or instruction.cc not in (ARM_CC_AL,ARM_CC_INVALID):
        return None
    encoded = int.from_bytes(instruction.bytes,'little')
    small,big = encoded & 0xFE00,encoded & 0xF800
    if small in (0x1C00,0x1E00):
        destination,source,amount = encoded & 7,(encoded >> 3) & 7,(encoded >> 6) & 7
        subtract = small == 0x1E00
        expected = [(ARM_OP_REG,ARM_REG_R0+destination),(ARM_OP_REG,ARM_REG_R0+source),(ARM_OP_IMM,amount)]
    elif big in (0x3000,0x3800):
        destination = source = (encoded >> 8) & 7
        amount,subtract = encoded & 255,big == 0x3800
        expected = [(ARM_OP_REG,ARM_REG_R0+destination),(ARM_OP_IMM,amount)]
    else:return None
    if instruction.mnemonic != ('subs' if subtract else 'adds') or len(operands) != len(expected) or any(
            operand.type != kind or (operand.reg if kind == ARM_OP_REG else operand.imm) != value
            for operand,(kind,value) in zip(operands,expected)):
        return None
    return ARM_REG_R0+destination,ARM_REG_R0+source,-amount if subtract else amount


def prove_operands(data,address,instructions,edges,sites,observed):
    """Join interval hulls only when every reaching path has a bounded load origin."""
    from capstone import CS_GRP_CALL
    from capstone.arm_const import (ARM_CC_AL,ARM_CC_INVALID,ARM_OP_REG,
        ARM_REG_R0,ARM_REG_R3,ARM_REG_R12,ARM_REG_LR)
    if address not in instructions or set(edges) != set(instructions) or not sites or set(sites)-set(instructions):
        raise ValueError('byte-range remainder requires its exact complete reached call CFG')
    clobbered = {*range(ARM_REG_R0,ARM_REG_R3+1),ARM_REG_R12,ARM_REG_LR}
    states,pending,updates = {address:{}},[address],0

    def arithmetic_fact(instruction,incoming):
        decoded = immediate_arithmetic(instruction)
        if decoded is None or decoded[1] not in incoming:return None
        destination,source,amount = decoded
        low,high,loads,arithmetic = incoming[source]
        low,high = low+amount,high+amount
        # Signed mathematical endpoints agree with the machine result only
        # without signed wrap. The narrower signed16 requirement also rejects
        # any intermediate range outside the supported dividend domain.
        if not -32768 <= low <= high <= 32767:return None
        return destination,(low,high,loads,arithmetic | {instruction.address})

    while pending:
        site = pending.pop();instruction = instructions[site]
        incoming,outgoing = states[site],dict(states[site])
        if CS_GRP_CALL in instruction.groups:
            for register in clobbered:outgoing.pop(register,None)
        else:
            _,written = instruction.regs_access()
            for register in written:outgoing.pop(register,None)
            operands = instruction.operands
            if instruction.size == 2 and instruction.cc in (ARM_CC_AL,ARM_CC_INVALID) and \
                    instruction.mnemonic in ('mov','movs') and len(operands) == 2 and \
                    all(op.type == ARM_OP_REG for op in operands) and operands[1].reg in incoming:
                outgoing[operands[0].reg] = incoming[operands[1].reg]
            loaded = load_range(instruction)
            if loaded is not None:
                outgoing[operands[0].reg] = (*loaded,frozenset((site,)),frozenset())
            result = arithmetic_fact(instruction,incoming)
            if result is not None:outgoing[result[0]] = result[1]
        for successor in edges[site]:
            if successor not in instructions:raise ValueError('byte-range CFG leaves exact instruction boundaries')
            previous = states.get(successor)
            merged = outgoing if previous is None else {
                register:(min(value[0],outgoing[register][0]),max(value[1],outgoing[register][1]),
                    value[2] | outgoing[register][2],value[3] | outgoing[register][3])
                for register,value in previous.items() if register in outgoing}
            if previous != merged:
                updates += 1
                if updates > MAX_UPDATES:raise ValueError('byte-range proof state budget exceeded')
                states[successor] = merged;pending.append(successor)
    if set(states) != set(instructions):raise ValueError('byte-range facts do not cover the complete owner')
    loads,arithmetic = [],[]
    for site,instruction in sorted(instructions.items()):
        loaded = load_range(instruction)
        if loaded is not None:
            loads.append([site-address,instruction.mnemonic,instruction.reg_name(instruction.operands[0].reg),
                *loaded,ordinary.pure.sha(instruction.bytes)])
        result = arithmetic_fact(instruction,states[site])
        if result is not None:
            destination,value = result
            arithmetic.append([site-address,instruction.mnemonic,instruction.reg_name(destination),
                immediate_arithmetic(instruction)[2],value[0],value[1],ordinary.pure.sha(instruction.bytes)])
    operands = []
    for site in sorted(sites):
        value = states[site].get(ARM_REG_R0)
        if value is None or not value[2]:
            raise ValueError(f'byte-range remainder requires signed16 r0 on every call path at {site:08X}')
        low,high,origins,operations = value
        operands.append([site-address,low,high,sorted(origin-address for origin in origins),
            sorted(operation-address for operation in operations),'zero-or-nonzero r1'])
    observed.update(load_transfers=loads,immediate_arithmetic_transfers=arithmetic,operand_ranges=operands)


def finish(data,address,calls,context,verified):ordinary.finish(data,address,calls,context,verified)


def verify(data,address,rom,mapping,index,calls,bindings,*,selector,manifest=None):
    import match
    if selector != SELECTOR:raise ValueError('byte-range remainder requires its explicit inventory-only selector')
    observed = {}
    verified = match.verify_leaf_instructions(data,address,True,calls,
        remainder_byte_range_inventory_context=(rom,mapping,index,bindings,observed,selector))
    if manifest is not None and ordinary.pure.text(manifest) != ordinary.pure.text(observed):
        raise ValueError('byte-range remainder inventory manifest differs from fresh native proof')
    return observed,verified


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile',required=True,choices=(SELECTOR,))
    parser.add_argument('--rom',required=True,type=Path);parser.add_argument('--mapping',required=True,type=Path)
    parser.add_argument('--index',required=True,type=Path);parser.add_argument('address',type=lambda value:int(value,16))
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


if __name__ == '__main__':main()
