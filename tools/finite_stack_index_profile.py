"""Exact two-value Thumb indices for read-only allocated local words."""
from capstone import CS_GRP_CALL
from capstone.arm_const import (ARM_CC_AL, ARM_CC_INVALID, ARM_OP_REG,
    ARM_OP_IMM, ARM_REG_R0, ARM_REG_R4, ARM_REG_R11, ARM_REG_SP)

SELECTOR = 'finite-local-word-index-v1'
SCHEMA = 'thumb-finite-local-word-index-v1'
MAX_VALUES, MAX_UPDATES = 2, 4096
DOMAIN = frozenset((0, 1, 4))


def validate(policy):
    if type(policy) is not str or policy != SELECTOR:
        raise ValueError('finite local indices require their explicit versioned policy')


def prove_constants(instructions, edges, address):
    """Keep every known MOVS0/1 / LSL2 alternative; missing arms stay unknown."""
    if address not in instructions or set(edges) != set(instructions):
        raise ValueError('finite indices require the complete exact CFG')
    states, pending, updates = {address: {}}, [address], 0
    while pending:
        site = pending.pop(); instruction = instructions[site]
        incoming = states[site]; outgoing = dict(incoming)
        if CS_GRP_CALL in instruction.groups:
            outgoing = {r:v for r,v in outgoing.items() if ARM_REG_R4 <= r <= ARM_REG_R11}
        else:
            _, written = instruction.regs_access()
            for register in written: outgoing.pop(register, None)
            operands = instruction.operands
            raw = int.from_bytes(instruction.bytes, 'little')
            unconditional = instruction.size == 2 and instruction.cc in (ARM_CC_AL, ARM_CC_INVALID)
            if unconditional and raw & 0xF800 == 0x2000 and raw & 255 in (0, 1) and \
                    instruction.mnemonic == 'movs' and len(operands) == 2 and \
                    operands[0].type == ARM_OP_REG and operands[0].reg == ARM_REG_R0+((raw>>8)&7) and \
                    operands[1].type == ARM_OP_IMM and operands[1].imm == raw & 255:
                outgoing[operands[0].reg] = {raw & 255:frozenset((site,))}
            elif unconditional and raw & 0xF800 == 0 and (raw>>6)&31 == 2 and \
                    instruction.mnemonic == 'lsls' and len(operands) == 3 and \
                    operands[0].type == operands[1].type == ARM_OP_REG and \
                    operands[0].reg == ARM_REG_R0+(raw&7) and \
                    operands[1].reg == ARM_REG_R0+((raw>>3)&7) and \
                    operands[2].type == ARM_OP_IMM and operands[2].imm == 2 and \
                    operands[1].reg in incoming and set(incoming[operands[1].reg]) <= {0,1}:
                outgoing[operands[0].reg] = {value<<2:origins|{site}
                    for value,origins in incoming[operands[1].reg].items()}
        for successor in edges[site]:
            if successor not in instructions: raise ValueError('finite index CFG leaves exact instruction boundaries')
            previous = states.get(successor)
            merged = outgoing if previous is None else {
                register:{value:previous[register].get(value,frozenset())|outgoing[register].get(value,frozenset())
                    for value in previous[register].keys()|outgoing[register].keys()}
                for register in previous.keys()&outgoing.keys()}
            if any(not values or len(values)>MAX_VALUES or not set(values)<=DOMAIN for values in merged.values()):
                raise ValueError('finite index alternatives exceed the explicit exact domain')
            if merged != previous:
                updates += 1
                if updates>MAX_UPDATES: raise ValueError('finite index proof-state budget exceeded')
                states[successor]=merged; pending.append(successor)
    if set(states)!=set(instructions): raise ValueError('finite index facts do not cover every reached instruction')
    return states


def offsets(values):
    if not values or len(values)>MAX_VALUES or any(type(offset) is not int or live is not True for offset,live in values):
        raise ValueError('finite local alias has unknown, expired or excessive alternatives')
    return tuple(sorted(offset for offset,_ in values))


def assignment(instruction, aliases, depth, constants):
    from match import stack_alias_assignment
    operands=instruction.operands
    if instruction.size==2 and instruction.mnemonic=='add' and \
            instruction.cc in (ARM_CC_AL,ARM_CC_INVALID) and len(operands)==3 and \
            all(op.type==ARM_OP_REG and not op.shift.type and not op.shift.value and not op.subtracted for op in operands):
        destination=operands[0].reg
        if ARM_REG_R0<=destination<=ARM_REG_R0+7 and \
                instruction.bytes==bytes((0x68+destination-ARM_REG_R0,0x44)) and \
                operands[1].reg==ARM_REG_SP and operands[2].reg==destination and destination in constants:
            values=frozenset((value-4*depth,True) for value in constants[destination])
            return destination,values,ARM_REG_SP
    read,_=instruction.regs_access()
    sources=set(read)&aliases.keys()
    if len(sources)>1: return None
    exact={register:offsets(values)[0] for register,values in aliases.items() if register in sources}
    first=stack_alias_assignment(instruction,exact,depth,{})
    if first is None:return None
    source=first[2]
    if source==ARM_REG_SP:values=frozenset(((first[1],True),))
    else:
        values=frozenset((stack_alias_assignment(instruction,{source:offset},depth,{})[1],True)
            for offset in offsets(aliases[source]))
    return first[0],values,source
