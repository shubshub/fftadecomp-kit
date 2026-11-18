"""Finite constant-control local word arrays under explicit returning-call ABI.

Only known CMP predicates select branches. Unknown predicates, repeated states,
uninitialized locals, protected-word writes, and local call arguments refuse.
External reads/calls retain explicit physical-access and frame-noninterference
premises. This does not establish callback installation or allocator effects.
"""
import hashlib
import json
from pathlib import Path
import struct

import match
import owner_graph_profile as graph
import owner_runtime_profile as operations
import function_thunk_profile as thunk
from capstone.arm import ARM_OP_IMM, ARM_OP_REG, ARM_REG_SP, ARM_REG_PC, ARM_REG_LR

SELECTOR = 'conditional-finite-local-word-loops-v1'
SCHEMA = 'elf-symbol-thumb-conditional-finite-local-word-loops-v1'
CONTROL_FLOW = 'finite constant-controlled local word loops with exact protected frames and conditional returning calls'
MAX_STEPS = 4096
MAX_FRAME = 4096
R0 = match.ARM_REG_R0
PRESERVED = tuple(range(R0 + 4, R0 + 12))
CLOBBERED = (R0, R0+1, R0+2, R0+3, match.ARM_REG_R12, ARM_REG_LR)
CONDITIONS = {
    'beq': lambda n,z,c,v: z, 'bne': lambda n,z,c,v: not z,
    'bhs': lambda n,z,c,v: c, 'blo': lambda n,z,c,v: not c,
    'bhi': lambda n,z,c,v: c and not z, 'bls': lambda n,z,c,v: not c or z,
    'bge': lambda n,z,c,v: n == v, 'blt': lambda n,z,c,v: n != v,
    'bgt': lambda n,z,c,v: not z and n == v, 'ble': lambda n,z,c,v: z or n != v,
}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def constant(value):
    return ('constant', value & 0xffffffff)


def compare(left, right):
    result = (left-right) & 0xffffffff
    return (bool(result & 0x80000000), result == 0, left >= right,
            bool((left ^ right) & (left ^ result) & 0x80000000))


def local(value):
    return value is not None and value[0] == 'local'


def execute(data, address, instructions, edges, calls, *, step_limit=MAX_STEPS):
    require(type(step_limit) is int and 0 < step_limit <= MAX_STEPS,
            'finite loops require the fixed bounded step limit')
    registers = {r: ('entry', r) for r in (*PRESERVED, ARM_REG_LR)}
    registers[ARM_REG_SP] = ('local', 0)
    cells, protected = {}, set()
    trace, accesses, call_records, branches = [], [], [], []
    seen, reached = set(), set()
    flags = None
    site, minimum = address, 0

    def value(operand):
        if operand.type == ARM_OP_IMM:
            return constant(operand.imm)
        require(operand.type == ARM_OP_REG, 'finite loop operand is not a register or immediate')
        return registers.get(operand.reg)

    def offset(base, delta):
        if base is None:
            return None
        if base[0] == 'constant':
            return constant(base[1]+delta)
        require(base[0] == 'local', 'finite loops exclude arithmetic on opaque entry words')
        return ('local', base[1]+delta)

    def access(pointer, loading, payload=None):
        require(local(pointer), 'finite local access lacks exact stack origin')
        at, sp = pointer[1], registers[ARM_REG_SP][1]
        require(at % 4 == 0 and sp <= at and at+4 <= 0,
                'finite local word access is outside the live aligned frame')
        require(at not in protected, 'ordinary local access overlaps a protected save')
        if loading:
            require(at in cells, 'finite local load reads an uninitialized word')
            result = cells[at]
        else:
            require(not local(payload), 'finite loops exclude stored private pointers')
            cells[at] = payload
            result = None
        accesses.append([site, 'read' if loading else 'write', at, 4])
        return result

    for _ in range(step_limit):
        require(site in instructions, 'finite loop execution left the complete CFG')
        key = (site, tuple(sorted(registers.items())), tuple(sorted(cells.items())),
               tuple(sorted(protected)), flags)
        require(key not in seen, 'finite loop repeats a machine abstraction state')
        seen.add(key); reached.add(site); trace.append(site)
        instruction = instructions[site]
        op, operands = instruction.mnemonic, instruction.operands
        regs = [x.reg for x in operands if x.type == ARM_OP_REG]
        sp = registers[ARM_REG_SP][1]
        next_site = site + instruction.size
        if site in calls:
            require(not any(local(registers.get(r)) for r in CLOBBERED),
                    'local aliases cannot cross a call in scratch registers')
            require(not any(local(x) for x in cells.values()),
                    'local pointer slots cannot cross an ordinary call')
            call_records.append(dict(site=site, target=calls[site], SP_offset=sp,
                preserved_local_aliases=[[r-R0,registers[r][1]] for r in PRESERVED
                                         if local(registers.get(r))]))
            for r in CLOBBERED:
                registers.pop(r, None)
            flags = None
        elif op == 'push':
            require(regs and not any(r in (ARM_REG_SP, ARM_REG_PC) for r in regs),
                    'unsupported finite-loop push register')
            new_sp = sp-4*len(regs)
            require(new_sp >= -MAX_FRAME, 'finite local frame exceeds its bound')
            for number, r in enumerate(regs):
                at = new_sp+4*number
                require(at not in cells, 'finite push overlaps live storage')
                cells[at] = registers.get(r); protected.add(at)
            registers[ARM_REG_SP] = ('local', new_sp)
            minimum = min(minimum, new_sp)
        elif op == 'pop':
            require(regs and ARM_REG_PC not in regs and ARM_REG_SP not in regs,
                    'finite loops require explicit interworking return')
            for number, r in enumerate(regs):
                at = sp+4*number
                require(at in protected, 'finite pop must consume a protected save')
                registers[r] = cells.pop(at); protected.remove(at)
            registers[ARM_REG_SP] = ('local', sp+4*len(regs))
        elif op in ('sub', 'add') and regs and regs[0] == ARM_REG_SP:
            require(len(operands) == 2 and operands[1].type == ARM_OP_IMM,
                    'finite frame adjustment must be a constant')
            amount = operands[1].imm
            require(amount > 0 and amount % 4 == 0, 'finite frame adjustment alignment differs')
            new_sp = sp + (amount if op == 'add' else -amount)
            require(-MAX_FRAME <= new_sp <= 0, 'finite frame adjustment exceeds entry bounds')
            if new_sp > sp:
                require(not any(sp <= at < new_sp for at in protected),
                        'finite release would discard protected saved words')
                cells = {at:x for at,x in cells.items() if at >= new_sp}
            else:
                require(not any(new_sp <= at < sp for at in cells), 'finite allocation overlaps storage')
            registers[ARM_REG_SP] = ('local', new_sp)
            minimum = min(minimum, new_sp)
        elif op in ('mov', 'movs'):
            require(len(operands) == 2 and regs[0] not in (ARM_REG_SP, ARM_REG_PC),
                    'finite loops exclude uncontrolled SP/PC writes')
            registers[regs[0]] = value(operands[1])
            if op == 'movs': flags = None
        elif op in ('adds', 'add', 'subs'):
            require(regs and regs[0] not in (ARM_REG_SP, ARM_REG_PC),
                    'finite arithmetic destination is controlled')
            left = registers.get(regs[0]) if len(operands) == 2 else value(operands[1])
            right = value(operands[-1])
            if right is not None and right[0] == 'constant':
                result = offset(left, -right[1] if op == 'subs' else right[1])
            elif op != 'subs' and left is not None and left[0] == 'constant' and local(right):
                result = offset(right, left[1])
            else:
                require(not local(left) and not local(right), 'local pointer arithmetic lacks a constant offset')
                result = None
            registers[regs[0]] = result
            if op != 'add': flags = None
        elif op == 'lsls':
            require(len(operands) == 3 and operands[2].type == ARM_OP_IMM,
                    'finite loops require immediate logical shifts')
            prior = value(operands[1]); amount = operands[2].imm
            require(not local(prior) and 0 <= amount < 32, 'finite shift cannot encode a local pointer')
            registers[regs[0]] = constant(prior[1] << amount) if prior and prior[0] == 'constant' else None
            flags = None
        elif op == 'cmp':
            left, right = map(value, operands)
            require(left is not None and right is not None and
                    left[0] == right[0] == 'constant', 'finite branch requires exact scalar operands')
            flags = compare(left[1], right[1])
        elif op in CONDITIONS:
            require(flags is not None, 'finite branch has unknown or stale flags')
            take = CONDITIONS[op](*flags)
            next_site = operands[0].imm if take else site+2
            branches.append([site, take, next_site])
        elif op == 'b':
            next_site = operands[0].imm
        elif op in ('ldr', 'str'):
            require(len(operands) == 2 and not operands[1].mem.index,
                    'finite word memory requires a base and immediate displacement')
            mem = operands[1].mem
            if mem.base == ARM_REG_PC:
                require(op == 'ldr', 'finite loop cannot write a literal pool')
                at = ((site+4) & ~3)+mem.disp-address
                require(0 <= at <= len(data)-4, 'finite literal is outside owner')
                registers[regs[0]] = constant(struct.unpack_from('<I', data, at)[0])
            else:
                pointer = offset(registers.get(mem.base), mem.disp)
                if local(pointer):
                    result = access(pointer, op == 'ldr', registers.get(regs[0]))
                    if op == 'ldr': registers[regs[0]] = result
                else:
                    require(op == 'ldr', 'finite loops exclude external stores')
                    require(pointer is not None and pointer[0] == 'constant' and pointer[1] % 4 == 0,
                            'external read requires an aligned constant address')
                    accesses.append([site, 'conditional-external-read', pointer[1], 4])
                    registers[regs[0]] = None
        elif op == 'ldm':
            require(len(regs) == 2 and regs[0] != regs[1] and instruction.writeback,
                    'finite loops admit only one-word local cursor loads')
            pointer = registers.get(regs[0])
            registers[regs[1]] = access(pointer, True)
            registers[regs[0]] = offset(pointer, 4)
        elif op == 'bx':
            require(len(regs) == 1 and registers.get(regs[0]) == ('entry', ARM_REG_LR),
                    'finite return lacks exact entry LR provenance')
            require(sp == 0 and not cells and not protected and
                    all(registers.get(r) == ('entry', r) for r in PRESERVED),
                    'finite return does not restore its complete entry frame')
            require(not any(local(v) for r,v in registers.items() if r != ARM_REG_SP),
                    'finite return retains a private pointer')
            require(reached == set(instructions), 'finite path does not cover the complete structural CFG')
            return dict(steps=len(trace), trace=trace, branches=branches, accesses=accesses,
                        calls=call_records, frame_bytes=-minimum, complete=True,
                        local_words_initialized_before_reads=True, protected_words_restored=True,
                        raw_numeric_result=None)
        else:
            raise ValueError('unsupported finite-loop instruction at %08X: %s' % (site, op))
        require(next_site in edges[site], 'finite successor differs from complete CFG')
        site = next_site
    raise ValueError('finite-loop step budget exhausted')


def prove(data, address, rom, mapping, index, objects, bindings):
    import owner_admission_profile as owner
    refinement = owner.refine(data, address, mapping)
    instructions, edges, local_calls, calls, words = graph.graph(data, address, refinement)
    require(not local_calls and not words, 'finite loops exclude local BL and word switches')
    require(bindings is not None and not bindings['functions'] and not bindings['switches'],
            'finite loops require exact call/data-only original bindings')
    rows = json.loads(mapping)
    row = next(x for x in rows if int(x['rom'],16) == address)
    text_rows = [x.split() for x in index.decode().splitlines() if x.split() and x.split()[0] == f'{address:08X}']
    require(row['instrs'] == len(instructions) and len(text_rows) == 1 and
            int(text_rows[0][3]) == len(instructions), 'finite loop exact instruction counts differ')
    operations.verify_operations(instructions, edges, address, local_calls, calls, refinement)
    if address == 0x080C6858:
        import history_unit_list as history
        return history.prove(data,address,rom,mapping,index,objects,bindings,
                             instructions,edges,calls,refinement)
    runtime_names = []
    for site, target in calls.items():
        if target == thunk.ALIASES['_call_via_r3']:
            runtime_names.append('_call_via_r3')
        else:
            match.function_address_target(f'func_{target:08X}', rows, address, len(data), len(rom))
    dependencies = thunk.dependencies(runtime_names, rom)
    names = [[site-address, '_call_via_r3' if target == thunk.ALIASES['_call_via_r3']
              else f'func_{target:08X}'] for site,target in sorted(calls.items())]
    require(bindings['calls'] == names, 'finite loop original call identities differ')
    result = execute(data, address, instructions, edges, calls)
    require(result['branches'] and calls, 'finite policy requires actual bounded loops and calls')
    return dict(schema=SCHEMA, instructions=len(instructions), calls=names, runtime_calls=[],
        partition=graph.partition(data,address,refinement,instructions,words),
        finite_local_words=result, thunk_dependencies=dependencies,
        premises=['Aligned live entry stack supports the complete bounded frame without address wrap.',
            'Each direct or source callback returns preserving R4-R11 and SP under the ordinary call ABI.',
            'External reads and callees do not modify the protected live caller frame or code.',
            'External pointer validity, callback installation, pointee extents and allocator behavior remain conditions.'],
        physical_memory_claim=False, allocator_effects_claim=False, installed_image_claim=False,
        producer_sha256={Path(m.__file__).name:hashlib.sha256(Path(m.__file__).read_bytes()).hexdigest()
                        for m in (match, match.armv4t,graph,operations,thunk,__import__(__name__))})
