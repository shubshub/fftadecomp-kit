"""Bounded scalar loops with exact local pointer spills and read-only leaf effects.

The earlier word-only selector stays separate. This policy retains every spilled
local origin, rejects its interpretation as scalar data, and authenticates the
complete actual leaf before allowing a scratch alias to cross its call. Ordinary
callees with retained pointer slots need a complete private-frame proof and keep
explicit returning-ABI and caller-frame noninterference conditions.
"""
import hashlib
import json
from pathlib import Path
import struct

import match
import owner_graph_profile as graph
import owner_runtime_profile as operations
import function_thunk_profile as thunk
import local_long_branch_profile as frame_source
import rom_mirror
import ignored_leaf_alias_profile as leaf_source
import consumer_scratch_alias_profile as read_source
from capstone.arm import ARM_OP_IMM, ARM_OP_REG, ARM_REG_SP, ARM_REG_PC, ARM_REG_LR

SELECTOR = 'conditional-finite-spilled-scalar-loops-v1'
SCHEMA = 'elf-symbol-thumb-conditional-finite-spilled-scalar-loops-v1'
CONTROL_FLOW = 'finite scalar loops with exact initialized local words, retained pointer spills and actual read-only leaf effects'
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


class CallEffects:
    """Actual leaf effects retain untouched registers and every local slot."""

    def __init__(self, rom, mapping, index, objects, caller, size, calls):
        self.rom, self.mapping, self.index, self.objects = rom, mapping, index, objects
        self.caller, self.size, self.calls = caller, size, dict(calls)
        self.leaves, self.ordinary = {}, {}

    def leaf(self, target):
        import ignored_leaf_alias_profile as ignored
        from consumer_scratch_alias_profile import scalar_read_effects
        if target not in self.leaves:
            class Readonly(ignored.IgnoredLeafAliasProof):
                instruction_effects = staticmethod(scalar_read_effects)
            proof = Readonly(self.rom,self.mapping,self.index,self.objects,
                             self.caller,self.size,self.calls)
            data,native,instructions,edges,returns,accesses = proof.leaf(target)
            site, visited, ordered = target, set(), []
            while True:
                require(site not in visited, 'scalar leaf cannot cycle')
                visited.add(site)
                read,written = accesses[site]
                require(ARM_REG_SP not in read | written,
                        'scalar leaf must not observe any stack or pointer slot')
                ordered.append((site,read,written))
                if site in returns: break
                require(len(edges[site]) == 1, 'scalar leaf requires one complete straight path')
                site = edges[site][0]
            require(visited == set(instructions), 'scalar leaf does not cover its full CFG')
            self.leaves[target] = (ordered,dict(address=target,bytes=len(data),
                body_sha256=hashlib.sha256(data).hexdigest(),owner=native,
                effects=[[pc,sorted(read),sorted(written)] for pc,read,written in ordered],
                caller_memory_observation=False,untouched_registers_retained=True))
        return self.leaves[target]

    def private_frame(self, target):
        import owner_admission_profile as owner
        import local_long_branch_profile as frame
        if target not in self.ordinary:
            rows=json.loads(self.mapping)
            match.function_address_target(f'func_{target:08X}',rows,self.caller,self.size,len(self.rom))
            row=next(r for r in rows if int(r['rom'],16)==target)
            end=int(row['end'],16)
            require(0 < end-target <= 1024, 'ordinary private-frame callee exceeds bounded extent')
            data=self.rom[target-match.ROM_BASE:end-match.ROM_BASE]
            owner.validate_span(data,target,self.rom,self.mapping,self.index)
            refinement=owner.refine(data,target,self.mapping)
            ins,edges,branches,calls,words=graph.graph(data,target,refinement)
            require(not branches and not words, 'private callee excludes local BL and switches')
            operations.verify_operations(ins,edges,target,branches,calls,refinement)
            for destination in calls.values():
                match.function_address_target(f'func_{destination:08X}',rows,target,len(data),len(self.rom))
            partition=graph.partition(data,target,refinement,ins,words)
            names=match.parse_data_symbols(self.objects)
            for word in partition['words']:
                if rom_mirror.typed_domain(word['value']):
                    require(word['value'] in names.values(), 'private callee literal lacks canonical data identity')
            native=frame.prove_frame(ins,edges,target,{},calls,stack_aliases=True)
            require(row['instrs']==len(ins), 'ordinary private-frame callee count differs')
            text_rows=[line.split() for line in self.index.decode().splitlines()
                       if line.split() and line.split()[0]==f'{target:08X}']
            require(len(text_rows)==1 and int(text_rows[0][3])==len(ins),
                    'ordinary private-frame text count differs')
            self.ordinary[target]=dict(address=target,bytes=len(data),
                body_sha256=hashlib.sha256(data).hexdigest(),frame=native,partition=partition,
                nested_calls_remain_conditional=True)
        return self.ordinary[target]

    def apply(self, site, target, registers, cells, protected, sp):
        require(self.calls.get(site)==target and self.caller<=site<self.caller+self.size,
                'scalar call effect lacks an exact reached original binding')
        aliases={r for r in CLOBBERED if local(registers.get(r))}
        slots={at:v for at,v in cells.items() if local(v)}
        for at,value in slots.items():
            require(sp <= at < 0 and sp <= value[1] < 0 and
                    (value[1]&~3) not in protected,
                    'call retains an expired or protected pointer slot')
        if aliases:
            ordered,record=self.leaf(target)
            for pc,read,written in ordered:
                require(not any(local(registers.get(r)) for r in read),
                        'actual scalar leaf observes an incoming local alias')
                for r in written-{ARM_REG_PC}: registers[r]=None
            registers[ARM_REG_LR]=None
            mode='actual-readonly-leaf-retaining-untouched-registers'
        else:
            if slots: self.private_frame(target)
            for r in CLOBBERED: registers.pop(r,None)
            mode='conditional-ordinary-ABI-with-private-frame' if slots else 'conditional-ordinary-ABI'
        return dict(mode=mode,incoming_aliases=sorted(aliases),
                    retained_pointer_slots=[[at,value[1]] for at,value in sorted(slots.items())])

    def manifest(self):
        return dict(readonly_leaves=[self.leaves[t][1] for t in sorted(self.leaves)],
                    ordinary_private_frames=[self.ordinary[t] for t in sorted(self.ordinary)])


def execute(data, address, instructions, edges, calls, *, call_proof, step_limit=MAX_STEPS):
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
        return ('local', base[1]+delta) if local(base) else None

    def access(pointer, loading, payload=None, width=4, signed=False):
        require(local(pointer), 'finite local access lacks exact stack origin')
        at, sp = pointer[1], registers[ARM_REG_SP][1]
        require(width in (1,2,4) and at % width == 0 and sp <= at and at+width <= 0,
                'finite local access is outside the live aligned frame')
        word = at & ~3
        require(word not in protected, 'ordinary local access overlaps a protected save')
        if loading:
            require(word in cells, 'finite local load reads an uninitialized word')
            result = cells[word]
            if width != 4:
                require(not local(result), 'partial scalar read would interpret a local pointer')
                if result is not None and result[0] == 'constant':
                    bits = (result[1] >> (8*(at-word))) & ((1 << (8*width))-1)
                    if signed and bits & (1 << (8*width-1)): bits -= 1 << (8*width)
                    result = constant(bits)
                else: result = None
        else:
            require(width == 4, 'spilled scalar policy excludes partial local writes')
            if local(payload):
                require(sp <= payload[1] < 0 and (payload[1] & ~3) not in protected,
                        'pointer spill has an expired or protected origin')
            cells[at] = payload
            result = None
        accesses.append([site, 'read' if loading else 'write', at, width])
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
            detail = call_proof.apply(site, calls[site], registers, cells, protected, sp)
            call_records.append(dict(site=site, target=calls[site], SP_offset=sp, effect=detail))
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
        elif op in ('lsls','lsrs','asrs','rsbs','muls','ands','orrs','eors'):
            require(regs and regs[0] not in (ARM_REG_SP,ARM_REG_PC), 'scalar destination is controlled')
            args = [value(x) for x in operands[1:]]
            if len(operands) == 2: args.insert(0, registers.get(regs[0]))
            require(not any(local(x) for x in args), 'scalar operation observes a local pointer')
            known = all(x is not None and x[0] == 'constant' for x in args)
            result = None
            if known:
                left,right = (x[1] for x in args)
                if op in ('lsls','lsrs','asrs'):
                    require(operands[-1].type == ARM_OP_IMM and 0 <= right <= 32,
                            'scalar shifts require bounded immediate amounts')
                    signed = left if left < 0x80000000 else left-0x100000000
                    result = left << right if op == 'lsls' else left >> right if op == 'lsrs' else signed >> right
                elif op == 'rsbs': result = right-left
                elif op == 'muls': result = left*right
                elif op == 'ands': result = left & right
                elif op == 'orrs': result = left | right
                else: result = left ^ right
            elif op in ('lsls','lsrs','asrs'):
                require(operands[-1].type == ARM_OP_IMM and 0 <= operands[-1].imm <= 32,
                        'scalar shifts require bounded immediate amounts')
            registers[regs[0]] = None if result is None else constant(result)
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
        elif op in ('ldr','str','ldrb','ldrh','ldrsb','ldrsh'):
            require(len(operands) == 2 and not instruction.writeback,
                    'scalar memory requires one nonwriting-back address')
            mem = operands[1].mem
            width = 1 if op in ('ldrb','ldrsb') else 2 if op in ('ldrh','ldrsh') else 4
            if mem.base == ARM_REG_PC:
                require(op == 'ldr' and not mem.index, 'scalar literal requires a PC-relative word load')
                at = ((site+4) & ~3)+mem.disp-address
                require(0 <= at <= len(data)-4, 'finite literal is outside owner')
                registers[regs[0]] = constant(struct.unpack_from('<I', data, at)[0])
            else:
                base = registers.get(mem.base)
                index = registers.get(mem.index) if mem.index else constant(0)
                require(not local(index), 'memory index cannot be a local pointer')
                if index is not None and index[0] == 'constant':
                    pointer = offset(base, mem.disp+index[1])
                else:
                    require(not local(base), 'local memory index lacks an exact scalar offset')
                    pointer = None
                if local(pointer):
                    result = access(pointer, op != 'str', registers.get(regs[0]), width, op in ('ldrsb','ldrsh'))
                    if op != 'str': registers[regs[0]] = result
                else:
                    require(op != 'str', 'finite loops exclude external stores')
                    if pointer is not None and pointer[0] == 'constant':
                        require(pointer[1] % width == 0 and pointer[1]+width <= 0x100000000,
                                'external scalar address is misaligned or wrapping')
                    accesses.append([site,'conditional-external-read', None if pointer is None else pointer[1],width])
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
    call_proof = CallEffects(rom,mapping,index,objects,address,len(data),calls)
    result = execute(data, address, instructions, edges, calls,call_proof=call_proof)
    require(result['branches'] and calls, 'finite policy requires actual bounded loops and calls')
    return dict(schema=SCHEMA, instructions=len(instructions), calls=names, runtime_calls=[],
        partition=graph.partition(data,address,refinement,instructions,words),
        finite_local_words=result, thunk_dependencies=dependencies, call_effects=call_proof.manifest(),
        premises=['Aligned live entry stack supports the complete bounded frame without address wrap.',
            'Each direct or source callback returns preserving R4-R11 and SP under the ordinary call ABI.',
            'External reads and ordinary callees neither read nor write caller private, saved or incoming frames or code through ambient or hidden aliases; the explicit local operations and authenticated leaf reads are the only exceptions.',
            'External reads require valid aligned live initialized storage, disjoint from all caller frames; loaded words carry no caller-private provenance. Pointer validity, callback installation, pointee extents and allocator behavior remain conditions.'],
        physical_memory_claim=False, allocator_effects_claim=False, installed_image_claim=False,
        producer_sha256={Path(m.__file__).name:hashlib.sha256(Path(m.__file__).read_bytes()).hexdigest()
                        for m in (match, match.armv4t,graph,operations,thunk,frame_source,leaf_source,read_source,__import__(__name__))})
