"""Callers that pass a private stack array to a pinned known list query.

func_08099CDC, func_08099D08 and func_08099D34 differ only in the owner list
word they load (+0x10, +0x14, +0x18).  Each builds a two-word state
{count=0, cursor=R1} and a closure {&state, func_0809AC20} in its own frame,
then calls the iterator func_080C7CC0 with the adapter func_0809ABE8.  The
iterator walks first=list+4, next=node+8 and calls the adapter through
_call_via_r6; the adapter loads node+0 through the getter func_080C7B74 and
calls the collector through _call_via_r2.  The collector stores the value at
the cursor, advances it by four, increments count and returns 1, so every node
is visited.  The query returns count.

That relation is a contract over the exact pinned bytes below; it is not
re-derived through the indirect thunks here.  Under it, a query reached with
n list nodes writes exactly out[0..n-1] (one word each, ascending), returns n
in R0, touches no other caller memory, preserves R4-R11/SP and returns to LR.
The ROM does not bound n: the list length is external state.  The profile
therefore takes one fixed premise, n <= 13, and requires every query buffer to
be at least 13 allocated private words.  The caller is then executed for each
n in 0..13 with the first n buffer words initialized and the rest left as they
were, and a read of any uninitialized private word refuses.
"""
import hashlib
import json
from pathlib import Path

import match
import owner_graph_profile as graph
import function_thunk_profile as thunk
import software_double_profile as software_double
from software_double_profile import indices, span_record
from capstone.arm import ARM_OP_IMM, ARM_OP_REG, ARM_OP_MEM, ARM_REG_SP, ARM_REG_PC, ARM_REG_LR

SELECTOR = 'conditional-known-query-stack-buffer-v1'
SCHEMA = 'elf-symbol-thumb-' + SELECTOR
DIVISION_SELECTOR = 'conditional-known-query-stack-buffer-unsigned-quotient-v1'
DIVISION_SCHEMA = 'elf-symbol-thumb-' + DIVISION_SELECTOR
CONTROL_FLOW = ('complete Thumb caller passing a private stack array of at least 13 words to a '
                'pinned known list query; list length n <= 13 is an unproved premise; every '
                'returned count 0..13 executed; '
                'conditional returning ABI and memory noninterference; termination unproved')
DIVISION_CONTROL_FLOW = CONTROL_FLOW + '; exact canonical unsigned quotient and zero-hook closure'
ROM_BASE = 0x08000000
CAPACITY_WORDS = 13
MAX_STATES = 65536
QUERY_TEMPLATE = ('00b584b000220092019106496a46029202aa5160{load}04492df0{branch}'
                  '009804b002bc084721ac0908e9ab0908')
# address: (owner list offset, encoded LDR R0,[R0,#offset], BL to 080C7CC0)
QUERIES = {
    0x08099CDC: (0x10, '0069', 'e4ff'),
    0x08099D08: (0x14, '4069', 'ceff'),
    0x08099D34: (0x18, '8069', 'b8ff'),
}
DEPENDENCIES = {
    0x080C7CC0: (16, '70b50e1c151c446800e0a468002c05d0201c291c7af0c2fa0028f6d170bc01bc0047'),
    0x0809ABE8: (9, '10b50c1c2cf0c2ff21686268a7f02afb10bc02bc0847'),
    0x0809AC20: (8, '4a6801c20868013008604a6001207047'),
    0x080C7B74: (2, '00687047'),
    0x0814225C: (1, '3047'),
    0x0814224C: (1, '1047'),
}
THUNK_PADDING = {0x0814225C: 'c046', 0x0814224C: 'c046'}
QUERY_FRAME_BYTES = 44  # root 20 + iterator 16 + adapter 8; collector and getter are leaves
R0 = match.ARM_REG_R0
R12 = match.ARM_REG_R12
PRESERVED = tuple(range(R0+4, R0+12))
CLOBBERED = (R0, R0+1, R0+2, R0+3, R12, ARM_REG_LR)
EXT = ('ext',)
DEAD = ('dead',)  # a pushed register that held no defined value; popping it leaves it undefined
CONDITIONS = {
    'beq': lambda n, z, c, v: z, 'bne': lambda n, z, c, v: not z,
    'bhs': lambda n, z, c, v: c, 'blo': lambda n, z, c, v: not c,
    'bmi': lambda n, z, c, v: n, 'bpl': lambda n, z, c, v: not n,
    'bvs': lambda n, z, c, v: v, 'bvc': lambda n, z, c, v: not v,
    'bhi': lambda n, z, c, v: c and not z, 'bls': lambda n, z, c, v: not c or z,
    'bge': lambda n, z, c, v: n == v, 'blt': lambda n, z, c, v: n != v,
    'bgt': lambda n, z, c, v: not z and n == v, 'ble': lambda n, z, c, v: z or n != v,
}
CONDITIONS['bcs'], CONDITIONS['bcc'] = CONDITIONS['bhs'], CONDITIONS['blo']
WIDTHS = {'ldr': 4, 'str': 4, 'ldrh': 2, 'strh': 2, 'ldrb': 1, 'strb': 1, 'ldrsh': 2, 'ldrsb': 1}
EXPLICIT_CONDITIONS = [
    'Every list reached by a pinned query from this caller has at most 13 nodes and is finite and acyclic. '
    'The ROM does not prove this bound; it is the single fixed premise that makes the 13-word buffer sufficient.',
    'Every reached owner, list, node and node-value load in the pinned query is aligned, live and readable, and '
    'no list node or loaded value overlaps an active stack frame, saved return or code.',
    'The pinned query, iterator, adapter, collector, getter and thunks run as their exact ROM bytes: each '
    'returns to its caller, restores R4-R11 and SP, and uses at most 44 bytes of stack below the caller SP.',
    'Each ordinary direct call returns preserving R4-R11 and SP and does not write the caller frame, including '
    'the query buffer, through any argument, ambient state or hidden alias. Its only reads of the caller frame '
    'are its own stack-passed arguments: initialized words starting at the caller SP at the call, as many as its '
    'actual prototype passes (not checked here). It reads no saved word and no uninitialized word. A callee may '
    'store into its own stack-passed parameter slots (gcc 2.95 can home a parameter there), so after each '
    'ordinary call the contiguous initialized unprotected words from the caller SP become unknown values; it '
    'stores nothing else in the caller frame.',
    'External reads and writes in the caller are to valid aligned live storage that does not overlap the caller '
    'frame, saved returns or code; their values carry no private-frame provenance.',
    'C object layout, function compatibility, effective types and initialized external scalars remain source '
    'obligations. No physical memory permission or termination is established.',
]


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def query_body(address):
    _, load, branch = QUERIES[address]
    return bytes.fromhex(QUERY_TEMPLATE.format(load=load, branch=branch))


def contract(rom, mapping, index):
    """Bind the pinned query family to the current ROM, mapping and text index."""
    entries, rows = indices(mapping, index)
    identities = []
    pinned = {address: (17, query_body(address)) for address in QUERIES}
    pinned.update({address: (count, bytes.fromhex(code)) for address, (count, code) in DEPENDENCIES.items()})
    for start, (count, body) in sorted(pinned.items()):
        end = start+len(body)
        row = span_record(start, end, entries, rows, rom)
        require(row['mode'] == 'thumb' and row['instrs'] == count and
                rom[start-ROM_BASE:end-ROM_BASE] == body,
                'pinned known-query dependency bytes, extent or count differ')
        identities.append(dict(address=start, end=end, instructions=count, body_sha256=sha(body)))
    for start, padding in sorted(THUNK_PADDING.items()):
        lo, hi = start+2, start+4
        require(rom[lo-ROM_BASE:hi-ROM_BASE] == bytes.fromhex(padding) and
                not any(int(e['rom'], 16) < hi and int(e['end'], 16) > lo for e in entries) and
                not any(int(r[0], 16) < hi and int(r[1], 16) > lo for r in rows),
                'pinned query thunk padding must remain separate and unowned')
    return dict(
        queries=[dict(address=a, owner_list_offset=QUERIES[a][0]) for a in sorted(QUERIES)],
        iterator=0x080C7CC0, adapter=0x0809ABE8, collector=0x0809AC20, getter=0x080C7B74,
        thunks=dict(_call_via_r6=0x0814225C, _call_via_r2=0x0814224C),
        identities=identities, capacity_words=CAPACITY_WORDS, stack_bytes_below_caller=QUERY_FRAME_BYTES,
        relation=('With n list nodes the query stores node value k at out+4k for k=0..n-1 in ascending order, '
                  'returns n in R0, writes no other caller memory, and preserves R4-R11/SP.'),
        visitors=['func_0809ABE8 via _call_via_r6 (only)', 'func_0809AC20 via _call_via_r2 (only)'],
        write_bound='premise n <= 13; the ROM imposes no cap',
        clobbers=['r0', 'r1', 'r2', 'r3', 'r12', 'lr'])


def compare(left, right):
    result = (left-right) & 0xffffffff
    return (bool(result & 0x80000000), result == 0, left >= right,
            bool((left ^ right) & (left ^ result) & 0x80000000))


def signed(value):
    value &= 0xffffffff
    return value-0x100000000 if value & 0x80000000 else value


def is_sp(value):
    return value[0] == 'sp'


def saved(value):
    return value[0] in ('entry', 'lr')


def execute(data, address, instructions, edges, calls, *, unsigned_quotient=False):
    """Explore every path for every premised count; return a deterministic summary."""
    registers = {r: EXT for r in range(R0, R0+4)}
    registers.update({r: ('entry', r-R0) for r in PRESERVED})
    registers[R12] = EXT
    registers[ARM_REG_LR] = ('lr',)
    initial = (address, tuple(sorted(registers.items())), 0, (), (), None)
    pending, seen = [initial], {initial}
    reached, local_reads, local_writes = set(), set(), set()
    external, query_calls, ordinary_calls, returns = set(), {}, set(), set()
    stack_words = {}
    counts_returned = set()
    minimum = 0

    def push(state):
        if state not in seen:
            require(len(seen) < MAX_STATES, 'known-query caller state budget exhausted')
            seen.add(state); pending.append(state)

    while pending:
        site, regs, sp, cells, protected, flags = pending.pop()
        require(site in instructions, 'known-query caller left its complete CFG')
        reached.add(site)
        regs, cells, protected = dict(regs), dict(cells), set(protected)
        ins = instructions[site]
        op, ops = ins.mnemonic, ins.operands
        rr = [o.reg for o in ops if o.type == ARM_OP_REG]
        following = [site+ins.size]
        minimum = min(minimum, sp)

        def value(operand):
            if operand.type == ARM_OP_IMM:
                return ('c', operand.imm & 0xffffffff)
            require(operand.type == ARM_OP_REG, 'unsupported known-query caller operand')
            if operand.reg == ARM_REG_SP:
                return ('sp', sp)
            return register(operand.reg)

        def register(number):
            if number == ARM_REG_SP:
                return ('sp', sp)
            require(number in regs, 'known-query caller reads PC or an untracked register as a value')
            return regs[number]

        def held(number, default=EXT):
            # Inspection only: an undefined register is not a private address.
            return regs.get(number, default)

        def scalar(*values):
            for v in values:
                require(not saved(v), 'saved register value used in arithmetic')
                require(not is_sp(v), 'private stack address used in unsupported arithmetic')

        def local(at, width, loading, payload=None):
            require(width == 4 and at % 4 == 0, 'known-query caller private access must be an aligned word')
            require(sp <= at and at+4 <= 0 and at not in protected,
                    'private access is outside allocated local words')
            if loading:
                require(at in cells, 'private load reads an uninitialized local word')
                local_reads.add((site, at))
                return cells[at]
            require(not is_sp(payload) and not saved(payload), 'private pointer or saved value stored to a local word')
            cells[at] = payload
            local_writes.add((site, at))
            return None

        if site in calls:
            target = calls[site]
            require(op == 'bl', 'known-query caller call is not a direct BL')
            require(not any(is_sp(held(r)) or saved(held(r)) for r in (R0, R0+2, R0+3, R12)),
                    'private stack address or saved value passed to a call')
            if target in QUERIES:
                base = held(R0+1)
                require(is_sp(base) and base[1] % 4 == 0, 'query buffer must be an aligned private stack address')
                buffer = [base[1]+4*k for k in range(CAPACITY_WORDS)]
                require(all(sp <= at and at+4 <= 0 and at not in protected for at in buffer),
                        'query buffer is smaller than the premised 13-word write bound')
                record = dict(site=site, target=target, buffer_entry_SP_offset=base[1],
                              buffer_words=CAPACITY_WORDS, caller_SP_offset=sp)
                require(query_calls.setdefault(site, record) == record,
                        'query buffer differs across incoming paths')
                for n in range(CAPACITY_WORDS+1):
                    after = dict(cells)
                    for at in buffer[:n]:
                        after[at] = EXT
                    # Only R0 is defined after the query. In particular the pinned
                    # collector leaves R2 = out+4n, which may address a saved word.
                    out = {r: v for r, v in regs.items() if r not in CLOBBERED}
                    out[R0] = ('c', n)
                    counts_returned.add(n)
                    require(site+4 in edges[site], 'query continuation differs from the complete CFG')
                    push((site+4, tuple(sorted(out.items())), sp, tuple(sorted(after.items())),
                          tuple(sorted(protected)), None))
                continue
            require(not is_sp(held(R0+1)) and not saved(held(R0+1)),
                    'private stack address passed to a call outside the pinned query contract')
            require(target not in DEPENDENCIES, 'direct call to a pinned query dependency')
            if unsigned_quotient and target == match.UDIVSI3_ADDRESS:
                # Only the two defined scalar ABI operands are consumed. The
                # native closure has no caller-frame reads or writes. Do not
                # manufacture quotient/flags facts or retain scratch values.
                scalar(register(R0), register(R0+1))
                for r in CLOBBERED:
                    regs.pop(r, None)
                regs[R0] = EXT
                flags = None
                require(site+4 in edges[site], 'quotient continuation differs from the complete CFG')
                push((site+4, tuple(sorted(regs.items())), sp, tuple(sorted(cells.items())),
                      tuple(sorted(protected)), flags))
                continue
            ordinary_calls.add((site, target))
            # Stack-argument evidence: the initialized unprotected words from SP,
            # which a callee may read and may overwrite as homed parameters.
            run = 0
            while sp+4*run < 0 and sp+4*run in cells and sp+4*run not in protected:
                cells[sp+4*run] = EXT
                run += 1
            stack_words.setdefault(site, set()).add(run)
            for r in CLOBBERED:
                regs.pop(r, None)
            regs[R0] = EXT
            flags = None
        elif op == 'push':
            require(rr and ARM_REG_SP not in rr and ARM_REG_PC not in rr, 'unsupported push')
            new = sp-4*len(rr)
            for k, r in enumerate(rr):
                at = new+4*k
                require(at not in cells, 'push overlaps live private storage')
                cells[at] = held(r, DEAD); protected.add(at)
            sp = new
        elif op == 'pop':
            require(rr and ARM_REG_SP not in rr, 'unsupported pop')
            for k, r in enumerate(rr):
                at = sp+4*k
                require(at in protected, 'pop must consume a protected saved word')
                protected.remove(at)
                restored = cells.pop(at)
                if restored == DEAD:
                    regs.pop(r, None)
                else:
                    regs[r] = restored
            sp += 4*len(rr)
            if ARM_REG_PC in rr:
                require(regs.pop(ARM_REG_PC, None) == ('lr',), 'pop to PC lacks entry return provenance')
                following = None
        elif op in ('add', 'sub') and rr and rr[0] == ARM_REG_SP and len(ops) == 2:
            require(ops[1].type == ARM_OP_IMM and ops[1].imm > 0 and ops[1].imm % 4 == 0,
                    'stack adjustment must be a positive word multiple')
            new = sp + (ops[1].imm if op == 'add' else -ops[1].imm)
            require(-4096 <= new <= 0, 'stack adjustment leaves the bounded frame')
            if new > sp:
                require(not any(sp <= at < new for at in protected), 'stack release discards saved words')
                cells = {at: v for at, v in cells.items() if at >= new}
            sp = new
        elif op == 'bx':
            require(len(rr) == 1 and regs.get(rr[0]) == ('lr',), 'return lacks entry LR provenance')
            following = None
        elif op in ('mov', 'movs'):
            require(len(ops) == 2 and rr[0] not in (ARM_REG_SP, ARM_REG_PC), 'uncontrolled SP or PC write')
            regs[rr[0]] = value(ops[1])
            if op == 'movs':
                flags = None
        elif op in ('adds', 'subs', 'add', 'sub'):
            require(rr and rr[0] not in (ARM_REG_SP, ARM_REG_PC), 'arithmetic writes SP or PC')
            left = value(ops[0] if len(ops) == 2 else ops[1])
            right = value(ops[-1])
            for v in (left, right):
                require(not saved(v), 'saved register value used in arithmetic')
            negative = op in ('subs', 'sub')
            if left[0] == right[0] == 'c':
                result = ('c', (left[1]-right[1] if negative else left[1]+right[1]) & 0xffffffff)
            elif is_sp(left) and right[0] == 'c':
                result = ('sp', left[1] + (-right[1] if negative else right[1]))
            elif is_sp(right) and left[0] == 'c' and not negative:
                result = ('sp', right[1]+left[1])
            else:
                scalar(left, right)
                result = EXT
            if is_sp(result):
                result = ('sp', signed(result[1]))
            regs[rr[0]] = result
            if op in ('adds', 'subs'):
                flags = None
        elif op in ('lsls', 'lsrs', 'asrs', 'ands', 'orrs', 'eors', 'bics', 'mvns', 'rsbs', 'muls'):
            require(rr and rr[0] not in (ARM_REG_SP, ARM_REG_PC), 'logical operation writes SP or PC')
            if len(ops) == 3:
                a, b = value(ops[1]), value(ops[2])
            elif op == 'mvns':
                a = b = value(ops[1])
            else:
                a, b = value(ops[0]), value(ops[1])
            scalar(a, b)
            if a[0] == b[0] == 'c':
                x, y = a[1], b[1]
                negative_x = signed(x)
                amount = y & 0xff
                r = {'lsls': (x << amount) if amount < 32 else 0,
                     'lsrs': (x >> amount) if amount < 32 else 0,
                     'asrs': negative_x >> min(amount, 32),
                     'ands': x & y, 'orrs': x | y, 'eors': x ^ y, 'bics': x & ~y,
                     'mvns': ~y, 'rsbs': y-x, 'muls': x*y}[op]
                regs[rr[0]] = ('c', r & 0xffffffff)
            else:
                regs[rr[0]] = EXT
            flags = None
        elif op in ('cmp', 'cmn', 'tst'):
            left, right = value(ops[0]), value(ops[1])
            scalar(left, right)
            flags = compare(left[1], right[1]) if op == 'cmp' and left[0] == right[0] == 'c' else None
        elif op in CONDITIONS:
            target = ops[0].imm
            if flags is None:
                following = [target, site+2]
            else:
                following = [target if CONDITIONS[op](*flags) else site+2]
        elif op == 'b':
            following = [ops[0].imm]
        elif op in WIDTHS:
            require(len(ops) == 2 and ops[1].type == ARM_OP_MEM and not ins.writeback,
                    'unsupported known-query caller memory access')
            mem, width, loading = ops[1].mem, WIDTHS[op], op.startswith('ldr')
            require(rr[0] not in (ARM_REG_SP, ARM_REG_PC), 'memory access transfers SP or PC')
            if mem.base == ARM_REG_PC:
                require(op == 'ldr' and not mem.index, 'only literal word loads may address PC')
                at = ((site+4) & ~3)+mem.disp-address
                require(0 <= at <= len(data)-4, 'literal is outside the complete function')
                regs[rr[0]] = ('c', int.from_bytes(data[at:at+4], 'little'))
            else:
                base = register(mem.base)
                offset = ('c', mem.disp & 0xffffffff)
                if mem.index:
                    offset = register(mem.index)
                    require(not mem.disp, 'indexed access with displacement is unsupported')
                require(not saved(base) and not saved(offset), 'memory access through a saved value')
                if is_sp(base) or is_sp(offset):
                    require(not (is_sp(base) and is_sp(offset)), 'two private addresses in one access')
                    pointer, delta = (base, offset) if is_sp(base) else (offset, base)
                    require(delta[0] == 'c', 'private access with an unknown index')
                    at = signed(pointer[1]+delta[1])
                    if loading:
                        require(op == 'ldr', 'known-query caller private access must be an aligned word')
                        regs[rr[0]] = local(at, width, True)
                    else:
                        require(op == 'str', 'known-query caller private access must be an aligned word')
                        local(at, width, False, register(rr[0]))
                else:
                    if loading:
                        regs[rr[0]] = EXT
                    else:
                        payload = register(rr[0])
                        require(not is_sp(payload) and not saved(payload),
                                'private address or saved value stored to external memory')
                    external.add((site, 'read' if loading else 'write', width))
        else:
            raise ValueError('unsupported known-query caller instruction at %08X: %s' % (site, op))
        if following is None:
            require(sp == 0 and not protected and not cells and
                    all(regs.get(r) == ('entry', r-R0) for r in PRESERVED),
                    'return does not restore the complete entry frame')
            require(not any(is_sp(held(r)) for r in (R0, R0+1, R0+2, R0+3, R12)),
                    'private stack address escapes through a return register')
            returns.add(site)
            continue
        for successor in following:
            require(successor in edges[site], 'successor differs from the complete structural CFG')
            push((successor, tuple(sorted(regs.items())), sp, tuple(sorted(cells.items())),
                  tuple(sorted(protected)), flags))
    require(reached == set(instructions), 'known-query caller paths do not cover the complete CFG')
    require(query_calls and counts_returned == set(range(CAPACITY_WORDS+1)) and returns,
            'known-query caller requires an actual query call and return')
    return dict(states=len(seen), returned_counts=sorted(counts_returned),
                query_calls=[query_calls[s] for s in sorted(query_calls)],
                ordinary_calls=sorted([s, t] for s, t in ordinary_calls),
                ordinary_call_initialized_words_at_SP=[[s, sorted(stack_words[s])] for s in sorted(stack_words)],
                local_reads=sorted([s, a] for s, a in local_reads),
                local_writes=sorted([s, a] for s, a in local_writes),
                external_accesses=sorted([s, k, w] for s, k, w in external),
                returns=sorted(returns), frame_bytes=-minimum,
                uninitialized_private_reads=0, all_paths_interpreted=True)


def quotient_contract(rom, mapping, index):
    """Canonical versioned identity, native closure and independent frame proof."""
    import zero_aware_unsigned_quotient_inventory as quotient
    import local_long_branch_profile as frame
    import owner_admission_profile as owner
    zero, address, end = 0x0814274C, quotient.UDIV, 0x08142B28
    proofs = quotient.prove_quotient_closure(rom, mapping, index)
    require(set(proofs) == {zero, address} and
            not any(p['writes'] or p['stack_reads'] for p in proofs.values()) and
            proofs[address]['returns'] == [0x08142B1C, 0x08142B26] and
            proofs[zero]['returns'] == [zero],
            'unsigned quotient requires both complete native runtime cases')
    data = rom[address-ROM_BASE:end-ROM_BASE]
    instructions, edges, branches, calls, words = graph.graph(
        data, address, owner.refine(data, address, mapping))
    require(not branches and not words and calls == {0x08142B20: zero} and not any(
        operand.mem.base != ARM_REG_SP or operand.mem.index
        for ins in instructions.values() for operand in ins.operands if operand.type == ARM_OP_MEM),
        'unsigned quotient requires stack-only runtime accesses and exact zero call')
    restored = frame.prove_frame(instructions, edges, address, {}, calls,
        call_preservation={site: frozenset(PRESERVED) for site in calls})
    require(restored['returns'] == proofs[address]['returns'],
            'unsigned quotient independent frame return coverage differs')
    return dict(identities=[list(row) for row in match.UDIVSI3_IDENTITIES],
        native_runtime_closure=[[site, proof] for site, proof in sorted(proofs.items())],
        frame=restored, maximum_additional_stack_bytes=restored['maximum_frame_bytes'],
        caller_memory_writes=[], caller_stack_reads=[], restores='r4-r11,sp,entry-lr',
        nonzero='exact canonical unsigned 32-bit quotient; no signed-overflow case',
        zero='exact returning zero hook 0814274C; R0 is zero',
        operands='defined scalar R0/R1, no private-frame or saved-value provenance',
        result='unknown scalar R0; no quotient or flags facts; R1-R3/R12/LR undefined',
        source_obligation='C division requires a nonzero divisor; runtime zero behavior does not discharge it')


def prove(data, address, rom, mapping, index, objects, bindings, *, selector=SELECTOR):
    import owner_admission_profile as owner
    require(all(type(raw) is bytes for raw in (data, rom, mapping, index)),
            'known-query stack buffer requires immutable complete inputs')
    require(selector in (SELECTOR, DIVISION_SELECTOR), 'unknown known-query stack buffer selector')
    division = selector == DIVISION_SELECTOR
    refinement = owner.refine(data, address, mapping)
    instructions, edges, local_calls, calls, words = graph.graph(data, address, refinement)
    require(not local_calls and not words, 'known-query stack buffer excludes local BL and word switches')
    require(type(bindings) is dict and not bindings['functions'] and not bindings['switches'],
            'known-query stack buffer requires exact call/data-only original bindings')
    rows = json.loads(mapping)
    # Legacy index counts are bounded annotations (named_data_buffer.validate_owner);
    # the complete structural CFG interpreted below establishes the real count.
    require(address not in QUERIES and address not in DEPENDENCIES, 'pinned query bodies are not callers')
    runtime = quotient_contract(rom, mapping, index) if division else None
    if division:
        require(match.UDIVSI3_ADDRESS in calls.values(), 'quotient composition requires an actual canonical division call')
    for site, target in calls.items():
        if division and target == match.UDIVSI3_ADDRESS:
            continue
        match.function_address_target(f'func_{target:08X}', rows, address, len(data), len(rom))
    names = [[site-address, '__udivsi3' if division and target == match.UDIVSI3_ADDRESS
              else f'func_{target:08X}'] for site, target in sorted(calls.items())]
    require(bindings['calls'] == names, 'known-query caller original call identities differ')
    pinned = contract(rom, mapping, index)
    result = execute(data, address, instructions, edges, calls, unsigned_quotient=division)
    proof = dict(schema=DIVISION_SCHEMA if division else SCHEMA, instructions=len(instructions),
        calls=[row for row in names if row[1] != '__udivsi3'],
        runtime_calls=[row for row in names if row[1] == '__udivsi3'],
        partition=graph.partition(data, address, refinement, instructions, words),
        query_contract=pinned, caller=result, explicit_conditions=list(EXPLICIT_CONDITIONS),
        list_bound_proved_from_ROM=False, physical_memory_permission=False,
        actual_C_function_compatibility_proved=False, termination_proved=False,
        producer_sha256={Path(m.__file__).name: sha(Path(m.__file__).read_bytes())
                         for m in (match, graph, thunk, owner, software_double, __import__(__name__))})

    if division:
        import zero_aware_unsigned_quotient_inventory as quotient
        import local_long_branch_profile as frame
        import software_float_profile as software_float
        proof['unsigned_quotient'] = runtime
        proof['producer_sha256'].update({Path(m.__file__).name: sha(Path(m.__file__).read_bytes())
            for m in (quotient, frame, software_float)})
    return proof
