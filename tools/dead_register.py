"""Dead registers: a value that no path reads before overwriting it.

`prove` is the walk behind the entry-prefix checks of three proofs and the
default call rule below.  A caller gives the start, the registers whose current
values must be dead, and a step function for one instruction (or one node of
its own graph).  The step raises ValueError for anything that may observe a
live value - a read, a save, a call, a return, an unknown transfer, whatever
the caller's effect table does not admit - and otherwise returns the live
registers it overwrites and its successors.  A value is dead when every path
writes it before reading it: every state the walk reaches is checked, a path
that ends with a live value refuses, and so does a cycle that can avoid the
killing write (least fixpoint), even one that never reads the value.

Three proofs use it with their own effect tables and messages: the
incoming-scratch overwrite selector (`incoming_scratch_overwrite_profile`),
the R6 callback scratch-prefix kill (`static_callback_r6_frame_profile`) and
the dead-argument named-data walk (`dead_argument_buffer_profile`).

`DeadStackRegisters` is the default stack-argument buffer proofs' policy.  A
call whose callee would be inspected only because of stack addresses in R0-R3
is not inspected when inspecting it refuses and every path from the callee's
entry writes each of those registers before reading it, with no call, return or
cycle on the way; the call then is a call that receives no stack address, which
the walk does not inspect either.  Everything else keeps the walk's refusal,
and a proof that fails re-raises it unchanged.

When that entry proof refuses, `through_calls` tries once more (THROUGH_CALLS),
for a callee that hands the value to a callee of its own before writing it, or
whose path to the write passes a switch the value never reaches:

* a BL to an indexed Thumb function (the proof's own complete mapped span; no
  runtime, no call thunk) is followed into that callee's entry with the same
  rules, nested at most MAX_NESTING deep; the callee must write every live
  register before reading it on every path, so the call ends the path, and a
  return with one live refuses;
* both edges of every direct conditional branch are followed to a least
  fixpoint, except that a branch whose flags come from the CMP/CMN/TST right
  before it - its only predecessor on the surviving paths, so nothing between
  writes the flags - and whose operands are exact constants there is decided:
  only the taken edge (or only the fallthrough) is followed.  A constant is
  one the forward fixpoint computes from immediates through MOVS/MOV, ADDS,
  SUBS, NEGS, MVNS, shifts by an immediate and two-constant logic; a load (so
  any value from memory), any other write, and a join of two different
  values or of a value and an unknown leave the register unknown.  Signed and
  unsigned conditions are evaluated on the exact 32-bit flags;
* every surviving path must write the register before any read, call or
  return; it refuses on a memory read while a register is live, an indirect
  call, any PC write (a `mov pc` dispatch on a surviving edge too), an SWI and
  any 32-bit decode but a BL.

The record names each followed call (site, callee, depth, its body hash and
its killing writes) and each decided branch (site, condition, operands,
edge), and the report line states them under `thumb-dead-stack-register-calls-v1`;
a callee the entry proof admits keeps its version-1 record and line.
"""
import hashlib
from collections import namedtuple, defaultdict

from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB, CS_GRP_CALL, CS_GRP_INT, CS_GRP_JUMP, CS_GRP_RET
from capstone.arm import (ARM_CC_AL, ARM_CC_INVALID, ARM_INS_B, ARM_INS_BL, ARM_REG_PC, ARM_REG_R0,
                          ARM_OP_IMM, ARM_OP_REG, ARM_CC_EQ, ARM_CC_NE, ARM_CC_HS, ARM_CC_LO, ARM_CC_MI,
                          ARM_CC_PL, ARM_CC_VS, ARM_CC_VC, ARM_CC_HI, ARM_CC_LS, ARM_CC_GE, ARM_CC_LT,
                          ARM_CC_GT, ARM_CC_LE)

import armv4t

STATE_BUDGET = 4096
SCHEMA = 'thumb-dead-stack-register-v1'
CALLS_SCHEMA = 'thumb-dead-stack-register-calls-v1'
MAX_NESTING = 2
MASK = 0xFFFFFFFF
ARGUMENTS = frozenset(ARM_REG_R0 + n for n in range(4))

Liveness = namedtuple('Liveness', 'states kills visited')


def prove(start, registers, step, *, end, cycle, budget, limit=STATE_BUDGET):
    """Prove every path from ``start`` writes each register in ``registers`` before reading it.

    ``step(node, live)`` returns ``(written, successors)`` or raises ValueError.
    The result counts the proved states, lists every (node, register) killing
    write and the nodes in the order the walk visited them.  ``end``, ``cycle``
    and ``budget`` are the refusals for a path that ends with a live value, for
    a cycle that can avoid the killing write (least fixpoint) and for more than
    ``limit`` states.
    """
    first = (start, frozenset(registers))
    pending, transitions, safe, kills, visited = [first], {}, set(), set(), []
    while pending:
        state = pending.pop()
        if state in transitions or state in safe:
            continue
        node, live = state
        visited.append(node)
        written, successors = step(node, live)
        killed = live & frozenset(written)
        kills.update((node, register) for register in killed)
        following = live - killed
        if not following:
            safe.add(state)
            continue
        if not successors:
            raise ValueError(end)
        transitions[state] = [(target, following) for target in successors]
        pending.extend(transitions[state])
        if len(transitions) + len(safe) > limit:
            raise ValueError(budget)
    while True:
        added = {state for state, successors in transitions.items()
                 if state not in safe and all(target in safe for target in successors)}
        if not added:
            break
        safe.update(added)
    if first not in safe:
        raise ValueError(cycle)
    return Liveness(len(safe), kills, visited)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def decoder():
    thumb = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    thumb.detail = True
    return thumb


def decode(data, owner, address, thumb=None):
    """One ARMv4T Thumb instruction (or BL pair) decoded on its own at ``address``."""
    if address % 2 or not owner <= address < owner + len(data):
        raise ValueError('dead register walk leaves its function')
    thumb = thumb or decoder()
    item = next(thumb.disasm(data[address - owner:address - owner + 4], address), None)
    if item is None or item.address != address or not (armv4t.encoding(item) or armv4t.bl_pair(item)):
        raise ValueError('dead register walk meets an instruction outside ARMv4T Thumb')
    return item


def thumb_step(owner, data):
    """The default effect table over one complete Thumb function body.

    B follows its edges; a BL, every other control transfer, a write of PC and
    SWI refuse while a value is live; any other instruction refuses if it reads
    a live value and kills what it writes.
    """
    thumb = decoder()

    def step(current, live):
        item = decode(data, owner, current, thumb)
        if item.size == 4:
            raise ValueError('dead register reaches a call before its killing write')
        if item.id == ARM_INS_B:
            target = item.operands[0].imm
            return (), (target,) if item.cc in (ARM_CC_AL, ARM_CC_INVALID) else (target, current + 2)
        read, written = item.regs_access()
        if {CS_GRP_CALL, CS_GRP_INT, CS_GRP_JUMP, CS_GRP_RET} & set(item.groups) or ARM_REG_PC in written:
            raise ValueError('dead register reaches a return or an unresolved transfer before its killing write')
        if live & set(read):
            raise ValueError('dead register is read before its killing write')
        return written, (current + 2,)
    return step


class ThroughCalls:
    """The entry proof's retry through calls and constant branches; False keeps the entry proof alone."""
    enabled = True


THROUGH_CALLS = ThroughCalls()
FLAG_SETTERS = ('cmp', 'cmn', 'tst')


def _operand(op, constants):
    if op.type == ARM_OP_IMM:
        return op.imm & MASK
    if op.type == ARM_OP_REG and op.shift.type == 0:
        return constants.get(op.reg)
    return None


def constant_step(item, constants):
    """The constants after ``item``: exact 32-bit values for the forms below, unknown for every other write."""
    read, written = item.regs_access()
    ops = [op for op in item.operands]
    mnemonic = item.mnemonic
    value = None
    destination = ops[0].reg if ops and ops[0].type == ARM_OP_REG else None
    values = [_operand(op, constants) for op in ops]
    known = all(v is not None for v in values[1:])
    if destination is not None and destination != ARM_REG_PC and len(ops) >= 2 and known:
        a = values[1] if len(ops) == 2 else values[1]
        if mnemonic in ('movs', 'mov') and len(ops) == 2:
            value = values[1]
        elif mnemonic == 'mvns' and len(ops) == 2:
            value = ~values[1]
        elif mnemonic in ('negs', 'rsbs') and (len(ops) == 2 or (len(ops) == 3 and values[2] == 0)):
            value = -values[1]
        elif mnemonic in ('adds', 'subs', 'ands', 'orrs', 'eors', 'bics', 'muls'):
            if len(ops) == 2:
                left, right = constants.get(destination), values[1]
            else:
                left, right = values[1], values[2]
            if left is not None and right is not None:
                value = {'adds': lambda: left + right, 'subs': lambda: left - right, 'ands': lambda: left & right,
                         'orrs': lambda: left | right, 'eors': lambda: left ^ right,
                         'bics': lambda: left & ~right, 'muls': lambda: left * right}[mnemonic]()
        elif mnemonic in ('lsls', 'lsrs', 'asrs') and len(ops) == 3 and ops[2].type == ARM_OP_IMM:
            shift, source = ops[2].imm, values[1]
            if 0 <= shift <= 31 if mnemonic == 'lsls' else 1 <= shift <= 31:
                if mnemonic == 'lsls':
                    value = source << shift
                elif mnemonic == 'lsrs':
                    value = source >> shift
                else:
                    value = (source - (1 << 32) if source >> 31 else source) >> shift
    result = {register: v for register, v in constants.items() if register not in written}
    if value is not None:
        result[destination] = value & MASK
    return result


def _flags(item, constants):
    """(N, Z, C, V) of a CMP/CMN/TST over exact constants (C and V None for TST), or None."""
    if item.mnemonic not in FLAG_SETTERS or len(item.operands) != 2:
        return None
    a, b = (_operand(op, constants) for op in item.operands)
    if a is None or b is None:
        return None
    if item.mnemonic == 'cmp':
        result = (a - b) & MASK
        carry, overflow = a >= b, bool(((a ^ b) & (a ^ result)) >> 31)
    elif item.mnemonic == 'cmn':
        total = a + b
        result = total & MASK
        carry, overflow = total > MASK, bool((~(a ^ b) & (a ^ result) & MASK) >> 31)
    else:
        result, carry, overflow = a & b, None, None
    return bool(result >> 31), result == 0, carry, overflow


def condition_holds(condition, flags):
    """Whether a Thumb condition holds on exact flags; None when it needs a flag TST leaves unknown."""
    n, z, c, v = flags
    table = {ARM_CC_EQ: lambda: z, ARM_CC_NE: lambda: not z, ARM_CC_MI: lambda: n, ARM_CC_PL: lambda: not n,
             ARM_CC_HS: lambda: c, ARM_CC_LO: lambda: None if c is None else not c,
             ARM_CC_VS: lambda: v, ARM_CC_VC: lambda: None if v is None else not v,
             ARM_CC_HI: lambda: None if c is None else c and not z,
             ARM_CC_LS: lambda: None if c is None else (not c) or z,
             ARM_CC_GE: lambda: None if v is None else n == v, ARM_CC_LT: lambda: None if v is None else n != v,
             ARM_CC_GT: lambda: None if v is None else (not z) and n == v,
             ARM_CC_LE: lambda: None if v is None else z or n != v}
    if condition not in table:
        return None
    return table[condition]()


def _reads_memory(item):
    return item.mnemonic.startswith(('ldr', 'ldm')) or item.mnemonic == 'pop'


def through_calls(proof, target, registers, depth=0):
    """Every surviving path from ``target``'s entry writes each live register before any read, call or return.

    Returns (Liveness, followed, decided); raises ValueError otherwise.
    """
    import match
    if depth > MAX_NESTING:
        raise ValueError('dead register call nesting exceeds its bound')
    if target in match.RUNTIME_HELPERS.values():
        raise ValueError('dead register follows no call thunk')
    data = proof.span(target)
    thumb = decoder()
    items = {}

    def item_at(node):
        if node not in items:
            items[node] = decode(data, target, node, thumb)
        return items[node]

    nested = {}

    def follow(site, callee, live):
        key = (callee, live)
        if key not in nested:
            result, inner_followed, inner_decided = through_calls(proof, callee, live, depth + 1)
            nested[key] = dict(site=site, callee=callee, depth=depth + 1, body_sha256=sha(proof.span(callee)),
                               registers=sorted(register - ARM_REG_R0 for register in live),
                               kills=sorted([s, r - ARM_REG_R0] for s, r in result.kills),
                               followed=inner_followed, decided=inner_decided)
        return nested[key]

    def check(node, live):
        """The refusals of one instruction reached with ``live``; returns the item."""
        item = item_at(node)
        if item.size == 4:
            if item.id != ARM_INS_BL or not armv4t.bl_pair(item) or \
                    item.cc not in (ARM_CC_AL, ARM_CC_INVALID) or item.operands[0].type != ARM_OP_IMM:
                raise ValueError('dead register reaches a 32-bit instruction that is no BL')
            return item
        if item.id == ARM_INS_B:
            return item
        read, written = item.regs_access()
        if {CS_GRP_CALL, CS_GRP_INT, CS_GRP_JUMP, CS_GRP_RET} & set(item.groups) or ARM_REG_PC in written:
            raise ValueError('dead register reaches a return or an unresolved transfer before its killing write')
        if live & set(read):
            raise ValueError('dead register is read before its killing write')
        if _reads_memory(item):
            raise ValueError('dead register reaches a memory read before its killing write')
        return item

    # Phase 1: the surviving graph, with live registers (union) and constants (exact-or-unknown meet) per node.
    entry = target
    live_in = {entry: frozenset(registers)}
    constants_in = {entry: {}}
    predecessors = defaultdict(set)
    decided = {}
    pending = [entry]
    steps = 0
    while pending:
        node = pending.pop()
        steps += 1
        if steps > STATE_BUDGET:
            raise ValueError('dead register callee state budget exceeded')
        live, constants = live_in[node], constants_in[node]
        item = check(node, live)
        if item.size == 4:
            callee = item.operands[0].imm
            if target <= callee < target + len(data):
                raise ValueError('dead register follows no local BL')
            follow(node, callee, live)
            continue
        if item.id == ARM_INS_B:
            destination = item.operands[0].imm
            if item.cc in (ARM_CC_AL, ARM_CC_INVALID):
                successors = (destination,)
            else:
                successors = (destination, node + 2)
                previous = node - 2
                if predecessors[node] == {previous} and previous in items and \
                        items[previous].mnemonic in FLAG_SETTERS:
                    flags = _flags(items[previous], constants_in[previous])
                    holds = condition_holds(item.cc, flags) if flags is not None else None
                    if holds is not None:
                        successors = (destination,) if holds else (node + 2,)
                        decided[node] = dict(site=node, condition=item.mnemonic, flag_site=previous,
                                             operands=[_operand(op, constants_in[previous])
                                                       for op in items[previous].operands],
                                             edge='taken' if holds else 'fallthrough', successor=successors[0])
                    else:
                        decided.pop(node, None)
                else:
                    decided.pop(node, None)
            following, after = live, constants
        else:
            _, written = item.regs_access()
            following = live - frozenset(written)
            after = constant_step(item, constants)
            successors = (node + 2,) if following else ()
        if not following:
            continue
        for successor in successors:
            grew = node not in predecessors[successor]
            predecessors[successor].add(node)
            if successor not in live_in:
                live_in[successor], constants_in[successor] = following, dict(after)
                pending.append(successor)
                continue
            merged_live = live_in[successor] | following
            merged = {register: v for register, v in constants_in[successor].items() if after.get(register) == v}
            if grew or merged_live != live_in[successor] or merged != constants_in[successor]:
                live_in[successor], constants_in[successor] = merged_live, merged
                pending.append(successor)
    # Decisions made before a later predecessor arrived were revisited above; keep only the final ones.
    # Phase 2: the least fixpoint over the decided graph (every path writes each register before a read).
    calls_ended = {record['site'] for record in nested.values()}

    def step(node, live):
        item = check(node, live)
        if item.size == 4:
            if node not in calls_ended:
                raise ValueError('dead register reaches a call before its killing write')
            return tuple(live), ()
        if item.id == ARM_INS_B:
            if node in decided:
                return (), (decided[node]['successor'],)
            destination = item.operands[0].imm
            return (), (destination,) if item.cc in (ARM_CC_AL, ARM_CC_INVALID) else (destination, node + 2)
        _, written = item.regs_access()
        return written, (node + 2,)

    result = prove(entry, registers, step, end='dead register reaches the end of its callee',
                   cycle='dead register callee has a path without its killing write',
                   budget='dead register callee state budget exceeded')
    followed = sorted(nested.values(), key=lambda row: (row['site'], row['callee']))
    return result, [dict(row) for row in followed], [decided[site] for site in sorted(decided)]


class DeadStackRegisters:
    """The default stack-argument buffer proofs' dead-register call rule (one policy object).

    Created only by ``BufferCallProof(..., dead_registers=True)`` on the exact
    plain and function-literal proofs; every other proof has none and keeps
    every refusal.
    """

    def __init__(self, proof):
        self.proof = proof
        self.entries = {}
        self.calls = {}

    # ledger ----------------------------------------------------------------
    def snapshot(self):
        return dict(self.calls)

    def restore(self, saved):
        self.calls.clear()
        self.calls.update(saved)

    def observed(self):
        return bool(self.calls)

    # the walk --------------------------------------------------------------
    def entry(self, target, registers):
        """Every path from ``target``'s entry writes each register in ``registers`` before reading it.

        A call or a return reached with a live value refuses (the callee would
        hand it on), and so does a cycle that can avoid the killing write.  The
        record names the body and every killing write.
        """
        registers = frozenset(registers)
        key = (target, registers)
        if key not in self.entries:
            if not registers or registers - ARGUMENTS:
                raise ValueError('dead register entry proof covers R0-R3 only')
            data = self.proof.span(target)
            followed = decided = None
            try:
                result = prove(target, registers, thumb_step(target, data),
                               end='dead register reaches the end of its callee',
                               cycle='dead register callee has a path without its killing write',
                               budget='dead register callee state budget exceeded')
            except ValueError:
                if not THROUGH_CALLS.enabled:
                    raise
                result, followed, decided = through_calls(self.proof, target, registers)
                if not followed and not decided:
                    raise
            self.entries[key] = dict(address=target, end=target + len(data), body_sha256=sha(data),
                                     registers=sorted(register - ARM_REG_R0 for register in registers),
                                     states=result.states,
                                     kills=sorted([site, register - ARM_REG_R0] for site, register in result.kills))
            if followed is not None:
                self.entries[key].update(schema=CALLS_SCHEMA, followed=followed, decided=decided)
        return self.entries[key]

    # the refusal site ------------------------------------------------------
    def call(self, address, arguments, incoming, protected, context, saved):
        """After inspecting ``address`` refused: the record that makes it an alias-free call, or None."""
        if not arguments or set(arguments) - ARGUMENTS or incoming or protected or \
                context.get('words') or context.get('watched') or self.proof.resident_effect_replay(address) or \
                type(context.get('site')) is not int:
            return None
        try:
            entry = self.entry(address, arguments)
        except ValueError:
            return None
        self.proof._restore_ledgers(saved)
        site = context['site']
        record = dict(site=site, callee=address,
                      registers=sorted([register - ARM_REG_R0, offset] for register, offset in arguments.items()),
                      entry=entry)
        self.calls[(site, address, tuple(sorted(arguments.items())))] = record
        return record

    # evidence --------------------------------------------------------------
    def evidence(self):
        return dict(schema=SCHEMA, calls=[self.calls[key] for key in sorted(self.calls)])

    def lines(self):
        out = []
        for key in sorted(self.calls):
            row = self.calls[key]
            entry = row['entry']
            registers = ' '.join(f'r{register}={offset}' for register, offset in row['registers'])
            kills = ' '.join(f'r{register}@0x{site:08X}' for site, register in entry['kills'])
            if 'followed' in entry:
                out.append(f'* buffer dead register: `{CALLS_SCHEMA}` call 0x{row["site"]:08X} to '
                           f'0x{row["callee"]:08X} passes {registers}; on every surviving path from its entry '
                           f'({entry["states"]} states) the register is written before any read, call or return'
                           f'{kills and " (" + kills + ")"}; followed: {followed_text(entry["followed"])}; '
                           f'decided: {decided_text(entry["decided"])}; no memory read, indirect call, PC write '
                           f'or SWI while live, so it is not inspected, as a call that receives no stack address '
                           f'is not')
                continue
            out.append(f'* buffer dead register: `{SCHEMA}` call 0x{row["site"]:08X} to 0x{row["callee"]:08X} '
                       f'passes {registers}; the callee writes {kills} before any read on every path '
                       f'from its entry ({entry["states"]} states), so it is not inspected, as a call '
                       f'that receives no stack address is not')
        return out


def followed_text(rows):
    """Each followed call: site -> callee (depth, body hash prefix) with its kills and its own nests."""
    parts = []
    for row in rows:
        kills = ' '.join(f'r{register}@0x{site:08X}' for site, register in row['kills'])
        inner = ''
        if row['followed'] or row['decided']:
            inner = f' [followed: {followed_text(row["followed"])}; decided: {decided_text(row["decided"])}]'
        parts.append(f'BL 0x{row["site"]:08X} to 0x{row["callee"]:08X} (depth {row["depth"]}, '
                     f'{row["body_sha256"][:16]}) writes {kills or "nothing"}{inner}')
    return ', '.join(parts) or 'none'


def decided_text(rows):
    parts = []
    for row in rows:
        operands = ', '.join(f'0x{value:08X}' for value in row['operands'])
        parts.append(f'0x{row["site"]:08X} {row["condition"]} {row["edge"]} to 0x{row["successor"]:08X} '
                     f'(flags from 0x{row["flag_site"]:08X} on {operands})')
    return ', '.join(parts) or 'none'
