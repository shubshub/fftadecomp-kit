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
"""
import hashlib
from collections import namedtuple

from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB, CS_GRP_CALL, CS_GRP_INT, CS_GRP_JUMP, CS_GRP_RET
from capstone.arm import ARM_CC_AL, ARM_CC_INVALID, ARM_INS_B, ARM_REG_PC, ARM_REG_R0

import armv4t

STATE_BUDGET = 4096
SCHEMA = 'thumb-dead-stack-register-v1'
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
            result = prove(target, registers, thumb_step(target, data),
                           end='dead register reaches the end of its callee',
                           cycle='dead register callee has a path without its killing write',
                           budget='dead register callee state budget exceeded')
            self.entries[key] = dict(address=target, end=target + len(data), body_sha256=sha(data),
                                     registers=sorted(register - ARM_REG_R0 for register in registers),
                                     states=result.states,
                                     kills=sorted([site, register - ARM_REG_R0] for site, register in result.kills))
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
            out.append(f'* buffer dead register: `{SCHEMA}` call 0x{row["site"]:08X} to 0x{row["callee"]:08X} '
                       f'passes {registers}; the callee writes {kills} before any read on every path '
                       f'from its entry ({entry["states"]} states), so it is not inspected, as a call '
                       f'that receives no stack address is not')
        return out
