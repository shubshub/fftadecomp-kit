"""Counted stack-cursor loops: an exact pass-by-pass replay of a loop that walks its own frame.

The core walk keeps one merged state per instruction.  A loop that advances a
stack alias every pass (``mov r4, sp`` ... ``stm r4!, {r2}``) brings a
different live offset back to its head, and the join refuses: one offset
cannot describe every pass, and dropping the register would turn a frame
address into an unchecked scalar.  This rule keeps the offsets exact instead.

It applies only where that join refuses in the owner's own walk under a
loop-replaying stack-argument buffer proof (``applies``), whose report states
bounded loop replays and whose replays recheck them; never in a buffer callee's
walk, nor under an owner switch with its own local cursor; and only at the
first visit of a 16-bit conditional branch back to an earlier head whose two
edges disagree in exactly one live register.  The region [head, latch] is then
walked once per pass with states keyed by (instruction, pass):

* every instruction of every pass goes through the unchanged core transfer, so
  frame bounds, saved-register and return-address words, pointer-bearing
  words, escapes and calls are checked at their exact offsets;
* only the latch is decided, from the exact operands of the last CMP, tracked
  by ``loop_replay_transfer`` and evaluated by ``loop_replay_condition`` (the
  bounded replay of buffer callees).  As in that replay, a call forgets the
  R4-R11 values an inspected callee writes.  Pass 0 starts from the walk's
  exact constants at the head, without any value that may have crossed (or
  come out of) a call on a path into the loop.  An undecided latch, or a loop
  that has not exited after MAX_PASSES passes, refuses;
* the exit state is the last pass's state, joined normally after the loop.

After the walk (``CursorLoops.finish``) the region must be entered only at its
head and left only by the latch's fall-through, and contain no retreating
edge, return, local branch, multiway branch or stack adjustment.  Exactly one
register may differ between the head states of the passes: the cursor, which
moves by one constant nonzero stride, and every access whose offset changes
between passes lies inside the one run of allocated local words that holds the
cursor's first offset.  The records are bound in the buffer proof fingerprint
and each is stated in one ``* buffer loop replay`` report line, which names the
calls the loop crosses and the callee-saved registers the proof trusts them to
preserve (the ordinary ARM ABI call summary): the cursor and every R4-R11
register whose known value a pass carried across one of them.
"""
from capstone import CS_GRP_CALL
from capstone.arm import (ARM_CC_AL, ARM_CC_INVALID, ARM_INS_B, ARM_INS_CMP, ARM_OP_IMM,
                          ARM_OP_MEM, ARM_OP_REG, ARM_REG_R0, ARM_REG_R4, ARM_REG_R11, ARM_REG_R12)

SCHEMA = "counted-stack-cursor-loop-v1"
MAX_PASSES = 4096
WIDTHS = {"ldr": 4, "str": 4, "ldrh": 2, "strh": 2, "ldrb": 1, "strb": 1, "ldrsh": 2, "ldrsb": 1}
TRACKED = frozenset(range(ARM_REG_R0, ARM_REG_R12 + 1))
CALLEE_SAVED = frozenset(range(ARM_REG_R4, ARM_REG_R11 + 1))


class Policy:
    """The one switch that takes the rule off the default path."""
    enabled = True


POLICY = Policy()


def applies(thumb, buffer_proof, bounded_index):
    """Only owner walks under proofs whose reports carry ``loop_replay_lines`` and whose replays recheck them.

    A buffer callee's own walk (``buffer_proof.active`` names the callee being
    checked) keeps the join, so a record never comes from a callee check that a
    bounded loop replay may abort.  An owner switch whose walk keys its states
    by its own local cursor (``menu_local_cursor``) keeps that cursor alone.
    """
    return POLICY.enabled is True and thumb is True and bounded_index is None and \
        buffer_proof is not None and buffer_proof.stack_arguments is True and \
        buffer_proof.loop_replay_eligible() and not buffer_proof.active and \
        getattr(buffer_proof.owner_switch, "cursor", None) is None


def offset_text(offset):
    return f"entry_sp{offset:+d}"


def alias_accesses(instruction, aliases, constants):
    """(entry-SP offset, width) of each access the core made through a stack alias."""
    operands = instruction.operands
    accesses = []
    if instruction.mnemonic in ("stm", "ldm") and operands and operands[0].type == ARM_OP_REG and \
            operands[0].reg in aliases:
        accesses.append((aliases[operands[0].reg], 4 * (len(operands) - 1)))
    for operand in operands:
        if operand.type == ARM_OP_MEM and operand.mem.base in aliases:
            offset = aliases[operand.mem.base] + operand.mem.disp
            index = constants.get(operand.mem.index) if operand.mem.index else 0
            if WIDTHS.get(instruction.mnemonic) is None or type(index) is not int:
                raise ValueError("counted stack-cursor loop access is not an exact stack-alias access")
            accesses.append((offset + index, WIDTHS[instruction.mnemonic]))
    return accesses


class Loop:
    def __init__(self, head, latch, end, cursor):
        self.head, self.latch, self.end, self.cursor = head, latch, end, cursor

    def name(self):
        return f"counted stack-cursor loop 0x{self.head:08X}-0x{self.latch:08X}"


class CursorLoops:
    """The loops one owner ``verify_leaf_instructions`` walk replays pass by pass."""

    def __init__(self, transfer, condition, clobbers, address, instructions, edges):
        self.transfer, self.condition = transfer, condition
        # call target -> R4-R11 that inspected callee (or one it inspects) writes (BufferCallProof.callee_clobbers)
        self.clobbers = clobbers
        # the walk's entry and its instructions and edges so far (the live maps of verify_leaf_instructions)
        self.address, self.instructions, self.edges = address, instructions, edges
        self.loops = []
        # (instruction, pass) -> (known register values, CMP operands, CMP site) before it
        self.facts = {}
        # (call site, pass) -> R4-R11 whose known values that pass carried across the call
        self.carried = {}
        self.outgoing = None
        self.changed = False

    def loop_at(self, site):
        return next((loop for loop in self.loops if loop.head <= site < loop.end), None)

    def crossed(self, loop):
        """R0-R12 whose value may have crossed or come out of a call on a path into the loop's head.

        The walk's constants keep R4-R11 across every call on the ABI premise,
        even across an inspected callee that writes them.  A forward fixpoint
        over the walk's instructions and edges: a call taints every register, an
        instruction that reads a tainted register taints what it writes, and any
        other write clears it.  The back edge does not enter the head.
        """
        before, pending, entering = {self.address: frozenset()}, [self.address], frozenset()
        while pending:
            site = pending.pop()
            instruction, successors = self.instructions.get(site), self.edges.get(site)
            if instruction is None or successors is None:
                continue
            read, written = instruction.regs_access()
            taint = before[site]
            if CS_GRP_CALL in instruction.groups:
                after = TRACKED
            elif taint.intersection(read):
                after = taint | TRACKED.intersection(written)
            else:
                after = taint.difference(written)
            for successor in successors:
                if successor == loop.head and not loop.head <= site < loop.end:
                    entering |= after
                merged = before.get(successor, frozenset()) | after
                if before.get(successor) != merged:
                    before[successor] = merged
                    pending.append(successor)
        return entering

    def entry_facts(self, loop, state):
        """Pass 0's known values: the walk's exact constants at the head, less any that may have crossed a call."""
        crossed = self.crossed(loop)
        return (tuple((register, value) for register, value in state[3]
                      if type(register) is int and ARM_REG_R0 <= register <= ARM_REG_R12 and
                      register not in crossed and type(value) is int and 0 <= value <= 0xFFFFFFFF), None, None)

    def engage(self, instruction, current, successor, previous, outgoing, previous_aliases,
               incoming_aliases, revisit, states, pending):
        """Start replaying the loop whose back edge current -> successor the join refused."""
        operands = instruction.operands
        before = dict(previous_aliases)
        live = [register for register, offset in incoming_aliases
                if register in before and before[register] != offset]
        end = current + instruction.size
        if revisit or instruction.id != ARM_INS_B or instruction.size != 2 or \
                instruction.cc in (ARM_CC_AL, ARM_CC_INVALID) or len(operands) != 1 or \
                operands[0].type != ARM_OP_IMM or operands[0].imm != successor or \
                not successor < current or len(live) != 1 or \
                not ARM_REG_R0 <= live[0] <= ARM_REG_R12 or previous[4] != outgoing[4] or \
                previous[5] != outgoing[5] or len(previous[1]) != len(outgoing[1]) or \
                any(loop.head < end and successor < loop.end for loop in self.loops):
            return False
        # A split-join state (a tuple key that is not a plain one) inside the region would
        # not be replayed pass by pass: the join keeps its refusal.
        if any(isinstance(key, tuple) and type(key) is not tuple and successor <= key[0] < end
               for key in (*states, *pending)):
            return False
        loop = Loop(successor, current, end, live[0])
        self.loops.append(loop)
        # Region sites still queued from the merged first pass are walked again as pass 0.
        pending[:] = [item for item in pending if isinstance(item, tuple) or not successor <= item < end]
        key = (successor, 0)
        states[key] = previous
        self.facts[key] = self.entry_facts(loop, previous)
        pending.append(key)
        return True

    def step(self, key, instruction):
        """Record the facts after `instruction`, walked in pass-mode state `key` (None: merged)."""
        if key is None:
            self.outgoing = None
            return
        known, flags, site = self.facts[key]
        known, next_flags = self.transfer(instruction, dict(known), flags)
        operands = instruction.operands
        if CS_GRP_CALL in instruction.groups:
            # As in the callee replay: an inspected callee's own writes to R4-R11 are not trusted to be restored.
            target = operands[0].imm if operands and operands[0].type == ARM_OP_IMM else None
            dropped = self.clobbers.get(target, ()) if target is not None else CALLEE_SAVED
            known = tuple(item for item in known if item[0] not in dropped)
            self.carried[key] = frozenset(register for register, _ in known if register in CALLEE_SAVED)
        if instruction.id == ARM_INS_CMP and instruction.cc in (ARM_CC_AL, ARM_CC_INVALID) and \
                instruction.size == 2 and len(operands) == 2 and operands[0].type == ARM_OP_REG:
            site = instruction.address if next_flags is not None else None
        elif next_flags is None:
            site = None
        self.outgoing = (known, next_flags, site)

    def merge(self, key, facts):
        previous = self.facts.get(key)
        if previous is None:
            merged = facts
        else:
            known = dict(facts[0])
            same = previous[1:] == facts[1:]
            merged = (tuple((register, value) for register, value in previous[0]
                            if known.get(register) == value),
                      previous[1] if same else None, previous[2] if same else None)
        self.changed = merged != previous
        self.facts[key] = merged

    def route(self, current, key, successor, instruction):
        """The state key an edge reaches, or None for an edge the decided latch rules out."""
        if key is None:
            loop = self.loop_at(successor)
            if loop is None:
                return successor
            if successor != loop.head:
                raise ValueError(f"{loop.name()}: control flow enters the loop at 0x{successor:08X} "
                                 f"from 0x{current:08X}, below its head")
            return (successor, 0)
        loop, number = self.loop_at(current), key[1]
        facts = self.outgoing
        if current == loop.latch:
            if facts[1] is None:
                raise ValueError(f"{loop.name()}: the latch is not decided by known compare operands "
                                 f"in pass {number}")
            taken = self.condition(instruction.cc, facts[1])
            if successor == loop.head:
                if not taken:
                    return None
                if number + 1 >= MAX_PASSES:
                    raise ValueError(f"{loop.name()}: no exit within {MAX_PASSES} passes")
                target = (successor, number + 1)
            elif successor == loop.end:
                return None if taken else self.route(current, None, successor, instruction)
            else:
                raise ValueError(f"{loop.name()}: the latch has an unexpected successor")
        elif loop.head < successor < loop.end and successor > current:
            target = (successor, number)
        else:
            raise ValueError(f"{loop.name()}: edge 0x{current:08X} -> 0x{successor:08X} leaves the "
                             "loop or retreats inside it")
        self.merge(target, facts)
        return target

    def settle(self, key, merged):
        """Whether the facts at `key` changed; a head's first pass takes them from its joined entry."""
        if type(key) is not tuple:
            return False
        loop = self.loop_at(key[0])
        if key[1] == 0 and loop.head == key[0]:
            facts = self.entry_facts(loop, merged)
            changed = self.facts.get(key) != facts
            self.facts[key] = facts
            return changed
        return self.changed

    def finish(self, address, instructions, edges, states, local_branches, calls):
        return [self.check(loop, address, instructions, edges, states, local_branches, calls)
                for loop in sorted(self.loops, key=lambda loop: loop.head)]

    def check(self, loop, address, instructions, edges, states, local_branches, calls):
        def require(condition, message):
            if not condition:
                raise ValueError(f"{loop.name()}: {message}")

        region = sorted(site for site in instructions if loop.head <= site < loop.end)
        for site in region:
            targets = edges[site]
            if site == loop.latch:
                require(set(targets) == {loop.head, loop.end},
                        "the latch is not a branch to the head with the exit as fall-through")
                continue
            require(targets and len(targets) <= 2 and site not in local_branches and
                    all(site < target < loop.end for target in targets),
                    f"0x{site:08X} returns, branches out, retreats or dispatches inside the loop")
        outside = [site for site in instructions if site not in region]
        require(all(not loop.head < target < loop.end for site in outside for target in edges[site]) and
                any(target == loop.head for site in outside for target in edges[site]),
                "the loop is entered other than at its head")
        # An entry edge walked after pass 0 was seeded, without changing the head's state, is seen here.
        tainted = self.crossed(loop)
        entered = [register for register, _ in self.facts[(loop.head, 0)][0] if register in tainted]
        require(not entered, " ".join(f"r{register - ARM_REG_R0}" for register in entered) +
                " may have crossed a call on a path into the loop")
        passes = sorted(key[1] for key in states if type(key) is tuple and key[0] == loop.head)
        count = len(passes)
        require(passes == list(range(count)) and count and
                all((site, number) in states for site in region for number in range(count)),
                "a pass does not reach every instruction of the loop")
        heads = [states[(loop.head, number)] for number in range(count)]
        frame = heads[0][1]
        layout = [slot[1:] for slot in frame]
        require(all([slot[1:] for slot in states[(site, number)][1]] == layout
                    for site in region for number in range(count)),
                "the frame changes inside the loop")
        depth = len(frame)
        latches = [states[(loop.latch, number)] for number in range(count)]
        offsets = [dict(state[2]).get(loop.cursor) for state in heads + latches[-1:]]
        require(all(type(offset) is int for offset in offsets), "the cursor is not an exact alias every pass")
        start, stride = offsets[0], offsets[-1] - offsets[-2]
        require(stride != 0 and all(offset == start + stride * number for number, offset in enumerate(offsets)),
                "the cursor does not move by one constant stride")
        others = [(tuple(item for item in state[2] if item[0] != loop.cursor), state[4], state[5])
                  for state in heads]
        require(all(other == others[0] for other in others), "a second register or a pointer word "
                "changes between passes")
        decisions, compare = [], None
        for number in range(count):
            _, flags, site = self.facts[(loop.latch, number)]
            require(flags is not None and site is not None and (compare is None or site == compare),
                    f"the latch is not decided by one compare in pass {number}")
            compare = site
            require(self.condition(instructions[loop.latch].cc, flags) == (number < count - 1),
                    f"the latch decision in pass {number} differs from the replay")
            decisions.append(flags)
        moving = {}
        for site in region:
            seen = [frozenset(alias_accesses(instructions[site], dict(states[(site, number)][2]),
                                             dict(states[(site, number)][3])))
                    for number in range(count)]
            if len(set(seen)) > 1:
                moving[site] = set().union(*seen)
        accesses = sorted(access for items in moving.values() for access in items)
        bounds = None
        if accesses:
            slot = (accesses[0][0] + 4 * depth) // 4
            require(0 <= slot < depth and frame[slot][2], "a cursor access is outside the allocated local words")
            low = high = slot
            while low > 0 and frame[low - 1][2]:
                low -= 1
            while high + 1 < depth and frame[high + 1][2]:
                high += 1
            bounds = [-4 * depth + 4 * low, -4 * depth + 4 * (high + 1)]
            require(all(bounds[0] <= offset and offset + width <= bounds[1] for offset, width in accesses),
                    "a cursor access leaves the allocated local words that hold its lowest access")
        crossed = [[site, calls[site]] for site in region if CS_GRP_CALL in instructions[site].groups]
        # The cursor and every R4-R11 value a pass carried across a call (the callee replay's trusted facts).
        carried = {loop.cursor}.union(*(self.carried[(site, number)] for site, _ in crossed for number in range(count)))
        operands = instructions[compare].operands
        limit = operands[1].reg if operands[1].type == ARM_OP_REG else None
        return dict(
            function=address, head=loop.head, latch=loop.latch, cursor=loop.cursor - ARM_REG_R0,
            start=start, stride=stride, passes=count, exit=offsets[-1],
            branch=instructions[loop.latch].mnemonic, compare=compare,
            counter=operands[0].reg - ARM_REG_R0, limit=None if limit is None else limit - ARM_REG_R0,
            values=[[flags[0], flags[1]] for flags in decisions], object=bounds,
            accessed=[accesses[0][0], max(offset + width for offset, width in accesses)] if accesses else None,
            calls=crossed,
            trusted=[register - ARM_REG_R0 for register in sorted(carried) if crossed and register in CALLEE_SAVED])


def report_line(record):
    """The one report line that states a counted stack-cursor loop record."""
    cursor, counter = f"r{record['cursor']}", f"r{record['counter']}"
    stride, values = record["stride"], record["values"]
    limits = f"{values[0][1]}" if len({value[1] for value in values}) == 1 else f"{values[0][1]}..{values[-1][1]}"
    right = f"#{limits}" if record["limit"] is None else f"r{record['limit']} (= {limits})"
    accessed, bounds = record["accessed"], record["object"]
    calls = " ".join(f"0x{site:08X}:0x{target:08X}" for site, target in record["calls"])
    trusted = " ".join(f"r{register}" for register in record["trusted"]) or "none"
    return (f"* buffer loop replay: `{SCHEMA}` function 0x{record['function']:08X} "
            f"head 0x{record['head']:08X} latch 0x{record['latch']:08X}: "
            f"{cursor} = {offset_text(record['start'])} {'+' if stride > 0 else '-'} {abs(stride)}*pass, "
            f"{record['passes']} passes; latch {record['branch']} on cmp {counter}, {right} at "
            f"0x{record['compare']:08X} with {counter} = {values[0][0]}..{values[-1][0]}; "
            + ("cursor accesses none; " if accessed is None else
               f"cursor accesses [{offset_text(accessed[0])}, {offset_text(accessed[1])}) inside allocated locals "
               f"[{offset_text(bounds[0])}, {offset_text(bounds[1])}); ") +
            f"exit {cursor} = {offset_text(record['exit'])}; " +
            (f"calls {calls}, trusted to preserve {trusted}" if calls else "calls none"))
