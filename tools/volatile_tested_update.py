"""Tested constant-update re-reads for the allowlisted volatile semantic check.

`if (sym.x < 16) sym.x++; else if (sym.y != 0) sym.y--;` reads each volatile
member twice in the source: once for the test, once for the update.  With
the qualifier agbcc performs both reads; without it the update reuses the
tested value.  The stripped compile therefore has one load of the member
where the real compile has two, and volatile_semantics refuses the second
as "the qualifier added a read" (0x0812BA08 and 0x080BA8E4 at
g_control_flags_03000940 +0x4C and +0x4D):

    real                         stripped
    ldrb  r0, [r2]               ldrb  r0, [r1]
    cmp   r0, #15                cmp   r0, #15
    bhi   .L18                   bhi   .L18
    ldrb  r0, [r2]               add   r0, r0, #1
    add   r0, r0, #1             strb  r0, [r1]
    ldrb  r1, [r2]
    strb  r0, [r2]

Two reads of a volatile member are observable, so the rule admits the second
one only as the update's own read: a read the source needs, whose value
leaves the function only through the one store the update makes.  Both reads
are in the real compile, which the match makes byte-identical to the ROM, so
the ROM performs both, and the source must have had both.

A load is a tested update re-read when, on the path being checked (each of
obligations 1-6 refuses by returning False in tested_update_reread, which
leaves the load a counterpart and keeps main's "the qualifier added a read"):

1. it is an unsigned load of a pinned member at the member's width, not
   forwarded from a store;
2. the nearest earlier record that is not a register operation, a literal
   load or a branch is the tested read: a load of the same address and width,
   unsigned, with the same executor value.  No memory access, call, push,
   pop or summarised loop lies between the two, and the equal values show
   that the executor saw no write that could reach the member;
3. a conditional branch between them reads flags set by a comparison
   (`cmp`, `cmn`, `tst`) of the tested read's value or of an unchanged copy
   of it, or by such a copy itself (the test); flags of a value computed from
   it (`lsl r3, r0, #24; bmi`) are no test;
4. the re-read's value, through unchanged copies, feeds exactly one `add` or
   `sub` of an immediate that is not zero at the member's width (the update);
   no other operation reads it or the update's result before the store;
5. before the store, the only other records are register operations that
   neither read nor overwrite those values, literal loads, unconditional
   branches and exactly one load: the store's own read-modify-write load,
   dead and explained by read_modify_write_store; the store has the
   re-read's address and width, its value register holds the update's result
   and its address registers hold neither value, and every consumer feeds
   the stored value;
6. after the store, neither value nor the flags the update set reaches a use
   on the path;
7. the stripped compile has no load for it: compare_function first pairs the
   counterparts without the rule (volatile_semantics.paired_counterparts, the
   forwarded re-reads optional).  Only where that fails does it pair again
   with the candidates optional too, and a candidate left unpaired is a
   tested update re-read.  A pair agrees in width, signedness, address,
   executor value and the observable events before it (kit#378), so both
   loads of a pair are the same read, and a test read from before a write
   cannot stand in for a load after it.  One tie-break for every optional
   entry: it is skipped wherever the rest still pairs up.  A function that
   passes without the rule keeps its verdict and its record, and one that no
   skip can pair up keeps that refusal and its message.  Not under a caller's
   own trace pairing (the overwritten-store composition, whose record would
   not print the premise): there no load is a candidate.

The equal values in (2) say that, in ordinary memory, the re-read returns the
tested value, so the stripped compile's reuse of it computes the same update.
The per-path comparison still checks all of that: the stores, calls and
conditions must be the stripped compile's, and every other load of the object
must be its counterpart.  The layout-perturbed compile must follow both reads.
The rule needs Policy.premise, printed in every report record that applies it.
"""

import volatile_semantics as semantics

NAME = "tested-update-reread-v1"


class Policy:
    """the one switch a maintainer needs: enabled = False restores main's refusal"""

    name = NAME
    enabled = True
    premise = ("nothing writes the member between its update re-read and the read of it just "
               "before, which the branch tests (no interrupt, DMA or other asynchronous write), so "
               "in ordinary memory the stripped compile's reuse of the tested value computes the "
               "same update")


POLICY = Policy()


class Rereads(list):
    """the instructions this rule explained in one function, as compare_function returns them"""


def update_step(step, tracked, width):
    """`add`/`sub` of a tracked register and an immediate that changes a width-byte value"""
    if step.alu_operation not in ("add", "sub") or step.copy or len(step.alu_sources) != 2:
        return False
    (source, _), (immediate_register, amount) = step.alu_sources
    return source in tracked and step.reads == {source} and immediate_register is None and \
        type(amount) is int and amount % (1 << (8 * width)) != 0


def tested_update_reread(records, position, pinned_width):
    """is the load at position the update read of a tested pinned member? (obligations 1-6)"""
    if not POLICY.enabled:
        return False
    load = records[position]
    # 1. an unsigned exact-width read of a pinned member, not forwarded
    if load.kind != "load" or load.signed or load.forwarded or len(load.writes) != 1 or \
            load.width != pinned_width(load.address):
        return False
    # 2. the tested read, with only register operations and branches between
    earlier = position - 1
    while earlier >= 0 and records[earlier].kind in ("alu", "literal", "branch"):
        earlier -= 1
    if earlier < 0:
        return False
    tested = records[earlier]
    if tested.kind != "load" or tested.signed or tested.address != load.address or \
            tested.width != load.width or tested.value != load.value:
        return False
    # 3. a conditional branch decides on the tested value
    values, flags, decided = set(tested.writes), False, False
    for step in records[earlier + 1:position]:
        if step.kind == "branch" and not step.unconditional and flags:
            decided = True
        uses = step.reads & values
        copied = step.copy and step.reads <= values      # a copy reads one register or a zero
        if step.flags_written:
            # cmp/cmn/tst write no register; a flag-setting `movs`/`adds #0` is a copy
            flags = bool(uses) and (not step.writes or copied)
        values -= step.writes
        if copied:
            values |= step.writes
    if not decided:
        return False
    # 4.-6. one constant update, stored back to the member, and nothing else
    tracked, consumers, between = set(load.writes), set(), []
    updated, stored, flags_live, insertions = False, False, False, 0
    for here in range(position + 1, len(records)):
        step = records[here]
        uses = step.reads & tracked
        if step.kind == "branch" and not step.unconditional and flags_live:
            return False
        if stored:
            if uses:
                return False
        elif step.kind == "store":
            if not updated or insertions != 1 or step.address != load.address or \
                    step.width != load.width or step.value_register not in tracked or \
                    (step.reads - {step.value_register}) & tracked:
                return False
            live, feeding = {step.value_register}, set()
            for dependency in reversed(between):
                if dependency.writes & live:
                    feeding.add(dependency.index)
                    live = (live - dependency.writes) | dependency.reads
            if not consumers <= feeding:
                return False
            stored = True
        elif step.kind == "load":
            if step.address != load.address or step.width != load.width or step.signed or \
                    uses or step.writes & tracked or insertions:
                return False
            if semantics.dead(records, here, next(iter(step.writes)), set()) is not True or \
                    semantics.read_modify_write_store(records, here, load.address, load.width) is None:
                return False
            insertions += 1
        elif step.kind == "branch":
            if not step.unconditional:
                return False
        elif step.kind not in ("alu", "literal"):
            return False
        elif uses:
            if step.copy and step.reads <= tracked:
                pass
            elif not updated and update_step(step, tracked, load.width):
                updated = True
            else:
                return False
            consumers.add(step.index)
        elif step.writes & tracked:
            return False
        if step.flags_written:
            flags_live = bool(uses)
        tracked -= step.writes
        if uses and not stored:
            tracked |= step.writes
        if not stored:
            between.append(step)
    return stored
