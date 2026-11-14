"""Live private-local aliases across ordinary calls in scheduler compositions.

The default scheduler branch profiles refuse every tracked local alias at an
ordinary call. This explicit profile admits two cases and nothing else:

* An alias in a callee-saved register (R4-R11) that is not an argument. It
  survives by the ARM ABI premise the kit already uses for all returning calls.
  The complete callee CFG (ARMv4T-decoded) is also walked per path: while a
  register still holds the alias, the only instruction that may read it is a
  push; the saved copy may only be popped back into the same register, is never
  loaded through SP, and cannot be reached through a copy of SP; every return
  must hold the alias again with the walked stack empty. A direct call made
  while the alias is still held is walked the same way; an indirect call, thunk
  or runtime helper reached while it is held is refused. A nested call made
  while only the saved copy is on the stack is not walked (stated premise).
* An alias passed in R0-R3 or R12. The callee body is replayed by the existing
  buffer-call machinery, which bounds every access to private local words,
  refuses stores, spills, pushes and returns of the pointer, and refuses pointer
  slots. This profile additionally refuses a returned alias, a thunk or runtime
  helper reached during the replay, and any access below the lowest local alias
  held in R0-R3 or R12 at the call. The ROM carries no per-local sizes, so the
  upper bound of the extent is the private frame itself.

The scheduler call keeps its descriptor contract unchanged.

Only under entry_liveness (selected by conditional-scheduler-three-per-path-
live-alias-v1) an alias in R0-R3 or R12 that the complete callee overwrites on
every path before reading it, calling or returning is not an argument, and a
passed alias that a closed leaf callee never writes, and so returns unchanged,
is handed back to the caller as a tracked alias, as the ordinary buffer
verifier does, instead of being refused. Any other returned alias is refused.
"""
import hashlib
from pathlib import Path

import match
import owner_graph_profile as graph

PREMISE = ('Values held in callee-saved registers R4-R11 survive every ordinary call by the ARM ABI '
           'premise used for all returning calls. Each callee reached while such a register holds a '
           'local alias is walked over its complete CFG, per path: the register is read only by push '
           'while it holds the alias and holds it again at every return, and a nested direct call made '
           'while it holds the alias is walked the same way; an indirect call, thunk or runtime helper '
           'reached then is refused. Instructions are decoded as ARMv4T Thumb. A saved alias is popped '
           'only back into its own register and never loaded through SP; while one is on the stack SP '
           'is read only by push, pop, an immediate or sole-predecessor literal SP adjustment, or an '
           'immediate SP-based load or store, and a held register is not saved after SP was copied '
           '(here or in a walked caller), so no frame pointer can reach the save slot. Slots allocated '
           'by an SP adjustment are stale until stored to and cannot be loaded or popped; only pop may '
           'release a saved alias slot; every return leaves the walked stack empty. A walked nested '
           'callee sees the walked caller frames above its entry SP and may not load or overwrite a '
           'saved alias there. A nested call made while only a saved copy is on the stack (the '
           'register itself already overwritten) is not walked; its target and body digest are recorded '
           'as unwalked_nested_targets, and that it does not read the caller save slot above its own '
           'entry SP rests on the ABI premise. A callee that receives '
           'an alias in R0-R3 or R12 is replayed: every access is bounded to private local words at or '
           'above the lowest local alias held in R0-R3 or R12 at the call, whether or not the callee '
           'uses that register as an argument, so a stale alias lowers the bound; the pointer is not '
           'stored, pushed, spilled or returned, and no thunk or runtime helper is reached. Callee '
           'effects on the aliased words and nested execution remain unproved.')
# Explicit opt-in refinement (conditional-scheduler-three-per-path-live-alias-v1 only).
ENTRY_LIVENESS_PREMISE = ('A local alias in R0-R3 or R12 that the complete callee CFG (ARMv4T-decoded) '
           'overwrites on every path before any read of that register, any call, any software interrupt '
           'and any return is dead '
           'at callee entry: it is not an argument, is not replayed and does not bound the replay, and '
           'is recorded as dead_at_entry_aliases. A passed alias in R0-R3 or R12 that a closed leaf '
           'callee (no call, no software interrupt) never writes is returned unchanged on every path '
           'and is handed back to the caller as the ordinary buffer verifier does: the caller keeps '
           'tracking the register as a local alias, so a later read, store, spill, call '
           'argument or return of it is checked like any other alias; it is recorded as '
           'returned_aliases. No other part of the live-alias contract changes.')
# Bounds on the per-path preserved-register walk.
MAX_NESTING, MAX_STATES = 4, 4096


def require(condition, message):
    if not condition:
        raise ValueError(message)


def _order(register):
    # PUSH/POP lists use ascending architectural numbers: R0-R12, then LR, then PC.
    if match.ARM_REG_R0 <= register <= match.ARM_REG_R0+12:
        return register - match.ARM_REG_R0
    return {match.ARM_REG_LR: 14, match.ARM_REG_PC: 15}[register]


# A slot allocated by an SP adjustment and not yet stored to: its old contents are not the callee's.
STALE = 'stale'


def _body_sha256(proof, address):
    # Identity only: read through the unbudgeted base span, so naming a body costs no dependency slot.
    try:
        return hashlib.sha256(match.BufferCallProof.span(proof, address)).hexdigest()
    except ValueError:
        return None


def check_preserved(proof, address, registers, chain=(), outer=(), copied_in=False):
    """Walk every path of a complete callee holding caller aliases in `registers`.

    A register holds the alias until written; it may be pushed but not otherwise
    read while it holds it, and must hold it again at every return. Stack slots
    remember which pushed register value they carry: a saved alias may be popped
    only back into its own register and never loaded through SP, and while one is
    on the stack SP may be read only by push, pop, an immediate or authenticated
    literal SP adjustment, or an immediate SP-based load/store. A held register
    may not be saved after SP has been copied on that path (or in a walked
    caller), and every return leaves the walked stack empty. Slots allocated by an
    SP adjustment are stale until stored to: they cannot be loaded or popped, and
    an SP release may not drop a saved alias. A nested walk sees its callers'
    walked frames as `outer`: it may not load or overwrite a saved alias there.
    Returns the targets walked and the direct targets called while only a saved
    copy was live (not walked).
    """
    import owner_admission_profile as owner
    import callee_preservation_profile as preservation
    from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
    require(len(chain) < MAX_NESTING and address not in chain,
            'live-alias preserved-register walk is recursive or too deeply nested')
    require(not match.function_thunk.reserved(address) and address not in match.RUNTIME_HELPERS.values(),
            'live-alias preserved register reaches a thunk or runtime helper')
    data = proof.span(address)
    if address not in proof.dependencies:
        proof.dependencies[address] = data
        proof.records[address] = dict(address=address, end=address+len(data), bytes=len(data),
            body_sha256=hashlib.sha256(data).hexdigest(), **proof.identities,
            structure=dict(kind='complete-indexed-body-preserved-register-walk',
                callee_effects_proved=False, nested_execution_proved=False))
    instructions, edges, branches, calls, _ = graph.graph(data, address, owner.refine(data, address, proof.mapping))
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    for site, instruction in instructions.items():
        require(preservation._decode(decoder, proof.rom, site, address, address+len(data)).id == instruction.id,
                'live-alias walk decoding differs from the ARMv4T decoder')
    predecessors = {}
    for site, successors in edges.items():
        for successor in successors:
            predecessors.setdefault(successor, set()).add(site)
    walked, unwalked = {address}, set()
    start = (address, frozenset(registers), (), copied_in)
    seen, pending = {start}, [start]
    while pending:
        site, held, stack, copied = pending.pop()
        instruction = instructions[site]
        operands = [o.reg for o in instruction.operands if o.type == match.ARM_OP_REG]
        read, written = instruction.regs_access()
        mnemonic = instruction.mnemonic
        require(site not in branches, 'live-alias preserved-register walk excludes local BL')
        saved = any(token not in (None, STALE) for token in stack + outer)
        memory = [o for o in instruction.operands if o.type == match.ARM_OP_MEM and o.mem.base == match.ARM_REG_SP]
        adjustment = None
        if mnemonic not in ('push', 'pop'):
            adjustment = match.thumb_stack_adjustment(instruction)
            if adjustment is None:
                adjustment = match.thumb_literal_stack_adjustment(instruction, data, address)
                if adjustment is not None:
                    # The helper's precondition: its literal LDR is the ADD's sole CFG predecessor.
                    require(predecessors.get(site) == {site-2} and edges.get(site-2) == (site,),
                            'live-alias callee literal SP adjustment lacks its sole literal load')
        immediate = bool(memory) and not memory[0].mem.index and mnemonic[:3] in ('ldr', 'str')
        if match.ARM_REG_SP in read and mnemonic not in ('push', 'pop') and adjustment is None and not immediate:
            require(not saved, 'live-alias callee copies SP while a saved alias is on the stack')
            copied = True
        if mnemonic == 'push':
            pushed = sorted(operands, key=_order)
            require(not copied or not held & set(pushed),
                    'live-alias callee saves a preserved alias after copying SP')
            stack = tuple(r if r in held else None for r in pushed) + stack
        else:
            require(not set(read) & held,
                    'live-alias callee reads a preserved alias register other than to save it')
        if mnemonic == 'pop':
            popped = sorted(operands, key=_order)
            require(len(popped) <= len(stack), 'live-alias callee pops above its entry stack')
            for register, token in zip(popped, stack):
                require(token != STALE, 'live-alias callee pops an unwritten stack slot')
                require(token is None or token == register,
                        'live-alias callee pops a saved alias into another register')
                held = held | {register} if token == register and register in registers else held - {register}
            stack = stack[len(popped):]
        elif adjustment is not None:
            require(adjustment <= len(stack), 'live-alias callee releases stack above its entry')
            require(adjustment < 0 or not any(t not in (None, STALE) for t in stack[:adjustment]),
                    'live-alias callee releases a saved alias slot without popping it')
            stack = (STALE,)*-adjustment + stack if adjustment < 0 else stack[adjustment:]
        elif mnemonic != 'push':
            require(match.ARM_REG_SP not in written,
                    'live-alias callee has an untracked stack pointer write')
            held = held - set(written)
            if immediate:
                width = 1 if mnemonic.endswith('b') else 2 if mnemonic.endswith('h') else 4
                first, last = memory[0].mem.disp // 4, (memory[0].mem.disp + width - 1) // 4
                view = stack + outer
                slots = range(first, min(last+1, len(view)))
                if mnemonic.startswith('ldr'):
                    # A saved alias, including one in a walked caller frame, and a stale slot are both refused.
                    require(not any(view[slot] == STALE for slot in slots),
                            'live-alias callee loads an unwritten stack slot')
                    require(not any(view[slot] is not None for slot in slots),
                            'live-alias callee loads a saved alias through SP')
                else:
                    # A store into a callee stack slot destroys any saved value there.
                    require(not any(view[slot] not in (None, STALE) for slot in slots if slot >= len(stack)),
                            'live-alias nested callee overwrites a caller save slot')
                    stack = tuple(None if slot in slots else token for slot, token in enumerate(stack))
        if site in calls and held:
            nested, nested_unwalked = check_preserved(proof, calls[site], held, chain + (address,), stack + outer, copied)
            walked |= nested
            unwalked |= nested_unwalked
        elif site in calls and saved:
            # Only a saved copy is live here; the callee is not walked and rests on the ABI premise.
            unwalked.add(calls[site])
        if not edges[site]:
            require(held >= set(registers),
                    'live-alias callee returns without restoring a preserved alias register')
            require(not stack, 'live-alias callee returns with an unbalanced stack')
        for successor in edges[site]:
            state = (successor, held, stack, copied)
            if state not in seen:
                require(len(seen) < MAX_STATES, 'live-alias preserved-register walk state budget exhausted')
                seen.add(state)
                pending.append(state)
    return walked, unwalked


def _callee_cfg(proof, address):
    """The complete ARMv4T-checked callee CFG, or None when it is not closed."""
    import owner_admission_profile as owner
    import callee_preservation_profile as preservation
    from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
    data = proof.span(address)
    try:
        instructions, edges, branches, calls, _ = graph.graph(data, address, owner.refine(data, address, proof.mapping))
    except ValueError:
        return None
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    for site, instruction in instructions.items():
        require(preservation._decode(decoder, proof.rom, site, address, address+len(data)).id == instruction.id,
                'live-alias entry liveness decoding differs from the ARMv4T decoder')
    return instructions, edges, branches, calls


def unchanged_leaf_registers(proof, address, registers):
    """Registers a closed callee with no call, no software interrupt and no write to them returns unchanged."""
    cfg = _callee_cfg(proof, address)
    if cfg is None:
        return set()
    instructions, _, branches, calls = cfg
    if calls or branches or any(match.CS_GRP_INT in i.groups for i in instructions.values()):
        return set()
    written = {r for i in instructions.values() for r in i.regs_access()[1]}
    return set(registers) - written


def dead_at_entry(proof, address, registers):
    """Registers the complete callee overwrites on every path before any observation.

    An instruction that reads the register, any call (BL, local or not), any
    software interrupt and any return observe it; an unconditional write kills it. A cycle that never
    kills it is not a proof (least fixpoint).
    """
    if not registers:
        return set()
    cfg = _callee_cfg(proof, address)
    if cfg is None:
        # No closed CFG, no liveness fact: every alias stays an argument.
        return set()
    instructions, edges, branches, calls = cfg
    dead = set()
    for register in registers:
        safe = set()
        while True:
            added = False
            for site, instruction in instructions.items():
                if site in safe:
                    continue
                read, written = instruction.regs_access()
                # A software interrupt reads its BIOS arguments without naming them.
                if register in read or site in calls or site in branches or \
                        match.CS_GRP_INT in instruction.groups:
                    continue
                if register in written or (edges[site] and all(t in safe for t in edges[site])):
                    safe.add(site)
                    added = True
            if not added:
                break
        if address in safe:
            dead.add(register)
    return dead


def check_call(proof, address, aliases, stack, slots, *, constants=None, site=None, words=None,
               entry_liveness=False):
    require(address in proof.branch_calls['ordinary_targets'],
            'live-alias call requires an indexed ordinary target')
    require(not slots and not words,
            'live-alias calls exclude pointer-bearing slots and word provenance')
    require(type(entry_liveness) is bool, 'entry-liveness selection must be Boolean')
    passed = {r: o for r, o in aliases.items() if r in match.CALLER_CLOBBERED}
    dead = {}
    if entry_liveness:
        killed = dead_at_entry(proof, address, set(passed) - {match.ARM_REG_LR})
        dead = {r: o for r, o in passed.items() if r in killed}
        passed = {r: o for r, o in passed.items() if r not in killed}
    preserved = {r: o for r, o in aliases.items() if r not in match.CALLER_CLOBBERED}
    require(match.ARM_REG_LR not in passed, 'live-alias calls cannot pass a pointer in the link register')
    for offset in aliases.values():
        proof.access(offset, 1, stack)
    observation = dict(site=site, target=address, kind='conditional-ordinary-ABI-call')
    if aliases:
        observation = dict(site=site, target=address, kind='live-local-alias-ordinary-call',
            passed_aliases=sorted(passed.items()), preserved_aliases=sorted(preserved.items()))
        if entry_liveness:
            observation['dead_at_entry_aliases'] = sorted(dead.items())
    if preserved:
        walked, unwalked = check_preserved(proof, address, preserved)
        observation.update(preserved_register_reads='push-only', preserved_register_restore='every-return',
            preserved_walk_targets=sorted(walked),
            unwalked_nested_targets=[[target, _body_sha256(proof, target)] for target in sorted(unwalked)])
    if passed:
        log = dict(access=[], calls=[])
        proof._live_log = log
        try:
            returned = proof.check_arguments(address, passed, stack, {}, frozenset(),
                constants=proof.argument_constants(constants or {}), site=site)
        finally:
            proof._live_log = None
        # Only a definite, unchanged alias is handed back: the callee is a closed leaf
        # that never writes the register, so every return holds the passed value.
        handed = dict(returned) if entry_liveness else {}
        require(not handed or (set(handed) <= unchanged_leaf_registers(proof, address, set(handed)) and
                               all(passed.get(r) == o for r, o in handed.items())),
                'live-alias callee cannot return a local alias')
        require(entry_liveness or not returned, 'live-alias callee cannot return a local alias')
        reached = set(log['calls'])
        require(not any(match.function_thunk.reserved(a) or a in match.RUNTIME_HELPERS.values()
                        for a in reached | {address}),
                'live-alias callee cannot reach a thunk or runtime helper')
        lowest = min(passed.values())
        require(all(offset >= lowest and offset+width <= 0 for offset, width in log['access']),
                'live-alias callee accesses private words below its lowest passed alias')
        observation.update(access_lowest=min((o for o, _ in log['access']), default=None),
            access_end=max((o+w for o, w in log['access']), default=None),
            nested_dependencies=sorted(reached - {address}))
        if entry_liveness:
            observation['returned_aliases'] = sorted(dict(returned).items())
    if aliases:
        observation.update(premise=PREMISE,
            source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
        if entry_liveness:
            observation['entry_liveness_premise'] = ENTRY_LIVENESS_PREMISE
    require(site not in proof.observations or proof.observations[site] == observation,
            'live-alias call differs across incoming paths')
    proof.observations[site] = observation
    return returned if passed and entry_liveness else {}
