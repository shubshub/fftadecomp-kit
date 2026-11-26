"""Closure slots on the default Thumb path, retried after the plain walk refuses (rule CF).

A closure is a small struct in the owner's own frame that holds the address of one of the owner's
locals and a function pointer, handed by address to a list walker that calls back through it:

    closure.argument = &found;  closure.callback = func_0809AC88;
    func_080C7CC0(list, func_0809ABE8, &closure);   /* 0809ABE8 loads both words, calls back */

The default buffer walks (`match.BufferCallProof` with stack arguments and exact call-via targets:
the plain path, the plain and function-literal data-buffer proofs and the function-buffer proof)
admit the owner's store of a frame address into its own frame word as a pointer-bearing slot, and
refuse any callee's load of that word:

    buffer access overlaps a pointer-bearing argument slot

That is the only trigger.  After it, and only then, the same walk is run once more with the
exact-word machinery of `protected_descriptor_word_profile` (the `protected-descriptor-word-v1`
selector's `word_memory`, `prune_words` and lifetime check, unchanged) on the same proof class, so
an exact aligned word load of a live closure word yields the value the owner stored there: a frame
address, whose later accesses are bounds-checked as every alias's are, or a call-target fact
(`call_via_target_profile.CallTarget`), through which the walk resolves a `_call_via_rN` call.
Every walk that does not refuse at the trigger is the walk it was before.

The kill set.  Each item removes a word's value (or every word's), so a later load of it refuses:
a pointer word stays a pointer-bearing slot of the owner, so its load without a surviving value is
refused, never read as a scalar; a constant word's load without a value is an unknown scalar.

* K1, writes.  Any store that overlaps a word, of any width, through an exact frame address, by the
  owner or by a walked callee, removes its value; a block store refuses.  An exact aligned word
  store of a frame address or a known constant gives the word that value, but only the owner makes
  a new word (K5): a walked callee may replace a word's value with one of the same kind, and any
  other store of its removes the value.
* K2, code that is not walked.  While any word is live every call is walked: the owner's pointer
  slots are incoming stack words of every callee, a summary (copy helper, BIOS wrapper, BIOS fill)
  refuses a call made with words, and a call the walk replaces by the dead-register rule (a callee
  that overwrites the frame address it is given before using it) removes every word.  An SWI
  anywhere in a walk refuses.  The rule refuses outright when the #350 callee watch records an
  escape, a dangling frame address or a stale reach of frame words.
* K3, loops.  A load of a word whose owner store lies on a cycle of the owner's control flow
  refuses.  Words join as every walk state does: a value survives a join only when it is the same
  on every edge, back edges included.
* K4, joins.  As K3: equal on every edge, or no value.
* K5, frames.  Only the owner's own stores (its span, depth 0) make words; a word outside the live
  frame is dropped at every frame change, and no frame is allocated after one is released (the
  selector's lifetime check, on the owner and on every walked callee).
* K6, stores the walk cannot place.  A store through an address the walk cannot place refuses while
  a frame address is live in a word, and removes every word's value otherwise.
* K7, call targets.  A call-target fact loaded from a word keeps the calls the stored fact had
  crossed before the store, and gains the origin ("slot", owner store site), so `call_via` checks
  those crossings when it resolves a call through it and names the slot in its target line.

A walk the retry admits records, in the buffer proof's report lines and fingerprint: the trigger,
and for every reloaded word the owner offset, the values it was reloaded with, the owner store
sites and the reload sites.
"""
import json
import re

NAME = "closure-slot-retry-v1"
TRIGGER = "buffer access overlaps a pointer-bearing argument slot"
LINE = "* buffer closure slot: "
SUMMARY = ("exact aligned frame words the owner stored, a frame address or a call-target fact, reloaded by "
           "exact word loads while every call is walked; any other store to a word, a store the walk cannot "
           "place, a block store and a dead-register call remove values; owner stores on a loop excluded")
_CHAIN = re.compile(r"(?:buffer callee 0x[0-9A-F]{8}: )*")


class RetryPolicy:
    """The one policy object of this rule: ``enabled = False`` restores the plain refusal."""

    def __init__(self, enabled):
        self.enabled = enabled

    def triggered(self, error):
        if not self.enabled or not isinstance(error, ValueError):
            return False
        text = str(error)
        return text[_CHAIN.match(text).end():] == TRIGGER


POLICY = RetryPolicy(True)


class WordResult(dict):
    """A walked callee's returned aliases, with the words it leaves (``words``)."""

    def __init__(self, aliases, words):
        super().__init__(aliases)
        self.words = tuple(sorted(words.items()))


class Slots:
    """The retried walk's closure words: the owner span, its store sites and the observed reloads."""

    def __init__(self, address, data, trigger):
        self.address, self.end, self.data = address, address + len(data), data
        self.trigger = trigger
        self.stores = {}      # offset -> {owner store site}
        self.reloads = {}     # offset -> {(site, kind, value)}

    def owned(self, site):
        return self.address <= site < self.end


def active(proof):
    return getattr(proof, "closure_slots", None) is not None


def word_context(words, frame_base, root_frame):
    # No watched registers: an R4-R11 frame address at a call is the #350 callee watch's
    # (callee_saved_watch.core_check), as on every default walk.
    return dict(words=dict(words), frame_base=frame_base, root_frame=root_frame, watched=())


def prune_words(proof, words, stack):
    import protected_descriptor_word_profile as descriptor
    return descriptor.ProtectedDescriptorWordProof.prune_words(proof, words, stack)


def check_lifetime(proof, data, address, instructions):
    import protected_descriptor_word_profile as descriptor
    descriptor.ProtectedDescriptorWordProof.check_lifetime(proof, data, address, list(instructions))


def _offset(instruction, aliases, sp_offset):
    """The frame offset an exact word load or store addresses, or None."""
    import match
    memories = [operand for operand in instruction.operands if operand.type == match.ARM_OP_MEM]
    if len(memories) != 1 or memories[0].mem.index:
        return None
    memory = memories[0].mem
    base = sp_offset if memory.base == match.ARM_REG_SP else aliases.get(memory.base)
    return None if base is None else base + memory.disp


def _same(previous, fact):
    """One unchanged word: the same kind, the same value and the same value type (a call-target fact
    equals a plain int of its value, so equality alone would hide a fact's replacement)."""
    return previous is not None and previous[0] == fact[0] and type(previous[1]) is type(fact[1]) and \
        previous == fact and (not hasattr(fact[1], "origins") or
                              (previous[1].origins, previous[1].crossed) == (fact[1].origins, fact[1].crossed))


def word_memory(proof, instruction, aliases, constants, stack, words, sp_offset, protected, *, root_frame=None):
    """The selector's exact-word step, with K5 (owner-only words) and K7 (slot call targets)."""
    import protected_descriptor_word_profile as descriptor
    import call_via_target_profile as call_via
    slots = proof.closure_slots
    before = dict(words)
    # Every alias this step can name is read before the step: the destination may overwrite it.
    offset = _offset(instruction, aliases, sp_offset)
    loaded, word_constant, word_load, pointer_store = descriptor.ProtectedDescriptorWordProof.word_memory(
        proof, instruction, aliases, constants, stack, words, sp_offset, protected, root_frame=root_frame)
    owner = slots.owned(instruction.address)
    for slot, fact in list(words.items()):
        if _same(before.get(slot), fact):
            continue
        if owner:
            slots.stores.setdefault(slot, set()).add(instruction.address)
        elif slot not in before or before[slot][0] != fact[0]:
            del words[slot]       # K5: a walked callee replaces a value with one of the same kind only
    if word_load:
        kind, value = ("pointer", loaded[1]) if loaded is not None else ("constant", word_constant)
        if isinstance(value, call_via.CallTarget):
            stores = slots.stores.get(offset, ())
            word_constant = value = call_via.CallTarget(
                value, value.origins | {("slot", site) for site in stores}, value.crossed)
        slots.reloads.setdefault(offset, set()).add((instruction.address, kind, int(value)))
    return loaded, word_constant, word_load, pointer_store


def _cyclic_sites(instructions):
    """The owner sites on a cycle of its control flow; every site when it has an indirect jump."""
    import match
    by_address = {item.address: item for item in instructions}
    successors = {}
    for site, item in by_address.items():
        regs = [operand.reg for operand in item.operands if operand.type == match.ARM_OP_REG]
        if item.mnemonic == "bx" or item.mnemonic == "pop" and match.ARM_REG_PC in regs:
            successors[site] = ()
        elif item.id == match.ARM_INS_B:
            successors[site] = (item.operands[0].imm,) + (
                (site + item.size,) if item.cc not in (match.ARM_CC_AL, match.ARM_CC_INVALID) else ())
        elif match.CS_GRP_CALL in item.groups:
            successors[site] = (site + item.size,)
        elif match.ARM_REG_PC in item.regs_access()[1]:
            return set(by_address)          # an owner switch or other indirect jump: no exact CFG
        else:
            successors[site] = (site + item.size,)
    cyclic = set()
    for start in by_address:
        pending, seen = list(successors[start]), set()
        while pending:
            site = pending.pop()
            if site == start:
                cyclic.add(start)
                break
            if site in seen or site not in successors:
                continue
            seen.add(site)
            pending.extend(successors[site])
    return cyclic


def finish(proof, instructions):
    """The retried walk's own checks (K2 escapes, K3 owner loops, K5 owner lifetime) and its record."""
    import callee_saved_watch as watch
    slots = proof.closure_slots
    items = list(instructions.values()) if isinstance(instructions, dict) else list(instructions)
    if not slots.reloads:
        raise ValueError("closure slots: the retried walk reloaded no closure word")
    premises = watch.premise_lines(proof)
    if any(watch.ESCAPE_PREMISE in line or watch.STALE_PREMISE in line or line.startswith(watch.FACT_PREFIX)
           for line in premises):
        raise ValueError("closure slots exclude escaped, dangling and stale-reach frame addresses")
    cyclic = _cyclic_sites(items)
    if any(site in cyclic for offset in slots.reloads for site in slots.stores.get(offset, ())):
        raise ValueError("closure slot reloaded from an owner store on a loop")
    check_lifetime(proof, slots.data, slots.address, items)
    proof.closure_retry = {
        "policy": NAME, "address": slots.address, "trigger": slots.trigger,
        "slots": [[offset, sorted(slots.stores.get(offset, ())),
                   [list(row) for row in sorted(slots.reloads[offset])]]
                  for offset in sorted(slots.reloads)]}


def activate(proof, address, data, trigger):
    proof.closure_slots = Slots(address, data, trigger)
    proof.word_provenance = True
    proof.word_reads = {}


def retry(error, walk, make_proof, data, address, premises=None, *, reset=None):
    """The default path's retries of a refused walk: this rule's on its trigger, else the stack-index
    retry (default_stack_index_profile) on its own.  ``reset()`` runs before either fresh walk.

    Returns (instructions, proof); a refused retry raises the plain refusal with its reason."""
    import default_stack_index_profile as default_index
    import call_via_target_profile as call_via
    if not POLICY.triggered(error):
        if reset is not None and default_index.POLICY.triggered(error):
            reset()
        return default_index.retry(error, walk, make_proof, data, address, premises)
    proof = make_proof()
    if not call_via.active(proof) or active(proof) or proof.word_provenance or \
            proof.index_policy is not None or proof.stack_index_retry is not None or not proof.stack_arguments:
        raise error           # only the default route's exact-target proofs take this retry
    if reset is not None:
        reset()
    activate(proof, address, data, TRIGGER)
    try:
        instructions = walk(proof)
        finish(proof, instructions)
    except ValueError as reason:
        raise ValueError(f"{error}; closure-slot retry: {reason}") from reason
    return instructions, proof


def walk(make_proof, run, data, address, premises, *, reset=None):
    """``run(make_proof())``, and on a trigger of either default retry that retry; (instructions, proof)."""
    proof = make_proof()
    try:
        return run(proof), proof
    except ValueError as error:
        return retry(error, run, make_proof, data, address, premises, reset=reset)


def _value(kind, value):
    return f"sp{value:+d}" if kind == "pointer" else f"0x{value:08X}"


def lines(proof):
    record = getattr(proof, "closure_retry", None)
    if record is None:
        return []
    out = [f"{LINE}`{record['policy']}` after `{record['trigger']}`: {SUMMARY}"]
    for offset, stores, reloads in record["slots"]:
        values = sorted({(kind, value) for _, kind, value in reloads})
        out.append(f"{LINE}0x{record['address']:08X} sp{offset:+d} = "
                   f"{', '.join(f'{kind} {_value(kind, value)}' for kind, value in values)}; "
                   f"stored at {', '.join(f'0x{site:08X}' for site in stores) or 'none'}; "
                   f"reloaded at {', '.join(sorted({f'0x{site:08X}' for site, _, _ in reloads}))}")
    return out


def fingerprint_payload(proof):
    record = getattr(proof, "closure_retry", None)
    if record is None:
        return None
    return json.dumps(record, sort_keys=True, separators=(",", ":")).encode()
