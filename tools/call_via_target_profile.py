"""Canonical call-via thunks beside function literals (T1) and exact call-via targets (T2).

Both rules sit on the default path, each behind its own policy object (``POLICY`` for T1,
``TARGETS`` for T2: one line gates each), and T2 applies only to the default path's two
buffer proofs, the plain ``BufferCallProof`` and the function-literal ``FunctionBufferCallProof``
(exact types: no subclass inherits it).

T1.  A caller with function literals may also call agbcc's ``_call_via_rN`` thunks.
The frameless function-address proof keeps refusing them (``canonical-thunks-v1``
stays the selector for that shape); the function-literal buffer proofs bind each
thunk by its canonical ELF name and ``bx rN`` bytes and walk it exactly as the plain
proof does: a thunk call that passes no frame address is an ordinary call, one that
passes a frame address is resolved by T2 or refused as before.

T2.  At ``bl _call_via_rN`` where the walk would inspect the thunk (a frame address
is passed), rN's value C is taken from:

* a register fact the walk carries (``CallTarget``): a reached PC-relative pool word
  of the walked body that is an odd indexed Thumb ROM entry, a zero-offset copy of
  such a fact, or such a fact in R0-R3 at the call that entered this walk (both the
  callee's alias walk and its core walk, ``BufferCallProof.inspect``, start with them); or
* the calling function's own exact value at the site (``strict_known``: literals, ROM
  words at known addresses, copies and immediate arithmetic in registers, over every
  path from its entry; no value crosses a call or SWI, and no frame word is a value
  source at all, so a word whose address a callee was given cannot hand back a stale
  value).

C resolves when C is odd and ``C & ~1`` is a unique indexed Thumb ROM entry that is
not a thunk, a pinned runtime or inside the calling function; otherwise each resolver
in ``proof.call_via_resolvers`` (``resolver(proof, site, register, C) -> address |
None``) is asked in order.  A resolved call is checked as ``bl address``.  The thunk is
``bx rN; mov r8, r8`` (bytes checked), which changes no register, flag or memory, so the
callee starts in exactly the state ``bl address`` gives.

A fact that crossed calls in R4-R11 before its use, in whatever register it is used from
(a copy into R0-R3 keeps the crossings), is relied on only after each crossed call is
checked by the callee-saved walk with the register it crossed in watched
(``callee_saved_watch.Checker.call``): a walked callee must only save and restore it; a
call the walk cannot resolve is admitted under that walk's recorded premise, one report
line per site.  Every resolution is a report line and part of the buffer fingerprint.
"""
import json
import os
import sys

SCHEMA = "call-via-exact-target-v1"
LINE = "* buffer call-via target: "


class Policy:
    """A maintainer's switch."""

    def __init__(self):
        self.enabled = True


POLICY = Policy()      # T1: function literals beside canonical call-via thunks
TARGETS = Policy()     # T2: exact call-via targets in the default buffer walks


class CallTarget(int):
    """An exact odd Thumb entry held in a register, the sites it came from and the calls it crossed.

    Equal to a plain int of the same value; two facts are equal only with equal origins and
    crossings, so a walk revisits a join whose merged fact grew.
    """

    def __new__(cls, value, origins=(), crossed=()):
        fact = int.__new__(cls, value)
        fact.origins = frozenset(origins)
        fact.crossed = frozenset(crossed)
        return fact

    def __eq__(self, other):
        if isinstance(other, CallTarget):
            return int(self) == int(other) and self.origins == other.origins and self.crossed == other.crossed
        return int(self) == other

    def __ne__(self, other):
        return not self == other

    __hash__ = int.__hash__

    def __repr__(self):
        return f"CallTarget(0x{int(self):08X})"


def join(previous, incoming):
    """A join of two register facts: the previous value, or None when they differ.

    Plain values join as before (kept only when equal); two call-target facts with the same
    value keep the value with the union of their origins and crossings."""
    if previous is None or incoming is None:
        return None
    if isinstance(previous, CallTarget) or isinstance(incoming, CallTarget):
        if not (isinstance(previous, CallTarget) and isinstance(incoming, CallTarget)) or \
                int(previous) != int(incoming):
            return None
        return CallTarget(previous, previous.origins | incoming.origins, previous.crossed | incoming.crossed)
    return previous if previous == incoming else None


def kit_match(proof):
    """The match module that defined ``proof``'s class.

    match.py runs as ``__main__`` when it issues a report and is imported as ``match`` by the profiles
    and by replay, so each proof class exists twice: a proof is checked against its own module's
    classes.  Only those two entries count: ``sys.modules["match"]`` itself, and ``__main__`` when it
    was loaded from match.py's own file.  Any other module, whatever ``__file__`` it states, does not."""
    import match
    name = type(proof).__module__
    module = sys.modules.get(name)
    if module is match or (name == "__main__" and module is not None and
                           getattr(module, "__file__", None) is not None and
                           os.path.realpath(module.__file__) == os.path.realpath(match.__file__)):
        return module
    return match


def active(proof):
    """The rule applies to the default route's exact plain and function-literal proofs only: those its
    constructors (and their replays) build with ``call_via_targets=True``, whose reports state the lines."""
    kit = kit_match(proof)
    return TARGETS.enabled and getattr(proof, "call_via_targets", False) is True and \
        type(proof) in (kit.BufferCallProof, kit.FunctionBufferCallProof)


def entry(proof, value):
    """``value & ~1`` when ``value`` is an odd unique indexed Thumb ROM entry that is not a thunk or a
    pinned runtime, else None.  No proof hook runs: the function index alone decides."""
    import match
    import rom_mirror
    import function_thunk_profile as thunk
    if type(value) not in (int, CallTarget) or not value & 1:
        return None
    address = rom_mirror.canonical(int(value)) & ~1
    if address in match.RUNTIME_HELPERS.values() or thunk.reserved(address) or \
            match.is_udivsi3_address(address) or match.modsi3.reserved(address) or \
            match.divsi3.reserved(address) or match.umodsi3.reserved(address) or \
            match.ashldi3.reserved(address) or match.software_double.reserved(address) or \
            match.software_float.reserved(address) or \
            not match.ROM_BASE <= address < match.ROM_BASE + len(proof.rom):
        return None
    candidates = [row for row in proof.entries if isinstance(row, dict) and isinstance(row.get("rom"), str)
                  and int(row["rom"], 16) & ~1 == address]
    if len(candidates) != 1 or candidates[0].get("mode") != "thumb" or int(candidates[0]["rom"], 16) != address:
        return None
    return address


def function_of(proof, site):
    """The unique indexed span holding ``site``, as (start, end), or None."""
    spans = [(int(row["rom"], 16), int(row["end"], 16)) for row in proof.entries
             if isinstance(row, dict) and isinstance(row.get("rom"), str) and isinstance(row.get("end"), str)
             and int(row["rom"], 16) <= site < int(row["end"], 16)]
    return spans[0] if len(spans) == 1 else None


_DECODER = None
# The longest walk strict_known makes over one function, in instruction visits.
STRICT_BUDGET = 20000


def _decoder():
    global _DECODER
    if _DECODER is None:
        from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
        _DECODER = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
        _DECODER.detail = True
    return _DECODER


def strict_known(proof, caller, site):
    """{register number: value} the calling function ``caller`` = (start, end) holds exactly at ``site``.

    A forward walk of its own instructions from its entry, joining every path (a value survives a
    join only when equal on every edge).  Values come only from PC-relative literal words, aligned
    ROM words loaded from a known address, immediates, register copies and immediate or register
    arithmetic.  Every register is unknown after a call or SWI, and frame words are never value
    sources, so no value can come back stale through a word whose address escaped.  Any control
    flow the walk cannot follow exactly (a branch out of the span, an indirect jump that is not the
    return idiom, an undecodable instruction, the budget) gives {} for every site.
    """
    cache = getattr(proof, "call_via_strict", None)
    if cache is None:
        states = _strict_walk(proof, caller)       # a proof without the cache: walk afresh
    else:
        if caller not in cache:
            cache[caller] = _strict_walk(proof, caller)
        states = cache[caller]
    return dict(states.get(site, {})) if states is not None else {}


def _strict_walk(proof, caller):
    import struct
    import match
    from capstone.arm import (ARM_INS_ADD, ARM_INS_B, ARM_INS_BL, ARM_INS_BX, ARM_INS_LDR, ARM_INS_LSL,
                              ARM_INS_MOV, ARM_INS_POP, ARM_INS_SUB, ARM_INS_SVC)
    start, end = caller
    rom = proof.rom
    if not match.ROM_BASE <= start < end <= match.ROM_BASE + len(rom):
        return None
    numbers = {match.ARM_REG_R0 + n: n for n in range(13)}
    numbers[match.ARM_REG_LR] = 14
    numbers[match.ARM_REG_SP] = 13
    numbers[match.ARM_REG_PC] = 15

    def rom_word(address):
        if address % 4 or not match.ROM_BASE <= address <= match.ROM_BASE + len(rom) - 4:
            return None
        return struct.unpack_from("<I", rom, address - match.ROM_BASE)[0]

    def value(state, operand):
        if operand.type == match.ARM_OP_IMM:
            return operand.imm & 0xFFFFFFFF
        if operand.type == match.ARM_OP_REG and numbers.get(operand.reg, 13) <= 12:
            return state.get(numbers[operand.reg])
        return None

    decoded = {}
    states = {}
    pending = [start]
    states[start] = {}
    visits = 0
    while pending:
        current = pending.pop()
        visits += 1
        if visits > STRICT_BUDGET or not start <= current < end or current % 2:
            return None
        if current not in decoded:
            instruction = next(_decoder().disasm(rom[current - match.ROM_BASE:min(current + 4, end) - match.ROM_BASE],
                                                 current, count=1), None)
            if instruction is None:
                return None
            decoded[current] = instruction
        instruction = decoded[current]
        state = dict(states[current])
        kind, operands = instruction.id, instruction.operands
        following = current + instruction.size
        successors = (following,)
        try:
            written = {numbers.get(register) for register in instruction.regs_access()[1]}
        except Exception:
            return None
        if 15 in written and kind not in (ARM_INS_POP, ARM_INS_B, ARM_INS_BL, ARM_INS_BX):
            return None                    # mov/add/ldr pc: an indirect jump the walk cannot follow
        result = None
        target_register = numbers.get(operands[0].reg) if operands and operands[0].type == match.ARM_OP_REG else None
        if kind == ARM_INS_B:
            target = operands[0].imm
            if not start <= target < end:
                return None
            successors = (target,) if instruction.cc in (match.ARM_CC_AL, match.ARM_CC_INVALID) else (target, following)
        elif kind == ARM_INS_BL:
            target = operands[0].imm
            if start <= target < end:
                successors = (target,)     # agbcc's far jump: a branch that writes LR
                state.pop(14, None)
            else:
                state = {}                 # a call: no register value crosses it
        elif kind == ARM_INS_SVC:
            state = {}
        elif kind == ARM_INS_BX:
            register = numbers.get(operands[0].reg)
            previous = decoded.get(current - 2)
            if register != 14 and not (previous is not None and previous.id == ARM_INS_POP and
                                       numbers.get(previous.operands[-1].reg) == register):
                return None
            successors = ()
        elif kind == ARM_INS_POP and 15 in written:
            successors = ()
        elif target_register is not None and target_register <= 12 and written <= {target_register, None}:
            if kind == ARM_INS_LDR and len(operands) == 2 and operands[1].type == match.ARM_OP_MEM:
                memory = operands[1].mem
                if memory.base == match.ARM_REG_PC and not memory.index:
                    result = rom_word(((current + 4) & ~3) + memory.disp)
                elif numbers.get(memory.base, 13) <= 12 and state.get(numbers[memory.base]) is not None:
                    offset = memory.disp
                    if memory.index:
                        index = numbers.get(memory.index, 13)
                        offset = state.get(index) if index <= 12 else None
                    if offset is not None:
                        result = rom_word((state[numbers[memory.base]] + offset) & 0xFFFFFFFF)
            elif kind == ARM_INS_MOV and len(operands) == 2:
                result = value(state, operands[1])
            elif kind in (ARM_INS_ADD, ARM_INS_SUB) and len(operands) in (2, 3):
                left, right = (operands[0], operands[1]) if len(operands) == 2 else (operands[1], operands[2])
                a, b = value(state, left), value(state, right)
                if a is not None and b is not None:
                    result = (a + b if kind == ARM_INS_ADD else a - b) & 0xFFFFFFFF
            elif kind == ARM_INS_LSL and len(operands) == 3 and operands[2].type == match.ARM_OP_IMM:
                a = value(state, operands[1])
                if a is not None:
                    result = (a << operands[2].imm) & 0xFFFFFFFF
        for number in written:
            if number is not None and number <= 14:
                state.pop(number, None)
        if result is not None:
            state[target_register] = result
        for successor in successors:
            if successor not in states:
                states[successor] = state
                pending.append(successor)
            else:
                joined = {number: known for number, known in states[successor].items()
                          if state.get(number) == known}
                if joined != states[successor]:
                    states[successor] = joined
                    pending.append(successor)
    return states


def extra_constant(proof, instruction, data, address, constants):
    """A call-target fact the instruction writes, or None (the walk's own rules then apply)."""
    import struct
    import match
    operands = instruction.operands
    if instruction.size != 2 or instruction.cc not in (match.ARM_CC_AL, match.ARM_CC_INVALID):
        return None
    if instruction.mnemonic == "ldr" and len(operands) == 2 and operands[0].type == match.ARM_OP_REG and \
            operands[1].type == match.ARM_OP_MEM and operands[1].mem.base == match.ARM_REG_PC and \
            not operands[1].mem.index:
        offset = ((instruction.address + 4) & ~3) + operands[1].mem.disp - address
        if offset < 0 or offset + 4 > len(data) or (address + offset) % 4:
            return None
        value = struct.unpack_from("<I", data, offset)[0]
        if entry(proof, value) is None:
            return None
        return CallTarget(value, {("pool", address + offset)})
    if instruction.mnemonic in ("add", "adds") and len(operands) == 3 and \
            operands[0].type == match.ARM_OP_REG and operands[1].type == match.ARM_OP_REG and \
            operands[2].type == match.ARM_OP_IMM and operands[2].imm == 0:
        value = constants.get(operands[1].reg)
        return value if isinstance(value, CallTarget) else None
    return None


def entry_facts(proof, constants):
    """The ``inspect`` keyword that seeds a walked callee's core walk with its caller's R0-R3 facts."""
    facts = argument_constants(constants or {}) if active(proof) else {}
    return {"entry_constants": facts} if facts else {}


def check_entry(proof, entry_constants):
    """verify_leaf_instructions' entry facts: only call-target facts in R0-R3, in an exact-target walk."""
    import match
    if not entry_constants:
        return ()
    if proof is None or not active(proof) or any(
            not isinstance(value, CallTarget) or not match.ARM_REG_R0 <= register <= match.ARM_REG_R0 + 3
            for register, value in entry_constants.items()):
        raise ValueError("entry call-target facts require an exact-target buffer walk and R0-R3 facts")
    return tuple(sorted(entry_constants.items()))


def argument_constants(constants):
    """The call-target facts a walked callee starts with: those its caller holds in R0-R3."""
    import match
    return {register: value for register, value in constants.items()
            if isinstance(value, CallTarget) and match.ARM_REG_R0 <= register <= match.ARM_REG_R0 + 3}


def cross(constants, site, target):
    """After a call at ``site`` to ``target``: every call-target fact left in R4-R11 crossed it there,
    recorded as (site, target, register number)."""
    import match
    for register, value in list(constants.items()):
        if isinstance(value, CallTarget) and match.ARM_REG_R0 + 4 <= register <= match.ARM_REG_R0 + 11:
            constants[register] = CallTarget(value, value.origins,
                                             value.crossed | {(site, target, register - match.ARM_REG_R0)})


def resolve(proof, thunk, constants, site):
    """The address a ``bl _call_via_rN`` at ``site`` is checked as, or None."""
    import match
    import callee_saved_watch
    if not active(proof) or thunk not in match.RUNTIME_HELPERS.values() or site is None:
        return None
    number = (thunk - match.RUNTIME_HELPERS["_call_via_r0"]) // 4
    if number > 12 or not match.thunk_is_call_via(proof.rom, thunk, number):
        return None
    caller = function_of(proof, site)
    if caller is None:
        return None
    fact = (constants or {}).get(match.ARM_REG_R0 + number)
    if isinstance(fact, CallTarget):
        value, kind = int(fact), "fact"
    else:
        value = strict_known(proof, caller, site).get(number)
        if type(value) is not int:
            return None
        fact, kind = None, "in-function"
    target = entry(proof, value)
    if target is not None and caller[0] <= target < caller[1]:
        return None
    if target is None:
        for resolver in getattr(proof, "call_via_resolvers", ()):
            target = resolver(proof, site, number, value)
            if target is not None:
                break
    if target is None:
        return None
    # Every crossing counts, whatever register holds the fact now: a copy keeps its crossings.
    crossed = sorted(fact.crossed) if fact is not None else []
    premises = set()
    for crossed_site, crossed_target, held in crossed:
        function = function_of(proof, crossed_site)
        if function is None:
            raise ValueError("call-via target crosses a call outside every indexed function")
        premises |= {(crossed_site, crossed_target, held, record)
                     for record in crossing_premises(proof, function, crossed_site, crossed_target, held)}
    key = (site, target)
    record = proof.call_via_records.setdefault(key, {
        "function": caller[0], "site": site, "thunk": thunk, "register": number, "value": value,
        "target": target, "kinds": [], "origins": [], "crossed": [], "premises": []})
    if record["value"] != value:
        raise ValueError("call-via site reaches one target through two values")
    record["kinds"] = sorted(set(record["kinds"]) | {kind})
    record["origins"] = sorted({tuple(origin) for origin in record["origins"]} |
                               (set(fact.origins) if fact is not None else set()))
    record["crossed"] = sorted({tuple(item) for item in record["crossed"]} | set(crossed))
    record["origins"] = [list(origin) for origin in record["origins"]]
    record["crossed"] = [list(item) for item in record["crossed"]]
    record["premises"] = [json.loads(item) for item in sorted(
        {json.dumps(item) for item in record["premises"]} | {json.dumps(_plain(item)) for item in premises})]
    proof.call_via_effective[site] = target
    return target


def effective(proof, site, target):
    """The target a call at ``site`` was checked as (the resolved one), consumed once."""
    if not active(proof):
        return target
    return proof.call_via_effective.pop(site, target)


def _plain(value):
    """A premise record as JSON-able lists."""
    if isinstance(value, (set, frozenset)):
        return [_plain(item) for item in sorted(value, key=repr)]
    if isinstance(value, (tuple, list)):
        return [_plain(item) for item in value]
    return value


def crossing_premises(proof, function, site, target, held):
    """The callee-saved walk of one crossed call, with R``held`` (holding the call target) watched.

    It runs on a checker of its own, so its premises are stated on this rule's own lines (the value
    watched is a call target, not an owner stack address) and none joins the shared check's lines.
    Its destination and the argument values it hands a walked callee come from the caller's strict
    values (``known``), never from that walk's ``known_at``.  Only the plain call and SWI premises
    are stated; any other premise the walk would need refuses."""
    import callee_saved_watch
    key = (function, site, target, held)
    cache = getattr(proof, "call_via_crossings", None)
    if cache is not None and key in cache:
        return cache[key]
    checker = callee_saved_watch.attach_image(callee_saved_watch.Checker(proof.rom, proof.entries), proof)
    checker.call(target, frozenset({held}), caller=function[0], site=site,
                 known=strict_known(proof, function, site))
    records = frozenset(checker.premises)
    unstated = sorted({record[0] for record in records} - {"call", "swi"})
    if unstated:
        raise ValueError(f"call-via target crossing at 0x{site:08X}: the callee-saved walk needs a premise "
                         f"this rule does not state ({', '.join(unstated)})")
    if cache is not None:
        cache[key] = records
    return records


PREMISE_LINE = "* buffer call-via premise: "
CROSSING_PREMISE = ("unproved premise: code reached through an unresolved function pointer, or outside ROM, "
                    "uses the value that register holds on entry only to save and restore it")
BIOS_CROSSING_PREMISE = ("unproved premise: the BIOS uses the value that register holds on entry only to save "
                         "and restore it")


def premise_line(record, premise):
    """A premise a resolution relies on: a call or SWI its call target crossed that the walk could not
    check, stated as what it is (the watched register holds the call target, not a stack address)."""
    import callee_saved_watch
    crossed_site, crossed_target, held, item = premise
    if item[0] == "call":
        _, function, site, chain, destination, registers, stacked, flagged = item
        through = " then ".join(f"_call_via_r{link}" if link < 16 else f"the bx r3 at 0x{link:08X}"
                                for link in chain)
        where = "to an unknown address" if destination is None else \
            f"resolved to 0x{destination:08X} ({callee_saved_watch.region(destination)})"
        head, text = f"call at 0x{site:08X} in 0x{function:08X} through {through} {where}", CROSSING_PREMISE
    else:
        _, function, site, number, registers, stacked, flagged = item
        routine = f" ({callee_saved_watch.BIOS_WRITES[number][0]})" if number in callee_saved_watch.BIOS_WRITES else ""
        head, text = f"SWI 0x{number:02X}{routine} at 0x{site:08X} in 0x{function:08X}", BIOS_CROSSING_PREMISE
    holders = ",".join(f"R{register}" for register in registers if register != 12) or f"R{held}"
    relied = f"with {holders} holding the call-via target 0x{record['value']:08X}"
    if stacked:
        relied += (f" and the frame word{'s' if len(stacked) > 1 else ''} at "
                   f"{','.join(f'sp{offset:+d}' for offset in stacked)} holding it")
    if flagged:
        relied += " and the condition flags depending on it"
    if 12 in registers:
        relied += " and R12 holding a frame address a callee returned"
        text = f"{text}, and {callee_saved_watch.R12_PREMISE}"
    return (f"{PREMISE_LINE}`{SCHEMA}` 0x{record['site']:08X} in 0x{record['function']:08X} relies on the "
            f"crossed call at 0x{crossed_site:08X} (0x{crossed_target:08X}): {head}, {relied}; {text}")


def lines(proof):
    result = []
    for _, record in sorted(getattr(proof, "call_via_records", {}).items()):
        site = record["site"]
        origins = ", ".join(f"{kind} 0x{at:08X}" for kind, at in record["origins"]) or "none"
        crossed = ", ".join(f"0x{s:08X}->0x{t:08X}:r{r}" for s, t, r in record["crossed"]) or "none"
        result.append(f"{LINE}`{SCHEMA}` 0x{site:08X} in 0x{record['function']:08X} "
                      f"_call_via_r{record['register']} = 0x{record['value']:08X} -> 0x{record['target']:08X} "
                      f"({'+'.join(record['kinds'])}; origins {origins}; crossed {crossed})")
        result.extend(premise_line(record, premise) for premise in record["premises"])
    return result


def fingerprint_payload(proof):
    records = getattr(proof, "call_via_records", {})
    if not records:
        return None
    return json.dumps([SCHEMA, [records[key] for key in sorted(records)]],
                      sort_keys=True, separators=(",", ":")).encode()
