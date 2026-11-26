"""A call target stored into a freshly allocated block, forwarded to its reload under a reviewed premise.

0x08005954 (the task creator) takes a block from the arena allocator 0x08007138, stores the task's
callback (its incoming R1, kept in R8) into the block's word 0 at 0x0800598A and reloads it at
0x08005A04 for `bl _call_via_r3` at 0x08005A08, which passes 0x08005954's own frame.  No call lies
between the store and the reload and the block's register is not written, but eight stores between
them go through other registers (the parent's or the scheduler's task lists, and 0x08005954's own
frame), so the walk cannot show that word 0 still holds the callback: the call-via value is unknown
and the call refuses.

That none of those stores reaches word 0 of the new block is a game-state premise (allocator and
task-list consistency), not something the ROM shows.  It is admitted only through a reviewed,
per-address entry in the decomp's `config/fresh_block_premises.json`:

    {"0x08005954": {"review": "<the review>", "rows": [{"allocator": "0x08007138",
      "call": "0x08005976", "base": "r7", "store": "0x0800598A", "reload": "0x08005A04",
      "offset": 0, "writes": ["0x080059B0", ...]}]}}

The kit checks each row against the function's bytes and refuses the entry when anything differs:

* the function is a unique indexed Thumb row holding `call`, `store` and `reload`;
* `call` is `bl allocator`, and the next instruction copies R0 into `base` (`adds base, r0, #0`
  or `mov base, r0`), so on that path `base` holds the allocator's result;
* `store` is `str rS, [base, #offset]` and `reload` is `ldr rL, [base, #offset]` (a word, offset a
  multiple of 4);
* on the function's control-flow graph (where a `bl` into the function's own span, agbcc's far
  jump, refuses) the copy into `base` is reached only from `call`, neither `store` nor `reload`
  lies on a loop, every path from its entry to `reload` passes `store`, every path to `store`
  passes the copy into `base`, and no instruction between the copy and `store` writes `base`
  except a call (the callee-saved ABI premise every walk makes);
* every instruction on a path from `store` to `reload` is not a call, a SWI, a branch through a
  register or a write of `base`; each store through `base` has an immediate offset outside
  `[offset, offset + 4)` (checked, not premised); and the set of every other memory write there is
  exactly `writes`.

So on every path the store and the reload run at most once each, the store first, with `base`
holding the allocator's latest result.  The premise is then exactly: none of the listed writes
changes word `offset` of the block.  The review states why and what is not proved.  With a valid
entry, both buffer walks of the function carry an exact call-target fact
(call_via_target_profile.CallTarget) that rS holds at `store` to rL at `reload` (a store of a
value with no fact leaves none); nothing else changes.  Without an entry, or for any other
function or pair, the walk is as before.  Every report whose walk forwarded a fact prints the
entry's review text verbatim and the row on one `* buffer fresh block premise:` line and binds both
into its buffer fingerprint; a report that forwarded nothing is unchanged.
"""
import json

SCHEMA = 'fresh-block-word-premise-v1'
PREMISES_PATH = 'config/fresh_block_premises.json'
FIELD = '* buffer fresh block premise'
ROW_KEYS = ('allocator', 'call', 'base', 'store', 'reload', 'offset', 'writes')
KEY_BASE = -(1 << 30)          # constants keys outside every register number


def snapshot(root):
    """The decomp's reviewed entry file, as bytes, or None when it has none."""
    from pathlib import Path
    try:
        return (Path(root) / PREMISES_PATH).read_bytes()
    except FileNotFoundError:
        return None


def applies(proof):
    """The default path's two stack-argument proofs with an entry file, of the match module that
    defined the proof (match.py issues as __main__ and replays as match:
    call_via_target_profile.kit_match)."""
    from call_via_target_profile import kit_match
    kit = kit_match(proof)
    return type(proof) in (kit.BufferCallProof, kit.FunctionBufferCallProof) and \
        getattr(proof, 'fresh_blocks', None) is not None


def _hex(text, what):
    if not isinstance(text, str) or not text.startswith('0x') or len(text) != 10:
        raise ValueError(f"fresh block premise: {what} is not a 0x-prefixed 32-bit address")
    return int(text, 16)


def parse(raw):
    """{function: (entry, [row])} from the entry file's bytes; ValueError on any malformed entry."""
    if raw is None:
        return {}
    if not isinstance(raw, bytes):
        raise ValueError("fresh block premises must be the entry file's bytes")
    try:
        entries = json.loads(raw)
    except ValueError as error:
        raise ValueError(f"fresh block premises: {PREMISES_PATH} is not JSON") from error
    if not isinstance(entries, dict):
        raise ValueError(f"fresh block premises: {PREMISES_PATH} is not an object")
    parsed = {}
    for key, entry in entries.items():
        function = _hex(key, 'an entry key')
        if not isinstance(entry, dict) or set(entry) != {'review', 'rows'} or \
                not isinstance(entry['review'], str) or not entry['review'].strip() or \
                not isinstance(entry['rows'], list) or not entry['rows']:
            raise ValueError(f"fresh block premise 0x{function:08X}: an entry is a review text and rows")
        rows = []
        for row in entry['rows']:
            if not isinstance(row, dict) or set(row) != set(ROW_KEYS):
                raise ValueError(f"fresh block premise 0x{function:08X}: a row has exactly {', '.join(ROW_KEYS)}")
            base = row['base']
            if not isinstance(base, str) or base not in tuple(f'r{n}' for n in range(4, 12)):
                raise ValueError(f"fresh block premise 0x{function:08X}: the base is one of r4-r11")
            offset = row['offset']
            if type(offset) is not int or offset % 4 or not 0 <= offset <= 124:
                raise ValueError(f"fresh block premise 0x{function:08X}: the offset is a word offset 0-124")
            writes = row['writes']
            if not isinstance(writes, list) or len(set(writes)) != len(writes):
                raise ValueError(f"fresh block premise 0x{function:08X}: writes is a list of distinct sites")
            rows.append(dict(allocator=_hex(row['allocator'], 'the allocator'), call=_hex(row['call'], 'the call'),
                             base=int(base[1:]), store=_hex(row['store'], 'the store'),
                             reload=_hex(row['reload'], 'the reload'), offset=offset,
                             writes=sorted(_hex(site, 'a write') for site in writes)))
        if len({(row['store'], row['reload']) for row in rows}) != len(rows):
            raise ValueError(f"fresh block premise 0x{function:08X}: a store/reload pair is listed twice")
        parsed[function] = (entry, rows)
    return parsed


# ---- the structural check --------------------------------------------------------------------

def _decoder():
    from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    decoder.detail = True
    return decoder


def _graph(data, start):
    """{address: (instruction, successors)} of the function's code reachable from its entry: `b`
    and conditional `b` edges, a `bl` out of the span falls through, a return (`bx`, `pop {.., pc}`)
    ends a path; a `bl` into the span (a far jump) and any other PC write refuse."""
    from capstone import CS_GRP_CALL, CS_GRP_INT
    from capstone.arm import ARM_INS_B, ARM_CC_AL, ARM_CC_INVALID, ARM_REG_PC
    decoder, nodes, pending = _decoder(), {}, [start]
    end = start + len(data)
    while pending:
        current = pending.pop()
        if current in nodes:
            continue
        if not start <= current < end - 1:
            raise ValueError("fresh block premise: control leaves the function's span")
        found = next(decoder.disasm(data[current - start:current - start + 4], current, 1), None)
        if found is None:
            raise ValueError(f"fresh block premise: no instruction at 0x{current:08X}")
        written = found.regs_access()[1]
        if found.id == ARM_INS_B:
            successors = (found.operands[0].imm,) + (
                () if found.cc in (ARM_CC_AL, ARM_CC_INVALID) else (current + found.size,))
        elif found.mnemonic == 'bx' or found.mnemonic == 'pop' and ARM_REG_PC in written:
            successors = ()
        elif CS_GRP_CALL in found.groups and found.mnemonic == 'bl':
            if start <= found.operands[0].imm < end:
                # agbcc's far jump (`bl` to a local label) never returns here: not modelled
                raise ValueError(f"fresh block premise: a far jump at 0x{current:08X}")
            successors = (current + found.size,)
        elif ARM_REG_PC in written or CS_GRP_INT in found.groups and found.mnemonic != 'svc':
            raise ValueError(f"fresh block premise: unsupported control transfer at 0x{current:08X}")
        else:
            successors = (current + found.size,)
        nodes[current] = (found, successors)
        pending.extend(successors)
    return nodes


def _reaches(nodes, sources, target, blocked):
    """Whether `target` is reachable from `sources` without entering a node in `blocked`."""
    seen, pending = set(), [source for source in sources if source not in blocked]
    while pending:
        current = pending.pop()
        if current == target:
            return True
        if current in seen:
            continue
        seen.add(current)
        pending.extend(successor for successor in nodes[current][1] if successor not in blocked)
    return False


def _between(nodes, start, end):
    """Nodes on some path from `start` to `end` (both excluded): reachable from `start` without
    passing `end`, and reaching `end`."""
    forward, pending = set(), list(nodes[start][1])
    while pending:
        current = pending.pop()
        if current in forward or current == end:
            continue
        forward.add(current)
        pending.extend(nodes[current][1])
    predecessors = {}
    for address, (_, successors) in nodes.items():
        for successor in successors:
            predecessors.setdefault(successor, []).append(address)
    backward, pending = set(), list(predecessors.get(end, ()))
    while pending:
        current = pending.pop()
        if current in backward or current == start:
            continue
        backward.add(current)
        pending.extend(predecessors.get(current, ()))
    return forward & backward


def _memory_write(instruction):
    return instruction.mnemonic.startswith(('str', 'stm', 'push'))


def _word_access(instruction, mnemonic, base, offset):
    """(rD) when `instruction` is exactly `mnemonic rD, [r<base>, #offset]`, else None."""
    from capstone.arm import ARM_OP_MEM, ARM_OP_REG, ARM_REG_R0
    operands = instruction.operands
    if instruction.mnemonic != mnemonic or len(operands) != 2 or operands[0].type != ARM_OP_REG or \
            operands[1].type != ARM_OP_MEM or operands[1].mem.base != ARM_REG_R0 + base or \
            operands[1].mem.index or operands[1].mem.disp != offset:
        return None
    return operands[0].reg - ARM_REG_R0


def check(proof, function, row):
    """The row's (rS, rL), after checking it against the function's bytes; ValueError otherwise."""
    from capstone import CS_GRP_CALL, CS_GRP_INT
    from capstone.arm import ARM_OP_MEM, ARM_OP_REG, ARM_OP_IMM, ARM_REG_R0
    data = proof.span(function)
    nodes = _graph(data, function)
    base, offset = row['base'], row['offset']
    for name in ('call', 'store', 'reload'):
        if row[name] not in nodes:
            raise ValueError(f"fresh block premise 0x{function:08X}: {name} 0x{row[name]:08X} is not "
                             "an instruction the function reaches")
    call = nodes[row['call']][0]
    if call.mnemonic != 'bl' or call.operands[0].imm != row['allocator']:
        raise ValueError(f"fresh block premise 0x{function:08X}: no call of the allocator at the call site")
    (copy,) = nodes[row['call']][1]
    move = nodes[copy][0]
    operands = move.operands
    if not (len(operands) >= 2 and operands[0].type == ARM_OP_REG and operands[0].reg == ARM_REG_R0 + base and
            operands[1].type == ARM_OP_REG and operands[1].reg == ARM_REG_R0 and
            (move.mnemonic == 'mov' and len(operands) == 2 or
             move.mnemonic == 'adds' and len(operands) == 3 and operands[2].type == ARM_OP_IMM and
             operands[2].imm == 0)):
        raise ValueError(f"fresh block premise 0x{function:08X}: the allocator's R0 is not copied into the base")
    stored = _word_access(nodes[row['store']][0], 'str', base, offset)
    loaded = _word_access(nodes[row['reload']][0], 'ldr', base, offset)
    if stored is None or loaded is None:
        raise ValueError(f"fresh block premise 0x{function:08X}: the store and reload are not word accesses "
                         "of the base at the offset")
    if any(address != row['call'] and copy in successors for address, (_, successors) in nodes.items()):
        raise ValueError(f"fresh block premise 0x{function:08X}: the copy into the base is reached other "
                         "than from the allocator call")
    for name in ('store', 'reload'):
        if _reaches(nodes, nodes[row[name]][1], row[name], set()):
            raise ValueError(f"fresh block premise 0x{function:08X}: the {name} lies on a loop")
    if _reaches(nodes, [function], row['reload'], {row['store']}):
        raise ValueError(f"fresh block premise 0x{function:08X}: a path reaches the reload without the store")
    if _reaches(nodes, [function], row['store'], {copy}):
        raise ValueError(f"fresh block premise 0x{function:08X}: a path reaches the store without the "
                         "allocator's result in the base")
    for address in _between(nodes, copy, row['store']):
        instruction = nodes[address][0]
        if ARM_REG_R0 + base in instruction.regs_access()[1] and CS_GRP_CALL not in instruction.groups:
            raise ValueError(f"fresh block premise 0x{function:08X}: the base is written before the store")
    writes = []
    for address in sorted(_between(nodes, row['store'], row['reload'])):
        instruction = nodes[address][0]
        if CS_GRP_CALL in instruction.groups or CS_GRP_INT in instruction.groups or instruction.mnemonic == 'bx':
            raise ValueError(f"fresh block premise 0x{function:08X}: a call or transfer lies between "
                             "the store and the reload")
        if ARM_REG_R0 + base in instruction.regs_access()[1]:
            raise ValueError(f"fresh block premise 0x{function:08X}: the base is written between the "
                             "store and the reload")
        if not _memory_write(instruction):
            continue
        memory = [operand for operand in instruction.operands if operand.type == ARM_OP_MEM]
        if instruction.mnemonic.startswith('str') and memory and memory[0].mem.base == ARM_REG_R0 + base:
            width = 4 if instruction.mnemonic == 'str' else 2 if instruction.mnemonic == 'strh' else 1
            disp = memory[0].mem.disp
            if memory[0].mem.index or disp < offset + 4 and disp + width > offset:
                raise ValueError(f"fresh block premise 0x{function:08X}: a store through the base may "
                                 "overwrite the stored word")
            continue                                   # checked: it misses the word
        if instruction.mnemonic.startswith('stm') and instruction.operands[0].reg == ARM_REG_R0 + base:
            raise ValueError(f"fresh block premise 0x{function:08X}: a block store through the base")
        writes.append(address)
    if writes != row['writes']:
        raise ValueError(f"fresh block premise 0x{function:08X}: the writes between the store and the reload "
                         f"are {', '.join(f'0x{site:08X}' for site in writes) or 'none'}, not the entry's")
    return stored, loaded


def rows_for(proof, function):
    """The checked rows of `function`'s entry (memoised per proof), or ()."""
    if not applies(proof):
        return ()
    cache = proof.fresh_block_checked
    if function not in cache:
        entry = proof.fresh_block_entries.get(function)
        cache[function] = () if entry is None else tuple(
            (row, check(proof, function, row)) for row in entry[1])
    return cache[function]


def extra_constant(proof, instruction, function, constants):
    """In a walk of `function`: at a row's store, remember the call-target fact rS holds; at its reload,
    return it for rL.  None everywhere else (and the walk's own rules apply)."""
    import call_via_target_profile as call_via
    from capstone.arm import ARM_REG_R0
    for row, (stored, loaded) in rows_for(proof, function):
        key = KEY_BASE - row['store']
        if instruction.address == row['store']:
            fact = constants.get(ARM_REG_R0 + stored)
            if isinstance(fact, call_via.CallTarget):
                constants[key] = fact
            else:
                constants.pop(key, None)       # the word now holds a value with no fact
            return None
        if instruction.address == row['reload']:
            fact = constants.pop(key, None)
            if isinstance(fact, call_via.CallTarget):
                proof.fresh_block_uses.add((function, row['store'], row['reload']))
                return fact
            return None
    return None


def record(proof):
    if not getattr(proof, 'fresh_block_uses', None):
        return None
    used = []
    for function, store, reload in sorted(proof.fresh_block_uses):
        entry, rows = proof.fresh_block_entries[function]
        (row,) = [raw for raw, parsed in zip(entry['rows'], rows)
                  if (parsed['store'], parsed['reload']) == (store, reload)]
        used.append(dict(function=function, review=entry['review'], row=row))
    return dict(schema=SCHEMA, used=used)


def fingerprint_payload(proof):
    evidence = record(proof)
    return None if evidence is None else json.dumps(evidence, sort_keys=True, separators=(',', ':')).encode()


def lines(proof):
    evidence = record(proof)
    if evidence is None:
        return []
    return [f"{FIELD}: `{SCHEMA}` 0x{item['function']:08X} row {json.dumps(item['row'], sort_keys=True)}; "
            f"review: {item['review']}" for item in evidence['used']]
