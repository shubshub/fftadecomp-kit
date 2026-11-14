"""Dispatch-identified switch pools (u16-scalars-v2) with a fixed outgoing-argument frame.

The selector keeps every u16-scalars-v2 layout and literal-binding rule. It adds
only a fixed Thumb frame whose words are write-only outgoing call arguments.
"""

SELECTOR = 'u16-scalars-frame-v1'
SCHEMA = 'elf-symbol-thumb-switch-data-u16-scalars-frame-v1'
SUMMARY = ('one guarded local Thumb table found by its dispatch load, with complete mapped object '
           'and u16 scalar words and a fixed write-only outgoing-argument frame')
# The manifest key deliberately avoids "frame_policy", which names the
# typed-outgoing-six-words-v1 family when status recovers saved selectors.
STACK_POLICY = 'write-only-outgoing-argument-words-v1'
# Conditional frame stores between calls can multiply the walked
# (site, phase, written) states; past this bound the proof refuses.
STATE_LIMIT = 1 << 16


def fingerprint(address, data, manifest):
    import hashlib
    from match_evidence import switch_manifest
    proof = hashlib.sha256()
    for payload in (SCHEMA.encode('ascii'), address.to_bytes(4, 'little'),
                    data, switch_manifest(manifest).encode('ascii')):
        proof.update(len(payload).to_bytes(8, 'little'))
        proof.update(payload)
    return proof.hexdigest()


def check_context(policy):
    if type(policy) is not str or policy != STACK_POLICY:
        raise ValueError('outgoing-argument switch frame requires its canonical stack policy')


def verify_frame(instructions, edges, address, calls):
    """Prove one fixed frame of write-only outgoing words on every reached path.

    The ordinary verifier already supplies the complete CFG, balanced saved
    registers, entry-LR return, typed literal ownership and the ordinary
    direct-call ABI boundary. This adds:

    * one constant `sub sp,#n` reached before any call or frame access, and
      every return reached only after an `add sp,#n` of the same size;
    * no other SP arithmetic and no SP register operand, so no stack address
      reaches a register and no block transfer is based on SP; 32-bit
      encodings other than the bound calls are refused;
    * frame accesses are only `str rX,[sp,#k]` with k a word offset below n;
      the caller never reads the frame;
    * each call consumes the words written since the previous call (or the
      allocation) as its outgoing arguments 5+: that set is a prefix of the
      frame, identical on every path to the call, and is empty again after
      the call because a callee may overwrite its incoming arguments;
    * no word is still pending at the release, and every frame word is
      consumed by some call;
    * the walk visits at most STATE_LIMIT states, or the proof refuses.

    No fact about a callee's arity or memory effects follows.
    """
    from capstone.arm import ARM_OP_MEM, ARM_OP_REG, ARM_REG_SP
    from match import thumb_stack_adjustment
    allocations, releases = {}, {}
    for site, item in instructions.items():
        adjustment = thumb_stack_adjustment(item)
        if adjustment:
            (allocations if adjustment < 0 else releases)[site] = abs(adjustment)
            continue
        if item.size != 2 and site not in calls:
            raise ValueError('outgoing-argument switch frame admits only 16-bit Thumb instructions and calls')
        if item.mnemonic in ('push', 'pop'):
            continue
        # Capstone names an ldm/stm base as a register operand, so this also
        # refuses SP-based block transfers.
        if any(operand.type == ARM_OP_REG and operand.reg == ARM_REG_SP for operand in item.operands):
            raise ValueError('outgoing-argument switch frame excludes stack-address materialization, '
                             'dynamic stack adjustment and stack block transfers')
    if len(allocations) != 1 or not releases or \
            set(releases.values()) != set(allocations.values()):
        raise ValueError('outgoing-argument switch frame requires one fixed allocation '
                         'released by the same constant')
    allocation, words = next(iter(allocations.items()))
    full = (1 << words) - 1
    consumed = {}
    pending = [(address, 0, 0)]
    seen = set()
    while pending:
        state = pending.pop()
        if state in seen:
            continue
        seen.add(state)
        if len(seen) > STATE_LIMIT:
            raise ValueError('outgoing-argument frame proof exceeds its state limit')
        site, phase, written = state
        item = instructions[site]
        if site == allocation:
            if phase != 0:
                raise ValueError('outgoing-argument frame allocation is repeated or out of lifetime')
            phase = 1
        elif site in releases:
            if phase != 1:
                raise ValueError('outgoing-argument frame release is outside its allocation')
            if written:
                raise ValueError('outgoing-argument word is written but no call consumes it')
            phase = 2
        for operand in item.operands:
            if operand.type != ARM_OP_MEM or operand.mem.base != ARM_REG_SP:
                continue
            if phase != 1 or item.mnemonic != 'str' or item.size != 2 or operand.mem.index or \
                    operand.mem.disp not in range(0, 4 * words, 4):
                raise ValueError('outgoing-argument frame access must store an owned aligned word')
            written |= 1 << (operand.mem.disp // 4)
        if site in calls:
            if phase != 1:
                raise ValueError('outgoing-argument frame calls must occur inside the frame lifetime')
            if written & (written + 1):
                raise ValueError('outgoing arguments must initialize a prefix of the frame')
            if consumed.setdefault(site, written) != written:
                raise ValueError('outgoing arguments must be initialized identically on every path to a call')
            written = 0
        if phase == 1 and item.mnemonic in ('push', 'pop'):
            # A saved-register push/pop inside the frame would shift its slots.
            raise ValueError('outgoing-argument slots cannot move inside their live frame')
        successors = edges[site]
        if not successors and phase != 2:
            raise ValueError('outgoing-argument frame return must follow its release')
        pending.extend((target, phase, written) for target in successors)
    if not consumed or max(consumed.values()) != full:
        raise ValueError('every outgoing-argument frame word must be consumed by a call')
