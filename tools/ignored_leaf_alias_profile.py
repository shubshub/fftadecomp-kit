"""Incoming aliases may die only in exact, noncalling Thumb leaf owners.

This is intentionally narrower than a general callee effect analysis. Every
reached instruction must have an explicitly decoded Thumb-1 effect, and an
incoming alias must be overwritten before any read and on every return path.
Original ROM instructions, not C prototypes, establish the contract.
"""
import hashlib
import json

SELECTOR = 'restoring-owner-ignored-leaf-alias-v1'
SCHEMA = 'elf-symbol-thumb-ignored-leaf-alias-v1'
CONTROL_FLOW = ('complete acyclic Thumb owner; exact bounded path states and '
                'original noncalling leaf incoming-alias overwrite proofs')
LEAF_SCHEMA = 'complete-thumb-leaf-incoming-alias-overwrite-v1'
MAX_LEAF_BYTES = 256


def sha(data):
    return hashlib.sha256(data).hexdigest()


def effects(instruction):
    """Decode a closed Thumb-1 subset with no unknown or implicit data effects.

    Only low argument/scratch registers may change. Stack operations are the
    canonical LR save and single-register restore, checked independently by
    the native frame/return proof. Ordinary loads/stores, ALU carry operations,
    high-register operations, interrupts, calls and indirect jumps are absent.
    """
    import match
    if instruction.size != 2:
        raise ValueError('ignored leaf has an unsupported instruction effect')
    word = int.from_bytes(instruction.bytes, 'little')
    r = lambda number: match.ARM_REG_R0 + number
    read, written = set(), set()
    if word & 0xE000 == 0 and word & 0x1800 != 0x1800:  # immediate shift
        read.add(r((word >> 3) & 7)); written.add(r(word & 7))
    elif word & 0xF800 == 0x1800:  # ADD/SUB register or imm3
        read.add(r((word >> 3) & 7)); written.add(r(word & 7))
        if not word & 0x0400:
            read.add(r((word >> 6) & 7))
    elif word & 0xE000 == 0x2000:  # MOV/CMP/ADD/SUB imm8
        operation, register = (word >> 11) & 3, r((word >> 8) & 7)
        if operation != 0:
            read.add(register)
        if operation != 1:
            written.add(register)
    elif word & 0xF800 == 0x4800:  # aligned PC-relative word load
        read.add(match.ARM_REG_PC); written.add(r((word >> 8) & 7))
    elif word == 0xB500:  # push {lr}
        read.update((match.ARM_REG_SP, match.ARM_REG_LR)); written.add(match.ARM_REG_SP)
    elif word & 0xFF00 == 0xBC00 and (word & 255).bit_count() == 1:  # pop {rN}
        read.add(match.ARM_REG_SP)
        written.update((match.ARM_REG_SP, r((word & 255).bit_length() - 1)))
    elif word & 0xF000 == 0xD000 and (word >> 8) & 15 < 14:  # condition branch
        written.add(match.ARM_REG_PC)
    elif word & 0xF800 == 0xE000:  # immediate branch
        written.add(match.ARM_REG_PC)
    elif word & 0xFF87 == 0x4700:  # BX, accepted only at native verified returns
        read.add(r((word >> 3) & 15) if (word >> 3) & 15 < 13 else
                 {13: match.ARM_REG_SP, 14: match.ARM_REG_LR,
                  15: match.ARM_REG_PC}[(word >> 3) & 15])
        written.add(match.ARM_REG_PC)
    else:
        raise ValueError('ignored leaf has an unsupported instruction effect')
    allowed = {match.ARM_REG_R0 + n for n in range(4)} | {
        match.ARM_REG_SP, match.ARM_REG_LR, match.ARM_REG_PC}
    if (read | written) - allowed or match.ARM_REG_LR in written:
        raise ValueError('ignored leaf does not establish callee-saved ABI preservation')
    # The encoding table is authoritative; disagreement with decoder metadata
    # is a refusal, including unexpected implicit register accesses.
    decoded_read, decoded_written = instruction.regs_access()
    if set(decoded_read) - {match.ARM_REG_CPSR} != read or \
            set(decoded_written) - {match.ARM_REG_CPSR} != written:
        raise ValueError('ignored leaf has unknown or inconsistent implicit effects')
    return read, written


def flag_effects(instruction):
    """Track all implicit condition-code inputs, including preserved C/V bits."""
    word = int.from_bytes(instruction.bytes, 'little')
    # N/Z/C/V bits in this local abstract mask.
    if word & 0xE000 == 0 and word & 0x1800 != 0x1800:
        carry = (word >> 11) & 3 != 0 or (word >> 6) & 31 != 0
        return 0, 3 | (4 if carry else 0)
    if word & 0xF800 == 0x1800:
        return 0, 15
    if word & 0xE000 == 0x2000:
        return 0, 3 if (word >> 11) & 3 == 0 else 15
    if word & 0xF000 == 0xD000 and (word >> 8) & 15 < 14:
        condition = (word >> 8) & 15
        return (2, 2, 4, 4, 1, 1, 8, 8, 6, 6, 9, 9, 11, 11)[condition], 0
    return 0, 0


class IgnoredLeafAliasProof:
    """Fresh context, restricted to one caller and its exact reached BL sites."""
    def __init__(self, rom, mapping, index, objects, caller, size, calls):
        self.rom, self.mapping, self.index, self.objects = rom, mapping, index, objects
        self.caller, self.size, self.calls = caller, size, dict(calls)
        self.dependencies = {}
        self.observations = {}

    def leaf(self, target):
        import match
        import owner_admission_profile as owner
        import owner_graph_profile as graph
        entries = json.loads(self.mapping)
        match.function_address_target(f'func_{target:08X}', entries, self.caller,
                                      self.size, len(self.rom))
        rows = [row for row in entries if int(row['rom'], 16) == target]
        if len(rows) != 1:
            raise ValueError('ignored leaf requires a unique complete original owner')
        end = int(rows[0]['end'], 16)
        if not 0 < end - target <= MAX_LEAF_BYTES:
            raise ValueError('ignored leaf exceeds the bounded complete-owner extent')
        data = self.rom[target-match.ROM_BASE:end-match.ROM_BASE]
        # Reject all calls and indirect/forwarding control before any summary
        # can be applied, including recursion and same-owner local BLs.
        refinement = owner.refine(data, target, self.mapping)
        instructions, edges, branches, calls, words = graph.graph(data, target, refinement)
        if calls or branches or words:
            raise ValueError('ignored leaf excludes calls, forwarding and local BL control')
        native, verified, refinement = owner.preflight(data, target, self.rom,
            self.mapping, self.index, self.objects, selector=owner.ACYCLIC_SELECTOR)
        if type(rows[0].get('instrs')) is not int or rows[0]['instrs'] != len(verified):
            raise ValueError('ignored leaf JSON reachable instruction count differs')
        accesses = {site: effects(item) for site, item in instructions.items()}
        pending, seen = [(target, 0)], set()
        while pending:
            current, defined = pending.pop()
            if (current, defined) in seen:
                continue
            seen.add((current, defined))
            read_flags, written_flags = flag_effects(instructions[current])
            if read_flags & ~defined:
                raise ValueError('ignored leaf observes incoming implicit condition flags')
            pending.extend((successor, defined | written_flags) for successor in edges[current])
        returns = {int(site, 16) for site in refinement['returns']}
        for site, item in instructions.items():
            if item.mnemonic == 'bx' and site not in returns:
                raise ValueError('ignored leaf excludes unproved indirect control')
        return data, native, instructions, edges, returns, accesses

    def check_call(self, site, target, aliases, pointer_slots):
        import match
        if self.calls.get(site) != target or not self.caller <= site < self.caller + self.size:
            raise ValueError('ignored leaf call is not bound to an exact original BL site')
        if pointer_slots:
            raise ValueError('ignored leaf excludes incoming stack pointer slots')
        registers = sorted(set(aliases) & set(match.CALLER_CLOBBERED))
        if not registers:
            raise ValueError('ignored leaf proof requires an incoming caller-clobbered alias')
        data, native, instructions, edges, returns, accesses = self.leaf(target)
        # Explore the entry value separately for each physical register. A
        # read before a full write observes that value, even if later erased.
        # A still-live value at any return cannot be removed from caller state.
        for register in registers:
            pending, seen = [(target, True)], set()
            while pending:
                current, live = pending.pop()
                if (current, live) in seen:
                    continue
                seen.add((current, live))
                read, written = accesses[current]
                if live and register in read:
                    raise ValueError(f'ignored leaf observes incoming {instructions[current].reg_name(register)} '
                                     f'at 0x{current:08X}')
                live = live and register not in written
                if current in returns and live:
                    raise ValueError('ignored leaf must overwrite the incoming alias on every return')
                pending.extend((successor, live) for successor in edges[current])
        identity = {'schema': LEAF_SCHEMA, 'address': target, 'end': target + len(data),
            'bytes': len(data), 'body_sha256': sha(data),
            'instructions': len(instructions), 'owner': native,
            'mapping_sha256': sha(self.mapping), 'index_sha256': sha(self.index),
            'objects_sha256': None if self.objects is None else sha(self.objects),
            'rom_sha256': sha(self.rom)}
        self.dependencies[target] = identity
        self.observations[(site, tuple(registers))] = [site-self.caller, f'func_{target:08X}',
            [instructions[target].reg_name(register) for register in registers]]
        return {}

    def manifest(self):
        return {'schema': LEAF_SCHEMA,
            'callees': [self.dependencies[target] for target in sorted(self.dependencies)],
            'discarded_aliases': [self.observations[key] for key in sorted(self.observations)]}
