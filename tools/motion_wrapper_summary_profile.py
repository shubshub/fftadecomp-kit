"""The pinned motion-task wrappers func_080D6238 and func_080D6284 as summarised calls (kit #424).

Each wrapper puts its arguments into a parameter block in its own frame, points a 28-byte task
descriptor at that block (`str r0,[r2,#4]` with r0 = sp) and starts a motion task through the
scheduler entry func_08005B6C.  A caller that keeps a position in a local and passes its address in
R1 or R2 is refused inside the wrapper today (`stack aliases cannot be stored or spilled`), although
the scheduled callback reads that position once, synchronously, and keeps nothing of it.

This module summarises a direct `bl` to either wrapper in the plain stack-argument buffer proof of
the default path (the proofs that also summarise the copy helper, copy_helper_summary_profile).  It
establishes every fact it relies on by executing the pinned bytes on the symbolic Thumb interpreter
below, on every run and on every replay:

* the bodies are the indexed spans with the pinned SHA-256 of `PINS`: the wrapper, func_08005B6C,
  func_08005954, the call thunks _call_via_r2 and _call_via_r3, and the wrapper's callback;
* the interpreter starts at the wrapper's entry with every argument register, every incoming stack
  word, R12, LR and R4-R11 symbolic, follows every path (both ways of each branch its known values
  leave open, joining nothing; a repeated state ends its path), inlines the pinned bodies and the
  callback reached through _call_via_r3, and treats only two calls as opaque: the allocator
  func_08007138 (its result is the fresh allocation) and the zero fill called through _call_via_r2 at
  0x08005984 (it writes only the allocation).  Any other call, encoding or operand refuses;
* it records, for each symbolic entry value, where it is read through (offsets and widths), where it
  is stored in the walked frames, whether it is written through, stored outside the walked frames
  (into the allocation or through an untracked pointer), passed to an opaque call, held in R4-R11 at
  an opaque call, or used as a number (arithmetic or a compare; a halfword or byte of it is only ever
  a number), and where it lies in the walked frames when the wrapper returns;
* it requires: no store to the caller's frame (at or above the wrapper's entry SP); a read of a frame
  word below the entry SP that nothing on the path wrote (or of a released word, or of a word below
  SP at an opaque call) is only copied between frame words, never used; no frame, allocation or
  return address in arithmetic with an unknown; the wrapper's scheduler call passes a descriptor in
  its frame whose word +4 is the parameter block below it; exactly one callback call on every path,
  entered with halfword 0 of its message equal to 0 (the scheduler copies the descriptor and zeroes
  the phase) and the block address in its word +4; the return through the entry LR with SP and
  R4-R11 restored and the same caller-clobbered results on every path.

At a call site the summary then applies these rules (all checked against the walk's state there):

1. the proof has no word-provenance, callee-frame or other summary context, and the site is a direct
   call;
2. a caller-clobbered local address is only in R1 or R2 (never R0, R3, R12 or LR), the wrapper
   stores it only into its parameter block, and its entry value is read through, if at all, only at
   the recorded offsets: each read lies in allocated local words that hold no pointer; it is never
   written through, stored outside the walked frames, passed to an
   opaque call, held in R4-R11 at one or used as a number;
3. every argument word the bodies read is an allocated local word of the caller that holds no
   pointer;
4. a local address in R4-R11 is never read through, written through, stored outside the walked
   frames, held in R4-R11 at an opaque call or used as a number, and is restored at the return;
5. the caller's frame is only read: no fact of it changes;
6. a caller-clobbered register that returns holding a local address (by the derived final values)
   returns as that alias; every other caller-clobbered register is dropped as at any call;
7. every word of the walked frames that holds a local address when the wrapper returns (the block
   words the wrapper stored R1 and R2 into, a saved R4-R7 word, a copied released word) is handed back
   as a released word at its entry-SP offset (forwarded_slot_profile): tracked until written, a walked
   read refuses, later calls are trusted under its premise.  The caller's own released words are given
   to the interpreter as frame words, so a body that read one would refuse.

Every observation and the derived facts of each wrapper are recorded, written as report lines and
bound into the buffer fingerprint; replay derives them again from the ROM.

Premises (``PREMISE``, stated in each report that applies the summary, not proved here): what the
allocator and the zero fill do, that the untracked loads and stores touch no stack word and not the
allocation's callback word, and that the bodies terminate.

`POLICY.enabled = False` leaves every wrapper call to the plain walk (refused as before).
"""
import hashlib
import json

from capstone.arm_const import ARM_REG_FP, ARM_REG_R8, ARM_REG_SB, ARM_REG_SL

import match

NAME = 'pinned-motion-wrapper-summary-v1'
SCHEDULER, SCHEDULER_BODY = 0x08005B6C, 0x08005954
CALL_VIA_R2, CALL_VIA_R3 = 0x0814224C, 0x08142250
ALLOCATOR = 0x08007138
ZERO_FILL_RETURN = 0x08005988      # the instruction after `bl _call_via_r2` in func_08005954
# Each wrapper and the callback its literal must name.
WRAPPERS = {0x080D6238: 0x080D5128, 0x080D6284: 0x080D5594}
CALLBACKS = frozenset(WRAPPERS.values())
PINS = {
    0x080D6238: (76, '0a19a6eb71968e280759110c15b810699187f7780484231d71b15c989e642e89'),
    0x080D6284: (72, '11199779f458bca3aa00fa38a9c4882b275dd91d258532714399b8edf8ff8d3a'),
    SCHEDULER: (60, 'c6a20896e48a2d20f9a4e9d59b780095f5e082b65619a2a96cee0ebc26e8c475'),
    SCHEDULER_BODY: (206, '4e3fba4f8cb6ee77b2d0251866e2f85338ab5550832ce8fc0807b3835b0c677e'),
    0x080D5128: (1132, '7b01f163d5d81228f09b010ac1a4aecf1146acb67c3b05d70ae45178207079d9'),
    0x080D5594: (1228, '2e97c6a2915a1ad6962295afe086cee8597da15e1c13fe16e91078f5a303ea06'),
    CALL_VIA_R2: (2, 'dd9261f0471768edc33bf979649f6297463be423da17c3f881684f5747e163a1'),
    CALL_VIA_R3: (2, '477db9ac7ca5efc12e37f882656b8fe5a363ffeb99b2e565a953d10c3c91ab21'),
}
PREMISE = ('the allocator func_08007138 returns an allocation separate from every stack word, preserves SP and '
           'R4-R11 and touches no stack word at or above its entry SP; the zero fill called through _call_via_r2 '
           'at 0x08005984 writes only that allocation; the untracked loads and stores (through scheduler list '
           'nodes, the manager, the parent and fixed RAM addresses) touch no stack word and not the '
           'allocation\'s callback word; the pinned bodies terminate')
SUMMARY = ('a direct call to a pinned motion-task wrapper, summarised from its pinned bytes and those of the '
           'scheduler and the callback (executed on every run); the caller\'s local addresses are only read '
           'through, inside the recorded offsets, and the words that still hold them below SP are tracked')
MAX_PATHS = 512
MAX_STEPS = 65536
MASK = 0xFFFFFFFF
R0 = match.ARM_REG_R0
R1, R2, R3, R12, LR = R0 + 1, R0 + 2, R0 + 3, match.ARM_REG_R12, match.ARM_REG_LR
# capstone ids of R4-R11 (capstone names R9-R11 SB, SL and FP).
HIGH = {4: R0 + 4, 5: R0 + 5, 6: R0 + 6, 7: R0 + 7, 8: ARM_REG_R8, 9: ARM_REG_SB, 10: ARM_REG_SL, 11: ARM_REG_FP}
REGISTER_NUMBER = {**{R0 + n: n for n in range(4)}, **{reg: n for n, reg in HIGH.items()},
                   R12: 12, match.ARM_REG_SP: 13, LR: 14, match.ARM_REG_PC: 15}


class Policy:
    """The default-path rule's switch: disabled, a wrapper call is walked (and refused) as before."""
    enabled = True


POLICY = Policy()


def require(condition, message):
    if not condition:
        raise ValueError(message)


# ---- symbolic values ------------------------------------------------------------------------
# ('c', n) constant; ('t', name, k) entry value `name` plus k; ('sp', off) address relative to the
# wrapper's entry SP; ('task', off) inside the allocation; ('ret', site) return address of an inlined
# call; ('u',) unknown scalar or untracked pointer; ('g',) uninitialised frame bytes; ('mix', cells)
# frame bytes of several origins; ('rel', key) a released word of the caller; ('part', names) a halfword
# or byte of a value holding the entry values ``names`` (a number, never an address); ('maybe', value) a
# word below SP at an opaque call, which may still hold ``value`` or anything the call left there.
UNKNOWN, GARBAGE = ('u',), ('g',)
WIDTH_MASK = {1: 0xFF, 2: 0xFFFF, 4: MASK}


def constant(value):
    return ('c', value & MASK)


def tags(value):
    """Entry names (and released keys) whose value, or part of it, is in ``value``."""
    if value[0] == 't':
        return {value[1]}
    if value[0] == 'rel':
        return {f'rel:{value[1]}'}
    if value[0] == 'part':
        return set(value[1])
    if value[0] == 'maybe':
        return tags(value[1])
    if value[0] == 'mix':
        found = set()
        for cell in value[1]:
            if cell is not None:
                found |= tags(cell[0])
        return found
    return set()


def opaque_content(value):
    """True for frame bytes that are not one known value: they may only be copied between words."""
    return value[0] in ('g', 'mix', 'rel', 'maybe')


def narrow(value, width):
    """``value`` read back through ``width`` bytes (zero-extended)."""
    if width == 4 or opaque_content(value):
        return value
    if value[0] == 'c':
        return constant(value[1] & WIDTH_MASK[width])
    return ('part', frozenset(tags(value)))


def add(value, delta):
    kind = value[0]
    if kind == 'c':
        return constant(value[1] + delta)
    if kind == 't':
        return ('t', value[1], value[2] + delta)
    if kind in ('sp', 'task'):
        return (kind, value[1] + delta)
    return None


class Facts:
    """What one derivation found, summed over every path."""

    def __init__(self):
        self.reads = {}            # entry name: {(offset, width)} read through it
        self.written = set()       # entry names written through
        self.stored = set()        # entry names stored outside the walked frames
        self.numbers = set()       # entry names used in arithmetic or a compare
        self.opaque = set()        # (site, kind) of the opaque calls
        self.untracked = set()     # sites of loads and stores through untracked pointers or fixed RAM addresses
        self.opaque_live = set()   # entry names in R4-R11 at an opaque call (the callee may save them below SP)
        self.argument_words = 0    # incoming stack words read
        self.callback = set()      # (callback, copy offset) of every callback entry
        self.results = None        # {register number: value} at the wrapper's return, equal on every path
        self.released = {}         # entry-SP offset of a word: {values it may hold at the return}
        self.frame_stores = {}     # entry name: {(body, entry-SP offset, width)} of frame stores holding it
        self.block = set()         # (descriptor, block) at the wrapper's scheduler call: R2 and its word +4
        self.paths = 0


class Derivation:
    """Execute the pinned bodies from the wrapper's entry; ``Facts`` or a refusal."""

    def __init__(self, rom, wrapper, released):
        self.rom, self.wrapper = rom, wrapper
        self.released = tuple(sorted(released))   # entry-SP offsets of the caller's released words
        self.facts = Facts()
        self.decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        self.decoder.detail = True
        self.cache = {}
        self.steps = 0

    def body_of(self, address):
        for start, (size, _) in PINS.items():
            if start <= address < start + size:
                return start
        raise ValueError(f'motion wrapper: 0x{address:08X} is outside the pinned bodies')

    def decode(self, address):
        if address not in self.cache:
            start = self.body_of(address)
            size = PINS[start][0]
            data = self.rom[address - match.ROM_BASE:start + size - match.ROM_BASE]
            found = list(self.decoder.disasm(data[:4], address, count=1))
            require(found and found[0].address == address and address + found[0].size <= start + size,
                    f'motion wrapper: no complete instruction at 0x{address:08X}')
            self.cache[address] = found[0]
        return self.cache[address]

    def rom_word(self, address):
        require(match.ROM_BASE <= address and address + 4 <= match.ROM_BASE + len(self.rom) and address % 4 == 0,
                f'motion wrapper: literal 0x{address:08X} is not a ROM word')
        return int.from_bytes(self.rom[address - match.ROM_BASE:address - match.ROM_BASE + 4], 'little')

    # ---- state: (pc, regs, sp, stack, task, flags, calls, callbacks) ----------------------
    def run(self):
        regs = {n: ('t', f'R{n}', 0) for n in range(4)}
        regs.update({n: ('t', f'S{n}', 0) for n in range(4, 12)})
        regs[12], regs[14] = ('t', 'R12', 0), ('t', 'LR', 0)
        stack = {}
        for position in self.released:
            for index in range(4):
                stack[position + index] = (('rel', position), index, 4)
        start = (self.wrapper, tuple(sorted(regs.items())), 0, tuple(sorted(stack.items())), (), None, (), 0)
        pending, seen = [start], {start}
        while pending:
            state = pending.pop()
            for successor in self.step(state):
                if successor not in seen:
                    seen.add(successor)
                    pending.append(successor)
                    require(len(seen) <= MAX_PATHS * 64, 'motion wrapper: state budget exhausted')
        require(self.facts.paths, 'motion wrapper: no path returns')
        return self.facts

    def step(self, state):
        self.steps += 1
        require(self.steps <= MAX_STEPS, 'motion wrapper: step budget exhausted')
        pc, regs, sp, stack, task, flags, calls, callbacks = state
        regs, stack, task = dict(regs), dict(stack), dict(task)
        ins = self.decode(pc)
        where = f'0x{pc:08X}'
        # Conditional branches are B with a condition (capstone spells them beq, bne, ...).
        mnemonic = 'b' if ins.id == match.ARM_INS_B else ins.mnemonic
        ops = ins.operands
        facts = self.facts
        nxt = pc + ins.size

        def reg(operand):
            require(operand.type == match.ARM_OP_REG, f'motion wrapper: operand at {where}')
            number = REGISTER_NUMBER.get(operand.reg)
            require(number is not None, f'motion wrapper: register at {where}')
            return number

        def get(number):
            if number == 13:
                return ('sp', sp)
            require(number != 15, f'motion wrapper: PC read at {where}')
            return regs[number]

        def put(number, value):
            require(number not in (13, 15), f'motion wrapper: SP or PC write at {where}')
            regs[number] = value

        def number_use(*values):
            for value in values:
                require(not opaque_content(value), f'motion wrapper: uses an uninitialised or released frame word at {where}')
                facts.numbers.update(tags(value))

        def arithmetic(*values):
            """Operands of arithmetic whose result is unknown: never a frame, allocation or return address."""
            number_use(*values)
            for value in values:
                require(value[0] not in ('sp', 'task', 'ret'),
                        f'motion wrapper: a frame, allocation or return address in arithmetic at {where}')

        def frame_load(offset, width):
            if offset >= 0:
                require(offset % 4 == 0 and width == 4, f'motion wrapper: partial argument word read at {where}')
                facts.argument_words = max(facts.argument_words, offset // 4 + 1)
                return ('t', f'W{offset // 4}', 0)
            require(offset + width <= 0, f'motion wrapper: a read straddles the entry SP at {where}')
            cells = [stack.get(offset + index) for index in range(width)]
            first = cells[0]
            if first is not None and first[2] == width and all(
                    cell is not None and cell[0] == first[0] and cell[2] == width and cell[1] == index
                    for index, cell in enumerate(cells)):
                return narrow(first[0], width)
            if all(cell is None for cell in cells):
                return GARBAGE
            return ('mix', tuple(cells))

        def frame_store(offset, width, value):
            require(offset + width <= 0, f'motion wrapper: writes the caller frame at {where}')
            if value[0] == 'c':
                value = constant(value[1] & WIDTH_MASK[width])
            for name in tags(value):
                facts.frame_stores.setdefault(name, set()).add((self.body_of(pc), offset, width))
            if value[0] == 'mix' and len(value[1]) == width:
                for index, cell in enumerate(value[1]):
                    if cell is None:
                        stack.pop(offset + index, None)
                    else:
                        stack[offset + index] = cell
            else:
                for index in range(width):
                    stack[offset + index] = (value, index, width)

        def outside_store(value):
            require(not opaque_content(value),
                    f'motion wrapper: stores an uninitialised or released frame word outside the frames at {where}')
            facts.stored.update(name for name in tags(value) if not name.startswith('rel:'))

        def load(base, disp, width):
            kind = base[0]
            if kind == 'sp':
                return frame_load(base[1] + disp, width)
            if kind == 'task':
                held = task.get(base[1] + disp)
                return narrow(held[0], width) if held is not None and held[1] == width else UNKNOWN
            if kind == 't':
                facts.reads.setdefault(base[1], set()).add((base[2] + disp, width))
                return UNKNOWN
            if kind == 'u':
                facts.untracked.add(pc)
                return UNKNOWN
            if kind == 'c':
                address = base[1] + disp
                if match.ROM_BASE <= address < match.ROM_BASE + len(self.rom):
                    require(width == 4, f'motion wrapper: narrow ROM read at {where}')
                    return constant(self.rom_word(address))
                facts.untracked.add(pc)
                return UNKNOWN
            raise ValueError(f'motion wrapper: load through an unsupported base at {where}')

        def store(base, disp, width, value):
            kind = base[0]
            if kind == 'sp':
                frame_store(base[1] + disp, width, value)
            elif kind == 'task':
                outside_store(value)
                if value[0] == 'c':
                    value = constant(value[1] & WIDTH_MASK[width])
                for key in [key for key in task if key < base[1] + disp + width and key + task[key][1] > base[1] + disp]:
                    del task[key]
                task[base[1] + disp] = (value, width)
            elif kind == 't':
                facts.written.add(base[1])
                outside_store(value)
            elif kind == 'u':
                facts.untracked.add(pc)
                outside_store(value)
            else:
                raise ValueError(f'motion wrapper: store through an unsupported base at {where}')

        def address_base(value):
            require(not opaque_content(value), f'motion wrapper: uses an uninitialised or released frame word at {where}')
            return value

        def memory(operand):
            require(operand.type == match.ARM_OP_MEM, f'motion wrapper: memory operand at {where}')
            mem = operand.mem
            number = REGISTER_NUMBER.get(mem.base)
            require(number is not None, f'motion wrapper: memory base at {where}')
            disp = mem.disp
            if mem.index:
                index = get(REGISTER_NUMBER[mem.index])
                require(index[0] == 'c', f'motion wrapper: register-indexed access at {where}')
                disp += index[1]
            if number == 15:
                return ('pc', ((pc + 4) & ~3) + disp)
            return (address_base(get(number)), disp)

        def finish(target):
            """A return or jump to ``target``: the successor states."""
            if target[0] == 'ret':
                require(calls and calls[-1] == target[1], f'motion wrapper: unbalanced return at {where}')
                return [(target[1], regs, calls[:-1])]
            if target == ('t', 'LR', 0) and not calls:
                self.wrapper_return(regs, sp, stack, callbacks)
                return []
            if pc == CALL_VIA_R2 and calls and calls[-1] == ZERO_FILL_RETURN and target[0] in ('c', 'u'):
                # The zero fill, reached through a function pointer the pinned body loads: opaque.
                opaque('zero fill' + (f' 0x{target[1]:08X}' if target[0] == 'c' else ''))
                task.clear()
                return [(ZERO_FILL_RETURN, regs, calls[:-1])]
            if target[0] == 'c':
                destination = target[1] & ~1
                require(target[1] & 1 and destination in CALLBACKS and pc == CALL_VIA_R3,
                        f'motion wrapper: indirect jump to 0x{target[1]:08X} at {where}')
                require(callbacks == 0, f'motion wrapper: a second callback call at {where}')
                return [(destination, regs, calls, 'callback')]
            raise ValueError(f'motion wrapper: unproved indirect branch at {where}')

        def opaque(kind):
            for number in range(4):
                value = regs[number]
                require(not opaque_content(value), f'motion wrapper: an uninitialised or released word reaches an '
                                                   f'opaque call at {where}')
                facts.stored.update(name for name in tags(value) if not name.startswith('rel:'))
            for number in range(4, 12):
                facts.opaque_live.update(name for name in tags(regs[number]) if not name.startswith('rel:'))
            # The callee's own frame lies below SP: a word there may be overwritten, and one that held an
            # entry value may still hold it, so it is kept for the released words but can no longer be used.
            for offset in [offset for offset in stack if offset < sp]:
                value, index, width = stack[offset]
                if tags(value):
                    stack[offset] = (value if value[0] == 'maybe' else ('maybe', value), index, width)
                else:
                    del stack[offset]
            facts.opaque.add((calls[-1] - 4 if kind.startswith('zero fill') else pc, kind))
            for number in (1, 2, 3, 12, 14):
                regs[number] = UNKNOWN
            regs[0] = ('task', 0) if kind == 'allocator' else UNKNOWN

        out = []
        # The flags after this instruction: unchanged unless it sets them (then unknown, or a compare's).
        result_flags = [flags if mnemonic in ('b', 'bx', 'push', 'pop', 'ldr', 'ldrh', 'ldrb', 'str', 'strh', 'strb',
                                              'ldm', 'ldmia', 'stm', 'stmia', 'mov', 'add', 'sub') else None]

        def go(target_pc, new_regs=None, new_calls=None, callback=False):
            out.append((target_pc, tuple(sorted((new_regs if new_regs is not None else regs).items())), sp,
                        tuple(sorted(stack.items())), tuple(sorted(task.items())), result_flags[0],
                        calls if new_calls is None else new_calls, callbacks + (1 if callback else 0)))

        if mnemonic == 'push':
            values = [get(reg(o)) for o in ops]
            order = sorted(range(len(ops)), key=lambda i: reg(ops[i]))
            sp -= 4 * len(ops)
            for slot, i in enumerate(order):
                frame_store(sp + 4 * slot, 4, values[i])
            go(nxt)
        elif mnemonic == 'pop':
            numbers = sorted(reg(o) for o in ops)
            loaded = [frame_load(sp + 4 * slot, 4) for slot in range(len(numbers))]
            sp += 4 * len(numbers)
            target = None
            for number, value in zip(numbers, loaded):
                if number == 15:
                    target = value
                else:
                    put(number, value)
            if target is None:
                go(nxt)
            else:
                for successor in finish(target):
                    go(successor[0], successor[1], successor[2], callback=len(successor) > 3)
        elif mnemonic in ('mov', 'movs') and len(ops) == 2:
            if ops[1].type == match.ARM_OP_IMM:
                put(reg(ops[0]), constant(ops[1].imm))
            else:
                require(not ops[1].shift.type or not ops[1].shift.value, f'motion wrapper: shifted move at {where}')
                source = get(reg(ops[1]))
                put(reg(ops[0]), source)
            go(nxt)
        elif mnemonic in ('adds', 'subs', 'add', 'sub'):
            sign = -1 if mnemonic.startswith('sub') else 1
            if len(ops) == 2 and ops[0].type == match.ARM_OP_REG and ops[0].reg == match.ARM_REG_SP:
                require(ops[1].type == match.ARM_OP_IMM, f'motion wrapper: SP adjustment at {where}')
                sp += sign * ops[1].imm
                require(sp <= 0, f'motion wrapper: SP rises above the entry at {where}')
                go(nxt)
            else:
                destination = reg(ops[0])
                left = get(reg(ops[1 if len(ops) == 3 else 0]))
                right_operand = ops[-1]
                right = constant(right_operand.imm) if right_operand.type == match.ARM_OP_IMM else get(reg(right_operand))
                if right[0] == 'c':
                    result = add(left, sign * right[1]) if not opaque_content(left) else None
                elif left[0] == 'c' and sign > 0:
                    result = add(right, left[1]) if not opaque_content(right) else None
                else:
                    result = None
                if result is None:
                    arithmetic(left, right)
                    result = UNKNOWN
                put(destination, result)
                go(nxt)
        elif mnemonic in ('lsls', 'lsrs', 'asrs', 'eors', 'ands', 'orrs', 'bics', 'mvns', 'negs', 'muls'):
            destination = reg(ops[0])
            operand = lambda o: get(reg(o)) if o.type == match.ARM_OP_REG else constant(o.imm)
            require(len(ops) in (2, 3), f'motion wrapper: operand count at {where}')
            if mnemonic in ('mvns', 'negs'):
                require(len(ops) == 2, f'motion wrapper: operand count at {where}')
                values = [operand(ops[1])]
            elif len(ops) == 2:
                # Two-operand forms: Rd = Rd op Rm (a shift by register shifts Rd by Rm).
                values = [get(destination), operand(ops[1])]
            else:
                values = [operand(ops[1]), operand(ops[2])]
            if all(value[0] == 'c' for value in values):
                a = values[0][1]
                b = values[1][1] & 0xFF if len(values) > 1 else 0
                signed = a - (1 << 32) if a & (1 << 31) else a
                # Capstone gives an immediate LSR or ASR #32 as 32; a shift by register uses the low byte.
                result = {'lsls': lambda: a << b if b < 32 else 0, 'lsrs': lambda: a >> b if b < 32 else 0,
                          'asrs': lambda: signed >> min(b, 31),
                          'eors': lambda: a ^ values[1][1], 'ands': lambda: a & values[1][1],
                          'orrs': lambda: a | values[1][1], 'bics': lambda: a & ~values[1][1],
                          'mvns': lambda: ~a, 'negs': lambda: -a, 'muls': lambda: a * values[1][1]}[mnemonic]()
                put(destination, constant(result))
            else:
                arithmetic(*values)
                put(destination, UNKNOWN)
            go(nxt)
        elif mnemonic in ('cmp', 'cmn', 'tst'):
            left = get(reg(ops[0]))
            right = constant(ops[1].imm) if ops[1].type == match.ARM_OP_IMM else get(reg(ops[1]))
            number_use(left, right)
            result_flags[0] = (mnemonic, left, right) if mnemonic == 'cmp' and left[0] == right[0] == 'c' else None
            go(nxt)
        elif mnemonic in ('ldr', 'ldrh', 'ldrb', 'str', 'strh', 'strb'):
            width = 4 if mnemonic in ('ldr', 'str') else 2 if mnemonic.endswith('h') else 1
            require(len(ops) == 2 and not ins.writeback, f'motion wrapper: memory form at {where}')
            target = memory(ops[1])
            if target[0] == 'pc':
                require(mnemonic == 'ldr', f'motion wrapper: PC-relative store at {where}')
                put(reg(ops[0]), constant(self.rom_word(target[1])))
            elif mnemonic.startswith('ldr'):
                put(reg(ops[0]), load(target[0], target[1], width))
            else:
                store(target[0], target[1], width, get(reg(ops[0])))
            go(nxt)
        elif mnemonic in ('ldm', 'ldmia', 'stm', 'stmia'):
            require(ins.writeback, f'motion wrapper: block transfer without writeback at {where}')
            base_number = reg(ops[0])
            base = address_base(get(base_number))
            numbers = sorted(reg(o) for o in ops[1:])
            require(base_number not in numbers, f'motion wrapper: block transfer of its base at {where}')
            for slot, number in enumerate(numbers):
                if mnemonic.startswith('ldm'):
                    put(number, load(base, 4 * slot, 4))
                else:
                    store(base, 4 * slot, 4, get(number))
            put(base_number, add(base, 4 * len(numbers)) or UNKNOWN)
            go(nxt)
        elif mnemonic == 'b':
            require(len(ops) == 1 and ops[0].type == match.ARM_OP_IMM, f'motion wrapper: branch form at {where}')
            taken = ops[0].imm
            if ins.cc in (match.ARM_CC_AL, match.ARM_CC_INVALID):
                go(taken)
            else:
                decided = condition(ins.cc, flags)
                if decided is None:
                    go(taken)
                    go(nxt)
                else:
                    go(taken if decided else nxt)
        elif mnemonic == 'bl':
            require(len(ops) == 1 and ops[0].type == match.ARM_OP_IMM, f'motion wrapper: call form at {where}')
            target = ops[0].imm
            regs[14] = ('ret', nxt)
            if target == ALLOCATOR:
                opaque('allocator')
                go(nxt)
            else:
                require(target in PINS and target not in WRAPPERS, f'motion wrapper: call to unpinned 0x{target:08X} at {where}')
                if target == SCHEDULER:
                    require(self.body_of(pc) == self.wrapper and not calls,
                            f'motion wrapper: the scheduler is called from outside the wrapper at {where}')
                    descriptor = regs[2]
                    require(descriptor[0] == 'sp', f'motion wrapper: the descriptor is not in the wrapper frame at {where}')
                    facts.block.add((descriptor[1], frame_load(descriptor[1] + 4, 4)))
                require(len(calls) < 8, f'motion wrapper: calls nest too deep at {where}')
                go(target, new_calls=calls + (nxt,))
        elif mnemonic == 'bx':
            for successor in finish(get(reg(ops[0]))):
                go(successor[0], successor[1], successor[2], callback=len(successor) > 3)
        else:
            raise ValueError(f'motion wrapper: unsupported instruction {mnemonic} {ins.op_str} at {where}')
        return [self.enter_callback(state) if state[0] in CALLBACKS and pc == CALL_VIA_R3 else state
                for state in out]

    def enter_callback(self, state):
        """The callback entry: halfword 0 of the message (R1) is 0 (the phase); record where the copy is."""
        pc, regs, sp, stack, task, flags, calls, callbacks = state
        values = dict(regs)
        message = values[1]
        require(message[0] == 'sp' and message[1] % 4 == 0, 'motion wrapper: the callback message is not a frame copy')
        stack_map = dict(stack)
        phase = [stack_map.get(message[1] + index) for index in range(2)]
        require(all(cell is not None and cell[0] == ('c', 0) and cell[2] == 2 and cell[1] == index
                    for index, cell in enumerate(phase)), 'motion wrapper: the callback is entered with a nonzero phase')
        copied = [stack_map.get(message[1] + 4 + index) for index in range(4)]
        require(all(cell is not None and cell[2] == 4 and cell[1] == index and cell[0] == copied[0][0]
                    for index, cell in enumerate(copied)), 'motion wrapper: the message copy holds no block address')
        self.facts.callback.add((pc, message[1], copied[0][0]))
        return state

    def wrapper_return(self, regs, sp, stack, callbacks):
        facts = self.facts
        require(sp == 0, 'motion wrapper: SP is not restored at the return')
        require(callbacks == 1, 'motion wrapper: a path returns without exactly one callback call')
        for number in range(4, 12):
            require(regs[number] == ('t', f'S{number}', 0), f'motion wrapper: R{number} is not restored at the return')
        results = {}
        for number in (0, 1, 2, 3, 12):
            value = regs[number]
            require(not opaque_content(value), 'motion wrapper: returns an uninitialised or released frame word')
            results[number] = value
        require(facts.results is None or facts.results == results,
                'motion wrapper: the caller-clobbered results differ between paths')
        facts.results = results
        words = {}
        for offset, cell in stack.items():
            for name in tags(cell[0]):
                words.setdefault(offset - offset % 4, set()).add(name)
        for word, names in words.items():
            cells = [stack.get(word + index) for index in range(4)]
            value = cells[0][0] if cells[0] is not None else None
            whole = value is not None and all(cell is not None and cell[0] == value and cell[1] == index and cell[2] == 4
                                              for index, cell in enumerate(cells))
            facts.released.setdefault(word, set()).add(value if whole else ('mix', tuple(cells)))
        facts.paths += 1
        require(facts.paths <= MAX_PATHS, 'motion wrapper: path budget exhausted')


def condition(cc, flags):
    """The outcome of a conditional branch under known compare flags, or None."""
    if flags is None:
        return None
    _, left, right = flags
    a, b = left[1], right[1]
    result = (a - b) & MASK
    n, z = bool(result & (1 << 31)), result == 0
    c = a >= b
    v = bool(((a ^ b) & (a ^ result)) & (1 << 31))
    table = {match.ARM_CC_EQ: z, match.ARM_CC_NE: not z, match.ARM_CC_HS: c, match.ARM_CC_LO: not c,
             match.ARM_CC_MI: n, match.ARM_CC_PL: not n, match.ARM_CC_VS: v, match.ARM_CC_VC: not v,
             match.ARM_CC_HI: c and not z, match.ARM_CC_LS: not c or z, match.ARM_CC_GE: n == v,
             match.ARM_CC_LT: n != v, match.ARM_CC_GT: not z and n == v, match.ARM_CC_LE: z or n != v}
    require(cc in table, 'motion wrapper: unsupported branch condition')
    return table[cc]


def describe(value):
    kind = value[0]
    if kind == 'c':
        return f'0x{value[1]:X}'
    if kind == 't':
        return value[1] + (f'{value[2]:+d}' if value[2] else '')
    if kind == 'sp':
        return f'entry-SP{value[1]:+d}'
    if kind == 'task':
        return f'allocation{value[1]:+d}'
    if kind == 'rel':
        return f'released entry-SP{value[1]:+d}'
    if kind == 'mix':
        return f"mixed({','.join(sorted(tags(value))) or 'no entry value'})"
    if kind == 'part':
        return f"part({','.join(sorted(value[1])) or 'no entry value'})"
    if kind == 'maybe':
        return f'maybe({describe(value[1])})'
    return {'u': 'unknown', 'g': 'uninitialised'}.get(kind, kind)


def facts_record(wrapper, facts, released_in):
    """The derived facts, as recorded in the evidence (JSON-ready, canonical)."""
    callback, copy, block = sorted(facts.callback)[0]
    (descriptor, wrapper_block), = facts.block
    return dict(
        wrapper=wrapper, callback=callback, copy=copy, descriptor=descriptor, block=describe(wrapper_block),
        frame_stores=sorted([name, sorted([f'0x{body:08X}', offset, width] for body, offset, width in places)]
                            for name, places in facts.frame_stores.items() if name in ('R1', 'R2')),
        bodies=sorted([f'0x{address:08X}', size, sha] for address, (size, sha) in PINS.items()
                      if address in (wrapper, callback, SCHEDULER, SCHEDULER_BODY, CALL_VIA_R2, CALL_VIA_R3)),
        reads=sorted([name, sorted([offset, width] for offset, width in pairs)] for name, pairs in facts.reads.items()),
        written=sorted(facts.written), stored=sorted(facts.stored), numbers=sorted(facts.numbers),
        argument_words=facts.argument_words,
        opaque=sorted([site, kind] for site, kind in facts.opaque),
        untracked=sorted(facts.untracked), opaque_live=sorted(facts.opaque_live),
        results=sorted([number, describe(value)] for number, value in facts.results.items()),
        released=sorted([offset, ' | '.join(sorted(describe(value) for value in values))]
                        for offset, values in facts.released.items()),
        released_in=sorted(released_in), paths=facts.paths)


class MotionSummaries:
    """The motion-wrapper summaries of one plain buffer proof: derivations and sites."""

    def __init__(self, rom, mapping):
        require(all(type(value) is bytes for value in (rom, mapping)),
                'motion summaries require immutable ROM and mapping snapshots')
        self.rom, self.mapping = rom, mapping
        self.derived = {}          # (wrapper, released offsets): (Facts, record)
        self.observations = {}

    @staticmethod
    def covers(address, arguments):
        """A call to a pinned wrapper with a local alias in R1 or R2, which the walk always refuses."""
        return POLICY.enabled and address in WRAPPERS and (R1 in arguments or R2 in arguments)

    def bodies(self, proof, wrapper):
        for address in (wrapper, WRAPPERS[wrapper], SCHEDULER, SCHEDULER_BODY, CALL_VIA_R2, CALL_VIA_R3):
            size, sha = PINS[address]
            body = self.rom[address - match.ROM_BASE:address - match.ROM_BASE + size]
            require(len(body) == size and hashlib.sha256(body).hexdigest() == sha,
                    f'the body at 0x{address:08X} differs from the pinned motion-task body')
            require(proof.span(address) == body, f'the mapped span at 0x{address:08X} is not the pinned body')
            proof.dependencies[address] = body

    def derive(self, proof, wrapper, released):
        key = (wrapper, released)
        if key not in self.derived:
            self.bodies(proof, wrapper)
            facts = Derivation(self.rom, wrapper, released).run()
            require(facts.callback and {entry[0] for entry in facts.callback} == {WRAPPERS[wrapper]} and
                    len(facts.callback) == 1, 'the callback reached is not the wrapper\'s pinned callback')
            require(len(facts.block) == 1, 'the wrapper calls the scheduler with differing descriptors')
            (descriptor, block), = facts.block
            (_, _, copied), = facts.callback
            require(block[0] == 'sp' and block[1] < descriptor and copied == block,
                    'the callback\'s message does not address the wrapper\'s parameter block')
            self.derived[key] = (facts, facts_record(wrapper, facts, released))
        self.bodies(proof, wrapper)
        return self.derived[key]

    def call(self, proof, address, arguments, stack, incoming, protected, aliases, *, site, words):
        """Apply the summary inside BufferCallProof.check_call."""
        try:
            require(proof.motion_summaries is self and proof.stack_arguments and not words and not (
                proof.word_provenance or proof.callee_frames or proof.single_word_stores or
                proof.forwarded_stack_arguments and not proof.default_forwarding or
                proof.exact_alias_state_budget is not None or
                proof.bios_fill_proof is not None or proof.discarded_exit_scratch is not None or
                proof.runtime_summaries is not None),
                'motion summary excludes word-provenance, callee-frame and other summary contexts')
            require(type(site) is int, 'motion summary requires an actual direct call site')
            released_keys = match.stale_words(arguments)          # {entry-SP offset: key}
            released = {position: arguments[key] for position, key in released_keys.items()}
            owner = {register: offset for register, offset in arguments.items()
                     if register not in released_keys.values()}
            if released:
                require(proof.default_forwarding, 'released forwarded words reach only the default forwarding proofs')
            require(set(owner) <= {R1, R2}, 'motion summary admits a local address only in R1 and R2')
            for offset in (*owner.values(), *incoming.values()):
                proof.validate_pointer_value(offset, stack)
            facts, record = self.derive(proof, address, tuple(sorted(released)))
            for position in incoming:
                require(position >= 4 * facts.argument_words,
                        'a pointer-bearing local word is an argument word the motion wrapper reads')
            for position in range(0, 4 * facts.argument_words, 4):
                # Each argument word read is a local word the caller allocated, never a saved register.
                proof.access(position - 4 * len(stack), 4, stack)
            names = {f'R{register - R0}': offset for register, offset in owner.items()}
            for number, register in HIGH.items():
                if register in aliases:
                    names[f'S{number}'] = aliases[register]
            reads = {name: sorted(pairs) for name, pairs in facts.reads.items()}
            for name, offset in names.items():
                require(name not in facts.written and name not in facts.stored and name not in facts.numbers,
                        f'the local address in {name} is written through, kept or used as a number')
                require(name not in facts.opaque_live,
                        f'the local address in {name} is in a callee-saved register at an opaque call')
                if name.startswith('S'):
                    require(name not in facts.reads, f'the local address in {name} is read through')
                else:
                    # The wrapper stores R1 and R2 only into its parameter block, the words below its descriptor.
                    (descriptor, block), = facts.block
                    for body, place, size in facts.frame_stores.get(name, ()):
                        require(body == address and size == 4 and block[1] <= place < descriptor,
                                f'the local address in {name} is stored outside the wrapper\'s parameter block')
                for delta, width in reads.get(name, ()):
                    # Each read lies in allocated local words (never a saved register) holding no pointer.
                    start = offset + delta
                    proof.access(start, width, stack)
                    require(not any(start < slot + 4 and start + width > slot for slot in protected),
                            f'a read through {name} overlaps a pointer-bearing word')
            # Entry values that hold a local address: the caller's names and its released words.
            holders = dict(names)
            holders.update({f'rel:{position}': value for position, value in released.items()})
            result = {}
            for number, value in facts.results.items():
                found = tags(value) & set(holders)
                if found:
                    require(value[0] == 't', 'a caller-clobbered result holds part of a local address')
                    result[R0 + number if number < 4 else R12] = holders[value[1]] + value[2]
            for position, values in facts.released.items():
                if not any(tags(value) & set(holders) for value in values):
                    continue
                require(len(values) == 1, 'a word below SP may hold a local address on only some paths')
                value, = values
                if value[0] == 'maybe':
                    value = value[1]          # it may still hold the value: tracked as if it does
                require(value[0] in ('t', 'rel'), 'a word below SP holds part of a local address at the return')
                held = holders[value[1]] + value[2] if value[0] == 't' else holders[f'rel:{value[1]}']
                result[match.FORWARD_STALE_BASE + position] = held
            observation = dict(site=site, wrapper=address, frame_bytes=4 * len(stack),
                               owner=sorted([name, offset] for name, offset in names.items()),
                               incoming=sorted([position, target] for position, target in incoming.items()),
                               released_in=sorted([position, value] for position, value in released.items()),
                               returned=sorted([key, value] for key, value in result.items()),
                               facts_sha256=hashlib.sha256(canonical(record).encode()).hexdigest())
            self.observations[canonical(observation)] = observation
        except ValueError as error:
            raise ValueError(f'buffer callee 0x{address:08X}: {error}') from error
        return proof.word_result(result, {})

    def snapshot(self):
        return dict(self.observations)

    def restore(self, saved):
        self.observations.clear()
        self.observations.update(saved)

    def evidence(self):
        used = {(record['wrapper'], tuple(position for position, _ in record['released_in']))
                for record in self.observations.values()}
        return dict(policy=NAME, premise=PREMISE,
                    facts=[self.derived[key][1] for key in sorted(used)],
                    observations=[self.observations[key] for key in sorted(self.observations)])

    def lines(self):
        """The report lines: one per derivation used, one per site, and the premise; none when unused."""
        if not self.observations:
            return []
        evidence = self.evidence()
        out = [f'* buffer motion wrapper: `{NAME}`: {SUMMARY}']
        for facts in evidence['facts']:
            reads = '; '.join(f'{name} read at ' + ' '.join(f'+{offset}:{width}' for offset, width in pairs)
                              for name, pairs in facts['reads'])
            out.append(
                f"* buffer motion wrapper facts: 0x{facts['wrapper']:08X} callback 0x{facts['callback']:08X} "
                f"(message copy at entry-SP{facts['copy']:+d}, phase 0, one call on each of {facts['paths']} paths); "
                f"bodies {' '.join(f'{address}:{sha[:16]}' for address, _, sha in facts['bodies'])}; "
                f"{reads or 'nothing read through an entry value'}; written through {' '.join(facts['written']) or 'none'}; "
                f"kept outside the frames {' '.join(facts['stored']) or 'none'}; used as numbers "
                f"{' '.join(facts['numbers']) or 'none'}; argument words {facts['argument_words']}; "
                f"opaque {' '.join(f'0x{site:08X}:{kind}' for site, kind in facts['opaque']) or 'none'} "
                f"(callee-saved there: {' '.join(facts['opaque_live']) or 'none'}); "
                f"untracked accesses at {' '.join(f'0x{site:08X}' for site in facts['untracked']) or 'none'}; "
                f"results {' '.join(f'r{number}={value}' for number, value in facts['results'])}; "
                f"words below SP {' '.join(f'entry-SP{offset:+d}={value}' for offset, value in facts['released']) or 'none'}"
                + (f"; caller released words at {' '.join(f'entry-SP{position:+d}' for position in facts['released_in'])}"
                   if facts['released_in'] else ''))
        for record in evidence['observations']:
            frame = record['frame_bytes']
            owner = ' '.join(f'{name}=sp{offset + frame:+d}' for name, offset in record['owner'])
            returned = ' '.join(
                (f'released entry-SP{key - match.FORWARD_STALE_BASE:+d}' if key < match.FORWARD_STALE_BASE // 2
                 else f'r{key - R0 if key != R12 else 12}') + f'=sp{value + frame:+d}' for key, value in record['returned'])
            out.append(f"* buffer motion wrapper site: 0x{record['wrapper']:08X} at 0x{record['site']:08X}: "
                       f"local addresses {owner}; returns {returned or 'none'}; pointer words passed "
                       f"{len(record['incoming'])}; facts {record['facts_sha256'][:16]}")
        out.append(f'* buffer motion wrapper premise: {PREMISE}')
        return out


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))
