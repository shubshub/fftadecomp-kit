"""Bounded conditional diagnostics; never MATCH or replay evidence."""

import argparse
import copy
from dataclasses import asdict, dataclass
import hashlib
import json
from pathlib import Path

from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
from capstone.arm_const import ARM_OP_IMM, ARM_OP_MEM, ARM_OP_REG


ROM_BASE = 0x08000000
VERSION = 'engine-cutpoints-diagnostic-v2'
REGISTER_NAMES = tuple(f'r{number}' for number in range(13)) + ('sp', 'lr')
HARD_LIMITS = {'steps': 128, 'states': 4, 'calls': 1, 'memory_bytes': 256, 'events': 64}
COMMON_PREMISES = ('live declared regions', 'no asynchronous memory writes',
                   'complete protected caller ranges')
COPY_OBLIGATIONS = (
    'Entry descriptor values and masks survived earlier allocator, clear and list writes.',
    'Execution reaches this copy cutpoint with the supplied live frames.',
    'Later task, list and callback writes preserve descriptor and control storage.',
    'C representation, effective types, function types and lifetimes are not checked.',
)
KILL_OBLIGATIONS = (
    'The allocator suffix returns and satisfies any allocation contract.',
    'Allocation extent, freshness and separation are not established.',
    'Suffix memory effects, register effects and preservation of the engine r9 alias are unproved.',
    'Later clear, list, callback and runtime-image effects are not checked.',
)


@dataclass(frozen=True)
class Fragment:
    origin: str
    index: int
    offset: int = 0


@dataclass(frozen=True)
class ByteState:
    defined: bool
    value: int | None = None
    symbol: str | None = None
    fragments: tuple[Fragment, ...] = ()


@dataclass(frozen=True)
class Interval:
    name: str
    start: int
    end: int


@dataclass(frozen=True)
class Region:
    name: str
    start: int
    data: tuple[ByteState, ...]
    readable: bool = True
    writable: bool = True


@dataclass(frozen=True)
class Context:
    registers: dict[str, tuple[ByteState, ...]]
    flags: dict[str, int | None]
    regions: tuple[Region, ...]
    protected: tuple[Interval, ...]
    frames: tuple[Interval, ...]
    premises: tuple[str, ...]


class Unsupported(ValueError):
    pass


class NotEstablished(ValueError):
    pass


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False).encode()


def digest(value):
    return hashlib.sha256(value).hexdigest()


def constant(value, origin=None, offset=0):
    if type(value) is not int or not 0 <= value <= 0xFFFFFFFF:
        raise Unsupported('constant is not a 32-bit integer')
    return tuple(ByteState(True, (value >> (8 * index)) & 255, None,
                           (Fragment(origin, index, offset),) if origin else ())
                 for index in range(4))


def unknown_word(name, origin=None):
    return tuple(ByteState(True, None, f'{name}:{index}',
                           (Fragment(origin, index),) if origin else ())
                 for index in range(4))


def integer(word):
    if all(part.defined and part.value is not None for part in word):
        return sum(part.value << (8 * index) for index, part in enumerate(word))
    return None


def required_integer(word):
    value = integer(word)
    if value is None:
        raise Unsupported('unresolved address or integer value')
    return value


def interval_end(start, length):
    if type(start) is not int or type(length) is not int or length <= 0 or \
            not 0 <= start < start + length <= 0x100000000:
        raise Unsupported('invalid or wrapping interval')
    return start + length


def overlaps(start, end, other_start, other_end):
    return start < other_end and other_start < end


def address_offset(word, amount):
    original = required_integer(word)
    value = original + amount
    if not 0 <= value <= 0xFFFFFFFF:
        raise Unsupported('address arithmetic wraps')
    if not any(part.fragments for part in word):
        return constant(value)
    first = word[0].fragments
    if len(first) != 1 or any(part.fragments != (Fragment(first[0].origin, index, first[0].offset),)
                              for index, part in enumerate(word)):
        raise Unsupported('arithmetic cannot reconstruct partial alias fragments')
    return constant(value, first[0].origin, first[0].offset + amount)


def check_byte(part):
    if not isinstance(part, ByteState) or type(part.defined) is not bool or \
            part.value is not None and (type(part.value) is not int or not 0 <= part.value <= 255) or \
            part.symbol is not None and (not isinstance(part.symbol, str) or not part.symbol) or \
            not isinstance(part.fragments, tuple):
        raise Unsupported('invalid byte state')
    for fragment in part.fragments:
        if not isinstance(fragment, Fragment) or not isinstance(fragment.origin, str) or \
                not fragment.origin or type(fragment.index) is not int or not 0 <= fragment.index < 4 or \
                type(fragment.offset) is not int:
            raise Unsupported('invalid alias fragment')


class _Cutpoint:
    def __init__(self, rom, mapping, entry_pc, exit_pc, context, limits, kind):
        if type(rom) is not bytes or type(mapping) is not bytes:
            raise Unsupported('ROM and map must be immutable byte snapshots')
        if not isinstance(context, Context):
            raise Unsupported('explicit Context required')
        if set(limits) != set(HARD_LIMITS) or any(type(value) is not int or
                not 0 <= value <= HARD_LIMITS[name] for name, value in limits.items()):
            raise Unsupported('invalid finite limits')
        if any(type(address) is not int or address % 2 for address in (entry_pc, exit_pc)):
            raise Unsupported('aligned Thumb cutpoints required')
        self.rom, self.mapping, self.kind = rom, mapping, kind
        self.entry_pc, self.exit_pc, self.pc = entry_pc, exit_pc, entry_pc
        self.context, self.limits = copy.deepcopy(context), dict(limits)
        self.registers = dict(self.context.registers)
        self.flags = dict(self.context.flags)
        self.events, self.trace, self.dependencies, self.calls = [], [], {}, []
        self.memory, self.visited = {}, set()
        self.killed = False
        self.entries = json.loads(mapping)
        if not isinstance(self.entries, list):
            raise Unsupported('map must be a function list')
        self.decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
        self.decoder.detail = True
        self._validate_context()
        self.containing = self._span(entry_pc)
        self.initial_memory = dict(self.memory)
        self.initial_registers = dict(self.registers)
        self.initial_flags = dict(self.flags)
        self.initial_sp = required_integer(self.registers['sp'])
        self.call_frames = [{'entry_pc': entry_pc, 'entry_sp': self.initial_sp,
                             'current_sp': self.initial_sp, 'saved_slots': [], 'locals': []}]
        self.states = 1
        self.steps = 0
        self._budget()

    def _validate_context(self):
        context = self.context
        if set(context.registers) != set(REGISTER_NAMES) or set(context.flags) != set('NZCV'):
            raise Unsupported('complete entry register and NZCV facts required')
        for word in context.registers.values():
            if not isinstance(word, tuple) or len(word) != 4:
                raise Unsupported('register must have four byte states')
            for part in word:
                check_byte(part)
        if any(value is not None and (type(value) is not int or value not in (0, 1))
               for value in context.flags.values()):
            raise Unsupported('invalid entry flags')
        if not isinstance(context.premises, tuple) or len(set(context.premises)) != len(context.premises) or \
                not set(COMMON_PREMISES) <= set(context.premises):
            raise Unsupported('missing explicit entry premises')
        if not context.protected or not context.frames:
            raise Unsupported('protected caller intervals and frame ownership required')
        if sum(len(region.data) for region in context.regions) > self.limits['memory_bytes']:
            raise Unsupported('memory_bytes budget exhausted')
        names = set()
        for region in context.regions:
            if not isinstance(region, Region) or not isinstance(region.name, str) or \
                    not region.name or region.name in names or not isinstance(region.data, tuple) or \
                    type(region.readable) is not bool or type(region.writable) is not bool:
                raise Unsupported('invalid region')
            names.add(region.name)
            end = interval_end(region.start, len(region.data))
            for address, part in enumerate(region.data, region.start):
                check_byte(part)
                if address in self.memory:
                    raise Unsupported('overlapping declared memory regions')
                self.memory[address] = part
            for protected in context.protected:
                if not isinstance(protected, Interval):
                    raise Unsupported('invalid protected interval')
                interval_end(protected.start, protected.end - protected.start)
                if overlaps(region.start, end, protected.start, protected.end):
                    raise Unsupported('tracked region overlaps protected saved/control bytes')
        for frame in context.frames:
            if not isinstance(frame, Interval) or not frame.name:
                raise Unsupported('invalid frame ownership')
            interval_end(frame.start, frame.end - frame.start)
        for region in context.regions:
            owners = [frame for frame in context.frames
                      if frame.start <= region.start and region.start + len(region.data) <= frame.end]
            if len(owners) != 1:
                raise Unsupported('tracked region needs one explicit frame owner')

    def _span(self, address, exact=False):
        entries = []
        for entry in self.entries:
            start, end = int(entry['rom'], 16), int(entry['end'], 16)
            if start <= address < end:
                entries.append((entry, start, end))
        if len(entries) != 1:
            raise Unsupported('mapped code must have a unique nonoverlapping containing span')
        entry, start, end = entries[0]
        if entry.get('mode') != 'thumb' or start % 2 or end % 2 or \
                not ROM_BASE <= start < end <= ROM_BASE + len(self.rom) or exact and address != start:
            raise Unsupported('complete aligned Thumb ROM span required')
        if any(int(other['rom'], 16) < end and int(other['end'], 16) > start
               for other in self.entries if other is not entry):
            raise Unsupported('dependency span overlaps another mapping')
        self.dependencies[start] = {'start': start, 'end': end,
                                   'sha256': digest(self.rom[start-ROM_BASE:end-ROM_BASE])}
        return start, end

    def _budget(self):
        used = {'steps': self.steps, 'states': self.states, 'calls': len(self.calls),
                'memory_bytes': len(self.memory), 'events': len(self.events)}
        for name, count in used.items():
            if count > self.limits[name]:
                raise Unsupported(f'{name} budget exhausted')

    def _access(self, address, width, write=False):
        end = interval_end(address, width)
        if address % width:
            raise Unsupported('unaligned memory access')
        regions = [region for region in self.context.regions
                   if region.start <= address and end <= region.start + len(region.data)]
        if len(regions) != 1 or not (regions[0].writable if write else regions[0].readable):
            raise Unsupported('memory event outside declared readable/writable extent')
        if any(overlaps(address, end, protected.start, protected.end)
               for protected in self.context.protected):
            raise Unsupported('memory event overlaps protected saved/control bytes')

    def _read(self, address, width):
        self._access(address, width)
        value = tuple(self.memory[address + offset] for offset in range(width))
        self.events.append({'pc': self.pc, 'operation': 'read', 'address': address,
                            'width': width, 'value': value})
        self._budget()
        return value

    def _write(self, address, value):
        self._access(address, len(value), True)
        self.events.append({'pc': self.pc, 'operation': 'write', 'address': address,
                            'width': len(value), 'value': value})
        self._budget()
        for offset, part in enumerate(value):
            self.memory[address + offset] = part

    def _name(self, operand):
        if operand.type != ARM_OP_REG:
            raise Unsupported('register operand required')
        name = self.decoder.reg_name(operand.reg)
        return {'sb': 'r9', 'sl': 'r10', 'fp': 'r11', 'ip': 'r12'}.get(name, name)

    def _operand(self, operand):
        if operand.type == ARM_OP_IMM:
            return constant(operand.imm)
        return self.registers[self._name(operand)]

    def _set_nz(self, word):
        value = integer(word)
        self.flags.update(N=None if value is None else int(bool(value & 0x80000000)),
                          Z=None if value is None else int(value == 0))

    def _add(self, first, second, subtract=False):
        left, right = integer(first), integer(second)
        if right == 0 and not subtract:
            self.flags.update(C=0, V=0)
            self._set_nz(first)
            return first
        if left is None or right is None or any(part.fragments for part in (*first, *second)):
            raise Unsupported('unsupported arithmetic on unknown values or aliases')
        signed_left = left if left < 0x80000000 else left - 0x100000000
        signed_right = right if right < 0x80000000 else right - 0x100000000
        total = left - right if subtract else left + right
        signed_total = signed_left - signed_right if subtract else signed_left + signed_right
        result = constant(total & 0xFFFFFFFF)
        self.flags.update(C=int(left >= right) if subtract else int(total > 0xFFFFFFFF),
                          V=int(not -0x80000000 <= signed_total <= 0x7FFFFFFF))
        self._set_nz(result)
        return result

    def _instruction(self):
        if not self.containing[0] <= self.pc < self.containing[1]:
            raise Unsupported('control flow leaves inspected containing span')
        offset = self.pc - ROM_BASE
        instruction = next(self.decoder.disasm(self.rom[offset:offset+4], self.pc, count=1), None)
        if instruction is None or instruction.size not in (2, 4) or \
                self.pc + instruction.size > self.containing[1]:
            raise Unsupported('undecodable or truncated instruction')
        if self.pc in self.visited:
            raise Unsupported('loops and repeated control states are unsupported')
        self.visited.add(self.pc)
        self.steps += 1
        self._budget()
        if self.kind == 'incoming-r3-kill' and not self.killed:
            read, _ = instruction.regs_access()
            if any(self.decoder.reg_name(register) == 'r3' for register in read):
                raise NotEstablished('incoming r3 is read, copied or spilled before its kill')
        return instruction

    def _r3_overwrite(self, instruction):
        if self.kind != 'incoming-r3-kill' or self.killed or not any(
                self.decoder.reg_name(register) == 'r3' for register in instruction.regs_access()[1]):
            return
        word = self.registers['r3']
        value = integer(word)
        original = required_integer(self.initial_registers['r3'])
        origins = {fragment.origin for part in self.initial_registers['r3'] for fragment in part.fragments}
        if value is not None and original <= value < original + 28 or \
                any(fragment.origin in origins for part in word for fragment in part.fragments):
            return
        if value is None:
            raise Unsupported('r3 overwrite independence is unresolved')
        if any(part.fragments for part in word):
            operands = instruction.operands
            if instruction.mnemonic != 'add' or len(operands) != 3 or \
                    self._name(operands[1]) != 'sp' or operands[2].type != ARM_OP_IMM or \
                    not self.initial_sp - 36 <= value < self.initial_sp:
                raise Unsupported('r3 overwrite independence is unresolved')
        self.killed = True

    def step(self):
        instruction = self._instruction()
        name, operands = instruction.mnemonic, instruction.operands
        next_pc = self.pc + instruction.size
        if name in ('ldm', 'stm'):
            if self.kind != 'descriptor-copy' or instruction.size != 2 or len(operands) < 2:
                raise Unsupported('block transfer unsupported in this context')
            base = self._name(operands[0])
            selected = [self._name(operand) for operand in operands[1:]]
            if base not in tuple(f'r{number}' for number in range(8)) or base in selected or \
                    any(register not in tuple(f'r{number}' for number in range(8)) for register in selected) or \
                    selected != sorted(set(selected), key=lambda register: int(register[1:])):
                raise Unsupported('unsupported base-in-list or block-transfer registers')
            address = required_integer(self.registers[base])
            writeback = address_offset(self.registers[base], 4 * len(selected))
            for index, register in enumerate(selected):
                if name == 'ldm':
                    self.registers[register] = self._read(address + 4 * index, 4)
                else:
                    self._write(address + 4 * index, self.registers[register])
            self.registers[base] = writeback
        elif name in ('ldr', 'str', 'strh'):
            if self.kind != 'descriptor-copy' or instruction.size != 2 or len(operands) != 2 or \
                    operands[1].type != ARM_OP_MEM or operands[1].mem.index or instruction.writeback:
                raise Unsupported('unsupported memory instruction')
            register = self._name(operands[0])
            memory = operands[1].mem
            base = self.decoder.reg_name(memory.base)
            if base not in self.registers or register not in self.registers:
                raise Unsupported('unsupported memory/control register')
            address = required_integer(address_offset(self.registers[base], memory.disp))
            if name == 'ldr':
                self.registers[register] = self._read(address, 4)
            else:
                self._write(address, self.registers[register][:2 if name == 'strh' else 4])
        elif name in ('mov', 'movs'):
            destination = self._name(operands[0])
            if destination not in self.registers or destination in ('sp', 'lr') or len(operands) != 2:
                raise Unsupported('unsupported control-register move')
            self.registers[destination] = self._operand(operands[1])
            if name == 'movs':
                self._set_nz(self.registers[destination])
        elif name in ('adds', 'add', 'sub'):
            destination = self._name(operands[0])
            if name in ('add', 'sub'):
                if name == 'sub' and destination == 'sp' and len(operands) == 2 and operands[1].type == ARM_OP_IMM:
                    amount = operands[1].imm
                    if self.kind != 'incoming-r3-kill' or amount % 4:
                        raise Unsupported('unsupported stack allocation')
                    before = required_integer(self.registers['sp'])
                    self.registers['sp'] = address_offset(self.registers['sp'], -amount)
                    after = required_integer(self.registers['sp'])
                    for address in range(after, before, 4):
                        self._access(address, 4, True)
                    self.call_frames[-1]['locals'].append({'start': after, 'end': before})
                    self.call_frames[-1]['current_sp'] = after
                elif name == 'add' and len(operands) == 3 and self._name(operands[1]) == 'sp' and \
                        operands[2].type == ARM_OP_IMM and destination not in ('sp', 'lr', 'pc'):
                    self.registers[destination] = address_offset(self.registers['sp'], operands[2].imm)
                else:
                    raise Unsupported('unsupported nonflag arithmetic')
            else:
                if destination in ('sp', 'lr', 'pc') or len(operands) not in (2, 3):
                    raise Unsupported('unsupported arithmetic destination')
                first = self.registers[destination] if len(operands) == 2 else self._operand(operands[1])
                self.registers[destination] = self._add(first, self._operand(operands[-1]))
        elif name == 'ands':
            destination = self._name(operands[0])
            first, second = self.registers[destination], self._operand(operands[1])
            if any(part.fragments for part in (*first, *second)):
                raise Unsupported('bit operations on alias fragments are unsupported')
            self.registers[destination] = constant(required_integer(first) & required_integer(second))
            self._set_nz(self.registers[destination])
        elif name == 'cmp':
            self._add(self._operand(operands[0]), self._operand(operands[1]), subtract=True)
        elif name in ('lsls', 'lsrs'):
            destination = self._name(operands[0])
            source = self._operand(operands[1])
            if len(operands) != 3 or operands[2].type != ARM_OP_IMM or \
                    any(part.fragments for part in source):
                raise Unsupported('unsupported shift')
            amount, value = operands[2].imm, required_integer(source)
            if not 1 <= amount <= 31:
                raise Unsupported('unsupported shift amount')
            self.flags['C'] = (value >> (32-amount if name == 'lsls' else amount-1)) & 1
            self.registers[destination] = constant((value << amount) & 0xFFFFFFFF if name == 'lsls' else value >> amount)
            self._set_nz(self.registers[destination])
        elif name in ('b', 'beq', 'bne'):
            if self.kind != 'incoming-r3-kill' or operands[0].type != ARM_OP_IMM:
                raise Unsupported('branch not supported in this segment')
            if name != 'b' and self.flags['Z'] is None:
                raise Unsupported('unknown branch condition')
            if name == 'b' or self.flags['Z'] == int(name == 'beq'):
                next_pc = operands[0].imm
        elif name == 'bl':
            if self.kind != 'incoming-r3-kill' or operands[0].type != ARM_OP_IMM:
                raise Unsupported('unchecked call is unsupported')
            self.calls.append({'pc': self.pc, 'target': operands[0].imm, 'return_pc': next_pc | 1})
            self._budget()
            self.containing = self._span(operands[0].imm, exact=True)
            self.registers['lr'] = constant(next_pc | 1)
            stack = required_integer(self.registers['sp'])
            self.call_frames.append({'entry_pc': operands[0].imm, 'entry_sp': stack,
                                     'current_sp': stack, 'saved_slots': [], 'locals': []})
            next_pc = operands[0].imm
        elif name in ('push', 'pop'):
            if self.kind != 'incoming-r3-kill' or instruction.size != 2:
                raise Unsupported('stack saves unsupported in this segment')
            selected = [self._name(operand) for operand in operands]
            if not selected or any(register not in REGISTER_NAMES or register == 'sp' for register in selected):
                raise Unsupported('unsupported save/control list')
            before = required_integer(self.registers['sp'])
            if name == 'push':
                self.registers['sp'] = address_offset(self.registers['sp'], -4 * len(selected))
                after = required_integer(self.registers['sp'])
                for index, register in enumerate(selected):
                    self._write(after + 4 * index, self.registers[register])
                    self.call_frames[-1]['saved_slots'].append({'register': register,
                        'address': after + 4 * index, 'value': self.registers[register]})
                self.call_frames[-1]['current_sp'] = after
            else:
                for index, register in enumerate(selected):
                    self.registers[register] = self._read(before + 4 * index, 4)
                self.registers['sp'] = address_offset(self.registers['sp'], 4 * len(selected))
                self.call_frames[-1]['current_sp'] = required_integer(self.registers['sp'])
        elif name == 'bx' and self.kind == 'incoming-r3-kill':
            if self._operand(operands[0]) != self.initial_registers['lr'] or \
                    self.registers['sp'] != self.initial_registers['sp']:
                raise Unsupported('indirect control before requested cutpoint')
            raise NotEstablished('returned before the kill cutpoint; no positive kill claim')
        else:
            raise Unsupported(f'unsupported instruction {name} at 0x{self.pc:08X}')
        self._r3_overwrite(instruction)
        self.trace.append({'pc': self.pc, 'instruction': name, 'registers': dict(self.registers),
                           'flags': dict(self.flags)})
        self.pc = next_pc

    def _copy_claim(self):
        source = required_integer(self.initial_registers['r9'])
        destination = self.initial_sp
        expected_events = []
        for start in (0, 12):
            expected_events.extend(('read', source + offset, 4) for offset in range(start, start+12, 4))
            expected_events.extend(('write', destination + offset, 4) for offset in range(start, start+12, 4))
        expected_events.extend((('read', source+24, 4), ('write', destination+24, 4), ('write', destination, 2)))
        if [(event['operation'], event['address'], event['width']) for event in self.events] != expected_events:
            raise NotEstablished('ordered seven-word copy and halfword-zero trace not established')
        expected_registers = dict(self.initial_registers)
        expected_registers.update(r0=constant(0), r1=self.initial_registers['sp'])
        for register, offset in (('r3', 12), ('r4', 16), ('r5', 20)):
            expected_registers[register] = tuple(self.initial_memory[source+offset+index] for index in range(4))
        expected_memory = dict(self.initial_memory)
        for offset in range(28):
            expected_memory[destination+offset] = constant(0)[offset] if offset < 2 else self.initial_memory[source+offset]
        expected_flags = dict(self.initial_flags, N=0, Z=1)
        if self.registers != expected_registers or self.memory != expected_memory or self.flags != expected_flags:
            raise NotEstablished('exact copy byte-state, register or flag poststate not established')

    def _kill_claim(self):
        size = required_integer(self.initial_registers['r1'])
        if size not in (40, 84) or not self.killed or len(self.calls) != 1:
            raise NotEstablished('supported incoming-r3 kill context not established')
        units = size // 4
        saved_lr = constant(self.calls[0]['return_pc'])
        initial = self.initial_registers
        expected = dict(initial)
        expected.update(r0=initial['r0'], r1=constant(units << 16), r2=initial['r0'],
                        r3=address_offset(initial['sp'], -32), r5=constant(units),
                        r7=initial['r8'], r8=initial['r0'], lr=saved_lr,
                        sp=address_offset(initial['sp'], -36))
        slots = ((-4, initial['lr']), (-24, initial['r4']), (-20, initial['r5']),
                 (-16, initial['r6']), (-12, initial['r7']), (-8, saved_lr), (-28, initial['r8']))
        expected_events = [('write', self.initial_sp+offset, 4, value) for offset, value in slots]
        events = [(event['operation'], event['address'], event['width'], event['value']) for event in self.events]
        expected_memory = dict(self.initial_memory)
        for offset, value in slots:
            for index, part in enumerate(value):
                expected_memory[self.initial_sp+offset+index] = part
        if self.registers != expected or self.flags != dict.fromkeys('NZCV', 0) or \
                events != expected_events or self.memory != expected_memory:
            raise NotEstablished('exact open-frame kill poststate not established')

    def run(self):
        source = required_integer(self.registers['r9' if self.kind == 'descriptor-copy' else 'r3'])
        destination = self.initial_sp if self.kind == 'descriptor-copy' else self.initial_sp - 36
        length = 28 if self.kind == 'descriptor-copy' else 36
        interval_end(source, 28)
        interval_end(destination, length)
        if source % 4 or destination % 4 or overlaps(source, source+28, destination, destination+length):
            raise Unsupported('unaligned or overlapping source/descriptor and destination/workspace')
        self._access(source, 4)
        self._access(source+24, 4)
        self._access(destination, 4, True)
        self._access(destination+length-4, 4, True)
        if self.kind == 'incoming-r3-kill' and integer(self.registers['r1']) is None:
            raise Unsupported('unknown size cannot establish incoming-r3 kill')
        while self.pc != self.exit_pc:
            self.step()
        if self.kind == 'descriptor-copy':
            self._copy_claim()
        else:
            self._kill_claim()

    def output(self):
        return {'poststate': {'pc': self.pc, 'registers': self.registers, 'flags': self.flags,
                             'regions': [Region(region.name, region.start,
                                 tuple(self.memory[address] for address in range(region.start, region.start+len(region.data))),
                                 region.readable, region.writable) for region in self.context.regions],
                             'frame_ownership': self.context.frames,
                             'open_frames': self.context.frames if self.kind == 'descriptor-copy' else self.call_frames},
                'events': self.events, 'trace': self.trace,
                'dependencies': list(self.dependencies.values()),
                'counts': {'steps': self.steps, 'states': self.states, 'calls': len(self.calls),
                           'memory_bytes': len(self.memory), 'events': len(self.events)}}


def plain(value):
    if hasattr(value, '__dataclass_fields__'):
        return plain(asdict(value))
    if isinstance(value, dict):
        return {name: plain(item) for name, item in value.items()}
    if isinstance(value, (tuple, list)):
        return [plain(item) for item in value]
    return value


def _check(rom, mapping, entry_pc, exit_pc, context, limits, kind):
    result = {'status': 'unsupported', 'claim': kind, 'version': VERSION, 'mode': 'thumb',
              'entry_pc': entry_pc, 'exit_pc': exit_pc,
              'undischarged_obligations': COPY_OBLIGATIONS if kind == 'descriptor-copy' else KILL_OBLIGATIONS}
    runner = None
    try:
        original_limits = dict(HARD_LIMITS) if limits is None else limits
        limits = dict(original_limits)
        captured_context = copy.deepcopy(context)
        context_snapshot = canonical(plain(captured_context))
        limits_snapshot = canonical(limits)
        runner = _Cutpoint(rom, mapping, entry_pc, exit_pc, captured_context, limits, kind)
        result.update(mapping_sha256=digest(mapping), context_sha256=digest(context_snapshot),
                      limits_sha256=digest(limits_snapshot), supplied_premises=plain(captured_context))
        runner.run()
        if canonical(plain(context)) != context_snapshot or canonical(original_limits) != limits_snapshot:
            raise Unsupported('entry inputs changed during evaluation')
        result.update(status='conditional-success', diagnostic='Only the named cutpoint claim under the supplied premises.')
    except NotEstablished as error:
        result.update(status='not-established', diagnostic=str(error))
    except (Unsupported, ValueError, TypeError, KeyError, AttributeError, OverflowError) as error:
        result.update(status='unsupported', diagnostic=str(error))
    if runner is not None:
        result.update(runner.output())
    result = plain(result)
    result['input_identity'] = digest(canonical({name: result.get(name) for name in
        ('claim', 'version', 'mode', 'entry_pc', 'exit_pc', 'mapping_sha256', 'context_sha256',
         'limits_sha256', 'dependencies')}))
    return result


def check_copy_cutpoint(rom, mapping, entry_pc, exit_pc, context, limits=None):
    return _check(rom, mapping, entry_pc, exit_pc, context, limits, 'descriptor-copy')


def check_r3_kill_cutpoint(rom, mapping, entry_pc, exit_pc, context, limits=None):
    return _check(rom, mapping, entry_pc, exit_pc, context, limits, 'incoming-r3-kill')


def real_context(kind, value):
    registers = {name: unknown_word('entry-' + name) for name in REGISTER_NAMES}
    flags = dict.fromkeys('NZCV', None)
    if kind == 'copy':
        source, destination = 0x03002050, 0x03002000
        registers.update(sp=constant(destination, 'engine-frame'), r9=constant(source, 'wrapper-frame'))
        initialized = set(range(4, 8)) | {20, 21} if value == 6920 else set(range(20, 26))
        source_data = tuple(ByteState(index in initialized, None, f'input-{index}',
            (Fragment('possible-input-pointer', index % 4, index // 4 * 4),)
            if index not in initialized or value == 6920 and 4 <= index < 8 else ()) for index in range(28))
        regions = (Region('source', source, source_data, True, False),
                   Region('destination', destination, tuple(ByteState(False, symbol=f'old-local-{index}') for index in range(28))))
        frames = (Interval('wrapper', source, source+28), Interval('engine', destination, destination+56))
        protected = (Interval('engine saves', destination+28, destination+56),)
    else:
        stack, source = 0x03002400, 0x03002800
        registers.update(sp=constant(stack, 'entry-stack'), r0=unknown_word('owner'),
                         r1=constant(value) if value is not None else unknown_word('size'),
                         r3=constant(source, 'borrowed-descriptor'), r9=constant(source, 'borrowed-descriptor'))
        regions = (Region('workspace', stack-36, tuple(ByteState(False, symbol=f'stack-{index}') for index in range(36))),
                   Region('descriptor', source, tuple(ByteState(False, symbol=f'descriptor-{index}') for index in range(28)), True, False))
        frames = (Interval('stack workspace', stack-36, stack), Interval('borrowed wrapper', source, source+28))
        protected = (Interval('caller control', stack, stack+4),)
    return Context(registers, flags, regions, protected, frames, COMMON_PREMISES)


def run_real_cases(root):
    root = Path(root).resolve()
    rom_path, map_path = root / 'baserom.bin', root / 'config/functions.json'
    rom, mapping = rom_path.read_bytes(), map_path.read_bytes()
    results = []
    for wrapper in (6920, 6970):
        results.append(check_copy_cutpoint(rom, mapping, 0x080059EE, 0x08005A04, real_context('copy', wrapper)))
    for size in (40, 84):
        results.append(check_r3_kill_cutpoint(rom, mapping, 0x08007138, 0x08006ED0, real_context('kill', size)))
    if rom_path.read_bytes() != rom or map_path.read_bytes() != mapping:
        raise Unsupported('current ROM or mapping changed before diagnostic emission')
    return {'diagnostic_only': True, 'rom_path': str(rom_path), 'rom_sha256': digest(rom),
            'mapping_path': str(map_path), 'mapping_sha256': digest(mapping), 'results': results}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    arguments = parser.parse_args()
    try:
        report = run_real_cases(arguments.root)
    except (OSError, Unsupported) as error:
        parser.exit(1, f'unsupported: {error}\n')
    print(json.dumps(report, indent=2))
    return int(any(result['status'] != 'conditional-success' for result in report['results']))


if __name__ == '__main__':
    raise SystemExit(main())
