"""Named-data buffer owners whose stale argument-register aliases are dead in the callee.

The named-data buffer walk (`named-data-buffer-v1`) follows every callee that
receives one of the owner's stack aliases in R0-R3, whatever the callee's
prototype.  agbcc often leaves such an alias in a register the next call does
not take: 080EA6F4 and 080ED4E8 call func_0801E610(&a, &b), which returns with
the address of `b` still in R1, and then func_080035F8(2), whose first R1
instruction is `ldr r1, =table`.  The walk follows the stale R1 into
func_080035F8 and refuses that function's own frame arithmetic.

`named-data-buffer-dead-argument-aliases-v1` keeps the walk and its alias rules
and changes one step: before a callee is walked, an owner alias in an argument
register is not passed when the callee's own bytes show the register is
written before it is read.  The check runs on the callee's indexed, validated
bytes from its entry, instruction by instruction, and stops at the first
instruction that

* reads the register (refuses: the alias stays an argument),
* writes it (the alias is dead), or
* is not one 16-bit ARMv4T instruction of an allowlisted form (refuses).

The allowlist is register and immediate data processing, single loads and
stores, PUSH and ADD/SUB SP by an immediate.  Everything else stops the scan:
SWI (capstone reports it reading only PC, but the BIOS reads R0-R3), BKPT,
UDF, any 32-bit decode (capstone decodes Thumb-2; on the ARM7TDMI `f04f 0100`
is a BL prefix and `lsls r0, r0, #4`, not `mov.w r1, #0`), post-ARMv4T 16-bit
forms (a high-register ADD/CMP/MOV of two low registers, the miscellaneous
space beyond ADD/SUB SP and PUSH), POP, LDM/STM, branches, calls, returns,
conditional instructions and any write of PC or (but for ADD/SUB SP and PUSH)
SP.  So only a straight-line entry prefix that unconditionally overwrites the
register counts; nothing in the callee can observe the alias.  The scan reads
the callee's bytes without spending the walk's dependency budget: a callee
whose aliases are all dead is not walked and is not a dependency.  When every
alias is dead, the call is exactly a call that receives no alias, which the
walk already admits under its ordinary premise; otherwise the callee is
walked with the remaining aliases.  Each dropped register is reported with the
callee's extent and body hash and the killing instruction.
"""
import hashlib

from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB, CS_GRP_JUMP, CS_GRP_CALL, CS_GRP_RET, CS_GRP_INT
from capstone.arm import ARM_CC_AL, ARM_CC_INVALID, ARM_REG_PC, ARM_REG_SP

import match
import named_data_buffer_profile as named

SELECTOR = named.DEAD_ARGUMENT_SELECTOR
SCHEMA = named.DEAD_ARGUMENT_SCHEMA
MAX_DEPENDENCIES = named.MAX_DEPENDENCIES
CONTROL_FLOW = ('complete Thumb owner with typed data literals and ROM-proved bounded buffer callees; '
                'owner aliases in argument registers that a callee overwrites in its straight-line '
                'entry prefix before reading them are not passed to it')
ARGUMENTS = tuple(match.ARM_REG_R0 + n for n in range(4))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


# 16-bit Thumb (ARMv4T) forms the scan may step over: register and immediate
# data processing, single loads and stores, and PUSH.  Everything else stops it
# - in particular SWI (the BIOS reads R0-R3), BKPT/UDF, every 32-bit or
# post-ARMv4T encoding (capstone decodes Thumb-2), POP, LDM/STM, branches.
ALLOWED = frozenset((
    'mov', 'movs', 'mvn', 'mvns', 'neg', 'negs', 'rsb', 'rsbs',
    'add', 'adds', 'sub', 'subs', 'adc', 'adcs', 'sbc', 'sbcs', 'mul', 'muls',
    'and', 'ands', 'orr', 'orrs', 'eor', 'eors', 'bic', 'bics',
    'lsl', 'lsls', 'lsr', 'lsrs', 'asr', 'asrs', 'ror', 'rors',
    'cmp', 'cmn', 'tst', 'adr',
    'ldr', 'ldrb', 'ldrh', 'ldrsb', 'ldrsh', 'str', 'strb', 'strh', 'push'))


def thumb1(instruction):
    """is this one 16-bit ARMv4T Thumb instruction of an allowed form?"""
    if instruction.size != 2 or instruction.mnemonic not in ALLOWED or \
            instruction.cc not in (ARM_CC_AL, ARM_CC_INVALID) or \
            {CS_GRP_JUMP, CS_GRP_CALL, CS_GRP_RET, CS_GRP_INT} & set(instruction.groups):
        return False
    half = int.from_bytes(instruction.bytes, 'little')
    if half >> 11 >= 0b11101:
        return False                      # a 32-bit prefix, BL halves included
    if half & 0xfc00 == 0x4400 and not half & 0xc0:
        return False                      # hi-register ADD/CMP/MOV of two low registers: not ARMv4T
    if 0xb000 <= half < 0xc000 and not (half & 0xff80 in (0xb000, 0xb080) or half & 0xfe00 == 0xb400):
        return False                      # only ADD/SUB SP,#imm and PUSH of the miscellaneous space
    read, written = instruction.regs_access()
    if ARM_REG_PC in written:
        return False
    if ARM_REG_SP in written and not (half & 0xff00 == 0xb000 or half & 0xfe00 == 0xb400):
        return False                      # MOV/ADD SP, rX and the like: the frame becomes untracked
    return True


def killing_instruction(data, address, register):
    """The offset of the entry-prefix instruction that overwrites register
    before any read of it, or None when the prefix does not prove it dead."""
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    decoder.detail = True
    expected = address
    for instruction in decoder.disasm(data, address):
        if instruction.address != expected or not thumb1(instruction):
            return None
        expected += instruction.size
        read, written = instruction.regs_access()
        if register in read:
            return None
        if register in written:
            return instruction.address - address
    return None


class DeadArgumentBufferProof(named.NamedDataBufferProof):
    """Named-data buffer walk that discounts aliases a callee overwrites unread."""

    def __init__(self, rom, mapping, index, objects):
        super().__init__(rom, mapping, index, objects)
        self.dead_arguments = {}

    def entry_bytes(self, address):
        """The callee's indexed, validated bytes, as span() reads them, without
        spending the walk's dependency budget: a callee whose aliases are all
        dead is never walked, so it is not a dependency of the proof."""
        entry = self.target(address)
        require(0 < int(entry['end'], 16) - address <= named.MAX_BYTES,
                'dead-argument callee exceeds bounded owner size')
        data = match.BufferCallProof.span(self, address)
        named.validate_owner(data, address, self.rom, self.mapping, self.index)
        return data

    def check_arguments(self, address, arguments, stack, incoming, protected, **context):
        candidates = sorted(register for register in arguments if register in ARGUMENTS)
        if candidates:
            data = self.entry_bytes(address)
            dead = {}
            for register in candidates:
                offset = killing_instruction(data, address, register)
                if offset is not None:
                    dead[register] = offset
            if dead:
                key = (context.get('site'), address, tuple(sorted(arguments.items())))
                observation = dict(
                    site=context.get('site'), callee=f'func_{address:08X}',
                    end=address + len(data), body_sha256=sha(data),
                    dead=[[f'r{register - match.ARM_REG_R0}', arguments[register], offset]
                          for register, offset in sorted(dead.items())],
                    passed=sorted([f'r{register - match.ARM_REG_R0}', offset]
                                  for register, offset in arguments.items() if register not in dead))
                previous = self.dead_arguments.setdefault(key, observation)
                require(previous == observation, 'dead argument observation differs between visits')
                arguments = {register: offset for register, offset in arguments.items()
                             if register not in dead}
        return super().check_arguments(address, arguments, stack, incoming, protected, **context)

    def dead_argument_manifest(self):
        require(self.dead_arguments, 'dead argument profile requires a discounted owner alias')
        return dict(
            selector=SELECTOR,
            rule=('an owner alias in R0-R3 is not passed to a callee whose entry prefix of '
                  'allowlisted 16-bit ARMv4T data-processing, single load/store, PUSH and '
                  'ADD/SUB SP instructions writes the register before any instruction reads it'),
            calls=[self.dead_arguments[key] for key in sorted(self.dead_arguments, key=repr)])
