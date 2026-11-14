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
* is a jump, call, return, a write of PC, a conditional instruction or an
  instruction capstone cannot decode (refuses).

So only a straight-line entry prefix that unconditionally overwrites the
register counts; nothing in the callee can observe the alias.  When every
alias is dead, the call is exactly a call that receives no alias, which the
walk already admits under its ordinary premise; otherwise the callee is
walked with the remaining aliases.  Each dropped register is reported with the
callee's extent and body hash and the killing instruction.
"""
import hashlib

from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB, CS_GRP_JUMP, CS_GRP_CALL, CS_GRP_RET
from capstone.arm import ARM_CC_AL, ARM_CC_INVALID, ARM_REG_PC

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


def killing_instruction(data, address, register):
    """The offset of the entry-prefix instruction that overwrites register
    before any read of it, or None when the prefix does not prove it dead."""
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    decoder.detail = True
    expected = address
    for instruction in decoder.disasm(data, address):
        if instruction.address != expected:
            return None
        expected += instruction.size
        read, written = instruction.regs_access()
        if register in read:
            return None
        if instruction.cc not in (ARM_CC_AL, ARM_CC_INVALID) or \
                {CS_GRP_JUMP, CS_GRP_CALL, CS_GRP_RET} & set(instruction.groups) or \
                ARM_REG_PC in written:
            return None
        if register in written:
            return instruction.address - address
    return None


class DeadArgumentBufferProof(named.NamedDataBufferProof):
    """Named-data buffer walk that discounts aliases a callee overwrites unread."""

    def __init__(self, rom, mapping, index, objects):
        super().__init__(rom, mapping, index, objects)
        self.dead_arguments = {}

    def check_arguments(self, address, arguments, stack, incoming, protected, **context):
        candidates = sorted(register for register in arguments if register in ARGUMENTS)
        if candidates:
            data = self.span(address)
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
            rule=('an owner alias in R0-R3 is not passed to a callee whose straight-line entry '
                  'prefix (no jump, call, return, PC write or conditional instruction) writes the '
                  'register before any instruction reads it'),
            calls=[self.dead_arguments[key] for key in sorted(self.dead_arguments, key=repr)])
