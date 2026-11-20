"""Actual scene continuations and bounded CpuSet operations for the record loader."""
from hashlib import sha256

from struct import pack, unpack_from

import match
import bios_cpuset_fill_profile as bios
from ability_range_local_bytes import require
from software_float_profile import ROM_SHA256
from positioned_equipment_chance import direct_sites
from unit_equipment_attribute import ops

OWNER = 0x0801A518
END = 0x0801AC78
RETURN = 0x0801AC6C
FILLS = (0x0801A884, 0x0801A966)
R2 = match.ARM_REG_R0 + 2


def scene_and_outputs(rom):
    base = match.ROM_BASE
    def word(addr):
        return unpack_from('<I', rom, addr-base)[0]

    require(not direct_sites(rom, OWNER) and rom.count(pack('<I', OWNER)) == 0 and
            rom.count(pack('<I', OWNER | 1)) == 1 and word(0x080242AC) == OWNER | 1,
            'record callback has unexpected references')
    require(direct_sites(rom, 0x080241B4) == [0x08023FAC] and
            not rom.count(pack('<I', 0x080241B5)), 'scene controller has unexpected callers')
    require([word(a) for a in (0x08023F7C, 0x08023F80, 0x08023F84, 0x08023FB4, 0x080242A8,
                               0x0804C964, 0x0804C968, 0x0804C96C)] ==
            [0x03002710, 0x03002820, 0x03000E40, 0x03002710, 0x03002710,
             0x03002710, 0x03002820, 0x03000E40], 'scene runner or its arrays changed')
    ops(rom, 0x08023F2C, 'ldr r4, [pc, #0x4c]', 'ldr r1, [pc, #0x50]', 'ldr r2, [pc, #0x50]',
        'adds r0, r4, #0', 'movs r3, #9', 'bl #0x8006a7c')
    ops(rom, 0x08024298, 'ldr r0, [pc, #0xc]', 'ldr r2, [pc, #0x10]', 'movs r1, #3', 'bl #0x8006adc')
    ops(rom, 0x08006AE2, 'ldr r4, [r0, #8]', 'lsls r3, r1, #2', 'adds r3, r3, r4', 'str r2, [r3]',
        'ldr r0, [r0, #0xc]', 'adds r0, r0, r1', 'movs r1, #0', 'strb r1, [r0]')
    ops(rom, 0x08023FA4, 'ldr r0, [pc, #0xc]', 'movs r1, #9', 'bl #0x80069f4', 'bl #0x80241b4')
    # The other scene using these fixed arrays reinitializes five slots before
    # progressing to its dispatch phase. This also clears the previous slot 3.
    ops(rom, 0x0804C8A2, 'bl #0x804c8c4', 'movs r0, #1', 'b #0x804c8bc')
    ops(rom, 0x0804C91C, 'ldr r4, [pc, #0x44]', 'ldr r1, [pc, #0x48]', 'ldr r2, [pc, #0x48]',
        'adds r0, r4, #0', 'movs r3, #5', 'bl #0x8006a7c')
    ops(rom, 0x08006A9C, 'movs r3, #0', 'ldr r0, [r5, #8]', 'lsls r1, r2, #2',
        'adds r1, r1, r0', 'str r3, [r1]', 'ldr r0, [r5, #0xc]', 'adds r0, r0, r2',
        'strb r3, [r0]', 'subs r2, #1', 'cmp r2, #0', 'bge #0x8006a9e')
    ops(rom, 0x08006A2A, 'strb r4, [r5, #3]', 'lsls r0, r4, #0x18', 'lsrs r0, r0, #0x18',
        'ldr r1, [r5, #0xc]', 'adds r1, r1, r4', 'bl #0x814224c')
    ops(rom, 0x08006A60, 'lsls r0, r4, #0x18', 'lsrs r0, r0, #0x18', 'ldr r1, [r5, #0xc]',
        'adds r1, r1, r4', 'ldr r2, [r2]', 'bl #0x814224c')
    ops(rom, 0x0814224C, 'bx r2')
    ops(rom, 0x08006A38, 'adds r0, r6, #1', 'lsls r0, r0, #0x18', 'lsrs r6, r0, #0x18',
        'adds r4, #1', 'cmp r4, r7', 'blt #0x8006a1a')
    ops(rom, 0x08006A1A, 'ldr r1, [r5, #8]', 'lsls r0, r4, #2', 'adds r0, r0, r1', 'ldr r2, [r0]')
    ops(rom, 0x08006A6E, 'adds r0, r6, #1', 'lsls r0, r0, #0x18', 'lsrs r6, r0, #0x18',
        'strb r6, [r5, #4]', 'pop {r4, r5, r6, r7}', 'pop {r0}', 'bx r0')
    ops(rom, 0x080241B4, 'push {r4, r5, lr}', 'sub sp, #0xc', 'movs r0, #0xd', 'bl #0x80c95a8')
    ops(rom, 0x080C95A8, 'lsls r0, r0, #0x10', 'lsrs r0, r0, #0x10', 'ldr r1, [pc, #8]',
        'ldr r2, [pc, #0xc]')
    require(word(0x080C95BC) == 0x2030, 'selected callback continuation changed')
    # Source provenance: the helper writes all three incoming words and never
    # writes R2. The root restores the whole frame before branching to its caller.
    ops(rom, 0x0801A71C, 'add r0, sp, #0x24', 'add r1, sp, #0x28', 'add r2, sp, #0x2c',
        'bl #0x801e68c', 'ldr r1, [pc, #0x64]', 'ldrh r0, [r1]', 'cmp r0, #0xff',
        'bne #0x801a730', 'b #0x801a82a')
    ops(rom, 0x0801E68C, 'push {r4, lr}', 'ldr r4, [pc, #0x14]', 'ldr r3, [r4, #0x10]',
        'str r3, [r0]', 'ldr r0, [r4, #0x14]', 'str r0, [r1]', 'ldr r0, [r4, #0x18]',
        'str r0, [r2]', 'pop {r4}', 'pop {r0}', 'bx r0')
    ops(rom, 0x0801A82A, 'movs r0, #4', 'b #0x801a8be')
    ops(rom, 0x0801A8BE, 'mov r3, sb', 'strb r0, [r3]', 'b #0x801ac5e')
    ops(rom, 0x0801AC5E, 'add sp, #0x40', 'pop {r3, r4, r5}', 'mov r8, r3', 'mov sb, r4',
        'mov sl, r5', 'pop {r4, r5, r6, r7}', 'pop {r0}', 'bx r0')
    # Both stored halfwords are initialized immediately before CpuSet. The
    # first count is an unsigned byte and the second is a fixed 256 halfwords.
    ops(rom, 0x0801A574, 'bl #0x801a060')
    ops(rom, 0x0801A09A, 'bl #0x801e204')
    ops(rom, 0x0801E210, 'ldr r5, [pc, #0x84]', 'movs r1, #0', 'mov sb, r1')
    ops(rom, 0x0801E27E, 'movs r0, #8', 'mov r1, sb', 'strb r1, [r5, #0x1c]', 'strb r0, [r5, #0x1d]')
    ops(rom, 0x0801E6D4, 'ldr r3, [pc, #8]', 'ldrb r2, [r3, #0x1c]', 'strb r2, [r0]',
        'ldrb r0, [r3, #0x1d]', 'strb r0, [r1]', 'bx lr')
    ops(rom, 0x0801A864, 'mov r4, sp', 'adds r4, #5', 'add r0, sp, #4', 'adds r1, r4, #0',
        'bl #0x801e6d4', 'mov r0, sp', 'adds r0, #6', 'movs r1, #0', 'strh r1, [r0]',
        'ldr r1, [pc, #0x1c]', 'ldrb r2, [r4]', 'lsls r2, r2, #4', 'movs r3, #0x80',
        'lsls r3, r3, #0x11', 'orrs r2, r3', 'bl #0x814186c', 'b #0x801a8bc')
    ops(rom, 0x0801A8BC, 'movs r0, #5', 'mov r3, sb', 'strb r0, [r3]', 'b #0x801ac5e')
    ops(rom, 0x0801A958, 'mov r0, sp', 'adds r0, #6', 'movs r1, #0', 'strh r1, [r0]',
        'ldr r4, [pc, #0x14]', 'ldr r2, [pc, #0x18]', 'adds r1, r4, #0', 'bl #0x814186c',
        'str r4, [r6, #4]', 'b #0x801a9ca')
    ops(rom, 0x0801A9CA, 'bl #0x801b878')
    ops(rom, 0x0801B878, 'ldr r2, [pc, #8]', 'ldrh r1, [r2, #0x2c]', 'movs r0, #1',
        'orrs r0, r1', 'strh r0, [r2, #0x2c]', 'bx lr')
    require([word(a) for a in (0x0801E298, 0x0801E6E0, 0x0801A898, 0x0801A978, 0x0801A97C)]
            == [0x02007F40, 0x02007F40, 0x03003860, 0x02007CB0, 0x01000100],
            'record loader fill objects or control changed')
    return dict(registration=[0x0802429E, 0x03002710, 3], scene=[0x08023FA8, 9],
                return_r2=[RETURN, -52], kills=[0x08006A20, 0x080C95AE],
                scope='original slot-3 registration and ordinary scene/table lifetime',
                cpuset='modeled returning SWI 0x0B halfword fill; no BIOS machine code verified',
                writes=[[FILLS[0], 0x03003860, '32 * unsigned-byte count', 0],
                        [FILLS[1], 0x02007CB0, 512, 0]],
                normal_initial_count=8)


class MapRecordProof(match.FunctionBufferCallProof):
    def __init__(self, data, rom, mapping, index, calls):
        super().__init__(rom, mapping, stack_arguments=True)
        require(sha256(rom).hexdigest() == ROM_SHA256 and self.span(OWNER) == data
                and len(data) == END-OWNER, 'record loader requires complete original ROM and owner')
        require(tuple(sorted(s for s, t in calls.items() if t == bios.ADDRESS)) == FILLS,
                'record loader CpuSet sites differ')
        self.fill = bios.BiosFillProof(data, OWNER, rom, mapping, index, calls, zero_extension=True)
        self.scene = scene_and_outputs(rom)
        self.return_seen = False

    def check_call(self, address, aliases, stack, slots=None, *, constants=None, site=None, words=None):
        if site in FILLS:
            args = {reg: offset for reg, offset in aliases.items() if reg in match.CALLER_CLOBBERED}
            require(not self.active and address == bios.ADDRESS and not slots and not words and
                    args == {match.ARM_REG_R0: -90}, 'record loader CpuSet source frame differs')
            ret = self.fill.check_call(site, args, stack)
            self.dependencies[address] = self.fill.wrapper
            return ret
        return super().check_call(address, aliases, stack, slots, constants=constants, site=site, words=words)

    def project(self, data, address, site, aliases):
        if not self.active and address == OWNER and data == self.fill.data and site == RETURN and aliases == {R2: -52}:
            self.return_seen = True
            return {}
        return aliases

    def finish(self):
        require(self.return_seen and sorted((a, o, w) for a, o, w, _, _ in self.fill.observations)
                == [(s, -90, 2) for s in FILLS], 'record loader did not prove each source and return')
        return dict(fill=self.fill.manifest(), provider=self.scene)
