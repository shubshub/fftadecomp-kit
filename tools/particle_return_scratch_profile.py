"""Prove the particle initializer's one expired halfword alias at its three ROM calls."""

import hashlib
from pathlib import Path
import struct

from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
from capstone.arm import ARM_INS_B, ARM_INS_BL, ARM_REG_PC, ARM_REG_R3, ARM_REG_R4, ARM_REG_R5

import armv4t
import match
import named_data_buffer_profile as named
import owner_graph_profile as graph
from software_float_profile import ROM_SHA256


ROOT = 0x080A97EC
RETURN = 0x080A993A
PROJECT = 0x0801C984
RANDOM = 0x08002804
REMAINDER = 0x08142950
PROJECTION_SITE = 0x080A9814
RANDOM_SITES = (0x080A985A, 0x080A9898, 0x080A98D0, 0x080A98E8, 0x080A9900, 0x080A991A)
REMAINDER_SITES = (0x080A9864, 0x080A98DA, 0x080A98F2, 0x080A990A, 0x080A9924)
CALLS = {PROJECTION_SITE: PROJECT, **dict.fromkeys(RANDOM_SITES, RANDOM),
         **dict.fromkeys(REMAINDER_SITES, REMAINDER)}

FIRST = 0x080AD66C
SECOND = 0x080B264C
SITES = (0x080AE118, 0x080B2D78, 0x080B2E18)
SPANS = {FIRST: 0x080AE7D8, SECOND: 0x080B2F1E}
KILLS = {SITES[0]: (0x080AE12E, 'movs', 'r3, #0x99'),
         SITES[1]: (0x080B2F10, 'pop', '{r3, r4, r5}'),
         SITES[2]: (0x080B2F10, 'pop', '{r3, r4, r5}')}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def decoder():
    cs = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    cs.detail = True
    return cs


def decode(cs, data, base, pc):
    require(pc % 2 == 0 and base <= pc < base + len(data), 'instruction outside particle caller')
    item = next(cs.disasm(data[pc-base:pc-base+4], pc, count=1), None)
    require(item is not None and armv4t.instruction(item), 'invalid particle caller Thumb instruction')
    return item


def check_bindings(address, bindings):
    expected = [[site-ROOT, '__modsi3' if target == REMAINDER else f'func_{target:08X}']
                for site, target in sorted(CALLS.items())]
    require(address == ROOT and bindings == dict(calls=expected, data=[[0xA8, 'data_08394560', 0]],
                                                  functions=[], switches=[]),
            'particle initializer requires the original compiler __modsi3 binding, known calls and asset')


def raw_references(rom):
    require(len(rom) == 0x1000000, 'particle reference inventory needs the full 16 MiB image')
    # A Thumb-1 BL pair can reach [-2^22, 2^22-2] from PC+4.
    first = max(match.ROM_BASE, ROOT - 4 - ((1 << 22) - 2))
    last = min(match.ROM_BASE + len(rom) - 4, ROOT - 4 + (1 << 22))
    sites = []
    pair = struct.Struct('<HH')
    for pc in range(first, last + 1, 2):
        prefix, suffix = pair.unpack_from(rom, pc - match.ROM_BASE)
        if prefix & 0xF800 == 0xF000:
            delta = ROOT - (pc + 4)
            if (prefix, suffix) == (0xF000 | ((delta >> 12) & 0x7FF), 0xF800 | ((delta >> 1) & 0x7FF)):
                sites.append(pc)
    require(tuple(sites) == SITES, 'particle direct call inventory differs')
    require(all(struct.pack('<I', value) not in rom for value in (ROOT, ROOT | 1)),
            'unexpected encoded particle entry pointer')
    digest = hashlib.sha256(rom).hexdigest()
    require(digest == ROM_SHA256, 'particle reference inventory requires the approved USA image')
    return dict(raw_thumb_bl_sites=sites, raw_even_entry_words=0, raw_thumb_entry_words=0,
                rom_bytes=len(rom), rom_sha256=digest)


def check_ops(cs, data, base, expected, message):
    for pc, (mnemonic, operands) in expected.items():
        item = decode(cs, data, base, pc)
        require((item.mnemonic, item.op_str) == (mnemonic, operands), message)


def particle_abi(proof, data):
    cs = decoder()
    check_ops(cs, data, ROOT, {
        0x080A97F8: ('ldr', 'r2, [sp, #0x1c]'), 0x080A97FA: ('ldr', 'r3, [sp, #0x20]'),
        0x080A97FC: ('lsls', 'r3, r3, #0x18'), 0x080A97FE: ('lsrs', 'r6, r3, #0x18'),
        0x080A981C: ('adds', 'r3, r4, #0'), 0x080A983E: ('ldrsh', 'r0, [r3, r1]'),
        0x080A9932: ('adds', 'r0, r4, #0'), RETURN: ('bx', 'r1'),
    }, 'particle entry parameters, retained halfword alias or returned entry differs')
    for i in range(3):
        check_ops(cs, data, ROOT, {
            0x080A9800+4*i: ('lsls', f'r{i}, r{i}, #0x10'),
            0x080A9802+4*i: ('asrs', f'r{i}, r{i}, #0x10'),
        }, 'particle projection inputs require three sign-extended halfwords')
    # The bounded-buffer callee interpreter separately follows both actual
    # pointers through all reachable operations, including its 36-byte frame.
    projection = proof.span(PROJECT)
    check_ops(cs, projection, PROJECT, {
        0x0801C9D2: ('strh', 'r0, [r3]'), 0x0801C9D8: ('ldr', 'r7, [sp, #0x24]'),
        0x0801C9DA: ('strh', 'r1, [r7]'),
    }, 'particle projection requires both actual output halfword stores')


def caller_arguments(data, address, site, cs):
    # Identify the writes assembling the two outgoing stack words. Along this
    # basic block require its selector immediate to reach the final STR unchanged.
    flag_pc, reg, value, z_pc, z_reg = {
        SITES[0]: (0x080AE114, ARM_REG_R4, 0, 0x080AE112, 'r5'),
        SITES[1]: (0x080B2D5A, ARM_REG_R5, 0, 0x080B2D74, 'r4'),
        SITES[2]: (0x080B2E14, ARM_REG_R4, 1, 0x080B2E12, 'r4'),
    }[site]
    reg_name = cs.reg_name(reg)
    check_ops(cs, data, address, {
        flag_pc: ('movs', f'{reg_name}, #{value}'), z_pc: ('str', f'{z_reg}, [sp]'),
        site-2: ('str', f'{reg_name}, [sp, #4]'),
    }, 'particle caller lacks its two outgoing arguments')
    for pc in range(flag_pc+2, site, 2):
        item = decode(cs, data, address, pc)
        require(reg not in item.regs_access()[1] and item.size == 2 and item.id != ARM_INS_B
                and ARM_REG_PC not in item.regs_access()[1], 'particle caller selector overwritten')
    return dict(z_store=z_pc, selector_store=site-2, selector=value, selector_definition=flag_pc)


def first_caller_route(data, cs):
    """Replay one real entry-to-call path, including case four of the guarded native table."""
    # Other switch cases and unchosen conditional branches make no claim about
    # the feasibility of this path. They cannot change a BL's return address.
    target_edges = {0x080AD68C: 0x080AD6CC, 0x080AD6DC: 0x080AD8E2, 0x080AD8EC: 0x080AD8F2}
    guard = {
        0x080AD8E8: ('ldrh', 'r0, [r0]'), 0x080AD8EA: ('cmp', 'r0, #6'),
        0x080AD8EC: ('bls', '#0x80ad8f2'), 0x080AD8EE: ('bl', '#0x80ae7c6'),
        0x080AD8F2: ('lsls', 'r0, r0, #2'), 0x080AD8F4: ('ldr', 'r1, [pc, #8]'),
        0x080AD8F6: ('adds', 'r0, r0, r1'), 0x080AD8F8: ('ldr', 'r0, [r0]'),
        0x080AD8FA: ('mov', 'pc, r0'),
    }
    check_ops(cs, data, FIRST, guard, 'particle caller dispatch guard changed')
    literal = ((0x080AD8F4 + 4) & ~3) + 8
    table = struct.unpack_from('<I', data, literal-FIRST)[0]
    require(table == 0x080AD904, 'particle caller table base differs')
    targets = struct.unpack_from('<7I', data, table-FIRST)
    require(all(target % 2 == 0 and table + 28 <= target < SPANS[FIRST] for target in targets)
            and targets[4] == 0x080AE0D2, 'particle caller table case outside owner or wrong case four')
    pc = FIRST
    path = []
    while pc != SITES[0]:
        require(pc not in path and len(path) < 100, 'particle caller route does not reach its call')
        path.append(pc)
        item = decode(cs, data, FIRST, pc)
        if pc == 0x080AD8FA:
            pc = targets[4]
        elif pc in target_edges:
            require(item.id == ARM_INS_B and item.operands[0].imm == target_edges[pc],
                    'particle caller witness branch differs')
            pc = target_edges[pc]
        elif item.id == ARM_INS_BL:
            require(not FIRST <= item.operands[0].imm < SPANS[FIRST], 'unexpected local BL on caller route')
            pc += item.size
        elif item.id == ARM_INS_B:
            require(item.mnemonic != 'b', 'unexpected unconditional branch on particle caller route')
            pc += item.size
        else:
            require(ARM_REG_PC not in item.regs_access()[1] and item.mnemonic != 'bx',
                    'unresolved particle caller route transfer')
            pc += item.size
    require(set(target_edges) <= set(path) and 0x080AD8FA in path, 'particle caller route bypasses dispatch')
    return dict(route_instructions=len(path)+1, taken_branches=sorted(map(list, target_edges.items())),
                dispatch=0x080AD8FA, table=table, case=4, destination=targets[4])


def continuation(data, address, site, cs):
    item = decode(cs, data, address, site)
    require(item.id == ARM_INS_BL and item.operands[0].imm == ROOT, 'incorrect incoming particle BL')
    start = site + item.size
    require(match.stack_alias_overwritten_before_use(data, address, start, ARM_REG_R3, cs),
            'particle continuation does not overwrite R3 on every path before use')
    # Record the exact reached instructions on this revision. The general liveness
    # proof above rejects early observations, unhandled transfers and live loops.
    pc = start
    visited = []
    while True:
        require(pc not in visited and len(visited) < 24, 'unexpected particle continuation extent')
        visited.append(pc)
        op = decode(cs, data, address, pc)
        read, written = op.regs_access()
        require(ARM_REG_R3 not in read, 'particle continuation read expired R3')
        if ARM_REG_R3 in written:
            require((pc, op.mnemonic, op.op_str) == KILLS[site], 'particle R3 overwrite differs')
            break
        if op.id == ARM_INS_B:
            require(op.mnemonic == 'b', 'unexpected split in exact particle continuation')
            pc = op.operands[0].imm
        else:
            pc += op.size
    return dict(caller=address, call=site, path=visited, overwrite=pc, instruction=op.mnemonic+' '+op.op_str,
                setup_example=caller_arguments(data, address, site, cs))


def consumers(proof):
    import owner_admission_profile as owner

    cs = decoder()
    records = []
    for address, end in SPANS.items():
        data = proof.rom[address-match.ROM_BASE:end-match.ROM_BASE]
        named.validate_owner(data, address, proof.rom, proof.mapping, proof.index)
        if address == FIRST:
            witness = first_caller_route(data, cs)
            sites = SITES[:1]
        else:
            ref = owner.refine(data, address, proof.mapping)
            ins, _, _, calls, words = graph.graph(data, address, ref)
            graph.partition(data, address, ref, ins, words)
            sites = SITES[1:]
            require(tuple(sorted(pc for pc, target in calls.items() if target == ROOT)) == sites,
                    'closed particle caller lacks its two incoming call sites')
            witness = dict(closed_instructions=len(ins), switches=len(ref['word_switches']))
        records.append(dict(address=address, end=end, sha256=hashlib.sha256(data).hexdigest(),
                            witness=witness, continuations=[continuation(data, address, s, cs) for s in sites]))
    return records


class ParticleReturnMixin:
    def bind_particle(self, address, data, calls):
        import owner_admission_profile as owner

        require(address == ROOT and len(data) == 340 and self.span(address) == data and calls == CALLS,
                'particle initializer root, extent or native call set differs')
        ref = owner.refine(data, address, self.mapping)
        ins, edges, branches, native_calls, words = graph.graph(data, address, ref)
        graph.partition(data, address, ref, ins, words)
        require(len(ins) == 152 and not branches and not words and native_calls == calls
                and [pc for pc in edges if not edges[pc]] == [RETURN], 'particle initializer graph differs')
        self.particle_data = data
        self.references = raw_references(self.rom)
        self.consumers = consumers(self)
        particle_abi(self, data)
        self.projected_halfwords = False
        self.expired_r3 = False

    def check_arguments(self, address, arguments, stack, incoming, protected, **context):
        if context.get('site') == PROJECTION_SITE:
            require(address == PROJECT and not self.active and len(stack) == 7
                    and arguments == {ARM_REG_R3: -24} and incoming == {0: -22} and protected == {-28},
                    'particle projection requires distinct in-frame halfwords at entry SP-24 and SP-22')
            self.projected_halfwords = True
        return super().check_arguments(address, arguments, stack, incoming, protected, **context)

    def project_return(self, data, address, site, aliases):
        if (self.active or address != ROOT or site != RETURN or data != getattr(self, 'particle_data', None)
                or not self.projected_halfwords or not self.consumers or type(aliases.get(ARM_REG_R3)) is not int
                or aliases != {ARM_REG_R3: -22}):
            return aliases
        self.expired_r3 = True
        return {}

    def particle_manifest(self):
        require(self.expired_r3 and self.projected_halfwords, 'particle proof lacks its actual returned alias')
        return dict(root=ROOT, return_site=RETURN, returned_scratch=['r3', -22],
                    projection_call=PROJECTION_SITE, projection_callee=PROJECT, frame_bytes=28,
                    input_coordinates='sign-extended s16 in r0/r1/r2 at projection', selector_width_bits=8,
                    output_halfwords=[['r3', -24], ['outgoing_sp+0', -22]],
                    halfword_store_sites=[0x0801C9D2, 0x0801C9DA], result_register='r0',
                    reference_inventory=self.references, callers=self.consumers,
                    setup_scope='Selector values describe the three decoded setup sequences. The R3 '
                                'overwrite proof starts at each BL continuation for every selector value.',
                    producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                    limits='Normal returns to the three identified direct ROM calls. Computed entries, '
                           'asynchronous observers, external pointer validity and pool capacity are unproved. '
                           'Runtime result is an unconstrained scalar; no termination or numeric theorem.')
