"""One initialized white palette halfword and one independent child descriptor."""
import hashlib
from pathlib import Path
import re
import struct

import bios_cpuset_fill_profile as bios

SELECTOR = 'conditional-scheduler-sdk-halfword-fill-v1'
SCHEMA = 'elf-symbol-thumb-' + SELECTOR
SCHEDULER = 0x08005B6C
# Owner, complete span, CpuSet call, destination, SP-relative scratch offset.
OWNERS = {
    0x0811D4A0: (348, 0x0811D502, 0x03003940, 0),
    0x0811E034: (452, 0x0811E092, 0x03003920, 16),
}
CONTROL = 0x01000010
WHITE = 0x7fff
HEADERS = {'include/ffta.h': '1e398c24c0eb33e722c9f4574e5df4ee1c6e3d0c9e2d40cd83f911716be54a2f',
           'include/control_flags.h': 'c131fe86127a1e141328bae3b02350dd16464f8e5db196eb65fa13b876613cff'}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def fill_evidence(data, address, wrapper):
    """Decode the complete local preparation, every literal value and the Thumb BL."""
    require(address in OWNERS, 'expected an indexed scene palette-fill owner')
    size, site, destination, offset = OWNERS[address]
    require(len(data) == size and wrapper == bios.WRAPPER, 'unexpected scene owner or CpuSet wrapper')
    start = site - 14
    instructions = struct.unpack_from('<7H', data, start - address)
    store_address, color, move, store, dest, control, call_argument = instructions
    sp_to_r1 = 0x4669 if offset == 0 else 0xa900 | offset // 4
    sp_to_r0 = 0x4668 if offset == 0 else 0xa800 | offset // 4
    require((store_address, move, store, call_argument) == (sp_to_r1, 0x1c10, 0x8008, sp_to_r0),
            'CpuFill16 requires a single initialized STRH and the same R0 source')
    for pc, opcode, register, expected in ((start+2, color, 2, WHITE), (start+8, dest, 1, destination),
                                          (start+10, control, 2, CONTROL)):
        require(opcode >> 8 == 0x48 + register, 'CpuFill16 requires its three PC-relative loads')
        literal = ((pc + 4) & ~3) + 4 * (opcode & 255)
        require(address <= literal <= address + size - 4 and
                struct.unpack_from('<I', data, literal-address)[0] == expected,
                'CpuFill16 color, external destination or control changed')
    delta = bios.ADDRESS - site - 4
    require(struct.unpack_from('<HH', data, site-address) ==
            (0xf000 | (delta >> 12 & 2047), 0xf800 | (delta >> 1 & 2047)),
            'expected direct Thumb call to CpuSet')
    return dict(site=site, store=start+6, current_sp_offset=offset,
                halfword=WHITE, destination=destination, control=CONTROL)


def bind(proof, data, address, edges, calls):
    require(list(calls.values()).count(SCHEDULER) == 1 and list(calls.values()).count(bios.ADDRESS) == 1,
            'scene fill requires one direct scheduler and one CpuSet')
    require(len(proof.scheduler_call_sites['sites']) == 1 and not proof.scheduler_call_sites['looped_sites'],
            'scene fill requires an unlooped direct scheduler site')
    proof._root_fill = bios.BiosFillProof(data, address, proof.rom, proof.mapping, proof.index, calls)
    evidence = fill_evidence(data, address, proof._root_fill.wrapper)
    site = evidence['site']
    require(calls.get(site) == bios.ADDRESS, 'CpuFill16 call must be reachable')
    for here in range(site-12, site+1, 2):
        require([prev for prev, successors in edges.items() if here in successors] == [here-2],
                'CpuFill16 initialization must dominate the call on every path')
    scheduler = proof.scheduler_call_sites['sites'][0]['site']
    for first, other in ((site, scheduler), (scheduler, site)):
        seen = set()
        pending = list(edges[first])
        while pending:
            node = pending.pop()
            if node in seen:
                continue
            require(node not in (first, other), 'scene fill and scheduler must occur on separate paths')
            seen.add(node)
            pending.extend(edges[node])
    proof.scene_fill = evidence


def check_fill(proof, address, aliases, stack, slots, site, words):
    import match
    import named_data_buffer_profile as named
    offset = proof.scene_fill['current_sp_offset'] - 4 * len(stack)
    require(aliases == {match.ARM_REG_R0: offset}, 'CpuFill16 must carry only its own source address')
    return named.check_bios_fill_call(proof, address, aliases, stack, slots, site, words)


def manifest(proof, scheduler):
    from capstone.arm import ARM_REG_R2
    from named_data_buffer_profile import BiosFillSourceProof
    require(len(proof._root_fill.observations) == 1 and len(scheduler['observations']) == 1,
            'scene proof must witness both local sites')
    site, offset, width, _, _ = next(iter(proof._root_fill.observations))
    require(site == proof.scene_fill['site'] and width == 2, 'scene fill must read one private halfword')
    descriptor = scheduler['observations'][0]
    require(descriptor['aliases'] == [(ARM_REG_R2, descriptor['descriptor_offset'])] and
            not descriptor['other_pointer_words'] and not descriptor['payload_words'],
            'scene scheduler permits only its R2 descriptor and no private pointer words')
    require(offset + 4 == descriptor['descriptor_offset'] and
            proof.scene_fill['current_sp_offset'] - descriptor['frame_bytes'] == offset,
            'fill word must immediately precede the descriptor in the same frame')
    return dict(scheduler, sdk_halfword=proof.scene_fill, bios=BiosFillSourceProof.bios_manifest(proof),
                fill_source_assumption=bios.LOCAL_SOURCE_CONTRACT,
                producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())


def source_offset(text, address):
    """Recognize one block-scoped CpuFill16 temporary and its only address use."""
    import plausible
    from sdk_cpuset_halfword import TOKEN
    if address not in OWNERS or any(marker in text for marker in ('\\', '??', '%:', '\0')):
        return None
    code = plausible.strip_comments_and_strings_keep_strings(text)
    header = 'ffta.h' if address == 0x0811D4A0 else 'control_flags.h'
    include = re.match(r'\s*#\s*include[ \t]+"' + re.escape(header) + r'"[ \t]*\n', code)
    if not include or '#' in code[include.end():]:
        return None
    tokens = list(TOKEN.finditer(code, include.end()))
    words = [token[0] for token in tokens]
    destination = f'data_{OWNERS[address][2]:08X}'
    pattern = TOKEN.findall('{ volatile u16 fill = 0x7FFF; func_0814186C((const void *)&fill,' +
                            destination + ',0x01000010); }')
    matches = [i for i in range(len(words)) if words[i:i+len(pattern)] == pattern]
    if len(matches) != 1 or words.count('fill') != 2 or words.count('func_0814186C') != 2:
        return None
    return tokens[matches[0]+1].start()


def qualifier(text, tree, project, address, closure):
    from rompath import rom_path
    offset = source_offset(text, address)
    relpath = f'src/{address:08X}.c'
    includes = {'include/ffta.h'} if address == 0x0811D4A0 else set(HEADERS)
    if offset is None or closure != ({relpath, *includes}, []):
        return None
    if any(hashlib.sha256((tree / name).read_bytes()).hexdigest() != HEADERS[name] for name in includes):
        return None
    path = rom_path(project, required=False)
    if not path:
        return None
    with open(path, 'rb') as rom:
        rom.seek(address - 0x08000000)
        data = rom.read(OWNERS[address][0])
        rom.seek(bios.ADDRESS - 0x08000000)
        fill_evidence(data, address, rom.read(len(bios.WRAPPER)))
    return offset
