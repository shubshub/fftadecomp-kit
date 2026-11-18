"""Linker absolute used as the maxScanlines byte in the USA m4a MPlayExtender."""
import hashlib
import json
import re
import struct

SELECTOR = 'addressed-m4a-extender-bios-fill-max-lines-v1'
SCHEMA = 'elf-symbol-thumb-' + SELECTOR
SYMBOL = 'gMaxLines'
ADDRESS = 0x081453F8
SIZE = 280
OFFSET = 0x110
LOAD = 0x08145478
STORE = 0x0814547C
MIXER_LOAD = 0x08145430
OWNER_SHA = '0ff9bedc7731c400d639fcdca45671c148fcbede4802fc2afd25a26b2bc849e3'


# Slot, entry, exclusive end, local instruction count, owner ABS32 offset.
# The independent ROM command table contains each same Thumb pointer.
CALLBACKS = ((17, 0x08145070, 0x08145082, 7, 0xE4),
             (19, 0x08145084, 0x08145096, 7, 0xE8),
             (29, 0x08145008, 0x08145048, 32, 0xF0))


def source_use(preprocessed):
    from plausible import strip_comments_and_strings
    code = strip_comments_and_strings(preprocessed)
    declared = re.findall(r"\bextern\s+char\s+gMaxLines\s*\[\s*\]\s*;", code)
    assigned = re.findall(r"\bsoundInfo\s*->\s*maxScanlines\s*=\s*"
                          r"\(\s*\(\s*u32\s*\)\s*gMaxLines\s*\)\s*;", code)
    if len(declared) != 1 or len(assigned) != 1 or len(re.findall(r"\bgMaxLines\b", code)) != 2:
        raise ValueError("m4a requires the historical declaration and scalar maxScanlines assignment")


def callbacks(rom, mapping, literals):
    entries = json.loads(mapping)
    result = []
    for slot, entry, end, count, offset in CALLBACKS:
        rows = [r for r in entries if int(r['rom'], 16) == entry]
        table_site = 0x0836D098 + 4*slot
        if table_site - 0x08000000 + 4 > len(rom):
            raise ValueError("missing original m4a command table")
        observed = struct.unpack_from('<I', rom, table_site-0x08000000)[0]
        if (len(rows) != 1 or int(rows[0]['end'], 16) != end or rows[0]['mode'] != 'thumb'
                or rows[0]['instrs'] != count or observed != entry | 1 or
                literals.get(offset) != (f'func_{entry:08X}', entry | 1)):
            raise ValueError("m4a callback entry differs from its index, relocation or ROM table")
        result.append([slot, entry, end, count, offset, table_site])
    return result


def symbol_value(rom, address, offset, addend, objects):
    if (address != ADDRESS or (offset, addend) != (OFFSET, 0) or
            type(offset) is not int or type(addend) is not int or SYMBOL in objects):
        raise ValueError('m4a requires its unmapped linker absolute at the original zero-addend relocation')
    start = ADDRESS - 0x08000000
    body = rom[start:start+SIZE]
    if hashlib.sha256(body).hexdigest() != OWNER_SHA or struct.unpack_from('<I', body, OFFSET)[0] != 80:
        raise ValueError('m4a max-lines linker value requires the original MPlayExtender ROM body')
    return 80


def split_records(records, rom, address, data, objects):
    if any(not isinstance(row, (list, tuple)) or len(row) != 3 for row in records):
        raise ValueError('m4a absolute requires complete typed binding rows')
    matches = [row for row in records if row[1] == SYMBOL]
    if len(matches) != 1:
        raise ValueError('m4a requires one original gMaxLines relocation')
    offset, _, addend = matches[0]
    value = symbol_value(rom, address, offset, addend, objects)
    if len(data) != SIZE or struct.unpack_from('<I', data, offset)[0] != value:
        raise ValueError('linked m4a max-lines word differs from its ROM scalar')
    return [row for row in records if row[1] != SYMBOL]


def verify_use(data, instructions, edges, partition, calls, literals):
    from capstone.arm import ARM_REG_R4
    if literals.get(0xD4) != ('data_03007FF0', 0x03007FF0) or calls != {0x08145486: 0x0814186C}:
        raise ValueError('m4a max-lines needs the original mixer object and CpuSet call')
    rows = [r for r in partition['words'] if r['address'] == ADDRESS + OFFSET]
    if len(rows) != 1 or rows[0]['load_sites'] != [LOAD] or rows[0]['value'] != 80:
        raise ValueError('m4a linker scalar must have exactly its single reached PC-relative load')
    # The literal loads r0; strb r0,[r4,#12] is its sole consumer before mov r0,sp.
    # Protect each interior instruction from an alternative incoming edge.
    chain = bytes.fromhex('2348002120730091224a6846')
    if data[LOAD-ADDRESS:LOAD-ADDRESS+len(chain)] != chain:
        raise ValueError('m4a linker scalar must flow to the byte field and then be killed')
    for site in range(LOAD+2, LOAD+len(chain), 2):
        if {prev for prev, successors in edges.items() if site in successors} != {site-2}:
            raise ValueError('alternate predecessor in m4a max-lines store')
    # On every predecessor path, r4 is exactly the mixer pointer dereferenced
    # from the typed global. The conditional exit bypasses the store.
    pred = {site: set() for site in instructions}
    for origin, successors in edges.items():
        for dest in successors:
            pred[dest].add(origin)
    cone, pending = set(), [STORE]
    while pending:
        site = pending.pop()
        if site not in cone:
            cone.add(site)
            pending.extend(pred[site])
    # The load dominates the store. Starting at the function entry and
    # excluding the one mixer load must leave the store unreachable.
    visited, pending = set(), [ADDRESS]
    while pending:
        site = pending.pop()
        if site != MIXER_LOAD and site not in visited:
            visited.add(site)
            pending.extend(edges[site])
    pointer_sequence = bytes.fromhex('27480468')
    if (STORE in visited or data[MIXER_LOAD-2-ADDRESS:MIXER_LOAD+2-ADDRESS] != pointer_sequence or
            pred[MIXER_LOAD] != {MIXER_LOAD-2} or
            {site for site in cone if ARM_REG_R4 in instructions[site].regs_access()[1]} != {MIXER_LOAD} or
            any(site in cone for site in calls)):
        raise ValueError('m4a mixer register provenance differs')
    return dict(name=SYMBOL, kind='SHN_ABS/STT_NOTYPE', value=80, relocation=['R_ARM_ABS32', OFFSET, 0],
                load=LOAD-ADDRESS, byte_store=STORE-ADDRESS, mixer_member_offset=12, owner_sha256=OWNER_SHA,
                contract='historical GBA MAX_LINES takes the linker symbol value; the ROM loads 80 '
                         'and stores its low byte to SoundMixerState.maxScanlines; no pointee or storage')
