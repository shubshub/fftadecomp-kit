"""Buffer owners that copy small constant ROM tables into private stack objects.

agbcc lowers `u8 a[3] = {0, 20, 40};` to a read-only constant plus a call to
the ROM copy helper func_081443FC, and the same copy can be spelled as an
explicit call with a named ROM table.  The named-data buffer walk refuses both
because it follows the helper into its word-copy loop and sees the destination
alias used in alignment arithmetic.

`named-data-buffer-rom-table-copy-v1` keeps the walk and its alias rules and
replaces only the step that enters the helper.  A call to the pinned helper is
summarised when all of the following hold:

* the helper is the exact canonical 98-byte copy routine, indexed as such, and
  its byte-copy path for counts up to 15 is pinned; no instruction of the
  helper writes a register above R5, and R4/R5 are saved and restored;
* R1 is a constant read from a code literal of the owner or of a walked callee
  and R2 is an exact constant count from 1 to 15; R0 is a tracked stack alias
  and the only alias passed;
* the whole destination range lies in allocated private words, below the
  current frame and clear of every pointer-bearing word;
* the source range lies in ROM and is either the initialiser the compiler
  emitted into the object's read-only section (the bytes of that section are
  bound to the ROM bytes at the address the owner's literals resolve to) or a
  table named exactly by an evidence-backed data symbol.

The destination alias is returned in R0, as the helper does; every other
argument register is dead.  Later uses of the stack object are ordinary
private-frame accesses under the unchanged buffer rules, and the object may
still be passed to callees that the existing buffer proof bounds.  Nothing is
proved about the physical stack, the readability of the source, or the C object
lifetime; those stay explicit conditions in the evidence.
"""
import hashlib
import struct

import compiler_copy80_prerequisite as copy80
import match
import named_data_buffer_profile as named
from local_rom_halfword_table_profile import COPY_PATH, COPY_SHA256

SELECTOR = named.ROM_TABLE_COPY_SELECTOR
SCHEMA = named.ROM_TABLE_COPY_SCHEMA
# The stack-index selector is this walk plus the explicit variable-index premise contract.
SELECTORS = (SELECTOR, named.STACK_INDEX_SELECTOR)
SCHEMAS = (SCHEMA, named.STACK_INDEX_SCHEMA)
CONTROL_FLOW = ('complete named-data owner with ROM-proved bounded buffer callees and '
                'constant ROM tables copied into private stack objects by the pinned copy helper')
HELPER = 0x081443FC
MAX_COUNT = 15
MAX_DEPENDENCIES = named.MAX_DEPENDENCIES
MAX_COPIES = 32
CONTRACT = ('Conditional: the pinned helper copies exactly the constant count of source bytes '
            'to the destination in ascending order, returns the destination in R0, preserves '
            'R4-R11 and SP, and clobbers R1-R3. Source ROM bytes are immutable; the destination '
            'range and the helper save frame are live ordinary memory disjoint from the source and '
            'from code. No physical stack, readability, nonalias or C lifetime fact is proved.')
CALLER_REGISTERS = (match.ARM_REG_R0, match.ARM_REG_R0 + 1, match.ARM_REG_R0 + 2,
                    match.ARM_REG_R0 + 3)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def helper_facts(rom, mapping, index):
    """Authenticate the complete helper and its register and path facts."""
    identity = copy80.verify_helper(HELPER, rom, mapping, index)
    body = rom[HELPER - match.ROM_BASE:HELPER - match.ROM_BASE + 98]
    require(sha(body) == COPY_SHA256 and all(
        struct.unpack_from('<H', body, pc)[0] == word for pc, word in COPY_PATH.items()),
        'canonical copy helper byte-loop path differs')
    decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
    decoder.detail = True
    written = set()
    for item in decoder.disasm(body, HELPER):
        written.update(item.regs_access()[1])
    general = {r for r in written if match.ARM_REG_R0 <= r <= match.ARM_REG_R0 + 12}
    require(written <= general | {match.ARM_REG_SP, match.ARM_REG_PC, match.ARM_REG_CPSR} and
            general <= {match.ARM_REG_R0 + n for n in range(6)},
            'copy helper writes a register above R5')
    written = general
    return dict(helper=HELPER, body_sha256=sha(body), instructions=49,
                written_registers=sorted(f'r{r - match.ARM_REG_R0}' for r in written),
                saved_and_restored=['r4', 'r5'], byte_path_counts=[1, MAX_COUNT],
                partition=identity['partition'])


def literal_value(instruction, data, address):
    """The code literal a Thumb PC-relative LDR reads, or None."""
    operands = instruction.operands
    if instruction.mnemonic != 'ldr' or instruction.size != 2 or len(operands) != 2 or \
            instruction.cc not in (match.ARM_CC_AL, match.ARM_CC_INVALID) or \
            operands[1].type != match.ARM_OP_MEM or operands[1].mem.base != match.ARM_REG_PC or \
            operands[1].mem.index or instruction.writeback:
        return None
    offset = ((instruction.address + 4) & ~3) + operands[1].mem.disp - address
    if offset < 0 or offset + 4 > len(data) or offset % 4:
        return None
    return struct.unpack_from('<I', data, offset)[0]


def check_rodata(rodata, rom, data, address):
    """Bind the object's read-only initialiser bytes to the real ROM bytes."""
    if rodata is None:
        return None
    require(type(rodata) is dict and set(rodata) == {'base', 'size', 'sha256', 'sites'} and
            type(rodata['base']) is int and type(rodata['size']) is int and rodata['size'] > 0 and
            type(rodata['sha256']) is str and type(rodata['sites']) is list and rodata['sites'],
            'malformed read-only initialiser binding')
    base, size = rodata['base'], rodata['size']
    require(match.ROM_BASE <= base and base + size <= match.ROM_BASE + len(rom) and
            (base + size <= address or address + len(data) <= base),
            'read-only initialiser lies outside ROM or overlaps the owner')
    require(sha(rom[base - match.ROM_BASE:base - match.ROM_BASE + size]) == rodata['sha256'],
            'ROM table bytes differ from the compiler initialiser bytes')
    for site, addend in rodata['sites']:
        require(type(site) is int and type(addend) is int and 0 <= addend < size and
                0 <= site <= len(data) - 4 and site % 4 == 0 and
                struct.unpack_from('<I', data, site)[0] == base + addend,
                'owner literal does not resolve into the initialiser at its recorded offset')
    return dict(rodata, sites=[list(site) for site in rodata['sites']])


class RomTableCopyBufferProof(named.NamedDataBufferProof):
    """Named-data buffer walk with the pinned ROM copy helper summarised."""

    def __init__(self, rom, mapping, index, objects, *, rodata=None, data=None, address=None):
        super().__init__(rom, mapping, index, objects)
        self.names = match.parse_data_symbols(objects)
        self.points = set(self.names.values())
        self.rodata = check_rodata(rodata, rom, data, address) if rodata is not None else None
        self.copies = {}
        self.helper = None

    def argument_constants(self, constants):
        return {register: value for register, value in constants.items()
                if register in CALLER_REGISTERS[1:3]}

    def extra_constant(self, instruction, data, address, constants):
        value = literal_value(instruction, data, address)
        return value if value is not None else super().extra_constant(instruction, data, address, constants)

    def source_kind(self, source, count):
        end = source + count
        require(match.ROM_BASE <= source and end <= match.ROM_BASE + len(self.rom),
                'copy source range is outside ROM')
        if self.rodata is not None and self.rodata['base'] <= source and \
                end <= self.rodata['base'] + self.rodata['size']:
            return 'object-initializer'
        require(source in self.points, 'copy source is neither the compiler initialiser nor a named ROM table')
        # Named symbols carry no size; the next named object is the only known end of this one.
        require(not any(source < point < end for point in self.points),
                'copy runs past the named ROM table into the next named object')
        return 'named-rom-table'

    def check_arguments(self, address, arguments, stack, incoming, protected, *, constants=None,
                        site=None, words=None, frame_base=None, root_frame=None, watched=()):
        if address != HELPER or not arguments:
            return super().check_arguments(address, arguments, stack, incoming, protected,
                constants=constants, site=site, words=words, frame_base=frame_base,
                root_frame=root_frame, watched=watched)
        try:
            require(set(arguments) == {match.ARM_REG_R0} and not incoming and not words,
                    'copy helper receives only a destination alias and no stack-passed pointers')
            constants = constants or {}
            source, count = constants.get(match.ARM_REG_R0 + 1), constants.get(match.ARM_REG_R0 + 2)
            require(type(source) is int and type(count) is int and 1 <= count <= MAX_COUNT,
                    'copy source must be a constant literal and the count an exact constant from 1 to 15')
            destination = arguments[match.ARM_REG_R0]
            require(destination in range(-4 * len(stack), 0), 'copy destination is outside the live frame')
            for offset in range(destination, destination + count):
                self.access(offset, 1, stack)
            require(not any(destination < slot + 4 and destination + count > slot for slot in protected),
                    'copy destination overlaps a pointer-bearing word')
            kind = self.source_kind(source, count)
            if self.helper is None:
                self.helper = helper_facts(self.rom, self.mapping, self.index)
            self.dependencies[address] = self.rom[address - match.ROM_BASE:address - match.ROM_BASE + 98]
            table = self.rom[source - match.ROM_BASE:source - match.ROM_BASE + count]
            record = dict(site=site, source=source, source_kind=kind, count=count,
                          destination_offset=destination, bytes_sha256=sha(table))
            previous = self.copies.setdefault(site, record)
            require(previous == record, 'copy site has different destinations or sources on different paths')
            require(len(self.copies) <= MAX_COPIES, 'too many ROM table copies')
        except ValueError as error:
            raise ValueError(f'buffer callee 0x{address:08X}: {error}') from error
        return self.word_result({match.ARM_REG_R0: destination}, {})

    def copy_manifest(self):
        require(self.copies and self.helper is not None, 'no ROM table copy was proved')
        return dict(schema=SCHEMA, helper=self.helper, contract=CONTRACT,
                    copies=[self.copies[site] for site in sorted(self.copies)],
                    object_initializer=self.rodata,
                    conditions=[
                        'source ROM bytes equal the recorded table bytes and are immutable',
                        'every destination range is live ordinary writable memory of the owner frame',
                        'the helper save frame below the owner frame is live ordinary memory',
                        'source, destination, helper frame and code ranges are mutually disjoint',
                        'no asynchronous modification of the copied or copying memory',
                        'compatible returning ordinary ABI; C object lifetime is separate'],
                    physical_access_proved=False, nonaliasing_proved=False)


def rodata_section(image):
    """The single plain read-only data section of an ELF object, or None."""
    found = [index for index, section in enumerate(image['sections'])
             if section[2] & 2 and section[5] and index != image['text_index']]
    if not found:
        return None
    require(len(found) == 1, 'only one allocated section besides .text is supported')
    index = found[0]
    section = image['sections'][index]
    require(image['section_names'][index] == '.rodata' and section[1] == 1 and section[2] == 2 and
            section[8] in (1, 2, 4) and 0 < section[5] <= 4096 and
            (image['type'] != 1 or section[3] == 0),
            'allocated section must be a plain read-only .rodata of bounded size')
    require(not any(image['sections'][n][7] == index for n in image['relocations']),
            'read-only initialiser carries relocations')
    return index, image['section_data'][index], section[8]


def rodata_binding(image, address, rom):
    """Bind a compiler initialiser section to the ROM bytes its literals address.

    The sites are the owner's literals against the .rodata section symbol. The
    base is the address those literals resolve to in the ROM and must agree over
    every site; the section bytes must then equal the ROM bytes there.
    """
    section = rodata_section(image)
    sites = []
    for number in image['relocations']:
        table = image['sections'][number]
        symbols = image['symbol_tables'].get(table[6])
        if table[1] != 9 or table[7] != image['text_index'] or symbols is None:
            continue
        for position in range(0, table[5], 8):
            site, info = struct.unpack_from('<II', image['section_data'][number], position)
            target = symbols[info >> 8]
            if info & 255 == 2 and section is not None and target['section'] == section[0]:
                sites.append((site, struct.unpack_from('<I', image['text'], site)[0]))
    if section is None:
        return None
    require(sites, 'read-only initialiser is never referenced by an owner literal')
    raw, alignment = section[1], section[2]
    bases = {struct.unpack_from('<I', rom, address - match.ROM_BASE + site)[0] - addend
             for site, addend in sites}
    require(len(bases) == 1, 'owner literals disagree on the initialiser address')
    base, = bases
    require(base % alignment == 0 and match.ROM_BASE <= base and
            base + len(raw) <= match.ROM_BASE + len(rom) and
            (base + len(raw) <= address or address + len(image['text']) <= base),
            'initialiser address is misaligned, outside ROM or inside the owner')
    require(all(0 <= addend < len(raw) for _, addend in sites), 'literal addend outside the initialiser')
    require(rom[base - match.ROM_BASE:base - match.ROM_BASE + len(raw)] == raw,
            'ROM table bytes differ from the compiler initialiser bytes')
    return dict(base=base, size=len(raw), sha256=sha(raw), sites=sorted([site, addend] for site, addend in sites))


def check_linked_rodata(linked, rodata, rom):
    """The linked image carries exactly the bound initialiser at its ROM address."""
    sections = [(index, section) for index, section in enumerate(linked['sections'])
                if section[2] & 2 and section[5] and index != linked['text_index']]
    if rodata is None:
        require(not sections, 'unexpected allocated section in linked owner')
        return
    require(len(sections) == 1 and linked['section_names'][sections[0][0]] == '.rodata' and
            sections[0][1][3] == rodata['base'] and sections[0][1][5] == rodata['size'] and
            sections[0][1][1] == 1 and sections[0][1][2] == 2,
            'linked read-only section differs from the bound initialiser')
    raw = linked['section_data'][sections[0][0]]
    require(raw == rom[rodata['base'] - match.ROM_BASE:rodata['base'] - match.ROM_BASE + rodata['size']] and
            sha(raw) == rodata['sha256'], 'linked initialiser bytes differ from the ROM table bytes')


def memcpy_target(image, target):
    """The compiler's `memcpy` is the pinned ROM copy helper, at its undefined symbol."""
    require(target['name'] == 'memcpy' and target['size'] == 0 and target['type'] in (0, 2) and
            target['bind'] == 1 and not target['value'] and not target['section'] and
            sum(row['name'] == 'memcpy' for row in image['symbols']) == 1,
            'copy requires the unique undefined compiler memcpy symbol')
    return HELPER


def name_calls(calls, bindings):
    """Report the compiler's memcpy sites under their original symbol name."""
    names = {site: name for site, name in (bindings or {}).get('calls', []) if name == 'memcpy'}
    helper = f'func_{HELPER:08X}'
    require(all(name == helper for site, name in calls if site in names),
            'compiler memcpy binding does not reach the pinned copy helper')
    return [[site, names.get(site, name)] for site, name in calls]
