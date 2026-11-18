"""Native FLASH512_V130 full-sector comparison using the SDK's local copy of VerifyFlashSector_Core."""
import shlex
import struct
import sys

from addressed_signed_runtime_profile import original_function
import flash_bank_command as bank
import flash_reader_install as install
import flash_sector_erase as erase
import library_units as units
import match
from software_double_profile import indices, span_record
import unit_fpbit_source as capture

ADDRESS, END, COUNT = 0x08141BE0, 0x08141C78, 60
COMPARE, COMPARE_END, THUNK, CALLER = 0x08141BB0, 0x08141BDE, 0x08142250, 0x08141D10
NAME, CORE, BANK = 'func_08141BE0', 'func_08141BB0', 'func_0814189C'
WAIT, TYPE, VENEER = 'data_04000204', 'data_0200F370', '_call_via_r3'
OBJECTS = {WAIT: 0x04000204, TYPE: 0x0200F370}
TARGETS = {**OBJECTS, CORE: COMPARE, BANK: bank.OWNER, VENEER: THUNK}
TEXT_SITES = {44: (10, BANK), 72: (2, WAIT), 80: (2, TYPE), 84: (2, CORE), 88: (2, NAME),
              134: (10, VENEER), 148: (2, TYPE)}
DUPLICATES = (WAIT, TYPE, CORE, NAME)
TOOLCHAIN = bank.TOOL
SOURCE_DIGEST = '0843939c1ea634a2133818eacf96a8b63777c51b219545445333226942983e2b'
LABEL = 'flash sector verification'
SCHEMA = 'elf-symbol-thumb-flash512-verify-sector-v1'
CONTROL = ('* control flow: the initialized 64-KiB descriptors select a 4096-byte sector. The SDK copies its '
           'Thumb compare routine into a 256-byte local and returns zero or the cartridge address of the first '
           'different byte. The caller supplies a readable source sector.')


def require(value, message):
    if not value:
        raise ValueError('flash sector verification: ' + message)


def unit_owner(unit, address, orphan=None):
    return address == ADDRESS and install.unit_owner(unit, install.ADDRESS, orphan)


def link_object(runner, workspace, args, original, root, relative, rom, mapping, index):
    capture.reviewed_source(root, relative, ADDRESS,
                            (NAME, CORE, BANK, TYPE, WAIT, 'FlashType', 'FlashSector', 'FlashVerify'), SOURCE_DIGEST)
    install.original_pools(original, ADDRESS, END, TEXT_SITES, DUPLICATES, OBJECTS)
    runner.sh(f"{args.objcopy} --remove-section=.rodata --remove-section=.rel.rodata {shlex.quote(workspace + '/f.o')}")
    stripped = match.elf_image(runner.read_binary(workspace + '/f.o'))
    require(units.signature(original, ADDRESS) == units.signature(stripped, ADDRESS) and
            original_function(stripped, ADDRESS)['size'] == END - ADDRESS, 'removing the duplicate altered the owner')
    linked = match.link_typed_targets(runner, workspace, args, NAME, ADDRESS, TARGETS, OBJECTS)
    match.allocated_text_only(linked)
    owner, offset = match.function_record(linked, NAME, ADDRESS, True)
    require(linked['type'] == 2 and not linked['relocations'] and offset == 0 and owner['bind'] == 1 and
            owner['value'] == ADDRESS | 1 and owner['size'] == len(linked['text']) == END - ADDRESS,
            'incorrect linked extent or symbol')
    for name, address in TARGETS.items():
        symbol, = [item for item in linked['symbols'] if item['name'] == name]
        object_symbol = name in OBJECTS
        require((symbol['value'], symbol['section'], symbol['type'], symbol['bind'], symbol['size']) ==
                (address if object_symbol else address | 1, 0xFFF1, 1 if object_symbol else 2, 1, 0),
                'incorrect typed linked address')
    touched = {i for site in TEXT_SITES for i in range(site, site + 4)}
    require(all(i in touched or old == new for i, (old, new) in enumerate(zip(original['text'], linked['text']))),
            'linker changed non-relocated bytes')
    return linked['text']


def operations(instructions, start, stop):
    return [i.mnemonic + ' ' + i.op_str for pc, i in sorted(instructions.items()) if start <= pc < stop]


def frame_copy(graph, rom):
    instructions, _, calls, partition = graph
    require(calls == {ADDRESS + 44: bank.OWNER, ADDRESS + 134: THUNK}, 'unexpected call sites')
    words = {word['address'] - ADDRESS: word['value'] for word in partition['words']}
    require(words == {72: OBJECTS[WAIT], 76: 0xfffc, 80: OBJECTS[TYPE], 84: COMPARE | 1,
                      88: ADDRESS | 1, 148: OBJECTS[TYPE]}, 'incorrect hardware, descriptor or Thumb literal')
    require(operations(instructions, ADDRESS, ADDRESS + 10) == [
        'push {r4, r5, lr}', 'sub sp, #0x100', 'adds r5, r1, #0', 'lsls r3, r0, #0x10', 'lsrs r4, r3, #0x10'],
        'incorrect frame or parameter widths')
    # bank.provider authenticates the WAITCNT update, size guard and bank arguments up to +0x34.
    require(operations(instructions, ADDRESS + 0x34, ADDRESS + 0x6e) == [
        'ldr r3, [pc, #0x1c]', 'movs r0, #1', 'eors r3, r0', 'mov r2, sp', 'ldr r0, [pc, #0x18]',
        'ldr r1, [pc, #0x14]', 'subs r0, r0, r1', 'lsls r0, r0, #0xf', 'b #0x8141c48',
        'ldrh r0, [r3]', 'strh r0, [r2]', 'adds r3, #2', 'adds r2, #2', 'subs r0, r1, #1',
        'lsls r0, r0, #0x10', 'lsrs r1, r0, #0x10', 'cmp r1, #0', 'bne #0x8141c3c'], 'changed copy loop')
    source = words[84] ^ 1
    count = ((words[88] - words[84]) >> 1) & 0xffff
    require(source == COMPARE and source + 2 * count == ADDRESS and count * 2 <= 256 and
            rom[COMPARE_END - bank.BASE:ADDRESS - bank.BASE] == bytes(2),
            'copy must contain the adjacent compare owner and two inter-function padding bytes')
    require(operations(instructions, ADDRESS + 0x6e, END) == [
        'mov r3, sp', 'adds r3, #1', 'ldr r0, [pc, #0x20]', 'ldr r0, [r0]', 'ldrb r1, [r0, #8]',
        'lsls r4, r1', 'adds r1, r4, #0', 'movs r2, #0xe0', 'lsls r2, r2, #0x14', 'adds r1, r1, r2',
        'ldrh r2, [r0, #4]', 'adds r0, r5, #0', 'bl #0x8142250', 'add sp, #0x100',
        'pop {r4, r5}', 'pop {r1}', 'bx r1'], 'incorrect local dispatch, compare count or return')
    return dict(local_bytes=256, destination_from_entry_sp=-268, copied_halfwords=count,
                source=[source, source + 2 * count], code_bytes=COMPARE_END-COMPARE,
                inter_function_padding_bytes=2, padding_ROM_credit=0, thunk=THUNK)


def native_proof(data, rom, mapping, index, objects):
    bank.provider(rom)
    data_symbols = match.parse_data_symbols(objects)
    require({name: data_symbols.get(name) for name in OBJECTS} == OBJECTS and
            data == rom[ADDRESS-bank.BASE:END-bank.BASE], 'incorrect hardware/descriptor symbols or complete owner')
    entries, rows = indices(mapping, index)
    def owner(start, end, count):
        require(span_record(start, end, entries, rows, rom)['instrs'] == count, 'incorrect original extent or count')
        return erase.closure(rom[start-bank.BASE:end-bank.BASE], start, mapping, count=count)
    graph = owner(ADDRESS, END, COUNT)
    core, _, calls, _ = owner(COMPARE, COMPARE_END, 23)
    require(not calls and operations(core, COMPARE, COMPARE_END) == [
        'push {r4, r5, lr}', 'adds r5, r0, #0', 'adds r3, r1, #0', 'subs r4, r2, #1', 'cmp r2, #0',
        'beq #0x8141bd6', 'movs r2, #1', 'rsbs r2, r2, #0', 'ldrb r1, [r3]', 'ldrb r0, [r5]',
        'adds r5, #1', 'adds r3, #1', 'cmp r1, r0', 'beq #0x8141bd0', 'subs r0, r3, #1', 'b #0x8141bd8',
        'subs r4, #1', 'cmp r4, r2', 'bne #0x8141bc0', 'movs r0, #0', 'pop {r4, r5}', 'pop {r1}', 'bx r1'],
        'copied comparator must read byte pairs and return the first mismatch address or zero')
    require(span_record(THUNK, THUNK+2, entries, rows, rom)['instrs'] == 1 and
            rom[THUNK-bank.BASE:THUNK+2-bank.BASE] == bytes.fromhex('1847'), 'expected bx r3 runtime veneer')
    caller = owner(CALLER, 0x08141D54, 30)
    require(caller[2] == {0x08141d2e: 0x0814224c, 0x08141d3e: ADDRESS} and
            operations(caller[0], 0x08141d32, 0x08141d48) == [
                'lsls r0, r0, #0x10', 'lsrs r2, r0, #0x10', 'cmp r2, #0', 'bne #0x8141d1c',
                'adds r0, r4, #0', 'adds r1, r5, #0', 'bl #0x8141be0', 'adds r2, r0, #0',
                'cmp r2, #0', 'bne #0x8141d1c'], 'wrong program-then-verify caller')
    for setup in bank.SETUPS:
        sector_size, shift, sectors = struct.unpack_from('<IBxH', rom, setup-bank.BASE+24)
        require((sector_size, shift, sectors) == (4096, 12, 16), 'incorrect installed sector geometry')
    return dict(instructions=COUNT, partition=graph[3], frame=frame_copy(graph, rom), caller=0x08141d3e,
                setups=list(bank.SETUPS), sector_bytes=4096, sector_shift=12, sector_count=16,
                comparison='unsigned byte pairs; zero or first mismatching flash address',
                pools=dict(duplicate_symbols=list(DUPLICATES), duplicate_bytes=16, excluded_ROM_credit=0))


def build(root, address, args=None):
    return capture.build(sys.modules[__name__], root, address, args)


def report_matches(report, root, address):
    return address == ADDRESS and report == build(root, address)[1]


def issue(root, address, args):
    return capture.issue(sys.modules[__name__], root, address, args)
