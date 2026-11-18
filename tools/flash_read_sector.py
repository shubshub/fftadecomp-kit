"""FLASH512_V130 ReadFlash via its stack-local byte-copy routine and original game caller."""
import sys

import flash_sector_verify as full
from flash_sector_verify import BANK, TYPE, WAIT, VENEER, TOOLCHAIN, bank, capture, operations, require
from software_double_profile import indices, span_record

ADDRESS, END, COUNT = 0x08141B14, 0x08141BB0, 63
CORE, CORE_END = 0x08141AF0, 0x08141B12
CALLER, CALLER_END = 0x0813AE30, 0x0813AF98
NAME, READ = 'func_08141B14', 'func_08141AF0'
TARGETS = {**full.OBJECTS, READ: CORE, BANK: bank.OWNER, VENEER: full.THUNK}
TEXT_SITES = {48: (10, BANK), 76: (2, WAIT), 84: (2, TYPE), 88: (2, READ), 92: (2, NAME),
              140: (10, VENEER), 152: (2, TYPE)}
DUPLICATES = (WAIT, TYPE, READ, NAME)
SOURCE_DIGEST = '04932427a83aa3c99524cc29d39d26bdcf6618d51543458bd55f003ebe050277'
SCHEMA = 'elf-symbol-thumb-flash512-read-sector-v1'
LABEL = 'flash sector read'
CONTROL = ('* control flow: given a readable interval in an initialized flash sector and writable output, the SDK '
           'copies its byte reader into a 128-byte local and reads the requested byte count from the sector offset. '
           'The void call returns after writing the destination. A zero count leaves the destination untouched.')


def unit_owner(unit, address, orphan=None):
    return address == ADDRESS and full.unit_owner(unit, full.ADDRESS, orphan)


def link_object(runner, workspace, args, original, root, relative, rom, mapping, index):
    return full.link_member(sys.modules[__name__], runner, workspace, args, original, root, relative,
                            callback_type='FlashRead')


def native_proof(data, rom, mapping, index, objects):
    owner = full.flash_environment(rom, mapping, index, objects)
    require(data == rom[ADDRESS-bank.BASE:END-bank.BASE], 'wrong complete read owner')
    ins, _, calls, partition = owner(ADDRESS, END, COUNT)
    require(calls == {0x08141b44: bank.OWNER, 0x08141ba0: full.THUNK}, 'wrong read bank or local call')
    words = {word['address'] - ADDRESS: word['value'] for word in partition['words']}
    require(words == {76: full.OBJECTS[WAIT], 80: 0xfffc, 84: full.OBJECTS[TYPE], 88: CORE | 1,
                      92: ADDRESS | 1, 152: full.OBJECTS[TYPE]}, 'wrong hardware, descriptor, or core extent')
    # bank.provider authenticates WAITCNT, the 128-KiB guard and the bank call.
    require(operations(ins, ADDRESS, 0x08141b22) == [
        'push {r4, r5, r6, r7, lr}', 'sub sp, #0x80', 'adds r5, r1, #0', 'adds r6, r2, #0',
        'adds r7, r3, #0', 'lsls r3, r0, #0x10', 'lsrs r4, r3, #0x10'], 'wrong frame or input arguments')
    require(operations(ins, 0x08141b4c, 0x08141b86) == [
        'ldr r3, [pc, #0x1c]', 'movs r0, #1', 'eors r3, r0', 'mov r2, sp', 'ldr r0, [pc, #0x18]',
        'ldr r1, [pc, #0x14]', 'subs r0, r0, r1', 'lsls r0, r0, #0xf', 'b #0x8141b80',
        'ldrh r0, [r3]', 'strh r0, [r2]', 'adds r3, #2', 'adds r2, #2', 'subs r0, r1, #1',
        'lsls r0, r0, #0x10', 'lsrs r1, r0, #0x10', 'cmp r1, #0', 'bne #0x8141b74'], 'wrong local halfword copy')
    source = words[88] ^ 1
    count = ((words[92] - words[88]) >> 1) & 0xffff
    require(source == CORE and source + 2 * count == ADDRESS and 2 * count <= 128 and
            rom[CORE_END-bank.BASE:ADDRESS-bank.BASE] == bytes(2), 'local copy exceeds core and its padding')
    require(operations(ins, 0x08141b86, END) == [
        'mov r3, sp', 'adds r3, #1', 'ldr r0, [pc, #0x20]', 'ldr r0, [r0]', 'ldrb r0, [r0, #8]',
        'lsls r4, r0', 'adds r0, r4, #0', 'movs r2, #0xe0', 'lsls r2, r2, #0x14', 'adds r1, r5, r2',
        'adds r0, r0, r1', 'adds r1, r6, #0', 'adds r2, r7, #0', 'bl #0x8142250', 'add sp, #0x80',
        'pop {r4, r5, r6, r7}', 'pop {r0}', 'bx r0'], 'incorrect cartridge offset, destination, count or void return')
    core, _, calls, _ = owner(CORE, CORE_END, 17)
    require(not calls and operations(core, CORE, CORE_END) == [
        'push {r4, lr}', 'adds r4, r0, #0', 'subs r3, r2, #1', 'cmp r2, #0', 'beq #0x8141b0c',
        'movs r2, #1', 'rsbs r2, r2, #0', 'ldrb r0, [r4]', 'strb r0, [r1]', 'adds r4, #1',
        'adds r1, #1', 'subs r3, #1', 'cmp r3, r2', 'bne #0x8141afe', 'pop {r4}', 'pop {r0}', 'bx r0'],
        'wrong copied source, destination, byte width, loop or zero-length behavior')
    # The game index records this whole caller, including its pool. Discover
    # its actual reachable instructions independently of its original halfword estimate.
    span_record(CALLER, CALLER_END, *indices(mapping, index), rom)
    caller = full.erase.closure(rom[CALLER-bank.BASE:CALLER_END-bank.BASE], CALLER, mapping, count=162)
    loads = ['movs r1, #0', 'mov r2, sp', 'movs r3, #0x80', 'bl #0x8141b14']
    require(caller[2] == {0x0813ae98: ADDRESS, 0x0813aea2: 0x081443b0, 0x0813af14: ADDRESS} and
            operations(caller[0], 0x0813ae92, 0x0813ae9c) == loads and
            operations(caller[0], 0x0813af0e, 0x0813af18) == loads, 'wrong game save-header calls')
    return dict(instructions=COUNT, partition=partition, setups=list(bank.SETUPS),
                frame=dict(local_bytes=128, destination_from_entry_sp=-148, copied_halfwords=count,
                           code_bytes=CORE_END-CORE, inter_function_padding_bytes=2, padding_ROM_credit=0),
                callers=[0x0813ae98, 0x0813af14], game_read=dict(offset=0, bytes=128, destination='caller SP'),
                access=dict(source='cartridge base + (sector << 12) + offset', width=1, count='incoming u32 r3'),
                pools=dict(duplicate_symbols=list(DUPLICATES), duplicate_bytes=16, excluded_ROM_credit=0))


def build(root, address, args=None):
    return capture.build(sys.modules[__name__], root, address, args)


def report_matches(report, root, address):
    return address == ADDRESS and report == build(root, address)[1]


def issue(root, address, args):
    return capture.issue(sys.modules[__name__], root, address, args)
