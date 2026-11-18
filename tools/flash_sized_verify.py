"""FLASH512_V130 VerifyFlashSectorNBytes and its caller-preserved unsigned byte count."""
import sys

import flash_sector_verify as full
from flash_sector_verify import BANK, CORE, TYPE, WAIT, VENEER, TOOLCHAIN, bank, capture, operations, require

ADDRESS, END, COUNT = 0x08141C78, 0x08141D10, 61
CALLER, NAME = 0x08141D54, 'func_08141C78'
TARGETS = {**full.TARGETS, full.NAME: full.ADDRESS}
TEXT_SITES = {32: (10, BANK), 72: (2, TYPE), 76: (2, WAIT), 84: (2, CORE), 88: (2, full.NAME),
              134: (10, VENEER), 148: (2, TYPE)}
DUPLICATES = (TYPE, WAIT, CORE, full.NAME)
SOURCE_DIGEST = 'fdfee0eb52e6e875c067a0806b6cd0988b6595f632fb68199849295a07ba275c'
SCHEMA = 'elf-symbol-thumb-flash512-verify-sector-n-bytes-v1'
LABEL = 'sized flash sector verification'
CONTROL = ('* control flow: the caller supplies a readable source and a byte count within the selected sector. '
           'The 256-byte local holds a Thumb comparison routine. It reads the requested prefix and returns zero '
           'or the first mismatching cartridge address. A zero count returns zero without reading either input.')


def unit_owner(unit, address, orphan=None):
    return address == ADDRESS and full.unit_owner(unit, full.ADDRESS, orphan)


def link_object(runner, workspace, args, original, root, relative, rom, mapping, index):
    return full.link_member(sys.modules[__name__], runner, workspace, args, original, root, relative)


def native_proof(data, rom, mapping, index, objects):
    owner = full.environment(rom, mapping, index, objects)
    require(data == rom[ADDRESS-bank.BASE:END-bank.BASE], 'incorrect complete sized verification owner')
    ins, _, calls, partition = owner(ADDRESS, END, COUNT)
    require(calls == {ADDRESS + 32: bank.OWNER, ADDRESS + 134: full.THUNK}, 'wrong bank call or indirect veneer')
    words = {word['address'] - ADDRESS: word['value'] for word in partition['words']}
    require(words == {72: full.OBJECTS[TYPE], 76: full.OBJECTS[WAIT], 80: 0xfffc, 84: full.COMPARE | 1,
                      88: full.ADDRESS | 1, 148: full.OBJECTS[TYPE]}, 'incorrect copied extent or descriptor')
    # bank.provider covers the bank guard and argument. The WAITCNT halfword
    # update follows the guard in the size-limited entry.
    require(operations(ins, ADDRESS, ADDRESS + 12) == [
        'push {r4, r5, r6, lr}', 'sub sp, #0x100', 'adds r5, r1, #0', 'adds r6, r2, #0',
        'lsls r2, r0, #0x10', 'lsrs r4, r2, #0x10'], 'incorrect incoming sector, source or size ABI')
    require(operations(ins, ADDRESS + 0x28, ADDRESS + 0x36) == [
        'ldr r2, [pc, #0x20]', 'ldrh r0, [r2]', 'ldr r1, [pc, #0x20]', 'ands r0, r1', 'movs r1, #3',
        'orrs r0, r1', 'strh r0, [r2]'], 'incorrect WAITCNT update')
    halfwords = full.copy_loop(ins, ADDRESS, 0x36, words, rom)
    require(operations(ins, ADDRESS + 0x6e, END) == [
        'mov r3, sp', 'adds r3, #1', 'ldr r0, [pc, #0x20]', 'ldr r0, [r0]', 'ldrb r1, [r0, #8]',
        'lsls r4, r1', 'adds r1, r4, #0', 'movs r0, #0xe0', 'lsls r0, r0, #0x14', 'adds r1, r1, r0',
        'adds r0, r5, #0', 'adds r2, r6, #0', 'bl #0x8142250', 'add sp, #0x100',
        'pop {r4, r5, r6}', 'pop {r1}', 'bx r1'], 'count, source, cartridge input or return changed')
    caller = owner(CALLER, 0x08141d9c, 32)
    require(caller[2] == {0x08141d74: 0x0814224c, 0x08141d86: ADDRESS} and
            operations(caller[0], CALLER, CALLER + 10) == [
                'push {r4, r5, r6, r7, lr}', 'adds r5, r1, #0', 'adds r7, r2, #0', 'lsls r0, r0, #0x10',
                'lsrs r4, r0, #0x10'] and
            operations(caller[0], 0x08141d78, 0x08141d90) == [
                'lsls r0, r0, #0x10', 'lsrs r3, r0, #0x10', 'cmp r3, #0', 'bne #0x8141d62',
                'adds r0, r4, #0', 'adds r1, r5, #0', 'adds r2, r7, #0', 'bl #0x8141c78', 'adds r3, r0, #0',
                'cmp r3, #0', 'bne #0x8141d62'], 'program-and-verify caller does not preserve the count')
    return dict(instructions=COUNT, partition=partition, caller=0x08141d86, setups=list(bank.SETUPS),
                frame=dict(local_bytes=256, destination_from_entry_sp=-272, copied_halfwords=halfwords,
                           code_bytes=46, inter_function_padding_bytes=2, padding_ROM_credit=0),
                comparison=dict(count='incoming u32 r2', zero_count_reads=0, result='zero or first differing flash address'),
                pools=dict(duplicate_symbols=list(DUPLICATES), duplicate_bytes=16, excluded_ROM_credit=0))


def build(root, address, args=None):
    return capture.build(sys.modules[__name__], root, address, args)


def report_matches(report, root, address):
    return address == ADDRESS and report == build(root, address)[1]


def issue(root, address, args):
    return capture.issue(sys.modules[__name__], root, address, args)
