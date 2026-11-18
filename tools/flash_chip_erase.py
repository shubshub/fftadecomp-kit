"""FLASH512_V130 chip erase, with the phase-3 polling reader installed in its live frame."""
from hashlib import sha256
from pathlib import Path
import struct

import flash_bank_command as bank
import flash_program_byte as program
import flash_sector_erase as sector
import library_units as units
import match

OWNER, END = 0x08141EB8, 0x08141F2C
NAME, SOURCE = 'func_08141EB8', 'src/08141EB8.c'
SCHEMA = 'elf-symbol-thumb-flash-chip-reader-v1'
CONTROL = 'complete six-write chip erase and phase-3 synchronous polling through the live local reader'
QUALIFIED = '68c1df745d191c796f39a43ca6fc1f30d453b4e66a9fee781645397da277c055'
STRIPPED = 'd2a85f83bb12e96067c16b77470bfb4cfd60056a16f8ab10f2f488fc101ece49'
CALLS = {0x08141EE8: sector.INSTALL, 0x08141EF8: 0x08142250}
OBJECTS = {0x64: ('data_0200F370', 0x0200F370), 0x70: (program.WAIT, 0x0200F368)}
BODY = sector.FLASH_DECLARATIONS + '''

u16 func_08141EB8(void)
{
    u16 readBuffer[32];
    u16 result;

    *(u16 *)0x04000204 = (*(u16 *)0x04000204 & ~3) | data_0200F370->wait[0];
    *(volatile u8 *)0x0E005555 = 0xAA;
    *(volatile u8 *)0x0E002AAA = 0x55;
    *(volatile u8 *)0x0E005555 = 0x80;
    *(volatile u8 *)0x0E005555 = 0xAA;
    *(volatile u8 *)0x0E002AAA = 0x55;
    *(volatile u8 *)0x0E005555 = 0x10;
    func_08141AB0(readBuffer);
    result = data_0200F368(3, (u8 *)0x0E000000, 0xFF);
    *(u16 *)0x04000204 = (*(u16 *)0x04000204 & ~3) | 3;

    return result;
}'''


def require(ok, message):
    if not ok:
        raise ValueError('flash chip erase: '+message)


def unit_owner(unit, address, orphan):
    return address == OWNER and sector.reader_unit(unit, orphan)


def provider(rom):
    program.provider(rom)
    require(sha256(rom[OWNER-bank.BASE:END-bank.BASE]).hexdigest() == QUALIFIED,
            'the chip command stores, reader installation, wait or return changed')
    # IdentifyFlash copies the selected setup's +4 word to the chip-erase slot.
    require(rom[0x141de6:0x141dee] == bytes.fromhex('0d49106840680860') and
            struct.unpack_from('<I',rom,0x141e1c)[0] == 0x0200F378, 'changed IdentifyFlash chip slot installation')
    for setup, ticks, speed in zip(bank.SETUPS, (200, 500, 2000, 200), (1, 0, 3, 3)):
        chip, _, wait, timing = struct.unpack_from('<4I', rom, setup-bank.BASE+4)
        require((chip, wait) == (OWNER|1, sector.WAIT|1) and
                struct.unpack_from('<H', rom, setup-bank.BASE+36)[0] == speed and
                struct.unpack_from('<3H', rom, timing-bank.BASE+18) == (ticks, 65469, 194),
                'changed selected chip eraser, wait pointer, bus speed or phase-3 timer')


def qualifier_offsets(text, tree, project, closure):
    from rompath import rom_path
    offsets = bank.source_qualifiers(text, tree, closure, OWNER, SOURCE, BODY)
    if offsets:
        bank.verify_unit(project, OWNER, END-OWNER)
        provider(Path(rom_path(project)).read_bytes())
    return offsets


def stripped_build(root):
    return sector.stripped_reader_build(root, OWNER, SOURCE, NAME, 104, STRIPPED,
        ((36,10,'func_08141AB0'),(52,10,program.VENEER),(88,2,'data_0200F370'),(100,2,program.WAIT)))


def record(root):
    import plausible
    root = Path(root)
    path = root/SOURCE
    require(list((root/'src').rglob(path.name)) == [path] and
            len(qualifier_offsets(path.read_text(), root, root, plausible.include_closure(root,path))) == 6,
            'six qualified original command writes required')
    stripped_build(root)
    return ('* allowlisted volatile flash chip erase: AA/55/80/AA/55/10 is issued in order. Removing the six '
            'qualifiers leaves only 55/10. Qualified and stripped linked bodies have SHA-256 '+QUALIFIED+' and '+STRIPPED+'.')


class ChipReaderFrame(sector.LocalReaderFrame):
    install_site, frame_offset = 0x08141EE8, -80


def native_proof(data, rom, mapping, index, objects, calls, literals, context, orphan):
    from software_double_profile import indices, span_record
    require(unit_owner(context['unit'],OWNER,orphan) and context['tool'] == units.resolve(sector.TOOL) and
            data == rom[OWNER-bank.BASE:END-bank.BASE] and calls == CALLS and literals == OBJECTS and
            all(match.parse_data_symbols(objects).get(name) == value for name,value in OBJECTS.values()),
            'incorrect library unit, source, direct call or named data')
    provider(rom)
    entries,rows = indices(mapping,index)
    graphs = {}
    for address,(end,count) in ((OWNER, (END,43)), *((a,sector.SPANS[a]) for a in (sector.INSTALL,sector.READER,sector.WAIT))):
        require(span_record(address,end,entries,rows,rom)['instrs'] == count, 'changed original function index')
        graphs[address] = sector.closure(rom[address-bank.BASE:end-bank.BASE],address,mapping,count=count)
    ins,edges,native_calls,partition = graphs[OWNER]
    selected = {x['address']: x for x in partition['words']}
    for offset, (_, value) in OBJECTS.items():
        require(selected[OWNER+offset]['value'] == value and selected[OWNER+offset]['load_sites'] ==
                [0x08141EC4 if offset == 0x64 else 0x08141EEC], 'changed active setup or indirect wait literal')
    require(native_calls == CALLS and not sector.reaches(edges, OWNER, 0x08141EF8, {0x08141EE8}),
            'reader must be installed before polling')
    frame = ChipReaderFrame(rom,mapping)
    checked = match.verify_leaf_instructions(data,OWNER,True,calls,buffer_proof=frame)
    require(getattr(frame,'installed',False) and sorted(i.address for i in checked) == sorted(ins),
            'native frame and ownership CFG disagree')
    installed = sector.installed_reader_and_wait(rom,graphs)
    return checked, dict(partition=partition, installer=installed,
        frame=dict(bytes=80,local_bytes=64,published_from_entry_sp=-79,reader_fetch_bytes=4),
        wait=dict(phase=3,address=bank.BUS,expected=255,call=0x08141EF8,installed=sector.WAIT|1),
        identify=dict(slot=0x0200F378, store=0x08141DEC, setup_member_offset=4, targets=[OWNER|1]*4),
        contract='Original IdentifyFlash setup, writable executable aligned stack disjoint from the flash bus, '
        'SDK globals and timer. The phase-3 wait calls the copied reader synchronously. The routine returns '
        'the low 16 bits of the wait result and restores WAITCNT low bits to 3. The returned frame ends the '
        'reader lifetime while 0200F364 retains its address. Later use requires a fresh installation.')


def replay(report, root, address):
    return sector.replay_member(report, root, address, OWNER, SCHEMA)
