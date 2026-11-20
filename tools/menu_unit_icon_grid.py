"""Verify the unit icon drawn in both ability selection grids."""
from hashlib import sha256
from pathlib import Path
import struct

import bios_wrapper_summary_profile as bios
import match
import menu_icon_row as menu
import menu_item_tile_row as item
import menu_unit_tile_row as unit
import named_data_buffer_profile as named
from software_double_profile import indices, span_record

OWNER = 0x080701BC
PALETTE = 0x080CBA14
TILE_ROW = 0x0802ACA0
ELIGIBLE = 0x080CB5A8
CALLS = {0x2C: PALETTE, 0x42: unit.DECODER, 0x4C: item.COPY, 0x6C: TILE_ROW, 0x8C: TILE_ROW}
PARTS = {
    OWNER: (164, 75, 'e7612bb0d3b8a873822ded2464895ef9429c12176e6f8c2bcb4b20f52bcb8137'),
    PALETTE: (40, 18, '31169a5cad16052e167a9f4b004e1bd011296ae355133a4336ce6b964d7d9b4d'),
    TILE_ROW: (50, 25, '7fecf550818cfc394025a9819da7768904761117ab76f9c549e1b433b12f6950'),
    ELIGIBLE: (140, 61, 'e96f97f8aa993ee359d6fb86c4ec1b3cc1b68f060d8bb6cf7d301cef65f3e1aa'),
    **{addr: unit.PARTS[addr] for addr in (unit.DECODER, 0x08005318, 0x080051C4)},
}
CONTRACT = (
    'Both original grids generate icon IDs 2 through 43. Their decoder initializes all 256 '
    'bytes before the BIOS reads the local. Each graphics destination accepts 128 halfwords. '
    'The map stride and tile pointer supply two writable runs of four halfwords, disjoint '
    'from graphics, the frame, and decoder globals. The returning synchronous CpuSet ABI '
    'preserves SP and R4-R11 and retains no local address in memory, R1-R3 or IP. R0 may '
    'retain its input. The decoder has exclusive use of its globals. No consumer follows '
    'the retained cursor after the decode until the decoder globals are reinitialized.'
)


def require(ok, reason):
    if not ok:
        raise ValueError('unit icon grid: ' + reason)


def environment_fingerprint():
    result = unit.environment_fingerprint()
    result['producers'][Path(__file__).name] = sha256(Path(__file__).read_bytes()).hexdigest()
    return result


def grid_callers(rom, indexed, rows):
    callers = []
    for start, end, after, digest in item.CALLERS:
        span_record(start, end, indexed, rows, rom)
        require(sha256(rom[start-menu.BASE:end-menu.BASE]).hexdigest() == digest, 'complete caller')
        # Each native caller starts ID at two, draws seven columns and six rows,
        # increments ID after every call, and sets (x,y) to (4*column+1,3*row+2).
        entry = after - 0x60
        menu.seq(rom, entry, 6, ['movs r4, #2', 'movs r1, #0', 'movs r5, #0'])
        menu.seq(rom, entry+0x22, 4, [f'bl #{ELIGIBLE:#x}'])
        menu.seq(rom, entry+0x42, 4, [f'bl #{OWNER:#x}'])
        menu.seq(rom, entry+0x46, 26, ['adds r0, r4, #1', 'lsls r0, r0, #0x10',
                 'lsrs r4, r0, #0x10', 'adds r0, r5, #1', 'lsls r0, r0, #0x10',
                 'lsrs r5, r0, #0x10', 'cmp r5, #6', f'bls #{entry+0x14:#x}',
                 'mov r1, r8', 'lsls r0, r1, #0x10', 'lsrs r1, r0, #0x10',
                 'cmp r1, #5', f'bls #{entry+4:#x}'])
        for offset, value in ((0xAA, 0x030008B0), (0xAE, 0x0200F428),
                              (0xC6, 0x44EC), (0xCA, 0x0600AE00)):
            require(struct.unpack_from('<I', rom, entry-menu.BASE+offset)[0] == value, 'grid literal')
        callers.append(dict(owner=start, site=entry+0x42, sha256=digest))
    return callers


class UnitIconGridProof(named.NamedDataBufferProof):
    def bind_row(self, body, address, calls, bindings):
        require(address == OWNER and body == self.rom[OWNER-menu.BASE:OWNER-menu.BASE+164],
                'complete original owner')
        require(calls == {OWNER+s:t for s,t in CALLS.items()} and bindings == dict(
                calls=[[s,f'func_{t:08X}'] for s,t in CALLS.items()], data=[], functions=[], switches=[]),
                'original call relocations')
        indexed, rows = indices(self.mapping, self.index)
        for addr, (size, count, digest) in PARTS.items():
            entry = span_record(addr, addr+size, indexed, rows, self.rom)
            require(entry['instrs'] == count and sha256(
                    self.rom[addr-menu.BASE:addr-menu.BASE+size]).hexdigest() == digest,
                    f'original component {addr:08X}')
        self.callers = grid_callers(self.rom, indexed, rows)
        require(span_record(item.COPY, item.COPY+4, indexed, rows, self.rom)['instrs'] == 2 and
                self.rom[item.COPY-menu.BASE:item.COPY-menu.BASE+4] == bytes.fromhex('0bdf7047'),
                'returning CpuSet wrapper')
        names = match.parse_data_symbols(self.objects)
        require(names.get('data_083B8F50') == 0x083B8F50 and names.get('data_083BB7F0') == unit.END and
                struct.unpack_from('<I', self.rom, 0xCBA10)[0] == unit.ARCHIVE and
                struct.unpack_from('<III', self.rom, 0x53C8) == (0x03002BB8,0x03002BB4,0x03002BB0) and
                sha256(self.rom[0x5408:0x5424]).hexdigest() ==
                'ddfe757da4fd7f8241c1a638f0f3e859ca8cb0fd1fd69fa2daa5f579ae865429',
                'unit table bounds, decoder globals and append consumer')
        require(sha256(self.rom[0x3B8F50:0x3B9004]).hexdigest() ==
                '2053d128177f5945b406b6ea5b36115c02f661cdac277f316466c8cf7fda1a18', 'palette table')
        self.archive = item.check_mode0_archive(self.rom[unit.ARCHIVE-menu.BASE:unit.END-menu.BASE],
                                                unit.END-unit.ARCHIVE, 44, 256)
        require(self.archive['archive_sha256'] == unit.DIGEST and
                [unit.graphic_index(v) for v in range(2,44)] == list(range(42)), 'grid graphics')
        # Every valid stream enters 080051C4, replacing IP with the ROM dictionary.
        # R3 receives the decoder's saved R8 (the external VRAM pointer). The next
        # instructions replace R0-R2, including a possible intermediate output cursor.
        menu.seq(self.rom, OWNER+0x46, 10, ['mov r0, sp', 'mov r1, r8', 'movs r2, #0x80',
                                            'bl #0x814186c'])
        self.observed = set()

    def check_call(self, address, aliases, stack, slots=None, *, constants=None, site=None, words=None):
        if site in (OWNER+0x42, OWNER+0x4C):
            require(not self.active and address == CALLS[site-OWNER] and len(stack) == 72 and
                    aliases == {match.ARM_REG_R0: -288} and not slots and not words,
                    'live local buffer arguments')
            bios.check_span((-288, 256, 4), stack, (), write=address == unit.DECODER)
            if address == item.COPY:
                require((constants or {}).get(match.ARM_REG_R2) == 128, 'CpuSet count')
            self.dependencies[address] = self.span(address)
            self.observed.add(site-OWNER)
            return {match.ARM_REG_R0: -288} if address == item.COPY else {}
        return super().check_call(address, aliases, stack, slots, constants=constants, site=site, words=words)

    def row_manifest(self):
        require(self.observed == {0x42,0x4C}, 'both local buffer calls must be reached')
        return dict(environment=environment_fingerprint(), contract=CONTRACT, callers=self.callers,
                    archive=self.archive, cursor=0x03002BB8, grid=dict(rows=6, columns=7,
                    first_id=2, last_id=43, graphics_base=0x0600AE00, map=0x030008B0),
                    local=dict(frame_bytes=288, offset=0, size=256), copy_halfwords=128,
                    components={f'{addr:08X}': digest for addr,(_,_,digest) in PARTS.items()})
