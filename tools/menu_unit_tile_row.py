"""The menu unit row's two conditional local decode/copy paths."""
from hashlib import sha256
from pathlib import Path
import struct

import bios_wrapper_summary_profile as bios
import match
import menu_icon_row as menu
import menu_item_tile_row as item
import named_data_buffer_profile as named
from software_double_profile import indices, span_record

OWNER = 0x08057CDC
DECODER = 0x080CB9E0
ROW = 0x0805871C
ARCHIVE = 0x083B9004
END = 0x083BB7F0
DIGEST = 'a9fdd2526210f00775467e9292dd6c815f20a9cd866c7420b0c1aad5e9388529'
CALLS = {0x24:ROW, 0x84:item.CLEAR, 0x98:item.TEXT, 0xB0:item.TEXT,
         0xCA:item.CLEAR, 0xD2:DECODER, 0xDC:item.COPY, 0xF8:item.CLEAR,
         0x106:item.TEXT, 0x11E:item.CLEAR, 0x126:DECODER, 0x130:item.COPY}
DATA = [(0x70, 'g_state_02000000'), (0xA0, 'data_030008B0'),
        (0xE4, 'data_030008B0'), (0x144, 'data_030008B0')]
PARTS = {
    OWNER: (328, 141, 'e58ebb85fc6b6cfb30cccc41f8109f6c53added3cfb03c27bc9dc133c5976337'),
    ROW: (16, 8, '4e3f3270f03142ad50ae1b8f32edc6b21b62b3d31c93dd5d138170cf264c102d'),
    DECODER: (52, 22, 'bc767538e9ac2bf3b152cfde247965585408b6a26121e8ba47f80e85b51e24c1'),
    **{addr: item.PARTS[addr] for addr in (item.CLEAR, item.TEXT, 0x08005318, 0x080051C4)},
}
# Complete original caller spans; each lists all of its BLs to the unit row.
CALLERS = {
    0x08055C38: (396, 143, 'b0eb13a6c84efafb7977b57be6e411355914cd1af270ed69f4caba050114d623', [0x08055CE8], 0),
    0x08055DC4: (252, 103, '34639f5ae2576c84892acb7fcff1b05bb30d0df923f9788c6d2febb1da6a5b0d', [0x08055E1E,0x08055E8C], 0),
    0x080570D8: (408, 146, '1acce5df8eb5ea9e11dc8105d495dceaf468c07e4b8d64fb2dd6b945c1b675c8', [0x0805718C], 1),
    0x08057298: (240, 97, '25810768ff0e4685e22a660ec9e009151b567656a463df49c2149e6f1e92d595', [0x080572EA,0x0805735A], 1),
}
CONTRACT = (
    'A live roster entry supplies the name, graphic and flags. In drawing modes 0 and 1 the '
    'graphic byte must be at least 2 to initialize the local buffer. Inputs 0 and 1 map to '
    '65534 and 65535; the decoder returns without initializing the buffer and the original '
    'still copies its 256 bytes. The callers shown do not check this field. Both graphics runs '
    'and the text state are valid, ABI-accessible and disjoint from the frame and decoder '
    'globals. Width is nonzero; each CpuFastSet fills 16*width words and the final destination '
    'has room for 256 bytes. Text rendering returns normally with the stated tile and string '
    'storage. The BIOS operations return synchronously, preserve SP and R4-R11, and do not '
    'retain local addresses in memory, R1-R3 or IP. R0 may retain its input. The decoder owns '
    'its globals exclusively. No consumer uses the retained cursor after the decode until '
    'the globals are reinitialized.'
)


def require(condition, reason):
    if not condition:
        raise ValueError('menu unit tile row: ' + reason)


def environment_fingerprint():
    result = item.environment_fingerprint()
    result['producers'][Path(__file__).name] = sha256(Path(__file__).read_bytes()).hexdigest()
    return result


def graphic_index(value):
    if value == 77 or value > 82:
        value = 45
    elif value > 43:
        value = 44
    return (value - 2) & 0xffff


class UnitTileRowProof(named.NamedDataBufferProof):
    def bind_row(self, body, address, calls, bindings):
        require(address == OWNER and calls == {OWNER+site:target for site,target in CALLS.items()},
                'owner and call graph')
        require(bindings == dict(calls=[[site,f'func_{target:08X}'] for site,target in CALLS.items()],
                                 data=[[site,name,0] for site,name in DATA], functions=[], switches=[]),
                'genuine named ELF calls and data')
        require(body == self.rom[OWNER-menu.BASE:OWNER-menu.BASE+328], 'complete original body')
        indexed, rows = indices(self.mapping, self.index)
        objects = match.parse_data_symbols(self.objects)
        require(objects.get('g_state_02000080') == 0x02000080 and
                objects.get('g_state_02001940') == 0x02000080 + 24*264 and
                objects.get('data_083BB7F0') == END, 'roster and archive extents')
        parts = dict(PARTS)
        parts.update({addr: values[:3] for addr, values in CALLERS.items()})
        for addr,(size,count,digest) in parts.items():
            entry = span_record(addr, addr+size, indexed, rows, self.rom)
            require(entry['instrs'] == count and
                    sha256(self.rom[addr-menu.BASE:addr-menu.BASE+size]).hexdigest() == digest,
                    f'original component {addr:08X}')
        for addr,(_,_,_,sites,_) in CALLERS.items():
            for site in sites:
                menu.seq(self.rom,site,4,[f'bl #{OWNER:#x}'])
        for addr, number in ((item.COPY,11), (0x08141868,12)):
            require(span_record(addr,addr+4,indexed,rows,self.rom)['instrs'] == 2 and
                    self.rom[addr-menu.BASE:addr-menu.BASE+4] == bytes((number,0xdf,0x70,0x47)),
                    'returning BIOS wrapper')
        require(struct.unpack_from('<I',self.rom,0xCBA10)[0] == ARCHIVE and
                struct.unpack_from('<III',self.rom,0x53C8) == (0x03002BB8,0x03002BB4,0x03002BB0),
                'archive and decoder globals')
        require(sha256(self.rom[0x5408:0x5424]).hexdigest() ==
                'ddfe757da4fd7f8241c1a638f0f3e859ca8cb0fd1fd69fa2daa5f579ae865429',
                'append through retained cursor')
        menu.seq(self.rom, DECODER+8, 34, [
            'cmp r1, #0x4d', 'beq #0x80cb9f0', 'cmp r1, #0x52', 'bls #0x80cb9f4',
            'movs r1, #0x2d', 'b #0x80cb9fa', 'cmp r1, #0x2b', 'bls #0x80cb9fa',
            'movs r1, #0x2c', 'ldr r0, [pc, #0x14]', 'subs r2, r1, #2',
            'lsls r2, r2, #0x10', 'lsrs r2, r2, #0x10', 'adds r1, r3, #0',
            'movs r3, #1', 'bl #0x8005318'])
        # Mode 0, shift 5, fixed output. All 44 streams are independently bounded.
        self.archive = item.check_mode0_archive(self.rom[ARCHIVE-menu.BASE:END-menu.BASE],
                                                END-ARCHIVE, 44, 256)
        require(self.archive['archive_sha256'] == DIGEST and
                {graphic_index(v) for v in range(2,256)} == set(range(44)) and
                [graphic_index(0), graphic_index(1)] == [65534,65535], 'graphic index or archive')
        for offset in (0xD6,0x12A):
            menu.seq(self.rom,OWNER+offset,10,['add r0, sp, #4','adds r1, r5, #0',
                     'movs r2, #0x80','bl #0x814186c'])
        self.observed = set()

    def check_call(self, address, aliases, stack, slots=None, *, constants=None, site=None, words=None):
        if site in (OWNER+0xD2,OWNER+0xDC,OWNER+0x126,OWNER+0x130):
            require(not self.active and address == CALLS[site-OWNER] and len(stack) == 74 and
                    aliases == {match.ARM_REG_R0:-292} and not slots and not words,
                    f'unexpected live local aliases at {site:08X}')
            bios.check_span((-292,256,4),stack,(),write=address == DECODER)
            if address == item.COPY:
                require((constants or {}).get(match.ARM_REG_R2) == 128,
                        'expected a 128-halfword CpuSet descriptor')
            self.observed.add(site-OWNER)
            self.dependencies[address] = self.span(address)
            if address == item.COPY:
                return {match.ARM_REG_R0:-292}
            # On valid input 080051C4 overwrites IP with the ROM dictionary.
            # The enclosing return pops its saved R8 (the external name) into R3
            # and LR into R1. The next three instructions kill R0, R1 and R2.
            return {}
        return super().check_call(address, aliases, stack, slots, constants=constants,
                                  site=site, words=words)

    def row_manifest(self):
        require(self.observed == {0xD2,0xDC,0x126,0x130}, 'both live decode/copy paths')
        return dict(environment=environment_fingerprint(), contract=CONTRACT, archive=self.archive,
                    roster=dict(base=0x02000080, entries=24, stride=264, name=0, graphic=7, flags=40),
                    local=dict(frame_bytes=296, buffer_offset=4, buffer_bytes=256,
                               graphic_word=260, outgoing_offset=0, mode_offset=296),
                    selected_modes=[0,1], default_draws=False, uninitialized_graphics=[0,1],
                    controls=dict(CpuFastSet='0x01000000 | (16 * width)', CpuSet_halfwords=128),
                    cursor=0x03002BB8, calls=sorted(self.observed),
                    callers={f'{addr:08X}':dict(sha256=digest,sites=sites,mode=mode)
                             for addr,(_,_,digest,sites,mode) in CALLERS.items()},
                    components={f'{addr:08X}':digest for addr,(_,_,digest) in PARTS.items()})
