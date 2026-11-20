"""Bound the retained icon decoder output for the menu's item-and-name row."""
from hashlib import sha256
from pathlib import Path
import json
import struct

import bios_wrapper_summary_profile as bios
import match
import menu_icon_row as menu
import named_data_buffer_profile as named
from software_double_profile import indices, span_record

OWNER = 0x080702E8
CLEAR = 0x08013A88
COPY = 0x0814186C
TEXT = 0x08015110
PALETTE = 0x080CB99C
ITEMS = 0x0851D180
ARCHIVE_END = 0x083D3D14
ARCHIVE_SHA = '0ea1b802e5a2aba6c8fde8d9c3b9e72f5036ce6d295c4fd25b31cbb0e2d8772f'
CALLS = {0x2C: CLEAR, 0x34: menu.DECODE, 0x3E: COPY, 0x66: TEXT, 0x88: PALETTE, 0xAA: PALETTE}
DATA = [(0x114, 'data_0200F428'), (0x11C, 'g_table_08526680'), (0x120, 'g_table_0851D180')]
PARTS = {
    OWNER: (300, 131, 'f4283cf11f235efb58ac8fee27226e9882e2f60f4d9198ff5ae74390304a4c71'),
    PALETTE: (20, 8, '0fc22a3064cc61ffb43e23ac9b60a8272d2506c7643ab911d0474974675e6418'),
    0x080CC788: (68, 28, '6ffdf3e2f796d8867fea825f6506bb11633ea2fe4e2cd7b0b1b404f3bc2f151b'),
    TEXT: (652, 326, '6e3fc4e251d30f4d5c882864a74935b9159d14a1097886f6a26923e23c6a2889'),
    **{address: menu.COMPONENTS[address] for address in (CLEAR, menu.DECODE, 0x08005318, 0x080051C4)},
}
CALLERS = ((0x08069658, 0x0806B228, 0x0806AF3E,
            '6ff852e01bb772a68a39b3e6d50b8fbc1c3f64600436e4f42fe5a5689ac93606'),
           (0x0806B6D0, 0x0806D2B4, 0x0806CFBA,
            'e56ae796d055438c5e936d99b05c4be186082537a5db9eea8bc945264a2e4daa'))

CONTRACT = (
    'The incoming item ID is below 376, the number of 32-byte item records up to the next table. '
    'The archive contains 522 bounded streams. Both original callers supply the halfword at menu+0x44EC; '
    'neither checks that bound here. The map and two runs of 13 halfwords starting at '
    '(u16)(y*stride+x) and that offset plus stride are writable, disjoint from the live frame, '
    'the decoder globals and graphics. The aligned destination supports a 26-tile clear and '
    'the text renderer accepts the selected name and its output space. The BIOS synchronously '
    'fills 208 words and copies 64 halfwords, returning via the ordinary ABI without retaining '
    'their source addresses apart from R0 retaining its input on return. Registers R1-R3 and IP '
    'do not acquire frame addresses from these services. The decoder owns its globals exclusively during '
    'decoding. From its return onward no consumer follows or mutates the retained cursor until the globals '
    'are reinitialized. Text rendering is conditional on its ordinary returning, nonaliasing ABI.'
)


def require(value, message):
    if not value:
        raise ValueError('item tile row: ' + message)


def environment_fingerprint():
    result = menu.environment_fingerprint()
    for module_path in (__file__, named.__file__, bios.__file__):
        path = Path(module_path)
        result['producers'][path.name] = sha256(path.read_bytes()).hexdigest()
    return result


def check_archive(archive):
    """Follow the original mode-0 token loop; count after each token before authorizing any write."""
    require(len(archive) == ARCHIVE_END - menu.ARCHIVE, 'archive extent')
    total, dictionary = struct.unpack_from('>HI', archive, 2)
    require(total == 522 and 8+4*total < dictionary <= len(archive)-4, 'index or dictionary extent')
    require(archive[dictionary:dictionary+4] == bytes.fromhex('00050080'), 'mode, shift or output length')
    offsets = struct.unpack_from('>'+str(total)+'I', archive, 8) + (dictionary,)
    require(offsets[0] == 8+4*total, 'first stream overlaps or skips the index')
    for start, end in zip(offsets, offsets[1:]):
        require(start < end <= dictionary, 'stream boundaries')
        cursor, produced = start, 0
        while cursor < end:
            token = archive[cursor]
            cursor += 1
            if token & 128:
                count = (token & 127) + 1
                require(cursor + count <= end, 'literal reads beyond its stream')
                cursor += count
            else:
                require(cursor < end, 'truncated dictionary token')
                count = (token >> 2) + 3
                entry = ((token << 8) | archive[cursor]) & 1023
                require(dictionary + 4 + entry + count <= len(archive), 'dictionary read outside its object')
                cursor += 1
            produced += count
            require(produced <= 128, 'decoder would overwrite the local icon')
        require(produced == 128, 'incomplete local icon')
    return dict(entries=total, bytes_per_icon=128, archive_sha256=sha256(archive).hexdigest())


def check_items(rom, objects):
    # 080CC788 uses 0x178 records with a 32-byte stride; the next named table
    # begins exactly at that limit. The two actual callers do not compare the ID.
    names = json.loads(objects)
    for name, value in [('g_table_0851D180', ITEMS), ('g_table_08520080', ITEMS + 32*376),
                        ('g_table_08526680', menu.NAMES), ('g_table_083C7FE4', 0x083C7FE4)]:
        require(int(names.get(name, '0'), 16) == value, 'item table boundary or name mapping')
    require(struct.unpack_from('<I', rom, PALETTE-menu.BASE+16)[0] == 0x083C7FE4,
            'palette table base')
    for item in range(376):
        index, = struct.unpack_from('<H', rom, ITEMS-menu.BASE+32*item)
        offset = menu.NAMES-menu.BASE+4*index
        require(0 <= offset <= len(rom)-4, 'name index')
        text, = struct.unpack_from('<I', rom, offset)
        require(menu.BASE <= text < menu.BASE+len(rom), 'string pointer outside ROM')


def check_callers(rom, indexed, rows):
    calls = []
    for start, end, block, digest in CALLERS:
        span_record(start, end, indexed, rows, rom)
        pos = block - menu.BASE
        require(sha256(rom[start-menu.BASE:end-menu.BASE]).hexdigest() == digest, 'caller setup or call changed')
        # Identical Thumb setup in both dispatchers. R7 holds the loaded menu pointer address.
        require(rom[pos-0x48:pos-0x46] == bytes.fromhex('254f'), 'menu pointer load')
        for delta, value in ((0x4E,0x0200F428), (0x6E,menu.NAMES), (0x72,ITEMS),
                             (0x66,0x44EC), (0x4A,0x030008B0), (0x76,0x0600AC00)):
            require(struct.unpack_from('<I',rom,pos+delta)[0] == value, 'caller literal')
        calls.append(dict(owner=start, site=block + 0x3E, sha256=digest))
    return calls


class ItemTileRowProof(named.NamedDataBufferProof):
    def bind_row(self, body, address, calls, bindings):
        require(address == OWNER and calls == {address+s:t for s,t in CALLS.items()}, 'owner and call graph')
        require(bindings == dict(calls=[[s, f'func_{t:08X}'] for s,t in CALLS.items()],
                                 data=[[s,name,0] for s,name in DATA], functions=[], switches=[]),
                'genuine named ELF roles')
        indexed, rows = indices(self.mapping, self.index)
        for addr, (size, n, digest) in PARTS.items():
            entry = span_record(addr, addr+size, indexed, rows, self.rom)
            require(entry['instrs'] == n and sha256(self.rom[addr-menu.BASE:addr-menu.BASE+size]).hexdigest() == digest,
                    f'original component {addr:08X}')
        require(body == self.rom[OWNER-menu.BASE:OWNER-menu.BASE+300], 'complete native owner')
        for addr, number in ((COPY, 11), (0x08141868, 12)):
            require(span_record(addr, addr+4, indexed, rows, self.rom)['instrs'] == 2 and
                    self.rom[addr-menu.BASE:addr-menu.BASE+4] == bytes((number, 0xDF, 0x70, 0x47)),
                    'original returning BIOS wrapper')
        check_items(self.rom, self.objects)
        menu.shared_context(self.rom)
        self.callers = check_callers(self.rom, indexed, rows)
        self.archive = check_archive(self.rom[menu.ARCHIVE-menu.BASE:ARCHIVE_END-menu.BASE])
        require(self.archive['archive_sha256'] == ARCHIVE_SHA, 'original archive contents')
        self.checked = set()
        # Locate each pointer kill explicitly, including the R2 scratch from either
        # decoder token path. The following BIOS hook consumes only R0-R2.
        menu.seq(self.rom, OWNER + 0x38, 10, ['add r0, sp, #4', 'adds r1, r4, #0',
                 'movs r2, #0x40', 'bl #0x814186c'])
        menu.seq(self.rom, OWNER + 0x42, 2, ['ldr r0, [pc, #0xd0]'])

    def check_call(self, address, aliases, stack, slots=None, *, constants=None, site=None, words=None):
        if site in (OWNER+0x34, OWNER+0x3E):
            require(not self.active and address == CALLS[site-OWNER] and len(stack) == 41 and
                    aliases == {match.ARM_REG_R0: -160} and not slots and not words,
                    f'unexpected frame/aliases at {site:08X}: {aliases}')
            bios.check_span((-160, 128, 4), stack, (), write=address == menu.DECODE)
            if address == COPY:
                require((constants or {}).get(match.ARM_REG_R2) == 64, 'CpuSet descriptor')
            self.checked.add(site)
            self.dependencies[address] = self.span(address)
            if address == COPY:
                # Preserve the possible input pointer in R0 until the ordinary owner
                # walk sees the context load overwrite it. Other scratch-register
                # results are restricted by the stated BIOS interface.
                return {match.ARM_REG_R0: -160}
            # For each admitted item the synchronous decoder enters 080051C4 once.
            # That function replaces IP with the ROM dictionary. The wrapper returns
            # via POP R0/BX R0, the enclosing decoder pops its return into R1, and
            # R3 receives its saved caller R8 (the row's X). R2 is a scalar/ROM
            # value or an intermediate output address overwritten at 08070324.
            return {}
        return super().check_call(address, aliases, stack, slots, constants=constants, site=site, words=words)

    def row_manifest(self):
        require(self.checked == {OWNER+0x34, OWNER+0x3E}, 'incomplete live local buffer observations')
        return dict(environment=environment_fingerprint(), contract=CONTRACT,
                    callers=self.callers, archive=self.archive, item_count=376, retained_cursor=0x03002BB8,
                    local=dict(frame_bytes=164, icon_offset=4, icon_bytes=128, outgoing_offset=0,
                               incoming_y_offset=164), loops=[[0,2],[2,13]], tile_bytes=32,
                    bios=dict(clear_words=208, copy_halfwords=64), text_mode=0, text_spacing=1,
                    components={f'{a:08X}': d for a,(_,_,d) in PARTS.items()})
