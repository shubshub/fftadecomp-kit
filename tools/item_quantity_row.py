"""Filtered inventory row, bounded archive icon, text width and clear range."""
import struct
from pathlib import Path

import menu_icon_row as menu
from menu_icon_row import BASE, require, sha

ADDRESS = 0x0805C220
FIRST = 362
LAST = 375
ITEM_TABLE = 0x0851D180
FONT_WIDTHS = 0x084966B0
MODE = 0x020020E3
CALLS = [(0x30, 'func_080CB980'), (0x3e, 'func_08017B68'), (0x4e, '__modsi3'),
         (0x6c, 'func_0814186C'), (0x96, 'func_08015110'), (0xa2, 'func_080161BC'),
         (0xba, 'func_08013A88'), (0xd6, 'func_0802979C'), (0xe6, 'func_080CB99C'),
         (0xf8, 'func_0805C340')]
DATA = [(0x10c, 'data_030008B0', menu.GRAPHICS), (0x110, 'data_0200F428', 0x0200F428),
        (0x118, 'g_table_08526680', menu.NAMES), (0x11c, 'g_table_0851D180', ITEM_TABLE)]
CALLERS = (0x0805BF44, 0x0805C178, 0x0805C1F4)
# All complete indexed components whose native behavior the contract interprets.
COMPONENTS = {
    0x0805C220: (288, 124, '9f553ba53a0c1062fd43415bef4d5b0b43db65f379b3a5c92c55440c16904197'),
    0x0805BE68: (344, 136, '98250669c7ff14701a1e3043baec1dc9d4bf224e5466eb90a114ffbe75441c99'),
    0x0805C10C: (276, 111, '916c849eb0f29604e64c317bf7adcd34a798fd5e9e6b471b64ac1e9664e6bdb6'),
    0x080CB210: (60, 21, 'a3cac7f25bbbc62f0804658ca37f9c34a46a2fc48145901549a6502fb7031c94'),
    0x080CC7F8: (114, 55, '28e7b371685f86a7e55821bda7e9888df08b90ae810563c9dedb18a3a1619405'),
    0x080CBD34: (140, 61, '5e9c4ccb745057c81d9ac2d936dc0fb0b6fcdd023f51a52d1e5c03f1dff6fc9d'),
    0x08014778: (582, 101, '131d000096d5cfdc53134bae6f6acc03e461f9b16eec73c16a2e78298b8298d2'),
    0x08013A5C: (42, 16, '00742b4c78a55e5970039983a44ffcf57309a6ee399d5166611a24fc63fee202'),
    0x08013BC0: (44, 21, '2427191d86ff36972d5726dfd465d28b72da422bb5abe3a658d0081c639cf71b'),
    0x080161BC: (24, 10, '9863650439ceebb8396d9aca79064228c113e105a9e6216f105c22439dd9fe83'),
    0x08141868: (4, 2, 'dedc152a89df8aadc9dc9526881c29e92f681504cf9bf438bbac1c6362fd9b42'),
    0x0814186C: (4, 2, '07967ebdc3979cd4fd4de37fd22b3e6de8965b00dae4ac5585577c9709839652'),
}


def environment_fingerprint():
    result = menu.environment_fingerprint()
    result['producers'][Path(__file__).name] = sha(Path(__file__).read_bytes())
    return result


def word(rom, address):
    return struct.unpack_from('<I', rom, address - BASE)[0]


def name_widths(rom, item):
    """Interpret only the glyph forms reached in the fourteen initialized rows."""
    require(FIRST <= item <= LAST, 'item outside selector-five inventory')
    name_index = struct.unpack_from('<H', rom, ITEM_TABLE-BASE+32*item)[0]
    require(name_index == 485 + item - FIRST, 'unexpected filtered item name index')
    start, end = struct.unpack_from('<II', rom, menu.NAMES-BASE+4*name_index)
    require(BASE <= start < end <= BASE+len(rom) and end-start <= 25, 'invalid item name extent')
    name = rom[start-BASE:end-BASE]
    require(name.endswith(b'\0') and 0 not in name[:-1], 'unexpected item name termination')
    cursor = proportional = fixed = 0
    single = False
    while cursor < len(name)-1:
        first = name[cursor]
        cursor += 1
        if first == 1:
            single = True
            continue
        if single:
            glyph = first - 1
        else:
            require(cursor < len(name)-1, 'truncated two-byte glyph')
            second = name[cursor]
            cursor += 1
            if (first, second) == (0x40, 0x73):
                proportional += 6
                fixed += 16
                continue
            require(first & 0x80, 'unsupported item-name control')
            glyph = ((first << 8) | second) & 0x7fff
        proportional += rom[FONT_WIDTHS-BASE+glyph]
        fixed += 16
    return start, (proportional+7)//8, (fixed+7)//8


def validate_native(rom, mapping, index, targets):
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    from software_double_profile import indices, span_record
    entries, rows = indices(mapping, index)
    components = dict(COMPONENTS)
    for address in (menu.DECODE, 0x08005318, 0x080051C4, 0x08017B68, 0x08013A88):
        components[address] = menu.COMPONENTS[address]
    for start, (size, count, digest) in components.items():
        record = span_record(start, start+size, entries, rows, rom)
        require(record['instrs'] == count and sha(rom[start-BASE:start-BASE+size]) == digest,
                f'item row component at {start:08X}')
    raw = rom[ADDRESS-BASE:ADDRESS-BASE+288]
    refinement = owner.refine(raw, ADDRESS, mapping)
    ins, edges, switches, calls, words = graph.graph(raw, ADDRESS, refinement)
    require(len(ins) == 124 and not switches and not words and
            all(target > site for site, targets_ in edges.items() for target in targets_) and
            calls == {ADDRESS+site: targets[name][0] for site, name in CALLS}, 'item row CFG or call graph')
    pools = graph.partition(raw, ADDRESS, refinement, ins, words)['words']
    require([(w['address']-ADDRESS, w['value'], [s-ADDRESS for s in w['load_sites']]) for w in pools] == [
        (0x10c, menu.GRAPHICS, [0x58]), (0x110, 0x0200F428, [0x70, 0xbe]),
        (0x114, 0x1184, [0x74, 0xc2]), (0x118, menu.NAMES, [0x7c]), (0x11c, ITEM_TABLE, [0x80])],
        'rooted item and name tables or menu context')
    require([site-ADDRESS for site, i in sorted(ins.items()) if 'sp' in i.op_str or i.mnemonic in ('push', 'pop')] ==
            [0, 8, 10, 0x12, 0x1e, 0x2c, 0x2e, 0x66, 0x92, 0x94, 0xcc, 0xce, 0xd2, 0xfc, 0xfe, 0x106, 0x108],
            'unclassified item row stack operation')
    menu.shared_context(rom)
    # 08014778 branches on zero, single-byte mode, the high bit, then the
    # embedded switch. Its sole reached control code selects the 6/16 path.
    require(word(rom,0x080147BC) == 0x7fff and word(rom,0x080147DC) == 0x080147E0 and
            word(rom,0x080147E0 + 4*(0x73-0x21)) == 0x08014944 and
            word(rom,0x08014958) == MODE-0x13 and word(rom,0x08013A78) == MODE-0x13 and
            word(rom,0x08013A7C) == FONT_WIDTHS, 'font glyph operands')
    # Selector 5 emits only live, nonzero-quantity records whose 16-bit
    # identifiers fall in [362,375]. The native callers still own selection.
    menu.seq(rom, 0x0805BE88, 6, ['movs r1, #5', 'bl #0x80cc7f8'])
    require(word(rom,0x080CBDB4) == (-(FIRST)) & 0xffffffff, 'filter lower bound')
    for site in CALLERS:
        menu.seq(rom, site, 4, ['bl #0x805c220'])
    menu.seq(rom, 0x0805C24E, 6, ['add r0, sp, #4', 'bl #0x80cb980'])
    menu.seq(rom, 0x0805C286, 10, ['add r0, sp, #4', 'adds r1, r5, #0', 'movs r2, #0x40', 'bl #0x814186c'])
    return {f'{start:08X}': dict(bytes=size, instructions=count, sha256=digest)
            for start, (size, count, digest) in components.items()}


CONTRACT = (
    'For a selected, initialized entry from the selector-five inventory, the icon decoder writes '
    '128 bytes at SP+4. A readable fifth incoming word and a live disjoint menu, text context, '
    'tilemap and sufficiently large aligned writable tile run are required. All coordinates and '
    'indices must designate their respective live objects. The height byte plus one is 1..256. '
    'CpuSet copies 64 halfwords synchronously. At the width measurement, mode zero admits all '
    'fourteen names; in either mode only measured widths below 12 guarantee a nonempty in-row '
    'CpuFastSet clear. A width of 12 programs zero and larger widths wrap the u16 tile count. '
    'The font mode remains stable through measurement. The BIOS calls require accessible, disjoint '
    'source and destination storage. The text, number, attribute and tilemap calls are ordinary '
    'returning ABI boundaries. Their incoming objects and stores must respect the live stack and '
    'decoder globals. The decoder has exclusive use of its IWRAM globals while active and leaves '
    'the icon address in 03002BB8. Consumers must replace that pointer before use after frame exit.'
)


def verify_original(raw, linked_file, address, rom, mapping, index, bindings, manifest=None, *, objects):
    import owner_admission_profile as owner
    import runtime_summary_profile as runtime
    require(address == ADDRESS, 'unexpected inventory row')
    targets = menu.verify_objects(raw, linked_file, address, rom, mapping, index, bindings, objects, CALLS, DATA, 288)
    native = validate_native(rom, mapping, index, targets)
    cases = {}
    for item in range(FIRST, LAST+1):
        pointer, narrow, fixed = name_widths(rom, item)
        require(narrow < 12, 'proportional item name would program a zero/wrapped clear')
        cases[str(item)] = dict(icon_sha256=sha(menu._decode_icon(rom, item)), name=pointer,
                                proportional_tiles=narrow, fixed_tiles=fixed)
    closure = runtime.RuntimeSummaries(rom,mapping,index)
    closure.observe(ADDRESS+0x4e, runtime.ENTRIES['__modsi3'])
    closure.observe(0x08013BCE, runtime.ENTRIES['__umodsi3'])
    result = dict(profile=runtime.SCHEMA, selector=runtime.SELECTOR, environment=environment_fingerprint(),
                  bindings=bindings, original_ELF_sha256=sha(raw), linked_ELF_sha256=sha(linked_file),
                  components=native, runtime=closure.manifest(), callers=list(CALLERS), items=cases,
                  frame=dict(size=172, icon_offset=4, icon_bytes=128, quantity=132, style=136,
                             incoming_style=172, outgoing_word=0), retained_output_word=0x03002BB8,
                  retained_length_word=0x03002BB0, font_mode=MODE, contract=CONTRACT)
    if manifest is not None:
        require(owner.text(result) == owner.text(manifest), 'cached item row differs from original replay')
    return result, 124
