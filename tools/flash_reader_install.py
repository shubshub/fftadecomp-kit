"""FLASH512_V130 SetReadFlash1, including its compiler-emitted self-address."""
import shlex
import struct
import sys

import flash_sector_erase as erase
import library_units as units
import match
import unit_fpbit_source as capture
from software_double_profile import indices, span_record

ADDRESS, END, COUNT = erase.INSTALL, 0x08141AEE, 24
READER, GLOBAL = erase.READER, 0x0200F364
NAME, READ, SLOT = 'func_08141AB0', 'func_08141AAC', 'data_0200F364'
LITERALS = (SLOT, READ, NAME)
LABEL = 'flash reader installation'
SCHEMA = 'elf-symbol-thumb-flash512-set-read-flash1-v1'
TOOLCHAIN = erase.TOOL
SOURCE_DIGEST = 'dac0cccaa3c5cf0259ed55d4f05d0907e3f2066aaacacdb1b65fd15cdb4d51e7'
CONTROL = ('* control flow: on aligned writable destination storage of at least four bytes, '
           'publish its Thumb address, copy the two original reader halfwords and restore the return link; '
           'the caller supplies executable storage for the subsequent byte reads')


def require(condition, message):
    if not condition:
        raise ValueError('flash reader installer: ' + message)


def unit_owner(unit, address, orphan=None):
    return (address == ADDRESS and orphan is None and unit is not None and
            (unit.name, unit.start, unit.end, unit.toolchain, unit.proof) ==
            ('agb_flash FLASH512_V130', erase.bank.OWNER, 0x0814220C, TOOLCHAIN, 0x0814195C) and
            unit.row['identity'] == [dict(address='0x0836CE28', ascii='FLASH512_V130')])


def original_literals(image):
    """The O1 pool and its unreferenced duplicate must have the same three original bindings."""
    pool_sites = {28 + 4 * i: (2, name) for i, name in enumerate(LITERALS)}
    original_pools(image, ADDRESS, END, pool_sites, LITERALS, {SLOT}, bytes.fromhex('c046'))


def original_pools(image, address, end, text_sites, duplicate_names, objects, trailing=b''):
    """Check a pinned flash member's in-body RELs and its unreferenced O1 ABS32 mirror."""
    owner_name = f'func_{address:08X}'
    text_index = image['text_index']
    names = image['section_names']
    require(image['type'] == 1 and len(image['symbol_tables']) == 1 and names.count('.rodata') == 1,
            'expected an original O1 duplicate pool')
    rodata = names.index('.rodata')
    allocated = [i for i, section in enumerate(image['sections']) if section[2] & 2 and section[5]]
    require(sorted(allocated) == sorted((text_index, rodata)) and
            image['sections'][text_index][1:4] == (1, 6, 0) and image['sections'][text_index][8] == 4 and
            image['sections'][rodata][1:4] == (1, 2, 0) and image['sections'][rodata][8] == 4 and
            image['section_data'][rodata] == bytes(len(duplicate_names) * 4),
            'unexpected allocated section or duplicate words')
    symbol, offset = match.function_record(image, owner_name, address, True)
    global_names = sorted({name for _, name in text_sites.values()})
    require(offset == 0 and symbol['bind'] == 1 and symbol['value'] == 1 and symbol['size'] == end-address and
            image['text'][end-address:] == trailing and
            sorted(s['name'] for s in image['symbols'] if s['bind'] != 0) == global_names,
            'expected the complete original owner and its named externals')
    duplicates = {i * 4: (2, name) for i, name in enumerate(duplicate_names)}
    require(set(duplicates.values()) == {binding for binding in text_sites.values() if binding[0] == 2},
            'duplicate words must mirror the in-body ABS32 bindings')
    expected = {'.rel.text': (text_index, text_sites), '.rel.rodata': (rodata, duplicates)}
    found = set()
    for rel in image['relocations']:
        section = image['sections'][rel]
        name = names[rel]
        require(name in expected and name not in found, 'unknown or duplicated relocation section')
        found.add(name)
        target, sites = expected[name]
        require(section[1:4] == (9, 64, 0) and section[7] == target and section[5] == 8 * len(sites) and
                section[8:] == (4, 8) and section[6] in image['symbol_tables'], 'wrong relocation section')
        symbols = image['symbol_tables'][section[6]]
        bindings = {}
        for site, info in struct.iter_unpack('<II', image['section_data'][rel]):
            kind, symbol_index = info & 255, info >> 8
            require(kind in (2, 10) and symbol_index < len(symbols) and site not in bindings and
                    image['section_data'][section[6]][16 * symbol_index + 13] == 0,
                    'expected unique ordinary ABS32 words or Thumb calls')
            item = symbols[symbol_index]
            bindings[site] = (kind, item['name'])
            canonical = bytes(4) if kind == 2 else bytes.fromhex('fff7feff')
            require(image['section_data'][target][site:site+4] == canonical, 'noncanonical relocation addend')
            if item['name'] == owner_name:
                require(item == symbol, 'self-address does not name the defined Thumb function')
            else:
                require(item['name'] in global_names and item['section'] == item['value'] == item['size'] == 0 and
                        item['bind'] == 1 and item['type'] in (0, 1 if item['name'] in objects else 2),
                        'incorrect external function or object binding')
        require(bindings == sites, 'incorrect pool or call bindings')
    require(found == set(expected), 'missing original pool or duplicate bindings')


def link_object(runner, workspace, args, original, root, relative, rom, mapping, index):
    from addressed_signed_runtime_profile import original_function
    capture.reviewed_source(root, relative, ADDRESS, (NAME, READ, SLOT, 'FlashReader'), SOURCE_DIGEST)
    original_literals(original)
    # No relocation in the object names the duplicate section. Each of its
    # words and relocations is the mirror of an authenticated in-body literal.
    runner.sh(f"{args.objcopy} --remove-section=.rodata --remove-section=.rel.rodata {shlex.quote(workspace + '/f.o')}")
    stripped = match.elf_image(runner.read_binary(workspace + '/f.o'))
    require(units.signature(original, ADDRESS) == units.signature(stripped, ADDRESS) and
            original_function(stripped, ADDRESS)['size'] == END-ADDRESS,
            'excluding the duplicate constants changed the owner')
    linked = match.link_typed_targets(runner, workspace, args, NAME, ADDRESS,
                                      {SLOT: GLOBAL, READ: READER}, {SLOT})
    match.allocated_text_only(linked)
    owner, offset = match.function_record(linked, NAME, ADDRESS, True)
    require(linked['type'] == 2 and not linked['relocations'] and offset == 0 and
            (owner['value'], owner['size']) == (ADDRESS | 1, END-ADDRESS) and
            linked['text'][END-ADDRESS:] == bytes.fromhex('c046'), 'wrong linked owner or alignment')
    for name, value, kind in ((SLOT, GLOBAL, 1), (READ, READER | 1, 2)):
        definitions = [s for s in linked['symbols'] if s['name'] == name]
        require(len(definitions) == 1 and (definitions[0]['value'], definitions[0]['section'],
                definitions[0]['type'], definitions[0]['bind'], definitions[0]['size']) ==
                (value, 0xFFF1, kind, 1, 0), 'wrong linked type or address')
    expected = bytearray(original['text'])
    struct.pack_into('<3I', expected, 28, GLOBAL, READER|1, ADDRESS|1)
    require(linked['text'] == expected, 'linked text changed outside the original literals')
    return linked['text'][:END-ADDRESS]


def native_proof(data, rom, mapping, index, objects):
    erase.provider(rom)
    require(match.parse_data_symbols(objects).get(SLOT) == GLOBAL and data == rom[ADDRESS-erase.BASE:END-erase.BASE],
            'wrong global mapping or original bytes')
    entries, rows = indices(mapping, index)
    graphs = {}
    for address in (ADDRESS, READER, erase.OWNER):
        end, count = erase.SPANS[address]
        require(span_record(address, end, entries, rows, rom)['instrs'] == count,
                'noncanonical index, extent or count')
        graphs[address] = erase.closure(rom[address-erase.BASE:end-erase.BASE], address, mapping)
    parent = rom[erase.OWNER-erase.BASE:erase.END-erase.BASE]
    frame = erase.LocalReaderFrame(rom, mapping)
    checked = match.verify_leaf_instructions(parent, erase.OWNER, True, erase.CALLS, buffer_proof=frame)
    require(getattr(frame, 'installed', False) and {i.address for i in checked} == set(graphs[erase.OWNER][0]),
            'the original sector eraser does not supply its 64-byte local')
    reader, edges, calls, _ = graphs[READER]
    require([(i.mnemonic, i.op_str) for _, i in sorted(reader.items())] ==
            [('ldrb', 'r0, [r0]'), ('bx', 'lr')] and not calls and not edges[READER+2],
            'copied reader must load one unsigned byte and return')
    installer = erase.reader_installer(rom, graphs[ADDRESS])
    partition = graphs[ADDRESS][3]
    return dict(instructions=COUNT, partition=partition, installer=installer, copied_reader='ldrb r0, [r0]; bx lr',
                caller=dict(address=erase.OWNER, call=0x08141F76, local_bytes=64, destination_from_entry_sp=-84),
                pool=dict(symbols=list(LITERALS), text_offsets=[28,32,36], duplicate_offsets=[0,4,8],
                          excluded_duplicate_bytes=12, excluded_alignment_bytes=2, excluded_ROM_credit=0))


def build(root, address, args=None):
    return capture.build(sys.modules[__name__], root, address, args)


def report_matches(report, root, address):
    return address == ADDRESS and report == build(root, address)[1]


def issue(root, address, args):
    return capture.issue(sys.modules[__name__], root, address, args)
