"""Original compiler-copy and named-literal bindings, without native admission."""
import hashlib
import json
from pathlib import Path
import re
import struct

import match
import owner_admission_profile as owner
import owner_graph_profile as graph
from private_float_pack_admission_profile import function_size
from software_double_profile import indices, span_record

SELECTOR = 'compiler-local-copy-elf-inventory-v1'
SCHEMA = 'thumb-compiler-local-copy-elf-inventory-v1'
HELPER = (0x081443FC, 0x0814445E, 49,
          'aa822d873bad381a62e3c3e07b06003a41beea59bc3edc791f7e316eb08b7ebb')
DATA = {'data_03003860': 0x03003860, 'data_03003E68': 0x03003E68}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def unique_symbol(image, name):
    values = [row for row in image['symbols'] if row['name'] == name]
    if len(values) != 1:
        raise ValueError('binding requires one unique ELF symbol')
    return values[0]


def verify(original, linked, address, rom, mapping, index, objects, *, selector, manifest=None):
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('compiler-copy ELF inventory requires its explicit selector')
    if type(address) is not int or any(type(v) is not bytes for v in (rom, mapping, index, objects)):
        raise ValueError('compiler-copy ELF inventory requires exact immutable inputs')
    if type(original) is not dict or type(linked) is not dict or original['type'] != 1 or \
            linked['type'] != 2 or linked['relocations']:
        raise ValueError('binding requires original ET_REL and resolved linked ET_EXEC')
    size = function_size(original, address)
    symbol, offset = match.function_record(original, f'func_{address:08X}', address, True)
    linked_symbol, linked_offset = match.function_record(linked, f'func_{address:08X}', address, True)
    if offset or linked_offset or function_size(linked, address) != size or \
            len(original['text']) != len(linked['text']) or any(
                row['section'] and (row['type'] == 1 or row['type'] == 2 and row is not symbol) or
                re.fullmatch(r'\$a(?:\..*)?', row['name']) for row in original['symbols']) or any(
                row['type'] == 2 and row['section'] == linked['text_index'] and row is not linked_symbol
                for row in linked['symbols']):
        raise ValueError('binding requires one unchanged complete Thumb function extent')
    body = rom[address-match.ROM_BASE:address-match.ROM_BASE+size]
    owner.validate_span(body, address, rom, mapping, index)
    entries, rows = indices(mapping, index)
    start, end, count, digest = HELPER
    helper = span_record(start, end, entries, rows, rom)
    if helper['instrs'] != count or sha(rom[start-match.ROM_BASE:end-match.ROM_BASE]) != digest or \
            start < address+size and end > address:
        raise ValueError('canonical complete copy helper identity/count/ownership differs')
    refinement = owner.refine(body, address, mapping)
    instructions, edges, branches, calls, words = graph.graph(body, address, refinement)
    partition = graph.partition(body, address, refinement, instructions, words)
    if branches or words or len(calls) != 1 or list(calls.values()) != [start] or \
            span_record(address, address+size, entries, rows, rom)['instrs'] != len(instructions):
        raise ValueError('binding requires exact complete owner CFG/count and its single copy call')
    data = match.parse_data_symbols(objects)
    if any(data.get(name) != point for name, point in DATA.items()):
        raise ValueError('named literal point differs from its explicit data map')
    expected = bytearray(original['text'])
    occupied, records = set(), []
    decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
    decoder.detail = True
    for number in original['relocations']:
        section = original['sections'][number]
        if section[1] != 9 or section[7] != original['text_index'] or section[9] != 8 or section[5] % 8:
            raise ValueError('binding requires canonical text REL relocations')
        symbols = original['symbol_tables'].get(section[6])
        raw = original['section_data'][number]
        if symbols is None or len(raw) != section[5]:
            raise ValueError('binding relocation table differs from its declared extent')
        for position in range(0, len(raw), 8):
            site, info = struct.unpack_from('<II', raw, position)
            kind, sym = info & 255, info >> 8
            if sym >= len(symbols) or kind not in (2, 10) or site % 2 or site+4 > size or \
                    occupied.intersection(range(site, site+4)):
                raise ValueError('invalid or overlapping original relocation')
            occupied.update(range(site, site+4))
            target = symbols[sym]
            name = target['name']
            if target != unique_symbol(original, name) or target['section'] or target['value'] or \
                    target['size'] or target['bind'] != 1:
                raise ValueError('binding requires unique global undefined zero-valued symbols')
            definition = unique_symbol(linked, name)
            if kind == 10:
                item = next(decoder.disasm(original['text'][site:site+4], address+site), None)
                actual = next(decoder.disasm(linked['text'][site:site+4], address+site), None)
                if name != 'memcpy' or target['type'] not in (0, 2) or \
                        calls.get(address+site) != start or item is None or actual is None or \
                        item.id != match.ARM_INS_BL or item.size != 4 or item.operands[0].imm != address+site or \
                        actual.id != match.ARM_INS_BL or actual.size != 4 or actual.operands[0].imm != start or \
                        definition['section'] != 0xFFF1 or definition['type'] != 2 or \
                        definition['value'] != start | 1 or definition['size'] or definition['bind'] != 1:
                    raise ValueError('copy binding requires the genuine compiler memcpy BL and exact Thumb definition')
                expected[site:site+4] = linked['text'][site:site+4]
                point = start
            else:
                literals = [row for row in partition['words'] if row['address'] == address+site]
                if name not in DATA or target['type'] not in (0, 1) or (address+site) % 4 or \
                        len(literals) != 1 or literals[0]['switch_word'] or not literals[0]['load_sites'] or \
                        literals[0]['value'] != DATA[name] or original['text'][site:site+4] != bytes(4) or \
                        definition['section'] != 0xFFF1 or definition['type'] != 1 or \
                        definition['value'] != DATA[name] or definition['size'] or definition['bind'] != 1:
                    raise ValueError('data binding requires an authentic zero-addend referenced typed literal')
                expected[site:site+4] = struct.pack('<I', DATA[name])
                point = DATA[name]
            records.append([site, kind, name, point])
    if sum(row[2] == 'memcpy' for row in records) != 1 or \
            {row[2] for row in records} != {'memcpy', *DATA} or any(
            row['name'] and not row['section'] and row['name'] not in {'memcpy', *DATA}
            for row in original['symbols']):
        raise ValueError('binding requires exactly one compiler copy and both named data relocations')
    if bytes(expected) != linked['text'] or linked['text'][:size] != body:
        raise ValueError('linker changed unrelocated bytes or complete linked FUNC differs from ROM')
    observed = dict(schema=SCHEMA, selector=SELECTOR, inventory_only=True, address=address,
        end=address+size, instructions=len(instructions), partition=partition,
        original_text_sha256=sha(original['text']), linked_text_sha256=sha(linked['text']),
        ROM_sha256=sha(rom), mapping_sha256=sha(mapping), index_sha256=sha(index),
        objects_sha256=sha(objects), relocations=sorted(records), helper_identity=list(HELPER),
        source_or_ELF_admission=False, copy_effects_proved=False, frame_preservation_proved=False,
        memory_safety_claim=False, physical_memory_claim=False, initialized_contents_claim=False,
        claim='Complete original binding and byte identity only; copy, indexed effects and frame obligations remain separate.',
        producer_source_sha256={Path(module.__file__).name: sha(Path(module.__file__).read_bytes())
            for module in (match, match.armv4t, owner, graph)})
    observed['producer_source_sha256'][Path(__file__).name] = sha(Path(__file__).read_bytes())
    if manifest is not None and json.dumps(manifest, sort_keys=True) != json.dumps(observed, sort_keys=True):
        raise ValueError('original compiler-copy ELF inventory manifest differs')
    return observed
