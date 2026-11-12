"""Bounded original-ELF orphan-address inventory; never native admission or GC."""
import hashlib
from pathlib import Path
import re
import struct

import analyze
import match

SELECTOR = 'compiler-orphan-address-constants-prerequisite-v1'
SCHEMA = 'thumb-compiler-orphan-address-constants-prerequisite-v1'
MAX_TEXT = 4096
MAX_ORPHAN = 64


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def reachable_literals(data, address, calls):
    """Syntactic original-byte CFG only: authenticated BL sites fall through.

    Return-shaped exits are not return provenance or ABI proofs. Native replay
    must independently establish those facts before any admission.
    """
    decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
    decoder.detail = True
    instructions, covered, loads, edges = {}, set(), {}, {}
    pending = [address]
    while pending:
        site = pending.pop()
        if site in instructions:
            continue
        offset = site-address
        require(site % 2 == 0 and 0 <= offset < len(data), 'orphan inventory CFG leaves complete function')
        item = next(decoder.disasm(data[offset:offset+4], site, count=1), None)
        require(item is not None and item.size in (2, 4), 'unsupported orphan inventory instruction')
        span = set(range(offset, offset+item.size))
        require(offset+item.size <= len(data) and not span & covered, 'overlapping orphan inventory instructions')
        instructions[site] = item
        covered.update(span)
        info = analyze.Decoder._describe(item)
        if info['pcldr'] is not None:
            literal = ((site+4)&~3)+info['pcldr'][1]-address
            require((address+literal)%4 == 0 and 0 <= literal <= len(data)-4,
                    'orphan duplicate requires complete aligned in-function literal')
            loads.setdefault(literal, []).append(offset)
        if offset in calls:
            require(item.mnemonic == 'bl' and item.size == 4 and
                    item.operands[0].imm == site, 'orphan inventory call requires canonical zero-addend BL')
            successors = [site+4]
        elif item.mnemonic == 'bx':
            require(len(item.operands) == 1 and item.operands[0].type == match.ARM_OP_REG,
                    'unsupported orphan inventory indirect exit')
            register = item.operands[0].reg
            previous = instructions.get(site-2)
            # A structural exit shape only; saved-return provenance is separate.
            require(register == match.ARM_REG_LR or previous is not None and
                    previous.mnemonic == 'pop' and len(previous.operands) == 1 and
                    previous.operands[0].reg == register,
                    'unsupported orphan inventory indirect exit')
            successors = []
        elif info['ret']:
            successors = []
        elif info['call']:
            raise ValueError('orphan inventory call lacks original relocation')
        elif info['jump'] or info['writes_pc']:
            require(info['tgt'] is not None and item.mnemonic.startswith('b'),
                    'unsupported orphan inventory control transfer')
            successors = [match.ROM_BASE+info['tgt']]
            if info['cond']:
                successors.append(site+item.size)
        else:
            successors = [site+item.size]
        edges[site] = successors
        pending.extend(successors)
    require(set(calls) == {site-address for site,item in instructions.items() if item.mnemonic == 'bl'},
            'orphan inventory has unreachable or missing call relocation')
    words = {byte for offset in loads for byte in range(offset,offset+4)}
    require(not words & covered, 'orphan duplicate literal overlaps reached code')
    missing = set(range(len(data)))-words-covered
    for offset in sorted(missing):
        if offset%2:
            continue
        require(offset+1 in missing and offset+2 in loads and (address+offset)%4 == 2 and
                data[offset:offset+2] == b'\0\0', 'unowned original text bytes outside reached literal alignment')
    require(all(offset%2 == 0 or offset-1 in missing for offset in missing), 'partial original text alignment')
    return loads, len(instructions)


def verify(original_elf, address, objects, preprocessed_source, *, selector, manifest=None):
    """Authenticate a prerequisite on immutable inputs without altering the ELF.

    Source and ELF hashes bind the supplied snapshots, not a proved compilation
    relationship. Neither exclusion nor a native profile is implemented here.
    """
    require(selector == SELECTOR and type(selector) is str, 'orphan prerequisite requires explicit selector')
    require(type(address) is int and match.ROM_BASE <= address < 0x09000000 and address%2 == 0 and
            all(type(value) is bytes for value in (original_elf,objects,preprocessed_source)),
            'orphan prerequisite requires immutable original inputs')
    image = match.elf_image(original_elf)
    require(image['type'] == 1, 'orphan prerequisite requires original relocatable ELF')
    function, offset = match.function_record(image,f'func_{address:08X}',address,True)
    require(offset == 0 and function['size'] == len(image['text']) and 0 < len(image['text']) <= MAX_TEXT and
            [row for row in image['symbols'] if row['type'] == 2 and row['section']] == [function],
            'orphan prerequisite requires sole complete sized Thumb function')
    header = struct.unpack_from('<HHIIIIIHHHHHH',original_elf,16)
    names = image['section_data'][header[12]]
    def section_name(section):
        start=section[0]
        require(0 <= start < len(names), 'invalid orphan section name')
        return names[start:names.index(b'\0',start)].decode('ascii')
    section_names=[section_name(section) for section in image['sections']]
    require(len(section_names) == len(set(section_names)), 'duplicate orphan section name')
    allowed={'','.text','.data','.bss','.rodata','.rel.text','.rel.rodata',
             '.ARM.attributes','.symtab','.strtab','.shstrtab'}
    require(set(section_names) <= allowed and section_names.count('.rodata') == 1,
            'orphan prerequisite excludes foreign sections')
    expected_types={'.text':1,'.data':1,'.bss':8,'.rodata':1,'.rel.text':9,
        '.rel.rodata':9,'.ARM.attributes':0x70000003,'.symtab':2,'.strtab':3,'.shstrtab':3}
    file_spans=[]
    section_table_start,section_table_size=header[5],40*header[11]
    for index,row in enumerate(image['sections']):
        name=section_names[index]
        if not name:
            require(index == 0 and not any(row), 'invalid null orphan section')
            continue
        require(row[1] == expected_types[name], 'foreign orphan companion section type')
        if name in ('.data','.bss'):
            require(row[5] == 0, 'nonempty orphan companion data or BSS')
        if name in ('.ARM.attributes','.symtab','.strtab','.shstrtab'):
            require(row[2] == 0, 'foreign orphan metadata section flags')
        if row[5] and row[1] != 8:
            lo,hi=row[4],row[4]+row[5]
            require(lo >= 52 and hi <= len(original_elf) and
                    not (lo < section_table_start+section_table_size and hi > section_table_start) and
                    all(not (lo < end and hi > start) for start,end in file_spans),
                    'overlapping or partial original ELF section storage')
            file_spans.append((lo,hi))
    orphan=section_names.index('.rodata')
    section=image['sections'][orphan]
    require(section[1:4] == (1,2,0) and 0 < section[5] <= MAX_ORPHAN and section[5]%4 == 0 and
            section[6:] == (0,0,4,0) and section[4]%4 == 0, 'orphan section must be bounded aligned read-only nonexecuting PROGBITS')
    text_section=image['sections'][image['text_index']]
    require(text_section[1:4] == (1,6,0) and text_section[6:] == (0,0,4,0),
            'orphan prerequisite requires canonical executable text')
    require(all(not row[2]&2 or not row[5] or index in (orphan,image['text_index'])
                for index,row in enumerate(image['sections'])), 'unexpected allocated orphan companion section')
    require(len(image['symbol_tables']) == 1, 'orphan prerequisite requires one symbol table')
    table_index, symbols = next(iter(image['symbol_tables'].items()))
    raw_symbols=image['section_data'][table_index]
    require(raw_symbols[:16] == bytes(16) and function['bind'] == 1, 'noncanonical original ELF function/symbol table')
    for number,row in enumerate(symbols):
        require(raw_symbols[number*16+13] == 0, 'noncanonical original ELF symbol visibility')
        if row['section'] == orphan:
            require(row['bind'] == 0 and row['size'] == 0 and raw_symbols[number*16+13] == 0 and
                    ((row['type'] == 3 and row['value'] == 0 and row['name'] in ('','.rodata')) or
                     (row['type'] == 0 and re.fullmatch(r'\$d(?:\.[0-9]+)?',row['name']) and
                      row['value']%4 == 0 and row['value'] < section[5])),
                    'orphan section contains exported or foreign symbol identity')
        if row['section'] and row is not function:
            require(row['type'] not in (1,2) and not re.fullmatch(r'\$a(?:\..*)?',row['name']),
                    'orphan prerequisite excludes extra objects or code')
    data_symbols=match.parse_data_symbols(objects)
    relocations={image['text_index']: [], orphan: []}
    used=set()
    for index in image['relocations']:
        row=image['sections'][index]
        require(row[1] == 9 and row[6] == table_index and row[7] in relocations and row[9] == 8 and
                row[5]%8 == 0 and row[2] in (0,64), 'orphan prerequisite requires canonical text/rodata REL')
        occupied={byte for site,_,_ in relocations[row[7]] for byte in range(site,site+4)}
        payload=image['section_data'][index]
        for pos in range(0,len(payload),8):
            site,info=struct.unpack_from('<II',payload,pos)
            require(info>>8 < len(symbols), 'invalid orphan relocation symbol')
            target=symbols[info>>8]
            require(target['section'] != orphan, 'incoming reference to orphan section')
            require(info&255 in (2,10) and 0 <= site <= image['sections'][row[7]][5]-4 and
                    not occupied.intersection(range(site,site+4)), 'unsupported partial or overlapping orphan relocation')
            occupied.update(range(site,site+4)); used.add(target['name'])
            require(target['section'] == target['value'] == target['size'] == 0 and target['bind'] == 1 and
                    raw_symbols[(info>>8)*16+13] == 0 and
                    sum(item['name'] == target['name'] for item in symbols) == 1,
                    'orphan relocation requires unique undefined zero-valued global identity')
            if info&255 == 10:
                require(row[7] == image['text_index'] and site%2 == 0 and target['type'] in (0,2) and
                        re.fullmatch(r'func_[0-9A-F]{8}',target['name']), 'unsupported orphan prerequisite call identity')
                addend=None
            else:
                require(site%4 == 0 and target['type'] in (0,1) and target['name'] in data_symbols,
                        'orphan address requires genuine aligned named-data identity')
                addend=struct.unpack_from('<i',image['section_data'][row[7]],site)[0]
                value=data_symbols[target['name']]+addend
                require(0 <= value <= 0xFFFFFFFF and not address <= value < address+len(image['text']),
                        'orphan named-data addend overflows or refers to owner')
            relocations[row[7]].append((site,target['name'],addend))
    require(all(row['section'] or not row['name'] or row['name'] in used for row in symbols),
            'orphan prerequisite contains unresolved unused identity')
    text=relocations[image['text_index']]
    calls={site:name for site,name,addend in text if addend is None}
    loads,count=reachable_literals(image['text'],address,calls)
    originals={(name,addend): [] for site,name,addend in text if addend is not None}
    for site,name,addend in text:
        if addend is not None:
            require(site in loads, 'duplicate original address is not a reached in-function literal')
            originals[name,addend].append(dict(offset=site,load_sites=loads[site]))
    copies=sorted(relocations[orphan])
    require([site for site,_,_ in copies] == list(range(0,section[5],4)),
            'orphan words require complete relocation coverage')
    require(all(addend is not None and (name,addend) in originals for _,name,addend in copies),
            'orphan word lacks identical authenticated in-function symbol/addend')
    observed=dict(schema=SCHEMA, selector=SELECTOR, address=address, complete_text_bytes=len(image['text']),
        syntactic_instructions=count, orphan_section=dict(index=orphan,name='.rodata',bytes=section[5],
            sha256=sha(image['section_data'][orphan])),
        duplicate_words=[dict(offset=site,symbol=name,addend=addend,
            original_literals=originals[name,addend]) for site,name,addend in copies],
        input_pins=dict(original_elf_sha256=sha(original_elf),text_sha256=sha(image['text']),
            objects_sha256=sha(objects),preprocessed_source_sha256=sha(preprocessed_source)),
        producer_sha256={module.__name__:sha(Path(module.__file__).read_bytes()) for module in
            (match,analyze)}, adapter_sha256=sha(Path(__file__).read_bytes()),
        native_admission=False, source_ELF_provenance_proved=False, section_exclusion_performed=False,
        runtime_unreachability_proved=False, ABI_or_return_provenance_proved=False,
        contract='Original ELF reference-graph and duplicate-word prerequisite only. '
            'Supplied source and ELF snapshots are fingerprinted; fresh fixed-toolchain provenance, '
            'explicit linker GC/exclusion, unchanged linked output, complete native frame/alias/return '
            'replay, typed call/index/ROM binding and distinct replayable admission remain required. '
            'No runtime unreachability, memory access, extent, nonaliasing or termination theorem.')
    if manifest is not None:
        require(observed == manifest, 'orphan prerequisite manifest differs from fresh original replay')
    return observed
