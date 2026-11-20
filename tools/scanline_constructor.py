"""Stack tables, allocation and line initialization of the USA scroll task constructor."""
from hashlib import sha256
from struct import pack, unpack_from

import match
import named_data_buffer_profile as buffers
import owner_graph_profile as graph
import plausible
from ability_range_local_bytes import block, require
from active_entry_shuffle_profile import compiler_symbol_roles
from copy_helper_summary_profile import contract
from known_query_native_closure_profile import environment_fingerprint
from positioned_equipment_chance import direct_sites
from rom_table_copy_profile import helper_facts, HELPER
from scanline_pair import provider
from scroll_wave_table_index import producers
from sdk_cpuset_halfword import TOKEN, base_header
from software_double_profile import indices, span_record
from unit_equipment_attribute import ops

OWNER, END = 0x0800CE08, 0x0800CF06
SOURCE = 'src/0800CE08.c'
SOURCE_HASH = '095cefad668ff4c49813732290f9b84ba5cad72d0903c2904e76c279ad0ad654'
CALLS = {OWNER + offset: target for offset, target in
         ((0x30, HELPER), (0x3C, HELPER), (0x52, 0x0800C3CC),
          (0x7E, 0x0800C614), (0x8C, 0x0800C614), (0xA2, 0x0800C614))}
TABLES = (0x0814980C, 0x08149818, 0x08149806)
BINDINGS = dict(calls=[[pc - OWNER, f'func_{target:08X}'] for pc, target in CALLS.items()],
                data=[[0x68 + 4*i, f'data_{a:08X}', 0] for i, a in enumerate(TABLES)],
                functions=[], switches=[])


def check_source(root):
    path = root / SOURCE
    text = path.read_text()
    reserved = ('Callbacks0800CE08', 'LineTable0800CE08', 'LineCallback', 'func_0800CE08',
                *(name for _, name in BINDINGS['calls']), *(name for _, name, _ in BINDINGS['data']))
    require(plausible.include_closure(root, path) == ({SOURCE, 'include/ffta.h'}, [])
            and base_header((root / 'include/ffta.h').read_bytes(), reserved)
            and not any(marker in text for marker in (chr(92), '??', '%:', chr(0)))
            and sha256(' '.join(TOKEN.findall(plausible.strip_comments_and_strings_keep_strings(text)))
                       .encode()).hexdigest() == SOURCE_HASH, 'changed scanline constructor source or header')


def check_original(image, bindings, targets):
    expected = {name: (CALLS[OWNER + offset], False) for offset, name in BINDINGS['calls']}
    expected.update({f'data_{a:08X}': (a, True) for a in TABLES})
    require(bindings == BINDINGS and targets == expected and
            all(row['size'] == 0 for row in image['symbols'] if row['name'] in targets),
            'incorrect scanline constructor ELF bindings')
    compiler_symbol_roles(image, targets)


def caller_modes(rom, mapping, index):
    sites = [0x080D8EDE, 0x080D924C, 0x080D93A2, 0x080D94F0, 0x080D959C]
    require(direct_sites(rom, OWNER) == sites and not any(pack('<I', p) in rom for p in (OWNER, OWNER | 1)),
            'changed scanline constructor entry references')
    ops(rom, sites[1]-4, 'movs r0, #0', 'adds r1, r5, #0', 'bl #0x800ce08')
    for site in sites[2:4]:
        ops(rom, site-2, 'movs r0, #0', 'bl #0x800ce08')
    wave = producers(rom, mapping, index, dict(data=[[0x144, 'data_08149AD4', 0],
                                                    [0x148, 'data_08149AF4', 0]], functions=[], switches=[]))
    modes = sorted({row[2] for row in wave['caller_arguments']})
    require(set(modes) <= {0, 1, 2}, 'wave descriptor mode exceeds constructor tables')
    require(direct_sites(rom, 0x080D993C) == [0x0811E2E4] and not direct_sites(rom, 0x080D9528)
            and not any(pack('<I', p) in rom for p in (0x080D993C, 0x080D993D, 0x080D9528))
            and rom.count(pack('<I', 0x080D9529)) == 1 and
            unpack_from('<I', rom, 0xD9968)[0] == 0x080D9529, 'changed second descriptor provider')
    ops(rom, 0x0811E2DE, 'movs r1, #0', 'movs r2, #2', 'ldr r3, [sp, #0x28]', 'bl #0x80d993c')
    ops(rom, 0x080D9948, 'lsls r2, r2, #0x18', 'lsrs r2, r2, #0x18', 'mov r4, sp',
        'strh r0, [r4, #0x14]', 'mov r0, sp', 'strh r1, [r0, #0x16]', 'strh r2, [r0, #0x18]')
    ops(rom, 0x080D9580, 'ldrh r1, [r6, #0x18]', 'strb r1, [r5, #8]')
    ops(rom, 0x080D9592, 'ldrb r0, [r5, #8]', 'movs r3, #0', 'ldrsh r1, [r1, r3]',
        'add r2, sp, r2', 'ldr r2, [r2]', 'bl #0x800ce08')
    return dict(sites=sites, wave=wave['caller_arguments'], fixed_modes=[0, 0, 0, 2])


def prove(data, rom, mapping, index, objects, bindings, ins, calls, refinement, words):
    provider(rom)
    require(data == rom[OWNER-match.ROM_BASE:END-match.ROM_BASE] and len(ins) == 114 and calls == CALLS
            and bindings == BINDINGS and not words, 'changed scanline constructor CFG or bindings')
    require(span_record(OWNER, END, *indices(mapping, index), rom)['instrs'] == 114,
            'incorrect reachable constructor instruction count')
    names = match.parse_data_symbols(objects)
    require(all(names.get(f'data_{a:08X}') == a for a in TABLES), 'incorrect scanline table address')
    partition = graph.partition(data, OWNER, refinement, ins, words)
    require([(row['address'], row['value'], row['load_sites']) for row in partition['words']] ==
            [(0x0800CE70, TABLES[0], [0x0800CE2A]), (0x0800CE74, TABLES[1], [0x0800CE32]),
             (0x0800CE78, TABLES[2], [0x0800CE3E])], 'changed constructor literal partition')
    block(ins, 0x0800CE26, 'add r6, sp, #0x10', 'adds r1, r6, #0', 'ldr r0, [pc, #0x44]',
          'ldm r0!, {r2, r3, r4}', 'stm r1!, {r2, r3, r4}', 'add r5, sp, #0x1c',
          'ldr r1, [pc, #0x40]', 'adds r0, r5, #0', 'movs r2, #6', 'bl #0x81443fc',
          'add r4, sp, #0x24', 'ldr r1, [pc, #0x38]', 'adds r0, r4, #0', 'movs r2, #6',
          'bl #0x81443fc', 'lsls r0, r7, #2', 'adds r6, r6, r0', 'ldr r0, [r6]',
          'lsls r2, r7, #1', 'adds r5, r5, r2', 'ldrh r1, [r5]', 'adds r4, r4, r2',
          'ldrh r2, [r4]', 'mov r3, r8', 'bl #0x800c3cc')
    block(ins, 0x0800CE5E, 'adds r5, r0, #0', 'cmp r7, #1', 'beq #0x800ce92', 'cmp r7, #1',
          'bgt #0x800ce7c', 'cmp r7, #0', 'beq #0x800ce84', 'b #0x800cece')
    block(ins, 0x0800CE7C, 'ldr r0, [sp, #0x2c]', 'cmp r0, #2', 'beq #0x800cea8', 'b #0x800cece',
          'adds r0, r5, #0', 'bl #0x800c614', 'str r0, [sp]', 'movs r1, #1', 'mov sb, r1', 'b #0x800cece')
    block(ins, 0x0800CE92, 'adds r0, r5, #0', 'bl #0x800c614', 'str r0, [sp]', 'movs r2, #0xa0',
          'lsls r2, r2, #1', 'adds r0, r0, r2', 'str r0, [sp, #4]', 'movs r3, #2', 'mov sb, r3', 'b #0x800cece')
    block(ins, 0x0800CEA8, 'adds r0, r5, #0', 'bl #0x800c614', 'adds r1, r0, #0', 'str r1, [sp]',
          'movs r4, #0xa0', 'lsls r4, r4, #1', 'adds r0, r1, r4', 'str r0, [sp, #4]', 'movs r2, #0xa0',
          'lsls r2, r2, #2', 'adds r0, r1, r2', 'str r0, [sp, #8]', 'movs r3, #0xf0', 'lsls r3, r3, #2',
          'adds r0, r1, r3', 'str r0, [sp, #0xc]', 'movs r4, #4', 'mov sb, r4')
    block(ins, 0x0800CECE, 'movs r1, #0', 'cmp r1, sb', 'bge #0x800cef4', 'movs r2, #0',
          'lsls r0, r1, #2', 'adds r4, r1, #1', 'mov r1, sp', 'adds r3, r1, r0', 'ldr r0, [r3]',
          'lsls r1, r2, #1', 'adds r0, r0, r1', 'mov r1, sl', 'strh r1, [r0]', 'adds r2, #1',
          'cmp r2, #0x9f', 'ble #0x800cede', 'adds r1, r4, #0', 'cmp r1, sb', 'blt #0x800ced4')
    helper = helper_facts(rom, mapping, index)
    effects = contract(rom[HELPER-match.ROM_BASE:HELPER-match.ROM_BASE+98], 6)
    layout = []
    for mode in range(3):
        callback = unpack_from('<I', rom, TABLES[0]-match.ROM_BASE + 4*mode)[0]
        size, width = (unpack_from('<H', rom, table-match.ROM_BASE + 2*mode)[0] for table in TABLES[1:])
        planes = 1 << mode
        require(size == planes*160*2 and width == planes*2, 'scanline allocation does not fit the planes')
        bank_bytes = (161*width + 3) & ~3
        layout.append(dict(mode=mode, callback=callback, stack_reads=[16+4*mode, 28+2*mode, 36+2*mode],
                           plane_offsets=list(range(0, size, 320)), halfword_writes=160*planes,
                           payload_bytes=size, bank_bytes=bank_bytes, allocation_bytes=32+size+2*bank_bytes))
    return dict(schema=buffers.SCHEMA, instructions=len(ins), calls=BINDINGS['calls'], runtime_calls=[],
                partition=partition, environment=environment_fingerprint(), caller_modes=caller_modes(rom,mapping,index),
                buffers=dict(copy_helper=helper, six_byte_copy=effects, modes=layout),
                contract='Mode 0, 1 or 2 from the reviewed caller and descriptor paths; descriptors and task '
                         'state remain live and unmodified between phases. The original manager has a free '
                         'slot and returns a successful disjoint aligned allocation. The installed clearer '
                         'is intact. The constructor initializes every payload halfword before returning.')
