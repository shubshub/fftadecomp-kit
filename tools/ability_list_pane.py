"""The USA ability pane, its two private range bytes and its original scene allocation."""
from hashlib import sha256
from pathlib import Path
import struct

from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB

import ability_range_local_bytes as ranges
import match
import menu_roster_filter as heap
import named_data_buffer_profile as named
import owner_graph_profile as graph
from ability_range_local_bytes import block, require
from known_query_native_closure_profile import environment_fingerprint
from sdk_cpuset_halfword import TOKEN, base_header
from software_double_profile import indices, span_record
from software_float_profile import ROM_SHA256

OWNER = 0x0807B928
FIRST = 0x080CCE60
LOOKUP = 0x080CD480
SCENE = 0x03002818
POINTS = 142
HEADER = 0x230
ROW = 20
PANE = 0x5AC0
SCENE_SIZE = 0x7240
ROW_TABLE = 0x0851BA84
ROW_END = 0x0851D0F4
JOBS = 0x08521A14
JOB_END = 0x085231A4
# Large menu callbacks supply only the executed argument-setup slices below.
NATIVE = (
    (0x0807B928, 0x0807BA3C, 'f3af8683c9fce373fe8d3a2b1b9722e2d5b77f45371f06554b0c5dc1f9ef9e31'),
    (0x080CCE60, 0x080CCF44, '66cde176e8895f3db88f9d5c02e2629aae32b32497fbfb4dc9bc7647ea7ce799'),
    (0x080CD480, 0x080CD498, 'efe226f48d56eb50677e049b1643e6061cea2dbbeee0fbf06d9cd6b007bc7b87'),
    (0x080C92F0, 0x080C9314, '75875c8fb568e97c7d96eee0e6bf7a48f39a75601d60204372f4ad19cd0a4c25'),
    (0x080C8570, 0x080C8A24, '1fa2f1bfd1d7974ce8a3387acaa6b2b301d42c79475938e5f6f6cc7cd8a18057'),
    (0x080C9ED8, 0x080C9F86, '327227bcbe2f91516265cbd688319a7904337e5a54bb337a450b6ed7892b2314'),
    (0x0807109C, 0x08071234, '71425f80bfd7caea0411e97db43834225697858317f1d57385cacf8486bcd53d'),
    (0x08071234, 0x080712D0, '29271412dd43fa7e6edf8e9bd02c548ae0df1b39f8584307c866ca110362073f'),
    (0x08070604, 0x08070A38, '9995772ba9da9c9c4b9cdb579fa588aaafc1e97772ae713c175d1442353e6e3e'),
    (0x0807C7E8, 0x0807D240, '754614a33f08a1bb8ec81e450eb1572e37b8a24e7a4c90aa3df7b46bbda57a8c'),
    (0x0807D240, 0x0807D8EA, '86d726a574733e23fa3d606fe0826690fa98b6de9eb5c0f727e1e128cfddc2ad'),
    (0x080245DC, 0x08024670, 'd6ad8f56db57b62aae82087cdfdb3b4e18ba8beb09e24a6b2ba59a1fa4789323'),
    (0x0800718C, 0x080071A0, 'e2282056fb7629c1349bf86ea51de56439b4bd6d9deb682033476d4260d2683d'),
    (0x080651FC, 0x08065608, '5c952cb6932767e30979a40dc050c62098fcd7d98f6ecabe339e0255a3c7b5f7'),
    (0x08022854, 0x08022868, 'dc40e21202fe3f3244adc6024444db000876a9b76336db4627e6826cb0f5d37b'),
)


def check_source(root):
    import plausible
    source = (Path(root) / 'src/0807B928.c').read_text()
    header = (Path(root) / 'include/ffta.h').read_bytes()
    require(base_header(header, ('func_0807B928', 'func_080CCE60', 'func_080CD480',
                                 'g_table_085567F0', 'data_03002818'))
            and not any(marker in source for marker in (chr(92), '??', '%:', chr(0))),
            'unexpected ability pane preprocessing or header')
    tokens = ' '.join(TOKEN.findall(plausible.strip_comments_and_strings_keep_strings(source)))
    prefix, end, body = tokens.partition('s32 index , count ; AbilityRow * rows ;')
    require(end and '#' not in body and sha256((prefix+end).encode()).hexdigest() ==
            'ed41d999ff8c9d04e30a1628a2d9f69a124b404aceae80909ff0979b23c0a8e9',
            'unexpected ability pane declarations, private indices or row dimensions')


def bindings():
    return dict(calls=[[88,'func_080CCE60'],[192,'func_080CD480']],
                data=[[256,'g_table_085567F0',0],[264,'data_03002818',0]], functions=[], switches=[])


def limits(rom, objects):
    names = match.parse_data_symbols(objects)
    expected = {'g_table_0851BA84': ROW_TABLE, 'data_0851D0F4': ROW_END,
                'g_table_08521A14': JOBS, 'data_085231A4': JOB_END,
                'data_03002818': SCENE, 'g_table_085567F0': 0x085567F0}
    require(all(names.get(key) == value for key, value in expected.items()), 'changed table bounds or scene symbol')
    starts = struct.unpack_from('<24I', rom, ROW_TABLE-match.ROM_BASE)
    require(starts[0] == ROW_TABLE+24*4, 'ability table must immediately precede its first row')
    widths = []
    for start, end in zip(starts, (*starts[1:],ROW_END)):
        require(start < end and (end-start)%8 == 0, 'invalid native ability-row extent')
        widths.append((end-start)//8)
    require(max(widths) == POINTS, 'unexpected maximum ability row')
    cap_table = struct.unpack_from('<I', rom, 0xC9EF0)[0]
    require(cap_table == 0x080C9EF4, 'changed native race capacity table')
    caps = [0]
    for race, target in enumerate(struct.unpack_from('<23I', rom, cap_table-match.ROM_BASE), 1):
        require(0x080C9F50 <= target <= 0x080C9F7E and target % 2 == 0, 'invalid race capacity target')
        opcode = struct.unpack_from('<H', rom, target-match.ROM_BASE)[0]
        require(opcode >> 8 == 0x20 and 0 < (opcode & 255) <= widths[race], 'invalid native race capacity')
        caps.append(opcode & 255)
    require(max(caps) == POINTS, 'changed native unit ability capacity')
    count, remainder = divmod(JOB_END-JOBS,52)
    require(count == 116 and remainder == 0, 'changed indexed job table capacity')
    ranges_seen, returning, repeating = set(), 0, 0
    for first in range(count):
        for fallback in range(count):
            job = first
            seen = set()
            while job not in seen:
                require(job < count, 'a job redirect escapes the original record table')
                seen.add(job)
                offset = JOBS - match.ROM_BASE + 52*job
                redirect = rom[offset+5]
                if redirect == 0:
                    ranges_seen.add((rom[offset+46],rom[offset+47]))
                    returning += 1
                    break
                job = fallback if redirect == 255 else redirect
            else:
                repeating += 1
    maximum = max(last for first,last in ranges_seen)
    iterations = max(max(0,last-first+1) for first,last in ranges_seen)
    require(maximum < POINTS and iterations <= POINTS, 'returning job range exceeds the unit point array')
    return dict(row_entries=widths, unit_ability_counts=caps, jobs=count, returning_job_pairs=returning, repeating_job_pairs=repeating,
                maximum_last=maximum, maximum_iterations=iterations,
                modes='1 uses job fields +5/+7, 2 uses +8 for both, and 3 uses job 1 for both. '
                      'Overrides of one for modes 1 or 2 select job 1 and ability row zero after the initial queries. '
                      'Other mode bytes return the range 0..0 and row zero. Mode 3 also uses row zero.',
                domain='Job IDs read by a mode are original table members. Redirects must return for completion. '
                       'For a nonempty scan, the returned row covers each inspected ability index; for each '
                       'accepted ability the unit race is below 24 and its own row covers that index; for ordinary '
                       'nonzero races the accepted index is within the native race capacity. The 142 point bytes in the live unit and the two different row lookups are separate bounds.')


def providers(rom, mapping, index):
    entries, rows = indices(mapping,index)
    for address, end, digest in (*NATIVE, *heap.heap_providers()):
        row = span_record(address,end,entries,rows,rom)
        require(sha256(rom[address-match.ROM_BASE:end-match.ROM_BASE]).hexdigest() == digest,
                f'changed original ability list provider at {address:08X}')
        if address == OWNER:
            require(row['instrs'] == 124, 'changed ability list instruction count')
    md = Cs(CS_ARCH_ARM,CS_MODE_THUMB)
    def check(address, *ops):
        offset = address-match.ROM_BASE
        block({i.address:i for i in md.disasm(rom[offset:offset+4*len(ops)],address)}, address, *ops)

    def word(address):
        return struct.unpack_from('<I', rom,address-match.ROM_BASE)[0]

    check(0x08024642, 'ldr r5, [pc, #0x24]', 'movs r4, #0xc6', 'lsls r4, r4, #8',
          'adds r0, r4, #0', 'bl #0x8022840', 'str r0, [r5]', 'ldr r0, [pc, #0x18]', 'str r4, [r0]')
    check(0x080711D6, 'ldr r2, [pc, #0x54]', 'adds r1, r0, r2', 'ldr r3, [pc, #0x54]',
          'adds r0, r0, r3', 'str r0, [r1]')
    require((word(0x0807122C),word(0x08071230)) == (0x2E1C,PANE) and PANE+HEADER+POINTS*ROW <= SCENE_SIZE,
            'changed pane partition or insufficient row allocation')
    check(0x080706E4, 'ldr r5, [pc, #0x5c]', 'ldr r1, [r5]', 'ldr r4, [pc, #0x5c]',
          'adds r2, r1, r4', 'ldr r0, [pc, #0x5c]', 'ldr r0, [r0]', 'str r0, [r2]')
    require(tuple(word(x) for x in (0x08070744,0x08070748,0x0807074C)) ==
            (SCENE,0x1D0C,0x030027F4), 'changed selected unit binding')
    for start, literals, caller in ((0x0807C89A,0x0807C964,0x0807C8B0),
                                    (0x0807D2EC,0x0807D37C,0x0807D302)):
        require(tuple(word(literals+4*i) for i in range(3)) == (0x1131,0xBF9,0x2E1C),
                f'changed original caller arguments at {start:08X}')
        check(caller, 'bl #0x807b928')
    check(0x080CCF1A, 'mov r0, r8', 'cmp r0, #0', 'beq #0x80ccf22', 'strb r7, [r0]',
          'mov r0, sb', 'cmp r0, #0', 'beq #0x80ccf2a', 'strb r1, [r0]', 'ldr r0, [pc, #0x14]',
          'lsls r1, r6, #2', 'adds r1, r1, r0', 'ldr r0, [r1]')
    check(0x080C9308, 'ldrb r0, [r3, #5]', 'ldrb r1, [r3, #7]', 'bl #0x80c8570')
    check(0x0806549C, 'lsls r0, r0, #0x10', 'lsrs r0, r0, #0xe', 'ldr r1, [pc, #0x74]',
          'adds r4, r4, r1', 'adds r4, r4, r0', 'ldr r0, [r4]', 'str r0, [r5]')
    require(word(0x08065514) == 0x030027F4 and word(0x08065518) == 0x424,
            'changed preceding unit selection')
    check(0x080CD480, 'lsls r0, r0, #0x18', 'lsls r1, r1, #0x18', 'ldr r2, [pc, #0xc]',
          'lsrs r0, r0, #0x16', 'adds r0, r0, r2', 'lsrs r1, r1, #0x15', 'ldr r0, [r0]',
          'adds r0, r0, r1', 'bx lr')
    require(word(0x080CD494) == ROW_TABLE, 'changed lookup row pointer')
    return dict(arena_allocation=0xC600, constructor=0x0807109C, live_size=SCENE_SIZE, pane_offset=PANE,
                selected_unit=[0x030027F4,0x1D0C], selected_unit_store=0x080706F0,
                callers=[0x0807C8B0,0x0807D302], release=0x08071234,
                condition='Successful live nested scene allocation, selected live 0x108-byte unit, stable '
                          'scene and unit slots, and writable nonoverlapping pane. The partition expires at release.')


def prove(data, rom, mapping, index, objects, original, ins, calls, refinement, words):
    require(len(ins) == 124 and not words and original == bindings() and
            calls == {0x0807B980:FIRST,0x0807B9E8:LOOKUP} and sha256(data).hexdigest() == NATIVE[0][2],
            'changed original ability pane owner, output registers or ELF bindings')
    resolver = named.NamedDataBufferProof(rom,mapping,index,objects)
    require(resolver.identities['rom_sha256'] == ROM_SHA256, 'ability pane requires the indexed USA ROM')
    category = ranges.query(resolver)
    require(struct.unpack_from('<6I',data,252) == (0xFFFFFDF4,0x085567F0,0x1A7,SCENE,0x1D0C,0x201),
            'changed frame size, text table or local byte offset')
    block(ins, 0x0807B972, 'lsls r1, r1, #0x18', 'lsrs r1, r1, #0x18', 'add r4, sp, #0x200',
          'ldr r5, [pc, #0xbc]', 'add r5, sp, r5', 'adds r2, r4, #0', 'adds r3, r5, #0', 'bl #0x80cce60')
    block(ins, 0x0807B98E, 'strh r3, [r0, #0xc]', 'ldrb r6, [r4]', 'ldrb r5, [r5]',
          'cmp r6, r5', 'bgt #0x807ba0c', 'lsls r0, r6, #3', 'adds r5, r0, r1', 'mov r4, r8', 'mov r2, sp')
    block(ins, 0x0807B9AC, 'adds r0, #0x40', 'adds r0, r0, r6', 'ldrb r0, [r0]', 'cmp r0, #0',
          'beq #0x807b9fe', 'ldrb r0, [r5, #6]', 'cmp r0, #0', 'beq #0x807b9fe',
          'movs r0, #0', 'strh r6, [r2]', 'strh r3, [r4]', 'strh r0, [r4, #2]',
          'ldrh r0, [r5]', 'str r0, [r4, #8]', 'ldrh r0, [r5, #2]', 'strh r0, [r4, #0xc]')
    block(ins, 0x0807B9E4, 'str r2, [sp, #0x204]', 'str r3, [sp, #0x208]', 'bl #0x80cd480',
          'ldrb r1, [r0, #7]', 'strb r1, [r4, #0xf]', 'ldrb r0, [r0, #6]', 'strb r0, [r4, #0x10]',
          'adds r4, #0x14', 'ldr r2, [sp, #0x204]', 'adds r2, #2', 'ldr r3, [sp, #0x208]',
          'adds r3, #1', 'adds r5, #8', 'adds r6, #1', 'ldr r0, [pc, #0x34]', 'add r0, sp, r0',
          'ldrb r0, [r0]', 'cmp r6, r0', 'ble #0x807b9a0', 'str r3, [r7]', 'adds r0, r3, #0')
    return dict(schema=named.ABILITY_RANGE_SCHEMA, instructions=len(ins), calls=original['calls'],runtime_calls=[],
                partition=graph.partition(data,OWNER,refinement,ins,words), category_query=category,
                scene=providers(rom,mapping,index), bounds=limits(rom,objects),
                frame=dict(size=0x20C,saved=32,indices=[0,512],first=512,last=513,spills=[516,520],
                           index_write=0x0807B9BE,
                           condition='Private writable frame. Only accepted ability indices are written as '
                                     'halfwords; neither the index array nor the range outputs escape the call.'),
                rows=dict(offset=HEADER,bytes=ROW,first_description_zeroed=True,point_bytes=POINTS,
                          storage='The header always points to its own rows; accepted rows retain scan order.'),
                environment=environment_fingerprint())
