"""Native bounds for the inventory list's two accepted-item arrays and scene pane."""
from hashlib import sha256
from pathlib import Path
import struct

from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB

from ability_range_local_bytes import block, require
from known_query_native_closure_profile import environment_fingerprint
import match
from menu_roster_filter import heap_providers
import named_data_buffer_profile as named
import owner_graph_profile as graph
from sdk_cpuset_halfword import TOKEN, base_header
from software_double_profile import indices, span_record
from software_float_profile import ROM_SHA256

OWNER = 0x0808CBDC
END = 0x0808D0C4
INVENTORY = 0x02001940
DEFINITIONS = 0x0851D180
SCENE = 0x03002818
PANE = 0x4340
NEXT_PANE = 0x5AC0
HEADER = 0x230
ROW = 20
LIMIT = 256

# Each row supplies both independently counted loops and their half-open category range.
GROUPS = (
    (0x0808CC52, 0x0808CC98, 21, 24),
    (0x0808CD0A, 0x0808CD50, 24, 27),
    (0x0808CDB2, 0x0808CDF8, 1, 20),
    (0x0808CE5A, 0x0808CEA0, 20, 21),
    (0x0808CF02, 0x0808CF48, 27, 30),
    (0x0808CF9E, 0x0808CFE4, 30, 31),
)
SITES = (0x0808D762, 0x0808D7E0, 0x0808DB94, 0x0808DC62, 0x0808DCA8,
         0x0808DF4C, 0x0808E338, 0x0808E85E, 0x0808ED90, 0x0808EDDC, 0x0808EFA8)
PROVIDERS = (
    (OWNER, END, '8971542cd47026ddd1234267907c44a0f2b5a1e12559c5ba9b0646308e81c19a'),
    (0x0808D624, 0x0808EE74, 'd13fbb048159738f286c63cf642e6b43812c6c48f955d3ea2fd6786d0b6e8436'),
    (0x0808EF90, 0x0808EFCA, '302003a95158cd0c82bdbb6c57b4c61be06e5ac0064da702dcc1ce9f6a538b5a'),
    (0x080CA900, 0x080CA9E6, '6ae7e31b93895ffe848beb082c2d9fcd1393b18efbeff6ce61fddf54e0695609'),
    (0x080CA9E8, 0x080CAA74, '21b05ab36a37a6f1c30dce480267fab9447b0c1d375bfe2eb5c17d43ba3fea6b'),
    (0x080CAB24, 0x080CABA6, 'd841628d8276a088ed301ab769b3058f0c4c71b4cea94fb818d96e1811c1e933'),
    (0x0807109C, 0x08071234, '71425f80bfd7caea0411e97db43834225697858317f1d57385cacf8486bcd53d'),
    (0x08071234, 0x080712D0, '29271412dd43fa7e6edf8e9bd02c548ae0df1b39f8584307c866ca110362073f'),
    (0x080245DC, 0x08024670, 'd6ad8f56db57b62aae82087cdfdb3b4e18ba8beb09e24a6b2ba59a1fa4789323'),
)

def check_source(root):
    import plausible
    root = Path(root)
    names = ('func_0808CBDC', 'ItemList', 'g_state_02001940', 'g_table_0851D180', 'g_table_08526680')
    require(base_header((root/'include/ffta.h').read_bytes(), names), 'changed inventory-list base types')
    source = (root/'src/0808CBDC.c').read_text()
    require(not any(marker in source for marker in (chr(92), '??', '%:', chr(0))),
            'unexpected inventory-list preprocessing')
    tokens = ' '.join(TOKEN.findall(plausible.strip_comments_and_strings_keep_strings(source)))
    require(sha256(tokens.encode()).hexdigest() == '6b662765f05f81fea7e9447f8e488f0a81e02633be6d6204ac0fa0035553acf7',
            'changed inventory-list C layout or semantics')


def bindings():
    data = [[0xEC, 'g_table_08526680', 0]]
    for inventory, definitions in ((0xF8,0x104),(0x1A0,0x1AC),(0x248,0x254),
                                   (0x2F0,0x2FC),(0x398,0x3A4),(0x484,0x490)):
        data.extend(([inventory,'g_state_02001940',0], [definitions,'g_table_0851D180',0]))
    return dict(calls=[], data=data, functions=[], switches=[])


def bound_groups(rom, objects):
    symbols = match.parse_data_symbols(objects)
    expected = {'g_state_02001940':INVENTORY, 'g_table_0851D180':DEFINITIONS,
                'g_table_08520080':DEFINITIONS+376*32, 'g_table_08526680':0x08526680,
                'data_03002818':SCENE}
    require(all(symbols.get(name) == address for name,address in expected.items()),
            'changed inventory, definition extent, strings or scene binding')
    categories = rom[DEFINITIONS-match.ROM_BASE+8:DEFINITIONS-match.ROM_BASE+376*32:32]
    require(len(categories) == 376 and categories[0] == 0, 'changed vacant inventory definition')
    limits = [sum(first <= c < end for c in categories) for _,_,first,end in GROUPS]
    require(limits == [23,51,252,12,23,14] and max(limits) < LIMIT and
            HEADER + LIMIT*ROW <= NEXT_PANE - PANE, 'inventory list exceeds stack or pane capacity')
    return limits


def scan(ins, pc, first, end, overflow):
    src, dest, slots, index, count = (('r2','r1','r3','r4','r6') if overflow else
                                      ('r1','r5','r2','r3','r4'))
    # The same reject target skips BOTH writes and the accepted-count update.
    skip = pc + 32
    block(ins, pc, f'ldrh r0, [{src}]', 'lsls r0, r0, #5',
          'add r0, ip' if overflow else 'adds r0, r0, r6', 'ldrb r0, [r0, #8]',
          f'cmp r0, #{hex(first) if first >= 10 else first}', f'blt #{hex(skip)}',
          f'cmp r0, #{hex(end)}', f'bge #{hex(skip)}',
          f'ldrb r0, [{src}, #2]', 'cmp r0, #0', f'beq #{hex(skip)}',
          f'strh {index}, [{slots}]', f'ldr r0, [{src}]', f'stm {dest}!, {{r0}}',
          f'adds {slots}, #2', f'adds {count}, #1', f'adds {src}, #4', f'adds {index}, #1',
          f'cmp {index}, #0xe' if overflow else 'cmp r3, r7', f'blt #{hex(pc)}')


def providers(rom, mapping, index):
    entries, rows = indices(mapping, index)
    for start,end,digest in (*PROVIDERS, *heap_providers()):
        body = rom[start-match.ROM_BASE:end-match.ROM_BASE]
        if start in (0x080CA900, 0x080CA9E8):
            # The shipped text index still counts literal halfwords for these two
            # supporting providers. Check both native spans and decode their CFGs.
            from owner_admission_profile import refine
            named.validate_owner(body, start, rom, mapping, index)
            count = refine(body,start,mapping)['instrs']
            expected_count = 106 if start == 0x080CA900 else 62
            entry = next(r for r in entries if int(r['rom'],16) == start)
            annotation = next(r for r in rows if int(r[0],16) == start)
            require(entry['instrs'] == expected_count == count and int(annotation[3]) in
                    (count,len(body)//2), 'changed inventory provider instruction accounting')
        else:
            row = span_record(start,end,entries,rows,rom)
        require(sha256(body).hexdigest() == digest,
                f'changed inventory-list native provider at {start:08X}')
        if start == OWNER:
            require(row['instrs'] == 564, 'wrong decoded inventory-list index count')
    md = Cs(CS_ARCH_ARM,CS_MODE_THUMB)
    def decode(pc, length):
        offset = pc-match.ROM_BASE
        return {i.address:i for i in md.disasm(rom[offset:offset+length], pc)}
    def word(pc):
        return struct.unpack_from('<I',rom,pc-match.ROM_BASE)[0]
    # The large live scene allocates 0x7240 bytes and binds its own neighboring panes.
    block(decode(0x080710B2,18),0x080710B2, 'ldr r4, [pc, #0x5c]', 'str r0, [r4]',
          'ldr r5, [pc, #0x5c]', 'ldr r1, [pc, #0x5c]', 'bl #0x8007138',
          'adds r1, r0, #0', 'str r1, [r5]')
    require(word(0x08071114) == SCENE and word(0x08071118) == 0x7240,
            'changed scene allocation')
    block(decode(0x080711CC,22),0x080711CC,'ldr r1, [pc, #0x54]', 'adds r2, r0, r1',
          'ldr r3, [pc, #0x54]', 'adds r1, r0, r3', 'str r1, [r2]',
          'ldr r2, [pc, #0x54]', 'adds r1, r0, r2', 'ldr r3, [pc, #0x54]',
          'adds r0, r0, r3','str r0, [r1]')
    require([word(x) for x in range(0x08071224,0x08071234,4)] == [0x2D50,PANE,0x2E1C,NEXT_PANE],
            'changed scene pane offsets')
    for site in SITES:
        start = site - (8 if site == SITES[0] else 6)
        code = decode(start, site+4-start)
        load = code[start]
        op, lit = struct.unpack_from('<H',rom,start-match.ROM_BASE)[0], load.op_str.split(',')[0]
        require(op >> 11 == 9 and word(((start+4)&~3) + (op & 255)*4) == 0x2D50,
                'caller does not use the item-pane field')
        block(code, start+2, f'adds r1, r1, {lit}', 'ldr r1, [r1]')
        block(code, site, 'bl #0x808cbdc')
    return dict(constructor=0x0807109C, release=0x08071234, scene_size=0x7240,
                field=0x2D50, offset=PANE, next_pane=NEXT_PANE, callsites=list(SITES))


def prove(data, address, rom, mapping, index, objects, original, ins, edges, calls, refinement, words):
    require(address == OWNER and len(data) == END-OWNER and len(ins) == 564 and not calls and not words
            and original == bindings() and sha256(rom).hexdigest() == ROM_SHA256
            and data == rom[OWNER-match.ROM_BASE:END-match.ROM_BASE],
            'complete original USA inventory-list leaf and its original ELF bindings required')
    limits = bound_groups(rom, objects)
    scene = providers(rom,mapping,index)
    block(ins,OWNER, 'push {r4, r5, r6, r7, lr}', 'mov r7, sl', 'mov r6, sb', 'mov r5, r8',
          'push {r5, r6, r7}', 'ldr r4, [pc, #0xdc]', 'add sp, r4', 'mov sl, r1',
          'lsls r0, r0, #0x10', 'lsrs r0, r0, #0x10', 'movs r1, #0xc0',
          'lsls r1, r1, #3', 'add r1, sp, r1', 'str r0, [r1]')
    block(ins,0x0808CC1E, 'movs r7, #0x8c', 'lsls r7, r7, #2', 'add r7, sl',
          'ldr r0, [pc, #0xa8]', 'add r0, sp, r0', 'str r7, [r0]', 'str r7, [r3, #0x18]')
    require(struct.unpack_from('<i',data,0x0808CCC4-OWNER)[0] == -0x608 and
            struct.unpack_from('<I',data,0x0808CCD0-OWNER)[0] == 0x604,
            'changed private stack allocation or row-base spill')
    block(ins,0x0808D01E, 'movs r6, #0x80', 'lsls r6, r6, #3', 'add r6, sp, r6',
          'mov r2, sp', 'ldr r3, [pc, #0x48]', 'add r3, sp, r3', 'ldr r4, [r3]', 'adds r1, r4, #0')
    block(ins,0x0808D0B0, 'movs r3, #0xc1', 'lsls r3, r3, #3', 'add sp, r3',
          'pop {r3, r4, r5}', 'mov r8, r3', 'mov sb, r4', 'mov sl, r5',
          'pop {r4, r5, r6, r7}', 'pop {r1}', 'bx r1')
    for first_scan,second_scan,first,end in GROUPS:
        block(ins,first_scan-10, 'adds r1, r0, #0', 'mov r5, sp', 'movs r2, #0x80',
              'lsls r2, r2, #3', 'add r2, sp, r2')
        block(ins,second_scan-12, 'mov ip, r3' if first_scan == GROUPS[0][0] else 'mov ip, r2',
              'mov r2, r8', 'add r1, sp, r1', 'movs r7, #0x80', 'lsls r7, r7, #3',
              'adds r3, r0, r7')
        scan(ins,first_scan,first,end,False)
        scan(ins,second_scan,first,end,True)
        block(ins, first_scan+40, 'lsls r0, r4, #0x18','lsrs r5, r0, #0x18','mov sb, r5',
              'lsls r1, r5, #2','lsls r0, r5, #1','add r0, sp, r0')
    backward = {(pc,to) for pc,targets in edges.items() for to in targets if to <= pc}
    require(backward == {(pc+38,pc) for group in GROUPS for pc in group[:2]} | {(0x0808D0A8,0x0808D02E)},
            'unexpected cycle or scan induction')
    block(ins,0x0808D00C,'lsls r0, r6, #0x18','lsrs r7, r0, #0x18','adds r5, r5, r7',
          'movs r0, #0','mov ip, r0','cmp ip, r5','bge #0x808d0aa')
    block(ins,0x0808D07E,'cmp ip, sb','bge #0x808d08a','strb r3, [r1, #0x10]',
          'ldrh r0, [r6]','strh r0, [r1, #0x12]','b #0x808d09a','cmp ip, r7','bge #0x808d092')
    block(ins,0x0808D09A,'adds r6, #2','adds r2, #4','adds r4, #0x14','adds r1, #0x14',
          'movs r3, #1','add ip, r3','cmp ip, r5','blt #0x808d02e','mov r7, sl',
          'str r5, [r7]', 'adds r0, r5, #0')
    partition = graph.partition(data,OWNER,refinement,ins,words)
    return dict(schema=named.ITEM_LIST_SCHEMA,instructions=len(ins),calls=[],runtime_calls=[],
                partition=partition, environment=environment_fingerprint(), scene=scene,
                inventory=dict(slots=[361,14],definition_stride=32,definitions=376,
                               category_limits=limits,maximum_rows=max(limits),
                               providers=[0x080CA900,0x080CA9E8,0x080CAB24],
                               condition='Stable original inventory. All slot IDs are 0..375. Occupied IDs are '
                               'unique across both banks. The native item adder looks up an existing ID before '
                               'inserting it into an empty slot. These are input conditions, including for loaded saves.'),
                frame=dict(size=0x608,saved=32,items=[0,0x400],slots=[0x400,0x600],
                           category_spill=0x600,rows_spill=0x604,
                           condition='Writable private frame, disjoint from inventory and live scene. '
                           'Each accepted entry initializes its word and halfword before either is read.'),
                rows=dict(offset=HEADER,stride=ROW,storage=LIMIT,
                          condition='Live nonoverlapping writable pane supplied by the scene until its release. '
                          'Both banks retain scan order. The second bank tag compares the output index with '
                          'the second bank count directly.'))
