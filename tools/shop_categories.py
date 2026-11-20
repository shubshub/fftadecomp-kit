"""Bounds of the regular, supplemental and fallback shop category lists on the USA ROM."""
from hashlib import sha256
from pathlib import Path
from struct import unpack_from

import named_data_buffer_profile as buffers
import owner_graph_profile as graph
import plausible
from ability_range_local_bytes import block, require
from active_entry_shuffle_profile import compiler_symbol_roles
from known_query_native_closure_profile import environment_fingerprint
from positioned_equipment_chance import direct_sites
from sdk_cpuset_halfword import TOKEN, base_header
from software_double_profile import indices, span_record
from software_float_profile import ROM_SHA256
from unit_equipment_attribute import BASE, ITEMS, ops, word

OWNER, END, CALLER, CALL_SITE = 0x0806ED30, 0x0806EE98, 0x08069658, 0x08069C2C
RANK, CATEGORY, FIELD, IS_WEAPON = 0x080CC8B4, 0x080CBD34, 0x080CA7A4, 0x080CB1F4
QUERY, SELECT, COUNT = 0x080CC9F0, 0x080CCCF0, 0x080CECF4
STATE, DISPLAY, FLAGS = 0x02000000, 0x08393B40, 0x02002CC0
SUPPLEMENTAL = (0x08528A44, 0x08528AA4, 0x08528B04, 0x08528B64, 0x08528BC4)
SOURCE_HASH = '475bd3e4fe7dc75d1c0aa59e3f8a45339af3cb7125a76137c5cd7a277455bfcb'
PINS = {
    OWNER: (END, '3143ffd4189a47f01f5d42cdd77a2e57eff6ab5bd03b00da118c23c20dcc6e2a'),
    CALLER: (0x0806B228, '6ff852e01bb772a68a39b3e6d50b8fbc1c3f64600436e4f42fe5a5689ac93606'),
    RANK: (0x080CC8D0, '898d223c5b33322baa2d0bf2f4688fb82dbbc221a45602c4e3a43f19b663b3eb'),
    CATEGORY: (0x080CBDC0, '5e9c4ccb745057c81d9ac2d936dc0fb0b6fcdd023f51a52d1e5c03f1dff6fc9d'),
    FIELD: (0x080CA8FE, 'ff46b43099ea0296e3f9646af8166d45efb5375d73b657984d4b2370b01221f1'),
    IS_WEAPON: (0x080CB210, '67614f5de7425edf94261d68997204b68c3643818af592b490e7da10d1f53852'),
    QUERY: (0x080CCA20, '02b91d8122fca84c5982edb0b1d7b464cc87b36195318e3bd19cd0482bccb7ba'),
    SELECT: (0x080CCD4E, '186086a95cf59fed70f2930df3ffa82856abbb432ed3097dc3458bc81eb422ca'),
    COUNT: (0x080CED2C, 'dc51e919087636d0f22cca20c4e740802ef755214995f5cfb010d0d2c954dc17'),
}
CALLS = {0x1C:RANK, 0x8A:CATEGORY, 0xBA:QUERY, 0xC8:CATEGORY, 0xDA:CATEGORY, 0xF0:COUNT}
OBJECTS = {'g_state_02000000': STATE, 'g_table_0851D180': ITEMS, 'data_08393B40': DISPLAY}
DATA = [[0x34, 'g_state_02000000', 0], [0xB0, 'g_table_0851D180', 0],
        [0x160, 'data_08393B40', 0], [0x164, 'g_table_0851D180', 0]]
BINDINGS = dict(calls=[[off,f'func_{target:08X}'] for off,target in CALLS.items()],
                data=DATA, functions=[], switches=[])


def check_source(root):
    path = Path(root)/'src/0806ED30.c'
    source = path.read_text()
    reserved = ('func_0806ED30', 'DisplayState', 'ItemInfo', 'ShopState', *OBJECTS,
                *(f'func_{address:08X}' for address in CALLS.values()))
    require(plausible.include_closure(root, path) == ({'src/0806ED30.c','include/ffta.h'}, []) and
            base_header((Path(root)/'include/ffta.h').read_bytes(), reserved) and
            not any(marker in source for marker in (chr(92), '??', '%:', chr(0))) and
            sha256(' '.join(TOKEN.findall(plausible.strip_comments_and_strings_keep_strings(source))).encode()).hexdigest() == SOURCE_HASH,
            'shop category source requires the six-byte local, display layout, and reviewed declarations')


def check_original(image, bindings, targets):
    expected = {name:(CALLS[off],False) for off,name in BINDINGS['calls']}
    expected.update({name:(address,True) for name,address in OBJECTS.items()})
    require(bindings == BINDINGS and targets == expected and
            not any(row['size'] for row in image['symbols'] if row['name'] in targets),
            'shop category original call and object relocation roles differ')
    compiler_symbol_roles(image, targets)


def classifier(rom):
    # Only selectors 3 and 6 are supplied by the category function. These two
    # table entries read byte fields directly and cannot call back into the UI.
    ops(rom, FIELD, 'push {r4, r5, lr}', 'lsls r0, r0, #0x10', 'lsrs r5, r0, #0x10',
        'lsls r1, r1, #0x18', 'lsrs r2, r1, #0x18', 'lsls r1, r5, #5', 'ldr r0, [pc, #0x10]',
        'adds r4, r1, r0', 'cmp r2, #0x12', 'bls #0x80ca7ba', 'b #0x80ca8f6',
        'lsls r0, r2, #2', 'ldr r1, [pc, #8]', 'adds r0, r0, r1', 'ldr r0, [r0]', 'mov pc, r0')
    require(word(rom,0x080CA7C4) == ITEMS and word(rom,0x080CA7C8) == 0x080CA7CC,
            'shop item field table base differs')
    for selector, offset in ((3,'8'),(6,'0xb')):
        ops(rom, word(rom,0x080CA7CC+4*selector),
            f'ldrb r0, [r4, #{offset}]', 'b #0x80ca8f8')
    ops(rom,0x080CA8F8,'pop {r4, r5}','pop {r1}','bx r1')
    ops(rom,IS_WEAPON,'push {lr}','lsls r0, r0, #0x10','movs r1, #0','ldr r2, [pc, #0x10]',
        'adds r0, r0, r2','lsrs r0, r0, #0x10','cmp r0, #0xfb','bhi #0x80cb206',
        'movs r1, #1','adds r0, r1, #0','pop {r1}','bx r1')
    require(word(rom,0x080CB20C) == 0xffff0000, 'item ID range differs')
    ops(rom,CATEGORY,'push {r4, r5, lr}','lsls r0, r0, #0x10','lsrs r4, r0, #0x10','adds r5, r4, #0')
    for site, field, value, dest, category in ((0x080CBD3C,6,3,0x080CBD4C,0),
            (0x080CBD4C,6,4,0x080CBD5C,1),(0x080CBD6C,3,20,0x080CBD7C,3)):
        imm = str(value) if value < 10 else hex(value)
        ops(rom,site,'adds r0, r4, #0',f'movs r1, #{field}','bl #0x80ca7a4',f'cmp r0, #{imm}',
            f'bne #{dest:#x}',f'movs r0, #{category}','b #0x80cbdba')
    ops(rom,0x080CBD5C,'adds r0, r4, #0','bl #0x80cb1f4','lsls r0, r0, #0x18',
        'cmp r0, #0','beq #0x80cbd6c','movs r0, #2','b #0x80cbdba')
    for site, field, value, branch in ((0x080CBD7C,3,'0x1d','beq #0x80cbda0'),
            (0x080CBD88,6,'5','beq #0x80cbda0'),(0x080CBD94,3,'0x1c','bne #0x80cbda4')):
        ops(rom,site,'adds r0, r4, #0',f'movs r1, #{field}','bl #0x80ca7a4',f'cmp r0, #{value}',branch)
    ops(rom,0x080CBDA0,'movs r0, #4','b #0x80cbdba','ldr r1, [pc, #0xc]','adds r0, r5, r1',
        'lsls r0, r0, #0x10','lsrs r0, r0, #0x10','cmp r0, #0xd','bls #0x80cbdb8','movs r0, #0xff','b #0x80cbdba')
    require(word(rom,0x080CBDB4) == (1<<32)-362, 'special item range differs')
    ops(rom,0x080CBDB8,'movs r0, #5','pop {r4, r5}','pop {r1}','bx r1')


def supplemental_lookup(rom):
    ops(rom,SELECT,'push {lr}','lsls r0, r0, #0x18','lsrs r0, r0, #0x18','subs r0, #2',
        'cmp r0, #4','bhi #0x80ccd48','lsls r0, r0, #2','ldr r1, [pc, #8]',
        'adds r0, r0, r1','ldr r0, [r0]','mov pc, r0')
    require(word(rom,0x080CCD08) == 0x080CCD0C, 'supplemental selector table differs')
    for i, table in enumerate(SUPPLEMENTAL):
        target = 0x080CCD20+8*i
        require(word(rom,0x080CCD0C+4*i) == target and word(rom,target+4) == table,
                'supplemental selector arm or data pointer differs')
        ops(rom,target,'ldr r0, [pc, #0]','b #0x80ccd4a')
    ops(rom,0x080CCD48,'movs r0, #0','pop {r1}','bx r1')
    ops(rom,QUERY,'push {r4, lr}','lsls r0, r0, #0x18','lsrs r0, r0, #0x18',
        'lsls r1, r1, #0x18','lsrs r4, r1, #0x18','bl #0x80cccf0','adds r1, r0, #0','cmp r1, #0',
        'beq #0x80cca08','cmp r4, #0','bne #0x80cca0c','movs r0, #0','b #0x80cca1a','subs r0, r4, #1',
        'lsls r0, r0, #1','adds r0, r1, r0','ldrb r1, [r0, #4]','ldrb r0, [r0, #5]',
        'lsls r0, r0, #8','orrs r0, r1','pop {r4}','pop {r1}','bx r1')
    ops(rom,COUNT,'push {r4, r5, r6, lr}','movs r4, #0','movs r6, #1','ldr r3, [pc, #0x2c]',
        'movs r5, #2','movs r2, #0x1d','ldrb r1, [r3, #1]','adds r0, r6, #0','ands r0, r1','cmp r0, #0',
        'beq #0x80ced14','adds r0, r5, #0','ands r0, r1','cmp r0, #0','beq #0x80ced14','adds r4, #1',
        'adds r3, #0xc','subs r2, #1','cmp r2, #0','bge #0x80ced00','lsls r0, r4, #0x18',
        'lsrs r0, r0, #0x18','pop {r4, r5, r6}','pop {r1}','bx r1')
    require(word(rom,0x080CED28) == FLAGS, 'supplemental count flag storage differs')


def category(rom, item):
    require(1 <= item <= 375, 'item outside the reviewed item records')
    offset = ITEMS-BASE+32*item
    kind, field = rom[offset+11], rom[offset+8]
    if kind in (3,4):
        return kind-3
    if item <= 252:
        return 2
    if field == 20:
        return 3
    if field in (28,29) or kind == 5:
        return 4
    return 5 if 362 <= item <= 375 else 255


def bounds(rom):
    require(rom[DISPLAY-BASE:DISPLAY-BASE+6] == bytes(range(6)), 'display category mapping differs')
    tables = [[0,*unpack_from('<30H',rom,address-BASE+4)] for address in SUPPLEMENTAL]
    masks = []
    for mask in (16,32,64):
        def marked(item):
            return rom[ITEMS-BASE+32*item+12] & mask
        regular = [item for item in range(1,362) if marked(item)]
        categories = {category(rom,item) for item in regular}
        require(categories <= set(range(5)), 'regular item crosses the normal category range')
        fallback = any(marked(item) for item in range(362,376))
        # The other 251 selector bytes all take the default null-pointer arm.
        # For each table, every inclusive prefix is possible since the counter
        # is the sum of thirty independent predicates in [0,1].
        cases = 0
        for table in [[0]*31,*tables]:
            seen = set(categories)
            special = False
            for item in table:
                if item:
                    n = category(rom,item)
                    require(n < 6, 'supplemental item indexes past six local bytes')
                    seen.add(n)
                    special |= n == 5
                size = len(seen) + int(fallback and not special)
                require(len(seen) <= 6 and size <= 6 and (5 in seen) == special,
                        'fallback would overflow the display entries')
                cases += 1
        masks.append(dict(mask=mask, normal_items=len(regular), normal_categories=sorted(categories),
                          fallback=fallback, selector_class_count_prefixes=cases))
    return dict(local_offsets=list(range(6)), possible_count=[0,30], selectors=256,
                default_selectors=251, total_selector_count_pairs=256*31,
                regular=[1,361], special=[362,375], ranks=masks,
                supplemental=[[i+2,[n for n in table if n]] for i,table in enumerate(tables)])


def owner_frame(ins):
    block(ins,OWNER,'push {r4, r5, r6, r7, lr}','mov r7, sl','mov r6, sb','mov r5, r8',
          'push {r5, r6, r7}','sub sp, #0xc','adds r6, r0, #0','lsls r1, r1, #0x18','lsrs r1, r1, #0x18',
          'str r1, [sp, #8]','ldr r0, [pc, #0x1c]','ldr r1, [pc, #0x20]','adds r0, r0, r1',
          'ldrh r0, [r0]','bl #0x80cc8b4','lsls r0, r0, #0x18','lsrs r0, r0, #0x18','movs r2, #0x10',
          'mov r8, r2','cmp r0, #1','bne #0x806ed7e','movs r3, #0x20','mov r8, r3','b #0x806ed86')
    block(ins,0x0806ED6C,'adds r0, r6, #1','ldrb r1, [r6, #7]','adds r0, r0, r1','movs r1, #5',
          'strb r1, [r0]','ldrb r0, [r6, #7]','adds r0, #1','strb r0, [r6, #7]','b #0x806ee80')
    block(ins,0x0806ED7E,'cmp r0, #1','bls #0x806ed86','movs r2, #0x40','mov r8, r2',
          'movs r0, #0','strb r0, [r6, #7]','mov sl, r0','movs r5, #0','movs r1, #0',
          'mov r3, sp','adds r0, r3, r5','strb r1, [r0]','adds r0, r5, #1','lsls r0, r0, #0x10',
          'lsrs r5, r0, #0x10','cmp r5, #5','bls #0x806ed90',
          'movs r0, #1','mov sb, r0','ldr r7, [pc, #0x34]','movs r5, #1','ldr r4, [pc, #0x34]',
          'lsls r0, r5, #5','adds r0, r0, r4','ldrb r0, [r0, #0xc]','mov r1, r8','ands r0, r1','cmp r0, #0',
          'beq #0x806edca','adds r0, r5, #0','bl #0x80cbd34','lsls r0, r0, #0x18','lsrs r0, r0, #0x18',
          'mov r2, sp','adds r1, r2, r0','movs r0, #1','strb r0, [r1]','adds r0, r5, #1','lsls r0, r0, #0x10',
          'lsrs r5, r0, #0x10','mov r3, sb','adds r0, r7, r3','cmp r5, r0','blt #0x806edaa','movs r5, #0','b #0x806ee20')
    block(ins,0x0806EDE4,'lsls r1, r5, #0x18','lsrs r1, r1, #0x18','ldr r0, [sp, #8]','bl #0x80cc9f0',
          'lsls r0, r0, #0x10','lsrs r4, r0, #0x10','cmp r4, #0','beq #0x806ee1a','adds r0, r4, #0',
          'bl #0x80cbd34','lsls r0, r0, #0x18','lsrs r0, r0, #0x18','cmp r0, #5','bne #0x806ee08',
          'movs r0, #1','mov sl, r0','adds r0, r4, #0','bl #0x80cbd34','lsls r0, r0, #0x18',
          'lsrs r0, r0, #0x18','mov r2, sp','adds r1, r2, r0','movs r0, #1','strb r0, [r1]',
          'adds r0, r5, #1','lsls r0, r0, #0x10','lsrs r5, r0, #0x10','bl #0x80cecf4','lsls r0, r0, #0x18',
          'lsrs r0, r0, #0x18','cmp r5, r0','bls #0x806ede4','movs r5, #0','adds r2, r6, #1',
          'ldr r3, [pc, #0x5c]','mov r1, sp','adds r0, r1, r5','ldrb r0, [r0]','cmp r0, #1','bne #0x806ee4c',
          'ldrb r1, [r6, #7]','adds r1, r2, r1','adds r0, r5, r3','ldrb r0, [r0]','strb r0, [r1]','ldrb r0, [r6, #7]',
          'adds r0, #1','strb r0, [r6, #7]','adds r0, r5, #1','lsls r0, r0, #0x10','lsrs r5, r0, #0x10','cmp r5, #5','bls #0x806ee32')
    block(ins,0x0806EE56,'mov r2, sl','cmp r2, #0','bne #0x806ee80','movs r5, #0xb5','lsls r5, r5, #1',
          'ldr r2, [pc, #0x30]','adds r1, r5, #0','adds r1, #0xe','lsls r0, r5, #5','adds r0, r0, r2',
          'ldrb r0, [r0, #0xc]','mov r3, r8','ands r0, r3','cmp r0, #0','beq #0x806ee76','b #0x806ed6c',
          'adds r0, r5, #1','lsls r0, r0, #0x10','lsrs r5, r0, #0x10','cmp r5, r1','blt #0x806ee66',
          'add sp, #0xc','pop {r3, r4, r5}','mov r8, r3','mov sb, r4','mov sl, r5','pop {r4, r5, r6, r7}','pop {r0}','bx r0')


def prove(data, rom, mapping, index, objects, bindings, ins, calls, refinement, words):
    import match
    require(sha256(rom).hexdigest() == ROM_SHA256 and data == rom[OWNER-BASE:END-BASE] and
            len(ins) == 161 and not words and bindings == BINDINGS and
            calls == {OWNER+off:target for off,target in CALLS.items()}, 'shop category body, CFG or bindings differ')
    entries, rows = indices(mapping,index)
    for address,(end,digest) in PINS.items():
        row = span_record(address,end,entries,rows,rom)
        require(sha256(rom[address-BASE:end-BASE]).hexdigest() == digest and
                (address != OWNER or row['instrs'] == len(ins)) and (address != COUNT or row['instrs'] == 25),
                'shop category ROM span or reachable count differs')
    names = match.parse_data_symbols(objects)
    named = {**OBJECTS, 'g_state_02002CC0':FLAGS, **{f'data_{p:08X}':p for p in SUPPLEMENTAL}}
    require(all(names.get(name) == address for name,address in named.items()), 'shop data mapping differs')
    partition = graph.partition(data,OWNER,refinement,ins,words)
    require(partition['code_bytes'] == 334 and partition['alignment'] == [[0x0806ED62,0x0806ED64]] and
            [(x['address']-OWNER,x['value']) for x in partition['words']] ==
            [(0x34,STATE),(0x38,0x1F6C),(0xAC,361),(0xB0,ITEMS),(0x160,DISPLAY),(0x164,ITEMS)],
            'shop literal words, code or alignment differ')
    require(direct_sites(rom,OWNER) == [CALL_SITE], 'shop direct caller inventory differs')
    ops(rom,0x08069C0A,'ldr r6, [pc, #0xe4]','adds r0, r0, r6','ldr r1, [pc, #0xe4]','movs r2, #0xf',
        'str r2, [sp]','movs r2, #9','str r2, [sp, #4]','movs r2, #2','movs r3, #0','bl #0x806ec20','mov r0, r8','ldr r1, [r0]','adds r0, r1, r6','ldr r2, [pc, #0xd0]',
        'adds r1, r1, r2','ldrb r1, [r1]','bl #0x806ed30')
    require(word(rom,0x08069CF0) == 0x4470 and word(rom,0x08069CF8) == 0x4BFB, 'shop caller field offsets differ')
    ops(rom,RANK,'push {lr}','lsls r0, r0, #0x10','lsrs r0, r0, #0x10','cmp r0, #9','bhi #0x80cc8c2',
        'movs r0, #0','b #0x80cc8cc','cmp r0, #0x13','bls #0x80cc8ca','movs r0, #2','b #0x80cc8cc',
        'movs r0, #1','pop {r1}','bx r1')
    owner_frame(ins)
    classifier(rom)
    supplemental_lookup(rom)
    return dict(schema=buffers.SCHEMA, instructions=len(ins), partition=partition, calls=bindings['calls'],
                runtime_calls=[], caller_sites=[CALL_SITE], local=[-44,-38], selector_spill=[-36,-32],
                saved=[-32,0], buffers=dict(category_bounds=bounds(rom)), environment=environment_fingerprint(),
                conditions=['The display entries and count (argument 0, offsets 1 through 7) are live and '
                            'writable. They may be a designated object in a caller frame, disjoint from '
                            'executing code, the owner and descendant private frames, live saved state '
                            'and return slots. The rank halfword and thirty flag bytes are readable. '
                            'The stack is word-aligned and live. No asynchronous mutation of these objects '
                            'or of the original ROM occurs.'])
