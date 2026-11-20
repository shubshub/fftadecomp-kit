"""The USA item menu's private three-entry list, name tables and character-tile rows."""
from collections import Counter
from hashlib import sha256
from pathlib import Path
import struct

from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
from capstone.arm import ARM_INS_B

import installed_zero_effects as zero
import iwram_installation_prerequisite as install
import match
import menu_roster_filter as heap
import named_data_buffer_profile as named
import owner_graph_profile as graph
import scheduler_zero_descriptor as boot
from ability_range_local_bytes import block, require
from known_query_native_closure_profile import environment_fingerprint
from scene_record_history import assembly
from sdk_cpuset_halfword import TOKEN, base_header
from software_double_profile import indices, span_record
from software_float_profile import ROM_SHA256

BASE = match.ROM_BASE
OWNER, COLLECT, DRAW = 0x0806FABC, 0x080C8D14, 0x0806FFAC
ITEMS, GRANTS, GRANTS_END = 0x0851D180, 0x08520080, 0x08521214
JOBS, JOBS_END, ROWS, ROWS_END = 0x08521A14, 0x085231A4, 0x0851BA84, 0x0851D0F4
ITEM_NAMES, ITEM_NAMES_END = 0x08526680, 0x08527244
ABILITY_NAMES, ABILITY_NAMES_END = 0x085567F0, 0x085573F4
SCENE, GRAPHICS = 0x0200F428, 0x030008B0
SELECTOR = named.GUARDED_SWITCH_SELECTOR
# Both indices must agree. The full USA digest is checked independently.
SPANS = ((OWNER,0x0806FB50,64),(COLLECT,0x080C8EBC,161),(DRAW,0x0806FFE4,23),
         (0x0806F7B8,0x0806F8DC,131),(0x0806F8DC,0x0806F992,67),
         (0x080CA7A4,0x080CA8FE,126),(0x080CD480,0x080CD498,9),
         (0x08013A88,0x08013AAA,16),(0x08141868,0x0814186C,2),
         (0x08068AE0,0x08068C10,102),(0x08017424,0x0801748E,53),
         (0x08017528,0x080175E0,87),(0x0814224C,0x0814224E,1))


def bindings():
    return dict(calls=[[44,'func_0806FFAC'],[58,'func_080C8D14'],[108,'func_0806FFAC']],
                data=[[136,'g_table_08526680',0],[140,'g_table_0851D180',0],[144,'g_table_085567F0',0]],
                functions=[], switches=[])


def check_source(root):
    import plausible
    source = (Path(root)/'src/0806FABC.c').read_text()
    header = (Path(root)/'include/ffta.h').read_bytes()
    require(base_header(header, ('func_0806FABC','func_0806FFAC','func_080C8D14',
                                'g_table_08526680','g_table_0851D180','g_table_085567F0')) and
            not any(mark in source for mark in (chr(92),'??','%:',chr(0))), 'unexpected menu preprocessing')
    tokens = ' '.join(TOKEN.findall(plausible.strip_comments_and_strings_keep_strings(source)))
    prefix, separator, body = tokens.partition('GrantedAbilities list ;')
    require(separator and '#' not in body and sha256((prefix+separator).encode()).hexdigest() ==
            '6b58c2a2f543ee415a96bba25faae8f9e6f5808153531cb48471aac0c4235b51',
            'changed list, item or menu declarations')


def words(rom, address, count=1):
    return struct.unpack_from(f'<{count}I', rom, address-BASE)


def name(rom, table, end, index):
    require(table+4*(index+1) <= end, 'name index exceeds the physical pointer table')
    pointer, = words(rom, table+4*index)
    require(BASE <= pointer < BASE+len(rom), 'invalid name string pointer')
    return pointer


def item_rows(rom, item, row_starts):
    """Return the item name, optional 28-byte output and ordered ability names."""
    require(type(item) is int and 0 <= item < (GRANTS-ITEMS)//32, 'item outside the physical records')
    record = ITEMS-BASE+32*item
    id_, = struct.unpack_from('<H',rom,record)
    item_name = name(rom,ITEM_NAMES,ITEM_NAMES_END,id_)
    if rom[record+8] == 0x1B:
        return item_name, None, ()
    grant = GRANTS+20*rom[record+29]
    require(grant+20 <= GRANTS_END, 'selector 18 exceeds grant records')
    count = rom[grant-BASE]
    require(count <= 9, 'grant count exceeds the nine pairs')
    names = []
    result = bytearray(28)
    i = 0
    while i < count:
        at = grant-BASE+2+i*2
        job, ability = rom[at:at+2]
        require(JOBS+(job+1)*52 <= JOBS_END, 'job outside the record table')
        row = rom[JOBS-BASE+job*52+4]
        require(row+1 < len(row_starts) and row_starts[row]+8*(ability+1) <= row_starts[row+1],
                'ability lookup exceeds its own physical row')
        id_, = struct.unpack_from('<H',rom,row_starts[row]-BASE+ability*8)
        width = 1
        if count > 1:
            if job in (5,9,11,22):
                width = 2
            elif job in (7,8):
                width = 3
        require(i+width <= count and len(names) < 3, 'group exceeds its source or private output')
        entry = 4+8*len(names)
        struct.pack_into('<HH',result,entry,id_,width)
        result[entry+4:entry+4+width] = rom[at:at+2*width:2]
        names.append(name(rom,ABILITY_NAMES,ABILITY_NAMES_END,id_))
        i += width
    struct.pack_into('<H',result,0,len(names))
    return item_name, bytes(result), tuple(names)


def table_bounds(rom, objects):
    required = dict(g_table_0851D180=ITEMS,g_table_08520080=GRANTS,g_table_08521214=GRANTS_END,
                    g_table_08521A14=JOBS,data_085231A4=JOBS_END,g_table_0851BA84=ROWS,data_0851D0F4=ROWS_END,
                    g_table_08526680=ITEM_NAMES,data_08526CD8=0x08526CD8,data_08527244=ITEM_NAMES_END,
                    g_table_085567F0=ABILITY_NAMES,g_table_085573F4=ABILITY_NAMES_END,
                    data_0200F428=SCENE,data_030008B0=GRAPHICS,g_callbacks_0836D4B8=boot.POINTER)
    symbols = match.parse_data_symbols(objects)
    require(all(symbols.get(k) == v for k,v in required.items()), 'changed named item-menu table or scene')
    starts = (*words(rom,ROWS,24), ROWS_END)
    require(starts[0] == ROWS+24*4 and all(hi > lo and (hi-lo)%8 == 0 for lo,hi in zip(starts,starts[1:])),
            'invalid physical category rows')
    histogram = Counter()
    serialized = sha256()
    for item in range((GRANTS-ITEMS)//32):
        item_name, out, names = item_rows(rom,item,starts)
        histogram['bypass' if out is None else str(len(names))] += 1
        serialized.update(struct.pack('<HB',item,len(names))+struct.pack('<I',item_name))
        serialized.update(out or b'')
        serialized.update(struct.pack(f'<{len(names)}I',*names))
    require(histogram == {'bypass':10,'0':150,'1':96,'2':82,'3':38}, 'original grant grouping differs')
    return dict(items=376,grant_records=225,pairs_per_record=9,groups=dict(histogram),
                ordered_outputs_sha256=serialized.hexdigest(),widths=[(b-a)//8 for a,b in zip(starts,starts[1:])],
                item_names='All 376 original item halfwords index readable pointers. The named interior '
                           'word 08526CD8 is item-name slot 406; higher item IDs reach beyond it.',
                selected_domain='Physical item IDs 0 through 375. This inventory does not assert all IDs appear in a scene.')


def collector_cfg(rom):
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    decoder.detail = True
    guard = 0x080C8DD6
    dispatch = 0x080C8DE2
    default = 0x080C8E8C
    table, = words(rom,0x080C8DE8)
    targets = words(rom,table,18)
    require(table == 0x080C8DEC and targets == tuple(0x080C8E34 if job in (5,9,11,22) else
            0x080C8E60 if job in (7,8) else default for job in range(5,23)), 'changed grouping switch')
    pending, seen, calls, returns = [COLLECT], {}, {}, []
    while pending:
        site = pending.pop()
        if site in seen:
            continue
        require(COLLECT <= site < 0x080C8EBC and not site%2, 'collector branch outside its owner')
        op = next(decoder.disasm(rom[site-BASE:site-BASE+4],site,count=1))
        seen[site] = op
        if site == dispatch:
            pending.extend(targets)
        elif op.mnemonic == 'bx':
            require(site == 0x080C8EBA and op.op_str == 'r1', 'unexpected collector return')
            returns.append(site)
        elif op.mnemonic == 'bl':
            calls[site] = op.operands[0].imm
            pending.append(site+4)
        elif op.id == ARM_INS_B:
            pending.append(op.operands[0].imm)
            if op.mnemonic != 'b':
                pending.append(site+op.size)
        else:
            require('pc' not in op.op_str.split(',')[0], 'unexpected indirect transfer in collector')
            pending.append(site+op.size)
    require(len(seen) == 161 and len(returns) == 1 and calls == {
        0x080C8D2E:0x0814224C,0x080C8D36:0x080CA7A4,0x080C8D6E:0x080CD480,0x080C8DBA:0x080CD480},
        'collector inventory or callees differ')
    block(seen,guard,'cmp r0, #0x11','bhi #0x80c8e8c','lsls r0, r0, #2','ldr r1, [pc, #8]',
          'adds r0, r0, r1','ldr r0, [r0]','mov pc, r0')
    block(seen,0x080C8D26,'ldr r0, [pc, #0x28]','ldr r2, [r0]','adds r0, r7, #0','movs r1, #0x1c',
          'bl #0x814224c','adds r0, r4, #0','movs r1, #0x12','bl #0x80ca7a4')
    require(words(rom,0x080C8D50)[0] == boot.POINTER and words(rom,0x080CA814)[0] == 0x080CA8F2,
            'collector initializer or selector 18 differs')
    return dict(instructions=len(seen),guard=guard,dispatch=dispatch,table=table,targets=list(targets),
                default=default,return_at=returns[0],calls=sorted(calls.items()))


def installed_list_clear(rom,mapping,index):
    plan = install.verify(rom[0x2768:0x27B8],0x08002768,rom,mapping,index,selector=install.SELECTOR,
                          call_site=0x08002796,pointer_address=boot.POINTER)
    payload = bytes.fromhex(plan['source_image']['bytes'])
    require(plan['arguments'] == dict(source=boot.IMAGE,destination=boot.DESTINATION,control=88)
            and plan['entry']['address'] == boot.DESTINATION and plan['source_image']['sha256'] == boot.IMAGE_SHA256,
            'changed installed clear')
    case = zero.verify_conditional(payload,boot.DESTINATION,boot.DESTINATION,28,selector=zero.SELECTOR)['cases'][0]
    require(case['alignment'] == 0 and case['reads'] == [('stack',-4,4)] and
            case['writes'] == [('stack',-4,4)]+[('destination',i,4) for i in range(0,28,4)]
            and case['SP_restored'] and case['protected_return'], 'changed seven-word local clear')
    return dict(installation=plan['arguments'],entry=plan['entry'],aligned_zero_words=7)


def prove(data,rom,mapping,index,objects,original,ins,calls,refinement,switches):
    require(sha256(rom).hexdigest() == ROM_SHA256 and data == rom[0x6FABC:0x6FB50] and len(ins) == 64 and
            not switches and bindings() == original and calls == {OWNER+44:DRAW,OWNER+58:COLLECT,OWNER+108:DRAW},
            'original USA menu bytes or compiler roles differ')
    entries,rows = indices(mapping,index)
    for start,end,count in SPANS:
        require(span_record(start,end,entries,rows,rom)['instrs'] == count,
                f'original item-menu instruction count at {start:08X} differs')
    for start,end,digest in heap.heap_providers():
        span_record(start,end,entries,rows,rom)
        require(sha256(rom[start-BASE:end-BASE]).hexdigest() == digest, 'changed scene heap provider')
    block(ins,0x0806FAEC,'ldrb r0, [r4, #8]','cmp r0, #0x1b','beq #0x806fb34','adds r0, r5, #0',
          'mov r1, sp','bl #0x80c8d14','lsls r0, r0, #0x18','lsrs r5, r0, #0x18')
    block(ins,0x0806FB08,'lsls r0, r4, #3','add r0, sp, r0','ldrh r0, [r0, #4]','lsls r0, r0, #2',
          'add r0, r8','ldr r1, [r0]','adds r4, #1','mov r2, sb','lsls r0, r2, #1','adds r2, r4, #0',
          'muls r2, r0, r2','ldrh r0, [r7]','adds r2, r2, r0','lsls r2, r2, #0x10','lsrs r2, r2, #0x10')
    require(words(rom,0x08068B58,3) == (SCENE,0x9C08,boot.POINTER) and
            words(rom,0x0806F8D4,2) == words(rom,0x0806F968,2) == (SCENE,0x1A88) and
            words(rom,0x0806A608,4) == (0x1A88,GRAPHICS,0x0600B000,0x39F4) and
            words(rom,0x0806B21C,3) == (0x4C06,0x1A88,0x44EC), 'changed scene/consumer geometry')
    assembly(rom,0x0806F930,0x0806F940,[
        'strh r2, [r6, #6]','ldr r5, [pc, #0x34]','ldr r0, [r5]','ldr r4, [pc, #0x34]',
        'adds r0, r0, r4','ldrh r1, [r6, #6]','bl #0x806fabc'])
    assembly(rom,0x0806FFC0,0x0806FFD6,[
        'movs r1, #0x18','bl #0x8013a88','ldr r0, [r5, #0x7c]','movs r1, #1','str r1, [sp]',
        'adds r1, r4, #0','adds r2, r6, #0','movs r3, #5','bl #0x8015110'])
    assembly(rom,0x08068B00,0x08068B16,[
        'ldr r5, [pc, #0x54]','ldr r4, [pc, #0x58]','adds r0, r4, #0','bl #0x8022840',
        'str r0, [r5]','ldr r1, [pc, #0x50]','ldr r2, [r1]','adds r1, r4, #0','bl #0x814224c'])
    assembly(rom,0x08068BE4,0x08068BF4,[
        'ldr r4, [pc, #0x24]','ldr r0, [r4]','cmp r0, #0','beq #0x8068bf4',
        'bl #0x8022854','movs r0, #0','str r0, [r4]'])
    return dict(schema=named.GUARDED_SWITCH_SCHEMA,instructions=len(ins),calls=original['calls'],runtime_calls=[],
                partition=graph.partition(data,OWNER,refinement,ins,switches),
                collector=collector_cfg(rom),initializer=installed_list_clear(rom,mapping,index),
                physical_tables=table_bounds(rom,objects),
                frame=dict(bytes=28,records=3,stride=8,first_name=4,non_escaping=True),
                scene=dict(slot=SCENE,allocation=[0x08068B06,0x9C08],release=0x08068BEC,menu_offset=0x1A88,
                           constructors=[0x0806A5F4,0x0806C65C],updates=[0x0806B1EC,0x0806D278],
                           owner_calls=[0x0806F896,0x0806F93C],active_item_offset=0x44EC,context_offset=0x39F4),
                drawing=dict(first_destination=0x0600B000,width=13,step_tiles=26,clear_bytes=768,
                             clear=[DRAW,0x08013A88,0x08141868],text=[0x08015110,5,1],
                             condition='Original initialized scene, successful live allocation through release, '
                             'intact installed image, aligned graphics surface, live font state and accessible '
                             'encoded names. The item row and up to three ability rows are 26 tiles apart; each '
                             'clear covers 24 tiles. The u16 tile expression may wrap for arbitrary callers. '
                             'Renderer effects and normal return depend on its own text, font and surface inputs.'),
                environment=environment_fingerprint())
