"""Conditional 13-entry scene query, two selected record pointers, and four history words."""
from hashlib import sha256
from pathlib import Path
import struct
import sys

from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB

import function_thunk_profile as thunk
import installed_zero_effects as zero
import iwram_installation_prerequisite as install
import known_query_stack_buffer_profile as query
import owner_graph_profile as graph
import scheduler_zero_descriptor as boot
from software_double_profile import indices, span_record

BASE = 0x08000000
OWNER, END = 0x080C68EC, 0x080C69C8
QUERY, PREDICATE, MEMBERSHIP = 0x08099CDC, 0x08133BC4, 0x08131BB8
SCENE = 0x02000080
CALLS = [[20,'_call_via_r2'],[30,'func_08099CDC'],[52,'func_08133BC4']]
DATA = [[216,'g_callbacks_0836D4B8',0]]
BODY = '7c9788a87bba6fae4251b264f669ea410a82f5f02ddeb72d8785cdd0cbcad05d'


def require(condition, detail):
    if not condition:
        raise ValueError('scene record history: ' + detail)


def assembly(rom, start, end, expected):
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    instructions = list(decoder.disasm(rom[start-BASE:end-BASE],start))
    require(sum(i.size for i in instructions) == end-start and
            [i.mnemonic+' '+i.op_str for i in instructions] == expected,
            f'original operations at {start:08X}')


def membership(rom, mapping, index):
    import owner_admission_profile as owner
    entries, rows = indices(mapping,index)
    for start, end, count in ((0x080C7554,0x080C755E,4),(PREDICATE,PREDICATE+14,6),
                              (MEMBERSHIP,0x08131BDE,16)):
        row = span_record(start,end,entries,rows,rom)
        data = rom[start-BASE:end-BASE]
        refinement = owner.refine(data,start,mapping)
        ins,_,local,_,words = graph.graph(data,start,refinement)
        require(len(ins) == row['instrs'] == count and not local and not words, 'related complete CFG')
        graph.partition(data,start,refinement,ins,words)
    assembly(rom,0x080BA5EC,0x080BA600,[
        'adds r0, r6, #0','adds r0, #0xb8','ldr r1, [r6]','bl #0x80c7554',
        'movs r0, #0x99','lsls r0, r0, #2','adds r1, r6, r0','movs r0, #0x22','strh r0, [r1]'])
    assembly(rom,0x080C7554,0x080C755E,['push {lr}','bl #0x80c68ec','pop {r0}','bx r0'])
    assembly(rom,PREDICATE,PREDICATE+14,['push {lr}','bl #0x8131bb8','lsls r0, r0, #0x18',
        'lsrs r0, r0, #0x18','pop {r1}','bx r1'])
    assembly(rom,MEMBERSHIP,0x08131BCA,['push {lr}','movs r2, #0','ldr r1, [pc, #0xc]',
        'movs r3, #0x84','lsls r3, r3, #1','cmp r1, r0','bne #0x8131bd0','movs r0, #1','b #0x8131bda'])
    require(rom[0x131bca:0x131bd0] == bytes(2)+struct.pack('<I',SCENE), 'scene literal or padding')
    assembly(rom,0x08131BD0,0x08131BDE,['adds r1, r1, r3','adds r2, #1','cmp r2, #0x17',
        'ble #0x8131bc2','movs r0, #0','pop {r1}','bx r1'])


def installed_clear(rom, mapping, index):
    for start,end,digest in boot.BOOT:
        require(sha256(rom[start-BASE:end-BASE]).hexdigest() == digest, 'boot installer route')
    plan = install.verify(rom[0x2768:0x27b8],0x08002768,rom,mapping,index,selector=install.SELECTOR,
                          call_site=0x08002796,pointer_address=boot.POINTER)
    require(plan['arguments'] == dict(source=boot.IMAGE,destination=boot.DESTINATION,control=88) and
            plan['copy_plan']['bytes'] == 176 and plan['copy_plan']['width'] == 2 and
            plan['entry']['pointer_word'] == boot.DESTINATION|1 and
            plan['source_image']['sha256'] == boot.IMAGE_SHA256, 'installed clearer or callback slot')
    image = bytes.fromhex(plan['source_image']['bytes'])
    effect = zero.verify_conditional(image,boot.DESTINATION,boot.DESTINATION,196,selector=zero.SELECTOR)
    case = effect['cases'][0]
    writes = [('destination',offset,4) for offset in range(0,196,4)]
    require(case['alignment'] == 0 and case['reads'] == [('stack',-4,4)] and
            case['writes'] == [('stack',-4,4)]+writes and case['SP_restored'] and case['protected_return'],
            '196-byte clear or private return save')
    return dict(install_site=plan['call_site'],pointer_word=boot.POINTER,entry=plan['entry'],
                size=196,aligned_zero_words=len(writes),image_sha256=effect['image_sha256'])


def selection(count):
    """Both predicate outcomes at every inspected initialized slot, stopping after two successes."""
    require(type(count) is int and 0 <= count <= query.CAPACITY_WORDS, 'query count outside 13-word frame')
    states = {(0,0)}
    reads, slots, exits = set(), set(), set()
    while states:
        index, kept = states.pop()
        if index == count or kept == 2:
            exits.add((index,kept))
            continue
        offset = -76+4*index
        require(-76 <= offset < -76+4*count <= -24, 'query word reaches an uninitialized or saved slot')
        reads.add(offset)
        slots.add(100+4*kept)
        states.update(((index+1,kept),(index+1,kept+1)))
    return dict(count=count,read_offsets=sorted(reads),record_offsets=sorted(slots),exits=sorted(exits))


def owner_accesses(rom):
    assembly(rom,OWNER,0x080C691C,['push {r4, r5, r6, r7, lr}','mov r7, r8','push {r7}',
        'sub sp, #0x34','adds r6, r0, #0','adds r4, r1, #0','ldr r0, [pc, #0xc8]','ldr r2, [r0]',
        'adds r0, r6, #0','movs r1, #0xc4','bl #0x814224c','str r4, [r6, #0x60]',
        'adds r0, r4, #0','mov r1, sp','bl #0x8099cdc','mov r8, r0','movs r7, #0','cmp r7, r8',
        'bge #0x80c6950','adds r5, r6, #0','adds r5, #0x79','mov r4, sp'])
    assembly(rom,0x080C691C,0x080C6950,['ldr r0, [r4]','ldr r0, [r0]','bl #0x8133bc4',
        'lsls r0, r0, #0x18','cmp r0, #0','beq #0x80c6948','ldrb r0, [r5]','lsls r0, r0, #2',
        'adds r1, r6, #0','adds r1, #0x64','adds r1, r1, r0','ldr r0, [r4]','ldr r0, [r0]',
        'str r0, [r1]','ldrb r0, [r5]','adds r0, #1','strb r0, [r5]','lsls r0, r0, #0x18',
        'lsrs r0, r0, #0x18','cmp r0, #1','bhi #0x80c6950','adds r4, #4','adds r7, #1',
        'cmp r7, r8','blt #0x80c691c'])
    assembly(rom,0x080C6950,0x080C6976,['adds r2, r6, #0','adds r2, #0x7c','movs r4, #0',
        'movs r0, #0x12','strh r0, [r2]','movs r0, #0x7e','adds r0, r0, r6','mov ip, r0',
        'ldrh r0, [r0]','adds r1, r0, #1','mov r3, ip','strh r1, [r3]','lsls r0, r0, #0x10',
        'lsrs r0, r0, #0xf','adds r3, r6, #0','adds r3, #0x80','adds r0, r3, r0','ldrh r1, [r2]','strh r1, [r0]'])
    def push(value,form_depth_pointer=False,end=False):
        return [f'movs r0, #{value}','strh r0, [r2]'] + (['mov r5, ip'] if form_depth_pointer else []) + [
            'ldrh r0, [r5]','adds r1, r0, #1','strh r1, [r5]','lsls r0, r0, #0x10','lsrs r0, r0, #0xf'
        ] + (['adds r3, r3, r0','ldrh r0, [r2]','strh r0, [r3]'] if end else
             ['adds r0, r3, r0','ldrh r1, [r2]','strh r1, [r0]'])
    assembly(rom,0x080C6976,0x080C69B6,push(5,True)+push(8)+push(2,end=True)+['strh r4, [r2]'])
    assembly(rom,0x080C69B6,0x080C69C2,['add sp, #0x34','pop {r3}','mov r8, r3',
        'pop {r4, r5, r6, r7}','pop {r0}','bx r0'])


def prove(data,address,rom,mapping,index,objects,bindings,ins,calls,refinement):
    import finite_local_word_loop_profile as finite
    import match
    require(address == OWNER and len(data) == END-OWNER and sha256(data).hexdigest() == BODY and
            data == rom[OWNER-BASE:END-BASE] and len(ins) == 104, 'complete 220-byte native owner')
    require(bindings == dict(calls=CALLS,data=DATA,functions=[],switches=[]) and
            calls == {OWNER+20:thunk.ALIASES['_call_via_r2'],OWNER+30:QUERY,OWNER+52:PREDICATE},
            'original relocations or call destinations')
    require(match.parse_data_symbols(objects).get('g_callbacks_0836D4B8') == boot.POINTER, 'named clearer slot')
    partition = graph.partition(data,address,refinement,ins,{})
    require(partition['words'] == [dict(address=OWNER+216,value=boot.POINTER,load_sites=[OWNER+12],switch_word=False)]
            and partition['alignment'] == [[OWNER+214,OWNER+216]], 'clearer pool and alignment')
    membership(rom,mapping,index)
    owner_accesses(rom)
    return dict(schema=finite.SCHEMA,instructions=len(ins),calls=CALLS,runtime_calls=[],partition=partition,
        thunk_dependencies=thunk.dependencies(['_call_via_r2'],rom),known_query=query.contract(rom,mapping,index),
        initializer=installed_clear(rom,mapping,index),finite_local_words=dict(
            frame=[-76,-24],callee_saves=[-24,0],query_stack_below=44,accepted_counts=[0,13],
            selection=[selection(n) for n in range(14)],predicate_stack_below=8,
            first_scene_record=SCENE,scene_record_count=24,record_bytes=264,
            original_caller=0x080C7556,outer_call=0x080BA5F2,
            dereferenced_local_sites=[0x080C691C,0x080C6934],loaded_object_sites=[0x080C691E,0x080C6936],
            source_offset=96,selected_word_offsets=[100,104],selected_count_offset=121,
            current_offset=124,depth_offset=126,history_offsets=[128,130,132,134],history_values=[18,5,8,2],
            final_depth=4,final_current=0),
        list_bound_proved_from_ROM=False, premises=[*query.EXPLICIT_CONDITIONS,
            'The 196-byte aligned state is ordinary live writable RAM, separate from the source list owner, list nodes, '
            'value objects, executing code, installed IWRAM image and all active stack frames. Each visited list item '
            'holds a readable aligned record pointer at offset zero. Duplicate records or value objects are allowed.',
            'The installed image and callback table remain intact after boot. The stack is aligned, has space for '
            'all nested saves, and no asynchronous writer changes code, list links, record pointers or the state. '
            'Testing membership compares address values only. The two retained pointers refer to primary scene '
            'records, independently of the expired list-result buffer. Global game-state reachability and '
            'allocation are premises.'],
        producer_sha256={Path(module.__file__).name:sha256(Path(module.__file__).read_bytes()).hexdigest()
                         for module in (sys.modules[__name__],finite,query,install,zero,boot,thunk,graph)})
