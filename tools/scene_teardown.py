"""The scene teardown's list snapshot, two installed clears and released allocations."""
from hashlib import sha256
from pathlib import Path
import sys

import function_thunk_profile as thunk
import iwram_installation_prerequisite as install
import known_query_stack_buffer_profile as query
import match
import owner_graph_profile as graph
import plausible
import scheduler_zero_descriptor as boot
from ability_range_local_bytes import block, require
from active_entry_shuffle_profile import compiler_symbol_roles
from positioned_equipment_chance import direct_sites
from sdk_cpuset_halfword import TOKEN, base_header
from software_double_profile import indices, span_record
from software_float_profile import ROM_SHA256
from unit_equipment_attribute import BASE, ops, word

OWNER, END = 0x08096CB8, 0x08096D7C
BODY = 'ddca11aea8dd465fa1fd9be1e08e755177c2b813c72bb60f614104c3d956f231'
SOURCE = '623c5656360d91f8846c2935a2f65528e79a94293ae4765a7dbdbf1544474310'
FLOW = ('scene teardown with a conditional 0..13-node snapshot, one destroy per initialized word, '
        'and two clear sizes derived from the installed initializer and scene allocation paths')
GATHER, DESTROY, THUNK = 0x08099CDC, 0x080995C0, thunk.ALIASES['_call_via_r2']
CALLERS = {0x08024112:(0x08024108,0x080241B4),0x081235F2:(0x081235E4,0x0812366E),
           0x08125568:(0x08125560,0x08125578)}
CALLS = {0x0e:0x0809D458,0x16:0x08096D7C,0x1c:GATHER,0x2a:DESTROY,0x34:0x08096D7C,
         0x38:0x080993F4,0x3c:0x0800718C,0x40:0x0808F77C,0x44:0x0800718C,0x58:THUNK,
         0x5e:0x08022854,0x68:0x08022080,0x70:0x0814913C,0x8a:THUNK,0x90:0x08022854,0x94:0x080BD054}
DATA = {0xac:('data_0200F4A8',0x0200F4A8),0xb0:('g_callbacks_0836D4B8',boot.POINTER),
        0xb4:('data_0200F4AC',0x0200F4AC),0xb8:('data_0200F4B8',0x0200F4B8),0xc0:('data_0200F4B0',0x0200F4B0)}
CALL_NAMES = [[off,'_call_via_r2' if tgt == THUNK else f'func_{tgt:08X}'] for off,tgt in CALLS.items()]
BINDINGS = dict(calls=CALL_NAMES,data=[[off,name,0] for off,(name,_) in DATA.items()],functions=[],switches=[])


def check_source(root):
    path = Path(root)/'src/08096CB8.c'
    source = path.read_text()
    names = ('func_08096CB8','SceneState','SceneContext','SceneChild','BufferInitializer',
             'SceneObject','ListSource',*(name for _,name in CALL_NAMES),*(name for name,_ in DATA.values()))
    require(plausible.include_closure(root,path) == ({'src/08096CB8.c','include/ffta.h'},[]) and
            base_header((Path(root)/'include/ffta.h').read_bytes(),names) and
            not any(marker in source for marker in (chr(92),'??','%:',chr(0))) and
            sha256(' '.join(TOKEN.findall(plausible.strip_comments_and_strings_keep_strings(source))).encode()).hexdigest() == SOURCE,
            'scene teardown requires the reviewed ABI, 13 pointer slots and actual source callbacks')


def check_original(image,bindings,targets):
    expected = {name:(CALLS[off],False) for off,name in CALL_NAMES}
    expected.update({name:(addr,True) for name,addr in DATA.values()})
    require(bindings == BINDINGS and targets == expected and
            not any(row['size'] for row in image['symbols'] if row['name'] in targets),
            'scene teardown original external calls and objects differ')
    compiler_symbol_roles(image,targets)


def owner_operations(ins):
    def check(start,*expected):
        return block(ins,OWNER+start,*expected)
    require(check(0,'push {r4, r5, r6, lr}','mov r6, r8','push {r6}','sub sp, #0x34',
        'ldr r4, [pc, #0xa0]','ldr r0, [r4]','ldr r0, [r0, #0x44]','bl #0x809d458',
        'movs r0, #0','str r0, [r4]','bl #0x8096d7c','mov r1, sp','bl #0x8099cdc',
        'cmp r0, #0','ble #0x8096cec','mov r5, sp','adds r4, r0, #0','ldm r5!, {r0}',
        'bl #0x80995c0','subs r4, #1','cmp r4, #0','bne #0x8096ce0') == OWNER+0x34,
        'scene teardown query and countdown')
    require(check(0x34,'bl #0x8096d7c','bl #0x80993f4','bl #0x800718c','bl #0x808f77c','bl #0x800718c',
        'ldr r0, [pc, #0x64]','mov r8, r0','ldr r4, [pc, #0x64]','ldr r0, [r4]','movs r1, #0x88',
        'lsls r1, r1, #7','mov r3, r8','ldr r2, [r3]','bl #0x814224c','ldr r0, [r4]',
        'bl #0x8022854','ldr r5, [pc, #0x54]','ldr r6, [r5]','movs r0, #0x34','bl #0x8022080',
        'adds r4, r0, #0','movs r0, #1','bl #0x814913c','adds r1, r0, #0','adds r1, r1, r4',
        'ldr r0, [pc, #0x40]','adds r1, r1, r0','movs r0, #0x20','rsbs r0, r0, #0',
        'ands r1, r0','adds r1, #0x20','mov r3, r8','ldr r2, [r3]','adds r0, r6, #0',
        'bl #0x814224c','ldr r0, [r5]','bl #0x8022854','bl #0x80bd054','ldr r1, [pc, #0x24]',
        'movs r0, #0','str r0, [r1]','add sp, #0x34','pop {r3}','mov r8, r3','pop {r4, r5, r6}',
        'pop {r0}','bx r0') == OWNER+0xaa, 'scene teardown clear arguments, releases and return')


def snapshot(count):
    require(type(count) is int and 0 <= count <= query.CAPACITY_WORDS == 13,'scene list exceeds its 13-word premise')
    # r5 starts at SP = entry_SP-72 and advances one word per LDM. The 20 upper bytes are saved registers.
    reads = [-72+4*i for i in range(count)]
    require(all(-72 <= offset < -72+4*count <= -20 for offset in reads),'scene read crosses the initialized prefix')
    return dict(count=count,reads=reads,releases=count)


def spans(rom,mapping,index):
    from owner_admission_profile import refine
    entries,rows = indices(mapping,index)
    require(direct_sites(rom,OWNER) == sorted(CALLERS),'scene teardown incoming BL sites differ')
    callers = []
    for site,(start,end) in CALLERS.items():
        row = span_record(start,end,entries,rows,rom)
        body = rom[start-BASE:end-BASE]
        ref = refine(body,start,mapping)
        require(row['instrs'] == ref['instrs'] and
                {'site':f'0x{site:08X}','target':f'0x{OWNER:08X}'} in ref['calls'],
                'scene teardown reached caller or instruction count differs')
        callers.append(dict(site=site,owner=start,end=end,sha256=sha256(body).hexdigest()))
    dependencies = {}
    for addr in sorted(set(CALLS.values()) | {0x08096BA0,0x08096ED4}):
        entry = next(e for e in entries if int(e['rom'],16) == addr)
        end = int(entry['end'],16)
        row = span_record(addr,end,entries,rows,rom)
        body = rom[addr-BASE:end-BASE]
        require(row['instrs'] == refine(body,addr,mapping)['instrs'],'scene teardown dependency instruction count differs')
        dependencies[f'{addr:08X}'] = dict(end=end,instructions=row['instrs'],sha256=sha256(body).hexdigest())
    return callers,dependencies


def clear_sizes(rom):
    ops(rom,0x08022080,'lsls r1, r0, #3','adds r1, r1, r0','lsls r1, r1, #3','lsls r0, r0, #5',
        'adds r0, r0, r1','movs r1, #0xfa','lsls r1, r1, #2','adds r0, r0, r1','bx lr')
    ops(rom,0x0814913C,'lsls r0, r0, #0x18','lsrs r0, r0, #0x18','ldr r1, [pc, #4]','muls r0, r1, r0','bx lr')
    require(word(rom,0x08149148) == 2442 and word(rom,OWNER+0xbc) == 0x1668,'scene allocation size literals')
    ops(rom,0x08096BAE,'ldr r5, [pc, #0xe8]','movs r4, #0x8a','lsls r4, r4, #7',
        'adds r0, r4, #0','bl #0x8022840','str r0, [r5]')
    ops(rom,0x08096ED6,'movs r0, #0x34','bl #0x8022080','adds r5, r0, #0','movs r0, #1','bl #0x814913c',
        'adds r4, r0, #0','adds r4, r4, r5','ldr r0, [pc, #0x3c]','adds r4, r4, r0','movs r0, #0x20',
        'rsbs r0, r0, #0','ands r4, r0','ldr r5, [pc, #0x38]','movs r0, #0x84','lsls r0, r0, #3',
        'adds r4, r4, r0','adds r0, r4, #0','bl #0x8022840','str r0, [r5]')
    require(word(rom,0x08096C98) == 0x0200F4AC and word(rom,0x08096F28) == 0x1668 and
            word(rom,0x08096F2C) == 0x0200F4B8,'scene setup size and pointer slots')
    context = (0x34*9<<3)+(0x34<<5)+(0xfa<<2)
    base = (context + word(rom,0x08149148) + word(rom,OWNER+0xbc)) & ~31
    result = [(0x0200F4AC,0x88<<7,0x8a<<7),(0x0200F4B8,base+32,base+(0x84<<3))]
    require(all(0 < size <= allocation and size%4 == 0 for _,size,allocation in result),'scene clear escapes allocation')
    return result


def installed_clears(rom,mapping,index,sizes):
    plan = boot.initializer_plan(rom,mapping,index)
    body = bytes.fromhex(plan['source_image']['bytes'])
    # These two original counts exceed the general small-clear executor's bound.
    # On an aligned destination, all iterations use the same single-word STM.
    decoder = match.Cs(match.CS_ARCH_ARM,match.CS_MODE_THUMB)
    base = boot.DESTINATION
    ins = {i.address:i for i in decoder.disasm(body[:50],base)}
    block(ins,base,'push {lr}','adds r2, r0, #0','cmp r1, #0','ble #0x3005ea6','cmp r1, #3',
          'bls #0x3005e9a','movs r0, #3','ands r0, r2','cmp r0, #0','bne #0x3005e9a',
          'movs r0, #0','stm r2!, {r0}','subs r1, #4','cmp r1, #3','bhi #0x3005e8e',
          'cmp r1, #0','ble #0x3005ea6')
    block(ins,base+46,'pop {r0}','bx r0')
    require(sizes == [(0x0200F4AC,0x4400,0x4500),(0x0200F4B8,0x3900,0x3D00)],
            'only the two native scene clear sizes are admitted')
    return dict(image_sha256=plan['source_image']['sha256'],install_site=plan['call_site'],entry=plan['entry'],
        private_save=[-4,0],clears=[dict(slot=slot,bytes=size,requested_allocation=allocation,zero_words=size//4)
                                  for slot,size,allocation in sizes])


def prove(data,address,rom,mapping,index,objects,bindings,ins,calls,refinement):
    import finite_local_word_loop_profile as finite
    require(address == OWNER and len(data) == END-OWNER and sha256(data).hexdigest() == BODY and
            data == rom[OWNER-BASE:END-BASE] and sha256(rom).hexdigest() == ROM_SHA256 and len(ins) == 69,
            'scene teardown requires the complete native owner and USA ROM')
    require(bindings == BINDINGS and calls == {OWNER+site:target for site,target in CALLS.items()},
            'scene teardown requires the exact compiler calls and pool relocs')
    locations = match.parse_data_symbols(objects)
    require(all(locations.get(name) == addr and word(rom,OWNER+off) == addr for off,(name,addr) in DATA.items()),
            'scene teardown has a stale named address')
    part = graph.partition(data,address,refinement,ins,{})
    require(part['alignment'] == [[OWNER+0xaa,OWNER+0xac]] and
            {w['address'] for w in part['words']} == {OWNER+off for off in (*DATA,0xbc)},
            'scene teardown literal pool or padding differs')
    owner_operations(ins)
    callers,dependencies = spans(rom,mapping,index)
    return dict(schema=finite.SCHEMA,instructions=len(ins),calls=CALL_NAMES,runtime_calls=[],partition=part,
        thunk_dependencies=thunk.dependencies(['_call_via_r2'],rom),known_query=query.contract(rom,mapping,index),
        finite_local_words=dict(frame=[-72,-20],saved=[-20,0],query=OWNER+0x1c,element_release=OWNER+0x2a,
                                counts=[snapshot(n) for n in range(14)]),
        clear=installed_clears(rom,mapping,index,clear_sizes(rom)),caller_sites=callers,dependencies=dependencies,
        list_bound_proved_from_ROM=False,termination_proved=False,
        premises=[*query.EXPLICIT_CONDITIONS,
            'This teardown is entered with an initialized live scene, valid state and child pointers, and the two '
            'live word-aligned allocations from the observed setup sites. Their pointer slots remain valid until '
            'the corresponding release. Both buffers, code, query results, active stack frames and installed image '
            'are separate, with no asynchronous writer. Every snapshotted object remains individually releasable '
            'in list order. Each ordinary call obeys its documented returning ABI; its source arguments fit in '
            'registers. The boot-installed clear image remains intact throughout both calls.'],
        producer_sha256={Path(m.__file__).name:sha256(Path(m.__file__).read_bytes()).hexdigest()
                         for m in (sys.modules[__name__],finite,query,match,graph,thunk,boot,install)})
