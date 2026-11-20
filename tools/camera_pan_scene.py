"""Original secondary-registry camera pan, its four private halfwords, and three scheduled children."""
from hashlib import sha256
from pathlib import Path
import struct

import affine_sequence_task as sequence_task
import match
import named_data_buffer_profile as named
import owner_graph_profile as graph
import plausible
import scene_coordinate_conversion as coordinates
from ability_range_local_bytes import block
from active_entry_shuffle_profile import compiler_symbol_roles
from known_query_native_closure_profile import environment_fingerprint
from scheduler_event_definition import sequence
from sdk_cpuset_halfword import TOKEN, base_header
from software_double_profile import indices, span_record
from software_float_profile import ROM_SHA256
from unit_equipment_attribute import BASE, word

OWNER, END = 0x0811C2E8, 0x0811C50C
REGISTRY, SCHEDULER, RUN = 0x080D3818, 0x08005954, 0x08005A24
WORLD, POSITION, LERP = 0x0801C960, 0x080DBDC8, 0x080E0608
SHADOW, POINTS, EFFECT, SPRITE = 0x03000940, 0x083A6C18, 0x0894DD84, 0x083A6C10
BODY = '2713c6afd540b11a6b09687e991e9c57b58e249e8a1e721614d684ab5b44cdb5'
SOURCE_HASH = '9573b69bd10fd54d9c5130bf3157cacc8f4f4f29732fef0e15fe9521e4d435b2'
CALLS = {78:0x080D35D8, 104:0x080DC1E8, 130:0x080DBA5C, 144:0x08003A74, 152:0x08003A80,
         166:0x080034B8, 172:0x080035A8, 208:WORLD, 228:coordinates.CONVERT, 246:0x08003508,
         256:0x08003558, 266:POSITION, 290:coordinates.CONVERT, 310:LERP, 328:LERP,
         336:sequence_task.CREATE, 354:0x080DFD8C, 410:0x080E064C, 418:0x080E064C, 428:0x08003508,
         438:0x08003558, 444:0x080E0690, 486:0x080D3F08, 498:0x080035A8, 510:0x080D4020, 518:0x080DBEB4}
OBJECTS = {'g_control_flags_03000940':SHADOW, 'data_083A6C18':POINTS, 'data_0894DD84':EFFECT, 'data_083A6C10':SPRITE}
DATA = [[offset,name,0] for offset,name in zip((372,376,380,384,544), (*OBJECTS, 'g_control_flags_03000940'))]
BINDINGS = dict(calls=[[off,f'func_{target:08X}'] for off,target in CALLS.items()], data=DATA, functions=[], switches=[])
ENDS = {
    0x080034B8:0x08003508, 0x08003508:0x08003558, 0x08003558:0x080035A8, 0x080035A8:0x080035D0,
    0x08003A74:0x08003A80, 0x08003A80:0x08003A88, 0x08005954:0x08005A22, 0x08005A24:0x08005AFE,
    0x08005B6C:0x08005BA8, 0x0801C960:0x0801C984, 0x0801C984:0x0801C9F0, 0x080D35D8:0x080D36B0,
    0x080D3818:0x080D3864, 0x080D3CB4:0x080D3E9C, 0x080D3E9C:0x080D3EC0, 0x080D3F08:0x080D3F34,
    0x080D4020:0x080D4038, 0x080DB00C:0x080DB540, 0x080DBA5C:0x080DBA88, 0x080DBDC8:0x080DBDEC,
    0x080DBEB4:0x080DBED4, 0x080DC1E8:0x080DC224, 0x080DC224:0x080DC268, 0x080DFB0C:0x080DFCAC,
    0x080DFD8C:0x080DFDD8, 0x080E0608:0x080E064A, 0x080E064C:0x080E0690, 0x080E0690:0x080E06A4,
    0x0811C2E8:0x0811C50C,
}
require = coordinates.require


def check_source(root):
    path = Path(root)/'src/0811C2E8.c'
    raw = path.read_text()
    reserved = ('func_0811C2E8', 'Point0811C2E8', 'Command0811C2E8', 'State0811C2E8', 'Motion0811C2E8',
                *OBJECTS, *(f'func_{a:08X}' for a in CALLS.values()))
    require(plausible.include_closure(root,path) == ({'src/0811C2E8.c','include/ffta.h','include/control_flags.h'}, [])
            and base_header((Path(root)/'include/ffta.h').read_bytes(),reserved)
            and sha256((Path(root)/'include/control_flags.h').read_bytes()).hexdigest() ==
                'c131fe86127a1e141328bae3b02350dd16464f8e5db196eb65fa13b876613cff'
            and not any(s in raw for s in (chr(92), '??', '%:', chr(0)))
            and sha256(' '.join(TOKEN.findall(plausible.strip_comments_and_strings_keep_strings(raw))).encode()).hexdigest() == SOURCE_HASH,
            'source must provide the original local declarations, four halfwords and callback ABI')


def check_original(image, bindings, targets):
    expected = {f'func_{target:08X}':(target,False) for target in CALLS.values()}
    expected.update({name:(address,True) for name,address in OBJECTS.items()})
    require(bindings == BINDINGS and targets == expected and all(s['size']==0 for s in image['symbols']
            if s['name'] in expected), 'original compile-time call or object relocations differ')
    compiler_symbol_roles(image,targets)


def owner_frame(ins, edges):
    # The private outputs are initialized on the single straight-line section of phase 101.
    # A branch into its middle could otherwise bypass the corresponding store.
    straight = [pc for pc in sorted(ins) if 0x0811C3A0 <= pc <= 0x0811C44A]
    for previous, pc in zip(straight, straight[1:]):
        require({source for source, targets in edges.items() if pc in targets} == {previous} and
                tuple(edges[previous]) == (pc,), 'projection consumer has an alternate entry')
    require([pc for pc in ins if not edges[pc]] == [0x0811C506], 'camera return differs')
    block(ins,OWNER,'push {r4, r5, r6, r7, lr}','mov r7, sb','mov r6, r8','push {r6, r7}',
          'sub sp, #0x14','mov sb, r0','mov r8, r1','adds r7, r2, #0')
    block(ins,0x0811C4F8,'movs r0, #0','add sp, #0x14','pop {r3, r4}','mov r8, r3','mov sb, r4',
          'pop {r4, r5, r6, r7}','pop {r1}','bx r1')
    block(ins,0x0811C3A0,'ldr r0, [pc, #0xbc]','ldrb r1, [r7]','lsls r1, r1, #2','adds r1, r1, r0',
          'movs r2, #0','ldrsh r0, [r1, r2]','movs r3, #2','ldrsh r1, [r1, r3]','mov r4, sp',
          'adds r4, #0xe','add r2, sp, #0xc','adds r3, r4, #0','bl #0x801c960',
          'ldr r0, [r7, #8]','add r1, sp, #0xc','movs r2, #0','ldrsh r1, [r1, r2]',
          'movs r3, #0','ldrsh r2, [r4, r3]','str r4, [sp]','add r3, sp, #0xc','bl #0x80dc224',
          'ldrh r0, [r4]','adds r0, #8','strh r0, [r4]','add r0, sp, #0xc','movs r1, #0',
          'ldrsh r0, [r0, r1]','movs r1, #3','bl #0x8003508','movs r2, #0','ldrsh r0, [r4, r2]',
          'movs r1, #3','bl #0x8003558','ldr r0, [r7, #8]','adds r1, r7, #4','adds r2, r7, #6',
          'bl #0x80dbdc8','ldr r0, [r7, #8]','movs r3, #4','ldrsh r1, [r7, r3]','movs r3, #6',
          'ldrsh r2, [r7, r3]','add r5, sp, #0x10','mov r6, sp','adds r6, #0x12','str r6, [sp]',
          'adds r3, r5, #0','bl #0x80dc224','adds r0, r7, #0','adds r0, #0x10','add r1, sp, #0xc',
          'movs r2, #0','ldrsh r1, [r1, r2]','movs r3, #0','ldrsh r2, [r5, r3]','movs r3, #0x5a',
          'bl #0x80e0608','adds r0, r7, #0','adds r0, #0x1c','movs r2, #0','ldrsh r1, [r4, r2]',
          'movs r3, #0','ldrsh r2, [r6, r3]','movs r3, #0x5a','bl #0x80e0608',
          'ldr r0, [pc, #0x2c]','mov r1, sb','bl #0x80d3e9c','str r0, [r7, #0xc]',
          'ldr r0, [pc, #0x28]','mov r1, sb','str r1, [sp]','movs r1, #1','movs r2, #4','movs r3, #0',
          'bl #0x80dfd8c')
    return dict(entry_relative_sp=-48, local=[-48,-28], saved=[-28,0], outgoing=[-48,-36],
                initialized_at=[[0x0811C3B8,[-36,-34]], [0x0811C3CC,[-36,-34]], [0x0811C40A,[-32,-30]]],
                signed_lerp_inputs=[[-36,-32],[-34,-30]], duration=90, stale_slot_overwritten=0x0811C442)


def ambient_registers(bodies, mapping):
    """Trace private addresses still resident in R4-R6, including calls with no pointer formal."""
    from owner_admission_profile import refine
    scheduled = 0x08005B6C
    expected = {sequence_task.CREATE: {scheduled: [4,5,6]}, 0x080DFD8C: {scheduled: [5,6]},
                scheduled: {SCHEDULER: []}, POSITION: {0x0801C984: []},
                coordinates.CONVERT: {coordinates.OBJECT_KIND: [6]}}
    records = []
    for address in (*expected, WORLD, 0x08003508, 0x08003558, LERP):
        body = bodies[address]
        ins,edges,_,calls,_ = graph.graph(body,address,refine(body,address,mapping))
        pending = [(address,frozenset(range(match.ARM_REG_R0+4,match.ARM_REG_R0+7)))]
        visited, forwarded = set(), {}
        while pending:
            pc,live = pending.pop()
            if (pc,live) in visited:
                continue
            visited.add((pc,live))
            op = ins[pc]
            reads,writes = op.regs_access()
            require(op.mnemonic in ('push','pop') or not live.intersection(reads),
                    f'callee reads an inherited private register at {pc:08X}')
            if pc in calls:
                remaining = sorted(r-match.ARM_REG_R0 for r in live)
                require(forwarded.get(calls[pc],remaining)==remaining, 'ambiguous register origin at nested call')
                forwarded[calls[pc]]=remaining
            # A restored register regains its caller value. The reviewed suffixes make no
            # data use of it; retain all restored R4-R6 as possibly private for that proof.
            after = live.difference(writes)
            if op.mnemonic == 'pop':
                after = after.union(r for r in writes if match.ARM_REG_R0+4<=r<=match.ARM_REG_R0+6)
            pending.extend((target,after) for target in edges[pc])
        require(forwarded==expected.get(address,{}), 'nested ambient coordinate aliases differ')
        records.append([address,[[t,rs] for t,rs in sorted(forwarded.items())]])
    # The only non-scheduler route carrying a pointer is R6 through the selector-one
    # getter. Its complete selected path was decoded by coordinates.verify and never uses R6.
    return records


def registered(rom, bodies):
    body = bodies[REGISTRY]
    sequence(body,REGISTRY,0x080D3822,['add r3, sp, #4','strh r0, [r3, #0x14]','str r1, [sp, #8]',
        'str r2, [sp, #0xc]','str r4, [sp, #0x10]','ldr r1, [pc, #0x24]','ldr r2, [pc, #0x28]',
        'adds r0, r0, r2','lsls r0, r0, #3','adds r0, r0, r1','ldr r1, [r0]','ldrh r2, [r0, #4]',
        'ldr r0, [pc, #0x20]','ldr r0, [r0]','ldr r3, [pc, #0x20]','ldr r3, [r3]','str r3, [sp]',
        'add r3, sp, #4','bl #0x8005954'])
    table, bias = struct.unpack_from('<Ii', body, 60)
    require((table,bias) == (0x08395320,-0x16B) and word(rom,0x08142250)&0xffff == 0x4718,
            'effect registry origin, index bias or scheduler thunk differs')
    require(rom.count(struct.pack('<I',OWNER|1)) == 3, 'camera callback registration inventory differs')
    rows = []
    for kind, point in zip((0x178,0x179,0x17C), ((304,280),(208,280),(176,296))):
        row = table+8*(kind+bias)
        index = (kind-0x78)&255
        require(struct.unpack_from('<IHH',rom,row-BASE) == (OWNER|1,48,0) and
                struct.unpack_from('<hh',rom,POINTS-BASE+index*4) == point,
                'camera callback row, payload or selected table point differs')
        rows.append([kind,row,index,*point])
    sequence(bodies[RUN],RUN,0x08005A66,['adds r2, r4, #0','adds r2, #0x18','ldr r3, [r4]',
             'adds r0, r4, #0','mov r1, sp','bl #0x8142250'])
    return rows


def prove(data, rom, mapping, index, objects, bindings, ins, calls, refinement, words):
    from owner_admission_profile import refine
    require(sha256(rom).hexdigest() == ROM_SHA256 and data == rom[OWNER-BASE:END-BASE] and
            sha256(data).hexdigest() == BODY and len(ins)==228 and not words and
            bindings == BINDINGS and calls == {OWNER+offset:t for offset,t in CALLS.items()},
            'original camera owner, call sites or typed objects differ')
    names = match.parse_data_symbols(objects)
    require(all(names.get(k)==v for k,v in OBJECTS.items()), 'camera object mapping differs')
    conversion = coordinates.verify(rom,mapping,index)
    entries, rows = indices(mapping,index)
    bodies = {}
    pins = []
    # Original US ROM identity above fixes the bodies. The map is independently mutable.
    for address in sorted(ENDS):
        row = next((r for r in entries if int(r['rom'],16)==address),None)
        require(row is not None, 'missing native dependency')
        end = int(row['end'],16)
        require(end == ENDS[address], f'original camera dependency extent differs at {address:08X}')
        span_record(address,end,entries,rows,rom)
        body = rom[address-BASE:end-BASE]
        native = refine(body,address,mapping)
        require(native['cfg_closed'] and native['instrs']==row['instrs'], f'camera dependency graph differs at {address:08X}')
        bodies[address] = body
        pins.append([address,end,native['instrs'],sha256(body).hexdigest()])
    regs = registered(rom,bodies)
    ambient = ambient_registers(bodies,mapping)
    _, edges, _, _, _ = graph.graph(data,OWNER,refinement)
    frame = owner_frame(ins,edges)
    sequence(bodies[WORLD], WORLD, WORLD,['push {r4, r5, lr}','ldr r5, [pc, #0x1c]','ldrh r4, [r5, #0x24]',
        'lsls r0, r0, #0x10','asrs r0, r0, #0x10','subs r0, r0, r4','strh r0, [r2]',
        'ldrh r0, [r5, #0x26]','lsls r1, r1, #0x10','asrs r1, r1, #0x10','subs r1, r1, r0',
        'strh r1, [r3]','pop {r4, r5}','pop {r0}','bx r0'])
    # The remaining callees between each outgoing pointer store and its overwrite never read
    # that entry word. The position helper constructs its own fifth argument in its own frame.
    for a in (0x08003508,0x08003558,LERP):
        operations = graph.graph(bodies[a],a,refine(bodies[a],a,mapping))[0].values()
        require(all('sp' not in i.op_str and i.mnemonic != 'bl' for i in operations), 'stale fifth argument read')
    sequence(bodies[POSITION],POSITION,POSITION,['push {r4, r5, r6, lr}','sub sp, #4','adds r3, r1, #0',
        'movs r1, #8','ldrsh r4, [r0, r1]','movs r5, #0xa','ldrsh r1, [r0, r5]','movs r6, #0xc',
        'ldrsh r5, [r0, r6]','str r2, [sp]','adds r0, r4, #0','adds r2, r5, #0','bl #0x801c984',
        'add sp, #4','pop {r4, r5, r6}','pop {r0}','bx r0'])
    constructor = sequence_task.constructor(bodies[sequence_task.CREATE],mapping)
    for maker,offset,callback in ((0x080DC1E8,52,0x080DB00C),(sequence_task.CREATE,32,0x080D3CB4),
                                  (0x080DFD8C,72,0x080DFB0C)):
        require(struct.unpack_from('<I',bodies[maker],offset)[0] == callback|1,'scheduled child callback literal differs')
    require(word(rom,0x080DC220) == 0x1118,'background payload extent differs')
    sequence(bodies[0x080DFD8C],0x080DFD8C,0x080DFDC0,['ldr r0, [pc, #0x10]','movs r1, #0x10',
        'mov r2, sp','ldr r3, [sp, #0x30]','bl #0x8005b6c'])
    sequence(bodies[0x080DFB0C],0x080DFB0C,0x080DFB46,['ldrh r0, [r1, #4]','strh r0, [r5, #8]',
        'ldr r0, [r1, #8]','str r0, [r5, #0xc]','b #0x80dfc98'])
    sequence(bodies[0x080D3CB4],0x080D3CB4,0x080D3CE4,['ldr r2, [r6, #4]','str r2, [r5]'])
    partition=graph.partition(data,OWNER,refinement,ins,words)
    return dict(schema=named.SCHEMA, instructions=len(ins), partition=partition, calls=bindings['calls'], runtime_calls=[],
                buffers=dict(coordinates=conversion, frame=frame, registry=regs, effect_constructor=constructor,
                        native_dependencies=pins, ambient_calls=ambient, child_callbacks=[[0x080DB00C,0x1118],[0x080D3CB4,44],[0x080DFB0C,16]]),
                environment=environment_fingerprint(), conditions=[
                'Scene tasks, actor and unit, graphics state, and scheduler heaps are live and separate from the private '
                'frames. A completed background task allows the projection phase to start. Ordinary scene calls preserve '
                'the ABI and private frame memory. Installed callbacks execute against valid scene resources.'])
