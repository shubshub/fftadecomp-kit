"""Registration, output halfwords and task teardown for the rising particle callback."""
from hashlib import sha256
from struct import pack

from capstone.arm import ARM_REG_SP
from ability_range_local_bytes import block, require
from active_entry_shuffle_profile import compiler_symbol_roles
from known_query_native_closure_profile import environment_fingerprint
import named_data_buffer_profile as buffers
from nested_formal_output_buffer_profile import NestedOutputBufferProof
import owner_graph_profile as graph
from owner_runtime_profile import verify_operations
from positioned_equipment_chance import direct_sites
from scheduler_event_definition import check_payload_argument
import scene_coordinate_conversion as coordinates
from software_double_profile import indices, span_record
from software_float_profile import ROM_SHA256
from unit_equipment_attribute import BASE, ops, word

OWNER, END = 0x0811D73C, 0x0811D8A4
PARENT = 0x0811DA64
ASSET, SEQUENCE = 0x083A6F2C, 0x083A70B4
CALLS = {0x0811D77C:0x080DBDC8, 0x0811D7A2:0x080DFAD0, 0x0811D7BE:coordinates.CONVERT,
         0x0811D7CA:0x08003508, 0x0811D7D4:0x08003558, 0x0811D7DC:0x080DBEB4,
         0x0811D7FC:0x080D6098, 0x0811D80A:0x08147EC8, 0x0811D822:0x080E0608,
         0x0811D830:0x080DFD8C, 0x0811D848:0x080E064C, 0x0811D860:coordinates.CONVERT,
         0x0811D86A:0x08003508, 0x0811D874:0x08003558, 0x0811D87A:0x081484CC, 0x0811D886:0x080D6134}
BINDINGS = dict(calls=[[pc-OWNER,f'func_{target:08X}'] for pc,target in CALLS.items()],
                data=[[0x100,'data_083A6F2C',0],[0x104,'data_083A70B4',0]],functions=[],switches=[])


def check_original(image, bindings, targets):
    expected = {f'func_{target:08X}':(target,False) for target in CALLS.values()}
    expected.update({f'data_{addr:08X}':(addr,True) for addr in (ASSET,SEQUENCE)})
    require(bindings == BINDINGS and targets == expected and
            all(row['size'] == 0 for row in image['symbols'] if row['name'] in targets),
            'rising particle compiler relocation roles differ')
    compiler_symbol_roles(image,targets)


def registration(rom, mapping, index):
    entries, rows = indices(mapping,index)
    def body(a,b):
        span_record(a,b,entries,rows,rom)
        return rom[a-BASE:b-BASE]
    for pointer in (OWNER,OWNER|1):
        found, pos = [], -1
        while (pos := rom.find(pack('<I',pointer),pos+1)) != -1:
            if not pos % 4:
                found.append(BASE+pos)
        require(found == ([0x0811DB78] if pointer & 1 else []),'rising particle registration words differ')
    require(not direct_sites(rom,OWNER),'unexpected direct caller')
    body(PARENT,0x0811DBCC)
    ops(rom,0x0811DB4C,'add r2, sp, #0x38','ldr r0, [r4, #8]','str r0, [r2, #4]',
        'adds r0, r4, #0','adds r0, #0xc','str r0, [r2, #8]','ldr r0, [pc, #0x1c]',
        'movs r1, #0x44','adds r3, r6, #0','bl #0x8005b6c','str r0, [r4, #0x18]')
    ops(rom,0x08005B80,'ldr r0, [r5]','str r3, [sp]','adds r1, r6, #0','adds r2, r4, #0',
        'mov r3, r8','bl #0x8005954')
    require(word(rom,0x08005BA4) == 0x02008FF0,'scheduler manager binding differs')
    ops(rom,0x0800597A,'adds r7, r0, #0','ldr r0, [pc, #0x38]','ldr r2, [r0]',
        'adds r0, r7, #0','adds r1, r4, #0','bl #0x814224c','mov r3, r8','str r3, [r7]')
    ops(rom,0x080059F2,'ldm r0!, {r3, r4, r5}','stm r1!, {r3, r4, r5}',
        'ldm r0!, {r3, r4, r5}','stm r1!, {r3, r4, r5}','ldr r0, [r0]','str r0, [r1]',
        'mov r1, sp','movs r0, #0','strh r0, [r1]','ldr r3, [r7]','adds r0, r7, #0',
        'bl #0x8142250','movs r0, #0x80','lsls r0, r0, #1','strh r0, [r7, #0x14]')
    check_payload_argument(body(0x08005954,0x08005A22),mapping)
    ops(rom,0x08005A5A,'mov r1, sp','ldrh r0, [r4, #0x14]','strh r0, [r1]',
        'mov r1, r8','ldr r0, [r1]','str r4, [r0, #8]','adds r2, r4, #0','adds r2, #0x18',
        'ldr r3, [r4]','adds r0, r4, #0','mov r1, sp','bl #0x8142250','mov r0, sp',
        'ldrh r0, [r0]','strh r0, [r4, #0x14]')
    return dict(parent=PARENT,phase=0x102,site=0x0811DB5E,callback_word=0x0811DB78,
                payload_bytes=68,payload_offset=24,construction_event_bytes=28,
                construction_call=0x08005A08,update_call=0x08005A70,destruction_call=0x080058E0,
                descriptor_object_from_parent=8,descriptor_source_address_in_parent=12)


def child_task(rom):
    # All caller-provided outgoing words are replaced before the spawn call.
    # Only the seven-pointer array inside the 68-byte heap payload is retained.
    ops(rom,0x0811D7E8,'movs r2, #7','str r2, [sp]','adds r2, r6, #0','adds r2, #0x14',
        'str r2, [sp, #4]','ldr r2, [pc, #0x48]','str r2, [sp, #8]','str r5, [sp, #0xc]',
        'movs r2, #0','movs r3, #1','bl #0x80d6098','str r0, [r6, #0x10]')
    ops(rom,0x080D6098,'push {r4, r5, r6, r7, lr}','sub sp, #0x34','ldr r4, [sp, #0x48]',
        'ldr r5, [sp, #0x4c]','ldr r6, [sp, #0x50]')
    ops(rom,0x080D60BC,'mov r0, sp','strh r4, [r0, #6]','str r5, [sp, #0xc]','str r6, [sp, #0x10]')
    ops(rom,0x080D60F6,'add r2, sp, #0x14','mov r0, sp','str r0, [r2, #4]','ldr r0, [pc, #0x10]',
        'movs r1, #0x1c','ldr r3, [sp, #0x54]','bl #0x8005b6c')
    require(word(rom,0x080D6110) == 0x080D4DED,'particle constructor registers another callback')
    ops(rom,0x080D4E2E,'ldrh r0, [r1, #6]','strh r0, [r5, #6]','ldrb r0, [r1, #8]',
        'strb r0, [r5, #0xa]','ldr r0, [r1, #0xc]','str r0, [r5, #0x14]','ldr r0, [r1, #0x10]',
        'str r0, [r5, #0x18]','b #0x80d5116','ldr r0, [r5, #0x14]','ldrh r1, [r5, #6]',
        'bl #0x80d5f74')
    ops(rom,0x080D6134,'push {r4, lr}','adds r4, r0, #0','bl #0x8005bb0','cmp r0, #0',
        'beq #0x80d6144','movs r0, #1','b #0x80d6146','movs r0, #0','cmp r0, #0',
        'bne #0x80d614e','adds r0, r4, #0','b #0x80d6156','adds r0, r4, #0',
        'bl #0x8005b58','movs r0, #0','pop {r4}','pop {r1}','bx r1')
    ops(rom,0x08005B58,'push {lr}','adds r1, r0, #0','ldr r0, [pc, #8]','ldr r0, [r0]','bl #0x80058a4')
    ops(rom,0x080058A4,'push {r4, r5, r6, r7, lr}','sub sp, #0x1c','adds r6, r0, #0','adds r7, r1, #0',
        'mov r1, sp','movs r0, #1','strh r0, [r1]')
    ops(rom,0x080058D6,'adds r2, r4, #0','adds r2, #0x18','ldr r3, [r4]','adds r0, r4, #0',
        'mov r1, sp','bl #0x8142250')
    ops(rom,0x080D5F82,'lsls r0, r5, #2','adds r4, r0, r7','ldr r0, [r4]','cmp r0, #0','beq #0x80d5f94',
        'bl #0x8011428','movs r0, #0','str r0, [r4]','adds r0, r5, #1','lsls r0, r0, #0x10',
        'lsrs r5, r0, #0x10','cmp r5, r6','blo #0x80d5f82')
    ops(rom,0x08005BB2,'movs r1, #0','ldrh r0, [r0, #0x14]','cmp r0, #2',
        'bne #0x8005bbc','movs r1, #1','adds r0, r1, #0')
    require(word(rom,0x080DFDD4) == 0x080DFB0D and word(rom,0x0811D840) == SEQUENCE,
            'sequence asset or callback differs')
    ops(rom,0x0811D826,'ldr r0, [pc, #0x18]','str r5, [sp]','movs r1, #1','movs r2, #4',
        'movs r3, #0','bl #0x80dfd8c','str r0, [r6, #0x40]')
    resources = [word(rom,ASSET+24*i) for i in range(7)]
    require(resources == [0x0850341C]*6+[0x08507F3C], 'seven particle entries differ')
    return dict(spawn=0x0811D7FC, callback=0x080D4DEC, allocation_size=28,outputs_payload=[20,48],
                entries_rom=[ASSET,ASSET+7*24],retained_count=7,poll=0x0811D886,
                terminal_state=2,destructor_event=1,destructor_thunk=0x080058E0,
                finished_particle_callback=0x080D4E40,output_clear_call=0x080D4E44,
                resource_words=resources,sequence=dict(entries=1,asset=SEQUENCE,callback=0x080DFB0C),
                other_descendants_proved=False)


def owner_frame(ins, edges, rom, mapping):
    # All SP readers/writers, including direct outgoing stores; BL pushes no
    # owner stack words. Address-derived reads through R4/R5 are checked below.
    expected = {OWNER,OWNER+2,0x0811D7B6,0x0811D7BA,0x0811D7BC,0x0811D7C2,
                0x0811D7EA,0x0811D7F0,0x0811D7F4,0x0811D7F6,0x0811D828,0x0811D856,
                0x0811D858,0x0811D85C,0x0811D89C,0x0811D89E,0x0811D8A0}
    require({pc for pc,i in ins.items() if ARM_REG_SP in set().union(*i.regs_access())} == expected,
            'unreviewed owner stack operation')
    block(ins,OWNER,'push {r4, r5, r6, r7, lr}','sub sp, #0x18','adds r5, r0, #0',
          'adds r7, r1, #0','adds r6, r2, #0')
    block(ins,0x0811D770,'ldr r0, [r7, #4]','str r0, [r6, #8]','ldr r1, [r7, #8]',
          'str r1, [r6, #0xc]','adds r1, r6, #2','adds r2, r6, #4','bl #0x80dbdc8','b #0x811d89a')
    block(ins,0x0811D79E,'ldr r0, [r6, #0xc]','ldr r0, [r0]','bl #0x80dfad0',
          'lsls r0, r0, #0x18','cmp r0, #0','beq #0x811d89a','ldr r0, [r6, #8]','movs r2, #2',
          'ldrsh r1, [r6, r2]','movs r3, #4','ldrsh r2, [r6, r3]')
    block(ins,0x0811D844,'adds r0, r6, #0','adds r0, #0x34','bl #0x80e064c','ldr r0, [r6, #8]',
          'movs r2, #2','ldrsh r1, [r6, r2]','movs r3, #0x34','ldrsh r2, [r6, r3]')
    block(ins,0x0811D7B6,'mov r4, sp','adds r4, #0x12','str r4, [sp]','add r3, sp, #0x10',
          'bl #0x80dc224','add r0, sp, #0x10','movs r1, #0','ldrsh r0, [r0, r1]',
          'movs r1, #3','bl #0x8003508','movs r2, #0','ldrsh r0, [r4, r2]',
          'movs r1, #3','bl #0x8003558','ldr r0, [r6, #8]','movs r1, #0','bl #0x80dbeb4')
    block(ins,0x0811D856,'add r4, sp, #0x14','mov r5, sp','adds r5, #0x16','str r5, [sp]',
          'adds r3, r4, #0','bl #0x80dc224','movs r1, #0','ldrsh r0, [r4, r1]','movs r1, #3',
          'bl #0x8003508','movs r2, #0','ldrsh r0, [r5, r2]','movs r1, #3','bl #0x8003558',
          'ldr r0, [r6, #0x30]','bl #0x81484cc','str r0, [r6, #0x30]','cmp r0, #0',
          'bne #0x811d89a','ldr r0, [r6, #0x10]','bl #0x80d6134')
    block(ins,0x0811D89A,'movs r0, #0','add sp, #0x18','pop {r4, r5, r6, r7}','pop {r1}','bx r1')
    require([pc for pc,next_pc in edges.items() if not next_pc] == [0x0811D8A2], 'unexpected return')
    # Each straight segment has only its preceding instruction as predecessor.
    for start,end in ((0x0811D7B6,0x0811D834),(0x0811D844,0x0811D880)):
        ordered = [pc for pc in sorted(ins) if start <= pc <= end]
        for before,after in zip(ordered,ordered[1:]):
            require({pc for pc,dst in edges.items() if after in dst} == {before},'side entry to output lifetime')
    # The stale outgoing Y address is live through the BG register stores;
    # on phase 0x102 its slot remains until deallocation. Neither immediate
    # subsequent poll touches any incoming stack argument or materializes SP.
    # Child frames start below callSP. Their explicit heap/callback inputs
    # and the ambient non-interference requirement are recorded separately.
    poll_bodies = ((0x081484CC,0x08148518),(0x080D6134,0x080D615C))
    from owner_admission_profile import refine
    for begin,end in poll_bodies:
        body = rom[begin-BASE:end-BASE]
        audit,_,_,_,_ = graph.graph(body,begin,refine(body,begin,mapping))
        require(all(i.mnemonic in ('push','pop') for i in audit.values()
                    if ARM_REG_SP in set().union(*i.regs_access())), 'poll observed incoming output slot')
    for start in (0x08003508,0x08003558):
        ops(rom,start,'push {lr}','lsls r0, r0, #0x10','lsrs r2, r0, #0x10','adds r3, r2, #0',
            'lsls r1, r1, #0x18','lsrs r1, r1, #0x18')
    require(word(rom,0x08003554) == word(rom,0x080035A4) == 0x03000940,'BG destination differs')
    return dict(frame=[-44,0],outgoing=[-44,-28],saved=[-20,0],
                projected_pairs=[[-28,-26],[-24,-22]],load_width=2,
                first_pair_slot_zero_overwrite=0x0811D7EA,second_pair_slot_zero_expires=0x0811D89C,
                first_bg_stores=[0x03000956,0x03000958],bg_scratch_kills=[0x0800350C,0x0800350E],
                return_value=0,retains_frame_address=False)


def prove(raw, rom, mapping, index, objects, bindings, ins, edges, branches, calls, refinement, words):
    require(sha256(rom).hexdigest() == ROM_SHA256 and raw == rom[OWNER-BASE:END-BASE] and
            not branches and not words and len(ins) == 160 and bindings == BINDINGS and calls == CALLS,
            'rising particle ROM, original bindings or CFG differs')
    entries, rows = indices(mapping,index)
    require(span_record(OWNER,END,entries,rows,rom)['instrs'] == len(ins),'incorrect indexed count')
    partition = graph.partition(raw,OWNER,refinement,ins,words)
    verify_operations(ins,edges,OWNER,branches,calls,refinement)
    require(partition['code_bytes'] == 352 and partition['literal_and_table_bytes'] == 8 and
            partition['alignment_bytes'] == 0,'unexpected code partition')
    nested = NestedOutputBufferProof(rom,mapping,index,objects)._prove()
    block(ins,0x0811D782,'movs r0, #0x19','strh r0, [r6]','ldrh r0, [r7]','adds r0, #1','b #0x811d898')
    block(ins,0x0811D78C,'ldrh r0, [r6]','cmp r0, #0','beq #0x811d79e','subs r0, #1',
          'strh r0, [r6]','lsls r0, r0, #0x10','cmp r0, #0','beq #0x811d79e','b #0x811d89a')
    block(ins,0x0811D810,'adds r0, r6, #0','adds r0, #0x34','movs r3, #4','ldrsh r1, [r6, r3]',
          'ldrh r2, [r6, #4]','subs r2, #0x10','lsls r2, r2, #0x10','asrs r2, r2, #0x10',
          'movs r3, #0x96','bl #0x80e0608')
    return dict(schema=buffers.SCHEMA, instructions=len(ins), partition=partition, calls=bindings['calls'],
                runtime_calls=[],environment=environment_fingerprint(),
                buffers=dict(registration=registration(rom,mapping,index),coordinate=coordinates.verify(rom,mapping,index),
                             phase_zero_projection=nested,output_frame=owner_frame(ins,edges,rom,mapping),particle=child_task(rom)),
                contract=dict(initial_timer=25, interpolation_steps=150, target_delta_mod_65536=65520,
                              coordinate_scalar_range=[-32768,32767],
                              assumptions=['The manager, node, parent, payload, source handle, objects, BG shadow and seven output slots are live, correctly aligned and disjoint from the active frames.',
                                           'The allocator, graphics, palette and sequence services return according to their ARM ABI, use the documented argument storage, and do not access unpassed caller-private memory.',
                                           'The particle task and any descendants form a stable finite tree. Other registered descendants receive a fresh phase-one event and preserve the traversal and all live objects. Arbitrary callback effects and heap ownership are conditional.']))
