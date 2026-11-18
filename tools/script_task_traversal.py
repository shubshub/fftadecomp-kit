"""Scheduler passes over the script fade tasks installed by command 08122C28."""
from hashlib import sha256
from pathlib import Path
import struct

import match
import owner_graph_profile as graph
from ability_range_local_bytes import block, require
from sdk_cpuset_halfword import TOKEN, base_header
from software_double_profile import indices, span_record

SELECTOR = 'conditional-script-task-traversal-v1'
SCHEMA = 'elf-symbol-thumb-' + SELECTOR
CONTROL_FLOW = ('complete scheduler frame traversal with a reviewed script fade registration, callback and '
                'subtree release; other registered callbacks require their own returning and lifetime contracts')
OWNER, END = 0x08005A24, 0x08005AFE
SLOT, SLOT_NAME = 0x02008FF0, 'data_02008FF0'
CALLBACK, COMMAND, PUMP = 0x08126B9C, 0x08122C28, 0x08121908
BINDINGS = dict(calls=[[0x4C,'_call_via_r3'],[0x90,'func_080058A4']],
                data=[[0x84,SLOT_NAME,0]], functions=[], switches=[])
TARGETS = {'_call_via_r3': (0x08142250, False), 'func_080058A4': (0x080058A4, False),
           SLOT_NAME: (SLOT, True)}
TOKENS = 'aa75aa0e9a8c568a7c04b267fc975e1639a922c804c00c3329625d60101b8ea7'
# The mode-15 application route pins the original provider owners. Only the stated
# branches are credited here, including the selected entries of the two dispatchers.
PROVIDERS = (
    (OWNER, END, '92a60c7b7568e688bda0434c5efc4945c67b84c3d73a03bb7f2a51fdb5f99187'),
    (COMMAND, 0x08122C3C, '84bce3fe5825479c5d2614a0cb435ec5f8cd79cffbb99d9b441f889c1c1a5cf6'),
    (0x08126AA8, 0x08126B08, '96fb438d3fe6055b001efa9098e02fad9c424fa49a470f8af9669cfbf9527406'),
    (0x08121B8C, 0x08121BB8, '6646f8955088430fdcc363b15cb3555c12a6ae52ec775c4a4aba44e43a7e292f'),
    (PUMP, 0x081219F4, 'd9d8b7a4ac2bd4e80952c1bca9f828975177b96309b576ec64346bea48ec30bb'),
    (0x08121C38, 0x08121C58, 'f6a98a0ab24dce161552ba3c2432668e8e1adb539c790c69604e1d7e9cb49c9c'),
    (CALLBACK, 0x08126BFC, '6e54b22e45fd6e8599a39686a6bd6ef7737a1455dc8457954fca45558ae06077'),
    (0x08022CD4, 0x08022D48, 'a47ac0dc2342784f5b2b64a3fbc9f0ae788d31b0599386f30e59c10d3332d54e'),
    (0x0800363C, 0x08003660, '6b95453a94f8c6961b47f8c147d219c1d04efaf1b3471dd1af65c525dc0f987b'),
    (0x08007620, 0x0800769E, 'ad6e8bbf75a6d483335b1e7e917d199bebee0711402c1c4e10c69b4e8a61215b'),
    (0x080241B4, 0x080245DC, 'b7e705d664c5fd13aec558491c5f264d436143ad472cb2337bcf3f714b0a279f'),
    (0x080C95A8, 0x080C95C0, '1972a08b68f4413fbec69e9c0ceef5227ed3608bb39299597a4de0c061164b84'),
    (0x08022D48, 0x08022DD0, '182b61cb36b38a63666bd3ede44b8e12d9f908207aad7befd0cf92e6aff4efd3'),
    (0x08007894, 0x080078A8, '9195828928e6510162be3c6ac5f0e90734ae6d02707088eb445ec13bfef5f426'),
    (0x080076F4, 0x0800777C, 'f5d817eb9cbea96e6fda920f2a22ff2d20c6fc5857f9883f704f37481a5ec676'),
)


def check_source(root, address):
    import plausible

    root = Path(root)
    require(address == OWNER, 'wrong traversal owner')
    source = (root/'src/08005A24.c').read_text()
    require(base_header((root/'include/ffta.h').read_bytes(), ('func_08005A24', SLOT_NAME, 'func_080058A4'))
            and not any(t in source for t in ('\\', '??', '%:', '\0')), 'changed traversal C input')
    tokens = TOKEN.findall(plausible.strip_comments_and_strings_keep_strings(source))
    require(sha256(' '.join(tokens).encode()).hexdigest() == TOKENS, 'changed task/event traversal source')


def check_bindings(bindings, targets, image):
    require(bindings == BINDINGS and targets == TARGETS and
            all(s['size'] == 0 for s in image['symbols'] if s['name'] in TARGETS),
            'wrong typed current manager, destructor or dynamic callback')


def registration(rom, mapping, index):
    import transfer_task_constructor as constructor
    import transfer_tree_destruction as teardown

    def word(offset):
        return struct.unpack_from('<I', rom, offset)[0]
    def native(start, end):
        return teardown.provider_ins(rom, start, end)

    layout = constructor.bind_allocator(rom, mapping, index)
    # The eight-byte script payload fits the original 36-byte allocation. The
    # resident word loop clears this allocation before installing the callback.
    plan = constructor.transfer.installer.initializer(rom, mapping, index)
    image = rom[0xA38A2C:0xA38ADC]
    zero = constructor.transfer.zero
    clear = zero.verify_conditional(image, 0x03005E78, 0x03005E78, 36, selector=zero.SELECTOR)['cases'][0]
    require(clear['writes'] == [('stack',-4,4)] + [('destination',i,4) for i in range(0,36,4)],
            'wrong allocation initialization')
    block(native(COMMAND,COMMAND+14), COMMAND, 'push {lr}', 'movs r1, #0', 'movs r2, #1', 'bl #0x8126aa8')
    create = native(0x08126AA8, 0x08126AEC)
    block(create, 0x08126AD8, 'str r4, [sp, #4]', 'cmp r5, #0', 'beq #0x8126af0', 'ldr r0, [pc, #0xc]',
          'ldr r3, [r4, #8]', 'movs r1, #8', 'mov r2, sp', 'bl #0x8121b8c')
    block(native(0x08121B8C,0x08121BB4), 0x08121B9A, 'ldr r0, [pc, #0x18]', 'ldr r0, [r0]',
          'ldr r0, [r0]', 'str r3, [sp]', 'adds r1, r5, #0', 'adds r2, r4, #0', 'adds r3, r6, #0',
          'bl #0x8005954')
    require(word(0x126AEC) == CALLBACK | 1 and word(0x121BB4) == word(0x1219AC) == 0x020159CC,
            'wrong script registration or manager shared with state-two pump')
    block(native(PUMP,0x0812191C), PUMP, 'push {r4, lr}', 'adds r4, r1, #0', 'ldrb r0, [r4]',
          'cmp r0, #4', 'bhi #0x81219ea', 'lsls r0, r0, #2', 'ldr r1, [pc, #4]', 'adds r0, r0, r1',
          'ldr r0, [r0]', 'mov pc, r0')
    require(word(0x12191C) == 0x08121920 and word(0x121920 + 2*4) == 0x08121990,
            'state two does not select this script pump')
    block(native(0x08121990,0x081219AC), 0x08121990, 'ldr r1, [pc, #0x18]', 'ldr r0, [r1]',
          'ldrb r0, [r0, #0xc]', 'cmp r0, #0', 'beq #0x812199e', 'movs r0, #3', 'strb r0, [r4]', 'ldr r0, [r1]', 'ldr r0, [r0]', 'bl #0x8005a24',
          'bl #0x8121c38')
    cb = native(CALLBACK, 0x08126BD4)
    block(cb, CALLBACK, 'push {lr}', 'adds r3, r1, #0', 'ldrh r1, [r3]', 'cmp r1, #1', 'beq #0x8126bf6',
          'cmp r1, #1', 'bgt #0x8126bb0', 'cmp r1, #0', 'beq #0x8126bc0', 'b #0x8126bf6',
          'movs r0, #0x80', 'lsls r0, r0, #1', 'cmp r1, r0', 'beq #0x8126bd8', 'adds r0, #2',
          'cmp r1, r0', 'beq #0x8126bec', 'b #0x8126bf6', 'ldr r0, [r3, #4]', 'str r0, [r2]',
          'movs r0, #0x10', 'movs r1, #0xf', 'bl #0x8022cd4', 'ldr r1, [pc, #4]', 'movs r0, #0xf',
          'strb r0, [r1]', 'b #0x8126bf6')
    # The callback's spare r3 still holds its event when it enters the mode-15
    # fade starter. The selected first leaf never uses r3 and the caller clears
    # it before the transition routine can observe the descriptor.
    fade = native(0x08022CD4,0x08022D02)
    block(fade, 0x08022CD4, 'push {r4, lr}', 'sub sp, #4', 'lsls r0, r0, #0x10', 'lsrs r4, r0, #0x10',
          'lsls r1, r1, #0x18', 'lsrs r1, r1, #0x18', 'cmp r1, #0xf', 'beq #0x8022cea')
    block(fade, 0x08022CEA, 'bl #0x800363c', 'ldr r0, [pc, #0x14]', 'lsls r1, r4, #0x10',
          'asrs r1, r1, #0x10', 'str r1, [sp]', 'movs r1, #0x10', 'movs r2, #0', 'movs r3, #0',
          'bl #0x8007620')
    display = native(0x0800363C,0x0800365A)
    block(display, 0x0800363C, 'ldr r1, [pc, #0x1c]', 'adds r2, r1, #0', 'adds r2, #0x4a',
          'ldrb r0, [r2]', 'movs r0, #0xff', 'strb r0, [r2]', 'adds r2, #1', 'ldrb r0, [r2]',
          'movs r0, #0', 'strb r0, [r2]', 'adds r1, #0x4e', 'ldrb r0, [r1]', 'movs r0, #0x10',
          'strb r0, [r1]', 'bx lr')
    block(native(0x08126BD8,0x08126BE6), 0x08126BD8, 'ldr r0, [pc, #0xc]', 'ldrb r0, [r0]',
          'cmp r0, #0', 'bne #0x8126bf6', 'movs r0, #0x81', 'lsls r0, r0, #1', 'b #0x8126bf4')
    block(native(0x08126BEC,0x08126BFC), 0x08126BEC, 'ldr r0, [r2]', 'movs r1, #1', 'strb r1, [r0, #6]',
          'movs r0, #3', 'strh r0, [r3]', 'movs r0, #0', 'pop {r1}', 'bx r1')
    require(word(0x126BD4) == word(0x126BE8) == word(0x241F0) == word(0x245D8) == 0x0200F390 and
            word(0x241F4) == 0x080241F8 and word(0x241F8+15*4) == 0x08024368, 'wrong shared fade state/dispatch')
    block(native(0x08024368,0x08024370), 0x08024368, 'movs r0, #0xf', 'bl #0x8022d48', 'b #0x80245c2')
    block(native(0x080245C2,0x080245D8), 0x080245C2, 'lsls r0, r0, #0x18', 'cmp r0, #0',
          'beq #0x80245ce', 'ldr r1, [pc, #0xc]', 'movs r0, #0', 'strb r0, [r1]')
    return dict(command=COMMAND, callback=CALLBACK, payload_size=8, allocated_bytes=36,
                allocator=layout.sha256, installed_clear=plan['image_sha256'], manager_slot=0x020159CC,
                pump=PUMP, pump_call=0x081219A2, application_mode=15, fade_tick=0x080241B4,
                phase_zero_reads=[[0,2],[4,4]], subsequent_event_reads=[[0,2]],
                subsequent_event_writes=[[0,2]], retained_event_address=False,
                phases={'0':'Save script owner from copied event +4 and start the 16-step transition.',
                        '256':'Wait for the fade byte to become zero, then write phase 258.',
                        '258':'Set byte +6 on the saved script owner, then write phase 3.',
                        '1':'Read only the teardown event phase and return.'})


def prove(data, address, rom, mapping, index, objects, bindings, ins, calls, refinement, words):
    require(address == OWNER and len(data) == 218 and len(ins) == 105 and not words and bindings == BINDINGS
            and calls == {OWNER+s:TARGETS[n][0] for s,n in BINDINGS['calls']}
            and match.parse_data_symbols(objects).get(SLOT_NAME) == SLOT, 'wrong traversal span or bindings')
    entries, rows = indices(mapping,index)
    for start,end,digest in PROVIDERS:
        span_record(start,end,entries,rows,rom)
        require(sha256(rom[start-match.ROM_BASE:end-match.ROM_BASE]).hexdigest() == digest,
                f'changed scheduler/script provider at {start:08X}')
    partition = graph.partition(data,address,refinement,ins,words)
    require(partition['words'] == [dict(address=OWNER+0x84,value=SLOT,load_sites=[OWNER+14],switch_word=False)]
            and not partition['alignment'] and sha256(data).hexdigest() == PROVIDERS[0][2], 'wrong owner image')
    block(ins, OWNER, 'push {r4, r5, r6, r7, lr}', 'mov r7, sl', 'mov r6, sb', 'mov r5, r8',
          'push {r5, r6, r7}', 'sub sp, #0x1c', 'adds r6, r0, #0', 'ldr r0, [pc, #0x74]', 'str r6, [r0]',
          'ldrh r1, [r6, #0xc]', 'movs r2, #1', 'eors r1, r2', 'strh r1, [r6, #0xc]', 'ldr r4, [r6, #4]',
          'mov sb, r0', 'cmp r4, #0', 'beq #0x8005ae8')
    block(ins, 0x08005A4E, 'ldrh r0, [r4, #0x16]', 'ldrh r2, [r6, #0xc]', 'adds r1, r7, #0', 'ands r1, r0',
          'cmp r2, r1', 'beq #0x8005a8a', 'mov r1, sp', 'ldrh r0, [r4, #0x14]', 'strh r0, [r1]',
          'mov r1, r8', 'ldr r0, [r1]', 'str r4, [r0, #8]', 'adds r2, r4, #0', 'adds r2, #0x18',
          'ldr r3, [r4]', 'adds r0, r4, #0', 'mov r1, sp', 'bl #0x8142250', 'mov r0, sp', 'ldrh r0, [r0]',
          'strh r0, [r4, #0x14]', 'ldrh r0, [r4, #0x16]', 'movs r1, #1', 'eors r0, r1', 'strh r0, [r4, #0x16]',
          'mov r1, r8', 'ldr r0, [r1]', 'mov r1, sl', 'str r1, [r0, #8]', 'ldrh r0, [r4, #0x14]', 'cmp r0, #3',
          'bne #0x8005aba', 'adds r5, r4, #0', 'ldr r3, [r4, #8]', 'cmp r3, #0', 'beq #0x8005aac',
          'ldrh r0, [r3, #0x16]', 'ldrh r2, [r6, #0xc]', 'adds r1, r7, #0', 'ands r1, r0', 'cmp r2, r1',
          'beq #0x8005aac', 'adds r4, r3, #0', 'b #0x8005aae')
    block(ins, 0x08005AAC, 'ldr r4, [r4, #0xc]', 'mov r1, r8', 'ldr r0, [r1]', 'adds r1, r5, #0',
          'bl #0x80058a4', 'b #0x8005ae4', 'ldr r3, [r4, #0x10]', 'cmp r3, #0', 'beq #0x8005acc',
          'ldrh r0, [r3, #0x16]', 'ldrh r2, [r6, #0xc]', 'adds r1, r7, #0', 'ands r1, r0', 'cmp r2, r1',
          'bne #0x8005ade', 'ldr r3, [r4, #8]', 'cmp r3, #0', 'beq #0x8005ae2', 'ldrh r0, [r3, #0x16]',
          'ldrh r2, [r6, #0xc]', 'adds r1, r7, #0', 'ands r1, r0', 'cmp r2, r1', 'beq #0x8005ae2',
          'adds r4, r3, #0', 'b #0x8005ae4', 'ldr r4, [r4, #0xc]', 'cmp r4, #0', 'bne #0x8005a4e',
          'movs r0, #0', 'mov r1, sb', 'str r0, [r1]', 'add sp, #0x1c', 'pop {r3, r4, r5}', 'mov r8, r3',
          'mov sb, r4', 'mov sl, r5', 'pop {r4, r5, r6, r7}', 'pop {r0}', 'bx r0')
    # Reuse the reviewed structural destructor and heap release. Its transfer-specific callback
    # path is separate; the script callback's phase-one behavior is established above.
    import transfer_tree_destruction as teardown
    destroy = rom[teardown.OWNER-match.ROM_BASE:teardown.END-match.ROM_BASE]
    import owner_admission_profile as admission
    ref = admission.refine(destroy,teardown.OWNER,mapping)
    inst,edges,_,sites,tables = graph.graph(destroy,teardown.OWNER,ref)
    release = teardown.prove(destroy,teardown.OWNER,rom,mapping,index,teardown.BINDINGS,inst,edges,sites,ref,tables)
    script = registration(rom,mapping,index)
    return dict(schema=SCHEMA,instructions=len(ins),calls=BINDINGS['calls'],runtime_calls=[],partition=partition,
        script_traversal=dict(registration=script, destructor=teardown.OWNER, cleanup=release['transfer_tree']['cleanup'],
            frame_bytes=60,event_bytes=28,defined_event_offsets=[0,1], current_task_offset=8,
            phase_predicate='manager.phase != (node.flags & 1); flip manager phase once and each visited node flag once.',
            traversal='Try unvisited child, then unvisited next sibling, otherwise ascend. Before deleting a subtree, '
                'save an unvisited sibling or the parent. The first node is taken from manager.head.',
            empty_manager='Toggle manager phase and clear global current manager; no callback or free.',
            requirements=['Valid, disjoint ordinary manager, heap, task forest, script owner and private frames. '
                'Manager phase is zero or one, all sibling/parent links are stable and finite, tasks are live and owned.',
                'The reviewed script tasks originate at the mode-one registration with successful task allocation. '
                'Their live script owner provides writable byte +6 and a null or live parent task at +8. '
                'The installed clear and ordinary heap routines retain their normal ABI and storage ownership.',
                'Other callbacks must return with the normal register ABI, consume only defined event fields, never retain the private event, '
                'and preserve the active manager and traversal links unless their changes are independently justified.',
                'Running the original display tick to completion is a caller/environment condition.'],
            arbitrary_callbacks_proved=False, fade_completion_unconditional=False,
            verifier_sha256=sha256(Path(__file__).read_bytes()).hexdigest()))
