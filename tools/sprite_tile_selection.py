"""The sprite owner's tile range selection and temporary key-ordered tree."""
from hashlib import sha256
from struct import unpack_from

import function_thunk_profile as thunk
import match
import named_data_buffer_profile as buffers
import owner_graph_profile as graph
import plausible
import scheduler_zero_descriptor as boot
from ability_range_local_bytes import block, require
from active_entry_shuffle_profile import compiler_symbol_roles
from known_query_native_closure_profile import environment_fingerprint
from literal_callback_closure_profile import complete
from menu_roster_filter import heap_providers
from sdk_cpuset_halfword import TOKEN, base_header
from software_double_profile import indices, span_record
from software_float_profile import ROM_SHA256
from transfer_tree_destruction import provider_ins

OWNER, END = 0x08021854, 0x0802192C
TABLE, CLEAR = 'g_callbacks_0836D4B8', '_call_via_r2'
FILTER, ITERATOR = 0x08022164, 0x080C7CC0
COUNT, EXPORT, WALK, APPEND = 0x080C7B20, 0x080C7B9C, 0x080C7D18, 0x080C7E68
EXTRACT = 0x080C7B78
SITES = ((0x8092784, 0x8096B2C, 0x8092C60), (0x80A5B98, 0x80A6F1E, 0x80A6CD2),
         (0x80B8414, 0x80BA66A, 0x80BA624))
CALLS = {OWNER+offset: target for offset, target in (
    (0x0A,0x080C79E0), (0x10,0x080C7B08), (0x22,0x08007138), (0x30,0x0814224C),
    (0x5A,ITERATOR), (0x60,COUNT), (0x6E,0x080C79E0), (0x76,0x08007170),
    (0x88,0x08007138), (0x92,EXPORT), (0xA6,EXTRACT), (0xB2,0x080C79E0))}
BINDINGS = dict(calls=[[pc-OWNER, CLEAR if point == thunk.ALIASES[CLEAR] else f'func_{point:08X}']
                       for pc,point in CALLS.items()], data=[[0x44,TABLE,0]],
                functions=[[0x80,'func_08022164']], switches=[])
SOURCES = {'src/08021854.c':'12c6980dafdce4d0e4efc57678acc34e12efe3770b26292fafecfe8b9fc487d9',
           'include/object_list.h':'75dcd13c44a28f6381bd5eee547c6df3688e3ea3ba7bde1730892a1174936b00'}
# Size and reachable instruction count of the complete closures exercised here.
SPAN = {0x080C79E0:(82,40), 0x080C7B08:(22,11), ITERATOR:(34,16), FILTER:(48,22),
        0x080C7B74:(4,2), 0x080C7AB4:(84,41), COUNT:(84,42), EXPORT:(44,19), WALK:(86,42),
        APPEND:(16,8), EXTRACT:(10,5), 0x08099C30:(4,2), 0x08021A3C:(136,61),
        0x080C799C:(24,11), 0x08097000:(232,93), 0x08022080:(18,9), 0x08007138:(54,26), 0x08007170:(12,5)}


def check_source(root):
    path = root/'src/08021854.c'
    require(plausible.include_closure(root, path) == (set(SOURCES) | {'include/ffta.h'}, [])
            and base_header((root/'include/ffta.h').read_bytes(),
                            ('SpriteOwner','SpriteCollection','SpriteSelection',TABLE,'func_08021854')),
            'changed sprite selection includes or scalar header')
    for name, digest in SOURCES.items():
        src = (root/name).read_text()
        require(not any(marker in src for marker in (chr(92),'??','%:',chr(0)))
                and sha256(' '.join(TOKEN.findall(plausible.strip_comments_and_strings_keep_strings(src)))
                           .encode()).hexdigest() == digest, 'changed sprite selection C or callback ABI')


def check_original(image, bindings, targets):
    expected = {name:(CALLS[OWNER+offset],False) for offset,name in BINDINGS['calls']}
    expected.update({TABLE:(boot.POINTER,True), 'func_08022164':(FILTER,False)})
    require(bindings == BINDINGS and targets == expected and
            all(row['size'] == 0 for row in image['symbols'] if row['name'] in expected),
            'incorrect sprite selection ELF call, object or function literal')
    compiler_symbol_roles(image, targets)


def walk_step(code, start, exit_pc, current, previous, root, children, callback=0):
    """Execute one native node transition on a finite proper binary tree.

    The only compared addresses are null, current, parent, root, distinct children
    and the initial sentinel. Their equality classes exhaust every possible input.
    """
    count_walk = not callback
    ptr, prev, root_reg = ('r1','r3','r5') if count_walk else ('r4','r2','r5')
    regs = {ptr:current, prev:previous, root_reg:root}
    if count_walk:
        regs['r4'] = 0
    else:
        regs['r6'] = 0x800
    parent,left,right = children
    fields = {current+8:parent, current+12:left, current+16:right}
    pc = start
    emitted = 0
    for _ in range(40):
        if pc == exit_pc:
            return 'exit', emitted
        item = code[pc]
        op = item.mnemonic
        args = list(item.operands)
        def reg(i):
            return item.reg_name(args[i].reg)
        def val(i):
            return args[i].imm if args[i].type == match.ARM_OP_IMM else regs[reg(i)]
        next_pc = pc + item.size
        if op == 'ldr':
            mem = args[1].mem
            regs[reg(0)] = fields[regs[item.reg_name(mem.base)] + mem.disp]
        elif op == 'cmp':
            equal = val(0) == val(1)
        elif op in ('b','bne','beq'):
            if op == 'b' or (op == 'beq') == equal:
                next_pc = val(0)
        elif op == 'adds' and len(args) == 3:
            regs[reg(0)] = val(1) + val(2)
        elif op == 'adds' and count_walk and reg(0) == 'r4' and val(1) == 1:
            emitted += 1
            regs['r4'] += 1
        elif op == 'bl' and callback and val(0) == thunk.ALIASES['_call_via_r7']:
            require(regs['r0'] == current and regs['r1'] == regs['r6'],
                    'tree export lost current node or cursor')
            # The complete APPEND body below returns one and overwrites R2 with the advanced cursor.
            emitted += 1
            regs.update(r0=1,r2=0x900)
        else:
            raise ValueError(f'unexpected sprite tree transition at {pc:08X}')
        pc = next_pc
        if pc == start:
            require(regs[prev] == current, 'tree transition did not retain previous node')
            return {parent:'up', left:'left',right:'right'}[regs[ptr]], emitted
    raise ValueError('sprite tree transition failed to finish')


def traversal(code, original):
    block(code[APPEND], APPEND, 'ldr r2, [r1]', 'stm r2!, {r0}', 'ldr r0, [r1, #4]',
          'adds r0, #1', 'str r0, [r1, #4]', 'str r2, [r1]', 'movs r0, #1', 'bx lr')
    require(unpack_from('<I',original[EXPORT],32)[0] == APPEND|1, 'changed tree cursor callback')
    block(code[EXPORT], EXPORT+12, 'str r1, [sp]', 'movs r0, #0', 'str r0, [sp, #4]',
          'ldr r1, [pc, #0xc]', 'adds r0, r2, #0', 'mov r2, sp', 'bl #0x80c7d18')
    block(code[WALK], WALK, 'push {r4, r5, r6, r7, lr}', 'adds r7, r1, #0', 'adds r6, r2, #0',
          'ldr r4, [r0, #8]', 'movs r2, #1', 'rsbs r2, r2, #0', 'adds r5, r4, #0')
    block(code[COUNT], COUNT+12, 'adds r1, r0, #0','movs r4, #0','movs r3, #1',
          'rsbs r3, r3, #0','adds r5, r1, #0','b #0x80c7b3c')
    cases = 0
    current = 0x100
    for start, end, helper in ((COUNT+28,COUNT+76,0),(WALK+14,WALK+80,APPEND)):
        for root in (current,0x500):
            parent = 0 if root == current else 0x200
            ascend = 'exit' if root == current else 'up'
            entering = -1 if root == current else parent
            for left in (0,0x300):
                for right in (0,0x400):
                    first,second = (('left',left),('right',right)) if helper else (('right',right),('left',left))
                    # A child subtree returns through the same reciprocal link.
                    # Visit the node exactly once between first and second subtrees.
                    states = [(entering, (first[0],0) if first[1] else
                               (second[0] if second[1] else ascend,1))]
                    if first[1]:
                        states.append((first[1], (second[0] if second[1] else ascend,1)))
                    if second[1]:
                        states.append((second[1], (ascend,0)))
                    for previous, expected in states:
                        require(walk_step(code[WALK if helper else COUNT],start,end,current,previous,
                                          root,(parent,left,right),helper) == expected,
                                'tree count and export do not visit each proper node exactly once')
                        cases += 1
    return dict(transitions=cases, count_order='right, node, left', export_order='left, node, right',
                append_bytes=4, node_visits='one per node by induction on finite reciprocal child subtrees')


def prove(data, rom, mapping, index, objects, bindings, ins, edges, calls, refinement, words):
    require(sha256(rom).hexdigest() == ROM_SHA256 and data == rom[OWNER-match.ROM_BASE:END-match.ROM_BASE]
            and len(ins) == 90 and calls == CALLS and bindings == BINDINGS and not words
            and match.parse_data_symbols(objects).get(TABLE) == boot.POINTER, 'wrong sprite selection ROM or bindings')
    entries, rows = indices(mapping,index)
    require(span_record(OWNER, END, entries, rows, rom)['instrs'] == len(ins), 'wrong sprite selection index count')
    partition = graph.partition(data,OWNER,refinement,ins,words)
    literals = [(row['address'],row['value'],row['load_sites']) for row in partition['words']]
    require(partition['code_bytes'] == 204 and partition['alignment'] ==
            [[0x08021896,0x08021898],[0x080218D2,0x080218D4]] and
            literals == [(0x08021898,boot.POINTER,[0x0802187C]),(0x080218D4,FILTER|1,[0x080218AA])],
            'changed sprite selection partition')
    bodies = {a:complete(a,size,n,rom,mapping,index) for a,(size,n) in SPAN.items()}
    code = {a:item[1] for a,item in bodies.items()}
    for name in (CLEAR,'_call_via_r6','_call_via_r7'):
        thunk.dependencies([name], rom)
        a = thunk.ALIASES[name]
        require(span_record(a,a+2,entries,rows,rom)['instrs'] == 1, 'wrong sprite callback thunk')
    for start,end,digest in heap_providers():
        span_record(start,end,entries,rows,rom)
        require(sha256(rom[start-match.ROM_BASE:end-match.ROM_BASE]).hexdigest() == digest, 'changed heap provider')
    block(code[0x08099C30],0x08099C30,'ldr r0, [r0, #8]','bx lr')
    for start,end,site in SITES:
        span_record(start,end,entries,rows,rom)
        block(provider_ins(rom,site-6,site+4), site-6, 'bl #0x8099c30','movs r1, #0','bl #0x8021854')
    # 08097000 stores the freshly constructed 08021A3C owner in the very
    # field returned by 08099C30. List and tree nodes use that owner's heap.
    block(code[0x08022080],0x08022080,'lsls r1, r0, #3','adds r1, r1, r0','lsls r1, r1, #3',
          'lsls r0, r0, #5','adds r0, r0, r1','movs r1, #0xfa','lsls r1, r1, #2',
          'adds r0, r0, r1','bx lr')
    block(code[0x08097000],0x08097054,'ldr r4, [r7]','movs r0, #0x34','bl #0x8022080',
          'adds r1, r0, #0','movs r5, #0x80','lsls r5, r5, #3','adds r1, r1, r5',
          'adds r0, r4, #0','bl #0x8007138','adds r4, r0, #0','str r4, [r7, #4]')
    block(code[0x08097000],0x08097080,'ldr r4, [r7, #4]','movs r0, #0x34','bl #0x8022080',
          'adds r1, r0, #0','adds r1, r1, r5','adds r0, r4, #0','bl #0x80070c8','adds r4, r0, #0',
          'movs r2, #0x90','lsls r2, r2, #1','movs r3, #0xf0','lsls r3, r3, #1',
          'str r5, [sp]','movs r1, #0','bl #0x8021a3c','str r0, [r7, #8]')
    block(code[0x08021A3C],0x08021A86,'str r7, [r4]','adds r0, r7, #0','bl #0x80c799c',
          'str r0, [r4, #4]')
    block(code[0x080C799C],0x080C799C,'push {r4, lr}','adds r4, r0, #0','movs r1, #0xc',
          'bl #0x8007138','str r4, [r0]','movs r1, #0','str r1, [r0, #4]','str r1, [r0, #8]')
    block(code[0x08007138],0x08007154,'lsls r1, r1, #0xe','lsrs r1, r1, #0x10','adds r0, r2, #0',
          'bl #0x8006ec0','movs r1, #0','cmp r0, #0','beq #0x8007168','adds r1, r0, #0',
          'adds r1, #0xc','adds r0, r1, #0')
    heap_bytes = 0x34 * (9*8+32) + 0xfa*4 + (0x80<<3)
    # Even ignoring the 12-byte block header and all other live allocations,
    # disjoint 24-byte payloads fit fewer than 310 nodes in the real heap.
    maximum = heap_bytes//24
    require(heap_bytes == 7432 and maximum == 309 and 4*maximum < 0x10000,
            'tree cardinality can wrap a signed loop or truncate its array allocation')
    block(code[0x08021A3C],0x08021A90, 'ldr r0, [r4]','bl #0x80c799c','str r0, [r4, #8]',
          'strh r5, [r4, #0xc]','strh r6, [r4, #0xe]','mov r0, r8','strh r0, [r4, #0x10]',
          'mov r0, sb','strh r0, [r4, #0x12]')
    block(ins,OWNER,'push {r4, r5, r6, r7, lr}','sub sp, #0xc','adds r4, r1, #0','adds r7, r0, #0',
          'ldr r0, [r7, #8]','bl #0x80c79e0','ldr r0, [r7, #8]','bl #0x80c7b08')
    block(ins,0x08021872,'ldr r0, [r7]','movs r1, #0x1c','bl #0x8007138','adds r5, r0, #0',
          'ldr r0, [pc, #0x18]','ldr r2, [r0]','adds r0, r5, #0','movs r1, #0x1c','bl #0x814224c')
    block(ins,0x08021868,'adds r6, r0, #0','cmp r6, #0','bne #0x8021872','movs r0, #0','b #0x8021924')
    block(ins,0x08021888,'str r7, [r5, #0x18]','cmp r4, #0','beq #0x802189c','ldrh r0, [r7, #0x10]',
          'strh r0, [r5]','ldrh r0, [r7, #0x12]','b #0x80218a2')
    block(ins,0x0802189C,'ldrh r0, [r7, #0xc]','strh r0, [r5]','ldrh r0, [r7, #0xe]','strh r0, [r5, #2]')
    block(ins,0x080218A4,'str r5, [sp]','ldr r0, [r7, #8]','str r0, [sp, #4]','ldr r1, [pc, #0x28]',
          'mov r2, sp','bl #0x80c7cc0','ldr r0, [r7, #8]','bl #0x80c7b20')
    block(code[ITERATOR],ITERATOR,'push {r4, r5, r6, lr}','adds r6, r1, #0','adds r5, r2, #0',
          'ldr r4, [r0, #4]','b #0x80c7ccc','ldr r4, [r4, #8]','cmp r4, #0','beq #0x80c7cdc',
          'adds r0, r4, #0','adds r1, r5, #0','bl #0x814225c','cmp r0, #0','bne #0x80c7cca')
    block(code[0x080C7B74],0x080C7B74,'ldr r0, [r0]','bx lr')
    block(code[FILTER], FILTER,'push {r4, lr}','adds r4, r1, #0','bl #0x80c7b74','adds r1, r0, #0',
          'ldr r3, [r4]','ldrh r0, [r3]','ldrh r2, [r1, #0x12]','cmp r0, r2','bhi #0x802218c',
          'ldrh r0, [r3, #2]','cmp r0, r2','bls #0x802218c','ldr r0, [r1, #0x38]','cmp r0, #0',
          'beq #0x802218c','ldr r0, [r4, #4]','ldrh r2, [r1, #0x12]','bl #0x80c7ab4',
          'movs r0, #1','pop {r4}','pop {r1}','bx r1')
    block(code[0x080C7AB4],0x080C7ABC,'ldr r0, [r5]','movs r1, #0x18','bl #0x8007138',
          'adds r3, r0, #0','str r4, [r3, #4]','str r6, [r3]','movs r0, #0','str r0, [r3, #8]',
          'str r0, [r3, #0xc]','str r0, [r3, #0x10]','str r0, [r3, #0x14]')
    block(code[0x080C7AB4],0x080C7AD4,'ldr r0, [r5, #8]','cmp r0, #0','bne #0x80c7ade',
          'str r3, [r5, #8]','b #0x80c7b00','adds r1, r0, #0','adds r2, r6, #0','ldr r0, [r1]',
          'cmp r2, r0','bge #0x80c7af2','ldr r0, [r1, #0xc]','cmp r0, #0','bne #0x80c7af8',
          'str r3, [r1, #0xc]','b #0x80c7afe','ldr r0, [r1, #0x10]','cmp r0, #0','beq #0x80c7afc',
          'adds r1, r0, #0','b #0x80c7ae2','str r3, [r1, #0x10]','str r1, [r3, #8]')
    block(ins,0x080218B8,'adds r6, r0, #0','str r6, [r5, #0x10]','cmp r6, #0','bgt #0x80218d8',
          'ldr r0, [r7, #8]','bl #0x80c79e0','ldr r0, [r7]','adds r1, r5, #0','bl #0x8007170')
    block(ins,0x080218D8,'ldr r0, [r7]','lsls r1, r6, #2','bl #0x8007138','adds r1, r0, #0',
          'str r1, [r5, #4]','ldr r0, [r7, #8]','bl #0x80c7b9c','movs r4, #0','cmp r4, r6',
          'bge #0x8021904','ldr r0, [r5, #4]','lsls r1, r4, #2','adds r1, r1, r0','ldr r0, [r1]',
          'add r2, sp, #8','bl #0x80c7b78','adds r4, #1','cmp r4, r6','blt #0x80218f0')
    block(code[EXTRACT],EXTRACT,'ldr r3, [r0, #4]','str r3, [r1]','ldr r0, [r0]','str r0, [r2]','bx lr')
    block(code[0x080C79E0],0x080C79E0,'push {r4, r5, r6, r7, lr}','adds r5, r0, #0',
          'ldr r7, [r5]','ldr r4, [r5, #8]','movs r2, #1','rsbs r2, r2, #0')
    block(code[0x080C79E0],0x080C7A16,'adds r0, r7, #0','adds r1, r4, #0','bl #0x8007170',
          'cmp r4, r6','beq #0x80c7a28','adds r2, r4, #0','ldr r4, [r4, #8]','b #0x80c79ee',
          'movs r0, #0','str r0, [r5, #8]')
    block(ins,0x08021904,'ldr r0, [r7, #8]','bl #0x80c79e0','ldr r0, [r5, #4]','str r0, [r5, #8]',
          'adds r2, r0, #0','movs r4, #0','b #0x802191c','ldm r2!, {r0}','ldrh r1, [r0, #0x12]',
          'strh r1, [r0, #0x14]','adds r4, #1','ldr r0, [r5, #0x10]','cmp r4, r0','blt #0x8021914',
          'adds r0, r5, #0','add sp, #0xc','pop {r4, r5, r6, r7}','pop {r1}','bx r1')
    require({(pc,to) for pc,tos in edges.items() for to in tos if to <= pc} ==
            {(0x08021902,0x080218F0),(0x08021920,0x08021914)}, 'changed selector cycle')
    clear = boot.initializer(rom,mapping,index)
    require(clear['result']['zero_write_span'] == [0,28], 'unexpected cleared selection size')
    block(code[0x08007170],0x08007170,'push {lr}','subs r1, #0xc','bl #0x8006fcc','pop {r0}','bx r0')
    return dict(schema=buffers.THUNK_SCHEMA, instructions=90, calls=BINDINGS['calls'], runtime_calls=[],
                partition=partition, environment=environment_fingerprint(), caller_sites=SITES,
                actor_heap=dict(constructor=0x08097000, owner_field=8, size=heap_bytes,
                               distinct_node_payloads_upper_bound=maximum, primary=[0,0x120], alternate=[0x1E0,0x400]),
                frame=dict(private_bytes=12, saved_bytes=20, filter_words=[0,4], extracted_key=8),
                clearer=dict(entry=clear['entry'], image=clear['image_sha256'], effects=clear['result']),
                traversal=traversal(code,{a:item[0] for a,item in bodies.items()}),
                providers=[[a,sd[0],sd[1],sha256(bodies[a][0]).hexdigest()] for a,sd in SPAN.items()],
                contracts=[
                    'Live word-aligned owner, heap, collection and finite stable list of live sprites. '
                    'The temporary tree is finite, acyclic and reciprocal. A qualifying sprite has a tile in '
                    'the chosen half-open range and a nonzero word at +0x38. All three original direct '
                    'callers select the primary range. The other branch selects the alternate range.',
                    'The original heap has room for each successful 24-byte tree node, the 28-byte result '
                    'and any required 4*n-byte value array. Its 7432-byte extent bounds n to 309. Allocations are distinct from live '
                    'objects. During postorder destruction the allocator retains the released node parent '
                    'word at +8 until the immediately following native load. The returned sprite values '
                    'are independently live. No allocation failure, concurrent mutation or physical access '
                    'guarantee is asserted.',
                    'Boot installed the original executable clearer and it remains intact. Frame, heap and '
                    'code are disjoint; returning calls preserve the ABI and do not expose private words. '
                    'The filter receives the two initialized external addresses; the extractor writes a '
                    'discarded key into bytes [8,12). Tree counting may retain R2 on the empty branch; '
                    'the following tree destruction replaces it before use. Nonempty counting first loads '
                    'a tree child into R2. The final destruction also kills the extracted-key pointer before use.'])
