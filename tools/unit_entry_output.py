"""The signed-count producer writes one word per iteration to its advancing R7 cursor."""
import hashlib
import struct

from known_query_native_closure_profile import environment_fingerprint
import allocator_search_relation as search
import match
import named_data_buffer_profile as named
import owner_graph_profile as graph
from scheduler_entry_profile import require

MENU, PRODUCER, CONTEXT = 0x08027528, 0x0809F78C, 0x08096D7C
ALLOC, INITIALIZE, SELECT, FREE = 0x08022840, 0x0809DE94, 0x0809E1E0, 0x08022854
ALLOCATION_BYTES, TABLE_OFFSET = 0xE1C, 0xD6C
# These four wrappers leave the incoming cursor in R7. Their sole nested call is
# followed until its own callee saves R7 and kills it before any observable use.
FORWARD = {ALLOC: 0x08007138, 0x08007138: 0x08006EC0, FREE: 0x08007170, 0x08007170: 0x08006FCC}
# The stack word containing the incoming R7 is at entry SP-8. Each tight
# epilogue reloads the same word into R7 and immediately restores the return.
SAVE = {
    0x08006EC0: ('mov r7, r8', 0x08006FC4),
    0x08006FCC: ('mov r7, sb', 0x080070C2),
    INITIALIZE: ('mov r7, sl', 0x0809DF60),
    SELECT: ('mov r7, sl', 0x0809E828),
}
PINS = {
    CONTEXT: (12, '87a96ac9b624426930b1c117b9e2b0809fc860ad0b25bab627b1d9211207c8a9'),
    PRODUCER: (100, '452af8f575282d88591b65918493bddbe88c1609dfa075ec268d7d9b498aed99'),
    ALLOC: (20, '14cb0536da48cf8687d014bc016ba15e46c4576c2f39fcccd74b5d3cd6daf29c'),
    FREE: (20, 'dc40e21202fe3f3244adc6024444db000876a9b76336db4627e6826cb0f5d37b'),
    0x08007138: (54, '41bb84543d24c53f9292d190bc5e895370602a394d7b1db5169b21fcfa6f027f'),
    0x08007170: (12, 'd4c4ef6651a1e11e3311b32b146dfc880c9fe0518ba2b55a0c274b892ef066a3'),
    0x08006EC0: (266, 'ce1efcfe278bbb02f1e96f0943f5be3fa8feef032f2bb456893e67bbd3b33b00'),
    0x08006FCC: (252, '1c178b498423212776ef0bf27836958dee9899b97b44059e586aa70bbf414d26'),
    INITIALIZE: (232, '850fdf6492f4e5abfe0897bd0d70dd9df6b29d90f1c621c4a0e39ef1ea0cbc11'),
    SELECT: (1614, 'fe09215615d486192aee1dd81d6f82e3b573d702f6cd0ce84cf406be323ee82b'),
}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def op(instruction):
    return instruction.mnemonic + ' ' + instruction.op_str


def check_producer(data, instructions, calls):
    # Full decoded path, including the positive guard, back edge, three indexed
    # heap accesses and the only output cursor update. R0 is replaced after free.
    expected = [
        'push {r4, r5, r6, r7, lr}', 'adds r5, r0, #0', 'adds r7, r1, #0',
        'lsls r4, r2, #0x10', 'lsrs r4, r4, #0x10', 'ldr r0, [pc, #0x50]',
        'bl #0x8022840', 'adds r6, r0, #0', 'adds r1, r5, #0', 'bl #0x809de94',
        'lsls r4, r4, #0x10', 'asrs r4, r4, #0x10', 'cmp r4, #0', 'ble #0x809f7d8',
        'movs r5, #0', 'adds r0, r6, #0', 'bl #0x809e1e0', 'lsls r1, r0, #5',
        'adds r1, r1, r0', 'lsls r1, r1, #3', 'adds r1, r1, r6', 'adds r2, r1, #0',
        'adds r2, #0xd8', 'strh r5, [r2]', 'adds r1, #0xd4', 'strh r5, [r1]',
        'lsls r0, r0, #2', 'ldr r2, [pc, #0x20]', 'adds r1, r6, r2', 'adds r1, r1, r0',
        'ldr r0, [r1]', 'stm r7!, {r0}', 'subs r4, #1', 'cmp r4, #0', 'bne #0x809f7ae',
        'adds r0, r6, #0', 'bl #0x8022854', 'movs r0, #1', 'pop {r4, r5, r6, r7}',
        'pop {r1}', 'bx r1',
    ]
    require([op(i) for _, i in sorted(instructions.items())] == expected and len(data) == 100 and
            data[90:92] == bytes(2) and struct.unpack_from('<II', data, 92) == (ALLOCATION_BYTES, TABLE_OFFSET)
            and calls == {PRODUCER+12: ALLOC, PRODUCER+20: INITIALIZE, PRODUCER+36: SELECT, PRODUCER+78: FREE},
            'producer count, cursor, heap offsets, literal pool, calls or return differs')


def cursor_extent(count_word, capacity):
    """Relative word stores on a normal return, for either stack or heap output."""
    require(type(count_word) is int and 0 <= count_word < 2**32 and type(capacity) is int
            and 0 <= capacity < 2**32, 'unsigned count word and output byte capacity required')
    low16 = count_word & 0xFFFF
    signed = (low16 ^ 0x8000) - 0x8000
    iterations = max(0, signed)
    require(iterations*4 <= capacity, 'signed count exceeds output capacity')
    return dict(signed_count=signed, iterations=iterations, store_site=PRODUCER+68,
                start=0, end=iterations*4, stride=4, width=4, return_value=1)


def counted_call(instructions, edges, calls, site, capacity):
    """Compose any verified output region with a reached literal-count producer call."""
    require(calls.get(site) == PRODUCER and op(instructions[site]) == 'bl #0x809f78c',
            'expected the actual advancing producer BL')
    count_site = site-2
    require({source for source, targets in edges.items() if site in targets} == {count_site},
            'a path bypasses the count definition')
    count = instructions[count_site]
    encoded = int.from_bytes(count.bytes, 'little')
    require(encoded & 0xFF00 == 0x2200 and count.mnemonic == 'movs' and count.operands[0].reg == match.ARM_REG_R2
            and count.operands[1].imm == (encoded & 255), 'expected immediate iteration count in R2')
    return cursor_extent(encoded & 255, capacity)


def heap_accesses(index):
    """Allocate-relative offsets under a nonwrapping, in-allocation selection."""
    require(type(index) is int and 0 <= index < 2**32, 'unsigned selector result required')
    reads = TABLE_OFFSET + index*4
    record = index*264
    require(reads+4 <= ALLOCATION_BYTES and record+0xD8+2 <= ALLOCATION_BYTES,
            'selected record or entry outside the allocated object')
    return dict(clear_halfwords=[record+0xD8, record+0xD4], read_word=reads)


def saved_cursor_frame(address, instructions, edges, restore):
    """Track SP on every CFG edge so each reload is the original R7 save."""
    depths, pending, forwarded = {address: 0}, [address], {}
    r7 = match.ARM_REG_R0+7
    while pending:
        site = pending.pop()
        i = instructions[site]
        sp = depths[site]
        if i.mnemonic in ('push', 'pop'):
            registers = [operand.reg for operand in i.operands]
            saving = i.mnemonic == 'push'
            lo = sp-4*len(registers) if saving else sp
            for n, register in enumerate(registers):
                if lo+4*n == -8:
                    require(site == (address if saving else restore) and register == r7,
                            'private saved cursor is spilled again or reloaded into another register')
            sp = lo if saving else sp+4*len(registers)
        elif i.mnemonic in ('sub', 'add') and i.op_str.startswith('sp, #'):
            amount = i.operands[1].imm
            sp += amount if i.mnemonic == 'add' else -amount
            require(sp <= -20, 'local allocation/deallocation crosses the saved cursor')
        elif match.ARM_REG_SP in i.regs_access()[0] or match.ARM_REG_SP in i.regs_access()[1]:
            if i.mnemonic in ('ldr', 'str') and i.op_str.split(', ', 1)[1].startswith('[sp'):
                offset = sp+i.operands[1].mem.disp
                require(sp <= offset <= -24 and offset%4 == 0, 'direct local access overlaps cursor save')
            else:
                # These are exactly the two word outputs passed to allocator_search_relation.
                expected = {0x08006ECE: ('add r3, sp, #4', -28), 0x08006ED2: ('mov r2, sp', -32)}
                require(address == 0x08006EC0 and site in expected and op(i) == expected[site][0]
                        and sp == -32, 'untracked address derived from the helper frame')
                forwarded[site] = expected[site][1]
        require(sp <= 0 and (edges[site] or sp == 0), 'helper returns with an unbalanced frame')
        for target in edges[site]:
            if target in depths:
                require(depths[target] == sp, 'inconsistent helper SP at CFG join')
            else:
                depths[target] = sp
                pending.append(target)
    require(set(depths) == set(instructions), 'saved cursor proof omitted reachable instructions')
    if address == 0x08006EC0:
        require(forwarded == {0x08006ECE: -28, 0x08006ED2: -32}
                and op(instructions[0x08006ED4]) == 'bl #0x8006c88',
                'allocator search requires the two private outputs below its cursor save')
    return sorted(forwarded.values())


def helper_cursor(address, instructions, edges, calls):
    if address in FORWARD:
        require(list(calls.values()) == [FORWARD[address]] and
                all(match.ARM_REG_R0+7 not in (*i.regs_access()[0], *i.regs_access()[1])
                    for i in instructions.values()), 'wrapper observes the cursor or forwards to a different helper')
        if address == ALLOC:
            require(op(instructions[address]) == 'push {lr}' and
                    op(instructions[address+2]) == 'adds r1, r0, #0',
                    'allocation wrapper must kill the incoming cursor in R1 before any use')
        return dict(address=address, action='forward R7', target=FORWARD[address])
    kill, restore = SAVE[address]
    require(op(instructions[address]) == 'push {r4, r5, r6, r7, lr}' and
            op(instructions[address+2]) == kill and
            op(instructions[restore]) == 'pop {r4, r5, r6, r7}' and
            op(instructions[restore+2]) in ('pop {r0}', 'pop {r1}') and
            op(instructions[restore+4]) == 'bx ' + instructions[restore+2].op_str[1:-1]
            and {k for k, targets in edges.items() if not targets} == {restore+4},
            'helper must save, immediately shadow, and finally restore the cursor')
    outputs = saved_cursor_frame(address, instructions, edges, restore)
    return dict(address=address, action='saved R7 at entry SP-8', kill=address+2, restore=restore,
                forwarded_local_word_offsets=outputs)


def native_producer(rom, mapping, index, objects):
    import owner_admission_profile as owner
    resolver = named.NamedDataBufferProof(rom, mapping, index, objects)
    resolver.dependency_budget = len(PINS)+1
    dependencies, cursors = [], []
    for address, (size, digest) in PINS.items():
        body = resolver.span(address)
        require(len(body) == size and sha(body) == digest, 'unit-list dependency extent or identity differs')
        ins, edges, branches, calls, words = graph.graph(body, address, owner.refine(body, address, mapping))
        require(not branches and not words, 'unit-list dependency contains an unsupported transfer')
        if address == CONTEXT:
            require([op(i) for _, i in sorted(ins.items())] == ['ldr r0, [pc, #4]', 'ldr r0, [r0]', 'bx lr']
                    and struct.unpack_from('<I', body, 8)[0] == 0x0200F4B0, 'unexpected menu context getter')
        elif address == PRODUCER:
            check_producer(body, ins, calls)
        else:
            cursors.append(helper_cursor(address, ins, edges, calls))
        dependencies.append(dict(address=address, bytes=size, instructions=len(ins), sha256=digest))
    # The only local addresses exported from the save/kill helper frames are
    # the allocator's two output words. The pinned median-search kernel has
    # exactly four word stores, all at offset zero through those two formals.
    start = 0x08006C88
    body = resolver.span(start)
    ins, _, _, calls, _ = graph.graph(body, start, owner.refine(body, start, mapping))
    layout = search.bind(body, start, len(ins), selector=search.SELECTOR)
    stores = [op(i) for _, i in sorted(ins.items()) if i.mnemonic.startswith(('str', 'stm'))]
    require(not calls and stores == ['str r0, [r7]', 'str r0, [r6]', 'str r3, [r6]', 'str r2, [r7]'],
            'allocator search writes outside its two local output words')
    dependencies.append(dict(address=start, bytes=len(body), instructions=len(ins), sha256=layout.sha256))
    return dict(dependencies=dependencies, nested_cursor_exposure=cursors,
                allocation_bytes=ALLOCATION_BYTES, record_stride=264, entry_table_offset=TABLE_OFFSET,
                valid_selected_indices=[0, (ALLOCATION_BYTES-0xDA)//264],
                first_selection=heap_accesses(0), last_selection=heap_accesses(12),
                conditions=[
                    'Helpers return under the ARM ABI, preserve protected save words and do not disclose '
                    'private saved-register storage. The allocator, initializer, selector and deallocator '
                    'have valid ordinary heap/context accesses separate from all live stack words and the '
                    'output array. Callback installation, heap traversal and termination are unproved.',
                    'Each selected index is in 0..12 and its table word identifies a persistent external '
                    'entry. Entry storage survives the temporary heap free. The selector and initializer '
                    'are not proved to establish those dynamic object properties.',
                    'The output consists of aligned writable words with sufficient capacity and nonwrapping '
                    'cursor arithmetic including the final one-past value. Helper scratch and external '
                    'memory are separate from this array.'])


def prove(data, address, rom, mapping, index, objects, *, bindings, ins, edges, calls, refinement):
    require(address == MENU and len(data) == 50 and calls == {MENU+6: CONTEXT, MENU+14: PRODUCER},
            'expected the indexed 50-byte menu owner and both exact BLs')
    expected = dict(calls=[[6, 'func_08096D7C'], [14, 'func_0809F78C']], data=[], functions=[], switches=[])
    require(bindings == expected, 'expected the genuine two direct call relocations and no literals')
    require([op(i) for _, i in sorted(ins.items())] == [
        'push {r4, lr}', 'sub sp, #0x50', 'adds r4, r0, #0', 'bl #0x8096d7c',
        'mov r1, sp', 'movs r2, #0x14', 'bl #0x809f78c', 'movs r2, #0', 'adds r4, #0x94',
        'mov r3, sp', 'ldr r0, [r4]', 'lsls r1, r2, #2', 'adds r1, r1, r0', 'ldm r3!, {r0}',
        'ldr r0, [r0]', 'str r0, [r1]', 'adds r2, #1', 'cmp r2, #0x13', 'ble #0x8027540',
        'add sp, #0x50', 'pop {r4}', 'pop {r0}', 'bx r0'],
        'menu local extent, count, consumer dereference, destination or restoration differs')
    capacity = 80
    effect = counted_call(ins, edges, calls, MENU+14, capacity)
    consumed = list(range(0, 4*(19+1), 4))
    require(consumed == list(range(effect['start'], effect['end'], effect['stride'])),
            'consumer reads words outside initialized output')
    return dict(schema=named.UNIT_OUTPUT_SCHEMA, instructions=len(ins), calls=expected['calls'], runtime_calls=[],
                partition=graph.partition(data, address, refinement, ins, {}), producer=native_producer(
                    rom, mapping, index, objects), local_array=dict(producer=effect, consumer_offsets=consumed,
                    caller_local=[-88, -8], caller_saved=[-8, 0], producer_saved=[-108, -88],
                    consumer_load=MENU+30, destination_field=0x94,
                    condition='Menu+0x94 yields a live 20-word destination separate from the owner frame. '
                              'Each emitted entry permits its word-zero dereference. The destination stores '
                              'preserve the menu pointer and all entry words needed by later iterations.'),
                environment=environment_fingerprint())
