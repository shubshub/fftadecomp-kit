"""The two private byte outputs and bounded scan of the USA ability range predicate."""
import hashlib
import struct

import match
import named_data_buffer_profile as named
import owner_graph_profile as graph
from known_query_native_closure_profile import environment_fingerprint
from software_double_profile import indices, span_record
from software_float_profile import ROM_SHA256

ROOT = 0x080CD2C4
QUERY = 0x080C8570
RECORDS = 0x08521A14
ROWS = 0x0851BA84


def require(condition, message):
    if not condition:
        raise ValueError(message)


def block(instructions, start, *operations):
    for operation in operations:
        item = instructions.get(start)
        require(item is not None and f'{item.mnemonic} {item.op_str}' == operation,
                f'ability-range operation differs at {start:08X}: expected {operation}')
        start += item.size
    return start


def resolve_ranges(rom):
    # The native inputs are zero-extended to eight bits. This enumerates physical
    # ROM reads; it does not assign all 256 records to the source-level object.
    returned, cycles = [], []
    for original in range(256):
        record, seen = original, set()
        while record not in seen:
            seen.add(record)
            base = RECORDS - match.ROM_BASE + 52 * record
            require(0 <= base and base + 48 <= len(rom), 'redirect record outside ROM')
            redirect = rom[base + 5]
            if redirect == 0:
                first, last = rom[base + 46:base + 48]
                require(last < 255, 'a returning ability range permits byte-counter wraparound')
                returned.append((original, first, last))
                break
            record = original if redirect == 255 else redirect
        else:
            cycles.append(original)
    require(returned, 'no returning ability query')
    return dict(returning_ids=len(returned), repeating_redirect_ids=cycles,
                returned_bounds_sha256=hashlib.sha256(b''.join(bytes(row) for row in returned)).hexdigest(),
                maximum_last=max(last for _, first, last in returned),
                maximum_iterations=max(max(0, last-first+1) for _, first, last in returned))


def query(proof):
    data = proof.span(QUERY)
    instructions, transfers = proof.inspect(QUERY, data)
    ins = {i.address: i for i in instructions}
    require(len(data) == 1204 and len(ins) == 501 and set(transfers) == {0x080C8594},
            'complete category query and preloaded switch required')
    # The first query leaves the output pointers in R8/R9; the second also
    # carries the first result in R4. Check both preservation and observation.
    protected = {match.ARM_REG_R0+8, match.ARM_REG_R0+9}
    require(all(not protected.intersection((*i.regs_access()[0], *i.regs_access()[1]))
                for i in ins.values()), 'category query observes a private output pointer')
    block(ins, QUERY, 'push {r4, r5, r6, lr}', 'lsls r0, r0, #0x18', 'lsrs r0, r0, #0x18',
          'lsls r1, r1, #0x18', 'lsrs r4, r1, #0x18', 'lsls r2, r2, #0x18', 'lsrs r5, r2, #0x18',
          'movs r1, #0x34', 'muls r1, r0, r1', 'ldr r0, [pc, #0x14]', 'adds r3, r1, r0',
          'adds r2, r0, #0', 'ldr r6, [pc, #0x10]', 'cmp r5, #0x2f', 'bhi #0x80c858a',
          'lsls r0, r5, #2', 'adds r0, r0, r6', 'ldr r0, [r0]', 'mov pc, r0')
    table = 0x080C85A0
    require(struct.unpack_from('<II', data, 0x080C8598-QUERY) == (RECORDS, table),
            'category-record base or code table changed')
    for selector, target, field in ((37, 0x080C895C, 46), (38, 0x080C896C, 47)):
        require(struct.unpack_from('<I', data, table-QUERY+4*selector)[0] == target and
                target in transfers[0x080C8594], 'wrong ability range dispatch arm')
        block(ins, target, 'ldrb r0, [r3, #5]', 'cmp r0, #0xff', 'beq #0x80c8a02',
              'cmp r0, #0', 'bne #0x80c8a0e', 'adds r0, r3, #0', f'adds r0, #{field:#x}', 'b #0x80c8a1c')
    block(ins, 0x080C8A02, 'movs r0, #0x34', 'muls r0, r4, r0', 'adds r3, r0, r2', 'b #0x80c858a')
    block(ins, 0x080C8A0E, 'ldrb r0, [r3, #5]', 'movs r1, #0x34', 'muls r0, r1, r0',
          'adds r3, r0, r2', 'b #0x80c858a')
    block(ins, 0x080C8A1C, 'ldrb r0, [r0]', 'pop {r4, r5, r6}', 'pop {r1}', 'bx r1')
    return dict(address=QUERY, bytes=len(data), instructions=len(ins), sha256=hashlib.sha256(data).hexdigest(),
                selector_fields=[[37, 46], [38, 47]], private_save_below_call_sp=[-16, 0],
                **resolve_ranges(proof.rom))


def observed_lifetime(instructions, edges, start, register):
    """Keep the alias on each neutral edge, including the loop back edge."""
    pending, seen, kills = [start], set(), []
    while pending:
        pc = pending.pop()
        if pc in seen:
            continue
        seen.add(pc)
        item = instructions[pc]
        reads, writes = item.regs_access()
        require(register not in reads and match.CS_GRP_CALL not in item.groups and
                match.CS_GRP_INT not in item.groups, f'private output alias observed at {pc:08X}')
        if register in writes:
            require(item.cc in (match.ARM_CC_AL, match.ARM_CC_INVALID), 'conditional alias overwrite')
            kills.append(pc)
        else:
            require(edges[pc], 'private output alias lives at an exit')
            pending.extend(edges[pc])
    return sorted(kills)


def scan_frame(ins, edges):
    block(ins, ROOT, 'push {r4, r5, r6, r7, lr}', 'mov r7, sb', 'mov r6, r8', 'push {r6, r7}',
          'sub sp, #4', 'adds r7, r0, #0', 'lsls r5, r1, #0x18', 'lsrs r5, r5, #0x18',
          'ldrb r6, [r7, #6]', 'mov r8, sp', 'movs r0, #1', 'add r0, sp, r0', 'mov sb, r0',
          'adds r0, r5, #0', 'adds r1, r5, #0', 'movs r2, #0x25', 'bl #0x80c8570',
          'adds r4, r0, #0', 'lsls r4, r4, #0x18', 'lsrs r4, r4, #0x18',
          'adds r0, r5, #0', 'adds r1, r5, #0', 'movs r2, #0x26', 'bl #0x80c8570',
          'lsls r0, r0, #0x18', 'lsrs r0, r0, #0x18', 'mov r1, r8', 'strb r4, [r1]',
          'mov r1, sb', 'strb r0, [r1]', 'ldr r2, [pc, #0x3c]', 'lsls r6, r6, #2',
          'adds r6, r6, r2', 'ldr r6, [r6]', 'mov r1, sp', 'ldrb r3, [r1]', 'cmp r3, r0',
          'bhi #0x80cd352', 'mov r8, r2', 'adds r5, r0, #0')
    # No write to either initialized local, and no call or store, in the scan.
    block(ins, 0x080CD318, 'lsls r4, r3, #3', 'adds r0, r6, r4', 'ldrb r0, [r0, #6]',
          'cmp r0, #0', 'beq #0x80cd348', 'adds r0, r7, #0', 'adds r0, #0x40',
          'adds r0, r0, r3', 'ldrb r2, [r0]', 'movs r1, #0x7f', 'ldrb r0, [r7, #6]',
          'lsls r0, r0, #2', 'add r0, r8', 'ldr r0, [r0]', 'adds r0, r0, r4', 'ands r1, r2',
          'ldrb r0, [r0, #7]', 'cmp r1, r0', 'bhs #0x80cd348', 'movs r0, #0', 'b #0x80cd354')
    block(ins, 0x080CD348, 'adds r0, r3, #1', 'lsls r0, r0, #0x18', 'lsrs r3, r0, #0x18',
          'cmp r3, r5', 'bls #0x80cd318', 'movs r0, #1', 'add sp, #4', 'pop {r3, r4}',
          'mov r8, r3', 'mov sb, r4', 'pop {r4, r5, r6, r7}', 'pop {r1}', 'bx r1')
    live = ((1, 0x080CD310, [0x080CD32A, 0x080CD35E]),
            (8, 0x080CD2FE, [0x080CD314, 0x080CD358]), (9, 0x080CD302, [0x080CD35A]))
    kills = {}
    for reg, start, expected in live:
        killed = observed_lifetime(ins, edges, start, match.ARM_REG_R0 + reg)
        require(killed == expected, 'unexpected output alias lifetime')
        kills[f'r{reg}'] = killed
    return dict(private_frame=[-32, -28], first_store=[0x080CD2FE, -32], last_store=[0x080CD302, -31],
                first_reload=0x080CD30E, last_forwarded_to_r5=0x080CD316, kills_before_read_or_return=kills,
                loop_backedge=[0x080CD350, 0x080CD318], return_instruction=0x080CD360)


def prove(data, address, rom, mapping, index, objects, bindings, ins, edges, calls, refinement):
    expected = dict(calls=[[32, 'func_080C8570'], [48, 'func_080C8570']],
                    data=[[128, 'g_table_0851BA84', 0]], functions=[], switches=[])
    require(address == ROOT and len(data) == 158 and len(ins) == 74 and bindings == expected and
            calls == {ROOT+32: QUERY, ROOT+48: QUERY}, 'two typed category calls and row table required')
    resolver = named.NamedDataBufferProof(rom, mapping, index, objects)
    require(resolver.identities['rom_sha256'] == ROM_SHA256 and resolver.span(ROOT) == data,
            'ability range requires the exact indexed USA image')
    entries, rows = indices(mapping, index)
    for start, size, count in ((ROOT, 158, 74), (QUERY, 1204, 501)):
        record = span_record(start, start+size, entries, rows, rom)
        require(record['instrs'] == count, 'indexed instruction count differs from native CFG')
    names = match.parse_data_symbols(objects)
    require(names.get('g_table_08521A14') == RECORDS and names.get('g_table_0851BA84') == ROWS,
            'named row and category tables required')
    # Keep the existing complete private-frame and register checks; no real
    # buffer is passed. The query and the scan below independently justify the
    # ordinary BLs and the different R1 states reaching the same loop join.
    verified = match.verify_leaf_instructions(data, ROOT, True, calls, buffer_proof=resolver)
    require({i.address for i in verified} == set(ins) and not resolver.dependencies,
            'unexpected reached owner instruction or alias-bearing query argument')
    return dict(schema=named.ABILITY_RANGE_SCHEMA, instructions=len(ins), calls=expected['calls'], runtime_calls=[],
                partition=graph.partition(data, ROOT, refinement, ins, {}), frame=scan_frame(ins, edges),
                category_query=query(resolver), environment=environment_fingerprint(),
                conditions=['The unit, ability-point bytes and selected rows are valid external readable objects. '
                            'Their storage and both ROM tables are separate from the active stack. '
                            'Physical record reads do not establish source-level object sizes.',
                            'A repeating category redirect can leave the caller suspended with its frame live. '
                            'The scan bound and normal-return restoration apply whenever both queries return.'])
