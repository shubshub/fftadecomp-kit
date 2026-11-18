"""Original stat-drain switch, nonzero ROM divisors and preserved getter result ABI."""
import hashlib
import struct

from capstone.arm import ARM_INS_B, ARM_REG_R4, ARM_REG_SP

SELECTOR = 'stat-drain-divisor-switch-v1'
SCHEMA = 'elf-symbol-thumb-' + SELECTOR
BASE = 0x08000000
ADDRESS, END = 0x08128C3C, 0x08128E3E
TABLE, NAME = 0x083A8260, 'data_083A8260'
VALUES = (10, 5, 2, 1, 3, 5, 10, 20)
DIV, UDIV = 0x081426B8, 0x08142AB0
GETTER, LOOKUP = 0x080C92F0, 0x080C8570
GETTER_SITES = (0x50, 0x96, 0xDC, 0x114, 0x14C, 0x184)
STATS = (0x17, 0x18, 0x1A, 0x1B, 0x1C, 0x1D)
SWITCH = [[0x2C + i*4, target] for i, target in enumerate(
    (0x30, 0x4C, 0x92, 0xD8, 0x110, 0x148, 0x180, 0x1B8))]
TARGETS = {NAME: (TABLE, True), 'func_080C92F0': (GETTER, False),
           '__udivsi3': (UDIV, False), '__divsi3': (DIV, False)}
HASHES = {
    ADDRESS: 'be2a80f6e99d48319262c8305a89da1692d78b9e23303abb4b24b82ff3cf4fee',
    GETTER: '75875c8fb568e97c7d96eee0e6bf7a48f39a75601d60204372f4ad19cd0a4c25',
    LOOKUP: '1fa2f1bfd1d7974ce8a3387acaa6b2b301d42c79475938e5f6f6cc7cd8a18057',
}


def require(condition, message):
    if not condition:
        raise ValueError('stat-drain switch: ' + message)


def check_bindings(address, bindings):
    calls = []
    for offset in GETTER_SITES:
        calls.extend(([offset, 'func_080C92F0'], [offset+6, '__udivsi3']))
    calls.append([0x1BC, '__divsi3'])
    require(address == ADDRESS and bindings == dict(calls=calls, data=[[0x28, NAME, 0]],
            functions=[], switches=SWITCH), 'original owner, object, switch or call roles differ')


def check_original(image, address, bindings, targets):
    import match
    check_bindings(address, bindings)
    require(targets == TARGETS, 'original ELF targets differ')
    symbol, _ = match.function_record(image, 'func_08128C3C', ADDRESS, True)
    require(symbol['size'] == END-ADDRESS and image['text'][symbol['size']:] == b'\xc0\x46',
            'original function or external alignment differs')
    # Native assembler declares all four external bindings as zero-sized STT_NOTYPE.
    for table, symbols in image['symbol_tables'].items():
        raw = image['section_data'][table]
        for number, row in enumerate(symbols):
            if row['name'] in targets:
                require(row['type'] == 0 and row['size'] == 0 and raw[16*number + 13] == 0,
                        'original external symbol type, size or visibility differs')


def instructions_at(instructions, site, halfwords):
    for word in halfwords:
        require(site in instructions and bytes(instructions[site].bytes) == struct.pack('<H', word),
                f'divisor producer or use at {site:08X} differs')
        site += 2


def getter_frames(rom, mapping, index, objects):
    import match
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    import local_long_branch_profile as frame

    def span(start, end):
        body = rom[start-BASE:end-BASE]
        owner.validate_span(body, start, rom, mapping, index)
        require(hashlib.sha256(body).hexdigest() == HASHES[start], 'original getter dependency differs')
        return body

    wrapper = span(GETTER, 0x080C9314)
    seq, edges, jumps, calls, words = graph.graph(wrapper, GETTER, owner.refine(wrapper, GETTER, mapping))
    require(not jumps and not words and calls == {0x080C930C: LOOKUP} and
            all(ARM_REG_R4 not in i.regs_access()[1] for i in seq.values()), 'getter can clobber R4')
    outer = frame.prove_frame(seq, edges, GETTER, {}, calls, stack_aliases=True)
    # The original lookup's backward guard/record redirect loops are supported by
    # its dedicated read-only verifier. Preserve that verifier's conditional return.
    lookup = span(LOOKUP, 0x080C8A24)
    name, table = 'g_table_08521A14', 0x08521A14
    targets = {p: struct.unpack_from('<I', lookup, p)[0]-LOOKUP for p in range(44, 240, 4)}
    switch = match.preloaded_switch_layout(lookup, LOOKUP, targets, {40: (name, table)})
    leaf, flow = match.verify_preloaded_switches(lookup, LOOKUP, rom, mapping, objects,
            dict(calls=[], data=[[40, name, 0]], switch=switch))
    stack = [(i.address, i.mnemonic, i.op_str) for i in leaf
             if ARM_REG_SP in i.regs_access()[1] or i.mnemonic in ('bx', 'push', 'pop')]
    require(len(leaf) == 501 and stack == [
        (LOOKUP, 'push', '{r4, r5, r6, lr}'), (0x080C8A1E, 'pop', '{r4, r5, r6}'),
        (0x080C8A20, 'pop', '{r1}'), (0x080C8A22, 'bx', 'r1')], 'lookup saved divisor or exit differs')
    # The other branches in this verified preloaded graph are direct Thumb B
    # instructions or dispatch to the checked table. Neither may jump over a pop
    # or push the save block a second time.
    forbidden = {LOOKUP, 0x080C8A20, 0x080C8A22}
    branch_targets = {i.operands[0].imm for i in leaf if i.id == ARM_INS_B}
    dispatch_targets = {LOOKUP + target for site, target in targets.items() if site != 44}
    require(forbidden.isdisjoint(branch_targets | dispatch_targets), 'lookup bypasses its saving epilogue')
    return dict(wrapper=[GETTER, HASHES[GETTER]], frame=outer,
                lookup=[LOOKUP, HASHES[LOOKUP]], lookup_instructions=len(leaf), lookup_flow=flow,
                saved_and_restored_r4=stack, unconditional_termination=False)


def prove(data, address, rom, mapping, index, objects, bindings):
    import match
    import one_object_mixed_switch_inventory as inventory
    import owner_graph_profile as graph
    check_bindings(address, bindings)
    require(len(data) == END-ADDRESS and match.parse_data_symbols(objects).get(NAME) == TABLE,
            'owner extent or named divisor object differs')
    refinement = inventory.refine(data, address, mapping)
    ins, edges, _, calls, _ = graph.graph(data, address, refinement, one_object_word_switch=True)
    original_names = {address+p: name for p, name in bindings['calls']}
    structural, verified = inventory.verify(data, address, rom, mapping, index, calls,
                                            original_names, selector=inventory.SELECTOR)
    require(structural['object_word'] == dict(address=address+0x28, value=TABLE,
                load_sites=[address+10], switch_word=False) and
            refinement['word_switches'][0]['relocations'] == bindings['switches'],
            'reached ROM word or guarded local table differs from original ELF roles')
    # Every route into the dispatcher first loads key byte +2, isolates exactly
    # its low three bits, then reads r4 from base+index. No prior edge can bypass it.
    instructions_at(ins, address, (0xB530, 0x0609, 0x0E0A, 0x6885, 0x2300, 0x4907,
                                    0x68C0, 0x7880, 0x0740, 0x0F40, 0x1840, 0x7804))
    for pc in range(address, address+24, 2):
        require(list(edges[pc]) == [pc+2], 'key extraction is not a dominating entry prefix')
    values = tuple(rom[TABLE-BASE:TABLE-BASE+8])
    require(values == VALUES and all(values), 'divisor table differs or contains zero')
    r4_writes = {pc for pc, i in ins.items() if ARM_REG_R4 in i.regs_access()[1]}
    require(r4_writes == {address+22, END-6}, 'saved divisor is overwritten before a use')
    predecessors = {pc: set() for pc in ins}
    for source, successors in edges.items():
        for target in successors:
            predecessors[target].add(source)
    uses = []
    for offset, stat in zip(GETTER_SITES, STATS):
        pc = address + offset
        instructions_at(ins, pc-4, (0x1C28, 0x2100|stat))  # r0=unit, r1=stat
        instructions_at(ins, pc+4, (0x1C21,))             # r1=r4 after getter
        require(predecessors[pc-2] == {pc-4} and predecessors[pc] == {pc-2} and
                predecessors[pc+4] == {pc} and predecessors[pc+6] == {pc+4},
                'unsigned divide lacks a returning getter and divisor transfer')
        uses.append([pc+6, 'unsigned32', stat])
    instructions_at(ins, address+0x1B8, (0x200A, 0x1C21))  # signed numerator ten, positive divisor
    require(predecessors[address+0x1BA] == {address+0x1B8} and
            predecessors[address+0x1BC] == {address+0x1BA}, 'side entry into signed division')
    uses.append([address+0x1BC, 'signed32', 10])
    getters = getter_frames(rom, mapping, index, objects)
    require(hashlib.sha256(data).hexdigest() == HASHES[ADDRESS], 'original USA stat-drain body differs')
    return dict(schema=SCHEMA, bindings=bindings, structural_inventory=structural, getter=getters,
                divisor=dict(key_offset=2, index_mask=7, base=TABLE, values=list(values),
                    range=[min(values), max(values)], uses=uses, signed_numerator=10,
                    division_by_zero=False, signed_overflow=False),
                conditions=['valid state, unit and key pointers; writable fields and a private stack',
                            'the native getter may redirect indefinitely; division follows only a return']), verified
