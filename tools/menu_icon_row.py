"""Original menu row, fixed icon streams and the transient decoder output cursor."""
import hashlib
import struct
from pathlib import Path

from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB

BASE = 0x08000000
OWNER = 0x08053E4C
CLAMPED = 0x08054314
DECODE = 0x080CB980
ARCHIVE = 0x083C83FC
SCALAR = 0x08142B28
GRAPHICS = 0x030008B0
NAMES = 0x08526680
CALLS = [(0x24, 'func_080CB980'), (0x2e, 'func_080CB980'), (0x36, 'func_080543CC'),
         (0x40, '__umodsi3'), (0x6a, 'func_08013A88'), (0x74, 'func_0814186C'), (0x9a, 'func_08015110')]
CLAMPED_CALLS = [(0x24, 'func_080CB980'), (0x2e, 'func_080CB980'), (0x38, 'func_08017B68'),
                 (0x44, '__modsi3'), (0x68, 'func_08013A88'), (0x72, 'func_0814186C'), (0x98, 'func_08015110')]
DATA = [(0xb0, 'data_030008B0', GRAPHICS), (0xb4, 'g_table_08526680', NAMES)]
CLAMPED_DATA = [(0xac, 'data_030008B0', GRAPHICS), (0xb0, 'g_table_08526680', NAMES)]
# Complete original-USA components. The compressed stream checks below use
# the exact decoder instructions in these spans, including the global cursor.
COMPONENTS = {
    OWNER: (188, 78, '837b8720d4d17a551db5b565b05bc3c02e4d476e54719c1699f26cc230226fec'),
    CLAMPED: (184, 77, '802677cf9538fe5cd6423bbca200e5b35fbd23c2bd964123938d6e9048532515'),
    0x08017B68: (52, 26, '258720036f74f142348aca5f219a0728d5665f3849c7449b90fe7535e17d1145'),
    DECODE: (28, 10, 'd49c4da57b88595e63906e6e76e287fb12f7387182c4d95cbedfc143f7920388'),
    0x08005318: (188, 87, 'a07f4430fc44968f569aef82b6965333cae3aea17fd2e45d1b937a261676f92d'),
    0x080051C4: (340, 153, '1afa2852712652f49790f372379027db64585c1ba112118f2d6ec1c6a9d1768d'),
    0x080543CC: (16, 8, '4e3f3270f03142ad50ae1b8f32edc6b21b62b3d31c93dd5d138170cf264c102d'),
    0x08013A88: (34, 16, '207bd64cd5b66c49b2509cbf95946deafc8c3929943a1ddf3116f81f51adaab0'),
}
CONTRACT = (
    "The known caller supplies the live tile run and text context, and a readable incoming fifth word. "
    "The caller-owned output has disjoint aligned writable storage for the icon, clear and rendered name. "
    "For a nonempty clear, width is at least 3; width 2 programs zero and width 0 or 1 wraps the halfword count. "
    "The adjusted name index must select a readable string pointer and the renderer must accept its contents. "
    "The BIOS premises are synchronous CpuSet halfword copy and CpuFastSet word fill on BIOS-accessible, "
    "disjoint storage. The decoder owns its three IWRAM globals exclusively while decoding. "
    "It leaves the icon's address in 03002BB8 and length 128 in 03002BB0. After the frame expires, "
    "no consumer may use the retained local address before it is reinitialized. The final text renderer "
    "is an ordinary returning ABI boundary under the caller's memory, nonaliasing and lifetime premises."
)


def require(condition, detail):
    if not condition:
        raise ValueError('menu icon row: ' + detail)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def environment_fingerprint():
    import multiple_switch_native_profile as multiple
    import runtime_summary_profile as runtime
    import small_local_copy_binding_profile as typed
    result = multiple.environment_fingerprint()
    for path in (Path(__file__), Path(runtime.__file__), Path(typed.__file__)):
        result['producers'][path.name] = sha(path.read_bytes())
    return result


def seq(rom, start, size, expected):
    data = rom[start-BASE:start-BASE+size]
    decoded = list(Cs(CS_ARCH_ARM, CS_MODE_THUMB).disasm(data, start))
    require(sum(i.size for i in decoded) == size and
            [i.mnemonic + ' ' + i.op_str for i in decoded] == expected, f'original instructions at {start:08X}')


def decode_icon(rom, number):
    require(number in (393, 394), 'icon outside the menu pair')
    return _decode_icon(rom, number)


def _decode_icon(rom, number):
    """Execute the two reachable mode-0 token forms with the original bounds."""
    table = ARCHIVE - BASE
    total, dictionary = struct.unpack_from('>HI', rom, table+2)
    require(0 <= number < total, 'icon or archive count changed')
    dictionary += table
    require(rom[dictionary:dictionary+4] == bytes.fromhex('00050080'), 'mode, dictionary bits or expected length')
    start, end = struct.unpack_from('>II', rom, table+8+4*number)
    cursor, limit = table+start, table+end
    require(table < cursor < limit <= dictionary < len(rom), 'compressed stream extent')
    output = bytearray()
    while len(output) < 128:
        require(cursor < limit, 'compressed icon ends before the 128-byte output')
        token = rom[cursor]
        cursor += 1
        if token & 0x80:
            count = (token & 127) + 1
            require(cursor + count <= limit, 'literal token exceeds compressed stream')
            piece = rom[cursor:cursor+count]
            cursor += count
        else:
            require(cursor < limit, 'incomplete dictionary token')
            count = (token >> 2) + 3
            offset = ((token << 8) | rom[cursor]) & 1023
            cursor += 1
            first = dictionary+4+offset
            piece = rom[first:first+count]
            require(len(piece) == count, 'dictionary token outside readable ROM')
        require(len(output) + count <= 128, 'decoder would overwrite the end of the icon')
        output.extend(piece)
    require(cursor == limit, 'unowned bytes after the icon stream')
    return bytes(output)


def native_parts(rom, mapping, index, address, expected_calls):
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    from software_double_profile import indices, span_record
    indexed, rows = indices(mapping, index)
    records = {}
    other_row = (OWNER, 0x080543CC) if address == CLAMPED else (CLAMPED, 0x08017B68)
    for start, (size, count, digest) in COMPONENTS.items():
        if start in other_row:
            continue
        record = span_record(start, start+size, indexed, rows, rom)
        raw = rom[start-BASE:start-BASE+size]
        require(record['instrs'] == count and sha(raw) == digest, f'component bytes or count at {start:08X}')
        refine = owner.refine(raw, start, mapping)
        ins, edges, branches, calls, words = graph.graph(raw, start, refine)
        require(len(ins) == count and not branches and not words, 'component CFG or local switch changed')
        partition = graph.partition(raw, start, refine, ins, words)
        if start == address:
            require(all(target > site for site, targets in edges.items() for target in targets),
                    'menu row contains a cycle')
            require(calls == expected_calls, 'owner call destinations')
            pools = [(w['address']-address, w['value'], [site-address for site in w['load_sites']])
                     for w in partition['words']]
            expected_pools = ([(0xa8,393,[0x2a]), (0xac,GRAPHICS,[0x4e]), (0xb0,NAMES,[0x82]), (0xb4,2500,[0x86])]
                              if address == CLAMPED else
                              [(0xac,393,[0x2a]), (0xb0,GRAPHICS,[0x50]), (0xb4,NAMES,[0x84]), (0xb8,2500,[0x88])])
            require(pools == expected_pools, 'icon/text pool load sites')
            stack_ops = [site-address for site, i in sorted(ins.items()) if 'sp' in i.op_str or i.mnemonic in ('push', 'pop')]
            tail = [0x6c,0x90,0x9c,0x9e,0xa2,0xa4] if address == CLAMPED else [0x6e,0x92,0x9e,0xa0,0xa4,0xa6]
            require(stack_ops == [0,4,6,12,0x22,0x2c]+tail, 'unclassified caller stack operation')
        records[f'{start:08X}'] = dict(size=size, instructions=count, sha256=digest)
    for addr, swi in ((0x08141868, 12), (0x0814186C, 11)):
        require(span_record(addr, addr+4, indexed, rows, rom)['instrs'] == 2 and
                rom[addr-BASE:addr-BASE+4] == bytes([swi, 0xdf, 0x70, 0x47]), 'original BIOS veneer')
    return records


def five_rows_context(rom):
    seq(rom, OWNER, 14, ['push {r4, r5, r6, r7, lr}', 'mov r7, r8', 'push {r7}', 'sub sp, #0x84',
        'adds r4, r0, #0', 'mov r8, r1', 'ldr r0, [sp, #0x9c]'])
    seq(rom, OWNER+0x9e, 12, ['add sp, #0x84', 'pop {r3}', 'mov r8, r3',
        'pop {r4, r5, r6, r7}', 'pop {r0}', 'bx r0'])
    seq(rom, OWNER+0x1a, 24, ['cmp r5, #0x55', 'bls #0x8053e76', 'movs r1, #0xc5',
        'lsls r1, r1, #1', 'add r0, sp, #4', 'bl #0x80cb980', 'b #0x8053e7e',
        'ldr r1, [pc, #0x80]', 'add r0, sp, #4', 'bl #0x80cb980'])
    seq(rom, OWNER+0x32, 28, ['adds r0, r4, #0', 'adds r1, r6, #0', 'bl #0x80543cc',
        'lsls r0, r0, #0x18', 'lsrs r0, r0, #0x18', 'movs r1, #5', 'bl #0x8142b28',
        'lsls r0, r0, #0x10', 'lsrs r0, r0, #0x10', 'ldrb r1, [r4, #0x15]',
        'lsls r2, r1, #1', 'muls r0, r2, r0'])
    seq(rom, OWNER+0x4e, 32, ['lsls r0, r0, #0x10', 'ldr r2, [pc, #0x5c]', 'lsrs r0, r0, #0x10',
        'ldrh r4, [r4, #0x1c]', 'adds r0, r0, r4', 'lsls r0, r0, #5', 'ldr r4, [r2, #0x10]',
        'adds r4, r4, r0', 'adds r6, r4, #0', 'adds r6, #0x80', 'subs r1, #2',
        'lsls r1, r1, #0x11', 'lsrs r1, r1, #0x10', 'adds r0, r6, #0', 'bl #0x8013a88'])
    seq(rom, OWNER+0x78, 24, ['adds r0, r5, #0', 'cmp r5, #0x55', 'bls #0x8053ece',
        'adds r0, r5, #0', 'subs r0, #0x55', 'lsls r0, r0, #0x10', 'ldr r1, [pc, #0x2c]',
        'lsrs r0, r0, #0xe', 'ldr r2, [pc, #0x2c]', 'adds r0, r0, r2', 'adds r0, r0, r1', 'ldr r2, [r0]'])
    seq(rom, OWNER+0x6e, 10, ['add r0, sp, #4', 'adds r1, r4, #0', 'movs r2, #0x40', 'bl #0x814186c'])
    seq(rom, OWNER+0x90, 14, ['movs r0, #1', 'str r0, [sp]', 'mov r0, r8', 'adds r1, r6, #0',
        'adds r3, r7, #0', 'bl #0x8015110'])
    seq(rom, 0x0805341c, 12, ['ldrh r2, [r0]', 'str r3, [sp]', 'adds r0, r6, #0',
        'adds r3, r5, #0', 'bl #0x8053e4c'])


def clamped_context(rom):
    seq(rom, CLAMPED, 36, ['push {r4, r5, r6, r7, lr}', 'mov r7, r8', 'push {r7}', 'sub sp, #0x84',
        'adds r4, r0, #0', 'mov r8, r1', 'ldr r0, [sp, #0x9c]', 'lsls r2, r2, #0x10',
        'lsrs r6, r2, #0x10', 'lsls r3, r3, #0x10', 'lsrs r5, r3, #0x10', 'lsls r0, r0, #0x18',
        'lsrs r7, r0, #0x18', 'cmp r5, #0x55', 'bls #0x805433e', 'movs r1, #0xc5',
        'lsls r1, r1, #1', 'add r0, sp, #4'])
    seq(rom, CLAMPED+0x24, 14, ['bl #0x80cb980', 'b #0x8054346', 'ldr r1, [pc, #0x7c]',
        'add r0, sp, #4', 'bl #0x80cb980'])
    seq(rom, CLAMPED+0x32, 28, ['lsls r1, r6, #0x18', 'asrs r1, r1, #0x18', 'adds r0, r4, #0',
        'bl #0x8017b68', 'lsls r0, r0, #0x10', 'lsrs r0, r0, #0x10', 'ldrb r1, [r4, #0x16]',
        'adds r1, #1', 'bl #0x8142950', 'ldrb r1, [r4, #0x15]', 'muls r0, r1, r0', 'lsls r0, r0, #0x11'])
    seq(rom, CLAMPED+0x4e, 30, ['ldr r2, [pc, #0x5c]', 'lsrs r0, r0, #0x10', 'ldrh r4, [r4, #0x1c]',
        'adds r0, r0, r4', 'lsls r0, r0, #5', 'ldr r4, [r2, #0x10]', 'adds r4, r4, r0',
        'adds r6, r4, #0', 'adds r6, #0x80', 'subs r1, #2', 'lsls r1, r1, #0x11', 'lsrs r1, r1, #0x10',
        'adds r0, r6, #0', 'bl #0x8013a88'])
    seq(rom, CLAMPED+0x6c, 10, ['add r0, sp, #4', 'adds r1, r4, #0', 'movs r2, #0x40', 'bl #0x814186c'])
    seq(rom, CLAMPED+0x76, 24, ['adds r0, r5, #0', 'cmp r5, #0x55', 'bls #0x8054394',
        'adds r0, r5, #0', 'subs r0, #0x55', 'lsls r0, r0, #0x10', 'ldr r1, [pc, #0x2c]',
        'lsrs r0, r0, #0xe', 'ldr r2, [pc, #0x2c]', 'adds r0, r0, r2', 'adds r0, r0, r1', 'ldr r2, [r0]'])
    seq(rom, CLAMPED+0x8e, 26, ['movs r0, #1', 'str r0, [sp]', 'mov r0, r8', 'adds r1, r6, #0',
        'adds r3, r7, #0', 'bl #0x8015110', 'add sp, #0x84', 'pop {r3}', 'mov r8, r3',
        'pop {r4, r5, r6, r7}', 'pop {r0}', 'bx r0'])
    seq(rom, 0x080539e0, 20, ['adds r4, r6, #0', 'adds r4, #0x2c', 'movs r0, #5', 'str r0, [sp]',
        'adds r0, r4, #0', 'adds r1, r5, #0', 'movs r2, #0', 'mov r3, sb', 'bl #0x8054314'])
    seq(rom, 0x08017b68, 52, ['push {r4, lr}', 'adds r3, r0, #0', 'lsls r1, r1, #0x18',
        'asrs r1, r1, #0x18', 'ldrh r0, [r3, #0x1a]', 'adds r1, r1, r0', 'lsls r1, r1, #0x10',
        'asrs r2, r1, #0x10', 'cmp r2, #0', 'bge #0x8017b80', 'movs r0, #0', 'b #0x8017b96',
        'movs r4, #0x18', 'ldrsh r0, [r3, r4]', 'subs r0, #1', 'cmp r2, r0', 'bgt #0x8017b8e',
        'lsrs r0, r1, #0x10', 'b #0x8017b96', 'ldrh r0, [r3, #0x18]', 'subs r0, #1',
        'lsls r0, r0, #0x10', 'lsrs r0, r0, #0x10', 'pop {r4}', 'pop {r1}', 'bx r1'])


def shared_context(rom):
    seq(rom, 0x0801511c, 12, ['adds r6, r0, #0', 'mov sl, r2', 'ldr r0, [sp, #0x50]',
        'lsls r3, r3, #0x18', 'lsrs r4, r3, #0x18', 'lsls r0, r0, #0x18'])
    require(struct.unpack_from('<I', rom, 0xcb998)[0] == ARCHIVE and
            struct.unpack_from('<III', rom, 0x53c8) == (0x03002bb8,0x03002bb4,0x03002bb0),
            'archive or decoder global identities')
    # This append routine would dereference the former frame if invoked without a reset.
    seq(rom, 0x08005408, 18, ['ldr r3, [pc, #0x10]', 'ldr r2, [r3]', 'ldr r1, [pc, #0x10]',
        'ldr r1, [r1]', 'adds r1, r1, r2', 'strb r0, [r1]', 'adds r2, #1', 'str r2, [r3]', 'bx lr'])
    require(struct.unpack_from('<II', rom, 0x541c) == (0x03002bb0,0x03002bb8), 'append cursor globals')


def verify_objects(raw, linked_file, address, rom, mapping, index, bindings, objects, calls, data, size):
    import match
    import owner_admission_profile as owner
    import runtime_summary_profile as runtime
    import small_local_copy_binding_profile as typed
    require(all(type(v) is bytes for v in (raw, linked_file, rom, mapping, index, objects)),
            'complete original input bytes required')
    original, linked = match.elf_image(raw), match.elf_image(linked_file)
    require(original['type'] == 1 and linked['type'] == 2 and not linked['relocations'], 'ELF roles')
    checked, targets = owner.original_bindings(original,address,rom,mapping,objects,selector=runtime.SELECTOR,index=index)
    expect = dict(calls=[list(row) for row in calls], data=[[offset,name,0] for offset,name,_ in data],
                  switches=[], functions=[])
    expect_targets = {name: (runtime.ENTRIES[name] if name in runtime.ENTRIES else int(name[5:],16), False)
                      for _,name in calls}
    expect_targets.update({name: (addr,True) for _,name,addr in data})
    require(checked == expect == bindings and targets == expect_targets, 'original ELF relocation roles')
    for name in targets:
        symbol, = [s for s in original['symbols'] if s['name'] == name]
        require((symbol['bind'], symbol['type'], symbol['size'], symbol['section'], symbol['value']) == (1,0,0,0,0),
                'expected an actual unique undefined global')
    for image in (original, linked):
        match.allocated_text_only(image)
        section = image['sections'][image['text_index']]
        sym, offset = match.function_record(image,f'func_{address:08X}',address,True)
        require(not offset and section[1:4] == (1,6,0 if image is original else address) and
                sym['size'] == len(image['text']) == size, 'canonical complete ELF text')
    typed.check_linked(linked,address,targets)
    body = linked['text']
    owner.validate_span(body,address,rom,mapping,index)
    rebuilt = bytearray(original['text'])
    for site,_ in calls:
        require(rebuilt[site:site+4] == bytes.fromhex('fff7feff'), 'nonzero compiler call addend')
        rebuilt[site:site+4] = body[site:site+4]
    for site,_,addr in data:
        require(rebuilt[site:site+4] == bytes(4), 'nonzero object addend')
        struct.pack_into('<I',rebuilt,site,addr)
    require(rebuilt == body, 'mismatch outside original/linked relocations')
    return targets


def verify_original(raw, linked_file, address, rom, mapping, index, bindings, manifest=None, *, objects):
    import owner_admission_profile as owner
    import runtime_summary_profile as runtime
    require(address in (OWNER, CLAMPED), 'unexpected menu row')
    calls = CLAMPED_CALLS if address == CLAMPED else CALLS
    data = CLAMPED_DATA if address == CLAMPED else DATA
    size, count, _ = COMPONENTS[address]
    targets = verify_objects(raw, linked_file, address, rom, mapping, index, bindings, objects, calls, data, size)
    records = native_parts(rom,mapping,index,address,{address+site: targets[name][0] for site,name in calls})
    (clamped_context if address == CLAMPED else five_rows_context)(rom)
    shared_context(rom)
    closure = runtime.RuntimeSummaries(rom,mapping,index)
    site, name = next((site,name) for site,name in calls if name in runtime.ENTRIES)
    closure.observe(address+site, runtime.ENTRIES[name])
    icons = {str(number):sha(decode_icon(rom,number)) for number in (393,394)}
    result = dict(profile=runtime.SCHEMA, selector=runtime.SELECTOR, bindings=bindings,
        environment=environment_fingerprint(), original_ELF_sha256=sha(raw), linked_ELF_sha256=sha(linked_file),
        components=records, runtime=closure.manifest(), bios=dict(CpuSet_halfwords=64,
        CpuFastSet_control='0x01000000 | ((u16)((width - 2) * 2) << 3)'),
        frame=dict(size=156, icon_offset=4, icon_bytes=128, outgoing_word=0, incoming_style_offset=156),
        icon_sha256=icons, retained_output_word=0x03002bb8, conditional_append=0x08005408,
        text_table=NAMES, first_name_index=625, contract=CONTRACT)
    if address == CLAMPED:
        result['clamped_row'] = dict(row_bits=8, signed_row=True, position_offset=26, count_offset=24,
            signed_comparison_bits=16, height_offset=22, divisor_min=1, divisor_max=256,
            empty_count_upper_result=65535, tile_offset_bits=16, actual_call=0x080539f0)
    if manifest is not None:
        require(owner.text(result) == owner.text(manifest), 'cached evidence differs from original replay')
    return result,count
