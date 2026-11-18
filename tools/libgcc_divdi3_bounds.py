"""Prove the high-byte normalization paths on the three original Thumb table reads."""


def table_reads(instructions, edges, partition):
    from capstone.arm import ARM_OP_MEM, ARM_REG_PC, ARM_REG_SP
    from libgcc_divdi3 import ADDRESS, TABLE, TABLE_WORDS, require
    literals = {site: (word['address'], word['value']) for word in partition['words'] for site in word['load_sites']}
    loads = {site for site, ins in instructions.items() if ins.mnemonic.startswith('ldr') and
             any(op.type == ARM_OP_MEM and op.mem.base not in (ARM_REG_PC, ARM_REG_SP) for op in ins.operands)}
    records = []
    for alias, start, high, merge, reg, index, shift, offset in (
            (0x081422CC, 0x081422DE, 0x081422F4, 0x081422FE, 'r7', 'r2', 'r1', TABLE_WORDS[0]),
            (0x081423C2, 0x081423C4, 0x081423D8, 0x081423E2, 'r7', 'r1', 'r2', TABLE_WORDS[1]),
            (0x08142534, 0x08142536, 0x0814254C, 0x08142556, 'r6', 'r1', 'r2', TABLE_WORDS[2])):
        region = set()

        def instruction(site, mnemonic, operands, successors=None):
            ins = instructions[site]
            require(ins.mnemonic == mnemonic and ins.op_str == operands and
                    edges[site] == ((site+2,) if successors is None else successors), 'original unsigned table-index flow')
            region.add(site)

        def literal(site, value):
            ins = instructions[site]
            require(ins.mnemonic == 'ldr' and ins.op_str.startswith('r0, [pc, ') and
                    literals[site][1] == value, 'the original bound and base literals')
            instruction(site, 'ldr', ins.op_str)

        def branch(site, mnemonic, dest):
            instruction(site, mnemonic, f'#{dest:#x}', (dest,) if mnemonic == 'b' else (dest, site+2))

        if alias != start-2:
            # The first path compares a copy in R7, then shifts the original R2.
            instruction(alias, 'adds', 'r7, r2, #0')
            instruction(alias+2, 'adds', 'r6, r3, #0')
            instruction(alias+4, 'mov', 'sl, r4')
            instruction(alias+6, 'mov', 'r8, r5')
            instruction(alias+8, 'cmp', 'r6, #0')
            branch(alias+10, 'beq', alias+14)
            branch(alias+12, 'b', 0x08142528)
            instruction(alias+14, 'cmp', 'r7, r8')
            branch(alias+16, 'bls', 0x081423B4)
        else:
            instruction(alias, 'adds', f'{index}, {reg}, #0')
        literal(start, 0xffff)
        instruction(start+2, 'cmp', f'{reg}, r0')
        branch(start+4, 'bhi', high)
        instruction(start+6, 'movs', f'{shift}, #0')
        instruction(start+8, 'cmp', f'{reg}, #0xff')
        branch(start+10, 'bls', merge)
        instruction(start+12, 'movs', f'{shift}, #8')
        branch(start+14, 'b', merge)
        literal(high, 0xffffff)
        instruction(high+2, 'movs', f'{shift}, #0x18')
        instruction(high+4, 'cmp', f'{reg}, r0')
        branch(high+6, 'bhi', merge)
        instruction(high+8, 'movs', f'{shift}, #0x10')
        literal(merge, TABLE)
        require(literals[merge][0] == ADDRESS+offset, 'the linked field for this specific indexed read')
        instruction(merge+2, 'lsrs', f'{index}, {shift}')
        instruction(merge+4, 'adds', f'r0, {index}, r0')
        instruction(merge+6, 'ldrb', 'r0, [r0]')
        require(all(p in region or not (set(out) & (region-{alias})) for p, out in edges.items()),
                'no entry between divisor copy, unsigned classification, shift and read')
        records.append(dict(site=merge+6, copy=alias, table_word=ADDRESS+offset, width=1,
                            minimum=TABLE, maximum=TABLE+255))
    require(loads == {r['site'] for r in records}, 'all non-frame, non-literal loads accounted for')
    # BHI/BLS partition all 32-bit inputs at 0xff, 0xffff and 0xffffff.
    # Dividing each interval by its selected power of two leaves at most 255.
    return dict(reads=records, unsigned_ranges_and_shifts=[
        [0, 255, 0], [256, 65535, 8], [65536, 16777215, 16], [16777216, 4294967295, 24]])
