"""Original menu list callback, two far epilogue jumps and two adjacent byte results."""
from hashlib import sha256
import struct

ADDRESS, END = 0x08052870, 0x080530A0
OUTPUT, INSTALLER, REGISTER, RUNNER, THUNK = 0x08053568, 0x08051DB4, 0x08006ADC, 0x080069F4, 0x0814224C
OBJECTS = {0x2F0: ('data_08422764', 0x08422764), 0x2F4: ('data_0841CE18', 0x0841CE18)}
FUNCTIONS = {0x2E4: ('func_08051084', 0x08051085), 0x5B4: ('func_080531F0', 0x080531F1),
             0x82C: ('func_08051DB4', 0x08051DB5)}
PINS = {
    ADDRESS: (END, 805, '17566c70ba3a91800a46a77743949bbfd092886e9e4ab3aca2a0fbc427220745'),
    INSTALLER: (0x080524C0, 685, '188de87274d5b94bc173f0a2e05602f793ee0ba1f77276f9b149daac7ffc6ca7'),
    REGISTER: (0x08006AF8, 14, 'adfcb3744861f340a5e92fd533d4d2906eae4c1878541e53f574283adcc0814e'),
    RUNNER: (0x08006A7C, 66, '870059083b005c705d9ed3a284ac753f0cb32cb52f1110640bd37b4b31d8e726'),
    OUTPUT: (0x080535BC, 34, '870b32ec0bea5798366dcce0313d164a66eda37d458c570f117e1b3fd9773eaa'),
    0x080CCA20: (0x080CCA54, 22, '4d971cabd9c535c92dac4a3264594ee0e7de7475898554caed890a44dc187b40'),
    0x0802B3A8: (0x0802B3D4, 22, '5701cbef1d6c4e849af1d8fd49ad6001b6040d8a001edc4d514b4039c54b75d0'),
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def require_pinned_leaf(rom, mapping, target, registers):
    """The loop replay trusts `registers` (capstone ids) across calls to `target`: check that premise
    in the pinned bytes. `target` must be a PINS span whose reached instructions make no call and write
    none of `registers`."""
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    from match import ROM_BASE
    require(target in PINS, f'loop replay trusts the unpinned callee {target:08X}')
    end, count, digest = PINS[target]
    body = rom[target-ROM_BASE:end-ROM_BASE]
    require(sha256(body).hexdigest() == digest, f'trusted callee {target:08X} differs from its pin')
    ins, _, _, calls, _ = graph.graph(body, target, owner.refine(body, target, mapping))
    require(len(ins) == count and not calls, f'trusted callee {target:08X} is not a pinned leaf')
    written = {register for instruction in ins.values() for register in instruction.regs_access()[1]}
    require(not written & set(registers), f'trusted callee {target:08X} writes a register the replay trusts')


class MenuListFrame:
    BRANCHES = {0x0805289A: 0x08053084, 0x080528B0: 0x08053084}

    def __init__(self, data, rom, mapping, index, objects, data_relocations, function_relocations):
        from match import ROM_BASE, parse_data_symbols
        from software_double_profile import indices, span_record
        entries, rows = indices(mapping, index)
        self.rom, self.mapping, self.evidence = rom, mapping, None
        require(data == rom[ADDRESS-ROM_BASE:END-ROM_BASE] and function_relocations == FUNCTIONS and
                all(data_relocations.get(off) == pair for off, pair in OBJECTS.items()),
                'menu list owner, animation resources or three callback bindings differ')
        for address, (end, count, digest) in PINS.items():
            row = span_record(address, end, entries, rows, rom)
            require(row['instrs'] == count and sha256(rom[address-ROM_BASE:end-ROM_BASE]).hexdigest() == digest,
                    f'menu list dependency differs at {address:08X}')
        symbols = parse_data_symbols(objects)
        require(all(symbols.get(name) == value for name, value in OBJECTS.values()) and
                struct.unpack_from('<III', rom, 0x5247C) == (0x0200F428, 0xCD8, ADDRESS|1) and
                struct.unpack_from('<11I', rom, 0x422764) == tuple(44+28*i for i in range(10)) + (300,) and
                struct.unpack_from('<IIH', rom, 0x41CE18) == (8, 48, 9) and
                rom[THUNK-ROM_BASE:THUNK-ROM_BASE+2] == bytes.fromhex('1047'),
                'menu runner, canonical callback thunk or animation role differs')

    def finish(self, data, address, ins, edges, branches, calls, buffers):
        import match
        from local_long_branch_profile import prove_frame, record
        from ability_range_local_bytes import block
        require(address == ADDRESS and len(ins) == 805 and len(calls) == 74 and branches == self.BRANCHES and
                buffers.rom == self.rom and buffers.span(address) == data and
                calls.get(0x08052AD0) == OUTPUT, 'menu list graph or byte-output call differs')
        block(ins, 0x08052AC4, 'bl #0x80535bc', 'mov r4, sp', 'adds r4, #0x1d', 'add r0, sp, #0x1c',
              'adds r1, r4, #0', 'bl #0x8053568')
        block(ins, 0x08052ADC, 'add r2, sp, #0x1c', 'ldrb r2, [r2]', 'ldrb r3, [r4]',
              'movs r4, #1', 'str r4, [sp]', 'bl #0x8053c74')
        block(ins, 0x08052B28, 'ldr r1, [pc, #0x34]', 'ldr r2, [pc, #0x38]', 'str r4, [sp]',
              'movs r3, #0', 'bl #0x802b3a8')
        # Re-walk the complete CFG independently. Local BL loses LR and does not clobber the
        # argument registers. Every exit must recover the original LR, SP, and R4-R11.
        proof = match.BufferCallProof(self.rom, self.mapping, loop_replay=True)
        frame = prove_frame(ins, edges, address, branches, calls, stack_aliases=True, buffer_proof=proof)
        require(frame['maximum_frame_bytes'] == 64 and frame['returns'] == [0x08053092],
                'menu list must restore the 32-byte allocation and eight saved words')
        # The re-walk replays the byte-output callee's loop; its lines state that replay and the
        # registers it trusts across un-inspected calls (frame binds only the proof's fingerprint).
        # Each trusted callee is checked here: a pinned leaf that writes none of those registers.
        trusted = {}
        for records in proof.loop_replays.values():
            for entry in records:
                for target, register in entry[3]:
                    trusted.setdefault(target, set()).add(register)
        for target, registers in sorted(trusted.items()):
            require_pinned_leaf(self.rom, self.mapping, target, registers)
        self.evidence = dict(frame=frame, long_branches=record(ins.values(), address),
                             local_output_call=0x08052AD0, output_offsets=[28, 29],
                             installer=[INSTALLER, 0x08052474, REGISTER], runner=RUNNER,
                             dispatch_sites=[0x08006A34, 0x08006A6A], callback_thunk=THUNK,
                             loop_replay_lines=proof.loop_replay_lines(),
                             trusted_pinned_leaves=[[target, sorted(r - match.ARM_REG_R0 for r in registers)]
                                                    for target, registers in sorted(trusted.items())])
