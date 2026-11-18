"""Bound the synchronous phase-zero consumption of the 080DE524 event definition."""
import hashlib
from pathlib import Path
import struct

import match
import scheduler_descriptor_lifetime as lifetime
from scheduler_entry_profile import require

OWNER, CALLBACK, CREATE = 0x080DE524, 0x080DDA94, 0x080DE604
WRAPPER, CORE, THUNK = 0x08005B6C, 0x08005954, 0x08142250
PREFIX_SHA256 = 'dbc1d1e57d96610e5cdcd537909f4025b2e0985dacbe186ff1726e516dc87275'
CALLS = {
    0x080DE56A: 0x080DD47C, 0x080DE57E: 0x080DD720, 0x080DE594: 0x080A880C,
    0x080DE5A8: 0x0809836C, 0x080DE5BE: 0x080DD350, 0x080DE5CA: 0x080DE12C,
    CREATE: WRAPPER,
}
# (definition offset, allocation payload offset, access width).
FIELDS = ((0, 0, 4), (4, 4, 4), (8, 8, 1), (9, 9, 1),
          (10, 10, 1), (11, 11, 1), (12, 14, 2))


def sequence(body, base, start, expected):
    """Decode an exact straight-line fragment, including its terminal branch if any."""
    cs = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
    actual = list(cs.disasm(body[start-base:], start, count=len(expected)))
    require([i.mnemonic + ' ' + i.op_str for i in actual] == expected,
            f'event definition instruction or operand differs at fragment {start:08X}')


def memory(reg, off):
    return f'[{reg}, #{hex(off) if off >= 10 else off}]' if off else f'[{reg}]'


def callback_phase(body):
    require(len(body) == 388, 'event callback requires its complete indexed body')
    # Phase is the halfword zero written by the scheduler after its 28-byte copy.
    sequence(body, CALLBACK, CALLBACK, [
        'push {r4, r5, r6, r7, lr}', 'adds r5, r1, #0', 'adds r4, r2, #0',
        'ldrh r1, [r5]', 'cmp r1, #1', 'beq #0x80ddaea',
        'cmp r1, #1', 'bgt #0x80ddaaa', 'cmp r1, #0', 'beq #0x80ddac0'])
    copies = []
    for source, dest, width in FIELDS:
        suffix = {1: 'b', 2: 'h', 4: ''}[width]
        reg = 'r2' if source == 4 else 'r0'
        copies.extend([f'ldr{suffix} {reg}, {memory("r1", source)}',
                       f'str{suffix} {reg}, {memory("r4", dest)}'])
    sequence(body, CALLBACK, 0x080DDAC0, ['ldr r1, [r5, #4]', *copies,
        'cmp r2, #0', 'bne #0x80ddae4', 'b #0x80ddc10', 'movs r0, #0',
        'strb r0, [r2]', 'b #0x80ddc10'])
    sequence(body, CALLBACK, 0x080DDC10, [
        'movs r0, #0', 'pop {r4, r5, r6, r7}', 'pop {r1}', 'bx r1'])
    return dict(address=CALLBACK, bytes=len(body), sha256=hashlib.sha256(body).hexdigest(),
                phase=0, descriptor_reads=[[0, 2], [4, 4]], field_transfers=FIELDS,
                optional_result_store=dict(site=0x080DDAE6, width=1, value=0),
                return_value=0, phase_zero_retains_frame_pointer=False)


def check_payload_argument(core, mapping):
    """Every returning list path sets R2 to the fresh allocation plus 24."""
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    ins, edges, _, calls, _ = graph.graph(core, CORE, owner.refine(core, CORE, mapping))
    require(calls == {CORE+34: 0x08007138, CORE+48: 0x0814224C, CORE+180: THUNK},
            'unexpected scheduler prefix or callback call')
    sequence(core, CORE, CORE+38, ['adds r7, r0, #0', 'ldr r0, [pc, #0x38]', 'ldr r2, [r0]',
        'adds r0, r7, #0', 'adds r1, r4, #0', 'bl #0x814224c', 'mov r3, r8', 'str r3, [r7]'])
    start, stop = CORE+52, CORE+154
    require(all(target <= start or site >= start for site, targets in edges.items() for target in targets),
            'scheduler prefix bypasses the callback store')
    pending, seen, cutpoint = [(start, None)], set(), set()
    while pending:
        site, offset = pending.pop()
        if (site, offset) in seen:
            continue
        seen.add((site, offset))
        if site == stop:
            cutpoint.add(offset)
            continue
        require(start <= site < stop and edges[site], 'list path bypasses the scheduler descriptor copy')
        i = ins[site]
        changed = set(i.regs_access()[1])
        require(not changed.intersection((match.ARM_REG_R0+7, match.ARM_REG_R0+8, match.ARM_REG_R0+9)),
                'list path clobbers the task, callback or descriptor register')
        if match.ARM_REG_R2 in changed:
            if i.mnemonic == 'adds' and i.op_str == 'r2, r7, #0':
                offset = 0
            else:
                require(i.mnemonic == 'adds' and i.op_str == 'r2, #0x18' and offset == 0,
                        'list path changes the payload address')
                offset = 24
        pending.extend((target, offset) for target in edges[site])
    require(cutpoint == {24}, 'scheduler copy receives different payload addresses')


def bind(proof, data, address, ins, edges, calls):
    require(address == OWNER and len(data) == 248 and calls == CALLS and len(ins) == 110,
            'expected the indexed command dispatcher, event constructor and seven calls')
    # Bind the dispatcher prefix too: it initializes the adjacent duration, obtains the
    # object, and saves each incoming scalar/pointer used by the constructor below.
    require(hashlib.sha256(data[:0x080DE5D6-OWNER]).hexdigest() == PREFIX_SHA256,
            'event dispatch, argument slots or halfword duration writes differ')
    sequence(data, address, 0x080DE5D6, [
        'str r6, [sp, #0x20]', 'ldr r1, [sp, #0x30]', 'str r1, [sp, #0x24]',
        'add r0, sp, #0x20', 'add r2, sp, #0x34', 'ldrb r2, [r2]', 'strb r2, [r0, #8]',
        'mov r1, sl', 'strb r1, [r0, #9]', 'add r2, sp, #0x38', 'ldrb r2, [r2]',
        'strb r2, [r0, #0xa]', 'add r1, sp, #0x3c', 'ldrb r1, [r1]', 'strb r1, [r0, #0xb]',
        'add r2, sp, #0x40', 'ldrh r2, [r2]', 'strh r2, [r0, #0xc]', 'add r2, sp, #4',
        'str r0, [r2, #4]', 'ldr r0, [pc, #0x18]', 'movs r1, #0x10', 'ldr r3, [sp, #0x7c]',
        'bl #0x8005b6c', 'add sp, #0x44', 'pop {r3, r4, r5}', 'mov r8, r3', 'mov sb, r4',
        'mov sl, r5', 'pop {r4, r5, r6, r7}', 'pop {r1}', 'bx r1'])
    sequence(data, address, 0x080DE562, ['mov r7, sp', 'movs r0, #0', 'strh r0, [r7]'])
    sequence(data, address, 0x080DE5AC, ['ldrh r0, [r4, #0x12]', 'strh r0, [r7]'])
    start = 0x080DE5D6
    require(all(target <= start or site >= start for site, targets in edges.items() for target in targets)
            and struct.unpack_from('<I', data, 244)[0] == CALLBACK | 1,
            'event entry bypasses initialization or callback literal differs')
    # The surrounding contract independently authenticates both full indexed bodies
    # and the R3 thunk. Check the exact argument forwarding, copy/phase overwrite,
    # actual task callback reload and contiguous disposal of the copy.
    wrapper, core = proof.span(WRAPPER), proof.span(CORE)
    require(wrapper[:30] == lifetime.WRAPPER_HEAD and wrapper[34:56] == lifetime.WRAPPER_TAIL
            and core[:34] == lifetime.CALLEE_HEAD and core[154:180] == lifetime.COPY + lifetime.CALL_SETUP
            and core[184:] == lifetime.CALLEE_RETURN, 'scheduler copy, zero phase or continuation differs')
    sequence(wrapper, WRAPPER, WRAPPER+30, ['bl #0x8005954'])
    sequence(core, CORE, CORE+180, ['bl #0x8142250'])
    require(proof.span(THUNK) == bytes.fromhex('1847'), 'expected the exact ARMv4T BX R3 thunk')
    check_payload_argument(core, proof.mapping)
    cb = callback_phase(proof.span(CALLBACK))
    return dict(callback=cb, scheduler_copy=dict(site=CORE+154, size=28, phase_store=CORE+174,
                callback_site=CORE+180, thunk=THUNK, payload_size=16, payload_allocation_offset=24),
                duration_stores=[0x080DE566, 0x080DE5AE], descriptor_pointer_store=0x080DE5FC,
                assumptions=[
                    'The scheduler allocation, manager, parent/list nodes, object and optional output storage '
                    'are valid for their observed accesses and disjoint from the active private/saved frames. '
                    'The fresh allocation is separate from the existing manager and list nodes. The result byte, '
                    'when nonnull, is also separate from the live task and its header.',
                    'The allocator and installed zero helper return with their documented frame and memory '
                    'effects. Concrete heap, installed code and termination are not established. Ordinary '
                    'dispatch calls retain their recorded ABI premises.',
                    'Under these conditions the synchronous phase-zero callback reads only initialized '
                    'definition members and stores values, including the caller-supplied object and result '
                    'addresses. It does not store either borrowed frame address. Other callback phases are '
                    'outside this statement.'],
                source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())


def check_call(proof, aliases, stack, slots, site):
    base = -4 * len(stack)
    r0 = match.ARM_REG_R0
    require(site == CREATE and base == -100 and [i for i, w in enumerate(stack) if w[2]] == list(range(17)),
            'expected the 68-byte private frame and eight separate saved words')
    require(aliases == {r0+2: base+4, r0+7: base} and slots == {base+8: base+32},
            'event call requires only its R2 descriptor, R7 duration and descriptor+4 definition word')
    for start, length in ((base, 2), (base+4, 28), (base+32, 16)):
        for byte in range(start, start+length):
            proof.access(byte, 1, stack)
    observation = dict(site=site, target=WRAPPER, local_offset=base+4, bytes=28,
                       aliases=sorted(aliases.items()), pointer_words=sorted(slots.items()),
                       duration=[base, base+2], definition=[base+32, base+48],
                       definition_initialized_bytes=14, spilled_arguments=[base+48, base+68])
    require(site not in proof.observations or proof.observations[site] == observation,
            'event state differs across incoming scheduler paths')
    proof.observations[site] = observation
    return {}


def check_bindings(bindings):
    require(bindings == dict(calls=[[site-OWNER, f'func_{target:08X}'] for site, target in CALLS.items()],
                functions=[[244, 'func_080DDA94']], data=[], switches=[]),
            'expected the seven original calls and sole typed event callback literal')
