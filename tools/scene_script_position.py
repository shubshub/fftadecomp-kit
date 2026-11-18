"""Conditional caller-local effects of the reviewed mode-six scene constructors."""
from hashlib import sha256
from pathlib import Path
import struct

import bios_cpuset_fill_profile as bios
import match
from scheduler_entry_profile import require
import scheduler_helper2_state as helper
import scheduler_helper_common_state as common
from scheduler_callback_zero_phase import _call as thumb_call

SELECTOR = 'conditional-scene-mode6-position-v1'
CALLBACK = 0x080DFF04
PREDICATE = 0x080D8B28
GEOMETRY = 0x0801BB94
# Count, local packed position, ROM script argument, complete closed owner.
OWNERS = {
    0x08118A08: (3, 0x00B80068, 0x083A6110, 'b88a5a52e64831c00f918b9c9399762f8dabedd9d440ff9b3953839957e183c1'),
    0x08118AC0: (5, 0x00F800D8, 0x083A616C, 'fc61eb9ad6fba9d1e97012a9739eabcea2effe40f0e1dfb7bbb09a6c755a5fdd'),
    0x08118B94: (2, 0x01180038, 0x083A61C0, '403741710a2cd36c4d5316c17d39f43b3511bb16f60e4d52e86901cbb7cc39aa'),
    0x08118C4C: (4, 0x00F80078, 0x083A6208, '0908854eb0be864cd2121ffc1c1a9ed77d6ff07afe4c9ec41cbca270e1aefb14'),
}
CALLEES = {
    helper.ADDRESS: helper.BODY_SHA256,
    PREDICATE: 'd3ab84554a9d4be3eb334f19bf72f018caa66ab1d908e8462e84c43c91440095',
    GEOMETRY: '03e9643fc8f320b6f7eedb68aaf15c9d31f38be8e2739ef60e040ca4f7b2059d',
    CALLBACK: '9810cbaa6d2185d1305abd5dfb0a5ec5e77174a9b934fdc295b5146614e4f957',
}
FILL_SITES = (60, 80)
SCRIPT_SITE = 98


def helper_entry(proof, address, count, script, position):
    """Run the existing byte-origin interpreter from entry to the geometry call."""
    body = proof.dependencies[helper.ADDRESS]
    getter = thumb_call(body, helper.ADDRESS, 114)
    coordinates = thumb_call(body, helper.ADDRESS, 130)
    getter_body = proof.span(getter)
    identity = thumb_call(getter_body, getter, 2)
    layout = common.bind(body, helper.ADDRESS, getter_body, getter, proof.span(identity),
        identity, proof.span(coordinates), coordinates, selector=common.SELECTOR)

    # Coordinates are relative to entry SP. Register/parameter bytes whose
    # values are immaterial stay opaque. The base instantiates the check; it
    # establishes no actual address, initial memory permission or stack lifetime.
    words = common.words
    registers = {r: tuple(('opaque-byte', f'entry R{r}', j) for j in range(4)) for r in range(15)}
    registers.update({1: words._constant(script), 2: words._constant(count), 3: words._constant(6),
        13: words._pointer(0), 14: words._constant((address+SCRIPT_SITE+4)|1)})
    cells = dict(enumerate(words._pointer(12)))
    cells.update(enumerate(words._constant(position), 12))
    trace = common.derive(layout, 0x02010000, cells, registers, selector=common.SELECTOR)
    cut = trace['nested_call_cutpoint']
    events = trace['memory_events']
    reads = [event for event in events if event.get('signed')]
    dispatch = [event for event in events if event['operation'] == 'guarded-table-branch']
    x, y = struct.unpack('<hh', position.to_bytes(4, 'little'))
    parameters = trace['post_cells']
    require([parameters[str(i)] for i in (-28,-27,-26)] == [0,0,count] and
            tuple(parameters[str(i)] for i in range(-24,-20)) == words._constant(script),
            'the helper must pack the zero delay, count and caller ROM script before the predicate')
    require(trace['observed_mode'] == count and trace['observed_dispatch'] == 6 and
            cut and cut['call_site'] == 0x080E04DC and cut['target'] == PREDICATE and cut['SP'] == -72 and
            [cut['register_arguments'][reg] for reg in (0, 1)] ==
                [words._constant(x & 0xFFFFFFFF), words._constant(y & 0xFFFFFFFF)] and
            trace['registers'][5] == words._pointer(12) and trace['registers'][7] == words._pointer(-28) and
            [(r['site'],r['coordinate']) for r in reads] == [(0x080E04D6,12),(0x080E04DA,14)] and
            dispatch == [dict(site=0x080E043C, operation='guarded-table-branch', target=0x080E04D4)],
            'mode-six path did not reach the geometry predicate with exactly two signed scalar coordinates')
    return dict(schema=common.SELECTOR, mode=trace['observed_mode'], dispatch=dispatch[0],
        signed_reads=reads, signed_coordinates=[x,y], parameter_delay_before_predicate=0,
        parameter_count=count, parameter_data=script, predicate_call=cut['call_site'],
        helper_entry_relative_SP=cut['SP'], reached_instructions=trace['trace'],
        dependencies=trace['complete_owner_pins'], actual_reaching_state_proved=False)


def decoded(body, base, start, end, expected):
    """Check a complete instruction slice and return its actual sites."""
    decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
    items = list(decoder.disasm(body[start-base:end-base], start))
    require([i.mnemonic+' '+i.op_str for i in items] == expected and
            items[-1].address+items[-1].size == end, 'unexpected scene dependency instruction slice')
    return [i.address for i in items]


def scheduler_callback(proof):
    scheduler = proof.span(helper.SCHEDULER)
    callback = proof.dependencies[CALLBACK]
    # The manager replaces R5 on entry, allocation replaces R7, and the node
    # stores R8 (the original R1 callback) at offset zero before the dispatch.
    # The existing scheduler prefix contract supplies node and saved-word isolation.
    decoded(scheduler, helper.SCHEDULER, 0x0800595E, 0x08005968,
            ['adds r5, r0, #0', 'mov r8, r1', 'adds r4, r2, #0', 'mov sb, r3', 'ldr r6, [sp, #0x38]'])
    require(thumb_call(scheduler, helper.SCHEDULER, 34) == 0x08007138 and
            thumb_call(scheduler, helper.SCHEDULER, 48) == 0x0814224C and
            thumb_call(scheduler, helper.SCHEDULER, 180) == 0x08142250,
            'allocation, initialization or callback thunk target differs')
    decoded(scheduler, helper.SCHEDULER, 0x08005988, 0x0800598C, ['mov r3, r8', 'str r3, [r7]'])
    copy = decoded(scheduler, helper.SCHEDULER, 0x080059EE, 0x08005A08, [
        'mov r1, sp', 'mov r0, sb', 'ldm r0!, {r3, r4, r5}', 'stm r1!, {r3, r4, r5}',
        'ldm r0!, {r3, r4, r5}', 'stm r1!, {r3, r4, r5}', 'ldr r0, [r0]', 'str r0, [r1]',
        'mov r1, sp', 'movs r0, #0', 'strh r0, [r1]', 'ldr r3, [r7]', 'adds r0, r7, #0'])
    gate = decoded(callback, CALLBACK, CALLBACK, 0x080DFF1A, [
        'push {r4, r5, r6, lr}', 'adds r6, r0, #0', 'adds r5, r1, #0', 'adds r4, r2, #0',
        'ldrh r1, [r5]', 'cmp r1, #1', 'beq #0x80dff84', 'cmp r1, #1',
        'bgt #0x80dff1c', 'cmp r1, #0', 'beq #0x80dff2c'])
    fields = decoded(callback, CALLBACK, 0x080DFF2C, 0x080DFF3C, [
        'ldr r1, [r5, #4]', 'ldrb r0, [r1, #2]', 'strb r0, [r4, #2]',
        'ldr r0, [r1, #4]', 'str r0, [r4, #4]', 'ldrh r0, [r1]', 'strh r0, [r4]', 'b #0x80dff84'])
    epilogue = decoded(callback, CALLBACK, 0x080DFF84, 0x080DFF8C,
                       ['movs r0, #0', 'pop {r4, r5, r6}', 'pop {r1}', 'bx r1'])
    return dict(copied_descriptor_bytes=28, scheduler_copy_and_phase_zero=copy, phase_zero_dispatch=gate,
                phase_zero_parameter_copy=fields, phase_zero_return=epilogue,
                payload_field_widths=[[0,2],[2,1],[4,4]], callback_parameter_pointer_retained=False)


def bind(proof, data, address, calls):
    require(address in OWNERS, 'expected a reviewed scene callback')
    count, position, script, digest = OWNERS[address]
    require(sha256(data).hexdigest() == digest and
            struct.unpack_from('<5I', data, 108) ==
                (position, 0x03003920, 0x01000040, 0x01000070, script),
            'scene count, control words, destination, script or complete native owner differs')
    require(all(calls.get(address+site) == bios.ADDRESS for site in FILL_SITES) and
            calls.get(address+SCRIPT_SITE) == helper.ADDRESS, 'expected two CpuSet fills and the script call')
    proof.scene_bios = bios.BiosFillProof(data, address, proof.rom, proof.mapping, proof.index, calls)
    for target, expected in CALLEES.items():
        body = proof.span(target)
        require(sha256(body).hexdigest() == expected, 'scene script dependency identity differs')
        proof.dependencies[target] = body
        proof.records[target] = dict(address=target, end=target+len(body), bytes=len(body),
            body_sha256=expected, structure={'kind': 'mode-six script dependency'}, **proof.identities)
    # Each script call supplies a nonzero count and R3=6. The helper saves 20
    # bytes and allocates 52, so [SP+72] is the caller's first outgoing word.
    # Its unsigned guard admits slot 6; both outcomes of the geometry check
    # converge at 080E04F2. Other switch arms are never used by these owners.
    b = proof.dependencies[helper.ADDRESS]
    table = struct.unpack_from('<I', b, 0x50)[0]
    require(table == 0x080E044C and struct.unpack_from('<I', b, table+24-helper.ADDRESS)[0] == 0x080E04D4 and
            struct.unpack_from('<III', b, 280) == (0xFFFF0000, 0x0200F430, CALLBACK|1),
            'mode-six dispatch, direct scheduler manager or callback literal differs')
    entry = helper_entry(proof, address, count, script, position)
    # The canonical helper source verifier binds all instructions, literals and
    # table entries. The two possible predicate outcomes update only the delay;
    # both continue through this manager, parent load and scheduler call.
    require(thumb_call(b, helper.ADDRESS, 228) == PREDICATE and
            thumb_call(proof.dependencies[PREDICATE], PREDICATE, 18) == GEOMETRY and
            thumb_call(b, helper.ADDRESS, 266) == helper.SCHEDULER and
            b[232:266] == common.HELPER[232:266] and b[270:278] == common.HELPER[270:278],
            'predicate, parent, conditional delay, scheduler call or helper restore differs')
    proof.scene = dict(entry=entry, callback_effect=scheduler_callback(proof), possible_delay_halfwords=[0,20], owner=address, count=count, script=script, position=position,
        helper=helper.ADDRESS, helper_frame_bytes=72, position_stack_argument=0,
        dispatch=dict(site=0x080E043C, table=table, index=6, destination=0x080E04D4),
        signed_reads=[[0x080E04D6, 0, 2], [0x080E04DA, 2, 2]],
        predicate_call=0x080E04DC, predicate=PREDICATE, geometry=GEOMETRY,
        predicate_result_join=0x080E04F2, scheduler_call=0x080E0502, scheduler=helper.SCHEDULER,
        helper_descriptor=[4, 32], helper_parameters=[44, 52], fifth_argument_forwarded=False,
        parameter_pointer_store=0x080E04F2, parent_from_incoming_word=4,
        callback=CALLBACK, phase_zero_data_store=0x080DFF34,
        geometry_ambient_registers_saved_then_replaced=[5,7],
        scheduler_ambient_registers_saved_then_replaced=[5,7])


def check_call(proof, target, aliases, stack, slots, constants, site):
    root = proof.scene['owner']
    offset = site-root
    base = -4*len(stack)
    require(base == -36, 'expected the complete 36-byte saved and local frame')
    slots = slots or {}
    r0 = match.ARM_REG_R0
    if target == bios.ADDRESS:
        require(offset in FILL_SITES and not slots and aliases == {r0: base+(8 if offset == FILL_SITES[0] else 10)},
                'expected the respective private halfword fill source only')
        result = proof.scene_bios.check_call(site, aliases, stack)
    elif target == helper.ADDRESS:
        require(offset == SCRIPT_SITE and not aliases and slots == {base: base+12} and
                (constants or {}).get(r0+2) == proof.scene['count'] and (constants or {}).get(r0+3) == 6,
                'script requires its isolated aligned outgoing position pointer, count and mode six')
        for start, width in ((base,4),(base+4,4),(base+12,2),(base+14,2)):
            proof.access(start,width,stack)
        result = {}
    else:
        require(not aliases and not slots, 'ordinary scene call carries a private alias or outgoing pointer word')
        result = {}
    proof.observations[site] = dict(site=site,target=target,aliases=sorted(aliases.items()),
                                    pointer_words=sorted(slots.items()))
    return result


def check_bindings(address, bindings):
    script = OWNERS[address][2]
    expected = [[112, 'data_03003920', 0], [124, f'data_{script:08X}', 0]]
    if address == 0x08118AC0:
        expected.append([168, 'data_0894AB00', 0])
    require(bindings['data'] == expected and not bindings['functions'] and not bindings['switches'],
            'expected original named RAM destination and ROM scene data relocations')


def manifest(proof):
    require(set(proof.calls) == set(proof.observations) and len(proof.scene_bios.observations) == 2,
            'all scene calls and both fill sources must be observed')
    return dict(schema='elf-symbol-thumb-'+SELECTOR, script=proof.scene, bios_fill=proof.scene_bios.manifest(),
        runtime_dependencies=proof.runtime_dependencies, environment=proof.environment,
        observations=[proof.observations[s] for s in sorted(proof.observations)],
        assumptions=[
            'Both BIOS fills return with the checked source unit and ordinary ABI. The target ranges are numeric; physical permissions, isolation and BIOS return are premises.',
            'The mode-six helper reads the caller position only as signed halfwords. At the predicate call R5 still holds that pointer and R7 holds the helper parameters. The geometry entry saves both, then replaces them before data use. Nested calls return with protected frames intact.',
            'The scheduler saves helper R5 and R7 before replacing them. Its descriptor at helper SP+4 contains a pointer to helper SP+44. The phase-zero callback reads the parameter delay, count and ROM data word and writes those fields to the new task. Other bytes copied as representation are not certified initialized.',
            'The scheduler manager, parent, allocation and list nodes are physically valid and disjoint from all private frames. The allocator and installed zero routine return compatibly, preserve saved slots and do not retain private pointers. Stack memory remains stable throughout these calls.',
            'Other scene calls use the ordinary returning ABI and do not read private frame memory. No physical memory, initialization of all representation bytes, callback termination, or unconditional nonretention is established.'],
        actual_termination_proved=False, physical_noninterference_proved=False,
        source_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
