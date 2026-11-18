"""The two mutually exclusive synchronous task initializers used by USA 080DCFE4."""
from hashlib import sha256
from pathlib import Path
import struct

import match
import scheduler_descriptor_lifetime as lifetime
import scheduler_event_definition as event
from scheduler_entry_profile import require

OWNER, CREATE = 0x080DCFE4, 0x080DD082
EFFECT, DELAY = 0x080DC55C, 0x080DCAD4
CALLBACKS = {
    EFFECT: (1398, 'b0f66d500a3c111e45ec981de977b106af6440111f5c4b2469793a8382d6f5ad'),
    DELAY: (232, '66a2094ce841eefc89046e04d0601d60d8e642fe53fd0db2ee68ccf4e2cafc17'),
}
BINDINGS = dict(calls=[[158, 'func_08005B6C']], functions=[[108, 'func_080DC55C'], [164, 'func_080DCAD4']],
                data=[], switches=[])


def copy_record(proof):
    import installed_copy_effects as installed
    import iwram_installation_prerequisite as install
    import scheduler_zero_descriptor as zero
    rom = proof.rom
    for first, end, digest in zero.BOOT:
        require(sha256(rom[first-match.ROM_BASE:end-match.ROM_BASE]).hexdigest() == digest,
                'changed boot initialization path')
    plan = install.verify(proof.span(0x08002768), 0x08002768, rom, proof.mapping, proof.index,
                          selector=install.SELECTOR, call_site=0x08002796, pointer_address=0x0836D4BC)
    image = bytes.fromhex(plan['source_image']['bytes'])
    require(plan['arguments'] == dict(source=zero.IMAGE, destination=zero.DESTINATION, control=88)
            and plan['copy_plan']['width'] == 2 and plan['copy_plan']['bytes'] == 176
            and plan['entry']['pointer_word'] == 0x03005EE9
            and plan['entry']['source_address'] == 0x08A38A9C
            and plan['source_image']['sha256'] == zero.IMAGE_SHA256
            and proof.span(0x08A38A9C) == image[0x70:0xAE], 'wrong installed copy image or entry')
    result = installed.verify_conditional(image, zero.DESTINATION, 0x03005EE8, 20, selector=installed.SELECTOR)
    for case in result['cases']:
        for key, region in [('reads','source'), ('writes','destination')]:
            accesses = [a for a in case[key] if a[0] != 'stack']
            require(all(a[0] == region for a in accesses) and
                    sorted(byte for _, at, width in accesses for byte in range(at,at+width)) == list(range(20)),
                    'copy touches other memory or a different record size')
        require(case['protected_return'] and case['SP_restored'], 'copy disturbs return or stack')
    return dict(entry=plan['entry'], boot=zero.BOOT, image_sha256=result['image_sha256'],
                count=20, destination_payload_interval=[16,36], modeled_alignments=len(result['cases']),
                effects=result['conditional_conclusion'])


def callback(proof, address):
    data = proof.span(address)
    size, digest = CALLBACKS[address]
    require(len(data) == size and sha256(data).hexdigest() == digest, 'changed complete task callback')
    seq = lambda at, expected: event.sequence(data, address, at, expected)
    if address == EFFECT:
        seq(EFFECT, ['push {r4, r5, r6, r7, lr}', 'mov r7, sl', 'mov r6, sb', 'mov r5, r8',
                     'push {r5, r6, r7}', 'sub sp, #0x18', 'mov sl, r0', 'str r1, [sp, #0x14]',
                     'adds r5, r2, #0', 'ldrh r1, [r1]', 'cmp r1, #1', 'bne #0x80dc576'])
        seq(0x080DC576, ['cmp r1, #1', 'bgt #0x80dc580', 'cmp r1, #0', 'beq #0x80dc58a'])
        seq(0x080DC58A, ['ldr r0, [sp, #0x14]', 'ldr r1, [r0, #4]', 'ldr r0, [r1]',
            'str r0, [r5, #0xc]', 'ldrb r0, [r1, #4]', 'strb r0, [r5, #6]',
            'ldrb r0, [r1, #5]', 'strb r0, [r5, #7]', 'ldrb r0, [r1, #6]', 'strb r0, [r5, #8]',
            'ldrb r0, [r1, #7]', 'strb r0, [r5, #9]', 'ldr r2, [pc, #0x1c]', 'adds r0, r5, #0',
            'adds r0, #0x10', 'ldr r1, [r1, #8]', 'ldr r3, [r2]', 'movs r2, #0x14', 'bl #0x8142250',
            'ldr r1, [sp, #0x14]', 'ldrh r0, [r1, #0x14]', 'strh r0, [r5, #2]',
            'ldrh r0, [r1, #0x16]', 'strh r0, [r5, #4]', 'b #0x80dcac0'])
        seq(0x080DCAC0, ['movs r0, #0', 'add sp, #0x18', 'pop {r3, r4, r5}', 'mov r8, r3',
                          'mov sb, r4', 'mov sl, r5', 'pop {r4, r5, r6, r7}', 'pop {r1}', 'bx r1'])
        require(struct.unpack_from('<I', data, 0x64)[0] == 0x0836D4BC, 'wrong copy-table slot')
        return dict(address=address, sha256=digest, descriptor_reads=[[0,2],[4,4],[20,2],[22,2]],
                    argument_reads=[[0,4],[4,1],[5,1],[6,1],[7,1],[8,4]], record_copy=copy_record(proof),
                    task_payload_bytes=56, private_pointer_retained=False)
    seq(DELAY, ['push {r4, r5, r6, lr}', 'adds r5, r1, #0', 'adds r4, r2, #0', 'ldrh r1, [r5]',
                'cmp r1, #1', 'beq #0x80dcbb4', 'cmp r1, #1', 'bgt #0x80dcaea',
                'cmp r1, #0', 'beq #0x80dcafa'])
    seq(0x080DCAFA, ['ldr r1, [r5, #4]', 'ldr r0, [r1]', 'str r0, [r4]', 'ldrb r0, [r1, #4]',
        'strb r0, [r4, #4]', 'ldrh r0, [r1, #6]', 'strh r0, [r4, #6]', 'ldrh r0, [r1, #8]',
        'strh r0, [r4, #8]', 'ldrb r0, [r1, #5]', 'strb r0, [r4, #5]', 'ldrh r0, [r5, #0x14]',
        'strh r0, [r4, #0xa]', 'b #0x80dcbb4'])
    seq(0x080DCBB4, ['movs r0, #0', 'pop {r4, r5, r6}', 'pop {r1}', 'bx r1'])
    return dict(address=address, sha256=digest, descriptor_reads=[[0,2],[4,4],[20,2]],
                argument_reads=[[0,4],[4,1],[5,1],[6,2],[8,2]], task_payload_bytes=12,
                private_pointer_retained=False)


def bind(proof, data, address, ins, edges, calls):
    require(address == OWNER and len(data) == 184 and len(ins) == 87 and calls == {CREATE:event.WRAPPER}
            and sha256(data).hexdigest() == 'cf24b04613eba38ece78d32295519ad93004a5fd55a1d3671e7db7c12f82a28d',
            'expected complete original effect or delay task starter')
    require([site for site, tails in edges.items() if not tails] == [0x080DD09A] and
            set(site for site, tails in edges.items() if 0x080DD080 in tails) == {0x080DD04E,0x080DD07E},
            'unexpected task start join or return')
    # Only R3 is assigned between the two arms and the call. The callback in
    # R0 and the requested size in R1 therefore belong to the same R2 record.
    event.sequence(data, OWNER, 0x080DD03E, [
        'add r2, sp, #0xc', 'mov r0, r8', 'strh r0, [r2, #0x14]', 'strh r6, [r2, #0x16]',
        'mov r1, sp', 'str r1, [sp, #0x10]', 'ldr r0, [pc, #4]', 'movs r1, #0x38', 'b #0x80dd080'])
    event.sequence(data, OWNER, 0x080DD074, [
        'add r2, sp, #0x28', 'mov r1, sb', 'strh r1, [r2, #0x14]', 'str r0, [r2, #4]',
        'ldr r0, [pc, #8]', 'movs r1, #0xc', 'ldr r3, [sp, #0x70]', 'bl #0x8005b6c'])
    require(struct.unpack_from('<I', data, 108)[0] == EFFECT | 1 and
            struct.unpack_from('<I', data, 164)[0] == DELAY | 1, 'changed typed callback literals')
    wrapper, core = proof.span(event.WRAPPER), proof.span(event.CORE)
    require(wrapper[:30] == lifetime.WRAPPER_HEAD and wrapper[34:56] == lifetime.WRAPPER_TAIL
            and core[:34] == lifetime.CALLEE_HEAD and core[154:180] == lifetime.COPY + lifetime.CALL_SETUP
            and core[184:] == lifetime.CALLEE_RETURN and proof.span(event.THUNK) == bytes.fromhex('1847'),
            'changed scheduler initialization and return')
    event.sequence(wrapper,event.WRAPPER,event.WRAPPER+30,['bl #0x8005954'])
    event.sequence(core,event.CORE,event.CORE+180,['bl #0x8142250'])
    event.check_payload_argument(core,proof.mapping)
    return dict(owner=address, owner_sha256=sha256(data).hexdigest(),
                callback_phases=[callback(proof, EFFECT),callback(proof, DELAY)],
                scheduler=dict(descriptor_bytes=28, phase_overwrite=event.CORE+174, phase=0,
                               dispatch_site=event.CORE+180,payload_offset=24,allocation_sizes=[84,40]),
                assumptions=['Object is readable at +12 and, on the delay path, +0. On the effect path any nonnull '
                             'record passed to the scheduler is readable for 20 bytes. Caller-supplied references and '
                             'the record bytes are independent of all subsequently established private frames.',
                             'The allocator returns separate writable storage of 84 or 40 bytes with the payload at +24. Its '
                             'call and the installed zero helper return with the documented ABI. Manager, '
                             'parent/list nodes, installation and fresh task cannot overlap active frames or each other '
                             'except for the ordinary links installed by the scheduler. The external record is separate '
                             'from the destination. The installed copy bytes must still be resident in IWRAM.'],
                source_sha256=sha256(Path(__file__).read_bytes()).hexdigest())


def check_call(proof, aliases, stack, slots, constants, site):
    base=-4*len(stack)
    require(site==CREATE and base==-108 and [i for i,w in enumerate(stack) if w[2]]==list(range(20)),
            'unexpected 80-byte local frame or seven saved words')
    beginning=aliases.get(match.ARM_REG_R2)
    if beginning==base+12:
        cb, size, payload, desc, initialized = EFFECT,56,0,12,12
    else:
        cb, size, payload, desc, initialized = DELAY,12,68,40,10
    require(aliases=={match.ARM_REG_R2:base+desc} and slots=={base+desc+4:base+payload}
            and (constants or {}).get(match.ARM_REG_R0+1)==size,
            'changed branch descriptor, payload, task size or ambient frame alias')
    for start,length in ((desc,28),(payload,12)):
        for byte in range(start,start+length):
            proof.access(base+byte,1,stack)
    arm=dict(callback=cb,size=size,descriptor=[desc,desc+28],parameters=[payload,payload+12],
             initialized_parameter_bytes=initialized, pointer_word=desc+4)
    proof.observations.setdefault(site,{})[cb]=arm
    return {}


def manifest(proof):
    arms=proof.observations.get(CREATE,{})
    require(set(proof.observations)=={CREATE} and set(arms)=={EFFECT,DELAY},
            'both disjoint descriptor paths must reach the original scheduler')
    return dict(schema='elf-symbol-thumb-conditional-scheduler-descriptor-payload-calls-v1',
                runtime_dependencies=proof.runtime_dependencies, environment=proof.environment,
                effect_or_delay=proof.effect_or_delay,
                observations=[dict(site=CREATE,arms=[arms[EFFECT],arms[DELAY]])])
