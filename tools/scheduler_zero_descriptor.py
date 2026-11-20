"""Compose the installed zero routine with the direct 28-byte scheduler descriptor."""
import hashlib
from pathlib import Path
import struct

import function_thunk_profile as thunk
import installed_zero_effects as zero
import iwram_installation_prerequisite as install
import match
import scheduler_entry_profile as scheduler

SELECTOR = 'conditional-scheduler-zero-descriptor-v1'
SCHEMA = 'elf-symbol-thumb-' + SELECTOR
OWNER = 0x080D376C
INITIALIZE = OWNER + 12
CREATE = OWNER + 30
THUNK = thunk.ALIASES['_call_via_r2']
POINTER = 0x0836D4B8
IMAGE = 0x08A38A2C
DESTINATION = 0x03005E78
IMAGE_SHA256 = 'ce26dd719323641c1c4cbfa501368306ce6e31e193dabce7e84c7067f7590130'
SIZE = scheduler.DESCRIPTOR_BYTES
BOOT = (
    (0x08000254, 0x0800027A, '9a6c45bebd677677f2a7e9d2427f4c87bd737905eeab640f39bdcdd45f9a9b76'),
    (0x08002710, 0x08002768, '62739675d57afabfbf8dd443b4d34ecf7fd5306e6b347e52bcec135403f74261'),
)
require = scheduler.require


def initializer_plan(rom, mapping, index):
    for start, end, digest in BOOT:
        require(hashlib.sha256(rom[start-install.ROM_BASE:end-install.ROM_BASE]).hexdigest() == digest,
                'expected boot to call the reviewed CpuSet code installer through 08002710')
    plan = install.verify(rom[0x2768:0x27B8], 0x08002768, rom, mapping, index,
                          selector=install.SELECTOR, call_site=0x08002796, pointer_address=POINTER)
    require(plan['arguments'] == dict(source=IMAGE, destination=DESTINATION, control=88) and
            plan['copy_plan']['width'] == 2 and plan['copy_plan']['bytes'] == 176 and
            plan['entry']['pointer_word'] == (DESTINATION | 1) and
            plan['source_image']['sha256'] == IMAGE_SHA256,
            'expected the canonical 88-halfword image and its first Thumb entry')
    return plan


def initializer(rom, mapping, index):
    plan = initializer_plan(rom, mapping, index)
    effects = zero.verify_conditional(bytes.fromhex(plan['source_image']['bytes']), DESTINATION,
                                      DESTINATION, SIZE, selector=zero.SELECTOR)
    case = effects['cases'][0]  # The owner frame proves alignment zero modulo four.
    stores = [('destination', offset, 4) for offset in range(0, SIZE, 4)]
    require(case['alignment'] == 0 and case['writes'] == [('stack', -4, 4), *stores]
            and case['reads'] == [('stack', -4, 4)] and case['protected_return'] and case['SP_restored'],
            'expected seven aligned zero stores and the separate four-byte return save')
    return dict(boot=BOOT, installer=plan['installer'], copy_plan=plan['copy_plan'], entry=plan['entry'],
                bios_call=plan['call_site'], wrapper=plan['wrapper'], image_sha256=effects['image_sha256'],
                cases_checked=4, aligned_case=case, result=effects['conditional_conclusion'],
                assumptions=effects['unproved_premises'], installed_identity_proved=False)


def bind(proof, data, address, ins, edges, calls):
    require(address == OWNER and len(data) == 64 and calls == {INITIALIZE: THUNK, CREATE: scheduler.DIRECT},
            'expected the identified 64-byte constructor and its two exact Thumb calls')
    # All arguments, all memory effects, and the post-initializer register kills.
    # In particular R2 leaves the image one past the descriptor. The following
    # LDR kills it before any use. R0 (saved LR) is likewise redefined.
    expected = ['push {lr}', 'sub sp, #0x20', 'ldr r0, [pc, #0x24]', 'ldr r2, [r0]',
                'add r0, sp, #4', 'movs r1, #0x1c', 'bl #0x814224c',
                'ldr r0, [pc, #0x1c]', 'ldr r0, [r0]', 'ldr r1, [pc, #0x1c]',
                'ldr r2, [pc, #0x20]', 'movs r3, #0', 'str r3, [sp]', 'add r3, sp, #4',
                'bl #0x8005954', 'ldr r1, [pc, #0x18]', 'str r0, [r1]', 'add sp, #0x20',
                'pop {r0}', 'bx r0']
    require([f'{i.mnemonic} {i.op_str}' for _, i in sorted(ins.items())] == expected and
            struct.unpack_from('<5I', data, 44) == (
                POINTER, 0x0200F430, 0x080D3209, 0xB28, 0x020159C0),
            'unexpected owner descriptor, initializer arguments, manager, callback, parent or result store')
    proof.scheduler_entry = scheduler.bind(data, address, ins, edges, {CREATE: scheduler.DIRECT})
    proof.initializer = initializer(proof.rom, proof.mapping, proof.index)


def check_call(proof, address, aliases, stack, slots, constants, site):
    base = -4 * len(stack)
    offset = base + 4
    require(base == -36 and offset % 4 == 0 and not slots, 'expected parent word and private aligned descriptor')
    if site == INITIALIZE:
        r0 = match.ARM_REG_R0
        require(address == THUNK and aliases == {r0: offset} and (constants or {}).get(r0+1) == SIZE,
                'expected the local descriptor in R0 and exact byte count in R1')
        for byte in range(offset, offset + SIZE):
            proof.access(byte, 1, stack)
        proof.observations[site] = dict(site=site, target=address, local_offset=offset,
                                        bytes=SIZE, effect='conditional installed zero')
        return {}
    require(site == CREATE and address == scheduler.DIRECT and aliases == {match.ARM_REG_R3: offset}
            and proof.observations.get(INITIALIZE, {}).get('local_offset') == offset,
            'scheduler must consume the same private descriptor the initializer received')
    return scheduler.check_call(proof, address, aliases, stack, slots, site=site)


def check_bindings(manifest, bindings):
    scheduler.check_bindings(manifest, bindings)
    require(bindings == dict(calls=[[12, '_call_via_r2'], [30, 'func_08005954']],
                             data=[[44, 'g_callbacks_0836D4B8', 0], [48, 'data_0200F430', 0],
                                   [60, 'data_020159C0', 0]],
                             functions=[[52, 'func_080D3208']], switches=[]),
            'expected the original two Thumb call relocations and all four typed data/function literal bindings')


def manifest(proof):
    result = scheduler.manifest(proof)
    result.update(schema=SCHEMA, scheduler_schema=scheduler.SCHEMA, initializer=proof.initializer,
                  initialized_descriptor_bytes=SIZE, parent_value=0,
                  composition_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    return result
