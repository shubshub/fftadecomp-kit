"""Discard an affine result alias at the exact sequence-task constructor's first R3 write."""
from hashlib import sha256
from pathlib import Path
import struct

import bg_affine_transparent_leaf_profile as transparent
import effect_registry_scheduler as registry
from scroll_prefix_scene import PROVIDER
import match
import owner_graph_profile as graph

ROOT = 0x080FA76C
PRODUCER = 0x080032F8
AFFINE_SITE = 0x080FA9DE
CREATE_SITE = 0x080FA9E6
CREATE = 0x080D3E9C
SCHEDULE = 0x08005B6C
CALLBACK = 0x080D3CB4
SEQUENCE = 0x0894D9E4
ROOT_HASH = '5c7d815500b9508e28ef4ceeebecfb82e0fd6023f6e7e6c6501361776130f113'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def constructor(body, mapping):
    import owner_admission_profile as owner
    refinement = owner.refine(body, CREATE, mapping)
    ins, edges, branches, calls, words = graph.graph(body, CREATE, refinement)
    partition = graph.partition(body, CREATE, refinement, ins, words)
    shape = ['push {lr}', 'sub sp, #0x1c', 'adds r3, r1, #0',
             'mov r1, sp', 'movs r2, #0', 'strh r2, [r1, #0x14]',
             'strh r2, [r1, #0x16]', 'str r0, [sp, #4]',
             'ldr r0, [pc, #0xc]', 'movs r1, #0x2c', 'mov r2, sp',
             'bl #0x8005b6c', 'add sp, #0x1c', 'pop {r1}', 'bx r1']
    require(len(body) == 36 and not branches and not words and
            calls == {CREATE + 22: SCHEDULE} and
            [f'{i.mnemonic} {i.op_str}' for _, i in sorted(ins.items())] == shape and
            struct.unpack_from('<I', body, 32)[0] == CALLBACK | 1,
            'sequence constructor descriptor, operands, return or callback changed')
    # The first two instructions save only LR and move SP. ADDS overwrites R3
    # from R1, on the sole path before the scheduler can run arbitrary code.
    for pc in (CREATE, CREATE + 2, CREATE + 4):
        read, written = ins[pc].regs_access()
        require(tuple(edges[pc]) == (pc + 2,) and match.ARM_REG_R3 not in read and
                (match.ARM_REG_R3 in written) == (pc == CREATE + 4),
                'sequence constructor did not kill incoming R3 before any observation')
    return dict(address=CREATE, body_sha256=sha256(body).hexdigest(), partition=partition,
                kill=CREATE + 4, first_call=CREATE + 22, first_target=SCHEDULE,
                copied_parent_register=1, callback=CALLBACK | 1, descriptor_bytes=28,
                initialized_fields=[[4, 4, 'sequence'], [20, 2, 0], [22, 2, 0]],
                payload_size=44, result_register=0)


def scheduler_inputs(proof):
    # owner_admission_profile imports this module, and scheduler_event_definition reaches
    # owner_admission_profile at import time; importing it here keeps both importable first.
    from scheduler_event_definition import sequence as instructions
    # The two registry rows use the same 80-byte callback payload. The
    # phase-103 child separately requests 44 bytes plus the task header.
    direct = 0x08005954
    pins = {a: digest for a, _, digest in PROVIDER if a in (SCHEDULE, direct)}
    pins[registry.OWNER] = registry.OWNER_HASH
    pins[CALLBACK] = '71147746530e940b143a5356f38e0b502e506af62f8b13c5bb525c3c4cdbf1b9'
    bodies = {a: proof.span(a) for a in pins}
    require(all(sha256(bodies[a]).hexdigest() == digest for a, digest in pins.items()),
            'reviewed registry, scheduler or phase-zero callback changed')
    registrations = []
    for effect in (0x7F, 0xB8):
        row = registry.PRIMARY + 8 * (effect - 1)
        require(struct.unpack_from('<IHH', proof.rom, row - match.ROM_BASE) == (ROOT | 1, 80, 0x7fff),
                'reviewed affine effect registry row changed')
        registrations.append([effect, row])
    instructions(bodies[SCHEDULE], SCHEDULE, 0x08005B80, [
        'ldr r0, [r5]', 'str r3, [sp]', 'adds r1, r6, #0', 'adds r2, r4, #0', 'mov r3, r8',
        'bl #0x8005954', 'ldr r1, [r5]', 'ldrh r1, [r1, #0xc]', 'movs r2, #1',
        'eors r1, r2', 'strh r1, [r0, #0x16]'])
    instructions(bodies[direct], direct, 0x080059EE, [
        'mov r1, sp', 'mov r0, sb', 'ldm r0!, {r3, r4, r5}', 'stm r1!, {r3, r4, r5}',
        'ldm r0!, {r3, r4, r5}', 'stm r1!, {r3, r4, r5}', 'ldr r0, [r0]', 'str r0, [r1]',
        'mov r1, sp', 'movs r0, #0', 'strh r0, [r1]', 'ldr r3, [r7]', 'adds r0, r7, #0',
        'bl #0x8142250', 'movs r0, #0x80', 'lsls r0, r0, #1', 'strh r0, [r7, #0x14]',
        'adds r0, r7, #0'])
    require(proof.rom[0x142250:0x142252] == bytes.fromhex('1847'),
            'expected native synchronous callback dispatch through BX R3')
    instructions(bodies[CALLBACK], CALLBACK, 0x080D3CE4, [
        'ldr r2, [r6, #4]', 'str r2, [r5]', 'ldrh r0, [r6, #0x14]', 'strb r0, [r5, #4]',
        'ldrh r0, [r6, #0x16]', 'adds r0, #1', 'strh r0, [r5, #0xa]'])
    return dict(registrations=registrations, registry_scheduler_call=registry.CREATE,
                event_copy_bytes=28, phase_write=0x08005A02, dispatch=0x08005A08,
                entry_phase=0, native_spans=[[a, len(bodies[a]), pins[a]] for a in sorted(pins)],
                descriptor_reads=[[0, 2], [4, 4], [20, 2], [22, 2]], result_store=0x080FA9EA)


class AffineSequenceProof(transparent.BgAffineTransparentLeafProof):
    def check_scratch_call(self, consumer, producer_site, site, target, live):
        if (consumer, producer_site, site, target) != (ROOT, AFFINE_SITE, CREATE_SITE, CREATE):
            return super().check_scratch_call(consumer, producer_site, site, target, live)
        require(self._root[0] == ROOT and sha256(self._root[1]).hexdigest() == ROOT_HASH and
                self._root[2].get(producer_site) == PRODUCER and self._root[2].get(site) == CREATE and
                self._consumers and self._consumers[-1] == (PRODUCER, producer_site) and
                set(live) == {match.ARM_REG_R3},
                'sequence scratch requires the actual bound affine producer and R3 continuation')
        for key in ('rom', 'mapping', 'index', 'objects'):
            require(sha256(getattr(self, key)).hexdigest() == self.identities[key + '_sha256'],
                    'sequence scratch input changed')
        self.sequence_call = constructor(self.span(target), self.mapping)
        self.scheduler = scheduler_inputs(self)

    def scratch_manifest(self):
        result = super().scratch_manifest()
        require(hasattr(self, 'sequence_call'), 'expected an actual affine-to-sequence constructor site')
        result['sequence_constructor'] = dict(schema='affine-sequence-r3-kill-v1',
            root=ROOT, producer_site=AFFINE_SITE, producer=PRODUCER, site=CREATE_SITE,
            sequence=SEQUENCE, selected_register=3, constructor=self.sequence_call, scheduler=self.scheduler,
            source_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
        return result
