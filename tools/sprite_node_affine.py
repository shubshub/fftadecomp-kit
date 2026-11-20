"""Nested ObjAffineSet on the sprite renderer's frame, with outer IP preserved as a possible alias."""

from hashlib import sha256
from pathlib import Path

import bios_wrapper_summary_profile as bios
import function_thunk_profile as thunk
import match
import named_data_buffer_profile as named

ROOT = 0x080216F8
RENDER = 0x080018A0
MATRIX = 0x08000FC8
WRAPPER = 0x08141894
BIOS_CALL = 0x08001922
AFFINE_CALL = 0x080217BE
TRAVERSAL = 0x08021F18
BINDINGS = dict(calls=[[0xC6, 'func_080018A0'], [0x148, 'func_08001F34']],
                data=[], functions=[], switches=[])
BODIES = {
    ROOT: '62d3cf441001f2ba585e06911fa0aae0c0bce587a5d57f5304db908f413eac7d',
    RENDER: 'd2faf191b334f119a02ea3e146d67431580db260c64c8a78b02424e31a791418',
    MATRIX: 'd83cc653a221e0578bb0390613590aa3cdca381f13f100b4c691bd892fe0facc',
    TRAVERSAL: '1b28f97604da37d593eeabed05ed8b969343ae6fca07f0cb290ca7ac428c6325',
}
CONTRACT = (
    'Conditional returning GBA BIOS ObjAffineSet SWI 0x0F: R0 points to one eight-byte source '
    'record, with scale X, scale Y and angle in the first three halfwords; R1 points to four '
    'output halfwords spaced by R3=2 bytes, R2=1. No other caller memory is accessed. The '
    'routine preserves SP and R4-R11. It does not use incoming IP as an input or propagate it '
    'to memory or another register; IP returns its old value or a scalar. R2/R3 acquire no '
    'caller-frame addresses, and LR holds the return address. The renderer kills the possibly '
    'retained source and destination addresses in R0/R1 '
    'before use. These BIOS effects are premises. No numerical result, padding initialization, '
    'external object validity or termination claim.'
)
R0 = match.ARM_REG_R0
IP = match.ARM_REG_R12


def require(ok, reason):
    if not ok:
        raise ValueError('sprite node ObjAffineSet: ' + reason)


def local_records(aliases, stack, slots, words, constants):
    # Offsets are relative to the affine renderer's entry SP. The renderer
    # pushes eight words and allocates fifteen, leaving SP at entry SP - 92.
    require(len(stack) == 23 and aliases == {R0: -84, R0 + 1: -76, R0 + 4: -76}
            and not slots and not words, 'unexpected renderer frame, aliases or pointer words')
    count, stride = constants.get(R0 + 2), constants.get(R0 + 3)
    require(type(count) is int and count == 1 and type(stride) is int and stride == 2,
            'requires one record and a two-byte destination stride')
    bios.check_span((-84, 8, 4), stack, (), write=False)
    bios.check_span((-76, 8, 2), stack, (), write=True)


def killed(body, addr, after, registers, exits=frozenset()):
    decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
    decoder.detail = True
    for register in registers:
        require(match.stack_alias_overwritten_before_use(body, addr, after, register, decoder,
                                                        exit_sites=exits),
                'live register observed before overwrite or external return')


class SpriteAffineProof(named.RootReturnScratchBufferProof):
    """Keep both original native walks, one relative to each distinct frame."""

    def bind_return_root(self, address, data):
        require(address == ROOT, 'wrong root')
        super().bind_return_root(address, data)
        rows = [row.split() for row in self.index.decode().splitlines() if row.startswith('080216F8 ')]
        require(self.target(ROOT).get('instrs') == 172 and len(rows) == 1 and rows[0][3] == '172',
                'both index rows must count the 172 original Thumb instructions')
        bodies = {target: self.span(target) for target in BODIES}
        for target, body in bodies.items():
            require(sha256(body).hexdigest() == BODIES[target], 'changed body at %08X' % target)
        wrapper = self.span(WRAPPER)
        require(wrapper == bytes.fromhex('0fdf7047'), 'changed SWI 0x0F wrapper')
        self.dependencies[WRAPPER] = wrapper
        self.records[WRAPPER] = dict(address=WRAPPER, end=WRAPPER+4, bytes=4,
            body_sha256=sha256(wrapper).hexdigest(), **self.identities,
            structure=dict(kind='ObjAffineSet Thumb SWI and BX LR', instructions=2))
        killed(bodies[RENDER], RENDER, BIOS_CALL + 4, (R0, R0+1))
        # The caller loads the callback from its own literal and calls BX R7.
        parent = bodies[TRAVERSAL]
        require(int.from_bytes(parent[0x60:0x64], 'little') == (ROOT | 1),
                'changed caller callback literal')
        self.thunk = thunk.dependencies(['_call_via_r7'], self.rom)
        killed(parent, TRAVERSAL, 0x08021F8A, (R0+2,), frozenset({0x08021FB0}))
        self.seen = set()

    def check_call(self, address, aliases, stack, slots=None, *, constants=None, site=None, words=None):
        if address == RENDER:
            require(not self.active and site == AFFINE_CALL and len(stack) == 19 and
                    aliases == {R0+5: -34, R0+6: -36, R0+8: -34, IP: -38}
                    and not slots and not words, 'unexpected caller aliases at affine draw')
            for offset in aliases.values():
                self.access(offset, 2, stack)
            self.seen.add('draw')
        if address == WRAPPER:
            require(self.active == {RENDER} and site == BIOS_CALL, 'unexpected BIOS site')
            local_records(aliases, stack, slots, words, constants or {})
            self.seen.add('renderer frame')
            # Only the killed R0 and R1 carried these local pointers into the BIOS.
            return {}
        return super().check_call(address, aliases, stack, slots, constants=constants,
                                  site=site, words=words)

    def check_arguments(self, address, arguments, stack, incoming, protected, **context):
        if address == WRAPPER:
            require(self.active == {RENDER} and context.get('site') == BIOS_CALL and
                    self.seen >= {'draw', 'renderer frame'} and len(stack) == 19 and
                    arguments == {IP: -38} and not incoming and not protected and
                    not any(context.get(key) for key in ('words', 'frame_base', 'root_frame', 'watched')),
                    'unexpected outer-frame state at BIOS')
            self.access(-38, 2, stack)
            self.seen.add('callback frame')
            # No assumption that the BIOS kills IP. The standard outer walk
            # now follows this possible alias into the original matrix allocator.
            return dict(arguments)
        return super().check_arguments(address, arguments, stack, incoming, protected, **context)

    def manifest(self, bindings):
        require(bindings == BINDINGS and self.seen == {'draw', 'renderer frame', 'callback frame'}
                and {RENDER, MATRIX, WRAPPER} <= self.dependencies.keys()
                and self.root_scratch_manifest()['observations'] == [[346, 2, -40]],
                'incomplete observations or incorrect original ELF call names')
        return dict(schema='conditional-sprite-node-ObjAffineSet-v1', contract=CONTRACT,
            root=ROOT, renderer=RENDER, caller=TRAVERSAL, caller_thunk=self.thunk,
            caller_discards_R2=True, caller_bl=0x08021F86, callback_literal=0x08021F78,
            root_draw_site=AFFINE_CALL, nested_site=BIOS_CALL,
            wrapper=[WRAPPER, '0fdf7047'], local_input=[8, 8], local_output=[16, 8],
            count=1, stride=2, output_halfwords=[16,18,20,22],
            root_y_alias={'register': 'IP', 'root_sp_offset': 38, 'possible_after_BIOS': True},
            local_pointer_kills=[0x08001928, 0x08001926],
            matrix_allocator=[0x08001948, MATRIX],
            bodies=[[address, digest] for address, digest in sorted(BODIES.items())],
            verifier_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
