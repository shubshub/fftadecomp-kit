"""Opt-in scratch transparency across complete, noncalling ordinary leaves.

A selected R2/R3 must be untouched throughout the leaf. It stays live in the
consumer continuation: conditional caller-clobbered ABI is never a kill.
"""
import hashlib
import json
from pathlib import Path

import bios_bg_affine_set_profile as affine
import ignored_leaf_alias_profile as ignored
import incoming_scratch_overwrite_profile as incoming
import match
import named_data_buffer_profile as buffers

def environment_fingerprint():
    from entry_recursive_ordinary_call_profile import environment_fingerprint as fingerprint
    return fingerprint()


SCHEMA = 'complete-thumb-untouched-scratch-leaf-v1'
MAX_BYTES = 256
MAX_STATES = 4096
CONTRACT = (
    'conditional ordinary returning ARM ABI; exact noncalling acyclic Thumb '
    'leaf never reads or writes selected R2/R3, which remain live across the '
    'call until the complete consumer proves a killing write or normal return; '
    'no physical readability, memory initialization, nonalias or termination theorem')


def effects(instruction):
    """The existing closed leaf effects plus register-offset signed halfword load."""
    word = int.from_bytes(instruction.bytes, 'little')
    if instruction.size != 2 or word & 0xFE00 != 0x5E00:
        return ignored.effects(instruction)
    register = lambda number: match.ARM_REG_R0 + number
    read = {register((word >> 3) & 7), register((word >> 6) & 7)}
    written = {register(word & 7)}
    if (read | written) - {register(n) for n in range(4)}:
        raise ValueError('transparent leaf excludes callee-saved register effects')
    decoded_read, decoded_written = instruction.regs_access()
    if set(decoded_read) != read or set(decoded_written) != written:
        raise ValueError('transparent leaf has inconsistent implicit load effects')
    return read, written


class BgAffineTransparentLeafProof(affine.BgAffineSetScratchProof):
    def __init__(self, rom, mapping, index, objects):
        if any(type(value) is not bytes for value in (rom, mapping, index, objects)):
            raise ValueError('transparent leaf requires immutable current inputs')
        super().__init__(rom, mapping, index, objects)
        self._transparent_calls = {}

    def check_scratch_call(self, consumer, producer_site, site, target, live):
        if not hasattr(self, '_root') or consumer != self._root[0] or \
                self._root[2].get(site) != target or not self._consumers or \
                self._consumers[-1][1] != producer_site or \
                self._root[2].get(producer_site) != self._consumers[-1][0]:
            raise ValueError('transparent leaf requires exact active root consumer calls')
        if not live or set(live) - {match.ARM_REG_R2, match.ARM_REG_R3}:
            raise ValueError('transparent leaf accepts only actual R2/R3 scratch')
        current = {name + '_sha256': hashlib.sha256(getattr(self, name)).hexdigest()
                   for name in ('rom', 'mapping', 'index', 'objects')}
        if current != self.identities:
            raise ValueError('transparent leaf inputs changed')
        # span() retains the shared dependency budget and complete owner identity.
        data = self.span(target)
        if len(data) > MAX_BYTES:
            raise ValueError('transparent leaf exceeds complete-owner byte budget')
        ins, edges, ordinary = incoming.authenticate_ordinary(
            self.rom, self.mapping, self.index, self.objects,
            consumer, len(self._root[1]), target)
        if ordinary['calls']:
            raise ValueError('transparent leaf excludes nested ordinary calls')
        # A topological pass rejects cycles without relying on traversal termination.
        incoming_edges = {site: 0 for site in ins}
        for successors in edges.values():
            for successor in successors:
                incoming_edges[successor] += 1
        ready = [site for site, count in incoming_edges.items() if count == 0]
        reached = 0
        while ready:
            here = ready.pop()
            reached += 1
            for successor in edges[here]:
                incoming_edges[successor] -= 1
                if incoming_edges[successor] == 0:
                    ready.append(successor)
        if reached != len(ins):
            raise ValueError('transparent leaf excludes cyclic control')
        accesses = {site: effects(item) for site, item in ins.items()}
        for read, written in accesses.values():
            if (read | written) & set(live):
                raise ValueError('transparent leaf reads or writes selected live scratch')
        pending, seen = [(target, 0)], set()
        while pending:
            here, flags = pending.pop()
            if (here, flags) in seen:
                continue
            if len(seen) >= MAX_STATES:
                raise ValueError('transparent leaf state budget exceeded')
            seen.add((here, flags))
            read_flags, written_flags = ignored.flag_effects(ins[here])
            if read_flags & ~flags:
                raise ValueError('transparent leaf observes incoming condition flags')
            pending.extend((successor, flags | written_flags) for successor in edges[here])
        observation = dict(consumer=consumer,
            consumer_sha256=hashlib.sha256(self._root[1]).hexdigest(),
            producer_site=producer_site, producer_target=self._consumers[-1][0],
            site=site, target=target, selected=sorted(r-match.ARM_REG_R0 for r in live),
            returned_live=sorted(r-match.ARM_REG_R0 for r in live),
            callee=ordinary, states=len(seen))
        self._transparent_calls[json.dumps(observation, sort_keys=True)] = observation

    def scratch_manifest(self):
        manifest = super().scratch_manifest()
        if not self._transparent_calls:
            raise ValueError('transparent leaf requires actual checked call observations')
        manifest['transparent_leaf_calls'] = dict(schema=SCHEMA, contract=CONTRACT,
            byte_budget=MAX_BYTES, state_budget=MAX_STATES,
            environment=environment_fingerprint(),
            observations=[self._transparent_calls[key] for key in sorted(self._transparent_calls)],
            source_sha256={Path(module.__file__).name:
                hashlib.sha256(Path(module.__file__).read_bytes()).hexdigest()
                for module in (affine, ignored, incoming, match, buffers, __import__(__name__))})
        return manifest
