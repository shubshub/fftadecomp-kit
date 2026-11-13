"""Explicit BIOS BgAffineSet calls whose source and destination are tracked locals.

The four wrapper bytes are pinned, but they do not prove the BIOS interface:
the selector supplies a conditional returning-ABI premise for SWI 0x0E and
this module proves only the memory bounds that premise needs. BgAffineSet
reads `count` 20-byte source records and writes `count` 16-byte destination
records (GBATEK, "BgAffineSet"); nothing else is read or written.
"""
import hashlib
from pathlib import Path

import match
import named_data_buffer_profile as buffers
import owner_graph_profile as graph

ADDRESS = 0x08141864
NAME = 'func_08141864'
WRAPPER = bytes.fromhex('0edf7047')
SOURCE_RECORD = 20
DESTINATION_RECORD = 16
MAX_COUNT = 255
SCHEMA = 'conditional-bios-bgaffineset-local-buffers-v1'
CONTRACT = (
    'conditional returning GBA BIOS BgAffineSet (SWI 0x0E) boundary: r0 is a '
    'tracked local source of count 20-byte records, r1 a tracked local '
    'destination of count 16-byte records, r2 a proven constant count; the '
    'source and destination spans are whole local frame words and disjoint, '
    'and no other memory is read or written; compatible ordinary returning '
    'ABI for r0-r3; no source initialization, numeric result, physical '
    'readability or termination theorem')


class BgAffineSetProof(buffers.NamedDataBufferProof):
    """Ordinary bounded-buffer calls plus exact BgAffineSet local-buffer sites."""

    def bind_root(self, data, address, calls):
        import owner_admission_profile as owner
        if hasattr(self, '_root'):
            raise ValueError('BgAffineSet root context is single use')
        owner.validate_span(data, address, self.rom, self.mapping, self.index)
        refinement = owner.refine(data, address, self.mapping)
        instructions, edges, branches, actual, words = graph.graph(data, address, refinement)
        graph.partition(data, address, refinement, instructions, words)
        if branches or words or calls != actual or ADDRESS not in calls.values():
            raise ValueError('BgAffineSet requires an actual direct call in its closed owner')
        if self.span(ADDRESS) != WRAPPER:
            raise ValueError('BgAffineSet requires the exact indexed SWI 0x0E return wrapper')
        self._root = (address, bytes(data), dict(calls))
        self._observations = set()

    def check_call(self, address, aliases, stack, slots=None, *, constants=None,
                   site=None, words=None):
        if not hasattr(self, '_root') or self._root[2].get(site) != address:
            raise ValueError('BgAffineSet profile requires its exact bound root call')
        if address != ADDRESS:
            return super().check_call(address, aliases, stack, slots,
                constants=constants, site=site, words=words)
        arguments = {reg: offset for reg, offset in aliases.items()
                     if reg in match.CALLER_CLOBBERED}
        if slots or words or match.ARM_REG_LR in aliases or \
                set(arguments) != {match.ARM_REG_R0, match.ARM_REG_R1}:
            raise ValueError('BgAffineSet requires exactly a local source and a local destination')
        count = (constants or {}).get(match.ARM_REG_R2)
        if type(count) is not int or not 1 <= count <= MAX_COUNT:
            raise ValueError('BgAffineSet count is not a proven constant in 1..255')
        source, destination = arguments[match.ARM_REG_R0], arguments[match.ARM_REG_R1]
        if source % 4 or destination % 4:
            raise ValueError('BgAffineSet buffers must be word aligned')
        source_end = source + SOURCE_RECORD * count
        destination_end = destination + DESTINATION_RECORD * count
        for start, end in ((source, source_end), (destination, destination_end)):
            for word in range(start, end, 4):
                self.access(word, 4, stack)
        if source < destination_end and destination < source_end:
            raise ValueError('BgAffineSet source and destination overlap')
        if self.span(address) != WRAPPER:
            raise ValueError('BgAffineSet complete wrapper changed')
        self.dependencies[address] = WRAPPER
        self.records[address] = dict(address=address, end=address+len(WRAPPER),
            bytes=len(WRAPPER), body_sha256=hashlib.sha256(WRAPPER).hexdigest(),
            **self.identities,
            structure=dict(kind=buffers.BG_AFFINE_SCHEMA, instructions=2,
                wrapper_hex=WRAPPER.hex(), conditional_ABI=CONTRACT))
        self._observations.add((site, source, destination, count))
        return {}

    def bios_manifest(self):
        if not hasattr(self, '_root') or not self._observations:
            raise ValueError('BgAffineSet profile requires an actual checked call')
        address, data, _ = self._root
        return dict(schema=SCHEMA, contract=CONTRACT,
            owner=[address, len(data), hashlib.sha256(data).hexdigest()],
            dependency=[ADDRESS, len(WRAPPER), hashlib.sha256(WRAPPER).hexdigest()],
            sites=[list(row) for row in sorted(self._observations)],
            producer_sha256={Path(module.__file__).name:
                hashlib.sha256(Path(module.__file__).read_bytes()).hexdigest()
                for module in (buffers, __import__(__name__))})


class BgAffineSetScratchProof(BgAffineSetProof, buffers.DiscardedReturnScratchProof):
    """Compose exact local BIOS spans with authenticated scratch nonobservation."""
