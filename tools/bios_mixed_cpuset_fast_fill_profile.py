"""Compose the CpuSet and CpuFastSet local-source fill proofs in one owner.

Each wrapper call is checked only by its own existing proof: 0x0814186C by
bios_cpuset_fill_profile.BiosFillProof (bit24 on every reaching path, unit
width from bit26), 0x08141868 by bios_fast_fill_source_profile (bit24, one
aligned word), and every other callee by the unchanged named-data buffer
check.  Nothing about either proof is widened; the owner must call both.
"""
import hashlib
from pathlib import Path

import bios_cpuset_fill_profile as cpuset
import bios_fast_fill_source_profile as fast_fill
import named_data_buffer_profile as buffers

SCHEMA = 'conditional-bios-cpuset-cpufastset-mixed-local-fill-source-v1'
CONTRACT = (fast_fill.MixedFastFillSourceProof.contract + '; CpuSet sites keep '
            'their own conditional local-source contract: ' + cpuset.CONTRACT)


class MixedCpuSetFastFillProof(fast_fill.MixedFastFillSourceProof):
    """Dispatch each actual wrapper site to its own unchanged fill proof."""

    schema = SCHEMA
    contract = CONTRACT

    def bind_root(self, data, address, calls):
        targets = set(calls.values())
        if cpuset.ADDRESS not in targets or fast_fill.ADDRESS not in targets:
            raise ValueError('mixed CpuSet/CpuFastSet fill requires actual calls to both wrappers')
        super().bind_root(data, address, calls)
        self._root_fill = cpuset.BiosFillProof(data, address, self.rom,
            self.mapping, self.index, calls)

    def check_call(self, address, aliases, stack, slots=None, *, constants=None,
                   site=None, words=None):
        if address != cpuset.ADDRESS:
            return super().check_call(address, aliases, stack, slots,
                constants=constants, site=site, words=words)
        # Defence in depth: BiosFillProof.check_call already refuses a site
        # outside its own bound calls, but the dispatch here must never route
        # a CpuSet target through anything but the root's actual CpuSet site.
        if not hasattr(self, '_root') or self._root[2].get(site) != address:
            raise ValueError('mixed CpuSet fill requires its exact bound root call')
        return buffers.check_bios_fill_call(self, address, aliases, stack,
            slots, site, words)

    def _producers(self):
        return {Path(module.__file__).name:
                hashlib.sha256(Path(module.__file__).read_bytes()).hexdigest()
                for module in (cpuset, fast_fill, buffers, __import__(__name__))}

    def bios_manifest(self):
        return dict(super().bios_manifest(), producer_sha256=self._producers())

    def cpuset_manifest(self):
        # Defence in depth: bind_root already requires a CpuSet call and the
        # owner walk checks every reached site, so an empty observation set
        # should be unreachable; refuse rather than emit an unbacked manifest.
        if not hasattr(self, '_root_fill') or not self._root_fill.observations:
            raise ValueError('mixed CpuSet fill requires an actual checked local source')
        return dict(self._root_fill.manifest(), producer_sha256=self._producers())
