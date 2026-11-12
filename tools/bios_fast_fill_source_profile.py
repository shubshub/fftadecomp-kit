"""Explicit conditional CpuFastSet fill with a bounded root-local source word."""
import hashlib
from pathlib import Path

import bios_cpuset_fill_profile as bits
import match
import named_data_buffer_profile as buffers
import owner_graph_profile as graph

ADDRESS = 0x08141868
WRAPPER = bytes.fromhex('0cdf7047')
SCHEMA = 'conditional-bios-cpufastset-local-fill-source-v1'
MIXED_SCHEMA = 'conditional-bios-cpufastset-mixed-local-fill-source-v1'
CONTRACT = (
    'conditional returning GBA BIOS CpuFastSet fill boundary: control bit24 '
    'selects a repeated 32-bit source word; only the aligned local source span '
    'is proved, with an external caller-supplied destination and compatible '
    'ordinary returning ABI; no source initialization, physical readability, '
    'physical nonalias, destination capacity, numeric result or termination theorem')


class FastFillSourceProof(buffers.NamedDataBufferProof):
    """Reuse closed CFG bit facts; keep CpuSet and every old selector unchanged."""

    mixed_calls = False
    schema = SCHEMA
    contract = CONTRACT

    def bind_root(self, data, address, calls):
        import owner_admission_profile as owner
        if hasattr(self, '_root'):
            raise ValueError('CpuFastSet root context is single use')
        owner.validate_span(data, address, self.rom, self.mapping, self.index)
        refinement = owner.refine(data, address, self.mapping)
        instructions, edges, branches, actual, words = graph.graph(data, address, refinement)
        graph.partition(data, address, refinement, instructions, words)
        allowed = (ADDRESS in calls.values() if self.mixed_calls else
                   set(calls.values()) == {ADDRESS})
        if branches or words or calls != actual or not allowed:
            raise ValueError('CpuFastSet fill requires only its actual direct wrapper calls')
        wrapper = self.span(ADDRESS)
        if wrapper != WRAPPER:
            raise ValueError('CpuFastSet fill requires exact indexed SWI 0x0C return wrapper')
        self._root = (address, bytes(data), dict(calls))
        self._states = bits.prove_bits(instructions, edges, address, data)
        self._observations = set()

    def check_call(self, address, aliases, stack, slots=None, *, constants=None,
                   site=None, words=None):
        if not hasattr(self, '_root') or address != ADDRESS or self._root[2].get(site) != ADDRESS:
            raise ValueError('CpuFastSet fill requires its exact bound root call')
        arguments = {reg: offset for reg, offset in aliases.items()
                     if reg in match.CALLER_CLOBBERED}
        if slots or words or match.ARM_REG_LR in aliases or set(arguments) != {match.ARM_REG_R0}:
            raise ValueError('CpuFastSet fill requires only local R0 and an external destination')
        ones, zeros = self._states[site].get(match.ARM_REG_R0 + 2, (0, 0))
        if not ones & (1 << 24):
            raise ValueError('CpuFastSet fill bit24 is not set on every reaching path')
        offset = arguments[match.ARM_REG_R0]
        self.access(offset, 4, stack)
        data = self.span(address)
        if data != WRAPPER:
            raise ValueError('CpuFastSet complete wrapper changed')
        self.dependencies[address] = data
        self.records[address] = dict(address=address, end=address+4, bytes=4,
            body_sha256=hashlib.sha256(data).hexdigest(), **self.identities,
            structure=dict(kind=buffers.FAST_FILL_SCHEMA, instructions=2,
                wrapper_hex=data.hex(), conditional_ABI=self.contract))
        self._observations.add((site, offset, 4, ones, zeros))
        return {}

    def bios_manifest(self):
        if not hasattr(self, '_root') or not self._observations:
            raise ValueError('CpuFastSet fill requires an actual checked local source')
        address, data, _ = self._root
        return dict(schema=self.schema, contract=self.contract,
            owner=[address, len(data), hashlib.sha256(data).hexdigest()],
            dependency=[ADDRESS, len(WRAPPER), hashlib.sha256(WRAPPER).hexdigest()],
            sites=[list(row) for row in sorted(self._observations)],
            producer_sha256={Path(module.__file__).name:
                hashlib.sha256(Path(module.__file__).read_bytes()).hexdigest()
                for module in (bits, buffers, __import__(__name__))})


class MixedFastFillSourceProof(FastFillSourceProof):
    """Compose root fill sites with unchanged ordinary local-buffer checks."""

    mixed_calls = True
    schema = MIXED_SCHEMA
    contract = (CONTRACT + '; ordinary callees retain bounded-buffer checks; '
                'callee-saved control bits survive under the conditional '
                'ordinary returning ABI')

    def check_call(self, address, aliases, stack, slots=None, *, constants=None,
                   site=None, words=None):
        if not hasattr(self, '_root') or self._root[2].get(site) != address:
            raise ValueError('mixed CpuFastSet requires its exact bound root call')
        if address == ADDRESS:
            return super().check_call(address, aliases, stack, slots,
                constants=constants, site=site, words=words)
        return buffers.NamedDataBufferProof.check_call(self, address, aliases,
            stack, slots, constants=constants, site=site, words=words)
