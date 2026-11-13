"""Explicit one-object word switch, CpuSet fill and returned local aliases.

Only existing native bounded-callee return facts cross the strict frame seam.
This does not grant memory permissions, initialization or BIOS destination bounds.
"""
import hashlib
import json
from pathlib import Path
import struct

import match
import named_data_buffer_profile as named
import bios_cpuset_fill_profile as bios
import owner_graph_profile as graph

SELECTOR = named.BIOS_WORD_SWITCH_SELECTOR
SCHEMA = named.BIOS_WORD_SWITCH_SCHEMA
CONTROL_FLOW = ('complete one-object word switch with bounded local buffers, retained '
                'native callee-return aliases and conditional BIOS CpuSet fill source bounds')
RETURN_POLICY = 'native-returned-local-aliases-v1'


def refine(data, address, mapping):
    import analyze
    return analyze.refine_function(data, address, json.loads(mapping),
        max_bytes=len(data), max_instructions=len(data)//2, rom_end=0x09000000,
        same_owner_long_branches=True, one_object_word_switch=True)


class BiosWordSwitchBufferProof(named.BiosFillSourceProof):
    def bind_root(self, data, address, calls, words):
        import owner_runtime_profile as operations
        if hasattr(self, '_root_switch'):
            raise ValueError('BIOS word-switch context is single use')
        named.validate_owner(data, address, self.rom, self.mapping, self.index)
        refinement = refine(data, address, self.mapping)
        ins, edges, branches, actual, actual_words = graph.graph(
            data, address, refinement, one_object_word_switch=True)
        switches = refinement['word_switches']
        if branches or calls != actual or words != actual_words or len(switches) != 1 or \
                switches[0].get('interposed_words') != 1:
            raise ValueError('BIOS buffer requires one exact one-object-word switch without local BL')
        operations.verify_operations(ins, edges, address, branches, calls, refinement)
        offset = switches[0]['literal'] - 4
        value = struct.unpack_from('<I', data, offset)[0]
        if not (0x02000000 <= value < 0x04000000 or match.ROM_BASE <= value < match.ROM_BASE+len(self.rom)):
            raise ValueError('interposed switch object must be a RAM or ROM point')
        self.switch_data = {offset: ('native-switch-object', value)}
        layout = match.switch_layout(data, address, words, self.switch_data)
        self._root_fill = bios.BiosFillProof(data, address, self.rom,
            self.mapping, self.index, calls, one_object_word_switch=True)
        self._root_switch = (bytes(data), address, dict(calls), dict(words))
        self._root_graph = ({site: bytes(item.bytes) for site,item in ins.items()}, edges)
        self._root_manifest = dict(schema=SCHEMA, switch=layout,
            partition=graph.partition(data,address,refinement,ins,words),
            body_sha256=hashlib.sha256(data).hexdigest(), **self.identities)
        self.return_observations = set()

    def validate_frame(self, instructions, edges, address, branches, calls):
        if type(self) is not BiosWordSwitchBufferProof or not hasattr(self, '_root_switch') or \
                branches or address != self._root_switch[1] or calls != self._root_switch[2] or \
                ({site: bytes(item.bytes) for site,item in instructions.items()}, edges) != self._root_graph:
            raise ValueError('returned aliases require their exact authenticated root graph')

    def check_call(self, address, aliases, stack, slots=None, *, constants=None, site=None, words=None):
        if not hasattr(self, '_root_switch') or self._root_switch[2].get(site) != address or slots or words:
            raise ValueError('BIOS word-switch calls require exact root sites without pointer slots')
        result = super().check_call(address, aliases, stack, slots,
            constants=constants, site=site, words=words)
        if type(result) is not dict or any(type(reg) is not int or reg not in match.CALLER_CLOBBERED or
                reg == match.ARM_REG_LR or type(offset) is not int for reg,offset in result.items()):
            raise ValueError('native returned alias facts require exact caller-clobbered local offsets')
        for register, offset in result.items():
            self.access(offset, 1, stack)
            self.return_observations.add((site,address,register-match.ARM_REG_R0,offset))
        return result

    def root_manifest(self):
        import local_long_branch_profile as frame
        import owner_admission_profile as owner
        import owner_runtime_profile as operations
        if {row[0] for row in self._root_fill.observations} != {
                site for site,target in self._root_switch[2].items() if target == bios.ADDRESS}:
            raise ValueError('every CpuSet site requires an actual checked local fill source')
        return dict(self._root_manifest, returned_local_alias_policy=RETURN_POLICY,
            returned_local_aliases=[list(row) for row in sorted(self.return_observations)],
            bios_fill=self.bios_manifest(),
            contract='Native bounded helper replay authenticates every returned local alias; '
                'subsequent accesses, calls, joins, lifetimes and exits remain checked. '
                'Ordinary calls without tracked arguments retain the returning ABI premise. '
                'BIOS source-unit bounds are conditional on the existing CpuSet fill contract. '
                'No initialization, physical memory permissions, nonalias, destination bounds, '
                'numeric results, arithmetic C equivalence or termination theorem.',
            producer_sha256={Path(module.__file__).name:hashlib.sha256(Path(module.__file__).read_bytes()).hexdigest()
                for module in (bios,named,graph,frame,owner,operations,match,__import__(__name__))})

    def fingerprint(self):
        return hashlib.sha256((super().fingerprint()+json.dumps(self.root_manifest(),
            sort_keys=True,separators=(',',':'))).encode()).hexdigest()


def context(proof, data, address, calls, words, data_words):
    if type(proof) is not BiosWordSwitchBufferProof:
        return False
    if not hasattr(proof,'_root_switch') or proof._root_switch != (data,address,calls,words) or \
            data_words != proof.switch_data:
        raise ValueError('BIOS word-switch differs from authenticated complete root')
    return True


def control_words(instructions, edges, calls, partition, address):
    return sorted(bios.scalar_control_words(instructions,edges,calls,partition,address) +
                  bios.saved_scalar_control_words(instructions,edges,calls,partition,address))
