"""Explicit consumer-bound R2 projection at conditional normal word returns.

Private prerequisite, not a selector or proof of C abstract-machine escape,
physical memory, termination, or arithmetic equivalence. R0 remains the sole
ordinary word result; all callback/helper/frame effects still replay normally.
"""
import hashlib
import json
from pathlib import Path

import match
import owner_graph_profile as graph
import callback_local_two_output_frame as local
import descriptor_output_alias_profile as frame

SCHEMA = 'consumer-bound-normal-word-return-r2-prerequisite-v1'
ABI = 'ordinary-arm-normal-return-r0-word-v1'
_KEYS = {'schema', 'abi', 'consumer', 'call_site', 'callback', 'helper',
         'rom_sha256', 'mapping_sha256', 'index_sha256', 'objects_sha256',
         'consumer_sha256', 'callback_sha256', 'helper_sha256', 'source_sha256'}


def sha(value):
    return hashlib.sha256(value).hexdigest()


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


class ConsumerBoundary:
    """Derive a fresh, exact direct-call consumer attestation, never load one.

    The explicit ABI premise restricts observable normal results to a single
    word in R0. Complete native return/frame verification and an actual R0
    scalar-result use in the continuation supplement, rather than infer, that
    premise. Source bytes bind the evidence but a declaration is not a proof.
    Indirect/canonical-veneer producers require a separate closed composition;
    they are deliberately not represented as direct calls here.
    """

    policy_keys = _KEYS

    def call_target(self, policy):
        return policy['callback']

    def __init__(self, rom, mapping, index, objects, source, *, policy=None):
        if type(policy) is not dict or set(policy) != self.policy_keys or \
                policy['schema'] != SCHEMA or policy['abi'] != ABI:
            raise ValueError('exact explicit normal-word-result ABI policy required')
        for key in ('consumer', 'call_site', 'callback', 'helper'):
            if type(policy[key]) is not int or policy[key] % 2:
                raise ValueError('aligned integer boundary identities required')
        for key in _KEYS:
            if key.endswith('_sha256'):
                value = policy[key]
                if type(value) is not str or len(value) != 64 or \
                        any(c not in '0123456789abcdef' for c in value):
                    raise ValueError('exact lowercase boundary hashes required')
        self.inputs = (rom, mapping, index, objects, source)
        for key, value in zip(('rom', 'mapping', 'index', 'objects', 'source'), self.inputs):
            if type(value) is not bytes or sha(value) != policy[key + '_sha256']:
                raise ValueError('stale boundary input: ' + key)
        self.policy = canonical(policy)
        self.receipt = self._derive()
        self.seal = sha(canonical(self.receipt).encode())

    def _derive(self):
        # owner_admission_profile imports this module through the word-result
        # callback profile; importing it here keeps this module importable first.
        import owner_admission_profile as owner
        policy = json.loads(self.policy)
        rom, mapping, index, objects, source = self.inputs
        spans = frame.DescriptorOutputAliasProof(rom, mapping, index, objects)
        bodies = {key: spans.span(policy[key]) for key in ('consumer', 'callback', 'helper')}
        for key, body in bodies.items():
            if sha(body) != policy[key + '_sha256']:
                raise ValueError('stale complete boundary owner: ' + key)
        address, data = policy['consumer'], bodies['consumer']
        refinement = owner.refine(data, address, mapping)
        instructions, edges, branches, calls, words = graph.graph(data, address, refinement)
        if branches or words or calls != {policy['call_site']: self.call_target(policy)}:
            raise ValueError('consumer requires its one authentic direct callback call')
        partition = graph.partition(data, address, refinement, instructions, words)
        structural = frame._StructuralFrameProof(rom, mapping, index, objects)
        verified = match.verify_leaf_instructions(data, address, True, validated_calls=calls,
                                                  buffer_proof=structural, call_resolver=spans.target)
        if {item.address for item in verified} != set(instructions):
            raise ValueError('consumer native frame lacks exact full CFG coverage')
        call = instructions[policy['call_site']]
        continuation = call.address + call.size
        first = instructions[continuation]
        # A real scalar-result comparison must precede any replacement of R0.
        # No branch value or numeric consequence of this comparison is assumed.
        if first.mnemonic != 'cmp' or not first.operands or \
                first.operands[0].type != match.ARM_OP_REG or \
                first.operands[0].reg != match.ARM_REG_R0:
            raise ValueError('consumer lacks inspected R0 word-result use')
        returns = {int(site, 16) for site in refinement['returns']}
        pending, paths, safe, kills, normal = [continuation], {}, set(), set(), set()
        while pending:
            site = pending.pop()
            if site in paths:
                continue
            item = instructions[site]
            reads, writes = map(set, item.regs_access())
            if match.ARM_REG_R2 in reads:
                raise ValueError('consumer reads/stores/forwards R2 before its boundary')
            if match.CS_GRP_CALL in item.groups or match.CS_GRP_INT in item.groups:
                raise ValueError('consumer forwards scratch through a call or interrupt')
            if site in returns:
                paths[site] = ()
                safe.add(site)
                normal.add(site)
            elif match.ARM_REG_R2 in writes and item.cc in (match.ARM_CC_AL, match.ARM_CC_INVALID):
                paths[site] = ()
                safe.add(site)
                kills.add(site)
            else:
                paths[site] = edges[site]
                pending.extend(edges[site])
        while True:
            added = {site for site, targets in paths.items() if site not in safe and targets
                     and all(target in safe for target in targets)}
            if not added:
                break
            safe.update(added)
        if continuation not in safe:
            raise ValueError('consumer has an unclosed scratch-live branch or loop')
        return {'schema': SCHEMA, 'policy': policy, 'abi_conditional': ABI,
                'normal_result': 'R0 single word; numeric value unknown',
                'projected_register': 'R2 only', 'consumer_instructions': len(instructions),
                'partition': partition, 'continuation': continuation,
                'checked_live_sites': sorted(paths), 'kill_frontiers': sorted(kills),
                'normal_word_return_frontiers': sorted(normal),
                'source_sha256': sha(source), 'proof': 'full native restoring-frame and closed CFG',
                'claims_excluded': ['physical memory', 'termination', 'C type equivalence',
                                    'abstract C pointer nonescape', 'unknown caller overwrites']}

    def validate(self):
        if self.seal != sha(canonical(self.receipt).encode()) or self.receipt != self._derive():
            raise ValueError('mutated or stale consumer attestation')
        return self.receipt


class WordResultScratchProof(local.CallbackLocalTwoOutputProof):
    """277 replay plus one consumer-attested, expired-local R2 projection."""

    def __init__(self, *inputs, policy=None, boundary=None):
        if type(boundary) is not ConsumerBoundary:
            raise ValueError('fresh complete consumer boundary required')
        attestation = boundary.validate()
        bound = attestation['policy']
        if tuple(inputs) != boundary.inputs[:4] or type(policy) is not dict or \
                any(policy.get(key) != bound[key] for key in ('callback', 'helper')):
            raise ValueError('callback effects and consumer boundary bindings differ')
        super().__init__(*inputs, policy=policy)
        self.boundary = boundary
        self.projections = []
        self._consumer_active = False

    def check_arguments(self, address, arguments, stack, incoming, protected, **kwargs):
        if address == self.callback:
            bound = self.boundary.validate()['policy']
            if kwargs.get('site') != bound['call_site'] or kwargs.get('root_frame') != bound['consumer']:
                raise ValueError('callback lacks its authentic bound consumer call-site')
            self._consumer_active = True
            try:
                return super().check_arguments(address, arguments, stack, incoming, protected, **kwargs)
            finally:
                self._consumer_active = False
        return super().check_arguments(address, arguments, stack, incoming, protected, **kwargs)

    def normal_return_aliases(self, address, site, aliases):
        if address != self.callback or not self._consumer_active or self._context is None:
            return aliases
        self.boundary.validate()
        if match.ARM_REG_R0 in aliases:
            raise ValueError('normal word result R0 carries a local alias')
        r2 = match.ARM_REG_R2
        if r2 not in aliases:
            return aliases
        #277 independently binds its exact 8B local frame and ordered output
        #helper. Only the second output address can leave this context in R2.
        expected = self._context[0] - 16
        if aliases[r2] != expected or any(register != r2 and value == expected
                                        for register, value in aliases.items()):
            raise ValueError('scratch projection has an unexpected or copied local alias')
        projected = dict(aliases)
        del projected[r2]
        self.projections.append({'callback': address, 'return_site': site,
            'register': 'R2', 'expired_local_offset': expected,
            'consumer_seal': self.boundary.seal, 'R0_projected': False})
        return projected

    def manifest(self):
        result = super().manifest()
        result.update({'word_return_schema': SCHEMA, 'boundary': self.boundary.validate(),
            'boundary_seal': self.boundary.seal, 'scratch_projections': list(self.projections),
            'projection_source_sha256': sha(Path(__file__).read_bytes()),
            'claim': 'private direct-call conditional word-result boundary prerequisite only; '
                     'no original R7 producer, root owner/ELF, or native admission'})
        return result
