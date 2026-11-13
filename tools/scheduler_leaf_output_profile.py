"""Compose bounded leaf output aliases with conditional scheduler invocations.

Only the existing complete leaf CFG and buffer-alias replay discharge local
pointer accesses. Other memory identities and scheduler effects stay conditional.
"""
import hashlib
from pathlib import Path

import match
import named_data_buffer_profile as named


def require(condition, message):
    if not condition:
        raise ValueError(message)


def check_call(proof, address, aliases, stack, slots, *, site):
    require(address in proof.branch_calls['ordinary_targets'],
            'scheduler leaf output requires an indexed ordinary target')
    require(not slots, 'scheduler leaf output excludes pointer-bearing slots')
    observation = dict(site=site, target=address, kind='conditional-ordinary-ABI-call')
    if aliases:
        require(set(aliases) <= set(match.CALLER_CLOBBERED) - {match.ARM_REG_LR},
                'scheduler leaf output excludes preserved-register aliases')
        helper = named.NamedDataBufferProof(proof.rom, proof.mapping,
                                            proof.index, proof.objects)
        body = helper.span(address)
        instructions, transfers = helper.inspect(address, body)
        require(not transfers and not any(match.CS_GRP_CALL in item.groups
                                         for item in instructions),
                'scheduler output helper requires a complete leaf body')
        returned = helper.check_call(address, aliases, stack, site=site)
        require(not returned, 'scheduler output helper cannot return a local alias')
        require(helper.requested == {address} and set(helper.records) == {address},
                'scheduler output helper excludes additional dependencies')
        require(proof.dependencies[address] == body,
                'scheduler output helper differs from authenticated ordinary body')
        observation = dict(site=site, target=address,
            kind='complete-leaf-buffer-alias-replay',
            aliases=sorted(aliases.items()), frame=[list(word) for word in stack],
            pointer_words=[], returned_aliases=[], helper=helper.records[address],
            source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            assumptions=[
                'Nonlocal objects are readable/writable as reached and separate from caller stack.',
                'Local pointer accesses and nonescape follow the complete existing buffer-alias replay; '
                'this establishes no value equivalence, physical memory safety or termination.'])
    require(site not in proof.observations or proof.observations[site] == observation,
            'scheduler leaf output differs across incoming call paths')
    proof.observations[site] = observation
    return {}
