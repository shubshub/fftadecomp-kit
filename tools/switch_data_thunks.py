"""Canonical _call_via_rN thunk calls inside the complete switch-data family.

Each selector keeps every rule of the complete-object-words switch-data proof
(fixed or dispatch-identified pool, with or without the write-only
outgoing-argument frame; reached u16 scalar words bound when present) and
additionally admits the compiler's indirect-call thunks. The thunk
binding is the one canonical-thunks-v1 already proves: a ROM-checked
``bx rN; mov r8, r8`` pair under the conditional returning indirect ARM ABI.
Function words, local buffers, other runtimes and a second table stay refused.
A thunk call is bound exactly once, in the ``thunks`` list; the ordinary
``calls`` list never names a thunk.
"""

import hashlib

POLICY = 'canonical-call-thunks-v1'
# selector -> (schema, outgoing frame). Only the fixed-gap pool layout is admitted.
SELECTORS = {
    'switch-thunks-v1': ('elf-symbol-thumb-switch-data-thunks-v1', False),
    'switch-thunks-frame-v1': ('elf-symbol-thumb-switch-data-thunks-frame-v1', True),
}
SCHEMAS = {selector: value[0] for selector, value in SELECTORS.items()}
BY_SCHEMA = {schema: selector for selector, schema in SCHEMAS.items()}
SUMMARIES = {
    selector: ('one guarded local Thumb table with complete mapped object words, u16 scalar words '
               'where present, and canonical call thunks'
               + (' and a fixed write-only outgoing-argument frame' if frame else ''))
    for selector, (_, frame) in SELECTORS.items()}
FIELDS = frozenset(('thunk_policy', 'thunks', 'dependencies'))


def selected(selector):
    return type(selector) is str and selector in SELECTORS


def framed(selector):
    """Whether a selector admits the write-only outgoing-argument frame."""
    if not selected(selector):
        raise ValueError('switch thunks require an explicit versioned selector')
    return SELECTORS[selector][1]


def selector_for_manifest(manifest):
    """The selector a thunk manifest's markers name, or None when it has no thunk policy."""
    if type(manifest) is not dict or 'thunk_policy' not in manifest:
        return None
    if manifest['thunk_policy'] != POLICY or 'pool_policy' in manifest:
        raise ValueError('switch thunks require their canonical policy marker and fixed pool layout')
    return 'switch-thunks-frame-v1' if 'stack_policy' in manifest else 'switch-thunks-v1'


def selector_for_report(report):
    """The selector a saved report's verification line names; callers must replay it."""
    lines = [line for line in report.splitlines() if line.lstrip().startswith('* verification')]
    for selector, schema in SCHEMAS.items():
        if lines == [f'* verification: `{schema}`']:
            return selector
    if any(schema in line for line in report.splitlines() for schema in SCHEMAS.values()):
        raise ValueError('mixed or malformed switch-thunk selection')
    return None


def exact(left, right):
    """Compare manifest facts as canonical JSON, so 4.0 or true cannot stand for 4 or 1."""
    import json
    return json.dumps(left, sort_keys=True) == json.dumps(right, sort_keys=True)


def check_link(selector, function_relocations, targets):
    """Binding gate: every runtime-helper call is a canonical alias and at least one exists."""
    from match import RUNTIME_HELPERS
    import function_thunk_profile as function_thunk
    framed(selector)
    thunks = {name for name, target in targets.items() if target in RUNTIME_HELPERS.values()}
    if function_relocations or not thunks or any(
            name not in function_thunk.ALIASES or function_thunk.ALIASES[name] != targets[name]
            for name in thunks):
        raise ValueError('switch thunks require canonical _call_via aliases without function words')
    return thunks


def thunk_sites(selector, calls):
    """Call sites that go through canonical thunks (at least one is required)."""
    import function_thunk_profile as function_thunk
    from match import RUNTIME_HELPERS
    framed(selector)
    sites = {site for site, target in calls.items() if target in RUNTIME_HELPERS.values()}
    if not sites or any(calls[site] not in function_thunk.ALIASES.values() for site in sites):
        raise ValueError('switch thunk calls differ from the selector')
    return sites


def verify_thunk_targets(instructions, edges, address, calls, pointer):
    """Refuse a thunk call whose target register may hold a local code address.

    Local provenance enters through every load of the switch table pointer
    literal at ``pointer``, any other read of PC, the entry return address and
    the return address each BL leaves in LR. It follows every register
    operation and every load whose address uses a tainted register, so table
    entries and the dispatch registers that stay live into the cases are
    tainted too. No store may use a tainted register, and pops are tainted
    because stack words are not tracked, so provenance cannot be laundered
    through memory. Results returned by callees are untainted under the
    ordinary call ABI premise; values loaded through untainted addresses and
    values built from immediates are not tracked.

    The walk is a new decode of every reached instruction, so it admits only
    16-bit encodings plus the bound BL pairs, and refuses ``svc``, ``bkpt`` and
    ``udf`` (kit #180): the model must agree with the ARM7TDMI on every byte.
    """
    import function_thunk_profile as function_thunk
    from capstone import CS_GRP_INT
    from capstone.arm import (ARM_INS_BKPT, ARM_INS_BL, ARM_INS_SVC, ARM_INS_UDF, ARM_OP_MEM,
                              ARM_REG_LR, ARM_REG_PC, ARM_REG_R0, ARM_REG_R12, ARM_REG_SP)
    from match import CALLER_CLOBBERED
    registers = {*range(ARM_REG_R0, ARM_REG_R12 + 1), ARM_REG_LR}
    thunks = {site: ARM_REG_R0 + (target - function_thunk.START) // 4
              for site, target in calls.items() if target in function_thunk.ALIASES.values()}
    states = {}
    pending = [(address, frozenset((ARM_REG_LR,)))]
    while pending:
        site, incoming = pending.pop()
        if site in states and incoming <= states[site]:
            continue
        tainted = states[site] = states.get(site, frozenset()) | incoming
        item = instructions[site]
        if item.size != 2 and not (item.id == ARM_INS_BL and item.size == 4 and site in calls) or \
                item.id in (ARM_INS_BKPT, ARM_INS_UDF, ARM_INS_SVC) or CS_GRP_INT in item.groups:
            raise ValueError('switch thunks admit only 16-bit ARMv4T encodings and bound BL pairs')
        read, written = item.regs_access()
        read, written = set(read), set(written) & registers
        literals = [((item.address + 4) & ~3) + operand.mem.disp for operand in item.operands
                    if operand.type == ARM_OP_MEM and operand.mem.base == ARM_REG_PC]
        if item.id == ARM_INS_BL:
            if thunks.get(site) in tainted:
                raise ValueError('thunk target register can hold a local code address')
            tainted = (tainted - set(CALLER_CLOBBERED) if site in calls else tainted) | {ARM_REG_LR}
        elif item.mnemonic == 'pop':
            tainted = tainted | written
        elif item.mnemonic.startswith(('str', 'stm')):
            if tainted & read:
                raise ValueError('a local code address cannot be stored')
        elif item.mnemonic != 'push':
            source = literals == [pointer] if literals else \
                item.mnemonic == 'adr' or bool(read & (tainted | {ARM_REG_PC, ARM_REG_SP}))
            tainted = tainted | written if source else tainted - written
        pending.extend((target, frozenset(tainted)) for target in edges[site])


def fingerprint(address, data, manifest):
    from match_evidence import switch_manifest
    selector = selector_for_manifest(manifest)
    framed(selector)
    proof = hashlib.sha256()
    for payload in (SCHEMAS[selector].encode('ascii'), address.to_bytes(4, 'little'),
                    data, switch_manifest(manifest).encode('ascii')):
        proof.update(len(payload).to_bytes(8, 'little'))
        proof.update(payload)
    return proof.hexdigest()
