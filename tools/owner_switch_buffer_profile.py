"""A guarded jump table in the owner of the default typed-data buffer walk.

An owner with typed object literals that passes a local buffer to a callee is
proved on the default path by `data_buffer_profile.prove`, which runs the plain
stack-argument `BufferCallProof`.  When the owner itself dispatched through an
agbcc jump table, that proof never ran: the link had switch relocations, so
`match.py` sent the owner to the switch profiles, whose walk carries no buffer
proof and refuses at the first stack alias that reaches a call (`stack aliases
cannot cross calls in caller-clobbered registers`, or `unsupported stack-alias
use or escape` for an outgoing stack argument).  When that walk refuses a plain
switch-data owner for any reason, `match.py` now runs the typed-data proof; if
it refuses too, both messages are reported.  The switch profiles were
introduced as closed evidence that no buffer proof could join ("switch evidence
cannot combine frame or buffer proof profiles"): a buffer report had no record
of a switch, and its replay no way to recover the switch edges.

This module supplies that record; the walk itself is unchanged.  It already
treats an authenticated switch as one multi-way branch, following every table
target with the same abstract state (aliases, stack, pointer slots and return
provenance), keeps the table and its pointer out of the executed bytes, and
refuses runtime call thunks beside a switch.  `OwnerSwitch` authenticates the
switch from the ROM bytes with the primitives `GuardedSwitchBufferProof.inspect`
uses for a callee (named_data_buffer_profile, reused for callees by
switch_callee_profile):

1. the proof is the default path's plain stack-argument `BufferCallProof`
   (the instance with jump-table callee summaries), bound to one owner only
   (`owner switch requires the default plain stack-argument buffer proof`);
2. `analyze.refine_function` finds exactly one word switch, with no interposed
   scalar words (`owner switch requires one guarded table without scalar words`),
   unless the words are the dispatch's own literal pool placed by
   `interposed_pool_switch` (each reserved as data, read by a reached PC load and
   bound by the typed-data proof as an ordinary literal; the report line says so);
3. `owner_graph_profile.graph` closes the owner CFG with no local BL control
   (`owner switch excludes local BL control`), apart from the switch's own far
   default arm: agbcc's `bls dispatch; bl default` guard, a same-owner BL the
   layout already recognizes.  The walk takes it as a jump that loses LR (no
   call ABI, no continuation), so every later return must still come from the
   saved entry LR; the report line states the arm (FAR_DEFAULT).  When the
   default block is the owner's shared tail, agbcc reaches it with a far BL
   from elsewhere in the owner too (a `return 1` beyond a narrow branch's
   reach, from a case or from before the switch).  Every same-owner BL to that
   target, wherever it sits, is walked the same way when every same-owner BL
   targets the guard arm's own target and the guard's BL is one of them
   (SHARED_FAR_DEFAULT); a far BL to any other block still refuses;
4. the linked object's switch relocations and direct calls are exactly those the
   ROM bytes give (`owner switch differs from its linked relocations`);
5. the walk re-derives the layout from those table words (`match.switch_layout`:
   the canonical unsigned guard, a bound covering the table, forward in-span
   cases) and refuses any path into the guard or the dispatch that bypasses the
   comparison (`switch selector bound is bypassed by an unverified predecessor
   edge`);
6. the walk's verified instructions are exactly the owner graph's
   (`owner switch walk differs from the complete owner graph`).

At the owner's own normal returns, an address inside its expired frame left in
R2 or R3 is dropped and recorded (OWNER_EXIT_SCRATCH), under the
`thumb-discarded-exit-scratch-v1` premise the kit already states at other
roots: R2/R3 carry no results under the agbcc Thumb ABI, so the owner's caller
never reads them (a premise about the callers, not checked; every record and
line states it).  R0/R1, every callee return and every other alias keep the
escape refusal (`local stack pointer escapes through a return register`), and
so does a walk that kept any join apart (split_join_profile), on any register:
its split states can reach one return with different R2/R3 offsets (directly,
or copied from a split R12, which the return check exempts), and the record
names one offset per return.  It binds only the plain proof's owner with its
authenticated far default arms and table, whose returns end the walk; the
stack-index leaf keeps its own binding.  The hook is exit_scratch_aliases,
which match.py calls at every stack-argument return.

The walk runs without incoming narrow reads.  The table pointer counts as the
switch's word, not an untyped literal, when the dispatch's load is its only PC
load; as in the switch profiles (#139), what the cases do with the table base or
the case address left in registers after the dispatch is not checked (both are
ROM code addresses, never stack aliases), and the report line says so.  The
record (layout, transfer, successors, table hash) is bound into the buffer
fingerprint and stated in one `* buffer owner switch:` line; the data-buffer
replay relinks the source and recomputes both.
"""
import hashlib
import json

POLICY = 'guarded-switch-owner-v1'
LINE = '* buffer owner switch'
# Stated in each report line: what the typed-literal coverage checks of the table pointer.
POINTER_RULE = 'table pointer: only PC load is the dispatch, case uses of the table registers unchecked'
# The switch's own far default arm (a same-owner BL in the guard), taken as a jump that loses LR.
FAR_DEFAULT_NAME = 'guarded-switch-far-default-v1'
FAR_DEFAULT_RULE = ('far default arm ({name}): same-owner BL at 0x{site:08X} to 0x{target:08X} taken as a jump '
                    'that loses LR; every return re-proved from the saved entry LR')


class FarDefault:
    """The far-default arm's single switch; False restores `owner switch excludes local BL control`."""
    enabled = True


FAR_DEFAULT = FarDefault()
# Further same-owner BLs to the far default arm's own target (the owner's shared tail).
SHARED_FAR_DEFAULT_NAME = 'guarded-switch-shared-far-default-v1'
SHARED_FAR_DEFAULT_RULE = ('shared far default ({name}): same-owner BLs at {sites} to 0x{target:08X}, the guard '
                           'arm\'s own target, each taken as a jump that loses LR; every return re-proved from '
                           'the saved entry LR')


class SharedFarDefault:
    """Further same-owner BLs to the far default's target; False keeps the guard's arm only."""
    enabled = True


SHARED_FAR_DEFAULT = SharedFarDefault()
# R2/R3 own-frame addresses at the plain owner's normal returns.
EXIT_SCRATCH_LINE = '* buffer owner switch exit scratch'


class OwnerExitScratch:
    """The plain owner's R2/R3 return projection; False restores the escape refusal."""
    enabled = True


OWNER_EXIT_SCRATCH = OwnerExitScratch()
# The plain switch-data manifests (one or several typed objects); every other switch
# policy keeps its own walk and refusal.
PLAIN_FIELDS = frozenset(('calls', 'switch', 'data', 'data_policy'))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def far_default(switch, address, branches):
    """{site: target} of the switch's own far default BL and of every other BL to that target.

    branches are the owner graph's same-owner BL edges.  The guard's BL to the layout's
    default must be one of them; any BL to another block refuses.  More than one edge
    needs SHARED_FAR_DEFAULT.
    """
    if not branches:
        return {}
    branches = dict(branches)
    site, target = address + switch['guard'] + 2, address + switch['default']
    require(FAR_DEFAULT.enabled and switch['dispatch'] - switch['comparison'] == 8 and
            branches.get(site) == target and set(branches.values()) == {target} and
            (len(branches) == 1 or SHARED_FAR_DEFAULT.enabled), 'owner switch excludes local BL control')
    return branches


class OwnerSwitch:
    """The one guarded jump table of the owner a plain buffer proof walks."""

    def __init__(self, proof, data, address, calls, linked):
        import analyze
        import match
        import owner_graph_profile as graph
        from stack_index_precondition_profile import StackIndexV2BufferProof
        plain = type(proof) is match.BufferCallProof and proof.switch_callees is not None
        indexed_leaf = type(proof) is StackIndexV2BufferProof and not calls
        require((plain or indexed_leaf) and proof.stack_arguments is True and proof.owner_switch is None,
                'owner switch requires the default plain stack-argument buffer proof or a bounded-index leaf')
        import interposed_pool_switch as pool
        data = bytes(data)
        refinement = analyze.refine_function(data, address, json.loads(json.dumps(proof.entries)),
            max_bytes=len(data), max_instructions=len(data) // 2, rom_end=0x09000000,
            same_owner_long_branches=True, interposed_pool_switch=pool.POLICY.enabled)
        switches = refinement['word_switches']
        require(len(switches) == 1 and (not switches[0].get('interposed_words', 0) or pool.marked(switches[0])),
                'owner switch requires one guarded table without scalar words')
        instructions, edges, branches, actual, words = graph.graph(data, address, refinement)
        self.returns = frozenset(int(site, 16) for site in refinement['returns'])
        self.returns_end = bool(self.returns) and not any(edges[site] for site in self.returns)
        require(plain or not branches, 'owner switch excludes local BL control')
        # The walk takes this arm as a jump; match.verify_leaf_instructions re-derives it.
        self.branches = far_default(switches[0], address, branches)
        require(dict(linked) == words and dict(calls) == actual,
                'owner switch differs from its linked relocations')
        layout = {key: value for key, value in switches[0].items() if key != 'schema'}
        transfer = address + layout['dispatch'] + 8
        if indexed_leaf:
            partition = graph.partition(data, address, refinement, instructions, words)
            for word in partition['words']:
                if word['switch_word']:
                    expected = [transfer - 6] if word['address'] == address + layout['literal'] else []
                    require(word['load_sites'] == expected,
                            'bounded-index leaf switch words may only feed the canonical dispatch')
        self.key = (data, address, dict(actual), dict(words))
        self.instructions = frozenset(instructions)
        self.record = dict(policy=POLICY, address=address, end=address + len(data), bytes=len(data),
            body_sha256=hashlib.sha256(data).hexdigest(), switch=layout, transfer=transfer,
            successors=list(edges[transfer]),
            table_words_sha256=hashlib.sha256(b''.join(
                data[offset:offset + 4] for offset in sorted(words))).hexdigest())
        if len(self.branches) == 1:
            # Only an owner whose switch has the far default arm carries this key.
            (site, target), = self.branches.items()
            self.record['far_default'] = dict(policy=FAR_DEFAULT_NAME, site=site, target=target)
        elif self.branches:
            # An owner that reaches the same target by further far BLs carries this key instead.
            target, = set(self.branches.values())
            self.record['shared_far_default'] = dict(policy=SHARED_FAR_DEFAULT_NAME, target=target,
                                                     sites=sorted(self.branches))
        self.cursor = None
        from menu_local_cursor import OWNER, END, MenuCursor
        if plain and address == OWNER and address + len(data) == END:
            self.cursor = MenuCursor(instructions, edges)
        self.complete = False

    def evidence(self):
        require(self.complete, 'owner switch walk is incomplete')
        if self.cursor is not None:
            self.record['local_cursor'] = self.cursor.evidence()
        return self.record

    def lines(self):
        import interposed_pool_switch as pool
        record = self.evidence()
        cursor = record.get('local_cursor')
        detail = (f"; counted local STM at 0x{cursor['store']:08X} through SP offsets {cursor['offsets']}, "
                  f"adjacent output at SP+{cursor['adjacent_output']}" if cursor else '')
        if 'pool_policy' in record['switch']:
            detail += '; ' + pool.RULE.format(words=record['switch']['interposed_words'])
        if 'far_default' in record:
            arm = record['far_default']
            detail += '; ' + FAR_DEFAULT_RULE.format(name=arm['policy'], site=arm['site'], target=arm['target'])
        if 'shared_far_default' in record:
            arm = record['shared_far_default']
            detail += '; ' + SHARED_FAR_DEFAULT_RULE.format(
                name=arm['policy'], target=arm['target'], sites=', '.join(f'0x{site:08X}' for site in arm['sites']))
        lines = [f'{LINE}: `{POLICY}` 0x{record["address"]:08X}: dispatch at 0x{record["transfer"]:08X}, '
                 f'bound {record["switch"]["bound"]}, {len(record["successors"])} successors, '
                 f'table {record["table_words_sha256"][:16]}; {POINTER_RULE}{detail}']
        if 'exit_scratch' in record:
            scratch = record['exit_scratch']
            sites = ', '.join(f'`0x{site:08X} r{register} {offset:+d}`' for site, register, offset in scratch['sites'])
            lines.append(f"{EXIT_SCRATCH_LINE}: `{scratch['schema']}` premise, not checked: {scratch['contract']}; "
                         f"own-frame addresses dropped at the owner's normal returns: {sites}; R0/R1 and every "
                         f"callee return keep the escape refusal")
        return lines

    def bind_exit_scratch(self, proof, address, data):
        """Bind the R2/R3 return projection (named_data_buffer_profile.RootReturnScratchMixin) to proof."""
        import match
        require(type(proof) is match.BufferCallProof and proof.owner_switch is self and
                getattr(proof, '_return_root', None) is None and self.key[:2] == (bytes(data), address) and
                self.returns_end, 'owner exit scratch requires the plain owner and its complete normal returns')
        proof._return_root = (address, bytes(data), self.returns)
        proof._return_scratch = {}
        proof._return_scratch_joins = set()

    def record_exit_scratch(self, proof):
        """After the walk: the final projected sites, bound into the record only when there are any."""
        from local_long_branch_profile import DISCARDED_SCRATCH_SCHEMA, DISCARDED_SCRATCH_CONTRACT
        sites = sorted((site, register, offset)
                       for site, pairs in proof._return_scratch.items() for register, offset in pairs)
        require(not proof._return_scratch_joins, 'owner exit scratch projects no joins')
        require(not (sites and _split_walk(proof, self.record['address'])),
                'owner exit scratch refuses a walk that kept a join apart')
        if sites:
            self.record['exit_scratch'] = dict(schema=DISCARDED_SCRATCH_SCHEMA, registers=[2, 3],
                                               contract=DISCARDED_SCRATCH_CONTRACT,
                                               sites=[list(site) for site in sites])


def _split_walk(proof, address):
    """Whether the walk of `address` kept any join apart (on any register)."""
    return any(key[0] == address for key in getattr(proof, 'split_joins', {}))


def exit_scratch_aliases(proof, data, address, site, aliases):
    """The plain owner's R2/R3 return projection, bound only by walk() (OWNER_EXIT_SCRATCH).

    Any other proof, an unbound one and a walk that kept a join apart keep the aliases, so the
    walk's escape refusal stands.  The projection itself is RootReturnScratchMixin's: only the bound
    owner's own normal returns, never a callee walk, and only addresses inside its expired frame.
    """
    import match
    if type(proof) is not match.BufferCallProof or proof.owner_switch is None or \
            getattr(proof, '_return_root', None) is None or _split_walk(proof, address):
        return aliases
    from named_data_buffer_profile import RootReturnScratchMixin
    return RootReturnScratchMixin.root_return_aliases(proof, data, address, site, aliases)


def retries(manifest, args, calls, data_relocations, function_relocations, thumb, matches_rom):
    """Whether match.py's default switch path retries a refused owner under the typed-data buffer proof.

    Structural only: which refusal the buffer-free switch walk raises first depends on its
    walk order, and the data-buffer replay runs the proof whenever the link has a table.
    matches_rom: the linked bytes equal the ROM span; a mismatch keeps its own refusal alone.
    """
    return matches_rom is True and thumb is True and bool(calls) and bool(data_relocations) and \
        not function_relocations and args.switch_data_profile is None and isinstance(manifest, dict) and \
        set(manifest) <= PLAIN_FIELDS and 'preload' not in manifest['switch']


def walk(proof, data, address, calls, linked):
    """Bind the owner's switch to proof and run the unchanged plain walk over it.

    calls and linked are the linked object's direct calls and switch relocations.
    """
    import match
    owner = OwnerSwitch(proof, data, address, calls, linked)
    proof.owner_switch = owner
    exit_scratch = False
    if proof.index_policy is not None:
        proof.index_policy.owner_switch = owner
        from named_data_buffer_profile import RootReturnScratchMixin
        RootReturnScratchMixin.bind_return_root(proof, address, data, indexed_leaf=owner)
    elif type(proof) is match.BufferCallProof and OWNER_EXIT_SCRATCH.enabled and owner.returns_end:
        owner.bind_exit_scratch(proof, address, data)
        exit_scratch = True
    _, _, calls, words = owner.key
    instructions = match.verify_leaf_instructions(data, address, True, calls, buffer_proof=proof,
                                                  switch_relocations=words)
    require({item.address for item in instructions} == owner.instructions,
            'owner switch walk differs from the complete owner graph')
    if exit_scratch:
        owner.record_exit_scratch(proof)
    owner.complete = True
    return instructions


def context(proof, data, address, calls, words, data_words):
    """True when proof carries the bound switch of exactly this owner walk."""
    owner = getattr(proof, 'owner_switch', None)
    if owner is None:
        return False
    require(data_words is None and owner.key == (bytes(data), address, dict(calls or {}), dict(words)),
            'owner switch differs from its authenticated owner')
    return True
