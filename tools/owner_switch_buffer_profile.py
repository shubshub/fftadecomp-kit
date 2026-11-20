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
   scalar words (`owner switch requires one guarded table without scalar words`);
3. `owner_graph_profile.graph` closes the owner CFG with no local BL control
   (`owner switch excludes local BL control`);
4. the linked object's switch relocations and direct calls are exactly those the
   ROM bytes give (`owner switch differs from its linked relocations`);
5. the walk re-derives the layout from those table words (`match.switch_layout`:
   the canonical unsigned guard, a bound covering the table, forward in-span
   cases) and refuses any path into the guard or the dispatch that bypasses the
   comparison (`switch selector bound is bypassed by an unverified predecessor
   edge`);
6. the walk's verified instructions are exactly the owner graph's
   (`owner switch walk differs from the complete owner graph`).

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
# The plain switch-data manifests (one or several typed objects); every other switch
# policy keeps its own walk and refusal.
PLAIN_FIELDS = frozenset(('calls', 'switch', 'data', 'data_policy'))


def require(condition, message):
    if not condition:
        raise ValueError(message)


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
        data = bytes(data)
        refinement = analyze.refine_function(data, address, json.loads(json.dumps(proof.entries)),
            max_bytes=len(data), max_instructions=len(data) // 2, rom_end=0x09000000,
            same_owner_long_branches=True)
        switches = refinement['word_switches']
        require(len(switches) == 1 and not switches[0].get('interposed_words', 0),
                'owner switch requires one guarded table without scalar words')
        instructions, edges, branches, actual, words = graph.graph(data, address, refinement)
        require(not branches, 'owner switch excludes local BL control')
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
        self.complete = False

    def evidence(self):
        require(self.complete, 'owner switch walk is incomplete')
        return self.record

    def lines(self):
        record = self.evidence()
        return [f'{LINE}: `{POLICY}` 0x{record["address"]:08X}: dispatch at 0x{record["transfer"]:08X}, '
                f'bound {record["switch"]["bound"]}, {len(record["successors"])} successors, '
                f'table {record["table_words_sha256"][:16]}; {POINTER_RULE}']


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
    if proof.index_policy is not None:
        proof.index_policy.owner_switch = owner
        from named_data_buffer_profile import RootReturnScratchMixin
        RootReturnScratchMixin.bind_return_root(proof, address, data, indexed_leaf=owner)
    _, _, calls, words = owner.key
    instructions = match.verify_leaf_instructions(data, address, True, calls, buffer_proof=proof,
                                                  switch_relocations=words)
    require({item.address for item in instructions} == owner.instructions,
            'owner switch walk differs from the complete owner graph')
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
