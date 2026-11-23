"""Jump-table callees in the default stack buffer walk (kit #241).

A local pointer that reaches a callee dispatching through an agbcc jump table
made the plain buffer walk decode the callee with no switch layout, reach
`mov pc, r0` and refuse (`unresolved program-counter write`).  The layout is
already proved by `GuardedSwitchBufferProof.inspect`
(named_data_buffer_profile), but only under `bounded-buffer-guarded-switch-v1`
and its relatives.

This module makes that same proof available to the plain stack-argument
buffer proof of the default path, and nowhere else.  It adds no rule of its
own: when `analyze.refine_function` finds a word switch in an inspected
callee, inspection is delegated to an unchanged `GuardedSwitchBufferProof`
built on the same ROM, mapping and index, as `NamedDataBufferProof.inspect`
builds its delegate, but without that path's refusal of calls: direct calls
and two-constant tables are admitted, as under `bounded-buffer-guarded-switch-v1`.
`GuardedSwitchBufferProof.inspect` requires

1. exactly one table, with zero or two interposed scalar words;
2. the canonical unsigned-guarded dispatch, a bound covering the table and
   every case a forward offset inside the callee (`analyze.refine_function`);
3. no local BL control, and every direct call a canonical indexed function;
4. the callee CFG verified by `verify_leaf_instructions` with the table words
   as switch relocations, and equal to the complete owner-graph instruction set.

It returns the verified instructions and the dispatch's finite successors.
The plain proof's own alias walk then follows every case under its unchanged
access, escape, join and return rules.  The selectors' span checks (owner size,
dependency budget, index-row agreement) are not applied; the plain walk's own
span rules apply, as for every other callee.  A callee with no word switch takes the
plain path as before; any other layout, including the preloaded one, is
refused as before.

Each delegated callee's `complete-guarded-buffer-switch-v1` record is bound
into the buffer fingerprint (only when one exists) and stated in one report
line; replay recomputes them.
"""
import json

POLICY = 'guarded-switch-callee-v1'


def require(condition, message):
    if not condition:
        raise ValueError(message)


class SwitchCallees:
    """The jump-table callees one plain buffer proof inspected, and their records."""

    def __init__(self, rom, mapping, index):
        require(all(type(value) is bytes for value in (rom, mapping, index)),
                'switch callees require immutable ROM, mapping and index snapshots')
        self.rom, self.mapping, self.index = rom, mapping, index
        self.records = {}
        self._entries = None

    def entries(self):
        """The decoded mapping, decoded once: `analyze.refine_function` only reads it."""
        if self._entries is None:
            self._entries = json.loads(self.mapping)
        return self._entries

    def inspect(self, proof, address, data):
        """The delegated inspection of a jump-table callee, or None for any other callee."""
        import analyze
        import named_data_buffer_profile as named
        require(proof.switch_callees is self and proof.stack_arguments,
                'switch callees require their plain stack-argument buffer proof')
        refinement = analyze.refine_function(data, address, self.entries(),
            max_bytes=len(data), max_instructions=len(data) // 2, rom_end=0x09000000,
            same_owner_long_branches=True, two_constant_word_switch=True)
        if not refinement['word_switches']:
            return None
        delegate = named.GuardedSwitchBufferProof(self.rom, self.mapping, self.index, None)
        import callee_saved_watch
        callee_saved_watch.delegate(delegate, proof)
        instructions, transfers = delegate.inspect(address, data)
        record = delegate.records[address]
        previous = self.records.setdefault(address, record)
        require(previous == record, 'switch callee inspected differently on different paths')
        return instructions, transfers

    def evidence(self):
        return dict(policy=POLICY, callees=[self.records[address] for address in sorted(self.records)])

    def lines(self):
        """One report line per delegated callee; empty when none was inspected."""
        lines = []
        for address in sorted(self.records):
            structure = self.records[address]['structure']
            switch = structure['switch']
            lines.append(f'* buffer switch callee: `{POLICY}` 0x{address:08X}: dispatch at '
                         f'0x{structure["transfer"]:08X}, {len(structure["successors"])} successors, '
                         f'{switch.get("interposed_words", 0)} scalar words, table '
                         f'{structure["table_words_sha256"][:16]}')
        return lines
