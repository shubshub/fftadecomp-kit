"""Guarded word jump tables behind their dispatch block's own literal pool.

agbcc ends a jump-table dispatch with `mov pc, rN`, an unconditional transfer,
so the pending literal pool is flushed right there: the words that earlier
blocks load with `ldr rX, [pc, #imm]` (numbers, RAM and ROM object addresses)
sit between the dispatch and the table-pointer word.  The pointer is the last
pool word because the dispatch's own load is emitted last, and the table
follows it.  `match.switch_layout` looks for the pointer only at a fixed pool
position (no words or five, or a run of link-time object relocations), so the
owner refinement leaves such a dispatch unresolved, and the owner route and
the default path's owner-switch buffer proof refuse the whole owner.

This rule places the table with the existing dispatch-identified layout,
`match.switch_layout(..., interposed_pool=True)` (the primitive of the
`u16-scalars-v2` switch-data selector), and adds no fact about the table:

* location: the exact five-op dispatch (lsls #2; ldr [pc]; adds; ldr [rN];
  mov pc) whose PC load reaches the pointer word, and only zero alignment
  between `mov pc` and the pool; the pointer is the address of the next word;
* extent: the guard's `cmp selector, #imm` on the dispatch's selector, one of
  the three canonical guards, with every instruction from the compare to
  `mov pc` reached only through its guarded predecessor;
* entries: every table word an even address in the owner, after the table
  (forward cases only, never into the guard, dispatch, pool, pointer or
  table bytes), each a CFG edge onto a decoded instruction.

The pool words are data, never code: the refinement reserves every byte from
the dispatch's end to the pointer, requires a reached PC load of every pool
word, and the owner's proof then binds each loaded word under its existing
literal rules (a typed object relocation for a RAM or ROM address, a number
otherwise).  The layout is tried only where every existing layout found no
table, so a refinement or a link that resolves a table today is unchanged;
`POLICY.enabled = False` restores every refusal.
"""

NAME = 'interposed-pool-word-switch-v1'
# Stated in the report line of an owner switch that uses this rule.
RULE = ('table behind its {words}-word literal pool (' + NAME + '): every pool word reserved as data, '
        'read by a reached PC load and bound as a literal')


class Policy:
    """The rule's single switch."""
    enabled = True


POLICY = Policy()


def pool_words(address, descriptor):
    """The number of words from the dispatch's word-aligned end to the table pointer."""
    start = ((address + descriptor['dispatch'] + 13) & ~3) - address
    words, rest = divmod(descriptor['literal'] - start, 4)
    if rest or words < 0:
        raise ValueError('interposed switch pool is not word aligned before its table pointer')
    return words


def refine(data, address, relocations, dispatch, comparison):
    """The refinement descriptor of one table behind an interposed pool, or None.

    relocations are the pointer and table words read from the bytes, for the
    bound of the compare at `comparison`; the layout must have exactly that
    dispatch and compare, and at least one interposed word.
    """
    import match
    try:
        descriptor = match.switch_layout(data, address, relocations, interposed_pool=True)
    except ValueError:
        return None
    if descriptor['dispatch'] != dispatch or descriptor['comparison'] != comparison:
        return None
    words = pool_words(address, descriptor)
    if not words:
        return None
    descriptor['interposed_words'] = words
    descriptor['pool_policy'] = NAME
    return descriptor


def marked(switch):
    """True for a refinement descriptor this rule produced, while the rule is enabled."""
    return POLICY.enabled and isinstance(switch, dict) and switch.get('pool_policy') == NAME


def replay(data, address, words, switch):
    """owner_graph_profile.graph's byte replay of a descriptor this rule produced."""
    import match
    if not marked(switch):
        raise ValueError('interposed switch pool requires its enabled policy')
    layout = match.switch_layout(data, address, words, interposed_pool=True)
    if pool_words(address, layout) != switch.get('interposed_words'):
        raise ValueError('interposed switch pool word count differs from native replay')
    return layout
