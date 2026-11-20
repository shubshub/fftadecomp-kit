"""Exact switch pool words that lie outside the GBA bus.

The u16 scalar policy binds every reached literal word that is not the table
pointer, a typed object or a bound function as an exact number, and admits
only values up to 0xFFFF so that no unbound object, I/O or code address can
pass as a number. A binary32 constant such as 0.5f (0x3F000000) is refused
by that bound although it names nothing.

This policy admits such a word when its value is at least 0x10000000.
GBATEK's memory map lists 10000000-FFFFFFFF as not used (the upper four
address bits are not decoded), and its "reading from unused memory" entry
says an access there returns the recently prefetched opcode, not a mirror of
a lower region. So the word is not itself an object, I/O or code address. One residual is
a premise, not a proof: agbcc folds `sym + 0x80000000` (or `&arr[-0x10000000]`) into one
literal word, and a source that hard-codes that linked value would be admitted here while
its symbolic form is refused (the binding value wraps). Such an offset is assumed absent.
Nothing beyond the exact value is claimed. Each word is recorded as
`[offset, value]` under `wide_scalars`, kept apart from the u16 `scalars`, and
replay compares it with the linked bytes. Words below 0x10000000 that exceed
0xFFFF stay refused, as before.
"""

POLICY = 'unmapped-bus-scalar-words-v1'
LOW = 0x10000000
PREMISE = ('each `wide_scalars` word is an exact number of at least 0x10000000; GBATEK lists '
           '10000000-FFFFFFFF as unused memory whose reads return the prefetched opcode, so the '
           'word is no mapped address; an object address offset by 0x10000000 or more, which '
           'agbcc would fold into one such word, is assumed absent from the source')
REPORT_PREFIX = '* switch wide scalar premise: '
FIELDS = frozenset(('wide_scalar_policy', 'wide_scalars'))


def admits(value):
    """True for a 32-bit word value this policy binds."""
    return type(value) is int and LOW <= value <= 0xFFFFFFFF


def report_line():
    return f'{REPORT_PREFIX}{PREMISE}'


def check_context(policy):
    if type(policy) is not str or policy != POLICY:
        raise ValueError('wide switch scalar words require their canonical policy marker')
