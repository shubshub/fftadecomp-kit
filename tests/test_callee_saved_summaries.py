"""Kit #350: a summary never admits what the walk in context refuses, and never states less.

`callee_saved_watch` skips a callee with a summary where it may, and walks it in its caller's
context otherwise.  The summary is an optimisation: it must never admit a call the walk in
context refuses, and every premise the walk in context states must be stated with summaries
too.  The fixture lists the callee checks the decomp's shipped reports make (a call made
while R4-R11 hold an owner stack address), and the function index rows those walks reach.
Each check runs on the retail ROM twice, as issuance runs it and with every callee walked in
context, and the two are compared:

* where summaries admit, the walk in context admits too;
* every premise line the walk in context states is stated with summaries, at the same site,
  for at least the same registers and frame words (at a site stated at several depths, as
  below). INDEX lines compare the excluded words at or above the
  access's SP. Words below it are dead stack, which the premise excludes as such, and which
  a summary forgets where the walk in context remembers what a callee left there;
* the copies handed back with summaries include those handed back in context.

A walk in context that hits its budget (its update or memory bound) is run again with a
raised one (minutes, about 1 GB); the fixture lists those checks, and every one is compared
all the same.  Where the walk in context cannot end because a callee recurses deeper than it
walks, the comparison is by induction: that walk skips with summaries only the recursive
calls, and is compared as above.  No check is exempt.

A site that summaries state at several depths ("+": recursion, or call paths of different
depth) declares the words it names, as offsets from the SP of the site's shallowest execution,
and every word of the stack between each execution's SP and the entry of the callee whose
summary states it.  The comparison there is that claim itself: every word the walk in context
names at the site, at whatever depth, is an address the walk with summaries names there, or
lies between that execution's SP and the entry of such a callee, where the walk in context
entered it at the same SP.  Both walks record each premise with its SP and chain only for this
test (``Checker.trace``).
"""
import hashlib
import json
import os
from pathlib import Path
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import callee_saved_watch as watch

FIXTURE = Path(__file__).with_name('fixtures') / 'callee_saved_summary_checks.json'
ROM_SHA256 = '43fc8204c6dceee58828aebc7af0c72eb807e99f35ad641c8bb0a4fa8b6edc19'
BUDGET = ('the callee-saved check exceeded its budget', 'calls nested too deeply to check')
RAISED = (10 ** 7, 4 * 10 ** 7)      # updates, held frame words: the raised budget


def covered(record, records):
    """Whether ``record`` (a walk in context's merged premise) is stated among ``records``.  The
    frame words of a site stated at several depths are compared by ``region_missing``."""
    kind = record[0].rstrip('+')
    same = [other for other in records if other[0].rstrip('+') == kind and other[1:3] == record[1:3]]
    if kind == 'call':
        same = [other for other in same if other[3:5] == record[3:5]]
        return set(record[5]) <= set().union(*(other[5] for other in same)) and \
            set(record[6]) <= set().union(*(other[6] for other in same)) and \
            (not record[7] or any(other[7] for other in same))
    if kind == 'swi':
        same = [other for other in same if other[3] == record[3]]
        return set(record[4]) <= set().union(*(other[4] for other in same)) and \
            set(record[5]) <= set().union(*(other[5] for other in same)) and \
            (not record[6] or any(other[6] for other in same))
    if kind == 'index':
        same = [other for other in same if other[3] == record[3]]
        return bool(same) and {off for off in record[4] if off >= 0} <= set().union(*(other[4] for other in same))
    if kind in ('escape', 'bits'):
        same = [other for other in same if other[3] == record[3]]
        return bool(same) and set(record[4]) <= set().union(*(other[4] for other in same)) and \
            set(record[5]) <= set().union(*(other[5] for other in same))
    if kind in ('stale', 'rebuilt', 'bytes', 'unset'):
        return bool(same) and set(record[3]) <= set().union(*(other[3] for other in same))
    return record in records


def word_field(record):
    """(key fields, frame words) of a record: what must match exactly, and the words compared."""
    kind = record[0].rstrip('+')
    if kind in ('stale', 'rebuilt', 'bytes', 'unset'):
        return (), set(record[3])
    if kind == 'index':
        return (record[3],), {off for off in record[4] if off >= 0}
    if kind == 'call':
        return tuple(record[3:5]), set(record[6])
    if kind == 'swi':
        return (record[3],), set(record[5])
    if kind in ('escape', 'bits'):        # the words an address may reach, and those that depend
        return (record[3],), {('reached', off) for off in record[4]} | {('dependent', off) for off in record[5]}
    return None, None


def without_words(record):
    """The record with its frame words left out: the site, registers and flags still compared."""
    kind = record[0].rstrip('+')
    if kind in ('stale', 'rebuilt', 'bytes', 'unset'):
        return record[:3] + ((),)
    if kind == 'index':
        return record[:4] + ((),)
    if kind == 'call':
        return record[:6] + ((),) + record[7:]
    if kind == 'swi':
        return record[:5] + ((),) + record[6:]
    if kind in ('escape', 'bits'):
        return record[:4] + ((), ())
    return record


def region_missing(record, in_context, summarised):
    """The words the walk in context names at ``record``'s site that the summary's lines there do
    not declare.  ``in_context`` and ``summarised`` hold each walk's (record, SP at its site,
    chain of (function, entry SP)).  A line stated at several depths declares the words it names,
    as offsets from the SP of the site's shallowest execution, so the same addresses the walk with
    summaries names there; and every word of the stack between an execution's SP and the entry of
    the callee whose summary states it, which a walk in context that enters that callee at the
    same SP reaches through it."""
    kind = record[0].rstrip('+')
    key, _ = word_field(record)

    def same(raw):
        return raw[0].rstrip('+') == kind and raw[1:3] == record[1:3] and word_field(raw)[0] == key
    def place(at, word):                  # an address, tagged where the record has two lists
        return (word[0], at + word[1]) if isinstance(word, tuple) else at + word
    named = set().union(*({place(at, word) for word in word_field(raw)[1]} for raw, at, _ in summarised if same(raw)))
    entries = {chain[-1] for raw, _, chain in summarised if same(raw) and raw[0].endswith('+')}
    missing = []
    for raw, at, chain in in_context:
        if not same(raw):
            continue
        bound = max((entry for callee, entry in entries if (callee, entry) in chain), default=None)
        for word in word_field(raw)[1]:
            address = at + (word[1] if isinstance(word, tuple) else word)
            if place(at, word) not in named and not (bound is not None and at <= address < bound):
                missing.append((raw[:3], at, word))
    return sorted(set(missing))


class TracedPremises(set):
    """A walk's premises, each recorded with the SP and chain where the walk adds it."""

    def __init__(self, checker):
        super().__init__()
        self.checker = checker

    def add(self, record):
        if self.checker._now is not None:
            self.checker.trace.append((record,) + self.checker._now)
        super().add(record)


class RegionRuleTests(unittest.TestCase):
    """The comparison at a site stated at several depths, on recorded walks: SITE is stated with
    summaries applied when CALLEE is entered at SP -40, naming the word at -96 from the site's
    shallowest SP -100."""
    SITE = ('stale+', 0x08001000, 0x08001010, (4,))
    CHAIN = ((0x08000000, 0), (0x08002000, -40))
    SUMMARISED = [(SITE, -100, CHAIN)]

    def missing(self, words, at=-100, chain=CHAIN):
        record = ('stale',) + self.SITE[1:3] + (tuple(words),)
        return [word for _, _, word in region_missing(record, [(record, at, chain)], self.SUMMARISED)]

    def test_a_named_address_or_a_word_inside_the_callee_is_declared(self):
        self.assertEqual(self.missing([4]), [])            # -96, named
        self.assertEqual(self.missing([20, 56]), [])       # -80 and -44: between the SP and -40
        self.assertEqual(self.missing([4], at=-160), [])   # -156 at a deeper execution: inside

    def test_a_word_neither_named_nor_inside_the_callee_is_missing(self):
        self.assertEqual(self.missing([60, 80]), [60, 80])   # -40 and -20: the caller's frame
        self.assertEqual(self.missing([-4]), [-4])           # -104: below the SP
        # Entered at another SP, or not through the callee, nothing is inside: only the address
        # named counts, not the same offset from another SP.
        self.assertEqual(self.missing([20], chain=((0x08000000, 0), (0x08002000, -44))), [20])
        self.assertEqual(self.missing([4], at=-160, chain=self.CHAIN[:1]), [4])

    def test_with_a_nested_recursion_the_bound_is_the_summarised_callees_entry(self):
        # In context the walk enters CALLEE at -40 and a recursion inside it at -60 and -80: a
        # word of CALLEE's own frame (-50) or of the inner recursion's outer level (-70) is
        # inside, a word of CALLEE's caller (-20) is not.
        chain = self.CHAIN + ((0x08003000, -60), (0x08003000, -80))
        self.assertEqual(self.missing([50, 30], at=-100, chain=chain), [])
        self.assertEqual(self.missing([80], at=-100, chain=chain), [80])

    def test_escape_and_bits_lines_follow_the_same_rule(self):
        # An escape line names the words a stored address may reach and the words that depend on
        # an owner stack address; each list is compared by address, separately, as above.
        for kind in ('escape', 'bits'):
            summarised = [((kind + '+',) + self.SITE[1:3] + ('G', (4,), (8,)), -100, self.CHAIN)]
            with self.subTest(kind=kind):
                def missing(reached, dependent, at=-100, chain=self.CHAIN):
                    record = (kind,) + self.SITE[1:3] + ('G', tuple(reached), tuple(dependent))
                    return [word for _, _, word in region_missing(record, [(record, at, chain)], summarised)]
                self.assertEqual(missing([4], [8]), [])
                self.assertEqual(missing([4], [8], at=-160), [])               # inside the callee
                self.assertEqual(missing([60], []), [('reached', 60)])         # the caller's frame
                self.assertEqual(missing([4, 8], [], chain=self.CHAIN[:1]), [('reached', 8)])


@unittest.skipUnless(FIXTURE.is_file(), 'the recorded checks are missing')
class SummaryAgreementTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        selected = os.environ.get('FFTA_ROM')
        if not selected or not Path(selected).is_file():
            raise unittest.SkipTest('FFTA_ROM must reference the approved ROM')
        cls.rom = Path(selected).read_bytes()
        if hashlib.sha256(cls.rom).hexdigest() != ROM_SHA256:
            raise unittest.SkipTest('FFTA_ROM is not the approved ROM')
        cls.fixture = json.loads(FIXTURE.read_text())

    def walk(self, target, watched, summaries, raised=False, recursion=False):
        saved = watch.MAX_UPDATES, watch.MAX_HELD_WORDS
        if raised:
            watch.MAX_UPDATES, watch.MAX_HELD_WORDS = RAISED
        try:
            checker = watch.Checker(self.rom, self.fixture['functions'])
            if not summaries and not recursion:
                checker.isolation = lambda callee: None       # every callee walked in context
            if recursion:
                checker.summarised = lambda callee, chain: callee in chain   # only recursive calls
            checker.trace = []
            checker.premises = TracedPremises(checker)
            try:
                copies = checker.call(target, frozenset(watched))
            except watch.WatchRefusal as error:
                return 'refused', str(error), None, None
            return 'ok', watch.merged_premises(checker.premises), copies, checker.trace
        finally:
            watch.MAX_UPDATES, watch.MAX_HELD_WORDS = saved

    def compare(self, summarised, in_context):
        self.assertEqual(in_context[0], 'ok', f'summaries admit what the walk in context refuses: {in_context[1]}')
        several = {other[1:3] for other in summarised[1] if other[0].endswith('+')}
        missing = []
        for record in in_context[1]:
            if record[1:3] in several and word_field(record)[0] is not None:
                missing += [('word', item) for item in region_missing(record, in_context[3], summarised[3])]
                record = without_words(record)
            if not covered(record, summarised[1]):
                missing.append(record)
        self.assertEqual(missing, [], 'premises the walk in context states and summaries do not')
        self.assertLessEqual(set(in_context[2].items()), set(summarised[2].items()))

    def agree(self, part):
        """Every check of PART (``parts``) compared as above, and the checks of PART whose walk in
        context hits its budget are exactly the fixture's budget checks in PART."""
        budget = []
        checks = parts(self.fixture['checks'])[part]
        for name, watched in checks:
            key = check_key(name, watched)
            target = int(name, 16)
            summarised = self.walk(target, watched, True)
            in_context = self.walk(target, watched, False)
            if in_context[0] == 'refused' and in_context[1].split(': ', 1)[-1].startswith(BUDGET):
                budget.append(key)
                if summarised[0] != 'ok':
                    continue
                in_context = self.walk(target, watched, False, raised=True)
                if in_context[0] == 'refused' and 'nested too deeply' in in_context[1]:
                    in_context = self.walk(target, watched, False, raised=True, recursion=True)
            if summarised[0] != 'ok':
                continue
            with self.subTest(check=key):
                self.compare(summarised, in_context)
        mine = {check_key(name, watched) for name, watched in checks}
        self.assertEqual(sorted(budget), sorted(key for key in (check_key(name, watched)
                                                                for name, watched in self.fixture['budget'])
                                                if key in mine))


PARTS = 6


def check_key(name, watched):
    return f'{name}:{",".join(map(str, watched))}'


def parts(checks):
    """The fixture's checks in PARTS parts, every PARTS-th one from each start."""
    return [checks[start::PARTS] for start in range(PARTS)]


def part_test(part):
    """The test that compares part PART (``parts``), so a suite can run the parts side by side."""
    def test(self):
        self.agree(part)
    test.__name__ = f'test_summaries_admit_and_state_no_less_than_the_walk_in_context_part_{part + 1}'
    test.__doc__ = f'The comparison of part {part + 1} of {PARTS} of the recorded checks.'
    return test


for _part in range(PARTS):
    setattr(SummaryAgreementTests, part_test(_part).__name__, part_test(_part))
del _part


@unittest.skipUnless(FIXTURE.is_file(), 'the recorded checks are missing')
class PartitionTests(unittest.TestCase):
    """The parts above cover the fixture's checks: each check in exactly one part, a test per
    part, and every budget check among them, so the parts compare and bound exactly what one
    comparison of every check would."""

    def test_the_parts_partition_the_checks(self):
        fixture = json.loads(FIXTURE.read_text())
        keys = [check_key(name, watched) for name, watched in fixture['checks']]
        self.assertEqual(len(keys), len(set(keys)))
        split = [[check_key(name, watched) for name, watched in part] for part in parts(fixture['checks'])]
        self.assertEqual(len(split), PARTS)
        self.assertTrue(all(split))
        self.assertEqual(sorted(key for part in split for key in part), sorted(keys))
        budget = {check_key(name, watched) for name, watched in fixture['budget']}
        self.assertLessEqual(budget, set(keys))
        self.assertEqual(budget, {key for part in split for key in part if key in budget})
        tests = [f'test_summaries_admit_and_state_no_less_than_the_walk_in_context_part_{k}' for k in range(1, PARTS + 1)]
        self.assertEqual(sorted(name for name in dir(SummaryAgreementTests)
                                if name.startswith('test_summaries_admit_and_state_no_less_than_the_walk_in_context')),
                         sorted(tests))
        # Each test compares its own part: part k is index k - 1.
        for index, name in enumerate(tests):
            case = SummaryAgreementTests(name)
            compared = []
            case.agree = compared.append
            getattr(case, name)()
            self.assertEqual(compared, [index], name)


if __name__ == '__main__':
    unittest.main()
