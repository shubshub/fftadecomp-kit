"""Reviewed store bounds in a replayed callee loop, retried after the default walk refuses.

The default stack-argument walk (`match.BufferCallProof` with stack arguments, as match.py's plain
path and `match_evidence.buffer_report_matches` build it) replays a callee loop path by path when
its joined pass cannot keep a buffer pointer exact (bounded-loop-replay-v2). A loop that stores
through an advancing pointer once per qualifying iteration then explores every outcome of each
qualifying test, and refuses the first store that leaves the owner's allocated local words:

    buffer callee 0x0812E4F4: bounded loop replay at 0x0812E540: 2-byte strh at caller sp+4:
    buffer access is unaligned or outside allocated local words

0812E4F4 stores one halfword per equipment slot holding a qualifying item, into the caller's
u16[2]; a third store would reach a saved register.  Whether a third qualifying item can exist is
a fact about the game, not about the code.

That refusal (`TRIGGER`, the whole message: callee chain, site, store, caller offset) is the only
trigger; every walk that does not refuse with it is the walk it was before.  After it, and only
then, the same walk (with the default stack-index retry, `default_stack_index_profile.walk`) is
run again with a `StoreBounds` attached (`proof.store_bounds`), in two passes:

1. **Measure.** Rows are the trigger's (callee, site) and every row of the owner's reviewed entry.
   In the bounded loop replay of a row's callee, each path counts the executions of each row site
   (the count is part of the replay state, so the replay's dedupe and state budget see it; it starts
   at zero in each walk of the callee, so it is per call).  A store at a row site whose access would
   leave the allocated local words ends its path, and the number of earlier executions of that site
   on the path is recorded.  Nothing is admitted by this pass.  The largest bound the frame allows
   for a site is the least such count; a site where no store refuses needs no row.  A new trigger at
   another site joins the rows and the pass is repeated (`MAX_ROWS` sites at most); any other refusal
   raises the plain walk's refusal unchanged.
2. **Prune.** Only when the owner's entry in `config/store_bound_premises.json` (`PREMISES_PATH`)
   lists exactly the sites the measure pass needs, each with a bound no larger than the frame allows:
   each path counts again, and a path on which a row site would execute for the (bound+1)-th time
   ends there, before the store, and its replay state is counted as pruned.  Every execution up to the bound is the
   ordinary replayed store with all its checks.  Each row must prune at least one path.

A row states a count, never reachability ("this store, or this call, never runs").  So a row with a
bound below 1 is malformed, and a frame that allows no execution at a site's first execution raises
the trigger unchanged.  And each replayed walk of a row callee keeps its state graph (`CallBounds`):
the walk is refused when no path of the call returns and some end at a bound, or when, from a state
in which a row store runs for the first time on its path, no continuation returns and some end at that
store's bound.  The replay follows both ways of every branch its known values leave open, so the code itself
then runs a row store past its bound whenever that store runs, and the row would assert that the state
never occurs.  In the measure pass, where paths end at the refusing stores, either finding raises the
trigger unchanged: no entry the frame allows could pass (a prune pass ends each path no later), so none
is printed.  In the prune pass it refuses the reviewed entry.  A bound reached only after a later
execution stays a count (the code allows fewer executions) and is admitted.

A missing or differing entry refuses and prints the entry to review, with the largest bounds the
frame allows; the reviewer proves each bound from the ROM (or a smaller one) and shows it before it
ships (user ruling of 2026-11-27 on stack-store premises: "admit if proved, shown to me").

The one unproved fact is each row's "the site executes at most `bound` times per call of the
callee".  It is a STORE premise.  The report states every row, the call site that reached it and the
number of pruned paths, says that paths past a bound are not verified, and binds the owner's entry
by the SHA-256 of its canonical JSON (only that entry, so other reports do not change when the file
grows).  Nothing else is premised: no alias is dropped, stores up to the bound are checked, and a
store at any other site keeps its checks and its refusal.

Scope: rows apply only inside the bounded loop replay of an inspected callee (never to the owner's
own instructions), only to the default stack-argument walk of match.py's plain path and of the
composed data-buffer proof, and to their replays (`match_evidence.buffer_report_matches`,
`data_buffer_profile.verify_source`, and the legacy buffer replay of
`function_thunk_profile.verify_source`), and only behind `POLICY` (disabled: the trigger is raised
unchanged).
"""
import hashlib
import json
from pathlib import Path
import re

NAME = 'reviewed-callee-store-bound-v1'
PREMISES_PATH = 'config/store_bound_premises.json'
MAX_ROWS = 8
STORES = {'str': 4, 'strh': 2, 'strb': 1}
NOT_A_STORE = 'is not a store (a store-bound row names a STR, STRH or STRB)'
TRIGGER = re.compile(r'^(?:buffer callee 0x[0-9A-F]{8}: )*buffer callee 0x(?P<callee>[0-9A-F]{8}): '
                     r'bounded loop replay at 0x(?P<site>[0-9A-F]{8}): [124]-byte (?:str|strh|strb) '
                     r'at caller sp\+-?\d+: buffer access is unaligned or outside allocated local words$')
SUMMARY = ('reviewed store bounds in a replayed callee loop, retried after the default walk refused a '
           'replayed store outside the allocated local words: each row site executes at most its bound '
           'times per call of its callee (a STORE premise, proved by the reviewed entry, not by this '
           'walk); a path past a bound ends before the store and is not verified; every store up to a '
           'bound, and every store at any other site, keeps its checks')


class Policy:
    """The one policy object of this rule: ``enabled = False`` raises the trigger unchanged."""
    enabled = True


POLICY = Policy()


class StoreBoundRefusal(ValueError):
    """A refused retry that names the entry to review; ``entry`` is the suggested entry."""

    def __init__(self, message, entry):
        super().__init__(message)
        self.entry = entry


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def triggered(error):
    """(callee, site) of a trigger refusal, else None."""
    found = TRIGGER.match(str(error)) if isinstance(error, ValueError) else None
    return None if found is None else (int(found['callee'], 16), int(found['site'], 16))


def snapshot(root):
    """The decomp's reviewed store-bound file, or None."""
    try:
        return (Path(root) / PREMISES_PATH).read_bytes()
    except FileNotFoundError:
        return None


def hexword(value, what):
    if type(value) is not str or not re.fullmatch(r'0x[0-9A-F]{8}', value):
        raise ValueError(f'store bound: {PREMISES_PATH} {what} is not an 0xXXXXXXXX address')
    return int(value, 16)


class DuplicateKey(ValueError):
    pass


def unique(pairs):
    """``json.loads`` object hook: a repeated key at any level refuses (JSON keeps the last silently, so a
    reader of the file could see another entry, review or bound than the walk uses)."""
    result = {}
    for key, value in pairs:
        if key in result:
            raise DuplicateKey(f'store bound: {PREMISES_PATH} repeats the key {json.dumps(key)}')
        result[key] = value
    return result


def parse_entry(premises, owner):
    """The owner's reviewed entry as (entry, {(callee, site): bound}), or (None, {})."""
    if premises is None:
        return None, {}
    try:
        table = json.loads(premises, object_pairs_hook=unique)
    except DuplicateKey:
        raise
    except ValueError as error:
        raise ValueError(f'store bound: {PREMISES_PATH} is not JSON') from error
    if type(table) is not dict:
        raise ValueError(f'store bound: {PREMISES_PATH} is not an object of owner entries')
    for key in table:
        hexword(key, 'owner key')
    entry = table.get(f'0x{owner:08X}')
    if entry is None:
        return None, {}
    if type(entry) is not dict or set(entry) != {'review', 'rows'} or type(entry['review']) is not str or \
            not entry['review'].strip() or type(entry['rows']) is not list or not entry['rows']:
        raise ValueError(f'store bound: the entry 0x{owner:08X} needs a non-empty review and rows')
    rows = {}
    for row in entry['rows']:
        if type(row) is not dict or set(row) != {'callee', 'site', 'bound'} or type(row['bound']) is not int or \
                row['bound'] < 1:
            raise ValueError(f'store bound: a row of 0x{owner:08X} is not {{callee, site, bound >= 1}}')
        key = (hexword(row['callee'], 'row callee'), hexword(row['site'], 'row site'))
        if key in rows:
            raise ValueError(f'store bound: the entry 0x{owner:08X} repeats a row')
        rows[key] = row['bound']
    if entry['rows'] != rows_json(rows):
        raise ValueError(f'store bound: the rows of 0x{owner:08X} are not in (callee, site) order')
    return entry, rows


def rows_json(rows):
    return [dict(callee=f'0x{callee:08X}', site=f'0x{site:08X}', bound=bound)
            for (callee, site), bound in sorted(rows.items())]


class StoreBounds:
    """One pass's rows and records, attached to a BufferCallProof as ``store_bounds``.

    ``bounds`` maps (callee, site) to a bound (prune pass) or None (measure pass).
    """

    def __init__(self, owner, bounds):
        self.owner = owner
        self.bounds = dict(bounds)
        self.measure = all(bound is None for bound in self.bounds.values())
        if not self.measure and any(type(bound) is not int or bound < 1 for bound in self.bounds.values()):
            raise ValueError('store bound: a pass either measures every row or bounds every row')
        # (callee, site): least earlier execution count at a refusing store (measure pass)
        self.refusing = {}
        # (callee, site, call site): paths pruned at the bound (prune pass)
        self.pruned = {}

    def sites(self, callee):
        """{site: bound} of the rows of ``callee``; empty when none."""
        return {site: bound for (row_callee, site), bound in self.bounds.items() if row_callee == callee}

    def call(self, callee, call_site):
        """The bookkeeping of one replayed walk of the row callee ``callee`` called at ``call_site``."""
        return CallBounds(self, callee, call_site)

    def snapshot(self):
        return dict(self.refusing), dict(self.pruned)

    def restore(self, saved):
        self.refusing.clear()
        self.refusing.update(saved[0])
        self.pruned.clear()
        self.pruned.update(saved[1])

    def step(self, proof, callee, call_site, instruction, aliases, stack, counts, bound):
        """One replayed execution of a row site: False ends the path here; True runs the store.

        ``counts`` is the path's {site: executions so far}; on True it is advanced.
        """
        site = instruction.address
        width = STORES.get(instruction.mnemonic)
        operands = instruction.operands
        from capstone.arm_const import ARM_OP_MEM
        if width is None or len(operands) != 2 or operands[1].type != ARM_OP_MEM:
            raise ValueError(f'store bound: the row site 0x{site:08X} in 0x{callee:08X} {NOT_A_STORE}')
        done = counts.get(site, 0)
        if self.measure:
            memory = operands[1].mem
            offset = aliases.get(memory.base)
            if type(offset) is int and not memory.index:
                try:
                    proof.access(offset + memory.disp, width, stack)
                except ValueError:
                    key = (callee, site)
                    self.refusing[key] = min(self.refusing.get(key, done), done)
                    return False
        elif done >= bound:
            key = (callee, site, call_site)
            self.pruned[key] = self.pruned.get(key, 0) + 1
            return False
        counts[site] = done + 1
        return True


class CallBounds:
    """One replayed walk of a row callee.  It keeps the walk's state graph, whose nodes are the replay's
    (address, state) pairs, so that ``finish`` can refuse a walk that verifies the premise instead of
    the call (a path "ends at a bound" where the prune pass cuts it, or where the measure pass ends it at
    a refusing row store):

    * no path of the call returns, and some end at a bound; or
    * the code itself runs a row store past its bound: from a state in which a row store runs for the
      first time on its path, no replayed continuation returns and some end at that store's bound.  The
      row would then assert that the state never occurs, which is a reachability premise (as a bound of 0
      would be), not a count.  (Continuations cut only at another row's bound are that row's count.)

    The replay explores both ways of every branch its known values leave open, so "no continuation
    returns" holds for every input: the overrun is forced by the code, not by the unknown values.
    """

    def __init__(self, bounds, callee, call_site):
        self.bounds, self.callee, self.call_site = bounds, callee, call_site
        self.successors = {}
        self.returns = set()
        self.prunes = set()
        self.first = {}     # node: row site, where that store runs for the first time on the path

    def step(self, proof, instruction, aliases, stack, counts, bound, node):
        """``StoreBounds.step`` at ``node``."""
        first = instruction.address not in counts
        if not self.bounds.step(proof, self.callee, self.call_site, instruction, aliases, stack, counts, bound):
            self.prunes.add(node)
            return False
        if first:
            self.first[node] = instruction.address
        return True

    def edge(self, node, successor):
        self.successors.setdefault(node, []).append(successor)

    def returned(self, node):
        self.returns.add(node)

    def finish(self):
        if not self.prunes:
            return
        where = f'0x{self.callee:08X} (called at 0x{self.call_site:08X})'
        if not self.returns:
            raise ValueError(f'store bound: no replayed path of {where} returns and {len(self.prunes)} end at a '
                             f'bound: the walk would verify the premise, not the call')
        predecessors = {}
        for node, targets in self.successors.items():
            for target in targets:
                predecessors.setdefault(target, []).append(node)

        def reaching(ends):
            seen, work = set(ends), list(ends)
            while work:
                for node in predecessors.get(work.pop(), ()):
                    if node not in seen:
                        seen.add(node)
                        work.append(node)
            return seen
        completes = reaching(self.returns)
        forced = []
        for site in sorted({node[0] for node in self.prunes}):
            # A path cut at another row's bound is that row's count, not this store's.
            overruns = reaching({node for node in self.prunes if node[0] == site})
            if any(node in overruns and node not in completes
                   for node, first in self.first.items() if first == site):
                forced.append(site)
        if forced:
            stores = ', '.join(f'0x{site:08X}' for site in forced)
            raise ValueError(f'store bound: in {where}, once the store at {stores} first runs no replayed '
                             f'continuation returns and some end at its bound: the code itself runs the store '
                             f'more often than its row allows')


def run_pass(make_proof, run, data, address, index_premises, bounds):
    import default_stack_index_profile as default_index

    def bounded():
        proof = make_proof()
        if proof.store_bounds is not None or not proof.stack_arguments:
            raise ValueError('store bound retry requires a fresh stack-argument buffer proof')
        proof.store_bounds = StoreBounds(address, bounds)
        return proof
    return default_index.walk(bounded, run, data, address, index_premises)


def retry(error, make_proof, run, data, address, index_premises, premises):
    """After a trigger refusal ``error``: measure, compare with the reviewed entry, then prune.

    Anything but a trigger (or the policy disabled) raises ``error`` unchanged.  Returns
    (instructions, proof) of the pruned pass."""
    trigger = triggered(error)
    if trigger is None or not POLICY.enabled:
        raise error
    entry, reviewed = parse_entry(premises, address)
    needed = dict.fromkeys(sorted({trigger, *reviewed}))
    while True:
        try:
            _, measured = run_pass(make_proof, run, data, address, index_premises, needed)
        except ValueError as reason:
            if NOT_A_STORE in str(reason):
                raise ValueError(f'{error}; default store-bound retry: {reason}') from reason
            found = triggered(reason)
            if found is None or found in needed or len(needed) >= MAX_ROWS:
                raise error from reason
            needed[found] = None
            continue
        break
    frame = dict(sorted(measured.store_bounds.refusing.items()))
    if trigger not in frame:
        raise error
    if any(bound < 1 for bound in frame.values()):
        # A store that leaves the frame at its first execution: only "it never runs" would admit it.
        raise error
    suggested = {key: min(reviewed.get(key, bound), bound) for key, bound in frame.items()}
    differs = None
    if entry is None:
        differs = 'none found'
    elif set(reviewed) != set(frame):
        differs = 'the entry lists other sites than the walk needs'
    elif any(reviewed[key] > frame[key] for key in frame):
        differs = 'a bound lets a store leave the allocated local words'
    if differs is not None:
        proposal = {'review': entry['review'] if entry else
                    'PROVE each bound from the ROM, then show the row and its evidence before it ships',
                    'rows': rows_json(suggested)}
        text = json.dumps({f'0x{address:08X}': proposal}, indent=2)
        raise StoreBoundRefusal(
            f'{error}; default store-bound retry: store bound: the replayed stores of 0x{address:08X} need a '
            f'reviewed entry in {PREMISES_PATH} that repeats these rows ({differs}); the largest bounds the '
            f'frame allows are shown, and each must be proved from the ROM (a smaller proved bound is also '
            f'accepted); add:\n{text}', {f'0x{address:08X}': proposal})
    try:
        instructions, proof = run_pass(make_proof, run, data, address, index_premises, reviewed)
        bounds = proof.store_bounds
        unused = sorted(key for key in reviewed
                        if not any(key == (callee, site) for callee, site, _ in bounds.pruned))
        if unused:
            raise ValueError(f'store bound: the row 0x{unused[0][1]:08X} in 0x{unused[0][0]:08X} prunes no path')
    except ValueError as reason:
        raise ValueError(f'{error}; default store-bound retry: {reason}') from reason
    proof.store_bound_retry = {
        'policy': NAME, 'address': address, 'trigger': str(error),
        'entry_sha256': hashlib.sha256(canonical(entry).encode()).hexdigest(),
        'rows': rows_json(reviewed),
        'pruned': sorted([callee, site, call_site, count]
                         for (callee, site, call_site), count in bounds.pruned.items())}
    return instructions, proof


def walk(make_proof, run, data, address, index_premises, premises):
    """``closure_slot_profile.walk`` (the plain walk and the default stack-index or closure-slot retry),
    and on a store-bound trigger this rule's retry, whose passes take only the stack-index retry."""
    import closure_slot_profile as closure
    try:
        return closure.walk(make_proof, run, data, address, index_premises)
    except ValueError as error:
        return retry(error, make_proof, run, data, address, index_premises, premises)


def fingerprint_payload(record):
    return None if record is None else canonical(record)


def lines(record):
    """The report lines of an admitted retry (buffer proof lines, recomputed by every replay)."""
    if record is None:
        return []
    out = [f"* buffer store bound: `{record['policy']}` after `{record['trigger']}`: {SUMMARY}"]
    for callee, site, call_site, count in record['pruned']:
        bound = next(row['bound'] for row in record['rows']
                     if row['callee'] == f'0x{callee:08X}' and row['site'] == f'0x{site:08X}')
        out.append(f'* buffer store bound row: callee 0x{callee:08X} store 0x{site:08X} executes at most {bound} '
                   f'times per call (reached at 0x{call_site:08X}); {count} replayed states past the bound end '
                   f'before the store and are not verified')
    out.append(f"* buffer store bound premise: STORE premise: each bound above is the reviewed entry "
               f"0x{record['address']:08X} of {PREMISES_PATH} (canonical JSON SHA-256 `{record['entry_sha256']}`), "
               f"proved from the ROM by that review, not by this walk")
    return out
