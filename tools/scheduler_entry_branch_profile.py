"""Two mutually exclusive calls through the pinned pool-manager wrapper.

This separate selector preserves the original single-entry contract. It admits
no other calls, cycles or path containing two wrapper invocations. Descriptor
bounds, aliases and conditional scheduler effects reuse the existing entry
profile; callback effects, nonescape and termination remain unproved.
"""
import hashlib
from pathlib import Path

import scheduler_entry_profile as entry
from scheduler_predicate_profile import acyclic

SELECTOR = 'conditional-scheduler-entry-branch-descriptor-calls-v1'
SCHEMA = 'elf-symbol-thumb-' + SELECTOR
MAX_CALL_SITES = 2


def phases(edges, calls):
    entry.require(len(calls) == MAX_CALL_SITES and set(calls.values()) == {entry.POOL}
                  and set(calls) <= set(edges),
                  'scheduler entry branches require exactly two pinned wrapper call sites')
    after = dict.fromkeys(edges, False)
    for site in acyclic(edges):
        entry.require(not (after[site] and site in calls),
                      'scheduler entry branches exclude calls after a scheduler return')
        scheduled = after[site] or site in calls
        for target in edges[site]:
            after[target] |= scheduled
    return dict(scheduler_sites=sorted(calls), call_site_budget=MAX_CALL_SITES,
                maximum_scheduler_calls_per_path=1, calls_after_scheduler=False)


def bind(data, address, ins, edges, calls):
    branches = phases(edges, calls)
    # The same closed entry binding supplies both complete dependency identities.
    site = min(calls)
    bound = entry.bind(data, address, ins, edges, {site: calls[site]})
    return bound, branches


def manifest(proof):
    result = entry.manifest(proof)
    result.update(schema=SCHEMA, branch_calls=proof.scheduler_entry_branches,
                  entry_source_sha256=result['source_sha256'],
                  source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    return result
