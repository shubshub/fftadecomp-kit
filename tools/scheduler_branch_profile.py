"""Acyclic caller composition with one scheduler invocation per path.

Other calls use the existing ordinary indexed-call ABI summary. Their complete
body identities are authenticated, but their effects and nested execution are
not proved. No tracked local pointer may be present at those call sites.
"""
import hashlib
from pathlib import Path

import match
from scheduler_predicate_profile import acyclic

SCHEDULER = 0x08005B6C
MAX_SCHEDULER_SITES = 2
MAX_CALL_SITES = 8
MAX_ORDINARY_TARGETS = 4
WIDE_ORDINARY_TARGETS = 8
WIDE_CALL_SITES = 12


def require(condition, message):
    if not condition:
        raise ValueError(message)


def phases(edges, calls, *, following_calls=False, wide_targets=False, twenty_four_targets=False):
    require(type(following_calls) is bool, 'following-call selection must be Boolean')
    require(type(wide_targets) is bool and not (following_calls and wide_targets),
            'wide-target selection must be Boolean and separate from following calls')
    require(type(twenty_four_targets) is bool and
            not (twenty_four_targets and (following_calls or wide_targets)),
            'twenty-four-target selection must be Boolean and exclusive')
    target_budget = WIDE_ORDINARY_TARGETS if wide_targets else MAX_ORDINARY_TARGETS
    call_budget = WIDE_CALL_SITES if wide_targets else MAX_CALL_SITES
    if twenty_four_targets:
        target_budget, call_budget = 24, 32
    schedulers = sorted(site for site, target in calls.items() if target == SCHEDULER)
    ordinary = sorted(set(calls.values()) - {SCHEDULER})
    require(1 <= len(schedulers) <= MAX_SCHEDULER_SITES and
            1 <= len(ordinary) <= target_budget and
            len(calls) <= call_budget and set(calls) <= set(edges),
            'scheduler branches exceed the explicit call-site or target bounds')
    after = dict.fromkeys(edges, False)
    following_sites = []
    for site in acyclic(edges):
        # Union at joins retains every scheduler-return path. The separate
        # following-call selector permits only ordinary calls afterwards; each
        # such call still undergoes the complete frame/alias check.
        if after[site] and site in calls:
            require(following_calls and calls[site] != SCHEDULER,
                    'scheduler branches exclude every call after a scheduler return')
            following_sites.append(site)
        scheduled = after[site] or calls.get(site) == SCHEDULER
        for target in edges[site]:
            after[target] |= scheduled
    if following_calls:
        require(len(schedulers) == 1 and following_sites,
                'following-call contract requires one scheduler site and a reached following ordinary call')
    result = dict(scheduler_sites=schedulers, ordinary_targets=ordinary,
        scheduler_site_budget=MAX_SCHEDULER_SITES, call_site_budget=call_budget,
        ordinary_target_budget=target_budget,
        maximum_scheduler_calls_per_path=1, ordinary_calls_after_scheduler=bool(following_sites))
    if following_calls:
        result['following_ordinary_sites'] = sorted(following_sites)
    return result


def bind(proof, edges, calls, *, following_calls=False, wide_targets=False, twenty_four_targets=False):
    result = phases(edges, calls, following_calls=following_calls, wide_targets=wide_targets, twenty_four_targets=twenty_four_targets)
    for target in result['ordinary_targets']:
        require(not match.function_thunk.reserved(target) and
                target not in match.RUNTIME_HELPERS.values(),
                'scheduler branches require ordinary indexed Thumb call targets')
        body = proof.span(target)
        proof.dependencies[target] = body
        proof.records[target] = dict(address=target, end=target+len(body), bytes=len(body),
            body_sha256=hashlib.sha256(body).hexdigest(), **proof.identities,
            structure=dict(kind='complete-indexed-body-conditional-ordinary-call',
                callee_effects_proved=False, nested_execution_proved=False))
    result.update(source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        ordinary_call_contract=(
            'Each ordinary indexed call uses the existing returning ARM ABI summary: '
            'compatible registers, exact SP and protected caller/saved words preserved. '
            'No tracked local-register alias, pointer word or word-provenance fact may '
            'enter it. Complete body identity does not prove purity, memory effects, '
            'nested execution, readability, allocation separation or termination.'),
        ordinary_callee_effects_proved=False, nested_execution_proved=False)
    return result
