"""Explicit conditional overwritten-store prerequisite; no native/report admission.

This bounded rule admits no memory read between the candidate and overwrite.
It deliberately refuses event-version expressions instead of guessing how to
renumber opaque memory/call identities after removal. Legacy semantics remain
unchanged and are not replaced by this prerequisite.
"""
import hashlib
import json
from pathlib import Path

import volatile_semantics as semantics

SELECTOR = 'conditional-overwritten-control-store-prerequisite-v1'
SCHEMA = 'conditional-overwritten-control-store-prerequisite-v1'
PREMISE = ('Authenticated ordinary control members are stable live ordinary memory; '
    'no concurrent, asynchronous, hardware or external observer can observe intermediate '
    'stores. Exact constant stores may be removed only before a complete exact-member '
    'overwrite without any intervening memory read, unknown effect, call, branch, '
    'return or address observation. No volatile hardware/MMIO equivalence is claimed.')


def require(condition, message):
    if not condition:
        raise semantics.SemanticError(message)


def has_versions(value):
    if not isinstance(value, tuple):
        return False
    if value and value[0] in ('load','ret','clobber','raw-call'):
        return True
    return any(has_versions(part) for part in value)


def normalise(path, symbol, size, pinned, *, _typed_correspondence=False):
    """Retain order, delete only exact constant stores with local witnesses.

    Record/trace association is authenticated by exact ordered store tuples.
    An untracked stack escape or memory/call version expression is unsupported.
    No final-memory comparison, permutation or event sorting is performed.
    """
    require(not any(event[0] == 'escape' for event in path.trace),
            'overwritten-store prerequisite excludes frame escapes')
    records=path.records
    stores=[(position,row) for position,row in enumerate(records)
            if row.kind == 'store' and not semantics.is_stack(row.address)]
    events=[(index,event) for index,event in enumerate(path.trace) if event[0] == 'store']
    require(len(stores) == len(events), 'overwritten-store record/trace ownership differs')
    association={}
    for (position,row),(index,event) in zip(stores,events):
        require(event == ('store',row.width,row.address,row.value),
                'overwritten-store record/trace identity differs')
        association[position]=index
    removed=[]
    for position,row in stores:
        offset=semantics.object_offset(row.address,symbol,size)
        if offset not in pinned or row.width != pinned[offset] or type(row.value) is not int:
            continue
        require(not row.self_assignment, 'overwritten-store cannot discharge load/store self-assignment')
        for other_position in range(position+1,len(records)):
            other=records[other_position]
            if other.kind in ('alu','literal'):
                continue
            if other.kind != 'store':
                break
            other_offset=semantics.object_offset(other.address,symbol,size)
            # Every intervening store must itself be an exact pinned ordinary
            # member. Unknown destinations can observe/alias and are barriers.
            if other_offset not in pinned or other.width != pinned[other_offset]:
                break
            if other.address == row.address:
                if other.width == row.width and type(other.value) is int and not other.self_assignment:
                    removed.append(dict(event=association[position],instruction=row.index,
                        offset=offset,width=row.width,value=row.value,
                        overwritten_by_instruction=other.index))
                break
    deleted={row['event'] for row in removed}
    if deleted and not _typed_correspondence:
        # Fail closed for every opaque event identity, including conditions and
        # values not visible in the final trace. A later extension must perform
        # independently tested provenance-preserving reindexing, not integer replacement.
        require(not any(has_versions(event) for event in path.trace) and
                not any(has_versions(condition) for condition in path.conditions) and
                not any(has_versions(getattr(row,'value',None)) or has_versions(row.address)
                        for row in records),
                'overwritten-store prerequisite cannot reindex memory/call version expressions')
    return [event for index,event in enumerate(path.trace) if index not in deleted],removed


def path_fingerprint(path):
    def serialise(value):
        if isinstance(value,(set,frozenset)):
            return sorted((serialise(part) for part in value),key=repr)
        if isinstance(value,(list,tuple)):
            return [serialise(part) for part in value]
        if isinstance(value,dict):
            return {key:serialise(part) for key,part in value.items()}
        return value
    snapshot=dict(decisions=path.decisions,conditions=path.conditions,trace=path.trace,
        records=[row.__dict__ for row in path.records])
    return hashlib.sha256(json.dumps(serialise(snapshot),sort_keys=True,separators=(',',':')).encode()).hexdigest()


def compare_paths(real, stripped, symbol, size, pinned, *, selector, premise, manifest=None):
    """Conditional trace prerequisite on executor Paths, not compiler admission.

    Callers must separately authenticate the declaration/source/ELF, every
    existing volatile load/RMW/self-assignment rule and real/permuted compiles.
    This API supplies no replacement for any of those gates.
    """
    require(selector == SELECTOR and premise == PREMISE,
            'overwritten-store prerequisite requires explicit selector and observation premise')
    require(type(symbol) is str and type(size) is int and size > 0 and type(pinned) is dict and
            pinned and all(type(offset) is int and type(width) is int and width in (1,2) and
                0 <= offset <= size-width for offset,width in pinned.items()) and
            all(a == b or not (a < b+pinned[b] and b < a+pinned[a]) for a in pinned for b in pinned),
            'overwritten-store prerequisite requires exact nonoverlapping byte/halfword members')
    require(real.conditions == stripped.conditions and real.decisions == stripped.decisions,
            'overwritten-store control decisions differ')
    mine,removed=normalise(real,symbol,size,pinned)
    theirs,other_removed=normalise(stripped,symbol,size,pinned)
    require(mine == theirs, 'overwritten-store surviving ordered events differ')
    observed=dict(schema=SCHEMA,premise=PREMISE,symbol=symbol,size=size,members=sorted(pinned.items()),
        real_path_sha256=path_fingerprint(real),stripped_path_sha256=path_fingerprint(stripped),
        real_removed=removed,stripped_removed=other_removed,
        surviving_events=len(mine),native_admission=False,source_ELF_admission=False,
        volatile_classification_complete=False,independent_permutation_complete=False,
        producer_sha256={Path(module.__file__).name:hashlib.sha256(Path(module.__file__).read_bytes()).hexdigest()
            for module in (semantics,)},adapter_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    require(manifest is None or manifest == observed, 'overwritten-store prerequisite manifest is stale')
    return observed
