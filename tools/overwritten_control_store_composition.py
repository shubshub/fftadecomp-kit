"""Bounded classifier composition; deliberately no native admission routing."""
import hashlib
from pathlib import Path

import volatile_semantics as semantics
import overwritten_control_store_prerequisite as prerequisite

SELECTOR = "conditional-classified-overwritten-control-stores-v1"
PREMISE = prerequisite.PREMISE


def compare_function(name, real, stripped, permuted, signatures, symbol, size, pinned,
                     mapping, *, selector, premise, interfaces=None, manifest=None):
    prerequisite.require(selector == SELECTOR and premise == PREMISE,
                         "classified overwritten stores require explicit policy and premise")
    # Neither store elimination nor real/stripped agreement can excuse fixed-slot
    # accesses. Preserve this independent check on the original complete paths.
    semantics.perturbation_check(name, real, permuted, signatures, symbol, size,
                                pinned, mapping, interfaces)
    witnesses = []

    def ordered(real_path, stripped_path, classified):
        # Only the existing classifier's dead full-member insertion loads can be
        # crossed. Do not infer deadness from a final trace or discard a live read.
        prefix, real_tail, stripped_tail = unchanged_fill_prefix(real_path, stripped_path, interfaces)
        filtered = semantics.Path(real_tail.decisions, real_tail.conditions, real_tail.trace,
            [row for row in real_tail.records
             if not (row.kind == "load" and row.index in classified)])
        mine, removed = prerequisite.normalise(filtered, symbol, size, pinned,
                                               _typed_correspondence=True)
        theirs, other_removed = prerequisite.normalise(stripped_tail, symbol, size, pinned,
                                                       _typed_correspondence=True)
        correspondence = compare_survivors(filtered, stripped_tail, removed, other_removed)
        witnesses.append(dict(unchanged_fill_prefix=prefix, real_removed=removed, stripped_removed=other_removed,
            correspondence=correspondence,
            real_path_sha256=prerequisite.path_fingerprint(real_path),
            stripped_path_sha256=prerequisite.path_fingerprint(stripped_path),
            classified_dead_reads=sorted(classified)))
        # The original comparator's condition check remains strict. Typed versions
        # in conditions remain outside this bounded composition.
        return correspondence["real"], correspondence["stripped"]

    result = semantics.compare_function(name, real, stripped, signatures, symbol, size,
        pinned, interfaces, unloaded_all_ones=True, _ordered_trace_check=ordered)
    observed = dict(schema=SELECTOR, premise=premise, result=result, paths=witnesses,
                adapter_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                producer_sha256={Path(module.__file__).name:
                    hashlib.sha256(Path(module.__file__).read_bytes()).hexdigest()
                    for module in (semantics, prerequisite)},
                native_admission=False, independent_permutation_complete=True,
                volatile_classification_complete=True)

    prerequisite.require(manifest is None or manifest == observed,
                         "classified overwritten-store manifest is stale")
    return observed


def compare_survivors(real, stripped, removed, other_removed, *, manifest=None):
    """Typed ordered bijection, scoped to these exact two path instances.

    Only supported Executor term forms are translated; unknown forms refuse.
    Conditions stay strict and cannot contain event references in this subset.
    """
    require = prerequisite.require
    require(real.conditions == stripped.conditions and real.decisions == stripped.decisions,
            "event correspondence control decisions differ")
    require(not any(prerequisite.has_versions(c) for c in real.conditions),
            "event correspondence excludes versioned conditions")

    def canonical(path, killed):
        deleted = {row['event'] for row in killed}
        require(all(type(i) is int and 0 <= i < len(path.trace) and
                    path.trace[i][0] == 'store' for i in deleted),
                "event correspondence malformed removal")
        mapping = {old: new for new, old in enumerate(i for i in range(len(path.trace))
                                                     if i not in deleted)}

        def reference(index, kind, before):
            require(type(index) is int and 0 <= index < before and index in mapping,
                    "event reference removed, foreign or forward")
            require(path.trace[index][0] == kind, "event reference has wrong kind")
            return mapping[index]

        def term(value, before):
            if type(value) is int or type(value) is str:
                return value
            require(isinstance(value, tuple) and bool(value), "unknown event expression form")
            tag = value[0]
            if tag == 'load':
                require(len(value) == 4 and value[1] in (1,2,4), "malformed load expression")
                version = value[3]
                if version == 'entry':
                    mapped = version
                else:
                    require(isinstance(version, tuple) and len(version) == 2 and
                            version[0] in ('call','store'), "malformed memory version")
                    mapped = (version[0], reference(version[1], version[0], before))
                    require(not any(event[0] in ('call','store')
                        for event in path.trace[version[1]+1:before]),
                        'memory version is superseded or requires disjointness proof')
                    if version[0] == 'store':
                        event = path.trace[version[1]]
                        a, ta = semantics.linear(value[2]); b, tb = semantics.linear(event[2])
                        require(ta == tb and a < b + event[1] and b < a + value[1],
                                "store version lacks overlap provenance")
                return ('load',value[1],term(value[2],before),mapped)
            if tag in ('ret','clobber'):
                require(len(value) in ((2,) if tag == 'ret' else (2,3)), "malformed call result")
                identity = value[1]
                if isinstance(identity, tuple):
                    require(len(identity) >= 2 and identity[0] == 'raw-call', "malformed raw call")
                    identity = ('raw-call',reference(identity[1],'call',before),
                                *(term(arg,before) for arg in identity[2:]))
                    # Raw-call conditional interface provenance is not recorded
                    # by a bare trace. Do not infer it from the tuple spelling.
                    require(False, "raw-call requires conditional interface provenance")
                else:
                    identity = reference(identity,'call',before)
                return (tag,identity,*value[2:])
            if tag == 'lin':
                require(len(value) == 3 and type(value[1]) is int and isinstance(value[2],tuple),
                        "malformed linear expression")
                require(all(type(pair) is tuple and len(pair) == 2 and type(pair[1]) is int
                            for pair in value[2]), 'malformed linear coefficients')
                return ('lin',value[1],tuple((term(atom,before), coefficient)
                    for atom,coefficient in value[2]))
            arities = {'sym':2,'arg':2,'entry':2,'frame':2,'code':2,'sp':1,
                       'trunc':3,'sext':3,'byte':3,'and':3,'orr':3,'eor':3,
                       'lsl':3,'lsr':3,'asr':3,'mul':3}
            require(tag in arities and len(value) == arities[tag], "unknown event expression form")
            return (tag,*(term(part,before) if isinstance(part,tuple) else part for part in value[1:]))

        events=[]
        for index,event in enumerate(path.trace):
            if index in deleted: continue
            tag=event[0]
            if tag == 'store' and len(event) == 4:
                events.append((tag,event[1],term(event[2],index),term(event[3],index)))
            elif tag == 'call' and len(event) == 3 and isinstance(event[1],str):
                events.append((tag,event[1],tuple(term(arg,index) for arg in event[2])))
            elif tag == 'return' and len(event) in (1,2):
                events.append((tag,*(term(arg,index) for arg in event[1:])))
            else:
                require(False, "unsupported surviving event or escape")
        return events, sorted(mapping.items())

    mine, left = canonical(real,removed)
    theirs, right = canonical(stripped,other_removed)
    require(mine == theirs, "typed surviving ordered events differ")
    observed=dict(real=mine,stripped=theirs,real_bijection=left,stripped_bijection=right,
        adapter_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        producer_sha256=hashlib.sha256(Path(semantics.__file__).read_bytes()).hexdigest(),
        real_path_sha256=prerequisite.path_fingerprint(real),
        stripped_path_sha256=prerequisite.path_fingerprint(stripped))
    require(manifest is None or manifest == observed, "event correspondence manifest is stale")
    return observed


def unchanged_fill_prefix(real, stripped, interfaces):
    """Exact two-fill prefix only, authenticated by executor call records.

    Invoked only on paths freshly explored/replayed by compare_function. No
    caller-supplied prefix length, snapshots or local-fill tuple is authority.
    """
    import bios_cpuset_fill_profile as bios
    require = prerequisite.require
    if not any(event[0] == 'escape' for event in real.trace + stripped.trace):
        return [], real, stripped
    require(type(interfaces) is bios.ConditionalVolatileInterfaces and
            bool(interfaces.local_fill_premise), 'unchanged prefix needs actual conditional fill provider')

    def split(path):
        calls = [(i,row) for i,row in enumerate(path.records) if row.kind == 'call']
        require(len(calls) == 2, 'unchanged prefix requires exactly two conditional calls')
        for _,row in calls:
            require(row.derived == bios.NAME and row.local_fill_premise == interfaces.local_fill_premise and
                    row.conditional_interface == interfaces.conditional_premises[bios.NAME],
                    'unchanged prefix missing conditional call provenance')
        expected = ['escape','call','store','escape','call']
        require(len(path.trace) >= 5 and [e[0] for e in path.trace[:5]] == expected,
                'unchanged prefix requires exact two-fill event shape')
        require(not any(e[0] in ('escape','call') for e in path.trace[5:]),
                'unchanged prefix excludes later escape or call')
        before = path.records[:calls[1][0]+1]
        # No global/control event may be hidden by prefix reconciliation.
        require(all(row.kind != 'store' or semantics.is_stack(row.address) for row in before),
                'unchanged prefix cannot contain candidate or global stores')
        stack = [row for row in before if row.kind == 'store' and semantics.is_stack(row.address)]
        # Saved pushes have entry-valued contents; local fill source stores
        # must all be known initialized constants in this bounded subset.
        locals_ = [row for row in stack if type(row.value) is int]
        require(len(locals_) == 2 and all(row.width == 2 and row.value == 0 for row in locals_),
                'unchanged prefix requires two initialized halfword source stores')
        base = semantics.signed32(semantics.linear(locals_[0].address)[0])
        require(semantics.signed32(semantics.linear(locals_[1].address)[0])-base == 2,
                'unchanged prefix local stores must be contiguous')
        require(path.trace[2] == ('store',2,('frame',2),0),
                'unchanged prefix exposed stack store identity differs')
        require(path.trace[0] == ('escape',((0,0),(1,0))) and
                path.trace[3] == ('escape',((0,0),(1,0),(2,0),(3,0))),
                'unchanged prefix complete frame snapshots differ')
        for number,event in enumerate((path.trace[1],path.trace[4])):
            require(event[1] == bios.NAME and len(event[2]) == 3 and
                    event[2][0] == ('local-fill-source',('frame',number*2),2,('bytes',0,0)),
                    'unchanged prefix source extent or frame coordinate differs')
        tail_records = path.records[calls[1][0]+1:]
        require(not any(row.kind == 'store' and semantics.is_stack(row.address)
                        for row in tail_records), 'unchanged prefix excludes later frame mutation')
        tail = semantics.Path(path.decisions,path.conditions,path.trace[5:],tail_records)
        # Event references retain full-trace indexes. This slice intentionally
        # refuses them rather than rebasing through the preserved prefix.
        require(not any(prerequisite.has_versions(event) for event in tail.trace),
                'unchanged prefix excludes later raw or versioned dependencies')
        return path.trace[:5],tail

    a,left = split(real); b,right = split(stripped)
    require(a == b, 'unchanged conditional fill prefixes differ')
    return a,left,right


def record(symbol, results):
    """Fresh canonical composition evidence carried by normal volatile replay."""
    import json
    fingerprint = hashlib.sha256(json.dumps(results,sort_keys=True,separators=(',',':')).encode()).hexdigest()
    return (f"* allowlisted volatile semantics: `{symbol}` conditional ordinary overwritten control stores; "
            f"{PREMISE}; independent member permutation and original volatile classifiers preserved; "
            f"composition SHA-256 {fingerprint}")
