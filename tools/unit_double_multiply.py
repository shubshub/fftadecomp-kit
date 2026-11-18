"""Original old-agbcc dp-bit __muldf3, its four limb products and binary64 callers."""
import sys

import library_units as units
import private_double_pack_effects_inventory as parts
import private_double_selected_record_inventory as selected
import software_double_profile as double
import software_float_profile as runtime
import unit_fpbit_source as source

ADDRESS, END, COUNT = 0x081430F0, 0x0814339C, 323
SCHEMA = 'elf-symbol-thumb-dp-bit-muldf3-unit-v1'
TOOLCHAIN = 'old-agbcc-O2-v1'
LABEL = 'dp-bit multiply'
CONTROL = ('* control flow: both encoded inputs unpack into distinct local component records; four native '
           'wide multiplies form the finite product. Packing zero times infinity reads the fixed RAM record '
           'under a conditional readability premise. Its contents are runtime inputs.')
DATA = 'data_03005E50'
UNPACK, WIDE, SHIFT, PACK = 0x08142D34, 0x08142A20, 0x08144378, 0x08142BE8
TARGETS = {'func_08142D34': UNPACK, '__muldi3': WIDE, DATA: selected.FIXED_RECORD, 'func_08142BE8': PACK}
SITES = {0x18: 'func_08142D34', 0x22: 'func_08142D34', 0x84: DATA, 0xf0: '__muldi3',
         0x100: '__muldi3', 0x110: '__muldi3', 0x120: '__muldi3', 0x286: 'func_08142BE8'}
CALLS = {ADDRESS+offset: TARGETS[name] for offset, name in SITES.items() if name != DATA}
CALLERS = {0x0814278C: (0x081427B8,), 0x081428E4: (0x081428FA, 0x08142906)}
SOURCE_DIGEST = '6b71f8e58d6e0379cdf6800754d39275e5735265ddc7da34921c525a726ce3f3'
HEADER = ('include/dp_bit.h', 'fef9d4d221e7a2c9f9134f1e698ca5c81359e04103fd450e7c19fd3017281652')


def unit_owner(unit, address, orphan=None):
    return address == ADDRESS and orphan is None and source.dp_unit(unit)


def check_source(capture, relative):
    names = ('FFTA_DP_BIT_H', 'encoded_double', 'fp_number_type', 'fractype', 'halffractype', 'fp_class_type',
             'func_08142D34', 'func_08142BE8', 'func_081430F0', '__muldi3', DATA)
    source.reviewed_source(capture, relative, ADDRESS, names, SOURCE_DIGEST, headers=(HEADER,))


def link_object(runner, workspace, args, original, capture, relative, rom, mapping, index):
    import match
    from addressed_signed_runtime_profile import linked_bytes
    check_source(capture, relative)
    source.fixed_bindings(original, ADDRESS, END, TARGETS, SITES, DATA)
    linked = match.link_typed_targets(runner, workspace, args, 'func_081430F0', ADDRESS, TARGETS, {DATA})
    if any(item['size'] for item in linked['symbols'] if item['name'] in TARGETS):
        raise ValueError('dp-bit multiply requires storage-free absolute linker definitions')
    return linked_bytes(original, linked, ADDRESS, CALLS, TARGETS, data_relocations={0x84: (DATA, 0)})


def native_proof(data, rom, mapping, index, objects):
    import match
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    if (units.sha(rom) != runtime.ROM_SHA256 or data != rom[ADDRESS-match.ROM_BASE:END-match.ROM_BASE] or
            match.parse_data_symbols(objects).get(DATA) != selected.FIXED_RECORD):
        raise ValueError('dp-bit multiply requires its original USA ROM bytes and named fixed RAM record')
    entries, rows = double.indices(mapping, index)
    identities = {identity[0]: identity for identity in double.IDENTITIES}
    dependencies, callers = {}, []
    for start in (UNPACK, WIDE, SHIFT, PACK, ADDRESS, *CALLERS):
        _, end, count, digest = identities[start]
        record = double.span_record(start, end, entries, rows, rom)
        body = rom[start-match.ROM_BASE:end-match.ROM_BASE]
        if record['instrs'] != count or units.sha(body) != digest:
            raise ValueError('dp-bit multiply helper, owner or external caller identity changed')
        if start in CALLERS:
            ins, _, _, calls, _ = graph.graph(body, start, owner.refine(body, start, mapping))
            sites = tuple(sorted(site for site, target in calls.items() if target == ADDRESS))
            if sites != CALLERS[start] or len(ins) != count:
                raise ValueError('dp-bit multiply requires its original wide conversion callers')
            callers.append(dict(address=start, end=end, instructions=count, sites=sites, sha256=digest))
        elif start != ADDRESS:
            bounds = next((bounds for _, helper, bounds in parts.HELPERS if helper[0] == start), parts.policy())
            edges = tuple((site, target) for site, target in double.EDGES if start <= site < end)
            dependencies[start] = runtime.prove_runtime(rom, entries, start, end, count, dependencies,
                call_edges=edges, scalar_entries=(), argument_effect_policy=bounds,
                stack_load_widths=(1, 2, 4) if start in (UNPACK, PACK) else (4,),
                stack_store_widths=(1, 2, 4) if start == PACK else (4,))
    proof = source.multiply_effects(data, rom, mapping, entries, dependencies, ADDRESS, END, COUNT, CALLS,
                                    ADDRESS+0x84, selected.FIXED_RECORD, selected.ABSOLUTE_POLICY)
    return dict(proof, callers=callers)


def build(root, address, args=None):
    return source.build(sys.modules[__name__], root, address, args)


def report_matches(report, root, address):
    return address == ADDRESS and report == build(root, address)[1]


def issue(root, address, args):
    return source.issue(sys.modules[__name__], root, address, args)
