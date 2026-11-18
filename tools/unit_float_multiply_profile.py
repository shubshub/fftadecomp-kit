"""Fresh source replay of the old-agbcc fp-bit __mulsf3 library member."""
import re
import sys

import unit_fpbit_source as source
import library_units as units
import private_float_inline_division_inventory as parts
import software_float_profile as runtime

SCHEMA = "elf-symbol-thumb-fp-bit-mulsf3-unit-v1"
COUNT = 171
LABEL = "fp-bit multiply"
CONTROL = "* control flow: reached Thumb returns restore the frame and callee-saved registers; conditional reads of the NaN record"
ADDRESS, END = 0x08143CEC, 0x08143E54
UNIT_START, UNIT_END = 0x081439C8, 0x081443AE
TOOLCHAIN = "old-agbcc-O2-v1"
UNIT_DIGEST = "29f04fc63c3da5f6796be91008ee1c5537db51b98999a6886b3a7b47dd09c92c"
UNPACK, MULTIPLY, PACK = 0x08143A84, 0x08142A20, 0x081439C8
OBJECT = "data_03005E68"
TARGETS = {"func_08143A84": UNPACK, "__muldi3": MULTIPLY, "func_081439C8": PACK, OBJECT: 0x03005E68}
SITES = {0x12: "func_08143A84", 0x1c: "func_08143A84", 0x80: OBJECT,
         0xc8: "__muldi3", 0x152: "func_081439C8"}
CALLS = {ADDRESS + offset: TARGETS[name] for offset, name in SITES.items() if name != OBJECT}


def unit_owner(unit, address, orphan=None):
    return (unit is not None and address == ADDRESS and orphan is None and unit.toolchain == TOOLCHAIN and
            unit.name == "libgcc fp-bit, _cmpdi2, _lshrdi3" and
            (unit.start, unit.end, unit.proof) == (UNIT_START, UNIT_END, 0x0814435C) and
            unit.row["identity"] == [{"address": f"0x{UNIT_START:08X}", "size": UNIT_END - UNIT_START,
                                      "sha256": UNIT_DIGEST}])


def original_bindings(image):
    source.fixed_bindings(image, ADDRESS, END, TARGETS, SITES, OBJECT)


def native_proof(data, rom, mapping, index, objects):
    import match
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    from software_double_profile import indices, span_record
    if units.sha(rom) != runtime.ROM_SHA256 or match.parse_data_symbols(objects).get(OBJECT) != TARGETS[OBJECT]:
        raise ValueError("fp-bit multiply requires the approved ROM and named NaN record")
    entries, rows = indices(mapping, index)
    identities = {record[0]: record for record in runtime.IDENTITIES}
    dependencies = {}
    if data != rom[ADDRESS-match.ROM_BASE:END-match.ROM_BASE]:
        raise ValueError("fp-bit multiply differs from the complete pinned ROM caller")
    for start in (UNPACK, MULTIPLY, PACK, ADDRESS):
        _, end, count, digest = identities[start]
        record = span_record(start, end, entries, rows, rom)
        body = rom[start-match.ROM_BASE:end-match.ROM_BASE]
        if record["instrs"] != count or units.sha(body) != digest:
            raise ValueError("fp-bit multiply helper or caller identity differs")
        if start != ADDRESS:
            bounds = next((bounds for _, identity, bounds in parts.HELPERS if identity[0] == start), parts.policy())
            dependencies[start] = runtime.prove_runtime(rom, entries, start, end, count, {}, call_edges=(),
                scalar_entries=(), argument_effect_policy=bounds)
    count = identities[ADDRESS][2]
    refinement = owner.refine(data, ADDRESS, mapping)
    ins, edges, branches, calls, words = graph.graph(data, ADDRESS, refinement)
    if calls != CALLS or branches or words or len(ins) != count:
        raise ValueError("fp-bit multiply has a different CFG or helper bindings")
    partition = graph.partition(data, ADDRESS, refinement, ins, words)
    if not any(word['address'] == ADDRESS + 0x80 and word['value'] == TARGETS[OBJECT] and
               word['load_sites'] and not word['switch_word'] for word in partition['words']):
        raise ValueError("fp-bit multiply requires its reached named data literal")
    caller = runtime.prove_runtime(rom, entries, ADDRESS, END, count, dependencies,
        call_edges=tuple(sorted(calls.items())), scalar_entries=(ADDRESS,), argument_effect_policy=parts.policy(),
        compose_pointer_returns=True, absolute_read_policy=parts.ABSOLUTE_POLICY)
    if caller['native_edges'] != [[site, list(succ)] for site, succ in sorted(edges.items())] or \
            caller['absolute_reads']['reads'] != parts.ABSOLUTE_POLICY['reads'] or \
            caller['argument_effects']['reads'] or caller['writes'] or caller['stack_reads']:
        raise ValueError("fp-bit multiply has unaccounted reachable effects")
    return {"instructions": count, "partition": partition, "returns": caller["returns"],
            "helper_calls": sorted(calls.items()), "conditional_reads": caller["absolute_reads"]["reads"],
            "caller_cfg_and_effects_sha256": units.sha(units.canonical(caller).encode()),
            "helper_proofs_sha256": units.sha(units.canonical(dependencies).encode())}


def link_object(runner, workspace, args, original, capture, relative, rom, mapping, index):
    import match
    from addressed_signed_runtime_profile import linked_bytes
    from plausible import strip_comments_and_strings
    preprocessed = runner.read_binary(workspace + "/f.i").decode()
    if re.search(r"\b__muldi3\b", strip_comments_and_strings(preprocessed)):
        raise ValueError("fp-bit multiply requires compiler-generated wide multiplication")
    original_bindings(original)
    linked = match.link_typed_targets(runner, workspace, args, f"func_{ADDRESS:08X}", ADDRESS, TARGETS, {OBJECT})
    return linked_bytes(original, linked, ADDRESS, CALLS, TARGETS, data_relocations={0x80: (OBJECT, 0)})


def build(root, address, args=None):
    return source.build(sys.modules[__name__], root, address, args)


def report_matches(report, root, address):
    return address == ADDRESS and report == build(root, address)[1]


def issue(root, address, args):
    return source.issue(sys.modules[__name__], root, address, args)
