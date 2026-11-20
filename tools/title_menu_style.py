"""Prove the title menu stack indices under its two explicitly reviewed cursor premises."""

import json
from hashlib import sha256
from pathlib import Path
import match
import owner_admission_profile as owner
import owner_graph_profile as graph
import stack_index_precondition_profile as indexed
from runtime_summary_profile import RuntimeSummaries
from umodsi3_profile import prove_divisors
from ability_range_local_bytes import require

ADDRESS = 0x08136A10
END = 0x08136DEC
DIGEST = "87a70ea2ff9b20120fcb4d56480d9df2f362bd0760dc15c17d4a708fc6c261c1"
READS = {
    0x08136AB2: (0x08136AAC, 0x8962),
    0x08136C96: (0x08136C92, 0x8963),
}
STORES = {0x08136ABC: (-44, 0x08136AB2), 0x08136C9C: (-40, 0x08136C96)}
RUNTIMES = {0x08136D6C: 0x08142B28, 0x08136D7C: 0x08142AB0}
OBJECTS = {
    0x8136B04: 0x83A8C6C,
    0x8136C54: 0x83A8C78,
    0x8136DC8: 0x83A8CD4,
    0x8136DCC: 0x83A8CE2,
    0x8136DD0: 0x83A8CF0,
    0x8136DE8: 0x83A8CFE,
}


def expression(site):
    parent, field = READS[site]
    return (
        "ld",
        1,
        False,
        ("bin", "add", ("ld", 4, False, ("c", 0x0200F3B0), parent), ("c", field)),
        site,
    )


class ThreeSelections(indexed.Analysis):
    """Restrict precisely the two external byte values named in the reviewed premises."""

    def access(
        self, state, site, base, disp, index, width, load, register, *, signed=False
    ):
        super().access(
            state, site, base, disp, index, width, load, register, signed=signed
        )
        if site in READS:
            expr = self.expr(state, register)
            require(
                load and not signed and width == 1 and expr == expression(site),
                "title selection byte-load provenance differs",
            )
            self.write(state, register, indexed.norm("S", 0, 2, 0), expr)


def check_arrays(data, instructions, policy):
    require(
        not (policy.spills or policy.returned or policy.accesses)
        and policy.derivations == {0x08136AB6, 0x08136C98},
        "private style address derivation or stack escape differs",
    )
    analysis = ThreeSelections(
        data,
        ADDRESS,
        policy.derivations,
        policy.accesses,
        {},
        signed_shift_congruence=True,
    )
    sites = analysis.syntactic_sites()
    require(
        sites
        == set(instructions)
        | {pc + 2 for pc, op in instructions.items() if op.mnemonic == "bl"},
        "native and independent style CFGs differ",
    )
    states = analysis.run()
    require(
        set(analysis.records) == set(STORES)
        and not analysis.premises
        and analysis.checked_derivations == policy.derivations,
        "uncovered private style store",
    )
    for site, (start, _) in STORES.items():
        require(
            analysis.records[site] == ["store", 1, start, start + 2, 0]
            and all(b in states[site].init for b in range(start, start + 3))
            and analysis.frame_check(states[site], start, start + 2, 1, load=True)
            is None,
            "all three style bytes must be initialized and inside the local frame",
        )
    return analysis.records


def prove(data, rom, mapping, index, objects, reviewed):
    owner.validate_span(data, ADDRESS, rom, mapping, index)
    selected = [row for row in json.loads(mapping) if int(row["rom"], 16) == ADDRESS]
    text_rows = [
        line.split()
        for line in index.decode().splitlines()
        if line.startswith(f"{ADDRESS:08X} ")
    ]
    require(
        len(selected) == len(text_rows) == 1
        and selected[0]["instrs"] == 390
        and text_rows[0][3] == "390",
        "title dual-index instruction count differs",
    )
    require(
        len(data) == END - ADDRESS and sha256(data).hexdigest() == DIGEST,
        "exact title owner differs",
    )
    refinement = owner.refine(data, ADDRESS, mapping)
    ins, edges, branches, calls, words = graph.graph(data, ADDRESS, refinement)
    require(
        len(ins) == 390 and len(calls) == 21 and not (branches or words),
        "title control flow differs",
    )
    part = graph.partition(data, ADDRESS, refinement, ins, words)
    values = {row["address"]: row["value"] for row in part["words"]}
    names = match.parse_data_symbols(objects)
    for site, addr in OBJECTS.items():
        require(
            values.get(site) == addr and names.get(f"data_{addr:08X}") == addr,
            "missing title ROM object or literal binding",
        )
    runtime = {pc: dest for pc, dest in calls.items() if RuntimeSummaries.covers(dest)}
    require(
        runtime == RUNTIMES
        and prove_divisors(ins, edges, ADDRESS, runtime)
        == {0x08136D6C: 30, 0x08136D7C: 5},
        "title compiler runtime site or divisor differs",
    )
    p = indexed.StackIndexV2BufferProof(
        rom, mapping, index, objects, data=data, address=ADDRESS
    )
    p.runtime_summaries = RuntimeSummaries(rom, mapping, index)
    checked = match.verify_leaf_instructions(
        data,
        ADDRESS,
        True,
        calls,
        buffer_proof=p,
        runtime_summaries=p.runtime_summaries,
    )
    require(
        set(ins) == {op.address for op in checked}
        and p.runtime_summaries.sites == RUNTIMES,
        "title owner or canonical runtime coverage differs",
    )
    require(
        not p.records and not p.dependencies and not p.index_copies(),
        "title owner unexpectedly lends a private buffer or copies a table",
    )
    rows = p.index_policy.evidence["preconditions"]
    require(
        len(rows) == len(STORES) and {row["site"] for row in rows} == set(STORES),
        "expected exactly two external selection premises",
    )
    verified = check_arrays(data, ins, p.index_policy)
    output = []
    for row in rows:
        site = row["site"]
        start, read = STORES[site]
        require(
            row["width"] == 1
            and row["kind"] == "store"
            and row["scale"] == 1
            and row["expression"] == "(u32)" + indexed.render(expression(read))
            and row["array_entry_sp"][0] == start,
            "title style source differs",
        )
        output.append(
            dict(
                row,
                bound=3,
                array_entry_sp=[start, start + 3],
                array_sp=[start + 72, start + 75],
            )
        )
    checked_rows = indexed.accept({"preconditions": output}, ADDRESS, reviewed)
    return dict(
        instructions=len(ins),
        runtime_sites=p.runtime_summaries.manifest()["sites"],
        runtime=p.runtime_summaries.manifest(),
        private_style_stores=[[s, *r] for s, r in sorted(verified.items())],
        conditional_indices=checked_rows,
    )


def owner_proof(
    data,
    rom,
    mapping,
    index,
    objects,
    bindings,
    ins,
    calls,
    refinement,
    words,
    premises,
):
    import runtime_summary_profile as runtime
    import named_data_buffer_profile as named

    summary = prove(
        data, rom, mapping, index, objects, indexed.parse_premises(premises)
    )
    constants = graph.partition(data, ADDRESS, refinement, ins, words)
    targets = {
        0x0200F3B0: "data_0200F3B0",
        0x03000000: "data_03000000",
        0x02000000: "g_state_02000000",
    }
    targets.update(
        {
            a: f"data_{a:08X}"
            for a in (*OBJECTS.values(), 0x083A8C9E, 0x083A8CAC, 0x083A8CC0)
        }
    )
    labels = [
        [r["address"] - ADDRESS, targets[r["value"]], 0]
        for r in constants["words"]
        if r["value"] in targets
    ]
    plain = [
        [pc - ADDRESS, f"func_{dest:08X}"]
        for pc, dest in sorted(calls.items())
        if pc not in RUNTIMES
    ]
    helpers = [
        [pc - ADDRESS, runtime.FAMILY[dest]] for pc, dest in sorted(RUNTIMES.items())
    ]
    require(
        bindings
        == dict(calls=sorted(plain + helpers), data=labels, functions=[], switches=[]),
        "title menu requires exact typed original ELF imports and addends",
    )
    return dict(
        schema=runtime.SCHEMA,
        instructions=summary["instructions"],
        calls=plain,
        runtime_calls=helpers,
        partition=constants,
        buffers=dict(
            dependency_budget=named.MAX_DEPENDENCIES,
            owner_byte_budget=named.MAX_BYTES,
            dependencies=[],
            title_menu_style=summary["private_style_stores"],
            stack_index_preconditions=summary["conditional_indices"],
            runtime_summaries=summary["runtime"],
            title_style_producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        ),
    )
