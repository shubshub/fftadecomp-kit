"""Original scaled polygon scan converter and its privately saved coordinates."""

from hashlib import sha256
from pathlib import Path
import json

import match
import ordinary_formal_output_spill_profile as formal
import owner_graph_profile as graph

OWNER, END = 0x0800F480, 0x0800F6A6
JOIN, REMAINDER = 0x0800F522, 0x0800F544
WINDING, LEFT, RIGHT = 0x0800DECC, 0x0800DFB0, 0x0800E05C
LINE = (0x080075CC, 0x080076A0, 0x08007880)
R4, R5, R6 = (match.ARM_REG_R0 + n for n in (4, 5, 6))
EXPECTED_CALLS = {
    0x0800F4B2: WINDING,
    REMAINDER: formal.BiosRemainderSpillProof.wrapper_address,
    0x0800F5C6: RIGHT,
    0x0800F5E8: LEFT,
    0x0800F600: RIGHT,
    0x0800F63C: RIGHT,
    0x0800F654: LEFT,
    0x0800F67A: LEFT,
    0x0800F692: RIGHT,
}
BODIES = {
    OWNER: (550, 266, "a9941c6349ed69f42117d50ab1bde133ee2894a65198a01956dd84e0224417fd"),
    WINDING: (228, 112, "0ed10c277d024d2928619ad08d10b866fcfdfc605224d67ccdf4efeb4e3dd366"),
    LEFT: (170, 82, "99901786b083d5f38e3f4dd59b7d5869db58295655fcd7bc29ab92d9292fc996"),
    RIGHT: (180, 85, "a47e5f64cc65775cf327f81c9537c8223ea737e394f7997be1ce4b9fe9474118"),
    LINE[0]: (82, 41, "fabe74ee62782a4aa7c19892051162aa8cbddac5933389fe36101ee650f6ae80"),
    LINE[1]: (84, 42, "2d9d439311772de3361680e4b4b19685e89ef56f32e9772d01334dcb9f942383"),
    LINE[2]: (18, 9, "6910f725526c99f9f6057873874f34209091f84111ff9ac11530fe7c7e2387c9"),
    0x0800E110: (144, 68, "b26cfdba7222495acbcf9d9bc850e70558095f619ef20b07ccdb7e0aed114a0c"),
    0x0800E1A0: (200, 98, "a55e289abd2cdd1f45a49d074974736d7b92ea529b168430c786e31336bd9664"),
}
CONTRACT = (
    "Requires an aligned readable polygon with a positive u16 vertex count, readable four-halfword "
    "scale, 160 writable span pairs, and disjoint input, output and active stack. The two actual "
    "animation callers supply mode 1, a valid frame in their packed stream, and state offsets +8 "
    "and +0x290. Count zero has no division contract. For geometric winding, cross products and "
    "their difference must fit s32; for a full cyclic traversal first+count-1 must fit u16. "
    "First minima and maxima win ties; a zero determinant selects direction 1. The first vertex "
    "is scaled without the coordinate offsets. Remaining vertices apply offsets before scaling. "
    "Positive, reflected and collapsed scales follow signed Q8 arithmetic with halfword narrowing. "
    "Edge workers clip rows to 0..159; stored x values are halfwords. BIOS service 6 takes R0/R1, "
    "returns scalar quotient/remainder, ignores entry R2/R3 and preserves R4-R11/SP/LR on return. "
    "Interrupt interference, offered object validity and BIOS implementation are conditional."
)


def require(value, message):
    if not value:
        raise ValueError("scaled polygon: " + message)


def environment_fingerprint():
    import addressed_signed_runtime_profile as alignment

    producers = (
        "scaled_polygon",
        "owner_admission_profile",
        "owner_graph_profile",
        "ordinary_formal_output_spill_profile",
        "named_data_buffer_profile",
        "descriptor_output_alias_profile",
        "protected_descriptor_word_profile",
        "watched_switch_preservation_profile",
        "addressed_signed_runtime_profile",
        "match",
        "match_evidence",
        "function_thunk_profile",
        "owner_runtime_profile",
        "analyze",
        "armv4t",
        "local_long_branch_profile",
        "plausible",
    )
    return dict(
        toolchain=alignment.toolchain_fingerprint(),
        runtime=alignment.runtime_fingerprint(),
        producers={
            name: sha256(Path(__file__).with_name(name + ".py").read_bytes()).hexdigest()
            for name in producers
        },
    )


def elf_alignment(image, symbol):
    from addressed_signed_runtime_profile import terminal_alignment

    terminal_alignment(image, symbol)
    require(
        symbol["size"] == END - OWNER and len(image["text"]) == END - OWNER + 2,
        "original sized function with exactly two external alignment bytes",
    )


def rom_alignment(rom, mapping, index):
    mapped = json.loads(mapping)
    spans = [(int(row["rom"], 16), int(row["end"], 16)) for row in mapped]
    rows = [
        line.split()
        for line in index.decode().splitlines()
        if line.strip() and not line.lstrip().startswith("#")
    ]
    for records in (
        [(int(row["rom"], 16), int(row["end"], 16), row["instrs"]) for row in mapped],
        [(int(row[0], 16), int(row[1], 16), int(row[3])) for row in rows],
    ):
        components = {start: (end - start, count) for start, end, count in records if start in BODIES}
        require(
            components == {start: triple[:2] for start, triple in BODIES.items()},
            "paired component extent or instruction count",
        )
    for entries in (spans, [(int(row[0], 16), int(row[1], 16)) for row in rows]):
        require(
            (OWNER, END) in entries
            and sum(lo == END + 2 for lo, hi in entries) == 1
            and not any(lo < END + 2 and END < hi for lo, hi in entries),
            "external padding is owned or either indexed boundary moved",
        )
    require(rom[END - match.ROM_BASE : END - match.ROM_BASE + 2] == bytes(2), "external ROM alignment")


def native_body(data, address, count):
    size, expected_count, digest = BODIES[address]
    require(
        len(data) == size and count == expected_count and sha256(data).hexdigest() == digest,
        f"complete original body or CFG count at {address:08X}",
    )
    return dict(address=address, size=size, instructions=count, sha256=digest)


def original_graph(rom, mapping, index, address):
    import owner_admission_profile as admission

    size = BODIES[address][0]
    data = rom[address - match.ROM_BASE : address - match.ROM_BASE + size]
    admission.validate_span(data, address, rom, mapping, index)
    ref = admission.refine(data, address, mapping)
    ins, edges, branches, calls, words = graph.graph(data, address, ref)
    require(not branches and not words, "unexpected indirect or local call")
    graph.partition(data, address, ref, ins, words)
    return native_body(data, address, len(ins)), data, ins, edges, calls


def edge_frame(address, ins, edges, calls):
    # Both original rasterizers allocate 48 bytes. The outgoing word occupies
    # [0,4), the eleven s32 line fields [4,48), and all private saves [48,72).
    step, done, end = (0x82, 0x8E, 0x9E) if address == LEFT else (0x88, 0x94, 0xA4)
    require(
        calls == {address + 0x6C: LINE[0], address + step: LINE[1], address + done: LINE[2]},
        "edge worker line transitions",
    )
    expected = {
        0: ("push", "{r4, r5, r6, r7, lr}"),
        4: ("push", "{r7}"),
        6: ("sub", "sp, #0x30"),
        8: ("ldr", "r4, [sp, #0x48]"),
        0x68: ("str", "r0, [sp]"),
        0x6A: ("add", "r0, sp, #4"),
        0x7C: ("ldr", "r1, [sp, #4]"),
        step - 2: ("add", "r0, sp, #4"),
        done - 2: ("add", "r0, sp, #4"),
        end: ("add", "sp, #0x30"),
        end + 2: ("pop", "{r3}"),
        end + 6: ("pop", "{r4, r5, r6, r7}"),
        end + 8: ("pop", "{r0}"),
    }
    stack = {
        pc - address: (i.mnemonic, i.op_str)
        for pc, i in ins.items()
        if match.ARM_REG_SP in set().union(*i.regs_access())
    }
    require(stack == expected, "edge private save, incoming spans and line-buffer layout")
    require(
        ins[address + 2].mnemonic == "mov"
        and ins[address + 2].op_str == "r7, r8"
        and ins[address + end + 4].mnemonic == "mov"
        and ins[address + end + 4].op_str == "r8, r3"
        and {pc for pc, succ in edges.items() if not succ} == {address + end + 10}
        and ins[address + end + 10].mnemonic == "bx"
        and ins[address + end + 10].op_str == "r0",
        "edge common restoring return",
    )
    # The only copy of each watched entry register before these kills is its
    # initial private PUSH. No saved alias reaches the child calls or any use.
    pending = {R4, R5, R6}
    kills = {}
    for pc in range(address + 2, address + 24, 2):
        item = ins[pc]
        require(edges[pc] == (pc + 2,), "branch before opaque register kill")
        read, written = map(set, item.regs_access())
        require(not (read & pending), "observed edge entry alias")
        for reg in pending & written:
            kills[reg - match.ARM_REG_R0] = pc
        pending -= written
    require(not pending, "edge failed to overwrite private entry aliases")
    return dict(
        private_saves=[48, 72],
        line_buffer=[4, 48],
        incoming_spans_word=0,
        overwritten_before_use=sorted(kills.items()),
        restore=address + end + 6,
    )


class PolygonProof(formal.BiosRemainderSpillProof):
    def bind_polygon(self, data, address, ins, edges, calls):
        import owner_admission_profile as admission
        import named_data_buffer_profile as buffers

        require(address == OWNER and calls == EXPECTED_CALLS, "owner and nine reached calls")
        self.root = data, address
        self.ins, self.edges, self.calls = ins, edges, calls
        self.root_bios, self.root_join, self.saved_edges = set(), set(), set()
        self.polygon = dict(owner=native_body(data, address, len(ins)), callers=[], edges=[])
        require(self.span(self.wrapper_address) == self.wrapper_bytes, "BIOS remainder wrapper")
        rom_alignment(self.rom, self.mapping, self.index)
        for target in (0x0800E110, 0x0800E1A0):
            record, _, _, _, native_calls = original_graph(self.rom, self.mapping, self.index, target)
            site = 0x0800E178 if target == 0x0800E110 else 0x0800E20A
            require(native_calls.get(site) == OWNER, "original animation frame producer")
            self.polygon["callers"].append(dict(**record, call=site))
        for target in (LEFT, RIGHT):
            record, raw, items, flow, deps = original_graph(self.rom, self.mapping, self.index, target)
            frame = edge_frame(target, items, flow, deps)
            worker, _, _ = admission.preflight(
                raw,
                target,
                self.rom,
                self.mapping,
                self.index,
                self.objects,
                selector=buffers.ROOT_SCRATCH_SELECTOR,
            )
            nested = worker["proof"]["buffers"]["dependencies"]
            require({r["address"] for r in nested} == set(LINE), "complete line-worker effects")
            for row in nested:
                size, count, digest = BODIES[row["address"]]
                require(
                    (row["bytes"], row["structure"]["instructions"], row["body_sha256"])
                    == (size, count, digest),
                    "original nested line state or footprint",
                )
            self.polygon["edges"].append(dict(**record, frame=frame, worker=worker))

    def killed(self, site, reg):
        """Every successor must overwrite this value before use, return or loop."""
        pending, seen, kills = [site], set(), set()
        while pending:
            pc = pending.pop()
            if pc in seen:
                continue
            seen.add(pc)
            item = self.ins[pc]
            read, written = item.regs_access()
            if pc == REMAINDER:
                # Ignore neither register after the service. The value may
                # survive in either; its actual continuation must overwrite it.
                if reg not in (match.ARM_REG_R2, match.ARM_REG_R3):
                    return ()
            elif pc in self.calls or reg in read:
                return ()
            elif reg in written and item.cc in (match.ARM_CC_AL, match.ARM_CC_INVALID):
                kills.add(pc)
                continue
            if not self.edges[pc] or any(target <= pc for target in self.edges[pc]):
                return ()
            pending.extend(self.edges[pc])
        return tuple(sorted(kills))

    def join_dead(self, data, address, successor, reg, previous, incoming):
        if (
            (data, address) != self.root
            or self.scopes
            or successor != JOIN
            or reg != match.ARM_REG_R2
            or {previous, incoming} != {-72, -64}
        ):
            return False
        kills = self.killed(successor, reg)
        if kills:
            self.root_join.add((successor, reg - match.ARM_REG_R0, -72, -64, kills))
        return bool(kills)

    def check_call(self, address, aliases, stack, slots=None, *, constants=None, site=None, words=None):
        if site == REMAINDER and address == self.wrapper_address:
            require(not slots and not words and len(stack) == 18, "root BIOS frame")
            for reg, offset in aliases.items():
                if reg not in match.CALLER_CLOBBERED:
                    continue
                kills = self.killed(site + 4, reg)
                require(
                    reg in (match.ARM_REG_R2, match.ARM_REG_R3) and kills, "root BIOS observes a live local"
                )
                self.validate_pointer_value(offset, stack)
                self.root_bios.add((site, reg - match.ARM_REG_R0, offset, kills))
            return self.word_result({}, {})
        if address in (LEFT, RIGHT) and self.calls.get(site) == address:
            require(
                not slots and not words and len(stack) == 18 and set(aliases) <= {R4, R5, R6},
                "edge call carries a local outside its private preserved registers",
            )
            for reg, offset in aliases.items():
                self.validate_pointer_value(offset, stack)
                self.saved_edges.add((site, address, reg - match.ARM_REG_R0, offset))
            return self.word_result({}, {})
        return super().check_call(address, aliases, stack, slots, constants=constants, site=site, words=words)

    def polygon_manifest(self):
        native_body(self.span(WINDING), WINDING, self.records[WINDING]["structure"]["instructions"])
        require(self.root_join and self.root_bios and self.saved_edges, "missing local lifetime observations")
        require(
            {site for site, *_ in self.saved_edges} == {0x0800F5C6, 0x0800F5E8, 0x0800F600, 0x0800F63C},
            "edge contexts differ from the compiler output",
        )
        return dict(
            self.polygon,
            schema="usa-scaled-polygon-scanline-v1",
            mode_join=sorted(self.root_join),
            root_bios=sorted(self.root_bios),
            saved_edges=sorted(self.saved_edges),
            contract=CONTRACT,
            size=END - OWNER,
            external_elf_alignment="c046",
            external_ROM_alignment="0000",
            environment=environment_fingerprint(),
        )
