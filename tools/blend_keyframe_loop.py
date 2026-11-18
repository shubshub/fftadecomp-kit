"""Volatile comparison for the USA blend-alpha callback's read-only keyframe search."""
from hashlib import sha256
import re

import library_units
import volatile_semantics as vs

OWNER = 0x08006720
FUNCTION = "func_08006720"
SYMBOL = "g_control_flags_03000940"
RUNTIME = "__divsi3"
# The loop proof below is for these three native compiler forms. The first
# has the original USA relocations applied independently by the match profile.
TEXT = (
    "aa02651c2969649477c2be60d578d98e5fcebe82848896345a9d406462dbb825",
    "8c97bf02ae1c9ca3998e7a910e1893a96924c95c95953dcab8ef87d21bc7d26a",
    "e4efabbff2a27d00f21c24337e9dd21156982acba888b35460173f3521bde5d2",
)
ROM_PARTS = (
    (0x6720, 0x6878, "ef57997e8064759e162a95d674db181d793a6e610f334d9f427ef382394709a9"),
    # 08006920 constructs a 12-byte-payload callback, taking records and count.
    (0x6920, 0x6940, "ec2443a344d0b3540835eb651fb1ab8b2c995ce107350eb905f42581472dc7ff"),
    # Allocator/initial callback and per-frame dispatcher both pass task,
    # descriptor, task+0x18. Initialization sets the scheduled event to 0x100.
    (0x5954, 0x5B00, "85db977f9e85dae6c63016b6da1ac443d2b674e4d48547b2cdba86a6d5a37c25"),
    (0x5B6C, 0x5BA8, "c6a20896e48a2d20f9a4e9d59b780095f5e082b65619a2a96cee0ebc26e8c475"),
    # 08000718 programs DMA0 from 03000942 to 04000008 for 39 halfwords.
    (0x0718, 0x0788, "d85bea0cb703a088cb7a895f53f83fe423cb279c46c69070b3a3b7db0f4c37bf"),
)


def require(condition, explanation):
    if not condition:
        raise ValueError("blend keyframe search: " + explanation)


def verify_object(image, variant):
    import match
    match.allocated_text_only(image)
    require(image["type"] == 1 and len(image["relocations"]) == 1, "expected one relocatable text section")
    body, relocations, offset, value, size = library_units.signature(image, OWNER)
    a, b, c, d = (160, 234, 258, 300) if variant == 1 else (172, 246, 272, 316)
    require((offset, value, size) == (0, 1, len(body)) and sha256(body).hexdigest() == TEXT[variant],
            "original compiler text or full Thumb symbol differs")
    require(relocations == ((a, 2, SYMBOL), (b, 10, RUNTIME), (c, 10, RUNTIME), (d, 2, SYMBOL)),
            "expected exactly the two shadow addresses and two division calls")
    for name in (SYMBOL, RUNTIME):
        referenced = [s for s in image["symbols"] if s["name"] == name]
        require(len(referenced) == 1 and all(referenced[0][key] == expected for key, expected in
                (("section", 0), ("value", 0), ("size", 0), ("type", 0), ("bind", 1))),
                "expected an undefined external symbol")


def expected_blocks(stripped):
    # Canonical agbcc register allocations. The guard reads the current and
    # next signed little-endian times, first low byte then high, and cursor+10.
    index, base, count, payload = ("r4", "r5", "r8", "r9") if stripped else ("r3", "r4", "r5", "sl")
    init = (f"mov {index}, #0|mov r0, {payload}|ldr {base}, [r0]|ldr r1, [r0, #4]|mov {count}, r1"
            if stripped else f"mov {index}, #0|mov r6, {payload}|ldr {base}, [r6]|ldr {count}, [r6, #4]")
    times = ("ldrb r1, [r3]|ldrb r0, [r3, #1]" if stripped else
             "mov r0, r9|ldrb r1, [r0]|ldrb r0, [r0, #1]")
    cursor = (f"mov r6, {payload}|mov r1, #10" if stripped else f"mov r1, {payload}|mov r6, #10")
    cursor += "|ldrsh r2, [r6, r1]" if stripped else "|ldrsh r2, [r1, r6]"
    extend = "lsl r0, r0, #16|asr r0, r0, #16|cmp r2, r0"
    combine = "lsl r0, r0, #8|orr r0, r0, r1"
    current = f"add r3, {base}, r1" if stripped else f"add r0, {base}, r1|mov r9, r0"
    return index, {
        ".L7": init + "|b .L8",
        ".L13": f"{times}|{combine}|{cursor}|{extend}|blt .L10|ldrb r1, [r7]|ldrb r0, [r7, #1]"
                f"|{combine}|{extend}|blt .L9",
        ".L10": f"add {index}, {index}, #1",
        ".L8": f"lsl r1, {index}, #2|{current}|add r0, {index}, #1|cmp r0, {count}|bge .L11"
               f"|add r0, r1, #4|add r7, {base}, r0|b .L12",
        ".L11": "mov r7, #0",
        ".L12": "cmp r7, #0|bne .L13",
    }


REG = re.compile(r"\b(?:r(?:1[0-5]|[0-9])|sl|fp|ip|sp|lr|pc)\b")


def regset(text):
    return {vs.register(r) for r in REG.findall(text)}


def effects(instruction):
    op, args, _ = instruction
    reads = regset(" ".join(args))
    writes = set()
    if op in {"mov", "add", "sub", "ldr", "ldrb", "ldrsh", "ldrh", "lsl", "asr", "lsr", "orr", "mul"}:
        require(len(args) >= 2 and args[0] != "pc", "unsupported data or control transfer")
        reads = regset(" ".join(args[1:]))
        writes = regset(args[0])
    elif op == "cmp":
        writes = {"flags"}
    elif op in {"bne", "beq", "bgt", "blt", "bge"}:
        reads = {"flags"}
    elif op == "bl":
        require(args == [RUNTIME], "unexpected call")
        # r0 is the result. Conservatively allow every other scratch
        # register/flag to survive when computing live values across BL.
        reads, writes = {"r0", "r1"}, {"r0", "lr"}
    elif op == "pop":
        writes, reads = reads | {"sp"}, {"sp"}
    elif op == "push":
        reads, writes = reads | {"sp"}, {"sp"}
    elif op == "bx":
        require(args == ["r1"], "unexpected return")
        reads |= {"r0", "sp", *(f"r{i}" for i in range(4, 12))}
    else:
        require(op in {"str", "strh", "strb", "b"}, "unsupported instruction in liveness proof")
    return reads, writes


def finite_iteration(assembly, stripped):
    functions, _ = vs.parse_assembly(assembly)
    require(set(functions) == {FUNCTION}, "additional compiler function")
    code, labels, pools = functions[FUNCTION]
    declared = re.findall(r"(?m)^([.\w$]+):", assembly)
    require(len(set(declared)) == len(declared), "duplicate compiler label")
    require("r12" not in regset(" ".join(i[2] for i in code)), "symbolic index register is live")
    index, blocks = expected_blocks(stripped)
    boundaries = [*blocks, ".L9"]
    for start, stop in zip(boundaries, boundaries[1:]):
        actual = [" ".join((op, ", ".join(args))).strip() for op, args, _ in code[labels[start]:labels[stop]]]
        require(actual == blocks[start].split("|"), "incorrect read-only search block " + start)
    require(len(pools) == 2 and all(value == [("sym", SYMBOL)] for value in pools.values()), "unexpected literal pool")
    successors, touched = [], []
    for pc, instruction in enumerate(code):
        op, args, _ = instruction
        touched.append(effects(instruction))
        if op == "bx":
            following = []
        elif op == "b":
            following = [labels[args[0]]]
        elif op in {"bne", "beq", "bgt", "blt", "bge"}:
            following = [pc + 1, labels[args[0]]]
        else:
            following = [pc + 1]
        require(all(0 <= end < len(code) for end in following), "invalid compiler CFG")
        if not labels[".L7"] <= pc < labels[".L9"]:
            require(all(not labels[".L7"] < end < labels[".L9"] for end in following),
                    "external entry bypasses index initialization")
        successors.append(following)

    # Live-in least fixed point on the original, uncut CFG, including the
    # exit, division helper's ABI, restored callee-saves and the return word.
    live = [set() for _ in code]
    changed = True
    while changed:
        changed = False
        for pc in reversed(range(len(code))):
            reads, writes = touched[pc]
            after = set().union(*(live[end] for end in successors[pc]))
            before = reads | (after - writes)
            if before != live[pc]:
                live[pc] = before
                changed = True
    loop_writes = set().union(*(item[1] for item in touched[labels[".L13"]:labels[".L9"]]))
    require(loop_writes & live[labels[".L8"]] == {index}, "additional live state crosses the backedge")
    epilogue = [" ".join((op, ", ".join(args))) for op, args, _ in code[labels[".L4"]:]]
    require(epilogue == ["mov r0, #0", "add sp, sp, #8", "pop {r3, r4, r5}", "mov r8, r3",
            "mov r9, r4", "mov sl, r5", "pop {r4, r5, r6, r7}", "pop {r1}", "bx r1"],
            "cutoff must have a store-free return")
    for label, replacement in ((".L7", f"mov {index}, ip"), (".L10", "b .L4")):
        # Modify exactly the instruction validated above. Label count matters
        # because parse_assembly otherwise gives the last duplicate label.
        pattern = rf"(?m)^{re.escape(label)}:\n[ \t]*{re.escape(code[labels[label]][2])}$"
        assembly, count = re.subn(pattern, f"{label}:\n\t{replacement}", assembly)
        require(count == 1, "ambiguous cut instruction")
    return assembly


def record(assemblies, images, preprocessed, entry, interfaces, rom, location):
    require(entry["symbol"] == SYMBOL and location == 0x03000940, "unexpected shadow binding")
    require(rom is not None and all(sha256(rom[start:end]).hexdigest() == digest
            for start, end, digest in ROM_PARTS), "USA callback, installation, dispatch or display upload differs")
    require(rom[0x142250:0x142252] == b"\x18\x47", "expected the original BX r3 callback veneer")
    for variant, image in enumerate(images):
        verify_object(image, variant)
    reduced = [finite_iteration(assembly, i == 1) for i, assembly in enumerate(assemblies)]
    results = vs.compare(reduced[0], reduced[1], preprocessed, SYMBOL, entry["declaration"], reduced[2], interfaces)
    return (vs.record(SYMBOL, results, perturbed=True) +
            ". Keyframe search induction starts at zero and advances one four-byte record per continuation. "
            "The comparison covers an arbitrary iteration, assuming stable ordinary readable records and mutually disjoint "
            "valid records, event, payload and shadow storage. BLDALPHA shadow bytes +0x4c/+0x4d are uploaded by 08000718")


def report_scope(report):
    # The finite-loop record is issued for the complete runtime-linked owner.
    # The full addressed profile then recreates both the ELF and its report.
    import addressed_signed_runtime_profile as profile
    require(profile.selector_for_report(report) == "compiler-signed-runtime-data-v1",
            "the keyframe induction requires the complete addressed runtime report")
