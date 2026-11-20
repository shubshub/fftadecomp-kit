"""Conditional native proof for the bounded four-choice action effect at 081323D0."""

import hashlib
import struct

import weighted_effect_fallback as fallback

BASE = 0x08000000
ADDRESS = 0x081323D0
PICKER = 0x0812D660
SCORER = 0x0812D1DC
RNG = 0x08002804
MOD = 0x08142950
THUNK = 0x08142248
TABLE = 0x083A87B0
WEIGHTS = 0x083A8484
SELECTOR = "conditional-four-choice-effect-v1"
SCHEMA = "elf-symbol-thumb-" + SELECTOR
CALLS = [
    [0x08, "func_080CD8FC"],
    [0x1A, "func_0812D660"],
    [0x2A, "func_08002804"],
    [0x34, "__modsi3"],
    [0x54, "_call_via_r1"],
    [0x68, "func_080CDD88"],
]
DATA = [[0x60, "data_083A87B0", 0]]
TARGETS = {
    name: (int(name[5:], 16), False) for _, name in CALLS if name.startswith("func_")
}
TARGETS.update(
    {
        "__modsi3": (MOD, False),
        "_call_via_r1": (THUNK, False),
        "data_083A87B0": (TABLE, True),
    }
)
CHOICES = (
    (15, 19, 0x081320E8),
    (25, 22, 0x08132160),
    (35, 51, 0x08132B44),
    (25, 24, 0x081321B4),
)


def require(condition, message):
    if not condition:
        raise ValueError("weighted effect: " + message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def check_bindings(address, bindings, targets=None):
    if address == fallback.ADDRESS:
        calls, data = fallback.CALLS, fallback.DATA
        expected = dict(TARGETS)
        del expected["func_0812D660"]
        expected["func_0812D7FC"] = (fallback.PICKER, False)
    else:
        require(address == ADDRESS, "unreviewed effect owner")
        calls, data, expected = CALLS, DATA, TARGETS
    require(
        bindings == dict(calls=calls, data=data, functions=[], switches=[])
        and (targets is None or targets == expected),
        "original ELF call/data roles or complete owner differ",
    )


def thumb16(instructions, start, expected):
    for offset, encoded in enumerate(expected.split()):
        value = int(encoded, 16)
        pc = start + offset * 2
        require(
            pc in instructions
            and bytes(instructions[pc].bytes) == value.to_bytes(2, "little"),
            f"native instruction at {pc:08X} differs",
        )


def weighted_rolls(rom, *, weights=WEIGHTS, choices=CHOICES, has_fallback=False):
    result = []
    for i, (weight, kind, target) in enumerate(choices):
        require(
            struct.unpack_from("<HH", rom, weights - BASE + 4 * i) == (weight, kind),
            "weighted ROM record differs",
        )
        pointer = struct.unpack_from("<I", rom, TABLE - BASE + 12 * kind)[0]
        require(
            pointer == target | 1,
            "selected descriptor does not contain its exact Thumb entry",
        )
        result.append(
            dict(
                weight=weight,
                kind=kind,
                descriptor=TABLE + 12 * kind,
                target=target,
                first=None,
                last=None,
            )
        )
    # The second and subsequent rows are fetched only on a signed positive remainder.
    # This exhausts every result of the checked nonnegative PRNG value modulo 101.
    unselected = []
    for roll in range(101):
        residual = roll
        for record in result:
            residual -= record["weight"]
            if residual <= 0:
                if record["first"] is None:
                    record["first"] = roll
                record["last"] = roll
                break
        else:
            require(has_fallback, "roll escapes the four real records")
            unselected.append(roll)
    if has_fallback:
        require(unselected == list(range(96, 101)), "equipment fallback interval differs")
        result.append(dict(kind=-1, target=None, first=96, last=100))
    require(
        all(record["first"] is not None for record in result),
        "an intended descriptor is unreachable",
    )
    return result


def caller_shape(data, instructions, calls, partition):
    require(
        sha(data) == "ff027f52dd6f35181d05b8905a419655c93a0b3b022b1d602f88330482b47dfe"
        and calls == {ADDRESS + offset: TARGETS[name][0] for offset, name in CALLS},
        "complete caller control flow or six targets differ",
    )
    # Allocate four after saving R4, R5 and LR. The zero-mode picker gets the literal
    # local SP, not the saved-register area, in R3; source/target derive from the action.
    thumb16(instructions, ADDRESS, "b530 b081 1c05 68a8")
    thumb16(instructions, 0x081323DC, "0600 2800 d128 6828 68a9 2200 466b")
    # Threshold is the signed low half of 10 times the signed low half of any result.
    thumb16(instructions, 0x081323EE, "0400 1400 0084 1824 0464 0c24")
    thumb16(instructions, 0x081323FE, "0400 1400 490a")
    # Signed roll test, sign-extended local halfword, 12*kind, word at offset zero,
    # and original state in R0 for the canonical BX R1.
    thumb16(
        instructions,
        0x08132408,
        "0424 0400 4284 db15 4a07 4668 2300 5ec1 0048 1840 0080 1880 6801 1c28",
    )
    thumb16(instructions, 0x08132448, "b001 bc30 bc01 4700")
    require(
        [(w["address"], w["value"], w["load_sites"]) for w in partition["words"]]
        == [(0x0813242C, 1001, [0x08132402]), (0x08132430, TABLE, [0x08132410])],
        "caller literal loads and divisor differ",
    )


def picker_shape(data, instructions, calls, partition):
    require(
        sha(data) == "be795bdba61e9630dc6a3318b00e3f02c9b4a59cdd5964b235bd8f102bbc2998",
        "complete picker or zero-mode branch differs",
    )
    require(
        calls
        == {
            **dict.fromkeys(
                (0x0812D6BA, 0x0812D6EA, 0x0812D722, 0x0812D758, 0x0812D7E4), SCORER
            ),
            0x0812D768: RNG,
            0x0812D772: MOD,
        },
        "picker targets differ",
    )
    # Preserve R8-R10 and R4-R7. R4 is the caller's halfword, R7/R6 the two game
    # objects. Since the caller passed zero in R2, skip the entire averaging branch.
    thumb16(
        instructions,
        PICKER,
        "b5f0 4657 464e 4645 b4e0 b086 1c07 1c0e 1c1c 0612 2a00 d100 e076",
    )
    thumb16(instructions, 0x0812D76C, "0400 1400 2165")
    # R3 starts at index zero. Read the first weight, then on a positive residual
    # advance R3 and read exactly the weight at base + 4*R3. Kind is offset two.
    thumb16(instructions, 0x0812D776, "0400 1402 2300 4908 8808 1a12")
    thumb16(
        instructions,
        0x0812D782,
        "1c3d 35f6 20f7 19c0 4680 20f6 1980 4681 20f7 1980 4682 20f8 1980 4684 e007",
    )
    thumb16(
        instructions,
        0x0812D7A4,
        "3301 4814 0099 1809 8808 1a12 2a00 dcf7 8848 8020 2300 5ee1",
    )
    # STRH [R4] followed by LDRSH [R4,zero]. R4 is overwritten before the
    # scorer sees it. Its four outgoing words hold signed coordinate bytes and
    # the selected scalar kind; none holds the caller's stack pointer.
    thumb16(
        instructions,
        0x0812D7BC,
        "2200 56aa 4644 2300 56e3 464c 2000 5620 9000 4654 2000 5620 9001 4664 2000 5620 "
        "9002 9103 1c38 1c31",
    )
    thumb16(instructions, 0x0812D7E8, "b006 bc38 4698 46a1 46aa bcf0 bc02 4708")
    require(
        [(w["address"], w["value"], w["load_sites"]) for w in partition["words"]]
        == [(0x0812D7A0, WEIGHTS, [0x0812D77C]), (0x0812D7F8, WEIGHTS, [0x0812D7A6])],
        "both picker table loads must resolve to the same typed record array",
    )


def prove(data, address, rom, mapping, index, objects, bindings):
    from capstone.arm import ARM_REG_R4, ARM_REG_R11
    import match
    import modsi3_profile as remainder
    import mod_only_structural_inventory as mod_inventory
    import named_data_buffer_profile as named
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    import local_long_branch_profile as frame
    import software_double_profile as canonical

    check_bindings(address, bindings)
    sentinel = address == fallback.ADDRESS
    picker = fallback.PICKER if sentinel else PICKER
    weights = fallback.WEIGHTS if sentinel else WEIGHTS
    slot = 29 if sentinel else 30
    owner_mod = 0x0813237A if sentinel else 0x08132404
    picker_mod = 0x0812D90E if sentinel else 0x0812D772
    names = match.parse_data_symbols(objects)
    for name, expected in (
        (f"data_{weights:08X}", weights),
        ("data_083A87B0", TABLE),
        ("data_0200F3F0", 0x0200F3F0),
        ("g_state_030034B0", 0x030034B0),
    ):
        require(names.get(name) == expected, f"original named object {name} differs")
    entries, rows = canonical.indices(mapping, index)
    ends = {int(r["rom"], 16): int(r["end"], 16) for r in entries}

    def native(start):
        require(start in ends, "missing mapped code entry")
        end = ends[start]
        record = canonical.span_record(start, end, entries, rows, rom)
        raw = rom[start - BASE : end - BASE]
        refined = owner.refine(raw, start, mapping)
        ins, edges, branches, calls, words = graph.graph(raw, start, refined)
        require(
            not branches and not words and len(ins) == record["instrs"],
            "exact reachable count/graph differs",
        )
        partition = graph.partition(raw, start, refined, ins, words)
        return raw, ins, edges, calls, partition

    def restoring(start, native_parts):
        _, ins, edges, calls, _ = native_parts
        return frame.prove_frame(
            ins,
            edges,
            start,
            {},
            calls,
            call_preservation={
                pc: frozenset(range(ARM_REG_R4, ARM_REG_R11 + 1)) for pc in calls
            },
        )

    raw, ins, edges, calls, partition = native(address)
    require(data == raw, "linked ELF bytes differ from original ROM")
    (fallback.caller_shape if sentinel else caller_shape)(raw, ins, calls, partition)
    helper = native(picker)
    (fallback.picker_shape if sentinel else picker_shape)(helper[0], helper[1], helper[3], helper[4])
    helper_frame = restoring(picker, helper)
    require(
        helper_frame["maximum_frame_bytes"] == 56,
        "picker frame size or restoration differs",
    )
    for start, span, owner_calls, site in (
        (address, raw, calls, owner_mod),
        (picker, helper[0], helper[3], picker_mod),
    ):
        require(
            remainder.verify_context(
                span, start, owner_calls, (rom, mapping, {site: "__modsi3"})
            ),
            "actual numeric runtime binding differs",
        )
    closure = canonical.prove_remainder_closure(rom, mapping, index)
    mod_frames = mod_inventory.runtime_frames(rom, mapping, closure)
    rng = native(RNG)
    require(len(rng[0]) == 32 and not rng[3], "PRNG extent or calls differ")
    thumb16(rng[1], RNG, "4a04 6811 4804 4348 4904 1840 6010 0040 0c40 4770")
    require(
        struct.unpack_from("<III", rng[0], 20) == (0x030034B0, 0x41C64E6D, 0x3039),
        "PRNG storage or recurrence differs",
    )
    dispatch = native(0x0813388C)[0]
    require(
        sha(dispatch)
        == "b1a2ee4c8cefef5b7581b6599971145c0e7a1a78a4e47f2b1c344ca282824d5c"
        and struct.unpack_from("<I", rom, TABLE - BASE + slot * 12)[0] == address | 1
        and canonical.span_record(THUNK, THUNK + 2, entries, rows, rom)["instrs"] == 1
        and rom[THUNK - BASE : THUNK - BASE + 2] == bytes.fromhex("0847"),
        "dispatcher, own descriptor or BX R1 differs",
    )
    choices = weighted_rolls(rom, weights=weights, choices=fallback.CHOICES if sentinel else CHOICES,
                             has_fallback=sentinel)

    score = native(SCORER)
    require(
        sha(score[0])
        == "c8089bf2287153953c402bb6633e03e5df957f462fd8a2a6a61ff72edb1923ca",
        "original scoring routine differs",
    )
    # The getter loads incoming words 0,4,8,12 after saving 52 bytes and later
    # uses its OWN separate four-byte chance local. Reuse the shipped buffer
    # verifier for the setter and nested writes to that local.
    thumb16(score[1], 0x0812D1EC, "980d 990e 9c0f 9f10")
    proof = named.GuardedSwitchBufferProof(rom, mapping, index, objects)
    reviewed, transfers = proof.inspect(SCORER, score[0])
    require(
        not transfers
        and {i.address for i in reviewed} == set(score[1])
        and set(proof.dependencies) == {0x0812C97C, 0x080C92F0},
        "nested scoring buffer call was not verified",
    )
    # Validate each of the actual descriptor callbacks and all of THEIR direct
    # descendants as restoring named scalar routine bodies. Bind this reviewed
    # closure to its original instructions, including the leaf memory effects.
    records = {}

    def callback(start):
        if start in records:
            return
        part = native(start)
        restored = restoring(start, part)
        records[start] = dict(
            end=start + len(part[0]),
            sha256=sha(part[0]),
            frame=restored["maximum_frame_bytes"],
            calls=sorted(part[3].items()),
            returns=restored["returns"],
        )
        for target in part[3].values():
            callback(target)

    for record in choices:
        if record["target"] is not None:
            callback(record["target"])
    from signed_divmod_profile import text

    closure_digest = sha(
        text([[a, records[a]["sha256"]] for a in sorted(records)]).encode()
    )
    require(
        closure_digest
        == ("2d7b73dbc0218a45a0100421fe40511aeb853e1c54f3cd6fab2cbfbb288208b0" if sentinel else
            "54ef182ace58b36a810fa5d3b30d99f754fb5d7eb22d7f7655e6ffc8cdfbd605"),
        "selected callback or transitive status leaf differs",
    )
    manifest = dict(
        schema=SCHEMA,
        bindings=bindings,
        partition=partition,
        dispatcher=[0x081338BA, THUNK, slot],
        picker=dict(
            address=picker,
            sha256=sha(helper[0]),
            frame=helper_frame,
            mode=0,
            table=weights,
            choices=choices,
            output=dict(
                register="r3",
                write=0x0812D930 if sentinel else 0x0812D7B6,
                read=0x0812D934 if sentinel else 0x0812D7BA,
                bytes=2,
                owner_local=[-16, -12],
                written=[-16, -14],
                caller_read=0x0813238A if sentinel else 0x08132416,
            ),
        ),
        runtime=dict(
            rng=RNG,
            rng_range=[0, 32767],
            exact_divisors=[[picker_mod, 101], [owner_mod, 1001]],
            closure_frames=mod_frames,
            residual_r3_at_picker_rng="PRNG does not read R3; MOD uses only its own frame",
        ),
        scorer=dict(
            address=SCORER,
            sha256=sha(score[0]),
            stack_words=[0, 4, 8, 12],
            outgoing_from_owner_sp=[-72, -56],
            buffer_dependencies=[
                [a, sha(b)] for a, b in sorted(proof.dependencies.items())
            ],
            guarded_accesses=proof.guarded_manifest(),
            formal_arguments=[
                "source",
                "target",
                "source x",
                "source y",
                "target x",
                "target y",
                "target height",
                "kind",
            ],
            other_direct_calls=sorted(score[3].items()),
            numeric_return="arbitrary low signed halfword",
        ),
        callback=dict(
            site=0x081323B0 if sentinel else 0x08132424,
            register="r1",
            argument="r0=original action",
            thunk=THUNK,
            selected_closure=[[a, records[a]] for a in sorted(records)],
        ),
        owner_frame=dict(local=[-16, -12], saved=[-12, 0], return_site=0x081323CE if sentinel else 0x0813244E),
        premises=[
            "Word-aligned accessible private stack, stable code/ROM, and accessible ordinary little-endian game objects.",
            "Action state, unit storage, RNG state and external writes remain disjoint from protected stack storage.",
            "Other ordinary scorer calls return under the existing ABI, preserving R4-R11, SP and caller storage.",
            "No asynchronous change to the live stack, code, weighted records or descriptor pointers during the call.",
        ],
    )
    if sentinel:
        manifest["equipment_fallback"] = fallback.equipment_path(rom, mapping, index, objects, native)
        manifest["picker"]["output"]["positive_descriptor_read"] = 0x081323A2
        manifest["premises"].extend(manifest["equipment_fallback"]["equipment_premises"])
    return manifest, ins
