"""Effect 29 has four descriptor callbacks and a separate equipment-based fallback."""

import struct

ADDRESS = 0x0813233C
PICKER = 0x0812D7FC
WEIGHTS = 0x083A8494
EQUIPMENT = 0x0812C8DC
CALLS = [
    [0x08, "func_080CD8FC"], [0x16, "func_080CDD88"], [0x24, "func_0812D7FC"],
    [0x34, "func_08002804"], [0x3E, "__modsi3"], [0x74, "_call_via_r1"],
]
DATA = [[0x7C, "data_083A87B0", 0]]
CHOICES = (
    (10, 27, 0x08132268), (25, 22, 0x08132160),
    (35, 35, 0x081324CC), (25, 24, 0x081321B4),
)


def caller_shape(raw, ins, calls, partition):
    from weighted_effect_profile import sha, thumb16, require, THUNK, RNG, MOD, TABLE
    require(sha(raw) == "9726ab387aa37e3069ddc89f01421f0775ac56b65f2f6f2e044f0a246c6651d5"
            and calls == {ADDRESS+8: 0x080CD8FC, ADDRESS+0x16: 0x080CDD88, ADDRESS+0x24: PICKER,
                          ADDRESS+0x34: RNG, ADDRESS+0x3E: MOD, ADDRESS+0x74: THUNK},
            "effect 29 body or calls differ")
    thumb16(ins, ADDRESS, "b530 b081 1c05 68a8")
    thumb16(ins, 0x08132348, "0600 2800 d004 68a8 2100")
    thumb16(ins, 0x08132356, "e031 6828 68a9 2200 466b")
    thumb16(ins, 0x08132364, "0400 1400 0084 1824 0464 0c24")
    thumb16(ins, 0x08132374, "0400 1400 4907")
    # A failed threshold sets flags. On success the signed kind distinguishes
    # the fallback write from the table lookup; only positive kinds index it.
    thumb16(ins, 0x0813237E, "0424 0400 4284 db1a 4668 2300 5ec0 2800 dc05 68a9 2001 8308 e017")
    thumb16(ins, 0x0813239C, "4a06 4668 2300 5ec1 0048 1840 0080 1880 6801 1c28")
    thumb16(ins, 0x081323B4, "e008")
    thumb16(ins, 0x081323BC, "8ce9 2280 0052 1c10 4308 84e8 b001 bc30 bc01 4700")
    require([(r["address"], r["value"], r["load_sites"]) for r in partition["words"]] ==
            [(0x08132398, 1001, [0x08132378]), (0x081323B8, TABLE, [0x0813239C])],
            "effect 29 divisor or descriptor literal differs")


def picker_shape(raw, ins, calls, partition):
    from weighted_effect_profile import require, sha, thumb16, SCORER, RNG, MOD
    require(sha(raw) == "bfe0c50c602e5607d56eeec872505ba2051a5c46b0c13f970a43c73b337587dd"
            and calls == {**dict.fromkeys((0x0812D856, 0x0812D886, 0x0812D8BE, 0x0812D8F4,
                                          0x0812D96E), SCORER), 0x0812D904: RNG,
                          0x0812D90E: MOD, 0x0812D988: EQUIPMENT},
            "effect 29 picker body or calls differ")
    # The zero-mode edge skips the averaging code. R4 saves R3, the address
    # of the caller's halfword. Both possible writes occur before a nested call.
    thumb16(ins, PICKER, "b5f0 4657 464e 4645 b4e0 b086 1c07 1c0e 1c1c 0612 2a00 d100 e076")
    thumb16(ins, 0x0812D908, "0400 1400 2165")
    thumb16(ins, 0x0812D912, "0400 1403 2200 e000 3201 2a03 d82b 4814 0091 1809 8808 1a1b 2b00 dcf5 8848 8020 2000 5e21")
    thumb16(ins, 0x0812D936, "1c38 30f6 2200 5682 3001 2300 56c3 1c30 30f6 7800 0600 1600 9000")
    thumb16(ins, 0x0812D950, "1c30 30f7 7800 0600 1600 9001 1c30 30f8 7800 0600 1600 9002 9103 1c38 1c31")
    thumb16(ins, 0x0812D972, "e00b")
    thumb16(ins, 0x0812D978, "2101 4249 1c08 8020 1c38 1c31 2202 2300")
    thumb16(ins, 0x0812D98C, "b006 bc38 4698 46a1 46aa bcf0 bc02 4708")
    require([(r["address"], r["value"], r["load_sites"]) for r in partition["words"]] ==
            [(0x0812D974, WEIGHTS, [0x0812D920])], "effect 29 weights literal differs")


def equipment_path(rom, mapping, index, objects, native):
    import owner_admission_profile as owner
    import positioned_equipment_chance as chance
    from signed_divmod_profile import text
    from weighted_effect_profile import require, sha, thumb16, SCORER, BASE, TABLE, THUNK
    # Unlike the neighbouring picker, R4 still carries the output pointer when
    # the scorer/equipment helper is entered. Both save it in private stack
    # storage and overwrite R4 before any non-save use or nested call.
    thumb16(native(SCORER)[1], SCORER, "b5f0 4657 464e 4645 b4e0 b085 9002 1c0d 980d 990e 9c0f")
    raw, ins, _, calls, _ = native(EQUIPMENT)
    thumb16(ins, EQUIPMENT, "b5f0 b087 1c05 1c0e 0614 0e24")
    signed_chance = chance.prove(raw, rom, mapping, index, objects,
                                 chance.equipment.bindings(chance.CALLS), ins, calls,
                                 owner.refine(raw, EQUIPMENT, mapping), {})
    require(0x0812D988 in signed_chance["caller_sites"], "fallback caller was not reviewed")
    # Recheck the actual indirect caller: record kind -> 12-byte descriptor,
    # word zero -> BX R1, with the address of the global action in R0.
    _, dispatch, _, dispatch_calls, _ = native(0x0813388C)
    thumb16(dispatch, 0x081338A8, "4d1d 6b20 7841 0048 1840 0080 1940 6801 1c20")
    require(dispatch_calls[0x081338BA] == THUNK and
            struct.unpack_from("<III", rom, 0x08133918-BASE) == (0x0200F3F0, 0x0000FFDF, TABLE),
            "real dispatcher action pointer, mask, descriptor binding or BX differs")
    return dict(callee=EQUIPMENT, call=0x0812D988, arguments=["source", "target", 2, 0],
                proof_sha256=sha(text(signed_chance).encode()), selector_proof=signed_chance["schema"],
                equipment_premises=signed_chance["conditions"],
                sentinel=-1, write=0x0812D97E, applied_at=0x08132394, target_offset=0x18,
                target_width=2, value=1)
