"""USA four-slot scanline manager. The three canonical compiles have the same complete machine transition."""

from hashlib import sha256
from pathlib import Path
import json
import re
import struct

import bg_affine_rows
import library_units
import plausible
import scanline_wave
import scroll_prefix_scene
import volatile_semantics as vs

BASE = 0x08000000
OWNER, END = 0x0800C4B4, 0x0800C5F4
SYMBOL = "g_control_flags_03000940"
BODY = "c6d6ae60535de05d825bbee9eee235c75d08b321162757be40dcb5fba421c9a4"
OBJECT = "bafd25fdc7695968d999b99e399dc216c1ea6ee15d02c61daa15cf52a2ae0c4a"
TOKENS = "9c67460fa92ffddc8df61a2aa2d05976266737b54364711e5a0d074da748b809"
CALLS = (
    (90, "_call_via_r2", 0x0814224C),
    (108, "func_0814186C", 0x0814186C),
    (160, "func_08000D90", 0x08000D90),
    (204, "func_080009AC", 0x080009AC),
    (262, "func_0814186C", 0x0814186C),
)
DATA = (
    (64, "data_02009148", 0x02009148),
    (232, "data_02009148", 0x02009148),
    (236, SYMBOL, 0x03000940),
    (272, "data_03000942", 0x03000942),
    (316, "data_03003860", 0x03003860),
)
# Additional constructor/callback paths beyond the wave, BG affine, and BG scroll providers.
PROVIDERS = (
    (0x0800C804, 0x0800C9E4, "4b7ceb147f4abc9eff443c5926649876170d9ec718fd376182b44d87984947ab"),
    (0x0800D324, 0x0800D3BA, "63e47da80196e2c8c3576b0776e028a69a66a68258894712ac27757283982095"),
    (0x0800D61C, 0x0800D664, "28df2f7430ea98719177a109c9ef6d9c1a6d42b7a137eb8f8773c953875785d0"),
    (0x0800DDB0, 0x0800DECC, "d573e491d6011e43ab7072fdc0e2988870860df12251e8ba67a3f934c0977201"),
    (0x0800E1A0, 0x0800E4DC, "11f428c1df900540753276d5335cecb029edec3fe93ce35506eab8b072f9426e"),
    (0x0800F308, 0x0800F6A6, "3f6a4fa7020fee884fe6b32a1af8c2198b30ce9e29ffecda37234458a383b749"),
    (0x0800F93C, 0x0800FFF8, "be5972e9addf5ee236ac8bc193f4867ae95fadd35b4069dd9c2209dd1e19e964"),
    (0x080D963C, 0x080D96F0, "2d588afdffe583cc0e6dfe1f8969f08a60d1e223dda38c9809e39b1a7da11bd4"),
    (0x080D9BC0, 0x080D9C56, "65b0735e364a18d009b5698c9f97374a327f1cfba9807c122ed2bd195ac4d918"),
    (0x080D9C58, 0x080D9CF4, "0d5b68179a3ba9e8ab2970fc5fe616d4d6c6b119a56db0b23ed092b67ab5da90"),
    (0x0800C34C, 0x0800C3CC, "858afbeada69fb493a81d901aab5c8c97863be1202be115017458d52be406a9b"),
)
CONSTRUCTOR_SITES = (
    0x0800CD0C,
    0x0800CE5A,
    0x0800CF4C,
    0x0800D01A,
    0x0800D0EE,
    0x0800D1C6,
    0x0800D630,
    0x0800E46C,
    0x0800F9DC,
    0x0800FA40,
    0x0800FAEA,
    0x0800FB9C,
    0x0800FC22,
    0x0800FCCE,
    0x0800FD80,
    0x0800FE30,
    0x0800FEC2,
    0x0800FF18,
    0x0800FF94,
    0x080D9684,
    0x080D9C0A,
    0x080D9C9C,
)


def require(condition, message):
    if not condition:
        raise ValueError("scanline dispatcher: " + message)


def branch(rom, address):
    high, low = struct.unpack_from("<HH", rom, address - BASE)
    require(high & 0xF800 == 0xF000 and low & 0xF800 == 0xF800, "expected original Thumb call")
    delta = (high & 2047) << 12 | (low & 2047) << 1
    return address + 4 + delta - ((delta & 0x400000) << 1)


def provider(rom):
    bg_affine_rows.provider(rom)
    scanline_wave.provider(rom)
    scroll_prefix_scene.provider(rom)
    for start, end, digest in PROVIDERS + (
        (OWNER, END, BODY),
        (0x0800D3BC, 0x0800D61A, bg_affine_rows.SHAPES["qualified"][1]),
    ):
        require(sha256(rom[start - BASE : end - BASE]).hexdigest() == digest, f"changed provider {start:08X}")
    require(branch(rom, 0x0800A646) == OWNER, "changed frame caller")
    require(all(branch(rom, site) == 0x0800C3CC for site in CONSTRUCTOR_SITES), "changed task registration")
    require(
        struct.unpack_from("<4I", rom, 0x149B24) == (0x04000020, 0x04000030, 0x04000040, 0x04000042),
        "changed affine/window targets",
    )


def check_image(image, rom, objects):
    import match

    match.allocated_text_only(image)
    raw, relocations, offset, value, size = library_units.signature(image, OWNER)
    symbol, _ = match.function_record(image, "func_0800C4B4", OWNER, True)
    require(
        (image["type"], symbol["bind"], symbol["type"], offset, value, size, len(raw))
        == (1, 1, 2, 0, 1, END - OWNER, END - OWNER)
        and sha256(raw).hexdigest() == OBJECT,
        "changed complete Thumb object",
    )
    require(
        len(image["relocations"]) == 1
        and image["sections"][image["relocations"][0]][7] == image["text_index"],
        "expected only .rel.text",
    )
    expected = [(site, 10, name) for site, name, _ in CALLS] + [(site, 2, name) for site, name, _ in DATA]
    require(relocations == tuple(sorted(expected)), "changed data or call relocations")
    for name in {name for _, _, name in expected}:
        syms = [s for s in image["symbols"] if s["name"] == name]
        require(
            len(syms) == 1
            and tuple(syms[0][k] for k in ("section", "value", "size", "type", "bind")) == (0, 0, 0, 0, 1),
            "changed undefined symbol " + name,
        )
    linked = bytearray(raw)
    for site, name, target in CALLS:
        require(
            raw[site : site + 4] == bytes.fromhex("fff7feff") and branch(rom, OWNER + site) == target,
            "changed call addend or destination " + name,
        )
        delta = target - (OWNER + site + 4)
        struct.pack_into("<HH", linked, site, 0xF000 | (delta >> 12 & 2047), 0xF800 | (delta >> 1 & 2047))
    for site, name, address in DATA:
        require(
            objects.get(name) == address and raw[site : site + 4] == bytes(4), "changed mapped base " + name
        )
        struct.pack_into("<I", linked, site, address)
    require(
        linked == rom[OWNER - BASE : END - BASE], "complete relocated compiler image differs from original"
    )


def second_pass(assembly, slot):
    """Project one iteration of pass 2 for the generic member-access verifier."""
    require(slot in range(4), "invalid physical slot")
    for anchor in (".L9:", "ble\t.L9\t@cond_branch\n\tmov\tr7, #0", "ble\t.L22\t@cond_branch"):
        require(assembly.count(anchor) == 1, "changed native slot-loop control")
    return (
        assembly.replace(".L9:", "b\t.Lscanline_second\n.L9:")
        .replace(
            "ble\t.L9\t@cond_branch\n\tmov\tr7, #0",
            f"ble\t.L9\t@cond_branch\n.Lscanline_second:\n\tmov\tr7, #{slot}",
        )
        .replace("ble\t.L22\t@cond_branch", "b\t.Lscanline_done\n.Lscanline_done:")
    )


def record(assemblies, images, preprocessed, entry, interfaces, rom, objects):
    require(
        entry["symbol"] == SYMBOL and interfaces is not None, "missing named control or ROM callee interfaces"
    )
    provider(rom)
    require(len(images) == len(assemblies) == 3, "three canonical compiles required")
    for image in images:
        check_image(image, rom, objects)
    # Preserve the exact typed field, callback ABI, member use and transfer expression. All three
    # ELF images include the same calls, pools and loads. Given equal machine states every original
    # instruction has the same transition, including the real BX and conditional BIOS side effects.
    # Induction therefore composes across arbitrary interleavings of slot states, without assuming
    # an opaque callback preserves caller-saved registers, RAM, the active bank, or flags.
    require(assemblies[0] == assemblies[1] == assemblies[2], "changed control assembly")
    # Each original pass starts at 0 and increments r7 until its signed value exceeds 3.
    # The callback uses r2 as its target, while r0/r1 supply the payload and bank independently.
    # No branch can avoid the final increment or re-enter the body at an intermediate instruction.
    functions, _ = vs.parse_assembly(assemblies[0])
    require(set(functions) == {"func_0800C4B4"}, "unexpected emitted function")
    code, labels, pools = functions["func_0800C4B4"]
    normalized = json.dumps(([(op, args) for op, args, _ in code], labels, pools), sort_keys=True).encode()
    require(
        sha256(normalized).hexdigest() == "e00a0935aff332c0d8850687102ab20fe838033afaaeea90c476e2acd94ecee2",
        "changed instructions, native branch labels or pools",
    )
    for loop, tail in ((".L9", ".L8"), (".L22", ".L21")):
        start, finish = labels[loop], labels[tail]
        require(
            tuple((op, tuple(args)) for op, args, _ in code[finish : finish + 3])
            == (("add", ("r7", "r7", "#1")), ("cmp", ("r7", "#3")), ("ble", (loop,))),
            "changed loop increment or endpoint",
        )
        require(
            all(
                op not in ("mov", "add", "sub", "ldr") or args[0] != "r7"
                for op, args, _ in code[start:finish]
            ),
            "changed slot inside loop",
        )
    require(
        rom[0xC50A:0xC512] == bytes.fromhex("081c291c35f19dfe")
        and rom[0xC4D4:0xC4D6] == bytes.fromhex("2268"),
        "changed callback field or ABI",
    )
    tokens = plausible.declaration_tokens(vs.translation_unit(preprocessed))
    start = [
        i
        for i in range(len(tokens))
        if tokens[i : i + 6] == ["typedef", "void", "(", "*", "ScanlineCallback", ")"]
    ]
    require(
        len(start) == 1 and sha256(" ".join(tokens[start[0] :]).encode()).hexdigest() == TOKENS,
        "changed typed dispatcher source or callback signature",
    )
    for slot in range(4):
        real, stripped, perturbed = (second_pass(assembly, slot) for assembly in assemblies)
        paths = vs.compare(real, stripped, preprocessed, SYMBOL, entry["declaration"], perturbed, interfaces)
        require(paths == [("func_0800C4B4", 14, [], [], [], [])], "changed per-slot member-access paths")
    return (
        "* allowlisted volatile scanline dispatcher: all three complete original/stripped/permuted "
        "320-byte Thumb images and ten external relocations agree. Both signed loops visit slots 0..3. "
        "Pass one calls the unchanged callback word through BX r2 with payload (or null) and inactive bank, "
        "copies one element to row 160 via CpuSet and rotates the bank. Pass two replays all 14 branch "
        "paths separately at each physical slot, cancels a previous handle and submits bank + element for "
        "HBlank DMA. A successful DISPCNT request stores one ordinary halfword to 03000940; "
        "04000008..04000053 copies element_size/2 halfwords into the LCD shadow at 03000942 + offset; "
        "05000000..050003FF stores one halfword to 03003860. Other destinations and failed submissions "
        "do not write a shadow. Requires initialized live task slots, successful allocations, "
        "ABI-returning callbacks with valid input resources and exclusive owned banks, "
        "front 0/1, old handles -1 or 0..3, valid hardware destinations for the whole transfer, "
        "and synchronized DMA/IRQ and task lifetime. A copy into the 80-byte control block requires "
        "destination - 04000008 + element_size <= 78; the native start-only check does not enforce it. "
        "For wave producers first <= 160 and last < 160, "
        "for affine producers BG 2/3, and for indexed windows a valid initialized shape and window index. "
        "The raw LCD copy is a BIOS halfword transfer through the physical shadow base, independent "
        "of the names permuted in the declaration."
    )


def report_body(report, root):
    from match_evidence import report_rom_path

    rom = Path(report_rom_path(root)).read_bytes()
    body = rom[OWNER - BASE : END - BASE]
    lines = report.splitlines()
    expected = (
        (r"^\* verification:", "* verification: `elf-symbol-thumb-data-v1`"),
        (r"^\* ROM bytes:", f"* ROM bytes: `{body.hex()}` (320 bytes)"),
        (r"^\* compiled\s*:", f"* compiled : `{body.hex()}`"),
        (r"^\*\*MATCH", "**MATCH - byte identical** - 320/320 bytes"),
    )
    return sha256(body).hexdigest() == BODY and all(
        [line for line in lines if re.match(pattern, line.lstrip())] == [value] for pattern, value in expected
    )
