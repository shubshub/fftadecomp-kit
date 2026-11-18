"""USA BG3 scroll effect. Bind the three native objects and its live scheduler/graphics arenas."""
from hashlib import sha256
from pathlib import Path
import re
import struct

import library_units
import volatile_semantics as vs

BASE = 0x08000000
OWNER = 0x080EF484
END = 0x080EF638
SHADOW = 0x03000940
SYMBOL = "g_control_flags_03000940"
BODY = "9ad81dbb4a276bab49a7afab1e2ce3fcbdbce360b7e0f2b24791adb125515fdb"
OBJECT = "b154c94482e244e92b19e4114b20133d6e505238f9006ce41e3a6fcb9e24c84b"
PROVIDER = (
    # Root heap, scene arena split, initialized eight-byte arena headers and allocator.
    (0x080227E8, 0x0802282C, "08927eaf71bf2128a7f7b182e0aaefccdc2cf8484bd7aec584add8cf449ed11d"),
    (0x08022840, 0x08022854, "14cb0536da48cf8687d014bc016ba15e46c4576c2f39fcccd74b5d3cd6daf29c"),
    (0x080D36B0, 0x080D376C, "474dc64bfa9564a33134e72500f5f21a95c8103860baa94b847b47f7e647179c"),
    (0x0800A5F8, 0x0800A61C, "845153fa47c7dabfdbf469c02749c64d501d38ee0e767fccb6d346e7fd0f291b"),
    (0x0800C6CC, 0x0800C70C, "7948845160595072adb72d5c6aac9995670b1a6c0cf00185704d5ea7bff91ccb"),
    (0x08005C14, 0x08005C32, "caccd91ce3241962205e03a6cd4b6b51a3b584a42e73622787c0741cd62e17c2"),
    (0x080070C8, 0x08007138, "35f111b2b660201921f661a3b04ffa329d46a3e76736e8d912a2203164b01d93"),
    (0x08006C88, 0x08006D36, "7753b4551e4d959c458be6fb052231a28bdd00592aa2a47c75f066aeb2de5dd5"),
    (0x08006D38, 0x08006D9E, "ebb75817e6e49a104d4d7562559c89ddc557fad028fc27e7b58bb62aa017566b"),
    (0x08006DA0, 0x08006E26, "52ccddd712513cc0c943490a0be055ad763ddc048fcd42af45a2e191bbb86384"),
    (0x08006E28, 0x08006EBE, "d7d37063b367add1fa0a31c1c1f7f89482d89a4168b56c001ac521d53dba530b"),
    (0x08006EC0, 0x08006FCA, "ce1efcfe278bbb02f1e96f0943f5be3fa8feef032f2bb456893e67bbd3b33b00"),
    (0x08007138, 0x0800716E, "41bb84543d24c53f9292d190bc5e895370602a394d7b1db5169b21fcfa6f027f"),
    # Parent creates a 0x24-byte owner. Scheduler sets event zero and dispatches later phases.
    (0x080EFAB0, 0x080EFCBE, "53ac27184d8f0659c1925d72db071051466eada880aa51d706a11e599ec32a4b"),
    (0x08005A24, 0x08005AFE, "92a60c7b7568e688bda0434c5efc4945c67b84c3d73a03bb7f2a51fdb5f99187"),
    (0x08005B6C, 0x08005BA8, "c6a20896e48a2d20f9a4e9d59b780095f5e082b65619a2a96cee0ebc26e8c475"),
    (0x08005954, 0x08005A22, "4e3fba4f8cb6ee77b2d0251866e2f85338ab5550832ce8fc0807b3835b0c677e"),
    (0x08005BFC, 0x08005C00, "f405d9773c7102b97b617a0b190d7c5a83a856a9a19141afc2d18f8882c1fda0"),
    # Scroll constructor, synchronous child callback, kind-zero provider and both getter calls.
    (0x080D9914, 0x080D993C, "266be9a25fc864057c78fe97921d41f5fdff48468ffd4c78e6ed0daa23753fbd"),
    (0x080D9488, 0x080D9528, "b61d7a09a59fa982143623d8690a4ddb0b2f57ba5789ec3ae660191b289a18ca"),
    (0x0800CE08, 0x0800CF06, "d95443032f3cea8de14c575311dc2e598097ace702a3e60b825b4d6cc9da8273"),
    (0x0800C3CC, 0x0800C4B4, "0de1cf88f1da097ba540acc0061d0f3ef1aa86f0e7ed9b0baa2a4aba876d579d"),
    (0x080D996C, 0x080D997C, "f48f67ef3e814741d428d1a43d38e061ff4de28d29abca6ab5549927765a9f32"),
    (0x0800C614, 0x0800C628, "be9c09e26151bf59569681249059d598963aaba6fc3520290ee1ffce08e7da0e"),
    (0x080D9BA8, 0x080D9BC0, "2b1a38d8134c744bffa1d047086873e2ed111fd35f7296d036e870ca3033fb4b"),
    (0x0800C628, 0x0800C64C, "d203051ca714409914caa0a6a4c5fe2ad714781a843b470b6438a31d54277d55"),
    # Display mask, initial scroll value, ordinary native memcpy, bank copy and lifecycle.
    (0x080035A8, 0x080035D0, "99b9c2aceea23bba27b88e49cff2b608c4513c8c547b757e18fbe5470482063e"),
    (0x080D499C, 0x080D49FC, "b3f51c264d0791fac0eb26e90feb06b0af3ccf3508a14a8c0ae572f6006741ae"),
    (0x081443FC, 0x0814445E, "aa822d873bad381a62e3c3e07b06003a41beea59bc3edc791f7e316eb08b7ebb"),
    (0x0800DE64, 0x0800DE70, "3e46c136cb982053fd4e19c3efcfddf10ff20263616c7c4545815f0e990127d0"),
    (0x0800C4B4, 0x0800C5F4, "c6d6ae60535de05d825bbee9eee235c75d08b321162757be40dcb5fba421c9a4"),
    (0x0800C668, 0x0800C6BE, "fbe0f1d49d066128ecccdfcf2e652a8c8594b43fbeb0380608af23f8fb7f5059"),
    (0x0800C6C0, 0x0800C6CA, "f0ae657c37c9ad0a178f1224db37cdabe0d487231e825815c25e9c4f27e1c770"),
    (0x080D9B64, 0x080D9B98, "67f91d578937823f3e0554a8db635396024a32c064b5cdf3b7be04f8862ff08b"),
)

# Offsets in the genuine ET_REL function. All five ABS32 addends are zero.
CALLS = ((78, 0x080D49FC), (90, 0x080D4B64), (98, 0x080035A8), (114, 0x080D3E9C),
         (138, 0x080E0608), (152, 0x080DFD8C), (186, 0x080E064C), (200, 0x0800BC08),
         (206, 0x080E0690), (218, 0x080D3F08), (256, 0x080D9914), (266, 0x080D499C),
         (276, 0x080D996C), (304, 0x080D9BA8), (322, 0x080D996C), (374, 0x080035A8),
         (398, 0x080D9B64), (412, 0x080D4D2C))
DATA = ((160, "data_088ED8CC", 0x088ED8CC), (168, SYMBOL, SHADOW),
        (172, "data_0894D804", 0x0894D804), (176, "data_08399B2C", 0x08399B2C),
        (392, SYMBOL, SHADOW))


def require(condition, message):
    if not condition:
        raise ValueError("scroll prefix: " + message)


def provider(rom):
    import scheduler_zero_descriptor as installed
    require(rom is not None, "missing original ROM")
    spans = PROVIDER + installed.BOOT + (
        (0x08002768, 0x080027B8, "6e9dc4c6a9f37a50fb532938d3c1d4e5bd2eb08e1e45744ec654f057d08dd718"),
        (installed.IMAGE, installed.IMAGE+176, installed.IMAGE_SHA256),
        (OWNER, END, BODY))
    for start, end, digest in spans:
        require(sha256(rom[start-BASE:end-BASE]).hexdigest() == digest,
                f"changed native provider or owner at {start:08X}")
    # BG3 vertical coordinate is (3 << 1) | 1 = 7. Both eight-word tables
    # are copied to the child's stack. Type zero selects entry zero of the
    # three provider tables. Its count is exactly 320 bytes and pitch is two.
    for address, fmt, words in (
        (0x08149AD4, "<8I", tuple(range(0x04000010, 0x04000020, 2))),
        (0x08149AF4, "<8I", tuple(range(0x0300094A, 0x0300095A, 2))),
        (0x08149806, "<3H", (2, 4, 8)),
        (0x0814980C, "<3I", (0x0800DE65, 0x0800DE71, 0x0800D325)),
        (0x08149818, "<3H", (320, 640, 1280)),
        (0x08149550, "<4H", (0x100, 0x200, 0x400, 0x800)),
        (installed.POINTER, "<I", (installed.DESTINATION | 1,)),
        (0x0814224C, "<H", (0x4710,)), (0x08142250, "<H", (0x4718,))):
        require(rom[address-BASE:address-BASE+struct.calcsize(fmt)] == struct.pack(fmt, *words),
                f"changed scroll callback, heap initializer or table at {address:08X}")


def check_image(image, rom, objects):
    import match
    match.allocated_text_only(image)
    raw, relocs, offset, value, size = library_units.signature(image, OWNER)
    require(len(image["relocations"]) == 1 and
            image["sections"][image["relocations"][0]][7] == image["text_index"], "expected a single .rel.text")
    owner, _ = match.function_record(image, "func_080EF484", OWNER, True)
    require(owner["bind"] == 1 and owner["type"] == 2, "missing public Thumb function")
    require((image["type"], offset, value, size, len(raw)) == (1, 0, 1, END-OWNER, END-OWNER)
            and sha256(raw).hexdigest() == OBJECT, "changed complete native Thumb symbol")
    expected = [(site, 10, f"func_{target:08X}") for site, target in CALLS]
    expected += [(site, 2, name) for site, name, _ in DATA]
    require(relocs == tuple(sorted(expected)), "changed BL or named-data relocations")
    for _, _, name in expected:
        symbols = [s for s in image["symbols"] if s["name"] == name]
        require(len(symbols) == 1 and tuple(symbols[0][key] for key in
                ("section", "value", "size", "type", "bind")) == (0, 0, 0, 0, 1),
                "expected genuine undefined external " + name)
    for site, name, address in DATA:
        require(objects.get(name) == address and struct.unpack_from("<I", raw, site)[0] == 0 and
                struct.unpack_from("<I", rom, OWNER-BASE+site)[0] == address, "changed literal " + name)


def check_placement(scene, task, child, scan, payload, descriptor):
    """Physical witnesses for the two successful allocations under the scene arena split."""
    require(all(type(i) is int and i % 4 == 0 for i in (scene, task, child, scan, payload, descriptor)),
            "expected word-aligned physical allocations")
    # 080D36B0 requests 0xA000 from the 080227E8 EWRAM heap, and makes
    # independent heaps in its first 0x6000 bytes and its final 0x4000 bytes.
    require(0x020159D0 <= scene and scene+0xA000 <= 0x02040000, "invalid EWRAM scene allocation")
    require(scene+20 <= scan and scan+1000 <= scene+0x6000 and payload == scan+32,
            "payload must follow the graphics heap scanline header")
    upper = scene+0x6000
    # All three public pointers follow 12-byte allocator headers. The owner
    # and child each have 24 bytes of scheduler header before their own state.
    require(upper+20 <= task and task+24+36 <= scene+0xA000 and
            upper+20 <= child and child+24+12 <= scene+0xA000 and
            (task+60 <= child-12 or child+36 <= task-12), "overlapping or out-of-arena scheduler owners")
    # Both phase-zero and recurring descriptors are private 28-byte stack
    # objects. The first six fields occupy bytes [0,24); stores use [0,2).
    require((0x02000000 <= descriptor and descriptor+28 <= 0x02040000 or
             0x03000000 <= descriptor and descriptor+28 <= 0x03008000) and
            all(descriptor+28 <= start or end <= descriptor for start, end in
                ((scene, scene+0xA000), (SHADOW, SHADOW+80))), "aliased or invalid scheduler descriptor")
    # [scan+32,+352) is the application array. [scan+352,+676) and
    # [scan+676,+1000) are the two physical banks, each rounded from 322 bytes.
    return (payload, payload+320), (scan+352, scan+676), (scan+676, scan+1000)


def finite_backedge(assembly):
    # This is a proof about the linked owner with checked ET_REL origins, not
    # a configurable loop bound. The first 160-row fill stays in the normal
    # executor. In the second loop r3 is the exclusive 320-byte payload, r5
    # the owner's 36-byte state in the other heap, r2 the unsigned row.
    functions, _ = vs.parse_assembly(assembly)
    require(set(functions) == {"func_080EF484"}, "unexpected compilation unit")
    code, labels, _ = functions["func_080EF484"]
    expected = (
        "ldr r0, [r5, #28]|bl func_080D996C|add r3, r0, #0|mov r2, #0|"
        "ldrh r1, [r5, #4]|cmp r2, r1|bcs .L18|"
        "lsl r0, r2, #1|add r0, r0, r3|ldrh r1, [r0]|add r1, r1, #2|strh r1, [r0]|"
        "add r0, r2, #1|lsl r0, r0, #16|lsr r2, r0, #16|ldrh r0, [r5, #4]|cmp r2, r0|bcc .L20|"
        "ldrh r0, [r5, #4]|add r0, r0, #2|strh r0, [r5, #4]|lsl r0, r0, #16|"
        "lsr r0, r0, #16|cmp r0, #72|bls .L3")
    # The only transition from 100 seeds 86. On the 86th predecrement
    # the 160-row fill saves that exact task, seeds zero and advances to 102.
    def block(label, stop):
        return [" ".join((op, ", ".join(args))).strip() for op, args, _ in code[labels[label]:labels[stop]]]
    require(block(".L6", ".L9")[-5:] == ["mov r0, #86", "strh r0, [r5, #4]", "ldrh r0, [r7]",
            "add r0, r0, #1", "b .L29"], "changed phase 100 entry counter")
    before_fill = block(".L9", ".L14")
    require(before_fill[:6] == ["ldrh r0, [r5, #4]", "sub r0, r0, #1", "strh r0, [r5, #4]",
            "lsl r0, r0, #16", "cmp r0, #0", "bne .L3"] and before_fill[-4:] == [
            "add r0, r4, #0", "bl func_080D996C", "add r2, r0, #0", "mov r1, #0"],
            "changed countdown or initial fill origin")
    require(block(".L14", ".L16") == ("lsl r0, r1, #1|add r0, r0, r2|strh r6, [r0]|"
            "add r0, r1, #1|lsl r0, r0, #16|lsr r1, r0, #16|cmp r1, #159|bls .L14|"
            "add r0, r4, #0|mov r1, #1|bl func_080D9BA8|str r4, [r5, #28]|mov r0, #0|"
            "strh r0, [r5, #4]|ldrh r0, [r7]|add r0, r0, #1|b .L29").split("|"), "changed fill or saved handle")
    start = labels[".L16"]
    require(labels[".L20"] == start+7 and labels[".L18"] == start+18, "changed native prefix labels")
    actual = [" ".join((op, ", ".join(args))).strip() for op, args, _ in code[start:start+25]]
    require(actual == expected.split("|"), "changed column, counter reload, width or exit")
    # No extra entry can bypass row-zero setup or enter the interior of the loop.
    for pc, (op, args, _) in enumerate(code):
        if op.startswith("b") and args and args[0] in labels and start < labels[args[0]] < start+18:
            require(pc == start+17 and labels[args[0]] == start+7, "unreviewed loop entry")
    require(block(".L18", ".L23")[-8:] == ["bl func_080035A8", "ldr r2, .L32", "ldrh r1, [r2]",
            "bic r1, r1, r0", "strh r1, [r2]", "ldrh r0, [r7]", "add r0, r0, #1", "b .L29"] and
            code[labels[".L29"]][2].split() == ["strh", "r0,", "[r7]"], "changed shadow or terminal advance")
    # Native objects and actual operations coincide for all three variants.
    # If the bound is nonzero, row 0 is executed here. Every later row repeats
    # exactly these same unsigned-halfword memory events at payload+2*i;
    # its store cannot modify the reloaded separate state or a pinned member.
    # r0/r1 and flags are overwritten on exit; r2/r3 have no later use.
    new, count = re.subn(r"(?m)^([ \t]*bcc[ \t]+)\.L20([ \t]+@cond_branch)$", r"\g<1>.L18\2", assembly)
    require(count == 1, "ambiguous native loop backedge")
    return new


def record(assemblies, images, preprocessed, entry, interfaces, rom, objects):
    require(entry["symbol"] == SYMBOL and objects.get(SYMBOL) == SHADOW, "unexpected control object")
    provider(rom)
    require(len(images) == len(assemblies) == 3, "three independent compiler variants required")
    for image in images:
        check_image(image, rom, objects)
    cuts = [finite_backedge(assembly) for assembly in assemblies]
    normal = vs.compare(cuts[0], cuts[1], preprocessed, SYMBOL, entry["declaration"], cuts[2], interfaces)
    return (vs.record(SYMBOL, normal, perturbed=True) +
            ". BG3 scroll prefix: native original/stripped/layout-perturbed objects and all 23 relocations agree. "
            "080EFC34 schedules 36 bytes; 080D9914 creates a separate 12-byte child; "
            "080D9488/0800CE08 allocate 320 ordinary row bytes and two 324-byte banks in the disjoint "
            "0x6000 graphics arena, outside the 0x4000 scheduler arena and 03000940 control block. "
            "Phase 101 fills 160 rows, resets the counter to zero and saves the live child; "
            "phase 102 adds two to prefixes 0,2,...,72, then enters 103 at 74. "
            "Owner display accesses are 16-bit OR/BIC of 0x0800 at offset zero. "
            "080D499C reads the BG offsets; the child uses BG3VOFS shadow 03000958 and DMA destination 0400001E. "
            "Requires initialized installed clear, healthy exclusive heaps, successful allocations and a free slot, "
            "normal scheduler entry, private 28-byte scheduler descriptors disjoint from control and both heaps, and no competing mutation or teardown.")


def report_body(report, root):
    from match_evidence import report_rom_path
    rom = Path(report_rom_path(root)).read_bytes()
    provider(rom)
    body = rom[OWNER-BASE:END-BASE].hex()
    lines = report.splitlines()
    expected = ((r"^\* verification:", "* verification: `elf-symbol-thumb-frame-data-v1`"),
                (r"^\* ROM bytes:", f"* ROM bytes: `{body}` (436 bytes)"),
                (r"^\* compiled\s*:", f"* compiled : `{body}`"),
                (r"^\*\*MATCH", "**MATCH - byte identical** - 436/436 bytes"))
    return all([s for s in lines if re.match(prefix, s.lstrip())] == [value] for prefix, value in expected)
