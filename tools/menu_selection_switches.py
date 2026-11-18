"""Native proof for the two guarded tables and ROM halfword lookup at 0804E224."""
import hashlib
import json
import struct
from pathlib import Path

from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
import multiple_switch_native_profile as multiple

BASE = 0x08000000
OWNER = 0x0804E224
GETTER = 0x08005BFC
IDS = 0x08529EE4
CALL_SITES = (0x0804CD0E, 0x0804CD74, 0x0804CE62, 0x0804CF7E, 0x0804D284, 0x0804D4AE)


def require(condition, message):
    if not condition:
        raise ValueError("menu selection switches: " + message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def environment_fingerprint():
    import small_local_copy_binding_profile as typed
    value = multiple.environment_fingerprint()
    for path in (Path(__file__), Path(typed.__file__)):
        value['producers'][path.name] = digest(path.read_bytes())
    return value


def sequence(rom, start, size, expected):
    code = rom[start-BASE:start-BASE+size]
    ins = list(Cs(CS_ARCH_ARM, CS_MODE_THUMB).disasm(code, start))
    require(sum(i.size for i in ins) == size and [i.mnemonic + ' ' + i.op_str for i in ins] == expected,
            f"original code differs at {start:08X}")


def context(rom):
    sequence(rom, GETTER, 4, ["adds r0, #0x18", "bx lr"])
    sequence(rom, 0x080CED2C, 6, ["movs r0, #0x96", "lsls r0, r0, #1", "bx lr"])
    ids = struct.unpack_from('<301H', rom, IDS-BASE)
    require(0xffff not in ids[:-1] and ids[-1] == 0xffff, "expected 300 ROM IDs then the sentinel")
    # This separate original consumer walks the same halfwords until 0xffff.
    sequence(rom, 0x080CE8AC, 14, ["ldr r2, [pc, #0x40]", "ldrh r0, [r2]", "ldr r1, [pc, #0x40]",
            "cmp r0, r1", "beq #0x80ce8d6", "adds r6, r1, #0", "adds r4, r2, #0"])
    sequence(rom, 0x080CE8BA, 28, ["ldr r1, [pc, #0x3c]", "adds r0, r0, r1", "lsls r0, r0, #0x10",
            "lsrs r0, r0, #0x10", "bl #0x80c9540", "lsls r0, r0, #0x18", "cmp r0, #0",
            "beq #0x80ce8ce", "adds r5, #1", "adds r4, #2", "ldrh r0, [r4]", "cmp r0, r6", "bne #0x80ce8ba"])
    require(struct.unpack_from('<II', rom, 0xce8f0) == (IDS, 0xffff), "ID walker table or sentinel changed")
    for site in CALL_SITES:
        field = 0x1c if site == CALL_SITES[0] else 0x20
        sequence(rom, site-4, 8, ["ldr r0, [r5]", f"ldr r0, [r0, #0x{field:x}]", f"bl #0x{OWNER:x}"])
        if site == CALL_SITES[0]:
            sequence(rom, site+4, 8, ["lsls r0, r0, #0x10", "asrs r0, r0, #0x10", "bl #0x804d6b0"])
        else:
            sequence(rom, site+4, 4, ["bl #0x804e9c4"])
    # Dispatch state 2 is an actual path through the original menu. It asks
    # the task for its signed selection; zero goes to the caller's common exit.
    sequence(rom, 0x0804CBB4, 30, [
        "push {r4, r5, r6, lr}", "sub sp, #0x18", "ldr r1, [pc, #0x18]", "ldr r0, [r1]",
        "ldrh r0, [r0, #8]", "adds r5, r1, #0", "cmp r0, #0x1a", "bls #0x804cbc8",
        "bl #0x804d59c", "lsls r0, r0, #2", "ldr r1, [pc, #0xc]", "adds r0, r0, r1", "ldr r0, [r0]", "mov pc, r0"])
    require(struct.unpack_from('<II', rom, 0x4CBD4) == (0x0201F544, 0x0804CBDC) and
            struct.unpack_from('<I', rom, 0x4CBDC+2*4)[0] == 0x0804CCF8, "caller dispatch slot changed")
    sequence(rom, 0x0804CCF8, 18, ["ldr r0, [r5]", "ldr r0, [r0, #0x1c]", "bl #0x804e1e0",
             "lsls r0, r0, #0x10", "cmp r0, #0", "bne #0x804cd0a", "bl #0x804d59c"])
    sequence(rom, 0x0804E1E0, 14, ["push {lr}", "bl #0x8005bfc", "movs r1, #6", "ldrsh r0, [r0, r1]",
                                     "pop {r1}", "bx r1"])
    sequence(rom, 0x0804D59C, 16, ["movs r0, #0", "bl #0x804e1b8", "movs r0, #0", "add sp, #0x18",
                                     "pop {r4, r5, r6}", "pop {r1}", "bx r1"])
    sequence(rom, 0x0804E9C4, 8, ["ldr r1, [pc, #4]", "ldr r1, [r1]", "str r0, [r1, #0x10]", "bx lr"])
    require(struct.unpack_from('<I', rom, 0x4e9cc)[0] == 0x0201F548, "full-word result consumer changed")
    return dict(task_payload_offset=24, known_calls=list(CALL_SITES), known_caller_state=2,
                selection_halfword_offset=6, first_result_sign_extended_bits=16, later_results_stored_bits=32,
                id_sentinel_walker=0x080ce8a8,
                caller_nonzero_check=0x0804CD04, id_table=IDS, id_count=300, terminator=0xffff,
                id_bytes_sha256=digest(rom[IDS-BASE:IDS-BASE+602]))


def lookup_semantics(rom, switches):
    """Bind signed index formation, load widths, physical strides and the ID-to-result mapping."""
    sequence(rom, OWNER+6, 14, ["adds r2, r0, #0", "ldrh r0, [r2, #6]", "subs r0, #1",
        "lsls r0, r0, #0x10", "lsrs r3, r0, #0x10", "ldrb r0, [r2, #8]", "subs r0, #1"])
    sequence(rom, OWNER+0x48, 16, ["movs r0, #6", "ldrsh r1, [r2, r0]", "movs r0, #1",
        "rsbs r0, r0, #0", "cmp r1, r0", "bne #0x804e27c", "adds r0, r1, #0", "b #0x804e352"])
    outer, inner = switches
    require([dest for _, dest in outer['relocations'][1:]] ==
            [0x48, 0x12c, 0x108, 0x108, 0xf2, 0x108, 0x12c, 0x11c], "incorrect menu type destinations")
    answers = {0x3b: 1, 0x3c: 2, 0x3d: 3, 0x3e: 4, 0x3f: 6, 0x4f: 5}
    for item, (_, dest) in enumerate(inner['relocations'][1:], 0x3b):
        if item in answers:
            sequence(rom, OWNER+dest, 4, [f"movs r0, #{answers[item]}", "b #0x804e352"])
        else:
            require(dest == inner['default'] == 0xec, "incorrect unmapped ID destination")
    sequence(rom, OWNER+0xec, 6, ["movs r0, #1", "rsbs r0, r0, #0", "b #0x804e352"])
    for offset, pool, operation in ((0x58, 0x18, "ldr"), (0xf2, 8, "ldrh"), (0x108, 8, "ldr")):
        sequence(rom, OWNER+offset, 14, ["ldr r0, [r2]", "lsls r1, r3, #0x10", "asrs r1, r1, #0xe",
            "ldr r2, [pc, #0x18]" if pool == 0x18 else "ldr r2, [pc, #8]",
            "adds r0, r0, r2", "adds r0, r0, r1", f"{operation} r0, [r0]"])
    sequence(rom, OWNER+0x66, 4, ["subs r0, #0x3b", "cmp r0, #0x14"])
    sequence(rom, OWNER+0x11c, 12, ["ldr r0, [pc, #8]", "lsls r1, r3, #0x10", "asrs r1, r1, #0xf",
        "adds r1, r1, r0", "ldrh r0, [r1]", "b #0x804e352"])
    sequence(rom, OWNER+0x12c, 6, ["movs r0, #0", "pop {r1}", "bx r1"])
    return dict(selection_bits=16, signed_index_bits=16, ram_stride=4, rom_stride=2,
                word_bank=0x424, secondary_id_bank=0x524,
                secondary_answers=[[item, value] for item, value in answers.items()])


def verify_original(raw_object, linked_file, address, rom, mapping, index, reported_bindings, manifest=None, *, objects):
    import addressed_signed_runtime_profile as alignment
    import analyze
    import local_long_branch_profile as frame
    import match
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    import owner_runtime_profile as operations
    import small_local_copy_binding_profile as typed
    from one_constant_scalar_switch_inventory import guard_predecessors
    from software_double_profile import indices, span_record

    pins = environment_fingerprint()
    require(address == OWNER and all(type(x) is bytes for x in (raw_object, linked_file, rom, mapping, index, objects)),
            "requires the fixed owner and immutable actual ELF, ROM and both maps")
    original, linked = match.elf_image(raw_object), match.elf_image(linked_file)
    require(original['type'] == 1 and linked['type'] == 2 and not linked['relocations'], "wrong ELF types or retained relocations")
    actual_bindings, targets = owner.original_bindings(original, OWNER, rom, mapping, objects, selector=multiple.SELECTOR, index=index)
    require(actual_bindings == reported_bindings and actual_bindings['calls'] == [[2, 'func_08005BFC']] and
            actual_bindings['data'] == [[0x128, 'g_table_08529EE4', 0]] and not actual_bindings['functions'] and
            targets == {'func_08005BFC': (GETTER, False), 'g_table_08529EE4': (IDS, True)},
            "unexpected original call, object or per-site binding")
    for name in targets:
        symbol, = (s for s in original['symbols'] if s['name'] == name)
        require((symbol['bind'], symbol['type'], symbol['size'], symbol['section'], symbol['value']) == (1, 0, 0, 0, 0),
                "expected genuine zero-sized undefined symbol")
    for image in (original, linked):
        match.allocated_text_only(image)
        symbol, offset = match.function_record(image, 'func_0804E224', address, True)
        require(not offset and symbol['size'] == 306, "wrong complete function extent")
        require(image['text'][306:] == bytes.fromhex('c046'), "missing canonical external Thumb alignment")
        alignment.terminal_alignment(image, symbol)
    typed.check_linked(linked, address, targets)
    body = linked['text'][:306]
    owner.validate_span(body, address, rom, mapping, index)
    require(digest(body) == '5bd17d96d8311a8c7a65b745f0a3d543a11d2760c78ba2036f80580412aa825d',
            "original field loads, signed indexing, dispatch results or frame changed")
    # Check the full relation between ET_REL and the linked .text, including
    # the assembler's external alignment. None of the case words may be ABS.
    relocated = bytearray(original['text'])
    require(relocated[2:6] == bytes.fromhex('fff7feff') and relocated[0x128:0x12c] == bytes(4),
            "call or ROM-ID relocation has a nonzero original addend")
    relocated[2:6] = body[2:6]
    struct.pack_into('<I', relocated, 0x128, IDS)
    for site, addend in actual_bindings['switches']:
        struct.pack_into('<I', relocated, site, address+addend)
    require(relocated == linked['text'], "linked instructions or data differ outside typed relocations")

    refinement = analyze.refine_function(body, address, json.loads(mapping), max_bytes=len(body), max_instructions=153,
        rom_end=BASE+len(rom), same_owner_long_branches=True, one_numeric_word_switch=True)
    ins, edges, branches, calls, words = graph.graph(body, address, refinement, one_numeric_word_switch=True)
    switches = refinement['word_switches']
    require(not branches and calls == {address+2: GETTER} and
            [(s['bound'], s.get('interposed_words', 0), s['literal'], s['table']) for s in switches] ==
            [(7, 0, 0x24, 0x28), (20, 1, 0x7c, 0x80)] and
            [[site, delta] for site, delta in sorted(words.items())] == actual_bindings['switches'] and len(words) == 31,
            "both guarded local tables must own every original section relocation")
    for switch in switches:
        guard_predecessors(ins, edges, address, switch)
    require(all(dst > src for src, successors in edges.items() for dst in successors), "back edge in menu query")
    partition = graph.partition(body, address, refinement, ins, words)
    scalars = [(word['address']-address, word['value'], [site-address for site in word['load_sites']])
               for word in partition['words'] if not word['switch_word']]
    require(scalars == [(0x78, 0x524, [0x5e]), (0x104, 0x424, [0xf8]), (0x118, 0x424, [0x10e]), (0x128, IDS, [0x11c])],
            "wrong named ID-table load or scalar data-bank offsets")
    operations.verify_operations(ins, edges, address, branches, calls, refinement)
    restored = frame.prove_frame(ins, edges, address, {}, calls)
    indexed, rows = indices(mapping, index)
    for start, size, count in ((address, 306, 80), (GETTER, 4, 2)):
        require(span_record(start, start+size, indexed, rows, rom)['instrs'] == count, "wrong dual-index extent or count")
    result = dict(profile=multiple.SCHEMA, selector=multiple.SELECTOR, bindings=actual_bindings,
        environment=pins, original_ELF_sha256=digest(raw_object), linked_ELF_sha256=digest(linked_file),
        ROM_sha256=digest(rom), data_mapping_sha256=digest(objects), instructions=len(ins),
        switches=switches, partition=partition, frame=restored, selection=context(rom),
        lookup=lookup_semantics(rom, switches),
        contract="The queried task and payload must be live and readable. Selection is a signed 16-bit "
            "one-based index and subtraction wraps to 16 bits on this target. Type 1 handles -1 before reading "
            "a secondary ID. Other type-1 selections need a readable backing secondary-ID entry. Types 3/4/5/6 "
            "need a valid entry in the 64-word bank. Type 8 needs a valid ROM ID (1 through 300); index 301 "
            "reads the sentinel and zero reads the preceding ROM halfword. A zero selection on type 5 reads "
            "before the entry bank. No universal input bounds are inferred from the callers.")
    require(environment_fingerprint() == pins, "native verifier or toolchain changed")
    if manifest is not None:
        require(owner.text(manifest) == owner.text(result), "menu-query manifest differs from fresh native evidence")
    return result, len(ins)
