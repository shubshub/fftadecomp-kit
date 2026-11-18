"""The two selector tables of the runner callback installed in slot 2 at 08031FE6."""
import json
import struct
from pathlib import Path

import menu_selection_switches as selection
import multiple_switch_native_profile as multiple

BASE = 0x08000000
OWNER = 0x08034E88
STATE = 0x03002810
STATE_NAME = 'g_state_03002810'
RUNNER = 0x03002720
FIRST = {1: 0x08043468, 3: 0x0803AE80, 4: 0x0803BAE8, 5: 0x08039424, 6: 0x0803A07C,
         7: 0x0803E3B4, 8: 0x08046A4C, 9: 0x0803D550, 10: 0x0803DC1C, 11: 0x0803DE40}
SECOND = {2: 0x0804393C, 13: 0x0803C21C, 14: 0x0803CA18, 15: 0x0803F6F8,
          16: 0x08049FB4, 17: 0x0804AFE0, 19: 0x0803D820}
INITIAL = 0x08034C94
TAIL = 0x0804B7E8


def require(condition, message):
    if not condition:
        raise ValueError('menu runner switches: ' + message)


def environment_fingerprint():
    import switch_constants_profile as constants
    pins = selection.environment_fingerprint()
    for path in (Path(__file__), Path(selection.__file__), Path(constants.__file__)):
        pins['producers'][path.name] = selection.digest(path.read_bytes())
    return pins


def registration(rom):
    seq = selection.sequence
    seq(rom, 0x080317D2, 12, ['ldr r0, [pc, #0x3c]', 'ldr r1, [pc, #0x3c]', 'ldr r2, [pc, #0x40]',
                              'movs r3, #5', 'bl #0x8006a7c'])
    seq(rom, 0x08031FDE, 12, ['ldr r4, [pc, #0x38]', 'ldr r2, [pc, #0x60]', 'adds r0, r4, #0',
                               'movs r1, #2', 'bl #0x8006adc'])
    seq(rom, 0x08031870, 8, ['ldr r0, [pc, #0x10]', 'movs r1, #5', 'bl #0x80069f4'])
    require(rom[0x14224c:0x14224e] == bytes.fromhex('1047'), 'original indirect-call veneer is not BX r2')
    arrays = struct.unpack_from('<III', rom, 0x31810)
    require(arrays == (RUNNER, 0x030009B0, 0x03000EC8) and
            all(struct.unpack_from('<I', rom, off)[0] == RUNNER for off in (0x32018, 0x31884)) and
            struct.unpack_from('<I', rom, 0x32044)[0] == (OWNER | 1), 'wrong runner, callback pointer or backing arrays')
    # Original initializer, setter (through BX r0), and both dispatch paths including the R2 thunk calls.
    for start, length, digest in (
        (0x08006A7C, 60, '877bd60e35bf7d06ab032e5c96a33ebdb416480ba6ede87050d91f229136bb03'),
        (0x08006ADC, 28, 'adfcb3744861f340a5e92fd533d4d2906eae4c1878541e53f574283adcc0814e'),
        (0x080069F4, 136, '870059083b005c705d9ed3a284ac753f0cb32cb52f1110640bd37b4b31d8e726')):
        require(selection.digest(rom[start-BASE:start-BASE+length]) == digest, 'original table access or runner ABI changed')
    return dict(runner=RUNNER, count=5, slot=2, words=arrays[1], flags=arrays[2], registration_call=0x08031FE6,
                callback_pointer=OWNER | 1, dispatcher_call=0x08031874, callback_args=[2, arrays[2]+2])


def selector_calls(rom, switches):
    seq = selection.sequence
    seq(rom, OWNER, 24, ['push {lr}', 'bl #0x8034c94', 'ldr r0, [pc, #0x1c]', 'ldr r0, [r0]', 'movs r1, #0x97',
                         'lsls r1, r1, #3', 'adds r0, r0, r1', 'ldrb r0, [r0]', 'subs r0, #1', 'cmp r0, #0xa',
                         'bhi #0x8034f2e'])
    seq(rom, 0x08034F2E, 16, ['ldr r0, [pc, #0x18]', 'ldr r0, [r0]', 'ldr r1, [pc, #0x18]', 'adds r0, r0, r1',
                               'ldrb r0, [r0]', 'subs r0, #2', 'cmp r0, #0x11', 'bhi #0x8034fd2'])
    seq(rom, 0x08034FD2, 24, ['ldr r0, [pc, #0x18]', 'ldr r0, [r0]', 'ldr r1, [pc, #0x18]', 'adds r0, r0, r1',
                               'ldrb r0, [r0]', 'cmp r0, #0x14', 'bne #0x8034fe6', 'movs r0, #2', 'bl #0x804b7e8',
                               'pop {r0}', 'bx r0'])
    expected = {OWNER+2: INITIAL, 0x08034FE2: TAIL}
    for idx, (switch, low, cases) in enumerate(zip(switches, (1, 2), (FIRST, SECOND))):
        for value, (_, dest) in enumerate(switch['relocations'][1:], low):
            if value not in cases:
                require(dest == switch['default'], 'unmapped selection does not go to next field')
                continue
            start = OWNER+dest
            seq(rom, start, 6, [f'movs r0, #{idx}', f'bl #0x{cases[value]:x}'])
            if dest+6 != switch['default']:
                seq(rom, start+6, 2, [f"b #0x{OWNER+switch['default']:x}"])
            expected[start+2] = cases[value]
    return dict(sorted(expected.items()))


def verify_original(raw_object, linked_file, address, rom, mapping, index, reported_bindings, manifest=None, *, objects):
    import analyze
    import framed_switch_inventory as ordinary
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
            'requires the original and linked ELF, ROM and both owner maps for 08034E88')
    original, linked = match.elf_image(raw_object), match.elf_image(linked_file)
    require(original['type'] == 1 and linked['type'] == 2 and not linked['relocations'], 'wrong ELF types or retained relocations')
    for image in (original, linked):
        match.allocated_text_only(image)
        func, offset = match.function_record(image, 'func_08034E88', address, True)
        require(offset == 0 and func['size'] == len(image['text']) == 364, 'wrong complete Thumb symbol')
    body = linked['text']
    owner.validate_span(body, address, rom, mapping, index)
    require(selection.digest(body) == '4103982c03be90373bf473d05c3222b3d36ffd978036d8be82fa80e61e053ea1', 'changed original runner body')
    bindings, targets = owner.original_bindings(original, address, rom, mapping, objects, selector=multiple.SELECTOR, index=index)
    require(bindings == reported_bindings and not bindings['functions'] and
            bindings['data'] == [[off, STATE_NAME, 0] for off in (0x24, 0xc0, 0x164)] and
            targets.get(STATE_NAME) == (STATE, True), 'wrong call/table/object bindings')
    for name in targets:
        sym, = (s for s in original['symbols'] if s['name'] == name)
        require((sym['bind'], sym['type'], sym['size'], sym['section'], sym['value']) == (1, 0, 0, 0, 0),
                'expected unique original zero-sized undefined symbol')
    typed.check_linked(linked, address, targets)
    layouts = dict(one_object_word_switch=True, two_constant_word_switch=True)
    refined = analyze.refine_function(body, address, json.loads(mapping), max_bytes=len(body), max_instructions=len(body)//2,
                                      rom_end=BASE+len(rom), same_owner_long_branches=True, **layouts)
    ins, edges, branches, calls, words = graph.graph(body, address, refined, **layouts)
    switches = refined['word_switches']
    require(not branches and [(s['bound'], s['interposed_words'], s['literal'], s['table'], s['default']) for s in switches] ==
            [(10, 1, 0x28, 0x2c, 0xa6), (17, 2, 0xc8, 0xcc, 0x14a)] and
            [[off, val] for off, val in sorted(words.items())] == bindings['switches'] and len(words) == 31,
            'guarded table slots differ from the original 31 local relocations')
    for switch in switches:
        guard_predecessors(ins, edges, address, switch)
    require(all(dst > src for src, dests in edges.items() for dst in dests), 'unexpected backward edge')
    require(calls == selector_calls(rom, switches) and len(calls) == 19, 'unexpected case target or call')
    bound_calls = ordinary.bind_calls(calls, mapping, address, len(body), len(rom))
    require(bindings['calls'] == [[pc-address, name] for pc, name in sorted(bound_calls.items())], 'call relocation sites or names changed')
    relocated = bytearray(original['text'])
    for off, _ in bindings['calls']:
        require(relocated[off:off+4] == bytes.fromhex('fff7feff'), 'nonzero original BL addend')
        relocated[off:off+4] = body[off:off+4]
    for off, _, _ in bindings['data']:
        struct.pack_into('<I', relocated, off, STATE)
    for off, value in words.items():
        struct.pack_into('<I', relocated, off, address+value)
    require(bytes(relocated) == body, 'linked body differs outside the 53 verified relocations')
    partition = graph.partition(body, address, refined, ins, words)
    literals = [(w['address']-address, w['value'], [p-address for p in w['load_sites']])
                for w in partition['words'] if not w['switch_word']]
    require(literals == [(0x24, STATE, [6]), (0xc0, STATE, [0xa6]), (0xc4, 0x4b9, [0xaa]),
                         (0x164, STATE, [0x14a]), (0x168, 0x4ba, [0x14e])], 'unexpected state or numeric pool load')
    operations.verify_operations(ins, edges, address, branches, calls, refined)
    restored = frame.prove_frame(ins, edges, address, {}, calls)
    entries, rows = indices(mapping, index)
    require(span_record(address, address+len(body), entries, rows, rom)['instrs'] == len(ins) == 89, 'wrong dual-map count')
    by_address = {int(e['rom'], 16): int(e['end'], 16) for e in entries}
    for target in calls.values():
        span_record(target, by_address[target], entries, rows, rom)
    for start, end, count in ((0x0803172C, 0x080318D0, 154), (0x0803197C, 0x08034C94, 4869),
                              (0x08006ADC, 0x08006AF8, 14), (0x08006A7C, 0x08006AB8, 30),
                              (0x080069F4, 0x08006A7C, 66), (0x0814224C, 0x0814224E, 1)):
        require(span_record(start, end, entries, rows, rom)['instrs'] == count, 'runner provider dual-map count changed')
    result = dict(profile=multiple.SCHEMA, selector=multiple.SELECTOR, environment=pins, bindings=bindings,
                  original_ELF_sha256=selection.digest(raw_object), linked_ELF_sha256=selection.digest(linked_file),
                  ROM_sha256=selection.digest(rom), data_mapping_sha256=selection.digest(objects), instructions=len(ins),
                  switches=switches, partition=partition, frame=restored, registration=registration(rom),
                  selector_offsets=[0x4b8, 0x4b9, 0x4ba], tail_value=20,
                  contract='Ordinary calls may change the state pointer and its contents. After each phase the pointer '
                           'must identify readable storage at the next byte offset. Returning ordinary calls preserve '
                           'the callee-saved registers and SP; their game effects and termination are conditional.')
    require(environment_fingerprint() == pins, 'native producer or toolchain changed')
    if manifest is not None:
        require(owner.text(manifest) == owner.text(result), 'manifest differs from fresh native evidence')
    return result, len(ins)
