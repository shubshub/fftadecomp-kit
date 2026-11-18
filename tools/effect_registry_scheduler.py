"""Per-site scheduler contract for the two immutable effect registries in the USA ROM."""
from copy import copy
from hashlib import sha256
from pathlib import Path
import struct

import match
import scheduler_call_site_profile as sites
import software_double_profile as spans

SELECTOR = 'conditional-effect-registry-scheduler-v1'
SCHEMA = 'elf-symbol-thumb-' + SELECTOR
OWNER, CREATE = 0x080D3508, 0x080D35AC
PRIMARY, EXTENDED, NEXT_TABLE = 0x083947D8, 0x08395280, 0x08395320
SPECIAL_ID, SPECIAL, EMPTY_ID = 0x159, 0x080E2398, 0xDB
TABLES = (
    (PRIMARY, EXTENDED, 1, 341, '8445ca358c2b5641c76840487888878690ad49f069fc945cefa35507f2b8feda'),
    (EXTENDED, NEXT_TABLE, 0x156, 20, '7d33b2a5ad66f2f46c63c46edef262ad7d4402387f1d6f833b38054e2679f45b'),
)
CALLS = {OWNER+34: 0x080D3B98, OWNER+50: 0x080D3B38, OWNER+114: 0x080D3B98, CREATE: sites.DIRECT}
BINDINGS = dict(calls=[[pc-OWNER, f'func_{target:08X}'] for pc, target in CALLS.items()],
                data=[[84, 'data_083947D8', 0], [180, 'data_08395280', 0],
                      [192, 'data_083947D8', 0], [200, 'data_0200F430', 0], [204, 'data_020159C0', 0]],
                functions=[[196, 'func_080E2398']], switches=[])
HELPERS = {
    0x080D3B98: (54, 'ad6d2e9fc0edf6f58dac07a50a993006deb1922969d32f3ccfcb093a4d574a7a'),
    0x080D3B38: (26, '569c49d911d8aa30f1aea0bdc131501b414ea110b7c55863f9ffc98fd40f57b4'),
    0x080A880C: (2, 'c7dfbb7d02759eacb64dbc916c1bb6f21eabaff1c1032ea5c9176abf7fd28df8'),
    0x080DD478: (4, 'a89b85f8bccd76763270edbe8d4a9000e557118189ef0a663b750b93593d16da'),
    0x080DD47C: (12, 'b38cf61085345953bac6fd7d2315a3df4b25880c25ff8533b8f623b2730bf8f0'),
    0x080C8384: (32, '094507d23c98de23e13cd1d53e4314319e136e685ab7fb775063cb8bbabec802'),
    # A different starter addresses NEXT_TABLE with id - 0x16B.
    0x080D3818: (76, 'c2e5c83c105f598aae186b4038d4c29613896d1d2c1375a2fc1fc387fbf58493'),
}
OWNER_HASH = 'f5d37bec0341368abf3dd018b4c5835c8427d973a87051b764bfbaecface5062'
require = sites.require


def registry_tables(proof):
    names = match.parse_data_symbols(proof.objects)
    for address in (PRIMARY, EXTENDED, NEXT_TABLE):
        require(names.get(f'data_{address:08X}') == address, 'wrong named registry boundary')
    entries, rows = spans.indices(proof.mapping, proof.index)
    ends = {int(row['rom'], 16): int(row['end'], 16) for row in entries}
    summaries, callbacks = [], set()
    for begin, end, first, count, digest in TABLES:
        data = proof.rom[begin-match.ROM_BASE:end-match.ROM_BASE]
        require(len(data) == count * 8 and sha256(data).hexdigest() == digest,
                'effect registry contents or boundary changed')
        members = set()
        for index, (pointer, size, tag) in enumerate(struct.iter_unpack('<IHH', data), first):
            if index == EMPTY_ID:
                require((pointer, size, tag) == (0, 0, 0), 'reserved empty primary entry changed')
            else:
                require(pointer & 1 and pointer-1 in ends and 0 < size <= 0xffff-28,
                        'effect row requires a nonnull indexed Thumb callback and bounded allocation size')
                members.add(pointer-1)
            if index == SPECIAL_ID:
                require((pointer, size) == (SPECIAL | 1, 40), 'special registry record differs from override')
        callbacks.update(members)
        summaries.append(dict(start=begin, end=end, sha256=digest, first_id=first, entries=count,
                              stride=8, unique_callback_entries=len(members)))
    # Check callback entry ownership in both indexes. This does not certify any callback's effects.
    for callback in sorted(callbacks):
        spans.span_record(callback, ends[callback], entries, rows, proof.rom)
    return summaries


def bind(proof, data, address, ins, edges, calls):
    import scheduler_event_definition as event
    require(address == OWNER and len(data) == 208 and len(ins) == 81 and calls == CALLS and
            sha256(data).hexdigest() == OWNER_HASH and [a for a in ins if not edges[a]] == [OWNER+176],
            'expected the complete original USA registry task starter and its four calls')
    for target, (length, digest) in HELPERS.items():
        body = proof.span(target)
        require(len(body) == length and sha256(body).hexdigest() == digest, 'effect registry dependency changed')
    require(struct.unpack_from('<II', proof.span(0x080D3818), 60) == (NEXT_TABLE, 0xfffffe95),
            'next registry must be independently addressed relative to 0x16B')
    tables = registry_tables(proof)
    core = proof.span(sites.DIRECT)
    event.check_payload_argument(core, proof.mapping)
    import scheduler_descriptor_lifetime as lifetime
    require(core[:34] == lifetime.CALLEE_HEAD and core[154:180] == lifetime.COPY + lifetime.CALL_SETUP
            and core[184:] == lifetime.CALLEE_RETURN and proof.span(event.THUNK) == bytes.fromhex('1847'),
            'scheduler descriptor copy, zero phase, callback or return changed')
    # R1 and R2 come from adjacent fields of the same selected row or the paired special override.
    for register, offsets, origin in ((1, (74, 98, 146), 3), (2, (76, 100, 148), 2)):
        definitions = sites.reaching_definitions(ins, edges, calls, address, CREATE,
                                                match.ARM_REG_R0+register, 'unresolved registry input')
        require(definitions == [(OWNER+at, match.ARM_REG_R0+origin) for at in offsets],
                'callback or payload size has another reaching definition')
    event.sequence(data, OWNER, OWNER+66, ['ldr r1, [pc, #0x10]', 'subs r0, r4, #1', 'lsls r0, r0, #3',
                  'adds r0, r0, r1', 'ldr r3, [r0]', 'ldrh r2, [r0, #4]', 'b #0x80d359e'])
    event.sequence(data, OWNER, OWNER+88, ['ldr r0, [pc, #0x58]', 'ldr r2, [pc, #0x5c]', 'adds r1, r4, r2',
                  'lsls r1, r1, #3', 'adds r1, r1, r0', 'ldr r3, [r1]', 'ldrh r2, [r1, #4]',
                  'ldr r0, [pc, #0x54]', 'cmp r4, r0', 'bne #0x80d359e'])
    event.sequence(data, OWNER, OWNER+130, ['ldr r1, [pc, #0x3c]', 'subs r0, r6, #1', 'lsls r0, r0, #3',
                  'adds r0, r0, r1', 'ldrh r0, [r0, #6]', 'strh r0, [r2, #0x16]', 'adds r0, r2, #0',
                  'strh r6, [r0, #0x18]', 'ldr r3, [pc, #0x30]', 'movs r2, #0x28'])
    event.sequence(data, OWNER, OWNER+150, ['ldr r0, [pc, #0x30]', 'ldr r0, [r0]', 'ldr r1, [pc, #0x30]',
                  'ldr r1, [r1]', 'str r1, [sp]', 'adds r1, r3, #0', 'add r3, sp, #4', 'bl #0x8005954'])
    require(set(pc for pc, tails in edges.items() if OWNER+150 in tails) == {OWNER+78, OWNER+106, OWNER+148}
            and not sites.looped_sites(edges, [CREATE]), 'registry paths do not meet at the expected call')
    record = dict(site=CREATE, target=sites.DIRECT, scheduler_entry='direct-entry', callback_register=1,
                  descriptor_register=3, callback_literal_offsets=[196], looped=False,
                  manager_chains=sites.manager_chains(data, address, ins, edges, calls, CREATE),
                  registry_tables=tables)
    return dict(sites=[record], looped_sites=[], dependencies=[sites.DIRECT],
                source_sha256=sha256(Path(__file__).read_bytes()).hexdigest())


def manifest(proof):
    # All standard v1 frame and caller obligations still hold. Keep its existing report
    # producer and fingerprints intact for every ordinary literal-callback owner.
    frame = copy(proof)
    frame.policy = sites.SELECTOR
    summary = sites.manifest(frame)
    summary['schema'] = SCHEMA
    observation = summary['observations'][0]
    require(len(summary['observations']) == 1 and observation['frame_bytes'] == 52 and
            observation['descriptor_offset'] == -48 and not observation['payload_words'] and
            observation['outgoing_argument_word'] == -52, 'unexpected private registry request layout')
    summary['registry'] = dict(
        owner_sha256=OWNER_HASH, predicate=0x080D3B98, object_flag_helper=0x080D3B38,
        common_initialized_fields=[[4,4], [8,4], [12,4], [20,2]],
        primary_and_special_additional_fields=[[22,2],[24,2]], excluded_dispatch_id=EMPTY_ID,
        special_id=SPECIAL_ID, special_callback=SPECIAL, special_size=40,
        special_argument_domain=[1,341], allocation_overhead=28, payload_offset=24,
        initial_callback_phase=0, all_callers_enforce_domain=False)
    summary['assumptions'] += [
        'The low half of the effect ID is 1..0x169 excluding the empty 0xDB dispatch row. The first 341 '
        'IDs select one primary entry; the next 20 select the extended registry. For 0x159 the full '
        '32-bit third argument, not only its low half, is 1..341. Entry 0xDB is valid as metadata here.',
        'Primary effects require an aligned readable object flags halfword at +4. For a primary or special '
        'metadata low byte of 16 the two successive aligned pointer loads at offset zero are valid; '
        'their final result may be null or must permit the category byte read at +6. Mode is 2 exactly '
        'when that tag matches and the final object is null or its category is outside 6..18; otherwise 0.',
        'The default extended path leaves descriptor halfwords +22 and +24 as representation bytes. '
        'Only the selected callback may supply any additional input requirements. Its effects, nonretention '
        'and termination remain conditional; an indexed function entry proves none of these.',
    ]
    return summary
