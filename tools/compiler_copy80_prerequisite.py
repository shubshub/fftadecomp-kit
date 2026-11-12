"""Conditional eighty-byte relation for the complete canonical copy helper.

This is a helper prerequisite, not a caller, source or ELF admission profile.
Caller arguments, actual object extents, permissions and C compatibility remain
independent obligations. No address-name adapter or matcher gate is installed.
"""
import hashlib
import json
from pathlib import Path

import match
import owner_graph_profile as graph
from local_rom_halfword_table_profile import COPY_SHA256, _indexed, require

SCHEMA = 'conditional-aligned-copy80-helper-prerequisite-v1'
CONDITIONS = [
    'actual helper inputs are destination, source and count80; caller provenance is separate',
    'source and destination are four-byte aligned disjoint80-byte ranges with nonwrapping end cursors',
    'source contains80 readable ordinary bytes at helper entry; their values remain arbitrary',
    'destination has80 writable ordinary bytes with a live compatible object lifetime',
    'the combined caller and twelve-byte helper frame is aligned, live and ordinarily readable/writable',
    'source, destination, combined frame and both complete code bodies are mutually disjoint',
    'the code, source, destination and active frame are not modified asynchronously during the copy',
    'the actual Thumb return continuation is valid and C/ABI compatibility is independently established',
]


def relation(source_bytes):
    """One ordered byte state, with disjoint regions under explicit conditions."""
    require(type(source_bytes) in (bytes, tuple) and len(source_bytes) == 80 and all(
        type(value) is int and 0 <= value < 256 or type(value) is str
        for value in source_bytes), 'exact eighty concrete or opaque source bytes required')
    cells = {('source', i): value for i, value in enumerate(source_bytes)}
    reads, writes, saves = [], [], []
    for offset, name in ((-12, 'entry_R4'), (-8, 'entry_R5'), (-4, 'entry_LR')):
        for i in range(4):
            value = f'{name}.byte{i}'
            cells['stack', offset+i] = value
            saves.append([offset+i, value])
    # Both addresses are aligned, so the initial guard takes the four-word loop.
    trace = list(range(0, 26, 2))
    remaining, cursor = 80, 0
    while remaining > 15:
        for _ in range(4):
            values = [cells['source', cursor+i] for i in range(4)]
            reads.append([cursor, 4, values])
            for i, value in enumerate(values):
                cells['destination', cursor+i] = value
                writes.append([cursor+i, value])
            cursor += 4
        remaining -= 16
        trace.extend(range(26, 48, 2))
    require(cursor == 80 and remaining == 0, 'copy must exhaust exactly eighty bytes')
    # No residual word or byte transfer executes. SUB R2,#1 creates the sentinel.
    trace.extend((48, 50, 62, 64, 66, 68, 70, 72, 90, 92, 94, 96))
    require(all(cells['stack', offset] == value for offset, value in saves),
            'helper protected save changed')
    require(all(cells['source', i] == value for i, value in enumerate(source_bytes)),
            'source changed during copy')
    return dict(destination_bytes=[cells['destination', i] for i in range(80)],
        copy_reads=reads, copy_writes=writes, helper_saves=saves,
        helper_instruction_offsets=trace, copy_words=20, sixteen_byte_iterations=5,
        final_registers=dict(r0='entry_destination', r1='entry_LR', r2=0xFFFFFFFF,
            r3='entry_source+80', r4='entry_R4', r5='entry_R5',
            r6_to_r12='unchanged', sp='entry_SP', lr='entry_LR'),
        final_flags=dict(N='bit31(entry_destination)', Z='entry_destination == 0', C=False, V=False),
        return_continuation='entry_LR via BX R1', frame_lifetime='helper frame expired after POP',
        caller_frame_writes=[], physical_access_proved=False, caller_arguments_proved=False)


def concrete_domain(*, entry_sp, source, destination, caller_frame_bytes, caller_code, helper_code):
    """Validate supplied numeric premises, without granting memory permissions.

    entry_sp is the caller's entry SP. Its supplied frame size is independently
    authenticated by the caller proof; it is not derived by this helper lemma.
    """
    require(all(type(value) is int and 0 <= value <= 0xFFFFFFFF
                for value in (entry_sp, source, destination)), 'u32 addresses required')
    require(type(caller_frame_bytes) is int and 0 <= caller_frame_bytes <= 4096 and
            caller_frame_bytes % 4 == 0, 'bounded aligned caller frame size required')
    require(entry_sp % 4 == source % 4 == destination % 4 == 0 and
            entry_sp >= caller_frame_bytes+12, 'aligned nonwrapping addresses and frame required')
    require(source+80 <= 0xFFFFFFFF and destination+80 <= 0xFFFFFFFF,
            'source and destination end cursors must not wrap')
    for code in (caller_code, helper_code):
        require(type(code) is tuple and len(code) == 2 and all(type(v) is int for v in code) and
                0 <= code[0] <= 0xFFFFFFFF and code[0] % 2 == 0 and
                code[1] > 0 and code[0]+code[1] <= 0x100000000,
                'nonwrapping complete code ranges required')
    require(helper_code[1] == 98, 'complete ninety-eight-byte helper required')
    regions = dict(source=(source, 80), destination=(destination, 80),
        frame=(entry_sp-caller_frame_bytes-12, caller_frame_bytes+12),
        caller_code=caller_code, helper_code=helper_code)
    for name, (base, size) in regions.items():
        require(base+size <= 0x100000000, f'{name} range wraps')
    rows = list(regions.items())
    for i, (left_name, (left, size)) in enumerate(rows):
        for right_name, (right, width) in rows[i+1:]:
            require(left+size <= right or right+width <= left,
                    f'{left_name} overlaps {right_name}')
    return dict(combined_frame=[entry_sp-caller_frame_bytes-12, entry_sp],
        source_range=[source, source+80], destination_range=[destination, destination+80],
        physical_access_granted=False, caller_arguments_proved=False,
        source_values_known=False, conditions=list(CONDITIONS))


def verify_helper(address, rom, mapping, index):
    """Authenticate the complete helper before exposing its conditional relation."""
    import owner_admission_profile as owner

    require(all(type(raw) is bytes for raw in (rom, mapping, index)) and
            type(address) is int and match.ROM_BASE <= address <= match.ROM_BASE+len(rom)-98 and
            address % 2 == 0,
            'exact immutable inputs and an aligned complete ROM helper required')

    def unique(pairs):
        result = {}
        for key, value in pairs:
            require(key not in result, 'duplicate helper mapping key')
            result[key] = value
        return result

    json.loads(mapping, object_pairs_hook=unique)
    body = rom[address-match.ROM_BASE:address-match.ROM_BASE+98]
    _indexed(body, address, 49, rom, mapping, index)
    require(hashlib.sha256(body).hexdigest() == COPY_SHA256, 'complete canonical copy helper differs')
    refinement = owner.refine(body, address, mapping)
    instructions, _, branches, calls, words = graph.graph(body, address, refinement)
    require(len(instructions) == 49 and not branches and not calls and not words,
            'complete forty-nine-instruction helper CFG required')
    partition = graph.partition(body, address, refinement, instructions, words)
    return dict(schema=SCHEMA, helper=address, complete_bytes=98, instructions=49,
        partition=partition, relation=relation(tuple(f'source_byte_{i}' for i in range(80))),
        conditions=list(CONDITIONS), source_or_ELF_admission=False,
        caller_arguments_proved=False, physical_access_proved=False,
        input_pins={name: hashlib.sha256(raw).hexdigest() for name, raw in
                    (('helper', body), ('rom', rom), ('mapping', mapping), ('index', index))},
        producer_sha256={path.name: hashlib.sha256(path.read_bytes()).hexdigest()
            for path in Path(__file__).parent.glob('*.py')})
