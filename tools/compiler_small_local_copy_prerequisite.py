"""Conditional small byte-copy helper relation; no caller or ELF admission."""
import json
import struct

import compiler_copy80_prerequisite as copy80
from local_rom_halfword_table_profile import COPY_PATH, require

SELECTOR = 'conditional-small-local-copy-helper-v1'
COUNTS = (2, 4, 8, 10)
CONDITIONS = (
    'actual helper arguments are destination, source and the selected exact count; caller provenance is separate',
    'source and destination are disjoint nonwrapping ranges of the selected count',
    'source bytes are live readable ordinary memory; destination bytes are live writable ordinary memory',
    'destination belongs to an independently authenticated caller-approved live window',
    'the aligned twelve-byte helper save frame is live readable/writable ordinary memory',
    'source, destination, helper save frame and complete code ranges are mutually disjoint',
    'code and participating memory are not modified asynchronously during the copy',
    'the actual Thumb return continuation is valid; caller frame safety and C/ABI compatibility are separate',
)


def count_value(count):
    require(type(count) is int and count in COUNTS, 'unsupported exact small-copy count')
    return count


def relation(source_bytes):
    """Execute the authenticated count<=15 byte path over opaque source bytes."""
    require(type(source_bytes) in (bytes, tuple), 'immutable source bytes required')
    count = count_value(len(source_bytes))
    require(all(type(v) is int and 0 <= v < 256 or type(v) is str and bool(v)
                for v in source_bytes), 'concrete bytes or opaque byte tokens required')
    cells = {('source', i): value for i, value in enumerate(source_bytes)}
    saves = []
    for offset, register in ((-12, 'entry_R4'), (-8, 'entry_R5'), (-4, 'entry_LR')):
        for i in range(4):
            value = f'{register}.byte{i}'
            cells['stack', offset+i] = value
            saves.append([offset+i, value])
    # CMP R2,#15 / BLS goes directly to SUB R2,#1 at +64. Neither
    # the alignment guard nor any word-transfer instruction executes.
    trace = [0, 2, 4, 6, 8, 10, 64, 66, 68, 70, 72, 74]
    reads, writes, cursor, remaining = [], [], 0, count-1
    while remaining != 0xFFFFFFFF:
        require(cursor < count, 'small copy exceeds its exact count')
        value = cells['source', cursor]
        reads.append([cursor, 1, [value]])
        cells['destination', cursor] = value
        writes.append([cursor, value])
        trace.extend((76, 78, 80, 82, 84, 86, 88))
        cursor += 1
        remaining = (remaining-1) & 0xFFFFFFFF
    trace.extend((90, 92, 94, 96))
    require(cursor == count and all(cells['stack', offset] == value for offset, value in saves),
            'small copy count or protected helper save differs')
    require(all(cells['source', i] == value for i, value in enumerate(source_bytes)),
            'small copy changed its source')
    return dict(count=count, destination_bytes=[cells['destination', i] for i in range(count)],
        copy_reads=reads, copy_writes=writes, helper_saves=saves,
        helper_instruction_offsets=trace, byte_iterations=count, copy_words=0,
        final_registers=dict(r0='entry_destination', r1='entry_LR', r2=0xFFFFFFFF,
            r3=f'entry_source+{count}', r4='entry_R4', r5='entry_R5',
            r6_to_r12='unchanged', sp='entry_SP', lr='entry_LR'),
        final_flags=dict(N='bit31(entry_destination)', Z='entry_destination == 0', C=False, V=False),
        return_continuation='entry_LR via BX R1', caller_arguments_proved=False,
        physical_access_proved=False, source_or_ELF_admission=False)


def concrete_domain(*, count, helper_sp, source, destination, destination_window,
                    caller_code, helper_code):
    """Check supplied numeric premises; the caller window itself is not proved."""
    count_value(count)
    require(all(type(v) is int and 0 <= v <= 0xFFFFFFFF
                for v in (helper_sp, source, destination)), 'u32 addresses required')
    require(helper_sp >= 12 and helper_sp % 4 == 0, 'aligned nonwrapping helper frame required')
    require(source+count <= 0xFFFFFFFF and destination+count <= 0xFFFFFFFF,
            'source and destination end cursors must not wrap')
    for region in (destination_window, caller_code, helper_code):
        require(type(region) is tuple and len(region) == 2 and
                all(type(v) is int for v in region) and 0 <= region[0] <= 0xFFFFFFFF and
                region[1] > 0 and region[0]+region[1] <= 0x100000000,
                'complete nonwrapping ranges required')
    require(caller_code[0] % 2 == helper_code[0] % 2 == 0 and helper_code[1] == 98,
            'aligned complete code and ninety-eight-byte helper required')
    lo, size = destination_window
    require(lo <= destination and destination+count <= lo+size,
            'destination is outside the supplied caller window')
    regions = dict(source=(source, count), destination=(destination, count),
        helper_frame=(helper_sp-12, 12), caller_code=caller_code, helper_code=helper_code)
    rows = list(regions.items())
    for i, (left_name, (left, width)) in enumerate(rows):
        for right_name, (right, length) in rows[i+1:]:
            require(left+width <= right or right+length <= left,
                    f'{left_name} overlaps {right_name}')
    return dict(regions=regions, destination_window=destination_window,
        caller_window_authenticated=False, caller_arguments_proved=False,
        physical_access_granted=False, conditions=list(CONDITIONS))


def verify_helper(address, rom, mapping, index, *, count, selector, manifest=None):
    """Authenticate all helper bytes and indexes before exposing the relation."""
    require(selector == SELECTOR and type(selector) is str, 'explicit small-copy selector required')
    count_value(count)
    identity = copy80.verify_helper(address, rom, mapping, index)
    body = rom[address-0x08000000:address-0x08000000+98]
    require(all(struct.unpack_from('<H', body, pc)[0] == opcode for pc, opcode in COPY_PATH.items()),
            'small-copy byte-loop instruction differs')
    observed = dict(schema=SELECTOR, helper=address, complete_bytes=98, instructions=49,
        partition=identity['partition'], input_pins=identity['input_pins'],
        producer_sha256=identity['producer_sha256'], conditions=list(CONDITIONS),
        relation=relation(tuple(f'source_byte_{i}' for i in range(count))),
        source_or_ELF_admission=False, actual_copy_invocation_proved=False,
        caller_arguments_proved=False, physical_access_proved=False)
    require(manifest is None or json.dumps(manifest, sort_keys=True) == json.dumps(observed, sort_keys=True),
            'small-copy helper manifest is stale')
    return observed
