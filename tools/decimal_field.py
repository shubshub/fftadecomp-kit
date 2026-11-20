"""The eight-byte local shared by the six-column formatter and the aligned strlen."""
from hashlib import sha256
from itertools import product
from pathlib import Path
from struct import unpack_from

import canonical_integer_scalar_inventory as integer
import divsi3_profile as division
import modsi3_profile as remainder
import named_data_buffer_profile as buffers
import owner_graph_profile as graph
import plausible
from ability_range_local_bytes import block, require
from active_entry_shuffle_profile import compiler_symbol_roles
from known_query_native_closure_profile import environment_fingerprint
from sdk_cpuset_halfword import TOKEN, base_header
from software_double_profile import indices, span_record
from software_float_profile import ROM_SHA256

OWNER, DECIMAL, LENGTH = 0x080142DC, 0x08002FB8, 0x081444B8
BASE = 0x08000000
PINS = {
    OWNER: (0x0801439C, 92, '3c5e56576da48a3f5a68284064152930cf24ad16edf18ae55c6eee443e20e4f4'),
    DECIMAL: (0x08003014, 44, 'd8908bda5f32ef9bd7499b902b915a5061bf9d008074dad7a3b04eda1d6598e6'),
    LENGTH: (0x081444FE, 31, 'e7cc29f69fbd6905cc26b5beb1ff80773d34d719b6c344f68afc534da4d53445'),
}
SOURCE_HASH = 'b960c54da427d343c9712b00b211c06a08db8bf0f4d79cc34ef2ba4976e8a221'
CALLS = {0x080142FE: DECIMAL, 0x08014306: LENGTH}
BINDINGS = dict(calls=[[pc-OWNER, f'func_{target:08X}'] for pc, target in CALLS.items()],
                data=[], functions=[], switches=[])


def check_source(root):
    path = Path(root) / 'src/080142DC.c'
    text = path.read_text()
    require(plausible.include_closure(root, path) == ({'src/080142DC.c', 'include/ffta.h'}, [])
            and base_header((Path(root)/'include/ffta.h').read_bytes(), ('func_080142DC',))
            and not any(marker in text for marker in (chr(92), '??', '%:', chr(0)))
            and sha256(' '.join(TOKEN.findall(plausible.strip_comments_and_strings_keep_strings(text))).encode()).hexdigest() == SOURCE_HASH,
            'decimal field requires its reviewed eight-byte local and compatible declarations')


def check_original(image, bindings, targets):
    expected = {name: (CALLS[OWNER+offset], False) for offset, name in BINDINGS['calls']}
    require(bindings == BINDINGS and targets == expected and
            all(row['size'] == 0 for row in image['symbols'] if row['name'] in targets),
            'decimal field requires the exact two direct compiler calls')
    compiler_symbol_roles(image, targets)


def has_zero(word):
    return ((word - 0x01010101) & ~word & 0x80808080) != 0


def strlen_words():
    alphabet = (0x20, *range(0x30, 0x3A))
    require(all(not has_zero(a | b<<8 | c<<16 | d<<24) for a,b,c,d in product(alphabet, repeat=4)),
            'the first aligned word must contain no zero byte')
    # Bytes 4 and 5 are initialized, byte 6 is NUL. No fact is assigned to
    # byte 7, even when it participates physically in this one aligned load.
    require(all(has_zero(a | b<<8 | opaque<<24)
                for a,b,opaque in product(alphabet, range(0x30,0x3A), range(256))),
            'the second word must stop the word scan for every opaque byte')
    return dict(word_read_offsets=[0,4], byte_scan_offsets=[4,5,6], length=6,
                initialized=[0,7], physically_readable=[0,8], opaque_byte=7, opaque_values=256,
                first_word_cases=len(alphabet)**4, second_word_cases=len(alphabet)*10*256)


def output_bounds():
    for digit_count, width in product(range(1,6), range(1,256)):
        # After skipping six minus digit_count leading spaces, the ROM pads
        # until remaining == width, then reads one decimal character per glyph.
        padding = max(width - digit_count, 0)
        digit_bytes = width - padding
        first = 6 - digit_count
        require(0 <= first < first + digit_bytes <= 6 and 2*width + 1 <= 511,
                'decimal field reads beyond the digits or wraps its byte count')
    return dict(widths=[1,255], byte_count=[3,511], source_digit_bytes=[0,6],
                zero_width_promoted=True, truncation='first width digits')


def runtime_results(half):
    """The common positive paths of the pinned DIV/MOD bodies for R1 == 5."""
    if half < 5:
        return 0, half
    # DIV +0x20..0x42 and MOD +0x18..0x3A scale R1 and its quotient
    # bit R3 together. The highest possible scaled divisor is 327680, so
    # the high-bit guards never fire and the second scaling loop is skipped.
    scaled, bit = 5, 1
    while scaled < half:
        scaled <<= 4
        bit <<= 4
    remainder_value, quotient = half, 0
    while True:
        # Both routines subtract the four trial divisors. DIV records the
        # logical bit shifts. MOD records right rotations for the final
        # partial group so it can undo subtractions for fractional bits.
        rotations = 0
        for shift in range(4):
            trial = scaled >> shift
            if remainder_value >= trial:
                remainder_value -= trial
                quotient |= bit >> shift
                if shift:
                    rotations |= (bit >> shift) | ((bit << (32-shift)) & 0xFFFFFFFF)
        if remainder_value == 0 or bit >> 4 == 0:
            break
        bit >>= 4
        scaled >>= 4
    high = rotations & 0xE0000000
    for shift in (3,2,1):
        rotated = (bit >> shift) | ((bit << (32-shift)) & 0xFFFFFFFF)
        if high & rotated:
            remainder_value += scaled >> shift
    return quotient, remainder_value


def producer(ins, edges, calls, rom, mapping, index):
    mod_pc, div_pc = 0x08002FD8, 0x08002FEC
    require(calls == {mod_pc: remainder.ADDRESS, div_pc: division.ADDRESS},
            'decimal producer runtime call sites differ')
    block(ins, DECIMAL, 'push {r4, r5, r6, r7, lr}', 'adds r6, r1, #0',
          'lsls r0, r0, #0x10', 'lsrs r5, r0, #0x10', 'adds r6, #6',
          'movs r0, #0', 'strb r0, [r6]', 'subs r6, #1', 'movs r7, #6')
    block(ins, 0x08002FCA, 'lsls r5, r5, #0x10', 'asrs r4, r5, #0x10',
          'movs r0, #1', 'ands r4, r0', 'lsrs r5, r5, #0x11', 'adds r0, r5, #0',
          'movs r1, #5', 'bl #0x8142950', 'lsls r0, r0, #1', 'adds r0, r0, r4',
          'adds r0, #0x30', 'strb r0, [r6]', 'subs r6, #1', 'subs r7, #1',
          'adds r0, r5, #0', 'movs r1, #5', 'bl #0x81426b8', 'lsls r0, r0, #0x10',
          'lsrs r5, r0, #0x10', 'cmp r0, #0', 'bne #0x8002fca')
    block(ins, 0x08002FF8, 'subs r7, #1', 'movs r0, #1', 'rsbs r0, r0, #0',
          'cmp r7, r0', 'beq #0x800300e', 'movs r1, #0x20', 'strb r1, [r6]',
          'subs r6, #1', 'subs r7, #1', 'cmp r7, r0', 'bne #0x8003004',
          'pop {r4, r5, r6, r7}', 'pop {r0}', 'bx r0')
    shifts = remainder.prove_operands(ins, edges, DECIMAL, [mod_pc], logical_shift_signed16=True)
    divisors = division.prove_divisors(ins, edges, DECIMAL, [mod_pc, div_pc])
    require(shifts == [[0x1A,'r5','r5',17]] and divisors == {mod_pc:5, div_pc:5},
            'half-value and positive five must reach both runtime calls')
    _, frames, components = integer.prove_called_closures(rom, mapping, index, {'__divsi3','__modsi3'})
    # The canonical closure validates the runtime instructions and stack,
    # while this restricted arithmetic model checks their actual return words.
    results = [runtime_results(half) for half in range(32768)]
    require(all(result == divmod(half,5) for half,result in enumerate(results)),
            'positive runtime paths do not produce the quotient and remainder by five')
    # These are the exact native loop recurrences for all possible entry
    # low halfwords. Each decimal digit moves the cursor back by one.
    counts = set()
    for number in range(65536):
        value = number
        cursor = 5
        while True:
            half = value >> 1
            quotient, rem = results[half]
            require(0 <= half <= 32767 and 2*rem+(value&1) == value%10 and quotient == value//10
                    and 0 <= cursor <= 5, 'decimal recurrence, digit, or write offset differs')
            cursor -= 1
            value = quotient
            if value == 0:
                break
        counts.add(5-cursor)
    require(counts == {1,2,3,4,5}, 'producer width exceeds the six-column buffer')
    return dict(input_low16_values=65536, digits=sorted(counts), highest_digit_offset=5,
                half_domain=[0,32767], runtime_operand_pairs=len(results), divisor=5, logical_shift=shifts, terminator_offset=6,
                initialized_writes=[0,7], before_base_cursor=-1, before_base_cursor_dereferenced=False,
                canonical_runtime_families=components, runtime_frames=sorted(frames.items()))


def prove(data, rom, mapping, index, bindings, ins, calls, refinement, words):
    import owner_admission_profile as owner
    require(sha256(rom).hexdigest() == ROM_SHA256 and bindings == BINDINGS and calls == CALLS and not words,
            'decimal field requires the exact ROM, owner calls, and a single scalar literal')
    entries, rows = indices(mapping,index)
    for address,(end,count,digest) in PINS.items():
        row = span_record(address,end,entries,rows,rom)
        code = rom[address-BASE:end-BASE]
        require(row['instrs'] == count and sha256(code).hexdigest() == digest,
                'decimal field dependency extent, bytes or instruction count differ')
    require(data == rom[OWNER-BASE:PINS[OWNER][0]-BASE] and len(ins) == PINS[OWNER][1],
            'decimal field owner CFG differs')
    graph_inputs = {}
    for address in (DECIMAL,LENGTH):
        body = rom[address-BASE:PINS[address][0]-BASE]
        decoded,edges,branches,inner,tables = graph.graph(body,address,owner.refine(body,address,mapping))
        require(len(decoded) == PINS[address][1] and not branches and not tables,
                'decimal field dependency graph differs')
        graph_inputs[address] = body,decoded,edges,inner
    body,decoded,edges,inner = graph_inputs[DECIMAL]
    digits = producer(decoded,edges,inner,rom,mapping,index)
    body,decoded,_,inner = graph_inputs[LENGTH]
    require(not inner and unpack_from('<II',body,0x1C) == (0xFEFEFEFF,0x80808080),
            'strlen zero-word constants or nested calls differ')
    block(decoded,LENGTH,'push {r4, r5, lr}','adds r1, r0, #0','adds r5, r1, #0',
          'movs r0, #3','ands r0, r1','cmp r0, #0','bne #0x81444f0','adds r2, r1, #0',
          'ldr r1, [r2]','ldr r4, [pc, #8]','adds r0, r1, r4','bics r0, r1',
          'ldr r3, [pc, #4]','b #0x81444e4')
    block(decoded,0x081444DC,'adds r2, #4','ldr r1, [r2]','adds r0, r1, r4','bics r0, r1',
          'ands r0, r3','cmp r0, #0','beq #0x81444dc','adds r1, r2, #0','b #0x81444f0',
          'adds r1, #1','ldrb r0, [r1]','cmp r0, #0','bne #0x81444ee','subs r0, r1, r5',
          'pop {r4, r5}','pop {r1}','bx r1')
    partition = graph.partition(data,OWNER,refinement,ins,words)
    require(partition['code_bytes'] == 188 and
            [(row['address'],row['value']) for row in partition['words']] == [(OWNER+188,0xFFFF8000)],
            'decimal field scalar literal or instruction coverage differs')
    block(ins,OWNER,'push {r4, r5, r6, r7, lr}','mov r7, r8','push {r7}','sub sp, #8')
    block(ins,0x080142F8,'lsls r0, r0, #0x10','asrs r0, r0, #0x10','mov r1, sp',
          'bl #0x8002fb8','mov r5, sp','mov r0, sp','bl #0x81444b8')
    block(ins,0x080142E4,'adds r4, r0, #0','lsls r1, r1, #0x10','lsrs r0, r1, #0x10',
          'lsls r2, r2, #0x18','lsrs r2, r2, #0x18','mov r8, r2','cmp r2, #0',
          'bne #0x80142f8','movs r1, #1','mov r8, r1')
    block(ins,0x0801430A,'adds r1, r0, #0','movs r6, #0','movs r3, #0','cmp r3, r1','bge #0x801432e',
          'ldrb r0, [r5]','cmp r0, #0x20','beq #0x801431e','adds r6, r1, #0','b #0x801432e',
          'adds r3, #1','adds r5, #1','cmp r3, r1','bge #0x801432e','ldrb r0, [r5]',
          'cmp r0, #0x20','beq #0x801431e','subs r6, r1, r3')
    block(ins,0x0801432E,'adds r2, r4, #0','movs r4, #0','mov ip, r4','cmp r4, r8','bge #0x8014380',
          'mov r3, r8','cmp r8, r6','ble #0x8014354','movs r0, #0x81','strb r0, [r2]','adds r2, #1',
          'movs r0, #0x18','strb r0, [r2]','adds r2, #1','adds r0, r4, #2','lsls r0, r0, #0x10',
          'lsrs r4, r0, #0x10','adds r6, #1','b #0x801437a')
    block(ins,0x08014354,'mov r7, ip','adds r0, r5, r7','ldrb r0, [r0]','adds r0, #0xe8',
          'ldr r7, [pc, #0x38]','adds r1, r7, #0','orrs r0, r1','lsls r0, r0, #0x10',
          'lsrs r1, r0, #0x10','movs r7, #1','add ip, r7','lsrs r0, r0, #0x18','strb r0, [r2]',
          'adds r2, #1','strb r1, [r2]','adds r2, #1','adds r0, r4, #2','lsls r0, r0, #0x10',
          'lsrs r4, r0, #0x10','subs r3, #1','cmp r3, #0','bne #0x801433a')
    block(ins,0x08014380,'movs r0, #0','strb r0, [r2]','adds r0, r4, #1',
          'lsls r0, r0, #0x10','lsrs r4, r0, #0x10','adds r0, r4, #0','add sp, #8',
          'pop {r3}','mov r8, r3','pop {r4, r5, r6, r7}','pop {r1}','bx r1')
    return dict(schema=buffers.DATAFREE_SCHEMA, instructions=len(ins), calls=BINDINGS['calls'], runtime_calls=[],
                partition=partition, producer=digits, strlen=strlen_words(), local=[-32,-24], saved=[-24,0],
                output=output_bounds(),
                conditions=['The per-call output buffer has 2*width+1 live writable bytes, including '
                            'the final terminator. It may be a designated writable object in a caller frame. '
                            'Its nonwrapping interval is disjoint from executing code, the formatter and '
                            'descendants’ private frame storage, and all live protected save and return slots. '
                            'The entry SP is word-aligned and all '
                            'nested private stack frames and the incoming return address are valid. '
                            'Reading the physically addressable high byte of the second local word grants '
                            'no initialization fact. Interrupts or other agents do not modify live storage.'],
                environment=environment_fingerprint())
