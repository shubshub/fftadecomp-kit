"""Trim a nine-cell name in a private initialized ten-halfword buffer."""
from hashlib import sha256
from struct import unpack_from

import bios_cpuset_fill_profile as bios
import function_thunk_profile as thunk
import installed_zero_effects as zero
import iwram_installation_prerequisite as installation
import literal_callback_closure_profile as closure
import match
import named_data_buffer_profile as buffers
import owner_graph_profile as graph
import plausible
import scheduler_zero_descriptor as boot
from ability_range_local_bytes import block, require
from active_entry_shuffle_profile import compiler_symbol_roles
from known_query_native_closure_profile import environment_fingerprint
from sdk_cpuset_halfword import TOKEN, base_header
from software_double_profile import indices, span_record
from software_float_profile import ROM_SHA256

OWNER = 0x0812A878
END = 0x0812A91C
TABLE = 'g_callbacks_0836D4B8'
VIA = '_call_via_r2'
CPUSET = 'func_0814186C'
CALLS = {OWNER + 16: thunk.ALIASES[VIA], OWNER + 60: bios.ADDRESS, OWNER + 152: bios.ADDRESS}
BINDINGS = dict(calls=[[16, VIA], [60, CPUSET], [152, CPUSET]], data=[[68, TABLE, 0]],
                functions=[], switches=[])
SOURCE_HASH = '2e0bef899e17ec40013d1e34221ee990432df4341e99edfc02ddee37396c341a'


def check_source(root):
    path = root / 'src/0812A878.c'
    text = path.read_text()
    require(plausible.include_closure(root, path) == ({'src/0812A878.c', 'include/ffta.h'}, [])
            and base_header((root / 'include/ffta.h').read_bytes(),
                            ('func_0812A878', CPUSET, TABLE, 'State0812A5BC', 'ClearBuffer'))
            and not any(marker in text for marker in (chr(92), '??', '%:', chr(0)))
            and sha256(' '.join(TOKEN.findall(plausible.strip_comments_and_strings_keep_strings(text)))
                       .encode()).hexdigest() == SOURCE_HASH,
            'name entry requires its reviewed state, ten-halfword local and clear/copy declarations')


def check_original(image, bindings, targets):
    require(bindings == BINDINGS and targets == {VIA: (thunk.ALIASES[VIA], False),
            CPUSET: (bios.ADDRESS, False), TABLE: (boot.POINTER, True)}
            and all(row['size'] == 0 for row in image['symbols'] if row['name'] in targets),
            'name entry requires its three original calls and immutable slot-zero object')
    compiler_symbol_roles(image, targets)


def callback(rom, mapping, index):
    plan = boot.initializer_plan(rom, mapping, index)
    effect = zero.verify_conditional(bytes.fromhex(plan['source_image']['bytes']), boot.DESTINATION,
                                     boot.DESTINATION, 20, selector=zero.SELECTOR)
    case = effect['cases'][0]
    require(case['alignment'] == 0 and case['reads'] == [('stack', -4, 4)]
            and case['writes'] == [('stack', -4, 4)] + [('destination', i, 4) for i in range(0, 20, 4)]
            and case['SP_restored'] and case['protected_return'] and not case['destination_read'],
            'installed clearer must initialize exactly the aligned local and restore the private return')
    entries, rows = indices(mapping, index)
    target = thunk.ALIASES[VIA]
    require(span_record(target, target + 2, entries, rows, rom)['instrs'] == 1,
            'indexed one-instruction R2 thunk required')
    return dict(boot=list(boot.BOOT), installer=plan['installer'], entry=plan['entry'],
                thunk=thunk.dependencies([VIA], rom), bios=plan['wrapper'], installation=plan['copy_plan'],
                image_sha256=effect['image_sha256'], clear=effect['conditional_conclusion'],
                aligned_reads=case['reads'], aligned_writes=case['writes'])


def caller(rom, mapping, index, objects):
    # These two original sites supply named, even output addresses. Neither the
    # loaded words nor the function index grants physical access to those bytes.
    start = 0x0812A5BC
    data, ins, edges, calls, _ = closure.complete(start, 602, 230, rom, mapping, index)
    site_and_object = [(0x0812A674, 0x02001F1C), (0x0812A6E8, 0x020021A0)]
    require([pc for pc in sorted(calls) if calls[pc] == OWNER] == [pc for pc, _ in site_and_object],
            'name entry caller lost one of its two direct routes')
    block(ins, start, 'push {r4, r5, r6, r7, lr}', 'sub sp, #0x18', 'adds r4, r0, #0', 'adds r6, r1, #0')
    r6_writes = sorted(pc for pc, item in ins.items() if 'r6' in [item.reg_name(r) for r in item.regs_access()[1]])
    require(r6_writes == [start + 6, 0x0812A810], 'caller state is not retained in R6')
    names = match.parse_data_symbols(objects)
    require(names.get('data_02001F1C') == site_and_object[0][1] and
            names.get('g_state_020021A0') == site_and_object[1][1], 'caller output symbols differ')
    for (pc, destination), spelling, displacement in zip(site_and_object, ('8', '0x44'), (8, 0x44)):
        block(ins, pc - 4, f'ldr r1, [pc, #{spelling}]',
              'adds r0, r6, #0', 'bl #0x812a878')
        require(all([origin for origin, ends in edges.items() if site in ends] == [site - 2]
                    for site in (pc - 2, pc))
                and unpack_from('<I', data, (pc & ~3) + displacement - start)[0] == destination,
                'caller must supply the original state and named output on every incoming edge')
    return dict(address=start, instructions=len(ins), data_sha256=sha256(data).hexdigest(),
                sites_and_outputs=site_and_object,
                condition='Earlier returning calls in the name-entry handler retain its callee-saved R6.')


def scan(ins):
    # Four saves followed by 20 private bytes. The installed clearer preserves
    # R4 and R6; subsequent instructions overwrite its cursor and return scratch.
    block(ins, OWNER, 'push {r4, r5, r6, lr}', 'sub sp, #0x14', 'adds r4, r0, #0', 'adds r6, r1, #0',
          'ldr r0, [pc, #0x38]', 'ldr r2, [r0]', 'mov r0, sp', 'movs r1, #0x14', 'bl #0x814224c',
          'movs r3, #0', 'ldr r5, [pc, #0x30]', 'adds r2, r4, r5')
    # R3 starts at zero and advances through 8 only along the matching-space
    # edge. At the mismatch R0 is state+0x312+2*i and R1 becomes the local.
    block(ins, 0x0812A892, 'lsls r1, r3, #1', 'adds r0, r2, r1', 'ldrb r0, [r0]', 'cmp r0, #0x40',
          'bne #0x812a8a6', 'adds r0, r1, #1', 'adds r0, r2, r0', 'ldrb r0, [r0]',
          'cmp r0, #0x73', 'beq #0x812a8c8', 'adds r0, r1, r5', 'adds r0, r4, r0', 'movs r2, #9',
          'subs r2, r2, r3', 'ldr r1, [pc, #0x14]', 'ands r2, r1', 'mov r1, sp',
          'bl #0x814186c', 'b #0x812a8d2')
    block(ins, 0x0812A8C8, 'adds r0, r3, #1', 'lsls r0, r0, #0x18', 'lsrs r3, r0, #0x18',
          'cmp r3, #8', 'bls #0x812a892')
    # Descending traversal writes both bytes of the current cell only. Its
    # unsigned decrement from zero leaves the shifted sign bit set and exits.
    block(ins, 0x0812A8D2, 'movs r3, #8', 'movs r4, #0', 'lsls r0, r3, #1', 'mov r1, sp',
          'adds r2, r1, r0', 'ldrb r1, [r2]', 'cmp r1, #0', 'bne #0x812a8ec',
          'strb r1, [r2]', 'adds r0, #1', 'add r0, sp, r0', 'strb r1, [r0]', 'b #0x812a900',
          'cmp r1, #0x40', 'bne #0x812a90a', 'adds r0, #1', 'mov r5, sp', 'adds r1, r5, r0',
          'ldrb r0, [r1]', 'cmp r0, #0x73', 'bne #0x812a90a', 'strb r4, [r2]', 'strb r4, [r1]',
          'subs r0, r3, #1', 'lsls r0, r0, #0x18', 'lsrs r3, r0, #0x18', 'cmp r0, #0',
          'bge #0x812a8d6', 'mov r0, sp', 'adds r1, r6, #0', 'movs r2, #0xa', 'bl #0x814186c',
          'add sp, #0x14', 'pop {r4, r5, r6}', 'pop {r0}', 'bx r0')
    suffixes = []
    for i in range(9):
        count, width = installation.plain_copy_units((9 - i) & 0x1fffff, 20)
        require(width == 2 and 2*i + count*width == 18 and 0 <= 2*i < 2*i+2 <= 18,
                'input suffix or trimming pair exceeds the nine cells')
        suffixes.append(dict(first=i, control=count, source=[0x312+2*i, 0x324], local=[0, count*width]))
    descending = []
    i = 8
    while len(descending) <= 9:
        descending.append(i)
        shifted = ((i - 1) << 24) & 0xffffffff
        if shifted & 0x80000000:
            break
        i = shifted >> 24
    require(descending == list(range(8, -1, -1)), 'trim must exit before the unsigned index wraps')
    require(installation.plain_copy_units(10, 20) == (10, 2), 'final copy must read all ten halfwords')
    return dict(suffixes=suffixes, trim_indices=descending, all_spaces_skips_first_copy=True, zero_terminator=[18,20],
                final_halfwords=10, final_output=[0,20], local=[-36,-16], saves=[-16,0], clearer_save=[-40,-36])


def prove(data, rom, mapping, index, objects, bindings, ins, calls, refinement, words):
    require(sha256(rom).hexdigest() == ROM_SHA256 and data == rom[OWNER-match.ROM_BASE:END-match.ROM_BASE]
            and len(ins) == 72 and calls == CALLS and bindings == BINDINGS and not words
            and match.parse_data_symbols(objects).get(TABLE) == boot.POINTER, 'name entry owner or relocations differ')
    entries, rows = indices(mapping, index)
    require(span_record(OWNER, END, entries, rows, rom)['instrs'] == len(ins),
            'name entry requires both index counts to equal the native reachable instruction count')
    partition = graph.partition(data, OWNER, refinement, ins, words)
    literals = [(row['address']-OWNER, row['value'], row['load_sites'], row['switch_word']) for row in partition['words']]
    require(partition['code_bytes'] == 150 and partition['alignment'] == [[OWNER+66, OWNER+68]]
            and literals == [(68,boot.POINTER,[OWNER+8],False), (72,0x312,[OWNER+22],False),
                             (76,0x1fffff,[OWNER+54],False)], 'name entry code and literals differ')
    return dict(schema=buffers.THUNK_SCHEMA, instructions=len(ins), calls=BINDINGS['calls'], runtime_calls=[],
                partition=partition, scan=scan(ins), provider=callback(rom,mapping,index),
                caller=caller(rom,mapping,index,objects), environment=environment_fingerprint(),
                conditions=[
                    'The installer executed and its 176 original bytes remain executable and unchanged in IWRAM '
                    'through every fetch of the clearer. The real BIOS executes both reached halfword copies '
                    'with the verified controls, returns normally, and preserves R4–R11 and SP. Its only '
                    'user-memory reads and writes are the specified source and destination windows, respectively. '
                    'It retains no buffer pointer.',
                    'The input state is live and aligned; its 18 name bytes are initialized and readable. '
                    'The output has 20 live writable halfword-aligned bytes. Both access ordinary nonwrapping '
                    'work RAM and are physically disjoint from this call’s local, active saves and executing '
                    'code. The output may alias the input name after its final read.',
                    'The word-aligned private stack covers entry SP minus 40 through entry SP, and the saved '
                    'return is a valid Thumb continuation. No interrupt, alias or concurrent writer changes '
                    'live memory during execution.'])
