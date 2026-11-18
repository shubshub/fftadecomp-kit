"""The scheduler's allocating constructor with the registered transfer callback."""
from hashlib import sha256
from pathlib import Path
import struct

import allocator_insert_relation as insertion
import allocator_remove_relation as removal
import allocator_search_relation as search
import allocator_split_relation as split
import allocator_wrapper_relation as allocation
import match
import owner_graph_profile as graph
import packed_transfer_task as transfer
import scheduler_allocator_descriptor_prefix as allocator_prefix
import scheduler_allocator_state as scheduler
import scheduler_copy_state as descriptor_copy
from ability_range_local_bytes import block, require
from sdk_cpuset_halfword import TOKEN, base_header
from software_double_profile import indices, span_record
from transfer_tree_destruction import provider_ins

SELECTOR = 'conditional-transfer-task-construction-v1'
SCHEMA = 'elf-symbol-thumb-' + SELECTOR
CONTROL_FLOW = ('complete allocating scheduler constructor with a reviewed transfer-task initializer; '
                'other registered callbacks require their own payload and returning ABI contracts')
OWNER, END = 0x08005954, 0x08005A22
TABLE = transfer.TABLE
SLOT = transfer.installer.POINTER
CALLS = ((0x22, 'func_08007138', 0x08007138), (0x30, '_call_via_r2', 0x0814224C),
         (0xB4, '_call_via_r3', 0x08142250))
BINDINGS = dict(calls=[[site, name] for site, name, _ in CALLS], data=[[0x64, TABLE, 0]],
                functions=[], switches=[])
TOKENS = 'abc3f1c0ed36d337948eded3328af985c4f2c619a8d546fc795c50838c495115'
PROVIDER_STARTS = {OWNER, 0x08006C88, 0x08006D38, 0x08006DA0, 0x08006E28, 0x08006EC0,
                   0x08007138, 0x0814224C, 0x08142250, 0x08006878, 0x08005B6C, 0x08005B28}
PROVIDERS = tuple(row for row in transfer.PROVIDERS if row[0] in PROVIDER_STARTS) + (
    (transfer.OWNER, transfer.END, transfer.OWNER_SHA),)


def check_source(root, address):
    import plausible

    require(address == OWNER, 'wrong scheduler constructor')
    root = Path(root)
    source = (root / 'src/08005954.c').read_text()
    require(base_header((root / 'include/ffta.h').read_bytes(), ('func_08005954', TABLE, 'func_08007138'))
            and not any(x in source for x in ('\\', '??', '%:', '\0')), 'changed constructor C inputs')
    tokens = TOKEN.findall(plausible.strip_comments_and_strings_keep_strings(source))
    require(sha256(' '.join(tokens).encode()).hexdigest() == TOKENS,
            'expected reviewed allocation, list attachment and by-value event copy')


def check_bindings(bindings, targets, image):
    expected = {name: (target, False) for _, name, target in CALLS}
    expected[TABLE] = (SLOT, True)
    require(bindings == BINDINGS and targets == expected and
            all(sym['size'] == 0 for sym in image['symbols'] if sym['name'] in expected),
            'wrong typed constructor relocations')


def bind_allocator(rom, mapping, index):
    """Bind the existing complete allocator and list-insertion relations at their original sites."""
    entries, rows = indices(mapping, index)
    owners = {}
    for start, end, digest in PROVIDERS:
        span = span_record(start, end, entries, rows, rom)
        data = rom[start - match.ROM_BASE:end - match.ROM_BASE]
        require(sha256(data).hexdigest() == digest, f'changed constructor provider at {start:08X}')
        owners[start] = data, start, span['instrs']
    search_layout = search.bind(*owners[0x08006C88], selector=search.SELECTOR)
    remove_code, remove_pc, remove_count = owners[0x08006DA0]
    median_code, median_pc, median_count = owners[0x08006D38]
    median_layout = removal.bind(remove_code, remove_pc, median_code, median_pc,
                                 (remove_count, median_count), selector=removal.SELECTOR)
    insert_layout = insertion.bind(*owners[0x08006E28], search_layout, median_layout, selector=insertion.SELECTOR)
    clear_thunk = 0x0814224C
    allocator = split.bind(*owners[0x08006EC0], insert_layout, clear_thunk, owners[clear_thunk][0],
                           SLOT, selector=split.SELECTOR)
    wrapper = allocation.bind(*owners[0x08007138], allocator, selector=allocation.SELECTOR)
    callback_thunk = 0x08142250
    return scheduler.bind(*owners[OWNER], wrapper, callback_thunk, owners[callback_thunk][0], selector=scheduler.SELECTOR)


def phase_zero(rom, mapping, index):
    caller = provider_ins(rom, 0x08006878, 0x080068A8)
    block(caller, 0x0800688A, 'str r0, [sp, #4]', 'mov r0, sp', 'strh r4, [r0, #0x14]',
          'ldr r0, [pc, #0x14]', 'movs r2, #0x80', 'lsls r2, r2, #0xf', 'adds r1, r1, r2',
          'lsrs r1, r1, #0x10', 'mov r2, sp', 'bl #0x8005b6c')
    wrapper = provider_ins(rom, 0x08005B6C, 0x08005BA4)
    block(wrapper, 0x08005B74, 'adds r6, r0, #0', 'adds r4, r1, #0', 'mov r8, r2', 'lsls r4, r4, #0x10',
          'lsrs r4, r4, #0x10', 'ldr r5, [pc, #0x24]', 'ldr r0, [r5]', 'str r3, [sp]', 'adds r1, r6, #0',
          'adds r2, r4, #0', 'mov r3, r8', 'bl #0x8005954', 'ldr r1, [r5]', 'ldrh r1, [r1, #0xc]',
          'movs r2, #1', 'eors r1, r2', 'strh r1, [r0, #0x16]')
    require(struct.unpack_from('<I', rom, 0x68A8)[0] == transfer.OWNER | 1 and
            struct.unpack_from('<I', rom, 0x5BA4)[0] == struct.unpack_from('<I', rom, 0x5B3C)[0] == 0x02008FF0,
            'wrong installed transfer callback or its global manager')
    callback = provider_ins(rom, transfer.OWNER, 0x08005FBE)
    block(callback, 0x08005EF8, 'push {r4, r5, r6, lr}', 'adds r5, r2, #0', 'ldrh r2, [r1]',
          'cmp r2, #1', 'beq #0x8005f50', 'cmp r2, #1', 'bgt #0x8005f0c', 'cmp r2, #0', 'beq #0x8005f16')
    block(callback, 0x08005F16, 'ldr r6, [r1, #4]', 'ldrh r0, [r1, #0x14]', 'strh r0, [r5]',
          'lsls r0, r0, #0x10', 'movs r4, #0', 'cmp r0, #0', 'beq #0x8005f42', 'lsls r1, r4, #1',
          'adds r1, r1, r4', 'lsls r1, r1, #2', 'adds r0, r5, r1', 'adds r1, r1, r6', 'adds r0, #0x34',
          'movs r2, #0xc', 'bl #0x81443fc', 'adds r0, r4, #1', 'lsls r0, r0, #0x10', 'lsrs r4, r0, #0x10',
          'ldrh r0, [r5]', 'cmp r4, r0', 'blo #0x8005f24', 'movs r0, #0x80', 'lsls r0, r0, #4',
          'strh r0, [r5, #4]', 'bl #0x8005b28', 'str r0, [r5, #8]', 'b #0x8005fb6')
    block(callback, 0x08005FB6, 'movs r0, #0', 'pop {r4, r5, r6}', 'pop {r1}', 'bx r1')
    helper = transfer.rom_copy.helper_facts(rom, mapping, index)
    offset = transfer.COPY - match.ROM_BASE
    effects = transfer.copy_effects.contract(rom[offset:offset + 98], transfer.RECORD_BYTES)
    return dict(caller=0x08006878, wrapper=0x08005B6C, callback=transfer.OWNER, input_fields=[[4,4],[20,2]],
                phase_zero_reads=[[0,2],[4,4],[20,2]], copy_helper=helper, record_copy=effects,
                record_bytes=12, first_record_from_node=76, secondary_allocation=2048,
                secondary_result='Null or live buffer written at node+32; creation accepts either result.',
                callback_retains_descriptor=False, counts=transfer.count_domain(rom))


def prove(data, address, rom, mapping, index, objects, bindings, ins, calls, refinement, words):
    require(address == OWNER and len(data) == END - OWNER and len(ins) == 97 and bindings == BINDINGS and
            calls == {OWNER + site: target for site, _, target in CALLS} and not words and
            match.parse_data_symbols(objects).get(TABLE) == SLOT, 'wrong constructor span, sites or table')
    layout = bind_allocator(rom, mapping, index)
    require(sha256(data).hexdigest() == layout.sha256, 'owner differs from complete allocation/list relation')
    partition = graph.partition(data, address, refinement, ins, words)
    require(partition['words'] == [dict(address=OWNER+0x64, value=SLOT, load_sites=[OWNER+0x28], switch_word=False)]
            and partition['alignment'] == [[OWNER+0x62, OWNER+0x64]], 'wrong constructor code/data partition')
    plan = transfer.installer.initializer(rom, mapping, index)
    # For an aligned task and 92+12*N bytes, this entire entry follows the word loop, storing
    # four bytes and subtracting four each time. Its two other branches implement byte tails.
    image = rom[transfer.installer.IMAGE-match.ROM_BASE:transfer.installer.IMAGE-match.ROM_BASE+176]
    native = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
    clear = {item.address: item for item in native.disasm(image[:50], transfer.installer.DESTINATION)}
    block(clear, 0x03005E78, 'push {lr}', 'adds r2, r0, #0', 'cmp r1, #0', 'ble #0x3005ea6',
          'cmp r1, #3', 'bls #0x3005e9a', 'movs r0, #3', 'ands r0, r2', 'cmp r0, #0', 'bne #0x3005e9a',
          'movs r0, #0', 'stm r2!, {r0}', 'subs r1, #4', 'cmp r1, #3', 'bhi #0x3005e8e',
          'cmp r1, #0', 'ble #0x3005ea6', 'movs r0, #0', 'strb r0, [r2]', 'adds r2, #1',
          'subs r1, #1', 'cmp r1, #0', 'bgt #0x3005e9c', 'pop {r0}', 'bx r0')
    require(rom[0x59EE:0x5A04] == descriptor_copy.COPY, 'changed private event copy or phase overwrite')
    origins = tuple(('opaque-byte', 'incoming descriptor', i) for i in range(28))
    copied = descriptor_copy._transport(origins)
    require(copied['bytes'] == (0, 0, *origins[2:]), 'copied event changed outside its phase')
    block(ins, 0x08005A04, 'ldr r3, [r7]', 'adds r0, r7, #0', 'bl #0x8142250', 'movs r0, #0x80',
          'lsls r0, r0, #1', 'strh r0, [r7, #0x14]', 'adds r0, r7, #0', 'add sp, #0x1c',
          'pop {r3, r4}', 'mov r8, r3', 'mov sb, r4', 'pop {r4, r5, r6, r7}', 'pop {r1}', 'bx r1')
    # The old descriptor also arrives at the allocator in caller-scratch R3. Both size
    # endpoints take its nonzero path. The retained prefix checks both rounding arms, and
    # the exhaustive count partition below places every admitted count on this same path.
    first_size, first_bytes, _ = transfer.allocation(0)
    last_size, last_bytes, _ = transfer.allocation(transfer.MAX_COUNT)
    first = allocator_prefix.prove(layout, first_size, selector=allocator_prefix.SELECTOR)
    last = allocator_prefix.prove(layout, last_size, selector=allocator_prefix.SELECTOR)
    require(first_bytes == 92 and last_bytes == 65528 and
            first['wrapper_prefix'] == last['wrapper_prefix'] and
            first['allocator_prefix'] == last['allocator_prefix'], 'source alias reaches a changed allocator path')
    proof = dict(allocator_layout=layout.sha256, providers=PROVIDERS, allocator_source_R3=first,
        nonzero_request_bounds=[first_bytes,last_bytes], frame_bytes=56, copied_bytes=28,
        replaced_bytes=[0,1], owner_writes_source=False, padding_is_transported_without_interpretation=True,
        clear_installer=plan['copy_plan'], clear_image=plan['image_sha256'], fifth_argument='parent at entry SP',
        attachment='Append at end of parent.child or manager.head, set previous link and optional parent.',
        call_arguments=['new task', 'private copied phase-zero event', 'new task+24'],
        post_callback='Write state 0x100 at +20, return the live task. Public wrapper then writes manager flags XOR 1.',
        transfer=phase_zero(rom, mapping, index),
        premises=['Completed original installation, stable callback slot and resident code. Successful first task '
                  'allocation, ordinary aligned heap, valid manager, finite stable sibling lists and a live optional parent.',
                  'Aligned readable 28-byte source with initialized callback-specific fields. Source, entries, '
                  'live task, manager, heap metadata and private frames respect their distinct lifetimes and do not overlap.',
                  'The transfer caller supplies 0 through 5453 records, all live for the count. Its secondary buffer '
                  'allocation can return null. The original allocator and callbacks preserve the calling convention.',
                  'Other callbacks must return, read only their initialized event fields, leave live task/links valid, '
                  'stay within their allocated payload and never retain the private descriptor. Their effects are unproved.'],
        arbitrary_callback_effects_proved=False, allocation_success_proved=False,
        verifier_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
    return dict(schema=SCHEMA, instructions=len(ins), calls=BINDINGS['calls'], runtime_calls=[],
                partition=partition, transfer_construction=proof)
