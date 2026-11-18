"""The compiler-generated 12-byte record copy in the original transfer task."""
from hashlib import sha256
from pathlib import Path
import struct

import copy_helper_summary_profile as copy_effects
import installed_zero_effects as zero
import owner_graph_profile as graph
import rom_table_copy_profile as rom_copy
import scheduler_zero_descriptor as installer
from sdk_cpuset_halfword import TOKEN, base_header
from software_double_profile import indices, span_record

SELECTOR = 'conditional-packed-transfer-task-v1'
SCHEMA = 'elf-symbol-thumb-' + SELECTOR
CONTROL_FLOW = 'complete transfer task callback with a conditional bounded packed-record copy and installed clear'
OWNER = 0x08005EF8
END = 0x08005FC4
COPY = 0x081443FC
SOURCE = 'src/08005EF8.c'
SOURCE_TOKENS = '627b782fcee5cf07ab871e4c4cd18eb2c771cf450456a6d193815b49912283d4'
OWNER_SHA = '70fc1af6b37822811745b4ebaf478769b3eccd55f9b990d6b7ba530d388fd678'
TABLE = 'g_callbacks_0836D4B8'
CALLS = ((0x3A, 'memcpy', COPY), (0x50, 'func_08005B28', 0x08005B28),
         (0x5E, 'func_08005B40', 0x08005B40), (0x96, 'func_08005C54', 0x08005C54),
         (0x9E, 'func_08005E7C', 0x08005E7C), (0xBA, '_call_via_r2', 0x0814224C))
# Providers reached by the constructor, heap, record handlers and scheduler.
PROVIDERS = (
    (0x08006878, 0x080068AC, '4d0a5fb1e3d398787b7035080b6f48e46d0e96cef0dab67c1e5ffcaf563bd106'),
    (0x08005B6C, 0x08005BA8, 'c6a20896e48a2d20f9a4e9d59b780095f5e082b65619a2a96cee0ebc26e8c475'),
    (0x08005954, 0x08005A22, '4e3fba4f8cb6ee77b2d0251866e2f85338ab5550832ce8fc0807b3835b0c677e'),
    (0x08005A24, 0x08005AFE, '92a60c7b7568e688bda0434c5efc4945c67b84c3d73a03bb7f2a51fdb5f99187'),
    (0x080058A4, 0x08005954, '166de15e21ac827dafd7511f418ab5e381d7d8d9b47925ed4372e1ba53ca4072'),
    (0x08005B28, 0x08005B40, 'ba04646db5270381ed1163725929afbf1af7d9702d082ec8b0c891ed2d56b3f3'),
    (0x08005B40, 0x08005B58, 'a7a21da660f85430985b854170b0379f3bc57f12fcee59a5df253093ba8a8bba'),
    (0x08005C54, 0x08005E7A, '31a747d5b87d24da832d609ee4acd5f0d9f816e347b6d0b4e5e50f446e7b21ab'),
    (0x08005E7C, 0x08005EF8, '6f396214c8ed286c45ab3d9d9d9b9e57785e1a6704c49b01a243f25ad0fec60c'),
    (0x08000ADC, 0x08000B20, 'a0d59e7af9a5bf324952c2546626f0aac87402155dc7dc986253afc170a68a07'),
    (0x08000B68, 0x08000BAC, '3dc94dda87897cb7b40168e4c5882b16b9d76731afae1d5eb748c4781de56961'),
    (0x0814224C, 0x0814224E, 'dd9261f0471768edc33bf979649f6297463be423da17c3f881684f5747e163a1'),
    (0x08142250, 0x08142252, '477db9ac7ca5efc12e37f882656b8fe5a363ffeb99b2e565a953d10c3c91ab21'),
    (0x08007138, 0x0800716E, '41bb84543d24c53f9292d190bc5e895370602a394d7b1db5169b21fcfa6f027f'),
    (0x08006EC0, 0x08006FCA, 'ce1efcfe278bbb02f1e96f0943f5be3fa8feef032f2bb456893e67bbd3b33b00'),
    (0x08007170, 0x0800717C, 'd4c4ef6651a1e11e3311b32b146dfc880c9fe0518ba2b55a0c274b892ef066a3'),
    (0x08006C88, 0x08006D36, '7753b4551e4d959c458be6fb052231a28bdd00592aa2a47c75f066aeb2de5dd5'),
    (0x08006DA0, 0x08006E26, '52ccddd712513cc0c943490a0be055ad763ddc048fcd42af45a2e191bbb86384'),
    (0x08006E28, 0x08006EBE, 'd7d37063b367add1fa0a31c1c1f7f89482d89a4168b56c001ac521d53dba530b'),
    (0x08006FCC, 0x080070C8, '1c178b498423212776ef0bf27836958dee9899b97b44059e586aa70bbf414d26'),
    (0x08006D38, 0x08006D9E, 'ebb75817e6e49a104d4d7562559c89ddc557fad028fc27e7b58bb62aa017566b'),
)

RECORD_BYTES = 12
PAYLOAD_HEADER = 0x34
TASK_PAYLOAD = 0x18
MAX_COUNT = (0xFFFF - 0x40 - 0x1C) // RECORD_BYTES


def require(condition, message):
    if not condition:
        raise ValueError('packed transfer task: ' + message)


def check_source(root, address):
    """Keep the source-side distinction between struct assignment and an explicit call."""
    import plausible

    require(address == OWNER, 'unexpected owner')
    text = (Path(root) / SOURCE).read_text()
    require(not any(marker in text for marker in ('\\', '??', '%:', '\0')) and
            base_header((Path(root) / 'include/ffta.h').read_bytes(), ('func_08005EF8', 'memcpy')),
            'unexpected header or preprocessing tokens')
    tokens = TOKEN.findall(plausible.strip_comments_and_strings_keep_strings(text))
    require(sha256(' '.join(tokens).encode()).hexdigest() == SOURCE_TOKENS,
            'expected the reviewed packed entry assignment and callback ABI')


def allocation(count):
    """Sizes seen at each actual narrowing, with exclusive end relative to the task."""
    require(type(count) is int and 0 <= count <= 0xFFFF, 'expected a u16 count')
    payload = (RECORD_BYTES * count + 0x40) & 0xFFFF
    allocated = (payload + 0x1C) & 0xFFFF
    records_end = TASK_PAYLOAD + PAYLOAD_HEADER + RECORD_BYTES * count
    return payload, allocated, records_end


def count_domain(rom):
    # Decode the two actual shift/add chains. The constructor retains the incoming
    # low halfword separately in its descriptor; the scheduler narrows the size again.
    sequences = ((0x6880, '2404240c610009198904'), (0x6892, '8022d2038918090c'),
                 (0x5968, '2404e02040032418240c'))
    for offset, encoding in sequences:
        body = bytes.fromhex(encoding)
        require(rom[offset:offset + len(body)] == body, 'changed original size calculation')
    for n in range(0x10000):
        r1 = (((n << 1) + n) << 18) & 0xFFFFFFFF
        r1 = ((r1 + (0x80 << 15)) & 0xFFFFFFFF) >> 16
        r4 = (((r1 << 16) + (0xE0 << 13)) & 0xFFFFFFFF) >> 16
        payload, allocated, end = allocation(n)
        require((r1, r4) == (payload, allocated) and
                (allocated >= end) == (n <= MAX_COUNT), 'invalid unsigned count partition')
    return dict(counts_checked=0x10000, max_count=MAX_COUNT,
                constructor_size='(12 * count + 64) mod 65536',
                scheduler_allocation='(constructor_size + 28) mod 65536',
                last_valid_sizes=allocation(MAX_COUNT), next_sizes=allocation(MAX_COUNT + 1))


def bindings():
    return dict(calls=[[site, name] for site, name, _ in CALLS], data=[[END - OWNER - 4, TABLE, 0]],
                functions=[], switches=[])


def original_target(image, address, site, target):
    require(address == OWNER and site == CALLS[0][0] and target['name'] == 'memcpy' and
            (target['section'], target['value'], target['size'], target['bind']) == (0, 0, 0, 1) and
            target['type'] in (0, 2) and sum(row['name'] == 'memcpy' for row in image['symbols']) == 1,
            'expected the unique compiler memcpy relocation at the record assignment')
    return COPY


def check_original(original, targets, image):
    expected = {name: (dest, False) for _, name, dest in CALLS}
    expected[TABLE] = (installer.POINTER, True)
    require(original == bindings() and targets == expected and
            all(row['size'] == 0 for row in image['symbols'] if row['name'] in expected),
            'unexpected relocation type, call identity or named callback table')


def prove(data, address, rom, mapping, index, objects, original, ins, calls, refinement, words):
    import match

    require(address == OWNER and len(data) == END - OWNER and sha256(data).hexdigest() == OWNER_SHA,
            'changed transfer callback')
    require(original == bindings() and calls == {OWNER + site: dest for site, _, dest in CALLS} and
            match.parse_data_symbols(objects).get(TABLE) == installer.POINTER, 'changed calls or callback table')
    require({item.address for item in match.verify_leaf_instructions(data, address, True, validated_calls=calls)}
            == set(ins) and len(ins) == 93, 'complete restoring Thumb frame required')

    entries, rows = indices(mapping, index)
    for start, end, digest in PROVIDERS:
        row = span_record(start, end, entries, rows, rom)
        if start in (0x08006878, 0x08005954):
            require(row['instrs'] == {0x08006878: 23, 0x08005954: 97}[start], 'stale scheduler extent count')
        require(sha256(rom[start - match.ROM_BASE:end - match.ROM_BASE]).hexdigest() == digest,
                f'changed native provider at {start:08X}')
    require(rom[0x36D490:0x36D498] == bytes(0x80 >> bit for bit in range(8)),
            'changed source-bit decoding table')
    helper = rom_copy.helper_facts(rom, mapping, index)
    copy = copy_effects.contract(rom[COPY - match.ROM_BASE:COPY - match.ROM_BASE + 98], RECORD_BYTES)
    plan = installer.initializer(rom, mapping, index)
    installed = rom[installer.IMAGE - match.ROM_BASE:installer.IMAGE - match.ROM_BASE + 176]
    clears = zero.verify_conditional(installed, installer.DESTINATION, installer.DESTINATION,
                                     RECORD_BYTES, selector=zero.SELECTOR)
    aligned = clears['cases'][0]
    require(aligned['alignment'] == 0 and aligned['writes'] ==
            [('stack', -4, 4), ('destination', 0, 4), ('destination', 4, 4), ('destination', 8, 4)] and
            aligned['protected_return'] and aligned['SP_restored'], 'changed progress clear')

    # In 06878 and 05954 the native shifts narrow first the constructor size, then that
    # size plus the scheduler header. The allocation and installed word clear receive
    # the same multiple of four. The aligned installed loop stores at +4*i, subtracts
    # four and repeats while more than three bytes remain; it finishes with no tail.
    require(struct.unpack_from('<5H', installed, 0x16) == (0xC201, 0x3904, 0x2903, 0xD8FB, 0x2900),
            'changed aligned installed word loop')
    counts = count_domain(rom)

    return dict(schema=SCHEMA, instructions=len(ins), calls=bindings()['calls'], runtime_calls=[],
        partition=graph.partition(data, address, refinement, ins, words),
        packed_transfer=dict(source_tokens=SOURCE_TOKENS, providers=PROVIDERS, copy_helper=helper,
            copy_effects=copy, installer=plan['copy_plan'], installed_sha256=plan['image_sha256'],
            progress_clear=aligned, constructor_payload_offset=TASK_PAYLOAD, first_record=PAYLOAD_HEADER,
            stride=RECORD_BYTES, count_domain=counts, production_counts_proved=False,
            allocation_success_proved=False, unknown_kind_advances=False,
            missing_task_allocation='Scheduler uses the returned pointer without a null guard.',
            missing_transfer_buffer='Phase zero stores the second result. Buffer-using steps require a live buffer.',
            phases={'0': 'Copy count complete 12-byte records, then allocate 2048 bytes.',
                    '256': 'End sets phase 2. Kinds 0 and 15 call their native step. A completed step '
                           'increments current and clears twelve bytes of progress. Other kinds stay pending.',
                    '1': 'Release nonnull transfer buffer and clear its pointer.'},
            conditions=['Completed initial installation, unchanged callback slot and resident code.',
                        'Valid scheduler context, sufficient heap and successful allocations, valid list links.',
                        'Task, stack and register-save areas have the required ABI alignment. Task and source are '
                        'live disjoint objects for the count; their ranges do not wrap '
                        'or overlap active frames. The descriptor is stable while copied.',
                        'Original record data, queue and transfer buffers obey the native step interfaces; '
                        'pending requests are consumed before the same embedded queue node is reused or freed.',
                        'Actual callee ABI and IRQ lifetime preserved; original callers, hardware completion '
                        'and termination are not established.']))
