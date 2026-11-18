"""Phase-one transfer task teardown in the generic scheduler's postorder walk."""
from hashlib import sha256
from pathlib import Path
import struct

import match
import owner_graph_profile as graph
import packed_transfer_task as transfer
from ability_range_local_bytes import block, require
from sdk_cpuset_halfword import TOKEN, base_header
from software_double_profile import indices, span_record

SELECTOR = 'conditional-transfer-tree-destruction-v1'
SCHEMA = 'elf-symbol-thumb-' + SELECTOR
CONTROL_FLOW = ('complete dynamic scheduler destructor with a reviewed phase-one transfer-task path; '
                'other registered callbacks require returning ABI and ownership premises')
OWNER, END = 0x080058A4, 0x08005954
SENTINEL, SENTINEL_WORD = 0x0202BA50, 0xAC
EVENT_BYTES = 28
SOURCE_TOKENS = '692902c365310e40224155fb9ce13276386b7f6791ac4c547ab688fbac1fc13f'
BINDINGS = dict(calls=[[0x3C, '_call_via_r3'], [0x9C, 'func_08007170']],
                data=[], functions=[], switches=[])
TARGETS = {'_call_via_r3': (0x08142250, False), 'func_08007170': (0x08007170, False)}

# Reuse the registered constructor, transfer callback's heap and scheduler identities.
EXTRA = ((0x08005B58, 0x08005B6C, 'a35add21d3068d5ef1fce128f82d09d97ea89ecd73c01d52fe87de8d8436c58e'),
         (transfer.OWNER, transfer.END, transfer.OWNER_SHA))
PROVIDERS = transfer.PROVIDERS + EXTRA


def check_source(root, address):
    import plausible

    require(address == OWNER, 'unexpected scheduler destructor')
    root = Path(root)
    source = (root / 'src/080058A4.c').read_text()
    require(base_header((root / 'include/ffta.h').read_bytes(), ('func_080058A4', 'func_08007170')) and
            not any(marker in source for marker in ('\\', '??', '%:', '\0')), 'changed C input closure')
    tokens = TOKEN.findall(plausible.strip_comments_and_strings_keep_strings(source))
    require(sha256(' '.join(tokens).encode()).hexdigest() == SOURCE_TOKENS,
            'expected the reviewed callback ABI, phase-only initialization and genuine address comparison')


def check_bindings(bindings, targets, image):
    require(bindings == BINDINGS and targets == TARGETS, 'wrong destructor call or data relocation')
    require(all(symbol['size'] == 0 for symbol in image['symbols'] if symbol['name'] in TARGETS),
            'unexpected sized callee symbol')


def provider_ins(rom, start, end):
    decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
    return {item.address: item for item in decoder.disasm(rom[start-match.ROM_BASE:end-match.ROM_BASE], start)}


def prove(data, address, rom, mapping, index, bindings, ins, edges, calls, refinement, words):
    require(address == OWNER and len(data) == END-OWNER and bindings == BINDINGS,
            'changed transfer-tree owner or original relocations')
    require(calls == {OWNER + site: TARGETS[name][0] for site, name in BINDINGS['calls']}
            and len(ins) == 84 and not words, 'changed destructor call inventory or CFG')
    require(set(ins) == set(range(OWNER, OWNER + 0xAC, 2)) - {0x080058E2, 0x08005942} and
            [pc for pc, item in ins.items() if item.mnemonic == 'bx'] == [0x0800594E],
            'expected the complete single-return frame described below')
    entries, rows = indices(mapping, index)
    for start, end, digest in PROVIDERS:
        span_record(start, end, entries, rows, rom)
        require(sha256(rom[start-match.ROM_BASE:end-match.ROM_BASE]).hexdigest() == digest,
                f'changed native scheduler or transfer provider at {start:08X}')

    # The local is assigned only once and kept across every destruction callback.
    block(ins, OWNER, 'push {r4, r5, r6, r7, lr}', 'sub sp, #0x1c', 'adds r6, r0, #0', 'adds r7, r1, #0',
          'mov r1, sp', 'movs r0, #1', 'strh r0, [r1]', 'adds r5, r7, #0', 'cmp r5, #0', 'beq #0x8005948')
    block(ins, 0x080058B8, 'ldr r1, [r5, #0x10]', 'cmp r1, #0', 'beq #0x80058ce', 'ldr r0, [r1, #8]',
          'cmp r0, #0', 'bne #0x80058ca', 'ldr r0, [r1, #0x10]', 'cmp r0, #0', 'beq #0x80058ce',
          'adds r1, r0, #0', 'b #0x80058be', 'adds r4, r1, #0', 'cmp r4, #0', 'bne #0x80058d6',
          'adds r4, r5, #0', 'adds r2, r4, #0', 'adds r2, #0x18', 'ldr r3, [r4]', 'adds r0, r4, #0',
          'mov r1, sp', 'bl #0x8142250')
    block(ins, 0x080058E4, 'cmp r4, r7', 'bne #0x80058ee', 'movs r5, #0', 'ldr r1, [r4, #4]', 'b #0x80058f8',
          'ldr r5, [r4, #4]', 'adds r1, r5, #0', 'cmp r5, #0', 'bne #0x80058f8', 'ldr r5, [r4, #0xc]',
          'cmp r1, #0', 'beq #0x8005900', 'ldr r0, [r4, #8]', 'str r0, [r1, #8]',
          'ldr r1, [r4, #8]', 'cmp r1, #0', 'beq #0x800590a', 'ldr r0, [r4, #4]', 'str r0, [r1, #4]',
          'ldr r1, [r4, #0xc]', 'cmp r1, #0', 'beq #0x800591a', 'ldr r0, [r1, #0x10]', 'cmp r0, r4',
          'bne #0x800591a', 'ldr r0, [r4, #8]', 'str r0, [r1, #0x10]', 'ldr r0, [r6, #4]', 'cmp r0, r4',
          'bne #0x8005924', 'ldr r0, [r4, #8]', 'str r0, [r6, #4]', 'movs r0, #0',
          'str r0, [r4, #0xc]', 'str r0, [r4, #8]', 'str r0, [r4, #4]')
    partition = graph.partition(data, address, refinement, ins, words)
    require(partition['words'] == [dict(address=OWNER+SENTINEL_WORD, value=SENTINEL,
            load_sites=[0x0800592C], switch_word=False)], 'wrong comparison-only address')
    block(ins, 0x0800592C, 'ldr r0, [pc, #0x20]', 'ldr r1, [r6]', 'cmp r4, r0', 'bne #0x800593c',
          'movs r0, #3', 'subs r0, #1', 'cmp r0, #0', 'bge #0x8005936', 'adds r0, r1, #0',
          'adds r1, r4, #0', 'bl #0x8007170', 'cmp r5, #0', 'bne #0x80058b8', 'add sp, #0x1c',
          'pop {r4, r5, r6, r7}', 'pop {r0}', 'bx r0')

    # The reviewed constructor supplies the callback address from its own literal. The scheduler
    # installs R1 as the node's callback, and the public destruction wrapper loads its manager.
    require(struct.unpack_from('<I', rom, 0x68A8)[0] == (transfer.OWNER | 1) and
            struct.unpack_from('<I', rom, 0x5B68)[0] == 0x02008FF0 and
            struct.unpack_from('<I', rom, 0x5B54)[0] == 0x02008FF0 and
            rom[0x142250:0x142252] == b'\x18\x47', 'changed callback, global manager or BX r3')
    constructor = provider_ins(rom, 0x08006878, 0x080068A8)
    block(constructor, 0x08006890, 'ldr r0, [pc, #0x14]', 'movs r2, #0x80', 'lsls r2, r2, #0xf',
          'adds r1, r1, r2', 'lsrs r1, r1, #0x10', 'mov r2, sp', 'bl #0x8005b6c')
    wrapper = provider_ins(rom, 0x08005B6C, 0x08005BA0)
    block(wrapper, 0x08005B74, 'adds r6, r0, #0', 'adds r4, r1, #0', 'mov r8, r2',
          'lsls r4, r4, #0x10', 'lsrs r4, r4, #0x10', 'ldr r5, [pc, #0x24]', 'ldr r0, [r5]',
          'str r3, [sp]', 'adds r1, r6, #0', 'adds r2, r4, #0', 'mov r3, r8', 'bl #0x8005954')
    require(struct.unpack_from('<I', rom, 0x5BA4)[0] == 0x02008FF0, 'changed constructor global manager')
    scheduler = provider_ins(rom, END, 0x080059B8)
    block(scheduler, 0x08005960, 'mov r8, r1')
    block(scheduler, 0x08005988, 'mov r3, r8', 'str r3, [r7]')
    phase = provider_ins(rom, transfer.OWNER, 0x08005FBE)
    block(phase, transfer.OWNER, 'push {r4, r5, r6, lr}', 'adds r5, r2, #0', 'ldrh r2, [r1]',
          'cmp r2, #1', 'beq #0x8005f50')
    block(phase, 0x08005F50, 'ldr r0, [r5, #8]', 'cmp r0, #0', 'beq #0x8005fb6', 'bl #0x8005b40',
          'movs r0, #0', 'str r0, [r5, #8]', 'b #0x8005fb6')
    block(phase, 0x08005FB6, 'movs r0, #0', 'pop {r4, r5, r6}', 'pop {r1}', 'bx r1')
    release = provider_ins(rom, 0x08005B40, 0x08005B52)
    block(release, 0x08005B40, 'push {lr}', 'adds r1, r0, #0', 'ldr r0, [pc, #0xc]',
          'ldr r0, [r0]', 'ldr r0, [r0]', 'bl #0x8007170', 'pop {r0}', 'bx r0')
    return dict(schema=SCHEMA, instructions=len(ins), calls=BINDINGS['calls'], runtime_calls=[], partition=partition,
        transfer_tree=dict(compared_address_word=SENTINEL_WORD, compared_address=SENTINEL,
            compared_address_access='compare only; countdown 3,2,1,0; heap argument reloaded on either path',
            event_bytes=EVENT_BYTES, initialized_event_bytes=[0,1], descriptor_read_offsets=[[0,2]],
            callback_load='node->callback, dynamically reloaded at 080058DA; BX r3',
            transfer_count_domain=transfer.count_domain(rom), reviewed_callback=transfer.OWNER, reviewed_constructor=0x08006878, destruction_wrapper=0x08005B58,
            callback_arguments=['node', 'live phase-one event', 'node+24'],
            phase_one='Reads the phase halfword only; if payload+8 is nonnull, frees that buffer with the '
                      'global manager heap and clears the field. Both returns replace R1 with saved LR.',
            cleanup='Prefer next sibling then child; invoke callback; use previous sibling, otherwise parent, '
                    'as continuation; repair reciprocal sibling links and parent or manager head; '
                    'clear parent/next/previous; free node on owner heap; stop after requested root.',
            empty_root='No callback or heap operation; R1 may carry the expired event address on void return. '
                       'No caller-saved register result is promised.',
            reviewed_domain='Finite, well-formed, stable task forest with valid prior/next/parent/child links; '
                'each node allocated by the supplied manager with successful task allocation, valid source entries, '
                'and a transfer count in the established nonwrapping range. '
                'Each reviewed transfer buffer is null or a distinct live allocation on the global manager heap. '
                'Both heaps and their live blocks are writable and disjoint from all live frames.',
            external_callbacks='Other registered targets are not identified or verified. They must be valid '
                'returning ARM ABI callbacks, preserve the traversal links and live nodes, use only the '
                'initialized event phase, keep it at one and never retain its address. Callback and heap '
                'routines must preserve callee-saved state and respect allocation ownership.',
            arbitrary_callback_effects_proved=False, allocator_invariants_proved=False,
            providers=PROVIDERS, verifier_sha256=sha256(Path(__file__).read_bytes()).hexdigest()))
