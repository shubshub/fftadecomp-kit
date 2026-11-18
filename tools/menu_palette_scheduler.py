"""The menu constructor's installed palette copy and synchronous scheduler callbacks."""
import copy
import hashlib
from pathlib import Path
import struct


SELECTOR = 'conditional-menu-palette-scheduler-v1'
SCHEMA = 'elf-symbol-thumb-' + SELECTOR
CONTROL_FLOW = ('original menu constructor, conditionally installed two-byte palette copy and '
                'synchronous scheduler phase zero under returning ABI and separate valid storage')
OWNER = 0x080253B0
SCHEDULER = 0x08005954
SPECIAL = 0x08028FF4
NORMAL = 0x08028DE0
SETUP = 0x08022B24
GETTER = 0x080CBA84
THUNK = 0x08142250
COPY_SITE = OWNER + 0x52
SETUP_SITE = OWNER + 0x3A
POINTER = 0x0836D4BC
DEST = 0x030039F8
PALETTES = (0x08419F60, 0x0841AA60)
CALLS = {OWNER + 0x24: SCHEDULER, SETUP_SITE: SETUP, OWNER + 0x44: GETTER,
         COPY_SITE: THUNK, OWNER + 0x62: SCHEDULER}
BINDINGS = dict(calls=[[pc-OWNER, '_call_via_r3' if target == THUNK else f'func_{target:08X}']
                       for pc, target in CALLS.items()],
                functions=[[0x30, 'func_08028FF4'], [0x78, 'func_08028DE0']],
                data=[[0x2C, 'data_0200F438', 0], [0x70, 'data_0836D4BC', 0],
                      [0x74, 'data_030039F8', 0]], switches=[])
# Each body must occupy its complete, non-overlapping span in both original indexes.
BODIES = {
    OWNER: (124, '0ab029a36a3f0e1aa56793c4a0218a9f113889571c9a22b8b3f319c9da5f8e42'),
    SCHEDULER: (206, '4e3fba4f8cb6ee77b2d0251866e2f85338ab5550832ce8fc0807b3835b0c677e'),
    SPECIAL: (404, '4e5c9850fa9ee399da40f8326cc53de75c8488b8a35a4b4264ccf318ea6784ac'),
    NORMAL: (532, 'a833c05805a95d06dd03f21941030f4c5b6dcc0cee36e0e8bb282288dc28f144'),
    0x08005BF8: (4, 'd19fad8501266b846fb3ccebe743c2dbfc819ce1d06e3660d17a537a9eb0439f'),
    SETUP: (126, 'd8b084cb94fed05da4a9738bbf8d8f46473d23fdd4c72a2afb0df6783cc9692b'),
    0x0801D880: (16, 'a8acf386f60d2fae037ff619e9b0be321c993448b423e258e43cc8a894897450'),
    GETTER: (56, '978a7d0ad9fc232a36c93f715fb762ddf9baa37a82f9bbed08f7e511042276e3'),
}


def require(ok, message):
    if not ok:
        raise ValueError('menu palette scheduler: ' + message)


def check_bindings(bindings):
    require(bindings == BINDINGS, 'wrong call, object, addend or callback relocation')


def check_linked(image, targets):
    for table, symbols in image['symbol_tables'].items():
        for n, row in enumerate(symbols):
            if row['name'] in targets:
                require(image['section_data'][table][n*16+13] == 0, 'nondefault linked symbol visibility')


def palette_copy(proof):
    import iwram_installation_prerequisite as install
    import installed_copy_effects as installed_copy
    import scheduler_zero_descriptor as zero

    rom = proof.rom
    for begin, end, digest in zero.BOOT:
        require(hashlib.sha256(rom[begin-install.ROM_BASE:end-install.ROM_BASE]).hexdigest() == digest,
                'boot installation path changed')
    plan = install.verify(rom[0x2768:0x27B8], 0x08002768, rom, proof.mapping, proof.index,
                          selector=install.SELECTOR, call_site=0x08002796, pointer_address=POINTER)
    image = bytes.fromhex(plan['source_image']['bytes'])
    require(plan['arguments'] == dict(source=zero.IMAGE, destination=zero.DESTINATION, control=88)
            and plan['copy_plan']['width'] == 2 and plan['copy_plan']['bytes'] == 176
            and plan['entry']['pointer_word'] == 0x03005EE9 and plan['entry']['source_address'] == 0x08A38A9C
            and plan['source_image']['sha256'] == zero.IMAGE_SHA256
            and proof.span(0x08A38A9C) == image[0x70:0xAE], 'wrong installed image or copy entry')
    effects = installed_copy.verify_conditional(image, zero.DESTINATION, 0x03005EE8, 2,
                                                selector=installed_copy.SELECTOR)
    case = effects['cases'][0]
    require(case['reads'] == [('source', 0, 1), ('source', 1, 1), ('stack', -8, 4), ('stack', -4, 4)]
            and case['writes'] == [('stack', -8, 4), ('stack', -4, 4), ('destination', 0, 1),
                                   ('destination', 1, 1)] and case['protected_return'] and case['SP_restored'],
            'wrong two-byte installed copy footprint')
    sources = [base + 12*32 + 24 for base in PALETTES]
    content = [rom[p-install.ROM_BASE:p-install.ROM_BASE+2].hex() for p in sources]
    require(content == ['f526', '0f26'], 'palette source words differ')
    return dict(site=COPY_SITE, selector_word=POINTER, boot=zero.BOOT, install_site=plan['call_site'],
                plan=plan['copy_plan'], entry=plan['entry'], image_sha256=effects['image_sha256'],
                palette_sources=sources, palette_bytes=content, destination=DEST, count=2, aligned_case=case,
                assumptions=effects['unproved_premises'], installed_identity_proved=False)


def phase_zero(proof):
    import scheduler_descriptor_lifetime as lifetime
    from scheduler_event_definition import check_payload_argument, sequence

    core = proof.span(SCHEDULER)
    require(core[:34] == lifetime.CALLEE_HEAD and core[154:180] == lifetime.COPY + lifetime.CALL_SETUP
            and core[184:] == lifetime.CALLEE_RETURN and proof.span(THUNK) == bytes.fromhex('1847'),
            'scheduler prefix, seven-word copy, phase overwrite, callback or cleanup changed')
    sequence(core, SCHEDULER, SCHEDULER+180, ['bl #0x8142250'])
    check_payload_argument(core, proof.mapping)
    normal = proof.span(NORMAL)
    sequence(normal, NORMAL, NORMAL, ['push {r4, r5, r6, lr}', 'adds r5, r1, #0', 'adds r4, r2, #0',
            'ldrh r1, [r5]', 'ldr r6, [pc, #0x18]', 'cmp r1, r6', 'beq #0x8028edc', 'cmp r1, r6',
            'bgt #0x8028e1c', 'movs r2, #0x80', 'lsls r2, r2, #1', 'cmp r1, r2', 'beq #0x8028e5e',
            'cmp r1, r2', 'bgt #0x8028e08', 'cmp r1, #0', 'beq #0x8028e50'])
    require(struct.unpack_from('<I', normal, 0x24)[0] == 0x103, 'first navigation phase changed')
    sequence(normal, NORMAL, 0x08028E50, ['str r0, [r4]', 'bl #0x8005bf8', 'str r0, [r4, #4]',
            'ldrh r0, [r5, #0x14]', 'strb r0, [r4, #8]', 'b #0x8028fe8'])
    sequence(proof.span(0x08005BF8), 0x08005BF8, 0x08005BF8, ['ldr r0, [r0, #0xc]', 'bx lr'])
    special = proof.span(SPECIAL)
    sequence(special, SPECIAL, SPECIAL, ['push {r4, r5, r6, lr}', 'adds r5, r1, #0', 'ldrh r1, [r5]',
            'cmp r1, #1', 'bne #0x8029000', 'b #0x802917c', 'cmp r1, #1', 'bgt #0x802900a',
            'cmp r1, #0', 'beq #0x802901c'])
    stores = ['ldr r2, [pc, #0x40]', 'ldr r0, [r2]', 'movs r1, #0x90',
              'lsls r1, r1, #3', 'adds r0, r0, r1', 'movs r1, #1', 'strb r1, [r0]']
    for value, literal in enumerate((0x34, 0x30, 0x28, 0x24, 0x1C), 2):
        reg = 'r2' if value == 6 else 'r1'
        stores.extend(['ldr r0, [r2]', f'ldr {reg}, [pc, #{hex(literal)}]', f'adds r0, r0, {reg}',
                       f'movs r1, #{value}', 'strb r1, [r0]'])
    sequence(special, SPECIAL, 0x0802901C, stores + ['b #0x802917c'])
    require(struct.unpack_from('<6I', special, 0x6C) == (0x0200F438, *range(0x481, 0x486)),
            'wrong menu order table or field offsets')
    epilogue = ['movs r0, #0', 'pop {r4, r5, r6}', 'pop {r1}', 'bx r1']
    sequence(special, SPECIAL, 0x0802917C, epilogue)
    sequence(normal, NORMAL, 0x08028FE8, epilogue)
    return dict(copy_bytes=28, phase_store=SCHEDULER+174, callback_site=SCHEDULER+180, phase=0,
                allocated_payload_offset=24, requested_payload_bytes=164,
                paths=[dict(site=OWNER+0x24, mode='17', callback=SPECIAL, caller_initialized=[],
                            copied_descriptor_reads=[[0, 2]], order_offsets=list(range(0x480, 0x486)),
                            order_values=list(range(1, 7))),
                       dict(site=OWNER+0x62, mode='other u8', callback=NORMAL, caller_initialized=[[20, 2]],
                            copied_descriptor_reads=[[0, 2], [20, 2]], argument='(u16)(mode - 1)',
                            payload_writes=[[0, 4, 'task'], [4, 4, 'task parent'], [8, 1, 'low argument byte']])],
                copied_phase_initialized_by_scheduler=[0, 2], opaque_bytes_observed_by_phase_zero=False,
                later_callback_phases_proved=False)


def bind(proof, data, address, ins, edges, calls):
    from active_entry_shuffle_profile import exact_edges
    from effect_scheduler_initializer import block
    from scheduler_event_definition import sequence
    from software_double_profile import indices, span_record

    require(address == OWNER and len(ins) == 45 and calls == CALLS, 'wrong constructor or direct calls')
    entries, rows = indices(proof.mapping, proof.index)
    require(span_record(OWNER, OWNER+len(data), entries, rows, proof.rom)['instrs'] == len(ins),
            'wrong paired owner instruction counts')
    for pc, (size, digest) in BODIES.items():
        body = proof.span(pc)
        require(len(body) == size and hashlib.sha256(body).hexdigest() == digest, f'original indexed body changed at {pc:08X}')
    require(data == proof.span(OWNER), 'owner body differs from the original ROM')
    exact_edges(ins, edges, OWNER, {0x18: (0x1A, 0x34), 0x28: (0x66,), 0x6C: ()})
    require(struct.unpack_from('<II', data, 0x2C) == (0x0200F438, SPECIAL | 1)
            and struct.unpack_from('<III', data, 0x70) == (POINTER, DEST, NORMAL | 1),
            'wrong data, palette destination or callback literals')
    block(ins, OWNER, 'push {r4, r5, r6, r7, lr}', 'sub sp, #0x20', 'adds r7, r1, #0',
          'lsls r0, r0, #0x18', 'lsrs r2, r0, #0x18', 'ldr r6, [pc, #0x20]', 'ldr r0, [r6]',
          'movs r1, #0', 'strb r2, [r0, #4]', 'ldr r0, [r6]')
    block(ins, OWNER+0x14, 'strh r1, [r0]', 'cmp r2, #0x11', 'bne #0x80253e4',
          'ldr r0, [r0, #0x20]', 'ldr r1, [pc, #0x10]', 'str r7, [sp]', 'movs r2, #0xa4',
          'add r3, sp, #4', 'bl #0x8005954', 'b #0x8025416')
    block(ins, OWNER+0x34, 'add r1, sp, #4', 'subs r0, r2, #1', 'strh r0, [r1, #0x14]',
          'bl #0x8022b24', 'ldr r4, [pc, #0x30]', 'ldr r5, [pc, #0x30]', 'movs r0, #0xc',
          'bl #0x80cba84', 'adds r1, r0, #0', 'adds r1, #0x18', 'ldr r3, [r4]', 'adds r0, r5, #0',
          'movs r2, #2', 'bl #0x8142250', 'ldr r0, [r6]', 'ldr r0, [r0, #0x20]',
          'ldr r1, [pc, #0x1c]', 'str r7, [sp]', 'movs r2, #0xa4', 'add r3, sp, #4', 'bl #0x8005954')
    # The setup inherits R1=&descriptor. Its immediate leaf overwrites R1 before a use.
    sequence(proof.span(SETUP), SETUP, SETUP, ['push {lr}', 'bl #0x801d880'])
    sequence(proof.span(0x0801D880), 0x0801D880, 0x0801D880,
             ['ldr r0, [pc, #8]', 'movs r1, #0x8a', 'lsls r1, r1, #2', 'adds r0, r0, r1',
              'ldrb r0, [r0]', 'bx lr'])
    getter = proof.span(GETTER)
    sequence(getter, GETTER, GETTER, ['push {lr}', 'lsls r0, r0, #0x18', 'lsrs r1, r0, #0x18',
             'ldr r0, [pc, #0x14]', 'ldr r2, [pc, #0x14]', 'adds r0, r0, r2', 'ldrb r0, [r0]',
             'lsls r0, r0, #0x1e', 'lsrs r0, r0, #0x1e', 'cmp r0, #2', 'beq #0x80cbaac',
             'lsls r0, r1, #5', 'ldr r1, [pc, #8]', 'b #0x80cbab0'])
    sequence(getter, GETTER, 0x080CBAAC, ['lsls r0, r1, #5', 'ldr r1, [pc, #8]',
             'adds r0, r0, r1', 'pop {r1}', 'bx r1'])
    require(struct.unpack_from('<III', getter, 0x1C) == (0x02000000, 0x2FC2, PALETTES[0])
            and struct.unpack_from('<I', getter, 0x34)[0] == PALETTES[1],
            'wrong palette mode selector or physical table')
    proof.menu_checked_sites = set()
    proof.menu_copy = palette_copy(proof)
    proof.menu_phase = phase_zero(proof)
    # The manager base in R6 reaches across the installed call. Give the genuine
    # validated BL to the reaching-definition walk so it enforces its preserved ABI.
    import match
    import scheduler_call_site_profile as scheduler
    sites = []
    for site in (OWNER+0x24, OWNER+0x62):
        offsets = scheduler.callback_literals(data, address, ins, edges, calls, site, match.ARM_REG_R1)
        chains = scheduler.manager_chains(data, address, ins, edges, calls, site)
        sites.append(dict(site=site, target=SCHEDULER, scheduler_entry='direct-entry', callback_register=1,
                          descriptor_register=3, callback_literal_offsets=offsets, looped=False,
                          manager_chains=chains))
    return dict(sites=sites, looped_sites=[], dependencies=[SCHEDULER],
                source_sha256=hashlib.sha256(Path(scheduler.__file__).read_bytes()).hexdigest())


def check_indirect(proof, site, address, aliases, returns):
    import match
    require(site == COPY_SITE and proof.calls.get(site) == address == THUNK and
            match.ARM_REG_R3 not in aliases and not set(returns) & (set(match.CALLER_CLOBBERED)-{match.ARM_REG_LR}),
            'unexpected indirect target or frame provenance')


def check_call(proof, site, aliases, stack, slots, constants):
    import match
    require(len(stack)*4 == 52 and not slots, 'expected private local descriptor and external parent')
    if site == SETUP_SITE:
        require(aliases == {match.ARM_REG_R1: -48}, 'setup must discard precisely the incoming descriptor in R1')
    else:
        require(site == COPY_SITE and not aliases and (constants or {}).get(match.ARM_REG_R2) == 2,
                'installed copy requires two bytes and external pointers')
    proof.menu_checked_sites.add(site)
    return {}


def manifest(proof):
    import match
    import scheduler_call_site_profile as scheduler

    require(proof.menu_checked_sites == {SETUP_SITE, COPY_SITE}, 'both non-scheduler call interfaces must be observed')
    view = copy.copy(proof)
    view.policy = scheduler.SELECTOR
    result = scheduler.manifest(view)
    require(all(row['descriptor_offset'] == -48 and row['outgoing_argument_word'] == -52
                and row['frame_bytes'] == 52 and row['aliases'] == [(match.ARM_REG_R3, -48)]
                and not row['payload_words'] and not row['other_pointer_words'] for row in result['observations']),
            'unexpected scheduler descriptor, parent or pointer alias')
    premises = result['assumptions'] + [
        'The menu object reached through 0200F438 has accessible mode/status, manager and order fields.',
        'The menu object, manager/list, optional parent, allocation, palette destination and live frames '
        'occupy valid separate storage. The installed IWRAM image remains executable and unmodified.',
    ]
    return dict(result, schema=SCHEMA, scheduler_schema=scheduler.SCHEMA, assumptions=premises,
                palette_copy=proof.menu_copy,
                synchronous_phase=proof.menu_phase, setup_discards_descriptor_at=0x0801D882,
                original_bodies=[[pc, size, digest] for pc, (size, digest) in sorted(BODIES.items())],
                composition_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
