"""Conditional scheduler registration beside the panel task's installed callbacks."""
from hashlib import sha256
from pathlib import Path
from struct import unpack_from

import bios_cpuset_fill_profile as bits
import function_thunk_profile as thunk
import installed_copy_effects as copy_effects
import installed_zero_effects as zero_effects
import scheduler_zero_descriptor as installer
import scheduler_call_site_profile as scheduler

SELECTOR = 'conditional-panel-transfer-scheduler-callbacks-v1'
OWNER = 0x081295C8
OWNER_HASH = 'ca9089a48e1d22f0fe93f40565dc43128c60fa5b1a4e61eda1ba43ef7e4eec8b'
REGISTER = 0x0812981C
CLEAR = (2, 'g_callbacks_0836D4B8', 0x0836D4B8, 0x03005E79)
COPY = (3, 'data_0836D4BC', 0x0836D4BC, 0x03005EE9)
SITES = {0x081297AE: (CLEAR, 608), 0x081297C4: (COPY, 64),
         0x081297DA: (COPY, 32), 0x08129888: (CLEAR, 608)}


def require(condition, message):
    if not condition:
        raise ValueError('panel transfer: ' + message)


def callback_record(rom, data, address, ins, edges, calls, site, spec, count, scalar_inputs):
    import match
    number, name, table, entry = spec
    reg = match.ARM_REG_R0 + number
    require(scalar_inputs[site].get(reg-1) == bits.exact(count),
            'native callback count differs')
    defs = scheduler.reaching_definitions(ins, edges, calls, address, site, reg, 'missing thunk target')
    require(len(defs) == 1, 'ambiguous callback load')
    definition, wanted = defs[0]
    load = scheduler.word_load(ins[definition], wanted)
    require(load is not None and load[1] == 0, 'expected the first callback table word')
    offsets = scheduler.callback_literals(data, address, ins, edges, calls, definition, load[0])
    require(all(unpack_from('<I', data, offset)[0] == table for offset in offsets)
            and unpack_from('<I', rom, table-match.ROM_BASE)[0] == entry,
            'wrong callback table or Thumb entry')
    return dict(site=site, register=number, target_load=definition,
                literal_offsets=offsets, table_name=name, table=table, entry=entry, count=count)


def image_effects(image):
    require(sha256(image).hexdigest() == installer.IMAGE_SHA256, 'unrecognized installed image')
    destination = installer.DESTINATION
    zero_cases = [zero_effects._case(image, destination, CLEAR[3] & ~1, 608, alignment)
                  for alignment in range(4)]
    copies = []
    for count in (32, 64):
        result = copy_effects.verify_conditional(image, destination, COPY[3] & ~1, count,
                                                 selector=copy_effects.SELECTOR)
        copies.append(dict(count=count, alignment_cases=len(result['cases']),
                           conclusion=result['conditional_conclusion'], premises=result['unproved_premises']))
    return dict(zero=dict(count=608, alignments=[case['alignment'] for case in zero_cases],
                          zero_write_span=[0, 608], private_stack_span=[-4, 0], SP_restored=True),
                copy=copies)


def bind(proof, data, address, ins, edges, calls):
    import match
    require(address == OWNER and len(data) == 1992 and sha256(data).hexdigest() == OWNER_HASH,
            'expected the phased tilemap task')
    expected = {site: thunk.ALIASES[f'_call_via_r{spec[0]}'] for site, (spec, _) in SITES.items()}
    require({site: target for site, target in calls.items() if thunk.reserved(target)} == expected,
            'unexpected callback edges')
    registrations = {site: target for site, target in calls.items() if target in scheduler.ENTRIES}
    require(registrations == {REGISTER: scheduler.POOL}, 'expected one pool-manager registration')
    scalar_inputs = bits.prove_bits(ins, edges, address, data)
    require(scalar_inputs[REGISTER].get(match.ARM_REG_R1) == bits.exact(0x98),
            'portrait task payload must be 152 bytes')
    proof.panel_callbacks = [
        callback_record(proof.rom, data, address, ins, edges, calls, site, spec, count, scalar_inputs)
        for site, (spec, count) in sorted(SITES.items())]
    plan = installer.initializer_plan(proof.rom, proof.mapping, proof.index)
    image = bytes.fromhex(plan['source_image']['bytes'])
    require(proof.span(installer.IMAGE + 0x70) == image[0x70:0xAE], 'copy entry native bounds differ')
    proof.panel_installation = dict(copy_plan=plan['copy_plan'], call_site=plan['call_site'],
                                    image_sha256=plan['source_image']['sha256'], obligations=plan['obligations'])
    proof.panel_effects = image_effects(image)
    proof.panel_checked = set()
    # Retain every validated BL as a barrier in the reaching-definition search.
    offsets = scheduler.callback_literals(data, address, ins, edges, calls, REGISTER, match.ARM_REG_R0)
    require(offsets == [0x08129838-OWNER] and unpack_from('<I', data, offsets[0])[0] == 0x08129D91,
            'pool call must receive the portrait callback')
    entry = scheduler.ENTRIES[scheduler.POOL]
    looped = scheduler.looped_sites(edges, registrations)
    require(not looped, 'unexpected loop through the pool registration')
    return dict(sites=[dict(site=REGISTER, target=scheduler.POOL, scheduler_entry=entry['kind'],
                 callback_register=0, descriptor_register=2, callback_literal_offsets=offsets,
                 looped=False)], looped_sites=[], dependencies=list(entry['dependencies']),
                source_sha256=sha256(Path(scheduler.__file__).read_bytes()).hexdigest())


def check_indirect(proof, site, target, aliases, returns):
    import match
    require(site in SITES and proof.calls[site] == target, 'unbound thunk')
    require(not aliases and not (set(returns) & (set(match.CALLER_CLOBBERED)-{match.ARM_REG_LR})),
            'callback carries local or return provenance')


def check_call(proof, site, target, aliases, slots):
    require(not aliases and not slots and proof.calls[site] == target,
            'installed callback requires external arguments without spilled local pointers')
    proof.panel_checked.add(site)
    return {}


def check_bindings(manifest, bindings):
    for row in manifest['panel_callbacks']['sites']:
        require(all([offset, row['table_name'], 0] in bindings['data'] for offset in row['literal_offsets']),
                'callback table must have its typed zero-addend relocation')
        require([row['site']-OWNER, f"_call_via_r{row['register']}"] in bindings['calls'],
                'expected original compiler thunk relocations')
    require(bindings['functions'] == [[0x08129838-OWNER, 'func_08129D90']],
            'expected one typed task callback')


def finish(proof, manifest):
    require(proof.panel_checked == set(SITES), 'every thunk must receive its checked external arguments')
    manifest['panel_callbacks'] = dict(sites=proof.panel_callbacks, installation=proof.panel_installation,
        image_effects=proof.panel_effects,
        contract='Actual ROM table words and indexed Thumb branch thunks; conditional returning '
                 'indirect callees preserve R4-R11 and SP and do not access the caller frame. '
                 'Zero and copy footprints apply if the proposed boot image persists, RAM buffers and separate '
                 'private stack are valid, physically disjoint and do not wrap, and code, saved state '
                 'and buffers have no interfering writes. Actual installation and physical aliasing remain premises.',
        dependencies_sha256={m.__name__: sha256(Path(m.__file__).read_bytes()).hexdigest()
                             for m in (bits, copy_effects, zero_effects, installer)},
        source_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
    return manifest
