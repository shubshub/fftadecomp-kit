"""A random equipped item is removed by action kinds 65 and 66."""
from hashlib import sha256
import struct

import active_entry_shuffle_profile as shuffle
import battle_action_value as battle
import equipment_removal_effect as removal
import positioned_equipment_chance as chance
import unit_equipment_attribute as equipment
from ability_range_local_bytes import block, require
from owner_admission_profile import refine
from software_float_profile import ROM_SHA256

OWNER, END, GUARD = 0x0813325C, 0x081332F8, 0x08133244
MEMBER, INVENTORY = 0x08131BB8, 0x080CA9E8
CALLS = {0x18: removal.WRAPPER, 0x22: shuffle.RNG, 0x2C: shuffle.REMAINDER,
         0x42: equipment.SLOT, 0x60: removal.CLEAR, 0x68: removal.VALIDATE,
         0x6E: MEMBER, 0x7C: INVENTORY, 0x8C: removal.REFRESH}
SYMBOLS = {offset: ('__modsi3' if address == shuffle.REMAINDER else f'func_{address:08X}')
           for offset, address in CALLS.items()}
TARGETS = {SYMBOLS[offset]: (address, False) for offset, address in CALLS.items()}
BINDINGS = dict(calls=[[offset, name] for offset, name in SYMBOLS.items()], data=[], functions=[], switches=[])
SOURCE_HASH = 'ba07a30e842681bae42de0fae27b827aefc018643e62b4fdbd394b2cb5d311b5'
PINS = {
    OWNER: (END, '0407b56572135f872ce2f80b234c9cada77bcb95efd08df5604fdb392d13f39a'),
    GUARD: (OWNER, '6a3472c3a89cdc5ae256bb2597cb90209edc79c5b8081da544d53f89f2c26f16'),
    MEMBER: (0x08131BDE, '8d2433ef5c27fd7b1bd803b3184129a9bea63edbb44a49725b82a5628d39d38e'),
    **{target: removal.PINS[target] for target in (removal.WRAPPER, removal.DISPATCH, removal.THUNK)},
}


def check_original(image, original, targets):
    require(original == BINDINGS and targets == TARGETS, 'random removal compiler call names or roles differ')
    shuffle.compiler_symbol_roles(image, targets)
    require(all(not row['size'] for row in image['symbols'] if row['name'] in targets),
            'random removal helper reference has a size')


def routes(rom, objects):
    require(chance.direct_sites(rom, OWNER) == [GUARD+16] and not chance.direct_sites(rom, GUARD),
            'random removal direct caller inventory differs')
    equipment.ops(rom, GUARD, 'push {lr}', 'adds r2, r0, #0', 'ldrh r1, [r2, #0x26]',
                  'movs r0, #0x10', 'ands r0, r1', 'cmp r0, #0', 'bne #0x8133258',
                  'adds r0, r2, #0', 'bl #0x813325c', 'pop {r0}', 'bx r0')
    result = []
    for kind, callback, record, action, variant in ((65, GUARD, 176, 289, 1), (66, OWNER, 129, 225, 0)):
        route = removal.dispatch(rom, objects, kind=kind, callback=callback, record_index=record)
        pointer = struct.pack('<I', callback | 1)
        require(rom.find(pointer) == rom.rfind(pointer) == route['descriptor']-equipment.BASE and
                rom[0x55187C+28*action+12+variant] == record, 'equipment action record or callback differs')
        result.append(dict(route, action=action, variant=variant, guarded=callback == GUARD))
    return result


def frame(ins):
    block(ins, OWNER, 'push {r4, r5, r6, r7, lr}', 'mov r7, r8', 'push {r7}', 'sub sp, #4',
          'adds r6, r0, #0', 'ldrh r1, [r6, #0x26]', 'movs r0, #0x10', 'ands r0, r1',
          'cmp r0, #0', 'bne #0x81332ec', 'ldr r0, [r6, #8]', 'mov r1, sp', 'bl #0x812f0cc',
          'adds r4, r0, #0', 'cmp r4, #0', 'beq #0x81332ec', 'bl #0x8002804',
          'lsls r0, r0, #0x10', 'asrs r0, r0, #0x10', 'adds r1, r4, #0', 'bl #0x8142950',
          'movs r5, #0', 'lsls r0, r0, #1', 'add r0, sp, r0', 'mov r8, r0')
    block(ins, 0x08133294, 'ldr r0, [r6, #8]', 'adds r1, r5, #0', 'adds r1, #0x1d',
          'lsls r1, r1, #0x18', 'lsrs r1, r1, #0x18', 'bl #0x80c7ea4', 'lsls r0, r0, #0x10',
          'lsrs r4, r0, #0x10', 'adds r7, r4, #0', 'cmp r4, #0', 'beq #0x81332e0',
          'mov r0, r8', 'ldrh r0, [r0]', 'cmp r4, r0', 'bne #0x81332e0',
          'ldr r0, [r6, #8]', 'lsls r2, r5, #0x18', 'lsrs r2, r2, #0x18', 'movs r1, #0',
          'bl #0x80caf78', 'ldr r0, [r6, #8]', 'movs r1, #1', 'bl #0x80cb54c',
          'ldr r0, [r6, #8]', 'bl #0x8131bb8', 'lsls r0, r0, #0x18', 'cmp r0, #0',
          'beq #0x81332dc', 'adds r0, r4, #0', 'movs r1, #1', 'bl #0x80ca9e8',
          'strh r7, [r6, #0x18]', 'b #0x81332e6', 'adds r5, #1', 'cmp r5, #4',
          'ble #0x8133294', 'ldr r0, [r6, #8]', 'bl #0x80ca2e8', 'add sp, #4',
          'pop {r3}', 'mov r8, r3', 'pop {r4, r5, r6, r7}', 'pop {r0}', 'bx r0')


def prove(data, rom, mapping, index, objects, original, ins, calls, refinement, words):
    require(sha256(rom).hexdigest() == ROM_SHA256 and data == rom[OWNER-equipment.BASE:END-equipment.BASE]
            and len(ins) == 69 and not words and original == BINDINGS
            and calls == {OWNER+off: target for off, target in CALLS.items()},
            'random equipment removal owner, calls or bindings differ')
    battle.check_dependencies(rom, mapping, index, objects, PINS, OWNER, len(ins))
    mutators = removal.validate_mutators(rom, mapping, index)
    # The historical text index counts extra halfwords for the inventory helper.
    inventory = rom[INVENTORY-equipment.BASE:0xCAA74]
    equipment.named.validate_owner(inventory, INVENTORY, rom, mapping, index)
    decoded = equipment.graph.graph(inventory, INVENTORY, refine(inventory, INVENTORY, mapping))[0]
    require(len(decoded) == 62 and sha256(inventory).hexdigest() ==
            '21b05ab36a37a6f1c30dce480267fab9447b0c1d375bfe2eb5c17d43ba3fea6b',
            'inventory subtraction helper differs')
    equipment.ops(rom, removal.WRAPPER, 'push {lr}', 'bl #0x812e4f4', 'pop {r1}', 'bx r1')
    frame(ins)
    seed, mod = shuffle.rng_and_remainder(shuffle.native_spans(rom, mapping, index), data, OWNER,
                                         calls, OWNER+0x2C, rom, mapping, index)
    require(equipment.match.parse_data_symbols(objects).get('g_state_030034B0') == seed['seed'],
            'equipment RNG seed mapping differs')
    cases = []
    for case in equipment.cursor_cases():
        count = case['selected']
        reads = [2*i for i in range(count)]
        require(reads == case['write_offsets'] and all(i <= 2 for i in reads), 'uninitialized selection read')
        cases.append(dict(mask=case['mask'], count=count, append_offsets=reads,
                          possible_read_offsets=reads, rng_called=count != 0))
    return dict(schema=equipment.named.EQUIPMENT_SCHEMA, instructions=len(ins),
                calls=[row for row in BINDINGS['calls'] if row[1] != '__modsi3'],
                runtime_calls=[[0x2C, '__modsi3']], partition=equipment.graph.partition(data, OWNER, refinement, ins, words),
                routes=routes(rom, objects), direct_site=GUARD+16, local=[-28,-24], saved=[-24,0],
                rng=seed, signed_remainder=dict(dividends=[0,32767], divisors=[1,2], frame=mod),
                mutators=[[address, count] for address, count in mutators.items()], cases=cases,
                scene_equipment=equipment.scene_rows(rom), equipment_copy=equipment.installed_copy(rom, mapping, index),
                result='Flag 0x10 or zero selected entries skips the effect. Otherwise the RNG advances once '
                       'and its signed remainder selects an initialized item. The first matching live slot '
                       'is cleared and validated. For a roster member the inventory helper is called with quantity one. '
                       'The item is recorded at +0x18, then the unit is refreshed.',
                conditions=['The target has five stable valid equipment slots through selection and search, '
                            'with at most two nonzero items whose field 6 is 1 or 2 and field 3 differs from '
                            '20. Neither dispatch enforces that bound after equipment edits. The 42 scene '
                            'rows establish examples of initial loadouts only.',
                            'The state, target, item rows, mutable inventory, RNG word and original helpers '
                            'satisfy their native contracts and are separate from the frame. Returning helpers '
                            'preserve SP and saved registers. The collector retains no pointer to the local.'],
                environment=equipment.environment_fingerprint())
