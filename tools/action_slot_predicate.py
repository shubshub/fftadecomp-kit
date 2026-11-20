"""Conditional two-item equipment output followed by the action slot predicate."""
from hashlib import sha256

import battle_action_value as battle
import multiple_switch_owner_prerequisite as backward
import owner_graph_profile as graph
import unit_equipment_attribute as equipment
from ability_range_local_bytes import block, require
from active_entry_shuffle_profile import compiler_symbol_roles, exact_edges
from one_constant_scalar_switch_inventory import guard_predecessors
from software_float_profile import ROM_SHA256

OWNER, END = 0x081306E0, 0x0813079C
STATE_NAME, STATE = 'data_0200F3F0', 0x0200F3F0
SOURCE_HASH = 'f1e1175604d60aea84a67a0324dc2bab46c25c2663825227e3d014b75a3b2d60'
BODY_HASH = '01e81f4bf91e0c931ee528b5ae29d8ed5899a74ee38a7eea2b99b95ba31fd40c'
CALLS = {0x10: equipment.WRAPPER, 0x28: 0x0812F2A4, 0x3E: 0x0812F328,
         0x44: 0x0812F34C, 0x48: 0x08130FBC, 0x54: 0x0812F39C,
         0x5A: 0x0812F34C, 0x5E: 0x0812F358, 0x9C: 0x08131B20}
CASES = (0x9C, 0xB2, 0xB2, 0xB2, 0x9C, 0xB2, 0xB2, 0x18)
WORDS = [[0x78, 0x7C]] + [[0x7C+4*i, dest] for i, dest in enumerate(CASES)]
BINDINGS = dict(equipment.bindings(CALLS), data=[[0x1C, STATE_NAME, 0]], switches=WORDS)


def check_original(image, original, targets):
    expected = {f'func_{target:08X}': (target, False) for target in CALLS.values()}
    expected[STATE_NAME] = (STATE, True)
    require(original == BINDINGS and targets == expected, 'action predicate original relocations differ')
    compiler_symbol_roles(image, targets)
    require(all(not row['size'] for row in image['symbols'] if row['name'] in targets),
            'action predicate undefined symbol has nonzero size')


def control_flow(data, address, mapping):
    import owner_admission_profile as owner
    require(address == OWNER and sha256(data).hexdigest() == BODY_HASH, 'unexpected action predicate body')
    # Request backward edges only for this pinned owner. The original ELF and all
    # eight case relocations are checked independently; only one table is legal.
    refinement = owner.refine(data, address, mapping, multiple_switch_profile=backward.SELECTOR)
    ins, edges, branches, calls, words = graph.graph(
        data, address, refinement, multiple_switch_profile=backward.SELECTOR)
    require(not branches and len(refinement['word_switches']) == 1 and words == dict(WORDS),
            'action predicate needs its single indexed switch')
    guard_predecessors(ins, edges, address, refinement['word_switches'][0])
    exact_edges(ins, edges, OWNER, {0x16:(0x18,0x20), 0x1A:(0xB4,), 0x50:(0x52,0xAC),
        0x6A:(0x6C,0xAC), 0x74:(0x18,0x9C,0xB2), 0xA4:(0xA6,0xA8),
        0xAA:(0xB4,), 0xB0:(0x3A,0xB2), 0xBA:()})
    return refinement, (ins, edges, branches, calls, words)


def prove(data, rom, mapping, index, objects, original, ins, calls, refinement, words):
    require(sha256(rom).hexdigest() == ROM_SHA256 and data == rom[OWNER-equipment.BASE:END-equipment.BASE]
            and len(ins) == 64 and original == BINDINGS and calls == {OWNER+i:t for i,t in CALLS.items()}
            and words == dict(WORDS), 'action predicate owner, switch or calls differ')
    battle.check_dependencies(rom, mapping, index, objects, {OWNER:(END,BODY_HASH)}, OWNER, len(ins))
    require(equipment.match.parse_data_symbols(objects).get(STATE_NAME) == STATE,
            'action predicate state mapping differs')
    part = graph.partition(data, OWNER, refinement, ins, words)
    require(part['code_bytes'] == 146 and part['literal_and_table_bytes'] == 40
            and part['alignment'] == [[OWNER+0x76,OWNER+0x78]], 'action predicate partition differs')
    reads = [(row['address']-OWNER, [site-OWNER for site in row['load_sites']]) for row in part['words']]
    require(reads == [(0x1C,[0x0C]),(0x78,[0x6E])] + [(row[0],[]) for row in WORDS[1:]],
            'action predicate literal use differs')
    block(ins, OWNER, 'push {r4, r5, r6, r7, lr}', 'sub sp, #4', 'adds r6, r0, #0',
          'adds r7, r1, #0', 'lsls r2, r2, #0x10', 'lsrs r4, r2, #0x10', 'ldr r5, [pc, #0xc]',
          'mov r1, sp', 'bl #0x812f0d8', 'cmp r4, #0', 'bne #0x8130700', 'movs r0, #1', 'b #0x8130794')
    block(ins, OWNER+0x20, 'mov r0, sp', 'ldrh r1, [r0]', 'adds r0, r4, #0', 'movs r2, #0',
          'bl #0x812f2a4', 'str r6, [r5]', 'str r7, [r5, #4]', 'ldrh r1, [r5, #0x26]',
          'movs r0, #2', 'orrs r0, r1', 'strh r0, [r5, #0x26]', 'movs r4, #0')
    block(ins, OWNER+0x3A, 'lsls r0, r4, #0x18', 'lsrs r0, r0, #0x18', 'bl #0x812f328',
          'movs r0, #0', 'bl #0x812f34c', 'bl #0x8130fbc', 'lsls r0, r0, #0x18', 'cmp r0, #0',
          'beq #0x813078c', 'adds r0, r4, #0', 'bl #0x812f39c', 'adds r0, r7, #0', 'bl #0x812f34c',
          'bl #0x812f358', 'lsls r0, r0, #0x18', 'lsrs r0, r0, #0x18', 'subs r0, #1')
    block(ins, OWNER+0x9C, 'bl #0x8131b20', 'movs r1, #0', 'cmp r0, #0', 'ble #0x8130788',
          'movs r1, #1', 'adds r0, r1, #0', 'b #0x8130794', 'adds r4, #1', 'cmp r4, #2',
          'ble #0x813071a', 'movs r0, #0', 'add sp, #4', 'pop {r4, r5, r6, r7}', 'pop {r1}', 'bx r1')
    cases = equipment.cursor_cases()
    require(all(set(case['write_offsets']) <= {0,2} for case in cases), 'equipment output escapes the local')
    return dict(schema=equipment.named.EQUIPMENT_SCHEMA, instructions=len(ins), calls=original['calls'],
        runtime_calls=[], partition=part, case_offsets=list(CASES), local=[-24,-20], saved=[-20,0],
        collector_clears=[0,2], owner_read_offsets=[0], equipment_cases=cases,
        scene_equipment=equipment.scene_rows(rom), equipment_copy=equipment.installed_copy(rom,mapping,index),
        conditions=['The live unit has at most two qualifying items in its five stable equipment slots. '
                    'The two-halfword producer initializes both slots and retains no output alias.',
                    'External objects and action state are valid and disjoint from the frame. Returning '
                    'ordinary helpers preserve SP and callee-saved registers.'],
        result='Action zero succeeds after equipment collection. Eligible kinds 1 and 5 test a signed '
               'positive score, kind 8 succeeds, and kinds 2, 3, 4, 6, 7 fail. Other kinds advance the '
               'three-slot loop. Exhaustion fails.', environment=equipment.environment_fingerprint())
