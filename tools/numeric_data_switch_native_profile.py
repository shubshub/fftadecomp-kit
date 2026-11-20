"""Original ELF-bound one-numeric-word switch with named data and strict frame.

Cycles use the existing restoring-frame fixed point. Ordinary calls remain
conditional ABI boundaries; data identities grant no memory permissions.
"""
import copy
import hashlib
import json
from pathlib import Path
import struct

import canonical_integer_native_profile as scalar_native
import rom_mirror

SELECTOR = 'numeric-data-switch-source-v1'
SCHEMA = 'elf-symbol-thumb-numeric-data-switch-source-v1'
CONTROL_FLOW = 'complete original ELF-bound numeric switch, typed data points and restoring scalar frame'


def environment_fingerprint():
    import one_constant_scalar_switch_inventory as inventory
    result = scalar_native.environment_fingerprint()
    result['numeric_switch_producers'] = {Path(module.__file__).name:
        hashlib.sha256(Path(module.__file__).read_bytes()).hexdigest()
        for module in (inventory, inventory.analyze, inventory.ordinary, inventory.thunks,
                       inventory.frame, inventory.graph, inventory.graph.armv4t, inventory.operations)}
    result['numeric_switch_producers'][Path(__file__).name] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    return result


def verify_structure(data, address, rom, mapping, index, bindings,
                     refinement, instructions, edges, branches, calls, partition):
    import one_constant_scalar_switch_inventory as inventory
    import match
    import owner_admission_profile as owner
    from capstone.arm import ARM_OP_REG, ARM_REG_SP
    entries = owner.validate_span(data, address, rom, mapping, index)
    switches = refinement['word_switches']
    if branches or len(switches) != 1 or switches[0].get('interposed_words') != 1:
        raise ValueError('numeric-data switch requires one guarded numeric table without local BL')
    inventory.guard_predecessors(instructions, edges, address, switches[0])
    selected = next(row for row in entries if int(row['rom'], 16) == address)
    rows = [line.split() for line in index.decode().splitlines()
            if line.split() and line.split()[0] == f'{address:08X}']
    if type(selected.get('instrs')) is not int or selected['instrs'] != len(instructions) or \
            len(rows) != 1 or len(rows[0]) < 4 or int(rows[0][3]) != len(instructions):
        raise ValueError('numeric-data switch requires exact dual-index instruction counts')
    inventory.operations.verify_operations(instructions, edges, address, branches, calls, refinement)
    adjustments = []
    for site, instruction in sorted(instructions.items()):
        if instruction.size != 2 and not (instruction.mnemonic == 'bl' and instruction.size == 4):
            raise ValueError('numeric-data switch excludes non-ARMv4T instruction widths')
        adjustment = match.thumb_stack_adjustment(instruction)
        if instruction.mnemonic.startswith(('ldm', 'stm')):
            raise ValueError('numeric-data switch excludes block transfers')
        if instruction.mnemonic not in ('push', 'pop') and adjustment is None and any(
                operand.type == ARM_OP_REG and operand.reg == ARM_REG_SP
                for operand in instruction.operands):
            raise ValueError('numeric-data switch excludes stack-address materialization')
        if adjustment is not None:
            adjustments.append([site - address, adjustment * 4])
    # No incoming words, aliases, callee effects or register-preservation overrides.
    restored = inventory.frame.prove_frame(instructions, edges, address, branches, calls)
    numeric = next(word for word in partition['words']
                   if word['address'] == address + switches[0]['literal'] - 4)
    if numeric['switch_word'] or not numeric['load_sites'] or not 0 <= numeric['value'] <= 0xffff:
        raise ValueError('numeric-data switch requires an actually reached u16 interposed literal')
    data_sites = {address + site for site, _, _ in bindings['data']}
    for word in partition['words']:
        value = word['value']
        if reserved(value) or (not word['switch_word'] and any(
                int(row['rom'], 16) & ~1 == rom_mirror.canonical(value) & ~1 for row in entries)):
            raise ValueError('numeric-data switch cannot materialize runtime or function addresses')
        if not word['switch_word'] and word['address'] not in data_sites and not 0 <= value <= 0xffff:
            raise ValueError('numeric-data switch scalar literals require bounded u16 category')
    if any(reserved(target) for target in calls.values()):
        raise ValueError('numeric-data switch excludes arithmetic runtimes and indirect thunks')
    return dict(address=address, end=address+len(data), instructions=len(instructions),
        word_switches=switches, partition=partition, frame=restored, stack_adjustments=adjustments,
        calls=bindings['calls'], runtime_calls=[], numeric_word=numeric,
        body_sha256=hashlib.sha256(data).hexdigest(), mapping_sha256=hashlib.sha256(mapping).hexdigest(),
        index_sha256=hashlib.sha256(index).hexdigest(), ROM_sha256=hashlib.sha256(rom).hexdigest(),
        ordinary_call_premise='conditional returning call preserving r4-r11/SP; caller-saved provenance cleared',
        memory_safety_claim=False, nonalias_claim=False, termination_claim=False,
        numeric_input_preconditions=[], arithmetic_C_equivalence=False,
        control_flow_guarantee='every reached region has a path to a checked return; no universal termination claim')


def reserved(value):
    import one_constant_scalar_switch_inventory as inventory
    import match
    return value in match.RUNTIME_HELPERS.values() or match.is_udivsi3_address(value) or any(
        module.reserved(value) for module in (inventory.thunks, match.divsi3, match.modsi3,
            match.umodsi3, match.ashldi3, match.software_double, match.software_float))


def verify_original(original, linked, address, rom, mapping, index, bindings, manifest=None, *, objects):
    import one_constant_scalar_switch_inventory as inventory
    import match
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    if type(address) is not int or any(type(value) is not bytes
            for value in (original, linked, rom, mapping, index, objects)):
        raise ValueError('numeric-data switch bridge requires immutable original inputs')
    before = environment_fingerprint()
    image, output = match.elf_image(original), match.elf_image(linked)
    actual, targets = owner.original_bindings(image, address, rom, mapping, objects,
                                               selector=SELECTOR, index=index)
    if type(bindings) is not dict or bindings != actual or actual['functions'] or not all(actual[role] for role in ('calls', 'data', 'switches')):
        raise ValueError('numeric-data switch bindings differ from original call/object roles')
    if any(symbol['size'] for symbol in image['symbols'] if symbol['name'] in targets and not symbol['section']):
        raise ValueError('numeric-data switch original undefined symbols require zero size')
    match.allocated_text_only(output)
    name = f'func_{address:08X}'
    root, offset = match.function_record(output, name, address, True)
    source, _ = match.function_record(image, name, address, True)
    from addressed_signed_runtime_profile import terminal_alignment
    terminal_alignment(output, root)
    if output['type'] != 2 or output['relocations'] or offset or root['size'] != source['size'] or \
            len(output['text']) != len(image['text']) or any(
                symbol['name'] and not symbol['section'] for symbol in output['symbols']):
        raise ValueError('numeric-data switch typed link changes complete owner or leaves undefined symbols')
    for key, (value, is_object) in targets.items():
        found = [symbol for symbol in output['symbols'] if symbol['name'] == key]
        if len(found) != 1 or found[0]['section'] != 0xfff1 or found[0]['bind'] != 1 or \
                found[0]['size'] or found[0]['type'] != (1 if is_object else 2) or \
                found[0]['value'] != (value if is_object else value | 1):
            raise ValueError('numeric-data switch link requires exact unique typed absolute definitions')
    if any(symbol['name'] not in set(targets) | {name} and symbol['type'] in (1, 2) and symbol['section']
           for symbol in output['symbols']):
        raise ValueError('numeric-data switch link adds an unowned function or object')
    expected = bytearray(image['text'])
    decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
    decoder.detail = True
    for site, key in actual['calls']:
        item = next(decoder.disasm(output['text'][site:site+4], address+site), None)
        if item is None or item.id != match.ARM_INS_BL or item.size != 4 or item.operands[0].imm != targets[key][0]:
            raise ValueError('numeric-data switch linked call differs from original identity')
        expected[site:site+4] = output['text'][site:site+4]
    for site, key, addend in actual['data']:
        if addend:
            raise ValueError('numeric-data switch named objects require zero addends')
        struct.pack_into('<I', expected, site, targets[key][0])
    for site, addend in actual['switches']:
        struct.pack_into('<I', expected, site, address + addend)
    if bytes(expected) != output['text']:
        raise ValueError('numeric-data switch link changes bytes outside original relocation roles')
    data = output['text'][:root['size']]
    refinement = inventory.refine(data, address, mapping)
    ins, edges, branches, calls, words = graph.graph(data, address, refinement, one_numeric_word_switch=True)
    if actual['switches'] != [[site, addend] for site, addend in sorted(words.items())]:
        raise ValueError('numeric-data switch original local relocations differ from guarded table')
    partition = graph.partition(data, address, refinement, ins, words)
    for site, key, _ in actual['data']:
        value = targets[key][0]
        word = next((row for row in partition['words'] if row['address'] == address+site), None)
        if word is None or (address+site) % 4 or not word['load_sites'] or word['switch_word'] or \
                word['value'] != value or not 0x02000000 <= value < 0x09000000 or any(
                    (value & ~1) == int(row['rom'], 16) for row in json.loads(mapping)):
            raise ValueError('numeric-data switch objects require actual referenced non-code point literals')
    expected_calls = {address+site: key for site, key in actual['calls']}
    if expected_calls != inventory.bind_calls(calls, mapping, address, len(data), len(rom)):
        raise ValueError('numeric-data switch CFG differs from original compiler call identities')
    checked = verify_structure(data, address, rom, mapping, index, actual,
        refinement, ins, edges, branches, calls, partition)
    instructions = ins
    if before != environment_fingerprint():
        raise ValueError('numeric-data switch producers, runtime or toolchain changed')
    result = dict(profile=SCHEMA, selector=SELECTOR, bindings=copy.deepcopy(actual), prerequisite=checked,
        environment=before, original_ET_REL_sha256=hashlib.sha256(original).hexdigest(),
        linked_ELF_sha256=hashlib.sha256(linked).hexdigest(), objects_sha256=hashlib.sha256(objects).hexdigest(),
        contract='Scalar word locals stay within the existing checked abstract frame; '
        'SP materialization, local aliases, pointer spills and incoming stack reads remain refused. '
        'Named object points grant no memory permissions, bounds or initialized values. Ordinary calls '
        'remain returning ABI boundaries. No numeric result, arithmetic C-equivalence, physical memory '
        'separation, memory safety, alias escape or termination theorem is inferred.')
    if manifest is not None and owner.text(manifest) != owner.text(result):
        raise ValueError('numeric-data switch source manifest differs from fresh original replay')
    return result, len(instructions)
