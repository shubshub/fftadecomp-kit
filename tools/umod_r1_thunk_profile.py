"""Explicit source admission for saved-only UMOD48 and canonical R1 callbacks.

The existing structural inventory proves complete runtime/frame closure.  Typed
original ELF relocations and the canonical-thunk source/report lifecycle remain
separate obligations.  The indirect destination retains its conditional ABI;
no arithmetic equivalence, readable extent or callback effect is inferred.
"""
import hashlib
import json
from pathlib import Path

SELECTOR = 'umod48-r1-thunks-v1'
SCHEMA = 'elf-symbol-thumb-function-address-thunks-umod48-r1-v1'


def check_link_context(selector, thunks, words, functions, switches, unsigned, flags, contexts):
    if type(selector) is not str or selector != SELECTOR or thunks is not True or \
            type(words) is not int or words != 5 or type(functions) is not dict or functions or \
            type(switches) is not dict or switches or type(unsigned) is not dict or \
            any(value is not False for value in flags) or any(value is not None for value in contexts):
        raise ValueError('UMOD/r1 linking requires its exclusive explicit typed context')


def check_link_bindings(calls, targets, literals, functions, switches, unsigned):
    import umod_r1_thunk_inventory as inventory
    import umodsi3_profile as remainder
    if type(calls) is not dict or len(calls) != 2 or \
            set(calls.values()) != {remainder.ADDRESS, inventory.THUNK_ADDRESS} or \
            functions or switches or type(unsigned) is not dict or unsigned != {
                site: '__umodsi3' for site, target in calls.items() if target == remainder.ADDRESS}:
        raise ValueError('UMOD/r1 requires one actual UMOD and one canonical R1 call, without other composition')
    names = {name for name, _ in literals.values()}
    if {name: target for name, target in targets.items() if name not in names} != {
            '__umodsi3': remainder.ADDRESS, inventory.THUNK: inventory.THUNK_ADDRESS}:
        raise ValueError('UMOD/r1 requires exact canonical call aliases and typed original objects')


def prove(data, address, rom, mapping, index, calls):
    import umod_r1_thunk_inventory as inventory
    bindings = inventory.bind_calls(calls, mapping, address, len(data), len(rom))
    return inventory.verify(data, address, rom, mapping, index, calls, bindings,
                            selector=inventory.SELECTOR)


def producer_sources():
    import analyze
    import function_thunk_profile
    import local_long_branch_profile
    import match
    import owner_admission_profile
    import owner_graph_profile
    import owner_runtime_profile
    import software_double_profile
    import software_float_profile
    import umod_only_ordinary_inventory
    import umod_r1_thunk_inventory
    import umodsi3_profile
    import unsigned_remainder_closure_inventory
    modules = (analyze, function_thunk_profile, local_long_branch_profile, match, match.armv4t,
        owner_admission_profile, owner_graph_profile, owner_runtime_profile,
        software_double_profile, software_float_profile, umod_only_ordinary_inventory,
        umod_r1_thunk_inventory, umodsi3_profile, unsigned_remainder_closure_inventory)
    result = {Path(module.__file__).name: hashlib.sha256(Path(module.__file__).read_bytes()).hexdigest()
              for module in modules}
    result[Path(__file__).name] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    return result


def make_manifest(calls, functions, literals, address, rom, objects, instructions):
    import function_thunk_profile as thunks
    import match
    import umod_r1_thunk_inventory as inventory
    import umodsi3_profile as remainder
    aliases = inventory.bind_calls(calls, b'[]', address,
        max(item.address + item.size for item in instructions) - address, len(rom))
    if functions:
        raise ValueError('UMOD/r1 excludes typed function literals')
    names = match.parse_data_symbols(objects) if literals else {}
    return {'selector': SELECTOR, 'runtime': thunks.RUNTIME, 'abi': thunks.ABI,
        'frame': match.uses_stack_frame(instructions), 'calls': [], 'functions': [],
        'thunks': [[site-address, name] for site, name in sorted(aliases.items()) if name == inventory.THUNK],
        'unsigned_remainder': [[site-address, '__umodsi3'] for site, target in sorted(calls.items())
                               if target == remainder.ADDRESS],
        'data': [[offset, name, value-names[name]] for offset, (name, value) in sorted(literals.items())],
        'dependencies': thunks.dependencies((inventory.THUNK,), rom),
        'producer_source_sha256': producer_sources()}


def verify(data, address, rom, mapping, index, objects, manifest):
    import function_thunk_profile as thunks
    import match
    import umod_r1_thunk_inventory as inventory
    import umodsi3_profile as remainder
    keys = {'selector', 'runtime', 'abi', 'frame', 'calls', 'functions', 'thunks',
            'unsigned_remainder', 'data', 'dependencies', 'producer_source_sha256'}
    if type(manifest) is not dict or set(manifest) != keys or manifest['selector'] != SELECTOR or \
            manifest['runtime'] != thunks.RUNTIME or manifest['abi'] != thunks.ABI or \
            type(manifest['frame']) is not bool or manifest['calls'] != [] or manifest['functions'] != [] or \
            manifest['producer_source_sha256'] != producer_sources():
        raise ValueError('UMOD/r1 source manifest or producer source bytes differ')
    _, literals = match.function_address_bindings(data, address, rom, mapping, objects,
        {'calls': [], 'functions': [], 'data': manifest['data']}, allow_empty_functions=True)
    calls, occupied = {}, {p for offset in literals for p in range(offset, offset+4)}
    for key, alias, target in (('thunks', inventory.THUNK, inventory.THUNK_ADDRESS),
                                ('unsigned_remainder', '__umodsi3', remainder.ADDRESS)):
        records = manifest[key]
        if type(records) is not list or len(records) != 1 or type(records[0]) is not list or \
                len(records[0]) != 2 or records[0][1] != alias:
            raise ValueError('UMOD/r1 requires exactly one canonical call record of each kind')
        offset = records[0][0]
        if type(offset) is not int or offset < 0 or offset % 2 or offset+4 > len(data) or \
                occupied.intersection(range(offset, offset+4)):
            raise ValueError('UMOD/r1 call record is misaligned, incomplete or overlapping')
        calls[address+offset] = target
        occupied.update(range(offset, offset+4))
    if manifest['dependencies'] != thunks.dependencies((inventory.THUNK,), rom):
        raise ValueError('UMOD/r1 canonical thunk dependency differs')
    proof, instructions = prove(data, address, rom, mapping, index, calls)
    thunks.verify_data_bindings(calls, literals, match.parse_data_symbols(objects) if literals else {}, json.loads(mapping))
    match.verify_data_literals(instructions, address, literals)
    # This distinct selector requires original typed ABS32 provenance for every
    # reached pool word; it grants no raw-address or scalar-pool composition.
    from capstone.arm import ARM_OP_MEM, ARM_REG_PC
    reached = {((item.address+4)&~3)+operand.mem.disp-address for item in instructions
               if item.mnemonic == 'ldr' for operand in item.operands
               if operand.type == ARM_OP_MEM and operand.mem.base == ARM_REG_PC and not operand.mem.index}
    if set(literals) != reached or match.uses_stack_frame(instructions) != manifest['frame']:
        raise ValueError('UMOD/r1 requires reached typed literals and the exact saved frame')
    if proof['caller_divisors'] != [[manifest['unsigned_remainder'][0][0], 48]]:
        raise ValueError('UMOD/r1 source manifest requires the actual all-path divisor 48')
    return instructions
