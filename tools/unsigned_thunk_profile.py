"""Explicit source admission for unsigned DIV/MOD with canonical thunk callbacks.

The structural inventory proves the complete saved-only caller frame, an
all-path constant divisor at every runtime call and the native UDIV/UMOD/zero
closure.  This selector adds the typed original-ELF relocation and
canonical-thunk source/report lifecycle.  Indirect destinations keep the
conditional ABI of the existing thunk selectors: no callback value, body or
effect is inferred, and no arithmetic or memory equivalence is claimed.
"""
import hashlib
import json
from pathlib import Path
import re

SELECTOR = 'unsigned-divmod-thunks-v1'
SCHEMA = 'elf-symbol-thumb-function-address-thunks-unsigned-divmod-v1'
HARDWARE = (0x04000000, 0x08000000)
# Identifiers only the compiler may emit.  The raw preprocessed text is also
# scanned, so an asm label string such as __asm("_call_via_r2") cannot give
# an ordinary declaration a reserved ELF symbol name.
RESERVED = r'_call_via_|\b(?:__udivsi3|__umodsi3|__divsi3|__modsi3)\b'
ASM = r'\b(?:__asm__|__asm|asm)\b'


def namespace(preprocessed):
    from plausible import strip_comments_and_strings
    import function_thunk_profile as thunks
    thunks.namespace(preprocessed)
    if type(preprocessed) is not str or '\0' in preprocessed or \
            re.search(RESERVED, preprocessed) or re.search(ASM, strip_comments_and_strings(preprocessed)):
        raise ValueError('unsigned thunk runtime, call-via and asm-label spellings are reserved for compiler emission')


def check_link_context(selector, thunks, words, functions, switches, quotient, remainder, flags, contexts):
    if type(selector) is not str or selector != SELECTOR or thunks is not True or \
            type(words) is not int or words != 5 or type(functions) is not dict or functions or \
            type(switches) is not dict or switches or type(quotient) is not dict or \
            type(remainder) is not dict or any(value is not False for value in flags) or \
            any(value is not None for value in contexts):
        raise ValueError('unsigned thunk linking requires its exclusive explicit typed context')


def check_link_bindings(calls, targets, literals, functions, switches, quotient, remainder):
    import function_thunk_profile as thunks
    import unsigned_divmod_thunk_inventory as inventory
    runtimes = inventory.OPERATIONS
    if type(calls) is not dict or functions or switches or type(quotient) is not dict or \
            type(remainder) is not dict or set(quotient) & set(remainder) or \
            quotient | remainder != {site: name for site, target in calls.items()
                                     for name, address in runtimes.items() if target == address} or \
            set(quotient.values()) - {'__udivsi3'} or set(remainder.values()) - {'__umodsi3'} or \
            not quotient | remainder or not any(target in thunks.ALIASES.values() for target in calls.values()):
        raise ValueError('unsigned thunks require actual canonical runtime and thunk calls, without other composition')
    names = {name for name, _ in literals.values()}
    for name, target in targets.items():
        if name in names:
            continue
        if name in runtimes or name in thunks.ALIASES:
            if target != {**runtimes, **thunks.ALIASES}[name]:
                raise ValueError('unsigned thunks require exact canonical call aliases')
        elif re.fullmatch(r'func_[0-9A-F]{8}', name) is None or int(name[5:], 16) != target or \
                inventory.reserved_target(target):
            raise ValueError('unsigned thunks require exact canonical call aliases and typed original objects')
    if set(calls.values()) != {targets[name] for name in targets if name not in names}:
        raise ValueError('unsigned thunk call targets differ from their aliases')


def prove(data, address, rom, mapping, index, calls):
    import unsigned_divmod_thunk_inventory as inventory
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
    import plausible
    import software_double_profile
    import software_float_profile
    import umod_only_ordinary_inventory
    import umodsi3_profile
    import unsigned_divmod_ordinary_inventory
    import unsigned_divmod_thunk_inventory
    import unsigned_remainder_closure_inventory
    import zero_aware_unsigned_quotient_inventory
    modules = (analyze, function_thunk_profile, local_long_branch_profile, match,
        owner_admission_profile, owner_graph_profile, owner_runtime_profile, plausible,
        software_double_profile, software_float_profile, umod_only_ordinary_inventory,
        umodsi3_profile, unsigned_divmod_ordinary_inventory, unsigned_divmod_thunk_inventory,
        unsigned_remainder_closure_inventory, zero_aware_unsigned_quotient_inventory)
    result = {Path(module.__file__).name: hashlib.sha256(Path(module.__file__).read_bytes()).hexdigest()
              for module in modules}
    result[Path(__file__).name] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    return result


def numeric_words(data, address, instructions, literals, rom_size):
    """Every reached untyped pool word: plain numbers, or fixed hardware addresses."""
    import struct
    from capstone.arm import ARM_OP_MEM, ARM_REG_PC
    import modsi3_profile as modsi3
    reached = {((item.address+4) & ~3)+operand.mem.disp-address for item in instructions
               if item.mnemonic == 'ldr' for operand in item.operands
               if operand.type == ARM_OP_MEM and operand.mem.base == ARM_REG_PC and not operand.mem.index}
    if not set(literals) <= reached or any(offset < 0 or offset+4 > len(data) for offset in reached):
        raise ValueError('unsigned thunk typed literals must be reached complete caller words')
    hardware = []
    for offset in sorted(reached - set(literals)):
        value = struct.unpack_from('<I', data, offset)[0]
        if modsi3.address_literal(value):
            # RAM and ROM addresses need typed ABS32 provenance.  Only fixed
            # I/O, palette, VRAM and OAM addresses may stay numeric.
            if not HARDWARE[0] <= value < HARDWARE[1] or modsi3.supported_data(value, rom_size):
                raise ValueError('unsigned thunks require typed provenance for RAM and ROM address words')
            hardware.append([offset, value])
    return hardware


def make_manifest(calls, functions, literals, address, rom, objects, instructions):
    import function_thunk_profile as thunks
    import match
    import unsigned_divmod_thunk_inventory as inventory
    if functions:
        raise ValueError('unsigned thunks exclude typed function literals')
    runtimes = {target: name for name, target in inventory.OPERATIONS.items()}
    aliases = {target: name for name, target in thunks.ALIASES.items()}
    names = match.parse_data_symbols(objects) if literals else {}
    end = max(item.address + item.size for item in instructions)
    for item in instructions:
        for operand in item.operands:
            if item.mnemonic == 'ldr' and operand.type == match.ARM_OP_MEM and operand.mem.base == match.ARM_REG_PC:
                end = max(end, ((item.address+4) & ~3)+operand.mem.disp+4)
    data = rom[address-match.ROM_BASE:end-match.ROM_BASE]
    return {'selector': SELECTOR, 'runtime': thunks.RUNTIME, 'abi': thunks.ABI,
        'frame': match.uses_stack_frame(instructions),
        'calls': [[site-address, f'func_{target:08X}'] for site, target in sorted(calls.items())
                  if target not in runtimes and target not in aliases],
        'functions': [],
        'thunks': [[site-address, aliases[target]] for site, target in sorted(calls.items()) if target in aliases],
        'unsigned_runtime': [[site-address, runtimes[target]] for site, target in sorted(calls.items())
                             if target in runtimes],
        'data': [[offset, name, value-names[name]] for offset, (name, value) in sorted(literals.items())],
        'numeric_hardware_words': numeric_words(data, address, instructions, literals, len(rom)),
        'dependencies': thunks.dependencies({aliases[target] for target in calls.values() if target in aliases}, rom),
        'producer_source_sha256': producer_sources()}


def verify(data, address, rom, mapping, index, objects, manifest):
    import function_thunk_profile as thunks
    import match
    import unsigned_divmod_thunk_inventory as inventory
    keys = {'selector', 'runtime', 'abi', 'frame', 'calls', 'functions', 'thunks', 'unsigned_runtime',
            'data', 'numeric_hardware_words', 'dependencies', 'producer_source_sha256'}
    if type(manifest) is not dict or set(manifest) != keys or \
            manifest['selector'] != SELECTOR or manifest['runtime'] != thunks.RUNTIME or \
            manifest['abi'] != thunks.ABI or type(manifest['frame']) is not bool or \
            manifest['functions'] != [] or manifest['producer_source_sha256'] != producer_sources():
        raise ValueError('unsigned thunk source manifest or producer source bytes differ')
    calls, literals = match.function_address_bindings(data, address, rom, mapping, objects,
        {'calls': manifest['calls'], 'functions': [], 'data': manifest['data']}, allow_empty_functions=True)
    if any(inventory.reserved_target(target) for target in calls.values()):
        raise ValueError('unsigned thunk ordinary calls cannot name runtime or thunk targets')
    occupied = {p for record in manifest['calls'] for p in range(record[0], record[0]+4)} | \
               {p for offset in literals for p in range(offset, offset+4)}
    aliases = {**inventory.OPERATIONS, **thunks.ALIASES}
    for key, allowed in (('thunks', set(thunks.ALIASES)), ('unsigned_runtime', set(inventory.OPERATIONS))):
        records, previous = manifest[key], -1
        if type(records) is not list or not records:
            raise ValueError('unsigned thunks require canonical runtime and thunk call records')
        for record in records:
            if type(record) is not list or len(record) != 2 or type(record[0]) is not int or \
                    type(record[1]) is not str or record[1] not in allowed:
                raise ValueError('unsigned thunk call record is malformed')
            offset = record[0]
            if offset <= previous or offset < 0 or offset % 2 or offset+4 > len(data) or \
                    occupied.intersection(range(offset, offset+4)):
                raise ValueError('unsigned thunk call record is misaligned, incomplete or overlapping')
            previous = offset
            calls[address+offset] = aliases[record[1]]
            occupied.update(range(offset, offset+4))
    if manifest['dependencies'] != thunks.dependencies({name for _, name in manifest['thunks']}, rom):
        raise ValueError('unsigned thunk canonical dependencies differ')
    proof, instructions = prove(data, address, rom, mapping, index, calls)
    thunks.verify_data_bindings(calls, literals, match.parse_data_symbols(objects) if literals else {},
                                json.loads(mapping))
    match.verify_data_literals(instructions, address, literals)
    if numeric_words(data, address, instructions, literals, len(rom)) != manifest['numeric_hardware_words'] or \
            match.uses_stack_frame(instructions) != manifest['frame']:
        raise ValueError('unsigned thunks require reached typed literals and the exact saved frame')
    # The inventory re-proves a nonzero all-path r1 constant at each of these
    # sites on every verification; the values stay in its fresh proof.
    if [offset for offset, _ in proof['caller_divisors']] != [offset for offset, _ in manifest['unsigned_runtime']]:
        raise ValueError('unsigned thunk manifest requires an actual all-path divisor at every runtime call')
    return instructions
