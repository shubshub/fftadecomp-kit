"""Selected compiler memcpy identity transport with unchanged native buffer replay."""
import hashlib
from pathlib import Path

import compiler_copy80_caller_prerequisite as caller

SELECTOR = 'named-data-buffer-compiler-copy80-binding-v1'
SCHEMA = 'elf-symbol-thumb-named-data-buffer-compiler-copy80-binding-v1'
CONTROL_FLOW = 'complete named-data buffer owner with conditional compiler memcpy identity'
CONTRACT = ('Original compiler memcpy identity only, under a compatible returning ordinary ABI. '
    'The count80 helper relation is conditional on every recorded prerequisite. '
    'No physical access, object extent, readability, writability, nonaliasing, '
    'C compatibility, copy effect for an actual invocation, or termination is proved. '
    'Native frame, alias, return provenance and other typed binding rules remain unchanged.')


def prerequisite(data, address, rom, mapping, index, objects):
    return caller.verify(data, address, rom, mapping, index, objects)


def original_target(image, address, rom, mapping, index, objects, site, target):
    import match
    symbol, offset = match.function_record(image, f'func_{address:08X}', address, True)
    data = rom[address-match.ROM_BASE:address-match.ROM_BASE+symbol['size']]
    proof = prerequisite(data, address, rom, mapping, index, objects)
    if offset or target['name'] != 'memcpy' or target['size'] != 0 or \
            target['type'] not in (0, 2) or target['bind'] != 1 or \
            target['value'] or target['section'] or \
            sum(row['name'] == 'memcpy' for row in image['symbols']) != 1 or \
            site != proof['call_site']-address:
        raise ValueError('compiler copy requires authentic unique memcpy identity at actual native site')
    return proof['helper']['helper']


def check_original(bindings, targets, image, address, rom, mapping, index, objects):
    copies = [(site, name) for site, name in bindings['calls'] if name == 'memcpy']
    if len(copies) != 1 or 'memcpy' not in targets or bindings['functions'] or \
            bindings['switches'] or not bindings['data']:
        raise ValueError('compiler copy requires exactly one memcpy call and named data only')
    target = next(row for row in image['symbols'] if row['name'] == 'memcpy')
    destination = original_target(image, address, rom, mapping, index, objects, copies[0][0], target)
    if any(name != 'memcpy' and value == (destination, False) for name, value in targets.items()):
        raise ValueError('compiler copy helper cannot be laundered through another call identity')


def native_manifest(data, address, rom, mapping, index, objects, bindings):
    proof = prerequisite(data, address, rom, mapping, index, objects)
    site, target = proof['call_site']-address, proof['helper']['helper']
    if type(bindings) is not dict or set(bindings) != {'calls','data','functions','switches'}:
        raise ValueError('typed owner bindings are required')
    if [site, 'memcpy'] not in bindings['calls'] or \
            sum(name == 'memcpy' for _, name in bindings['calls']) != 1 or \
            any(name == f'func_{target:08X}' for _, name in bindings['calls']):
        raise ValueError('compiler copy bindings differ from authentic actual native site')
    return dict(schema=SCHEMA, contract=CONTRACT, caller_prerequisite=proof,
        physical_access_proved=False, object_extent_proved=False, nonaliasing_proved=False,
        C_compatibility_proved=False, termination_proved=False,
        producer_sha256={path.name: hashlib.sha256(path.read_bytes()).hexdigest()
            for path in Path(__file__).parent.glob('*.py')})
