"""Original memcpy ELF identity composed with exact finite local-copy replay."""
import hashlib
from pathlib import Path

import finite_small_local_copy_profile as finite
import match

SELECTOR = 'named-data-buffer-finite-small-copy-binding-v1'
SCHEMA = 'elf-symbol-thumb-named-data-buffer-finite-small-copy-binding-v1'
CONTROL_FLOW = 'complete named-data owner with genuine compiler memcpy identity and exact bounded local halfword cursor replay'
CONTRACT = ('Exact original compiler memcpy relocation and named ROM source correspondence; '
    'complete native frame, alias and bounded-loop replay. Runtime source immutability, '
    'ordinary memory validity, external-store nonalias and C/ABI compatibility remain '
    'explicit conditional premises. No physical permission or unconditional memory-safety claim.')


def prerequisite(data,address,rom,mapping,index,objects):
    return finite.LoopProof(data,address,rom,mapping,index,objects,selector=finite.SELECTOR).copy


def original_target(image,address,rom,mapping,index,objects,site,target):
    symbol,offset=match.function_record(image,f'func_{address:08X}',address,True)
    data=rom[address-match.ROM_BASE:address-match.ROM_BASE+symbol['size']]
    proof=prerequisite(data,address,rom,mapping,index,objects)
    if offset or target['name']!='memcpy' or target['size'] or target['type'] not in (0,2) or \
            target['bind']!=1 or target['value'] or target['section'] or \
            sum(row['name']=='memcpy' for row in image['symbols'])!=1 or site!=proof['call_site']-address:
        raise ValueError('small copy requires unique genuine undefined memcpy identity at the actual native site')
    return proof['target']


def check_original(bindings,targets,image,address,rom,mapping,index,objects):
    symbol,_=match.function_record(image,f'func_{address:08X}',address,True)
    data=rom[address-match.ROM_BASE:address-match.ROM_BASE+symbol['size']]
    proof=prerequisite(data,address,rom,mapping,index,objects)
    expected=[proof['call_site']-address,'memcpy']
    source=[proof['source_literal_offset'],proof['source_identity'],0]
    if bindings['calls']!=[expected] or bindings['functions'] or bindings['switches'] or \
            source not in bindings['data'] or targets.get('memcpy')!=(proof['target'],False) or \
            targets.get(proof['source_identity'])!=(proof['source_point'],True):
        raise ValueError('small copy original bindings differ from actual memcpy and zero-addend named ROM source')
    # Generic owner validation authenticates every additional named literal.
    if any(name!='memcpy' and value==(proof['target'],False) for name,value in targets.items()):
        raise ValueError('small copy helper cannot be rebound through another function name')


def check_linked(linked,address,targets):
    """Check actual linked ABS symbol roles in addition to generic byte checks."""
    function,_=match.function_record(linked,f'func_{address:08X}',address,True)
    if any(row['type']==2 and row['section']==linked['text_index'] and row is not function
           for row in linked['symbols']):
        raise ValueError('small-copy linked owner contains another text function identity')
    for name,(point,is_object) in targets.items():
        rows=[row for row in linked['symbols'] if row['name']==name]
        if len(rows)!=1 or rows[0]['section']!=0xFFF1 or rows[0]['bind']!=1 or rows[0]['size'] or \
                rows[0]['type']!=(1 if is_object else 2) or \
                rows[0]['value']!=(point if is_object else point|1):
            raise ValueError('small-copy linked symbol differs from its exact typed original binding')


def prove(data,address,rom,mapping,index,objects,bindings):
    native,instructions=finite.verify(data,address,rom,mapping,index,objects,selector=finite.SELECTOR)
    copy=native['caller']
    if type(bindings) is not dict or set(bindings)!={'calls','data','functions','switches'} or \
            bindings['calls']!=[[copy['call_site']-address,'memcpy']] or \
            bindings['functions'] or bindings['switches'] or \
            [copy['source_literal_offset'],copy['source_identity'],0] not in bindings['data']:
        raise ValueError('small-copy native binding does not identify exact compiler call and named ROM source')
    return dict(schema=SCHEMA,instructions=len(instructions),calls=bindings['calls'],runtime_calls=[],
        partition=copy['partition'],finite_small_copy=native,contract=CONTRACT,
        source_correspondence=dict(name=copy['source_identity'],point=copy['source_point'],
            literal_offset=copy['source_literal_offset'],count=copy['count'],
            source_bytes_sha256=copy['source_bytes_sha256']),
        physical_access_proved=False,nonaliasing_proved=False,C_compatibility_proved=False,
        producer_sha256={path.name:hashlib.sha256(path.read_bytes()).hexdigest()
                         for path in Path(__file__).parent.glob('*.py')})
