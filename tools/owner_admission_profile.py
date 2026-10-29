"""Explicit complete-owner composition with original-ELF and source replay.

Local BL control, guarded word switches, restoring stack aliases, canonical
indirect thunks and constant nonzero unsigned division share one closed CFG.
The selector grants no permission to alter the compiler or bypass source checks.
"""
import argparse
from contextvars import ContextVar
import hashlib
import json
from pathlib import Path
import re
import shlex
import struct
import subprocess
import sys
import tempfile

import analyze
import owner_graph_profile as graph
import owner_runtime_profile as runtime
import function_thunk_profile as thunk
import ignored_leaf_alias_profile as ignored_leaf
import named_data_buffer_profile as named_buffer
import static_callback_buffer_profile as static_buffer
import protected_descriptor_word_profile as descriptor
import watched_switch_preservation_profile as watched_switch
import descriptor_output_alias_profile as output_alias
import descriptor_single_store_profile as single_store
from inert_spin_profile import fixed_configuration, index_snapshot, validate_span, marker_text

SCHEMA = 'elf-symbol-thumb-restoring-owner-runtime-v1'
SELECTOR = 'restoring-owner-runtime-v1'
CONTROL_FLOW = 'complete restoring Thumb owner; local BL control, guarded switches, canonical thunks and constant unsigned division'
ACYCLIC_SELECTOR = 'restoring-owner-acyclic-v1'
ACYCLIC_SCHEMA = 'elf-symbol-thumb-acyclic-stack-alias-v1'
ACYCLIC_STATE_BUDGET = 4096
ACYCLIC_CONTROL_FLOW = 'complete acyclic Thumb owner; exact bounded path states and ordinary direct-call ABI summaries'
_replay = ContextVar('owner_runtime_replay', default=False)


def text(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def selected(report):
    relevant = SCHEMA in report or ACYCLIC_SCHEMA in report or ignored_leaf.SCHEMA in report or named_buffer.SCHEMA in report or static_buffer.SCHEMA in report or descriptor.SCHEMA in report or watched_switch.SCHEMA in report or output_alias.SCHEMA in report or single_store.SCHEMA in report or any(marker_text(line).startswith('* owner runtime')
                                      for line in report.splitlines())
    if not relevant:
        return False
    fields = [line for line in report.splitlines() if marker_text(line).startswith('* verification')]
    if fields not in ([f'* verification: `{SCHEMA}`'], [f'* verification: `{ACYCLIC_SCHEMA}`'],
                      [f'* verification: `{ignored_leaf.SCHEMA}`'],
                      [f'* verification: `{named_buffer.SCHEMA}`'],
                      [f'* verification: `{static_buffer.SCHEMA}`'],
                      [f'* verification: `{descriptor.SCHEMA}`'],
                      [f'* verification: `{watched_switch.SCHEMA}`'],
                      [f'* verification: `{output_alias.SCHEMA}`'],
                      [f'* verification: `{single_store.SCHEMA}`']) or any(marker_text(line).startswith((
            '* function-address', '* unsigned division', '* software double', '* software float',
            '* inert spin', '* switches', '* buffer calls', '* signed quotient', '* signed remainder'))
            for line in report.splitlines()):
        raise ValueError('mixed or malformed complete-owner profile')
    return True


def selector_for_report(report):
    if not selected(report):
        raise ValueError('not a complete-owner report')
    if f'* verification: `{ignored_leaf.SCHEMA}`' in report.splitlines():
        return ignored_leaf.SELECTOR
    if f'* verification: `{single_store.SCHEMA}`' in report.splitlines():
        return single_store.SELECTOR
    if f'* verification: `{output_alias.SCHEMA}`' in report.splitlines():
        return output_alias.SELECTOR
    if f'* verification: `{watched_switch.SCHEMA}`' in report.splitlines():
        return watched_switch.SELECTOR
    if f'* verification: `{descriptor.SCHEMA}`' in report.splitlines():
        return descriptor.SELECTOR
    if f'* verification: `{static_buffer.SCHEMA}`' in report.splitlines():
        return static_buffer.SELECTOR
    if f'* verification: `{named_buffer.SCHEMA}`' in report.splitlines():
        return named_buffer.SELECTOR
    return ACYCLIC_SELECTOR if f'* verification: `{ACYCLIC_SCHEMA}`' in report.splitlines() else SELECTOR


def refine(data, address, mapping):
    return analyze.refine_function(data, address, json.loads(mapping), max_bytes=len(data),
            max_instructions=len(data)//2, rom_end=0x09000000, same_owner_long_branches=True)


def verify(data, address, rom, mapping, index, objects, manifest=None, *, bindings=None,
           selector=SELECTOR):
    """Replay complete structural/frame/runtime proof before typed provenance."""
    import match
    if selector not in (SELECTOR, ACYCLIC_SELECTOR, ignored_leaf.SELECTOR, named_buffer.SELECTOR, static_buffer.SELECTOR, descriptor.SELECTOR, watched_switch.SELECTOR, output_alias.SELECTOR, single_store.SELECTOR):
        raise ValueError('unknown complete-owner selector')
    buffer_selector = selector in (named_buffer.SELECTOR, static_buffer.SELECTOR, descriptor.SELECTOR, watched_switch.SELECTOR, output_alias.SELECTOR, single_store.SELECTOR)
    if buffer_selector and len(data) > named_buffer.MAX_BYTES:
        raise ValueError('named-data buffer caller exceeds bounded owner size')
    validate_span(data,address,rom,mapping,index)
    if buffer_selector:
        named_buffer.validate_owner(data,address,rom,mapping,index)
    refinement = refine(data,address,mapping)
    selected_rows=[line.split() for line in index.decode().splitlines()
                   if line.split() and line.split()[0]==f'{address:08X}']
    if not buffer_selector and (len(selected_rows)!=1 or len(selected_rows[0])<4 or int(selected_rows[0][3])!=refinement['instrs']):
        raise ValueError('complete-owner text reachable instruction count differs')
    ins, edges, branches, calls, words = graph.graph(data,address,refinement)
    if buffer_selector:
        module = single_store if selector == single_store.SELECTOR else output_alias if selector == output_alias.SELECTOR else watched_switch if selector == watched_switch.SELECTOR else descriptor if selector == descriptor.SELECTOR else static_buffer if selector == static_buffer.SELECTOR else named_buffer
        if branches or words:
            raise ValueError('named-data buffer caller excludes local BL and word switches')
        for destination in calls.values():
            match.function_address_target(f'func_{destination:08X}', json.loads(mapping),
                                          address, len(data), len(rom))
        buffers = (single_store.DescriptorSingleStoreProof if selector == single_store.SELECTOR else
                   output_alias.DescriptorOutputAliasProof if selector == output_alias.SELECTOR else
                   watched_switch.WatchedSwitchPreservationProof if selector == watched_switch.SELECTOR else
                   descriptor.ProtectedDescriptorWordProof if selector == descriptor.SELECTOR else
                   static_buffer.StaticCallbackBufferProof if selector == static_buffer.SELECTOR else
                   named_buffer.NamedDataBufferProof)(rom, mapping, index, objects)
        if selector in (descriptor.SELECTOR, watched_switch.SELECTOR, output_alias.SELECTOR, single_store.SELECTOR):
            buffers.check_lifetime(data, address, list(ins.values()))
        verified = match.verify_leaf_instructions(data, address, True, calls, buffer_proof=buffers)
        if not buffers.dependencies or set(ins) != {item.address for item in verified}:
            raise ValueError('named-data buffer profile requires exact inspected buffer calls')
        if selector in (static_buffer.SELECTOR, descriptor.SELECTOR) and not buffers.callbacks:
            raise ValueError('static callback profile requires an actual resolved buffer callback')
        proof = {'schema': module.SCHEMA, 'instructions': len(verified),
                 'calls': [[site-address, f'func_{target:08X}'] for site,target in sorted(calls.items())],
                 'runtime_calls': [], 'partition': graph.partition(data,address,refinement,ins,words),
                 'buffers': {'dependency_budget': module.MAX_DEPENDENCIES,
                    'owner_byte_budget': named_buffer.MAX_BYTES,
                    'dependencies': [buffers.records[target] for target in sorted(buffers.records)]}}
        if selector in (static_buffer.SELECTOR, descriptor.SELECTOR, watched_switch.SELECTOR, output_alias.SELECTOR, single_store.SELECTOR):
            proof['buffers'].update(context_budget=static_buffer.MAX_CONTEXTS,
                                    callbacks=buffers.observations())
        if selector in (output_alias.SELECTOR,single_store.SELECTOR):
            if not buffers.frame_observations() or not any(
                    row['kind']=='pointer' for row in buffers.word_observations()):
                raise ValueError('descriptor output alias profile requires actual callee stack origin and pointer-word replay')
            proof['buffers'].update(frame_aliases=buffers.frame_observations(),
                native_frame_replays=buffers.native_frame_observations(),
                word_reads=buffers.word_observations(), switch_contexts=buffers.switch_observations(),
                stack_byte_budget=output_alias.MAX_STACK_BYTES,
                lifetime='exact live root and callee frames; allocation after deallocation refused')
        if selector == single_store.SELECTOR:
            if not buffers.store_observations():
                raise ValueError('single-word store profile requires an actual bounded STMIA replay')
            proof['buffers']['single_word_stores'] = buffers.store_observations()
        if selector == watched_switch.SELECTOR:
            if not buffers.switch_observations():
                raise ValueError('watched switch profile requires an actual watched switch context')
            proof['buffers'].update(switch_contexts=buffers.switch_observations(),
                word_reads=buffers.word_observations(),
                lifetime='allocated root-frame words; allocation after deallocation refused')
        if selector == descriptor.SELECTOR:
            if not any(row['kind']=='pointer' for row in buffers.word_observations()):
                raise ValueError('descriptor profile requires an actual exact pointer-word reload')
            proof['buffers'].update(word_reads=buffers.word_observations(),
                lifetime='allocated root-frame words; allocation after deallocation refused')
    elif selector in (ACYCLIC_SELECTOR, ignored_leaf.SELECTOR):
        if branches or words:
            raise ValueError('acyclic owner excludes local BL and word switches')
        for destination in calls.values():
            match.function_address_target(f'func_{destination:08X}', json.loads(mapping),
                                          address, len(data), len(rom))
        aliases = None
        if selector == ignored_leaf.SELECTOR:
            entries = json.loads(mapping)
            row = next(row for row in entries if int(row['rom'], 16) == address)
            if type(row.get('instrs')) is not int or row['instrs'] != len(ins):
                raise ValueError('ignored leaf caller JSON reachable instruction count differs')
            aliases = ignored_leaf.IgnoredLeafAliasProof(rom,mapping,index,objects,address,len(data),calls)
        verified = match.verify_leaf_instructions(data,address,True,calls,
            acyclic_state_budget=ACYCLIC_STATE_BUDGET, ignored_leaf_alias_proof=aliases)
        if {item.address for item in verified} != set(ins):
            raise ValueError('acyclic native verification differs from complete owner CFG')
        proof = {'schema': ACYCLIC_SCHEMA, 'state_budget': ACYCLIC_STATE_BUDGET,
                 'instructions': len(verified), 'calls': [[site-address, f'func_{target:08X}']
                    for site,target in sorted(calls.items())], 'runtime_calls': [],
                 'partition': graph.partition(data,address,refinement,ins,words)}
        if aliases is not None:
            if not aliases.observations:
                raise ValueError('ignored leaf selector requires an actual discarded incoming alias')
            proof.update(schema=ignored_leaf.SCHEMA, ignored_leaf_aliases=aliases.manifest())
    else:
        proof = runtime.verify(data,address,rom,mapping,refinement)
    ordinary = {'calls':proof['calls'], 'data':[], 'functions':[]}
    if bindings is None:
        if manifest is None:
            raise ValueError('typed owner bindings are required')
        bindings = manifest.get('bindings')
    if type(bindings) is not dict or set(bindings) != {'calls','data','functions','switches'} or \
            bindings['calls'] != sorted(proof['calls'] + proof['runtime_calls']):
        raise ValueError('owner bindings do not cover every exact reached external call')
    ordinary.update(data=bindings['data'],functions=bindings['functions'])
    if selector == named_buffer.SELECTOR and (not bindings['data'] or bindings['functions'] or bindings['switches']):
        raise ValueError('named-data buffers require actual named object relocations and exclude function literals')
    _, literals = match.function_address_bindings(data,address,rom,mapping,objects,ordinary,
                                                 allow_empty_functions=True)
    if bindings['switches'] != [[offset, addend] for offset,addend in sorted(words.items())]:
        raise ValueError('owner local relocations do not equal guarded switch words')
    match.verify_data_literals(ins.values(),address,literals)
    functions = {offset:(name,struct.unpack_from('<I',data,offset)[0])
                 for offset,name in bindings['functions']}
    thunk.verify_literal_bindings(data,address,ins.values(),calls,mapping,functions)
    thunk.verify_data_bindings(calls,literals,match.parse_data_symbols(objects),json.loads(mapping))
    # All actual address-domain PC words require typed object/function provenance.
    # Exact local switch words are proved separately; numerical scalars remain scalar.
    address_words = {row['address']-address for row in proof['partition']['words']
        if row['load_sites'] and not row['switch_word'] and
        (0x02000000 <= row['value'] < 0x04000000 or
         0x04000000 <= row['value'] < 0x08000000 or
         0x08000000 <= row['value'] < 0x09000000)}
    if address_words != set(literals):
        raise ValueError('owner address literals require exact typed object/function coverage')
    schema = single_store.SCHEMA if selector == single_store.SELECTOR else \
        output_alias.SCHEMA if selector == output_alias.SELECTOR else \
        watched_switch.SCHEMA if selector == watched_switch.SELECTOR else \
        descriptor.SCHEMA if selector == descriptor.SELECTOR else \
        static_buffer.SCHEMA if selector == static_buffer.SELECTOR else \
        named_buffer.SCHEMA if selector == named_buffer.SELECTOR else \
        ignored_leaf.SCHEMA if selector == ignored_leaf.SELECTOR else \
        ACYCLIC_SCHEMA if selector == ACYCLIC_SELECTOR else SCHEMA
    observed={'profile':schema,
              'proof':proof,'bindings':bindings}
    if manifest is not None and text(observed)!=text(manifest):
        raise ValueError('owner manifest differs from complete fresh native replay')
    return observed, list(ins.values())



def preflight(data,address,rom,mapping,index,objects, *, selector=SELECTOR):
    """Inventory bindings derive only reached words and current named objects.

    This record has no source/ELF credit. Later compiler relocations must independently
    reconstruct the same calls, local tables and typed object/function words.
    """
    import match
    refinement=refine(data,address,mapping)
    instructions,edges,branches,calls,words=graph.graph(data,address,refinement)
    partition=graph.partition(data,address,refinement,instructions,words)
    entries=json.loads(mapping);names=match.parse_data_symbols(objects)
    reverse={value:name for name,value in thunk.ALIASES.items()}
    bindings={'calls':[[site-address,reverse.get(target,'__udivsi3' if target==match.UDIVSI3_ADDRESS
                     else f'func_{target:08X}')]for site,target in sorted(calls.items())],
              'data':[],'functions':[],'switches':[[offset,value]for offset,value in sorted(words.items())]}
    for word in partition['words']:
        value=word['value'];offset=word['address']-address
        if not word['load_sites'] or word['switch_word'] or not 0x02000000<=value<0x09000000:
            continue
        owners=[row for row in entries if int(row['rom'],16)==value&~1]
        if owners:
            if value%2!=1 or len(owners)!=1:
                raise ValueError('literal code entry requires unambiguous typed Thumb function pointer')
            bindings['functions'].append([offset,f'func_{value&~1:08X}'])
        else:
            candidates=sorted(name for name,base in names.items() if base==value)
            if not candidates:
                raise ValueError(f'owner literal requires genuine named object proof at {value:08X}')
            bindings['data'].append([offset,candidates[0],0])
    observed,verified=verify(data,address,rom,mapping,index,objects,bindings=bindings,
                             selector=selector)
    return observed,verified,refinement


def original_bindings(image,address,rom,mapping,objects, *, selector=SELECTOR):
    """Validate every original relocation, with no rewriting of the input ELF."""
    import match
    if image['type']!=1:
        raise ValueError('owner requires original relocatable ELF')
    match.allocated_text_only(image)
    symbol,offset=match.function_record(image,f'func_{address:08X}',address,True)
    if offset or symbol['size']!=len(image['text']) or any(
            item['type']==2 and item is not symbol and item['section'] or
            item['type']==1 and item['section'] or re.fullmatch(r'\$a(?:\..*)?',item['name'])
            for item in image['symbols']):
        raise ValueError('owner requires sole complete Thumb ELF function')
    size=symbol['size']; entries=json.loads(mapping); names=match.parse_data_symbols(objects)
    result={'calls':[],'data':[],'functions':[],'switches':[]}; targets={}; occupied=set()
    decoder=match.Cs(match.CS_ARCH_ARM,match.CS_MODE_THUMB);decoder.detail=True
    for section_index in image['relocations']:
        section=image['sections'][section_index]
        if section[1]!=9 or section[7]!=image['text_index'] or section[9]!=8 or section[5]%8:
            raise ValueError('owner requires canonical .text REL relocations')
        symbols=image['symbol_tables'].get(section[6])
        for position in range(0,section[5],8):
            site,info=struct.unpack_from('<II',image['section_data'][section_index],position)
            kind=info&255
            if symbols is None or info>>8>=len(symbols) or kind not in (2,10) or \
                    site<0 or site+4>size or occupied.intersection(range(site,site+4)):
                raise ValueError('invalid, unsupported or overlapping owner relocation')
            occupied.update(range(site,site+4)); target=symbols[info>>8];name=target['name']
            if kind==2 and target['section']:
                if target['type']!=3 or target['section']!=image['text_index'] or \
                        target['value'] or target['bind'] or (address+site)%4:
                    raise ValueError('local owner relocation requires zero-valued .text section symbol')
                addend=struct.unpack_from('<I',image['text'],site)[0]
                result['switches'].append([site,addend]);continue
            if target['section'] or target['value'] or target['bind']!=1 or \
                    sum(item['name']==name for item in image['symbols'])!=1:
                raise ValueError('owner requires unique undefined zero-valued global symbols')
            if kind==10:
                instruction=next(decoder.disasm(image['text'][site:site+4],address+site),None)
                if site%2 or target['type'] not in (0,2) or instruction is None or \
                        instruction.id!=match.ARM_INS_BL or instruction.size!=4 or \
                        instruction.operands[0].imm!=address+site:
                    raise ValueError('owner call requires canonical Thumb BL zero addend')
                destination=(thunk.ALIASES[name] if name in thunk.ALIASES else
                    match.UDIVSI3_ADDRESS if name=='__udivsi3' else
                    match.function_address_target(name,entries,address,size,len(rom)))
                result['calls'].append([site,name]);targets[name]=(destination,False)
            else:
                if (address+site)%4:
                    raise ValueError('unaligned owner literal relocation')
                addend=struct.unpack_from('<i',image['text'],site)[0]
                if name.startswith('func_'):
                    if target['type'] not in (0,2) or addend:
                        raise ValueError('function pointer requires canonical zero addend')
                    destination=match.function_address_target(name,entries,address,size,len(rom))
                    result['functions'].append([site,name]);targets[name]=(destination,False)
                else:
                    if target['type'] not in (0,1) or name not in names:
                        raise ValueError('unmapped or non-object owner literal')
                    result['data'].append([site,name,addend]);targets[name]=(names[name],True)
    if any(item['name'] and not item['section'] and item['name'] not in targets
           for item in image['symbols']):
        raise ValueError('unresolved owner symbol outside exact binding roles')
    for records in result.values():records.sort()
    if selector in (ACYCLIC_SELECTOR, ignored_leaf.SELECTOR, named_buffer.SELECTOR, static_buffer.SELECTOR, descriptor.SELECTOR, watched_switch.SELECTOR, output_alias.SELECTOR, single_store.SELECTOR):
        if any(destination in thunk.ALIASES.values() or match.is_udivsi3_address(destination)
               for destination,is_object in targets.values() if not is_object):
            raise ValueError('acyclic owner excludes arithmetic runtimes and indirect thunks')
    elif selector != SELECTOR:
        raise ValueError('unknown complete-owner selector')
    elif '__udivsi3' not in targets or not any(name in thunk.ALIASES for name in targets):
        raise ValueError('owner profile requires actual compiler UDIV and indirect thunk calls')
    return result,targets


def object_bytes(runner,workspace,args,original,address,rom,mapping,objects, *, selector=SELECTOR):
    import match
    fixed_configuration(args)
    preprocessed=runner.read_binary(workspace+'/f.i').decode()
    thunk.namespace(preprocessed)
    from plausible import strip_comments_and_strings
    if re.search(r'\b__udivsi3\b',strip_comments_and_strings(preprocessed)):
        raise ValueError('division identifiers are reserved for compiler emission')
    bindings,targets=original_bindings(original,address,rom,mapping,objects,selector=selector)
    definitions=['.syntax unified','.thumb']
    for name,(value,is_object) in sorted(targets.items()):
        definitions += [f'.global {name}',f'.type {name}, %'+('object' if is_object else 'function'),
                        f'.set {name}, 0x{value:08X}' if is_object else
                        f'.thumb_set {name}, 0x{value|1:08X}']
    runner.write_text(workspace+'/f.known.s','\n'.join(definitions)+'\n')
    runner.write_text(workspace+'/f.ld',f'SECTIONS {{ .text 0x{address:08X} : {{ *(.text) *(.glue_7) *(.glue_7t) }} '
        '.data 0 : { *(.data) } .bss 0 : { *(.bss) } .ARM.attributes 0 : { *(.ARM.attributes) } '
        '.unexpected 0 : { *(.vfp11_veneer) *(.v4_bx) *(.iplt) *(.igot.plt) } '
        '.rel.iplt 0 : { *(.rel.iplt) } ASSERT(SIZEOF(.unexpected)==0,"unexpected stubs") '
        'ASSERT(SIZEOF(.rel.iplt)==0,"unexpected relocations") /DISCARD/ : { *(.comment) *(.note.GNU-stack) } }')
    quoted=shlex.quote(workspace)
    runner.sh(f'{args.assembler} -mthumb-interwork {quoted}/f.known.s -o {quoted}/f.known.o')
    runner.sh(f'{args.linker} --fatal-warnings --no-undefined --no-relax --orphan-handling=error '
              f'-T {quoted}/f.ld -e func_{address:08X} {quoted}/f.o {quoted}/f.known.o -o {quoted}/f.elf')
    linked=match.elf_image(runner.read_binary(workspace+'/f.elf'))
    match.allocated_text_only(linked)
    record,offset=match.function_record(linked,f'func_{address:08X}',address,True)
    if linked['type']!=2 or offset or linked['relocations'] or \
            record['size']!=len(original['text']) or len(linked['text'])!=len(original['text']):
        raise ValueError('linker altered complete owner extent or retained relocations')
    expected=bytearray(original['text']);decoder=match.Cs(match.CS_ARCH_ARM,match.CS_MODE_THUMB);decoder.detail=True
    for site,name in bindings['calls']:
        item=next(decoder.disasm(linked['text'][site:site+4],address+site),None)
        if item is None or item.id!=match.ARM_INS_BL or item.size!=4 or \
                item.operands[0].imm!=targets[name][0]:
            raise ValueError('linked canonical call target differs from original symbol binding')
        expected[site:site+4]=linked['text'][site:site+4]
    for site,addend in bindings['switches']:struct.pack_into('<I',expected,site,address+addend)
    for site,name,addend in bindings['data']:struct.pack_into('<I',expected,site,targets[name][0]+addend)
    for site,name in bindings['functions']:struct.pack_into('<I',expected,site,targets[name][0]|1)
    if bytes(expected)!=linked['text']:
        raise ValueError('linker changed bytes outside exact original relocations')
    return linked['text'],bindings


def fingerprint(address,data,manifest,source,mapping,index,objects,rom,original_elf=None):
    import match
    parts=[manifest['profile'].encode(),address.to_bytes(4,'little'),data,text(manifest).encode(),source.encode(),
           mapping,index,b'absent' if objects is None else objects,hashlib.sha256(rom).digest(),
           text([match.DEFAULT_CC,match.DEFAULT_CPP,match.DEFAULT_AS,match.DEFAULT_OBJCOPY,
                 match.DEFAULT_LD,match.DEFAULT_FLAGS]).encode()]
    if manifest['profile'] in (named_buffer.SCHEMA, static_buffer.SCHEMA, descriptor.SCHEMA, watched_switch.SCHEMA, output_alias.SCHEMA, single_store.SCHEMA):
        if not isinstance(original_elf, bytes):
            raise ValueError('named-data buffer evidence requires original ELF identity')
        parts.append(hashlib.sha256(original_elf).digest())
    return sha(b''.join(len(value).to_bytes(8,'little')+value for value in parts))


def build(root,address,args=None,expected=None, *, selector=SELECTOR):
    """Fresh fixed-toolchain compilation and complete original-ELF provenance."""
    import match
    from match_evidence import source_paths,source_fingerprint,mapping_snapshot,data_snapshot,report_rom_path
    root=Path(root)
    args=args or argparse.Namespace(cc=match.DEFAULT_CC,cpp=match.DEFAULT_CPP,assembler=match.DEFAULT_AS,
        objcopy=match.DEFAULT_OBJCOPY,linker=match.DEFAULT_LD,flags=match.DEFAULT_FLAGS)
    fixed_configuration(args)
    source=source_fingerprint(root,address);mapping=mapping_snapshot(root);index=index_snapshot(root)
    objects=data_snapshot(root);rom_path=report_rom_path(root);rom=Path(rom_path).read_bytes()
    candidates=list((root/'src').rglob(f'{address:08X}.c'))
    if len(candidates)!=1:raise ValueError('owner requires one unique source')
    (root/'build').mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='owner_replay_',dir=root/'build') as directory:
        capture=Path(directory)
        for path in source_paths(root,address):
            destination=capture/path.relative_to(root);destination.parent.mkdir(parents=True,exist_ok=True)
            destination.write_bytes(path.read_bytes())
        runner=match.Runner(match.DEFAULT_CC,'Ubuntu',match.DEFAULT_WSL_PATH,root=capture,timeout=120)
        with runner.workspace() as workspace:
            raw,_,original=match.compile_object(runner,workspace,args,capture,address,
                                               candidates[0].relative_to(root).as_posix())
            data,bindings=object_bytes(runner,workspace,args,original,address,rom,mapping,objects,
                                      selector=selector)
            manifest,instructions=verify(data,address,rom,mapping,index,objects,expected,
                                         bindings=bindings,selector=selector)
        check=match._run_replay_process([sys.executable,str(Path(__file__).with_name('plausible.py')),
            '--quiet','--addr',f'0x{address:08X}','--json']+[str(p) for p in source_paths(capture,address)],capture,120)
        findings,allowed=match.plausibility_result(check,address)
        if findings or allowed or source_fingerprint(capture,address)!=source:
            raise ValueError('owner source is implausible or changed during captured compilation')
    if source_fingerprint(root,address)!=source or mapping_snapshot(root)!=mapping or \
            index_snapshot(root)!=index or data_snapshot(root)!=objects or \
            report_rom_path(root)!=rom_path or Path(rom_path).read_bytes()!=rom:
        raise ValueError('owner source, maps, headers or ROM changed during native verification')
    return data,manifest,source,mapping,index,objects,rom,len(instructions),raw


def render(address,result):
    import match
    data,manifest,source,mapping,index,objects,rom,count,original_elf=result
    acyclic = manifest['profile'] == ACYCLIC_SCHEMA
    ignored = manifest['profile'] == ignored_leaf.SCHEMA
    store = manifest['profile'] == single_store.SCHEMA
    output = manifest['profile'] == output_alias.SCHEMA
    switch = manifest['profile'] == watched_switch.SCHEMA
    words = manifest['profile'] == descriptor.SCHEMA
    static = manifest['profile'] == static_buffer.SCHEMA
    buffers = manifest['profile'] in (named_buffer.SCHEMA, static_buffer.SCHEMA, descriptor.SCHEMA, watched_switch.SCHEMA, output_alias.SCHEMA, single_store.SCHEMA)
    evidence={'address':address,'bytes':len(data),'instructions':count,'source_sha256':source,
        'mapping_sha256':sha(mapping),'index_sha256':sha(index),'objects_sha256':None if objects is None else sha(objects),
        'rom_sha256':sha(rom),'compiler':[match.DEFAULT_CC,match.DEFAULT_FLAGS],
        'manifest':manifest,'fingerprint':fingerprint(address,data,manifest,source,mapping,index,objects,rom,
                                                     original_elf if buffers else None)}
    if buffers:
        evidence['original_elf_sha256'] = sha(original_elf)
    return '\n'.join([f'# 0x{address:08X}','',f'* verification: `{manifest["profile"]}`',
        f'* owner runtime: {single_store.SELECTOR if store else output_alias.SELECTOR if output else watched_switch.SELECTOR if switch else descriptor.SELECTOR if words else static_buffer.SELECTOR if static else named_buffer.SELECTOR if buffers else ignored_leaf.SELECTOR if ignored else ACYCLIC_SELECTOR if acyclic else SELECTOR}',
        f'* control flow: {single_store.CONTROL_FLOW if store else output_alias.CONTROL_FLOW if output else watched_switch.CONTROL_FLOW if switch else descriptor.CONTROL_FLOW if words else static_buffer.CONTROL_FLOW if static else named_buffer.CONTROL_FLOW if buffers else ignored_leaf.CONTROL_FLOW if ignored else ACYCLIC_CONTROL_FLOW if acyclic else CONTROL_FLOW}',
        '* verified extent: complete ELF function symbol, including literal pools',
        '* relocations: none','* source plausibility: plausible','* hand-asm allow list: not listed',
        f'* owner runtime evidence: `{text(evidence)}`',f'* compiled : `{data.hex()}`',
        f'* ROM bytes: `{data.hex()}` ({len(data)} bytes)','',
        f'**MATCH - byte identical** - {len(data)}/{len(data)} bytes',''])


def report_matches(report,root,address):
    if _replay.get():return False
    token=_replay.set(True)
    try:
        if not selected(report):return False
        lines=[line for line in report.splitlines() if line.startswith('* owner runtime evidence: `')]
        if len(lines)!=1:return False
        encoded=lines[0][len('* owner runtime evidence: `'):-1]
        def unique(pairs):
            result={}
            for key,value in pairs:
                if key in result:raise ValueError('duplicate owner evidence key')
                result[key]=value
            return result
        evidence=json.loads(encoded,object_pairs_hook=unique)
        if text(evidence)!=encoded:return False
        result=build(root,address,expected=evidence['manifest'],selector=selector_for_report(report))
        return render(address,result)==report
    except (OSError,ValueError,KeyError,TypeError,IndexError,RuntimeError,subprocess.SubprocessError):
        return False
    finally:_replay.reset(token)


def issue(root,address,args):
    import match
    if args.mode!='thumb' or args.control_flow_profile!='ordinary' or \
            args.software_double_profile or args.software_double_remainder_profile or \
            args.function_address_profile or args.switch_profile or args.label or \
            args.wsl!='Ubuntu' or args.wsl_path!=match.DEFAULT_WSL_PATH:
        raise ValueError('owner profile requires its isolated fixed Thumb selector')
    result=build(root,address,args,selector=args.owner_runtime_profile)
    report=render(address,result)
    if args.emit:
        output=(Path(root)/args.emit).resolve()
        if (Path(root)/'build').resolve() not in output.parents or output.exists():
            raise ValueError('--emit requires a new file beneath build/')
        output.parent.mkdir(parents=True,exist_ok=True)
        with output.open('xb') as stream:stream.write(result[0])
    if not args.no_write:
        path=Path(root)/'docs/match'/f'{address:08X}.md';path.parent.mkdir(parents=True,exist_ok=True)
        path.write_text(report)
    control_flow = single_store.CONTROL_FLOW if args.owner_runtime_profile == single_store.SELECTOR else \
        output_alias.CONTROL_FLOW if args.owner_runtime_profile == output_alias.SELECTOR else \
        watched_switch.CONTROL_FLOW if args.owner_runtime_profile == watched_switch.SELECTOR else \
        descriptor.CONTROL_FLOW if args.owner_runtime_profile == descriptor.SELECTOR else \
        static_buffer.CONTROL_FLOW if args.owner_runtime_profile == static_buffer.SELECTOR else \
        named_buffer.CONTROL_FLOW if args.owner_runtime_profile == named_buffer.SELECTOR else \
        ignored_leaf.CONTROL_FLOW if args.owner_runtime_profile == ignored_leaf.SELECTOR else \
        ACYCLIC_CONTROL_FLOW if args.owner_runtime_profile == ACYCLIC_SELECTOR else CONTROL_FLOW
    print(f'extent    {len(result[0])} bytes (complete ELF symbol; {control_flow}; no relocations)')
    print('verdict MATCH - byte identical')
    return 0
