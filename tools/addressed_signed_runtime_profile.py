"""Explicit source admission for conditional addressed signed-runtime calls.

This authenticates the actual runtime entries and ordinary returning ARM ABI
boundary. It supplies no numeric division/remainder result or domain theorem.
"""
import argparse
from contextvars import ContextVar
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shlex
import shutil
import struct
import subprocess
import sys
import tempfile

import divsi3_profile as quotient
import modsi3_profile as remainder

SELECTOR = 'addressed-signed-runtime-v1'
SCHEMA = 'elf-symbol-thumb-addressed-signed-runtime-v1'
READONLY_SELECTOR = 'addressed-signed-runtime-readonly-word0-v1'
READONLY_SCHEMA = 'elf-symbol-thumb-addressed-signed-runtime-readonly-word0-v1'
DATA_SELECTOR = 'addressed-signed-runtime-data-v1'
DATA_SCHEMA = 'elf-symbol-thumb-addressed-signed-runtime-data-v1'
DATA_CONTRACT = ('typed named ABS32 object identity only; no physical readability, '
                 'allocation, pointee type, memory safety or C semantic facts')
SCHEMAS = {SELECTOR: SCHEMA, READONLY_SELECTOR: READONLY_SCHEMA, DATA_SELECTOR: DATA_SCHEMA}
OPERATIONS = {'func_081426B8': quotient.ADDRESS, remainder.ADDRESSED_NAME: remainder.ADDRESS}
ABI = 'conditional returning ARM ABI; arbitrary incoming word patterns; no numeric return facts'
_replay = ContextVar('addressed_signed_runtime_replay', default=False)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def text(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def context_selector(context):
    if type(context) is tuple:
        if len(context) == 5:
            return SELECTOR
        if len(context) == 6 and context[5] == READONLY_SELECTOR:
            return READONLY_SELECTOR
        if len(context) == 8 and context[5] == DATA_SELECTOR:
            return DATA_SELECTOR
    raise ValueError('addressed signed runtimes require an exact explicit context')


def object_value(name, addend, objects, entries, address, size):
    """The existing typed-data addend boundary, excluding code-as-data aliases."""
    import match
    if name not in objects or type(addend) is not int or not -0x80000000 <= addend <= 0x7FFFFFFF:
        raise ValueError('addressed data requires a mapped object and signed32 addend')
    base = objects[name]
    value = base + addend
    if not 0 <= value <= 0xFFFFFFFF or address <= value < address + size or \
            any(match.function_thunk.reserved(target) for target in (base, value)) or any(
            int(row['rom'], 16) <= (target & ~1) < int(row['end'], 16)
            for row in entries for target in (base, value)):
        raise ValueError('addressed data overflows or aliases indexed code')
    return value


def data_literals(data, address, rom, mapping, objects, records):
    import match
    if type(objects) is not bytes or type(records) is not list or not records:
        raise ValueError('addressed data requires an actual typed data snapshot and bindings')
    # Calls are authenticated separately by prepare; do not send reserved runtime
    # names through the ordinary function-address validator.
    calls, literals = match.function_address_bindings(data, address, rom, mapping, objects,
        {'calls': [], 'data': records, 'functions': []}, allow_empty_functions=True)
    parsed, entries = match.parse_data_symbols(objects), json.loads(mapping)
    for offset, name, addend in records:
        value = object_value(name, addend, parsed, entries, address, len(data))
        if literals[offset] != (name, value):
            raise ValueError('addressed data lost its typed object identity')
    if calls:
        raise ValueError('addressed data cannot introduce function bindings')
    return literals


def data_producer_fingerprint():
    """Pin the actual data admission, linker, CFG and source-replay producers."""
    import match
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    import local_long_branch_profile as frame
    modules = (match, owner, graph, frame, quotient, remainder, match.function_thunk,
               match.software_double, match.software_float, match.ashldi3, match.umodsi3)
    paths = {Path(module.__file__) for module in modules} | {Path(__file__)}
    paths.update(Path(__file__).with_name(name) for name in
                 ('match_evidence.py', 'inert_spin_profile.py', 'analyze.py', 'plausible.py'))
    return {path.name: sha(path.read_bytes()) for path in sorted(paths)}


def prepare(data, address, calls, context):
    import match
    import owner_admission_profile as owner
    selector = context_selector(context)
    if type(context[3]) is not dict or not context[3] or \
            type(context[4]) is not dict or context[4]:
        raise ValueError('addressed signed runtimes require a fresh exact context')
    rom, mapping, index, bindings, _ = context[:5]
    entries = owner.validate_span(data, address, rom, mapping, index)
    if selector == DATA_SELECTOR:
        data_literals(data, address, rom, mapping, context[6], context[7])
    if any(type(site) is not int or type(name) is not str or name not in OPERATIONS or
           calls.get(site) != OPERATIONS[name] for site, name in bindings.items()) or \
            set(bindings) != {site for site, target in calls.items() if target in OPERATIONS.values()}:
        raise ValueError('addressed signed runtimes require complete canonical addressed bindings')
    selected = []
    for module in (quotient, remainder):
        if module.ADDRESS not in {calls[site] for site in bindings}:
            continue
        module.verify_identity(rom, mapping)
        for lo, hi, digest in module.IDENTITIES:
            owner.validate_span(rom[lo-match.ROM_BASE:hi-match.ROM_BASE], lo, rom, mapping, index)
            selected.append([lo, hi, digest])
    for site, target in calls.items():
        if site not in bindings:
            match.function_address_target(f'func_{target:08X}', entries, address, len(data), len(rom))
    return sorted({tuple(row) for row in selected})


def finish(data, address, calls, context, verified, dependencies):
    import match
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    import local_long_branch_profile as frame
    refinement = owner.refine(data, address, context[1])
    instructions, edges, branches, actual_calls, words = graph.graph(data, address, refinement)
    if branches or words or calls != actual_calls or \
            set(instructions) != {item.address for item in verified}:
        raise ValueError('addressed signed runtimes require the exact closed direct-call CFG')
    partition = graph.partition(data, address, refinement, instructions, words)
    selector = context_selector(context)
    if selector == DATA_SELECTOR:
        literals = data_literals(data, address, context[0], context[1], context[6], context[7])
        match.verify_data_literals(instructions.values(), address, literals)
        address_words = {row['address'] - address for row in partition['words']
                         if remainder.address_literal(row['value'])}
        if address_words != set(literals):
            raise ValueError('addressed data requires exact typed coverage of reached address words')
    elif any(remainder.address_literal(row['value']) for row in partition['words']):
        raise ValueError('addressed signed runtimes exclude address literals and data bindings')
    if selector == READONLY_SELECTOR:
        import readonly_entry_stack_profile as incoming
        restored = frame.prove_frame(instructions, edges, address, {}, calls,
            entry_stack_policy={'schema': incoming.SCHEMA, 'words': [0]})
        if not restored['entry_stack']['reads']:
            raise ValueError('addressed readonly word0 requires an actual checked incoming read')
    else:
        restored = frame.prove_frame(instructions, edges, address, {}, calls)
    modules = (match, owner, graph, frame, quotient, remainder)
    if selector == READONLY_SELECTOR:
        modules += (incoming,)
    pins = {Path(module.__file__).name: sha(Path(module.__file__).read_bytes()) for module in modules}
    pins[Path(__file__).name] = sha(Path(__file__).read_bytes())
    if selector == DATA_SELECTOR:
        pins = data_producer_fingerprint()
    context[4].update(schema=SCHEMAS[selector], calls=[
        [site-address, context[3].get(site, f'func_{target:08X}')]
        for site, target in sorted(calls.items())], dependencies=[list(row) for row in dependencies],
        runtime_ABI=ABI, runtime_numeric_return_facts=[], arithmetic_C_equivalence=False,
        original_formal_type_certainty=False,
        ordinary_calls='conditional returning r4-r11/SP preserving ABI only; no transitive callee proof',
        termination='every reached region has a checked return path; universal termination unproved',
        frame=restored, partition=partition, producer_source_sha256=pins)
    if selector == DATA_SELECTOR:
        context[4].update(data_bindings=[list(row) for row in context[7]],
            data_contract=DATA_CONTRACT)


def verify(data, address, rom, mapping, index, calls, bindings, manifest=None, *, selector=SELECTOR,
           data_mapping=None, data_bindings=None):
    import match
    if selector not in SCHEMAS:
        raise ValueError('unknown addressed signed runtime selector')
    observed = {}
    context = (rom, mapping, index, bindings, observed)
    if selector == READONLY_SELECTOR:
        context += (selector,)
    elif selector == DATA_SELECTOR:
        context += (selector, data_mapping, data_bindings)
    if selector != DATA_SELECTOR and (data_mapping is not None or data_bindings is not None):
        raise ValueError('typed data requires its separate explicit addressed selector')
    instructions = match.verify_leaf_instructions(data, address, True, calls,
        addressed_signed_runtime_context=context)
    if manifest is not None and text(manifest) != text(observed):
        raise ValueError('addressed signed runtime manifest differs from fresh native verification')
    return observed, instructions


def original_bindings(image, address, rom, mapping, *, data_mapping=None, data_relocations=None):
    """Canonical addressed calls, with separately requested typed original ABS32."""
    import match
    with_data = data_mapping is not None or data_relocations is not None
    if with_data and (type(data_mapping) is not bytes or type(data_relocations) is not dict or
                      data_relocations):
        raise ValueError('addressed data linking requires a snapshot and fresh empty binding collection')
    objects = match.parse_data_symbols(data_mapping) if with_data else {}
    if image['type'] != 1:
        raise ValueError('addressed signed runtimes require original relocatable ELF')
    match.allocated_text_only(image)
    symbol, offset = match.function_record(image, f'func_{address:08X}', address, True)
    if offset or symbol['size'] != len(image['text']) or any(
            item is not symbol and item['type'] in (1, 2) and item['section'] or
            re.fullmatch(r'\$a(?:\..*)?', item['name']) for item in image['symbols']):
        raise ValueError('addressed signed runtimes require sole complete original Thumb text')
    entries = json.loads(mapping)
    calls, bindings, targets, occupied = {}, {}, {}, set()
    for section_index in image['relocations']:
        section = image['sections'][section_index]
        if section[1] != 9 or section[7] != image['text_index'] or section[9] != 8 or section[5] % 8:
            raise ValueError('addressed signed runtimes require canonical Thumb call REL sections')
        symbols = image['symbol_tables'].get(section[6])
        for position in range(0, section[5], 8):
            offset, info = struct.unpack_from('<II', image['section_data'][section_index], position)
            if info & 255 not in ((2, 10) if with_data else (10,)) or \
                    symbols is None or info >> 8 >= len(symbols) or offset % 2 or \
                    offset + 4 > symbol['size'] or occupied.intersection(range(offset, offset+4)):
                raise ValueError('addressed signed runtimes exclude data and irregular relocations')
            target_symbol = symbols[info >> 8]
            name = target_symbol['name']
            if info & 255 == 2:
                if (address + offset) % 4 or target_symbol['section'] or target_symbol['value'] or \
                        target_symbol['size'] or target_symbol['bind'] != 1 or \
                        target_symbol['type'] not in (0, 1) or \
                        sum(item['name'] == name for item in image['symbols']) != 1:
                    raise ValueError('addressed ABS32 requires an aligned unique undefined global object')
                addend = struct.unpack_from('<i', image['text'], offset)[0]
                object_value(name, addend, objects, entries, address, symbol['size'])
                data_relocations[offset] = (name, addend)
                targets[name] = objects[name]
                occupied.update(range(offset, offset+4))
                continue
            if target_symbol['section'] or target_symbol['value'] or target_symbol['bind'] != 1 or \
                    target_symbol['type'] not in (0, 2) or \
                    sum(item['name'] == name for item in image['symbols']) != 1:
                raise ValueError('addressed calls require unique undefined zero-valued global functions')
            target = OPERATIONS.get(name)
            if target is None:
                target = match.function_address_target(name, entries, address, len(image['text']), len(rom))
            else:
                bindings[address+offset] = name
            decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
            decoder.detail = True
            instruction = next(decoder.disasm(image['text'][offset:offset+4],address+offset),None)
            if instruction is None or instruction.id != match.ARM_INS_BL or instruction.size != 4 or \
                    len(instruction.operands) != 1 or instruction.operands[0].type != match.ARM_OP_IMM or \
                    instruction.operands[0].imm != address+offset:
                raise ValueError('addressed call relocation requires its canonical zero addend')
            calls[address+offset] = target
            targets[name] = target
            occupied.update(range(offset,offset+4))
    if not bindings or with_data and not data_relocations or any(
                           item['name'] and not item['section'] and item['name'] not in targets
                           for item in image['symbols']):
        raise ValueError('addressed runtime ELF requires actual addressed calls and no unresolved symbols')
    return calls, bindings, targets


def linked_bytes(original, linked, address, calls, targets, *, data_relocations=None):
    import match
    if linked['type'] != 2 or linked['relocations']:
        raise ValueError('addressed runtime link requires executable ELF without relocations')
    match.allocated_text_only(linked)
    name = f'func_{address:08X}'
    before, _ = match.function_record(original, name, address, True)
    after, offset = match.function_record(linked, name, address, True)
    if offset or after['value'] != address | 1 or after['size'] != before['size'] or \
            linked['sections'][linked['text_index']][3] != address or \
            len(linked['text']) != len(original['text']):
        raise ValueError('addressed runtime linker changed extent, mode, placement or text size')
    if data_relocations is not None and (type(data_relocations) is not dict or not data_relocations):
        raise ValueError('addressed data linker requires actual original bindings')
    data_relocations = data_relocations or {}
    data_names = {record[0] for record in data_relocations.values()}
    functions = [item['name'] for item in linked['symbols'] if item['type'] == 2]
    objects = [item['name'] for item in linked['symbols'] if item['type'] == 1]
    expected_functions = {name} | (set(targets) - data_names)
    if len(functions) != len(expected_functions) or set(functions) != expected_functions or \
            len(objects) != len(data_names) or set(objects) != data_names or any(
            item['name'] and not item['section'] or
            re.fullmatch(r'\$a(?:\..*)?', item['name']) for item in linked['symbols']):
        raise ValueError('addressed runtime linker introduced objects, undefined symbols or veneers')
    for target_name, target in targets.items():
        symbols = [item for item in linked['symbols'] if item['name'] == target_name]
        kind = 1 if target_name in data_names else 2
        value = target if kind == 1 else target | 1
        if len(symbols) != 1 or symbols[0]['type'] != kind or symbols[0]['bind'] != 1 or \
                symbols[0]['section'] != 0xFFF1 or symbols[0]['value'] != value:
            raise ValueError('addressed runtime linked target lost its absolute Thumb identity')
    occupied = set()
    for site, target in calls.items():
        offset = site-address
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB); decoder.detail = True
        instruction = next(decoder.disasm(linked['text'][offset:offset+4],site),None)
        if instruction is None or instruction.id != match.ARM_INS_BL or instruction.size != 4 or \
                instruction.operands[0].imm != target:
            raise ValueError('addressed runtime linked BL target differs')
        occupied.update(range(offset,offset+4))
    for offset, (target_name, addend) in data_relocations.items():
        if type(offset) is not int or (address+offset) % 4 or not 0 <= offset <= before['size']-4 or \
                type(addend) is not int or not -0x80000000 <= addend <= 0x7FFFFFFF or \
                target_name not in targets or occupied.intersection(range(offset,offset+4)) or \
                struct.unpack_from('<i', original['text'], offset)[0] != addend or \
                not 0 <= targets[target_name]+addend <= 0xFFFFFFFF or \
                struct.unpack_from('<I', linked['text'], offset)[0] != targets[target_name]+addend:
            raise ValueError('addressed linked data differs from its original typed ABS32 addend')
        occupied.update(range(offset,offset+4))
    if any(index not in occupied and first != second for index, (first,second) in
           enumerate(zip(original['text'],linked['text']))):
        raise ValueError('addressed runtime linker changed bytes outside call relocations')
    return linked['text']


def object_bytes(runner, workspace, args, original, address, rom, mapping, *,
                 selector=SELECTOR, data_mapping=None):
    import match
    from inert_spin_profile import fixed_configuration
    fixed_configuration(args)
    data = {} if selector == DATA_SELECTOR else None
    calls, bindings, targets = original_bindings(original,address,rom,mapping,
        data_mapping=data_mapping if data is not None else None, data_relocations=data)
    data_names = {record[0] for record in (data or {}).values()}
    definitions = ['.syntax unified','.thumb']
    for name,target in sorted(targets.items()):
        if name in data_names:
            definitions += [f'.global {name}',f'.type {name}, %object',f'.set {name}, 0x{target:08X}']
        else:
            definitions += [f'.global {name}',f'.type {name}, %function',f'.thumb_set {name}, 0x{target|1:08X}']
    runner.write_text(f'{workspace}/f.known.s','\n'.join(definitions)+'\n')
    runner.write_text(f'{workspace}/f.ld',
        f'SECTIONS {{ .text 0x{address:08X} : {{ *(.text) *(.glue_7) *(.glue_7t) }} '
        '.data 0 : { *(.data) } .bss 0 : { *(.bss) } '
        '.ARM.attributes 0 : { *(.ARM.attributes) } '
        '.unexpected 0 : { *(.vfp11_veneer) *(.v4_bx) *(.iplt) *(.igot.plt) } '
        '.rel.iplt 0 : { *(.rel.iplt) } '
        'ASSERT(SIZEOF(.unexpected) == 0, "unexpected linker stubs") '
        'ASSERT(SIZEOF(.rel.iplt) == 0, "unexpected dynamic relocations") '
        '/DISCARD/ : { *(.comment) *(.note.GNU-stack) } }')
    quoted = shlex.quote(workspace)
    runner.sh(f'export TMPDIR={quoted}; {args.assembler} -mthumb-interwork {quoted}/f.known.s -o {quoted}/f.known.o')
    runner.sh(f'export TMPDIR={quoted}; {args.linker} --fatal-warnings --no-undefined --no-relax '
              f'--orphan-handling=error -T {quoted}/f.ld -e func_{address:08X} '
              f'{quoted}/f.o {quoted}/f.known.o -o {quoted}/f.elf')
    runner.sh(f'{args.objcopy} -O binary --only-section=.text {quoted}/f.elf {quoted}/f.linked.bin')
    linked = match.elf_image(runner.read_binary(f'{workspace}/f.elf'))
    if runner.read_binary(f'{workspace}/f.linked.bin') != linked['text']:
        raise ValueError('addressed runtime objcopy differs from linked ELF text')
    result = linked_bytes(original,linked,address,calls,targets,data_relocations=data),calls,bindings
    if data is not None:
        result += ([[offset,name,addend] for offset,(name,addend) in sorted(data.items())],)
    return result


def toolchain_fingerprint():
    import match
    commands = (match.DEFAULT_CC,match.DEFAULT_CPP,match.DEFAULT_AS,match.DEFAULT_OBJCOPY,match.DEFAULT_LD)
    return [[command,sha(Path(shutil.which(os.path.expandvars(command)) or
                              os.path.expandvars(command)).read_bytes())] for command in commands]


def runtime_fingerprint():
    import capstone
    return dict(system=platform.system(), kernel=platform.release(), machine=platform.machine(),
        python=platform.python_version(), python_sha256=sha(Path(sys.executable).read_bytes()),
        capstone=capstone.__version__, binding_sha256=sha(Path(capstone.__file__).read_bytes()),
        capstone_native_sha256=sha(Path(capstone._cs._name).read_bytes()))


def build(root, address, args=None, expected=None, *, selector=SELECTOR):
    import match
    from inert_spin_profile import fixed_configuration,index_snapshot
    from match_evidence import source_fingerprint,source_paths,mapping_snapshot,data_snapshot,report_rom_path
    root = Path(root)
    args = args or argparse.Namespace(cc=match.DEFAULT_CC,cpp=match.DEFAULT_CPP,assembler=match.DEFAULT_AS,
        objcopy=match.DEFAULT_OBJCOPY,linker=match.DEFAULT_LD,flags=match.DEFAULT_FLAGS)
    fixed_configuration(args)
    if selector not in SCHEMAS:
        raise ValueError('unknown addressed signed runtime selector')
    runtime = runtime_fingerprint() if selector in (READONLY_SELECTOR, DATA_SELECTOR) else None
    producers = data_producer_fingerprint() if selector == DATA_SELECTOR else None
    source,mapping,index = source_fingerprint(root,address),mapping_snapshot(root),index_snapshot(root)
    objects,selected_rom = data_snapshot(root),report_rom_path(root)
    rom = Path(selected_rom).read_bytes(); tools = toolchain_fingerprint()
    candidates = list((root/'src').rglob(f'{address:08X}.c'))
    if len(candidates) != 1:
        raise ValueError('addressed signed runtime requires one uniquely addressed source')
    (root/'build').mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='addressed_signed_',dir=root/'build') as directory:
        captured = Path(directory)
        for path in source_paths(root,address):
            destination = captured/path.relative_to(root)
            destination.parent.mkdir(parents=True,exist_ok=True); destination.write_bytes(path.read_bytes())
        if source_fingerprint(captured,address) != source:
            raise ValueError('addressed signed runtime source capture differs')
        runner = match.Runner(match.DEFAULT_CC,'Ubuntu',match.DEFAULT_WSL_PATH,root=captured,timeout=120)
        with runner.workspace() as workspace:
            raw,_,original = match.compile_object(runner,workspace,args,captured,address,
                candidates[0].relative_to(root).as_posix())
            assembly = runner.read_binary(f'{workspace}/f.s')
            linked_result = object_bytes(runner,workspace,args,original,address,rom,mapping,
                selector=selector,data_mapping=objects)
            body,calls,bindings = linked_result[:3]
            data_options = (dict(data_mapping=objects,data_bindings=linked_result[3])
                            if selector == DATA_SELECTOR else {})
            manifest,instructions = verify(body,address,rom,mapping,index,calls,bindings,expected,
                                           selector=selector,**data_options)
            linked = runner.read_binary(f'{workspace}/f.elf')
        check = match._run_replay_process([sys.executable,str(Path(__file__).with_name('plausible.py')),
            '--quiet','--addr',f'0x{address:08X}','--json']+
            [str(path) for path in source_paths(captured,address)],captured,120)
        findings,allowed = match.plausibility_result(check,address)
        if findings or allowed or source_fingerprint(captured,address) != source:
            raise ValueError('addressed signed runtime source is implausible or changed')
    if source_fingerprint(root,address) != source or mapping_snapshot(root) != mapping or \
            index_snapshot(root) != index or data_snapshot(root) != objects or \
            report_rom_path(root) != selected_rom or Path(selected_rom).read_bytes() != rom or \
            toolchain_fingerprint() != tools or runtime is not None and runtime_fingerprint() != runtime or \
            producers is not None and (data_producer_fingerprint() != producers or
                manifest['producer_source_sha256'] != producers):
        raise ValueError('addressed signed runtime source, inputs or tools changed during verification')
    result = dict(address=address,body=body,manifest=manifest,source_sha256=source,
        mapping_sha256=sha(mapping),index_sha256=sha(index),objects_sha256=None if objects is None else sha(objects),
        rom_sha256=sha(rom),instructions=len(instructions),toolchain=tools,
        original_elf=raw,assembly=assembly,linked_elf=linked)
    if runtime is not None:
        result['runtime'] = runtime
    return result


def render(result):
    selector = next((key for key,value in SCHEMAS.items() if value == result['manifest']['schema']),None)
    if selector is None:
        raise ValueError('unknown addressed signed runtime manifest schema')
    premise = [] if selector != READONLY_SELECTOR else [
        '* incoming stack ABI: ' + result['manifest']['frame']['entry_stack']['contract']]
    if selector == DATA_SELECTOR:
        premise = ['* named data binding: ' + result['manifest']['data_contract']]
    evidence = {key:value for key,value in result.items() if key not in
                ('body','original_elf','assembly','linked_elf')}
    for key in ('body','original_elf','assembly','linked_elf'):
        evidence[key+'_sha256'] = sha(result[key])
    encoded = text(evidence)
    return '\n'.join([f'# 0x{result["address"]:08X}','',f'* verification: `{SCHEMAS[selector]}`',
        f'* addressed signed runtime: `{selector}`',f'* control flow: {ABI}',*premise,
        '* source plausibility: plausible',
        '* verified extent: complete original ELF function symbol including referenced literal pools',
        '* numeric division/remainder equivalence: unclaimed; original formal type certainty: unclaimed',
        f'* addressed signed runtime evidence: `{encoded}`',
        f'* addressed signed runtime proof SHA-256: `{sha(encoded.encode())}`',
        f'* compiled : `{result["body"].hex()}`',
        f'* ROM bytes: `{result["body"].hex()}` ({len(result["body"])} bytes)','',
        f'**MATCH - byte identical** - {len(result["body"])}/{len(result["body"])} bytes',''])


def selector_for_report(report):
    from inert_spin_profile import marker_text
    lines = report.splitlines()
    if not any(any(schema in line for schema in SCHEMAS.values()) or
               marker_text(line).startswith('* addressed signed runtime') for line in lines):
        return False
    for selector,schema in SCHEMAS.items():
        if [line for line in lines if marker_text(line).startswith('* verification:')] == [f'* verification: `{schema}`'] and \
                [line for line in lines if marker_text(line).startswith('* addressed signed runtime:')] == \
                [f'* addressed signed runtime: `{selector}`']:
            return selector
    raise ValueError('mixed or malformed addressed signed runtime report')


def selected(report):
    return bool(selector_for_report(report))


def report_matches(report, root, address):
    from match_evidence import source_fingerprint,mapping_snapshot,data_snapshot,report_rom_path,valid_match_verdict
    from inert_spin_profile import index_snapshot
    if _replay.get():
        return False
    token = _replay.set(True)
    try:
        selector = selector_for_report(report)
        if not selector or not valid_match_verdict(report):
            return False
        prefix = '* addressed signed runtime evidence: `'
        rows = [line for line in report.splitlines() if line.startswith(prefix)]
        if len(rows) != 1 or not rows[0].endswith('`'):
            return False
        def unique(pairs):
            result = {}
            for key,value in pairs:
                if key in result: raise ValueError('duplicate addressed signed runtime evidence key')
                result[key] = value
            return result
        encoded = rows[0][len(prefix):-1]; saved = json.loads(encoded,object_pairs_hook=unique)
        objects = data_snapshot(root)
        if text(saved) != encoded or saved['address'] != address or \
                saved['source_sha256'] != source_fingerprint(root,address) or \
                saved['mapping_sha256'] != sha(mapping_snapshot(root)) or \
                saved['index_sha256'] != sha(index_snapshot(root)) or \
                saved['objects_sha256'] != (None if objects is None else sha(objects)) or \
                saved['rom_sha256'] != sha(Path(report_rom_path(root)).read_bytes()) or \
                saved['toolchain'] != toolchain_fingerprint():
            return False
        if selector in (READONLY_SELECTOR, DATA_SELECTOR) and saved['runtime'] != runtime_fingerprint():
            return False
        return render(build(root,address,expected=saved['manifest'],selector=selector)) == report
    except (OSError,ValueError,KeyError,TypeError,IndexError,RuntimeError,subprocess.SubprocessError):
        return False
    finally:
        _replay.reset(token)


def issue(root, address, args):
    import match
    if args.mode != 'thumb' or args.control_flow_profile != 'ordinary' or args.label or \
            args.wsl != 'Ubuntu' or args.wsl_path != match.DEFAULT_WSL_PATH or any(
                getattr(args,name) is not None for name in ('signed_runtime_profile','signed_quotient_profile',
                'software_double_profile','software_double_remainder_profile','function_address_profile',
                'switch_profile','owner_runtime_profile')):
        raise ValueError('addressed signed runtimes require their isolated explicit Thumb selector')
    result = build(root,address,args,selector=args.addressed_signed_runtime_profile)
    if args.emit:
        output = (Path(root)/args.emit).resolve()
        if (Path(root)/'build').resolve() not in output.parents or output.exists():
            raise ValueError('--emit requires a new file beneath build/')
        output.parent.mkdir(parents=True,exist_ok=True)
        with output.open('xb') as stream:stream.write(result['body'])
    if not args.no_write:
        report = Path(root)/'docs/match'/f'{address:08X}.md'
        report.parent.mkdir(parents=True,exist_ok=True); report.write_text(render(result))
    print(f'extent    {len(result["body"])} bytes (complete ELF symbol; conditional addressed runtime ABI)')
    print('verdict MATCH - byte identical')
    return 0
