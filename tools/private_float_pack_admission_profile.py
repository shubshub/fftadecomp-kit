"""Explicit source admission for the pinned private unpack/pack local closure.

The existing effect inventory supplies the proof. This module authenticates
original ELF bindings and source replay; it adds no initialized-content,
floating-point equivalence, physical-memory or termination theorem.
"""
import argparse
from contextvars import ContextVar
import hashlib
import importlib
import json
from pathlib import Path
import re
import shlex
import struct
import subprocess
import sys
import tempfile

import private_float_pack_effects_inventory as inventory
from inert_spin_profile import fixed_configuration, index_snapshot, marker_text
from addressed_signed_runtime_profile import toolchain_fingerprint, runtime_fingerprint

SELECTOR = 'private-float-unpack-pack-v1'
SCHEMA = 'elf-symbol-thumb-private-float-unpack-pack-v1'
CONTRACT = ('pinned unpack/pack finite argument effects into live abstract locals; '
            'loaded words and result unknown; initialized contents, IEEE and C '
            'definedness equivalence, physical memory, nonalias, nonescape and '
            'universal termination unproved')
_replay = ContextVar('private_float_pack_replay', default=False)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def text(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def producer_fingerprint():
    """Conservatively bind all toolkit sources, including executed staged files."""
    paths = {path.name: path for path in Path(inventory.__file__).parent.glob('*.py')}
    for name in ('match', 'match_evidence', __name__):
        path = Path(importlib.import_module(name).__file__)
        paths[path.name] = path
    return {name: sha(path.read_bytes()) for name, path in sorted(paths.items())}


def selected(report):
    lines = report.splitlines()
    if not any(SCHEMA in line or marker_text(line).startswith('* private float pack')
               for line in lines):
        return False
    if [line for line in lines if marker_text(line).startswith('* verification')] != [
            f'* verification: `{SCHEMA}`'] or [line for line in lines
            if marker_text(line).startswith('* private float pack:')] != [
            f'* private float pack: `{SELECTOR}`']:
        raise ValueError('mixed or malformed private-float admission report')
    return True


def original_bindings(image, address, rom, mapping, index):
    """Authenticate only the two genuine private entry symbols, without aliases."""
    import match
    from software_double_profile import indices, span_record
    if image['type'] != 1:
        raise ValueError('private float requires original relocatable ELF')
    match.allocated_text_only(image)
    symbol, offset = match.function_record(image, f'func_{address:08X}', address, True)
    if offset or symbol['size'] != len(image['text']) or any(
            item['type'] == 2 and item is not symbol and item['section'] or
            item['type'] == 1 and item['section'] or
            re.fullmatch(r'\$a(?:\..*)?', item['name']) for item in image['symbols']):
        raise ValueError('private float requires one complete Thumb ELF function')
    entries, rows = indices(mapping, index)
    span_record(address, address + len(image['text']), entries, rows, rom)
    if sha(rom) != inventory.runtime.ROM_SHA256:
        raise ValueError('private float requires the approved ROM identity')
    targets = {}
    for _, (start, end, count, digest), _ in inventory.HELPERS:
        record = span_record(start, end, entries, rows, rom)
        if record['instrs'] != count or sha(rom[start-match.ROM_BASE:end-match.ROM_BASE]) != digest or \
                start < address + len(image['text']) and end > address:
            raise ValueError('private float helper identity/count/ownership differs')
        targets[f'func_{start:08X}'] = start
    calls, occupied = [], set()
    decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
    decoder.detail = True
    for section_index in image['relocations']:
        section = image['sections'][section_index]
        if section[1] != 9 or section[7] != image['text_index'] or section[9] != 8 or section[5] % 8:
            raise ValueError('private float requires canonical text REL relocations')
        symbols = image['symbol_tables'].get(section[6])
        for position in range(0, section[5], 8):
            site, info = struct.unpack_from('<II', image['section_data'][section_index], position)
            if symbols is None or info >> 8 >= len(symbols) or info & 255 != 10 or \
                    site % 2 or site + 4 > len(image['text']) or occupied.intersection(range(site, site+4)):
                raise ValueError('invalid or overlapping private-float call relocation')
            occupied.update(range(site, site+4))
            target = symbols[info >> 8]
            name = target['name']
            if name not in targets or target['section'] or target['value'] or target['bind'] != 1 or \
                    target['type'] not in (0, 2) or sum(item['name'] == name for item in image['symbols']) != 1:
                raise ValueError('private float requires unique undefined genuine helper functions')
            item = next(decoder.disasm(image['text'][site:site+4], address+site), None)
            if item is None or item.id != match.ARM_INS_BL or item.size != 4 or \
                    item.operands[0].imm != address+site:
                raise ValueError('private float requires canonical zero-addend Thumb BL')
            calls.append([site, name])
    calls.sort()
    expected = [f'func_{record[0]:08X}' for _, record, _ in inventory.HELPERS]
    if [name for _, name in calls] != expected or any(item['name'] and not item['section'] and
            item['name'] not in targets for item in image['symbols']):
        raise ValueError('private float requires exactly one unpack then one pack and no extra symbols')
    return calls, targets


def linked_bytes(original, linked, address, calls, targets):
    import match
    match.allocated_text_only(linked)
    record, offset = match.function_record(linked, f'func_{address:08X}', address, True)
    if linked['type'] != 2 or offset or linked['relocations'] or \
            record['size'] != len(original['text']) or len(linked['text']) != len(original['text']) or any(
            item['type'] == 2 and item is not record and item['section'] == linked['text_index']
            for item in linked['symbols']):
        raise ValueError('private float linker altered complete function extent or retained relocations')
    decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
    decoder.detail = True
    expected = bytearray(original['text'])
    for site, name in calls:
        item = next(decoder.disasm(linked['text'][site:site+4], address+site), None)
        if item is None or item.id != match.ARM_INS_BL or item.size != 4 or \
                item.operands[0].imm != targets[name]:
            raise ValueError('linked private-float call target differs from original binding')
        expected[site:site+4] = linked['text'][site:site+4]
    if bytes(expected) != linked['text']:
        raise ValueError('private float linker changed bytes outside original BL relocations')
    return linked['text']


def object_bytes(runner, workspace, args, original, address, rom, mapping, index):
    import match
    fixed_configuration(args)
    calls, targets = original_bindings(original, address, rom, mapping, index)
    definitions = ['.syntax unified', '.thumb']
    for name, target in sorted(targets.items()):
        definitions += [f'.global {name}', f'.type {name}, %function',
                        f'.thumb_set {name}, 0x{target|1:08X}']
    runner.write_text(workspace+'/f.known.s', '\n'.join(definitions)+'\n')
    runner.write_text(workspace+'/f.ld',
        f'SECTIONS {{ .text 0x{address:08X} : {{ *(.text) *(.glue_7) *(.glue_7t) }} '
        '.data 0 : { *(.data) } .bss 0 : { *(.bss) } .ARM.attributes 0 : { *(.ARM.attributes) } '
        '.unexpected 0 : { *(.vfp11_veneer) *(.v4_bx) *(.iplt) *(.igot.plt) } '
        '.rel.iplt 0 : { *(.rel.iplt) } ASSERT(SIZEOF(.unexpected)==0,"unexpected stubs") '
        'ASSERT(SIZEOF(.rel.iplt)==0,"unexpected relocations") '
        '/DISCARD/ : { *(.comment) *(.note.GNU-stack) } }')
    quoted = shlex.quote(workspace)
    runner.sh(f'export TMPDIR={quoted}; {args.assembler} -mthumb-interwork {quoted}/f.known.s -o {quoted}/f.known.o')
    runner.sh(f'export TMPDIR={quoted}; {args.linker} --fatal-warnings --no-undefined --no-relax '
              f'--orphan-handling=error -T {quoted}/f.ld -e func_{address:08X} '
              f'{quoted}/f.o {quoted}/f.known.o -o {quoted}/f.elf')
    linked = match.elf_image(runner.read_binary(workspace+'/f.elf'))
    return linked_bytes(original, linked, address, calls, targets), calls


def verify(data, address, rom, mapping, index, calls, *, selector=SELECTOR, manifest=None):
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('private float admission requires its explicit selector')
    proof, instructions = inventory.verify(data, address, rom, mapping, index, selector=inventory.SELECTOR)
    expected = [[site-address, f'func_{next(record[0] for role, record, _ in inventory.HELPERS if role == name):08X}']
                for site, name in proof['private_bindings']]
    if type(calls) is not list or calls != expected:
        raise ValueError('private float ELF bindings differ from the fresh reached closure')
    observed = dict(schema=SCHEMA, selector=SELECTOR, contract=CONTRACT, bindings=calls,
                    inventory=proof, producer_source_sha256=producer_fingerprint())
    if manifest is not None and text(manifest) != text(observed):
        raise ValueError('private float admission manifest differs from fresh proof')
    return observed, instructions


def fingerprint(evidence):
    return sha(text(evidence).encode())


def build(root, address, args=None, expected=None):
    import match
    from match_evidence import source_paths, source_fingerprint, mapping_snapshot, data_snapshot, report_rom_path
    root = Path(root)
    args = args or argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
        objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
    fixed_configuration(args)
    source, mapping, index = source_fingerprint(root, address), mapping_snapshot(root), index_snapshot(root)
    objects, rom_path = data_snapshot(root), report_rom_path(root)
    rom = Path(rom_path).read_bytes()
    tools, runtime, producers = toolchain_fingerprint(), runtime_fingerprint(), producer_fingerprint()
    candidates = list((root/'src').rglob(f'{address:08X}.c'))
    if len(candidates) != 1:
        raise ValueError('private float admission requires one unique source')
    (root/'build').mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='private_float_pack_', dir=root/'build') as directory:
        capture = Path(directory)
        for path in source_paths(root, address):
            target = capture/path.relative_to(root)
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(path.read_bytes())
        if source_fingerprint(capture, address) != source:
            raise ValueError('private float source capture differs')
        runner = match.Runner(match.DEFAULT_CC, 'Ubuntu', match.DEFAULT_WSL_PATH, root=capture, timeout=120)
        with runner.workspace() as workspace:
            raw, _, original = match.compile_object(runner, workspace, args, capture, address,
                candidates[0].relative_to(root).as_posix())
            data, calls = object_bytes(runner, workspace, args, original, address, rom, mapping, index)
            manifest, instructions = verify(data, address, rom, mapping, index, calls, manifest=expected)
            linked = runner.read_binary(workspace+'/f.elf')
        checker = Path(importlib.import_module('plausible').__file__)
        process = match._run_replay_process([sys.executable, str(checker), '--quiet', '--addr',
            f'0x{address:08X}', '--json']+[str(path) for path in source_paths(capture, address)], capture, 120)
        findings, allowed = match.plausibility_result(process, address)
        if findings or allowed or source_fingerprint(capture, address) != source:
            raise ValueError('private float source is implausible or changed')
    if source_fingerprint(root, address) != source or mapping_snapshot(root) != mapping or \
            index_snapshot(root) != index or data_snapshot(root) != objects or \
            report_rom_path(root) != rom_path or Path(rom_path).read_bytes() != rom or \
            toolchain_fingerprint() != tools or runtime_fingerprint() != runtime or \
            producer_fingerprint() != producers or manifest['producer_source_sha256'] != producers:
        raise ValueError('private float source, maps, ROM, tools or runtime changed')
    return dict(address=address, body=data, manifest=manifest, source_sha256=source,
        mapping_sha256=sha(mapping), index_sha256=sha(index),
        objects_sha256=None if objects is None else sha(objects), rom_sha256=sha(rom),
        instructions=len(instructions), toolchain=tools, runtime=runtime,
        original_elf=raw, linked_elf=linked)


def render(result):
    evidence = {key: value for key, value in result.items() if key not in ('body', 'original_elf', 'linked_elf')}
    for key in ('body', 'original_elf', 'linked_elf'):
        evidence[key+'_sha256'] = sha(result[key])
    return '\n'.join([f'# 0x{result["address"]:08X}', '', f'* verification: `{SCHEMA}`',
        f'* private float pack: `{SELECTOR}`', f'* control flow: {CONTRACT}',
        '* verified extent: complete original ELF function symbol, including literal pools',
        '* relocations: none', '* source plausibility: plausible', '* hand-asm allow list: not listed',
        f'* private float pack evidence: `{text(evidence)}`',
        f'* private float pack proof SHA-256: `{fingerprint(evidence)}`',
        f'* compiled : `{result["body"].hex()}`',
        f'* ROM bytes: `{result["body"].hex()}` ({len(result["body"])} bytes)', '',
        f'**MATCH - byte identical** - {len(result["body"])}/{len(result["body"])} bytes', ''])


def report_matches(report, root, address):
    from match_evidence import source_fingerprint, mapping_snapshot, data_snapshot, report_rom_path
    if _replay.get():
        return False
    token = _replay.set(True)
    try:
        if not selected(report):
            return False
        prefix = '* private float pack evidence: `'
        rows = [line for line in report.splitlines() if line.startswith(prefix)]
        if len(rows) != 1 or not rows[0].endswith('`'):
            return False
        def unique(pairs):
            result = {}
            for key, value in pairs:
                if key in result:
                    raise ValueError('duplicate private-float evidence key')
                result[key] = value
            return result
        encoded = rows[0][len(prefix):-1]
        saved = json.loads(encoded, object_pairs_hook=unique)
        objects = data_snapshot(root)
        if text(saved) != encoded or saved['address'] != address or \
                saved['source_sha256'] != source_fingerprint(root, address) or \
                saved['mapping_sha256'] != sha(mapping_snapshot(root)) or \
                saved['index_sha256'] != sha(index_snapshot(root)) or \
                saved['objects_sha256'] != (None if objects is None else sha(objects)) or \
                saved['rom_sha256'] != sha(Path(report_rom_path(root)).read_bytes()) or \
                saved['toolchain'] != toolchain_fingerprint() or saved['runtime'] != runtime_fingerprint() or \
                saved['manifest']['producer_source_sha256'] != producer_fingerprint():
            return False
        return render(build(root, address, expected=saved['manifest'])) == report
    except (OSError, ValueError, KeyError, TypeError, IndexError, RuntimeError, subprocess.SubprocessError):
        return False
    finally:
        _replay.reset(token)


def issue(root, address, args):
    import match
    if args.owner_runtime_profile != SELECTOR or args.mode != 'thumb' or \
            args.control_flow_profile != 'ordinary' or args.label or args.wsl != 'Ubuntu' or \
            args.wsl_path != match.DEFAULT_WSL_PATH or any(getattr(args, name, None) is not None for name in (
            'signed_runtime_profile', 'signed_quotient_profile', 'addressed_signed_runtime_profile',
            'software_double_profile', 'software_double_remainder_profile', 'function_address_profile',
            'switch_profile', 'switch_data_profile')):
        raise ValueError('private float admission requires its isolated explicit Thumb selector')
    result = build(root, address, args)
    if args.emit:
        output = (Path(root)/args.emit).resolve()
        if (Path(root)/'build').resolve() not in output.parents or output.exists():
            raise ValueError('--emit requires a new file beneath build/')
        output.parent.mkdir(parents=True, exist_ok=True)
        with output.open('xb') as stream:
            stream.write(result['body'])
    if not args.no_write:
        path = Path(root)/'docs/match'/f'{address:08X}.md'
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(render(result))
    print(f'extent    {len(result["body"])} bytes (complete ELF symbol; private unpack/pack effects)')
    print('verdict MATCH - byte identical')
    return 0
