"""Explicit original-ELF admission for one canonical unsigned DIV/MOD by ten."""
import argparse
from contextvars import ContextVar
import hashlib
import importlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

import unsigned_divmod_ordinary_inventory as inventory
import umodsi3_profile as remainder
from modsi3_profile import address_literal
from addressed_signed_runtime_profile import runtime_fingerprint, toolchain_fingerprint

SELECTOR = 'unsigned-divmod-ten-v1'
SCHEMA = 'elf-symbol-thumb-unsigned-divmod-ten-v1'
OPERATIONS = dict(inventory.OPERATIONS)
_replay = ContextVar('unsigned_divmod_ten_replay', default=False)


def text(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def sha(data):
    return hashlib.sha256(data).hexdigest()


def producers():
    names = ('match', 'armv4t', 'match_evidence', 'status', 'inert_spin_profile', 'analyze', 'plausible',
             'unsigned_divmod_ordinary_inventory', 'zero_aware_unsigned_quotient_inventory',
             'umod_only_ordinary_inventory', 'unsigned_remainder_closure_inventory',
             'owner_admission_profile', 'owner_graph_profile', 'owner_runtime_profile',
             'local_long_branch_profile', 'umodsi3_profile', 'function_thunk_profile',
             'addressed_signed_runtime_profile', 'modsi3_profile')
    paths = {Path(importlib.import_module(name).__file__) for name in names} | {Path(__file__)}
    return {path.name: sha(path.read_bytes()) for path in sorted(paths)}


def check_link_selector(selector, quotient, modulo, contexts, switches):
    """Only this explicit selector may compose the two existing binding sets."""
    if selector is None:
        return
    if type(selector) is not str or selector != SELECTOR or \
            type(quotient) is not dict or type(modulo) is not dict or \
            any(value is not None for value in contexts) or any(switches):
        raise ValueError('unsigned divmod requires its isolated canonical selector')


def require_calls(calls, bindings):
    if type(calls) is not dict or type(bindings) is not dict or len(calls) != 2 or \
            len(bindings) != 2 or set(bindings) != set(calls) or \
            set(bindings.values()) != set(OPERATIONS) or any(
                type(site) is not int or type(target) is not int or site % 2 or
                calls[site] != OPERATIONS.get(name) for site, name in bindings.items()
                for target in (calls[site],)):
        raise ValueError('unsigned divmod requires one actual canonical quotient and remainder call')


def verify(data, address, rom, mapping, index, calls, bindings, manifest=None):
    """Reuse complete unsigned runtime/zero/frame proofs, with a stricter caller."""
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    require_calls(calls, bindings)
    structural, verified = inventory.verify(data, address, rom, mapping, index, calls, bindings,
                                            selector=inventory.SELECTOR)
    refinement = owner.refine(data, address, mapping)
    instructions, edges, _, _, _ = graph.graph(data, address, refinement)
    divisors = remainder.prove_divisors(instructions, edges, address, calls)
    if set(divisors) != set(calls) or any(value != 10 for value in divisors.values()):
        raise ValueError('unsigned divmod requires CFG-proven r1=10 at both runtime calls')
    # Numeric literals are not authority to introduce an unbound address.
    if any(address_literal(row['value']) for row in structural['partition']['words']):
        raise ValueError('unsigned divmod excludes unbound address literals')
    observed = {'schema': SCHEMA, 'selector': SELECTOR,
        'unsigned_runtime_inventory': structural,
        'divisors': [[site-address, divisors[site]] for site in sorted(divisors)],
        'runtime_numeric_return_facts': [], 'arithmetic_C_equivalence': False,
        'memory_safety_claim': False, 'termination_claim': False,
        'physical_memory_nonalias_claim': False,
        'producer_source_sha256': producers()}
    if manifest is not None and text(manifest) != text(observed):
        raise ValueError('unsigned divmod manifest differs from complete fresh proof')
    return observed, verified


def object_bytes(runner, workspace, args, original, address, rom, mapping):
    import match
    if original['type'] != 1:
        raise ValueError('unsigned divmod requires original relocatable ELF')
    match.allocated_text_only(original)
    symbol, offset = match.function_record(original, f'func_{address:08X}', address, True)
    padding = original['text'][symbol['size']:]
    if offset or len(padding) > 3 or padding and not (
            not any(padding) or symbol['size'] % 4 == 2 and padding == b'\xc0\x46') or any(
            item['type'] == 2 and item is not symbol and item['section'] or
            item['type'] == 1 and item['section'] or re.fullmatch(r'\$a(?:\..*)?', item['name'])
            for item in original['symbols']):
        raise ValueError('unsigned divmod requires a sole complete original Thumb ELF function')
    quotient, modulo = {}, {}
    body, calls, literals = match.link_calls(runner, workspace, args, original, address, mapping,
        len(rom), rom, udivsi3_bindings=quotient, umodsi3_bindings=modulo,
        unsigned_runtime_profile=SELECTOR)
    require_calls(calls, quotient | modulo)
    if literals:
        raise ValueError('unsigned divmod excludes data and function literal relocations')
    return body, calls, quotient | modulo


def build(root, address, args=None, expected=None):
    """Every report admission reconstructs its original ELF from current source."""
    import match
    from inert_spin_profile import fixed_configuration, index_snapshot
    from match_evidence import (source_fingerprint, source_paths, mapping_snapshot,
                                data_snapshot, report_rom_path)
    root = Path(root)
    args = args or argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP,
        assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD,
        flags=match.DEFAULT_FLAGS)
    fixed_configuration(args)
    source, mapping, index = source_fingerprint(root, address), mapping_snapshot(root), index_snapshot(root)
    objects, selected_rom = data_snapshot(root), report_rom_path(root)
    rom = Path(selected_rom).read_bytes()
    pins, runtime, binaries = producers(), runtime_fingerprint(), toolchain_fingerprint()
    candidates = list((root / 'src').rglob(f'{address:08X}.c'))
    if len(candidates) != 1:
        raise ValueError('unsigned divmod requires one uniquely addressed source')
    (root / 'build').mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='unsigned_divmod_', dir=root / 'build') as directory:
        captured = Path(directory)
        for path in source_paths(root, address):
            destination = captured / path.relative_to(root)
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(path.read_bytes())
        if source_fingerprint(captured, address) != source:
            raise ValueError('unsigned divmod source capture differs')
        runner = match.Runner(match.DEFAULT_CC, 'Ubuntu', match.DEFAULT_WSL_PATH, root=captured, timeout=120)
        with runner.workspace() as workspace:
            raw, _, original = match.compile_object(runner, workspace, args, captured, address,
                candidates[0].relative_to(root).as_posix())
            assembly = runner.read_binary(f'{workspace}/f.s')
            body, calls, bindings = object_bytes(runner, workspace, args, original, address, rom, mapping)
            manifest, instructions = verify(body, address, rom, mapping, index, calls, bindings, expected)
            linked = runner.read_binary(f'{workspace}/f.elf')
        check = match._run_replay_process([sys.executable, str(Path(__file__).with_name('plausible.py')),
            '--quiet', '--addr', f'0x{address:08X}', '--json'] +
            [str(path) for path in source_paths(captured, address)], captured, 120)
        findings, allowed = match.plausibility_result(check, address)
        if findings or allowed or source_fingerprint(captured, address) != source:
            raise ValueError('unsigned divmod source is implausible or changed')
    if source_fingerprint(root, address) != source or mapping_snapshot(root) != mapping or \
            index_snapshot(root) != index or data_snapshot(root) != objects or \
            report_rom_path(root) != selected_rom or Path(selected_rom).read_bytes() != rom or \
            producers() != pins or manifest['producer_source_sha256'] != pins or \
            runtime_fingerprint() != runtime or toolchain_fingerprint() != binaries:
        raise ValueError('unsigned divmod source, maps, headers, ROM, producers or runtime changed during replay')
    return {'address': address, 'body': body, 'manifest': manifest, 'source_sha256': source,
        'mapping_sha256': sha(mapping), 'index_sha256': sha(index),
        'objects_sha256': None if objects is None else sha(objects), 'rom_sha256': sha(rom),
        'runtime': runtime, 'toolchain': binaries, 'instructions': len(instructions),
        'original_elf': raw, 'assembly': assembly, 'linked_elf': linked}


def render(result):
    import match
    evidence = {key: value for key, value in result.items()
                if key not in ('body', 'original_elf', 'assembly', 'linked_elf')}
    evidence['original_elf_sha256'] = sha(result['original_elf'])
    evidence['linked_elf_sha256'] = sha(result['linked_elf'])
    evidence['compiler'] = [match.DEFAULT_CC, match.DEFAULT_CPP, match.DEFAULT_AS,
                            match.DEFAULT_OBJCOPY, match.DEFAULT_LD, match.DEFAULT_FLAGS]
    evidence['body_sha256'] = sha(result['body'])
    encoded = text(evidence)
    return '\n'.join([f'# 0x{result["address"]:08X}', '', f'* verification: `{SCHEMA}`',
        f'* unsigned runtime: {SELECTOR}', f'* unsigned runtime evidence: `{encoded}`',
        f'* unsigned runtime proof SHA-256: `{sha(encoded.encode())}`',
        f'* compiler: `{match.DEFAULT_CC} {match.DEFAULT_FLAGS}`',
        '* verified extent: complete ELF function symbol, including literal pools',
        '* relocations: none', '* source plausibility: plausible',
        '* scope: structural unsigned runtime/frame proof; no numeric return or memory equivalence theorem',
        f'* compiled : `{result["body"].hex()}`',
        f'* ROM bytes: `{result["body"].hex()}` ({len(result["body"])} bytes)', '',
        f'**MATCH - byte identical** - {len(result["body"])}/{len(result["body"])} bytes', ''])


def selected(report):
    return bool(selector_for_report(report))


def selector_for_report(report):
    lines = report.splitlines()
    if SCHEMA not in report and not any(line.lstrip().startswith('* unsigned runtime') for line in lines):
        return False
    if [line for line in lines if line.lstrip().startswith('* verification')] != [f'* verification: `{SCHEMA}`'] or \
            [line for line in lines if line.lstrip().startswith('* unsigned runtime:')] != [f'* unsigned runtime: {SELECTOR}'] or \
            any(re.match(r'\s*\* (?:signed runtime|addressed signed runtime|owner runtime|private float pack|function address|switch profile|control flow)', line)
                for line in lines):
        raise ValueError('unsigned divmod requires an isolated unmixed versioned report')
    return SELECTOR


def report_matches(report, root, address):
    from match_evidence import valid_match_verdict
    if _replay.get():
        return False
    token = _replay.set(True)
    try:
        if not valid_match_verdict(report) or not selector_for_report(report):
            return False
        lines = [line for line in report.splitlines() if line.startswith('* unsigned runtime evidence: `')]
        if len(lines) != 1 or not lines[0].endswith('`'):
            return False
        def unique(pairs):
            result = {}
            for key, value in pairs:
                if key in result:
                    raise ValueError('duplicate unsigned divmod evidence key')
                result[key] = value
            return result
        encoded = lines[0][len('* unsigned runtime evidence: `'):-1]
        evidence = json.loads(encoded, object_pairs_hook=unique)
        if text(evidence) != encoded:
            return False
        return render(build(root, address, expected=evidence['manifest'])) == report
    except (OSError, ValueError, KeyError, TypeError, IndexError, RuntimeError, subprocess.SubprocessError):
        return False
    finally:
        _replay.reset(token)


def issue(root, address, args):
    import match
    if args.unsigned_runtime_profile != SELECTOR or args.mode != 'thumb' or \
            args.control_flow_profile != 'ordinary' or any(getattr(args, name) for name in
            ('signed_quotient_profile', 'signed_runtime_profile', 'addressed_signed_runtime_profile',
             'software_double_profile', 'software_double_remainder_profile', 'function_address_profile',
             'switch_profile', 'switch_data_profile', 'owner_runtime_profile', 'label')) or \
            args.wsl != 'Ubuntu' or args.wsl_path != match.DEFAULT_WSL_PATH:
        raise ValueError('unsigned divmod requires its isolated fixed Thumb selector')
    result = build(root, address, args)
    if args.emit:
        output = (Path(root) / args.emit).resolve()
        if (Path(root) / 'build').resolve() not in output.parents or output.exists():
            raise ValueError('--emit requires a new file beneath build/')
        output.parent.mkdir(parents=True, exist_ok=True)
        with output.open('xb') as stream:
            stream.write(result['body'])
    if not args.no_write:
        report = Path(root) / 'docs/match' / f'{address:08X}.md'
        report.parent.mkdir(parents=True, exist_ok=True)
        report.write_text(render(result))
    print(f'extent    {len(result["body"])} bytes (complete ELF symbol; unsigned divmod ten; no relocations)')
    print('verdict MATCH - byte identical')
    return 0
