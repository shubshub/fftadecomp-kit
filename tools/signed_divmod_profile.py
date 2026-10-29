"""Explicit numeric composition of the existing canonical signed runtimes."""
import argparse
from contextvars import ContextVar
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

import divsi3_profile as quotient
import modsi3_profile as remainder

SELECTOR = 'numeric-divmod-v1'
SCHEMA = 'elf-symbol-thumb-signed-divmod-numeric-v1'
SUMMARY = 'canonical signed quotient and remainder with existing CFG-proven numeric domains and restoring saves'
_replay = ContextVar('signed_divmod_replay', default=False)


def text(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def sha(data):
    return hashlib.sha256(data).hexdigest()


def prepare(data, address, calls, context):
    """Authenticate both exact call sets before the native verifier uses them."""
    import match
    import owner_admission_profile as owner
    if type(context) is not tuple or len(context) != 5 or \
            type(context[3]) is not dict or not context[3] or \
            type(context[4]) is not dict or context[4]:
        raise ValueError('signed divmod requires a fresh isolated canonical context')
    rom, mapping, index, bindings, observed = context
    owner.validate_span(data, address, rom, mapping, index)
    div = {site: name for site, name in bindings.items() if name == '__divsi3'}
    mod = {site: name for site, name in bindings.items() if name == '__modsi3'}
    if not div or not mod or set(div) | set(mod) != set(bindings) or \
            any(type(site) is not int or calls.get(site) !=
                (quotient.ADDRESS if name == '__divsi3' else remainder.ADDRESS)
                for site, name in bindings.items()):
        raise ValueError('signed divmod requires both actual canonical runtime call sets')
    quotient.verify_context(data, address, calls, (rom, mapping, div, {}))
    remainder.verify_context(data, address, calls, (rom, mapping, mod))
    entries = json.loads(mapping)
    for site, target in calls.items():
        if site not in bindings:
            match.function_address_target(f'func_{target:08X}', entries, address, len(data), len(rom))
            if match.function_thunk.reserved(target):
                raise ValueError('signed divmod excludes runtime/thunk substitution')
    return div, mod


def finish(data, address, calls, context, verified, divisors):
    """Retain complete byte partition and all r4-r11/SP/entry-LR restoration."""
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    import local_long_branch_profile as frame
    refinement = owner.refine(data, address, context[1])
    instructions, edges, branches, actual_calls, words = graph.graph(data, address, refinement)
    if calls != actual_calls or branches or words or \
            {item.address for item in verified} != set(instructions):
        raise ValueError('signed divmod requires the exact closed direct-call graph')
    partition = graph.partition(data, address, refinement, instructions, words)
    if any(remainder.address_literal(row['value']) for row in partition['words']):
        raise ValueError('signed divmod excludes unproved address literal provenance')
    restored = frame.prove_frame(instructions, edges, address, {}, calls, stack_aliases=True)
    context[4].update({
        'schema': SCHEMA,
        'calls': [[site - address, context[3].get(site, f'func_{target:08X}')]
                  for site, target in sorted(calls.items())],
        'divisors': [[site - address, value] for site, value in sorted(divisors.items())],
        'remainder_operands': [[site - address, 'signed16', 'nonzero']
                              for site, name in sorted(context[3].items()) if name == '__modsi3'],
        'dependencies': {'quotient': [list(row) for row in quotient.IDENTITIES],
                         'remainder': [list(row) for row in remainder.IDENTITIES]},
        'frame': restored, 'partition': partition,
        'ordinary_calls': 'entry-bound structural returning-call ABI premise only',
    })


def verify(data, address, rom, mapping, index, calls, bindings, manifest=None):
    import match
    observed = {}
    verified = match.verify_leaf_instructions(data, address, True, calls,
        signed_runtime_context=(rom, mapping, index, bindings, observed))
    if manifest is not None and text(manifest) != text(observed):
        raise ValueError('signed divmod manifest differs from complete fresh native proof')
    return observed, verified


def object_bytes(runner, workspace, args, original, address, rom, mapping):
    import match
    if original['type'] != 1:
        raise ValueError('signed divmod requires original relocatable ELF')
    match.allocated_text_only(original)
    symbol, offset = match.function_record(original, f'func_{address:08X}', address, True)
    if offset or symbol['size'] != len(original['text']) or any(
            item['type'] == 2 and item is not symbol and item['section'] or
            item['type'] == 1 and item['section'] or re.fullmatch(r'\$a(?:\..*)?', item['name'])
            for item in original['symbols']):
        raise ValueError('signed divmod requires a sole complete original Thumb ELF function')
    div, mod = {}, {}
    body, calls, literals = match.link_calls(runner, workspace, args, original, address, mapping,
        len(rom), rom, divsi3_bindings=div, modsi3_bindings=mod, signed_runtime_profile=SELECTOR)
    if literals or not div or set(div.values()) != {'__divsi3'} or \
            not mod or set(mod.values()) != {'__modsi3'}:
        raise ValueError('signed divmod requires both canonical original ELF relocations without data')
    return body, calls, div | mod


def build(root, address, args=None, expected=None):
    """Fresh source and original ELF are mandatory for every saved-report replay."""
    import match
    from match_evidence import (source_fingerprint, source_paths, mapping_snapshot,
                                data_snapshot, report_rom_path)
    from inert_spin_profile import index_snapshot
    root = Path(root)
    args = args or argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
        objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
    if (args.cc, args.cpp, args.assembler, args.objcopy, args.linker, args.flags) != (
            match.DEFAULT_CC, match.DEFAULT_CPP, match.DEFAULT_AS, match.DEFAULT_OBJCOPY,
            match.DEFAULT_LD, match.DEFAULT_FLAGS):
        raise ValueError('signed divmod requires the fixed approved toolchain')
    source, mapping, index = source_fingerprint(root, address), mapping_snapshot(root), index_snapshot(root)
    objects, selected_rom = data_snapshot(root), report_rom_path(root)
    rom = Path(selected_rom).read_bytes()
    candidates = list((root / 'src').rglob(f'{address:08X}.c'))
    if len(candidates) != 1:
        raise ValueError('signed divmod requires one uniquely addressed source')
    (root / 'build').mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='signed_divmod_', dir=root / 'build') as directory:
        captured = Path(directory)
        for path in source_paths(root, address):
            destination = captured / path.relative_to(root)
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(path.read_bytes())
        if source_fingerprint(captured, address) != source:
            raise ValueError('signed divmod source capture differs')
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
            raise ValueError('signed divmod source is implausible or changed')
    if source_fingerprint(root, address) != source or mapping_snapshot(root) != mapping or \
            index_snapshot(root) != index or data_snapshot(root) != objects or \
            report_rom_path(root) != selected_rom or Path(selected_rom).read_bytes() != rom:
        raise ValueError('signed divmod source, maps, headers or ROM changed during replay')
    return {'address': address, 'body': body, 'manifest': manifest, 'source_sha256': source,
            'mapping_sha256': sha(mapping), 'index_sha256': sha(index),
            'objects_sha256': None if objects is None else sha(objects), 'rom_sha256': sha(rom),
            'instructions': len(instructions), 'original_elf': raw, 'assembly': assembly, 'linked_elf': linked}


def render(result):
    import match
    evidence = {key: value for key, value in result.items()
                if key not in ('body', 'original_elf', 'assembly', 'linked_elf')}
    evidence['original_elf_sha256'] = sha(result['original_elf'])
    evidence['compiler'] = [match.DEFAULT_CC, match.DEFAULT_CPP, match.DEFAULT_AS,
                            match.DEFAULT_OBJCOPY, match.DEFAULT_LD, match.DEFAULT_FLAGS]
    evidence['body_sha256'] = sha(result['body'])
    encoded = text(evidence)
    return '\n'.join([f'# 0x{result["address"]:08X}', '', f'* verification: `{SCHEMA}`',
        f'* signed runtime: {SELECTOR}', f'* signed runtime evidence: `{encoded}`',
        f'* signed runtime proof SHA-256: `{sha(encoded.encode())}`',
        f'* compiler: `{match.DEFAULT_CC} {match.DEFAULT_FLAGS}`',
        '* verified extent: complete ELF function symbol, including literal pools',
        '* relocations: none', '* source plausibility: plausible',
        f'* compiled : `{result["body"].hex()}`',
        f'* ROM bytes: `{result["body"].hex()}` ({len(result["body"])} bytes)', '',
        f'**MATCH - byte identical** - {len(result["body"])}/{len(result["body"])} bytes', ''])


def selected(report):
    lines = report.splitlines()
    if SCHEMA not in report and not any(line.lstrip().startswith('* signed runtime') for line in lines):
        return False
    if [line for line in lines if line.lstrip().startswith('* verification')] != [f'* verification: `{SCHEMA}`'] or \
            [line for line in lines if line.lstrip().startswith('* signed runtime:')] != [f'* signed runtime: {SELECTOR}']:
        raise ValueError('signed divmod requires its isolated versioned report')
    return True


def report_matches(report, root, address):
    from match_evidence import valid_match_verdict
    if _replay.get():
        return False
    token = _replay.set(True)
    try:
        if not valid_match_verdict(report) or not selected(report):
            return False
        lines = [line for line in report.splitlines() if line.startswith('* signed runtime evidence: `')]
        if len(lines) != 1 or not lines[0].endswith('`'):
            return False
        def unique(pairs):
            value = {}
            for key, item in pairs:
                if key in value:
                    raise ValueError('duplicate signed divmod evidence key')
                value[key] = item
            return value
        encoded = lines[0][len('* signed runtime evidence: `'):-1]
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
    if args.mode != 'thumb' or args.control_flow_profile != 'ordinary' or args.signed_quotient_profile or \
            args.software_double_profile or args.software_double_remainder_profile or args.function_address_profile or \
            args.switch_profile or args.owner_runtime_profile or args.label or args.wsl != 'Ubuntu' or \
            args.wsl_path != match.DEFAULT_WSL_PATH:
        raise ValueError('signed divmod requires its isolated fixed Thumb selector')
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
    print(f'extent    {len(result["body"])} bytes (complete ELF symbol; signed divmod numeric proof; no relocations)')
    print('verdict MATCH - byte identical')
    return 0
