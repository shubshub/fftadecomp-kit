"""Reconstruct the original libgcc2 signed division member and its private leading-zero table."""
import argparse
from pathlib import Path
import struct
import sys
import tempfile

import library_units as units
import owner_admission_profile as owner
import owner_graph_profile as graph
import software_double_profile as wide
import software_float_profile as runtime

ADDRESS, END, COUNT = 0x08142280, 0x081426B8, 496
SELECTOR = 'libgcc-divdi3-v1'
SCHEMA = 'elf-symbol-thumb-libgcc-divdi3-v1'
TABLE = 0x0836CF98
TABLE_BYTES = bytes(value.bit_length() for value in range(256))
TABLE_WORDS = (0x12C, 0x184, 0x2FC)
TARGETS = {'__udivsi3': 0x08142AB0, '__umodsi3': 0x08142B28}
CALLS = {site: target for site, target in wide.WIDE_EDGES if ADDRESS <= site < END}
CALLERS = ((0x08127458, 0x08127592, 149, 0x081274F2,
            'c8d47ef776f97a660c229e3e434970f94e2faeaebcaf5f127a56a10419eda0d3'),
           (0x08127C94, 0x08127D0C, 59, 0x08127CD8,
            '9588adb6bb3f7c8a433d35eb2e67962cbe3159d6a43fee6d4b5b88f97930521b'))
# Raw .text of the independently built historical libgcc2.c -DL_divdi3 object.
ORIGINAL_TEXT = 'caa3c2bff4c7344c9348aa192bccecc7cb624be29f596ece7bc8da9facf1d35c'
SOURCE = 'e191477e4891b9f73041308ac24e5350795d20f143c3f4c97790e359b24dfb12'


def require(condition, message):
    if not condition:
        raise ValueError(f'libgcc signed division requires {message}')


def member_sections(image, linked):
    """One global Thumb function and one local, byte-aligned, read-only object."""
    import match
    base = ADDRESS if linked else 0
    table_address = TABLE if linked else 0
    require(image['type'] == (2 if linked else 1) and len(image['symbol_tables']) == 1,
            'a single-symbol-table ARM executable or relocatable object at the correct stage')
    indices = [i for i, name in enumerate(image['section_names']) if name == '.rodata']
    require(len(indices) == 1, 'one .rodata section')
    ro, text = indices[0], image['text_index']
    require({i for i, s in enumerate(image['sections']) if s[2] & 2 and s[5]} == {ro, text},
            'only the two nonempty allocated member sections')
    for i, flags, address, size, alignment in ((text, 6, base, END-ADDRESS, 4),
                                              (ro, 2, table_address, 256, 1)):
        section = image['sections'][i]
        require((section[1:4], section[5], section[8]) == ((1, flags, address), size, alignment),
                'exact section type, access flags, placement, size and alignment')
    require(image['section_data'][ro] == TABLE_BYTES, 'the original 256 bit lengths')
    function, offset = match.function_record(image, 'func_08142280', ADDRESS, True)
    require(offset == 0 and function['bind'] == 1 and function['size'] == END-ADDRESS,
            'the complete addressed global Thumb symbol')
    table_symbol = dict(name='__clz_tab', type=1, bind=0, value=table_address, size=256, section=ro)
    symbols = image['symbols']
    require([s for s in symbols if s['type'] == 1 or s['name'] == '__clz_tab'] == [table_symbol],
            'exactly one local, sized table object')
    require([s for s in symbols if s['type'] == 2 and s['section'] != 0xfff1] == [function],
            'exactly one member function')
    for name, target in TARGETS.items():
        expected = dict(name=name, type=2 if linked else 0, bind=1, size=0,
                        value=(target|1) if linked else 0, section=0xfff1 if linked else 0)
        require([s for s in symbols if s['name'] == name] == [expected], 'the original helper symbol roles')
    require({s['name'] for s in symbols if s['bind'] and s['name']} ==
            {*TARGETS, 'func_08142280'}, 'the exact external symbol namespace')
    return ro


def original_bindings(image):
    ro = member_sections(image, False)
    names = {v: k for k, v in TARGETS.items()}
    expected = {site-ADDRESS: names[target] for site, target in CALLS.items()}
    expected.update(dict.fromkeys(TABLE_WORDS))
    seen = set()
    require(len(image['relocations']) == 1, 'one complete text relocation section')
    idx, = image['relocations']
    section = image['sections'][idx]
    require(section[1] == 9 and section[7] == image['text_index'] and section[9] == 8 and
            section[5] == 8*len(expected) and section[6] in image['symbol_tables'], 'the original text REL layout')
    symbols = image['symbol_tables'][section[6]]
    for offset, info in struct.iter_unpack('<II', image['section_data'][idx]):
        require(offset in expected and offset not in seen and info >> 8 < len(symbols), 'unique original REL sites')
        seen.add(offset)
        symbol = symbols[info >> 8]
        name = expected[offset]
        addend = image['text'][offset:offset+4]
        if name is None:
            require((info & 255, symbol, addend) == (2, dict(name='', type=3, bind=0, section=ro, size=0,
                                                             value=0), bytes(4)),
                    'zero-addend ABS32 against the local .rodata section')
        else:
            require(info & 255 == 10 and symbol['name'] == name and addend == bytes.fromhex('fff7feff'),
                    'original zero-addend Thumb calls to each selected helper')
    require(seen == set(expected) and units.sha(image['text']) == ORIGINAL_TEXT, 'the complete historical object text')


def linked_member(image, rom, mapping):
    import match
    member_sections(image, True)
    body = image['text']
    require(not image['relocations'] and body == rom[ADDRESS-match.ROM_BASE:END-match.ROM_BASE] and
            TABLE_BYTES == rom[TABLE-match.ROM_BASE:TABLE-match.ROM_BASE+256], 'both fully linked ROM sections')
    require(all(struct.unpack_from('<I', body, off)[0] == TABLE for off in TABLE_WORDS), 'all three rebound table words')
    refinement = owner.refine(body, ADDRESS, mapping)
    ins, edges, branches, calls, words = graph.graph(body, ADDRESS, refinement)
    require(len(ins) == COUNT and calls == CALLS and not words and not branches, 'the 496-instruction original CFG')
    partition = graph.partition(body, ADDRESS, refinement, ins, words)
    from libgcc_divdi3_bounds import table_reads
    return body, dict(partition=partition, loads=table_reads(ins, edges, partition))


def native_context(rom, mapping, index):
    import match
    require(units.sha(rom) == runtime.ROM_SHA256, 'the original USA ROM')
    entries, rows = wide.indices(mapping, index)
    dependencies = wide.prove_wide_closure(rom, mapping, index)
    callers = []
    for start, end, count, site, checksum in CALLERS:
        entry = wide.span_record(start, end, entries, rows, rom)
        body = rom[start-match.ROM_BASE:end-match.ROM_BASE]
        require(entry['instrs'] == count and units.sha(body) == checksum, 'the original movement callers')
        ins, _, _, calls, _ = graph.graph(body, start, owner.refine(body, start, mapping))
        require(len(ins) == count and [p for p,t in calls.items() if t == ADDRESS] == [site],
                'the original callers and signed-wide call sites')
        callers.append([start, end, count, site, checksum])
    return dict(callers=callers, direct_calls=sorted(CALLS.items()),
                runtime_proofs=units.sha(units.canonical(dependencies).encode()))


def build(root, address, args=None):
    import match
    import plausible
    from match_evidence import source_fingerprint, mapping_snapshot, report_rom_path, source_paths
    from sdk_cpuset_halfword import base_header
    from unit_fpbit_source import compiler_hashes
    root = Path(root).resolve()
    require(address == ADDRESS, 'the original member address')
    old = units.resolve('old-agbcc-O2-v1')
    config = dict(cc=match.DEFAULT_CC, flags=match.DEFAULT_FLAGS, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                  linker=match.DEFAULT_LD, objcopy=match.DEFAULT_OBJCOPY)
    binaries = compiler_hashes(argparse.Namespace(**config))
    if args:
        wide.fixed_configuration(args)
        require(args.mode == 'thumb' and args.control_flow_profile == 'ordinary' and not args.unit_toolchain and
                not args.label and units._selectors(args) == ['owner_runtime_profile'] and
                args.owner_runtime_profile == SELECTOR, 'its isolated default compiler selector')

    def snapshots():
        return (source_fingerprint(root, address), mapping_snapshot(root), runtime.index_snapshot(root),
                units.snapshot(root), Path(report_rom_path(root)).read_bytes())
    source, mapping, index, unit_rows, rom = initial = snapshots()
    require(units.containing(units.parse(unit_rows, rom, mapping), address, END) is None, 'a standalone libgcc2 member')
    context = native_context(rom, mapping, index)
    relative = 'src/08142280.c'
    builds = {}
    directory = root/'build'
    directory.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(dir=directory, prefix='libgcc_divdi3_') as work:
        capture = Path(work)
        for path in source_paths(root, address):
            dest = capture/path.relative_to(root)
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(path.read_bytes())
        require(source_fingerprint(capture, address) == source and
                plausible.include_closure(capture, capture/relative) == ({relative, 'include/ffta.h'}, []) and
                units.sha((capture/relative).read_bytes()) == SOURCE and
                base_header((capture/'include/ffta.h').read_bytes(), ('func_08142280', '__clz_tab', *TARGETS)),
                'the reviewed libgcc2 arithmetic source and public base types')
        proc = match._run_replay_process([sys.executable, str(Path(__file__).with_name('plausible.py')),
            '--quiet', '--addr', f'0x{address:08X}', '--json', relative, 'include/ffta.h'], capture, 120)
        require(not any(match.plausibility_result(proc, address)), 'plausible C')
        for toolchain, cc, flags in (('default', config['cc'], config['flags']), (old['id'], old['cc'], old['flags'])):
            compiler = argparse.Namespace(**{**config, 'cc': cc, 'flags': flags})
            runner = match.Runner(cc, 'Ubuntu', match.DEFAULT_WSL_PATH, root=capture, timeout=120)
            with runner.workspace() as workspace:
                raw, _, original = match.compile_object(runner, workspace, compiler, capture, address, relative)
                original_bindings(original)
                linked = match.link_typed_targets(runner, workspace, compiler, 'func_08142280', address, TARGETS,
                                                  set(), libgcc_divdi3_table=True)
                body, cfg = linked_member(linked, rom, mapping)
                patches = {site-ADDRESS for site in CALLS} | set(TABLE_WORDS)
                patched = {offset+i for offset in patches for i in range(4)}
                require(all(original['text'][i] == byte for i, byte in enumerate(body) if i not in patched),
                        'only the twenty original relocation fields changed by GNU ld')
                builds[toolchain] = dict(object=units.sha(raw), linked=units.sha(runner.read_binary(workspace+'/f.elf')))
        require(source_fingerprint(capture, address) == source, 'stable captured source')
    require(snapshots() == initial and units.resolve(old['id']) == old and
            compiler_hashes(argparse.Namespace(**config)) == binaries, 'stable inputs and compilers')
    evidence = dict(builds=builds, historical_compiler=old, tool_binaries=binaries, source=source, cfg=cfg, context=context,
                    table=dict(address=TABLE, size=256, sha256=units.sha(TABLE_BYTES), original_rel_offsets=TABLE_WORDS))
    report = '\n'.join([f'# match report - 0x{address:08X}', '', f'* source: `{relative}`',
        f'* verification: `{SCHEMA}`', f'* source SHA-256: `{source}`',
        f"* compiler: `{config['cc']} {config['flags']}`",
        '* verified extent: complete ELF function symbol, including literal pools',
        '* control flow: signed two-word operands in R0:R1 and R2:R3 use unsigned limb division. '
        'The three computed reads select one byte of the private 256-byte bit-length table. '
        'The ordinary quotient requires a nonzero divisor and a representable signed result.',
        '* callers: 081274F2 divides a zero-extended 16-bit distance shifted by 32 by a '
        'zero-extended 16-bit duration shifted by 16, then stores both result words. '
        '08127CD8 divides a position shifted by 16 by the stored 64-bit step, then takes '
        'quotient bits 16 through 47 for the halfword frame index. The caller supplies a valid frame index.',
        '* relocations: 17 Thumb helper calls and 3 private section references resolved',
        '* source plausibility: plausible', '* hand-asm allow list: not listed',
        f'* libgcc division evidence: `{units.canonical(evidence)}`', f'* compiled : `{body.hex()}`',
        f'* ROM bytes: `{body.hex()}` ({len(body)} bytes)', '', f'**MATCH - byte identical** - {len(body)}/{len(body)} bytes', ''])
    return body, report


def issue(root, address, args):
    import unit_fpbit_source as source
    return source.issue(sys.modules[__name__], root, address, args)


def report_matches(report, root, address):
    return (address == ADDRESS and report.splitlines().count(f'* verification: `{SCHEMA}`') == 1 and
            report == build(root, address)[1])
