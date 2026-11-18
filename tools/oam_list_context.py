"""Verify the three contiguous sprite-list routines that share the HideEntries inline."""

import argparse
from hashlib import sha256
import json
from pathlib import Path
import re
import shlex
import struct
import subprocess
import tempfile

from sdk_cpuset_halfword import TOKEN, base_header

BASE = 0x08000000
MEMBERS = (0x0800105C, 0x08001194, 0x08001244)
OWNER = MEMBERS[-1]
END = 0x080012BC
SCHEMA = 'original-oam-list-context-v1'
HEADER = 'include/oam_lists.h'
GAME_HEADER = 'include/ffta.h'
INPUT_TOKENS = {
    'src/0800105C.c': 'b08aff98aa41f4ce53884c6e2a5a2532ae0cdf385156634ec3aa9c469aab086b',
    'src/08001194.c': '6c53f4b5e77ad422e80265ab45a133e11b8248ba25063f10966e6df1e33c3a6b',
    'src/08001244.c': '0693d56ca663b0d9c7335cfa742a420a155c80faf38266a8eb8804709659c57d',
    HEADER: 'e64a32e9f2159840a3e6ee6167dcb801bab5854207acd93d3b2d1165a2b5ead4',
}
COUNTS = (123, 65, 46)
VENEER = 0x0814224C
CALL_OFFSETS = ((0xDA, 0xE8), (0x12, 0x24), ())
DATA_WORDS = (
    (
        (0xFC, '03000028'),
        (0x100, '03002F58'),
        (0x104, '03002C50'),
        (0x108, '03002F60'),
        (0x10C, '03000020'),
        (0x110, '03003168'),
        (0x114, '03002C58'),
        (0x118, '03002F68'),
        (0x11C, '03000030'),
        (0x120, '03003170'),
        (0x124, '0836D4B8'),
        (0x130, '03003270'),
        (0x134, '030032B0'),
    ),
    (
        (0x88, '0836D4B8'),
        (0x8C, '03000028'),
        (0x90, '03003270'),
        (0x94, '030032B0'),
        (0x98, '03002C58'),
        (0x9C, '03002C50'),
        (0xA8, '03000030'),
        (0xAC, '03000020'),
    ),
    ((0x5C, '03002F58'), (0x60, '03002F68'), (0x64, '03002F60'), (0x68, '03003170'), (0x6C, '03003168')),
)
GROUP_DIGEST = '4cec81d45e300f9c0c2d7a99ad8b2d878c4f04ac16456752b41de878ea6ac108'
ALONE_DIGEST = 'b08362ecf5501cdc2bbb66b20e287dd8abad8c4db9dfe2d3130488f5c8270903'


def require(ok, message):
    if not ok:
        raise ValueError('OAM list context: ' + message)


def source(address):
    return f'src/{address:08X}.c'


def prefix_options(address, name, prefix):
    require(
        address == OWNER and name == source(OWNER) and prefix in (MEMBERS[:-1], MEMBERS[1:-1]),
        'unregistered ordered source context',
    )
    return ''.join(f'-include {shlex.quote(source(member))} ' for member in prefix)


def verify_dependencies(preprocessed, root, prefix):
    root = Path(root).resolve()
    names = re.findall(r'^#\s+\d+\s+"([^"\n]+)"', preprocessed, re.M)
    observed = {(root / name).resolve() for name in names if not name.startswith('<')}
    expected = {root / source(a) for a in (*prefix, OWNER)} | {root / HEADER, root / GAME_HEADER}
    require(observed == expected, 'preprocessor did not consume exactly the ordered sources and the two headers')


def check_indices(mapping, index, objects):
    rows = json.loads(mapping)
    text_rows = [line.split() for line in index.decode().splitlines() if line.strip() and not line.startswith('#')]
    for start, end, count in zip(MEMBERS, (*MEMBERS[1:], END), COUNTS):
        intersecting = [row for row in rows if int(row['rom'], 16) < end and int(row['end'], 16) > start]
        require(
            len(intersecting) == 1
            and (
                int(intersecting[0]['rom'], 16),
                int(intersecting[0]['end'], 16),
                intersecting[0]['instrs'],
                intersecting[0]['mode'],
            )
            == (start, end, count, 'thumb'),
            'changed JSON extent',
        )
        overlapping = [row for row in text_rows if int(row[0], 16) < end and int(row[1], 16) > start]
        require(
            overlapping == [[f'{start:08X}', f'{end:08X}', str(end - start), str(count), 'return']],
            'changed text extent',
        )
    for words in DATA_WORDS:
        for _, digits in words:
            name = ('g_callbacks_' if digits == '0836D4B8' else 'data_') + digits
            require(objects.get(name) == int(digits, 16), 'changed object binding ' + name)
    require(
        sum(
            int(row['rom'], 16) == VENEER and row['mode'] == 'thumb' and int(row['end'], 16) == VENEER + 2
            for row in rows
        )
        == 1,
        'missing clear veneer',
    )


def inputs(root):
    import plausible

    files = {}
    for path, expected in INPUT_TOKENS.items():
        file = root / path
        if path.startswith('src/'):
            require(list((root / 'src').rglob(file.name)) == [file], 'duplicate or missing addressed source')
            require(
                plausible.include_closure(root, file) == ({path, HEADER, GAME_HEADER}, []),
                'unexpected include closure',
            )
        require(not file.is_symlink() and not plausible.check_file(file), 'invalid source or header ' + path)
        data = file.read_bytes()
        text = data.decode('utf-8')
        require(not any(marker in text for marker in ('\\', '??', '%:', '\0')), 'unexpected preprocessor spelling')
        tokens = TOKEN.findall(plausible.strip_comments_and_strings_keep_strings(text))
        require(
            sha256(' '.join(tokens).encode()).hexdigest() == expected,
            'changed reviewed declarations or body ' + path,
        )
        files[path] = data
    header = (root / GAME_HEADER).read_bytes()
    names = (
        'AffineMatrix',
        'BufferInitializer',
        'HideEntries',
        'u64',
        'HIDDEN_OAM_ENTRY',
        *(f'func_{a:08X}' for a in MEMBERS),
    )
    require(base_header(header, names), 'unreviewed common ABI')
    files[GAME_HEADER] = header
    return files


def addresses(group):
    return [(MEMBERS.index(a), a, (MEMBERS[1:] + (END,))[MEMBERS.index(a)]) for a in group]


def relocations(image, group, objects):
    targets, bindings, expected = {}, {}, {}
    for i, addr, _ in addresses(group):
        base = addr - group[0]
        for offset in CALL_OFFSETS[i]:
            name = 'func_0814224C'
            targets[name] = VENEER
            expected[base + offset] = (10, name, bytes.fromhex('fff7feff'))
        for offset, digits in DATA_WORDS[i]:
            name = ('g_callbacks_' if digits == '0836D4B8' else 'data_') + digits
            targets[name] = bindings[name] = objects[name]
            expected[base + offset] = (2, name, bytes(4))
    rels = image['relocations']
    require(len(rels) == 1, 'expected one .rel.text')
    section = image['sections'][rels[0]]
    require(
        section[1] == 9
        and section[7] == image['text_index']
        and section[9] == 8
        and section[5] == 8 * len(expected),
        'changed relocation section',
    )
    syms = image['symbol_tables'][section[6]]
    for offset, info in struct.iter_unpack('<II', image['section_data'][rels[0]]):
        sym = syms[info >> 8]
        require(
            sym['bind'] == 1
            and sym['section'] == sym['type'] == sym['value'] == sym['size'] == 0
            and expected.pop(offset, None) == (info & 255, sym['name'], image['text'][offset : offset + 4]),
            'unregistered relocation, symbol or addend',
        )
    require(not expected, 'missing a relocation')
    return targets, bindings


def compile_group(stage, group, args, objects):
    import match

    base = group[0]
    primary = group[-1]
    runner = match.Runner(args.cc, root=str(stage), timeout=match.SIGNED_REPLAY_TIMEOUT)
    with runner.workspace() as ws:
        _, _, image = match.compile_object(
            runner, ws, args, str(stage), primary, source(primary), oam_prefix=group[:-1]
        )
        match.allocated_text_only(image)
        require(
            image['type'] == 1 and len(image['text']) == addresses(group)[-1][2] - base, 'wrong relocatable extent'
        )
        targets, data = relocations(image, group, objects)
        linked = match.link_typed_targets(runner, ws, args, f'func_{base:08X}', base, targets, data)
        match.allocated_text_only(linked)
        require(not linked['relocations'] and len(linked['text']) == len(image['text']), 'incomplete linked object')
        for obj in (image, linked):
            funcs = [sym for sym in obj['symbols'] if sym['type'] == 2 and sym['section'] == obj['text_index']]
            require(len(funcs) == len(group), 'unexpected text function')
            for i, addr, end in addresses(group):
                sym, start = match.function_record(obj, f'func_{addr:08X}', addr, True)
                require(
                    sym['bind'] == 1 and start == addr - base and sym['size'] == end - addr,
                    'changed complete symbol',
                )
        for i, addr, end in addresses(group):
            body = linked['text'][addr - base : end - base]
            calls = {addr + n: VENEER for n in CALL_OFFSETS[i]}
            code = match.verify_leaf_instructions(body, addr, True, calls, incoming_narrow_reads=True)
            require(len(code) == COUNTS[i], 'changed reachable instruction count')
            match.verify_data_literals(code, addr, {offset for offset, _ in DATA_WORDS[i]})
        return linked['text']


def build(root):
    import match
    from match_evidence import mapping_snapshot, data_snapshot, source_fingerprint, report_rom_path
    from empty_body_profile import index_snapshot

    root = Path(root).resolve()
    args = argparse.Namespace(
        cc=match.DEFAULT_CC,
        flags=match.DEFAULT_FLAGS,
        cpp=match.DEFAULT_CPP,
        assembler=match.DEFAULT_AS,
        objcopy=match.DEFAULT_OBJCOPY,
        linker=match.DEFAULT_LD,
    )

    def snapshot():
        return (
            inputs(root),
            mapping_snapshot(root),
            index_snapshot(root),
            data_snapshot(root),
            tuple(source_fingerprint(root, a) for a in MEMBERS),
            report_rom_path(root),
        )

    initial = snapshot()
    files, mapping, index, data, fingerprints, rompath = initial
    objects = match.parse_data_symbols(data)
    check_indices(mapping, index, objects)
    from scheduler_zero_descriptor import BOOT, IMAGE, IMAGE_SHA256

    rom = Path(rompath).read_bytes()
    require(sha256(rom[MEMBERS[0] - BASE : END - BASE]).hexdigest() == GROUP_DIGEST, 'changed original unit span')
    for start, end, digest in (
        *BOOT,
        (IMAGE, IMAGE + 176, IMAGE_SHA256),
        (0x08002768, 0x080027B8, "6e9dc4c6a9f37a50fb532938d3c1d4e5bd2eb08e1e45744ec654f057d08dd718"),
        (0x08000460, 0x080004B0, 'a45b5c91a123208bc6f72c3abb06ed2480139315ae57e635eaef02817351d859'),
        (0x08000290, 0x080002C6, '637d50860f5bb83a5f2c93a01068d486717b97872e6ed8009c5f23e9ccc25b17'),
    ):
        require(sha256(rom[start - BASE : end - BASE]).hexdigest() == digest, 'changed startup or frame caller')
    require(
        rom[VENEER - BASE : VENEER - BASE + 2] == bytes.fromhex('1047')
        and rom[0x36D4B8:0x36D4BC] == struct.pack('<I', 0x03005E79),
        'changed clear target',
    )
    directory = root / 'build'
    directory.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='oam-list-context.', dir=directory) as work:
        stage = Path(work)
        for name, contents in files.items():
            p = stage / name
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_bytes(contents)
        for addr, end in zip(MEMBERS[:-1], MEMBERS[1:]):
            predecessor = compile_group(stage, (addr,), args, objects)
            require(predecessor == rom[addr - BASE : end - BASE], 'changed standalone predecessor')
        alone = compile_group(stage, (OWNER,), args, objects)
        require(sha256(alone).hexdigest() == ALONE_DIGEST, 'changed standalone control')
        short = compile_group(stage, MEMBERS[1:], args, objects)
        require(short == rom[MEMBERS[1] - BASE : OWNER - BASE] + alone, 'changed genuine two-member control')
        linked = compile_group(stage, MEMBERS, args, objects)
        require(linked == rom[MEMBERS[0] - BASE : END - BASE], 'context does not match all three original members')
    require(snapshot() == initial, 'source, includes, maps or ROM selection changed during verification')
    body = linked[OWNER - MEMBERS[0] :]
    text = '\n'.join(
        (
            '# match report - 0x08001244',
            '',
            '* source: `src/08001244.c`',
            f'* verification: `{SCHEMA}`',
            f'* source SHA-256: `{fingerprints[-1]}`',
            f'* ordered context source SHA-256: `{fingerprints[0]}/{fingerprints[1]}/{fingerprints[2]}`',
            f'* mapping SHA-256: `{sha256(mapping).hexdigest()}`',
            f'* data symbols SHA-256: `{sha256(data).hexdigest()}`',
            f'* compiler: `{args.cc} {args.flags}`',
            '* verified extent: complete ELF function symbol, including literal pools',
            '* context: 0800105C, 08001194 and 08001244 include oam_lists.h; all 608 linked bytes equal the ROM.',
            f'* context SHA-256: `{GROUP_DIGEST}`',
            '* controls: each predecessor matches alone; alone and following 08001194 the owner matches 114/120 bytes.',
            '* behavior: startup 08000296 calls 0800105C; 08000464 and 08000468 call 08001194 then 08001244. '
            'The active secondary bank (0 or 1) has 32 and 16 eight-byte slots. Signed positive counts require '
            'their respective capacities. Each visited entry receives 0x0000000000F800A8, then both counts clear.',
            '* relocations: four R_ARM_THM_CALL to 0814224C and 26 R_ARM_ABS32 object words resolved over the context; '
            'the owner contains five object words, all read by reachable PC-relative loads.',
            f'* ROM bytes: `{body.hex()}` ({len(body)} bytes)',
            f'* compiled : `{body.hex()}`',
            '* source plausibility: plausible',
            '* hand-asm allow list: not listed',
            '',
            f'**MATCH - byte identical** - {len(body)}/{len(body)} bytes',
            '',
        )
    )
    return body, text


def issue(root, address, args):
    import match
    from software_double_profile import fixed_configuration

    fixed_configuration(args)
    require(
        address == OWNER
        and args.mode == 'thumb'
        and args.control_flow_profile == 'ordinary'
        and not args.label
        and not args.unit_toolchain
        and not args.palette_closure_bundle
        and not any(
            value
            for name, value in vars(args).items()
            if name.endswith('_profile') and name != 'control_flow_profile'
        ),
        'requires the ordinary Thumb build',
    )
    root = Path(root)
    body, report = build(root)
    if args.emit:
        out = (root / args.emit).resolve()
        require((root / 'build').resolve() in out.parents, 'emit must be a new file under build/')
        with out.open('xb') as stream:
            stream.write(body)
    if not args.no_write:
        p = root / 'docs/match/08001244.md'
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(report)
    print(
        f'function  0x{OWNER:08X}   {len(body)} bytes (Thumb)\nsource    {source(OWNER)}\n'
        f'extent    {len(body)} bytes (complete ELF symbol; three-member OAM list context; no relocations)\n'
        'bytes   identical\nsource  plausible\nverdict MATCH - byte identical\n'
        f'46/46 instructions identical ({len(body)}/{len(body)} bytes)'
    )
    return 0


def replay(report, root, address):
    if address != OWNER or report.splitlines().count(f'* verification: `{SCHEMA}`') != 1:
        return False
    try:
        return build(root)[1] == report
    except (OSError, ValueError, KeyError, IndexError, TypeError, RuntimeError, subprocess.SubprocessError):
        return False
