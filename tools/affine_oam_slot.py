"""Two qualified views used by the original USA affine-matrix slot allocator."""

import argparse
from hashlib import sha256
from pathlib import Path
import re
import struct

from sdk_cpuset_halfword import TOKEN, base_header

BASE = 0x08000000
OWNER = 0x08000FC8
SOURCE = 'src/08000FC8.c'
HEADER = 'include/ffta.h'
TOKENS = '19d1fdd4aec4779bc2bebd65014d0e5053967ed0237d5115d8105728836549d5'
OBJECTS = {'data_03000028': 0x03000028, 'data_03003270': 0x03003270, 'data_030032B0': 0x030032B0}
SHAPES = {
    'original': (148, 'd83cc653a221e0578bb0390613590aa3cdca381f13f100b4c691bd892fe0facc'),
    'ordinary': (124, 'e91663915cc987ce0d4a7dbf965fec0ed30642902870424c6152e1cddbe8692c'),
    'input_only': (164, 'fbb30ea5bfc3d5bd1a3e32022a63e212a31cad56d21cefbfe806f452aff6043e'),
    'table_only': (172, '2db858da4c3bae379b3505377446bfc58497282dfecdba35570e68b37cb4a25d'),
    'reversed': (148, '54dd612ffe9012765321728b006ec29ae2b23ca98317bcefcbd725262c115369'),
}
INPUT = re.compile(r'\bconst\s+(?P<qual>volatile)\s+AffineMatrix\s*\*\s*matrix\b')
TABLE = re.compile(r'\b(?P<qual>volatile)\s+AffineMatrix\s*\*\s*slots\b')
MEMBERS = re.compile(r'\bs16\s+pa\s*,\s*pb\s*,\s*pc\s*,\s*pd\s*;')

# 080018A0 invokes ObjAffineSet into a local output at SP+16, then copies all
# four halfwords through a second matrix at SP for this particular callee.
# The IRQ dispatcher selects slot +8 for VBlank, and the installed Thumb
# callback calls 080012BC. That routine reads the opposite bank, then stores
# the four matrix entries in successive OAM entries' fourth halfwords.
PROVIDER = (
    (0x080000C0, 0x080000FC, '4a1813e417f90be2f7b15bf7ee214fba1ec91497094d12a427a5be38e0393218'),
    (0x080018A0, 0x08001BBC, 'd2faf191b334f119a02ea3e146d67431580db260c64c8a78b02424e31a791418'),
    (0x08141894, 0x08141898, '9f004ab9239029bc7e051e24763751da64c47109e542f1d19f241ac89ceccb39'),
    (0x0800105C, 0x08001194, '70a974b30f60e2ce6bf1ed0fab51c73bc89526db26f69dbc298a9cf8951f75a9'),
    (0x08001194, 0x08001244, '894696301f081f3216efecf0151b96b2f9bc2b20a42dc83db1cde607ee512735'),
    (0x08000460, 0x080004B0, 'a45b5c91a123208bc6f72c3abb06ed2480139315ae57e635eaef02817351d859'),
    (0x08001CD0, 0x08001CE0, '0e9ec1883da36a70d35618f539b42a58265af17f628ce1f28cf282527273eb86'),
    (0x08000290, 0x080002C6, '637d50860f5bb83a5f2c93a01068d486717b97872e6ed8009c5f23e9ccc25b17'),
    (0x080000FC, 0x08000250, '237b613db5dbd17db5859925c91d4a063484ddfec7da970d941e2cb3afaf765b'),
    (0x080004B0, 0x0800052C, '895b06643d776f57dbbece8b3ebef57b7220ff39d75c5e6f952aa3937f0c0e0e'),
    (0x080012BC, 0x080014C8, '9b66e36f26b094d61539c4790834bd83d102e90433cf5b7e443c268cabbf8c64'),
)


def require(ok, message):
    if not ok:
        raise ValueError('affine OAM slot: ' + message)


def provider(rom):
    import scheduler_zero_descriptor as install

    for start, end, digest in (
        *PROVIDER,
        *install.BOOT,
        (0x08002768, 0x080027B8, '6e9dc4c6a9f37a50fb532938d3c1d4e5bd2eb08e1e45744ec654f057d08dd718'),
        (install.IMAGE, install.IMAGE + 176, install.IMAGE_SHA256),
        (0x0814224C, 0x0814224E, 'dd9261f0471768edc33bf979649f6297463be423da17c3f881684f5747e163a1'),
    ):
        require(
            sha256(rom[start - BASE : end - BASE]).hexdigest() == digest, f'changed original code at {start:08X}'
        )
    for a, words in (
        (0x08000388, (0x030008D0, 0x0814942C)),
        (0x08149434, (0x080004B1,)),
        (install.POINTER, (install.DESTINATION | 1,)),
    ):
        require(
            rom[a - BASE : a - BASE + 4 * len(words)] == struct.pack('<' + 'I' * len(words), *words),
            'changed installed IRQ or clear callback',
        )


def source_offsets(text, header):
    import plausible

    if not base_header(header, ('AffineMatrix', 'func_08000FC8', *OBJECTS)) or any(
        marker in text for marker in ('\\', '??', '%:', '\0')
    ):
        return set()
    code = plausible.strip_comments_and_strings_keep_strings(text)
    if not re.match(r'\A\s*#\s*include[ \t]+"ffta\.h"[ \t]*\n', code):
        return set()
    if sha256(' '.join(TOKEN.findall(code)).encode()).hexdigest() != TOKENS:
        return set()
    return {INPUT.search(code).start('qual'), TABLE.search(code).start('qual')}


def qualifier_offsets(text, tree, project, closure):
    import match
    from rompath import rom_path

    if closure != ({HEADER, SOURCE}, []):
        return set()
    offsets = source_offsets(text, (Path(tree) / HEADER).read_bytes())
    if offsets:
        symbols = match.parse_data_symbols(match.data_snapshot(project))
        require(all(symbols.get(k) == v for k, v in OBJECTS.items()), 'changed bank globals')
        rom = Path(rom_path(project)).read_bytes()
        provider(rom)
        require(
            sha256(rom[OWNER - BASE : OWNER - BASE + 148]).hexdigest() == SHAPES['original'][1],
            'changed allocator',
        )
    return offsets


def rewrite(text, variant):
    if variant == 'reversed':
        text, count = MEMBERS.subn('s16 pd, pc, pb, pa;', text)
        require(count == 1, 'expected one ordered matrix')
        return text
    for pattern, retained in ((INPUT, 'input_only'), (TABLE, 'table_only')):
        if variant in ('ordinary', 'input_only', 'table_only') and variant != retained:
            matches = list(pattern.finditer(text))
            require(len(matches) == 1, 'expected one qualified input and slot view')
            start, end = matches[0].span('qual')
            text = text[:start] + text[end:]
    return text


def check_bodies(bodies):
    import match

    for key, body in bodies.items():
        require((len(body), sha256(body).hexdigest()) == SHAPES[key], 'changed ' + key + ' native body')
    require(bodies.keys() == SHAPES.keys(), 'missing native control')
    # Four paired source/destination halfword comparisons. Each insertion
    # then reads the source, reads its destination and writes the source value.
    sites = [0x20 + 8 * i + j for i in range(4) for j in (0, 2)]
    sites += [0x68 + 6 * i + j for i in range(4) for j in (0, 2, 4)]
    qualified = match.verify_leaf_instructions(bodies['original'], OWNER, True)
    ordinary = match.verify_leaf_instructions(bodies['ordinary'], OWNER, True)
    accesses = [(i.address - OWNER, i.mnemonic) for i in qualified if i.mnemonic in ('ldrh', 'strh')]
    require(
        accesses == list(zip(sites, ['ldrh'] * 8 + ['ldrh', 'ldrh', 'strh'] * 4)), 'changed qualification effects'
    )
    require(
        [i.mnemonic for i in ordinary if i.mnemonic in ('ldr', 'ldrh', 'strh') and '[pc' not in i.op_str]
        == ['ldr'] * 4 + ['ldrh', 'strh'] * 4,
        'changed ordinary comparisons or stores',
    )
    expected = bytearray(bodies['original'])
    for site in sites:
        expected[site] ^= 0xC0  # Reverse the four halfword displacements 0/2/4/6.
    require(bodies['reversed'] == expected, 'access did not follow its named member')


def compile_bodies(root, rom):
    import match

    args = argparse.Namespace(
        cc=match.DEFAULT_CC,
        cpp=match.DEFAULT_CPP,
        flags=match.DEFAULT_FLAGS,
        assembler=match.DEFAULT_AS,
        objcopy=match.DEFAULT_OBJCOPY,
        linker=match.DEFAULT_LD,
    )
    runner = match.Runner(
        args.cc, 'Ubuntu', match.DEFAULT_WSL_PATH, root=str(root), timeout=match.SIGNED_REPLAY_TIMEOUT
    )
    bodies = {}
    with runner.workspace() as ws:
        for variant in SHAPES:
            _, _, image = match.compile_object(
                runner,
                ws,
                args,
                str(root),
                OWNER,
                SOURCE,
                rewrite=None if variant == 'original' else lambda text: rewrite(text, variant),
            )
            match.allocated_text_only(image)
            body, calls, data = match.link_calls(
                runner,
                ws,
                args,
                image,
                OWNER,
                match.mapping_snapshot(root),
                len(rom),
                rom,
                match.data_snapshot(root),
            )
            require(not calls and len(data) == 3 and dict(data.values()) == OBJECTS, 'changed bound objects')
            bodies[variant] = body
    check_bodies(bodies)
    require(bodies['original'] == rom[OWNER - BASE : OWNER - BASE + 148], 'linked allocator differs from original')
    return bodies


def record(root):
    import plausible
    from rompath import rom_path

    root = Path(root)
    source = root / SOURCE
    require(
        list((root / 'src').rglob(source.name)) == [source]
        and qualifier_offsets(source.read_text(), root, root, plausible.include_closure(root, source)),
        'expected the reviewed allocator and both access views',
    )
    compile_bodies(root, Path(rom_path(root)).read_bytes())
    hashes = '/'.join(shape[1] for shape in SHAPES.values())
    return (
        '* allowlisted volatile affine slot: original/ordinary/input-only/table-only/reversed '
        f'`{hashes}`; 08001922 ObjAffineSet result copied to the word-aligned eight-byte private input passed at 08001948; '
        'input remains stable. 08001B06 inserts the returned 5-bit index into OBJ attribute 1. '
        'Two 32-slot ordinary RAM banks, 8 bytes per matrix; current selector 0 or 1. '
        '0800105C bulk-clears both banks; 08001194 bulk-clears the active bank. Requires installed clear '
        'and IRQ handler, stable nonoverlapping input and exclusive writer bank. After the selector flips, '
        'VBlank +8/080004D8 reads the opposite bank and writes occupied PA/PB/PC/PD to '
        '07000006 + 32*slot + {0,8,16,24}; requires VBlank and no reset or bank reuse during the transfer.'
    )


def report_body(report, root):
    from rompath import rom_path

    with open(rom_path(root), 'rb') as stream:
        stream.seek(OWNER - BASE)
        body = stream.read(148)
    lines = report.splitlines()
    return len(body) == 148 and all(
        lines.count(line) == 1
        for line in (
            '* verification: `elf-symbol-thumb-data-v1`',
            f'* ROM bytes: `{body.hex()}` (148 bytes)',
            f'* compiled : `{body.hex()}`',
            '**MATCH - byte identical** - 148/148 bytes',
        )
    )
