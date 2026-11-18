"""The USA BLDALPHA ramp writer, its 160-row payload and the original scanline transfer."""

import argparse
from hashlib import sha256
from pathlib import Path
import re

from bg_affine_rows import scanline_pipeline
from sdk_cpuset_halfword import TOKEN, base_header

BASE = 0x08000000
OWNER = 0x0800DB0C
SOURCE = 'src/0800DB0C.c'
HEADER = 'include/ffta.h'
TOKENS = '80158d2ac54e1e7fb7f06a8c0ecea665118700273607e54ccc3761585ae58eda'
TARGETS = (0x0800C614, 0x080075CC, 0x080075CC, 0x080076A0, 0x080076A0, 0x0800C64C)
SHAPES = {
    'qualified': (218, '9f4f7b45606cd9f8bdc14ec0e1e8aea2c4cd3d0c5e7c3fb809cab1aaaa0a3cbb'),
    'ordinary': (210, 'e76047af6c92f74968d717143eb176a7de5865a3aa6f0927a82dfea564daf7ae'),
    'reversed': (216, '419c3d5ed3c8e4b755ededd0a8bafb7e8278a94591ab3e572e18e9aa0e6d6b91'),
}
PROVIDERS = (
    (0x080D96F0, 0x080D979A, '28c60de84e70f3b775b966a12d1859cb1fda6e43e50f82dbbfd0d0a1a2cca5b2'),
    (0x0800D61C, 0x0800D664, '28df2f7430ea98719177a109c9ef6d9c1a6d42b7a137eb8f8773c953875785d0'),
    (0x080075CC, 0x0800761E, 'fabe74ee62782a4aa7c19892051162aa8cbddac5933389fe36101ee650f6ae80'),
    (0x080076A0, 0x080076F4, '2d9d439311772de3361680e4b4b19685e89ef56f32e9772d01334dcb9f942383'),
    (0x0800DEC0, 0x0800DECC, '0d1aa48c21dc4e145ebc66645f16dd40de3cb612608c1d26f58e05477f762486'),
)
VIEW = re.compile(r'\b(?P<qual>volatile)\s+BlendTable\s*\*\s*table\b')
MEMBERS = re.compile(r'(u8\s+)eva(\s*:\s*8\s*;\s*u8\s+)evb(\s*:\s*8\s*;)')


def require(condition, message):
    if not condition:
        raise ValueError('BLDALPHA ramp: ' + message)


def provider(rom):
    scanline_pipeline(rom)
    for start, end, digest in PROVIDERS:
        require(sha256(rom[start - BASE : end - BASE]).hexdigest() == digest, f'changed native path at {start:08X}')


def qualifier_offsets(text, tree, project, closure):
    import plausible
    from rompath import rom_path

    if closure != ({SOURCE, HEADER}, []) or any(marker in text for marker in ('\\', '??', '%:', '\0')):
        return set()
    names = (
        'LineState',
        'BlendTable',
        'BlendRow',
        'Object0800C614',
        'func_0800DB0C',
        'func_0800C614',
        'func_0800C64C',
        'func_080075CC',
        'func_080076A0',
    )
    if not base_header((Path(tree) / HEADER).read_bytes(), names):
        return set()
    code = plausible.strip_comments_and_strings_keep_strings(text)
    if not re.match(r'\A\s*#\s*include[ \t]+"ffta\.h"[ \t]*\n', code):
        return set()
    view = VIEW.search(code)
    if not view or sha256(' '.join(TOKEN.findall(code)).encode()).hexdigest() != TOKENS:
        return set()
    rom = Path(rom_path(project)).read_bytes()
    provider(rom)
    length, digest = SHAPES['qualified']
    require(sha256(rom[OWNER - BASE : OWNER - BASE + length]).hexdigest() == digest, 'changed original writer')
    return {view.start('qual')}


def rewrite(source, kind):
    if kind == 'ordinary':
        return VIEW.sub('BlendTable *table', source, count=1)
    require(kind == 'reversed', 'unknown compiler control')
    return MEMBERS.sub(r'\1evb\2eva\3', source, count=1)


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
    runner = match.Runner(args.cc, root=str(root), timeout=match.SIGNED_REPLAY_TIMEOUT)
    mapping = match.mapping_snapshot(root)
    bodies = {}
    with runner.workspace() as ws:
        for kind, (length, digest) in SHAPES.items():
            _, _, image = match.compile_object(
                runner,
                ws,
                args,
                str(root),
                OWNER,
                SOURCE,
                rewrite=None if kind == 'qualified' else lambda s: rewrite(s, kind),
            )
            match.allocated_text_only(image)
            symbol, offset = match.function_record(image, 'func_0800DB0C', OWNER, True)
            require(
                offset == 0
                and symbol['bind'] == 1
                and symbol['size'] == length
                and image['text'][length:] == (bytes.fromhex('c046') if length % 4 else b''),
                'changed ELF extent',
            )
            body, calls, data = match.link_calls(runner, ws, args, image, OWNER, mapping, len(rom), rom)
            require(not data and tuple(calls[k] for k in sorted(calls)) == TARGETS, 'changed original calls')
            require(
                (len(body), sha256(body).hexdigest()) == (length, digest), 'changed complete ' + kind + ' writer'
            )
            bodies[kind] = body
    require(
        bodies['qualified'] == rom[OWNER - BASE : OWNER - BASE + len(bodies['qualified'])], 'changed original bytes'
    )
    return bodies


def record(root):
    import plausible
    from rompath import rom_path

    root = Path(root)
    path = root / SOURCE
    require(
        list((root / 'src').rglob(path.name)) == [path]
        and qualifier_offsets(path.read_text(), root, root, plausible.include_closure(root, path)),
        'expected the qualified payload view in the original writer',
    )
    compile_bodies(root, Path(rom_path(root)).read_bytes())
    return (
        '* allowlisted volatile BLDALPHA rows: 080D96F0 event 0 passes the 0800D61C task and six '
        'command bytes to 0800DB0C. C614 supplies its live 320-byte payload. Each reached row in [0,160) '
        'writes EVA then EVB at offsets 0 and 1, with a same-byte access before each store. '
        'Qualified/ordinary/reversed agbcc bodies '
        + '/'.join(digest for _, digest in SHAPES.values())
        + '. DEC0 copies 160 halfwords to the inactive bank via CpuSet. The manager duplicates row 0 at '
        'row 160 and stages it in LCD shadow 0300098C. VBlank uploads the shadow; repeated HBlank DMA '
        'reads one halfword from bank +2 onward, destination reload at BLDALPHA 04000052 (A2600001). '
        'Requires successful allocation, a live task, disjoint banks, an available channel and exclusive '
        'updates. Event 1 frees the task; retirement must preclude bank reuse before DMA stops.'
    )


def report_body(report, root):
    from rompath import rom_path

    length, digest = SHAPES['qualified']
    with open(rom_path(root), 'rb') as stream:
        stream.seek(OWNER - BASE)
        body = stream.read(length)
    lines = report.splitlines()
    return sha256(body).hexdigest() == digest and all(
        lines.count(line) == 1
        for line in (
            '* verification: `elf-symbol-thumb-frame-buffer-calls-v2`',
            f'* ROM bytes: `{body.hex()}` ({length} bytes)',
            f'* compiled : `{body.hex()}`',
            f'**MATCH - byte identical** - {length}/{length} bytes',
        )
    )
