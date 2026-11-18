"""The SDK CpuFill32 temporary in 0804BF78's two-pixel tile loops (kit issue 164)."""
import argparse
from hashlib import sha256
from pathlib import Path
import re
import struct

from bios_cpuset_fill_profile import ADDRESS as CPUSET, WRAPPER
from sdk_cpuset_halfword import HEADER, TOKEN, base_header

BASE = 0x08000000
OWNER = 0x0804BF78
SIZE = 204
SOURCE = 'src/0804BF78.c'
SOURCE_TOKENS = '8fd733d8f8c9580b8d41cf86fe348b0d95e40f80af6849216ab56c711ffc056a'
ORIGINAL = '5ed20bb60e8d49fe5e700f3826b20e93a6c5ad08baa906ea215cd4bcde819397'
QUALIFIER = re.compile(r'\bvolatile\s+(u32\s+fill\b)')
CALLS = {0x0804BFCE: CPUSET, 0x0804BFE4: CPUSET}
COPY, FILL = 0x04000001, 0x05000001


def require(condition, message):
    if not condition:
        raise ValueError('tile CpuFill32: ' + message)


def source_offset(text, header):
    import plausible
    if any(marker in text for marker in ('\\', '??', '%:', '\0')) or not base_header(
            header, ('func_0804BF78', 'func_0814186C', 'input', 'fill')):
        return None
    code = plausible.strip_comments_and_strings_keep_strings(text)
    if not re.match(r'\A\s*#\s*include[ \t]+"ffta\.h"[ \t]*\n', code):
        return None
    if sha256(' '.join(TOKEN.findall(code)).encode()).hexdigest() != SOURCE_TOKENS:
        return None
    return QUALIFIER.search(code).start()


def original(rom):
    body = rom[OWNER - BASE:OWNER - BASE + SIZE]
    require(sha256(body).hexdigest() == ORIGINAL, 'changed original tile editor')
    require(rom[CPUSET - BASE:CPUSET - BASE + 4] == WRAPPER, 'changed CpuSet wrapper')
    require(struct.unpack_from('<II', body, SIZE - 8) == (COPY, FILL), 'expected two single-word controls')
    return body


def qualifier_offsets(text, tree, project, closure):
    from rompath import rom_path
    if closure != ({SOURCE, HEADER}, []):
        return set()
    offset = source_offset(text, (Path(tree) / HEADER).read_bytes())
    if offset is None:
        return set()
    original(Path(rom_path(project)).read_bytes())
    return {offset}


def compare_words(qualified, ordinary):
    # The only different instructions are two uses of each disjoint private
    # word: the copy destination and its load, then the fill store and source.
    # The AND with the shifted 4bpp mask and both external pointers stay exact.
    expected = bytearray(qualified)
    for pc, before, after in ((0x0804BFCA, 0xA901, 0x4669),   # R1 = SP+4 / SP
                              (0x0804BFD8, 0x9801, 0x9800),   # R0 = [SP+4] / [SP]
                              (0x0804BFDC, 0x9000, 0x9001),   # [SP] / [SP+4] = R0
                              (0x0804BFDE, 0x4668, 0xA801)):  # R0 = SP / SP+4
        offset = pc - OWNER
        require(struct.unpack_from('<H', qualified, offset)[0] == before, 'unexpected private word use')
        struct.pack_into('<H', expected, offset, after)
    require(ordinary == expected, 'qualifier erasure changed more than the two private word locations')


def record(root):
    import match
    import plausible
    from rompath import rom_path
    root = Path(root)
    path = root / SOURCE
    require(list((root / 'src').rglob(path.name)) == [path] and
            qualifier_offsets(path.read_text(), root, root, plausible.include_closure(root, path)),
            'expected the single SDK fill temporary and the original owner')
    rom = Path(rom_path(root)).read_bytes()
    args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, flags=match.DEFAULT_FLAGS,
                              assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD)
    runner = match.Runner(args.cc, root=str(root), timeout=match.SIGNED_REPLAY_TIMEOUT)
    mapping = match.mapping_snapshot(root)
    with runner.workspace() as workspace:
        bodies = []
        for rewrite in (None, lambda text: QUALIFIER.sub(r'\1', text, count=1)):
            _, _, obj = match.compile_object(runner, workspace, args, str(root), OWNER, SOURCE, rewrite=rewrite)
            match.allocated_text_only(obj)
            symbol, offset = match.function_record(obj, 'func_0804BF78', OWNER, True)
            require(offset == 0 and symbol['bind'] == 1 and symbol['size'] == len(obj['text']) == SIZE,
                    'wrong complete ELF extent')
            body, calls, data = match.link_calls(runner, workspace, args, obj, OWNER, mapping, len(rom), rom)
            require(calls == CALLS and not data, 'expected only the copy and fill CpuSet calls')
            bodies.append(body)
    require(bodies[0] == original(rom), 'qualified body differs from original')
    compare_words(*bodies)
    return ('* allowlisted volatile SDK CpuFill32: 0804BFCE copies one tile word to entry SP-48. '
            '0804BFD8..0804BFDC loads it, clears the selected nibble and initializes the distinct '
            'word at entry SP-52. 0804BFE4 synchronously fills one external word from that address '
            'under the stated CpuSet premises. Removing only the qualifier swaps those two private '
            'words and preserves every other instruction. The fifth ABI argument supplies height. The caller '
            'must supply an aligned, live tile array disjoint from the frame, covering accessed words '
            '(at most index 264) and all formed pointers (a final unused row advance can form index '
            '512, which may be one-past). '
            'No incoming caller is established. Qualified/ordinary SHA-256 '
            + '/'.join(sha256(body).hexdigest() for body in bodies) + '.')


def report_body(report, root):
    from rompath import rom_path
    body = original(Path(rom_path(root)).read_bytes())
    lines = report.splitlines()
    return all(lines.count(line) == 1 for line in (
        '* verification: `elf-symbol-thumb-frame-buffer-calls-v1`',
        f'* ROM bytes: `{body.hex()}` ({SIZE} bytes)',
        f'* compiled : `{body.hex()}`',
        f'**MATCH - byte identical** - {SIZE}/{SIZE} bytes',
    )) and any(line.startswith('* buffer BIOS manifest: ') for line in lines)
