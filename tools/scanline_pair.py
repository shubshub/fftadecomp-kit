"""The USA mode-1 scroll task interleaves two 160-halfword planes in its inactive DMA bank."""
import argparse
from hashlib import sha256
from pathlib import Path
import re
import struct

from sdk_cpuset_halfword import TOKEN, base_header
from software_float_profile import ROM_SHA256

BASE = 0x08000000
OWNER = 0x0800DE70
SOURCE = 'src/0800DE70.c'
HEADER = 'include/ffta.h'
QUALIFIED = (78, 'e2580e0e4d24fcb32d30b456b80cb14d9bdbee3df19d3dfca9242dbe53b2897e')
STRIPPED = (64, '971f068cb90a304e94de92094e938823cf1d338a343e5cbfabc5d8e6fefd7117')
SOURCE_TOKENS = '61577863507ddb910a0d5f905e7d75051174d53af088f9054024b8b43e5e674f'
PAIR = re.compile(r'\btypedef\s+struct\s+__attribute__\s*\(\(\s*packed\s*\)\)\s*\{'
                  r'\s*(?P<first>volatile)\s+u16\s+first\s*;\s*(?P<second>volatile)\s+u16\s+second\s*;'
                  r'\s*\}\s*ScanlinePair\s*;')


def require(condition, message):
    if not condition:
        raise ValueError('scanline pair: ' + message)


def provider(rom):
    from bg_affine_rows import scanline_pipeline
    from scanline_dispatch import branch

    require(sha256(rom).hexdigest() == ROM_SHA256, 'expected original USA ROM')
    # Reuse the allocator, installed clear, back-bank, dispatcher and HBlank
    # evidence. The scroll constructor is 0800CE08, independent of the wave
    # constructor at 0800CC8C and the window constructor at 080D9C58.
    scanline_pipeline(rom)
    for site, target in ((0x080EA5C0, 0x080D979C), (0x080D97C4, 0x08005B6C),
                         (0x080D8EDE, 0x0800CE08), (0x0800CE38, 0x081443FC),
                         (0x0800CE44, 0x081443FC), (0x0800CE5A, 0x0800C3CC),
                         (0x0800CE94, 0x0800C614)):
        require(branch(rom, site) == target, f'changed original call at {site:08X}')
    # Phase 0x101 supplies mode 1, BG2, horizontal. 080D979C registers the
    # descriptor, and phase 0x100 of its child indexes the copied target table.
    for address, fmt, values in (
        (0x080EA5BA, '<3H', (0x2001, 0x2102, 0x2200)),
        (0x080EA614, '<I', (0x08398A78,)),
        (0x080D97D0, '<I', (0x080D8E01,)),
        (0x080D8F44, '<2I', (0x08149AD4, 0x08149AF4)),
        (0x08149AD4, '<8I', tuple(range(0x04000010, 0x04000020, 2))),
        (0x08149AF4, '<8I', tuple(range(0x0300094A, 0x0300095A, 2))),
        (0x0800CE70, '<3I', (0x0814980C, 0x08149818, 0x08149806)),
        (0x0814980C, '<3I', (0x0800DE65, OWNER | 1, 0x0800D325)),
        (0x08149818, '<3H', (320, 640, 1280)),
        (0x08149806, '<3H', (2, 4, 8)),
    ):
        require(struct.unpack_from(fmt, rom, address - BASE) == values, f'changed binding at {address:08X}')


def source_offsets(text, header):
    import plausible

    if not base_header(header, ('ScanlinePair', 'ScanlinePlanes', 'func_0800DE70')):
        return set()
    if any(marker in text for marker in ('\\', '??', '%:', '\0')):
        return set()
    code = plausible.strip_comments_and_strings_keep_strings(text)
    if not re.match(r'\A\s*#\s*include[ \t]+"ffta\.h"[ \t]*\n', code):
        return set()
    pair = PAIR.search(code)
    if pair and sha256(' '.join(TOKEN.findall(code)).encode()).hexdigest() == SOURCE_TOKENS:
        return {pair.start('first'), pair.start('second')}
    return set()


def qualifier_offsets(text, tree, project, closure):
    from rompath import rom_path

    if closure != ({SOURCE, HEADER}, []):
        return set()
    offsets = source_offsets(text, (Path(tree) / HEADER).read_bytes())
    if offsets:
        provider(Path(rom_path(project)).read_bytes())
    return offsets


def strip_pair(text):
    pairs = list(PAIR.finditer(text))
    require(len(pairs) == 1, 'expected both packed halfword members')
    pair = pairs[0]
    for field in ('second', 'first'):
        start, end = pair.span(field)
        text = text[:start] + text[end:]
    return text


def check_object(image, shape):
    import match

    match.allocated_text_only(image)
    symbol, offset = match.function_record(image, 'func_0800DE70', OWNER, True)
    require(image['type'] == 1 and not image['relocations'] and offset == 0 and symbol['bind'] == 1
            and symbol['size'] == shape[0], 'expected complete relocation-free global Thumb function')
    body = image['text'][:shape[0]]
    require(image['text'][shape[0]:] == (bytes.fromhex('c046') if shape == QUALIFIED else b'')
            and sha256(body).hexdigest() == shape[1], 'changed complete compiler body or trailing alignment')
    # The pinned bodies have one loop, an unsigned byte counter initially 0,
    # a bottom comparison to 159 and an output stride of 4. Two halfword
    # loads select plane bases spaced 320 bytes apart at index 2*line.
    # Check every memory site in the loop. A low-byte AND and high-byte shift
    # move both input halfwords into their respective little-endian lanes.
    ins = match.verify_leaf_instructions(body, OWNER, True)
    accesses = [(i.mnemonic, i.op_str.partition(', ')[2]) for i in ins
                if i.mnemonic in ('ldrh', 'ldrb', 'strb')]
    qualified = shape == QUALIFIED
    out = 'r4' if qualified else 'r3'
    source = ('r0', 'r3' if qualified else 'r2')
    expected = []
    for lane, base in enumerate(source):
        expected.append(('ldrh', f'[{base}]'))
        for byte in (lane*2, lane*2+1):
            operand = f'[{out}, #{byte}]' if byte else f'[{out}]'
            if qualified:
                expected.append(('ldrb', operand))
            expected.append(('strb', operand))
    require(accesses == expected, 'changed input, row width or same-byte insertion reads')
    if qualified:
        for i, instruction in enumerate(ins):
            if instruction.mnemonic == 'ldrb':
                store = ins[i+1]
                require(store.address == instruction.address+2 and store.mnemonic == 'strb'
                        and store.op_str.partition(', ')[2] == instruction.op_str.partition(', ')[2],
                        'destination read must immediately precede its own byte store')
    # In both compiles the bottom increments the byte index, advances by four,
    # and branches back to the indexed halfword loads while line <= 159.
    counter = 'r5' if qualified else 'r4'
    loop = OWNER + (0x12 if qualified else 0x10)
    require([(i.mnemonic, i.op_str) for i in ins[-9:-3]] == [
        ('adds', f'r0, {counter}, #1'), ('lsls', 'r0, r0, #0x18'),
        ('lsrs', f'{counter}, r0, #0x18'), ('adds', f'{out}, #4'),
        ('cmp', f'{counter}, #0x9f'), ('bls', f'#{loop:#x}')], 'changed row induction or bounds')
    return body


def compile_bodies(root, rom):
    import match

    args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, flags=match.DEFAULT_FLAGS,
                              assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY)
    runner = match.Runner(args.cc, root=str(root), timeout=match.SIGNED_REPLAY_TIMEOUT)
    bodies = []
    with runner.workspace() as workspace:
        for rewrite, shape in ((None, QUALIFIED), (strip_pair, STRIPPED)):
            _, _, image = match.compile_object(runner, workspace, args, str(root), OWNER, SOURCE, rewrite=rewrite)
            bodies.append(check_object(image, shape))
    require(bodies[0] == rom[OWNER-BASE:OWNER-BASE+QUALIFIED[0]], 'qualified object differs from original')
    return bodies


def record(root):
    import plausible
    from rompath import rom_path

    root = Path(root)
    path = root / SOURCE
    require(list((root / 'src').rglob(path.name)) == [path] and qualifier_offsets(
        path.read_text(), root, root, plausible.include_closure(root, path)), 'expected reviewed source and header')
    compile_bodies(root, Path(rom_path(root)).read_bytes())
    return ('* allowlisted volatile scanline pair: mode 1, 0800CE08 table 0814980C[1]; original/stripped '
            f'`{QUALIFIED[1]}/{STRIPPED[1]}`; 160 rows, two input u16 planes at +0/+320, four '
            'little-endian bytes per output row; only the qualified object reads each destination byte before storing. '
            '080EA5C0 passes (1,2,0) to 080D979C; the initialized 080D8E00 task selects BG2HOFS/BG2VOFS '
            '(04000018/0400001A). Requires successful slot/heap allocation and installed clear, '
            'live disjoint 640-byte payload and two 644-byte banks, untouched ownership, no concurrent writes or teardown. '
            '0800C4B4 packs into the inactive bank, duplicates row 0 at 160, swaps banks and, on successful DMA '
            'submission, shadows row 0 and schedules two halfwords per HBlank from bank+4.')


def report_body(report, root):
    from match_evidence import SCHEMA
    from rompath import rom_path

    with open(rom_path(root), 'rb') as rom:
        rom.seek(OWNER-BASE)
        body = rom.read(QUALIFIED[0])
    lines = report.splitlines()
    return sha256(body).hexdigest() == QUALIFIED[1] and all(lines.count(line) == 1 for line in (
        f'* verification: `{SCHEMA}`', f'* ROM bytes: `{body.hex()}` (78 bytes)',
        f'* compiled : `{body.hex()}`', '**MATCH - byte identical** - 78/78 bytes'))
