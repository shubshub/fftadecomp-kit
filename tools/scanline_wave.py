"""Validate the original scanline wave's packed DMA samples and bank provenance."""
import argparse
from hashlib import sha256
from pathlib import Path
import re
import struct

from sdk_cpuset_halfword import TOKEN, base_header

BASE = 0x08000000
OWNER = 0x0800C720
SAMPLE = 0x08007A4C
SOURCE = 'src/0800C720.c'
HEADER = 'include/ffta.h'
QUALIFIED = (226, '0fe51799cea4acfdf1c371e39345d01aff0a407ae300e101ef5af42e69da8df3')
STRIPPED = (206, '7c19b665f4153e79ec23f90eb99ccb8bf5140dbf225ad2c0c68ac4ddd7aa805a')
SOURCE_TOKENS = 'a42ff1321f42f581f08d1abe9332a94590bc9ee99aa7b2207762a3a69467cbb5'
ELEMENT = re.compile(r'\btypedef\s+struct\s+__attribute__\s*\(\(\s*packed\s*\)\)\s*\{'
                     r'\s*(?P<qual>volatile)\s+s16\s+value\s*;\s*\}\s*ScanlineValue\s*;')

# The constructor copies the six callbacks and both three-entry u16 tables.
# Its mode selects a 28/56/112-byte payload and 2/4/8-byte rows. The first
# three wrappers place 1/2/4 interleaved halfwords in the manager's bank.
PROVIDERS = (
    (0x0800CC8C, 0x0800CE08, '3a4f66e26915a587a2addb9f65e53c4c4fe473060cad33ff4337bd18b2c64e05'),
    (0x0800DDB0, 0x0800DE14, 'c44dd3542c47edf44fa110e8deac0a270159ba46391418169560003ba8ece81d'),
    (0x081443FC, 0x0814445E, 'aa822d873bad381a62e3c3e07b06003a41beea59bc3edc791f7e316eb08b7ebb'),
    (0x0800C628, 0x0800C64C, 'd203051ca714409914caa0a6a4c5fe2ad714781a843b470b6438a31d54277d55'),
    (SAMPLE, 0x08007A60, 'a3061421a198238073e66a8241975b55ea2ebc4c83d64c14437abc16d96d79c4'),
    (0x08149568, 0x08149768, '9287394fa9384eeaaa175244a8cb0a9af4b0ff78d0bb0f58869173d342410d30'),
)


def require(condition, message):
    if not condition:
        raise ValueError('scanline wave: ' + message)


def provider(rom):
    import scheduler_zero_descriptor as install
    from window_scanline import PROVIDER
    shared = {a: (a, e, h) for a, e, h in PROVIDER}
    # Allocator, bank update, DMA submission/programming, teardown, getter,
    # and the R2/R3 interwork veneers used by the installer and dispatch.
    pipeline = [shared[a] for a in (0x0800C3CC, 0x0800C4B4, 0x080009AC, 0x080008E0,
                                    0x0800C668, 0x0800C614, 0x0814186C, 0x0814224C, 0x08142250)]
    for start, end, digest in (*PROVIDERS, *pipeline, *install.BOOT,
            (0x08002768, 0x080027B8, '6e9dc4c6a9f37a50fb532938d3c1d4e5bd2eb08e1e45744ec654f057d08dd718'),
            (install.IMAGE, install.IMAGE + 176, install.IMAGE_SHA256)):
        require(sha256(rom[start-BASE:end-BASE]).hexdigest() == digest,
                f'changed original provider at {start:08X}')
    tables = ((0x081497E8, '<6I6H', (0x0800DDB1, 0x0800DDBD, 0x0800DDDD,
                                      0x0800DE15, 0x0800DE21, 0x0800DE41, 28, 56, 112, 2, 4, 8)),
              (install.POINTER, '<I', (install.DESTINATION | 1,)),
              (0x0836D470, '<4I', (0x040000B0, 0x040000BC, 0x040000C8, 0x040000D4)))
    for start, fmt, values in tables:
        require(rom[start-BASE:start-BASE+struct.calcsize(fmt)] == struct.pack(fmt, *values),
                f'changed callback, width or hardware table at {start:08X}')


def source_offset(text, header):
    import plausible
    if not base_header(header, ('ScanlineValue', 'ScanlineEffect', 'func_0800C720', 'func_08007A4C')):
        return None
    if any(marker in text for marker in ('\\', '??', '%:', '\0')):
        return None
    code = plausible.strip_comments_and_strings_keep_strings(text)
    if not re.match(r'\A\s*#\s*include[ \t]+"ffta\.h"[ \t]*\n', code):
        return None
    member = ELEMENT.search(code)
    if member and sha256(' '.join(TOKEN.findall(code)).encode()).hexdigest() == SOURCE_TOKENS:
        return member.start('qual')
    return None


def qualifier_offsets(text, tree, project, closure):
    from rompath import rom_path
    if closure != ({SOURCE, HEADER}, []):
        return set()
    offset = source_offset(text, (Path(tree)/HEADER).read_bytes())
    if offset is None:
        return set()
    rom = Path(rom_path(project)).read_bytes()
    provider(rom)
    require(sha256(rom[OWNER-BASE:OWNER-BASE+QUALIFIED[0]]).hexdigest() == QUALIFIED[1],
            'changed original scanline writer')
    return {offset}


def strip_member(text):
    matches = list(ELEMENT.finditer(text))
    require(len(matches) == 1, 'expected one packed signed halfword qualification')
    start, end = matches[0].span('qual')
    return text[:start] + text[end:]


def check_body(body, shape):
    from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
    require((len(body), sha256(body).hexdigest()) == shape, 'changed complete compiled writer')
    qualified = shape == QUALIFIED
    # At every site R4 is the current row pointer. The low and high byte
    # stores survive stripping. Each qualified store reads its own byte first.
    accesses = [(i.address-OWNER, i.mnemonic, i.op_str.partition(', ')[2])
                for i in Cs(CS_ARCH_ARM, CS_MODE_THUMB).disasm(body, OWNER)
                if '[r4' in i.op_str]
    offsets = (0x3E,0x40,0x42,0x46,0x92,0x94,0x98,0x9A,0xBE,0xC0,0xC2,0xC4) if qualified else (
               0x3E,0x42,0x86,0x8A,0xAE,0xB0)
    ops = ([('ldrb','[r4]'), ('strb','[r4]'), ('ldrb','[r4, #1]'), ('strb','[r4, #1]')]
           if qualified else [('strb','[r4]'), ('strb','[r4, #1]')]) * 3
    require(accesses == [(site, *op) for site, op in zip(offsets, ops)], 'changed sample width or row alias')


def object_contract(image, shape):
    import match
    match.allocated_text_only(image)
    require(image['type'] == 1, 'expected original ET_REL object')
    symbol, offset = match.function_record(image, 'func_0800C720', OWNER, True)
    require(offset == 0 and symbol['bind'] == 1 and symbol['size'] == shape[0]
            and image['text'][shape[0]:] == bytes.fromhex('c046'),
            'expected one complete function and its alignment')
    require(len(image['relocations']) == 1, 'expected one call relocation section')
    rel = image['relocations'][0]
    section = image['sections'][rel]
    require(section[1] == 9 and section[7] == image['text_index'] and section[5] == 8
            and section[9] == 8, 'expected one original .rel.text entry')
    site, info = struct.unpack('<II', image['section_data'][rel])
    target = image['symbol_tables'][section[6]][info >> 8]
    require(site == (0x74 if shape == QUALIFIED else 0x70) and info & 255 == 10
            and image['text'][site:site+4] == bytes.fromhex('fff7feff')
            and target['name'] == 'func_08007A4C' and target['bind'] == 1
            and target['type'] == target['section'] == target['value'] == target['size'] == 0,
            'expected the original undefined sine symbol and unapplied Thumb BL')


def compile_bodies(root, rom):
    import match
    args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, flags=match.DEFAULT_FLAGS,
                              assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD)
    runner = match.Runner(args.cc, root=str(root), timeout=match.SIGNED_REPLAY_TIMEOUT)
    mapping = match.mapping_snapshot(root)
    bodies = []
    with runner.workspace() as workspace:
        for rewrite, shape in ((None, QUALIFIED), (strip_member, STRIPPED)):
            obj, text, image = match.compile_object(runner, workspace, args, str(root), OWNER, SOURCE, rewrite=rewrite)
            object_contract(image, shape)
            body, calls, data = match.link_calls(runner, workspace, args, image, OWNER, mapping, len(rom), rom)
            require(not data and tuple(calls.values()) == (SAMPLE,), 'unexpected relocations or sine call')
            check_body(body, shape)
            bodies.append(body)
    require(bodies[0] == rom[OWNER-BASE:OWNER-BASE+len(bodies[0])], 'linked writer differs from original')
    return bodies


def record(root):
    import plausible
    from rompath import rom_path
    root = Path(root)
    path = root / SOURCE
    require(list((root/'src').rglob(path.name)) == [path] and qualifier_offsets(
        path.read_text(), root, root, plausible.include_closure(root, path)), 'reviewed writer and header required')
    compile_bodies(root, Path(rom_path(root)).read_bytes())
    return ('* allowlisted volatile scanline wave: packed signed 16-bit sample; original/stripped '
            f'`{QUALIFIED[1]}/{STRIPPED[1]}`; six same-byte insertion reads in the three row loops. '
            'Conditional on invocation of 0800CC8C (no known caller), bank 0 and kind 0..2, successful allocation '
            'and installed clear, live disjoint effect descriptors and inactive bank, preserved row bounds and no '
            'concurrent writes or teardown. Initialized first/last 0/159; general visible-row contract first <= 160, '
            'last < 160 (last < 255 for byte-loop termination). Strides 2/4/8 with aligned lane offsets 0..stride-2. '
            'When the manager updates the task, row 0 is duplicated to 160 and repeated HBlank DMA reads bank + stride; '
            'requires an available DMA channel and a valid caller-supplied hardware destination for the full transfer.')


def report_body(report, root):
    from rompath import rom_path
    with open(rom_path(root), 'rb') as rom:
        rom.seek(OWNER-BASE)
        body = rom.read(QUALIFIED[0])
    lines = report.splitlines()
    return sha256(body).hexdigest() == QUALIFIED[1] and all(lines.count(line) == 1 for line in (
        '* verification: `elf-symbol-thumb-frame-calls-v1`', f'* ROM bytes: `{body.hex()}` ({len(body)} bytes)',
        f'* compiled : `{body.hex()}`', f'**MATCH - byte identical** - {len(body)}/{len(body)} bytes'))
