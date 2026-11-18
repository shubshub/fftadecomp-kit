"""Volatile WINxH fields in two specific USA scanline payload writers (kit #168).

The writers edit heap RAM. The allocator, event-zero callback, bank switch and
HBlank DMA programming establish what that RAM represents. The constructor
does not dominate every possible entry. The record keeps its caller, lifetime,
row-range and noninterference premises, including the unreferenced rectangle.
"""
import argparse
from hashlib import sha256
from pathlib import Path
import re
import struct

from sdk_cpuset_halfword import TOKEN, base_header

BASE = 0x08000000
RECT = 0x080DA968
ELLIPSE = 0x080DA1C4
HEADER = 'include/ffta.h'
ELEMENT = re.compile(
    r'\btypedef\s+struct\s+__attribute__\s*\(\s*\(\s*packed\s*\)\s*\)\s*\{'
    r'\s*(?P<right>volatile)\s+u8\s+right\s*:\s*8\s*;'
    r'\s*(?P<left>volatile)\s+u8\s+left\s*:\s*8\s*;\s*\}\s*WindowLine\s*;')
# The source token fingerprints bind only the two reviewed C programs. This
# prevents extra expression-level reads or an alias that happens to compile
# identically. Body and transfer evidence below are independently required.
SOURCE_TOKENS = {
    RECT: 'e932b2672df436650fe5331575191662cc8a2722dc36591565e2a767a13857cb',
    ELLIPSE: '9cbc279cf9136df898b107ecad1f41c0e2dfa645da10d570a62e4a9d63e0f269',
}
# (complete original, qualifier-stripped body) after binding all Thumb calls.
# Stripping can change the whole frame and register allocation. Both audited
# controls retain their rectangle bounds or their even-diameter/row conditions.
OWNER_SHAPES = {
    RECT: ((166, 'ac85d657e591e6e33da7fbf0754b93a1799205cddb5f1109ff94a396d1ff4a55'),
           (150, 'dc10536a4b99d8817e2f41903ff1bedf56169b4492e19ff7f189dfb405ed8fe0')),
    ELLIPSE: ((272, '850c0ba131a4815366f2d7261a8a5861b7f5ebcf96e3c9c32cb44f9fab928e32'),
              (262, '88843664ee85ce57d3278ca8b1b574436bbca58f189fa68650b1e4bcf151b452')),
}
CALLEES = {RECT: (0x08005BFC, 0x0800C614),
           ELLIPSE: (0x08141870, 0x08141870, 0x080DA074, 0x080D9F60)}

PROVIDER = (
    # Window event constructor and synchronous event-zero dispatch; R2 = task + 0x18.
    (0x080DAB84, 0x080DABB4, 'b569a568f1b0d83745cbb2d4d299cd4fdab8813b99070e59c2342b56a2390e72'),
    (0x08005B6C, 0x08005BA8, 'c6a20896e48a2d20f9a4e9d59b780095f5e082b65619a2a96cee0ebc26e8c475'),
    (0x08005954, 0x08005A22, '4e3fba4f8cb6ee77b2d0251866e2f85338ab5550832ce8fc0807b3835b0c677e'),
    (0x08142250, 0x08142252, '477db9ac7ca5efc12e37f882656b8fe5a363ffeb99b2e565a953d10c3c91ab21'),
    # Event zero selects WIN0H/1H, allocates (320, 2) and writes payload +4. Event 1 frees it.
    (0x080D9C58, 0x080D9CF4, '0d5b68179a3ba9e8ab2970fc5fe616d4d6c6b119a56db0b23ed092b67ab5da90'),
    # Allocate payload +0x20, two aligned 324-byte banks and a one-halfword HBlank channel.
    (0x0800C3CC, 0x0800C4B4, '0de1cf88f1da097ba540acc0061d0f3ef1aa86f0e7ed9b0baa2a4aba876d579d'),
    # Per active slot, convert payload into the inactive bank; copy row zero to row 160;
    (0x0800C4B4, 0x0800C5F4, 'c6d6ae60535de05d825bbee9eee235c75d08b321162757be40dcb5fba421c9a4'),
    # toggle +0x0E, submit bank +2 and the original MMIO destination for repeated HBlank DMA.
    (0x080009AC, 0x08000A48, '44c9d06c56fdb3f8fb450903538f8bbb1ea0760c36a8391607942c3a117a4255'),
    # Stage and program DMAxSAD, DMAxDAD, DMAxCNT from the submitted slot.
    (0x080008E0, 0x080009AC, '08e98c62b17f375f553d9c4d65df8879d9a9e6421c6ea703ccac5df0d4ed9859'),
    # Copy 160 halfwords by CpuSet from the live payload into the bank selected by the manager.
    (0x080DAE70, 0x080DAE7C, 'f44f222de0b95c70408c1b6fccbe8b59b5663c7bba77ef1307da22502df44d6a'),
    (0x0814186C, 0x08141870, '07967ebdc3979cd4fd4de37fd22b3e6de8965b00dae4ac5585577c9709839652'),
    (0x0814224C, 0x0814224E, 'dd9261f0471768edc33bf979649f6297463be423da17c3f881684f5747e163a1'),
    # Close the slot and free its storage; the input task and slot must remain live.
    (0x0800C668, 0x0800C6BE, 'fbe0f1d49d066128ecccdfcf2e652a8c8594b43fbeb0380608af23f8fb7f5059'),
    # Payload getter and scanline-object storage-size guard.
    (0x08005BFC, 0x08005C00, 'f405d9773c7102b97b617a0b190d7c5a83a856a9a19141afc2d18f8882c1fda0'),
    (0x0800C614, 0x0800C628, 'be9c09e26151bf59569681249059d598963aaba6fc3520290ee1ffce08e7da0e'),
)

ELLIPSE_PATH = (
    # Scene creates WIN0H and passes its return immediately to DAD3C with diameter 32.
    (0x080EEC50, 0x080EEC6C, '06aa2a9cce13fee13b5ee325b002adf69684c5818b788e16c0ad5d0eeac6dbe5'),
    # DAD3C forwards the result of the payload accessor unchanged as the fourth argument.
    (0x080DAD3C, 0x080DAD74, 'bdb05d21087365cce5c36c1649119f95d277704b37eaf3fe82b00d0bcc9f13c2'),
    # The nested geometry writers reject out-of-range rows before each pair of byte stores.
    (0x080D9F60, 0x080DA074, 'ebc7f7c2f9ec6b910932b086e1be2cbffcbea48f47f2cc62e050c3756b539d3c'),
    (0x080DA074, 0x080DA1C4, '587185662bf2bbd2e60269989268113844ac1d399ce7c9583b2baff340cb9997'),
    # BIOS signed division used by the owner and fixed-point ellipse.
    (0x08141870, 0x08141874, '8e93a1720c694e06005b83e2dbaf36a800649ab8948fc4e15efa39309f4c5ce6'),
    # BIOS square-root wrapper used by the ellipse.
    (0x08141898, 0x0814189C, 'de4a71d0d630472b454682d19fb9bad740be092c8543ac383d1aab54f492cff4'),
)


def uses_element(root, address):
    import plausible
    path = Path(root) / 'src' / f'{address:08X}.c'
    return path.is_file() and bool(ELEMENT.search(plausible.strip_comments_and_strings(path.read_text())))


def source_offsets(text, header, address):
    import plausible
    if address not in SOURCE_TOKENS or not base_header(header, (
            'WindowLine', 'DrawingState', 'Object0800C614', 'draw_ellipse',
            f'func_{address:08X}', *(f'func_{target:08X}' for target in CALLEES[address]))):
        return set()
    if any(marker in text for marker in ('\\', '??', '%:', '\0')):
        return set()
    code = plausible.strip_comments_and_strings_keep_strings(text)
    if not re.match(r'\A\s*#\s*include[ \t]+"ffta\.h"[ \t]*\n', code):
        return set()
    tokens = ' '.join(TOKEN.findall(code)).encode('utf-8')
    element = ELEMENT.search(code)
    if not element or sha256(tokens).hexdigest() != SOURCE_TOKENS[address]:
        return set()
    return {element.start('right'), element.start('left')}


def provider_evidence(rom, address):
    if address not in OWNER_SHAPES:
        raise ValueError('unreviewed window scanline consumer')
    import scheduler_zero_descriptor as installed
    # The scheduler and scanline allocator both call table[0] to clear freshly
    # allocated RAM, including the bank selector at +0x0E. The installed
    # routine clears 1000 bytes here: 32-byte header + 320 + 324 + 324.
    # Its aligned STM loop consumes four bytes per iteration, then its byte
    # tail consumes the remainder. Physical installation and allocation are
    # explicit preconditions; this does not raise the generic zero proof limit.
    zero_image = (*installed.BOOT,
                  (0x08002768, 0x080027B8, '6e9dc4c6a9f37a50fb532938d3c1d4e5bd2eb08e1e45744ec654f057d08dd718'),
                  (installed.IMAGE, installed.IMAGE + 176, installed.IMAGE_SHA256))
    for start, end, digest in zero_image + PROVIDER + (ELLIPSE_PATH if address == ELLIPSE else ()):
        if sha256(rom[start-BASE:end-BASE]).hexdigest() != digest:
            raise ValueError(f'changed window provider, bank transfer or caller at {start:08X}')
    # The event loads this exact pair through its pool; destination index must
    # be 0 or 1. DMA control combines 0x22600001 with 0xA2000000 (one
    # halfword, source increment, destination reload, repeat, HBlank, enable).
    words = ((installed.POINTER, (installed.DESTINATION | 1,)),
             (0x08149B2C, (0x04000040, 0x04000042)),
             (0x080D9CC4, (0x08149B2C, 0x080DAE71)),
             (0x080DABB0, (0x080D9C59,)),
             (0x0836D470, (0x040000B0, 0x040000BC, 0x040000C8, 0x040000D4)))
    for start, values in words:
        if rom[start-BASE:start-BASE+4*len(values)] != struct.pack('<'+'I'*len(values), *values):
            raise ValueError(f'changed WINxH pipeline literal at {start:08X}')


def qualifier_offsets(text, tree, project, address, closure):
    from rompath import rom_path
    name = f'src/{address:08X}.c'
    if closure != ({name, HEADER}, []):
        return set()
    offsets = source_offsets(text, (Path(tree) / HEADER).read_bytes(), address)
    if offsets:
        rom = Path(rom_path(project)).read_bytes()
        provider_evidence(rom, address)
        length, digest = OWNER_SHAPES[address][0]
        if sha256(rom[address-BASE:address-BASE+length]).hexdigest() != digest:
            raise ValueError('changed original window scanline owner')
    return offsets


def rewrite_element(source, swap=False):
    elements = list(ELEMENT.finditer(source))
    if len(elements) != 1:
        raise ValueError('one original preprocessed WindowLine declaration required')
    m = elements[0]
    # Swap member names only inside the pinned declaration; uses stay identical.
    element = re.sub(r'\b(right|left)\b', lambda t: {'right': 'left', 'left': 'right'}[t[0]], m[0]) \
        if swap else re.sub(r'\bvolatile\s+', '', m[0])
    return source[:m.start()] + element + source[m.end():]


def check_bodies(address, qualified, stripped, swapped):
    from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
    # The paired original reads immediately precede same-member writes. On the
    # ellipse's even-diameter path the first two reads form the unsigned right
    # > left test; the next right read supplies the decrement. The last right
    # read is the dead insertion read, immediately before that byte's write.
    actual = ((0x84, 0x86, 0x88, 0x8A) if address == RECT else
              (0xB4, 0xB6, 0xB8, 0xBA, 0xE2, 0xE4, 0xEA, 0xEE, 0xF0))
    control = (('strb', 'strb') if address == RECT else
               ('strb', 'strb', 'ldrb', 'ldrb', 'strb'))
    for data, shape in zip((qualified, stripped), OWNER_SHAPES[address]):
        if (len(data), sha256(data).hexdigest()) != shape:
            raise ValueError('changed complete qualified or qualifier-stripped window writer')
    def byte_accesses(body):
        return [(i.address-address, i.mnemonic) for i in Cs(CS_ARCH_ARM, CS_MODE_THUMB).disasm(body, address)
                if i.mnemonic in ('ldrb', 'strb')]
    real = byte_accesses(qualified)
    if tuple(site for site, _ in real) != actual or tuple(op for _, op in byte_accesses(stripped)) != control:
        raise ValueError('window field access sequence changed')
    # For immediate Thumb-1 LDRB/STRB the low byte bit 6 changes offset 0
    # to 1 or vice versa. Every live/dead access follows its named field,
    # including the reads supplying the comparison and the decremented value.
    expected = bytearray(qualified)
    for site in actual:
        expected[site] ^= 0x40
    if swapped != expected:
        raise ValueError('an access did not follow its named byte field')


def compile_bodies(root, address, rom):
    import match
    source = f'src/{address:08X}.c'
    mapping = match.mapping_snapshot(root)
    args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, flags=match.DEFAULT_FLAGS,
                              assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD)
    runner = match.Runner(args.cc, 'Ubuntu', match.DEFAULT_WSL_PATH, root=str(root),
                          timeout=match.SIGNED_REPLAY_TIMEOUT)
    bodies = []
    with runner.workspace() as workspace:
        for rewrite in (None, rewrite_element, lambda s: rewrite_element(s, swap=True)):
            _, _, image = match.compile_object(runner, workspace, args, str(root), address, source, rewrite=rewrite)
            match.allocated_text_only(image)
            body, calls, data = match.link_calls(runner, workspace, args, image, address, mapping, len(rom), rom)
            if data or tuple(calls[k] for k in sorted(calls)) != CALLEES[address]:
                raise ValueError('unexpected external reference in window writer')
            bodies.append(body)
    check_bodies(address, *bodies)
    return bodies


def record(root, address):
    import plausible
    from rompath import rom_path
    root = Path(root)
    source = f'src/{address:08X}.c'
    path = root / source
    if list((root / 'src').rglob(path.name)) != [path] or not qualifier_offsets(
            path.read_text(), root, root, address, plausible.include_closure(root, path)):
        raise ValueError('expected the reviewed WindowLine declaration, writer and ROM provider')
    rom = Path(rom_path(root)).read_bytes()
    bodies = compile_bodies(root, address, rom)
    size = len(bodies[0])
    if bodies[0] != rom[address-BASE:address-BASE+size]:
        raise ValueError('complete linked window writer differs from the ROM')
    condition = ('caller unknown; input must be a live window task created with bank 0 or 1; '
                 'signed clipping bounds every accessed row to [0,160)' if address == RECT else
                 '080EEC58 creates bank 0; 080EEC68/080DAD6A deliver its payload, diameter 32; '
                 'entry requires signed y <= 160 for the uncapped first loop')
    hashes = '/'.join(sha256(body).hexdigest() for body in bodies)
    return ('* allowlisted volatile scanline: `window-row-bytes-v1` original/stripped/swapped '
            f'`{hashes}`; {condition}; assumes initialized live task, intact installed clear routine, successful allocation, exclusive 320-byte '
            'payload, stable values between compare/re-read and no concurrent mutation or teardown; '
            '160 two-byte WIN0H/WIN1H rows copied into alternating 324-byte banks before HBlank DMA')


def report_body(report, root, address):
    from rompath import rom_path
    length = OWNER_SHAPES[address][0][0]
    with open(rom_path(root), 'rb') as stream:
        stream.seek(address-BASE)
        body = stream.read(length)
    lines = report.splitlines()
    return len(body) == length and all(lines.count(line) == 1 for line in (
        '* verification: `elf-symbol-thumb-frame-calls-v1`',
        f'* ROM bytes: `{body.hex()}` ({length} bytes)', f'* compiled : `{body.hex()}`',
        f'**MATCH - byte identical** - {length}/{length} bytes'))
