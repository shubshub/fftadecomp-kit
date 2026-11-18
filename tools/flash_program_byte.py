"""FLASH512_V130 byte-program unlock, destination write and installed wait callback."""
from hashlib import sha256
from pathlib import Path
import re
import shlex
import struct
from types import SimpleNamespace

from flash_bank_command import BASE, SETUPS, TOOL, source_qualifiers, verify_unit
from rompath import rom_path

OWNER = 0x08141FC8
SOURCE = 'src/08141FC8.c'
NAME = 'func_08141FC8'
WAIT = 'data_0200F368'
VENEER = '_call_via_r3'
QUALIFIED = '71a7dd8636d4b2acb73c53fcab134e35409a1fe69ec4d08ca48984ea4025929a'
STRIPPED = '59ab4e100f643a300ed9fdf8d2d142a172f1ed96e38a40751e121dd943b0978c'
BODY = '''extern u16 (*data_0200F368)(u8 phase, u8 *address, u8 lastData);
u16 func_08141FC8(u8 *source, u8 *destination) {
    *(volatile u8 *)0x0E005555 = 0xAA;
    *(volatile u8 *)0x0E002AAA = 0x55;
    *(volatile u8 *)0x0E005555 = 0xA0;
    *destination = *source;
    return data_0200F368(1, destination, *source);
}'''

# Complete retail implementations and their pools. The three command writes,
# both source loads, callback call site and return conversion are in OWNER.
REGIONS = (
    (OWNER, 0x08142000, QUALIFIED),
    (0x08141D9C, 0x08141EB8, '7f57e5b819ad68428b238d16ae2b061d783df64bc770fcb3f2074807ab168c2e'),  # IdentifyFlash and wait
    (0x0814195C, 0x08141AAC, 'd8421dbc2ecdb5482bd3ef730e59c749074477709ea1d89191d363d040d2431a'),  # IRQ, set/start/stop timer
    (0x08141AAC, 0x08141AEE, 'bf6d58a69aa7ca1b0219e867a6730b59016edfe054f6a16438a0231ab8ad2f79'),  # byte read and RAM installer
    (0x08142000, 0x08142124, 'd2c5c7e7aa5ebc5e91bc799b1e19e69a2c1708e5774a32af96b5e34f9c9f89dd'),  # sector programmer 1
    (0x08142160, 0x0814220C, 'ff87b44a9a488bbef794279cec9d28851f43df370c51e0dfac310b0aa8438142'),  # sector programmer 2
)


def require(ok, message):
    if not ok:
        raise ValueError('flash program byte: ' + message)


def provider(rom):
    import match
    require(len(rom) >= max(SETUPS)-BASE+42 and rom[0x36ce28:0x36ce35] == b'FLASH512_V130',
            'incomplete cartridge image or changed flash unit identity')
    for start, end, digest in REGIONS:
        require(sha256(rom[start-BASE:end-BASE]).hexdigest() == digest, f'changed retail code or pool at 0x{start:08X}')
    require(match.thunk_is_call_via(rom, 0x08142250, 3) and match.thunk_is_call_via(rom, 0x08142248, 1),
            'changed wait or RAM-reader veneer')
    require(struct.unpack_from('<4I', rom, 0x36ce38) == SETUPS, 'changed flash setup list')
    for p, sector, times, ident in zip(SETUPS, (0x08142001, 0x08142161, 0x08142161, 0x08142001),
            (0x0836ce70, 0x0836cf20, 0x0836cf08, 0x0836ce70), (0xd4bf, 0x1b32, 0x1cc2, 0)):
        p -= BASE
        require(struct.unpack_from('<I', rom, p)[0] == sector and
                struct.unpack_from('<4I', rom, p+12) == (0x08141e31, times, 0x10000, 0x1000) and
                struct.unpack_from('<2H', rom, p+28) == (12, 16) and
                struct.unpack_from('<H', rom, p+40)[0] == ident and
                struct.unpack_from('<3H', rom, times-BASE+6) == (10, 65469, 194),
                'changed sector geometry, programmer, wait callback, phase-1 timer or cartridge ID')


def qualifier_offsets(text, tree, project, closure):
    offsets = source_qualifiers(text, tree, closure, OWNER, SOURCE, BODY)
    if offsets:
        verify_unit(project, OWNER, 56)
        provider(Path(rom_path(project)).read_bytes())
    return offsets


def compile_bodies(root):
    """Link both native diagnostic builds. Only the normal verifier awards ROM credit."""
    import library_units
    import match
    root = Path(root)
    require(match.parse_data_symbols(match.data_snapshot(root)).get(WAIT) == 0x0200F368 and
            match.RUNTIME_HELPERS[VENEER] == 0x08142250, 'changed wait pointer or veneer binding')
    tool = library_units.resolve(TOOL)
    args = SimpleNamespace(cc=tool['cc'], flags=tool['flags'], cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                           linker=match.DEFAULT_LD, objcopy=match.DEFAULT_OBJCOPY)
    runner = match.Runner(args.cc, root=str(root), timeout=match.SIGNED_REPLAY_TIMEOUT)
    bodies = []
    with runner.workspace() as workspace:
        q = shlex.quote(workspace)
        for length, digest in ((56, QUALIFIED), (52, STRIPPED)):
            rewrite = None if length == 56 else lambda s: re.sub(r'\bvolatile\b', '', s)
            _, _, original = match.compile_object(runner, workspace, args, root, OWNER, SOURCE, rewrite=rewrite)
            signature = library_units.signature(original, OWNER)
            text, relocs, offset, value, size = signature
            require(original['type'] == 1 and offset == 0 and value == 1 and size == len(text) == length and
                    relocs == ((length-26, 10, VENEER), (length-4, 2, WAIT)),
                    'wrong native function extent or typed relocation sites')
            # GNU ld follows section references from the function. Its unreachable duplicate
            # .rodata does not participate in either diagnostic .text comparison. The saved
            # positive still requires the existing library-unit orphan prerequisite.
            runner.sh(f'{args.linker} -r --gc-sections -e {NAME} {q}/f.o -o {q}/f.gc.o && mv {q}/f.gc.o {q}/f.o')
            retained = match.elf_image(runner.read_binary(f'{workspace}/f.o'))
            match.allocated_text_only(retained)
            require(retained['type'] == 1 and library_units.signature(retained, OWNER) == signature,
                    'section GC changed native function identity or relocations')
            linked = match.link_typed_targets(runner, workspace, args, NAME, OWNER,
                    {VENEER: 0x08142250, WAIT: 0x0200F368}, {WAIT})
            symbol, offset = match.function_record(linked, NAME, OWNER, True)
            match.allocated_text_only(linked)
            require(linked['type'] == 2 and not linked['relocations'] and offset == 0 and
                    symbol['bind'] == 1 and symbol['size'] == len(linked['text']) == length and
                    sha256(linked['text']).hexdigest() == digest, 'changed linked original or qualifier-stripped control')
            bodies.append(linked['text'])
    with open(rom_path(root), 'rb') as file:
        file.seek(OWNER-BASE)
        require(file.read(56) == bodies[0], 'compiled byte programmer differs from ROM')
    return bodies


def record(root):
    import plausible
    root = Path(root)
    path = root/SOURCE
    require(list((root/'src').rglob(path.name)) == [path] and
            len(qualifier_offsets(path.read_text(), root, root, plausible.include_closure(root, path))) == 3,
            'expected three original qualified command stores')
    compile_bodies(root)
    return ('* allowlisted volatile flash byte programming: FLASH512_V130 O1 issues AA@0E005555, 55@0E002AAA, '
            'A0@0E005555, then writes the source byte to the destination. It reloads the source for '
            'the phase-1 wait callback at 0200F368 and returns its low halfword. Both installed sector '
            'programmers call this routine. All four IdentifyFlash setups install 08141E31 as the wait callback. '
            'The linked original and qualifier-stripped controls have SHA-256 ' + QUALIFIED + ' and ' + STRIPPED +
            '. Removing volatile drops the first unlock write.')


def report_body(report, root):
    import library_units
    with open(rom_path(root), 'rb') as file:
        file.seek(OWNER-BASE)
        body = file.read(56)
    lines = report.splitlines()
    return sha256(body).hexdigest() == QUALIFIED and all(lines.count(line) == 1 for line in (
        '* verification: `elf-symbol-thumb-data-v1`', f'{library_units.TOOLCHAIN_LINE}`{TOOL}`',
        f'* compiled : `{body.hex()}`', f'* ROM bytes: `{body.hex()}` (56 bytes)', '**MATCH - byte identical** - 56/56 bytes'))
