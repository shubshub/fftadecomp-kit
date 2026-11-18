"""FLASH512_V130 SwitchFlashBank's ordered byte writes on the cartridge backup bus."""
from hashlib import sha256
from pathlib import Path
import re
import struct
from types import SimpleNamespace

from sdk_cpuset_halfword import TOKEN, base_header

BASE = 0x08000000
OWNER = 0x0814189C
SOURCE = 'src/0814189C.c'
HEADER = 'include/ffta.h'
BUS = 0x0E000000
PORT1 = BUS + 0x5555
PORT2 = BUS + 0x2AAA
TOOL = 'agbcc-O1-v1'
QUALIFIED = '767e511b2235e2114eb4064def581ecc5f3b0d969b2e0127ad0729f4f6eb5d61'
STRIPPED = 'b6ea54117e7710f5641ff4732b89d169639e2b6353cabeefa3ec9739cf6e7f46'
BODY = '''void func_0814189C(u8 bank) {
    *(volatile u8 *)0x0E005555 = 0xAA;
    *(volatile u8 *)0x0E002AAA = 0x55;
    *(volatile u8 *)0x0E005555 = 0xB0;
    *(volatile u8 *)0x0E000000 = bank;
}'''
# The three sector access paths load the installed FlashType, test its 128-KiB
# size, and pass (u8)(sector >> 4) to SwitchFlashBank only on equality.
CALLERS = ((0x08141B14, 0x08141B4C, 0x08141B68, '2331fe5ffacadf9902f72781d1c54f036a30592de4775b1dc3d12d2209f657eb'),
           (0x08141BE0, 0x08141C14, 0x08141C30, 'e27629809423e590595c5e5d905a1257352f8de09e905d00e17a7b8c2577143e'),
           (0x08141C78, 0x08141CA0, 0x08141CC0, '236b6424f26b0f21b8cbdc0ed4d92b6dee4520d3eea2aa6c992e68e67bf1e523'))
SETUPS = (0x0836CEB4, 0x0836CF64, 0x0836CF38, 0x0836CE88)


def require(ok, message):
    if not ok:
        raise ValueError('flash bank command: ' + message)


def provider(rom):
    def word(address):
        return struct.unpack_from('<I', rom, address-BASE)[0]

    for start, end, pool, digest in CALLERS:
        require(sha256(rom[start-BASE:end-BASE]).hexdigest() == digest and word(pool) == 0x0200F370,
                'sector caller, size guard or FlashType pointer changed')
    require(sha256(rom[0x141d9c:0x141e30]).hexdigest() == '5218400579dc03503815bc8f3c234f22266b5fce05471be1f041e293d4edbb36',
            'IdentifyFlash setup lookup or installer changed')
    require(struct.unpack_from('<4I', rom, 0x36ce38) == SETUPS and
            [word(p+20) for p in SETUPS] == [0x10000]*4 and
            [struct.unpack_from('<H', rom, p-BASE+40)[0] for p in SETUPS] == [0xd4bf, 0x1b32, 0x1cc2, 0],
            'named flash IDs, capacities or fallback changed')
    require(sha256(rom[OWNER-BASE:OWNER-BASE+36]).hexdigest() == QUALIFIED, 'original command width, value, order or address changed')


def qualifier_offsets(text, tree, project, closure):
    import library_units
    import plausible
    from rompath import rom_path
    if closure != ({SOURCE, HEADER}, []) or any(marker in text for marker in ('\\', '??', '%:', '\0')):
        return set()
    if not base_header((Path(tree) / HEADER).read_bytes(), ('func_0814189C',)):
        return set()
    clean = plausible.strip_comments_and_strings_keep_strings(text)
    include = re.match(r'\A[ \t\n]*#[ \t]*include[ \t]+"ffta\.h"[ \t]*\n', clean)
    if include is None:
        return set()
    tokens = list(TOKEN.finditer(clean, include.end()))
    if [t[0] for t in tokens] != TOKEN.findall(BODY):
        return set()
    unit = library_units.containing(library_units.load(project), OWNER, OWNER+36)
    require(unit is not None and (unit.name, unit.start, unit.end, unit.toolchain, unit.proof) ==
            ('agb_flash FLASH512_V130', OWNER, 0x0814220C, TOOL, 0x0814195C) and
            unit.row['identity'] == [{'address': '0x0836CE28', 'ascii': 'FLASH512_V130'}], 'wrong library unit or build configuration')
    provider(Path(rom_path(project)).read_bytes())
    return {t.start() for t in tokens if t[0] == 'volatile'}


def compile_bodies(root):
    import library_units
    import match
    from rompath import rom_path
    root = Path(root)
    tool = library_units.resolve(TOOL)
    args = SimpleNamespace(cc=tool['cc'], flags=tool['flags'], cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                           linker=match.DEFAULT_LD, objcopy=match.DEFAULT_OBJCOPY)
    runner = match.Runner(args.cc, root=str(root), timeout=match.SIGNED_REPLAY_TIMEOUT)
    bodies = []
    with runner.workspace() as workspace:
        for length, digest, rewrite in ((36, QUALIFIED, None), (28, STRIPPED, lambda s: re.sub(r'\bvolatile\b', '', s))):
            _, _, image = match.compile_object(runner, workspace, args, root, OWNER, SOURCE, rewrite=rewrite)
            match.allocated_text_only(image)
            symbol, offset = match.function_record(image, 'func_0814189C', OWNER, True)
            require(image['type'] == 1 and not image['relocations'] and offset == 0 and
                    symbol['bind'] == 1 and symbol['size'] == len(image['text']) == length and
                    sha256(image['text']).hexdigest() == digest, 'changed complete O1 original or qualifier-stripped control')
            bodies.append(image['text'])
    with open(rom_path(root), 'rb') as file:
        file.seek(OWNER-BASE)
        require(file.read(36) == bodies[0], 'compiled command differs from original ROM')
    return bodies


def record(root):
    import plausible
    root = Path(root)
    path = root/SOURCE
    require(list((root/'src').rglob(path.name)) == [path] and
            len(qualifier_offsets(path.read_text(), root, root, plausible.include_closure(root, path))) == 4,
            'expected four original qualified flash stores')
    compile_bodies(root)
    return ('* allowlisted volatile flash bank command: FLASH512_V130 O1 issues AA@0E005555, 55@0E002AAA, '
            'B0@0E005555, low byte of bank@0E000000 in order. The original and qualifier-stripped ET_REL '
            'bodies have SHA-256 ' + QUALIFIED + ' and ' + STRIPPED + '. Removing volatile drops the first unlock write. '
            'The three indexed sector callers require a 128-KiB FlashType. IdentifyFlash installs a 64-KiB '
            'descriptor for all three cartridge IDs and its fallback; those callers skip the bank command there.')


def report_body(report, root):
    import library_units
    from rompath import rom_path
    with open(rom_path(root), 'rb') as file:
        file.seek(OWNER-BASE)
        body = file.read(36)
    lines = report.splitlines()
    return sha256(body).hexdigest() == QUALIFIED and all(lines.count(line) == 1 for line in (
        '* verification: `elf-symbol-cfg-leaf-v2`', f'{library_units.TOOLCHAIN_LINE}`{TOOL}`',
        f'* compiled : `{body.hex()}`', f'* ROM bytes: `{body.hex()}` (36 bytes)', '**MATCH - byte identical** - 36/36 bytes'))
