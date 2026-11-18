"""The original USA BG2/BG3 scanline producer and its packed DMA row view."""

import argparse
from hashlib import sha256
from pathlib import Path
import re
import struct

from sdk_cpuset_halfword import TOKEN, base_header

BASE = 0x08000000
OWNER = 0x0800D3BC
BIOS = 0x08141864
SOURCE = 'src/0800D3BC.c'
HEADER = 'include/ffta.h'
TOKENS = '4c2f8881de8ddea9b53e09a58ae65836c53e472f3c40b5ac65e3572c13fd57b1'
SHAPES = {
    'qualified': (606, 'd86e7f5b4e4f12dbbb07249dd0658ba2911afb6ecdd7181c4260ee6de848e679', (0x6E, 0x190)),
    'ordinary': (524, '5ff93d91e91c30765a4bc6b40818db71ac35d4ac28fefc901a6bbeeb41c4a967', (0x6E, 0x166)),
    'reversed': (606, '2c9e45d80e17b7beee2cd54bcd892743dbb74d9a820a46668e7b5ffa9641c4c7', (0x6E, 0x190)),
    'aligned': (390, '9b512e36ebda7adef527e9b1ffa6b605f21fb0fd07f85b357f57db0175430503', (0x68, 0x11E)),
}
VIEW = re.compile(r'\b(?P<qual>volatile)\s+AffineLine\s*\*\s*out\b')
MEMBERS = re.compile(
    r'(typedef\s+struct\s*\{\s*)((?:[us]16\s+\w+\s*;\s*){8})(\}\s*)'
    r'(?P<packed>__attribute__\s*\(\(\s*packed\s*\)\))\s*AffineLine\s*;'
)
CONSTRUCTORS = (
    (0x0800CF08, 0x0800CFC8, '13c547cbf222c46889eab5c25f01e560574a54e7b6140424394edbf4bcc1adb0'),
    (0x0800CFC8, 0x0800D090, '10526b37b1922937dbb24d101581a4809d6c43b3f0783bd290dc03a025d41dfc'),
    (0x0800D090, 0x0800D168, '81128855f07b0c756a1aae32da0afce48e9c6be50df038267d0131930478901e'),
    (0x0800D168, 0x0800D23C, 'f120f2a15a430ffedfdd863f12ccac26ba4730e0f903bd1553036a9ea91ff837'),
)


def require(condition, message):
    if not condition:
        raise ValueError('BG affine rows: ' + message)


def scanline_pipeline(rom):
    """Authenticate the common task, IRQ, double-bank and shadow DMA path."""
    import scheduler_zero_descriptor as install
    from affine_oam_slot import PROVIDER as irq_code
    from window_scanline import PROVIDER as manager_code

    shared = (
        0x0800C3CC,
        0x0800C4B4,
        0x080009AC,
        0x080008E0,
        0x0800C668,
        0x0800C614,
        0x0814186C,
        0x0814224C,
        0x08142250,
    )
    irq = (0x080000C0, 0x080000FC, 0x08000290, 0x080004B0)
    pipeline = [item for item in manager_code if item[0] in shared]
    pipeline += [item for item in irq_code if item[0] in irq]
    require(len(pipeline) == len(shared) + len(irq), 'incomplete manager or IRQ evidence')
    for start, end, digest in (
        *pipeline,
        *install.BOOT,
        (0x0800A640, 0x0800A652, 'de05784b78f2014a09b57caf7a381fad80d0c3c25ea76f41487b35be1fc3e2ba'),
        (0x08000718, 0x08000788, 'd85bea0cb703a088cb7a895f53f83fe423cb279c46c69070b3a3b7db0f4c37bf'),
        (0x08000D08, 0x08000D48, '54d51125dd563be37ebe2c475fac7d6a696b2ff11eec134bf713edda6f7d5610'),
        (0x08000D90, 0x08000DBC, '3947c7599d6035d4b151ebd384b6cc2357bd378eab3daa26d614ec07d05c5874'),
        (0x08003A08, 0x08003A3E, 'b255abdb822d7b27b6d4b6d2e5b9e02d502c67a040a84236dbd202abc060f616'),
        (0x0800C64C, 0x0800C656, '1108ceb7999c22d8b9e9f54599a465caaa0a1b9e57750f9ad908339105cc3f72'),
        (0x08002768, 0x080027B8, '6e9dc4c6a9f37a50fb532938d3c1d4e5bd2eb08e1e45744ec654f057d08dd718'),
        (install.IMAGE, install.IMAGE + 176, install.IMAGE_SHA256),
    ):
        require(
            sha256(rom[start - BASE : end - BASE]).hexdigest() == digest, f'changed native provider at {start:08X}'
        )
    for address, values in (
        (install.POINTER, (install.DESTINATION | 1,)),
        (0x08000388, (0x030008D0, 0x0814942C)),
        (0x08149434, (0x080004B1,)),
        (0x0836D480, (0x040000B0, 0x040000BC, 0x040000C8, 0x040000D4)),
        (0x0836D470, (0x040000B0, 0x040000BC, 0x040000C8, 0x040000D4)),
    ):
        require(
            rom[address - BASE : address - BASE + 4 * len(values)] == struct.pack('<' + 'I' * len(values), *values),
            'changed boot or hardware table',
        )


def provider(rom):
    import bios_bg_affine_set_profile as bios

    scanline_pipeline(rom)
    for start, end, digest in CONSTRUCTORS:
        require(sha256(rom[start - BASE : end - BASE]).hexdigest() == digest, f'changed constructor at {start:08X}')
    require(rom[0x149820:0x149828] == struct.pack('<2I', 0x04000020, 0x04000030), 'changed BG target table')
    require(rom[BIOS - BASE : BIOS - BASE + 4] == bios.WRAPPER, 'changed BgAffineSet wrapper')


def source_offset(text, header):
    import plausible

    if not base_header(
        header, ('AffineLine', 'AffineWave', 'BgAffineSrc', 'BgAffineDst', 'func_0800D3BC', 'func_08141864')
    ) or any(marker in text for marker in ('\\', '??', '%:', '\0')):
        return None
    code = plausible.strip_comments_and_strings_keep_strings(text)
    if not re.match(r'\A\s*#\s*include[ \t]+"ffta\.h"[ \t]*\n', code):
        return None
    view = VIEW.search(code)
    if view and sha256(' '.join(TOKEN.findall(code)).encode()).hexdigest() == TOKENS:
        return view.start('qual')
    return None


def qualifier_offsets(text, tree, project, closure):
    from rompath import rom_path

    if closure != ({SOURCE, HEADER}, []):
        return set()
    offset = source_offset(text, (Path(tree) / HEADER).read_bytes())
    if offset is None:
        return set()
    rom = Path(rom_path(project)).read_bytes()
    provider(rom)
    length, digest, _ = SHAPES['qualified']
    require(sha256(rom[OWNER - BASE : OWNER - BASE + length]).hexdigest() == digest, 'changed original producer')
    return {offset}


def rewrite(source, kind):
    if kind == 'ordinary':
        found = list(VIEW.finditer(source))
        require(len(found) == 1, 'expected one qualified access view')
        start, end = found[0].span('qual')
        return source[:start] + source[end:]
    found = list(MEMBERS.finditer(source))
    require(len(found) == 1, 'expected one packed 16-byte row')
    if kind == 'aligned':
        start, end = found[0].span('packed')
        return source[:start] + source[end:]
    require(kind == 'reversed', 'unknown compiler control')
    start, end = found[0].span(2)
    declarations = re.findall(r'[us]16\s+\w+\s*;', source[start:end])
    return source[:start] + ' '.join(reversed(declarations)) + source[end:]


def row_accesses(body):
    import match
    from capstone.arm import ARM_REG_R7

    decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
    decoder.detail = True
    return [
        (ins.address - OWNER, ins.mnemonic, ins.operands[1].mem.disp)
        for ins in decoder.disasm(body, OWNER)
        if len(ins.operands) == 2
        and ins.operands[1].type == match.ARM_OP_MEM
        and ins.operands[1].mem.base == ARM_REG_R7
    ]


def check_bodies(bodies):
    require(bodies.keys() == SHAPES.keys(), 'missing compiler control')
    for kind, (length, digest, _) in SHAPES.items():
        body = bodies[kind]
        require((len(body), sha256(body).hexdigest()) == (length, digest), 'changed ' + kind + ' producer')
        step = 2 if kind == 'aligned' else 1
        accesses = []
        for offset in range(0, 16, step):
            offset = offset ^ 14 if kind == 'reversed' else offset
            if kind != 'ordinary':
                accesses.append(('ldrh' if step == 2 else 'ldrb', offset))
            accesses.append(('strh' if step == 2 else 'strb', offset))
        require(
            [(mnemonic, disp) for _, mnemonic, disp in row_accesses(body)] == accesses * 2,
            'changed access widths or named members in base/inside-band arms',
        )
    # In the reversed struct every byte changes member pair but keeps its low
    # or high position. Only bits 6..10 (immediate displacement) may change.
    reversed_body = bytearray(bodies['qualified'])
    for site, _, _ in row_accesses(reversed_body):
        (word,) = struct.unpack_from('<H', reversed_body, site)
        struct.pack_into('<H', reversed_body, site, word ^ (14 << 6))
    require(reversed_body == bodies['reversed'], 'reordering changed an unrelated instruction')


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
        for kind, (length, _, sites) in SHAPES.items():
            _, _, image = match.compile_object(
                runner,
                ws,
                args,
                str(root),
                OWNER,
                SOURCE,
                rewrite=None if kind == 'qualified' else lambda text: rewrite(text, kind),
            )
            match.allocated_text_only(image)
            symbol, offset = match.function_record(image, 'func_0800D3BC', OWNER, True)
            require(
                offset == 0
                and symbol['bind'] == 1
                and symbol['size'] == length
                and image['text'][length:] == (b'\xc0\x46' if length % 4 else b''),
                'changed full ELF extent',
            )
            body, calls, data = match.link_calls(runner, ws, args, image, OWNER, mapping, len(rom), rom)
            require(not data and calls == {OWNER + site: BIOS for site in sites}, 'changed original BIOS bindings')
            bodies[kind] = body
    check_bodies(bodies)
    require(
        bodies['qualified'] == rom[OWNER - BASE : OWNER - BASE + len(bodies['qualified'])], 'changed ROM extent'
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
        'expected the reviewed producer',
    )
    compile_bodies(root, Path(rom_path(root)).read_bytes())
    return (
        '* allowlisted volatile BG affine rows: packed 16-byte BGxPA/PB/PC/PD/X/Y transfer; native '
        'qualified/ordinary/reversed/aligned '
        + '/'.join(value[1] for value in SHAPES.values())
        + '. On invocation of CF08/CFC8/D090/D168 (no known native parent), target 2 or 3, successful task '
        'allocation and installed clear: 0x2B8 live payload and two disjoint 161x16-byte RAM banks. '
        'BgAffineSet reads one aligned 20-byte record (payload +12 or private frame +0) and writes '
        'one aligned 16-byte record (frame +36 or +20); requires returning BIOS ABI and valid inputs. '
        'The producer writes rows 0..159; the manager copies row 0 into row 160 and the register shadow. '
        'VBlank uploads row 0 via the 39-halfword LCD shadow transfer. After bank rotation and DMA setup, '
        'hardware reads eight halfwords per HBlank from bank +16 '
        'with destination reload at BG2PA 04000020 or BG3PA 04000030. Requires an active task, available '
        'channel (control A2600008), exclusive inactive bank and no teardown or reuse during transfer. '
        'Release frees the task before the next VBlank stop; retirement must be synchronized.'
    )


def report_body(report, root):
    from rompath import rom_path

    length, digest, _ = SHAPES['qualified']
    with open(rom_path(root), 'rb') as stream:
        stream.seek(OWNER - BASE)
        body = stream.read(length)
    lines = report.splitlines()
    return sha256(body).hexdigest() == digest and all(
        lines.count(line) == 1
        for line in (
            '* verification: `elf-symbol-thumb-frame-buffer-calls-v1`',
            f'* ROM bytes: `{body.hex()}` ({length} bytes)',
            f'* compiled : `{body.hex()}`',
            '**MATCH - byte identical** - 606/606 bytes',
        )
    )
