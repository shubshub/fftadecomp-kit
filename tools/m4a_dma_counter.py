"""The FFTA m4a VSyncOn mixer's asynchronously accessed DMA counter byte."""
import argparse
from hashlib import sha256
from pathlib import Path
import re
import struct

from sdk_cpuset_halfword import TOKEN, base_header

BASE = 0x08000000
OWNER = 0x081457FC
SOURCE = 'src/081457FC.c'
HEADER = 'include/ffta.h'
MIXER = 0x03007FF0
SYMBOL = 'data_03007FF0'
DMA1_CONTROL = 0x040000C6
LOCK = 0x68736D53

BODY = """
typedef struct { u32 lockStatus; volatile u8 dmaCounter; } SoundMixerState;
extern SoundMixerState *data_03007FF0;
void func_081457FC(void) {
    SoundMixerState *soundInfo = data_03007FF0;
    u32 lockStatus = soundInfo->lockStatus;
    if (lockStatus == 0x68736D53) return;
    *(volatile u16 *)0x040000C6 = 0xB600;
    soundInfo->dmaCounter = 0;
    soundInfo->lockStatus = lockStatus - 10;
}
"""

# The reset vector installs the ARM IRQ handler at 03007FFC. IE & IF bit 0
# selects byte offset 8 of the callback table. The ARM stub dispatches via BX.
# Boot copies that slot from 0814942C+8 to 030008D0+8 and subsequently points
# the IRQ vector at its IWRAM copy of the same position-independent dispatcher.
# The DMA3 helper's index-zero path copies 080000FC..0800025C (including pools).
# m4aSoundInit passes 020084E0 to SoundInit, which stores it at 03007FF0.
# In SoundMain the saved mixer pointer is restored at 08144558; its
# byte at +4 and the frames-per-cycle byte at +11 select the PCM buffer slice.
DEPENDENCIES = (
    (0x08000000, 0x08000004, 'e3de0a6864e3119f5ccb28524e580cd769e44efefd06ba6c0bf7c2807bfd3a16'),
    (0x080000C0, 0x08000140, '5d0590c22c0baa0f16f65a50fc39694fa85bc8e262736dece59be806d95c41f1'),
    (0x0800018C, 0x080001E4, 'c6b6f2a7eebce73fa5c155a570cce755bd6ff847488359e652ba6f579b858c6f'),
    (0x0800023C, 0x0800032E, '0b2aefaa431393570b6fc38b87824950313a7fc711076b487a275eab2ff5a33c'),
    (0x08000388, 0x08000398, '399bd93446b080a94004dd8161d40f292ac4688386b72ab05289db2624707f84'),
    (0x0800058C, 0x080005CC, 'e7dda1ce75b71aace6b92947f718adf007ddff63575616bb7eea953ba84cb95a'),
    (0x080023EC, 0x08002424, '4f73b08adbcfdd8ca79cde107fd6285620d158acc1ec4af6c48c625fc827274a'),
    (0x08002462, 0x0800247C, 'ee04bddba4f24925b582e81669719fbb869144915891ad6632af827642d15633'),
    (0x0814513C, 0x081451B4, '006ed3db573bc9aee356fe171e253024335078859f86b926b586d139fd603f9f'),
    (0x0814553C, 0x08145608, 'e94a015e3d7b691e0c020e05509c3b94b334005bfc67a3c0c5dbed792bab04d7'),
    (0x08144510, 0x08144584, 'd661542ce661382a2c24945ac2921a658f890118b4ed3d54d626057c82c23f63'),
)


def source_offset(text, header):
    import plausible
    if not base_header(header) or any(marker in text for marker in ('\\', '??', '%:', '\0')):
        return None
    code = plausible.strip_comments_and_strings_keep_strings(text)
    include = re.match(r'\A[ \t\n]*#[ \t]*include[ \t]+"ffta\.h"[ \t]*\n', code)
    if not include:
        return None
    tokens = list(TOKEN.finditer(code, include.end()))
    if [token[0] for token in tokens] != TOKEN.findall(BODY):
        return None
    # Only the RAM member. The ordinary MMIO plausibility rule checks the cast.
    return next(token.start() for token in tokens if token[0] == 'volatile')


def word(data, offset):
    return int.from_bytes(data[offset:offset + 4], 'little')


def instructions(data, start):
    from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
    decoded = list(Cs(CS_ARCH_ARM, CS_MODE_THUMB).disasm(bytes(data), start))
    if not decoded or decoded[-1].address + decoded[-1].size != start + len(data):
        raise ValueError('incomplete Thumb instruction stream')
    return [f'{ins.mnemonic} {ins.op_str}' for ins in decoded]


def irq_evidence(rom):
    for start, end, digest in DEPENDENCIES:
        if sha256(rom[start-BASE:end-BASE]).hexdigest() != digest:
            raise ValueError(f'changed IRQ installation, dispatch or PCM mixer path at {start:08X}')
    if word(rom, 0x08149434-BASE) != 0x080004B1 or instructions(
            rom[0x4B0:0x4B8], BASE + 0x4B0) != ['push {r7, lr}', 'mov r7, sp', 'bl #0x8144af0']:
        raise ValueError('VBlank slot 2 must call the mixer interrupt routine')
    # Both PC-relative loads are anchored to the linked addresses below. The
    # lock guard either returns or reaches the byte decrement. On expiration,
    # the second store reloads the very same byte from framesPerDmaCycle.
    if instructions(rom[0x144AF0:0x144B24], 0x08144AF0) != [
            'ldr r0, [pc, #0x298]', 'ldr r0, [r0]', 'ldr r2, [pc, #0x298]',
            'ldr r3, [r0]', 'subs r3, r3, r2', 'cmp r3, #1', 'bhi #0x8144b22',
            'ldrb r1, [r0, #4]', 'subs r1, #1', 'strb r1, [r0, #4]', 'bgt #0x8144b22',
            'ldrb r1, [r0, #0xb]', 'strb r1, [r0, #4]',
            'ldr r2, [pc, #0x18]', 'ldr r1, [r2, #8]', 'lsls r1, r1, #7', 'blo #0x8144b16',
            'ldr r1, [pc, #0x14]', 'str r1, [r2, #8]', 'movs r1, #4', 'lsls r1, r1, #8',
            'strh r1, [r2, #0xa]', 'movs r1, #0xb6', 'lsls r1, r1, #8',
            'strh r1, [r2, #0xa]', 'bx lr'] or \
            (word(rom, 0x144D8C), word(rom, 0x144D90)) != (MIXER, LOCK) or \
            (word(rom, 0x144B24), word(rom, 0x144B28)) != (0x040000BC, 0x84400004):
        raise ValueError('VBlank must conditionally decrement and reload the mixer counter at +4')


def owner_evidence(body, qualified):
    size = 56 if qualified else 52
    pool = size - 12
    code_end = 42 if qualified else 40
    if len(body) != size or body[code_end:pool] != bytes(pool - code_end) or \
            struct.unpack_from('<III', body, pool) != (MIXER, LOCK, DMA1_CONTROL):
        raise ValueError('wrong complete mixer owner, alignment, signature or DMA1CNT_H literal')
    # Check the complete reached stream in both builds. Only the optional LDRB,
    # its alignment and the resulting PC/branch displacements may differ.
    def literal(site, register, slot):
        displacement = OWNER + pool + 4 * slot - ((OWNER + site + 4) & ~3)
        return f'ldr {register}, [pc, #{displacement:#x}]'
    return_site = OWNER + (36 if qualified else 34)
    expected = ['push {r4, lr}', literal(2, 'r0', 0), 'ldr r2, [r0]', 'ldr r3, [r2]',
                literal(8, 'r0', 1), 'cmp r3, r0', f'beq #{return_site:#x}',
                literal(14, 'r1', 2), 'movs r4, #0xb6', 'lsls r4, r4, #8',
                'adds r0, r4, #0', 'strh r0, [r1]']
    if qualified:
        expected.append('ldrb r0, [r2, #4]')
    expected.extend(['movs r0, #0', 'strb r0, [r2, #4]', 'adds r0, r3, #0',
                     'subs r0, #0xa', 'str r0, [r2]', 'pop {r4}', 'pop {r0}', 'bx r0'])
    if instructions(body[:code_end], OWNER) != expected:
        raise ValueError('unexpected mixer/DMA1 access, guard, load-before-store or return')


def bound_object(image, qualified):
    import library_units
    import match
    if image['type'] != 1:
        raise ValueError('expected a relocatable original ELF')
    match.allocated_text_only(image)
    if len(image['relocations']) != 1:
        raise ValueError('expected one original relocation section')
    text, relocations, offset, value, size = library_units.signature(image, OWNER)
    pool = (56 if qualified else 52) - 12
    named = [sym for sym in image['symbols'] if sym['name'] == SYMBOL]
    if (offset, value, size, len(text)) != (0, 1, pool + 12, pool + 12) or \
            relocations != ((pool, 2, SYMBOL),) or word(text, pool) != 0 or len(named) != 1 or \
            any(named[0][key] != expected for key, expected in (
                ('bind', 1), ('type', 0), ('value', 0), ('size', 0), ('section', 0))):
        raise ValueError('expected one zero-addend ABS32 to the undefined mixer pointer')
    body = text[:pool] + struct.pack('<I', MIXER) + text[pool + 4:]
    owner_evidence(body, qualified)
    return body


def strip_member(preprocessed):
    changed, count = re.subn(r'\bvolatile\s+(u8\s+dmaCounter\s*;)', r'\1', preprocessed)
    if count != 1:
        raise ValueError('expected the one preprocessed mixer counter qualifier')
    return changed


def record(root):
    import library_units
    import m4a_track_switch
    import match
    import plausible
    from rompath import rom_path
    root = Path(root)
    sources = list((root / 'src').rglob(f'{OWNER:08X}.c'))
    if sources != [root / SOURCE] or plausible.include_closure(root, sources[0]) != ({SOURCE, HEADER}, []) or \
            source_offset(sources[0].read_text(), (root / HEADER).read_bytes()) is None:
        raise ValueError('expected the original VSyncOn source and only the base header')
    if plausible.check_file(sources[0]) or plausible.check_file(root / HEADER):
        raise ValueError('VSyncOn source or header failed plausibility, including the DMA1 MMIO qualifier')
    mapping = match.parse_data_symbols((root / 'config/data_symbols.json').read_bytes())
    if mapping.get(SYMBOL) != MIXER or list(mapping.values()).count(MIXER) != 1:
        raise ValueError('expected the unique indexed mixer pointer at 03007FF0')
    unit = library_units.containing(library_units.load(root), OWNER)
    start, end, digest = m4a_track_switch.UNIT
    if unit is None or (unit.start, unit.end, unit.toolchain, unit.proof) != (
            start, end, m4a_track_switch.TOOLCHAIN, 0x08146264) or unit.row['identity'] != [
            {'address': f'0x{start:08X}', 'size': end-start, 'sha256': digest}]:
        raise ValueError('expected the identified m4a old_agbcc music library')
    rom = Path(rom_path(root)).read_bytes()
    irq_evidence(rom)
    tool = library_units.resolve(unit.toolchain)
    args = argparse.Namespace(cc=tool['cc'], flags=tool['flags'], cpp=match.DEFAULT_CPP,
                              assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY)
    runner = match.Runner(args.cc, 'Ubuntu', match.DEFAULT_WSL_PATH, root=str(root),
                          timeout=match.SIGNED_REPLAY_TIMEOUT)
    with runner.workspace() as workspace:
        _, _, original = match.compile_object(runner, workspace, args, str(root), OWNER, SOURCE)
        _, _, stripped = match.compile_object(runner, workspace, args, str(root), OWNER, SOURCE,
                                              rewrite=strip_member)
    body = bound_object(original, True)
    control = bound_object(stripped, False)
    if body != rom[OWNER-BASE:OWNER-BASE+len(body)]:
        raise ValueError('qualified function differs from the USA ROM')
    return ('* allowlisted volatile mixer counter: `m4a-vblank-dma-counter-v1` '
            'mixer pointer `03007FF0` byte `+4`; VBlank slot `08149434`, '
            'decrement/reload stores `08144B02/08144B08`; foreground load/reset '
            '`08145814/08145818`; DMA1 halfword store `08145812`; '
            f'old_agbcc qualified/stripped bodies `{sha256(body).hexdigest()}` / '
            f'`{sha256(control).hexdigest()}`')


def report_body(report, root):
    """Bind both reported hex strings and the verdict to the entire checked owner."""
    from rompath import rom_path
    with open(rom_path(root), 'rb') as stream:
        stream.seek(OWNER - BASE)
        body = stream.read(56)
    lines = report.splitlines()
    return len(body) == 56 and all(lines.count(line) == 1 for line in (
        f'* ROM bytes: `{body.hex()}` (56 bytes)', f'* compiled : `{body.hex()}`',
        '**MATCH - byte identical** - 56/56 bytes'))
