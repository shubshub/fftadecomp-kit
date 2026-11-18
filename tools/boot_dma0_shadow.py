"""Prove the boot unit's DMA0 register programming, readback and hardware poll."""
import re
import struct
from pathlib import Path

OWNER = 0x08000718
SIZE = 112
SOURCE = 'src/08000718.c'
HEADER = 'include/ffta.h'
DMA = 0x040000B0
LCD = 0x04000008
SHADOW = 0x03000942
DISPLAY = 0x03000940
SAVED = 0x03002BBC
ENABLE = 1 << 31
COUNT = 39
SYMBOLS = dict(data_03000942=SHADOW, data_03002BBC=SAVED,
               g_control_flags_03000940=DISPLAY, data_040000B0=DMA, data_04000008=LCD)

BODY = """
extern u16 data_03000942[];
extern u16 data_03002BBC;
void func_08000718(void) {
    u16 *src = data_03000942;
    {
        volatile u32 *dma = (volatile u32 *)0x040000B0;
        dma[0] = (u32)src;
        dma[1] = 0x04000008;
        dma[2] = 0x80000027;
        (void)dma[2];
    }
    {
        volatile u32 *dma = (volatile u32 *)0x040000B0;
        while (dma[2] & 0x80000000) ;
    }
    data_03002BBC = *(u16 *)0x03000940;
}
"""


def source_offsets(text, header):
    """Only the documented qualifiers on these two local register bindings."""
    import plausible
    from sdk_cpuset_halfword import base_header, TOKEN
    if any(marker in text for marker in ('\\', '??', '%:', '\0')) or not base_header(
            header, reserved_names=('func_08000718',)):
        return set()
    code = plausible.strip_comments_and_strings_keep_strings(text)
    include = re.match(r'\A[ \t\n]*#[ \t]*include[ \t]+"ffta\.h"[ \t]*\n', code)
    if not include:
        return set()
    tokens = list(TOKEN.finditer(code, include.end()))
    if [token[0] for token in tokens] != TOKEN.findall(BODY):
        return set()
    return {token.start() for token in tokens if token[0] == 'volatile' and
            plausible.justified(text, text.count('\n', 0, token.start()) + 1)}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def straight_line(code, data, slots, *, setup=False):
    """Evaluate the address arithmetic, frame slots and observable data accesses.

    Each region starts with unknown scratch registers. A read produces a fresh
    token rather than assuming any particular hardware or RAM value.
    """
    from capstone.arm import ARM_OP_IMM, ARM_OP_MEM, ARM_OP_REG
    regs, events = {}, []

    def scratch(ins, op):
        name = ins.reg_name(op.reg)
        require(op.type == ARM_OP_REG and name in ('r0', 'r1', 'r2', 'r3'), 'unexpected register')
        return name

    for ins in code:
        op = ins.operands
        name = ins.mnemonic
        require(bool(op), 'expected explicit operands in the DMA register flow')
        reg = scratch(ins, op[0])
        if name == 'adds' and len(op) in (2, 3) and op[-1].type == ARM_OP_IMM:
            base = reg if len(op) == 2 else scratch(ins, op[1])
            value = regs.get(base)
            require(type(value) is int, 'address addition requires a known base')
            regs[reg] = (value + op[-1].imm) & 0xffffffff
            continue
        require(name in ('ldr', 'str', 'ldrh', 'strh') and len(op) == 2 and
                op[1].type == ARM_OP_MEM and not op[1].mem.index and not ins.writeback,
                'unexpected instruction in DMA register flow')
        base = ins.reg_name(op[1].mem.base)
        offset = op[1].mem.disp
        if base == 'pc':
            site = ((ins.address + 4) & ~3) + offset - OWNER
            require(name == 'ldr' and site % 4 == 0 and 0 <= site <= SIZE - 4, 'invalid DMA literal')
            regs[reg] = struct.unpack_from('<I', data, site)[0]
        elif base == 'r7':
            require(offset in (0, 4) and name in ('ldr', 'str'), 'invalid private frame access')
            if name == 'ldr':
                require(offset in slots, 'uninitialized private frame word')
                regs[reg] = slots[offset]
            else:
                require(setup and reg in regs, 'only setup may initialize a private frame word')
                slots[offset] = regs[reg]
        else:
            pointer = regs.get(base)
            require(type(pointer) is int, 'unknown address used for a memory event')
            address = (pointer + offset) & 0xffffffff
            if name.startswith('ldr'):
                token = ('read', ins.address)
                regs[reg] = token
                events.append((name, address, token))
            else:
                require(reg in regs, 'unknown store value')
                events.append((name, address, regs[reg]))
    return regs, events


def native_evidence(data):
    """Summarize one arbitrary hardware observation per lap, including perpetual busy."""
    import match
    require(len(data) == SIZE, 'wrong DMA0 function extent')
    code = sorted(match.verify_leaf_instructions(data, OWNER, True), key=lambda ins: ins.address)
    ops = [(ins.mnemonic, ins.op_str) for ins in code]
    require(ops[:3] == [('push', '{r7, lr}'), ('sub', 'sp, #8'), ('mov', 'r7, sp')] and
            ops[-4:] == [('add', 'sp, #8'), ('pop', '{r7}'), ('pop', '{r0}'), ('bx', 'r0')],
            'expected balanced two-slot boot frame')
    # The retry trampoline jumps back across the first literal pool. The
    # branch on clear skips that trampoline and reaches the saved DISPCNT.
    branches = [(index, ins) for index, ins in enumerate(code) if ins.mnemonic.startswith('b')]
    require([ins.mnemonic for _, ins in branches] == ['bne', 'b', 'b', 'bx'],
            'expected one poll decision and its retry and exit')
    (test, busy), (clear_i, clear), (retry_i, retry), _ = branches
    by_address = {ins.address: index for index, ins in enumerate(code)}
    head = by_address.get(retry.operands[0].imm, -1)
    require(3 < head < test - 3 and clear_i == test + 1 and retry_i == test + 2 and
            busy.operands[0].imm == retry.address and clear.address == busy.address + 2 and
            clear.operands[0].imm == code[retry_i + 1].address, 'invalid hardware retry or clear exit')
    slots = {}
    _, start = straight_line(code[3:head], data, slots, setup=True)
    require(len(start) == 4 and start[:3] == [('str', DMA, SHADOW), ('str', DMA + 4, LCD),
            ('str', DMA + 8, ENABLE | COUNT)] and start[3][:2] == ('ldr', DMA + 8),
            'expected DMA0 source, destination, halfword count/enable and immediate readback')
    # No loop-carried registers or frame writes. The shifts isolate exactly bit
    # 31 of the word returned by this iteration's separate 32-bit MMIO read.
    regs, events = straight_line(code[head:test - 3], data, slots)
    require(len(events) == 1 and events[0][:2] == ('ldr', DMA + 8) and
            regs.get('r1') == events[0][2] and ops[test - 3:test] == [
                ('lsrs', 'r2, r1, #0x1f'), ('lsls', 'r0, r2, #0x1f'), ('cmp', 'r0, #0')],
            'poll must branch on enable from one fresh 32-bit DMA0 control read')
    _, copy = straight_line(code[retry_i + 1:-4], data, slots)
    require(len(copy) == 2 and copy[0][:2] == ('ldrh', DISPLAY) and
            copy[1] == ('strh', SAVED, copy[0][2]), 'expected the saved DISPCNT halfword after clear')
    return (start[3][2][1], events[0][2][1], busy.address, code[head].address,
            clear.operands[0].imm)


def rom_body(project):
    from match_evidence import report_rom_path
    with open(report_rom_path(project), 'rb') as rom:
        rom.seek(OWNER - 0x08000000)
        body = rom.read(SIZE)
    require(len(body) == SIZE, 'incomplete boot DMA0 ROM body')
    return body


def selected(text, tree, project, symbols):
    """Bind the admission to this header, these mapped shadows and the live ROM."""
    offsets = source_offsets(text, (tree / HEADER).read_bytes())
    if len(offsets) != 4:
        return set(), None
    for symbol, expected in SYMBOLS.items():
        value = symbols.get(symbol)
        if (int(value, 0) if isinstance(value, str) else value) != expected:
            raise ValueError(f'wrong boot DMA0 identity for {symbol}')
    readback, poll, branch, head, clear = native_evidence(rom_body(project))
    record = (f'* allowlisted volatile MMIO: DMA0 SAD=0x{SHADOW:08X}, DAD=0x{LCD:08X}, '
              f'CNT=0x{ENABLE | COUNT:08X}, control readback at 0x{readback:08X}, '
              f'fresh control read at 0x{poll:08X}, bit 31 set at 0x{branch:08X} retries '
              f'0x{head:08X}, clear enters 0x{clear:08X} for halfword copy '
              f'0x{DISPLAY:08X}->0x{SAVED:08X}, completion is hardware-dependent')
    return offsets, record

def record(root):
    """Repeat the compiler and native checks independently for a saved report."""
    import library_units
    import match
    import plausible
    root = Path(root)
    sources = list((root / 'src').rglob(f'{OWNER:08X}.c'))
    require(sources == [root / SOURCE] and plausible.include_closure(root, sources[0]) == (
            {SOURCE, HEADER}, []), 'expected the unique boot DMA0 source and base header')
    mapping = match.parse_data_symbols((root / 'config/data_symbols.json').read_bytes())
    _, line = selected(sources[0].read_text(encoding='utf-8'), root, root, mapping)
    require(line is not None, 'expected the documented DMA0 set, readback and wait source')
    unit = library_units.containing(library_units.load(root), OWNER, OWNER + SIZE)
    require(unit is not None and unit.toolchain == 'agbcc-O0-v1', 'expected the boot agbcc-O0 unit')
    tool = library_units.resolve(unit.toolchain)
    text, relocations, offset, value, size = library_units.compiled_signature(
        root, OWNER, tool['cc'], tool['flags'])
    expected = ((0x44, 2, 'data_03000942'), (0x68, 2, 'data_03002BBC'))
    require((len(text), offset, value, size) == (SIZE, 0, 1, SIZE) and relocations == expected,
            'expected the complete Thumb symbol with both original IWRAM ABS32 relocations')
    linked = bytearray(text)
    for site, _, name in relocations:
        require(struct.unpack_from('<I', text, site)[0] == 0, 'expected a zero-addend IWRAM binding')
        struct.pack_into('<I', linked, site, mapping[name])
    require(bytes(linked) == rom_body(root), 'complete boot DMA0 compiler output differs from ROM')
    return line


def report_body(report, root):
    """Pin the report to the entire recompiled symbol, including both pools."""
    body = rom_body(root).hex()
    expected = {
        '* verification:': '* verification: `elf-symbol-thumb-frame-data-v1`',
        '* unit toolchain:': '* unit toolchain: `agbcc-O0-v1`',
        '* ROM bytes:': f'* ROM bytes: `{body}` ({SIZE} bytes)',
        '* compiled :': f'* compiled : `{body}`',
        '**MATCH': f'**MATCH - byte identical** - {SIZE}/{SIZE} bytes',
    }
    lines = report.splitlines()
    return all([line for line in lines if line.lstrip().startswith(prefix)] == [entry]
               for prefix, entry in expected.items())
