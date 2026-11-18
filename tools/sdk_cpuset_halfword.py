"""The initialized halfword that the 0813FB7C CpuFill16 idiom exposes to CpuSet."""
import re

OWNER = 0x0813FB7C
SIZE = 0x34
SOURCE = 'src/0813FB7C.c'
HEADER = 'include/ffta.h'
CONTROL = 0x01000010
TOKEN = re.compile(r'[A-Za-z_]\w*|0[xX][0-9A-Fa-f]+|[0-9]+|<<|\S', re.ASCII)
BODY = """
extern void func_0814186C(const void *source, void *destination, u32 control);
void func_0813FB7C(void *destination, u8 color) {
    u16 pattern = (color << 12) | (color << 8) | (color << 4) | color;
    volatile u16 fill = pattern;
    func_0814186C((const void *)&fill, destination, 0x01000010);
}
"""


def base_header(header, reserved_names=('func_0814186C', 'func_0813FB7C')):
    """Only the base typedefs, passive struct declarations and other prototypes."""
    import plausible
    text = header.decode('utf-8')
    if any(marker in text for marker in ('\\', '??', '%:', '\0')):
        return False
    code = plausible.strip_comments_and_strings_keep_strings(text)
    guard = re.fullmatch(r'\s*#ifndef[ \t]+FFTA_H[ \t]*\n\s*#define[ \t]+FFTA_H[ \t]*\n'
                         r'(.*?)^#[ \t]*endif\s*', code, re.S | re.M | re.ASCII)
    if not guard:
        return False
    declarations = ' '.join(TOKEN.findall(guard[1]))
    types = ' '.join(f'typedef {sign} {kind} {name} ;' for kind, bits in (
        ('char', 8), ('short', 16), ('int', 32)) for sign, name in (
            ('unsigned', f'u{bits}'), ('signed', f's{bits}')))
    if not declarations.startswith(types):
        return False
    if any(re.search(r'\b' + re.escape(name) + r'\b', declarations) for name in reserved_names):
        return False
    # The remainder cannot introduce macros, attributes, initializers, code,
    # aliases of the base types, or declarations of the two bound functions.
    type_name = r'(?:[us](?:8|16|32)|[A-Z][A-Za-z0-9_]*)'
    name = r'(?:\* )?[a-z][A-Za-z0-9_]*(?: \[ (?:0x[0-9A-Fa-f]+|[0-9]+) \])?'
    field = fr'{type_name} {name}(?: , {name})* ; '
    structure = fr'typedef struct \{{ (?:{field})+\}} [A-Z][A-Za-z0-9_]* ;'
    param = fr'{type_name} {name}'
    prototype = fr'(?:void|{type_name}) func_[0-9A-F]{{8}} \( (?:void|{param}(?: , {param})*) \) ;'
    return re.fullmatch(fr'(?: (?:{structure}|{prototype}))*', declarations[len(types):]) is not None


def source_offset(text, header):
    import plausible
    if not base_header(header) or any(marker in text for marker in ('\\', '??', '%:', '\0')):
        return None
    source = plausible.strip_comments_and_strings_keep_strings(text)
    include = re.match(r'\A[ \t\n]*#[ \t]*include[ \t]+"ffta\.h"[ \t]*\n', source)
    if not include:
        return None
    tokens = list(TOKEN.finditer(source, include.end()))
    if [token[0] for token in tokens] != TOKEN.findall(BODY):
        return None
    return next(token.start() for token in tokens if token[0] == 'volatile')


def native_evidence(data, wrapper):
    """Check all reached instructions and all 32 input bits of the stored halfword."""
    from bios_cpuset_fill_profile import ADDRESS, WRAPPER
    from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
    from capstone.arm import ARM_OP_IMM, ARM_OP_MEM, ARM_OP_REG, ARM_REG_PC, ARM_REG_R2
    if len(data) != SIZE or wrapper != WRAPPER:
        raise ValueError('expected the complete palette fill owner and CpuSet wrapper')
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    decoder.detail = True
    # The complete owner ends in one zero alignment halfword and one word.
    code = list(decoder.disasm(data[:-6], OWNER))
    if len(code) < 13 or code[-1].address + code[-1].size != OWNER + SIZE - 6 or \
            data[-6:-4] != b'\0\0' or int.from_bytes(data[-4:], 'little') != CONTROL:
        raise ValueError('incomplete code, control or literal alignment')
    frame = [(i.mnemonic, i.op_str) for i in code]
    if frame[:3] != [('push', '{lr}'), ('sub', 'sp, #4'), ('adds', 'r3, r0, #0')]:
        raise ValueError('expected a private four-byte local and saved external destination')
    # A bit is represented by the set of entry R1 bits whose OR produces it.
    # Starting with all 32 independent bits also checks that the input's high
    # bits are harmless. R3 must preserve the destination throughout.
    origins = tuple(1 << bit for bit in range(32))
    registers = {'r1': origins}
    for ins in code[3:-9]:
        ops = ins.operands
        regs = [ins.reg_name(op.reg) for op in ops if op.type == ARM_OP_REG]
        if len(regs) != 2 or any(reg not in ('r0', 'r1', 'r2') for reg in regs):
            raise ValueError('unexpected access while calculating the pattern')
        dest, source = regs
        value = registers.get(source)
        if value is None:
            raise ValueError('pattern uses an unknown input')
        if ins.mnemonic == 'orrs' and len(ops) == 2 and dest in registers:
            registers[dest] = tuple(x | y for x, y in zip(registers[dest], value))
        elif ins.mnemonic in ('lsls', 'lsrs') and len(ops) == 3 and ops[2].type == ARM_OP_IMM:
            shift = ops[2].imm
            if not 0 < shift <= 32:
                raise ValueError('unsupported pattern shift')
            zeros = (0,) * shift
            registers[dest] = (zeros + value)[:32] if ins.mnemonic == 'lsls' else (value + zeros)[shift:]
        else:
            raise ValueError('expected pure register shifts and ORs')
    expected = [0] * 16
    for shift in (0, 4, 8, 12):
        for bit in range(min(8, 16 - shift)):
            expected[shift + bit] |= origins[bit]
    if registers.get('r0', ())[:16] != tuple(expected):
        raise ValueError('initialized halfword differs from the replicated color')
    # Apart from the save and restore, these are all memory and call effects.
    # The STRH and first call argument name the same still-allocated SP.
    if frame[-9:-7] != [('mov', 'r1, sp'), ('strh', 'r0, [r1]')] or \
            frame[-6:-4] != [('mov', 'r0, sp'), ('adds', 'r1, r3, #0')] or \
            frame[-3:] != [('add', 'sp, #4'), ('pop', '{r0}'), ('bx', 'r0')]:
        raise ValueError('expected one initialized local, caller destination and balanced return')
    load, call = code[-7], code[-4]
    ops = load.operands
    if load.mnemonic != 'ldr' or len(ops) != 2 or ops[0].type != ARM_OP_REG or ops[0].reg != ARM_REG_R2 or \
            ops[1].type != ARM_OP_MEM or ops[1].mem.base != ARM_REG_PC or ops[1].mem.index or \
            ((load.address + 4) & ~3) + ops[1].mem.disp != OWNER + SIZE - 4:
        raise ValueError('expected R2 from the single immutable control word')
    if call.mnemonic != 'bl' or len(call.operands) != 1 or call.operands[0].type != ARM_OP_IMM or \
            call.operands[0].imm != ADDRESS:
        raise ValueError('expected the direct CpuSet call')
    return dict(store=code[-8].address, call=call.address, entry_sp_offset=-8,
                source_bytes=2, local_stores=1, control=CONTROL, halfwords=16)


def selected_offset(text, tree, project):
    from bios_cpuset_fill_profile import ADDRESS, WRAPPER
    from rompath import rom_path
    offset = source_offset(text, (tree / HEADER).read_bytes())
    if offset is None:
        return None
    path = rom_path(project, required=False)
    if not path:
        return None
    with open(path, 'rb') as rom:
        rom.seek(OWNER - 0x08000000)
        data = rom.read(SIZE)
        rom.seek(ADDRESS - 0x08000000)
        native_evidence(data, rom.read(len(WRAPPER)))
    return offset
