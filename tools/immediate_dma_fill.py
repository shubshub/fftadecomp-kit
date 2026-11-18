"""Check the USA local-source DMA fill against its complete Thumb control flow."""
import re
import struct
from pathlib import Path

from capstone.arm import ARM_OP_IMM, ARM_OP_MEM, ARM_REG_PC
import owner_graph_profile as graph

SELECTOR = "immediate-dma-stack-fill-v1"
SCHEMA = "elf-symbol-thumb-" + SELECTOR
CONTROL_FLOW = "complete Thumb channel search, returned channel and conditional synchronous local-source DMA fill"
BASE = 0x08000000
WORD = 0x08000DBC
HALFWORD = 0x08000E40
TABLE = 0x0836D470
REGISTERS = (0x040000B0, 0x040000BC, 0x040000C8, 0x040000D4)
LOCKS, STATES = 0x03002BC0, 0x03002BD0
ROOTS = {WORD, HALFWORD}

# The qualifier admission is intentionally confined to this typed, bounded source.
SOURCE = """#include "ffta.h"


typedef struct {
    u8 unknown_00[12];
    u8 state;
    u8 unknown_0d[3];
} DmaChannel;

typedef struct {
    const void *source;
    void *destination;
    u32 control;
} DmaRegisters;

extern u16 data_03002BC0[];
extern DmaChannel data_03002BD0[];
extern DmaRegisters *const data_0836D470[];

static inline s32 available_channel(const void *source, void *destination)
{
    s32 channel;

    if ((u32)destination >= 0x08000000) {
        channel = 3;
    } else {
        channel = 0;
        if ((u32)source >= 0x08000000)
            channel = 1;
    }

    for (; channel < 4; channel++) {
        if (!data_03002BC0[channel] &&
            (data_03002BD0[channel].state == 0 ||
             data_03002BD0[channel].state == 2))
            return channel;
    }
    return -1;
}

s32 func_08000DBC(u32 value, void *destination, u16 count)
{
    s32 channel = available_channel(&value, destination);

    if (channel >= 0) {
        u32 control = 0x85000000 | count;

        volatile DmaRegisters *registers = data_0836D470[channel];

        registers->source = &value;
        registers->destination = destination;
        registers->control = control;
    }
    return channel;
}
"""


def require(condition, message):
    if not condition:
        raise ValueError("immediate DMA fill: " + message)


def channels(rom):
    require(rom[TABLE-BASE:TABLE-BASE+16] == struct.pack("<4I", *REGISTERS),
            "expected the four original channel SAD/DAD/CNT register blocks")
    return list(REGISTERS)


def source_tokens(text):
    import plausible
    from sdk_cpuset_halfword import TOKEN
    return TOKEN.findall(plausible.strip_comments_and_strings_keep_strings(text))


def qualifier(text, tree, project, closure, address, objects):
    """The privileged qualifier belongs only to the three typed MMIO stores."""
    from plausible import strip_comments_and_strings
    from rompath import rom_path
    from sdk_cpuset_halfword import base_header
    name = f"src/{address:08X}.c"
    require(address in ROOTS and closure == ({name, "include/ffta.h"}, []), "unexpected source closure")
    require(base_header((Path(tree) / "include/ffta.h").read_bytes(),
                        ("available_channel", f"func_{address:08X}", "DmaChannel", "DmaRegisters",
                         "data_03002BC0", "data_03002BD0", "data_0836D470")),
            "unexpected base header")
    require(int(str(objects["data_0836D470"]), 0) == TABLE, "wrong register table binding")
    channels(Path(rom_path(project)).read_bytes())
    require(not any(item in text for item in ("\\", "??", "%:", "\0")), "unreviewed source spelling")
    reference = SOURCE
    if address == HALFWORD:
        reference = reference.replace("func_08000DBC(u32 value", "func_08000E40(u16 value").replace(
            "0x85000000", "0x81000000")
    require(source_tokens(text) == source_tokens(reference), "unreviewed source or table-index bound")
    local = re.search(r"\bvolatile\b", strip_comments_and_strings(text))
    preceding = text[:local.start()].splitlines() if local else []
    require(len(preceding) >= 2 and "plausible:" in preceding[-2], "undocumented MMIO qualifier")
    return local.start()


def strip_qualifier(preprocessed):
    changed, count = re.subn(r"\bvolatile(?=\s+DmaRegisters\s*\*\s*registers\b)", "", preprocessed)
    require(count == 1, "exactly one local MMIO qualifier must be present after preprocessing")
    return changed


def encoded(instruction, labels, pools):
    op, args = instruction.mnemonic, instruction.op_str
    if op in ("b", "bhi", "bls", "bgt", "bne", "beq", "ble", "blt"):
        require(len(instruction.operands) == 1 and instruction.operands[0].type == ARM_OP_IMM,
                "unresolved branch")
        return op + " " + labels.get(instruction.operands[0].imm, "?")
    if op == "ldr" and instruction.operands[1].type == ARM_OP_MEM and instruction.operands[1].mem.base == ARM_REG_PC:
        slot = ((instruction.address + 4) & ~3) + instruction.operands[1].mem.disp
        return f"ldr {args.split(',')[0]}, " + pools.get(slot, "?")
    return op + " " + args


def halfword_callers(rom):
    """The four observed game BLs discard R0 on the loop and return paths."""
    from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
    engine = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    calls = []
    for start in (0x0808A894, 0x0808A91C):
        block = rom[start-BASE:start-BASE+40]
        expected = [
            "mov r0, r8", "adds r1, r7, #0", "adds r2, r5, #0", f"bl #0x{HALFWORD:x}",
            "adds r7, #0x40", "mov r0, r8", "adds r1, r6, #0", "adds r2, r5, #0", f"bl #0x{HALFWORD:x}",
            "adds r6, #0x40", "subs r4, #1", "cmp r4, #0", f"bne #0x{start:x}", "pop {r3}",
            "mov r8, r3", "pop {r4, r5, r6, r7}", "pop {r0}", "bx r0",
        ]
        observed = list(engine.disasm(block, start))
        require([op.mnemonic + " " + op.op_str for op in observed] == expected and
                sum(op.size for op in observed) == 40, "caller observes the channel or differs from the audited loop")
        calls.extend(op.address for op in observed if op.mnemonic == "bl")
    return calls


def prove(data, address, rom, mapping, index, objects, *, ins, edges, calls, refinement, bindings):
    import match
    require(address in ROOTS, "wrong owner")
    half = address == HALFWORD
    require((len(data), len(ins)) == ((136, 58) if half else (132, 57)) and not calls, "wrong extent")
    require(data == rom[address-BASE:address-BASE+len(data)], "linked bytes differ from original")
    slots = {0x40: ("limit", 0x07FFFFFF), 0x44: ("locks", LOCKS),
             0x48: ("states", STATES), 0x80: ("registers", TABLE)}
    if half:
        slots = {site + 4: value for site, value in slots.items()}
    for site, (_, expected) in slots.items():
        require(struct.unpack_from("<I", data, site)[0] == expected, "incorrect literal")
    padding = (0x42, 0x82) if half else (0x7E,)
    require(all(data[offset:offset+2] == b"\x00\x00" for offset in padding), "incorrect pool alignment")
    objects_by_name = match.parse_data_symbols(objects)
    named = [[pos, f"data_{value:08X}", 0] for pos, (kind, value) in slots.items() if kind != "limit"]
    require(bindings == dict(calls=[], functions=[], switches=[], data=named)
            and all(objects_by_name.get(name) == slots[pos][1] for pos, name, _ in named),
            "wrong original named data relocations")
    registers = channels(rom)
    starts = {0: "entry", 0x1C: "search", 0x2C: "test", 0x3C: "found", 0x4C: "next",
              0x56: "none", 0x5A: "select", 0x74: "return"}
    if half:
        # One additional STRH setup instruction before the forward branch,
        # then the new halfword of alignment before the first literal pool.
        starts = {offset if offset == 0 else offset + (2 if offset < 0x40 else 4): label
                  for offset, label in starts.items()}
    labels = {address + k: v for k, v in starts.items()}
    pools = {address + k: v for k, (v, _) in slots.items()}
    blocks = {
        "entry": "push {r4, r5, r6, lr}|sub sp, #4|str r0, [sp]|adds r5, r1, #0|"
                 "lsls r2, r2, #0x10|lsrs r6, r2, #0x10|ldr r0, limit|movs r4, #3|"
                 "cmp r5, r0|bhi search|movs r4, #0|cmp sp, r0|bls search|movs r4, #1",
        "search": "cmp r4, #3|bgt none|ldr r2, locks|ldr r1, states|lsls r0, r4, #4|"
                  "adds r3, r0, r1|lsls r0, r4, #1|adds r1, r0, r2",
        "test": "ldrh r0, [r1]|cmp r0, #0|bne next|ldrb r0, [r3, #0xc]|cmp r0, #0|"
                "beq found|cmp r0, #2|bne next",
        "found": "adds r3, r4, #0|b select",
        "next": "adds r3, #0x10|adds r1, #2|adds r4, #1|cmp r4, #3|ble test",
        "none": "movs r3, #1|rsbs r3, r3, #0",
        "select": "cmp r3, #0|blt return|movs r1, #0x85|lsls r1, r1, #0x18|orrs r1, r6|"
                  "ldr r2, registers|lsls r0, r3, #2|adds r0, r0, r2|ldr r0, [r0]|"
                  "mov r2, sp|str r2, [r0]|str r5, [r0, #4]|str r1, [r0, #8]",
        "return": "adds r0, r3, #0|add sp, #4|pop {r4, r5, r6}|pop {r1}|bx r1",
    }
    if half:
        blocks["entry"] = blocks["entry"].replace("str r0, [sp]|adds r5, r1, #0",
                                                   "adds r5, r1, #0|mov r1, sp|strh r0, [r1]")
        blocks["select"] = blocks["select"].replace("movs r1, #0x85", "movs r1, #0x81")
    # Check locations too: concatenating the two code ranges could otherwise
    # hide a fallthrough into literal data. Every decoded halfword is consumed.
    expected = {}
    for start, name in starts.items():
        for idx, text in enumerate(blocks[name].split("|")):
            expected[address + start + 2*idx] = text
    require(set(expected) == set(ins) and
            all(item.size == 2 and encoded(item, labels, pools) == expected[at] for at, item in ins.items()),
            "native channel search, frame, returns or register programming changed")
    proof = dict(schema=SCHEMA, instructions=len(ins), calls=[], runtime_calls=[],
        partition=graph.partition(data, address, refinement, ins, {}), dma_fill=dict(
            address_limit_word=0x44 if half else 0x40, registers=registers, locks=LOCKS, state=(STATES, 16, 12), allowed_states=[0, 2],
            start_channel="destination >= 08000000: 3; otherwise local >= 08000000: 1; otherwise 0",
            return_value="first eligible channel or -1, with no DMA stores on exhaustion",
            source="one initialized 4-byte local at entry SP minus 20, valid until return",
            control=0x85000000, source_fixed=True, destination_increment=True, unit_bytes=4,
            effective_count="channels 0..2 use low 14 bits, zero means 16384; channel 3 uses low 16 bits, zero means 65536",
            premises="Aligned active CPU frame, stable ordinary channel bookkeeping, exclusive DMA registers and "
                     "idle selected channel. A successful fill additionally requires immediate synchronous DMA, "
                     "hardware-visible aligned local and writable destination throughout the entire effective count, "
                     "no address masking/wrap or overlap with the active frame, register blocks or bookkeeping. "
                     "The transfer must consume the local before stack reuse. Later DMA use must replace SAD before re-enabling the channel with an expired source. The CPU does not poll for completion."))
    if half:
        proof["dma_fill"].update(control=0x81000000, unit_bytes=2,
            source="initialized low halfword of a four-byte frame slot at entry SP minus 20; upper halfword unused",
            known_callers_discarding_channel=halfword_callers(rom))
    return proof
