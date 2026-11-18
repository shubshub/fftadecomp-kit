"""The two immediate fixed-source DMA3 transactions in the USA boot video initializer."""
import re
import struct
from hashlib import sha256
from pathlib import Path

from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
from immediate_dma_fill import BASE, SCHEMA, encoded, require, source_tokens
from sdk_cpuset_halfword import base_header

OWNER = 0x08003410
OAM_INIT = 0x08003454
BOOT = 0x08002710
SAD = 0x040000D4
CONTROL_FLOW = "two fixed-source DMA3 register sequences with control readbacks around the original OAM initializer"
STRIPPED_SHA = "e2db32ff6005c50df197b565be03dceef8dacf08e10abfae3515421a99f57d9f"

DECLARATIONS = """
#include "ffta.h"
typedef struct { const void *source; void *destination; u32 control; } DmaRegisters;
extern volatile DmaRegisters data_040000D4;
void func_08003454(void);
void func_08003410(void) { u16 zero;
"""
TRANSFER = """
{ u16 *source = &zero;
  *source = 0;
  data_040000D4.source = source;
  data_040000D4.destination = (void *)DEST;
  data_040000D4.control = COUNT;
  (void)data_040000D4.control; }
"""


def source_qualifier(text, header):
    from plausible import strip_comments_and_strings
    require(base_header(header, ("DmaRegisters", "func_08003410", "func_08003454", "data_040000D4")),
            "unexpected boot initializer header")
    require(not any(item in text for item in ("\\", "??", "%:", "\0")), "unreviewed source spelling")
    expected = (DECLARATIONS + TRANSFER.replace("DEST", "0x06000000").replace("COUNT", "0x8100C000") +
                "func_08003454();" + TRANSFER.replace("DEST", "0x05000000").replace("COUNT", "0x81000200") + "}")
    require(source_tokens(text) == source_tokens(expected), "unreviewed DMA3 register source or transfer size")
    qualifier = re.search(r"\bvolatile\b", strip_comments_and_strings(text))
    before = text[:qualifier.start()].splitlines()
    require(len(before) >= 2 and "plausible:" in before[-2], "undocumented DMA3 qualifier")
    return qualifier.start()


def qualifier(text, tree, project, closure, objects):
    from rompath import rom_path
    require(closure == ({"src/08003410.c", "include/ffta.h"}, []), "unexpected boot source closure")
    require(int(str(objects["data_040000D4"]), 0) == SAD, "wrong DMA3 SAD object")
    rom = Path(rom_path(project)).read_bytes()
    native(rom[OWNER-BASE:OAM_INIT-BASE], qualified=True)
    return source_qualifier(text, (Path(tree) / "include/ffta.h").read_bytes())


def strip_qualifier(preprocessed):
    changed, count = re.subn(r"\bvolatile(?=\s+DmaRegisters\s+data_040000D4\b)", "", preprocessed)
    require(count == 1, "one qualified DMA3 object is required")
    return changed


def required_bindings(qualified):
    return dict(calls=[[0x1A if qualified else 0x18, "func_08003454"]], functions=[], switches=[],
                data=[[0x38 if qualified else 0x34, "data_040000D4", 0]])


def native(body, *, qualified):
    code_size = 56 if qualified else 52
    require(len(body) == code_size + 12 and
            struct.unpack_from("<3I", body, code_size) == (SAD, 0x8100C000, 0x81000200),
            "wrong fixed DMA3 block or transfer controls")
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    decoder.detail = True
    pools = {OWNER + code_size + 4*i: label for i, label in enumerate(("SAD", "vram", "palette"))}
    instructions = list(decoder.disasm(body[:code_size], OWNER))
    expected = ["push {r4, r5, lr}", "sub sp, #4", "mov r0, sp", "movs r5, #0", "strh r5, [r0]",
                "ldr r4, SAD", "str r0, [r4]", "movs r0, #0xc0", "lsls r0, r0, #0x13",
                "str r0, [r4, #4]", "ldr r0, vram", "str r0, [r4, #8]"]
    readback = ["ldr r0, [r4, #8]"] if qualified else []
    expected += readback + [f"bl #0x{OAM_INIT:x}", "mov r0, sp", "strh r5, [r0]", "str r0, [r4]",
                            "movs r0, #0xa0", "lsls r0, r0, #0x13", "str r0, [r4, #4]",
                            "ldr r0, palette", "str r0, [r4, #8]"] + readback
    expected += ["add sp, #4", "pop {r4, r5}", "pop {r0}", "bx r0"]
    require(sum(item.size for item in instructions) == code_size and
            [encoded(item, {}, pools) for item in instructions] == expected,
            "boot frame, local initialization, DMA stores/readbacks or OAM call changed")


def check_stripped(body, original_bindings):
    require(original_bindings == required_bindings(False), "wrong stripped DMA3 source or OAM relocation")
    native(body, qualified=False)
    require(sha256(body).hexdigest() == STRIPPED_SHA, "stripped boot DMA3 body changed")


def oam_initializer(body):
    registers = ("r2", "r1", "r1", "r4", "r2", "r1", "r1", "r1",
                 "r2", "r1", "r1", "r1", "r2", "r1", "r1", "r4")
    expected = ["push {r4, lr}", "movs r0, #0xe0", "lsls r0, r0, #0x13", "movs r1, #0x80",
                "lsls r1, r1, #2", "adds r2, r1, #0", "movs r1, #0", "movs r3, #0x80",
                "lsls r3, r3, #1", "adds r4, r3, #0", "movs r3, #0x1f"]
    for reg in registers:
        expected += [f"strh {reg}, [r0]", "adds r0, #2"]
    expected += ["subs r3, #1", "cmp r3, #0", "bge #0x800346a", "pop {r4}", "pop {r0}", "bx r0"]
    ins = list(Cs(CS_ARCH_ARM, CS_MODE_THUMB).disasm(body, OAM_INIT))
    require(len(body) == 98 and all(i.size == 2 for i in ins) and
            [i.mnemonic + " " + i.op_str for i in ins] == expected,
            "intervening OAM initializer or preservation of SP/R4/R5 changed")


def prove(data, address, rom, mapping, index, objects, *, ins, edges, calls, refinement, bindings):
    from inert_spin_profile import validate_span
    from match import parse_data_symbols
    from owner_graph_profile import partition
    require(address == OWNER and data == rom[OWNER-BASE:OAM_INIT-BASE], "wrong original boot owner")
    native(data, qualified=True)
    require(len(ins) == 27 and calls == {OWNER+0x1A: OAM_INIT} and
            bindings == required_bindings(True) and parse_data_symbols(objects).get("data_040000D4") == SAD,
            "wrong original DMA3 or OAM bindings")
    oam = rom[OAM_INIT-BASE:OAM_INIT-BASE+98]
    validate_span(oam, OAM_INIT, rom, mapping, index)
    oam_initializer(oam)
    boot = rom[BOOT-BASE:BOOT-BASE+88]
    validate_span(boot, BOOT, rom, mapping, index)
    # Both cookie outcomes in the original boot routine converge on the adjacent
    # installer/initializer calls. The instructions after the latter overwrite R0.
    require(sha256(boot).hexdigest() == "62739675d57afabfbf8dd443b4d34ecf7fd5306e6b347e52bcec135403f74261",
            "boot caller changed")
    return dict(schema=SCHEMA, instructions=len(ins), calls=bindings["calls"], runtime_calls=[],
        partition=partition(data, address, refinement, ins, {}), dma_fill=dict(
            known_boot_call=0x08002746, return_type="void", register_block=SAD,
            transfers=[[0x06000000, 0x06018000, 0x8100C000], [0x05000000, 0x05000400, 0x81000200]],
            source="zero at entry SP minus 16, initialized by STRH independently for each DMA",
            mode="immediate DMA3, 16-bit fixed source, incrementing destination, no repeat or IRQ",
            oam=dict(entry=OAM_INIT, begin=0x07000000, end=0x07000400, matrices=32,
                     preserved=["SP", "R4", "R5"]),
            control_readbacks=[OWNER+0x18, OWNER+0x2E], stripped_bytes=64, stripped_sha256=STRIPPED_SHA,
            premises="Valid aligned hardware-visible stack and disjoint writable video memory. DMA3 must be idle "
                "and exclusively owned. Video timing must permit both transfers and OAM CPU writes. Immediate DMA "
                "must complete before the CPU resumes and reuses its source or releases the frame. The single control readbacks are not completion "
                "polls. Replace SAD before later channel re-enable when the stack source has expired."))
