"""Immediate fixed-source DMA fills from a local unit on the plain direct-call path (kit #239).

The walk tests assemble Thumb bodies with the ARM tools (no ROM); the report tests
replay synthetic framed reports; the native tests compile natural C with the fixed
agbcc and `-mthumb-interwork -O2` and run `match.py` on a synthetic tree.
"""
import argparse
import ast
from contextlib import redirect_stdout
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import test_stack_alias_join_lifetime as fixtures

match = fixtures.match
evidence = fixtures.fixtures.evidence
import data_buffer_profile as data_buffer
import report_fixtures
import dma_fill_profile as dma

BASE = fixtures.BASE
ROOT = Path(__file__).resolve().parents[1]
ESCAPE = "unsupported stack-alias use or escape"
BASE_REFUSAL = "not exactly one DMA source register on every path"
WINDOW = "one straight destination and control store after the source store"
READBACK = "control read-back immediately after the enable"
CONTROL = "control is not an exact immediate fixed-source enable"
UNIT = "outside allocated local words"
DESTINATION = "destination is not an exact unit-aligned address"
REGION = "not wholly in a stackless region or in IWRAM below the stack floor"
ISOLATION = "DMA fills require the plain Thumb direct-call path"
POINTER = "source unit is a pointer-bearing local word"

# push {r4, r5, lr}; sub sp, #8: five words below entry SP, two of them allocated.
TEMPLATE = """push {{r4, r5, lr}}
sub sp, #8
{before}
{source}
ldr r4, ={register}
str r0, [r4]
{window}
str r1, [r4, #4]
{tail}
str r2, [r4, #8]
{readback}
{after}
add sp, #8
pop {{r4, r5}}
pop {{r1}}
bx r1
.ltorg"""
DEFAULTS = dict(before="", source="mov r0, sp\nmovs r5, #0\nstrh r5, [r0]", register="0x040000D4",
                window="movs r1, #0xc0\nlsls r1, r1, #0x13", tail="ldr r2, =0x8100C000",
                readback="ldr r0, [r4, #8]", after="")
VRAM_RECORD = {"site": 12, "channel": 3, "source": -20, "frame": 20, "unit": 2,
               "destination_store": 18, "control_store": 22, "readback": 24, "control": 0x8100C000,
               "destination": 0x06000000, "bytes": 0x18000, "region": "vram"}


# The boot code the stack premise is read from, alone in an otherwise empty ROM.
BOOT_ROM = bytearray(0x100)
BOOT_ROM[0:4] = bytes.fromhex("2e0000ea")             # b 0x080000C0
BOOT_ROM[0xC0:0xD8] = bytes.fromhex("1200a0e300f029e128d09fe51f00a0e300f029e118d09fe5")
BOOT_ROM[0xF4:0xFC] = bytes.fromhex("c07e0003a07f0003")  # System SP 0x03007EC0, IRQ SP 0x03007FA0
BOOT_ROM = bytes(BOOT_ROM)
PREMISE_LINES = [
    "* DMA fill premise: GBATEK (DMA Transfers): DMAxSAD and DMAxDAD are write-only; an immediate transfer with a "
    "fixed source reads the source unit count times, writes only the destination span and holds the CPU until it ends",
    "* DMA fill premise: the channel is idle when the control word is written",
    "* DMA fill premise: no interrupt reprograms the channel between the source store and the enable",
    "* DMA fill premise: no later transfer starts from the stale source address without rewriting it",
    "* DMA fill premise: every live stack word (System/User, IRQ or BIOS supervisor) lies in IWRAM at or above "
    "0x03003EC0: the System stack grows at most 16 KiB below its boot SP 0x03007EC0, and the IRQ and supervisor "
    "stacks lie above it",
    "* DMA fill premise: R4-R11 are preserved across each call the facts cross (the ordinary ARM ABI summary); "
    "trusted, not proved"]


def source(**changes):
    return TEMPLATE.format(**dict(DEFAULTS, **changes))


def calls(data):
    decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
    decoder.detail = True
    return {i.address: i.operands[0].imm for i in decoder.disasm(data, BASE) if match.CS_GRP_CALL in i.groups}


class DmaFillWalkTests(unittest.TestCase):
    setUp = fixtures.StackAliasJoinLifetimeTests.setUp
    body = fixtures.StackAliasJoinLifetimeTests.body

    def calls(self, data):
        return calls(data)

    def walk(self, text, fills=True, rom=BOOT_ROM, **options):
        data = self.body(text)
        policy = dma.Fills(rom) if fills else None
        match.verify_leaf_instructions(data, BASE, True, calls(data), incoming_narrow_reads=True,
                                       dma_fills=policy, **options)
        return policy

    def records(self, text, **options):
        return self.walk(text, **options).records

    def refused(self, text, message, **options):
        with self.assertRaisesRegex(ValueError, message):
            self.walk(text, **options)

    def test_immediate_halfword_fill_is_recorded_and_refused_without_the_policy(self):
        self.assertEqual(self.records(source()), [VRAM_RECORD])
        with self.assertRaisesRegex(ValueError, ESCAPE):
            self.walk(source(), fills=False)
        # A function without such a store records nothing, writes no lines and walks as before.
        fills = self.walk("push {r4, lr}\nsub sp, #4\nmov r0, sp\nstr r1, [r0]\nadd sp, #4\npop {r4}\npop {r1}\nbx r1")
        self.assertEqual((fills.records, fills.report_lines()), ([], []))

    def test_each_channel_unit_and_the_interrupt_bit(self):
        cases = (("0x040000B0", "ldr r1, =0x02000000", "ldr r2, =0x85000004", 0, 4, 16, "ewram"),
                 ("0x040000BC", "ldr r1, =0x07000000", "ldr r2, =0x81000200", 1, 2, 0x400, "oam"),
                 # a DMA0-2 count of 0 is 0x4000 units
                 ("0x040000C8", "ldr r1, =0x06000000", "ldr r2, =0x81000000", 2, 2, 0x8000, "vram"),
                 # a DMA3 count of 0 is 0x10000 units
                 ("0x040000D4", "ldr r1, =0x02000000", "ldr r2, =0x81000000", 3, 2, 0x20000, "ewram"),
                 ("0x040000D4", "ldr r1, =0x05000000", "ldr r2, =0xC1000200", 3, 2, 0x400, "palette"))
        for register, window, tail, channel, unit, size, region in cases:
            with self.subTest(register=register, tail=tail):
                (record,) = self.records(source(register=register, window=window, tail=tail))
                self.assertEqual((record["channel"], record["unit"], record["bytes"], record["region"]),
                                 (channel, unit, size, region))
                self.assertEqual(record["control"], int(tail.split("=")[1], 16))

    def test_region_ends_are_exact(self):
        good = (("ldr r1, =0x05000000", "ldr r2, =0x81000200"),
                ("ldr r1, =0x05000200", "ldr r2, =0x81000100"),
                ("ldr r1, =0x07000300", "ldr r2, =0x81000080"),
                ("ldr r1, =0x0203FFFC", "ldr r2, =0x85000001"),
                ("ldr r1, =0x06017FFE", "ldr r2, =0x81000001"))
        for window, tail in good:
            with self.subTest(window=window, tail=tail):
                self.records(source(window=window, tail=tail))
        bad = (("ldr r1, =0x05000202", "ldr r2, =0x81000100"),
               ("ldr r1, =0x07000302", "ldr r2, =0x81000080"),
               ("ldr r1, =0x02040000", "ldr r2, =0x85000001"),
               ("ldr r1, =0x0203FFFC", "ldr r2, =0x85000002"),
               ("ldr r1, =0x06018000", "ldr r2, =0x81000001"),
               ("ldr r1, =0x06010000", "ldr r2, =0x8100C000"),
               ("ldr r1, =0x04000000", "ldr r2, =0x81000001"),
               ("ldr r1, =0x08000000", "ldr r2, =0x81000001"),
               ("ldr r1, =0x0E000000", "ldr r2, =0x81000001"),
               ("ldr r1, =0x04FFFFFE", "ldr r2, =0x81000002"),
               ("ldr r1, =0x0203FFFE", "ldr r2, =0x81000002"),
               ("ldr r1, =0x05FFFFFE", "ldr r2, =0x81000001"),
               ("ldr r1, =0x06FFFFFE", "ldr r2, =0x81000001"))
        for window, tail in bad:
            with self.subTest(window=window, tail=tail):
                self.refused(source(window=window, tail=tail), REGION)

    def test_iwram_spans_end_at_the_stack_floor(self):
        self.assertEqual(dma.stack_floor(BOOT_ROM), 0x03003EC0)
        for window, tail, destination in (("ldr r1, =0x03003860", "ldr r2, =0x81000100", 0x03003860),
                                          # the 08135B40 second fill: a literal plus a constant, control kept in r2
                                          ("ldr r1, =0x03003860\nmovs r3, #0x80\nlsls r3, r3, #2\nadds r1, r1, r3",
                                           "ldr r2, =0x81000100", 0x03003A60),
                                          ("ldr r1, =0x03003CC0", "ldr r2, =0x81000100", 0x03003CC0),
                                          ("movs r1, #3\nlsls r1, r1, #24", "ldr r2, =0x85000100", 0x03000000)):
            with self.subTest(window=window):
                (record,) = self.records(source(window=window, tail=tail))
                self.assertEqual((record["region"], record["destination"]), ("iwram", destination))
        for window, tail in (("ldr r1, =0x03003CC2", "ldr r2, =0x81000100"),   # ends 2 bytes past the floor
                             ("ldr r1, =0x03003EC0", "ldr r2, =0x81000001"),
                             # the issue's case: 0xC000 halfwords from 0x03007000 cover the stacks
                             ("ldr r1, =0x03007000", "ldr r2, =0x8100C000"),
                             ("ldr r1, =0x03007D00", "ldr r2, =0x81000100"),
                             ("ldr r1, =0x03007FF0", "ldr r2, =0x81000001"),
                             ("ldr r1, =0x02FFFFFE", "ldr r2, =0x81000002")):
            with self.subTest(window=window):
                self.refused(source(window=window, tail=tail), REGION)
        # Without the pinned boot code no IWRAM span qualifies; stackless regions need no ROM.
        iwram = source(window="ldr r1, =0x03003860", tail="ldr r2, =0x81000100")
        for offset in (0, 3, 0xC0, 0xCA, 0xD6, 0xF4, 0xFB):
            rom = bytearray(BOOT_ROM)
            rom[offset] ^= 1
            with self.subTest(offset=offset):
                self.assertIsNone(dma.stack_floor(bytes(rom)))
                self.refused(iwram, REGION, rom=bytes(rom))
        self.assertIsNone(dma.stack_floor(None))
        self.refused(iwram, REGION, rom=None)
        self.assertEqual(self.records(source(), rom=None), [VRAM_RECORD])

    def test_exact_value_forms(self):
        cases = (("ldr r3, =0x06000000\nmov r8, r3\nmov r1, r8", 0x06000000),
                 ("ldr r3, =0x06000000\nmovs r1, r3", 0x06000000),
                 ("ldr r1, =0x0C000000\nlsrs r1, r1, #1", 0x06000000),
                 ("ldr r1, =0x06000100\nmovs r3, #0x80\nlsls r3, r3, #1\nsubs r1, r1, r3", 0x06000000),
                 ("ldr r1, =0x0600FFFF\nldr r3, =0xFFFF0000\nands r1, r3", 0x06000000),
                 ("ldr r1, =0x06000FF0\nldr r3, =0x00000FF0\neors r1, r3", 0x06000000),
                 ("ldr r1, =0x06000FF0\nldr r3, =0x00000FF0\nbics r1, r3", 0x06000000),
                 ("ldr r3, =0x06000010\nsubs r1, r3, #4\nsubs r1, #0xc", 0x06000000),
                 ("ldr r3, =0x05FFFFF0\nadds r1, r3, #4\nadds r1, #0xc", 0x06000000))
        for window, value in cases:
            with self.subTest(window=window):
                self.assertEqual(self.records(source(window=window))[0]["destination"], value)
        for window, value in (("ldr r3, =0x03003860\nadds r1, r3, #4", 0x03003864),
                              ("ldr r3, =0x03003860\nmovs r1, #8\nadds r1, r3, r1\nsubs r1, r1, #4", 0x03003864),
                              ("ldr r1, =0x03003870\nldr r3, =0xFFFFFFF0\nsubs r1, r1, r3", 0x03003880)):
            with self.subTest(window=window):
                self.assertEqual(self.records(source(window=window, tail="ldr r2, =0x81000100"))[0]["destination"],
                                 value)
        # LSRS #32 gives zero.
        self.refused(source(window="ldr r1, =0x06000000\nlsrs r1, r1, #32"), REGION)
        for window in ("ldr r1, =0x0C000000\nasrs r1, r1, #1", "ldr r1, =0xF9FFFFFF\nmvns r1, r1",
                       "ldr r1, =0x06000000\nadds r1, r1, r3", "ldr r1, =0x06000000\nadcs r1, r3",
                       "ldr r1, =0x06000000\nmov r8, r3\nmov r1, r8"):
            with self.subTest(window=window):
                self.refused(source(window=window), DESTINATION)

    def test_register_moves_track_only_r0_to_r12(self):
        self.assertEqual(self.records(source(window="ldr r3, =0x06000000\nmov r12, r3\nmov r1, r12"))[0]["destination"],
                         0x06000000)
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        r = match.ARM_REG_R0
        for code, incoming in (("7146", {r + 14: 5, match.ARM_REG_LR: 5}),   # mov r1, lr
                               ("6946", {r + 13: 5, match.ARM_REG_SP: 5}),   # mov r1, sp
                               ("9e46", {r + 3: 5})):                                 # mov lr, r3
            (item,) = decoder.disasm(bytes.fromhex(code), BASE)
            with self.subTest(instruction=f"{item.mnemonic} {item.op_str}"):
                self.assertIsNone(dma.transfer(item, incoming, b"", BASE))
        (item,) = decoder.disasm(bytes.fromhex("9446"), BASE)   # mov r12, r2
        self.assertEqual(dma.transfer(item, {r + 2: 5}, b"", BASE), (r + 12, 5))
        # A literal load must read a whole word inside the function.
        (item,) = decoder.disasm(bytes.fromhex("0048"), BASE)   # ldr r0, [pc, #0]
        self.assertEqual(dma.transfer(item, {}, bytes(4) + bytes.fromhex("78563412"), BASE), (r, 0x12345678))
        with self.assertRaisesRegex(ValueError, "literal escapes the complete function"):
            dma.transfer(item, {}, bytes(7), BASE)

    def test_equal_values_from_distinct_literal_words_survive_a_join(self):
        join = "cmp r3, #0\nbeq other\nldr r1, first\nb joined\nother:\nldr r1, second\njoined:"
        words = "\n.align 2\nfirst: .word 0x06000000\nsecond: .word {second}"
        self.assertEqual(self.records(source(before=join, window="") + words.format(second="0x06000000"))[0]
                         ["destination"], 0x06000000)
        self.refused(source(before=join, window="") + words.format(second="0x06000002"), DESTINATION)

    def test_values_cross_calls_only_in_r4_to_r11(self):
        # The 08003410 shape: the base kept in r4 across a call, a second fill to palette RAM.
        second = ("bl callee\nmov r0, sp\nstrh r5, [r0]\nstr r0, [r4]\nmovs r1, #0xa0\nlsls r1, r1, #0x13\n"
                  "str r1, [r4, #4]\nldr r2, =0x81000200\nstr r2, [r4, #8]\nldr r0, [r4, #8]")
        records = self.records(source(after=second))
        self.assertEqual([record["region"] for record in records], ["vram", "palette"])
        self.assertEqual(self.records(source(after="ldr r5, =0x81000200\nbl callee\n" + second.replace(
            "ldr r2, =0x81000200\n", "adds r2, r5, #0\n")))[1]["control"], 0x81000200)
        # r3 does not survive a call.
        moved = second.replace("str r0, [r4]", "str r0, [r3]").replace("[r4", "[r3")
        self.refused(source(after="adds r3, r4, #0\n" + moved), BASE_REFUSAL)
        self.refused(source(after="ldr r2, =0x81000200\n" + second.replace("ldr r2, =0x81000200\n", "")), CONTROL)
        # Nor does r12, the intra-procedure-call scratch register: base, control and destination held in r12
        # are exact without a call between and refused across one.
        dest = "movs r1, #0xa0\nlsls r1, r1, #0x13\n"
        for call in ("", "bl callee\n"):
            fills = {
                "base": ("mov r12, r4\n" + call + moved.replace("bl callee\n", "mov r3, r12\n"), BASE_REFUSAL),
                "control": ("ldr r2, =0x81000200\nmov r12, r2\n" + call + "mov r2, r12\n" +
                            second.replace("bl callee\n", "").replace("ldr r2, =0x81000200\n", ""), CONTROL),
                "destination": (dest + "mov r12, r1\n" + call + "mov r1, r12\n" +
                                second.replace("bl callee\n", "").replace(dest, ""), DESTINATION),
            }
            for label, (after, refusal) in fills.items():
                with self.subTest(label, call=bool(call)):
                    if call:
                        self.refused(source(after=after), refusal)
                    else:
                        self.assertEqual(len(self.records(source(after=after))), 2)

    def test_joins_keep_only_equal_values(self):
        branch = "cmp r3, #0\nbeq other\nldr r4, ={first}\nb joined\nother:\nldr r4, ={second}\njoined:"

        def joined(text):
            return source().replace("ldr r4, =0x040000D4\n", text + "\n")
        self.assertEqual(len(self.records(joined(branch.format(first="0x040000D4", second="0x040000D4")))), 1)
        for first, second in (("0x040000D4", "0x040000B0"), ("0x040000D4", "0x040000D8")):
            with self.subTest(second=second):
                self.refused(joined(branch.format(first=first, second=second)), BASE_REFUSAL)
        self.refused(joined("cmp r3, #0\nbeq joined\nldr r4, =0x040000D4\njoined:"), BASE_REFUSAL)

    def test_base_must_be_exactly_a_source_register(self):
        for register in ("0x040000D8", "0x040000DC", "0x040000D0", "0x040000B4", "0x040000E0", "0x04000000",
                         "0x040000D5", "0x140000D4"):
            with self.subTest(register=register):
                self.refused(source(register=register), BASE_REFUSAL)
        self.refused(source().replace("ldr r4, =0x040000D4", "adds r4, r3, #0"), BASE_REFUSAL)

    def test_control_word_bits(self):
        good = ("0x8100C000", "0x81000001", "0x85000001", "0xC100FFFF", "0x8100FFFF", "0x81000000")
        for control in good:
            with self.subTest(control=control):
                self.records(source(tail=f"ldr r2, ={control}", window="ldr r1, =0x02000000"))
        bad = ("0x0100C000",   # enable clear
               "0x8000C000",   # incrementing source
               "0x8080C000",   # decrementing source
               "0x8180C000",   # prohibited source control
               "0x9100C000",   # VBlank start
               "0xA100C000",   # HBlank start
               "0xB100C000",   # special start
               "0x8300C000",   # repeat
               "0x8900C000",   # Game Pak DRQ
               "0x8120C000",   # decrementing destination
               "0x8140C000",   # fixed destination
               "0x8160C000",   # incrementing destination with reload
               "0x8101C000",   # unused bit 16
               "0x8110C000")   # unused bit 20
        for control in bad:
            with self.subTest(control=control):
                self.refused(source(tail=f"ldr r2, ={control}", window="ldr r1, =0x02000000"), CONTROL)
        # DMA0-2 counts have 14 bits.
        for register in ("0x040000B0", "0x040000BC", "0x040000C8"):
            for control in ("0x81004000", "0x81008000"):
                with self.subTest(register=register, control=control):
                    self.refused(source(register=register, tail=f"ldr r2, ={control}",
                                        window="ldr r1, =0x02000000"), CONTROL)
        self.records(source(tail="ldr r2, =0x81004000", window="ldr r1, =0x02000000"))

    def test_control_must_be_an_exact_value(self):
        for tail in ("adds r2, r3, #0", "ldr r2, =0x81000000\norrs r2, r3", "ldr r2, [r3]", "movs r2, #1"):
            with self.subTest(tail=tail):
                self.refused(source(tail=tail), CONTROL if tail != "ldr r2, [r3]" else ESCAPE)
        self.refused(source(before="ldr r2, [r3]", tail=""), CONTROL)
        # Exact arithmetic is followed: lsls, orrs and adds of known values.
        self.assertEqual(self.records(source(
            tail="movs r2, #0x81\nlsls r2, r2, #24\nmovs r3, #0x10\norrs r2, r3"))[0]["control"], 0x81000010)

    def test_window_is_one_straight_path_of_register_instructions(self):
        # A store without the fill's shape in the bytes keeps the escape refusal at that store.
        for window in ("movs r1, #0xc0\nmovs r0, #0\nbl callee\nlsls r1, r1, #0x13",
                       "movs r1, #0xc0\nb next\nnext:\nlsls r1, r1, #0x13",
                       "movs r1, #0xc0\nstr r5, [r3]\nlsls r1, r1, #0x13",
                       "movs r1, #0xc0\nstrh r5, [r0]\nlsls r1, r1, #0x13",
                       "movs r1, #0xc0\nldr r3, [r0]\nlsls r1, r1, #0x13",
                       "movs r1, #0xc0\npush {r5}\npop {r5}\nlsls r1, r1, #0x13",
                       "movs r1, #0xc0\nadds r4, #0\nlsls r1, r1, #0x13",
                       "movs r1, #0xc0\nmov r4, r8\nlsls r1, r1, #0x13",
                       "movs r1, #0xc0\nadds r4, r5, #0\nlsls r1, r1, #0x13",
                       "movs r1, #0xc0\nstr r0, [r4]\nlsls r1, r1, #0x13",
                       "movs r1, #0xc0\nlsls r1, r1, #0x13\nstr r1, [r4, #4]",
                       "movs r1, #0xc0\nlsls r1, r1, #0x13\nstr r1, [r4, #12]",
                       "movs r1, #0xc0\nlsls r1, r1, #0x13\nstrh r2, [r4, #8]"):
            with self.subTest(window=window):
                self.refused(source(window=window), ESCAPE)
        # Destination and control stores at other offsets or as halfwords.
        for old, new in (("str r1, [r4, #4]", "str r1, [r4, #12]"), ("str r2, [r4, #8]", "str r2, [r4, #12]"),
                         ("str r1, [r4, #4]", "strh r1, [r4, #2]"), ("str r2, [r4, #8]", "strh r2, [r4, #4]"),
                         ("str r2, [r4, #8]", "str r2, [r4]")):
            with self.subTest(new=new):
                self.refused(source().replace(old, new), ESCAPE)
        # The destination stored through another register, and other register forms.
        self.refused(source().replace("str r1, [r4, #4]\n", "adds r5, r4, #0\nstr r1, [r5, #4]\n"), ESCAPE)
        for window in ("movs r1, #0xc0\nadd r1, r8\nlsls r1, r1, #0x13", "movs r1, #0xc0\ncmp r1, r8\nlsls r1, r1, #0x13",
                       "movs r1, #0xc0\nadd r3, sp, #0\nlsls r1, r1, #0x13"):
            with self.subTest(window=window):
                self.refused(source(window=window), ESCAPE)
        self.records(source(window="movs r1, #0xc0\nmov r3, r8\ncmp r3, #0\nmuls r3, r3\nlsls r1, r1, #0x13"))
        # The control store before the destination store.
        self.refused(source(window="movs r1, #0xc0\nlsls r1, r1, #0x13\nldr r2, =0x8100C000\nstr r2, [r4, #8]",
                            tail=""), ESCAPE)
        # No destination store at all.
        self.refused(source().replace("str r1, [r4, #4]\n", ""), ESCAPE)
        # Sixteen instructions from the source store to the control store are the bound.
        filler = "\n".join(["movs r3, #0"] * 11)
        self.records(source(window="movs r1, #0xc0\nlsls r1, r1, #0x13\n" + filler))
        self.refused(source(window="movs r1, #0xc0\nlsls r1, r1, #0x13\n" + filler + "\nmovs r3, #0"), ESCAPE)
        # The shape is in the bytes but a control-flow edge enters the window: refused after the walk.
        self.refused(source(source="mov r0, sp\nmovs r5, #0\nstrh r5, [r0]\ncmp r3, #0\nbeq inside",
                            window="inside:\nmovs r1, #0xc0\nlsls r1, r1, #0x13"), WINDOW)

    def test_control_read_back_follows_the_enable(self):
        for readback in ("movs r0, #0", "ldr r0, [r4, #4]", "ldr r0, [r5, #8]", "ldrh r0, [r4, #8]",
                         "movs r3, #0\nldr r0, [r4, #8]", "b next\nnext:\nldr r0, [r4, #8]"):
            with self.subTest(readback=readback):
                self.refused(source(readback=readback), ESCAPE)
        # The read-back is in the bytes but another path enters it: refused after the walk.
        self.refused(source(readback="back:\nldr r0, [r4, #8]").replace(
            "ldr r4, =0x040000D4\n", "cmp r3, #0\nbeq back\nldr r4, =0x040000D4\n"), READBACK)

    def test_source_unit_lies_in_allocated_local_words(self):
        # sp+8 is the saved r4.
        self.refused(source(source="add r0, sp, #8\nmovs r5, #0"), UNIT)
        # A word unit from a halfword-aligned local.
        self.refused(source(source="mov r0, sp\nadds r0, #2", window="ldr r1, =0x02000000",
                            tail="ldr r2, =0x85000001"), "unaligned or outside allocated local words")
        (record,) = self.records(source(source="mov r0, sp\nadds r0, #6"))
        self.assertEqual(record["source"], -14)
        (record,) = self.records(source(source="add r0, sp, #4", window="ldr r1, =0x02000000",
                                        tail="ldr r2, =0x85000001"))
        self.assertEqual((record["source"], record["unit"]), (-16, 4))
        # Without an allocation SP addresses a saved register.
        text = ("push {r4, lr}\nmov r0, sp\nldr r4, =0x040000D4\nstr r0, [r4]\nldr r1, =0x02000000\n"
                "str r1, [r4, #4]\nldr r2, =0x81000001\nstr r2, [r4, #8]\nldr r3, [r4, #8]\n"
                "pop {r4}\npop {r1}\nbx r1\n.ltorg")
        self.refused(text, UNIT)

    def test_source_unit_never_holds_a_stack_address(self):
        # On the version-2 path (stack_arguments, as main's retry and the data-buffer proof walk) a
        # local word may hold a local's address (a pointer slot). A fill from that word copies the
        # stack address into the destination span, count times: an escape into readable memory.
        text = ("push {{r4, r5, lr}}\nsub sp, #8\nmov r0, sp\nstr r0, [sp, #4]\n{source}\n"
                "ldr r4, =0x040000D4\nstr r0, [r4]\nldr r1, =0x02000000\nstr r1, [r4, #4]\n"
                "ldr r2, ={control}\nstr r2, [r4, #8]\nldr r0, [r4, #8]\n"
                "add sp, #8\npop {{r4, r5}}\npop {{r1}}\nbx r1\n.ltorg")
        for control in ("0x85000010", "0x81000010"):     # the whole word, or its low halfword
            with self.subTest(control=control):
                self.refused(text.format(source="add r0, sp, #4", control=control), POINTER,
                             buffer_proof=match.BufferCallProof(b"", None, stack_arguments=True))
        # the upper halfword of the pointer word
        self.refused(text.format(source="add r0, sp, #4\nadds r0, #2", control="0x81000010"), POINTER,
                     buffer_proof=match.BufferCallProof(b"", None, stack_arguments=True))
        # The scalar word beside it is admitted on the same path.
        (record,) = self.records(text.format(source="mov r0, sp", control="0x85000010"),
                                 buffer_proof=match.BufferCallProof(b"", None, stack_arguments=True))
        self.assertEqual((record["source"], record["unit"], record["region"]), (-20, 4, "ewram"))
        # Without stack arguments the pointer store itself stays an escape.
        self.refused(text.format(source="add r0, sp, #4", control="0x85000010"), ESCAPE)

    def test_destination_is_exact_and_aligned(self):
        self.refused(source(window="adds r1, r3, #0"), DESTINATION)
        self.refused(source(window="ldr r1, =0x06000001"), DESTINATION)
        self.refused(source(window="ldr r1, =0x02000002", tail="ldr r2, =0x85000001"), DESTINATION)

    def test_only_the_plain_source_store_is_admitted(self):
        # The alias as the destination, a halfword source store and an offset store stay escapes.
        for text in (source(window="movs r1, #0xc0\nlsls r1, r1, #0x13\nstr r0, [r4, #4]"),
                     source().replace("str r0, [r4]\n", "strh r0, [r4]\n"),
                     source().replace("str r0, [r4]\n", "str r0, [r4, #4]\n")):
            with self.subTest(text=text.splitlines()[4:9]), self.assertRaisesRegex(ValueError, ESCAPE):
                self.walk(text)
        # A second source store in the window.
        self.refused(source().replace("str r0, [r4]\n", "adds r5, r0, #0\nstr r0, [r4]\nstr r5, [r4]\n"), ESCAPE)
        # A store of the alias somewhere that is not a source register is refused after the walk.
        self.refused(source(register="0x02000000"), BASE_REFUSAL)

    def test_one_source_offset_per_site(self):
        text = source()
        data = self.body(text)
        fills = self.walk(text)
        site = BASE + fills.records[0]["site"]
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        instructions = {}
        for item in decoder.disasm(data, BASE):
            instructions[item.address] = item
            if item.mnemonic == "bx":
                break
        edges = {address: () if item.mnemonic == "bx" else (address + item.size,)
                 for address, item in instructions.items()}
        predecessors = {address: set() for address in instructions}
        for address, successors in edges.items():
            for successor in successors:
                predecessors[successor].add(address)
        stack = ((False, False, True),) * 2 + ((False, True, False),) * 3
        policy = dma.Fills()
        self.assertTrue(policy.admit(data, BASE, instructions[site], site, {match.ARM_REG_R0: -20}, stack, {match.ARM_REG_R0}, ()))
        self.assertTrue(policy.admit(data, BASE, instructions[site], site, {match.ARM_REG_R0: -16}, stack, {match.ARM_REG_R0}, ()))
        with self.assertRaisesRegex(ValueError, "source differs between paths"):
            policy.finish(data, BASE, instructions, edges, predecessors)
        # Every recorded frame state is checked: a merged state without the allocation refuses.
        policy = dma.Fills()
        policy.admit(data, BASE, instructions[site], site, {match.ARM_REG_R0: -20}, stack, {match.ARM_REG_R0}, ())
        policy.admit(data, BASE, instructions[site], site, {match.ARM_REG_R0: -20}, ((False, False, False),) + stack[1:],
                     {match.ARM_REG_R0}, ())
        with self.assertRaisesRegex(ValueError, UNIT):
            policy.finish(data, BASE, instructions, edges, predecessors)
        # ... and so is every recorded pointer set: the unit's word holds a stack address on one path.
        policy = dma.Fills()
        policy.admit(data, BASE, instructions[site], site, {match.ARM_REG_R0: -20}, stack, {match.ARM_REG_R0}, ())
        policy.admit(data, BASE, instructions[site], site, {match.ARM_REG_R0: -20}, stack, {match.ARM_REG_R0}, {-20})
        with self.assertRaisesRegex(ValueError, POINTER):
            policy.finish(data, BASE, instructions, edges, predecessors)
        # a pointer in the neighbouring word does not touch the halfword unit
        policy = dma.Fills()
        policy.admit(data, BASE, instructions[site], site, {match.ARM_REG_R0: -20}, stack, {match.ARM_REG_R0}, {-16, -24})
        policy.finish(data, BASE, instructions, edges, predecessors)
        self.assertEqual([record["source"] for record in policy.records], [-20])
        # admit() refuses everything but the one offending source register of a plain store.
        policy = dma.Fills()
        for aliases, offending in (({match.ARM_REG_R0: -20, match.ARM_REG_R0 + 4: -16}, {match.ARM_REG_R0}),
                                   ({match.ARM_REG_R0: -20}, {match.ARM_REG_R0, match.ARM_REG_R0 + 1}),
                                   ({match.ARM_REG_R0 + 1: -20}, {match.ARM_REG_R0 + 1})):
            self.assertFalse(policy.admit(data, BASE, instructions[site], site, aliases, stack, offending, ()))
        self.assertFalse(policy.admit(data, BASE, instructions[BASE + 18], BASE + 18, {match.ARM_REG_R0 + 1: -20}, stack,
                                      {match.ARM_REG_R0 + 1}, ()))
        policy.finish(data, BASE, instructions, edges, predecessors)
        self.assertEqual(policy.records, [])
        self.assertFalse(policy.admit(data, BASE, instructions[site], site, {match.ARM_REG_R0: -20}, stack, {match.ARM_REG_R0}, ()))
        with self.assertRaisesRegex(ValueError, "already complete"):
            policy.finish(data, BASE, instructions, edges, predecessors)
        with self.assertRaisesRegex(ValueError, "exact closed walk CFG"):
            dma.exact_values(instructions, {}, BASE, data)
        with self.assertRaisesRegex(ValueError, "leave the walk CFG"):
            dma.exact_values({BASE: instructions[BASE]}, {BASE: (BASE + 2,)}, BASE, data)

    def test_a_fill_inside_a_walked_callee_stays_refused(self):
        # The policy is given only to the root walk; an inspected callee's own fill (0801AF08's case)
        # is refused inside the callee walk, and the policy sees nothing.
        assembly = self.root / "callee.s"
        assembly.write_text(".syntax unified\n.arch armv4t\n.thumb\n.text\n.global caller, caller_end, callee_end\ncaller:\n"
                            "push {r4, lr}\nsub sp, #4\nmov r0, sp\nbl callee\nadd sp, #4\npop {r4}\npop {r1}\n"
                            "bx r1\ncaller_end:\n.org 0x100\ncallee:\n" + source() + "\ncallee_end:\n")
        for command in (["arm-none-eabi-as", "-mthumb-interwork", str(assembly), "-o", str(self.root / "callee.o")],
                        ["arm-none-eabi-ld", "-Ttext=0x08000000", "-e", "caller", str(self.root / "callee.o"),
                         "-o", str(self.root / "callee.elf")],
                        ["arm-none-eabi-objcopy", "-O", "binary", "--only-section=.text", str(self.root / "callee.elf"),
                         str(self.root / "callee.bin")]):
            subprocess.run(command, check=True, capture_output=True)
        image = (self.root / "callee.bin").read_bytes()
        symbols = {row["name"]: row["value"] for row in match.elf_image((self.root / "callee.elf").read_bytes())["symbols"]}
        data = image[:symbols["caller_end"] - BASE]
        mapping = json.dumps([{"rom": f"0x{BASE:08X}", "end": f"0x{symbols['caller_end']:08X}", "mode": "thumb"},
                              {"rom": "0x08000100", "end": f"0x{symbols['callee_end']:08X}", "mode": "thumb"}])
        # The callee body alone is admitted by the root rule ...
        self.assertEqual(self.records(source()), [VRAM_RECORD])
        # ... but reached as a buffer callee it keeps the escape refusal.
        for stack_arguments in (False, True):
            fills = dma.Fills(BOOT_ROM)
            with self.subTest(stack_arguments=stack_arguments), \
                    self.assertRaisesRegex(ValueError, "buffer callee 0x08000100: " + ESCAPE):
                match.verify_leaf_instructions(
                    data, BASE, True, calls(data), incoming_narrow_reads=True, dma_fills=fills,
                    buffer_proof=match.BufferCallProof(image, mapping, stack_arguments=stack_arguments))
            self.assertEqual(fills.observations, {})

    def test_policy_requires_the_plain_thumb_direct_call_path(self):
        data = self.body(source())
        calls = self.calls(data)
        for options in (dict(dma_fills=dma.Fills()), dict(dma_fills=dma.Fills(), incoming_narrow_reads=False),
                        dict(dma_fills=object(), incoming_narrow_reads=True),
                        dict(dma_fills=type("Derived", (dma.Fills,), {})(), incoming_narrow_reads=True)):
            with self.subTest(options=options), self.assertRaisesRegex(ValueError, ISOLATION):
                match.verify_leaf_instructions(data, BASE, True, calls, **options)
        with self.assertRaisesRegex(ValueError, ISOLATION):
            match.verify_leaf_instructions(data, BASE, False, calls, dma_fills=dma.Fills())
        for options in (dict(self_calls=frozenset({BASE + 4})), dict(acyclic_state_budget=64),
                        dict(inert_spin_context={})):
            with self.subTest(options=options), self.assertRaisesRegex(ValueError, "plain Thumb direct-call path"):
                match.verify_leaf_instructions(data, BASE, True, calls, incoming_narrow_reads=True,
                                               dma_fills=dma.Fills(), **options)
        for proof in (match.BufferCallProof(b"", None), match.BufferCallProof(b"", None, stack_arguments=True)):
            fills = dma.Fills()
            match.verify_leaf_instructions(data, BASE, True, calls, buffer_proof=proof,
                                           incoming_narrow_reads=True, dma_fills=fills)
            self.assertEqual(fills.records, [VRAM_RECORD])

    def test_only_the_plain_path_and_its_replay_pass_the_policy(self):
        found = set()
        for path in sorted((ROOT / "tools").glob("*.py")):
            for function in ast.walk(ast.parse(path.read_text())):
                if isinstance(function, (ast.FunctionDef, ast.AsyncFunctionDef)) and any(
                        isinstance(node, ast.Call) and any(keyword.arg == "dma_fills" for keyword in node.keywords)
                        for node in ast.walk(function)):
                    found.add((path.name, function.name))
        self.assertEqual(found, {("match.py", "main"), ("match_evidence.py", "legacy_report_control_flow"),
                                 ("data_buffer_profile.py", "prove"), ("data_buffer_profile.py", "verify_source")})
        # and only main and the two validators build one
        built = set()
        for path in sorted((ROOT / "tools").glob("*.py")):
            for function in ast.walk(ast.parse(path.read_text())):
                if isinstance(function, (ast.FunctionDef, ast.AsyncFunctionDef)) and any(
                        isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and
                        node.func.attr == "Fills" for node in ast.walk(function)):
                    built.add((path.name, function.name))
        self.assertEqual(built, {("match.py", "main"), ("match_evidence.py", "legacy_report_control_flow"),
                                 ("data_buffer_profile.py", "report_matches")})


class DmaFillReportTests(unittest.TestCase):
    setUp = fixtures.StackAliasJoinLifetimeTests.setUp
    body = fixtures.StackAliasJoinLifetimeTests.body

    def tree(self, text, objects=None):
        data = self.body(text)
        mapping = json.dumps([
            {"rom": f"0x{BASE:08X}", "end": f"0x{BASE + len(data):08X}", "mode": "thumb"},
            {"rom": "0x08000100", "end": "0x08000102", "mode": "thumb"}]).encode()
        for name in ("config", "src"):
            (self.root / name).mkdir(exist_ok=True)
        (self.root / "config/functions.json").write_bytes(mapping)
        if objects is not None:
            (self.root / "config/data_symbols.json").write_text(json.dumps(objects))
        (self.root / "baserom.bin").write_bytes(data.ljust(0x100, b"\0") + bytes.fromhex("7047"))
        (self.root / "src/08000000.c").write_text("/* synthetic fingerprint input */\n")
        return data, mapping

    def report(self, data, mapping, lines, schema=evidence.FRAMED_LINKED_SCHEMA, objects=None):
        """The report match.py writes for these bytes (report_fixtures), with `lines` in place of its DMA
        fill block, right after the stack-frame line; `lines` may be a tampered block."""
        try:
            instructions = match.verify_leaf_instructions(data, BASE, True, call_resolver=lambda target: None,
                                                          incoming_narrow_reads=True, dma_fills=dma.Fills(BOOT_ROM))
        except (ValueError, KeyError, TypeError, AttributeError):
            instructions = report_fixtures.decode(data, BASE)
        linked = any(instruction.mnemonic == "bl" for instruction in instructions)
        data_schema = schema in (evidence.DATA_SCHEMA, evidence.FRAMED_DATA_SCHEMA)
        text = report_fixtures.complete(
            self.root, BASE, data, schema, instructions, mapped=linked or data_schema,
            control_flow=evidence.CALL_SUMMARY if linked else "closed leaf CFG", data_profile=data_schema)
        rows = text.split("\n")
        frame = f"* stack frame: {evidence.STACK_SUMMARY}"
        at = rows.index(frame) + 1 if frame in rows else next(
            index for index, row in enumerate(rows) if row.startswith("* source SHA-256: ")) + 1
        return "\n".join(rows[:at] + list(lines) + rows[at:])

    def lines(self, text):
        data = self.body(text)
        fills = dma.Fills()
        match.verify_leaf_instructions(data, BASE, True, calls(data), incoming_narrow_reads=True, dma_fills=fills)
        return fills.report_lines()

    def replays(self, report):
        return evidence.report_matches(report, self.root, BASE)

    def test_report_lines_state_every_premise_verbatim(self):
        lines = self.lines(source())
        self.assertEqual(lines[0], dma.SUMMARY_FIELD + dma.SUMMARY)
        self.assertEqual(lines[1:-1], PREMISE_LINES)
        self.assertEqual(lines[-1], f"{dma.MANIFEST_FIELD}`{json.dumps(dict(sites=[VRAM_RECORD]), sort_keys=True, separators=(',', ':'))}`")

    def test_saved_report_replays_and_tampers_refuse(self):
        text = source(after="bl callee")
        data, mapping = self.tree(text)
        lines = self.lines(text)
        good = self.report(data, mapping, lines)
        self.assertTrue(self.replays(good))
        self.assertFalse(self.replays(self.report(data, mapping, [])))
        sites = lines[-1]
        records = json.loads(sites[len(dma.MANIFEST_FIELD) + 1:-1])["sites"]
        tampered = {}
        for key in records[0]:
            edited = json.loads(json.dumps(records))
            edited[0][key] = edited[0][key] + 2 if isinstance(edited[0][key], int) else edited[0][key] + "x"
            tampered[key] = lines[:-1] + [f"{dma.MANIFEST_FIELD}`{json.dumps(dict(sites=edited), sort_keys=True, separators=(',', ':'))}`"]
        for index in range(len(lines)):
            tampered[f"drop line {index}"] = lines[:index] + lines[index + 1:]
            tampered[f"edit line {index}"] = lines[:index] + [lines[index] + "."] + lines[index + 1:]
            tampered[f"indent line {index}"] = lines[:index] + ["  " + lines[index]] + lines[index + 1:]
            tampered[f"repeat line {index}"] = lines[:index + 1] + lines[index:]
        tampered.update({
            "extra key": lines[:-1] + [sites.replace('{"bytes"', '{"a":1,"bytes"')],
            "extra manifest key": lines[:-1] + [sites.replace('{"sites"', '{"a":1,"sites"')],
            "no site": lines[:-1] + [f"{dma.MANIFEST_FIELD}`{{\"sites\":[]}}`"],
            "bare list": lines[:-1] + [f"{dma.MANIFEST_FIELD}`{json.dumps(records, sort_keys=True, separators=(',', ':'))}`"],
            "spaced": lines[:-1] + [sites.replace(",", ", ")],
            "swap": [lines[1], lines[0]] + lines[2:],
            "sites first": [sites] + lines[:-1],
            "extra premise": lines[:-1] + ["* DMA fill premise: none"] + [sites]})
        for name, lines_ in tampered.items():
            with self.subTest(name=name):
                self.assertNotEqual(lines_, lines)
                self.assertFalse(self.replays(self.report(data, mapping, lines_)))

    def test_lines_sit_right_after_the_stack_frame_line(self):
        text = source(after="bl callee")
        data, mapping = self.tree(text)
        lines = self.lines(text)
        self.assertTrue(self.replays(self.report(data, mapping, lines)))
        bare = self.report(data, mapping, []).splitlines()
        frame = bare.index(f"* stack frame: {evidence.STACK_SUMMARY}")
        self.assertEqual(self.report(data, mapping, lines).splitlines(), bare[:frame + 1] + lines + bare[frame + 1:])
        # the whole block before the source line, the verification line, the stack-frame line, the verdict
        for index in (0, 1, frame, len(bare) - 1):
            with self.subTest(index=index):
                self.assertFalse(self.replays("\n".join(bare[:index] + lines + bare[index:])))
        # the manifest split from the premises by the next field
        self.assertFalse(self.replays("\n".join(bare[:frame + 1] + lines[:-1] + bare[frame + 1:frame + 2] + lines[-1:] +
                                               bare[frame + 2:])))

    def test_check_report_pins_the_block_to_the_one_stack_frame_line(self):
        data = self.body(source())
        fills = dma.Fills()
        match.verify_leaf_instructions(data, BASE, True, calls(data), incoming_narrow_reads=True, dma_fills=fills)
        block = fills.report_lines()
        frame = "* stack frame: " + evidence.STACK_SUMMARY
        dma.check_report(fills, ["* verification: `x`", frame] + block + ["* other: y"])
        refused = {
            "a second stack-frame line": [frame] + block + [frame],
            "an indented stack-frame line only": ["  " + frame] + block,
            "no stack-frame line": block,
            "a field between the frame and the block": [frame, "* other: y"] + block,
            "a field inside the block": [frame] + block[:2] + ["* other: y"] + block[2:],
            "a field before the manifest": [frame] + block[:-1] + ["* other: y"] + block[-1:],
        }
        for label, lines in refused.items():
            with self.subTest(label):
                with self.assertRaisesRegex(ValueError, "DMA fill lines"):
                    dma.check_report(fills, lines)

    def test_stray_lines_without_a_store_refuse_indented_or_not(self):
        for after, schema in (("", evidence.FRAMED_SCHEMA), ("bl callee", evidence.FRAMED_LINKED_SCHEMA)):
            plain = source(after=after).replace("str r0, [r4]\n", "str r5, [r4]\n")
            data, mapping = self.tree(plain)
            self.assertTrue(self.replays(self.report(data, mapping, [], schema=schema)))
            for line in (PREMISE_LINES[1], "  " + PREMISE_LINES[1], "\t" + dma.SUMMARY_FIELD + "x",
                         "* DMA other: x", "* DMA fillers: x"):
                with self.subTest(schema=schema, line=line[:30]):
                    self.assertFalse(self.replays(self.report(data, mapping, [line], schema=schema)))

    def test_the_schema_guard_refuses_lines_that_another_validator_would_ignore(self):
        # The switch and function-address validators read their own fields and ignore other lines, so the
        # guard in report_matches refuses DMA fill lines there. Each validator and the whole-text comparison
        # after it are patched to accept, so the report replays without the lines and only the guard can
        # refuse it with them.
        data, mapping = self.tree(source())
        lines = self.lines(source())
        for schema, validator in ((evidence.SWITCH_SCHEMA, "switch_report_matches"),
                                  (evidence.FUNCTION_ADDRESS_SCHEMA, "function_address_report_matches"),
                                  (evidence.FRAMED_FUNCTION_ADDRESS_SCHEMA, "function_address_report_matches")):
            with self.subTest(schema=schema), patch.object(evidence, validator, lambda *args, **kwargs: True), \
                    patch.object(evidence, "closed_report", lambda *args, **kwargs: True):
                self.assertTrue(self.replays(self.report(data, mapping, [], schema=schema)))
                self.assertFalse(self.replays(self.report(data, mapping, lines, schema=schema)))
                for line in (lines[1], "  " + lines[1], "\t" + lines[0], "\u00a0" + lines[-1]):
                    with self.subTest(line=line[:24]):
                        self.assertFalse(self.replays(self.report(data, mapping, [line], schema=schema)))

    def test_plain_field_check_admits_the_lines_only_on_the_framed_plain_schemas(self):
        import plain_report_fields as fields
        lines = self.lines(source())
        for schema in (evidence.FRAMED_SCHEMA, evidence.FRAMED_LINKED_SCHEMA, evidence.FRAMED_DATA_SCHEMA,
                       evidence.SCHEMA, evidence.LINKED_SCHEMA, evidence.DATA_SCHEMA, evidence.BUFFER_SCHEMA,
                       evidence.STACK_BUFFER_SCHEMA):
            required, optional, repeated = fields.layout(schema)
            admitted = [line for line in lines if line.startswith(required + optional + repeated)]
            framed = schema in (evidence.FRAMED_SCHEMA, evidence.FRAMED_LINKED_SCHEMA, evidence.FRAMED_DATA_SCHEMA)
            with self.subTest(schema=schema):
                self.assertEqual(admitted, lines if framed else [])
        # the field check holds the block to the writer's place: right after the stack-frame line
        data, mapping = self.tree(source())
        report = self.report(data, mapping, lines, schema=evidence.FRAMED_SCHEMA).splitlines()
        fields.check(report, evidence.FRAMED_SCHEMA, BASE, self.root)
        moved = [line for line in report if not line.startswith(dma.MARKER)]
        moved[moved.index("* source plausibility: plausible"):0] = lines
        with self.assertRaisesRegex(ValueError, "writer's order"):
            fields.check(moved, evidence.FRAMED_SCHEMA, BASE, self.root)

    def test_addressed_remainder_replay_keeps_the_lines_checked(self):
        # A call to __modsi3 sends the legacy replay to the addressed-remainder check, which has no
        # DMA fill rule: the lines must refuse there even when that check passes.
        def tree(text):
            data = self.body(text)
            mapping = json.dumps([
                {"rom": f"0x{BASE:08X}", "end": f"0x{BASE + len(data):08X}", "mode": "thumb"},
                {"rom": "0x08142950", "end": "0x08142954", "mode": "thumb"}]).encode()
            for name in ("config", "src"):
                (self.root / name).mkdir(exist_ok=True)
            (self.root / "config/functions.json").write_bytes(mapping)
            (self.root / "baserom.bin").write_bytes(data.ljust(0x142960, b"\0"))
            (self.root / "src/08000000.c").write_text("/* synthetic fingerprint input */\n")
            return data, mapping
        lines = self.lines(source())

        def addressed(root, address, data, *args):
            # the addressed check passes; its instructions are the decode the fixture's listing shows
            return report_fixtures.decode(data, address)
        with patch.object(match, "verify_addressed_modsi3_source", addressed):
            # the addressed path passes for the same body without the store ...
            data, mapping = tree(source(after="bl 0x08142950").replace("str r0, [r4]\n", "str r5, [r4]\n"))
            self.assertTrue(self.replays(self.report(data, mapping, [])))
            # ... and with the store and its lines it refuses
            data, mapping = tree(source(after="bl 0x08142950"))
            self.assertFalse(self.replays(self.report(data, mapping, lines)))

    def test_lines_belong_to_the_plain_framed_profiles(self):
        data, mapping = self.tree(source())
        lines = self.lines(source())
        self.assertTrue(self.replays(self.report(data, mapping, lines, schema=evidence.FRAMED_SCHEMA)))
        for schema in (evidence.SCHEMA, evidence.LINKED_SCHEMA, evidence.DATA_SCHEMA, evidence.BUFFER_SCHEMA,
                       evidence.STACK_BUFFER_SCHEMA, evidence.SWITCH_SCHEMA, evidence.FUNCTION_ADDRESS_SCHEMA,
                       evidence.FRAMED_FUNCTION_ADDRESS_SCHEMA):
            with self.subTest(schema=schema):
                self.assertFalse(self.replays(self.report(data, mapping, lines, schema=schema)))

    def test_claim_without_the_store_in_the_bytes_is_refused(self):
        lines = self.lines(source())
        plain = source().replace("str r0, [r4]\n", "str r5, [r4]\n")
        data, mapping = self.tree(plain)
        self.assertTrue(self.replays(self.report(data, mapping, [], schema=evidence.FRAMED_SCHEMA)))
        self.assertFalse(self.replays(self.report(data, mapping, lines, schema=evidence.FRAMED_SCHEMA)))



def tools_present():
    return Path(os.path.expandvars(match.DEFAULT_CC)).is_file() and \
        all(shutil.which(tool) for tool in (match.DEFAULT_AS, match.DEFAULT_LD, match.DEFAULT_OBJCOPY))


A = 0x08000200
HEADER = """typedef unsigned short u16;
typedef unsigned int u32;
typedef struct { const void *source; void *destination; u32 control; } Dma;
extern Dma data_040000D4;
extern u16 data_03003860[];
extern void func_08000400(void);
"""
FILL = """
static inline void fill16(void *destination, u32 control)
{
    u16 zero;
    u16 *value = &zero;

    *value = 0;
    {
        /* plausible: DMA3 MMIO requires volatile writes and control readback. */
        volatile Dma *dma = &data_040000D4;

        dma->source = value;
        dma->destination = destination;
        dma->control = control;
        (void)dma->control;
    }
}
"""
NATIVE = HEADER + FILL + """
void func_08000200(void)
{
    fill16(%(first)s, %(control)s);
    func_08000400();
    fill16(%(second)s, 0x81000100);
}
"""


def build(root, text, boot=True, leaf=bytes.fromhex("7047")):
    """A tree whose ROM holds the boot stack setup, the caller compiled from `text` at 0x08000200
    and a leaf at 0x08000400."""
    root = Path(root)
    for name in ("src", "include", "config", "symbols", "build"):
        (root / name).mkdir(parents=True, exist_ok=True)
    rom = bytearray(0x1000)
    if boot:
        rom[:0x100] = BOOT_ROM
    rom[0x400:0x400 + len(leaf)] = leaf
    (root / "src/08000200.c").write_text(text)
    objects = json.dumps({"data_040000D4": "0x040000D4", "data_03003860": "0x03003860"}).encode()
    (root / "config/data_symbols.json").write_bytes(objects)
    args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                              objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
    runner = match.Runner(match.DEFAULT_CC, root=root, wsl_path=match.DEFAULT_WSL_PATH, timeout=120)
    with runner.workspace() as workspace:
        _, _, original = match.compile_object(runner, workspace, args, root, A, "src/08000200.c")
        symbol, _ = match.function_record(original, "func_08000200", A, True)
        entries = [{"rom": f"0x{A:08X}", "end": f"0x{A + symbol['size']:08X}", "mode": "thumb"},
                   {"rom": "0x08000400", "end": f"0x{0x08000400 + len(leaf):08X}", "mode": "thumb"}]
        mapping = json.dumps(entries).encode()
        body, _, _ = match.link_calls(runner, workspace, args, original, A, mapping, len(rom), bytes(rom),
                                      objects, {})
    rom[A - BASE:A - BASE + len(body)] = body
    (root / "config/functions.json").write_bytes(mapping)
    (root / "symbols/functions.txt").write_text("".join(
        f"{int(entry['rom'], 16):08X} {int(entry['end'], 16):08X} "
        f"{int(entry['end'], 16) - int(entry['rom'], 16)} 0 return\n" for entry in entries))
    (root / "baserom.bin").write_bytes(bytes(rom))
    return root


def run(root):
    report = Path(root) / "docs/match/08000200.md"
    if report.exists():
        report.unlink()
    environment = dict(os.environ, FFTA_ROM=str(Path(root) / "baserom.bin"), PYTHONDONTWRITEBYTECODE="1")
    result = subprocess.run([sys.executable, str(ROOT / "tools/match.py"), "--root", str(root), "0x08000200"],
                            capture_output=True, text=True, env=environment, timeout=600)
    return result.returncode, result.stdout + result.stderr, report.read_text() if report.exists() else None


def check_report(root):
    """match.py --check-report: whether the saved report is exactly the one this run would write."""
    environment = dict(os.environ, FFTA_ROM=str(Path(root) / "baserom.bin"), PYTHONDONTWRITEBYTECODE="1")
    result = subprocess.run([sys.executable, str(ROOT / "tools/match.py"), "--root", str(root), "--check-report",
                             "--no-write", "0x08000200"], capture_output=True, text=True, env=environment, timeout=600)
    return result.returncode, result.stdout + result.stderr


@unittest.skipUnless(tools_present(), "fixed compiler and ARM tools required")
class DmaFillNativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix="dma_fill_", dir=scratch)
        cls.base = Path(cls.temporary.name)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def natural(self, name, boot=True, **values):
        text = NATIVE % dict(dict(first="(void *)0x06000000", control="0x8100C000",
                                  second="data_03003860 + 0x100"), **values)
        return run(build(self.base / name, text, boot))

    def replays(self, root, report):
        with patch.dict(os.environ, FFTA_ROM=str(Path(root) / "baserom.bin")):
            return evidence.report_matches(report, root, A)

    def test_natural_fills_match_record_and_replay(self):
        code, output, report = self.natural("good")
        self.assertEqual(code, 0, output)
        self.assertIn("verdict MATCH - byte identical", output)
        lines = report.splitlines()
        self.assertIn(f"* verification: `{evidence.FRAMED_DATA_SCHEMA}`", lines)
        stack = lines.index(f"* stack frame: {evidence.STACK_SUMMARY}")
        self.assertEqual(lines[stack + 1:stack + 2 + len(PREMISE_LINES)],
                         [dma.SUMMARY_FIELD + dma.SUMMARY] + PREMISE_LINES)
        (sites,) = [line for line in lines if line.startswith(dma.MANIFEST_FIELD)]
        self.assertEqual(lines.index(sites), stack + 2 + len(PREMISE_LINES))
        records = json.loads(sites[len(dma.MANIFEST_FIELD) + 1:-1])["sites"]
        self.assertEqual([(r["region"], r["destination"], r["bytes"], r["unit"], r["channel"]) for r in records],
                         [("vram", 0x06000000, 0x18000, 2, 3), ("iwram", 0x03003A60, 0x200, 2, 3)])
        root = self.base / "good"
        self.assertTrue(self.replays(root, report))
        # the saved report is exactly the one match.py writes (render_report), and a changed block is not
        code, output = check_report(root)
        self.assertEqual(code, 0, output)
        self.assertIn("report  identical to the saved", output)
        saved = root / "docs/match/08000200.md"
        saved.write_text(report.replace(sites, sites.replace('"vram"', '"oam"')))
        code, output = check_report(root)
        self.assertNotEqual(code, 0, output)
        self.assertIn("report  DIFFERS from the saved", output)
        saved.write_text(report)
        self.assertFalse(self.replays(root, report.replace(sites + "\n", "")))
        for premise in PREMISE_LINES:
            with self.subTest(premise=premise[:40]):
                self.assertFalse(self.replays(root, report.replace(premise + "\n", "")))
        # The same report against a ROM whose boot code sets another System SP refuses.
        rom = bytearray((root / "baserom.bin").read_bytes())
        rom[0xF5] ^= 1
        (root / "baserom.bin").write_bytes(bytes(rom))
        self.assertFalse(self.replays(root, report))

    def test_a_local_buffer_call_beside_a_fill_keeps_the_buffer_schema_refused(self):
        text = HEADER.replace("extern void func_08000400(void);", "extern void func_08000400(u16 *);") + """
void func_08000200(void)
{
    u16 zero;
    u16 *value = &zero;

    *value = 0;
    {
        /* plausible: DMA3 MMIO requires volatile writes and control readback. */
        volatile Dma *dma = (volatile Dma *)0x040000D4;

        dma->source = value;
        dma->destination = (void *)0x06000000;
        dma->control = 0x8100C000;
        (void)dma->control;
    }
    func_08000400(&zero);
}
"""
        code, output, report = run(build(self.base / "buffer", text))
        self.assertNotEqual(code, 0, output)
        self.assertIsNone(report)
        self.assertIn("DMA fill records require the plain frame, call, data or data-buffer schemas", output)

    def test_records_without_a_stack_frame_line_refuse_as_a_compile_failure(self):
        # Unreachable on real bytes (a record needs a stack alias, so the walk uses the frame), but if a
        # report would carry DMA lines without the stack-frame line, main refuses with a message instead
        # of failing in render_report.
        code, output, _ = self.natural("frameless")
        self.assertEqual(code, 0, output)
        real = match.uses_stack_frame
        root = self.base / "frameless"
        (root / "docs/match/08000200.md").unlink()
        with patch.object(match, "uses_stack_frame",
                          lambda instructions: False if isinstance(instructions, list) else real(instructions)), \
                patch.dict(os.environ, FFTA_ROM=str(root / "baserom.bin")), \
                patch.object(sys, "argv", ["match.py", "--root", str(root), "0x08000200"]), \
                redirect_stdout(io.StringIO()):
            with self.assertRaises(SystemExit) as raised:
                match.main()
        self.assertEqual(str(raised.exception), "compile failed:\nDMA fill records require the stack-frame line")
        self.assertFalse((root / "docs/match/08000200.md").exists())

    def test_a_fill_beside_a_data_buffer_call_matches_and_replays(self):
        # typed DMA registers make the evidence data-buffer evidence, which carries the same lines
        text = HEADER.replace("extern void func_08000400(void);", "extern void func_08000400(u16 *);") + FILL + """
void func_08000200(void)
{
    u16 zero = 0;

    fill16((void *)0x06000000, 0x8100C000);
    fill16(data_03003860 + 0x100, 0x81000100);
    func_08000400(&zero);
}
"""
        # the leaf clears R0-R3 before it returns, so no stack address comes back to the caller's return
        root = build(self.base / "data_buffer", text, leaf=bytes.fromhex("00200021002200237047"))
        code, output, report = run(root)
        self.assertEqual(code, 0, output)
        self.assertIn("verdict MATCH - byte identical", output)
        lines = report.splitlines()
        self.assertIn(f"* verification: `{data_buffer.SCHEMA}`", lines)
        self.assertIn(f"* buffer calls: {evidence.STACK_BUFFER_SUMMARY}", lines)
        fields = dma.report_fields(lines)
        self.assertEqual(fields[:1 + len(PREMISE_LINES)], [dma.SUMMARY_FIELD + dma.SUMMARY] + PREMISE_LINES)
        (sites,) = fields[1 + len(PREMISE_LINES):]
        records = json.loads(sites[len(dma.MANIFEST_FIELD) + 1:-1])["sites"]
        self.assertEqual([(r["region"], r["destination"], r["bytes"]) for r in records],
                         [("vram", 0x06000000, 0x18000), ("iwram", 0x03003A60, 0x200)])
        self.assertTrue(self.replays(root, report))
        code, output = check_report(root)
        self.assertEqual(code, 0, output)
        self.assertIn("report  identical to the saved", output)
        buffer_calls = next(line for line in lines if line.startswith("* buffer calls: "))
        split = report.replace(buffer_calls + "\n", "").replace(
            dma.SUMMARY_FIELD + dma.SUMMARY + "\n", dma.SUMMARY_FIELD + dma.SUMMARY + "\n" + buffer_calls + "\n")
        tampered = [report.replace(sites + "\n", ""), report.replace(sites, sites.replace('"vram"', '"oam"')), split,
                    report.replace(sites, "  " + sites), report.replace(sites, sites + "\n" + sites),
                    report.replace(dma.SUMMARY_FIELD, dma.SUMMARY_FIELD + " "),
                    "".join(line + "\n" for line in lines if not line.startswith(dma.MARKER)),
                    report.replace(f"`{data_buffer.SCHEMA}`", f"`{data_buffer.FUNCTION_SCHEMA}`")]
        tampered += [report.replace(premise + "\n", "") for premise in PREMISE_LINES]
        for index, text in enumerate(tampered):
            with self.subTest(index=index):
                self.assertNotEqual(text, report)
                self.assertFalse(self.replays(root, text))
        # the validator reads the stack floor from the selected ROM's boot code
        rom = bytearray((root / "baserom.bin").read_bytes())
        rom[0xF5] ^= 1
        (root / "baserom.bin").write_bytes(bytes(rom))
        self.assertFalse(self.replays(root, report))

    def test_a_fill_of_a_stack_address_beside_a_data_buffer_call_refuses(self):
        # natural C: the fill value is a local's address, so the fill's source word is a pointer
        # slot of the version-2 walk and the transfer would copy &zero into EWRAM
        text = HEADER.replace("extern void func_08000400(void);", "extern void func_08000400(u16 *);") + """
static inline void fill32(void *destination, u32 value, u32 control)
{
    u32 word = value;

    {
        /* plausible: DMA3 MMIO requires volatile writes and control readback. */
        volatile Dma *dma = &data_040000D4;

        dma->source = &word;
        dma->destination = destination;
        dma->control = control;
        (void)dma->control;
    }
}

void func_08000200(void)
{
    u16 zero = 0;

    fill32((void *)0x02000000, (u32)&zero, 0x85000010);
    func_08000400(&zero);
}
"""
        root = build(self.base / "pointer_word", text, leaf=bytes.fromhex("00200021002200237047"))
        code, output, report = run(root)
        self.assertNotEqual(code, 0, output)
        self.assertIsNone(report)
        self.assertIn(POINTER, output)

    def test_natural_refusals(self):
        cases = ((dict(control="0x8000C000"), CONTROL),
                 (dict(control="0x9100C000"), CONTROL),
                 (dict(first="(void *)0x06010000"), REGION),
                 (dict(first="(void *)0x03007000"), REGION),
                 # 0x200 bytes from 0x03004060 cross the stack floor 0x03003EC0
                 (dict(second="data_03003860 + 0x400"), REGION),
                 (dict(boot=False), REGION))
        for index, (values, message) in enumerate(cases):
            with self.subTest(values=values):
                code, output, report = self.natural(f"bad{index}", **values)
                self.assertNotEqual(code, 0, output)
                self.assertIsNone(report)
                self.assertIn(message, output)


if __name__ == "__main__":
    unittest.main(verbosity=2)
