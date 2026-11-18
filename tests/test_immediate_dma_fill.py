"""Verify native register programming, local lifetime, channel selection and full evidence."""
import copy
import json
import os
from pathlib import Path
import struct
import subprocess
import sys
import unittest

TOOLS = Path(__file__).resolve().parents[1] / "tools"
sys.path.insert(0, str(TOOLS))
import immediate_dma_fill as dma
import match_evidence
import owner_admission_profile as owner


@unittest.skipUnless(os.environ.get("FFTA_DMA_FILL_ROOT"), "requires USA ROM, source and checked index")
class NativeFill(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ["FFTA_DMA_FILL_ROOT"]).resolve()
        cls.rom = (cls.root/"baserom.bin").read_bytes()
        cls.mapping = match_evidence.mapping_snapshot(cls.root)
        cls.index = (cls.root/"symbols/functions.txt").read_bytes()
        cls.objects = match_evidence.data_snapshot(cls.root)
        cls.address = dma.WORD
        cls.offset, cls.size = cls.address - dma.BASE, 132
        cls.body = cls.rom[cls.offset:cls.offset+cls.size]
        cls.report = (cls.root/f"docs/match/{cls.address:08X}.md").read_text()
        marker = "* owner runtime evidence: `"
        cls.evidence = json.loads(next(row[len(marker):-1] for row in cls.report.splitlines() if row.startswith(marker)))
        cls.bindings = cls.evidence["manifest"]["bindings"]

    def verify(self, body, rom=None, bindings=None):
        if rom is None:
            image = bytearray(self.rom)
            image[self.offset:self.offset+self.size] = body
            rom = bytes(image)
        ref = owner.refine(body, self.address, self.mapping)
        ins, edges, _, calls, _ = owner.graph.graph(body, self.address, ref)
        return dma.prove(body, self.address, rom, self.mapping, self.index, self.objects,
            ins=ins, edges=edges, calls=calls, refinement=ref, bindings=bindings or self.bindings)

    def test_canonical_positive_and_report_negatives(self):
        self.assertTrue(match_evidence.report_matches(self.report, str(self.root), self.address))
        self.assertIn("before re-enabling", self.report)
        for marker in ("immediate-dma-stack-fill-v1", "before re-enabling", "132/132"):
            self.assertFalse(match_evidence.report_matches(self.report.replace(marker, "altered", 1),
                                                          str(self.root), self.address))
        command = [sys.executable, str(TOOLS/"match.py"), "--root", str(self.root), "--no-write",
                   f"{self.address:08X}"]
        default = subprocess.run(command, capture_output=True, text=True)
        self.assertNotEqual(default.returncode, 0)
        self.assertIn("stack-address materialization", default.stdout + default.stderr)

    def test_changed_machine_semantics_and_data_cells(self):
        proof = self.verify(self.body)
        self.assertEqual(proof["instructions"], 57)
        # Stacked source, count narrowing, physical comparisons, lock and state
        # predicates, progression, fallback, register writes, return and pop.
        for offset in (0, 2, 4, 8, 10, 0x0C, 0x12, 0x16, 0x18, 0x1E,
                       0x2C, 0x30, 0x32, 0x38, 0x3A, 0x3C, 0x40, 0x44, 0x48,
                       0x50, 0x54, 0x58, 0x5C, 0x5E, 0x62, 0x64, 0x6A, 0x6C,
                       0x6E, 0x70, 0x72, 0x74, 0x76, 0x7C, 0x7E, 0x80):
            mutated = bytearray(self.body)
            mutated[offset] ^= 1
            with self.subTest(offset=hex(offset)), self.assertRaises(ValueError):
                self.verify(bytes(mutated))
        for index in range(4):
            mutated = bytearray(self.rom)
            mutated[dma.TABLE - dma.BASE + index*4] ^= 4
            with self.assertRaisesRegex(ValueError, "register blocks"):
                self.verify(self.body, rom=mutated)
        for i in range(3):
            wrong = copy.deepcopy(self.bindings)
            wrong["data"][i][2] = 4
            with self.assertRaisesRegex(ValueError, "original named data"):
                self.verify(self.body, bindings=wrong)

    def test_qualifier_is_only_the_native_register_block(self):
        path = f"src/{self.address:08X}.c"
        source = (self.root / path).read_text()
        args = (self.root, self.root, ({path, "include/ffta.h"}, []), self.address,
                json.loads(self.objects))
        self.assertEqual(dma.qualifier(source, *args), source.index("volatile"))
        for old, new in (("[channel];", "[channel + 4];"), ("channel < 4", "channel <= 4"),
                         ("registers->source = &value", "registers->source = destination"),
                         ("volatile DmaRegisters", "volatile volatile DmaRegisters"),
                         ("registers->control", "registers->destination"), ("plausible:", "note:")):
            with self.subTest(new=new), self.assertRaises(ValueError):
                dma.qualifier(source.replace(old, new), *args)

    def test_original_cpu_register_trace(self):
        try:
            from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_MEM_WRITE
            from unicorn.arm_const import UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2
            from unicorn.arm_const import UC_ARM_REG_R4, UC_ARM_REG_R5, UC_ARM_REG_R6
            from unicorn.arm_const import UC_ARM_REG_SP, UC_ARM_REG_LR, UC_ARM_REG_PC
        except ImportError:
            self.skipTest("independent Thumb execution needs Unicorn")

        value, stack, stop = 0xA51BCDEF, 0x03007E00, 0x03007F00
        for channel, count, dest in ((0, 0, 0x02002000), (1, 0x4000, 0x02002000),
                                     (2, 0xCAFEFFFF, 0x02002000), (3, 0, 0x02002000),
                                     (3, 3, 0x08001000), (-1, 3, 0x02002000)):
            cpu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
            for base, size in ((dma.BASE, 0x400000), (0x03000000, 0x8000), (0x04000000, 0x1000)):
                cpu.mem_map(base, size)
            cpu.mem_write(dma.BASE, self.rom[:0x400000])
            for i in range(4):
                cpu.mem_write(dma.LOCKS + 2*i, struct.pack("<H", int(i != channel and i % 2 == 0)))
                cpu.mem_write(dma.STATES + 16*i + 12, bytes([2 if i == channel else 3]))
            writes = []
            def capture(uc, kind, address, width, data, user):
                if 0x040000B0 <= address <= 0x040000DC:
                    writes.append((address, width, data))
                    if len(writes) == 3:
                        self.assertEqual(uc.mem_read(stack-20, 4), struct.pack("<I", value))
                        self.assertEqual(uc.reg_read(UC_ARM_REG_SP), stack-20)
            cpu.hook_add(UC_HOOK_MEM_WRITE, capture)
            for reg, data in ((UC_ARM_REG_SP, stack), (UC_ARM_REG_LR, stop | 1),
                              (UC_ARM_REG_R0, value), (UC_ARM_REG_R1, dest), (UC_ARM_REG_R2, count),
                              (UC_ARM_REG_R4, 4), (UC_ARM_REG_R5, 5), (UC_ARM_REG_R6, 6)):
                cpu.reg_write(reg, data)
            cpu.emu_start(self.address | 1, stop, count=200)
            self.assertEqual(cpu.reg_read(UC_ARM_REG_PC), stop)
            self.assertEqual(cpu.reg_read(UC_ARM_REG_SP), stack)
            self.assertEqual(tuple(cpu.reg_read(r) for r in (UC_ARM_REG_R4, UC_ARM_REG_R5, UC_ARM_REG_R6)), (4, 5, 6))
            self.assertEqual(cpu.reg_read(UC_ARM_REG_R0), channel & 0xFFFFFFFF)
            if channel < 0:
                self.assertEqual(writes, [])
            else:
                sad = dma.REGISTERS[channel]
                self.assertEqual(writes, [(sad, 4, stack-20), (sad+4, 4, dest),
                                           (sad+8, 4, 0x85000000 | (count & 0xFFFF))])
                # CPU traces only establish programming. The physical transfer
                # length and synchronous completion are GBA hardware premises.


if __name__ == "__main__":
    unittest.main()
