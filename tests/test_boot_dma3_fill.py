"""Original USA boot code, indexed callees, typed ELFs and modeled immediate DMA3."""
import copy
import os
from pathlib import Path
import struct
import sys
from types import SimpleNamespace
import unittest

TOOLS = Path(__file__).resolve().parents[1] / "tools"
sys.path.insert(0, str(TOOLS))
import boot_dma3_fill as boot
import immediate_dma_fill as dma
import match
import match_evidence as evidence
import owner_admission_profile as owner
import small_local_copy_binding_profile as typed


@unittest.skipUnless(os.environ.get("FFTA_BOOT_DMA3_ROOT"), "needs original USA ROM, indexed source and report")
class BootDma3Tests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ["FFTA_BOOT_DMA3_ROOT"]).resolve()
        cls.rom = Path(evidence.report_rom_path(cls.root)).read_bytes()
        cls.mapping = evidence.mapping_snapshot(cls.root)
        cls.index = owner.index_snapshot(cls.root)
        cls.objects = evidence.data_snapshot(cls.root)
        args = SimpleNamespace(cc=match.DEFAULT_CC, flags=match.DEFAULT_FLAGS, cpp=match.DEFAULT_CPP,
                               assembler=match.DEFAULT_AS, linker=match.DEFAULT_LD, objcopy=match.DEFAULT_OBJCOPY)
        runner = match.Runner(args.cc, root=str(cls.root))
        cls.variants = []
        for rewrite in (None, boot.strip_qualifier):
            with runner.workspace() as workspace:
                _, _, image = match.compile_object(runner, workspace, args, cls.root, boot.OWNER,
                                                   "src/08003410.c", rewrite=rewrite)
                body, bindings = owner.object_bytes(runner, workspace, args, image, boot.OWNER, cls.rom,
                    cls.mapping, cls.objects, selector=dma.SELECTOR, index=cls.index)
                linked = match.elf_image(runner.read_binary(workspace + "/f.elf"))
                cls.variants.append((image, linked, body, bindings))

    def test_source_and_saved_replay(self):
        header = (self.root / "include/ffta.h").read_bytes()
        source = (self.root / "src/08003410.c").read_text()
        self.assertEqual(boot.source_qualifier(source, header), source.index("volatile"))
        for old, new in (("0x8100C000", "0x8500C000"), ("0x05000000", "0x05000002"), ("*source = 0", "*source = 1"),
                         ("u16 zero;", "u32 zero;"), ("(void)data_040000D4.control;", ""),
                         ("extern volatile", "extern"), ("plausible:", "note:")):
            with self.subTest(new=new), self.assertRaises(ValueError):
                boot.source_qualifier(source.replace(old, new, 1), header)
        report = (self.root / "docs/match/08003410.md").read_text()
        self.assertTrue(evidence.report_matches(report, str(self.root), boot.OWNER))
        for original in ("68/68", "idle", boot.STRIPPED_SHA, "control readbacks"):
            with self.subTest(original=original):
                self.assertIn(original, report)
                self.assertFalse(evidence.report_matches(report.replace(original, "altered", 1), str(self.root), boot.OWNER))

    def test_machine_widths_order_and_two_original_bindings(self):
        for qualified, (image, linked, body, bindings) in zip((True, False), self.variants):
            boot.native(body, qualified=qualified)
            self.assertEqual(bindings, boot.required_bindings(qualified))
            if qualified:
                self.assertEqual(body, self.rom[boot.OWNER-boot.BASE:boot.OAM_INIT-boot.BASE])
            else:
                boot.check_stripped(body, bindings)
            for offset in range(0, len(body), 2):
                # Mutate both pointers, register uses, counts, widths, return and literals.
                changed = bytearray(body)
                changed[offset] ^= 4
                with self.subTest(qualified=qualified, offset=offset), self.assertRaises(ValueError):
                    boot.native(changed, qualified=qualified)
            targets = {"func_08003454": (boot.OAM_INIT, False), "data_040000D4": (boot.SAD, True)}
            for name in targets:
                for key, value in (("section", 1), ("bind", 0), ("size", 4), ("type", 3), ("value", 4)):
                    changed = copy.deepcopy(image)
                    next(row for row in changed["symbols"] if row["name"] == name)[key] = value
                    with self.subTest(original=name, key=key), self.assertRaises(ValueError):
                        owner.original_bindings(changed, boot.OWNER, self.rom, self.mapping, self.objects,
                                                selector=dma.SELECTOR, index=self.index)
                    changed = copy.deepcopy(linked)
                    next(row for row in changed["symbols"] if row["name"] == name)[key] = value
                    with self.subTest(linked=name, key=key), self.assertRaises(ValueError):
                        typed.check_linked(changed, boot.OWNER, targets)
            changed = copy.deepcopy(bindings)
            changed["data"][0][2] = 4
            if qualified:
                with self.assertRaisesRegex(ValueError, "bindings"):
                    self.verify(body, self.rom, changed)
            else:
                with self.assertRaisesRegex(ValueError, "relocation"):
                    boot.check_stripped(body, changed)

    def verify(self, body, rom, bindings):
        refinement = owner.refine(body, boot.OWNER, self.mapping)
        ins, edges, _, calls, _ = owner.graph.graph(body, boot.OWNER, refinement)
        return boot.prove(body, boot.OWNER, rom, self.mapping, self.index, self.objects,
                          ins=ins, edges=edges, calls=calls, refinement=refinement, bindings=bindings)

    def test_intervening_oam_and_boot_entry(self):
        _, _, body, bindings = self.variants[0]
        proof = self.verify(body, self.rom, bindings)
        self.assertEqual(proof["instructions"], 27)
        self.assertEqual(proof["dma_fill"]["known_boot_call"], 0x08002746)
        for site in (0x0800271A, 0x08002742, 0x08002746, 0x0800274A,
                     0x08003454, 0x08003458, 0x08003468, 0x08003476, 0x080034A8,
                     0x080034AA, 0x080034AE, 0x080034B0, 0x080034B2):
            changed = bytearray(self.rom)
            changed[site-boot.BASE] ^= 4
            with self.subTest(site=hex(site)), self.assertRaisesRegex(ValueError, "boot caller|OAM initializer"):
                self.verify(body, changed, bindings)

    def test_original_cpu_and_modeled_immediate_transfer(self):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_CODE, UC_HOOK_MEM_READ, UC_HOOK_MEM_WRITE
        from unicorn.arm_const import UC_ARM_REG_R4, UC_ARM_REG_R5, UC_ARM_REG_SP, UC_ARM_REG_LR, UC_ARM_REG_PC
        for qualified, (_, _, body, _) in zip((True, False), self.variants):
            cpu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
            stack, stop = 0x03007E00, 0x03007F00
            vram, palette, oam = 0x06000000, 0x05000000, 0x07000000
            for base, size in ((boot.BASE, 0x4000), (0x03000000, 0x8000), (0x04000000, 0x1000),
                               (vram-0x1000, 0x1A000), (palette-0x1000, 0x2000), (oam-0x1000, 0x2000)):
                cpu.mem_map(base, size)
            cpu.mem_write(boot.BASE, self.rom[:0x4000])
            cpu.mem_write(boot.OWNER, body)
            cpu.mem_write(stack-16, bytes.fromhex("3993a75c"))
            for base, length in ((vram, 0x18000), (palette, 0x400), (oam, 0x400)):
                cpu.mem_write(base-2, b"\x99" * (length+4))
            for reg, value in ((UC_ARM_REG_SP, stack), (UC_ARM_REG_LR, stop|1),
                               (UC_ARM_REG_R4, 0xAA), (UC_ARM_REG_R5, 0xBB)):
                cpu.reg_write(reg, value)
            events, local_writes, oam_writes = [], [], []
            def record(uc, kind, at, size, value, _):
                if at == stack-16:
                    local_writes.append((at, size, value))
                if oam <= at < oam+0x400:
                    oam_writes.append((at, size, value))
                if boot.SAD <= at <= boot.SAD+8:
                    events.append(("write", at, size, value))
                    if at == boot.SAD+8:
                        src, dest = struct.unpack("<II", uc.mem_read(boot.SAD, 8))
                        self.assertEqual((src, size, value >> 16), (stack-16, 4, 0x8100))
                        self.assertEqual(uc.reg_read(UC_ARM_REG_SP), src)
                        self.assertEqual(bytes(uc.mem_read(src, 4)), bytes.fromhex("0000a75c"))
                        # Only this hook supplies the physical DMA completion premise.
                        uc.mem_write(dest, bytes(uc.mem_read(src, 2)) * (value & 0xFFFF))
            def read(uc, kind, at, size, value, _):
                events.append(("read", at, size))
            def entered_oam(uc, at, size, _):
                events.append(("OAM", at))
                self.assertEqual(bytes(uc.mem_read(vram, 0x18000)), bytes(0x18000))
                self.assertEqual(bytes(uc.mem_read(palette, 0x400)), b"\x99" * 0x400)
            cpu.hook_add(UC_HOOK_MEM_WRITE, record)
            cpu.hook_add(UC_HOOK_MEM_READ, read, begin=boot.SAD, end=boot.SAD+11)
            cpu.hook_add(UC_HOOK_CODE, entered_oam, begin=boot.OAM_INIT, end=boot.OAM_INIT)
            cpu.emu_start(boot.OWNER|1, stop, count=2000)
            self.assertEqual((cpu.reg_read(UC_ARM_REG_PC), cpu.reg_read(UC_ARM_REG_SP),
                              cpu.reg_read(UC_ARM_REG_R4), cpu.reg_read(UC_ARM_REG_R5)), (stop, stack, 0xAA, 0xBB))
            expected = []
            for dest, control in ((vram, 0x8100C000), (palette, 0x81000200)):
                if dest == palette:
                    expected.append(("OAM", boot.OAM_INIT))
                expected += [("write", boot.SAD, 4, stack-16), ("write", boot.SAD+4, 4, dest),
                             ("write", boot.SAD+8, 4, control)]
                if qualified:
                    expected.append(("read", boot.SAD+8, 4))
            self.assertEqual(events, expected)
            self.assertEqual(local_writes, [(stack-16, 2, 0)] * 2)
            matrix = [0x200, 0, 0, 0x100, 0x200, 0, 0, 0, 0x200, 0, 0, 0, 0x200, 0, 0, 0x100]
            self.assertEqual(oam_writes, [(oam+2*i, 2, value) for i, value in enumerate(matrix*32)])
            for base, expected in ((vram, bytes(0x18000)), (palette, bytes(0x400)), (oam, struct.pack("<16H", *matrix)*32)):
                self.assertEqual(bytes(cpu.mem_read(base-2, len(expected)+4)), b"\x99\x99" + expected + b"\x99\x99")


if __name__ == "__main__":
    unittest.main()
