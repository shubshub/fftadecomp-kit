"""Original compiler outputs, search induction, linked evidence and named BLDALPHA writes."""
import copy
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

TOOLS = Path(__file__).resolve().parents[1] / "tools"
sys.path.insert(0, str(TOOLS))
import blend_keyframe_loop as blend
import match
import match_evidence
import volatile_semantics as vs


@unittest.skipUnless(os.environ.get("FFTA_BLEND_KEYFRAME_ROOT"), "needs indexed USA ROM/keyframe callback")
class KeyframeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        game = Path(os.environ["FFTA_BLEND_KEYFRAME_ROOT"]).resolve()
        cls.scratch = tempfile.TemporaryDirectory()
        cls.addClassCleanup(cls.scratch.cleanup)
        cls.root = Path(cls.scratch.name)
        for name in ("config", "symbols", "include", "baserom.bin"):
            (cls.root / name).symlink_to((game / name).resolve())
        (cls.root / "src").mkdir()
        source = game / "src/08006720.c"
        if not source.is_file():
            source = game / "Parked/08006720/08006720.c"
        cls.source = cls.root / "src/08006720.c"
        cls.source.write_bytes(source.read_bytes())
        with patch.object(blend, "record", wraps=blend.record) as checked:
            cls.records = match.allowlisted_volatile_semantics(cls.root, blend.OWNER)
        cls.assemblies, cls.images, cls.preprocessed, cls.entry, cls.interfaces, cls.rom, cls.location = checked.call_args.args
        result = subprocess.run([sys.executable, str(TOOLS / "match.py"), "--root", str(cls.root),
            "--addressed-signed-runtime-profile", "compiler-signed-runtime-data-v1", "08006720"],
            capture_output=True, text=True)
        if result.returncode or "verdict MATCH - byte identical" not in result.stdout:
            raise AssertionError(result.stdout + result.stderr)
        cls.report = (cls.root / "docs/match/08006720.md").read_text()

    def test_canonical_report_and_replay(self):
        self.assertIn("**MATCH - byte identical** - 344/344 bytes", self.report)
        self.assertIn("agrees on 16 paths", self.report)
        self.assertIn("read-modify-write loads at [78, 83, 126, 140]", self.report)
        self.assertIn("Keyframe search induction", self.report)
        self.assertTrue(match_evidence.report_matches(self.report, str(self.root), blend.OWNER))

    def test_replay_refuses_reworded_relocated_and_shortened_reports(self):
        for old, new in [
                ("Keyframe search induction", "Keyframe search bounded sampling"),
                ("03000940", "03000942"), ("compiler-signed-runtime-data-v1", "compiler-signed-runtime-v1"),
                ("344/344", "342/342")]:
            with self.subTest(old=old):
                changed = self.report.replace(old, new, 1)
                self.assertNotEqual(self.report, changed)
                self.assertFalse(match_evidence.report_matches(changed, str(self.root), blend.OWNER))

    def test_symmetric_extent_forgery_and_changed_live_source_are_refused(self):
        body = self.rom[0x6720:0x6878].hex()
        changed = self.report.replace(body, body + "0000").replace("(344 bytes)", "(346 bytes)")
        changed = changed.replace("344/344 bytes", "346/346 bytes")
        self.assertFalse(match_evidence.report_matches(changed, str(self.root), blend.OWNER))
        source = self.source.read_text()
        try:
            mutated = source.replace(".bldalpha_hi =", ".bldalpha_lo =", 1)
            self.assertNotEqual(mutated, source)
            self.source.write_text(mutated)
            self.assertFalse(match_evidence.report_matches(self.report, str(self.root), blend.OWNER))
        finally:
            self.source.write_text(source)

    def test_original_backedge_register_and_effect_checks(self):
        for index, assembly in enumerate(self.assemblies):
            stripped = index == 1
            iv = "r4" if stripped else "r3"
            self.assertIn(f"mov {iv}, ip", blend.finite_iteration(assembly, stripped))
            for old, new in [
                    (f"mov\t{iv}, #0", f"mov\t{iv}, #1"),
                    (f"add\t{iv}, {iv}, #1", f"add\t{iv}, {iv}, #2"),
                    (f"lsl\tr1, {iv}, #2", f"lsl\tr1, {iv}, #1"),
                    ("blt\t.L10", "bgt\t.L10"), ("bge\t.L11", "bgt\t.L11"),
                    ("beq\t.L7", "beq\t.L8"),
                    (".L10:\n", ".L10:\n\tstrb\tr0, [r7]\n"),
                    (".L9:\n", ".L9:\n\tstrb\tr2, [r7]\n"),
                    (".L9:\n", ".L9:\n\tmov\tr0, ip\n"),
                    ("\tldrsh\tr2,", "\tldrh\tr2,"),
                    (".L4:\n", ".L4:\n\tstrb\tr0, [r7]\n")]:
                with self.subTest(variant=index, old=old, new=new):
                    altered = assembly.replace(old, new, 1)
                    self.assertNotEqual(assembly, altered)
                    with self.assertRaises(ValueError):
                        blend.finite_iteration(altered, stripped)

    def test_counterfactuals_are_real_native_objects_with_typed_relocations(self):
        for i, image in enumerate(self.images):
            blend.verify_object(image, i)
            for variant in ("text", "object", "section", "relocation", "symbol"):
                wrong = copy.deepcopy(image)
                if variant == "text":
                    body = bytearray(wrong["text"])
                    body[16] ^= 2
                    wrong["text"] = bytes(body)
                elif variant == "object":
                    wrong["type"] = 2
                elif variant == "section":
                    section = list(wrong["sections"][wrong["text_index"]])
                    section[2] |= 1
                    wrong["sections"][wrong["text_index"]] = tuple(section)
                elif variant == "symbol":
                    next(s for s in wrong["symbols"] if s["name"] == blend.SYMBOL)["value"] = 1
                else:
                    pos = wrong["relocations"][0]
                    data = bytearray(wrong["section_data"][pos])
                    data[4] = 10
                    wrong["section_data"][pos] = bytes(data)
                with self.subTest(i=i, variant=variant), self.assertRaises(ValueError):
                    blend.verify_object(wrong, i)
        with self.assertRaises(ValueError):
            blend.verify_object(self.images[0], 2)

    def test_original_verifier_bound_and_named_member_preserved(self):
        a, b, c = self.assemblies
        d = self.entry["declaration"]
        with self.assertRaisesRegex(ValueError, "more than 32 unknown branch"):
            vs.compare(a, b, self.preprocessed, blend.SYMBOL, d, c, self.interfaces)
        # Undisplaced counterfactual cannot witness accesses through named members.
        cut_a, cut_b = blend.finite_iteration(a, False), blend.finite_iteration(b, True)
        with self.assertRaises(ValueError):
            vs.compare(cut_a, cut_b, self.preprocessed, blend.SYMBOL, d, cut_a, self.interfaces)

    def test_original_scheduler_reaches_both_named_stores_and_dma_configuration(self):
        # Optional independent execution. The actual verifier has no emulator dependency.
        try:
            from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_CODE, UC_HOOK_MEM_WRITE
            from unicorn.arm_const import UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2
            from unicorn.arm_const import UC_ARM_REG_SP, UC_ARM_REG_LR, UC_ARM_REG_PC
        except ImportError:
            self.skipTest("requires Unicorn for the supplemental original-ROM execution")

        cpu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        for address, size in ((0x08000000, 0x400000), (0x02000000, 0x40000),
                              (0x03000000, 0x8000), (0x04000000, 0x1000)):
            cpu.mem_map(address, size)
        cpu.mem_write(0x08000000, self.rom[:0x400000])
        # Exactly the range copied at boot by 08002768.
        cpu.mem_write(0x03005E78, self.rom[0xA38A2C:0xA38ADC])
        manager, heap, records = 0x02001000, 0x02002000, 0x02010000
        stop = 0x03007F00
        states, stores, divisions, dma, outputs = [], [], [], [], []

        def word(address, value):
            cpu.mem_write(address, value.to_bytes(4, "little"))

        def read(address, width):
            return int.from_bytes(cpu.mem_read(address, width), "little")

        def trace(uc, pc, size, data):
            if pc == blend.OWNER:
                states.append((read(uc.reg_read(UC_ARM_REG_R1), 2),
                               uc.reg_read(UC_ARM_REG_R0), uc.reg_read(UC_ARM_REG_R2)))
            if pc == 0x081426B8:
                divisions.append(pc)
            if pc == 0x08000744:
                # The host emulator has no GBA DMA controller. Acknowledge the
                # recorded control write at its first real polling read.
                word(0x040000B8, 0)

        def write(uc, kind, address, size, value, data):
            if address in (0x0300098C, 0x0300098D):
                stores.append((uc.reg_read(UC_ARM_REG_PC), address, size))
            if 0x040000B0 <= address <= 0x040000B8:
                dma.append((address, size, value))

        def call(address, *args):
            cpu.reg_write(UC_ARM_REG_SP, 0x03007E00)
            cpu.reg_write(UC_ARM_REG_LR, stop | 1)
            for reg, value in zip((UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2), args):
                cpu.reg_write(reg, value)
            cpu.emu_start(address | 1, stop, count=100000)
            self.assertEqual(cpu.reg_read(UC_ARM_REG_PC), stop)
            return cpu.reg_read(UC_ARM_REG_R0)

        cpu.hook_add(UC_HOOK_CODE, trace)
        cpu.hook_add(UC_HOOK_MEM_WRITE, write)
        cpu.mem_write(records, bytes((0, 0, 0, 18, 2, 0, 4, 14, 6, 0, 16, 2)))
        self.assertEqual(call(0x080070C8, heap, 0x1000), heap)
        word(manager, heap)
        word(0x02008FF0, manager)
        task = call(0x08006920, records, 3, 0)
        self.assertEqual((read(task, 4), read(task + 24, 4), read(task + 28, 4)),
                         (blend.OWNER | 1, records, 3))
        for _ in range(8):
            call(0x08005A24, manager)
            outputs.append(tuple(cpu.mem_read(0x0300098C, 2)))
        self.assertEqual(states, [(0, task, task + 24)] + [(0x100, task, task + 24)] * 7)
        self.assertEqual(outputs, [(0, 0), (0, 18), (2, 16), (4, 14), (7, 11),
                                   (10, 8), (13, 5), (16, 2)])
        self.assertEqual((read(task + 34, 2), read(task + 20, 2), len(divisions)), (7, 2, 12))
        self.assertEqual(set(stores), {(0x080067BC, 0x0300098C, 1), (0x080067C6, 0x0300098D, 1),
                                       (0x08006824, 0x0300098C, 1), (0x08006842, 0x0300098D, 1)})
        call(0x08000718)
        self.assertEqual(dma, [(0x040000B0, 4, 0x03000942), (0x040000B4, 4, 0x04000008),
                               (0x040000B8, 4, 0x80000027)])

    def test_rom_installer_scheduler_and_display_upload_identity(self):
        for start, end, digest in blend.ROM_PARTS:
            with self.subTest(start=start), self.assertRaisesRegex(ValueError, "USA callback"):
                changed = bytearray(self.rom)
                changed[start] ^= 1
                blend.record(self.assemblies, self.images, self.preprocessed, self.entry, self.interfaces,
                             changed, self.location)
        changed = bytearray(self.rom)
        changed[0x142250] ^= 8
        with self.assertRaisesRegex(ValueError, "callback veneer"):
            blend.record(self.assemblies, self.images, self.preprocessed, self.entry, self.interfaces,
                         changed, self.location)
        with self.assertRaisesRegex(ValueError, "shadow binding"):
            blend.record(self.assemblies, self.images, self.preprocessed, self.entry, self.interfaces,
                         self.rom, self.location + 2)


if __name__ == "__main__":
    unittest.main()
