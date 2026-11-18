"""Original ELF, nested halfword output and actual descriptor dispatch of effect 30."""

import copy
import importlib.util
import os
from pathlib import Path
import struct
import sys
import unittest

TOOLS = Path(__file__).resolve().parents[1] / "tools"
sys.path.insert(0, str(TOOLS))
import match
import match_evidence
import owner_admission_profile as owner
import signed_divmod_profile as driver
import weighted_effect_profile as effect


class BindingBoundaries(unittest.TestCase):
    def test_neighbour_and_alternate_compiler_names_are_excluded(self):
        good = dict(calls=effect.CALLS, data=effect.DATA, functions=[], switches=[])
        with self.assertRaises(ValueError):
            effect.check_bindings(0x0813233C, good, effect.TARGETS)
        for role, position, value in (
            ("calls", 3, [0x34, "func_08142950"]),
            ("calls", 4, [0x54, "_call_via_r2"]),
            ("data", 0, [0x60, "data_083A87B0", 4]),
        ):
            changed = copy.deepcopy(good)
            changed[role][position] = value
            with self.subTest(value=value), self.assertRaises(ValueError):
                effect.check_bindings(effect.ADDRESS, changed, effect.TARGETS)


@unittest.skipUnless(
    os.environ.get("FFTA_WEIGHTED_EFFECT_ROOT"),
    "set FFTA_WEIGHTED_EFFECT_ROOT to a USA game fixture",
)
class WeightedEffect(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ["FFTA_WEIGHTED_EFFECT_ROOT"])
        cls.result = driver.build(cls.root, effect.ADDRESS, selector=effect.SELECTOR)
        cls.rom = (cls.root / "baserom.bin").read_bytes()
        cls.mapping = match_evidence.mapping_snapshot(cls.root)
        cls.index = owner.index_snapshot(cls.root)
        cls.objects = match_evidence.data_snapshot(cls.root)
        cls.bindings = cls.result["manifest"]["bindings"]

    def test_positive_source_report_and_tampered_replay(self):
        r = self.result
        self.assertEqual(len(r["body"]), 128)
        self.assertEqual(r["instructions"], 53)
        self.assertTrue(
            match_evidence.report_matches(
                driver.render(r), str(self.root), effect.ADDRESS
            )
        )
        manifest = r["manifest"]
        self.assertEqual(
            [(item["first"], item["last"]) for item in manifest["picker"]["choices"]],
            [(0, 15), (16, 40), (41, 75), (76, 100)],
        )
        self.assertEqual(len(manifest["callback"]["selected_closure"]), 16)
        changed = copy.deepcopy(r)
        changed["manifest"]["picker"]["output"]["written"][1] += 2
        self.assertFalse(
            match_evidence.report_matches(
                driver.render(changed), str(self.root), effect.ADDRESS
            )
        )

    def test_original_binding_kind_addend_and_symbol_types(self):
        original = match.elf_image(self.result["original_elf"])

        def check(image):
            return owner.original_bindings(
                image,
                effect.ADDRESS,
                self.rom,
                self.mapping,
                self.objects,
                selector=effect.SELECTOR,
                index=self.index,
            )

        self.assertEqual(check(original)[0], self.bindings)
        for alteration in (
            "wrong-original-type",
            "data-addend",
            "changed-call-addend",
            "relocation-kind",
            "symbol-size",
        ):
            image = copy.deepcopy(original)
            if alteration == "wrong-original-type":
                image["type"] = 2
            elif alteration in ("data-addend", "changed-call-addend"):
                code = bytearray(image["text"])
                if alteration == "data-addend":
                    struct.pack_into("<I", code, 0x60, 4)
                else:
                    code[0x36] ^= 1
                image["text"] = bytes(code)
            elif alteration == "relocation-kind":
                section = next(iter(image["relocations"]))
                raw = bytearray(image["section_data"][section])
                raw[4] = 2
                image["section_data"][section] = bytes(raw)
            else:
                symbol = next(
                    s for s in image["symbols"] if s["name"] == "_call_via_r1"
                )
                symbol["size"] = 4
            with self.subTest(alteration=alteration), self.assertRaises(ValueError):
                check(image)

    def test_wrong_owner_output_weight_descriptor_and_nested_dependencies(self):
        def reject(rom, address):
            raw = rom[effect.ADDRESS - effect.BASE : effect.ADDRESS - effect.BASE + 128]
            with self.subTest(address=hex(address)), self.assertRaises(ValueError):
                effect.prove(
                    raw,
                    effect.ADDRESS,
                    rom,
                    self.mapping,
                    self.index,
                    self.objects,
                    self.bindings,
                )

        # Original BL, local-output argument, chance branch, descriptor stride,
        # caller divisor, picker store width, table weight, live descriptor word,
        # nested scorer's entry-stack read, and a transitive callback body.
        for pc in (
            0x081323EA,
            0x081323E8,
            0x0813240E,
            0x0813241C,
            0x0813242C,
            0x0812D7B6,
            effect.WEIGHTS,
            effect.TABLE + 51 * 12,
            0x0812D1EC,
            0x080CE430,
        ):
            image = bytearray(self.rom)
            image[pc - effect.BASE] ^= 1
            reject(bytes(image), pc)
        with self.assertRaises(ValueError):
            effect.prove(
                self.result["body"],
                effect.ADDRESS,
                self.rom,
                self.mapping,
                self.index.replace(
                    b"081323D0 08132450   128  53", b"081323D0 08132450   128  54"
                ),
                self.objects,
                self.bindings,
            )

    @unittest.skipUnless(
        importlib.util.find_spec("unicorn"), "unicorn ARM CPU oracle unavailable"
    )
    def test_all_101_actual_rng_outcomes_and_callback_targets(self):
        from unicorn import (
            Uc,
            UC_ARCH_ARM,
            UC_MODE_THUMB,
            UC_HOOK_CODE,
            UC_HOOK_MEM_WRITE,
        )
        from unicorn import arm_const as arm

        cpu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        cpu.mem_map(effect.BASE, 0x400000)
        cpu.mem_write(effect.BASE, self.rom[:0x400000])
        cpu.mem_map(0x02000000, 0x3000)
        cpu.mem_map(0x03000000, 0x8000)
        obj, source, unit, sp, stop = (
            0x02000100,
            0x02000900,
            0x02001800,
            0x03007700,
            0x08000100,
        )
        regs = [getattr(arm, f"UC_ARM_REG_R{i}") for i in range(12)]
        saved = [0x51000000 + i for i in range(8)]
        observed = []
        writes = []
        scorer = []
        threshold = 100

        def at(uc, pc, size, _):
            if pc == effect.SCORER:
                args = [uc.reg_read(r) for r in regs[:4]]
                words = struct.unpack(
                    "<4I", uc.mem_read(uc.reg_read(arm.UC_ARM_REG_SP), 16)
                )
                scorer.append((args, words))
                uc.reg_write(regs[0], threshold & 0xFFFFFFFF)
                # The scalar result is opaque; its four volatile registers carry
                # no live owner-local pointer or preserved result after the call.
                for r in regs[1:4]:
                    uc.reg_write(r, 0x79100000 + r)
                uc.reg_write(arm.UC_ARM_REG_PC, uc.reg_read(arm.UC_ARM_REG_LR))
            elif pc == effect.THUNK:
                observed.append((uc.reg_read(regs[0]), uc.reg_read(regs[1])))

        def write(uc, access, address, size, value, _):
            if sp - 16 <= address < sp - 12:
                writes.append((uc.reg_read(arm.UC_ARM_REG_PC), address, size, value))

        cpu.hook_add(UC_HOOK_CODE, at)
        cpu.hook_add(UC_HOOK_MEM_WRITE, write)
        inverse = pow(0x41C64E6D, -1, 1 << 32)
        for roll, threshold, blocked in [(n, 100, False) for n in range(101)] + [
            (35, -1, False),
            (35, 100, True),
        ]:
            cpu.mem_write(obj, bytes(0x50))
            cpu.mem_write(source, bytes(0x150))
            cpu.mem_write(unit, bytes(0x150))
            cpu.mem_write(source + 0xF6, b"\x80\x7e")
            cpu.mem_write(unit + 0xF6, b"\xfe\x7f\x81")
            cpu.mem_write(obj, struct.pack("<I", source))
            cpu.mem_write(obj + 8, struct.pack("<I", unit))
            cpu.mem_write(unit + 0xE8, bytes([16 if blocked else 0]))
            cpu.mem_write(sp - 16, b"\xee\xee\xab\xcd")
            seed = ((roll << 16) - 0x3039) * inverse & 0xFFFFFFFF
            cpu.mem_write(0x030034B0, struct.pack("<I", seed))
            for reg, value in zip(regs[4:], saved):
                cpu.reg_write(reg, value)
            cpu.reg_write(arm.UC_ARM_REG_SP, sp)
            cpu.reg_write(arm.UC_ARM_REG_LR, stop | 1)
            cpu.reg_write(regs[0], obj)
            observed.clear()
            writes.clear()
            scorer.clear()
            cpu.emu_start(effect.ADDRESS | 1, stop, count=10000)
            self.assertEqual(cpu.reg_read(arm.UC_ARM_REG_PC), stop)
            self.assertEqual(cpu.reg_read(arm.UC_ARM_REG_SP), sp)
            self.assertEqual([cpu.reg_read(r) for r in regs[4:]], saved)
            self.assertEqual(bytes(cpu.mem_read(sp - 14, 2)), b"\xab\xcd")
            choice = next(
                row
                for row in self.result["manifest"]["picker"]["choices"]
                if row["first"] <= roll <= row["last"]
            )
            if blocked:
                self.assertEqual(scorer, [])
                self.assertEqual(writes, [])
            else:
                self.assertEqual(
                    scorer,
                    [
                        (
                            [source, unit, 0xFFFFFF80, 0x7E],
                            (0xFFFFFFFE, 0x7F, 0xFFFFFF81, choice["kind"]),
                        )
                    ],
                )
                self.assertEqual(writes, [(0x0812D7B6, sp - 16, 2, choice["kind"])])
            self.assertEqual(
                observed,
                [(obj, choice["target"] | 1)]
                if threshold == 100 and not blocked
                else [],
            )
            self.assertEqual(
                bool(struct.unpack("<H", cpu.mem_read(obj + 0x26, 2))[0] & 0x100),
                threshold < 0 or blocked,
            )
