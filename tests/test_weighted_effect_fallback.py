"""The real descriptor-29 owner, including the five unselected rolls."""

import copy
import importlib.util
import os
from pathlib import Path
import struct
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import match_evidence
import owner_admission_profile as owner
import signed_divmod_profile as driver
import weighted_effect_profile as effect
import weighted_effect_fallback as fallback


@unittest.skipUnless(os.environ.get("FFTA_WEIGHTED_FALLBACK_ROOT"), "set FFTA_WEIGHTED_FALLBACK_ROOT to a game fixture")
class WeightedFallback(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ["FFTA_WEIGHTED_FALLBACK_ROOT"])
        cls.result = driver.build(cls.root, fallback.ADDRESS, selector=effect.SELECTOR)
        cls.rom = (cls.root / "baserom.bin").read_bytes()
        cls.mapping = match_evidence.mapping_snapshot(cls.root)
        cls.index = owner.index_snapshot(cls.root)
        cls.objects = match_evidence.data_snapshot(cls.root)

    def test_original_elf_and_replay(self):
        manifest = self.result["manifest"]
        self.assertEqual(len(self.result["body"]), 148)
        self.assertEqual(self.result["instructions"], 63)
        self.assertEqual(manifest["dispatcher"], [0x081338BA, effect.THUNK, 29])
        self.assertEqual([(v["first"], v["last"], v["kind"]) for v in manifest["picker"]["choices"]],
                         [(0, 10, 27), (11, 35, 22), (36, 70, 35), (71, 95, 24), (96, 100, -1)])
        self.assertEqual(len(manifest["callback"]["selected_closure"]), 13)
        self.assertEqual(manifest["equipment_fallback"]["call"], 0x0812D988)
        self.assertTrue(match_evidence.report_matches(driver.render(self.result), self.root, fallback.ADDRESS))
        changed = copy.deepcopy(self.result)
        changed["manifest"]["equipment_fallback"]["target_offset"] = 0x16
        self.assertFalse(match_evidence.report_matches(driver.render(changed), self.root, fallback.ADDRESS))

    def test_original_roles_and_mutated_dependencies(self):
        manifest = self.result["manifest"]
        bindings = manifest["bindings"]
        for prev in (effect.CALLS, [[s, "func_08142950" if n == "__modsi3" else n] for s, n in fallback.CALLS]):
            with self.assertRaises(ValueError):
                effect.check_bindings(fallback.ADDRESS, {**bindings, "calls": prev})
        for pc in (0x08132394, 0x0812D91E, 0x0812D97E, fallback.WEIGHTS, effect.TABLE + 29 * 12,
                   effect.TABLE + 35 * 12, 0x081324CC, fallback.EQUIPMENT, 0x081338BA):
            with self.subTest(pc=hex(pc)), self.assertRaises(ValueError):
                image = bytearray(self.rom)
                image[pc - effect.BASE] ^= 1
                raw = bytes(image[fallback.ADDRESS-effect.BASE:fallback.ADDRESS-effect.BASE+148])
                effect.prove(raw, fallback.ADDRESS, bytes(image), self.mapping, self.index, self.objects, bindings)

    @unittest.skipUnless(importlib.util.find_spec("unicorn"), "Unicorn unavailable")
    def test_native_rolls_and_both_threshold_outcomes(self):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_CODE, UC_HOOK_MEM_WRITE
        from unicorn import arm_const as arm

        cpu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        cpu.mem_map(effect.BASE, 0x400000)
        cpu.mem_write(effect.BASE, self.rom[:0x400000])
        cpu.mem_map(0x02000000, 0x3000)
        cpu.mem_map(0x03000000, 0x8000)
        state, source, target, sp, stop = 0x02000100, 0x02000900, 0x02001800, 0x03007700, 0x08000100
        regs = [getattr(arm, f"UC_ARM_REG_R{i}") for i in range(12)]
        preserved = list(range(0x61000004, 0x6100000C))
        writes, score_calls, callbacks = [], [], []

        def entry(uc, pc, size, context):
            if pc == effect.THUNK:
                callbacks.append((uc.reg_read(regs[0]), uc.reg_read(regs[1])))
            elif pc in (effect.SCORER, fallback.EQUIPMENT):
                args = [uc.reg_read(r) for r in regs[:4]]
                outgoing = struct.unpack("<4I", uc.mem_read(uc.reg_read(arm.UC_ARM_REG_SP), 16))
                score_calls.append((pc, args, outgoing))
                uc.reg_write(regs[0], score & 0xFFFFFFFF)
                for r in regs[1:4]:
                    uc.reg_write(r, 0xDBAD0000 + r)
                uc.reg_write(arm.UC_ARM_REG_PC, uc.reg_read(arm.UC_ARM_REG_LR))

        def store(uc, access, address, width, value, context):
            if sp-16 <= address < sp-12:
                writes.append((uc.reg_read(arm.UC_ARM_REG_PC), address, width, value))

        cpu.hook_add(UC_HOOK_CODE, entry)
        cpu.hook_add(UC_HOOK_MEM_WRITE, store)
        inverse = pow(0x41C64E6D, -1, 1 << 32)
        for roll, score, blocked in ([(r, 100, False) for r in range(101)]
                                     + [(0, -1, False), (100, -1, False), (60, 100, True)]):
            with self.subTest(roll=roll, score=score, blocked=blocked):
                for obj in (state, source, target):
                    cpu.mem_write(obj, bytes(0x150))
                cpu.mem_write(state, struct.pack("<I", source))
                cpu.mem_write(state+8, struct.pack("<I", target))
                cpu.mem_write(target+0x18, b"\x34\x12")
                cpu.mem_write(target+0xE8, bytes([16 if blocked else 0]))
                cpu.mem_write(source+0xF6, b"\x80\x7e")
                cpu.mem_write(target+0xF6, b"\xfe\x7f\x81")
                cpu.mem_write(sp-16, b"\xad\xde\xab\xcd")
                cpu.mem_write(0x030034B0, struct.pack("<I", ((roll << 16) - 0x3039) * inverse & 0xffffffff))
                for reg, value in zip(regs[4:], preserved):
                    cpu.reg_write(reg, value)
                cpu.reg_write(arm.UC_ARM_REG_SP, sp)
                cpu.reg_write(arm.UC_ARM_REG_LR, stop | 1)
                cpu.reg_write(regs[0], state)
                writes.clear()
                score_calls.clear()
                callbacks.clear()
                cpu.emu_start(fallback.ADDRESS | 1, stop, count=10000)
                self.assertEqual(cpu.reg_read(arm.UC_ARM_REG_PC), stop)
                self.assertEqual(cpu.reg_read(arm.UC_ARM_REG_SP), sp)
                self.assertEqual([cpu.reg_read(r) for r in regs[4:]], preserved)
                self.assertEqual(bytes(cpu.mem_read(sp-14, 2)), b"\xab\xcd")
                self.assertEqual(struct.unpack("<H", cpu.mem_read(state+0x26, 2))[0] & 0x100,
                                 0x100 if blocked or score < 0 else 0)
                self.assertEqual(struct.unpack("<H", cpu.mem_read(target+0x18, 2))[0],
                                 1 if not blocked and roll >= 96 and score == 100 else 0x1234)
                if blocked:
                    self.assertEqual((writes, score_calls, callbacks), ([], [], []))
                elif roll >= 96:
                    self.assertEqual(writes, [(0x0812D97E, sp-16, 2, 65535)])
                    self.assertEqual([(p, a) for p, a, _ in score_calls],
                                     [(fallback.EQUIPMENT, [source, target, 2, 0])])
                    self.assertEqual(callbacks, [])
                else:
                    kind, callback = next((k, t) for last, k, t in
                                          ((10,27,0x08132268), (35,22,0x08132160),
                                           (70,35,0x081324CC), (95,24,0x081321B4)) if roll <= last)
                    self.assertEqual(writes, [(0x0812D930, sp-16, 2, kind)])
                    self.assertEqual(score_calls, [(effect.SCORER, [source, target, 0xffffff80, 0x7e],
                                                    (0xfffffffe, 0x7f, 0xffffff81, kind))])
                    self.assertEqual(callbacks, [(state, callback | 1)] if score == 100 else [])
