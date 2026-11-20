"""Native nested occupant search, installed shadow setter, ABI, and admission refusals."""
import copy
import json
import os
from pathlib import Path
import struct
import shutil
import tempfile
import sys
import unittest
from types import SimpleNamespace

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import actor_sprite_shadow as shadow
import match
import match_evidence
import named_data_buffer_profile as buffers
import owner_admission_profile as owner
import test_scene_sprite_visitor as scene_test
from rompath import rom_path

BASE, SP = scene_test.BASE, scene_test.SP
SCENE, LIST, NODE, ACTOR = scene_test.SCENE, scene_test.LIST, scene_test.NODE, scene_test.VALUE
SPRITE, SHADOW = scene_test.SPRITES
OTHER, UNIT, OTHER_UNIT = 0x02005200, 0x02005400, 0x02005600


class ShadowFrameTests(unittest.TestCase):
    def test_wrong_frame_pointer_or_spill_rejected(self):
        r2 = match.ARM_REG_R0 + 2
        for args in [({r2: -24}, [0]*7, {}, {}),
                     ({r2: -28}, [0]*6, {}, {}),
                     ({r2: -28}, [0]*7, {0: -28}, {}),
                     ({r2: -28}, [0]*7, {}, {0: -28}),
                     ({r2: -28, r2-1: -20}, [0]*7, {}, {})]:
            with self.subTest(args=args), self.assertRaisesRegex(ValueError, "12-byte private search"):
                shadow.tile_lookup(SimpleNamespace(active=[]), *args)


@unittest.skipUnless(os.getenv("FFTA_ACTOR_SHADOW_ROOT"), "requires the native USA ROM and corrected owner indexes")
class ActorShadowTests(unittest.TestCase):
    machine = scene_test.SceneSpriteTests.machine
    run_to = scene_test.SceneSpriteTests.run_to
    call = scene_test.SceneSpriteTests.call
    install = scene_test.SceneSpriteTests.install

    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ["FFTA_ACTOR_SHADOW_ROOT"])
        cls.rom = Path(rom_path(cls.root)).read_bytes()
        cls.mapping = match_evidence.mapping_snapshot(cls.root)
        cls.index = (cls.root / "symbols/functions.txt").read_bytes()
        cls.objects = match_evidence.data_snapshot(cls.root)

    def verify(self, rom, bindings, mapping=None, index=None):
        return owner.verify(data=rom[shadow.OWNER-BASE:shadow.OWNER-BASE+280], address=shadow.OWNER,
                            rom=rom, mapping=mapping or self.mapping, index=index or self.index,
                            objects=self.objects, bindings=bindings, selector=buffers.THUNK_ROOT_SCRATCH_SELECTOR)

    def test_evidence_replay_and_mutations(self):
        manifest, _ = self.verify(self.rom, shadow.BINDINGS)
        # The code and both literal words account for the entire ELF symbol.
        receipt = manifest["proof"]["buffers"]["actor_sprite_shadow"]
        self.assertEqual([receipt["partition"][k] for k in ("code_bytes", "alignment_bytes", "literal_and_table_bytes")],
                         [270, 2, 8])
        self.assertEqual(receipt["setter"]["target"]["entry"], 0x03006BBD)
        self.assertFalse(receipt["setter"]["image"]["installed_identity_proved"])
        # Each mutation changes the authentic dependency in a complete synthetic ROM.
        # The leaf store and return, literal Thumb bit, CpuSet count, phase guard, scoped
        # callback store, iterator thunk and caller adapter are independent evidence.
        for address in (0x08A39770, 0x08A39772, 0x08394040, 0x0808F758, 0x08023F16,
                        0x0809ABD8, 0x0814225C, 0x0814225E, 0x0809ABF4, 0x08098008, 0x08097FA8):
            with self.subTest(address=hex(address)):
                rom = bytearray(self.rom)
                rom[address-BASE] ^= 1
                with self.assertRaises(ValueError):
                    self.verify(bytes(rom), shadow.BINDINGS)
        bindings = copy.deepcopy(shadow.BINDINGS)
        bindings["functions"][0][1] = "func_0809ABE8"
        with self.assertRaises(ValueError):
            self.verify(self.rom, bindings)
        # Equal but false counts in both ownership indexes must still fail.
        entries = json.loads(self.mapping)
        for entry in entries:
            if int(entry["rom"], 16) == shadow.OWNER:
                entry["instrs"] = 140
        index = self.index.replace(b"08097F04 0809801C   280 130 ", b"08097F04 0809801C   280 140 ")
        self.assertNotEqual(index, self.index)
        with self.assertRaisesRegex(ValueError, "owner/count"):
            self.verify(self.rom, shadow.BINDINGS, json.dumps(entries).encode(), index)

    def test_source_callback_result_and_signed_coordinates(self):
        shadow.check_source(self.root)
        (self.root/"build").mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(dir=self.root/"build") as scratch:
            fixture = Path(scratch)
            (fixture/"src").mkdir()
            (fixture/"include").mkdir()
            source = fixture/"src/08097F04.c"
            header = fixture/"include/movement_tile.h"
            for path in [source, header, fixture/"include/object_list.h", fixture/"include/ffta.h"]:
                shutil.copyfile(self.root/path.relative_to(fixture), path)
            original = source.read_text()
            source.write_text(original.replace("u32 func_08097F04", "u8 func_08097F04"))
            with self.assertRaisesRegex(ValueError, "source or shared tile declarations"):
                shadow.check_source(fixture)
            source.write_text(original)
            header.write_text(header.read_text().replace("    s8 x;", "    u8 x;"))
            with self.assertRaisesRegex(ValueError, "source or shared tile declarations"):
                shadow.check_source(fixture)

    def exercise(self, occupants, flags=0, scene_flags=0, kind=1, animation=1):
        from unicorn import UC_HOOK_CODE, UC_HOOK_MEM_WRITE
        from unicorn.arm_const import UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R4

        uc = self.machine()
        self.install(uc)
        word = lambda address, value: uc.mem_write(address, struct.pack("<I", value))
        word(SCENE+0x10, LIST)
        word(SCENE+0x24, scene_flags)
        word(ACTOR, UNIT)
        word(ACTOR+0x30, flags)
        word(ACTOR+0x54, SPRITE)
        word(ACTOR+0x58, SHADOW)
        word(ACTOR+0x80, SCENE)
        uc.mem_write(ACTOR+8, struct.pack("<5h", 512, 160, 64, -5, 3))
        uc.mem_write(ACTOR+0x36, struct.pack("<H", animation))
        uc.mem_write(UNIT+4, bytes([kind]))
        uc.mem_write(UNIT+0xF6, bytes([16, 2]))
        word(OTHER, OTHER_UNIT)
        uc.mem_write(OTHER+10, struct.pack("<h", 16))
        uc.mem_write(OTHER_UNIT+0xF6, bytes([16 if "other" in occupants else 5, 2]))
        word(LIST+4, NODE if occupants else 0)
        for n, name in enumerate(occupants):
            node = NODE + n*32
            uc.mem_write(node, struct.pack("<III", ACTOR if name == "self" else OTHER, 0,
                                           node+32 if n+1 < len(occupants) else 0))
        uc.mem_write(SHADOW+0x14, b"\x7a"*6)
        callee_saved = [0x31415900 + i for i in range(8)]
        for n, value in enumerate(callee_saved):
            uc.reg_write(UC_ARM_REG_R4+n, value)
        projections, setters, lookups, returns, setter_writes = [], [], [], [], []
        in_setter = False

        def trace(machine, pc, size, user_data):
            nonlocal in_setter
            in_setter = pc == 0x03006BBC
            args = [machine.reg_read(UC_ARM_REG_R0+i) for i in range(4)]
            if pc == 0x0808EFCC:
                projections.append(args)
            elif in_setter:
                setters.append(args[:2])
            elif pc == shadow.movement.ITERATOR:
                lookups.append(args[:3])
                self.assertEqual(machine.mem_read(args[2]+4, 2), b"\x10\x02")
                self.assertEqual(machine.mem_read(args[2]+8, 4), bytes(4))
            elif pc == 0x08097FBA:
                if not occupants:
                    self.assertEqual(machine.reg_read(UC_ARM_REG_R2), SP-28)
                returns.append(int.from_bytes(machine.mem_read(SP-20, 4), "little"))

        def write(machine, access, address, size, value, user_data):
            if in_setter:
                setter_writes.append((address, size, value & 0xFF))

        uc.hook_add(UC_HOOK_CODE, trace)
        uc.hook_add(UC_HOOK_MEM_WRITE, write)
        uc.reg_write(UC_ARM_REG_R1, SCENE)
        self.call(uc, shadow.OWNER, ACTOR)
        self.assertEqual(uc.reg_read(UC_ARM_REG_R0), 1)
        self.assertEqual([uc.reg_read(UC_ARM_REG_R4+i) for i in range(8)], callee_saved)
        hidden = bool(flags & 1 or flags & 0x20000 and scene_flags & 0x40)
        eligible = not hidden and not flags & 0x8000 and kind not in (0x1f, *range(0x40, 0x47)) and animation not in (0, 12, 16, 128)
        draws_shadow = eligible and not flags & 4
        expected = [] if hidden else [[SPRITE, 507, 160, 67]]
        found = next((ACTOR if name == "self" else OTHER for name in occupants if name != "miss"), 0)
        if draws_shadow:
            # Native terrain lookup returns -1 outside 16x16. An eligible neighbor
            # substitutes its height+48. A matching self leaves the physical result.
            expected.append([SHADOW, 507, 64 if found == OTHER else 0xfffffff0, 67])
        self.assertEqual(projections, expected)
        self.assertEqual(lookups, [[LIST, shadow.movement.CALLBACK | 1, SP-28]] if eligible else [])
        self.assertEqual(returns, [found] if eligible else [])
        self.assertEqual(setters, [[SHADOW, 0xfffffffe]] if draws_shadow else [])
        self.assertEqual(setter_writes, [(SHADOW+0x16, 1, 0xfe)] if draws_shadow else [])
        self.assertEqual(uc.mem_read(SHADOW+0x14, 6), b"\x7a\x7a\xfe\x7a\x7a\x7a" if draws_shadow else b"\x7a"*6)

    def test_real_installer_native_execution_and_return_abi(self):
        for args in [((),), (("miss",),), (("other",),), (("self",),), (("self", "other"),),
                     ((), 4), ((), 1), ((), 0x20000, 0x40), ((), 0x8000),
                     ((), 0, 0, 0x40), ((), 0, 0, 1, 12)]:
            with self.subTest(args=args):
                self.exercise(*args)
