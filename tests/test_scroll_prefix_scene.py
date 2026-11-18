"""Real USA scanline scene, both heaps and all phase-102 prefix lengths."""
import argparse
import copy
import os
from pathlib import Path
import struct
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import scroll_prefix_scene as scene


class ScrollPlacement(unittest.TestCase):
    def test_both_arenas_and_exclusive_endpoint(self):
        # Lower/upper endpoints in the actual scene partition, including the
        # two private 12-byte heap headers and the complete stack descriptor.
        base = 0x02016000
        owner = base+0x6000+20
        child = owner+60+12
        scan = base+0x6000-1000
        self.assertEqual(scene.check_placement(base,owner,child,scan,scan+32,0x03007B00)[-1][1],
                         base+0x6000)
        for changed in ((owner,child-4,scan,scan+32,0x03007B00),
                        (owner,child,scan+4,scan+36,0x03007B00),
                        (owner,child,scan,scan+32,scene.SHADOW-24)):
            with self.subTest(changed=changed), self.assertRaises(ValueError):
                scene.check_placement(base,*changed)


class NativeScroll(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import match
        from rompath import rom_path
        import json
        import volatile_semantics as vs

        root = os.environ.get("FFTA_SCROLL_FIXTURE")
        if not root:
            raise unittest.SkipTest("FFTA_SCROLL_FIXTURE must name a checkout with the reviewed source and ROM")
        cls.root = Path(root)
        cls.rom = Path(rom_path(root)).read_bytes()
        cls.objects = match.parse_data_symbols((cls.root/"config/data_symbols.json").read_bytes())
        cls.declaration = json.loads((Path(match.__file__).parent/"volatile_allow.json").read_text())["entries"][0]
        cls.images = []
        cls.assemblies = []
        args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                                  flags=match.DEFAULT_FLAGS, objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD)
        runner = match.Runner(args.cc, "Ubuntu", match.DEFAULT_WSL_PATH, root=str(cls.root))
        with runner.workspace() as ws:
            for rewrite in (None, vs.strip_pinned_volatile, vs.perturb_pinned):
                _, _, image = match.compile_object(runner, ws, args, root, scene.OWNER, "src/080EF484.c",
                    rewrite=None if rewrite is None else lambda text: rewrite(text, cls.declaration["declaration"]))
                cls.images.append(image)
                cls.assemblies.append(runner.read_binary(f"{ws}/f.s").decode())
                bindings = {f"func_{target:08X}": target for _, target in scene.CALLS}
                bindings.update({name: address for _, name, address in scene.DATA})
                linked = match.link_typed_targets(runner, ws, args, "func_080EF484", scene.OWNER, bindings, set(cls.objects))
                if linked["text"] != cls.rom[scene.OWNER-scene.BASE:scene.END-scene.BASE]:
                    raise ValueError("linked variant differs from complete ROM body")

    def test_native_variants_and_typed_bindings(self):
        for image, asm in zip(self.images, self.assemblies):
            scene.check_image(image, self.rom, self.objects)
            self.assertNotEqual(scene.finite_backedge(asm), asm)
            for site in (0x11E, 0x120, 0x158, 0x160, 0x164, 0x16A, 0x170, 0x174):
                changed = dict(image)
                body = bytearray(image["text"])
                body[site] ^= 1
                changed["text"] = bytes(body)
                with self.assertRaises(ValueError):
                    scene.check_image(changed, self.rom, self.objects)
            changed = copy.deepcopy(image)
            section = changed["relocations"][0]
            raw = bytearray(changed["section_data"][section])
            struct.pack_into("<I", raw, 0, 80)
            changed["section_data"][section] = bytes(raw)
            with self.assertRaises(ValueError):
                scene.check_image(changed, self.rom, self.objects)
        bad = dict(self.objects, g_control_flags_03000940=scene.SHADOW+2)
        with self.assertRaises(ValueError):
            scene.check_image(self.images[0], self.rom, bad)

    def test_source_loop_and_provider_mutations(self):
        scene.provider(self.rom)
        for pc in (0x080EFC2E, 0x080059FE, 0x08005A74, 0x080D9914, 0x080D9488, 0x0800CE5A,
                   0x0800C3CC, 0x080D996C, 0x0800C614, 0x08149806, 0x08149818, 0x08149AF4+28,
                   0x080EF5BC, 0x080EF5D6, 0x080EF5E4, 0x080EF5F4, 0x08149556, 0x0836D4B8):
            changed = bytearray(self.rom)
            changed[pc-scene.BASE] ^= 1
            with self.subTest(pc=pc), self.assertRaises(ValueError):
                scene.provider(changed)
        for before, after in (("ldrh\tr0, [r5, #4]\n\tcmp\tr2, r0", "ldrh\tr0, [r3, #4]\n\tcmp\tr2, r0"),
                              ("bcc\t.L20", "bls\t.L20"), ("cmp\tr0, #72", "cmp\tr0, #160")):
            self.assertIn(before, self.assemblies[0])
            with self.assertRaises(ValueError):
                scene.finite_backedge(self.assemblies[0].replace(before, after))

    def test_native_allocation_full_phase_history_and_alias_counterexamples(self):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_CODE, UC_HOOK_MEM_READ, UC_HOOK_MEM_WRITE, UC_MEM_WRITE
        from unicorn.arm_const import (UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3,
                                      UC_ARM_REG_R4, UC_ARM_REG_R5, UC_ARM_REG_R9, UC_ARM_REG_SP,
                                      UC_ARM_REG_LR, UC_ARM_REG_PC)
        import scheduler_zero_descriptor as zero
        machine = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        machine.mem_map(scene.BASE, (len(self.rom)+4095)&~4095)
        machine.mem_write(scene.BASE, self.rom)
        machine.mem_map(0x02000000, 0x40000)
        machine.mem_map(0x03000000, 0x8000)
        machine.mem_write(zero.DESTINATION, self.rom[zero.IMAGE-scene.BASE:zero.IMAGE-scene.BASE+176])
        sp, stop = 0x03007E00, 0x03007FF0
        def write(address, fmt, *values):
            machine.mem_write(address, struct.pack("<"+fmt, *values))
        def get(address, fmt="I"):
            return struct.unpack("<"+fmt, machine.mem_read(address, struct.calcsize("<"+fmt)))[0]
        def run(pc, *arguments, end=stop, count=2000000):
            for reg, value in zip((UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3), arguments):
                machine.reg_write(reg, value)
            machine.reg_write(UC_ARM_REG_SP, sp)
            machine.reg_write(UC_ARM_REG_LR, stop|1)
            machine.emu_start(pc|1, end, count=count)
            self.assertEqual(machine.reg_read(UC_ARM_REG_PC), end)
            return machine.reg_read(UC_ARM_REG_R0)
        # Unrelated sprite/sequence tasks are opaque. The creator, installed
        # clear, heap initializer, allocator search/split, bank initializer,
        # descriptor, scheduler dispatch, both getters and iteration are real.
        opaque = {0x0800C2C0:0, 0x080105B8:0, 0x0801159C:0, 0x080D49FC:0,
                  0x080D4B64:1, 0x080D3E9C:1, 0x080DFD8C:1, 0x080D3F08:0,
                  0x0800BC08:0}
        def skip(uc, address, size, data):
            uc.reg_write(UC_ARM_REG_R0, opaque[address])
            uc.reg_write(UC_ARM_REG_PC, uc.reg_read(UC_ARM_REG_LR))
        for pc in opaque:
            machine.hook_add(UC_HOOK_CODE, skip, begin=pc, end=pc)
        # Native initializer seeds all later allocations from the cartridge's
        # actual scene EWRAM region. The live GBA heap byte count and arena
        # partition are produced by the guest, never supplied as call results.
        run(0x080227E8)
        write(0x02000100, "B", 0)
        run(0x080D36B0, 0, 0x02000100)
        base = get(0x020159B8)
        manager = get(0x0200F430)
        self.assertEqual(get(0x02009140), base)
        self.assertEqual(get(manager), base+0x6000)
        # Replay the parent constructor's real call site, with no sibling tasks
        # in this witness. The outer callback's own descriptor contains x/y.
        write(0x02008FF0, "I", manager)
        machine.reg_write(UC_ARM_REG_R5, 0x02000120)
        machine.reg_write(UC_ARM_REG_R9, 0)
        write(0x02000126, "HH", 100, 70)
        write(scene.SHADOW, "H", 0x0137)
        write(scene.SHADOW+24, "H", 0xFFFD)
        control_events = []
        def watch_control(uc, kind, address, width, value, data):
            pc = uc.reg_read(UC_ARM_REG_PC)
            if scene.OWNER <= pc < scene.END:
                control_events.append((pc, kind, address, width, value))
        machine.hook_add(UC_HOOK_MEM_READ|UC_HOOK_MEM_WRITE, watch_control, begin=scene.SHADOW, end=scene.SHADOW+79)
        descriptors = set()
        def owner_entry(uc, address, size, unused):
            descriptors.add(uc.reg_read(UC_ARM_REG_R1))
        machine.hook_add(UC_HOOK_CODE, owner_entry, begin=scene.OWNER, end=scene.OWNER)
        task = run(0x080EFC22, end=0x080EFC38)
        self.assertEqual(get(task), scene.OWNER|1)
        self.assertEqual(get(task+20,"H"), 0x100)
        state = task+24
        self.assertEqual(get(scene.SHADOW,"H"), 0x0937)
        def tick():
            run(0x08005A24, manager)
        for _ in range(62):
            if get(task+20,"H") != 0x100:
                break
            tick()
        self.assertEqual((get(task+20,"H"), get(state+4,"H")), (0x101,86))
        for remaining in range(85,0,-1):
            tick()
            self.assertEqual((get(task+20,"H"), get(state+4,"H")), (0x101,remaining))
        tick()
        child = get(state+28)
        scan = get(child+24+4)
        buf = run(0x080D996C, child)
        self.assertEqual(len(descriptors), 2)
        for descriptor in descriptors:
            spans = scene.check_placement(base, task, child, scan, buf, descriptor)
        self.assertEqual(spans, ((buf,buf+320),(get(scan+24),get(scan+24)+324),(get(scan+28),get(scan+28)+324)))
        self.assertEqual((get(scan+16,"H"),get(scan+18,"H"),get(scan+4),get(scan+12,"H")),
                         (320,2,0x0400001E,5))
        expected = [0xFFFD]*160
        self.assertEqual(list(struct.unpack("<160H",machine.mem_read(buf,320))),expected)
        rows = []
        def row_event(uc, kind, address, width, value, data):
            if uc.reg_read(UC_ARM_REG_PC) == 0x080EF5DC and kind == UC_MEM_WRITE:
                rows.append((address, width))
        machine.hook_add(UC_HOOK_MEM_WRITE,row_event)
        for count in range(0,73,2):
            self.assertEqual((get(task+20,"H"), get(state+4,"H")), (0x102,count))
            rows.clear()
            tick()
            self.assertEqual(rows, [(buf+2*i,2) for i in range(count)])
            for i in range(count):
                expected[i]=(expected[i]+2)&65535
            self.assertEqual(list(struct.unpack("<160H",machine.mem_read(buf,320))),expected)
        self.assertEqual((get(task+20,"H"),get(state+4,"H"),get(scene.SHADOW,"H")), (0x103,74,0x0137))
        self.assertEqual([(pc,address,width) for pc,_,address,width,_ in control_events],
                         [(pc,scene.SHADOW,2) for pc in (0x080EF4EC,0x080EF4F0,0x080EF600,0x080EF604)])
        for bad in ((base,task,task,scan,buf),(base,task,child,task,task+32),
                    (base,task,child,scan,state+4),(base,task,child,scan,scene.SHADOW+2),
                    (base,task,child,scan,get(scan+24)),(base,task,child,scan,buf+2),
                    (0x03000000,task,child,scan,buf),(base,task,child,base+0x6000-996,base+0x6000-964)):
            with self.subTest(bad=bad), self.assertRaises(ValueError):
                scene.check_placement(*bad, descriptor)
        for bad in (scene.SHADOW, task+24, child+24, buf):
            with self.assertRaises(ValueError):
                scene.check_placement(base, task, child, scan, buf, bad)
        # When no hardware slot is free the real allocator entry returns NULL.
        # A zero payload-size field also makes the genuine getter return NULL.
        saved = bytes(machine.mem_read(0x02009148, 16))
        write(0x02009148,"4I",scan,scan,scan,scan)
        self.assertEqual(run(0x0800C3CC,0x0800DE65,320,2,0x0400001E),0)
        machine.mem_write(0x02009148,saved)
        write(scan+16,"H",0)
        self.assertEqual(run(0x080D996C,child),0)
        write(scan+16,"H",320)
        # Re-entering phase 102 with an unproven counter can clobber the DMA
        # bank. Native instruction execution reproduces the first out-of-range
        # write at row 160. This is why the induction needs phase 101.
        desc=0x03007700
        write(desc, "H", 0x102)
        write(state+4,"H",161)
        rows.clear()
        run(scene.OWNER,task,desc,state)
        self.assertIn((buf+320,2),rows)
        # Repoint the underlying getter at pinned RAM. The same unmodified
        # owner really writes there and the physical contract rejects it.
        write(scan+20,"I",scene.SHADOW+2)
        write(desc,"H",0x102)
        write(state+4,"H",2)
        rows.clear()
        run(scene.OWNER,task,desc,state)
        self.assertEqual(rows, [(scene.SHADOW+2,2),(scene.SHADOW+4,2)])

    def test_complete_report_and_corrupted_extents(self):
        from match_evidence import report_matches
        report=(self.root/"docs/match/080EF484.md").read_text()
        self.assertTrue(report_matches(report,str(self.root),scene.OWNER))
        original=next(s for s in report.splitlines() if s.startswith("* ROM bytes:"))
        linked=next(s for s in report.splitlines() if s.startswith("* compiled :"))
        data=self.rom[scene.OWNER-scene.BASE:scene.END-scene.BASE]
        for new in (data[:-2], data+b"\x00\x00", bytes([data[0]^1])+data[1:]):
            fake=report.replace(original,f"* ROM bytes: `{new.hex()}` ({len(new)} bytes)").replace(
                linked,f"* compiled : `{new.hex()}`").replace("436/436 bytes", f"{len(new)}/{len(new)} bytes")
            self.assertFalse(scene.report_body(fake,self.root))
        for line in (original,linked):
            self.assertFalse(scene.report_body(report.replace(line,line+"\n"+line),self.root))


if __name__ == "__main__":
    unittest.main()
