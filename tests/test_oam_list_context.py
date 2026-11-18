import argparse
from hashlib import sha256
import os
from pathlib import Path
import struct
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import oam_list_context as oam


@unittest.skipUnless(os.getenv('FFTA_OAM_LIST_ROOT'), 'requires the reviewed OAM sources, USA ROM and agbcc')
class ListContextTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        from rompath import rom_path
        import match

        cls.root = Path(os.environ['FFTA_OAM_LIST_ROOT']).resolve()
        cls.rom = Path(rom_path(cls.root)).read_bytes()
        cls.body, cls.report = oam.build(cls.root)
        cls.args = argparse.Namespace(
            cc=match.DEFAULT_CC,
            cpp=match.DEFAULT_CPP,
            flags=match.DEFAULT_FLAGS,
            assembler=match.DEFAULT_AS,
            objcopy=match.DEFAULT_OBJCOPY,
            linker=match.DEFAULT_LD,
        )
        cls.objects = match.parse_data_symbols(match.data_snapshot(cls.root))

    def machine(self):
        from test_affine_oam_slot import AffineTests
        from scheduler_zero_descriptor import DESTINATION, IMAGE

        cpu = AffineTests.machine(self)
        cpu.mem_write(DESTINATION, self.rom[IMAGE - oam.BASE : IMAGE - oam.BASE + 176])
        cpu.mem_write(oam.OWNER, self.body)
        return cpu

    def run_to(self, cpu, start, stop):
        from unicorn.arm_const import UC_ARM_REG_SP, UC_ARM_REG_PC

        cpu.reg_write(UC_ARM_REG_SP, 0x03007E00)
        cpu.emu_start(start | 1, stop, count=100000)
        self.assertEqual(cpu.reg_read(UC_ARM_REG_PC), stop)
        self.assertEqual(cpu.reg_read(UC_ARM_REG_SP), 0x03007E00)

    def test_real_startup_frame_banks_counts_and_bounds(self):
        from test_affine_oam_slot import AffineTests

        hidden = struct.pack('<Q', 0x00F800A8)
        sizes = {0x03002C58: 48, 0x03000030: 128, 0x03002F68: 32, 0x03003170: 16}
        for bank in (0, 1):
            for a, b in ((0, 0), (-2147483648, -1), (1, 3), (32, 16)):
                with self.subTest(bank=bank, a=a, b=b):
                    cpu = self.machine()
                    cpu.mem_write(0x03000000, b'\xa5' * 0x3600)
                    self.run_to(cpu, 0x08000296, 0x0800029A)
                    for start, count in sizes.items():
                        self.assertEqual(cpu.mem_read(start, 16 * count), hidden * (2 * count))
                        cpu.mem_write(start, b'\xcc' * (16 * count))
                    counts = {0x03002C50: 2, 0x03000020: 4, 0x03002F60: a, 0x03003168: b}
                    self.assertEqual(cpu.mem_read(0x03003270, 64 + 512), bytes(64 + 512))
                    self.assertEqual(cpu.mem_read(0x03000028, 1) + cpu.mem_read(0x03002F58, 1), bytes(2))
                    for start, count in counts.items():
                        self.assertEqual(cpu.mem_read(start, 8), bytes(8))
                        cpu.mem_write(start + 4 * bank, struct.pack('<i', count))
                        cpu.mem_write(start + 4 * (1 - bank), struct.pack('<I', 7))
                    for at in (0x03000028, 0x03002F58):
                        cpu.mem_write(at, bytes((bank,)))
                    self.run_to(cpu, 0x08000464, 0x0800046C)
                    for (start, capacity), amount in zip(sizes.items(), counts.values()):
                        writes = max(0, amount)
                        self.assertEqual(
                            cpu.mem_read(start + 8 * capacity * bank, 8 * capacity),
                            hidden * writes + b'\xcc' * (8 * (capacity - writes)),
                        )
                        self.assertEqual(
                            cpu.mem_read(start + 8 * capacity * (1 - bank), 8 * capacity), b'\xcc' * (8 * capacity)
                        )
                    for start in counts:
                        self.assertEqual(cpu.mem_read(start + 4 * bank, 4), bytes(4))
                        self.assertEqual(cpu.mem_read(start + 4 * (1 - bank), 4), struct.pack('<I', 7))
        # Positive counts come from the caller. A count of 33 really does
        # reach the second bank, so the verifier never claims an internal clamp.
        cpu = self.machine()
        cpu.mem_write(0x03002F60, struct.pack('<i', 33))
        AffineTests.call(self, cpu, oam.OWNER)
        self.assertEqual(cpu.mem_read(0x03002F68 + 32 * 8, 16), hidden + bytes(8))

    def test_reports_replay_and_context_identity(self):
        from match_evidence import report_matches
        import status

        file = self.root / 'docs/match/08001244.md'
        self.assertEqual(file.read_text(), self.report)
        self.assertEqual(status.report_extent(self.report), 120)
        self.assertTrue(report_matches(self.report, self.root, oam.OWNER))
        for member in oam.MEMBERS[:-1]:
            text = (self.root / 'docs/match' / f'{member:08X}.md').read_text()
            self.assertIn('* verification: `elf-symbol-thumb-data-v1`', text)
            self.assertTrue(report_matches(text, self.root, member))
        for old, new in (
            (oam.GROUP_DIGEST, '0' * 64),
            ('114/120', '120/120'),
            ('120/120 bytes', '119/120 bytes'),
            ('0800105C, 08001194', '08001194, 0800105C'),
            (oam.SCHEMA, 'elf-symbol-thumb-data-v1'),
        ):
            with self.subTest(old=old):
                self.assertNotEqual(self.report.replace(old, new), self.report)
                self.assertFalse(report_matches(self.report.replace(old, new), self.root, oam.OWNER))
        self.assertFalse(report_matches(self.report, self.root, oam.MEMBERS[1]))

    def test_source_input_and_relocation_controls(self):
        import match

        with tempfile.TemporaryDirectory(dir=self.root / 'build') as folder:
            stage = Path(folder)
            files = oam.inputs(self.root)
            for name, data in files.items():
                p = stage / name
                p.parent.mkdir(exist_ok=True)
                p.write_bytes(data)
            for name, old, new in (
                (oam.HEADER, b'count > 0', b'count >= 0'),
                (oam.HEADER, b'[2][0x10]', b'[2][0x20]'),
                (oam.source(oam.OWNER), b' = 0;', b' = 1;'),
                (oam.source(oam.MEMBERS[1]), b'0x100', b'0x80'),
            ):
                with self.subTest(mutation=new), self.assertRaises(ValueError):
                    self.assertIn(old, files[name])
                    (stage / name).write_bytes(files[name].replace(old, new))
                    try:
                        oam.inputs(stage)
                    finally:
                        (stage / name).write_bytes(files[name])
            # Const on the physical ROM table is a genuinely different C
            # declaration. It permits caching across the two calls to BX R2.
            h = stage / oam.HEADER
            h.write_bytes(
                files[oam.HEADER].replace(b'extern BufferInitializer g_', b'extern BufferInitializer const g_')
            )
            with self.assertRaises(ValueError):
                oam.compile_group(stage, (oam.MEMBERS[0],), self.args, self.objects)
            h.write_bytes(files[oam.HEADER])
            runner = match.Runner(self.args.cc, root=str(stage))
            with runner.workspace() as ws:
                _, _, image = match.compile_object(
                    runner, ws, self.args, str(stage), oam.OWNER, oam.source(oam.OWNER), oam_prefix=oam.MEMBERS[:-1]
                )
                index = image['relocations'][0]
                raw = image['section_data'][index]
                for offset in (0, 4, 8 * 4, 8 * 16):
                    bad = bytearray(raw)
                    bad[offset] ^= 1
                    image['section_data'][index] = bad
                    with self.assertRaises(ValueError):
                        oam.relocations(image, oam.MEMBERS, self.objects)
                image['section_data'][index] = raw
            for prefix in (tuple(reversed(oam.MEMBERS[:-1])), oam.MEMBERS, oam.MEMBERS[:1]):
                with self.assertRaises(ValueError):
                    oam.prefix_options(oam.OWNER, oam.source(oam.OWNER), prefix)

    def test_indexes_object_bindings_and_normal_status(self):
        import json
        import match
        import status
        from empty_body_profile import index_snapshot

        mapping = match.mapping_snapshot(self.root)
        index = index_snapshot(self.root)
        entries = json.loads(mapping)
        original = next(r for r in entries if int(r['rom'], 16) == oam.OWNER)
        for changed in (dict(original), dict(original, rom='0x08001246')):
            with self.assertRaises(ValueError):
                oam.check_indices(json.dumps(entries + [changed]).encode(), index, self.objects)
        changed = index.replace(b'08001244 080012BC', b'08001244 080012B8')
        with self.assertRaises(ValueError):
            oam.check_indices(mapping, changed, self.objects)
        with self.assertRaises(ValueError):
            oam.check_indices(mapping, index, dict(self.objects, data_03002F60=0x03003168))
        # This partial fixture lacks the whole-game library samples. Capture
        # the production collector's individual native decisions for these owners.
        results = {}
        status.collect(self.root, True, quiet=True, jobs=2, _publication_results=results)
        for address, end in zip(oam.MEMBERS, (*oam.MEMBERS[1:], oam.END)):
            count, length, failures, verified = results[oam.source(address)]
            self.assertEqual(
                (count, length, failures, verified), (1, end - address, [], [(address, end - address, False)])
            )

    def test_genuine_affine_predecessor_too_is_not_an_exact_unit(self):
        import match

        with tempfile.TemporaryDirectory(dir=self.root / 'build') as folder:
            stage = Path(folder)
            for name, data in oam.inputs(self.root).items():
                path = stage / name
                path.parent.mkdir(exist_ok=True)
                path.write_bytes(data)
            # The additional member needs the same definitions in this comparison.
            # Keep its entire original C body and replace its private declarations
            # with their compatible reviewed header. No game source is modified.
            address = 0x08000FC8
            original = (self.root / oam.source(address)).read_text()
            declaration = 'int func_08000FC8('
            self.assertEqual(original.count(declaration), 1)
            (stage / oam.source(address)).write_text(
                '#include "oam_lists.h"\n' + original[original.index(declaration) :]
            )
            names = tuple(map(oam.source, (address, *oam.MEMBERS)))
            (stage / 'unit.c').write_text(''.join(f'#include "{name}"\n' for name in names))
            runner = match.Runner(self.args.cc, root=str(stage))
            with runner.workspace() as ws:
                from shlex import quote

                w = quote(ws)
                runner.sh(f'{self.args.cpp} -nostdinc -undef -I include unit.c -o {w}/f.i')
                runner.sh(f'{self.args.cc} {self.args.flags} {w}/f.i -o {w}/f.s')
                runner.sh(f'{self.args.assembler} -mthumb-interwork {w}/f.s -o {w}/f.o')
                image = match.elf_image(runner.read_binary(ws + '/f.o'))
                targets = {s['name'] for s in image['symbols'] if s['name'] and s['section'] == 0}
                bindings = {name: (self.objects[name] if name in self.objects else oam.VENEER) for name in targets}
                self.assertEqual(targets - self.objects.keys(), {'func_0814224C'})
                out = match.link_typed_targets(
                    runner, ws, self.args, 'func_08000FC8', address, bindings, targets & self.objects.keys()
                )
                self.assertEqual(len(out['text']), 756)
                pos = oam.OWNER - address
                self.assertEqual(out['text'][:pos], self.rom[address - oam.BASE : oam.OWNER - oam.BASE])
                self.assertEqual(sha256(out['text'][pos:]).hexdigest(), oam.ALONE_DIGEST)
