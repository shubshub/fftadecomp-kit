"""Complete-owner admission retains original ELF, source, ABI and replay guards."""
import argparse
import copy
import json
import os
from pathlib import Path
import shutil
import struct
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import match_evidence
import owner_admission_profile as owner

SOURCE = '''typedef unsigned int u32;
extern u32 func_08011000(u32 *values);
extern u32 data_02010000[8];
u32 func_08010000(u32 (*callback)(u32), u32 value) {
    u32 values[2];
    values[0] = value;
    values[1] = value + 1;
    value = func_08011000(values);
    switch (value & 7) {
    case 0: value += data_02010000[0]; break;
    case 1: value -= data_02010000[1]; break;
    case 2: value ^= data_02010000[2]; break;
    case 3: value |= data_02010000[3]; break;
    case 4: value &= data_02010000[4]; break;
    case 5: value *= data_02010000[5]; break;
    case 6: value = data_02010000[6] - value; break;
    default: value = data_02010000[7]; break;
    }
    value = callback(value);
    return value / 10;
}
'''


class MarkerTests(unittest.TestCase):
    def test_default_report_is_not_selected(self):
        self.assertFalse(owner.selected('* verification: `ordinary`\n'))

    def test_mixed_or_duplicate_profile_refused(self):
        marker = f'* verification: `{owner.SCHEMA}`\n'
        for report in (marker * 2, marker + '* function-address profile: other\n',
                       '* owner runtime: incomplete\n'):
            with self.subTest(report=report), self.assertRaises(ValueError):
                owner.selected(report)


@unittest.skipUnless(os.environ.get('FFTA_OWNER_TEST_ROM') and
                     Path(os.path.expandvars(match.DEFAULT_CC)).is_file() and
                     shutil.which('arm-none-eabi-ld'), 'approved ROM and fixed compiler required')
class NativeAdmissionTests(unittest.TestCase):
    A, B = 0x08010000, 0x08011000

    @classmethod
    def setUpClass(cls):
        scratch = Path(os.environ.get('TMPDIR', Path.cwd() / 'build/tests'))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix='owner_native_', dir=scratch)
        cls.root = Path(cls.temporary.name)
        for name in ('src', 'config', 'symbols', 'include', 'build'):
            (cls.root / name).mkdir()
        cls.args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP,
            assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD,
            flags=match.DEFAULT_FLAGS)
        (cls.root / 'src/08010000.c').write_text(SOURCE)
        dependency = cls.root / 'src/08011000.c'
        dependency.write_text('unsigned int func_08011000(unsigned int *values) '
                              '{ return values[0] + values[1]; }\n')
        rom = Path(os.environ['FFTA_OWNER_TEST_ROM']).read_bytes()
        if len(rom) != 16*1024*1024 or owner.sha(rom) != \
                '43fc8204c6dceee58828aebc7af0c72eb807e99f35ad641c8bb0a4fa8b6edc19':
            raise ValueError('native fixture requires full approved ROM identity')
        # Runtime identities are actual immutable ROM owners, never invented stubs.
        rows = [
            {'rom': '0x08142AB0', 'end': '0x08142B28', 'mode': 'thumb', 'instrs': 60},
            {'rom': '0x0814274C', 'end': '0x0814274E', 'mode': 'thumb', 'instrs': 1}]
        cls.objects = b'{"data_02010000":"0x02010000"}\n'
        runner = match.Runner(match.DEFAULT_CC, 'Ubuntu', match.DEFAULT_WSL_PATH,
                              root=cls.root, timeout=120)
        with runner.workspace() as workspace:
            _, callee, _ = match.compile_object(runner, workspace, cls.args, cls.root,
                                                cls.B, 'src/08011000.c')
            dependency.unlink()
            cls.original, body, cls.image = match.compile_object(runner, workspace, cls.args,
                                               cls.root, cls.A, 'src/08010000.c')
            rows = [{'rom': f'0x{start:08X}', 'end': f'0x{end:08X}', 'mode': 'thumb',
                     'instrs': 1} for start, end in ((cls.A, cls.A+len(body)),
                                                  (cls.B, cls.B+len(callee)))] + rows
            for address in match.function_thunk.ALIASES.values():
                rows.append({'rom': f'0x{address:08X}', 'end': f'0x{address+4:08X}',
                             'mode': 'thumb', 'instrs': 2})
            mapping = json.dumps(rows).encode()
            cls.data, cls.bindings = owner.object_bytes(runner, workspace, cls.args,
                                    cls.image, cls.A, rom, mapping, cls.objects)
        rom = bytearray(rom)
        rom[cls.A-match.ROM_BASE:cls.A-match.ROM_BASE+len(cls.data)] = cls.data
        rom[cls.B-match.ROM_BASE:cls.B-match.ROM_BASE+len(callee)] = callee
        cls.rom = bytes(rom)
        cls.refinement = owner.refine(cls.data, cls.A, mapping)
        rows[0]['instrs'] = cls.refinement['instrs']
        rows[1]['instrs'] = len(list(match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB).disasm(callee, cls.B)))
        cls.mapping = json.dumps(rows, indent=2).encode()
        cls.index = ''.join(f'{int(r["rom"],16):08X} {int(r["end"],16):08X} '
                           f'{int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n'
                           for r in rows).encode()
        (cls.root / 'config/functions.json').write_bytes(cls.mapping)
        (cls.root / 'symbols/functions.txt').write_bytes(cls.index)
        (cls.root / 'config/data_symbols.json').write_bytes(cls.objects)
        (cls.root / 'baserom.bin').write_bytes(cls.rom)
        cls.environment = patch.dict(os.environ, FFTA_ROM=str(cls.root / 'baserom.bin'))
        cls.environment.start()
        cls.result = owner.build(cls.root, cls.A)
        cls.manifest = cls.result[1]
        cls.report = owner.render(cls.A, cls.result)
        report = cls.root / 'docs/match/08010000.md'
        report.parent.mkdir(parents=True)
        report.write_text(cls.report)

    @classmethod
    def tearDownClass(cls):
        cls.environment.stop()
        cls.temporary.cleanup()

    def replay(self, **changes):
        values = dict(data=self.data, address=self.A, rom=self.rom, mapping=self.mapping,
                      index=self.index, objects=self.objects, manifest=self.manifest)
        values.update(changes)
        return owner.verify(**values)

    def original_bindings(self, image):
        return owner.original_bindings(image, self.A, self.rom, self.mapping, self.objects)

    def test_natural_full_original_elf_and_all_components(self):
        self.assertEqual(self.result[8], self.original)
        self.assertEqual(len(self.data), 188)
        self.assertEqual(self.result[7], 58)
        self.assertTrue(self.bindings['switches'])
        self.assertTrue(self.bindings['data'])
        self.assertEqual([name for _, name in self.bindings['calls']],
                         ['func_08011000', '_call_via_r4', '__udivsi3'])
        self.assertEqual(self.replay()[0], self.manifest)

    def test_fresh_source_bound_report_dispatch(self):
        self.assertTrue(match_evidence.report_matches(self.report, self.root, self.A))

    def test_stale_source_or_header_refused(self):
        source = self.root / 'src/08010000.c'
        original = source.read_bytes()
        try:
            source.write_bytes(original+b'\n/* changed source identity */\n')
            self.assertFalse(match_evidence.report_matches(self.report, self.root, self.A))
        finally:
            source.write_bytes(original)
        header = self.root / 'include/added.h'
        try:
            header.write_text('typedef unsigned int changed_header;\n')
            self.assertFalse(match_evidence.report_matches(self.report, self.root, self.A))
        finally:
            header.unlink()

    def test_changed_report_fingerprint_refused(self):
        self.assertFalse(owner.report_matches(self.report.replace('"fingerprint":"',
                                                                 '"fingerprint":"0'), self.root, self.A))

    def test_trailing_or_duplicate_evidence_refused(self):
        self.assertFalse(owner.report_matches(self.report+'extra\n', self.root, self.A))
        evidence = next(line for line in self.report.splitlines() if line.startswith('* owner runtime evidence:'))
        self.assertFalse(owner.report_matches(self.report+evidence+'\n', self.root, self.A))

    def test_wrong_runtime_identity_refused(self):
        rom = bytearray(self.rom)
        rom[match.UDIVSI3_ADDRESS-match.ROM_BASE] ^= 1
        with self.assertRaises(ValueError):
            self.replay(rom=bytes(rom))

    def test_wrong_thunk_identity_refused(self):
        rom = bytearray(self.rom)
        rom[match.function_thunk.ALIASES['_call_via_r4']-match.ROM_BASE] ^= 1
        with self.assertRaises(ValueError):
            self.replay(rom=bytes(rom))

    def test_zero_divisor_refused_even_when_rom_matches(self):
        data = bytearray(self.data)
        call = next(offset for offset, name in self.bindings['calls'] if name=='__udivsi3')
        self.assertEqual(data[call-2:call], b'\x0a\x21')
        data[call-2] = 0
        rom = bytearray(self.rom)
        rom[self.A-match.ROM_BASE:self.A-match.ROM_BASE+len(data)] = data
        with self.assertRaisesRegex(ValueError, 'nonzero constant'):
            self.replay(data=bytes(data), rom=bytes(rom))

    def test_wrong_count_or_overlap_refused(self):
        rows = json.loads(self.mapping)
        rows[0]['instrs'] += 1
        with self.assertRaises(ValueError):
            self.replay(mapping=json.dumps(rows).encode())
        rows = json.loads(self.mapping)
        rows.append(dict(rows[0], rom=f'0x{self.A+2:08X}'))
        with self.assertRaises(ValueError):
            self.replay(mapping=json.dumps(rows).encode())
        with self.assertRaises(ValueError):
            self.replay(index=self.index.replace(b' 58 return', b' 59 return'))

    def test_unbound_data_or_switch_word_refused(self):
        for key in ('data', 'switches', 'calls'):
            manifest = copy.deepcopy(self.manifest)
            manifest['bindings'][key].pop()
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.replay(manifest=manifest)

    def test_private_runtime_alias_is_not_canonical_provenance(self):
        image = copy.deepcopy(self.image)
        for symbol in image['symbols']:
            if symbol['name']=='__udivsi3':
                symbol['name']='func_08142AB0'
        with self.assertRaises(ValueError):
            self.original_bindings(image)

    def test_partial_function_symbol_refused(self):
        image = copy.deepcopy(self.image)
        symbol = next(row for row in image['symbols'] if row['name']=='func_08010000')
        symbol['size'] -= 2
        with self.assertRaises(ValueError):
            self.original_bindings(image)

    def test_original_elf_unknown_or_overlapping_relocation_refused(self):
        for kind in (255, 'overlap'):
            image = copy.deepcopy(self.image)
            section = image['relocations'][0]
            raw = bytearray(image['section_data'][section])
            if kind == 'overlap':
                struct.pack_into('<I', raw, 8, struct.unpack_from('<I', raw, 0)[0])
            else:
                offset, info = struct.unpack_from('<II', raw, 0)
                struct.pack_into('<II', raw, 0, offset, (info & ~255)|kind)
            image['section_data'][section] = bytes(raw)
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                self.original_bindings(image)

    def test_changed_toolchain_refused(self):
        args = copy.copy(self.args)
        args.flags = '-O0'
        with self.assertRaises(ValueError):
            owner.build(self.root, self.A, args)

    def test_default_leaf_profile_stays_closed(self):
        ordinary = {self.A+offset: self.B for offset, name in self.bindings['calls']
                    if name=='func_08011000'}
        with self.assertRaises(ValueError):
            match.verify_leaf_instructions(self.data, self.A, True, ordinary)

    def test_status_and_compiled_rebuild_dispatch(self):
        import status
        import rebuild
        self.assertEqual(rebuild.saved_profile_arguments(self.report, self.root, self.A),
                         ['--owner-runtime-profile', owner.SELECTOR])
        totals = status.collect(str(self.root), True, quiet=True)
        self.assertEqual((totals[1], totals[3], totals[4]), (1, len(self.data), []))
        self.assertEqual(rebuild.compiled_rebuild(self.root), 0)


if __name__ == '__main__':
    unittest.main()
