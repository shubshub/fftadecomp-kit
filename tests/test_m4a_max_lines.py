import copy
import json
import os
from pathlib import Path
import struct
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import addressed_signed_runtime_profile as profile
import m4a_max_lines as lines


class M4aPolicyTests(unittest.TestCase):
    def test_source_declares_and_consumes_a_scalar_without_a_dereference(self):
        source = 'extern char gMaxLines[];\nvoid f(void) { soundInfo->maxScanlines = ((u32)gMaxLines); }'
        lines.source_use(source)
        for old, new in [('char', 'int'), ('[]', '[1]'), ('maxScanlines', 'dmaCounter'),
                         ('((u32)gMaxLines)', '*gMaxLines'), ('}', 'use(gMaxLines); }')]:
            with self.subTest(new=new), self.assertRaises(ValueError):
                lines.source_use(source.replace(old, new))

    def test_scalar_default_refusals(self):
        for offset, addend, owner, objects in [(0x114, 0, lines.ADDRESS, {}),
                (0x110, 1, lines.ADDRESS, {}), (0x110, 0, lines.ADDRESS + 4, {}),
                (0x110, 0, lines.ADDRESS, {lines.SYMBOL: 80}), (0x110, 0, lines.ADDRESS, {})]:
            with self.subTest(args=(offset, addend, owner, objects)), self.assertRaises(ValueError):
                lines.symbol_value(b'', owner, offset, addend, objects)
        for rows in ([], [None], [[0x110, 'other', 0]],
                     [[0x110, lines.SYMBOL, 0], [0x110, lines.SYMBOL, 0]]):
            with self.subTest(rows=rows), self.assertRaises(ValueError):
                lines.split_records(rows, b'', lines.ADDRESS, b'', {})


@unittest.skipUnless(os.getenv('FFTA_M4A_EXTENDER_ROOT'), 'needs FFTA USA ROM and indexed MPlayExtender source')
class M4aNativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import match
        import match_evidence as evidence
        cls.root = Path(os.environ['FFTA_M4A_EXTENDER_ROOT']).resolve()
        cls.result = profile.build(cls.root, lines.ADDRESS, selector=lines.SELECTOR)
        cls.rom = Path(evidence.report_rom_path(cls.root)).read_bytes()
        cls.mapping = evidence.mapping_snapshot(cls.root)
        cls.objects = evidence.data_snapshot(cls.root)
        cls.original = match.elf_image(cls.result['original_elf'])
        cls.linked = match.elf_image(cls.result['linked_elf'])
        cls.relocations = {}
        cls.calls, _, cls.targets = profile.original_bindings(cls.original, lines.ADDRESS, cls.rom,
            cls.mapping, data_mapping=cls.objects, data_relocations=cls.relocations, selector=lines.SELECTOR)
        cls.functions = {name for name, _ in cls.relocations.values() if profile.function_literal(name, lines.SELECTOR)}

    def test_real_linker_binding_and_bios_evidence(self):
        import match_evidence as evidence
        m = self.result['manifest']
        self.assertEqual(self.relocations[0x110], (lines.SYMBOL, 0))
        self.assertEqual(self.targets[lines.SYMBOL], 80)
        sym, = [s for s in self.linked['symbols'] if s['name'] == lines.SYMBOL]
        self.assertEqual((sym['section'], sym['type'], sym['value']), (0xFFF1, 0, 80))
        self.assertFalse(any(row[1] == lines.SYMBOL for row in m['data_bindings']))
        self.assertEqual(m['native_buffers']['bios_fill']['sites'][0][0], 0x08145486)
        self.assertEqual(len(m['m4a_callback_rows']), 3)
        t = profile.render(self.result)
        self.assertTrue(evidence.report_matches(t, str(self.root), lines.ADDRESS))
        for old, new in [('"kind":"SHN_ABS/STT_NOTYPE"', '"kind":"object"'),
                         ('"mixer_member_offset":12', '"mixer_member_offset":13')]:
            with self.subTest(new=new):
                self.assertIn(old, t)
                self.assertFalse(evidence.report_matches(t.replace(old, new), str(self.root), lines.ADDRESS))

    def test_wrong_original_symbol_wrong_linked_type_address_or_heap_alias_refused(self):
        def bind(image, selector=lines.SELECTOR, objects=None):
            return profile.original_bindings(image, lines.ADDRESS, self.rom, self.mapping,
                data_mapping=objects or self.objects, data_relocations={}, selector=selector)
        with self.assertRaises(ValueError):
            bind(self.original, profile.BIOS_SCALAR_FUNCTION_DATA_SELECTOR)
        for changed in ('type', 'value', 'bind', 'section', 'name'):
            image = copy.deepcopy(self.original)
            for members in image['symbol_tables'].values():
                for sym in members:
                    if sym['name'] == lines.SYMBOL:
                        sym[changed] = {'type': 1, 'value': 80, 'bind': 0, 'section': 1, 'name': 'other'}[changed]
            with self.subTest(original=changed), self.assertRaises(ValueError):
                bind(image)
        mapped = json.loads(self.objects)
        mapped[lines.SYMBOL] = '0x00000050'
        with self.assertRaises(ValueError):
            bind(self.original, objects=json.dumps(mapped).encode())
        for key, value in [('type', 1), ('value', 81), ('section', 1), ('size', 4)]:
            image = copy.deepcopy(self.linked)
            next(s for s in image['symbols'] if s['name'] == lines.SYMBOL)[key] = value
            with self.subTest(linked=key), self.assertRaises(ValueError):
                profile.linked_bytes(self.original, image, lines.ADDRESS, self.calls, self.targets,
                    data_relocations=self.relocations, function_literals=self.functions, selector=lines.SELECTOR)

    def test_real_relocation_requires_abs32_and_zero_addend(self):
        def bind(image):
            return profile.original_bindings(image, lines.ADDRESS, self.rom, self.mapping,
                data_mapping=self.objects, data_relocations={}, selector=lines.SELECTOR)

        image = copy.deepcopy(self.original)
        text = bytearray(image['text'])
        struct.pack_into('<i', text, lines.OFFSET, 4)
        image['text'] = bytes(text)
        with self.assertRaises(ValueError):
            bind(image)

        image = copy.deepcopy(self.original)
        entries = [(index, pos, info) for index in image['relocations']
                   for pos, (offset, info) in enumerate(struct.iter_unpack('<II', image['section_data'][index]))
                   if offset == lines.OFFSET]
        (index, pos, info), = entries
        self.assertEqual(info & 255, 2)  # R_ARM_ABS32
        relocs = bytearray(image['section_data'][index])
        struct.pack_into('<I', relocs, pos * 8 + 4, (info & ~255) | 3)  # R_ARM_REL32
        image['section_data'][index] = bytes(relocs)
        with self.assertRaises(ValueError):
            bind(image)

    def test_reached_literal_only_and_dominating_mixer_pointer(self):
        import owner_admission_profile as owner
        import owner_graph_profile as graph
        data = self.result['body']
        refinement = owner.refine(data, lines.ADDRESS, self.mapping)
        ins, edges, _, calls, words = graph.graph(data, lines.ADDRESS, refinement)
        partition = graph.partition(data, lines.ADDRESS, refinement, ins, words)
        literals = {0xD4: ('data_03007FF0', 0x03007FF0)}
        self.assertEqual(lines.verify_use(data, ins, edges, partition, calls, literals)['value'], 80)
        changed = bytearray(data)
        changed[lines.STORE - lines.ADDRESS] ^= 1
        for body, edge in [(changed, edges), (data, {**edges, lines.ADDRESS: (lines.STORE,)}),
                           (data, {**edges, lines.ADDRESS: (lines.LOAD,)})]:
            with self.assertRaises(ValueError):
                lines.verify_use(body, ins, edge, partition, calls, literals)
        broken = copy.deepcopy(partition)
        next(row for row in broken['words'] if row['address'] == lines.ADDRESS+0x110)['load_sites'].append(lines.LOAD+2)
        with self.assertRaises(ValueError):
            lines.verify_use(data, ins, edges, broken, calls, literals)
        bindings = {off: (f'func_{addr:08X}', addr|1) for _, addr, _, _, off in lines.CALLBACKS}
        entries = json.loads(self.mapping)
        next(row for row in entries if row['rom'] == '0x08145070')['end'] = '0x08145084'
        with self.assertRaises(ValueError):
            lines.callbacks(self.rom, json.dumps(entries), bindings)
        changed_table = bytearray(self.rom)
        slot, entry, _, _, _ = lines.CALLBACKS[0]
        struct.pack_into('<I', changed_table, 0x0836D098 - 0x08000000 + 4 * slot, entry)
        with self.assertRaises(ValueError):
            lines.callbacks(changed_table, self.mapping, bindings)

if __name__ == '__main__':
    unittest.main()
