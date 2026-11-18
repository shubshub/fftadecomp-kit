import argparse
import copy
import os
from pathlib import Path
import struct
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import m4a_dma_counter as counter
import plausible


class CounterSourceTests(unittest.TestCase):
    header = b"""#ifndef FFTA_H
#define FFTA_H
typedef unsigned char u8; typedef signed char s8;
typedef unsigned short u16; typedef signed short s16;
typedef unsigned int u32; typedef signed int s32;
#endif
"""
    source = '#include "ffta.h"\n' + counter.BODY

    def test_exact_qualifier_only(self):
        self.assertEqual(counter.source_offset(self.source, self.header), self.source.index('volatile'))
        for old, new in [('u32 lockStatus;', 'volatile u32 lockStatus;'),
                         ('volatile u8', 'volatile u16'), ('dmaCounter = 0', 'dmaCounter = 1'),
                         ('0x040000C6', '0x040000C4'), ('volatile u16 *', 'volatile u32 *'),
                         ('0xB600', '0xB601'), ('*data_03007FF0', 'data_03007FF0[1]'),
                         ('if (lockStatus', 'if (*(&soundInfo->dmaCounter) && lockStatus')]:
            with self.subTest(new=new):
                self.assertIsNone(counter.source_offset(self.source.replace(old, new), self.header))
        self.assertIsNone(counter.source_offset(self.source, self.header.replace(b'#endif', b'#define dmaCounter x\n#endif')))
        self.assertTrue(any(rule == 'volatile' for _, rule, _, _ in plausible.check_text(self.source)))

    def test_strip_preserves_hardware(self):
        result = counter.strip_member(self.source)
        self.assertEqual(result, self.source.replace('volatile u8 dmaCounter', 'u8 dmaCounter'))
        for text in [result, self.source + 'volatile u8 dmaCounter;']:
            with self.assertRaises(ValueError):
                counter.strip_member(text)


@unittest.skipUnless(os.getenv('FFTA_M4A_VSYNC_ROOT'), 'needs FFTA USA ROM and indexed VSyncOn source')
class CounterNativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import library_units
        import match
        import match_evidence
        cls.root = Path(os.environ['FFTA_M4A_VSYNC_ROOT']).resolve()
        cls.rom = Path(match_evidence.report_rom_path(cls.root)).read_bytes()
        t = library_units.resolve('old-agbcc-O2-v1')
        args = argparse.Namespace(cc=t['cc'], flags=t['flags'], cpp=match.DEFAULT_CPP,
                                  assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY)
        runner = match.Runner(args.cc, 'Ubuntu', match.DEFAULT_WSL_PATH, root=str(cls.root))
        with runner.workspace() as ws:
            cls.images = [match.compile_object(runner, ws, args, str(cls.root), counter.OWNER,
                          counter.SOURCE, rewrite=change)[2] for change in (None, counter.strip_member)]

    def test_real_objects_and_load_before_store(self):
        for image, qualified in zip(self.images, (True, False)):
            body = counter.bound_object(image, qualified)
            if qualified:
                start = counter.OWNER - counter.BASE
                self.assertEqual(body, self.rom[start:start + 56])
            # MMIO width, store value, guard edge, read or zero, reset target and literal.
            for offset in [12, 16, 22, 24, 28 if qualified else 26, len(body)-4]:
                changed = bytearray(body)
                changed[offset] ^= 2
                with self.subTest(offset=offset, qualified=qualified), self.assertRaises(ValueError):
                    counter.owner_evidence(changed, qualified)

    def test_original_relocation_and_undefined_symbol(self):
        for qualified, original in zip((True, False), self.images):
            for attribute in ('addend', 'relocation type', 'offset', 'size', 'type', 'section', 'bind', 'linked ELF', 'writable text'):
                image = copy.deepcopy(original)
                if attribute == 'addend':
                    text = bytearray(image['text'])
                    text[-12] = 4
                    image['text'] = bytes(text)
                elif attribute in ('offset', 'relocation type'):
                    rel = image['relocations'][0]
                    data = bytearray(image['section_data'][rel])
                    offset, info = struct.unpack_from('<II', data)
                    struct.pack_into('<II', data, 0, offset - 4 if attribute == 'offset' else offset,
                                     info if attribute == 'offset' else (info & ~255) | 3)
                    image['section_data'][rel] = bytes(data)
                elif attribute == 'linked ELF':
                    image['type'] = 2
                elif attribute == 'writable text':
                    index = image['text_index']
                    section = list(image['sections'][index])
                    section[2] |= 1
                    image['sections'][index] = tuple(section)
                else:
                    sym = next(sym for sym in image['symbols'] if sym['name'] == counter.SYMBOL)
                    sym[attribute] = 2
                with self.subTest(attribute=attribute, qualified=qualified), self.assertRaises(ValueError):
                    counter.bound_object(image, qualified)

    def test_irq_vector_slot_setup_caller_and_counter_accesses(self):
        counter.irq_evidence(self.rom)
        rom = bytearray(self.rom)
        # VBlank mask/table, IRQ-vector update, DMA3 copy, slot pointer, BL,
        # same RAM pointer, guard, decrement, reload field, DMA1 tail and PCM use.
        for site in (0x138, 0x1B0, 0x2C4, 0x32C, 0x2410, 0x149434, 0x4B4,
                     0x144D8C, 0x144AFC, 0x144AFE, 0x144B02, 0x144B06,
                     0x144B08, 0x144B20, 0x144B24, 0x144562, 0x14519C, 0x145590):
            rom[site] ^= 2
            with self.subTest(site=hex(counter.BASE+site)), self.assertRaises(ValueError):
                counter.irq_evidence(rom)
            rom[site] ^= 2

    def test_record_replayed_and_mmio_justification_required(self):
        import match_evidence
        report = (self.root / 'docs/match/081457FC.md').read_text()
        line = counter.record(self.root)
        self.assertIn(line, report)
        self.assertTrue(match_evidence.report_matches(report, str(self.root), counter.OWNER))
        for changed in [report.replace(line, ''), report.replace('+4', '+5'), report.replace(line, line+'\n'+line)]:
            with self.assertRaises(ValueError):
                match_evidence.strip_volatile_records(changed, [line])
        self.assertFalse(match_evidence.report_matches(report.replace(line, ''), str(self.root), counter.OWNER))
        start = counter.OWNER - counter.BASE
        extended = self.rom[start:start+60].hex()
        oversized = report.replace(extended[:112], extended).replace('(56 bytes)', '(60 bytes)').replace(
            '56/56 bytes', '60/60 bytes')
        self.assertFalse(match_evidence.report_matches(oversized, str(self.root), counter.OWNER))
        source = (self.root / counter.SOURCE).read_text()
        closure = ({counter.SOURCE, counter.HEADER}, [])
        kwargs = dict(relpath=counter.SOURCE, tree=self.root, project=self.root, closure=closure)
        self.assertFalse(plausible.check_text(source, **kwargs))
        self.assertTrue(any(rule == 'volatile' for _, rule, _, _ in
                            plausible.check_text(source.replace('plausible:', 'routine:'), **kwargs)))
        for name, paths in [('src/other.c', closure), (counter.SOURCE, ({counter.SOURCE}, []))]:
            self.assertTrue(any(rule == 'volatile' for _, rule, _, _ in plausible.check_text(
                source, relpath=name, tree=self.root, project=self.root, closure=paths)))


if __name__ == '__main__':
    unittest.main()
