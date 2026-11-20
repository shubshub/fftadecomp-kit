"""Particle projection, machine return provenance and complete original caller continuations."""

import os
from pathlib import Path
import struct
import subprocess
import sys
import tempfile
import unittest

from capstone.arm import ARM_REG_R0, ARM_REG_R2, ARM_REG_R3

TOOLS = Path(__file__).resolve().parents[1] / 'tools'
sys.path.insert(0, str(TOOLS))
import match
import match_evidence
import named_data_buffer_profile as named
import particle_return_scratch_profile as particle
import runtime_summary_profile as summary


def replace(data, offset, fmt, *values):
    out = bytearray(data)
    struct.pack_into(fmt, out, offset, *values)
    return bytes(out)


class RootProjectionTests(unittest.TestCase):
    def test_only_bound_exact_type_one_register_one_offset_at_native_return(self):
        p = object.__new__(summary.ParticleReturnScratchProof)
        p.active = set()
        p.particle_data = b'test owner'
        p.projected_halfwords = True
        p.consumers = ['authenticated']
        alias = {ARM_REG_R3: -22}
        apply = named.root_return_scratch_aliases
        self.assertEqual(apply(p, p.particle_data, particle.ROOT, particle.RETURN, alias), {})
        for address, site, data, aliases in [
            (particle.PROJECT, particle.RETURN, p.particle_data, alias),
            (particle.ROOT, particle.RETURN+2, p.particle_data, alias),
            (particle.ROOT, particle.RETURN, b'other', alias),
            (particle.ROOT, particle.RETURN, p.particle_data, {ARM_REG_R0: -22}),
            (particle.ROOT, particle.RETURN, p.particle_data, {ARM_REG_R2: -22}),
            (particle.ROOT, particle.RETURN, p.particle_data, {ARM_REG_R3: -24}),
            (particle.ROOT, particle.RETURN, p.particle_data, {ARM_REG_R3: -22.0}),
            (particle.ROOT, particle.RETURN, p.particle_data, {ARM_REG_R3: -22, ARM_REG_R0: -24}),
        ]:
            self.assertEqual(apply(p, data, address, site, aliases), aliases)
        for name, changed in [('active', {particle.PROJECT}), ('consumers', []), ('projected_halfwords', False)]:
            before = getattr(p, name)
            setattr(p, name, changed)
            self.assertEqual(apply(p, p.particle_data, particle.ROOT, particle.RETURN, alias), alias)
            setattr(p, name, before)
        class Unregistered(summary.ParticleReturnScratchProof):
            pass
        self.assertEqual(apply(object.__new__(Unregistered), b'', particle.ROOT, particle.RETURN, alias), alias)
        self.assertFalse(named.root_scratch_join_dead(p, p.particle_data, particle.ROOT,
                         particle.RETURN, ARM_REG_R3, -22, -24, particle.decoder()))

    def test_frame_size_output_offsets_and_outgoing_slot(self):
        p = object.__new__(summary.ParticleReturnScratchProof)
        p.active = set()
        for depth, first, incoming, slots in [
            (6, -24, {0: -22}, {-28}), (7, -22, {0: -22}, {-28}),
            (7, -24, {0: -24}, {-28}), (7, -24, {4: -22}, {-28}),
            (7, -24, {0: -22}, {-24}),
        ]:
            with self.subTest(depth=depth, first=first, incoming=incoming), self.assertRaisesRegex(ValueError, 'halfwords'):
                p.check_arguments(particle.PROJECT, {ARM_REG_R3: first}, [None]*depth,
                                  incoming, slots, site=particle.PROJECTION_SITE)


@unittest.skipUnless(os.environ.get('FFTA_PARTICLE_ROOT'), 'set FFTA_PARTICLE_ROOT to the recovered USA game root')
class NativeParticleTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.game = Path(os.environ['FFTA_PARTICLE_ROOT']).resolve()
        cls.rom = (cls.game/'baserom.bin').read_bytes()
        cls.mapping = (cls.game/'config/functions.json').read_bytes()
        cls.index = (cls.game/'symbols/functions.txt').read_bytes()
        cls.objects = (cls.game/'config/data_symbols.json').read_bytes()
        cls.proof = summary.ParticleReturnScratchProof(cls.rom, cls.mapping, cls.index, cls.objects)

    def native(self, address):
        return self.rom[address-match.ROM_BASE:particle.SPANS[address]-match.ROM_BASE]

    def test_raw_thumb_references_and_unaligned_pointer_words(self):
        sites = particle.raw_references(self.rom)['raw_thumb_bl_sites']
        self.assertEqual(tuple(sites), particle.SITES)
        for value in (particle.ROOT, particle.ROOT | 1):
            with self.assertRaisesRegex(ValueError, 'pointer'):
                particle.raw_references(replace(self.rom, 0x1001, '<I', value))
        with self.assertRaisesRegex(ValueError, 'call inventory'):
            particle.raw_references(replace(self.rom, particle.SITES[0]-match.ROM_BASE, '<H', 0x46C0))
        extra = particle.SITES[0] + 4
        delta = particle.ROOT - (extra+4)
        with self.assertRaisesRegex(ValueError, 'call inventory'):
            particle.raw_references(replace(self.rom, extra-match.ROM_BASE, '<HH',
                    0xF000 | ((delta >> 12) & 0x7FF), 0xF800 | ((delta >> 1) & 0x7FF)))
        with self.assertRaisesRegex(ValueError, 'approved USA'):
            particle.raw_references(replace(self.rom, 0x1001, '<B', self.rom[0x1001] ^ 1))

    def test_kill_before_read_in_all_three_continuations(self):
        cs = particle.decoder()
        callers = particle.consumers(self.proof)
        second = callers[1]['witness']
        self.assertEqual((second['closed_instructions'], second['switches']), (1032, 1))
        rows = [continuation for caller in callers for continuation in caller['continuations']]
        self.assertEqual([r['setup_example']['selector'] for r in rows], [0, 0, 1])
        self.assertEqual([r['overwrite'] for r in rows], [0x080AE12E, 0x080B2F10, 0x080B2F10])
        self.assertEqual([len(r['path']) for r in rows], [10, 4, 9])
        for row in rows:
            site, address = row['call'], row['caller']
            data = self.native(address)
            for location, half in [(site+4, 0x0018), (site+4, 0x6013),  # movs r0,r3 / str r3,[r2]
                                   (site+4, 0x4770), (site+4, 0xE7FE),  # bx lr / live self-loop
                                   (row['overwrite'], 0x46C0)]:
                altered = replace(data, location-address, '<H', half)
                with self.subTest(site=site, at=location, word=half), self.assertRaises(ValueError):
                    particle.continuation(altered, address, site, cs)
            outgoing = row['setup_example']
            with self.assertRaisesRegex(ValueError, 'outgoing arguments'):
                particle.continuation(replace(data, outgoing['selector_store']-address, '<H', 0x9402),
                                      address, site, cs)

    def test_guarded_route_table_index_and_projection_width(self):
        cs = particle.decoder()
        data = self.native(particle.FIRST)
        case = particle.first_caller_route(data, cs)
        self.assertEqual((case['route_instructions'], case['case'], case['destination']), (73, 4, 0x080AE0D2))
        for pc, word in [(0x080AD8EA, 0x2805), (0x080AD8F4, 0x4901), (0x080AD68C, 0xE017)]:
            with self.assertRaises(ValueError):
                particle.first_caller_route(replace(data, pc-particle.FIRST, '<H', word), cs)
        with self.assertRaisesRegex(ValueError, 'wrong case four'):
            particle.first_caller_route(replace(data, case['table']+16-particle.FIRST, '<I', case['destination']+2), cs)
        altered = replace(self.rom, 0x0801C9DA-match.ROM_BASE, '<H', 0x6039)  # word store, not STRH
        proof = summary.ParticleReturnScratchProof(altered, self.mapping, self.index, self.objects)
        with self.assertRaisesRegex(ValueError, 'halfword stores'):
            particle.particle_abi(proof, proof.span(particle.ROOT))
        truncated = self.index.replace(b'080B264C 080B2F1E', b'080B264C 080B2F1C')
        self.assertNotEqual(truncated, self.index)
        proof = summary.ParticleReturnScratchProof(self.rom, self.mapping, truncated, self.objects)
        with self.assertRaisesRegex(ValueError, 'index'):
            particle.consumers(proof)

    def test_native_cli_and_saved_evidence(self):
        with tempfile.TemporaryDirectory() as directory:
            game = Path(directory)
            for item in ('baserom.bin', 'config', 'include', 'symbols'):
                (game/item).symlink_to(self.game/item, target_is_directory=(self.game/item).is_dir())
            (game/'src').mkdir()
            src = game/'src/080A97EC.c'
            natural = (self.game/'src'/src.name).read_text()
            src.write_text(natural)
            command = [sys.executable, '-B', str(TOOLS/'match.py'), '--root', str(game),
                       '080A97EC', '--owner-runtime-profile']
            for old, why in [(summary.SELECTOR, 'return register'), (named.ROOT_SCRATCH_SELECTOR, 'canonical addressed function')]:
                refused = subprocess.run(command+[old], capture_output=True, text=True)
                self.assertNotEqual(refused.returncode, 0)
                self.assertIn(why, refused.stderr)
            hit = subprocess.run(command+[named.PARTICLE_SELECTOR], capture_output=True, text=True)
            self.assertEqual(hit.returncode, 0, hit.stderr)
            self.assertIn('340 bytes', hit.stdout)
            report = (game/'docs/match/080A97EC.md').read_text()
            replay = lambda text: match_evidence.report_matches(text, str(game), particle.ROOT)
            self.assertTrue(replay(report))
            for old, new in [('"returned_scratch":["r3",-22]', '"returned_scratch":["r3",-24]'),
                             ('"selector_width_bits":8', '"selector_width_bits":16'),
                             ('"route_instructions":73', '"route_instructions":72')]:
                self.assertIn(old, report)
                self.assertFalse(replay(report.replace(old, new)))
            src.write_text(natural.replace('extern u32 func_08002804(void);',
                        'extern u32 func_08002804(void);\nextern s32 func_08142950(s32, s32);').replace(
                        '(s16)func_08002804() % 3', 'func_08142950((s16)func_08002804(), 3)'))
            self.assertFalse(replay(report))
            refused = subprocess.run(command+[named.PARTICLE_SELECTOR], capture_output=True, text=True)
            self.assertNotEqual(refused.returncode, 0)
            self.assertIn('compiler __modsi3 binding', refused.stderr)


class CallerDecodeTests(unittest.TestCase):
    # Capstone's Thumb mode also decodes Thumb-2 and ARMv5 encodings, which the ARM7TDMI does not execute.
    def test_refuses_thumb_outside_armv4t(self):
        cs = particle.decoder()
        for name, words in [('cbz r0', (0xB100,)), ('cbnz r0', (0xB900,)), ('bkpt #0', (0xBE00,)),
                            ('Thumb-2 mov.w r1, #0', (0xF04F, 0x0100))]:
            data = struct.pack(f'<{1+len(words)}H', 0x2000, *words)  # each after an ARMv4T movs r0, #0
            with self.subTest(name):
                self.assertEqual(particle.decode(cs, data, particle.ROOT, particle.ROOT).mnemonic, 'movs')
                # Capstone decodes the item, so only the ARMv4T check can refuse it.
                self.assertIsNotNone(next(cs.disasm(data[2:], particle.ROOT+2, count=1), None))
                with self.assertRaisesRegex(ValueError, 'invalid particle caller Thumb instruction'):
                    particle.decode(cs, data, particle.ROOT, particle.ROOT+2)

    def test_accepts_an_armv4t_sequence(self):
        cs = particle.decoder()
        # push {r4, lr}; adds r4, r0, #0; bl (a BL pair); movs r0, #0; pop {r4}; pop {r1}; bx r1
        data = struct.pack('<8H', 0xB510, 0x1C04, 0xF000, 0xF800, 0x2000, 0xBC10, 0xBC02, 0x4708)
        pc, mnemonics = particle.ROOT, []
        while pc < particle.ROOT + len(data):
            item = particle.decode(cs, data, particle.ROOT, pc)
            mnemonics.append(item.mnemonic)
            pc += item.size
        self.assertEqual(mnemonics, ['push', 'adds', 'bl', 'movs', 'pop', 'pop', 'bx'])


if __name__ == '__main__':
    unittest.main()
