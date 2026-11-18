"""The scene selector composes one initialized SDK halfword and an independent scheduler site."""
from pathlib import Path
import struct
import sys
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
from capstone.arm import ARM_REG_R0, ARM_REG_R2
import conditional_local_buffer_profile as local
import named_data_buffer_profile as named
import scene_scheduler_cpufill as scene

D, E = scene.OWNERS
WRAPPER = scene.bios.WRAPPER


def kernel(owner):
    size, site, dest, offset = scene.OWNERS[owner]
    data = bytearray(size)
    first = site-14
    pool = (site+11) & ~3
    for pc, reg, which in ((first+2, 2, 0), (first+8, 1, 1), (first+10, 2, 2)):
        opcode = (0x48+reg) << 8 | (pool + 4*which - ((pc+4) & ~3))//4
        struct.pack_into('<H', data, pc-owner, opcode)
    for pc, opcode in ((first, 0x4669 if not offset else 0xa900 | offset//4),
                       (first+4, 0x1c10), (first+6, 0x8008),
                       (first+12, 0x4668 if not offset else 0xa800 | offset//4)):
        struct.pack_into('<H', data, pc-owner, opcode)
    struct.pack_into('<III', data, pool-owner, scene.WHITE, dest, scene.CONTROL)
    delta = scene.bios.ADDRESS - site - 4
    struct.pack_into('<HH', data, site-owner, 0xf000 | ((delta>>12)&2047), 0xf800 | ((delta>>1)&2047))
    return data, pool, site


def branch_fixture(address):
    data, _, site = kernel(address)
    scheduler = site+36
    entry = site-14
    edges = {p: [p+2] for p in range(entry, site, 2)}
    edges.update({address: [entry, scheduler], site: [], scheduler: []})
    calls = {site: scene.bios.ADDRESS, scheduler: scene.SCHEDULER}
    proof = SimpleNamespace(rom=b'', mapping=b'', index=b'', scheduler_call_sites={
        'sites': [{'site': scheduler}], 'looped_sites': []})
    return data, site, scheduler, edges, calls, proof


class SceneFillTests(unittest.TestCase):
    def test_two_stack_layouts_and_all_native_inputs(self):
        for address, (size, site, dest, offset) in scene.OWNERS.items():
            data, pool, _ = kernel(address)
            result = scene.fill_evidence(data, address, WRAPPER)
            self.assertEqual((result['store'], result['destination'], result['current_sp_offset']),
                             (site-8, dest, offset))
            for at in (site-14, site-12, site-10, site-8, site-6, site-4, site-2, site,
                       pool, pool+4, pool+8):
                with self.subTest(owner=address, at=at):
                    bad = bytearray(data)
                    bad[at-address] ^= 1
                    with self.assertRaises(ValueError):
                        scene.fill_evidence(bad, address, WRAPPER)
            for changed, wrapper in ((data[:-2], WRAPPER), (data, b'\0'*4)):
                with self.assertRaises(ValueError):
                    scene.fill_evidence(changed, address, wrapper)

    def test_fill_on_all_predecessors_and_separate_paths(self):
        for address in scene.OWNERS:
            data, site, sched, edges, calls, proof = branch_fixture(address)
            with patch.object(scene.bios, 'BiosFillProof', return_value=SimpleNamespace(wrapper=WRAPPER)):
                scene.bind(proof, data, address, edges, calls)
                for origin, target in ((site, sched), (sched, site-14), (site, site-14),
                                       (sched, site-4), (address, site-6)):
                    changed = dict(edges)
                    changed[origin] = [*edges[origin], target]
                    with self.assertRaises(ValueError):
                        scene.bind(proof, data, address, changed, calls)
                with self.assertRaises(ValueError):
                    scene.bind(proof, data, address, edges, {site: scene.bios.ADDRESS})
                with self.assertRaises(ValueError):
                    scene.bind(proof, data, address, edges, calls | {address+2: scene.bios.ADDRESS})

    def test_private_source_register_and_descriptor_do_not_overlap(self):
        proof = SimpleNamespace(scene_fill={'site': 100, 'current_sp_offset': 16},
                                _root_fill=SimpleNamespace(observations={(100,-52,2,0,0)}))
        descriptor = {'aliases': [(ARM_REG_R2, -48)], 'descriptor_offset': -48,
                      'other_pointer_words': [], 'payload_words': [], 'frame_bytes': 68}
        with patch.object(named, 'check_bios_fill_call', return_value={}) as check:
            scene.check_fill(proof, scene.bios.ADDRESS, {ARM_REG_R0:-52}, (0,)*17, {}, 100, {})
            check.assert_called_once()
            for aliases in ({}, {ARM_REG_R0:-48}, {ARM_REG_R0:-52, ARM_REG_R2:-52}):
                with self.assertRaises(ValueError):
                    scene.check_fill(proof, scene.bios.ADDRESS, aliases, (0,)*17, {}, 100, {})
        with patch.object(named.BiosFillSourceProof,'bios_manifest',return_value={'sites': []}):
            scene.manifest(proof, {'observations':[descriptor]})
            for replacement in ({'descriptor_offset': -52, 'aliases': [(ARM_REG_R2,-52)]},
                                {'aliases': []}, {'payload_words': [1]}, {'frame_bytes': 64}):
                with self.assertRaises(ValueError):
                    scene.manifest(proof, {'observations':[descriptor | replacement]})

    def test_only_the_scoped_sdk_store_qualifies(self):
        for address, (_, _, dest, _) in scene.OWNERS.items():
            hdr = 'ffta.h' if address == D else 'control_flags.h'
            symbol = f'data_{dest:08X}'
            text = (f'#include "{hdr}"\nextern void func_0814186C(const void *, void *, u32);\n'
                    'void call(void) { { volatile u16 fill = 0x7FFF; '
                    f'func_0814186C((const void *)&fill, {symbol}, 0x01000010); }} }}\n')
            self.assertEqual(scene.source_offset(text,address), text.index('volatile'))
            for before, after in (('0x7FFF','0x7FFE'), ('u16 fill','u32 fill'),
                                  ('&fill,','&fill+1,'), ('0x01000010','0x01000020'),
                                  (symbol,'other'), ('\nextern','\n#define fill other\nextern')):
                self.assertIsNone(scene.source_offset(text.replace(before,after),address))
            self.assertIsNone(scene.source_offset(text+'extern int fill;\n',address))
        self.assertNotEqual(local.SCHEDULER_CALL_SITES, scene.SELECTOR)
        self.assertNotIn(scene.SELECTOR, named.THUNK_SELECTORS)


if __name__ == '__main__':
    unittest.main()
