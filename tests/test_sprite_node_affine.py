import copy
import os
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import named_data_buffer_profile as named
import owner_admission_profile as owner
import sprite_node_affine as sprite


class RecordBounds(unittest.TestCase):
    def test_missing_scalars_wrong_stride_and_saved_words(self):
        aliases = {sprite.R0: -84, sprite.R0 + 1: -76, sprite.R0 + 4: -76}
        constants = {sprite.R0 + 2: 1, sprite.R0 + 3: 2}
        # These fixture words use the same (return, saved, local) tuple as
        # verify_leaf_instructions. Only the original 60 bytes are locals.
        stack = [(False, False, True)] * 15 + [(False, True, False)] * 8
        sprite.local_records(aliases, stack, {}, {}, constants)
        for changes in ({sprite.R0 + 2: 2}, {sprite.R0 + 3: 8}, {sprite.R0 + 2: None},
                        {sprite.R0 + 2: True}):
            with self.subTest(changes=changes), self.assertRaises(ValueError):
                sprite.local_records(aliases, stack, {}, {}, {**constants, **changes})
        for register, new in ((sprite.R0, -76), (sprite.R0+1, -74), (sprite.IP, -38)):
            with self.subTest(register=register), self.assertRaises(ValueError):
                sprite.local_records({**aliases, register: new}, stack, {}, {}, constants)
        for slot in (2, 3, 4, 5):
            damaged = stack.copy()
            damaged[slot] = (False, True, False)
            with self.subTest(saved_word=slot), self.assertRaises(ValueError):
                sprite.local_records(aliases, damaged, {}, {}, constants)
        for slot in (4, 5):
            damaged = stack.copy()
            damaged[slot] = (True, False, True)
            with self.subTest(return_word=slot), self.assertRaises(ValueError):
                sprite.local_records(aliases, damaged, {}, {}, constants)
        with self.assertRaises(ValueError):
            sprite.local_records(aliases, stack, {-76: -38}, {}, constants)


@unittest.skipUnless(os.getenv('FFTA_SPRITE_NODE_ROOT'), 'requires the original game and two refined index rows')
class OriginalSprite(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        root = Path(os.environ['FFTA_SPRITE_NODE_ROOT'])
        cls.rom = (root / 'baserom.bin').read_bytes()
        cls.mapping = (root / 'config/functions.json').read_bytes()
        cls.index = (root / 'symbols/functions.txt').read_bytes()
        cls.objects = (root / 'config/data_symbols.json').read_bytes()
        cls.data = cls.rom[sprite.ROOT-match.ROM_BASE:sprite.ROOT-match.ROM_BASE+348]

    def proof(self, rom=None, index=None):
        return sprite.SpriteAffineProof(self.rom if rom is None else rom, self.mapping,
                                       self.index if index is None else index, self.objects)

    def native(self, bindings):
        return owner.verify(self.data, sprite.ROOT, self.rom, self.mapping, self.index, self.objects,
                            selector=named.ROOT_SCRATCH_SELECTOR, bindings=bindings)

    def test_complete_native_walk(self):
        manifest, verified = self.native(sprite.BINDINGS)
        self.assertEqual(len(verified), 172)
        buffers = manifest['proof']['buffers']
        receipt = buffers['sprite_node_affine']
        self.assertEqual(buffers['root_return_scratch']['observations'], [[346, 2, -40]])
        self.assertEqual(receipt['output_halfwords'], [16, 18, 20, 22])
        self.assertEqual(receipt['root_y_alias'], dict(register='IP', root_sp_offset=38,
                                                       possible_after_BIOS=True))
        self.assertEqual(manifest['bindings'], sprite.BINDINGS)
        self.assertEqual({d['address'] for d in buffers['dependencies']},
                         {sprite.RENDER, sprite.MATRIX, sprite.WRAPPER})

    def test_wrong_elf_and_missing_index_correction(self):
        wrong = copy.deepcopy(sprite.BINDINGS)
        wrong['calls'][0][1] = 'func_08001F34'
        with self.assertRaises(ValueError):
            self.native(wrong)
        wrong = self.index.replace(b'080216F8 08021854   348 172', b'080216F8 08021854   348 174')
        self.assertNotEqual(wrong, self.index)
        with self.assertRaisesRegex(ValueError, '172 original'):
            self.proof(index=wrong).bind_return_root(sprite.ROOT, self.data)

    def test_mutated_bios_veneer_frame_setup_caller_and_leaf(self):
        for address in (sprite.WRAPPER, sprite.WRAPPER + 2, 0x0800191C, 0x0800191E,
                        0x08001920, 0x08001928, 0x08021F78, sprite.MATRIX):
            rom = bytearray(self.rom)
            rom[address-match.ROM_BASE] ^= 1
            with self.subTest(address=hex(address)), self.assertRaises(ValueError):
                self.proof(bytes(rom)).bind_return_root(sprite.ROOT, self.data)

    def test_second_walk_preserves_ip_and_rejects_escaping_aliases(self):
        proof = self.proof()
        proof.bind_return_root(sprite.ROOT, self.data)
        proof.active.add(sprite.RENDER)
        proof.seen.update(('draw', 'renderer frame'))
        stack = [(False, False, True)] * 11 + [(False, True, False)] * 8
        args = {sprite.IP: -38}
        kwargs = dict(site=sprite.BIOS_CALL)
        self.assertEqual(proof.check_arguments(sprite.WRAPPER, args, stack, {}, frozenset(), **kwargs),
                         args)
        for alias in ({sprite.IP: -40}, {sprite.R0: -38}, {sprite.IP: -38, sprite.R0+2: -38}):
            with self.subTest(alias=alias), self.assertRaises(ValueError):
                proof.check_arguments(sprite.WRAPPER, alias, stack, {}, frozenset(), **kwargs)
        with self.assertRaises(ValueError):
            proof.check_arguments(sprite.WRAPPER, args, stack, {}, {-40}, **kwargs)
        with self.assertRaises(ValueError):
            proof.check_arguments(sprite.WRAPPER, args, stack, {}, frozenset(), site=sprite.BIOS_CALL+2)
        with self.assertRaises(ValueError):
            proof.manifest(sprite.BINDINGS)


if __name__ == '__main__':
    unittest.main()
