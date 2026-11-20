"""Native palette-copy input proofs and conservative opaque-call behaviour."""

import json
import struct
import unittest

import test_volatile_loop_induction as induction
import scene_palette_copy as scene
import volatile_semantics as semantics


class NativeInputs(unittest.TestCase):
    def fixture(self):
        start, end = scene.OWNER, scene.END
        target = scene.cpuset.ADDRESS
        base = semantics.ROM_BASE
        rom = bytearray(target + 4 - base)
        rom[start-base:end-base] = b'\x00\x20' * ((end-start)//2)
        struct.pack_into('<H', rom, start-base, 0xB500)
        struct.pack_into('<H', rom, end-base-2, 0xBD00)
        for site in scene.SITES:
            delta = target - site - 4
            struct.pack_into('<HHH', rom, site-base-2, 0x225F,
                             0xF000 | (delta >> 12 & 2047), 0xF800 | (delta >> 1 & 2047))
        rom[target-base:target-base+4] = scene.cpuset.WRAPPER
        rows = [(start, end), (target, target+4)]
        mapping = json.dumps([dict(rom=hex(lo), end=hex(hi), mode='thumb') for lo, hi in rows]).encode()
        index = ''.join(f'{lo:08X} {hi:08X} {hi-lo}\n' for lo, hi in rows).encode()
        return rom, mapping, index

    def test_complete_closed_owner_and_wrapped_service(self):
        rom, mapping, index = self.fixture()
        scene.native_inputs(scene.OWNER, bytes(rom), mapping, index)

    def test_changed_service_return_control_or_bl_refuses(self):
        for address, new in [(scene.cpuset.ADDRESS, 0xDF0C), (scene.cpuset.ADDRESS+2, 0x4718),
                             (scene.SITES[1]-2, 0x225E), (scene.SITES[1]+2, 0xF800)]:
            with self.subTest(address=address):
                rom, mapping, index = self.fixture()
                struct.pack_into('<H', rom, address-semantics.ROM_BASE, new)
                with self.assertRaises(ValueError):
                    scene.native_inputs(scene.OWNER, bytes(rom), mapping, index)

    def test_alternate_edge_bypassing_control_refuses(self):
        rom, mapping, index = self.fixture()
        # BNE +0 from BL-4 reaches the BL directly, bypassing MOVS R2,#95.
        struct.pack_into('<H', rom, scene.SITES[0]-semantics.ROM_BASE-4, 0xD100)
        with self.assertRaisesRegex(ValueError, 'every reaching path'):
            scene.native_inputs(scene.OWNER, bytes(rom), mapping, index)

    def test_paired_indexes_must_describe_the_complete_wrapper(self):
        rom, mapping, index = self.fixture()
        for bad_mapping, bad_index in [
                (mapping.replace(b'0x8141870', b'0x8141872'), index),
                (mapping, index.replace(b'08141870 4', b'08141872 6'))]:
            with self.assertRaises(ValueError):
                scene.native_inputs(scene.OWNER, bytes(rom), bad_mapping, bad_index)


class RegisterInputs(induction.Base):
    def compare_scene(self, before, after=(), name=scene.cpuset.NAME, selected=True):
        declarations = induction.PREPROCESSED + f'\nextern void {name}(int, int, int);\n'
        body = induction.FRAME + induction.loop() + (
                'mov\tr0, #1', 'mov\tr1, #2', 'mov\tr2, #95', *before, 'bl\t'+name,
                *after) + induction.MEMBER + induction.END
        provider = self.interfaces()
        return self.compare(body, scene.CopyInputs(provider) if selected else provider, declarations)

    def test_r3_is_an_unnamed_input_only_for_the_unselected_case(self):
        different = (('real', 'mov\tr3, #7'), ('stripped', 'mov\tr3, #8'))
        self.compare_scene(different)
        with self.assertRaises(semantics.SemanticError):
            self.compare_scene(different, selected=False)
        with self.assertRaises(semantics.SemanticError):
            self.compare_scene(different, name='func_08000300')

    def test_named_inputs_and_postcall_r3_are_observable(self):
        self.compare_scene(('mov\tr3, #7',), ('str\tr3, [r5]',))
        for reg in ('r0', 'r1', 'r2'):
            with self.subTest(reg=reg), self.assertRaises(semantics.SemanticError):
                self.compare_scene((('real', f'mov\t{reg}, #7'), ('stripped', f'mov\t{reg}, #8')))
        with self.assertRaises(semantics.SemanticError):
            self.compare_scene((('real', 'mov\tr3, #7'), ('stripped', 'mov\tr3, #8')),
                               ('str\tr3, [r5]',))


if __name__ == '__main__':
    unittest.main()
