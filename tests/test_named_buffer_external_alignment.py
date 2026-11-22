"""Compiler alignment outside a complete named-buffer owner stays outside it."""
import argparse
import copy
import os
from pathlib import Path
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import named_data_buffer_profile as buffers
import owner_admission_profile as owner


class ExternalAlignmentTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        scratch = Path(os.environ.get('TMPDIR', Path.cwd() / 'build/tests'))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix='external_alignment_', dir=scratch)
        cls.root = Path(cls.temporary.name)
        (cls.root / 'src').mkdir()
        (cls.root / 'src/08010000.c').write_text(
            'void func_08010000(unsigned char *destination)\n'
            '{\n    *destination = 1;\n}\n')
        cls.args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP,
            assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY,
            linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        cls.runner = match.Runner(match.DEFAULT_CC, 'Ubuntu', match.DEFAULT_WSL_PATH,
                                 root=cls.root, timeout=120)
        with cls.runner.workspace() as workspace:
            cls.original, _, cls.image = match.compile_object(cls.runner, workspace,
                cls.args, cls.root, 0x08010000, 'src/08010000.c')
        cls.record, _ = match.function_record(cls.image, 'func_08010000', 0x08010000, True)
        assert cls.record['size'] == 6
        assert cls.image['text'][6:] == b'\xc0\x46'

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def bindings(self, image, selector=buffers.SELECTOR):
        return owner.original_bindings(image, 0x08010000, bytes(0x10008),
                                       b'[]', b'{}', selector=selector)

    def test_original_compiler_padding_preserved_but_not_returned(self):
        before = copy.deepcopy(self.image)
        with self.runner.workspace() as workspace:
            self.runner.write_text(workspace + '/f.i',
                (self.root / 'src/08010000.c').read_text())
            Path(workspace, 'f.o').write_bytes(self.original)
            body, bindings = owner.object_bytes(self.runner, workspace, self.args,
                self.image, 0x08010000, bytes(0x10008), b'[]', b'{}',
                selector=buffers.SELECTOR)
            linked = match.elf_image(self.runner.read_binary(workspace + '/f.elf'))
        self.assertEqual(body, self.image['text'][:6])
        self.assertEqual(linked['text'], self.image['text'])
        self.assertEqual(linked['text'][6:], b'\xc0\x46')
        self.assertEqual(bindings, dict(calls=[], data=[], functions=[], switches=[]))
        self.assertEqual(self.image, before)

    def test_other_trailing_bytes_or_extents_refused(self):
        for suffix in (b'\x00\x00', b'\x70\x47', b'\xc0\x46\xc0\x46', b'\x00'):
            image = copy.deepcopy(self.image)
            image['text'] = image['text'][:6] + suffix
            with self.subTest(suffix=suffix), self.assertRaisesRegex(ValueError, 'sole complete'):
                self.bindings(image)

    def test_other_selectors_keep_their_original_extent_contract(self):
        # restoring-owner-runtime-v1 admits the same closing halfword (its own tests).
        for selector in (owner.ACYCLIC_SELECTOR,):
            with self.subTest(selector=selector), self.assertRaisesRegex(ValueError, 'sole complete'):
                self.bindings(self.image, selector)

    def test_additional_defined_function_or_object_refused(self):
        for kind in (1, 2):
            image = copy.deepcopy(self.image)
            image['symbols'].append(dict(name='extra', type=kind, section=image['text_index'],
                size=2, value=7, bind=1))
            with self.subTest(kind=kind), self.assertRaisesRegex(ValueError, 'sole complete'):
                self.bindings(image)


if __name__ == '__main__':
    unittest.main(verbosity=2)
