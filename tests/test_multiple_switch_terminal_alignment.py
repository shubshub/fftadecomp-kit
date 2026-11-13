"""The explicit multi-switch source route permits only canonical external alignment."""
import copy
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

import addressed_signed_runtime_profile as alignment
import match
import multiple_switch_native_profile as native
import owner_admission_profile as owner

ADDRESS = 0x08010000


class MultipleSwitchTerminalAlignmentTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(dir=os.environ['TMPDIR'])
        self.addCleanup(self.directory.cleanup)
        root = Path(self.directory.name)
        source = root / 'envelope.s'
        source.write_text('.syntax unified\n.thumb\n.global func_08010000\n'
            '.type func_08010000,%function\n.thumb_func\nfunc_08010000:\nbx lr\n'
            '.size func_08010000,.-func_08010000\n.balign 4\n')
        subprocess.run([match.DEFAULT_AS, '-mthumb-interwork', str(source),
                        '-o', str(root / 'envelope.o')], check=True, capture_output=True)
        self.image = match.elf_image((root / 'envelope.o').read_bytes())
        self.mapping = json.dumps([dict(rom='0x08010000', end='0x08010002',
                                       mode='thumb', instrs=1)]).encode()

    def bindings(self, image, selector=native.SELECTOR):
        return owner.original_bindings(image, ADDRESS, b'', self.mapping, b'{}',
                                       selector=selector)

    def test_canonical_external_alignment_does_not_enlarge_symbol(self):
        self.assertEqual(self.image['text'], b'\x70\x47\xc0\x46')
        result, _ = self.bindings(self.image)
        self.assertEqual(result, dict(calls=[], data=[], functions=[], switches=[]))
        symbol, _ = match.function_record(self.image, 'func_08010000', ADDRESS, True)
        self.assertEqual(symbol['size'], 2)

    def test_default_owner_remains_strict(self):
        with self.assertRaisesRegex(ValueError, 'sole complete Thumb ELF'):
            self.bindings(self.image, owner.SELECTOR)

    def test_noncanonical_padding_and_ownership_fail_closed(self):
        for kind in ('padding', 'extra-padding', 'alignment', 'flags', 'symbol-owner', 'size'):
            image = copy.deepcopy(self.image)
            if kind == 'padding':
                image['text'] = image['text'][:2] + b'\0\0'
            elif kind == 'extra-padding':
                image['text'] += b'\xc0\x46'
            elif kind in ('alignment', 'flags'):
                section = list(image['sections'][image['text_index']])
                section[8 if kind == 'alignment' else 2] = 2
                image['sections'][image['text_index']] = section
            elif kind == 'symbol-owner':
                image['symbols'].append(dict(name='owned_tail', value=2, size=2,
                    type=0, bind=1, section=image['text_index']))
            else:
                symbol, _ = match.function_record(image, 'func_08010000', ADDRESS, True)
                symbol['size'] = 1
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                self.bindings(image)

    def test_native_environment_binds_alignment_producer(self):
        environment = native.environment_fingerprint()
        expected = hashlib.sha256(Path(alignment.__file__).read_bytes()).hexdigest()
        self.assertEqual(environment['producers']['addressed_signed_runtime_profile'], expected)


if __name__ == '__main__':
    unittest.main()
