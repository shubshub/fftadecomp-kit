"""Runtime fingerprints resolve loaded sonames without trusting cwd files."""
import hashlib
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import capstone
import addressed_signed_runtime_profile as profile


class RuntimeLibraryTests(unittest.TestCase):
    def fingerprint(self, name, maps=''):
        seen = []
        def read_bytes(path):
            seen.append(str(path))
            return str(path).encode()
        with patch.object(capstone._cs, '_name', name), \
                patch.object(Path, 'read_text', return_value=maps), \
                patch.object(Path, 'read_bytes', read_bytes):
            result = profile.runtime_fingerprint()
        return result, seen

    def test_absolute_library_preserves_existing_identity(self):
        result, seen = self.fingerprint('/libraries/libcapstone.so.5')
        self.assertIn('/libraries/libcapstone.so.5', seen)
        self.assertEqual(result['capstone_native_sha256'],
                         hashlib.sha256(b'/libraries/libcapstone.so.5').hexdigest())

    def test_soname_uses_unique_mapped_path_including_spaces(self):
        path = '/task storage/lib/libcapstone.so.5'
        maps = f'1000-2000 r--p 00000000 08:01 42 {path}\n2000-3000 r-xp 00001000 08:01 42 {path}\n'
        result, seen = self.fingerprint('libcapstone.so.5', maps)
        self.assertIn(path, seen)
        self.assertNotIn('libcapstone.so.5', seen)
        self.assertEqual(result['capstone_native_sha256'], hashlib.sha256(path.encode()).hexdigest())

    def test_missing_deleted_and_ambiguous_libraries_fail_closed(self):
        for maps in ('', '1000-2000 r-xp 0 08:01 42 /lib/libcapstone.so.5 (deleted)\n',
                     '1000-2000 r-xp 0 08:01 42 /first/libcapstone.so.5\n'
                     '2000-3000 r-xp 0 08:01 43 /second/libcapstone.so.5\n'):
            with self.subTest(maps=maps), self.assertRaisesRegex(ValueError, 'unavailable or ambiguous'):
                self.fingerprint('libcapstone.so.5', maps)


if __name__ == '__main__':
    unittest.main(verbosity=2)
