"""A restoring owner with a canonical thunk call and a function literal gets a verdict, not a KeyError.

Under restoring-owner-runtime-v1 an owner that calls a `_call_via_rN` thunk has its
data literals checked by function_thunk_profile.verify_data_bindings: no data literal
may name an indexed code entry.  The owner passed every literal there, function
literals included, and the check reads each name from the data-symbol map, so a
function literal raised KeyError.  Function literals are checked by
verify_literal_bindings; only the data bindings belong in the data check.
"""
import copy
from pathlib import Path
import shutil
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import match
import owner_admission_profile as owner
import test_restoring_owner_optional_runtime as base

# Install the callee as a callback in external memory: a typed function literal.
LITERAL = ['ldr r0, .Lcallback', 'str r0, [r5]']
POOL = ['.Lcallback:', '.word func_08011000']
OBJECTS = b'{"data_02010000":"0x02010000"}'
DATA = ['ldr r0, .Lcallback', 'str r0, [r5]', 'ldr r1, .Lobject', 'str r4, [r1]']
DATA_POOL = POOL + ['.Lobject:', '.word data_02010000']


@unittest.skipUnless(shutil.which(match.DEFAULT_AS) and shutil.which(match.DEFAULT_LD),
                     'the fixed binutils are required')
class ThunkFunctionLiteralTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix='owner_thunk_literal_')
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)

    def fixture(self, middle, pool, objects=b'{}', thunk=True):
        directory = self.root / f'f{len(list(self.root.iterdir()))}'
        directory.mkdir()
        fixture = base.Fixture(directory, base.owner_assembly(thunk=thunk, middle=middle, pool=pool))
        fixture.objects = objects
        return fixture.link()

    def test_thunk_owner_with_a_function_literal_gets_a_verdict(self):
        fixture = self.fixture(LITERAL, POOL)
        self.assertEqual([name for _, name in fixture.bindings['functions']], ['func_08011000'])
        manifest, _ = fixture.verify()
        self.assertEqual(manifest['profile'], owner.OPTIONAL_SCHEMA)
        self.assertEqual([name for _, name in manifest['proof']['runtime_calls']], ['_call_via_r3'])
        self.assertEqual(fixture.verify(manifest=manifest)[0], manifest)

    def test_data_literals_are_still_checked_beside_a_function_literal(self):
        fixture = self.fixture(DATA, DATA_POOL, OBJECTS)
        self.assertEqual([name for _, name, _ in fixture.bindings['data']], ['data_02010000'])
        fixture.verify()
        # A data symbol at an indexed code entry is refused by the data check, as before
        # (with the word itself at the entry, verify_literal_bindings refuses it first).
        named = self.fixture(DATA, DATA_POOL[:-1] + ['.word data_08011000+4'],
                             b'{"data_08011000":"0x08011000"}')
        with self.assertRaisesRegex(ValueError, 'thunk callers cannot bind indexed function entries as data'):
            named.verify()
        entry = self.fixture(DATA, DATA_POOL[:-1] + ['.word data_08011000'], b'{"data_08011000":"0x08011000"}')
        with self.assertRaisesRegex(ValueError, 'code-entry thunk literals require canonical function provenance'):
            entry.verify()

    def test_without_a_thunk_the_data_check_does_not_run(self):
        manifest, _ = self.fixture(LITERAL, POOL, thunk=False).verify()
        self.assertEqual(manifest['proof']['runtime_calls'], [])

    def test_forged_function_binding_still_refused(self):
        fixture = self.fixture(LITERAL, POOL)
        bindings = copy.deepcopy(fixture.bindings)
        bindings['functions'] = []
        with self.assertRaises(ValueError):
            fixture.verify(bindings=bindings)


if __name__ == '__main__':
    unittest.main()
