"""New combined-only checks; reuse fixtures without running either old test suite."""
import contextlib
import hashlib
import inspect
import io
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parents[1]
PRODUCTION = Path(os.environ.get('FFTA_TEST_PRODUCTION_KIT', HERE))
sys.dont_write_bytecode = True
sys.path[:0] = [str(HERE/'tools'), str(PRODUCTION/'tools'), str(HERE/'tests')]
import match
import function_thunk_profile as thunks
import umod_r1_thunk_profile as r1
import unsigned_divmod_profile as divmod
import test_umod_r1_thunk_source as r1_fixtures
import test_unsigned_divmod_profile as divmod_fixtures


class PipelineBoundary(Exception):
    pass


class UnsignedRuntimeCoexistenceTests(unittest.TestCase):
    def setUp(self):
        scratch = Path(os.environ['FFTA_TEST_SCRATCH'])
        scratch.mkdir(parents=True, exist_ok=True)
        temporary = tempfile.TemporaryDirectory(prefix='coexist_', dir=scratch)
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        guard = patch.object(subprocess, 'run', side_effect=AssertionError('real subprocess forbidden'))
        guard.start(); self.addCleanup(guard.stop)
        runner = patch.object(match, 'Runner', side_effect=AssertionError('real compiler forbidden'))
        runner.start(); self.addCleanup(runner.stop)

    @contextlib.contextmanager
    def fixture(self, cls, method):
        case = cls(method)
        try:
            case.setUp()
            yield case
        finally:
            case.doCleanups()

    def test_01_both_original_ELF_paths_survive_the_shared_guard_merge(self):
        with self.fixture(r1_fixtures.UmodR1SourceTests,
                'test_synthetic_complete_frame_divisor_and_typed_pool') as f:
            original, linked = f.images()
            with patch.object(r1_fixtures.inventory.remainder, 'verify_identity'):
                calls, functions, literals = thunks.original_bindings(original,
                    r1_fixtures.A, f.mapping, f.rom, f.objects, selector=r1.SELECTOR)
            targets = {'__umodsi3': r1_fixtures.inventory.remainder.ADDRESS,
                r1_fixtures.inventory.THUNK: r1_fixtures.inventory.THUNK_ADDRESS,
                'synthetic_object': r1_fixtures.OBJECT}
            body = match.linked_function_bytes(original, linked, r1_fixtures.NAME,
                r1_fixtures.A, calls, targets, literals, functions, {}, function_thunks=True,
                umodsi3_bindings={site:'__umodsi3' for site, target in calls.items()
                    if target == r1_fixtures.inventory.remainder.ADDRESS},
                umod_r1_profile=r1.SELECTOR)
            self.assertEqual(body, f.body)
        with self.fixture(divmod_fixtures.UnsignedDivmodCompositionTests,
                'test_01_complete_unsigned_composition_and_ordered_memory_effects') as f:
            data = f.fixture()
            original = match.elf_image(divmod_fixtures.elf_bytes(data))
            linked = match.elf_image(divmod_fixtures.elf_bytes(data, linked=True))
            (calls, targets, literals), options = f.bind(data, original)
            body = match.linked_function_bytes(original, linked,
                f'func_{divmod_fixtures.A:08X}', divmod_fixtures.A, calls, targets,
                literals, **options)
            self.assertEqual(body, data['data'])

    def test_02_both_selectors_together_refuse_before_ELF_or_source_execution(self):
        options = dict(function_thunks=True, umodsi3_bindings={}, udivsi3_bindings={},
            umod_r1_profile=r1.SELECTOR, unsigned_runtime_profile=divmod.SELECTOR)
        with self.assertRaises(ValueError):
            match.call_bindings({}, 'func_08010000', 0x08010000, b'[]', 0, b'', {}, {}, {}, **options)
        with self.assertRaises(ValueError):
            match.linked_function_bytes({}, {}, 'func_08010000', 0x08010000,
                {}, {}, {}, {}, {}, **options)
        with self.assertRaises(ValueError):
            match.link_calls(None, None, None, {}, 0x08010000, b'[]', 0,
                b'', {}, {}, {}, **options)
        argv = ['match.py', '--root', str(self.root), '--unsigned-runtime-profile',
            divmod.SELECTOR, '--function-address-profile', r1.SELECTOR, '0x08010000']
        with patch.object(sys, 'argv', argv), patch.object(match, 'repo_root', return_value=str(self.root)), \
                patch.object(divmod, 'build', side_effect=AssertionError('mixed source replay forbidden')):
            with self.assertRaisesRegex(ValueError, 'isolated fixed Thumb selector'):
                match.main()

    def test_03_report_namespaces_and_actual_combined_producer_hashes_stay_separate(self):
        first = f'* verification: `{r1.SCHEMA}`\n* function-address thunks: {r1.SELECTOR}\n'
        second = f'* verification: `{divmod.SCHEMA}`\n* unsigned runtime: {divmod.SELECTOR}\n'
        self.assertEqual(thunks.selector_for_report(first), r1.SELECTOR)
        self.assertFalse(divmod.selector_for_report(first))
        self.assertEqual(divmod.selector_for_report(second), divmod.SELECTOR)
        self.assertIsNone(thunks.selector_for_report(second))
        for select in (thunks.selector_for_report, divmod.selector_for_report):
            with self.assertRaises(ValueError):
                select(first + second)
        digest = hashlib.sha256(Path(match.__file__).read_bytes()).hexdigest()
        left, right = r1.producer_sources(), divmod.producers()
        self.assertEqual(left['match.py'], digest)
        self.assertEqual(right['match.py'], digest)
        self.assertIn('umod_r1_thunk_profile.py', left)
        self.assertIn('unsigned_divmod_profile.py', right)
        self.assertEqual(set(thunks.SELECTORS), {thunks.SELECTOR, thunks.ZERO_SELECTOR, r1.SELECTOR,
                                                thunks.INTERPOSED_SELECTOR, thunks.UNSIGNED_SELECTOR})
        self.assertEqual(thunks.schema_for(thunks.SELECTOR), thunks.SCHEMA)
        self.assertEqual(thunks.schema_for(thunks.ZERO_SELECTOR), thunks.ZERO_SCHEMA)
        # Both forwarding paths remain in actual integrated lifecycle sources.
        status_source = Path(HERE/'tools/status.py').read_text()
        self.assertIn('command += ["--unsigned-runtime-profile", unsigned_runtime_profile]', status_source)
        self.assertIn('command += ["--function-address-profile", thunk_profile]', status_source)
        evidence_source = Path(HERE/'tools/match_evidence.py').read_text()
        self.assertIn('unsigned_divmod_profile.report_matches(report, root, address)', evidence_source)
        self.assertIn('function_thunk.report_matches(report, root, address)', evidence_source)

    def test_04_link_forwarding_carries_exactly_one_explicit_context_and_DEFAULT_none(self):
        for function in (match.call_bindings, match.linked_function_bytes, match.link_calls):
            parameters = inspect.signature(function).parameters
            for name in ('umod_r1_profile', 'unsigned_runtime_profile'):
                self.assertIs(parameters[name].default, None)
                self.assertIs(parameters[name].kind, inspect.Parameter.KEYWORD_ONLY)
        contexts = [dict(function_thunks=True, umodsi3_bindings={},
                        umod_r1_profile=r1.SELECTOR),
                    dict(udivsi3_bindings={}, umodsi3_bindings={},
                        unsigned_runtime_profile=divmod.SELECTOR), {}]
        for supplied in contexts:
            with patch.object(match, 'call_bindings', side_effect=PipelineBoundary) as capture:
                with self.assertRaises(PipelineBoundary):
                    match.link_calls(None, None, None, {}, 0x08010000, b'[]', 0,
                        b'', None, {} if supplied.get('function_thunks') else None,
                        {} if supplied.get('function_thunks') else None, **supplied)
                actual = capture.call_args.kwargs
                for name in ('umod_r1_profile', 'unsigned_runtime_profile'):
                    self.assertEqual(actual[name], supplied.get(name))


if __name__ == '__main__':
    unittest.main()
