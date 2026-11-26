"""kit#375, rules P and T: planted and unbound reads through a typed pointer or copy are refused.

A typeof carries the pinned members' qualifiers off the object, onto the typed
pointer's target or the typed copy.  The semantic check pairs only loads of
`symbol + k` by member, so these regressions were admitted before:
- T1, T1b, T2: a planted or doubled read of the copy (the stripped compile makes
  no such load);
- T3, T4: a local struct holding the copy (frame loads the stripped compile
  does not make);
- P1, P2, P3: a read or store through the pointer before, or without, its
  binding.
Now every load outside the object, frame loads included, must be the stripped
compile's load in order when P or T admits a typeof; the pointer's binding must
dominate its uses; a local copy is refused on every route; and neither rule is
admitted on the overwritten-store composition route.  The controls (P0, T0, an
R4 re-read) still pass.
"""
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import match
import plausible
import volatile_semantics as semantics
import test_volatile_semantics as fixtures_module

SYMBOL = "g_control_flags_03000940"
BINDING = {"helper": 0x081443FC, "site": 0x08028C40, "selector": "named-data-buffer-compiler-copy80-binding-v1"}
PREFIX = "#include \"control_flags.h\"\ntypedef unsigned int u32;\n"

FIXTURES = [
    ('T1', True, 'refuse', 'a planted read of the copy after the save', 'typedef struct {\n    u8 unknown_00[0x64];\n    __typeof__(g_control_flags_03000940) control;\n} State080200C8;\n\nvoid func_08028C34(State080200C8 *state)\n{\n    state->control = g_control_flags_03000940;\n    (void)state->control.bg0cnt;\n}\n'),
    ('T1b', True, 'refuse', 'a copy member read twice, which the stripped compile reads once', 'typedef struct {\n    u8 unknown_00[0x64];\n    __typeof__(g_control_flags_03000940) control;\n} State08027208;\n\nvoid func_08028C34(State08027208 *state)\n{\n    state->control = g_control_flags_03000940;\n    g_control_flags_03000940.display = state->control.bg0cnt + state->control.bg0cnt;\n}\n'),
    ('T2', False, 'refuse', 'no save, a planted read of the copy', 'typedef struct {\n    u8 unknown_00[0x64];\n    __typeof__(g_control_flags_03000940) control;\n} State080213DC;\n\nvoid func_08028C34(State080213DC *state)\n{\n    (void)state->control.bg0cnt;\n    g_control_flags_03000940.display = state->control.display;\n}\n'),
    ('T3', True, 'refuse', 'a local struct holding the copy, saved, then a planted read', 'typedef struct {\n    u8 unknown_00[4];\n    __typeof__(g_control_flags_03000940) control;\n} State08027918;\n\nextern void func_08001234(void *);\n\nvoid func_08028C34(void)\n{\n    State08027918 local;\n    local.control = g_control_flags_03000940;\n    (void)local.control.bg0cnt;\n    g_control_flags_03000940.display = local.control.display;\n}\n'),
    ('T4', False, 'refuse', "a local instance of the copy's struct, never saved, read", 'typedef struct {\n    u8 unknown_00[4];\n    __typeof__(g_control_flags_03000940) control;\n} State0802B164;\n\nvoid func_08028C34(void)\n{\n    State0802B164 local;\n    (void)local.control.bg0cnt;\n    g_control_flags_03000940.display = 1;\n}\n'),
    ('P1', False, 'refuse', 'the typed pointer read before its binding', 'void func_08028C34(void)\n{\n    __typeof__(g_control_flags_03000940) *control;\n    (void)control->bg0cnt;\n    control = &g_control_flags_03000940;\n    control->display = 1;\n}\n'),
    ('P2', False, 'refuse', 'the typed pointer bound on one path, read on the other', 'void func_08028C34(int flag)\n{\n    __typeof__(g_control_flags_03000940) *control;\n    if (flag) {\n        control = &g_control_flags_03000940;\n        control->display = 1;\n        return;\n    }\n    (void)control->bg1cnt;\n}\n'),
    ('P3', False, 'refuse', 'the typed pointer bound in a nested block, stored through after it', 'void func_08028C34(int flag)\n{\n    __typeof__(g_control_flags_03000940) *control;\n    if (flag) {\n        control = &g_control_flags_03000940;\n    }\n    control->bg0cnt = 5;\n}\n'),
    ('P0', False, 'admit', 'the 08125FA8 shape', 'extern void *func_081443FC(void *, const void *, u32);\n\nvoid func_08028C34(u8 *saved)\n{\n    __typeof__(g_control_flags_03000940) *control;\n    control = &g_control_flags_03000940;\n    func_081443FC(saved, control, 0x50);\n    control->display |= 0xC00;\n    control->bldcnt_lo &= ~0x1C;\n}\n'),
    ('T0', True, 'admit', 'the 08125A5C shape', 'typedef struct {\n    u8 unknown_00[0x64];\n    __typeof__(g_control_flags_03000940) control;\n} State0802A6A0;\n\nvoid func_08028C34(State0802A6A0 *state, int restore)\n{\n    if (restore) {\n        g_control_flags_03000940.display = state->control.display;\n        g_control_flags_03000940.bldcnt_lo = state->control.bldcnt_lo;\n        g_control_flags_03000940.bldcnt_hi = state->control.bldcnt_hi;\n        return;\n    }\n    state->control = g_control_flags_03000940;\n}\n'),
    ('R4', False, 'admit', 'a re-read stored after the test, then the member changed', 'extern u8 data_02000000[];\n\nvoid func_08028C34(u8 x)\n{\n    u8 value;\n    g_control_flags_03000940.bldy_lo = x;\n    value = g_control_flags_03000940.bldy_lo;\n    if (value == 9) {\n        g_control_flags_03000940.bldy_lo = 0;\n        data_02000000[0] = value;\n    }\n}\n'),
]


@unittest.skipUnless(Path(os.path.expandvars(match.DEFAULT_CC)).is_file() and shutil.which("cpp") and
                     shutil.which(match.DEFAULT_AS) and shutil.which(match.DEFAULT_OBJCOPY), "fixed compiler required")
class CompiledRegressionTests(unittest.TestCase):
    """the semantic check through agbcc, with the copy80 route's memcpy binding where the fixture saves"""

    @classmethod
    def setUpClass(cls):
        cls.directory = tempfile.TemporaryDirectory()
        cls.root = Path(cls.directory.name)
        entry = plausible.volatile_allow_entries()[0]
        for name in ("config", "src", "include"):
            (cls.root / name).mkdir()
        (cls.root / "config" / "data_symbols.json").write_text(
            json.dumps({entry["symbol"]: entry["address"], "data_02000000": "0x02000000"}))
        (cls.root / entry["header"]).write_text(fixtures_module.HEADER.format(
            declaration=entry["declaration"].replace("; ", ";\n    ")))

    @classmethod
    def tearDownClass(cls):
        cls.directory.cleanup()

    def check(self, source, binding):
        (self.root / "src" / "08028C34.c").write_text(PREFIX + source)
        token = semantics.COMPILER_COPY.set(BINDING if binding else None)
        try:
            with mock.patch.dict(os.environ, FFTA_ROM=str(self.root / "baserom.bin")):
                return match._allowlisted_volatile_compiles(
                    self.root, 0x08028C34, argparse_namespace(), runner(self.root),
                    plausible.allowlisted_volatile_used(self.root, 0x08028C34), "src/08028C34.c", None, None, None,
                    False)
        finally:
            semantics.COMPILER_COPY.reset(token)

    def test_each_regression_is_refused_and_each_control_admitted(self):
        for key, binding, expect, what, source in FIXTURES:
            with self.subTest(fixture=key, what=what):
                if expect == "admit":
                    (line,) = self.check(source, binding)
                    self.assertTrue(line.startswith("* allowlisted volatile semantics: "), line)
                else:
                    with self.assertRaises((ValueError, semantics.SemanticError)):
                        self.check(source, binding)

    def test_the_refusal_reasons(self):
        reasons = {"T1": "is not the stripped compile's load there", "T1b": "is not the stripped compile's load there",
                   "T2": "is not the stripped compile's load there", "T3": "a local instance of the struct",
                   "T4": "a local instance of the struct", "P1": "is used before its binding",
                   "P2": "must be bound in its declaration's own block", "P3": "must be bound in its declaration's own block"}
        for key, binding, expect, what, source in FIXTURES:
            if key in reasons:
                with self.subTest(fixture=key), self.assertRaises((ValueError, semantics.SemanticError)) as caught:
                    self.check(source, binding)
                self.assertIn(reasons[key], str(caught.exception))


def argparse_namespace():
    import argparse
    return argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                              objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS,
                              owner_runtime_profile=None)


def runner(root):
    return match.Runner(match.DEFAULT_CC, "Ubuntu", match.DEFAULT_WSL_PATH, root=str(root), timeout=300)


if __name__ == "__main__":
    unittest.main()
