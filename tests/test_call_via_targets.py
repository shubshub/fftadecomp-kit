"""Call-via thunks beside function literals on the default path (T1).

Natural C callers are compiled with the fixed agbcc and `-mthumb-interwork -O2` and linked at
0x08000200 beside assembled callees (test_data_buffer_calls.build), with agbcc's `_call_via_rN`
thunks at their ROM addresses; match.py runs on the default path and the reports are replayed.
"""
import json
import os
from pathlib import Path
import struct
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
sys.path.insert(0, str(ROOT / "tests"))
import match
import match_evidence as evidence
import data_buffer_profile as data_buffer
import call_via_target_profile as call_via
from test_data_buffer_calls import A, BASE, HEADER, STORES, build, run, tools_present, verification

# The caller itself also calls through a parameter (T1 at the owner's own link).
HOOK = HEADER + """extern void func_08000500(void);
extern void func_08000400(u16 value, u16 *out, void (*callback)(void));
void func_08000200(u16 value, void (*hook)(void))
{
    u16 buffer[4];

    hook();
    func_08000400(value, buffer, func_08000500);
    data_02000000[0] = buffer[0];
    data_02000000[1] = buffer[3];
}
"""


# No typed data: the function-buffer proof (verify_function_buffers), not the data-buffer one.
HOOK_PLAIN = """typedef unsigned short u16;
extern void func_08000500(void);
extern void func_08000400(u16 value, u16 *out, void (*callback)(void));
u16 func_08000200(u16 value, void (*hook)(void))
{
    u16 buffer[4];

    hook();
    func_08000400(value, buffer, func_08000500);
    return buffer[0] + buffer[3];
}
"""
# A numeric code pointer beside the thunk call: no canonical function provenance.
NUMERIC_PLAIN = """typedef unsigned short u16;
extern void func_08000500(void);
extern void func_08000400(u16 value, u16 *out, void (*callback)(void));
u16 func_08000200(u16 value)
{
    u16 buffer[4];
    void (*f)(u16, u16 *) = (void (*)(u16, u16 *))0x08000501;

    func_08000400(value, buffer, func_08000500);
    f(value, 0);
    return buffer[0] + buffer[3];
}
"""


def index_thunks(root):
    """The thunks are indexed two-byte spans, as in the ROM."""
    entries = json.loads((root / "config/functions.json").read_bytes())
    for value in sorted(match.RUNTIME_HELPERS.values()):
        entries.append({"rom": f"0x{value:08X}", "end": f"0x{value + 2:08X}", "mode": "thumb"})
    (root / "config/functions.json").write_text(json.dumps(entries))
    (root / "symbols/functions.txt").write_text("".join(
        f"{int(entry['rom'], 16):08X} {int(entry['end'], 16):08X} "
        f"{int(entry['end'], 16) - int(entry['rom'], 16)} 0 return\n" for entry in entries))
    return root


@unittest.skipUnless(tools_present(), "fixed compiler and ARM tools required")
class CallViaNativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix="call_via_targets_", dir=scratch)
        cls.base = Path(cls.temporary.name)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def replays(self, report, root):
        with patch.dict(os.environ, FFTA_ROM=str(root / "baserom.bin")):
            return evidence.report_matches(report, root, A)

    def admitted(self, root):
        code, output, report = run(root)
        self.assertEqual(code, 0, output)
        self.assertEqual(verification(report), data_buffer.FUNCTION_SCHEMA)
        self.assertTrue(self.replays(report, root))
        return report

    def refused(self, root, message):
        code, output, report = run(root)
        self.assertNotEqual(code, 0, output)
        self.assertIsNone(report)
        self.assertRegex(output, message)
        return output

    def test_owner_thunk_beside_function_literal_and_buffer(self):
        root = index_thunks(build(self.base / "hook", HOOK,
                                  [("func_08000400", STORES), ("func_08000500", "bx lr")], large=True,
                                  function_literal_thunks=True))
        report = self.admitted(root)
        (encoded,) = [line for line in report.splitlines() if line.startswith(data_buffer.MANIFEST_FIELD)]
        manifest = json.loads(encoded[len(data_buffer.MANIFEST_FIELD) + 1:-1])
        self.assertTrue(any(row[1].startswith("_call_via_r") for row in manifest["calls"]), manifest)
        self.assertEqual([row[1] for row in manifest["functions"]], ["func_08000500"])
        # Without the default route the owner's own link keeps refusing function literals beside thunks.
        with self.assertRaisesRegex(match.Refusal, "function-address evidence does not support runtime call thunks"):
            build(self.base / "hook_selector", HOOK, [("func_08000400", STORES), ("func_08000500", "bx lr")],
                  large=True)

    def test_function_buffer_path_binds_thunks_by_their_bytes(self):
        root = index_thunks(build(self.base / "hook_plain", HOOK_PLAIN,
                                  [("func_08000400", STORES), ("func_08000500", "bx lr")], large=True,
                                  function_literal_thunks=True))
        code, output, report = run(root)
        self.assertEqual(code, 0, output)
        self.assertEqual(verification(report), evidence.FUNCTION_BUFFER_SCHEMA)
        self.assertTrue(self.replays(report, root))
        (encoded,) = [line for line in report.splitlines() if line.startswith("* function address manifest: ")]
        names = [row[1] for row in json.loads(encoded[len("* function address manifest: `"):-1])["calls"]]
        (thunk,) = [name for name in names if name.startswith("_call_via_r")]
        # A thunk whose bytes differ does not replay.
        rom = bytearray((root / "baserom.bin").read_bytes())
        address = match.RUNTIME_HELPERS[thunk] - BASE
        rom[address] ^= 8
        (root / "baserom.bin").write_bytes(bytes(rom))
        self.assertFalse(self.replays(report, root))

    def test_numeric_code_pointer_beside_a_thunk_refused(self):
        root = index_thunks(build(self.base / "numeric", NUMERIC_PLAIN,
                                  [("func_08000400", STORES), ("func_08000500", "bx lr")], large=True,
                                  function_literal_thunks=True))
        self.refused(root, "code-entry thunk literals require canonical function provenance")

    def test_default_route_only(self):
        import argparse
        base = dict(control_flow_profile="ordinary")
        self.assertTrue(match.default_call_route(argparse.Namespace(**base)))
        for name in ("owner_runtime_profile", "function_address_profile", "switch_data_profile",
                     "signed_quotient_profile", "unsigned_quotient_profile"):
            with self.subTest(name=name):
                self.assertFalse(match.default_call_route(argparse.Namespace(**base, **{name: "x"})))
        self.assertFalse(match.default_call_route(argparse.Namespace(control_flow_profile="other")))
        self.assertFalse(match.default_call_route(argparse.Namespace(**base), {"tool": "x"}))
        with patch.object(call_via.POLICY, "enabled", False), self.assertRaisesRegex(
                match.Refusal, "function-address evidence does not support runtime call thunks"):
            build(self.base / "hook_policy", HOOK, [("func_08000400", STORES), ("func_08000500", "bx lr")],
                  large=True, function_literal_thunks=True)
