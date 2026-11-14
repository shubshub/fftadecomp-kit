"""The own-span rule for thunk callers outside the canonical-thunk manifest.

Synthetic bytes only; no game ROM or compiler.  A thunk caller whose reached
PC-relative literal names its own bytes (A+8, inside the call, with or without
the Thumb bit) is refused on the legacy buffer replay (manifest=None) and on
the ordinary match.py path; the same caller with a RAM literal is admitted.
"""
from contextlib import contextmanager, ExitStack, redirect_stdout
import io
import json
import os
from pathlib import Path
import struct
import sys
import tempfile
import unittest
from unittest.mock import patch

CASE = Path(__file__).resolve().parents[1]
sys.dont_write_bytecode = True
sys.path.insert(0, str(CASE / "tools"))
import match
import match_evidence as evidence
import function_thunk_profile as profile
import test_interposed_pool_thunks as interposed

A = match.ROM_BASE + 0x10000
THUNK = profile.ALIASES["_call_via_r3"]
OUTSIDE = 0x02001000
OWN = (A + 8, A + 9)


def bl(site, target):
    offset = target - site - 4
    return struct.pack("<HH", 0xF000 | ((offset >> 12) & 0x7FF), 0xF800 | ((offset >> 1) & 0x7FF))


def caller(value):
    """push {lr}; ldr r3,=value; bl _call_via_r3; pop {r0}; bx r0; .word value"""
    return struct.pack("<HH", 0xB500, 0x4B02) + bl(A + 4, THUNK) + struct.pack("<HHI", 0xBC01, 0x4700, value)


@contextmanager
def tree(data, address=A, mapping=None, rom=None):
    scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", CASE / "build"))
    scratch.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="own_span_", dir=scratch) as directory:
        root = Path(directory)
        for child in ("src", "include", "config", "symbols"):
            (root / child).mkdir()
        (root / f"src/{address:08X}.c").write_text("void synthetic(void);\n")
        if mapping is None:
            mapping = json.dumps([dict(rom=f"0x{address:08X}", end=f"0x{address + len(data):08X}",
                                       mode="thumb")]).encode()
        if rom is None:
            image = bytearray(profile.END - match.ROM_BASE)
            image[address - match.ROM_BASE:address - match.ROM_BASE + len(data)] = data
            struct.pack_into("<HH", image, THUNK - match.ROM_BASE, 0x4718, 0x46C0)
            rom = bytes(image)
        (root / "config/functions.json").write_bytes(mapping)
        (root / "config/data_symbols.json").write_bytes(b"{}")
        (root / "symbols/functions.txt").write_text(
            f"{address:08X} {address + len(data):08X} {len(data)} 5 bx\n")
        (root / "baserom.bin").write_bytes(rom)
        with patch.dict(os.environ, {"FFTA_ROM": str(root / "baserom.bin")}):
            yield root


class Runner:
    def __init__(self, *args, **kwargs):
        pass

    @contextmanager
    def workspace(self):
        yield "/synthetic-workspace"


def boundaries(data, calls, switches=None):
    """Only the compiler, the linker and the plausibility subprocess are replaced."""
    def link(*args, **kwargs):
        if switches:
            args[10].update(switches)  # the ordinary path's switch_relocations
        return data, calls, {}
    return [patch.object(match, "Runner", Runner),
            patch.object(match, "compile_object", return_value=(b"", None, {"relocations": [1]})),
            patch.object(match, "link_calls", side_effect=link),
            patch.object(match, "_run_replay_process", return_value=object()),
            patch.object(match, "plausibility_result", return_value=([], None))]


@contextmanager
def applied(patches):
    with ExitStack() as stack:
        for item in patches:
            stack.enter_context(item)
        yield


class LegacyBufferReplay(unittest.TestCase):
    """function_thunk_profile.verify_source with manifest=None (no buffer proof)."""

    def replay(self, value):
        data = caller(value)
        with tree(data) as root, applied(boundaries(data, {A + 4: THUNK})):
            return profile.verify_source(root, A, data, (root / "baserom.bin").read_bytes(),
                                         evidence.mapping_snapshot(root), profile.index_snapshot(root),
                                         evidence.data_snapshot(root), evidence.source_fingerprint(root, A))

    def test_outside_literal_is_admitted(self):
        self.assertTrue(self.replay(OUTSIDE))

    def test_literal_naming_the_callers_own_bytes_is_refused(self):
        for value in OWN:
            with self.subTest(value=value), self.assertRaisesRegex(ValueError, "caller's own bytes"):
                self.replay(value)


class OrdinaryMatchPath(unittest.TestCase):
    """match.main with no thunk selector, for a caller that reaches a thunk."""

    def run_main(self, data, calls, address=A, switches=None, **environment):
        with tree(data, address, **environment) as root, applied(boundaries(data, calls, switches)), \
                patch.object(sys, "argv", ["match.py", "--root", str(root), "--no-write", f"0x{address:08X}"]), \
                redirect_stdout(io.StringIO()) as output:
            try:
                code = match.main()
            except SystemExit as error:
                code = error.code
        return code, output.getvalue()

    def test_outside_literal_is_admitted(self):
        code, output = self.run_main(caller(OUTSIDE), {A + 4: THUNK})
        self.assertEqual(code, 0)
        self.assertIn("16/16 bytes", output)

    def test_literal_naming_the_callers_own_bytes_is_refused(self):
        for value in OWN:
            with self.subTest(value=value):
                code, _ = self.run_main(caller(value), {A + 4: THUNK})
                self.assertIn("caller's own bytes", str(code))

    def test_switch_callers_with_a_thunk_call_are_refused_before_the_own_span_rule(self):
        # Without a thunk selector the switch evidence refuses the thunk call
        # itself, so the own-span rule never sees a switch table pointer here.
        f = interposed.fixture(interposed=0)
        code, _ = self.run_main(f["data"], f["calls"], interposed.A, f["switches"],
                                mapping=f["mapping"], rom=f["rom"])
        self.assertIn("does not support runtime call thunks", str(code))


if __name__ == "__main__":
    unittest.main()
