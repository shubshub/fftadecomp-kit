"""Closed-unit ELF ownership and real old-agbcc multiply replay."""
import argparse
from contextlib import redirect_stdout
import io
import copy
from pathlib import Path
import json
import os
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import library_units as units
import match
import match_evidence as evidence
import status
import unit_float_multiply_profile as multiply


class AdmissionTests(unittest.TestCase):
    def test_pinned_owner_toolchain_and_object(self):
        row = dict(name="libgcc fp-bit, _cmpdi2, _lshrdi3", start="0x081439C8", end="0x081443AE",
                   proof="0x0814435C", toolchain="old-agbcc-O2-v1",
                   identity=[dict(address="0x081439C8", size=2534,
                                  sha256="29f04fc63c3da5f6796be91008ee1c5537db51b98999a6886b3a7b47dd09c92c")])
        def admitted(row, address=0x08143CEC, orphan=None):
            return multiply.SCHEMA in units.schemas(units.Unit(row, units.canonical(row)), address, orphan)

        self.assertTrue(admitted(row))
        self.assertFalse(admitted(row, 0x08143E54))
        self.assertFalse(admitted(row, orphan={}))
        self.assertNotIn(multiply.SCHEMA, units.schemas())
        for key, value in dict(identity=[], name="dp-bit", start="0x081439CA", end="0x081443AC",
                               proof="0x08143CEC", toolchain="agbcc-O1-v1").items():
            with self.subTest(key=key):
                self.assertFalse(admitted(dict(row, **{key: value})))


class NativeTests(unittest.TestCase):
    def setUp(self):
        game = Path(os.environ.get("FFTA_ROOT", ROOT.parent / "fftadecomp")).resolve()
        self.addr = multiply.ADDRESS
        self.src = Path("src/08143CEC.c")
        cc = units.TOOLCHAINS[multiply.TOOLCHAIN]["cc"]
        rom = Path(os.environ.get("FFTA_ROM", game / "baserom.bin")).resolve()
        if not (game/self.src).is_file() or not rom.is_file() or not Path(os.path.expandvars(cc)).is_file():
            self.skipTest("requires fp-bit source in FFTA_ROOT, FFTA_ROM and old_agbcc")
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT/"build"))
        scratch.mkdir(parents=True, exist_ok=True)
        tmp = self.enterContext(tempfile.TemporaryDirectory(dir=scratch))
        self.root = Path(tmp)
        self.enterContext(patch.dict(os.environ, TMPDIR=tmp, FFTA_ROM=str(rom)))
        for path in (*evidence.source_paths(game, self.addr), game/units.TABLE, game/"config/functions.json",
                     game/"config/data_symbols.json", game/"symbols/functions.txt"):
            target = self.root/path.relative_to(game)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(path, target)
        self.args = argparse.Namespace(cc=cc, flags=match.DEFAULT_FLAGS, cpp=match.DEFAULT_CPP,
                                      assembler=match.DEFAULT_AS, linker=match.DEFAULT_LD, objcopy=match.DEFAULT_OBJCOPY)

    def test_elf_requires_compiler_aliases_zero_addends_and_all_sites(self):
        runner = match.Runner(self.args.cc, root=self.root)
        with runner.workspace() as workspace:
            _, _, original = match.compile_object(runner, workspace, self.args, self.root, self.addr, self.src.as_posix())
        multiply.original_bindings(original)
        for cause in ("addressed alias", "weak symbol", "nonzero BL addend", "missing REL", "nonzero object addend"):
            image = copy.deepcopy(original)
            target = next(s for s in image["symbols"] if s["name"] == "__muldi3")
            if cause == "addressed alias":
                target["name"] = "func_08142A20"
            elif cause == "weak symbol":
                target["bind"] = 2
            elif cause == "missing REL":
                image["relocations"] = []
            else:
                text = bytearray(image["text"])
                text[0xc8 if cause == "nonzero BL addend" else 0x80] ^= 1
                image["text"] = bytes(text)
            with self.subTest(cause=cause), self.assertRaises(ValueError):
                multiply.original_bindings(image)

    def test_canonical_replay_and_forgery(self):
        body, report = multiply.build(self.root, self.addr, self.args)
        self.assertEqual(units.sha(body), "ddb81777890d79690a3c02c5d524f54fcf019175aa88f81f1355ef91fb70e10e")
        self.assertTrue(evidence.report_matches(report, self.root, self.addr))
        args = argparse.Namespace(**vars(self.args), label=None, emit=None, no_write=True)
        output = io.StringIO()
        with redirect_stdout(output):
            self.assertEqual(multiply.issue(self.root, self.addr, args), 0)
        self.assertEqual(status.matcher_extent(output.getvalue()), len(body))
        self.assertFalse(evidence.report_matches(report.replace("171,", "170,", 1), self.root, self.addr))
        _, _, digest, _ = units.binding(report)
        self.assertFalse(evidence.report_matches(report.replace(digest, "0"*64), self.root, self.addr))
        code = (self.root / self.src).read_text()
        code = "extern long long __muldi3(long long, long long);\n" + code.replace(
            "(long long)a->fraction * (long long)b->fraction", "__muldi3(a->fraction, b->fraction)")
        (self.root / self.src).write_text(code)
        with self.assertRaisesRegex(ValueError, "compiler-generated"):
            multiply.build(self.root, self.addr, self.args)
        objects = self.root / "config/data_symbols.json"
        bindings = json.loads(objects.read_bytes())
        bindings[multiply.OBJECT] = "0x03005E78"
        with self.assertRaisesRegex(ValueError, "named NaN record"):
            multiply.native_proof(body, Path(os.environ["FFTA_ROM"]).read_bytes(),
                                  (self.root/"config/functions.json").read_bytes(),
                                  (self.root/"symbols/functions.txt").read_bytes(), json.dumps(bindings).encode())


if __name__ == "__main__":
    unittest.main()
