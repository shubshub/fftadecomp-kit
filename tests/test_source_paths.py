"""Discovery parity with the original pathlib implementation."""
import hashlib
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
from match_evidence import source_paths, source_fingerprint


def original(root, address):
    root = Path(root)
    paths = {q for q in (root / "src").rglob(f"{address:08X}.c")}
    include = root / "include"
    if include.is_dir():
        paths.update(path for path in include.rglob("*") if path.is_file())
    paths.update((root / "src").rglob("*.h"))
    return sorted(paths)


class SourcePathsTests(unittest.TestCase):
    def setUp(self):
        (ROOT / "build").mkdir(exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(dir=ROOT / "build")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def put(self, name):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(name)
        return path

    def parity(self):
        for address in (0x0808A0B4, 0x08000000):
            self.assertEqual(source_paths(self.root, address), original(self.root, address))

    def test_nested_duplicates_hidden_and_mutations(self):
        self.parity()
        for name in ("src/0808A0B4.c", "src/nested/0808A0B4.c",
                     "src/.hidden/0808A0B4.c", "src/nested/a.h", "src/.h",
                     "src/unrelated.c", "src/0808a0b4.c", "src/upper.H",
                     "include/nested/data.bin", "include/.hidden",
                     "include/.dir/a.h"):
            self.put(name)
            self.parity()
        expected = hashlib.sha256()
        for path in original(self.root, 0x0808A0B4):
            name = path.relative_to(self.root).as_posix().encode()
            data = path.read_bytes()
            expected.update(len(name).to_bytes(8, "little"))
            expected.update(name)
            expected.update(len(data).to_bytes(8, "little"))
            expected.update(data)
        self.assertEqual(source_fingerprint(self.root, 0x0808A0B4), expected.hexdigest())
        (self.root / "src/nested/0808A0B4.c").unlink()
        self.parity()

    def test_directory_matches_and_symlinks(self):
        self.put("outside/0808A0B4.c")
        self.put("outside/a.h")
        self.put("include/real")
        (self.root / "src").mkdir()
        (self.root / "src/directory.h").mkdir()
        (self.root / "src/0808A0B4.c").mkdir()
        for name, target in (("src/link", "../outside"),
                             ("src/link.h", "../outside"),
                             ("src/broken.h", "missing"),
                             ("src/file.h", "../outside/a.h"),
                             ("include/link", "../outside"),
                             ("include/broken", "missing"),
                             ("include/alias", "real")):
            (self.root / name).symlink_to(target)
        self.parity()

    def test_symlinked_roots(self):
        self.put("real_src/0808A0B4.c")
        self.put("real_src/nested/a.h")
        self.put("real_include/nested/data")
        (self.root / "src").symlink_to("real_src", target_is_directory=True)
        (self.root / "include").symlink_to("real_include", target_is_directory=True)
        self.parity()


if __name__ == "__main__":
    unittest.main()
