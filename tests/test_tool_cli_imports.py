"""Every tool with a command-line entry point imports in a fresh interpreter."""
from pathlib import Path
import re
import subprocess
import sys
import unittest

TOOLS = Path(__file__).resolve().parents[1] / 'tools'
MAIN = re.compile(r'''^if __name__ *== *['"]__main__['"]''', re.M)


class ToolCliImportTests(unittest.TestCase):
    def test_each_cli_module_imports_first(self):
        names = sorted(path.stem for path in TOOLS.glob('*.py') if MAIN.search(path.read_text(encoding='utf-8')))
        self.assertTrue(names)
        for name in names:
            with self.subTest(module=name):
                run = subprocess.run([sys.executable, '-c', f'import {name}'], cwd=TOOLS,
                                     capture_output=True, text=True, timeout=120,
                                     env={'PYTHONDONTWRITEBYTECODE': '1', 'PATH': '/usr/bin:/bin'})
                self.assertEqual(run.returncode, 0, run.stderr[-2000:])


if __name__ == '__main__':
    unittest.main()
