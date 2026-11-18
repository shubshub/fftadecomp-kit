import sys
import tempfile
import unittest
from pathlib import Path


sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import cgb_registers as cgb
import plausible


HEADER = "#ifndef FFTA_H\n#define FFTA_H\ntypedef unsigned char u8;\n#endif\n"
DEFINES = '#include "ffta.h"\n#define ACTIVE 0x80\n#define SOUND_CHANNEL_SF_ON (ACTIVE | 3)\n'


def routine():
    # Build a minimal instance of the actual four-channel selection pattern.
    prefix = cgb.ENTRY + " /* plausible: ordered byte sound registers. */\n"
    prefix += "\n".join("volatile u8 *%s;" % name for name in cgb.LOCALS)
    body = prefix + cgb.LOOP
    for i, ports in enumerate(cgb.PORTS):
        body += "case %d:" % (i + 1) if i < 3 else "default:"
        for name, port in zip(cgb.LOCALS, ports):
            body += f"{name} = (volatile u8 *)0x{0x04000000 + port:08X};\n"
        body += "break;\n"
    return DEFINES + body + "}" + "".join("*%s = 1;" % name for name in cgb.LOCALS) + "}}"


class CgbRegistersTests(unittest.TestCase):
    def offsets(self, source):
        return cgb.selected_offsets(source, plausible.strip_comments_and_strings(source))

    def test_exact_group_only(self):
        source = routine()
        offsets = self.offsets(source)
        self.assertEqual(len(offsets), 25)
        self.assertTrue(all(source[i:i + 8] == "volatile" for i in offsets))
        unrelated = source.replace("*nrx0ptr = 1;", "volatile u8 frame; *nrx0ptr = 1;")
        self.assertEqual(len(self.offsets(unrelated)), 25)
        self.assertNotIn(unrelated.index("volatile u8 frame"), self.offsets(unrelated))
        self.assertEqual(len(self.offsets(source.replace("*nrx0ptr = 1;", "*nrx0ptr = (*nrx3ptr & 0x08);"))), 25)

    def test_fail_closed_on_control_binding_or_use_change(self):
        source = routine()
        mutations = [
            ("0x04000060", "0x02000060"), ("0x04000065", "0x04000064"),
            ("0x04000079", "0x04000081"), ("default:", "case 4:"),
            ("continue;", "goto later;"), ("switch (ch)", "switch (ch + 1)"),
            ("break;", "if (ch) break;"), ("0x04000062;", "0x04000062 + ch;"),
            ("volatile u8 *nrx0ptr", "volatile u16 *nrx0ptr"),
            ("(volatile u8 *)0x04000060", "(volatile u16 *)0x04000060"),
            ("*nrx2ptr = 1;", "v = &*nrx2ptr;"), ("*nrx2ptr = 1;", "f(nrx2ptr);"),
            ("*nrx2ptr = 1;", "*nrx2ptr++ = 1;"), ("*nrx2ptr = 1;", "nrx2ptr = ram;"),
            ("*nrx2ptr = 1;", "nrx2ptr[1] = 1;"),
            ("*nrx2ptr = 1;", "{ u8 *nrx2ptr = ram; *nrx2ptr = 1; }"),
            ("*nrx2ptr = 1;", "*nrx2ptr = 1; p = &(*nrx2ptr);"),
            ("plausible:", "note:"), ("void func_", "void outer(void) { void func_"),
            ("*nrx0ptr = 1;", "}} void again(void) {{ *nrx0ptr = 1;"),
        ]
        for old, new in mutations:
            with self.subTest(change=new):
                self.assertNotEqual(source, source.replace(old, new, 1))
                self.assertFalse(self.offsets(source.replace(old, new, 1)))

    def test_file_scope_and_include_closure(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            for subdir in ("include", "config", "src"):
                (root / subdir).mkdir()
            (root / "config/data_symbols.json").write_text("{}")
            (root / cgb.HEADER).write_text(HEADER)
            canonical, other = root / cgb.SOURCE, root / "src/08145CA0.c"
            canonical.write_text(routine())
            other.write_text(routine())
            self.assertEqual(plausible.check_file(canonical), [])
            self.assertTrue(any(row[1] == "volatile" for row in plausible.check_file(other)))
            (root / "include/extra.h").touch()
            canonical.write_text('#include "extra.h"\n' + routine())
            self.assertTrue(any(row[1] == "volatile" for row in plausible.check_file(canonical)))
            canonical.write_text(routine())
            (root / cgb.HEADER).write_text(HEADER.replace("unsigned char", "unsigned short"))
            self.assertTrue(any(row[1] == "volatile" for row in plausible.check_file(canonical)))

    def test_defines_are_numeric_and_base_type_is_unsigned_byte(self):
        self.assertTrue(cgb.literal_defines(DEFINES, HEADER))
        for extra in ("#define nrx0ptr ram", "#define ALIAS nrx1ptr", "#define A(x) x",
                      "#include HEADER", "#define ALIAS (3) | (4", "#define MISSING OTHER",
                      "#undef ACTIVE", "#define ACTIVE 7", "%:define PORT 7", "#if 1"):
            with self.subTest(extra=extra):
                self.assertFalse(cgb.literal_defines(DEFINES + extra + "\n", HEADER))
        for header in (HEADER.replace("unsigned char", "unsigned short"),
                       HEADER + "#define u8 u32\n", HEADER + '#include "other.h"\n'):
            self.assertFalse(cgb.literal_defines(DEFINES, header))


if __name__ == "__main__":
    unittest.main()
