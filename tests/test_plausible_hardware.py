import sys
from pathlib import Path
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import plausible


class HardwareVolatileTests(unittest.TestCase):
    comment = "/* plausible: DMA3 hardware requires ordered access and polling. */\n"
    declaration = "extern DmaRegisters dma3;\n"
    binding = "volatile DmaRegisters *dma = &dma3;\n"
    mapping = {"dma3": "0x040000D4"}

    def rules(self, source, mapping=None):
        return [rule for _, rule, _, _ in plausible.check_text(
            source, data_symbols=mapping)]

    def test_documented_direct_hardware_access(self):
        self.assertEqual(self.rules(self.comment +
            "*(volatile u16 *)0x04000000 = value;"), [])

    def test_mapped_pointer_member_access_and_polling(self):
        source = self.declaration + self.comment + self.binding + (
            "dma->source = source; dma->destination = destination;\n"
            "dma->control = control; value = dma->control;\n"
            "while (dma->control & 0x80000000) value = dma->control;\n")
        self.assertEqual(self.rules(source, self.mapping), [])
        self.assertEqual(self.rules(source.replace("*dma", "* const dma"), self.mapping), [])

    def test_duplicate_scoped_bindings_and_comment_text(self):
        block = "{\n" + self.comment + self.binding + "dma->control = value;\n}\n"
        self.assertEqual(self.rules(self.declaration + block + block, self.mapping), [])
        self.assertEqual(self.rules("/* header\ntext */\n" + self.comment +
            "*(volatile u16 *)0x04000000 = value;"), [])

    def test_unjustified_or_fake_comment_remains_rejected(self):
        access = "*(volatile u16 *)0x04000000 = value;"
        for prefix in ("", 'const char *s = "plausible: hardware";\n', self.comment + "\n"):
            with self.subTest(prefix=prefix):
                self.assertIn("volatile", self.rules(prefix + access))

    def test_ram_locals_and_outside_register_window_remain_rejected(self):
        for source in ("volatile int local;", "volatile int local = 0x040000D4;",
                       "*(volatile u16 *)0x02000000 = value;",
                       "*(volatile u16 *)0x04000400 = value;",
                       "*(volatile u16 *)0x04000000 + offset;"):
            with self.subTest(source=source):
                self.assertIn("volatile", self.rules(self.comment + source))

    def test_mapping_and_external_declaration_required(self):
        source = self.declaration + self.comment + self.binding
        for mapping in ({}, {"dma3": "0x020000D4"}, {"dma3": "invalid"}):
            with self.subTest(mapping=mapping):
                self.assertIn("volatile", self.rules(source, mapping))
        self.assertIn("volatile", self.rules(self.comment + self.binding, self.mapping))
        self.assertIn("volatile", self.rules(source + "DmaRegisters dma3;", self.mapping))

    def test_pointer_retargeting_escape_and_shadowing_are_rejected(self):
        source = self.declaration + self.comment + self.binding
        for suffix in ("dma = ram;", "dma++;", "dma += 1;", "escape(&dma);",
                       "escape(dma);", "int dma;", "value = &dma->control;"):
            with self.subTest(suffix=suffix):
                self.assertIn("volatile", self.rules(source + suffix, self.mapping))

    def test_other_errors_cannot_be_justified(self):
        for source, rule in (("asm(\"nop\");", "inline-asm"),
                             ("if (0) update();", "dead-code"),
                             ("#pragma GCC optimize(0)", "optimize-pragma")):
            with self.subTest(source=source):
                self.assertIn(rule, self.rules(self.comment + source))


if __name__ == "__main__":
    unittest.main()
