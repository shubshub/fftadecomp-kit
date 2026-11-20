"""Kit#357 item 1: the hardware-register exception holds only for an access inside the I/O window.

The direct form `*(volatile T *)ADDR` admits a scalar T with no `&` in front;
the bound form `volatile T *local = &symbol;` admits a scalar T or a struct of
scalars and pointers, defined in the same text, that fits in the window from
the symbol's address.  With --addr, the census also checks that cpp leaves each
admitted qualifier where the exception holds (the macro shapes in #357's
comment).
"""
import json
from pathlib import Path
import subprocess
import sys
import unittest

sys.dont_write_bytecode = True
TOOLS = Path(__file__).resolve().parents[1] / "tools"
sys.path.insert(0, str(TOOLS))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import plausible
from test_plausible_volatile_spellings import CensusTree, HAVE_CPP

COMMENT = "/* plausible: hardware register, volatile is required here */\n"
DMA = "typedef struct { const void *source; void *destination; u32 control; } DmaRegisters;\n"


def rules(source, mapping=None):
    return [rule for _, rule, _, _ in plausible.check_text(source, data_symbols=mapping or {},
                                                           volatile_allow=[])]


class DirectFormTests(unittest.TestCase):
    def test_issue_reproducers_are_refused(self):
        arithmetic = ("void f(void)\n{\n" + COMMENT + "    *((&*(volatile u16 *)0x04000000) - 0x1000000) = 1;\n"
                      + COMMENT + "    *((&*(volatile u16 *)0x04000000) - 0x1000000) = 2;\n}\n")
        member = ("typedef struct { unsigned char unknown_00[0x01000000]; u16 value; } IoWindow;\n"
                  "u16 g(void)\n{\n" + COMMENT + "    return (*(volatile IoWindow *)0x04000000).value;\n}\n")
        self.assertEqual(rules(arithmetic), ["volatile", "volatile"])
        self.assertEqual(rules(member), ["volatile"])
        self.assertEqual(rules(COMMENT + "*(volatile u16 *)0x04000000 = v;\n"), [])

    def test_only_scalar_integer_types(self):
        for ctype in ("u8", "u16", "u32", "s8", "s16", "s32", "char", "signed char", "unsigned char",
                      "short", "short int", "unsigned short", "unsigned short int", "int", "unsigned int",
                      "unsigned", "signed", "long", "unsigned long", "long int"):
            with self.subTest(ctype=ctype):
                self.assertEqual(rules(COMMENT + f"*(volatile {ctype} *)0x04000000 = v;\n"), [])
        for ctype in ("struct Regs", "union Regs", "Regs", "IoWindow", "void", "u64", "long long",
                      "unsigned long long", "float", "vu16"):
            with self.subTest(ctype=ctype):
                self.assertEqual(rules(COMMENT + f"*(volatile {ctype} *)0x04000000 = v;\n"), ["volatile"])

    def test_the_whole_access_must_fit_in_the_window(self):
        for ctype, address, ok in (("u32", 0x040003FC, True), ("u32", 0x040003FD, False),
                                   ("u16", 0x040003FE, True), ("u16", 0x040003FF, False),
                                   ("u8", 0x040003FF, True), ("u8", 0x04000400, False),
                                   ("u8", 0x03FFFFFF, False)):
            with self.subTest(ctype=ctype, address=hex(address)):
                self.assertEqual(rules(COMMENT + f"*(volatile {ctype} *)0x{address:08X} = v;\n"),
                                 [] if ok else ["volatile"])

    def test_an_address_taken_access_is_refused(self):
        for expression in ("p = &*(volatile u16 *)0x04000000;", "p = & *(volatile u16 *)0x04000000;",
                           "p = &(*(volatile u16 *)0x04000000);", "p = &((*(volatile u16 *)0x04000000));",
                           "return &*(volatile u16 *)0x04000000;", "p = (u16 *)&*(volatile u16 *)0x04000000;",
                           "f(&*(volatile u16 *)0x04000000);", "p = c ? &*(volatile u16 *)0x04000000 : q;"):
            with self.subTest(expression=expression):
                self.assertEqual(rules(COMMENT + expression + "\n"), ["volatile"])

    def test_an_address_taken_through_any_grouping_is_refused(self):
        # review-357 C1: GNU comma lvalues, casts and any depth of parentheses
        deep = "(" * 300 + "*(volatile u16 *)0x04000000" + ")" * 300
        for expression in ("(&(0, *(volatile u16 *)0x04000000))[-0x1000000] = 1;",
                           "(&(a, b, *(volatile u16 *)0x04000000))[-0x1000000] = 1;",
                           "(&" + deep + ")[-0x1000000] = 1;",
                           "p = &" + " " * 300 + "*(volatile u16 *)0x04000000;",
                           "p = (u16 *)&(u16)*(volatile u16 *)0x04000000;",
                           "p = &(u16)(*(volatile u16 *)0x04000000);",
                           # a cast after `return` or after a control header is still a cast
                           "return (u16 *)&*(volatile u16 *)0x04000000;",
                           "if (c) (u16 *)&*(volatile u16 *)0x04000000;",
                           # a stray close bracket, as an unused conditional branch can leave, pairs with nothing
                           "(&(0, a ], *(volatile u16 *)0x04000000))[-0x1000000] = 1;",
                           "return &(*(volatile u16 *)0x04000000);",
                           "lo = (&(0, *(volatile u8 *)0x04000000))[data + 2 - (const u8 *)0x04000000];"):
            with self.subTest(expression=expression[:60]):
                self.assertEqual(rules(COMMENT + expression + "\n"), ["volatile"])

    def test_a_binary_and_after_a_parenthesised_operand_or_a_literal(self):
        # review-357 MINOR 2: an expression group, a call or a literal before `&` is an operand
        for expression in ("return (a | b) & *(volatile u16 *)0x04000130;",
                           "x = f(y) & *(volatile u16 *)0x04000130;",
                           "x = 'c' & *(volatile u8 *)0x04000130;",
                           "x = \"s\"[0] & *(volatile u8 *)0x04000130;",
                           "if (f(*(volatile u16 *)0x04000130)) x = 1;",
                           "x = (u16)(*(volatile u16 *)0x04000130) & 1;",
                           # the access is a call's argument, whatever is done with the call's result
                           "p = &(*f(*(volatile u16 *)0x04000130));",
                           # a statement inside a statement expression ends the walk
                           "x = &(a, ({ *(volatile u16 *)0x04000130 = 1; b; }));"):
            with self.subTest(expression=expression):
                self.assertEqual(rules(COMMENT + expression + "\n"), [])
        # a lone name in parentheses may be a type, so without the unit's typedefs it counts as a cast
        self.assertEqual(rules(COMMENT + "x = (a) & *(volatile u16 *)0x04000130;\n"), ["volatile"])

    def test_transparent_keywords_do_not_hide_an_ampersand(self):
        # review-357 delta C1': `__extension__` and `__real__` keep the lvalue, so `&` reaches through them
        for expression in ("(&__extension__ *(volatile u16 *)0x04000000)[-0x1000000] = 1;",
                           "(__extension__ &*(volatile u16 *)0x04000000)[-0x1000000] = 1;",
                           "(&__real__ *(volatile u16 *)0x04000000)[-0x1000000] = 1;",
                           "(&__imag__ (*(volatile u16 *)0x04000000))[-0x1000000] = 1;",
                           "(&__extension__ (0, *(volatile u16 *)0x04000000))[-0x1000000] = 1;",
                           "lo = (&__extension__ *(volatile u8 *)0x04000000)[data + 2 - (const u8 *)0x04000000];"):
            with self.subTest(expression=expression):
                self.assertEqual(rules(COMMENT + expression + "\n"), ["volatile"])
        self.assertEqual(rules(COMMENT + "x = __extension__ *(volatile u16 *)0x04000000;\n"), [])

    def test_a_compound_literal_does_not_end_the_walk(self):
        # review-357 delta C3': the literal's braces are an operand, not a statement boundary
        for expression in ("(&((u32){0}, *(volatile u16 *)0x04000000))[-0x1000000] = 1;",
                           "lo = (&((const u8 *){0}, *(volatile u8 *)0x04000000))[data - (const u8 *)0x04000000];"):
            with self.subTest(expression=expression):
                self.assertEqual(rules(COMMENT + expression + "\n"), ["volatile"])
        # an access inside a literal or an initializer is a value
        self.assertEqual(rules(COMMENT + "f((u32[]){ *(volatile u16 *)0x04000000, 1 });\n"), [])

    def test_digraphs_are_read_as_their_brackets(self):
        # agbcc reads `<%` `%>` `<:` `:>` as braces and brackets, mixed freely with the real ones
        self.assertEqual(rules(COMMENT + "(&((u32){0%>, *(volatile u16 *)0x04000000))<:-0x1000000:> = 1;\n"),
                         ["volatile"])
        self.assertEqual(rules("typedef struct <% unsigned char unknown_00<:0x01000000:>; unsigned short value; %> u16;\n"
                               "u16 g(void)\n{\n" + COMMENT + "    return (*(volatile u16 *)0x04000000).value;\n}\n"),
                         ["volatile"])
        self.assertEqual(rules(COMMENT + "x = a<:1:> & *(volatile u16 *)0x04000000;\n"), [])
        self.assertEqual(plausible.spell_digraphs("a<:1:> <%b%> %:%:%:"), "a[ 1 ] { b } ##  # ")

    def test_the_exemption_reads_digraphs_itself(self):
        # the census hands hardware_volatile_offsets the code as written, digraphs and all
        text = ("typedef struct <% unsigned char unknown_00<:0x01000000:>; unsigned short value; %> u16;\n"
                "u16 g(void)\n{\n" + COMMENT + "    return (*(volatile u16 *)0x04000000).value;\n}\n")
        self.assertEqual(plausible.hardware_volatile_offsets(text, plausible.strip_comments_and_strings(text), {}),
                         set())

    def test_an_unknown_context_is_refused(self):
        # the walk is a whitelist: what it does not model is refused
        for expression in ("x = sizeof &*(volatile u16 *)0x04000000;",
                           "x = sizeof *(volatile u16 *)0x04000000;",
                           "__typeof__(*(volatile u16 *)0x04000000) copy = 0;",
                           "typeof(&*(volatile u16 *)0x04000000) p;",
                           "x = __builtin_expect(*(volatile u16 *)0x04000000, 0);",
                           "return ADDRESS_OF *(volatile u16 *)0x04000000;",
                           "x = a .*(volatile u16 *)0x04000000;",
                           # an operand or a stray `)` before the access is not a context the walk knows
                           "x = (a + b) *(volatile u16 *)0x04000000;",
                           "x = a) *(volatile u16 *)0x04000000;",
                           # in the lint, u8 .. s32 are type names, not operands, so this `&` is unary
                           "x = u16 & *(volatile u16 *)0x04000000;"):
            with self.subTest(expression=expression):
                self.assertEqual(rules(COMMENT + expression + "\n"), ["volatile"])

    def test_statement_bodies_and_casts_are_admitted(self):
        # review-357 delta MINOR 1: a `for` header's semicolons are inside its parentheses
        for expression in ("for (i = 0; i < 4; i++) *(volatile u32 *)0x040000A0 = src[i];",
                           "for (;;) *(volatile u32 *)0x040000A0 = 0;",
                           "while (n--) *(volatile u16 *)0x04000000 = 0;",
                           "if (c) *(volatile u16 *)0x04000000 = 1; else *(volatile u16 *)0x04000000 = 2;",
                           "do *(volatile u16 *)0x04000000 = 1; while (c);",
                           "switch (c) { case 1: *(volatile u16 *)0x04000000 = 1; }",
                           "done: *(volatile u16 *)0x04000000 = 1;",
                           "x = (s16)(u16)*(volatile u16 *)0x04000006;",
                           "return (u16)*(volatile u16 *)0x04000006;",
                           "while (n--) (void)*(volatile u16 *)0x04000006;",
                           "x = (short)(*(volatile u16 *)0x04000006);",
                           "x = a ? b : *(volatile u16 *)0x04000006;"):
            with self.subTest(expression=expression):
                self.assertEqual(rules("void f(void)\n{\n" + COMMENT + expression + "\n}\n"), [])
        # a splice is whitespace, and a directive inside a statement is not part of it
        for statement in ("x = \\\n" + COMMENT + "    *(volatile u16 *)0x04000006;",
                          "x = y,\n#ifdef BUGFIX\n    z = 1,\n#endif\n" + COMMENT + "    *(volatile u16 *)0x04000006 = 1;"):
            with self.subTest(statement=statement):
                self.assertEqual(rules("void f(void)\n{\n" + statement + "\n}\n"), [])

    def test_macro_bodies_are_walked_alone(self):
        self.assertEqual(rules(COMMENT + "#define REG (*(volatile u16 *)0x04000000)\nvoid f(void) { REG = 1; }\n"), [])
        self.assertEqual(rules("#define REG " + COMMENT.strip() + " \\\n    *(volatile u16 *)0x04000000\n"), [])
        self.assertEqual(rules(COMMENT + "#define REG_ADDR (&*(volatile u16 *)0x04000000)\n"), ["volatile"])
        # a directive before a statement is not part of it
        self.assertEqual(rules("void f(void)\n{\n#if 1\n" + COMMENT + "    *(volatile u16 *)0x04000000 = 1;\n"
                               "#endif\n" + COMMENT + "    *(volatile u16 *)0x04000000 = 2;\n}\n"), [])

    def test_a_redeclared_scalar_name_is_refused(self):
        # review-357 C2: a typedef can make u8 .. s32 an array or a struct
        for definition, access in (
                ("typedef struct { u8 unknown_00[0x01000000]; unsigned short value; } u16;",
                 "x = (*(volatile u16 *)0x04000000).value;"),
                ("typedef unsigned char u8[0x01000001];", "(*(volatile u8 *)0x04000000)[0x01000000] = 1;"),
                ("typedef unsigned char u8[1];", "lo = (*(volatile u8 *)0x04000000)[data + 2 - (const u8 *)0x04000000];"),
                ("typedef unsigned int u16;", "*(volatile u16 *)0x040003FE = 1;"),
                ("typedef struct { int a; } s8, u8;", "*(volatile u8 *)0x04000000 = 1;"),
                # review-357 delta C2': `typedef` may stand anywhere among the specifiers
                ("unsigned char typedef u8[0x01000001];", "(*(volatile u8 *)0x04000000)[0x01000000] = 1;"),
                ("unsigned char typedef u8[1];", "lo = (*(volatile u8 *)0x04000000)[data + 2 - (const u8 *)0x04000000];"),
                ("const typedef unsigned short u16[2];", "x = (*(volatile u16 *)0x04000000)[1];"),
                ("struct Big { u8 unknown_00[0x01000000]; u16 value; } typedef u16;",
                 "x = (*(volatile u16 *)0x04000000).value;"),
                ("typedef __typeof__(unsigned char [0x01000001]) u8;", "(*(volatile u8 *)0x04000000)[0x01000000] = 1;"),
                ("typedef __attribute((aligned(1))) unsigned char u8[0x01000001];",
                 "(*(volatile u8 *)0x04000000)[0x01000000] = 1;"),
                ("typedef unsigned char __attribute__((aligned(sizeof(int)))) u8[0x01000001];",
                 "(*(volatile u8 *)0x04000000)[0x01000000] = 1;"),
                ("typedef unsigned int *__restrict u8;", "*(volatile u8 *)0x040003FF = 0;"),
                # review-357 round 3 (C2''): an attribute between the keyword and the body
                ("struct __attribute__((packed)) { u8 unknown_00[0x01000000]; unsigned short value; } typedef u16;",
                 "x = (*(volatile u16 *)0x04000000).value;"),
                ("union __attribute__((packed)) { unsigned char unknown_00[0x01000001]; } typedef u8;",
                 "x = (*(volatile u8 *)0x04000000).unknown_00[0x01000000];"),
                ("enum __attribute__((packed)) { BIG = 0x01000000 } typedef u16;", "*(volatile u16 *)0x040003FE = 1;"),
                ("struct Tag __attribute__((aligned(sizeof(int)))) { unsigned char b[1]; } typedef u8;",
                 "lo = (*(volatile u8 *)0x04000000).b[data + 2 - (const u8 *)0x04000000];")):
            for scope in ("file", "block"):
                source = (definition + "\nvoid f(void)\n{\n" + COMMENT + access + "\n}\n" if scope == "file" else
                          "void f(void)\n{\n" + definition + "\n" + COMMENT + access + "\n}\n")
                with self.subTest(definition=definition, scope=scope):
                    self.assertEqual(rules(source), ["volatile"])
        # a directive before the declaration is not part of it
        self.assertEqual(rules('#include "ffta.h"\nunsigned char typedef u8[0x01000001];\nvoid f(void)\n{\n' + COMMENT +
                               "(*(volatile u8 *)0x04000000)[0x01000000] = 1;\n}\n"), ["volatile"])
        canonical = ("typedef unsigned char u8;\ntypedef signed short s16;\nvoid f(void)\n{\n" + COMMENT +
                     "*(volatile u8 *)0x04000000 = 1;\n" + COMMENT + "*(volatile s16 *)0x04000002 = 1;\n}\n")
        self.assertEqual(rules(canonical), [])

    def test_an_attributed_scalar_typedef_is_refused(self):
        # review-357 final round (A10): `mode` changes the size, so an attribute is never canonical
        for name, builtin in (("u8", "unsigned char"), ("s8", "signed char"), ("u16", "unsigned short"),
                              ("s16", "signed short"), ("u32", "unsigned int"), ("s32", "signed int")):
            for mode in ("DI", "HI"):
                for definition in (f"typedef {builtin} {name} __attribute__((mode({mode})));",
                                   f"typedef {builtin} __attribute__((mode({mode}))) {name};"):
                    with self.subTest(definition=definition):
                        self.assertEqual(rules(definition + "\nvoid f(void)\n{\n" + COMMENT +
                                               f"    *(volatile {name} *)0x040003FC = 1;\n}}\n"), ["volatile"])
        declarations = dict(plausible.typedef_declarations("typedef unsigned int u32 __attribute__((mode(DI)));\n"))
        self.assertEqual(declarations["u32"].strip(), "typedef unsigned int u32 __attribute__((mode(DI)));")

    def test_typedef_declarations(self):
        code = ("typedef unsigned short u16;\ntypedef struct Tag { u8 a; u32 b; } Name, *NamePtr;\n"
                "typedef struct __attribute__((packed)) { u8 a; } Packed;\ntypedef void (*Handler)(u16 value);\n"
                "typedef u16 Halves[2], Half;\ntypedef const volatile unsigned char *Port;\n"
                "unsigned char typedef Byte;\nstruct Pair { u8 a; } typedef PairName;\n"
                "typedef __typeof__(unsigned char [4]) Word;\nvoid f(void) { short typedef Local; }\n"
                "struct __attribute__((packed)) { u8 a; } typedef S1;\nunion U __attribute__((x)) { u8 a; } typedef S2;\n"
                "enum __attribute__((packed)) { E0 } typedef S3;\n")
        self.assertEqual([name for name, _ in plausible.typedef_declarations(code)],
                         ["u16", "Name", "NamePtr", "Packed", "Handler", "Halves", "Half", "Port", "Byte",
                          "PairName", "Word", "Local", "S1", "S2", "S3"])
        declarations = dict(plausible.typedef_declarations(code))
        self.assertEqual(declarations["Byte"].strip(), "unsigned char typedef Byte;")
        self.assertEqual(declarations["PairName"].strip(), "struct Pair { u8 a; } typedef PairName;")

    def test_an_address_converted_to_a_value_is_admitted(self):
        for expression in ("set((void *)&*(volatile u32 *)0x040000A0);", "set((u32)&*(volatile u32 *)0x040000A0);",
                           "a = (unsigned int)&(*(volatile u16 *)0x04000000);"):
            with self.subTest(expression=expression):
                self.assertEqual(rules(COMMENT + expression + "\n"), [])
        for expression in ("p = (u16 *)&*(volatile u16 *)0x04000000;", "p = (volatile void *)&*(volatile u16 *)0x04000000;",
                           "p = (Address)&*(volatile u16 *)0x04000000;", "p = (const u32)&*(volatile u16 *)0x04000000;"):
            with self.subTest(expression=expression):
                found = plausible.check_text(COMMENT + expression + "\n", data_symbols={}, volatile_allow=[])
                # the access's own qualifier is refused (a second one in the cast is refused anyway)
                self.assertIn((2, "volatile"), [(line, rule) for line, rule, _, _ in found])
        # a cast to a redeclared integer name is not a conversion to a value
        self.assertEqual(rules("typedef unsigned char *u32;\n" + COMMENT +
                               "p = (u32)&*(volatile u16 *)0x04000000;\n"), ["volatile"])

    def test_a_volatile_dereference_of_a_converted_address_is_refused(self):
        # the value is admitted, but a later volatile access through it is a qualifier of its own,
        # outside the exception: it has no literal address
        source = ("void f(void)\n{\n" + COMMENT + "    void *p = (void *)&*(volatile u16 *)0x04000000;\n" + COMMENT +
                  "    *(volatile u16 *)p = 1;\n" + COMMENT + "    a = (u32)&*(volatile u16 *)0x04000000;\n" +
                  COMMENT + "    *(volatile u16 *)(a + 0x1000000) = 1;\n}\n")
        found = [(line, rule) for line, rule, _, _ in plausible.check_text(source, data_symbols={}, volatile_allow=[])]
        self.assertEqual(found, [(6, "volatile"), (10, "volatile")])

    def test_binary_operators_are_not_address_taken(self):
        for expression in ("x = y & *(volatile u16 *)0x04000004;", "x = 3 & *(volatile u16 *)0x04000004;",
                           "x = a[1] & *(volatile u16 *)0x04000004;",
                           "if (a && *(volatile u16 *)0x04000004) x = 1;",
                           "x = (*(volatile u16 *)0x04000004) & 1;",
                           "while (*(volatile u8 *)0x04000006 == 159) ;"):
            with self.subTest(expression=expression):
                self.assertEqual(rules(COMMENT + expression + "\n"), [])


class BoundFormTests(unittest.TestCase):
    MAPPING = {"dma3": "0x040000D4"}

    def bound(self, definition, ctype="DmaRegisters", use="dma->control = 1;"):
        return (definition + f"extern {ctype} dma3;\nvoid f(void)\n{{\n" + COMMENT +
                f"    volatile {ctype} *dma = &dma3;\n    {use}\n}}\n")

    def test_a_struct_of_scalars_and_pointers_is_admitted(self):
        self.assertEqual(rules(self.bound(DMA), self.MAPPING), [])
        tagged = "struct DisplayStatus {\n    u16 status;\n};\n"
        self.assertEqual(rules(self.bound(tagged, "struct DisplayStatus", "x = dma->status;"),
                               self.MAPPING), [])
        self.assertEqual(rules(self.bound("", "u16", "*dma = 1;"), self.MAPPING), [])

    def test_unknown_or_unmeasured_types_are_refused(self):
        for definition, ctype in (
                ("", "DmaRegisters"),                                                   # not defined here
                ("typedef struct { u32 words[3]; } DmaRegisters;\n", "DmaRegisters"),  # array
                ("typedef struct { u32 a : 4; u32 b : 28; } DmaRegisters;\n", "DmaRegisters"),  # bit-field
                ("typedef struct { struct { u32 a; } inner; } DmaRegisters;\n", "DmaRegisters"),  # nested
                ("typedef struct { Word a; } DmaRegisters;\n", "DmaRegisters"),        # unknown typedef
                ("typedef struct { u32 a, b; } DmaRegisters;\n", "DmaRegisters"),      # two declarators
                (DMA + DMA, "DmaRegisters"),                                           # two definitions
                ("typedef u32 Word;\n", "Word")):                                      # typedef of a scalar
            with self.subTest(definition=definition, ctype=ctype):
                self.assertEqual(rules(self.bound(definition, ctype), self.MAPPING), ["volatile"])

    def test_the_whole_object_must_fit_in_the_window(self):
        for address, ok in ((0x040003F4, True), (0x040003F8, False), (0x04000400, False)):
            with self.subTest(address=hex(address)):
                self.assertEqual(rules(self.bound(DMA), {"dma3": hex(address)}), [] if ok else ["volatile"])
        big = ("typedef struct { u32 a; u32 b; u32 c; u32 d; u32 e; u32 f; u32 g; u32 h; u32 i; u32 j; "
               "u32 k; u32 l; u32 m; u32 n; u32 o; u32 p; u32 q; u32 r; u32 s; u32 t; u32 u; u32 v; u32 w; "
               "u32 x; u32 y; u32 z; } DmaRegisters;\n")
        self.assertEqual(plausible.struct_size(big, "DmaRegisters"), 0x68)
        self.assertEqual(rules(self.bound(big), {"dma3": "0x0400039C"}), ["volatile"])
        self.assertEqual(rules(self.bound(big), {"dma3": "0x04000398"}), [])
        self.assertEqual(rules(self.bound("", "u32", "*dma = 1;"), {"dma3": "0x040003FE"}), ["volatile"])

    def test_an_address_taken_use_is_refused(self):
        # review-357 M1
        for use in ("(&(dma->control))[-0x800037] = 1;", "u32 *p = &(dma->control);",
                    "u32 *p = (u32 *)&(u32)dma->control;", "u32 *p = &(0, dma->control);"):
            with self.subTest(use=use):
                self.assertEqual(rules(self.bound(DMA, use=use), self.MAPPING), ["volatile"])
        for use in ("(&(*dma))[-0x1000002] = 1;", "(&(0, *dma))[-0x1000002] = 1;"):
            with self.subTest(use=use):
                self.assertEqual(rules(self.bound("", "u16", use), self.MAPPING), ["volatile"])

    def test_transparent_keywords_do_not_hide_an_ampersand_on_a_use(self):
        # review-357 delta C1' (D4)
        for use in ("(&__extension__ dma->control)[-0x800037] = 1;", "u32 *p = &__real__ dma->control;",
                    "u32 *p = (u32 *)&((u32){0}, dma->control);", "x = sizeof dma->control;"):
            with self.subTest(use=use):
                self.assertEqual(rules(self.bound(DMA, use=use), self.MAPPING), ["volatile"])

    def test_uses_in_statement_bodies_are_admitted(self):
        # review-357 delta MINOR 1 (F7): an unbraced loop body is a statement
        for use in ("for (i = 0; i < 4; i++) *dma = i;", "while (n--) *dma = 0;", "if (c) *dma = 1; else *dma = 2;",
                    "x = (u16)*dma;"):
            with self.subTest(use=use):
                self.assertEqual(rules(self.bound("", "u16", use), self.MAPPING), [])

    def test_an_attributed_member_scalar_name_is_refused(self):
        # review-357 final round (B8): `{ u32 a; u32 b; }` measures 8, but is 16 with u32 in DImode
        source = ("typedef unsigned int u32 __attribute__((mode(DI)));\ntypedef struct { u32 a; u32 b; } Regs;\n"
                  "extern Regs data_040003B0;\nvoid f(void)\n{\n" + COMMENT +
                  "    volatile Regs *dma = &data_040003B0;\n    dma->b = 1;\n    dma->b = 2;\n}\n")
        mapping = {"data_040003B0": "0x040003B0"}
        self.assertEqual(rules(source, mapping), ["volatile"])
        self.assertEqual(rules(source.split("\n", 1)[1], mapping), [])

    def test_a_redeclared_member_scalar_name_is_refused(self):
        # review-357 delta M1': the measured struct's members are sized by name too
        regs = "typedef struct { u16 control; } Regs;\n"
        source = self.bound(regs, "Regs", "dma->control[0x800000] = 1;")
        self.assertEqual(rules(source.replace("void f(void)\n{\n", "void f(void)\n{\n"
                                              "    typedef unsigned short u16[0x800001];\n"), self.MAPPING),
                         ["volatile"])
        self.assertEqual(rules("unsigned short typedef u16[0x800001];\n" + source, self.MAPPING), ["volatile"])
        self.assertEqual(rules(self.bound(regs, "Regs"), self.MAPPING), [])
        self.assertIsNone(plausible.struct_size("typedef char u16[9];\n" + regs, "Regs"))

    def test_a_redeclared_type_name_is_refused(self):
        # review-357 C2: B4 and B6
        self.assertEqual(rules("void f(void)\n{\n    typedef unsigned short u16[0x800001];\n" +
                               self.bound("", "u16", "(*dma)[0x800000] = 1;").split("void f(void)\n{\n", 1)[1],
                               self.MAPPING), ["volatile"])
        big = "typedef struct { u32 words[0x400000]; u16 control; } Big;\n"
        source = self.bound(DMA + big, use="dma->control = 1;").replace(
            "void f(void)\n{\n", "void f(void)\n{\n    typedef Big DmaRegisters;\n")
        self.assertEqual(rules(source, self.MAPPING), ["volatile"])
        # review-357 delta C2' (B6b): the same with `typedef` after its specifier
        self.assertEqual(rules(source.replace("typedef Big DmaRegisters;", "Big typedef DmaRegisters;"),
                               self.MAPPING), ["volatile"])
        # review-357 round 3 (B6c): and after an attributed struct's body
        self.assertEqual(rules(source.replace("typedef Big DmaRegisters;",
                                              "struct __attribute__((packed)) { u8 unknown_00[0x01000000]; "
                                              "u16 control; } typedef DmaRegisters;"), self.MAPPING), ["volatile"])

    def test_a_struct_tag_defined_twice_is_refused(self):
        tagged = "struct Regs {\n    u16 status;\n};\n"
        self.assertEqual(rules(self.bound(tagged, "struct Regs", "x = dma->status;"), self.MAPPING), [])
        big = "struct Regs { u32 a; u32 b; u32 c; u32 d; u32 e; u32 f; u32 g; u32 h; u32 i; u32 j; u32 status; };\n"
        source = self.bound(tagged, "struct Regs", "x = dma->status;").replace(
            "void f(void)\n{\n", "void f(void)\n{\n    " + big)
        self.assertEqual(rules(source, {"dma3": "0x040003F8"}), ["volatile"])

    def test_a_definition_split_by_a_splice_is_still_measured(self):
        # review-357 MINOR 3: the size is read with the splices deleted, as cpp reads them
        for definition in ("typedef struct \\\n{ const void *source; void *destination; u32 control; } DmaRegisters;\n",
                           "typedef struct { const \\\nvoid *source; void *destination; u32 control; } DmaRegisters;\n"):
            with self.subTest(definition=definition):
                self.assertEqual(rules(self.bound(definition), self.MAPPING), [])

    def test_the_struct_is_rounded_to_four_bytes(self):
        # review-357 MINOR 1: agbcc reads a {u8; u8} struct with one 4-byte `ldr`
        pair = "typedef struct { u8 a; u8 b; } DmaRegisters;\n"
        self.assertEqual(rules(self.bound(pair, use="x = dma->a;"), {"dma3": "0x040003FE"}), ["volatile"])
        self.assertEqual(rules(self.bound(pair, use="x = dma->a;"), {"dma3": "0x040003FC"}), [])

    def test_struct_layout(self):
        # members align to their size, and agbcc rounds every struct up to 4 bytes (review-357)
        for body, size in (("u8 a; u32 b;", 8), ("u16 a; u8 b;", 4), ("u8 a; u8 b;", 4), ("u32 *p;", 4),
                           ("const void *p; u16 h;", 8), ("u8 * const p; u8 b;", 8), ("unsigned short a;", 4),
                           ("u8 a; u16 b; u8 c;", 8), ("u8 a;", 4), ("u8 a; u8 b; u8 c; u8 d; u8 e;", 8)):
            with self.subTest(body=body):
                self.assertEqual(plausible.struct_size("typedef struct { " + body + " } T;", "T"), size)
                self.assertEqual(plausible.struct_size("struct T { " + body + " };", "struct T"), size)
        self.assertIsNone(plausible.struct_size("typedef struct { } T;", "T"))


@unittest.skipUnless(HAVE_CPP, "the census runs cpp")
class PlacementTests(CensusTree, unittest.TestCase):
    """#357's comment: a macro can carry a justified hardware qualifier onto other memory."""

    def setUp(self):
        super().setUp()
        (self.tree / "include" / "ffta.h").write_text(
            "typedef unsigned char u8;\ntypedef signed char s8;\ntypedef unsigned short u16;\n"
            "typedef unsigned int u32;\n")
        (self.tree / "config" / "data_symbols.json").write_text(json.dumps({"dma3": "0x040000D4"}))

    def moved(self, source):
        self.write(source)
        found = self.census()
        self.assertTrue(any("not in an access the hardware exception admits" in message or
                            "address is taken" in message for message in found), found)
        result, document = self.run_checker()
        self.assertEqual(result.returncode, 1)
        self.assertIn("volatile-census", [f["rule"] for f in document["findings"]])

    def test_a_macro_type_name_is_refused(self):
        # a type name that is not a scalar is refused by the rule itself
        source = ('#include "ffta.h"\n#define REG s8 *)&data_x = 1, *(s8\nextern s8 data_x;\n'
                  "void func_08000000(void)\n{\n" + COMMENT + "    *(volatile REG *)0x04000000 = 1;\n}\n")
        self.assertEqual(rules(source), ["volatile"])
        # a scalar's name redefined passes the rule, and the census sees where cpp puts the qualifier
        source = source.replace("#define REG", "#define u8").replace("volatile REG", "volatile u8")
        self.assertEqual(rules(source), [])
        self.moved(source)

    def test_a_qualifier_split_out_of_a_binding_is_refused(self):
        source = ('#include "ffta.h"\n' + DMA + "extern DmaRegisters dma3;\n#define FIRST(q, ...) q\n"
                  "#define SPLIT(x) FIRST(x, )\n" + COMMENT +
                  "#define QUAL SPLIT(volatile DmaRegisters *dma = &dma3;)\n#define DmaRegisters ,\n"
                  "extern QUAL u8 gFlag;\nvoid f(void) { gFlag = 1; gFlag = 2; }\n")
        self.moved(source)

    def test_an_address_taken_through_a_macro_is_refused(self):
        # an object-like macro before the access is a context the walk does not know
        self.assertEqual(rules('#include "ffta.h"\n#define ADDRESS_OF &\nu16 *f(void)\n{\n' + COMMENT +
                               "    return ADDRESS_OF *(volatile u16 *)0x04000000;\n}\n"), ["volatile"])
        # a function-like one reads as a call, so the census sees what cpp makes of it
        for source in ('#include "ffta.h"\n#define ADDRESS_OF(x) &x\nu16 *f(void)\n{\n' + COMMENT +
                       "    return ADDRESS_OF(*(volatile u16 *)0x04000000);\n}\n",
                       '#include "ffta.h"\n' + COMMENT + "#define REG (*(volatile u16 *)0x04000000)\n"
                       "void f(void) { u16 *p = (u16 *)&REG; p[0x800000] = 1; }\n"):
            with self.subTest(source=source):
                self.moved(source)

    def test_a_renamed_symbol_is_refused_by_the_rule(self):
        source = ('#include "ffta.h"\n' + DMA + "extern DmaRegisters dma3;\nextern DmaRegisters ram_obj;\n"
                  "#define dma3 ram_obj\nvoid f(void)\n{\n" + COMMENT +
                  "    volatile DmaRegisters *dma = &dma3;\n    dma->control = 1;\n    dma->control = 2;\n}\n")
        self.assertEqual(rules(source, {"dma3": "0x040000D4"}), ["volatile"])

    def test_a_use_changed_by_a_macro_is_refused(self):
        source = ('#include "ffta.h"\n' + DMA + "extern DmaRegisters dma3;\n#define ADDRESS_OF &\n"
                  "void f(void)\n{\n" + COMMENT + "    volatile DmaRegisters *dma = &dma3;\n"
                  "    u32 *p = (u32 *)ADDRESS_OF dma->control;\n    p[0x100000] = 1;\n}\n")
        self.assertEqual(rules(source, {"dma3": "0x040000D4"}), ["volatile"])
        source = source.replace("#define ADDRESS_OF &", "#define ADDRESS_OF(x) &x").replace(
            "ADDRESS_OF dma->control", "ADDRESS_OF(dma->control)")
        self.assertEqual(rules(source, {"dma3": "0x040000D4"}), [])
        self.moved(source)

    def test_a_retyped_binding_is_refused(self):
        source = ('#include "ffta.h"\n' + DMA + "typedef struct { u32 words[0x100000]; } Big;\n"
                  "#define DmaRegisters Big\nextern DmaRegisters dma3;\nvoid f(void)\n{\n" + COMMENT +
                  "    volatile DmaRegisters *dma = &dma3;\n    dma->words[0] = 1;\n}\n")
        self.moved(source)

    def test_every_hardware_qualifier_is_checked(self):
        # the first access keeps its shape; only the second is moved
        source = ('#include "ffta.h"\nextern s8 data_x;\nvoid f(u16 v)\n{\n' + COMMENT +
                  "    *(volatile u16 *)0x04000000 = v;\n#define u16 s8 *)&data_x = 1, *(s8\n" + COMMENT +
                  "    *(volatile u16 *)0x04000002 = 1;\n}\n")
        self.assertEqual(rules(source), [])
        self.moved(source)

    def test_a_symbol_shadowed_from_a_header_is_refused(self):
        # review-357 M2: a macro in another linted file renames a local to the bound symbol
        (self.tree / "config" / "data_symbols.json").write_text(json.dumps({"data_04000004": "0x04000004"}))
        self.write('#include "ffta.h"\n#include "shadow.h"\nextern u16 data_04000004;\nvoid f(void)\n{\n'
                   "    u16 SCRATCH;\n" + COMMENT + "    volatile u16 *reg = &data_04000004;\n"
                   "    *reg = 1;\n    *reg = 2;\n}\n", headers={"shadow.h": "#define SCRATCH data_04000004\n"})
        self.assertEqual(plausible.check_file(self.tree / "src" / "08000000.c"), [])
        self.moved(self.tree.joinpath("src", "08000000.c").read_text())

    def test_a_scalar_name_is_declared_exactly_once_in_the_unit(self):
        # the lead's rule for review-357 C2: in the unit, ffta.h's typedef is the only declaration
        source = ('#include "ffta.h"\nvoid f(void)\n{\n    typedef unsigned short u16;\n' + COMMENT +
                  "    *(volatile u16 *)0x04000000 = 1;\n}\n")
        self.assertEqual(rules(source), [])
        self.moved(source)
        # the bound form's scalar, and the scalar names of its struct's members, too
        for definition, ctype, use in (("", "u16", "*dma = 1;"),
                                       ("typedef struct { u16 control; } Regs;\n", "Regs", "dma->control = 1;")):
            with self.subTest(ctype=ctype):
                source = ('#include "ffta.h"\n' + definition + f"extern {ctype} dma3;\nvoid f(void)\n{{\n"
                          "    typedef unsigned short u16;\n" + COMMENT + f"    volatile {ctype} *dma = &dma3;\n"
                          f"    {use}\n}}\n")
                self.assertEqual(rules(source, {"dma3": "0x040000D4"}), [])
                self.moved(source)
        unit = "typedef unsigned short u16;\n"
        self.assertTrue(plausible.names_hold(unit, "u16", unit=True))
        self.assertFalse(plausible.names_hold(unit + unit, "u16", unit=True))
        self.assertFalse(plausible.names_hold("", "u16", unit=True))
        self.assertTrue(plausible.names_hold("", "u16"))

    def test_a_digraph_typedef_from_a_macro_is_read_in_the_unit(self):
        # cpp keeps a digraph's spelling, so the census reads `<%` as a brace itself
        source = ('#include "ffta.h"\n#define SHADOW typedef struct <% unsigned char unknown_00<:0x01000000:>; '
                  "unsigned short value; %> u16;\nunsigned short f(void)\n{\n    SHADOW\n" + COMMENT +
                  "    return (*(volatile u16 *)0x04000000).value;\n}\n")
        self.assertEqual(rules(source), [])
        self.moved(source)

    def test_the_attributed_typedef_shape_is_refused_through_the_checker(self):
        # review-357 round 3 (E6): 0800E110's indexed read with `u8` retyped after an attributed body,
        # through the command match.py runs; the same without the attribute (E6n) is refused too
        for attribute in ("__attribute__((packed)) ", ""):
            with self.subTest(attribute=attribute):
                self.write('#include "ffta.h"\nu8 f(const u8 *data)\n{\n    struct ' + attribute +
                           "{ unsigned char b[1]; } typedef u8;\n" + COMMENT +
                           "    return (*(volatile u8 *)0x04000000).b[data + 2 - (const u8 *)0x04000000];\n}\n")
                result, document = self.run_checker()
                self.assertEqual(result.returncode, 1)
                self.assertEqual([(f["line"], f["rule"]) for f in document["findings"]], [(6, "volatile")])

    def test_two_bindings_of_one_name_in_sequence_are_admitted(self):
        # review-357 MINOR 4: each binding's uses end with its block
        block = ("    {\n" + COMMENT + "        volatile DmaRegisters *dma = &dma3;\n"
                 "        dma->control = 1;\n    }\n")
        self.write('#include "ffta.h"\n' + DMA + "extern DmaRegisters dma3;\nvoid f(void)\n{\n" + block + block + "}\n")
        self.assertEqual(self.census(), [])

    def test_a_parenthesised_operand_before_a_register_macro_is_admitted(self):
        # review-357 MINOR 2 (F1): in the unit, `(a | b)` is an expression, not a cast
        self.write('#include "ffta.h"\n' + COMMENT + "#define REG_KEYINPUT (*(volatile u16 *)0x04000130)\n"
                   "u16 f(u16 a, u16 b) { return (a | b) & REG_KEYINPUT; }\n"
                   "typedef u16 Mask;\nu16 g(u16 a) { return (Mask)(a) & REG_KEYINPUT; }\n")
        self.assertEqual(self.census(), [])

    def test_a_register_address_converted_to_a_value_is_admitted(self):
        # review-357 MINOR 2 (F3): a DMA destination is an address value, not an access
        for use in ("set_destination((void *)&REG_FIFO_A);", "set_destination((const void *)&REG_FIFO_A);",
                    "set_address((u32)&REG_FIFO_A);", "set_address((unsigned int) & REG_FIFO_A);"):
            with self.subTest(use=use):
                self.write('#include "ffta.h"\n' + COMMENT + "#define REG_FIFO_A (*(volatile u32 *)0x040000A0)\n"
                           "extern void set_destination(const void *p);\nextern void set_address(u32 a);\n"
                           "void f(void) { " + use + " }\n")
                self.assertEqual(self.census(), [])

    def test_a_volatile_dereference_of_a_register_address_value_is_refused(self):
        self.write('#include "ffta.h"\n' + COMMENT + "#define REG_FIFO_A (*(volatile u32 *)0x040000A0)\n"
                   "void f(void)\n{\n    void *p = (void *)&REG_FIFO_A;\n" + COMMENT +
                   "    ((volatile u32 *)p)[0x100000] = 1;\n}\n")
        result, document = self.run_checker()
        self.assertEqual(result.returncode, 1)
        self.assertEqual([(f["line"], f["rule"]) for f in document["findings"]], [(8, "volatile")])

    def test_a_register_address_kept_as_a_pointer_is_refused(self):
        for use in ("u32 *p = (u32 *)&REG_FIFO_A; p[0x100000] = 1;", "volatile u32 *p = &REG_FIFO_A;",
                    "set_destination((volatile void *)&REG_FIFO_A);", "set_destination(&REG_FIFO_A);"):
            with self.subTest(use=use):
                self.write('#include "ffta.h"\n' + COMMENT + "#define REG_FIFO_A (*(volatile u32 *)0x040000A0)\n"
                           "extern void set_destination(volatile void *p);\nvoid f(void) { " + use + " }\n")
                found = self.census()
                self.assertTrue(any("address is taken" in message and "conservative" in message
                                    for message in found), found)

    def test_admitted_shapes_stay_admitted(self):
        for source in (
                '#include "ffta.h"\n' + COMMENT + "#define REG_IE (*(volatile u16 *)0x04000200)\n"
                "void f(u16 v) { REG_IE = v; REG_IE |= 1; while (REG_IE & 2) ; }\n",
                '#include "ffta.h"\nvoid f(u16 v)\n{\n' + COMMENT + "    *(volatile u16 *)0x04000000 = v;\n}\n",
                '#include "ffta.h"\n' + DMA + "extern DmaRegisters dma3;\nvoid f(void)\n{\n" + COMMENT +
                "    volatile DmaRegisters *dma = &dma3;\n    dma->control = 1;\n"
                "    while (dma->control & 0x80000000) ;\n}\n"):
            with self.subTest(source=source):
                self.write(source)
                self.assertEqual(self.census(), [])
                result, document = self.run_checker()
                self.assertEqual((result.returncode, document["findings"]), (0, []))

    def test_the_census_marks_only_admitted_qualifiers_as_hardware(self):
        markers = {"volatile": "__mkaaaa", "__volatile__": "__mkbbbbbbbb", "__volatile": "__mkcccccc",
                   plausible.HARDWARE: "__mkhhhh"}
        text = COMMENT + "*(volatile u16 *)0x04000000 = v;\nvolatile u8 local;\n"
        code = plausible.strip_comments_and_strings(text)
        exempt = plausible.hardware_volatile_offsets(text, code, {})
        marked = plausible.census_marked(text, markers, exempt)
        self.assertIn("*(__mkhhhh u16 *)", marked)
        self.assertIn("__mkaaaa u8 local", marked)
        self.assertEqual(plausible.census_placement("int x;\n", markers, {}), [])
        self.assertTrue(plausible.census_placement("__mkhhhh u8 gFlag;\n", markers, {}))


class CommaWalkTests(unittest.TestCase):
    """At a comma, `?` or `:` the walk steps outward only through a parenthesis.

    Inside braces or a subscript the access is a value, whatever stands before
    them: `&` in front of a compound literal takes the address of the literal,
    a copy, not of the register one of its initializers reads.  A parenthesis
    the walk leaves this way is a group, so a call's name or a control header
    before it ends the walk, as it does for a parenthesis around the access.
    """

    def test_an_initializer_of_an_address_taken_literal_is_a_value(self):
        for expression in ("p = &(Pair){ 1, *(volatile u16 *)0x04000000, 2 };",
                           "p = &(struct Pair){ 1, *(volatile u16 *)0x04000000, 2 };",
                           "p = &(Pair){ c ? 1 : *(volatile u16 *)0x04000000, 2 };",
                           "g(&(Pair){ 1, *(volatile u16 *)0x04000000, 2 });",
                           "(&(Pair){ 1, *(volatile u16 *)0x04000000, 2 })->a = 3;",
                           "return &(Pair){ 1, *(volatile u16 *)0x04000000, 2 };"):
            with self.subTest(expression=expression):
                self.assertEqual(rules(COMMENT + expression + "\n"), [])

    def test_a_comma_inside_a_subscript_is_a_value(self):
        for expression in ("x = table[i, *(volatile u16 *)0x04000000, 0];",
                           "p = &table[i, *(volatile u16 *)0x04000000, 0];",
                           "x = 1[p, *(volatile u16 *)0x04000000, 0];",
                           "x = \"s\"[0, *(volatile u16 *)0x04000000, 0];"):
            with self.subTest(expression=expression):
                self.assertEqual(rules(COMMENT + expression + "\n"), [])

    def test_a_comma_inside_a_call_or_a_control_header_is_a_value(self):
        for expression in ("x = f(a, *(volatile u16 *)0x04000000);", "f(a, *(volatile u16 *)0x04000000, b);",
                           "x = f(c ? 1 : *(volatile u16 *)0x04000000);",
                           "if (a, *(volatile u16 *)0x04000000) x = 1;",
                           "while (n--, *(volatile u16 *)0x04000000) ;"):
            with self.subTest(expression=expression):
                self.assertEqual(rules(COMMENT + expression + "\n"), [])

    def test_a_comma_group_is_still_walked_outward(self):
        # through a parenthesis the walk goes on, and `&` before the group reaches the register
        for expression in ("(&((Pair){ 1, 2 }, *(volatile u16 *)0x04000000))[-0x1000000] = 1;",
                           "(&(f(a, b), *(volatile u16 *)0x04000000))[-0x1000000] = 1;",
                           "(&(a ? b : 0, *(volatile u16 *)0x04000000))[-0x1000000] = 1;"):
            with self.subTest(expression=expression):
                self.assertEqual(rules(COMMENT + expression + "\n"), ["volatile"])


if __name__ == "__main__":
    unittest.main()
