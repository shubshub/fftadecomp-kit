"""ROM wait-state mirror words name ROM (#377); synthetic, no compiler.

0x0A000000-0x0BFFFFFF and 0x0C000000-0x0DFFFFFF map the same Game Pak ROM as
0x08000000-0x09FFFFFF. Every rule that classes a word as ROM, as code or as an
address needing typed provenance folds a mirror word first, and so refuses it
where it refuses the wait-state-0 word. 0x0E000000-0x0FFFFFFF (SRAM/flash) is
not folded: such words stay numbers.
"""
from contextlib import contextmanager
import json
from pathlib import Path
import struct
import sys
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import addressed_signed_runtime_profile as addressed
import ashldi3_profile
import divsi3_profile
import function_thunk_profile as thunk
import inert_spin_profile as inert_spin
import lshrdi3_profile
import match
import modsi3_profile
import rom_mirror
import software_double_profile
import software_float_profile
import umodsi3_profile

WS1, WS2, SRAM = 0x02000000, 0x04000000, 0x06000000  # offsets of 0x0A, 0x0C and 0x0E from 0x08
A = 0x08010000
CALLEE = 0x08020000
THUNK = thunk.ALIASES["_call_via_r3"]


def bl(site, target):
    offset = target - site - 4
    return struct.pack("<HH", 0xF000 | ((offset >> 12) & 0x7FF), 0xF800 | ((offset >> 1) & 0x7FF))


def caller(value):
    """push {lr}; ldr r3,=value; bl _call_via_r3; pop {r0}; bx r0; .word value"""
    return struct.pack("<HH", 0xB500, 0x4B02) + bl(A + 4, THUNK) + struct.pack("<HHI", 0xBC01, 0x4700, value)


def decoded(data):
    decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
    decoder.detail = True
    return list(decoder.disasm(data[:12], A))


@contextmanager
def extra_reached_word(value):
    """owner_graph_profile.partition, plus one reached non-switch pool word holding value.

    Lets an inventory's word-classification loop see a word its compiled fixture
    cannot hold; every other partition fact is unchanged.
    """
    import owner_graph_profile as graph
    original = graph.partition

    def partition(data, address, *args, **kwargs):
        result = original(data, address, *args, **kwargs)
        extra = {'address': address + len(data), 'value': value, 'load_sites': [address], 'switch_word': False}
        return dict(result, words=[*result['words'], extra])
    with patch.object(graph, 'partition', partition):
        yield


MAPPING = json.dumps([{"rom": f"0x{A:08X}", "end": f"0x{A + 16:08X}", "mode": "thumb"},
                      {"rom": f"0x{CALLEE:08X}", "end": f"0x{CALLEE + 2:08X}", "mode": "thumb"}]).encode()


class FoldTests(unittest.TestCase):
    def test_the_two_mirrors_fold_onto_wait_state_zero(self):
        for value, expected in ((0x0A000000, 0x08000000), (0x0BFFFFFF, 0x09FFFFFF), (0x0C000000, 0x08000000),
                                (0x0DFFFFFF, 0x09FFFFFF), (0x0A000501, 0x08000501), (0x0D142245, 0x09142245)):
            with self.subTest(value=hex(value)):
                self.assertTrue(rom_mirror.mirror(value))
                self.assertEqual(rom_mirror.canonical(value), expected)

    def test_other_values_are_unchanged(self):
        for value in (0, 0x02000000, 0x03007F00, 0x04000000, 0x07FFFFFF, 0x08000000, 0x09FFFFFF,
                      0x0E000000, 0x0E000010, 0x0FFFFFFF, 0x10000000, 0xFFFFFFFF):
            with self.subTest(value=hex(value)):
                self.assertFalse(rom_mirror.mirror(value))
                self.assertEqual(rom_mirror.canonical(value), value)

    def test_typed_domain_is_the_owner_domain_with_mirrors_folded(self):
        for value in (0x02000000, 0x04000000, 0x08000000, 0x08FFFFFF, 0x0A000000, 0x0AFFFFFC, 0x0C000300,
                      0x0CFFFFFF):
            with self.subTest(value=hex(value)):
                self.assertTrue(rom_mirror.typed_domain(value))
        for value in (0x01FFFFFF, 0x09000000, 0x09FFFFFF, 0x0B000000, 0x0BFFFFFC, 0x0D000000, 0x0DFFFFFF,
                      0x0E000000, 0x0E000010, 0x0FFFFFFF, 0x10000000):
            with self.subTest(value=hex(value)):
                self.assertFalse(rom_mirror.typed_domain(value))


class ReservedRuntimeTests(unittest.TestCase):
    def test_a_mirror_of_a_pinned_runtime_is_that_runtime(self):
        starts = [(thunk.reserved, thunk.START), (match.is_udivsi3_address, match.UDIVSI3_ADDRESS),
                  (ashldi3_profile.reserved, ashldi3_profile.ADDRESS),
                  (lshrdi3_profile.reserved, lshrdi3_profile.ADDRESS)]
        starts += [(module.reserved, module.IDENTITIES[0][0]) for module in (
            modsi3_profile, divsi3_profile, umodsi3_profile, software_float_profile, software_double_profile)]
        for predicate, start in starts:
            for value in (start, start | 1):
                with self.subTest(predicate=predicate.__module__, value=hex(value)):
                    self.assertTrue(predicate(value))
                    self.assertTrue(predicate(value + WS1))
                    self.assertTrue(predicate(value + WS2))
                    self.assertFalse(predicate(value + SRAM))


class ThunkLiteralTests(unittest.TestCase):
    def bind(self, value, functions=None):
        data = caller(value)
        thunk.verify_literal_bindings(data, A, decoded(data), {A + 4: THUNK}, MAPPING, functions or {})

    def own(self, value):
        data = caller(value)
        thunk.verify_own_span_literals(data, A, decoded(data))

    def test_a_mirror_of_a_code_entry_or_thunk_needs_function_provenance(self):
        for value in (CALLEE | 1, CALLEE, THUNK, THUNK | 1):
            for mirror in (0, WS1, WS2):
                with self.subTest(value=hex(value + mirror)), \
                        self.assertRaisesRegex(ValueError, "code-entry thunk literals require canonical function"):
                    self.bind(value + mirror)
        # Canonical provenance is the exact Thumb entry, never a mirror spelling.
        self.bind(CALLEE | 1, {12: (f"func_{CALLEE:08X}", CALLEE | 1)})
        with self.assertRaisesRegex(ValueError, "canonical function provenance"):
            self.bind((CALLEE | 1) + WS1, {12: (f"func_{CALLEE:08X}", CALLEE | 1)})

    def test_sram_and_plain_numbers_are_not_code(self):
        for value in ((CALLEE | 1) + SRAM, THUNK + SRAM, 0x0FFFFFFF, 0x02001000, (CALLEE | 1) + 0x08000000):
            with self.subTest(value=hex(value)):
                self.bind(value)
                self.own(value)

    def test_a_mirror_of_the_callers_own_bytes_is_its_own_bytes(self):
        for value in (A + 8, A + 9, A | 1):
            for mirror in (0, WS1, WS2):
                with self.subTest(value=hex(value + mirror)), \
                        self.assertRaisesRegex(ValueError, "caller's own bytes"):
                    self.own(value + mirror)
        self.own(A + 16 + WS1)

    def test_objects_cannot_name_a_mirror_of_a_code_entry_or_thunk(self):
        entries = json.loads(MAPPING)
        calls = {A + 4: THUNK}
        for name, base, value in (("g_code", 0x02000000, CALLEE + WS1), ("g_code", 0x02000000, (CALLEE | 1) + WS2),
                                  ("g_thunk", 0x02000000, THUNK + WS1), ("g_base", CALLEE + WS1, 0x02000000)):
            with self.subTest(name=name, base=hex(base), value=hex(value)), \
                    self.assertRaisesRegex(ValueError, "cannot bind indexed function entries as data"):
                thunk.verify_data_bindings(calls, {12: (name, value)}, {name: base}, entries)
        thunk.verify_data_bindings(calls, {12: ("g_sram", CALLEE + SRAM)}, {"g_sram": 0x02000000}, entries)


class DataSymbolTests(unittest.TestCase):
    def test_a_data_symbol_names_the_canonical_address(self):
        for value in ("0x0A000300", "0x0BFFFFFC", "0x0C000000", "0x0DFFFFFF"):
            with self.subTest(value=value), self.assertRaisesRegex(ValueError, "ROM wait-state mirror"):
                match.parse_data_symbols(json.dumps({"data_x": value}).encode())
        for value in ("0x08000300", "0x09FFFFFC", "0x0E000010", "0x0FFFFFFF", "0x02000000"):
            with self.subTest(value=value):
                self.assertEqual(match.parse_data_symbols(json.dumps({"data_x": value}).encode()),
                                 {"data_x": int(value, 16)})


class OwnSpanBindingTests(unittest.TestCase):
    """Typed object values that are a mirror of the caller's own bytes."""

    def function_bindings(self, value, base=0x06000000):
        data = struct.pack("<HHI", 0x4770, 0x46C0, value)
        rom = bytearray(0x20000)
        rom[A - match.ROM_BASE:A - match.ROM_BASE + len(data)] = data
        mapping = json.dumps([{"rom": f"0x{A:08X}", "end": f"0x{A + len(data):08X}", "mode": "thumb"}]).encode()
        manifest = {"calls": [], "data": [[4, "g_object", value - base]], "functions": []}
        return match.function_address_bindings(data, A, bytes(rom), mapping,
                                               json.dumps({"g_object": f"0x{base:08X}"}).encode(), manifest,
                                               allow_empty_functions=True)

    def test_function_address_object_binding_cannot_name_a_mirror_of_itself(self):
        for value in (A, A + 4, A + 7):
            for mirror in (0, WS1, WS2):
                with self.subTest(value=hex(value + mirror)), self.assertRaisesRegex(ValueError, "references itself"):
                    self.function_bindings(value + mirror)
        for value in (A + 8 + WS1, A + SRAM, 0x08100000 + WS1):
            with self.subTest(value=hex(value)):
                self.assertEqual(self.function_bindings(value)[1], {4: ("g_object", value)})

    def test_addressed_object_value_cannot_alias_a_mirror_of_code(self):
        entries = [{"rom": f"0x{A:08X}", "end": f"0x{A + 8:08X}", "mode": "thumb"},
                   {"rom": f"0x{CALLEE:08X}", "end": f"0x{CALLEE + 0x40:08X}", "mode": "thumb"}]
        objects = {"g_object": 0x02000000}
        for value in (A + 4, CALLEE, CALLEE + 9, THUNK):
            for mirror in (0, WS1, WS2):
                with self.subTest(value=hex(value + mirror)), self.assertRaisesRegex(ValueError, "aliases indexed code"):
                    addressed.object_value("g_object", value + mirror - 0x02000000, objects, entries, A, 8)
        # A code-image alias is the exact entry start; its mirror is not one.
        self.assertEqual(addressed.object_value("g_entry", 0, {"g_entry": CALLEE}, entries, A, 8, image=True),
                         CALLEE)
        for mirror in (WS1, WS2):
            with self.subTest(alias=hex(CALLEE + mirror)), self.assertRaisesRegex(ValueError, "aliases indexed code"):
                addressed.object_value("g_entry", 0, {"g_entry": CALLEE + mirror}, entries, A, 8, image=True)
        for value in (CALLEE + 0x40 + WS1, CALLEE + SRAM, A + 8 + WS2):
            with self.subTest(value=hex(value)):
                self.assertEqual(addressed.object_value("g_object", value - 0x02000000, objects, entries, A, 8),
                                 value)
        # The caller's own span is refused even where the index does not list the caller.
        for value in (A + 4 + WS1, A + WS2):
            with self.subTest(own=hex(value)), self.assertRaisesRegex(ValueError, "aliases indexed code"):
                addressed.object_value("g_object", value - 0x02000000, objects, entries[1:], A, 8)

    def test_inert_spin_data_cannot_name_a_mirror_of_its_own_function(self):
        data = struct.pack("<HH", 0xE7FE, 0x46C0)
        size = 8
        rom = bytearray(0x20000)
        mapping = json.dumps([{"rom": f"0x{A:08X}", "end": f"0x{A + size:08X}", "mode": "thumb"}]).encode()
        index = f"{A:08X} {A + size:08X} {size} 1 spin\n".encode()
        for value in (A + WS1, A + 4 + WS2):
            body = data + struct.pack("<I", value)
            rom[A - match.ROM_BASE:A - match.ROM_BASE + size] = body
            manifest = {"calls": [], "frame": False, "spins": [0], "data": [[4, "g_object", value - 0x06000000]]}
            with self.subTest(value=hex(value)), self.assertRaisesRegex(ValueError, "references its own function"):
                inert_spin.verify(body, A, bytes(rom), mapping, index, manifest,
                                  data_mapping=b'{"g_object":"0x06000000"}')



class OrdinaryCalleeLiteralTests(unittest.TestCase):
    """Callee literal words that must name a mapped object, a mirror word included."""
    T = 0x08010100

    def tree(self, value):
        body = struct.pack("<HHI", 0x4800, 0x4770, value)  # ldr r0,[pc,#0]; bx lr; .word value
        rom = bytearray(0x20000)
        rom[self.T - match.ROM_BASE:self.T - match.ROM_BASE + len(body)] = body
        rows = [{"rom": f"0x{A:08X}", "end": f"0x{A + 4:08X}", "mode": "thumb", "instrs": 2},
                {"rom": f"0x{self.T:08X}", "end": f"0x{self.T + len(body):08X}", "mode": "thumb", "instrs": 2}]
        index = "".join(f"{int(r['rom'], 16):08X} {int(r['end'], 16):08X} "
                        f"{int(r['end'], 16) - int(r['rom'], 16)} 2 return\n" for r in rows)
        return bytes(rom), json.dumps(rows).encode(), index.encode()

    def scratch(self, value, objects=b"{}"):
        import incoming_scratch_overwrite_profile as incoming
        rom, mapping, index = self.tree(value)
        return incoming.authenticate_ordinary(rom, mapping, index, objects, A, 4, self.T)

    def private_frame(self, value, objects=b"{}"):
        import finite_spilled_scalar_loop_profile as loops
        rom, mapping, index = self.tree(value)
        return loops.CallEffects(rom, mapping, index, objects, A, 4, {}).private_frame(self.T)

    def test_mirror_words_need_a_mapped_object_as_rom_words_do(self):
        for check, message in ((self.scratch, "genuine mapped object identity"),
                               (self.private_frame, "lacks canonical data identity")):
            for value in (0x08000300, 0x0A000300, 0x0C000300, 0x0AFFFFFC):
                with self.subTest(check=check.__name__, value=hex(value)), self.assertRaisesRegex(ValueError, message):
                    check(value)
            for value in (0x0E000300, 0x0FFFFFFF, 0x0B000300):
                with self.subTest(check=check.__name__, value=hex(value)):
                    check(value)
            check(0x02001000, b'{"g_object":"0x02001000"}')


class OwnerComparisonOnlyWordTests(unittest.TestCase):
    """The owner rule's two comparison-only exemptions refuse every ROM word.

    The transfer-tree sentinel and the DMA channel threshold are each pinned to one
    value by their own profile, so no owner that profile accepts holds another word
    there. Each profile's proof is replaced here by the facts the owner rule reads
    from it, which shows the owner rule alone with words the profile refuses first.
    """
    WORD = 4
    OTHER = 0x08010000  # a second indexed Thumb function

    def verify(self, module, key, field, address, value):
        import owner_admission_profile as owner
        body = struct.pack("<HHI", 0x4800, 0x4770, value)  # ldr r0,[pc,#0]; bx lr; .word value
        rom = bytearray(0x20000)
        rom[address - match.ROM_BASE:address - match.ROM_BASE + len(body)] = body
        rom[self.OTHER - match.ROM_BASE:self.OTHER - match.ROM_BASE + 2] = struct.pack("<H", 0x4770)  # bx lr
        mapping = json.dumps([{"rom": f"0x{address:08X}", "end": f"0x{address + len(body):08X}",
                               "mode": "thumb", "instrs": 2},
                              {"rom": f"0x{self.OTHER:08X}", "end": f"0x{self.OTHER + 2:08X}",
                               "mode": "thumb", "instrs": 1}]).encode()
        index = (f"{address:08X} {address + len(body):08X} {len(body)} 2 return\n"
                 f"{self.OTHER:08X} {self.OTHER + 2:08X} 2 1 return\n").encode()
        refinement = owner.refine(body, address, mapping)
        ins = owner.graph.graph(body, address, refinement)[0]
        proof = dict(schema=module.SCHEMA, instructions=len(ins), calls=[], runtime_calls=[],
                     partition=owner.graph.partition(body, address, refinement, ins, {}),
                     **{key: {field: self.WORD}})
        with patch.object(module, "prove", lambda *args, **named: proof):
            return owner.verify(body, address, bytes(rom), mapping, index, b"{}", selector=module.SELECTOR,
                                bindings=dict(calls=[], data=[], functions=[], switches=[]))[0]["proof"]

    def check(self, module, key, field, address, canonical, message):
        for value in (0x0A000000, 0x0A02BA50, 0x0C02BA50, 0x0AFFFFFC, 0x0CFFFFFF):
            with self.subTest(address=hex(address), value=hex(value)), self.assertRaisesRegex(ValueError, message):
                self.verify(module, key, field, address, value)
        # Unchanged: the profile's own value is exempt, and a word outside the typed
        # domain (SRAM, a mirror of the space past the image, a number) is not.
        proof = self.verify(module, key, field, address, canonical)
        self.assertEqual((proof[key], [row["value"] for row in proof["partition"]["words"]]),
                         ({field: self.WORD}, [canonical]))
        for value in (0x0E000000, 0x0FFFFFFF, 0x0BFFFFFC, 0x1234):
            with self.subTest(address=hex(address), value=hex(value)), self.assertRaisesRegex(ValueError, message):
                self.verify(module, key, field, address, value)

    def test_a_mirror_word_is_not_the_transfer_tree_sentinel(self):
        import transfer_tree_destruction as tree
        self.check(tree, "transfer_tree", "compared_address_word", tree.OWNER, tree.SENTINEL,
                   "destruction sentinel must be a comparison-only address")

    def test_a_mirror_word_is_not_the_dma_channel_threshold(self):
        import immediate_dma_fill as dma
        for address in sorted(dma.ROOTS):
            self.check(dma, "dma_fill", "address_limit_word", address, 0x07FFFFFF,
                       "DMA channel threshold must be a comparison-only scalar")

    def test_a_rom_word_is_never_comparison_only(self):
        # The owner's own entry and another indexed function's, with and without the
        # Thumb bit, that function's two mirror spellings, and both ends of the
        # wait-state-0 ROM.
        import immediate_dma_fill as dma
        import transfer_tree_destruction as tree
        sites = [(tree, "transfer_tree", "compared_address_word", tree.OWNER,
                  "destruction sentinel must be a comparison-only address")]
        sites += [(dma, "dma_fill", "address_limit_word", address,
                   "DMA channel threshold must be a comparison-only scalar") for address in sorted(dma.ROOTS)]
        for module, key, field, address, message in sites:
            for value in (address, address | 1, self.OTHER, self.OTHER | 1, 0x0A010001, 0x0C010001,
                          match.ROM_BASE, 0x08FFFFFF):
                with self.subTest(address=hex(address), value=hex(value)), self.assertRaisesRegex(ValueError, message):
                    self.verify(module, key, field, address, value)

if __name__ == "__main__":
    unittest.main()
