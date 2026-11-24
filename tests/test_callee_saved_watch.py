"""Callees that read R4-R11 while the caller keeps a stack address there (kit #350)."""
import itertools
import struct
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import callee_saved_watch as watch
import match
import owner_admission_profile as owner
import stack_index_precondition_profile as sip
from test_nested_known_query import assemble
from test_rom_table_copy import fixture, HELPER, OWNER

BASE = match.ROM_BASE
CALLEE, OTHER, THIRD = 0x08014000, 0x08014100, 0x08014200
VIA_R3, VIA_R6 = match.RUNTIME_HELPERS['_call_via_r3'], match.RUNTIME_HELPERS['_call_via_r6']
VIA_R2 = match.RUNTIME_HELPERS['_call_via_r2']
BX_LR = 0x4770
# agbcc's high-register frame: push {r4-r7,lr}; mov r7,sl; mov r6,sb; mov r5,r8; push {r5-r7};
# ... pop {r3,r4,r5}; mov r8,r3; mov sb,r4; mov sl,r5; pop {r4-r7}; pop {r0}; bx r0
HIGH_PROLOGUE = (0xB5F0, 0x4657, 0x464E, 0x4645, 0xB4E0)
HIGH_EPILOGUE = (0xBC38, 0x4698, 0x46A1, 0x46AA, 0xBCF0, 0xBC01, 0x4700)


def rom_with(functions):
    """A ROM image and mapping holding each {address: tokens} function (and the call-via thunks)."""
    rom = bytearray(0x150000)
    entries = []
    for address, tokens in functions.items():
        raw = assemble(address, tokens)
        rom[address - BASE:address - BASE + len(raw)] = raw
        entries.append(dict(rom=f'0x{address:08X}', end=f'0x{address + len(raw):08X}', mode='thumb'))
    for number in range(15):
        thunk = match.RUNTIME_HELPERS[f'_call_via_r{number}']
        rom[thunk - BASE:thunk - BASE + 4] = struct.pack('<2H', 0x4700 | number << 3, 0x46C0)
        entries.append(dict(rom=f'0x{thunk:08X}', end=f'0x{thunk + 2:08X}', mode='thumb'))
    return bytes(rom), entries


def check(functions, watched, target=CALLEE, constants=None):
    rom, entries = rom_with(functions)
    return watch.Checker(rom, entries).call(target, frozenset(watched), constants)


class CheckerTests(unittest.TestCase):
    def test_saving_and_restoring_is_no_use(self):
        # push {r4-r7,lr}; movs r7,#0; pop {r4-r7}; pop {r1}; bx r1
        self.assertEqual(check({CALLEE: (0xB5F0, 0x2700, 0xBCF0, 0xBC02, 0x4708)}, {4, 7}), {})

    def test_every_use_of_a_watched_value_refuses(self):
        reads = {
            'store base': (0x6039, BX_LR),                       # str r1,[r7]
            'load base': (0x6839, BX_LR),                        # ldr r1,[r7]
            'index': (0x59C9, BX_LR),                            # ldr r1,[r1,r7]
            'stored value': (0x600F, BX_LR),                     # str r7,[r1]
            'comparison': (0x2F00, BX_LR),                       # cmp r7,#0
            'derived base': (0x19C9, 0x6008, BX_LR),             # adds r1,r1,r7; str r0,[r1]
            'branch': (0x4738,),                                 # bx r7
            'block store': (0xC080, BX_LR),                      # stmia r0!,{r7}
        }
        for name, body in reads.items():
            with self.subTest(name), self.assertRaisesRegex(watch.WatchRefusal, 'watched callee-saved'):
                check({CALLEE: body}, {7})

    def test_only_the_bits_that_reach_a_use_count(self):
        # agbcc's struct-in-register merge (0x08124ACC): push {r4,r5,lr}; ldr r4,=0xFFFFFF00;
        # ands r5,r4; orrs r5,r0; <two>; strb r0,[r1]; pop {r4,r5}; pop {r0}; bx r0.
        # Bits 8-31 of R5 still hold the caller's address; only bits that reach a use count.
        def body(*two):
            return (0xB530, 0x4C04, 0x4025, 0x4305, *two, 0x7008, 0xBC30, 0xBC01, 0x4700, 0xFF00, 0xFFFF)
        # lsls r0,r5,#24; lsrs r0,r0,#24: the stored byte is the callee's own.
        self.assertEqual(check({CALLEE: body(0x0628, 0x0E00)}, {5}), {})
        # lsrs r0,r5,#8; nop: the stored byte is bits 8-15 of the address.
        with self.assertRaisesRegex(watch.WatchRefusal, 'a store at'):
            check({CALLEE: body(0x0A28, 0x46C0)}, {5})
        # ands r5,r4 sets Z from address bits: beq on it refuses (orrs r5,r0 replaced).
        flags = (0xB530, 0x4C04, 0x4025, 0xD000, 0x0628, 0x0E00, 0x7008, 0xBC30, 0xBC01, 0x4700,
                 0xFF00, 0xFFFF)
        with self.assertRaisesRegex(watch.WatchRefusal, 'conditional branch'):
            check({CALLEE: flags}, {5})
        # lsls r0,r5,#24 leaves bit 8 of the address in C: bcs refuses, beq tests a clean Z.
        with self.assertRaisesRegex(watch.WatchRefusal, 'conditional branch'):
            check({CALLEE: body(0x0628, 0xD200)}, {5})
        self.assertEqual(check({CALLEE: body(0x0628, 0xD000)}, {5}), {})
        # A carry chain from address bits is refused at the adcs.
        with self.assertRaisesRegex(watch.WatchRefusal, 'carry'):
            check({CALLEE: (0x1C29, 0x1949, 0x4140, BX_LR)}, {5})     # adds r1,r5,#0; adds r1,r1,r5; adcs r0,r0
        # A sum carries dependent low bits upwards: the low byte of R5 plus R0, shifted right by
        # 8 and stored as a byte (lsls r1,r5,#24; lsrs r1,r1,#24; adds r1,r1,r0; lsrs r1,r1,#8).
        with self.assertRaisesRegex(watch.WatchRefusal, 'a store at'):
            check({CALLEE: (0x0629, 0x0E09, 0x1809, 0x0A09, 0x7011, BX_LR)}, {5})
        self.assertEqual(check({CALLEE: (0x0629, 0x0E09, 0x0A09, 0x7011, BX_LR)}, {5}), {})
        # Shifted and summed address bits stay dependent: a sum used as a base refuses.
        with self.assertRaisesRegex(watch.WatchRefusal, 'memory access base'):
            check({CALLEE: (0x0069, 0x1C49, 0x6808, BX_LR)}, {5})     # lsls r1,r5,#1; adds r1,#1; ldr r0,[r1]

    @staticmethod
    def merged(*tail, mask=0xFFFFFF00, extra=None):
        """0x08124ACC's merge with ``mask``: push {r4,r5,lr}; ldr r4,=mask; ands r5,r4;
        orrs r5,r0; <tail>; pop {r4,r5}; pop {r0}; bx r0, checked with R5 watched.  R5 keeps
        the address bits ``mask`` selects."""
        code = [0xB530, 0x4C00, 0x4025, 0x4305, *tail, 0xBC30, 0xBC01, 0x4700]
        size = len(assemble(CALLEE, code))
        code[1] |= (size + size % 4 - 4) // 4
        code += [0x46C0] * (size % 4 // 2) + [mask & 0xFFFF, mask >> 16]
        return check({CALLEE: tuple(code), **(extra or {})}, {5})

    def test_the_merged_register_keeps_its_address_bits(self):
        # After ands r5,r4 (0xFFFFFF00) and orrs r5,r0, bits 8-31 of R5 are still the address.
        for name, tail in {'str r5,[r1]': (0x600D,), 'strh r5,[r1]': (0x800D,),
                           'cmp r5,#0': (0x2D00,), 'tst r5,r4': (0x4225,), 'cmn r5,r0': (0x42C5,)}.items():
            with self.subTest(name), self.assertRaisesRegex(watch.WatchRefusal, 'a store at|a comparison at'):
                self.merged(*tail)
        self.assertEqual(self.merged(0x700D), {})                          # strb r5,[r1]: bits 0-7 are R0's
        # As a call argument (adds r0,r5,#0; bl OTHER) the callee is walked with R0 watched.
        with self.assertRaisesRegex(watch.WatchRefusal, f'callee 0x{OTHER:08X}'):
            self.merged(0x1C28, OTHER, extra={OTHER: (0x6801, BX_LR)})     # ldr r1,[r0]
        self.assertEqual(self.merged(0x1C28, OTHER, extra={OTHER: (BX_LR,)}), {})
        # ... and an unresolved callee may not receive it (ldr r3,[r2]; bl _call_via_r3).
        with self.assertRaisesRegex(watch.WatchRefusal, 'receives an owner stack address'):
            self.merged(0x1C28, 0x6813, VIA_R3)

    def test_ops_not_modelled_exactly_stay_conservative(self):
        refused = 'a store at|carry|a comparison at'
        cases = {
            # muls r1,r5 then strb r1,[r2]: a product depends on every bit.
            'mul': ((0x4369, 0x7011), True),
            # adds r1,r5,#0; lsrs r1,r2 with R2 unknown; strb r1,[r2].
            'unknown shift amount': ((0x1C29, 0x40D1, 0x7011), True),
            # movs r2,#24 first: a known amount is exact, so lsls leaves no address bit ...
            'lsls by a known 24': ((0x2218, 0x1C29, 0x4091, 0x7011), False),
            # ... and lsrs moves bits 24-31 into the stored byte.
            'lsrs by a known 24': ((0x2218, 0x1C29, 0x40D1, 0x7011), True),
            # movs r2,#0; rors r1,r2: rotates are not modelled, a full dependence.
            'rotate': ((0x2200, 0x1C29, 0x41D1, 0x7011), True),
            # lsrs r1,r5,#8 leaves bits 0-23; negs carries them through bit 31; lsrs #24; strb.
            'neg': ((0x0A29, 0x4249, 0x0E09, 0x7011), True),
            'no neg': ((0x0A29, 0x0E09, 0x7011), False),
            # mvns r1,r5 keeps the mask: its low byte is R0's, its halfword is not (and R1, still
            # dependent at the return, is handed back).
            'mvn, byte': ((0x43E9, 0x7011), {1: 5}),
            'mvn, halfword': ((0x43E9, 0x8011), True),
            # subs r1,r5,#1 sets C from the address; sbcs r0,r0 uses it.
            'sbc': ((0x1E69, 0x4180), True),
        }
        for name, (tail, outcome) in cases.items():
            with self.subTest(name):
                if outcome is True:
                    with self.assertRaisesRegex(watch.WatchRefusal, refused):
                        self.merged(*tail)
                else:
                    self.assertEqual(self.merged(*tail), outcome or {})
        # Flags flow through a walked callee: dependent flags set before the call (lsls r0,r5,#1: C)
        # reach a bcs after it; clean ones do not, and a compare in between clears them.
        with self.assertRaisesRegex(watch.WatchRefusal, 'conditional branch'):
            check({CALLEE: (0xB500, 0x0068, OTHER, 0xD2FF, 0xBD00), OTHER: (BX_LR,)}, {5})
        self.assertEqual(check({CALLEE: (0xB500, OTHER, 0xD0FF, 0xBD00), OTHER: (BX_LR,)}, {5}), {})
        self.assertEqual(check({CALLEE: (0xB500, 0x0068, OTHER, 0x2900, 0xD0FF, 0xBD00),
                                OTHER: (BX_LR,)}, {5}), {0: 5})          # R0 = R5 << 1, handed back
        # ASR fills with a dependent sign bit (only bit 31 kept): asrs/lsrs r1,r5,#31; lsrs r1,r1,#1; strb.
        with self.assertRaisesRegex(watch.WatchRefusal, refused):
            self.merged(0x17E9, 0x0849, 0x7011, mask=0x80000000)
        self.assertEqual(self.merged(0x0FE9, 0x0849, 0x7011, mask=0x80000000), {})

    def test_a_copy_returned_in_r0_r3_or_r12_is_handed_back(self):
        # adds r0,r7,#0; bx lr: the caller must keep R0 tracked as the R7 address.
        self.assertEqual(check({CALLEE: (0x1C38, BX_LR)}, {7}), {0: 7})
        # mov ip,r8; bx lr
        self.assertEqual(check({CALLEE: (0x46C4, BX_LR)}, {8}), {12: 8})
        # A copy into another callee-saved register at the return is refused.
        with self.assertRaisesRegex(watch.WatchRefusal, 'R6 holds an owner stack address'):
            check({CALLEE: (0x1C3E, BX_LR)}, {7})                # adds r6,r7,#0

    def test_a_compare_of_constants_decides_its_branch(self):
        # push {r5,lr}; movs r2,#N; cmp r2,#15; bls 1f; str r2,[sp,#4] (over the saved LR); 1: pop {r5,pc}.
        # With N = 8 the store is unreachable (a copy helper's size test with a constant size).
        self.assertEqual(check({CALLEE: (0xB520, 0x2208, 0x2A0F, 0xD900, 0x9201, 0xBD20)}, {5}), {})
        with self.assertRaisesRegex(watch.WatchRefusal, 'indirect branch'):
            check({CALLEE: (0xB520, 0x2210, 0x2A0F, 0xD900, 0x9201, 0xBD20)}, {5})
        # An instruction that sets flags in between forgets them (adds r3,r3,#0): both edges.
        with self.assertRaisesRegex(watch.WatchRefusal, 'indirect branch'):
            check({CALLEE: (0xB520, 0x2208, 0x2A0F, 0x1C1B, 0xD900, 0x9201, 0xBD20)}, {5})

    def test_a_base_that_is_one_frame_word_or_a_scalar(self):
        # push {r5,lr}; sub sp,#4; str rX,[sp]; movs r1,#0; cmp r0,#0; beq 1f; mov r1,sp;
        # 1: ldr r2,[r1]; str r3,[r2]; add sp,#4; pop {r5,pc}: R1 is 0 or SP, so the load reads
        # [sp] (or untracked memory), not every frame word.
        def body(spill):
            return (0xB520, 0xB081, 0x2200, spill, 0x2100, 0x2800, 0xD000, 0x4669, 0x680A, 0x6013,
                    0xB001, 0xBD20)
        self.assertEqual(check({CALLEE: body(0x9200)}, {5}), {1: watch.DEAD})   # str r2,[sp]; R1 left
        with self.assertRaisesRegex(watch.WatchRefusal, 'memory access base'):
            check({CALLEE: body(0x9500)}, {5})                             # str r5,[sp]
        # A store of the watched value through it may also write untracked memory (str r5,[r1]).
        with self.assertRaisesRegex(watch.WatchRefusal, 'a store'):
            check({CALLEE: (0xB520, 0xB081, 0x2100, 0x2800, 0xD000, 0x4669, 0x600D, 0xB001, 0xBD20)}, {5})

    def test_indexed_stack_accesses_stay_inside_their_array(self):
        # push {r5,lr}; sub sp,#8; movs r2,#0; str r2,[sp]; str r2,[sp,#4]; mov r1,sp;
        # ldrb r2,[r1,r0]; str r3,[r2]; add sp,#8; pop {r5,pc}: the index is unknown, and the saved
        # R5 at sp+8 is excluded under the recorded premise.
        init = (0xB520, 0xB082, 0x2200, 0x9200, 0x9201)
        rom, entries = rom_with({CALLEE: init + (0x4669, 0x5C0A, 0x6013, 0xB002, 0xBD20)})
        checker = watch.Checker(rom, entries)
        self.assertEqual(checker.call(CALLEE, frozenset({5})), {1: watch.DEAD})
        self.assertEqual(checker.premises, {('index', CALLEE, CALLEE + 12, 'load', (8,))})
        class Proof:
            pass
        proof = Proof()
        proof.rom, proof.entries = rom, entries
        watch.checker_for(proof).call(CALLEE, frozenset({5}))
        self.assertEqual(watch.premise_lines(proof), [
            f'{watch.PREMISE_PREFIX} indexed stack load at 0x{CALLEE + 12:08X} in 0x{CALLEE:08X}, excluding the '
            f'frame word at sp+8 (saved, released or in another function\'s frame); {watch.INDEX_PREMISE}'])
        # An indexed store of the watched value may land in any local: str r5,[r1,r0]; ldr r2,[sp,#4].
        with self.assertRaisesRegex(watch.WatchRefusal, 'memory access base'):
            check({CALLEE: init + (0x4669, 0x500D, 0x9A01, 0x6013, 0xB002, 0xBD20)}, {5})
        self.assertEqual(check({CALLEE: init + (0x4669, 0x9A01, 0x6013, 0xB002, 0xBD20)}, {5}), {1: watch.DEAD})
        # A local never written holds whatever earlier code left there, perhaps a frame address:
        # a store through it (ldr r2,[sp,#4]; str r3,[r2] with no initialisation) is premised at
        # the load (UNSET_PREMISE).
        rom, entries = rom_with({CALLEE: (0xB520, 0xB082, 0x4669, 0x9A01, 0x6013, 0xB002, 0xBD20)})
        checker = watch.Checker(rom, entries)
        checker.call(CALLEE, frozenset({5}))
        self.assertEqual(checker.premises, {('unset', CALLEE, CALLEE + 6, (4,))})
        # In the caller's code after the call the owner's frame is untracked, so it refuses.
        rom, entries = rom_with({CALLEE: (0x4669, 0x500D, BX_LR)})        # mov r1,sp; str r5,[r1,r0]
        with self.assertRaisesRegex(watch.WatchRefusal, 'untracked stack word'):
            watch.Checker(rom, entries).continuation(CALLEE, CALLEE, {5: 5})

    def test_bits_of_a_frame_address_are_no_address(self):
        # push {r5,lr}; mov r0,sp; lsls r0,r0,#24; lsrs r0,r0,#24; ldr r1,=0x03001000; strb r0,[r1]:
        # the low byte of SP stored to IWRAM is bits of the saved R5's address: refused, as that
        # address would be (review-350's P14).
        body = (0xB520, 0x4668, 0x0600, 0x0E00, 0x4901, 0x7008, 0xBD20, 0x46C0, 0x1000, 0x0300)
        with self.assertRaisesRegex(watch.WatchRefusal, 'lets bits of a frame address escape that may reach a saved'):
            check({CALLEE: body}, {5})
        # An arithmetic shift right by 7 or more is no address either: asrs r0,r0,#16; ldrb r2,[r0].
        self.assertEqual(check({CALLEE: (0xB520, 0x4668, 0x1400, 0x7802, 0xBD20)}, {5}), {})
        # The distance between two frame addresses is none: mov r0,sp; add r1,sp,#4; subs r0,r1,r0;
        # ldrb r2,[r0].
        self.assertEqual(check({CALLEE: (0xB520, 0x4668, 0xA901, 0x1A08, 0x7802, 0xBD20)}, {5}), {1: watch.DEAD})
        # Shifted back into the high bits it may be one: lsls r0,r0,#24 again; ldr r2,[r0] refuses.
        with self.assertRaisesRegex(watch.WatchRefusal, 'unknown provenance'):
            check({CALLEE: (0xB520, 0x4668, 0x0600, 0x0E00, 0x0600, 0x6802, 0xBD20)}, {5})

    def test_a_proved_index_range_is_checked_word_by_word(self):
        # An index whose range is proved needs no premise: every word it may reach is checked.
        # push {r5,lr}; sub sp,#4; movs r3,#0; str r3,[sp] (a 4-byte table at sp); mov r1,sp;
        # movs r2,#3; ands r2,r0; ldrb r3,[r1,r2]; ldr r0,[r3]
        table = (0xB520, 0xB081, 0x2300, 0x9300, 0x4669)
        rom, entries = rom_with({CALLEE: table + (0x2203, 0x4002, 0x5C8B, 0x6818, 0xB001, 0xBD20)})
        checker = watch.Checker(rom, entries)
        self.assertEqual(checker.call(CALLEE, frozenset({5})), {1: watch.DEAD})
        self.assertEqual(checker.premises, set())
        # A guarded compare (cmp r2,#3; bhi) bounds it the same way.
        rom, entries = rom_with({CALLEE: table + (0x2A03, 0xD801, 0x5C8B, 0x6818, 0xB001, 0xBD20)})
        checker = watch.Checker(rom, entries)
        self.assertEqual(checker.call(CALLEE, frozenset({5})), {1: watch.DEAD})
        self.assertEqual(checker.premises, set())
        # A loop bound: movs r2,#0; 1: ldrb r3,[r1,r2]; ldr r0,[r3]; adds r2,#1; cmp r2,#3; bls 1b.
        loop = table + (0x2200, 0x5C8B, 0x6818, 0x3201, 0x2A03, 0xD9FA, 0xB001, 0xBD20)
        rom, entries = rom_with({CALLEE: loop})
        checker = watch.Checker(rom, entries)
        self.assertEqual(checker.call(CALLEE, frozenset({5})), {1: watch.DEAD})
        self.assertEqual(checker.premises, set())

    def test_a_range_only_widening_gave_is_an_unknown_index_where_it_would_overrun(self):
        # push {r5,lr}; sub sp,#8; mov r1,sp; movs r2,#0; str r2,[sp]; str r2,[sp,#4];
        # movs r0,#0x20 (a widening threshold, 31); 1: lsls r3,r2,#2; ldr r0,[r1,r3]; ldr r0,[r0];
        # adds r2,#1; <compare>; blt 1b.  The array is sp+0..sp+7; the saved R5 is at sp+8.
        def loop(compare):
            code = (0xB520, 0xB082, 0x4669, 0x2200, 0x9200, 0x9201, 0x2020, 0x0093, 0x58C8, 0x6800, 0x3201,
                    compare, 0xDBF9, 0xB002, 0xBD20)
            rom, entries = rom_with({CALLEE: code})
            checker = watch.Checker(rom, entries)
            checker.call(CALLEE, frozenset({5}))
            return checker.premises
        # cmp r2,r4: nothing bounds the index, so widening gives its range: an unknown index,
        # premised to stay in the array, not checked word by word into the saved R5.
        self.assertEqual(loop(0x42A2), {('index', CALLEE, CALLEE + 16, 'load', (8,))})
        # cmp r2,#2: the comparison proves 0..1, both in the array: no premise.
        self.assertEqual(loop(0x2A02), set())
        # cmp r2,#K: it proves 0..K-1, and index 2 reads the saved R5 on every run: refused, not
        # premised, however far widening first took the range before the comparison bounded it.
        for bound in (3, 4, 8):
            with self.subTest(bound=bound):
                with self.assertRaisesRegex(watch.WatchRefusal, 'uses a watched callee-saved'):
                    loop(0x2A00 | bound)

    def test_a_compare_bounded_loop_that_overruns_its_array_is_refused(self):
        # push {r5,lr}; sub sp,#8; movs r1,#0; mov r0,sp; 1: str r6,[r0,r1]; adds r1,#4;
        # <compare>; <branch> 1b; add sp,#8; pop {r5,pc}.  The array is sp+0..sp+7; sp+8 and
        # sp+12 are the saved R5 and LR.  A range the comparison proves is checked word by word:
        # a store over the saved words refuses on every run, never an INDEX premise.
        def loop(compare, branch):
            return check({CALLEE: (0xB520, 0xB082, 0x2100, 0x4668, 0x5046, 0x3104, compare, branch,
                                   0xB002, 0xBD20)}, {5})
        for name, compare, branch in (("i <= 12, signed", 0x290C, 0xDDFA), ("i <= 12, unsigned", 0x290C, 0xD9FA),
                                      ("i < 16, signed", 0x2910, 0xDBFA), ("i != 12", 0x290C, 0xD1FA)):
            with self.subTest(loop=name):
                with self.assertRaises(watch.WatchRefusal):
                    loop(compare, branch)
        # In bounds (i < 8, signed and unsigned): admitted with no premise.
        for compare, branch in ((0x2908, 0xDBFA), (0x2908, 0xD3FA)):
            rom, entries = rom_with({CALLEE: (0xB520, 0xB082, 0x2100, 0x4668, 0x5046, 0x3104, compare, branch,
                                              0xB002, 0xBD20)})
            checker = watch.Checker(rom, entries)
            checker.call(CALLEE, frozenset({5}))
            self.assertEqual(checker.premises, set())
        # A byte loop bounded by a register the walk knows (movs r3,#4; lsls r3,r3,#1: 8, a value
        # no threshold names): widening first takes the index to 0..255, over the saved words,
        # and the comparison bounds it to 0..7 only on the back edge.  The walk is repeated with
        # the head's range the join of the bounded paths, and the first pass's INDEX line, which
        # rested on the widened range, is not stated.  movs r1,#0; mov r0,sp; 1: strb r6,[r0,r1];
        # adds r1,#1; cmp r1,r3; blt 1b.
        rom, entries = rom_with({CALLEE: (0xB520, 0xB082, 0x2304, 0x005B, 0x2100, 0x4668, 0x5446, 0x3101, 0x4299,
                                          0xDBFB, 0xB002, 0xBD20)})
        checker = watch.Checker(rom, entries)
        checker.call(CALLEE, frozenset({5}))
        self.assertEqual(checker.premises, set())

    def test_a_one_past_the_end_read_of_a_saved_word_is_not_admitted(self):
        # 0x080FCF68's shape (sides[3], one past a 3-byte table): the table is at sp+1, so with
        # the index proved 0..3 the last byte read is the saved R5's.  The read is checked
        # exactly, and the address bits it loads reach a use: refused, not premised.
        # push {r5,lr}; sub sp,#4; movs r0,#0; str r0,[sp]; mov r1,sp; adds r1,#1; cmp r2,#3;
        # bhi 1f; ldrb r3,[r1,r2]; ldr r0,[r3]; 1: add sp,#4; pop {r5,pc}
        table = (0xB520, 0xB081, 0x2000, 0x9000, 0x4669, 0x3101)
        with self.assertRaisesRegex(watch.WatchRefusal, 'a memory access base'):
            check({CALLEE: table + (0x2A03, 0xD801, 0x5C8B, 0x6818, 0xB001, 0xBD20)}, {5})
        # With no bound at all the same read is premised, naming the saved word it excludes.
        rom, entries = rom_with({CALLEE: table + (0x46C0, 0x46C0, 0x5C8B, 0x6818, 0xB001, 0xBD20)})
        checker = watch.Checker(rom, entries)
        checker.call(CALLEE, frozenset({5}))
        self.assertEqual(watch.merged_premises(checker.premises), [('index', CALLEE, CALLEE + 16, 'load', (4,))])
        # In 0x080FCF68 itself the byte past the table is a never-written pad byte: what earlier
        # code left there, perhaps a byte of a frame address.  A byte is no address, so a load
        # through it reaches no frame word ...
        table = (0xB520, 0xB081, 0x2000, 0x466A, 0x7010, 0x7050, 0x7090, 0x4669, 0x2A03)
        # movs r0,#0; mov r2,sp; strb r0,[r2]; strb r0,[r2,#1]; strb r0,[r2,#2]; mov r1,sp; cmp r2,#3
        self.assertEqual(check({CALLEE: table + (0xD801, 0x5C8B, 0x6818, 0xB001, 0xBD20)}, {5}), {1: watch.DEAD, 2: watch.DEAD})
        # ... but shifted back into the high bits it may be one again: lsls r3,r3,#24; ldr r0,[r3].
        # The word may hold plain data as well, so the access is admitted under the premise that
        # the byte read is plain data, stated at the load (0x08014014) where it is relied on.
        rom, entries = rom_with({CALLEE: table + (0xD802, 0x5C8B, 0x061B, 0x6818, 0xB001, 0xBD20)})
        checker = watch.Checker(rom, entries)
        checker.call(CALLEE, frozenset({5}))
        self.assertIn(('bytes', CALLEE, CALLEE + 20, (0,)), checker.premises)
        # A byte of a word that certainly holds a frame address is bits of one: no premise
        # (push {r5,lr}; sub sp,#4; mov r0,sp; str r0,[sp]; mov r1,sp; ldrb r3,[r1]; lsls r3,#24;
        # ldr r0,[r3]).
        with self.assertRaisesRegex(watch.WatchRefusal, 'unknown provenance'):
            check({CALLEE: (0xB520, 0xB081, 0x4668, 0x9000, 0x4669, 0x780B, 0x061B, 0x6818, 0xB001, 0xBD20)}, {5})

    def test_a_pointer_walk_stays_inside_its_array(self):
        # push {r5,lr}; sub sp,#4; mov r0,sp; movs r1,#0; 1: strh r1,[r0]; adds r0,#2; cmp r2,#0;
        # bne 1b; add sp,#4; pop {r5,pc}: the loop bound is unknown, so the pointer may pass the
        # saved R5 and LR; under the premise it does not, and the site is recorded.
        rom, entries = rom_with({CALLEE: (0xB520, 0xB081, 0x4668, 0x2100, 0x8001, 0x3002, 0x2A00, 0xD1FB,
                                          0xB001, 0xBD20)})
        checker = watch.Checker(rom, entries)
        self.assertEqual(checker.call(CALLEE, frozenset({5})), {0: watch.DEAD})
        self.assertEqual(watch.merged_premises(checker.premises), [('index', CALLEE, CALLEE + 8, 'store', (4, 8))])

    def test_a_narrow_store_leaves_the_rest_of_a_frame_address(self):
        # push {r5,lr}; sub sp,#8; mov r0,sp; str r0,[sp,#4]; movs r1,#0; strh r1,[r0,#4];
        # ldr r2,[sp,#4]; <tail>: the high half of the stored SP survives the strh, so R2 is a
        # frame address of unknown provenance (or a number), never a plain number.
        def body(*tail):
            return (0xB520, 0xB082, 0x4668, 0x9001, 0x2100, 0x8081, 0x9A01) + tail + (0xB002, 0xBD20)
        # movs r3,#0; str r3,[r2]: not a stack array base plus an index, so no premise covers it.
        with self.assertRaisesRegex(watch.WatchRefusal, 'unknown provenance'):
            check({CALLEE: body(0x2300, 0x6013)}, {5})
        # Returned, it is a frame address handed back: movs r3,#0.
        self.assertEqual(check({CALLEE: body(0x2300)}, {5}), {0: watch.DEAD, 2: watch.DEAD})
        # str r5,[r2] refuses too.
        with self.assertRaisesRegex(watch.WatchRefusal, 'a store|unknown provenance'):
            check({CALLEE: body(0x6015)}, {5})

    def test_a_returned_frame_address_may_not_be_used(self):
        # sub sp,#8; add r2,sp,#4; add sp,#8; bx lr: R2 is left pointing into the dead frame.
        dead = (0xB082, 0xAA01, 0xB002, BX_LR)
        self.assertEqual(check({CALLEE: dead}, {5}), {2: watch.DEAD})
        rom, entries = rom_with({CALLEE: dead, OTHER: (0x2200, 0x6810, BX_LR)})  # movs r2,#0; ldr r0,[r2]
        watch.Checker(rom, entries).continuation(OTHER, OTHER, {2: watch.DEAD})  # overwritten: admitted
        rom, entries = rom_with({CALLEE: dead, OTHER: (0x6810, BX_LR)})  # ldr r0,[r2]
        with self.assertRaisesRegex(watch.WatchRefusal, 'uses a frame address a callee returned'):
            watch.Checker(rom, entries).continuation(OTHER, OTHER, {2: watch.DEAD})
        # Compared, it is not used as an address: cmp r2,#12; ble; bx lr.
        rom, entries = rom_with({CALLEE: dead, OTHER: (0x2A0C, 0xDDFF, BX_LR)})
        watch.Checker(rom, entries).continuation(OTHER, OTHER, {2: watch.DEAD})

    def test_the_high_register_epilogue_hands_back_its_reloaded_r3(self):
        # The epilogue reloads the saved R8 into R3 before mov r8,r3: R3 holds R8's value at return.
        body = HIGH_PROLOGUE + (0x2000,) + HIGH_EPILOGUE
        self.assertEqual(check({CALLEE: body}, {8}), {3: 8})
        self.assertEqual(check({CALLEE: body}, {4, 5, 6, 7}), {})

    def test_nested_calls_are_checked_while_the_value_is_live(self):
        # The callee leaves R7 alone and calls OTHER, which reads it.
        reader = {CALLEE: (0xB500, OTHER, 0xBC01, 0x4700), OTHER: (0x6839, BX_LR)}
        with self.assertRaisesRegex(watch.WatchRefusal, f'callee 0x{OTHER:08X}'):
            check(reader, {7})
        # Once the callee has overwritten R7, OTHER's read is of the callee's own value.
        writer = {CALLEE: (0xB580, 0x2700, OTHER, 0xBC80, 0xBC01, 0x4700), OTHER: (0x6839, BX_LR)}
        self.assertEqual(check(writer, {7}), {})
        # A call directly after another call is followed too.
        third = 0x08014200
        twice = {CALLEE: (0xB500, third, OTHER, 0xBC01, 0x4700), OTHER: (0x6839, BX_LR), third: (BX_LR,)}
        with self.assertRaisesRegex(watch.WatchRefusal, f'callee 0x{OTHER:08X}'):
            check(twice, {7})
        # A copy OTHER hands back is tracked in the caller too.
        handed = {CALLEE: (0xB500, OTHER, 0xBC02, 0x4708), OTHER: (0x1C38, BX_LR)}
        self.assertEqual(check(handed, {7}), {0: 7})

    def test_a_stale_copy_in_an_argument_register_is_checked_in_the_next_callee(self):
        # mov r3,r8 and a call: OTHER receives R3 = the watched value; it may not read it.
        body = (0xB500, 0x4643, OTHER, 0xBC01, 0x4700)
        self.assertEqual(check({CALLEE: body, OTHER: (0x2300, BX_LR)}, {8}), {})
        with self.assertRaisesRegex(watch.WatchRefusal, f'callee 0x{OTHER:08X}'):
            check({CALLEE: body, OTHER: (0x2B00, BX_LR)}, {8})

    def test_call_via_thunks(self):
        # _call_via_rN with the watched address in RN (R6 and R7 in the issue) would branch into
        # the stack.
        for number in range(4, 12):
            with self.subTest(number=number), \
                    self.assertRaisesRegex(watch.WatchRefusal, f'branches to the watched R{number}'):
                check({}, {number}, target=match.RUNTIME_HELPERS[f'_call_via_r{number}'])
        # With a known R3 the destination itself is checked.
        self.assertEqual(check({CALLEE: (BX_LR,)}, {5}, target=VIA_R3, constants={3: CALLEE | 1}), {})
        with self.assertRaisesRegex(watch.WatchRefusal, f'callee 0x{CALLEE:08X}'):
            check({CALLEE: (0x6829, BX_LR)}, {5}, target=VIA_R3, constants={3: CALLEE | 1})
        # ... followed through a thunk whose register holds another thunk.
        with self.assertRaisesRegex(watch.WatchRefusal, f'callee 0x{CALLEE:08X}'):
            check({CALLEE: (0x6829, BX_LR)}, {5}, target=VIA_R6, constants={6: VIA_R3 | 1, 3: CALLEE | 1})
        # A ROM mirror is ROM code, never code outside ROM: folded onto the ROM it names (kit #377)
        # and walked there.
        for mirror in (0x0A000000 | (CALLEE + 1) & 0x01FFFFFF, 0x0C000000 | (CALLEE + 1) & 0x01FFFFFF):
            with self.subTest(mirror=hex(mirror)):
                self.assertEqual(check({CALLEE: (BX_LR,)}, {5}, target=VIA_R3, constants={3: mirror}), {})
                with self.assertRaisesRegex(watch.WatchRefusal, f'callee 0x{CALLEE:08X}'):
                    check({CALLEE: (0x6829, BX_LR)}, {5}, target=VIA_R3, constants={3: mirror})
        # A known destination that is not Thumb code refuses.
        with self.assertRaisesRegex(watch.WatchRefusal, 'not Thumb code'):
            check({CALLEE: (BX_LR,)}, {5}, target=VIA_R3, constants={3: CALLEE})

    def test_an_unresolved_call_is_admitted_under_the_recorded_premise(self):
        # ldr r3,[r0] (unknown); bl _call_via_r3 inside a callee, R5 still watched.
        body = (0xB500, 0x6803, VIA_R3, 0xBC01, 0x4700)
        rom, entries = rom_with({CALLEE: body, OTHER: (0xB500, 0x6803, VIA_R3, 0xBD00)})
        checker = watch.Checker(rom, entries)
        self.assertEqual(checker.call(CALLEE, frozenset({5})), {})
        self.assertEqual(checker.premises, {('call', CALLEE, CALLEE + 4, (3,), None, (5,), (), False)})
        # The same call made by the owner itself (its site given).
        self.assertEqual(checker.call(VIA_R3, frozenset({4, 8}), {}, caller=OTHER, site=OTHER + 4), {})
        self.assertIn(('call', OTHER, OTHER + 4, (3,), None, (4, 8), (), False), checker.premises)
        # Without a caller and site no premise can be stated, so the call refuses.
        with self.assertRaisesRegex(watch.WatchRefusal, 'indirect call through a call-via thunk'):
            checker.call(VIA_R3, frozenset({5}))
        # IP is scratch that thunks read (_call_via_ip): a watched copy there refuses at the call
        # (push {r5,lr}; mov ip,r5; ldr r3,[r0]; bl _call_via_r3), as in kit #348.
        with self.assertRaisesRegex(watch.WatchRefusal, 'receives an owner stack address in R12'):
            check({CALLEE: (0xB520, 0x46AC, 0x6803, VIA_R3, 0xBD20)}, {5})
        # A watched value copied into R0-R3 or R12 reaches the unknown callee as an argument.
        copied = (0xB500, 0x1C28, 0x6813, VIA_R3, 0xBC01, 0x4700)  # adds r0,r5,#0; ldr r3,[r2]
        with self.assertRaisesRegex(watch.WatchRefusal, 'receives an owner stack address in R0'):
            check({CALLEE: copied}, {5})
        # A frame address passed to it (a buffer argument) is covered by the premise, unless it
        # points at a word that holds the watched value (push {r5,lr}; mov r0,sp; ldr r3,[r2]).
        # The unwalked code may hand the address back in R0-R3 or R12: left there at the return,
        # they are frame addresses the caller may not use.
        rom, entries = rom_with({CALLEE: (0xB520, 0xA801, 0x6813, VIA_R3, 0xBD20)})   # add r0,sp,#4
        checker = watch.Checker(rom, entries)
        self.assertEqual(checker.call(CALLEE, frozenset({5})), dict.fromkeys((0, 1, 2, 3, 12), watch.DEAD))
        self.assertEqual(checker.premises, {('call', CALLEE, CALLEE + 6, (3,), None, (5,), (0,), False)})
        with self.assertRaisesRegex(watch.WatchRefusal, 'address of a frame word'):
            check({CALLEE: (0xB520, 0x4668, 0x6813, VIA_R3, 0xBD20)}, {5})
        # The caller (push {r5,lr}; bl CALLEE; movs r0-r3,#0; ldr r3,[r3]; bl _call_via_r3) passes
        # nothing to its own unresolved call, but leaves that DEAD address in IP: an argument it is
        # given, which may address any word of the walked frames, and the premise states that it
        # does not branch to it.  A watched value there still refuses (above).
        owner = (0xB520, CALLEE, 0x2000, 0x2100, 0x2200, 0x2300, 0x681B, VIA_R3, 0xBD20)
        rom, entries = rom_with({CALLEE: (0xB520, 0xA801, 0x6813, VIA_R3, 0xBD20), OTHER: owner})
        checker = watch.Checker(rom, entries)
        checker.call(CALLEE, frozenset({5}), caller=OTHER, site=OTHER + 2)
        self.assertIn(('call', OTHER, OTHER + 16, (3,), None, (12,), (), False), checker.premises)

        class Proof:
            pass
        proof = Proof()
        proof.rom, proof.entries = rom, entries
        watch.checker_for(proof).premises.update(checker.premises)
        # The same left in IP at a SWI (svc #0x0B in place of the call), under the BIOS premise.
        swi = owner[:7] + (0xDF0B, 0xBD20)
        rom, entries = rom_with({CALLEE: (0xB520, 0xA801, 0x6813, VIA_R3, 0xBD20), OTHER: swi})
        checker2 = watch.Checker(rom, entries)
        checker2.call(CALLEE, frozenset({5}), caller=OTHER, site=OTHER + 2)
        self.assertIn(('swi', OTHER, OTHER + 16, 0x0B, (12,), (), False), checker2.premises)
        swi_proof = Proof()
        swi_proof.rom, swi_proof.entries = rom, entries
        watch.checker_for(swi_proof).premises.update(checker2.premises)
        self.assertIn(f'* callee-saved premise: SWI 0x0B (CpuSet) at 0x{OTHER + 16:08X} in 0x{OTHER:08X}, with R12 '
                      f'holding a frame address a callee returned; {watch.bios_premise(0x0B)}',
                      watch.premise_lines(swi_proof))
        # At a SWI, R12 is no argument: the BIOS dispatcher saves it and loads the routine's address
        # there.  THIRD, called after CALLEE returns, keeps a plain local (str r0,[sp]) across code
        # that is not walked and stores its bits out (ldr r1,[sp]; lsls r1,#12; ldr r2,=G;
        # strh r1,[r2]).  Code reached through a function pointer may have written the address in
        # R12 there; the BIOS may not.
        g = 0x02000100
        head = (0xB500, 0xB081, 0x2000, 0x9000, 0x2100, 0x2200, 0x2300, 0x681B)
        tail = (0x9900, 0x0309, 0x4A02, 0x8011, 0xB001, 0xBC01, 0x4700, 0x46C0, g & 0xFFFF, g >> 16)
        # (IntrWait, a SWI with no documented writes: one that may store what it is handed.)
        for mid, admitted in (((VIA_R3,), False), ((0xDF04, 0x46C0), True)):
            rom, entries = rom_with({CALLEE: (0xB520, 0xA801, 0x6813, VIA_R3, 0xBD20),
                                     OTHER: (0xB520, CALLEE, THIRD, 0xBD20), THIRD: head + mid + tail})
            checker3 = watch.Checker(rom, entries)
            if admitted:
                checker3.call(CALLEE, frozenset({5}), caller=OTHER, site=OTHER + 2)
                self.assertIn(('swi', THIRD, THIRD + 16, 0x04, (12,), (), False), checker3.premises)
            else:
                with self.assertRaisesRegex(watch.WatchRefusal, 'bits of a frame address'):
                    checker3.call(CALLEE, frozenset({5}), caller=OTHER, site=OTHER + 2)
        rom, entries = rom_with({CALLEE: (0xB520, 0xA801, 0x6813, VIA_R3, 0xBD20), OTHER: owner})
        self.assertIn(f'* callee-saved premise: call at 0x{OTHER + 16:08X} in 0x{OTHER:08X} through _call_via_r3 '
                      f'to an unknown address, with R12 holding a frame address a callee returned; '
                      f'{watch.PREMISE.replace(", and returns", ", returns")}, and {watch.R12_PREMISE}',
                      watch.premise_lines(proof))
        # Every other refusal stands: a read of the watched value before that call.
        with self.assertRaisesRegex(watch.WatchRefusal, 'watched callee-saved'):
            check({CALLEE: (0xB500, 0x6829, 0x6803, VIA_R3, 0xBC01, 0x4700)}, {5})

    def test_the_bios_stores_no_address_it_is_handed(self):
        # push {lr}; sub sp,#8; mov r0,sp; movs r1,#0; str r1,[sp,#4]; <svc #N; nop; nop | ldr r3,[r2];
        # bl _call_via_r3>; ldr r1,[sp,#4]; lsls r1,r1,#12; ldr r2,=G; strh r1,[r2]: the local at
        # sp+4 is in the object the code not walked is handed.  Code reached through a function
        # pointer may store that address there, so its bits escape.  An enumerated BIOS routine
        # stores what GBATEK documents (BIOS_WRITES): nothing, numbers, or a copy of the objects.
        g = 0x02000100
        head = (0xB500, 0xB082, 0x4668, 0x2100, 0x9101)
        tail = (0x9901, 0x0309, 0x4A02, 0x8011, 0xB002, 0xBC01, 0x4700, 0x46C0, g & 0xFFFF, g >> 16)
        with self.assertRaisesRegex(watch.WatchRefusal, 'bits of a frame address'):
            check({CALLEE: head + (0x6813, VIA_R3) + tail}, {5})
        for number in (0x06, 0x0B, 0x0E, 0x0F):          # Div, CpuSet, BgAffineSet, ObjAffineSet
            with self.subTest(swi=hex(number)):
                rom, entries = rom_with({CALLEE: head + (0xDF00 | number, 0x46C0, 0x46C0) + tail})
                checker = watch.Checker(rom, entries)
                checker.call(CALLEE, frozenset({5}))
                self.assertEqual(sorted(checker.premises), [('stale', CALLEE, CALLEE + 10, (0,)),
                                                            ('swi', CALLEE, CALLEE + 10, number, (5,), (), False)])
                proof = type('Proof', (), {})()
                proof.rom, proof.entries = rom, entries
                watch.checker_for(proof).premises.update(checker.premises)
                self.assertIn(f'{watch.PREMISE_PREFIX} SWI 0x{number:02X} ({watch.BIOS_WRITES[number][0]}) at '
                              f'0x{CALLEE + 10:08X} in 0x{CALLEE:08X}, with R5 depending on owner stack addresses; '
                              f'{watch.bios_premise(number)}', watch.premise_lines(proof))
        # A SWI the decomp's reports do not reach (LZ77UnCompWram) may store any address it is handed.
        with self.assertRaisesRegex(watch.WatchRefusal, 'bits of a frame address'):
            check({CALLEE: head + (0xDF11, 0x46C0, 0x46C0) + tail}, {5})
        # The buffer holds its own address (str r0,[sp]): CpuSet's copy may put it at sp+4, so it stays
        # an address there and its bits escape; the routines that compute numbers or store nothing
        # leave sp+4 plain.
        head = (0xB500, 0xB082, 0x4668, 0x9000, 0x2100, 0x9101)
        tail = (0x9901, 0x0309, 0x4A02, 0x8011, 0xB002, 0xBC01, 0x4700, g & 0xFFFF, g >> 16)
        for number in (0x0B, 0x0C):
            with self.subTest(swi=hex(number)), self.assertRaisesRegex(watch.WatchRefusal, 'bits of a frame address'):
                check({CALLEE: head + (0xDF00 | number, 0x46C0, 0x46C0) + tail}, {5})
        for number in (0x06, 0x0E, 0x0F):
            with self.subTest(swi=hex(number)):
                rom, entries = rom_with({CALLEE: head + (0xDF00 | number, 0x46C0, 0x46C0) + tail})
                checker = watch.Checker(rom, entries)
                checker.call(CALLEE, frozenset({5}))
                self.assertEqual(sorted(checker.premises), [('swi', CALLEE, CALLEE + 12, number, (5,), (), False)])

    def test_a_game_state_invariant_is_named_in_its_index_line(self):
        rom, entries = rom_with({CALLEE: (BX_LR,)})
        proof = type('Proof', (), {})()
        proof.rom, proof.entries = rom, entries
        watch.checker_for(proof).premises.update({('index', 0x0809AC20, 0x0809AC22, 'store', (4,)),
                                                  ('index', CALLEE, CALLEE, 'store', (4,))})
        lines = watch.premise_lines(proof)
        self.assertEqual([line.endswith(f'; game-state invariant: {watch.GAME_STATE_INVARIANTS[0x0809AC22]}')
                          for line in lines], [False, True])

    def test_an_enumerated_swi_given_frame_addresses_is_stated(self):
        # In the owner's continuation nothing depends on its stack address any more; THIRD clears
        # R0-R3 and R12, then hands its buffer to ObjAffineSet (svc #0x0F), directly or through a
        # wrapper skipped with its summary.  What the routine stores there is premised: the line
        # says "given frame addresses".  IntrWait (svc #0x04) gets no write premise and no line.
        wrap = 0x08014300
        head = (0xB500, 0xB082, 0x2000, 0x4684, 0x2100, 0x2200, 0x2300, 0x4668)
        tail = (0xB002, 0xBC01, 0x4700)
        callee = (0xB520, 0xA801, 0x6813, VIA_R3, 0xBD20)
        owner = (0xB520, CALLEE, THIRD, 0xBD20)
        for third, functions, swi in ((head + (0xDF0F,) + tail, {}, ('swi', THIRD, THIRD + 16, 0x0F, (), (), False)),
                                      (head + (wrap,) + tail, {wrap: (0xDF0F, BX_LR)},
                                       ('swi', wrap, wrap, 0x0F, (), (), False)),
                                      (head + (0xDF04,) + tail, {}, None)):
            with self.subTest(swi=swi):
                rom, entries = rom_with({CALLEE: callee, OTHER: owner, THIRD: third, **functions})
                checker = watch.Checker(rom, entries)
                checker.call(CALLEE, frozenset({5}), caller=OTHER, site=OTHER + 2)
                swis = [record for record in checker.premises if record[0] == 'swi']
                self.assertEqual(swis, [swi] if swi else [])

    def test_function_pointers_in_rom_are_resolved_and_walked(self):
        table, ram = 0x08020000, 0x03005E79
        reader, quiet = (0x6829, BX_LR), (BX_LR,)          # ldr r1,[r5]: reads the watched R5

        def caller(*after, literal):
            # push {lr}; ldr r3,=literal; <after>; bl _call_via_r3; pop {r0}; bx r0; .word literal
            code = [0xB500, 0x4B00, *after, VIA_R3, 0xBC01, 0x4700]
            size = len(assemble(CALLEE, code))
            code[1] |= (size + size % 4 - 4) // 4                 # the pool word after the code
            return tuple(code) + ((0x46C0,) if size % 4 else ()) + (literal & 0xFFFF, literal >> 16)

        def run(code, other, rom_word=None):
            rom, entries = rom_with({CALLEE: code, OTHER: other})
            rom = bytearray(rom)
            if rom_word is not None:
                rom[table - BASE:table - BASE + 4] = struct.pack('<I', rom_word)
            checker = watch.Checker(bytes(rom), entries)
            return checker.call(CALLEE, frozenset({5})), checker.premises

        # A literal function pointer: the destination is walked.
        direct = caller(literal=OTHER | 1)
        with self.assertRaisesRegex(watch.WatchRefusal, f'callee 0x{OTHER:08X}'):
            run(direct, reader)
        self.assertEqual(run(direct, quiet), ({}, set()))
        # A pointer read from a ROM word (a table or ROM variable): also walked.
        indirect = caller(0x681B, literal=table)                        # ldr r3,[r3]
        with self.assertRaisesRegex(watch.WatchRefusal, f'callee 0x{OTHER:08X}'):
            run(indirect, reader, rom_word=OTHER | 1)
        self.assertEqual(run(indirect, quiet, rom_word=OTHER | 1), ({}, set()))
        # A ROM word naming code in RAM (an installed IWRAM routine): premised, destination stated.
        self.assertEqual(run(indirect, reader, rom_word=ram),
                         ({}, {('call', CALLEE, CALLEE + 6, (3,), ram, (5,), (), False)}))
        # A pointer kept in a frame word (sub sp,#4; str r3,[sp]; ldr r3,[sp]; add sp,#4): the word
        # load brings back what the store wrote, so the destination is still walked ...
        kept = caller(0xB081, 0x9300, 0x9B00, 0xB001, literal=OTHER | 1)
        with self.assertRaisesRegex(watch.WatchRefusal, f'callee 0x{OTHER:08X}'):
            run(kept, reader)
        # ... unless the word is written again in between (ldr r0,[r0]; str r0,[sp]): premised.
        rewritten = caller(0xB081, 0x9300, 0x6800, 0x9000, 0x9B00, 0xB001, literal=OTHER | 1)
        self.assertEqual(run(rewritten, reader), ({}, {('call', CALLEE, CALLEE + 16, (3,), None, (5,), (), False)}))

    def test_a_pointer_survives_a_call_that_preserves_it(self):
        # push {r5,lr}; ldr r6,=OTHER|1; bl THIRD; bl _call_via_r6; pop {r5,pc}: R5 is live at the
        # call to THIRD, so THIRD is walked in context, R6 provably survives and OTHER is walked.
        third = 0x08014200
        code = (0xB520, 0x4E03, third, VIA_R6, 0xBD20, 0x46C0, (OTHER | 1) & 0xFFFF, OTHER >> 16)
        functions = {CALLEE: code, OTHER: (0x6829, BX_LR), third: (BX_LR,)}
        with self.assertRaisesRegex(watch.WatchRefusal, f'callee 0x{OTHER:08X}'):
            check(functions, {5})
        # With R5 overwritten first (movs r5,#0), only its saved copy is live: THIRD is skipped
        # with its summary, which shows it returns R6 unchanged, so OTHER is resolved and
        # skipped too (its read is through R5, now 0).  Nothing is premised.
        code = (0xB520, 0x2500, 0x4E02, third, VIA_R6, 0xBD20, (OTHER | 1) & 0xFFFF, OTHER >> 16)
        rom, entries = rom_with({**functions, CALLEE: code})
        checker = watch.Checker(rom, entries)
        self.assertEqual(checker.call(CALLEE, frozenset({5})), {})
        self.assertEqual(checker.premises, set())
        # A callee that clobbers R6 (movs r6,#0) leaves the thunk unresolved: premised.
        rom, entries = rom_with({**functions, CALLEE: code, third: (0x2600, BX_LR)})
        checker = watch.Checker(rom, entries)
        self.assertEqual(checker.call(CALLEE, frozenset({5})), {})
        self.assertEqual(checker.premises, {('call', CALLEE, CALLEE + 10, (6,), None, (), (0,), False)})

    def test_known_arguments_resolve_a_callback(self):
        # CALLEE keeps its R1 argument in R6 and calls it: adds r6,r1,#0; bl _call_via_r6
        code = (0xB500, 0x1C0E, VIA_R6, 0xBC01, 0x4700)
        rom, entries = rom_with({CALLEE: code, OTHER: (0x6829, BX_LR)})
        with self.assertRaisesRegex(watch.WatchRefusal, f'callee 0x{OTHER:08X}'):
            watch.Checker(rom, entries).call(CALLEE, frozenset({5}), {1: OTHER | 1})
        checker = watch.Checker(rom, entries)
        self.assertEqual(checker.call(CALLEE, frozenset({5}), {}), {})
        self.assertEqual(checker.premises, {('call', CALLEE, CALLEE + 4, (6,), None, (5,), (), False)})

    def test_premise_lines(self):
        class Proof:
            rom, entries = rom_with({})
        proof = Proof()
        self.assertEqual(watch.premise_lines(proof), [])
        checker = watch.checker_for(proof)
        checker.premises.update({('call', CALLEE, CALLEE + 4, (3,), None, (5,), (), False),
                                 ('call', OTHER, OTHER + 6, (6, 2), 0x03005E79, (4, 8), (0, 12), True),
                                 ('swi', THIRD, THIRD + 2, 6, (), (-4,), False)})
        self.assertEqual(watch.premise_lines(proof), [
            f'{watch.PREMISE_PREFIX} call at 0x{CALLEE + 4:08X} in 0x{CALLEE:08X} through _call_via_r3 '
            f'to an unknown address, with R5 depending on owner stack addresses; {watch.PREMISE}',
            f'{watch.PREMISE_PREFIX} call at 0x{OTHER + 6:08X} in 0x{OTHER:08X} through _call_via_r6 then '
            f'_call_via_r2 resolved to 0x03005E79 (IWRAM), with R4,R8 and the frame words at sp+0,sp+12 '
            f'and the condition flags depending on owner stack addresses; {watch.PREMISE}',
            f'{watch.PREMISE_PREFIX} SWI 0x06 (Div) at 0x{THIRD + 2:08X} in 0x{THIRD:08X}, with the frame word '
            f'at sp-4 depending on owner stack addresses; {watch.bios_premise(0x06)}'])
        self.assertEqual([watch.region(a) for a in (0x02000000, 0x03007FFF, 0x06000001, 0x09000000, 0x0A000001,
                                                    0x0D000000)],
                         ['EWRAM', 'IWRAM', 'VRAM', 'ROM space beyond the image', 'ROM mirror', 'ROM mirror'])

    def test_a_large_frame_set_up_through_a_register(self):
        # push {r5,lr}; ldr r3,=-512; add sp,r3; ldr r3,=512; add sp,r3; pop {r5,pc}
        body = (0xB520, 0x4B02, 0x449D, 0x4B02, 0x449D, 0xBD20, 0xFE00, 0xFFFF, 0x0200, 0x0000)
        self.assertEqual(check({CALLEE: body}, {5}), {})

    def test_a_delegate_proof_reports_through_its_parent(self):
        class Proof:
            rom, entries = rom_with({})
        parent, child = Proof(), Proof()
        watch.delegate(child, parent)
        watch.checker_for(child).premises.add(('call', CALLEE, CALLEE + 4, (3,), None, (5,), (), False))
        self.assertEqual(len(watch.premise_lines(parent)), 1)
        self.assertEqual(watch.premise_lines(child), watch.premise_lines(parent))

    def test_local_calls_swi_and_recursion(self):
        # push {lr}; bl 1f; pop {pc}; 1: bx lr: a local call returns to its continuation.
        local = (0xB500, CALLEE + 8, 0xBD00, BX_LR)
        self.assertEqual(check({CALLEE: local}, {7}), {})
        # svc 1; bx lr: admitted under the BIOS premise, which is recorded.
        rom, entries = rom_with({CALLEE: (0xDF01, BX_LR)})
        checker = watch.Checker(rom, entries)
        self.assertEqual(checker.call(CALLEE, frozenset({7})), {})
        self.assertEqual(checker.premises, {('swi', CALLEE, CALLEE, 1, (7,), (), False)})
        # A SWI given a watched value in R0-R3 refuses (adds r0,r7,#0; svc 1).
        with self.assertRaisesRegex(watch.WatchRefusal, 'R0 at a SWI'):
            check({CALLEE: (0x1C38, 0xDF01, BX_LR)}, {7})
        # Recursion while a watched value is live is walked in context until MAX_DEPTH, then
        # refuses (push {lr}; cmp r0,#0; beq 1f; bl self; 1: pop {pc}).
        recursive = (0xB500, 0x2800, 0xD001, CALLEE, 0xBD00)
        with self.assertRaisesRegex(watch.WatchRefusal, 'nested too deeply'):
            check({CALLEE: recursive}, {7})

    def test_a_handed_back_copy_is_checked_in_the_caller(self):
        rom, entries = rom_with({CALLEE: (0xB500, OTHER, 0x6018, 0xBD00),     # bl; str r0,[r3]; pop {pc}
                                 OTHER: (0x2300, 0x6018, 0xBD00)})           # movs r3,#0; ...
        checker = watch.Checker(rom, entries)
        with self.assertRaisesRegex(watch.WatchRefusal, 'watched callee-saved'):
            checker.continuation(CALLEE, CALLEE + 6, {3})                      # r3 used as a base
        checker.continuation(OTHER, OTHER, {3})                                # overwritten first
        with self.assertRaisesRegex(watch.WatchRefusal, 'indirect branch'):
            checker.continuation(OTHER, OTHER + 4, {0})                       # live at the return

    def test_unmodelled_control_refuses(self):
        with self.assertRaisesRegex(watch.WatchRefusal, 'not a recognised word switch'):
            check({CALLEE: (0x4687,)}, {7})                       # mov pc,r0
        with self.assertRaisesRegex(watch.WatchRefusal, 'indirect branch'):
            check({CALLEE: (0x4700,)}, {7})                       # bx r0
        with self.assertRaisesRegex(ValueError, 'only R4-R11'):
            check({CALLEE: (BX_LR,)}, {3})


TAIL = (0x2000, 0x2100, 0x2200, 0x2300)


def owner_code(middle):
    """push {r4-r7,lr}; sub sp,#16; r4 = entry_R0 & 3; copy 4 table bytes to sp; <middle>;
    mov r1,sp; ldrb r0,[r1,r4]; movs r0-r3,#0; return."""
    code = [0xB5F0, 0xB084, 0x1C04, 0x2103, 0x400C, 0x4668, 0, 0x2204, HELPER, *middle,
            0x4669, 0x5D08, *TAIL, 0xB004, 0xBCF0, 0xBC02, 0x4708]
    raw = len(assemble(OWNER, code))
    literal = raw + (-raw % 4)
    code[6] = 0x4900 | ((literal - ((2 * 6 + 4) & ~3)) // 4)
    return code


def verify(middle, callee, selector=sip.SELECTOR):
    """Verify the owner ``owner_code(middle)`` with ``callee`` at CALLEE, or with every function
    of a {address: tokens} dict."""
    functions = callee if isinstance(callee, dict) else {CALLEE: callee}
    thunk = struct.pack('<2H', 0x4718, 0x46C0)                   # _call_via_r3: bx r3; nop
    patch = {VIA_R3 + n: b for n, b in enumerate(thunk)}
    extra = [(VIA_R3, 2, 1)]
    for address, tokens in functions.items():
        raw = assemble(address, tokens)
        patch.update({address + n: b for n, b in enumerate(raw)})
        extra.append((address, len(raw), len(tokens)))
    arguments, _ = fixture(owner_code(middle), selector=selector, extra_functions=extra, patch_rom=patch)
    return owner.verify(**arguments)


RANGED_R7 = (0x466B, 0x195B, 0x1C1F, 0x2300)    # mov r3,sp; adds r3,r3,r5; adds r7,r3,#0; movs r3,#0
RANGED_R8 = (0x466B, 0x195B, 0x4698, 0x2300)    # ... mov r8,r3; movs r3,#0


class OwnerTests(unittest.TestCase):
    """The issue's and the #348 review's reproducers, admitted on main before #350."""

    def test_ranged_address_in_a_callee_saved_register(self):
        cases = {
            'callee stores through r7': (RANGED_R7 + (CALLEE,), (0x6039, BX_LR)),
            'callee not walked: bx r7': (RANGED_R7 + (0x2000, CALLEE), (0x4738, 0x46C0)),
        }
        for selector in sip.SELECTORS:
            for name, (middle, callee) in cases.items():
                with self.subTest(selector=selector, case=name), \
                        self.assertRaisesRegex(sip.Refusal, 'callee-saved register at a call'):
                    verify(middle, callee, selector)

    def test_a_handed_back_address_must_be_dead_in_the_owner(self):
        # The callee copies the address into ip or r0; the owner's later use of the copy refuses.
        cases = {
            'mov ip,r7': (RANGED_R7 + (CALLEE, 0x4663, 0x601E), (0x46BC, BX_LR)),
            'adds r0,r7,#0': (RANGED_R7 + (CALLEE, 0x6006), (0x1C38, BX_LR)),
            'mov ip,r8': (RANGED_R8 + (CALLEE, 0x4663, 0x601E, 0x46A0), (0x46C4, BX_LR)),
        }
        for name, (middle, callee) in cases.items():
            with self.subTest(name), self.assertRaisesRegex(sip.Refusal, 'callee-saved register at a call'):
                verify(middle, callee)
        # The agbcc epilogue's reloaded R3, overwritten before any use, is admitted.
        manifest, _ = verify(RANGED_R8 + (CALLEE, 0x46A0), HIGH_PROLOGUE + (0x2000,) + HIGH_EPILOGUE)
        self.assertEqual(manifest['profile'], sip.SCHEMA)

    def test_exact_alias_in_a_callee_saved_register(self):
        # The core's analogue: mov r7,sp kept over the call.
        with self.assertRaisesRegex(ValueError, 'watched callee-saved'):
            verify((0x466F, 0x2000, CALLEE), (0x6039, BX_LR))      # callee str r1,[r7]
        # adds r0,r7,#0 hands it back; the owner's store at [r0,#32] (its saved LR) uses the copy.
        with self.assertRaisesRegex(ValueError, 'watched callee-saved'):
            verify((0x466F, 0x2000, CALLEE, 0x6206), (0x1C38, BX_LR))
        # A copy the owner overwrites first (movs r0,#0) is dead and admitted.
        manifest, _ = verify((0x466F, 0x2000, CALLEE, 0x2000), (0x1C38, BX_LR))
        self.assertEqual(manifest['profile'], sip.SCHEMA)

    def test_controls_are_admitted(self):
        # A scalar in R4 read by the callee (the 0x0809801C callers' shape) is no stack address.
        for callee in ((0x4022, BX_LR), (BX_LR,)):                 # ands r2,r4
            manifest, _ = verify((0x2000, CALLEE), callee)
            self.assertEqual(manifest['profile'], sip.SCHEMA)
        # A ranged address in R7 over a callee that saves and restores R7.
        manifest, _ = verify(RANGED_R7 + (CALLEE,), (0xB580, 0x2700, 0xBC80, 0xBC01, 0x4700))
        self.assertEqual(manifest['profile'], sip.SCHEMA)
        self.assertNotIn('callee_saved_premises', manifest['proof']['buffers'])

    def test_an_unresolved_call_is_stated_in_the_manifest(self):
        # The callee calls through _call_via_r3 with an unknown R3 while R7 holds the address.
        callee = (0xB500, 0x6803, VIA_R3, 0xBC01, 0x4700)
        for selector in sip.SELECTORS:
            with self.subTest(selector=selector):
                manifest, _ = verify(RANGED_R7 + (0x2000, CALLEE), callee, selector)
                self.assertEqual(manifest['proof']['buffers']['callee_saved_premises'], [
                    f'{watch.PREMISE_PREFIX} call at 0x{CALLEE + 4:08X} in 0x{CALLEE:08X} through '
                    f'_call_via_r3 to an unknown address, with R7 depending on owner stack addresses; '
                    f'{watch.PREMISE}'])
        # The callee reading R7 before that call still refuses.
        with self.assertRaisesRegex(sip.Refusal, 'callee-saved register at a call'):
            verify(RANGED_R7 + (0x2000, CALLEE), (0xB500, 0x6839, 0x6803, VIA_R3, 0xBC01, 0x4700))



EXACT = (0x466F, 0x2000)          # mov r7,sp; movs r0,#0: the core's exact alias R7 = owner SP


class ReviewReproducerTests(unittest.TestCase):
    """The #350 review's reproducers: each walk admitted a use of the owner's address."""

    def refuses(self, functions, watched, pattern='uses a watched callee-saved'):
        with self.assertRaisesRegex(watch.WatchRefusal, pattern):
            check(functions, watched)

    def test_frame_addresses_handed_back_by_unwalked_code_stay_frame_addresses(self):
        # The review's N1-N3: code that is not walked, given a buffer at sp, may hand its address
        # back exactly (memcpy returns dest) or anywhere in the buffer.  The caller then reads
        # [r0,#8], one past the 8-byte buffer: exactly the saved R5 when it is handed back as given,
        # so the read is modelled, not premised, and the store through the copy refuses.
        # N1: push {r5,lr}; sub sp,#8; mov r0,sp; ldr r3,[r1]; bl _call_via_r3; ldr r1,[r0,#8];
        # movs r2,#0; str r2,[r1]
        n1 = (0xB520, 0xB082, 0x4668, 0x680B, VIA_R3, 0x6881, 0x2200, 0x600A, 0xB002, 0xBD20)
        # N2: the same through the BIOS (svc #0x0B returns R0, R1 and R3 changed).
        n2 = (0xB520, 0xB082, 0x4668, 0xDF0B, 0x6881, 0x2200, 0x600A, 0xB002, 0xBD20)
        # N3: it may store the address into the buffer (s->p = &s->q); ldr r1,[sp]; ldr r1,[r1,#8].
        n3 = (0xB520, 0xB082, 0x4668, 0x680B, VIA_R3, 0x9900, 0x6889, 0x2200, 0x600A, 0xB002, 0xBD20)
        for name, body in (('N1', n1), ('N2', n2), ('N3', n3)):
            with self.subTest(name):
                self.refuses({CALLEE: body}, {5}, 'memory access base')
        # An interior read ([r0,#4], inside the buffer) is premised: as given it reads the buffer's
        # second word, and anywhere in the buffer it stays inside under the premise, which names the
        # saved word it excludes (sp+8); the store through what it read likewise.
        interior = (0xB520, 0xB082, 0x4668, 0x680B, VIA_R3, 0x6841, 0x2200, 0x600A, 0xB002, 0xBD20)
        rom, entries = rom_with({CALLEE: interior})
        checker = watch.Checker(rom, entries)
        self.assertEqual(checker.call(CALLEE, frozenset({5})), dict.fromkeys((0, 1, 3, 12), watch.DEAD))
        self.assertEqual(checker.premises, {('call', CALLEE, CALLEE + 8, (3,), None, (5,), (8,), False),
                                            ('stale', CALLEE, CALLEE + 8, (0, 4)),
                                            ('index', CALLEE, CALLEE + 12, 'load', (8,)),
                                            ('index', CALLEE, CALLEE + 16, 'store', (8, 12))})
        # No premise where the access can reach no admissible word: a buffer-less frame (push
        # {r5,lr}; mov r0,sp; ldr r2,[r1]; adds r0,r0,r2; ldr r1,[r0]) reaches only saved words.
        self.refuses({CALLEE: (0xB520, 0x4668, 0x680A, 0x1880, 0x6801, 0xBD20)}, {5}, 'can reach only saved')
        # Without the premises, the handed-back address read as an address refuses: here the
        # word read back is used to address memory through bits rebuilt from it.
        with self.assertRaisesRegex(watch.WatchRefusal, 'unknown provenance|memory access base'):
            check({CALLEE: (0xB520, 0xB082, 0x4668, 0x680B, VIA_R3, 0x6881, 0x0609, 0x600A, 0xB002, 0xBD20)}, {5})

    def test_bytes_and_words_that_may_hold_part_of_an_address_are_premised_where_they_can_be_plain(self):
        # REBUILT: push {r5,lr}; sub sp,#8; mov r0,sp; str r0,[sp,#4]; ldr r2,[r1]; mov r3,sp;
        # adds r3,r3,r2; lsls r0,#16; lsrs r0,#16; strh r0,[r3] (bits of SP, through an array
        # base plus an index, which may hit sp+4); ldr r0,[sp,#4]; ldr r0,[r0].  The store may
        # have missed sp+4, which then still holds the whole address: premised at the load.
        body = (0xB520, 0xB082, 0x4668, 0x9001, 0x680A, 0x466B, 0x189B, 0x0400, 0x0C00, 0x8018, 0x9801, 0x6800,
                0xB002, 0xBD20)
        rom, entries = rom_with({CALLEE: body})
        checker = watch.Checker(rom, entries)
        checker.call(CALLEE, frozenset({5}))
        self.assertEqual(checker.premises, {('index', CALLEE, CALLEE + 18, 'store', (8, 12)),
                                            ('rebuilt', CALLEE, CALLEE + 20, (4,))})
        # The same store certainly at sp+4 (strh r0,[r3,#4] with r3 = sp) leaves part of an
        # address: no premise can hold, and the access through it refuses.
        exact = (0xB520, 0xB082, 0x4668, 0x9001, 0x466B, 0x0400, 0x0C00, 0x8098, 0x9801, 0x6800, 0xB002, 0xBD20)
        self.refuses({CALLEE: exact}, {5}, 'unknown provenance')
        # READ: push {r5,lr}; movs r5,#0; sub sp,#8; mov r0,sp; ldr r3,[r1]; bl _call_via_r3 (it
        # may store addresses in the buffer); mov r0,sp; bl OTHER.  OTHER (ldrb r1,[r0]; bx lr),
        # summarised, reads a byte of a word that may hold a frame address or plain data: premised
        # at OTHER's load, as the walk in context would name it.
        reader = (0xB520, 0x2500, 0xB082, 0x4668, 0x680B, VIA_R3, 0x4668, OTHER, 0xB002, 0xBD20)
        rom, entries = rom_with({CALLEE: reader, OTHER: (0x7801, BX_LR)})
        checker = watch.Checker(rom, entries)
        checker.call(CALLEE, frozenset({5}))
        self.assertIn(('bytes', OTHER, OTHER, (0,)), checker.premises)
        # A word read (ldr r1,[r0]) is walked in context instead, with no such premise.
        rom, entries = rom_with({CALLEE: reader, OTHER: (0x6801, BX_LR)})
        checker = watch.Checker(rom, entries)
        checker.call(CALLEE, frozenset({5}))
        self.assertFalse([record for record in checker.premises if record[0].startswith(('read', 'bytes'))])

    def test_an_address_split_into_bits_stored_out_is_premised_at_each_store(self):
        # review-350's P14: push {r5,lr}; sub sp,#8; mov r0,sp; lsrs r2,r0,#8; ldr r1,=G;
        # str r2,[r1]; lsls r3,r0,#24; lsrs r3,#24; str r3,[r1,#4]; then the address rebuilt from
        # G (ldr r2,[r1]; lsls r2,#8; ldr r3,[r1,#4]; orrs r2,r3; movs r3,#0; str r3,[r2,#8])
        # writes the saved R5.  Each store of bits varies with the frame address: a line each.
        g = 0x02000100
        split = (0xB520, 0xB082, 0x4668, 0x0A02, 0x4906, 0x600A, 0x0603, 0x0E1B, 0x604B, 0x680A, 0x0212,
                 0x684B, 0x431A, 0x2300, 0x6093, 0xB002, 0xBD20, 0x46C0, g & 0xFFFF, g >> 16)
        rom, entries = rom_with({CALLEE: split})
        checker = watch.Checker(rom, entries)
        checker.call(CALLEE, frozenset({5}))
        self.assertEqual({record for record in checker.premises if record[0] == 'bits'},
                         {('bits', CALLEE, CALLEE + 10, '0x02000100', (0,), (8,)),
                          ('bits', CALLEE, CALLEE + 16, '0x02000104', (0,), (8,))})
        # P15b: OTHER(sp) splits it (lsrs r2,r0,#8; ldr r1,=G; str r2,[r1]; lsls r3,r0,#24;
        # lsrs r3,#24; str r3,[r1,#4]; bx lr), THIRD rebuilds it and writes: the same two lines,
        # at OTHER's stores.
        splitter = (0x0A02, 0x4902, 0x600A, 0x0603, 0x0E1B, 0x604B, BX_LR, 0x46C0, g & 0xFFFF, g >> 16)
        rebuilder = (0x4902, 0x680A, 0x0212, 0x684B, 0x431A, 0x2300, 0x6093, BX_LR, g & 0xFFFF, g >> 16)
        rom, entries = rom_with({CALLEE: (0xB520, 0xB082, 0x4668, OTHER, THIRD, 0xB002, 0xBD20),
                                 OTHER: splitter, THIRD: rebuilder})
        checker = watch.Checker(rom, entries)
        checker.call(CALLEE, frozenset({5}))
        self.assertEqual({record[:3] for record in checker.premises if record[0] == 'bits'},
                         {('bits', OTHER, OTHER + 4), ('bits', OTHER, OTHER + 10)})
        # P12d: the halves written to DMA3DAD (lsls r2,r0,#16; lsrs r2,#16; strh r2,[r1];
        # lsrs r0,#16; strh r0,[r1,#2]): the high half is the IWRAM page, the same for every
        # frame address, so only the low half gets a line.
        dma = (0xB520, 0xB082, 0x4668, 0x4904, 0x0402, 0x0C12, 0x800A, 0x0C00, 0x8048, 0xB002, 0xBD20, 0x46C0,
               0x00D8, 0x0400)
        rom, entries = rom_with({CALLEE: dma})
        checker = watch.Checker(rom, entries)
        checker.call(CALLEE, frozenset({5}))
        self.assertEqual({record[:4] for record in checker.premises if record[0] == 'bits'},
                         {('bits', CALLEE, CALLEE + 12, '0x040000D8')})

    def test_bits_of_a_frame_address_stored_out_escape_unless_they_are_the_same_for_every_frame(self):
        # push {r5,lr}; sub sp,#8; mov r0,sp; <derive into r0>; ldr r1,=0x02000000; str r0,[r1]
        # (review-350's repro_constaddr cases; R5 watched).
        def stored(*derive):
            code = (0xB520, 0xB082, 0x4668) + derive + (0x4901, 0x6008, 0xB002, 0xBD20) + \
                ((0x46C0,) if len(derive) % 2 == 0 else ()) + (0x0000, 0x0200)
            rom, entries = rom_with({CALLEE: code})
            checker = watch.Checker(rom, entries)
            checker.call(CALLEE, frozenset({5}))
            return {record[:3] + record[4:] for record in checker.premises}
        # The same value for every frame address: no line.  x != 0 (negs r1,r0; orrs r0,r1;
        # lsrs r0,#31), the IWRAM page (lsrs #24, #30, #31) and a distance (add r1,sp,#4; subs).
        for derive in ((0x4241, 0x4308, 0x0FC0), (0x0E00,), (0x0FC0,), (0x0F80,), (0xA901, 0x1A08)):
            with self.subTest(derive=derive):
                self.assertEqual(stored(*derive), set())
        # Bits that vary with it (lsrs r0,#8): a line naming the words the address reaches.
        site = CALLEE + 10
        self.assertEqual(stored(0x0A00), {('bits', CALLEE, site, (0,), (8,))})
        # Half of the address stored as a halfword (movs r1,#0x80; lsls r1,#18; strh r0,[r1]),
        # as written to a DMA address register in halves: the same.
        rom, entries = rom_with({CALLEE: (0xB520, 0xB082, 0x4668, 0x2180, 0x0489, 0x8008, 0xB002, 0xBD20)})
        checker = watch.Checker(rom, entries)
        self.assertEqual(checker.call(CALLEE, frozenset({5})), {0: watch.DEAD})
        self.assertEqual(checker.premises, {('bits', CALLEE, CALLEE + 10, '0x02000000', (0,), (8,))})

    def test_a_summary_states_its_premises_where_the_walk_in_context_does(self):
        # Every caller saves R5 and overwrites it (push {r5,lr}; movs r5,#0), so that only the
        # saved copy is live and OTHER is skipped with its summary where it has one.
        def both(functions):
            out = []
            for summaries in (True, False):
                rom, entries = rom_with(functions)
                checker = watch.Checker(rom, entries)
                if not summaries:
                    checker.isolation = lambda callee: None
                checker.call(CALLEE, frozenset({5}))
                out.append(watch.merged_premises(checker.premises))
                if summaries:
                    self.assertIsNotNone(checker.isolated.get(OTHER), 'OTHER is summarised')
            return out
        def calling(callee):        # sub sp,#8; mov r0,sp; bl callee; add sp,#8; pop {r5,pc}
            return (0xB520, 0x2500, 0xB082, 0x4668, callee, 0xB002, 0xBD20)
        # OTHER stores through its input at an unknown offset (ldr r1,[r2] first; strb r3,[r0,r1];
        # bx lr): the INDEX line names OTHER's store, with or without its summary.
        caller = (0xB520, 0x2500, 0xB082, 0x4668, 0x6811, OTHER, 0xB002, 0xBD20)
        summarised, in_context = both({CALLEE: caller, OTHER: (0x5443, BX_LR)})
        self.assertEqual(in_context, [('index', OTHER, OTHER, 'store', (8, 12))])
        self.assertIn(in_context[0], summarised)
        # A narrow load through its input of a word code not walked may have filled (ldr r3,[r2];
        # bl _call_via_r3 first) whose byte it stores out (ldrb r1,[r0]; ldr r2,=G; strb r1,[r2]):
        # READ at OTHER's load either way.
        g = 0x02000100
        filler = (0xB520, 0x2500, 0xB082, 0x4668, 0x6813, VIA_R3, 0x4668, OTHER, 0xB002, 0xBD20)
        reader = (0x7801, 0x4A01, 0x7011, BX_LR, g & 0xFFFF, g >> 16)
        summarised, in_context = both({CALLEE: filler, OTHER: reader})
        self.assertIn(('bytes', OTHER, OTHER, (0,)), in_context)
        self.assertEqual(summarised, in_context)
        # The distance between two addresses in its input's object (adds r2,r0,r1; subs r2,r2,r0;
        # ldr r3,=G; strh r2,[r3]) is a plain number with or without the summary: no line.
        distance = (0x1842, 0x1A12, 0x4B01, 0x801A, BX_LR, 0x46C0, g & 0xFFFF, g >> 16)
        summarised, in_context = both({CALLEE: caller, OTHER: distance})
        self.assertEqual(summarised, [])
        self.assertEqual(in_context, [])
        # OTHER keeps its input in one local and leaves the other unwritten (push {lr}; sub sp,#8;
        # str r0,[sp]; ldr r3,[r2]; bl _call_via_r3): code not walked, given that address, may
        # read its stack arguments there, and the word nothing wrote holds what earlier code
        # left; STALE names it, with or without the summary.
        own = (0xB500, 0xB082, 0x9000, 0x6813, VIA_R3, 0xB002, 0xBC01, 0x4700)
        summarised, in_context = both({CALLEE: calling(OTHER), OTHER: own})
        self.assertIn(('stale', OTHER, OTHER + 8, (4, 12, 16)), in_context)
        self.assertEqual(summarised, in_context)
        # OTHER hands its input to THIRD with a global (adds r1,r0,#0; ldr r0,=G; bl THIRD),
        # which stores it there (str r1,[r0]): the frame address escapes through THIRD's summary
        # inside OTHER's as it does walked; a byte of it (strb r1,[r0]) is bits of it.
        other = (0xB500, 0x1C01, 0x4802, THIRD, 0xBC01, 0x4700, 0x46C0, g & 0xFFFF, g >> 16)
        for store, kind in ((0x6001, 'escape'), (0x7001, 'bits')):
            summarised, in_context = both({CALLEE: calling(OTHER), OTHER: other, THIRD: (store, BX_LR)})
            self.assertIn(kind, [record[0] for record in in_context])
            self.assertEqual(summarised, in_context)

    def test_a_summarised_call_forgets_what_was_known_of_the_registers_it_changes(self):
        # The review's S1: R0 is 1..256 before the call, the summarised callee returns 0, and
        # the branch on it must not be decided from the old range.  push {r5,lr}; movs r5,#0;
        # ldrb r0,[r1]; adds r0,#1; bl OTHER; cmp r0,#0; bne 1f; ldr r0,[sp]; ldr r0,[r0];
        # 1: pop {r5,pc}.  OTHER: movs r0,#0; bx lr.
        body = (0xB520, 0x2500, 0x7808, 0x3001, OTHER, 0x2800, 0xD101, 0x9800, 0x6800, 0xBD20)
        self.refuses({CALLEE: body, OTHER: (0x2000, BX_LR)}, {5}, 'memory access base')
        # A pop restores what its push saved: push {r0}; movs r0,#0; pop {r0} gives back R0's range
        # 1..256, so the branch is decided and the load is not reached.
        popped = (0xB520, 0x2500, 0x7808, 0x3001, 0xB401, 0x2000, 0xBC01, 0x2800, 0xD101, 0x9800, 0x6800, 0xBD20)
        self.assertEqual(check({CALLEE: popped}, {5}), {})
        # ... unless the saved word was written meanwhile (str r0,[sp]): the branch is not decided
        # and the load through the saved R5 refuses.
        rewritten = popped[:6] + (0x9000,) + popped[6:]
        self.refuses({CALLEE: rewritten}, {5}, 'memory access base')
        # An unresolved call between them does not write a pushed word (its premise), so the pop
        # still restores the range: push {r0}; ldr r3,[r1]; bl _call_via_r3; pop {r0}.
        across = (0xB520, 0x2500, 0x7808, 0x3001, 0xB401, 0x680B, VIA_R3, 0xBC01, 0x2800, 0xD101, 0x9800, 0x6800, 0xBD20)
        rom, entries = rom_with({CALLEE: across})
        checker = watch.Checker(rom, entries)
        self.assertEqual(checker.call(CALLEE, frozenset({5})), {})
        self.assertEqual(checker.premises, {('call', CALLEE, CALLEE + 12, (3,), None, (), (4,), False)})

    def test_stale_words_below_sp_may_be_frame_addresses(self):
        # N6: a callee skipped with its summary pushes a frame address (R6) and returns; the next
        # reads it as an uninitialised local and stores through what it points at.
        # CALLEE: push {r5,r6,lr}; mov r6,sp; movs r5,#0; bl OTHER; bl THIRD; pop {r5,r6,pc}
        # OTHER: push {r6,lr}; pop {r6,pc}
        # THIRD: sub sp,#8; ldr r0,[sp]; ldr r1,[r0]; movs r2,#0; str r2,[r1]; add sp,#8; bx lr
        n6 = {CALLEE: (0xB560, 0x466E, 0x2500, OTHER, THIRD, 0xBD60), OTHER: (0xB540, 0xBD40),
              THIRD: (0xB082, 0x9800, 0x6801, 0x2200, 0x600A, 0xB002, BX_LR)}
        # OTHER's summary says what it leaves below SP (R6, CALLEE's SP), so THIRD reads exactly
        # that address, loads the saved R5 through it and stores through the copy.
        self.refuses(n6, {5}, 'memory access base')
        # A local written on one path only is stale on the other: push {r5,lr}; sub sp,#8; cmp r0,#0;
        # beq 1f; mov r1,sp; str r1,[sp,#4]; 1: ldr r2,[sp,#4]; str r3,[r2].  The address written
        # is checked as one; what earlier code left is premised at the load (UNSET_PREMISE).
        def premised(functions):
            rom, entries = rom_with(functions)
            checker = watch.Checker(rom, entries)
            checker.call(CALLEE, frozenset({5}))
            return checker.premises
        self.assertEqual(premised({CALLEE: (0xB520, 0xB082, 0x2800, 0xD001, 0x4669, 0x9101, 0x9A01, 0x6013,
                                            0xB002, 0xBD20)}), {('unset', CALLEE, CALLEE + 12, (4,))})
        # Written on that path with an address of unknown provenance (lsls r1,r1,#1 of SP): no
        # premise covers that address, so it refuses.
        self.refuses({CALLEE: (0xB520, 0xB082, 0x2800, 0xD002, 0x4669, 0x0049, 0x9101, 0x9A01, 0x6013,
                               0xB002, 0xBD20)}, {5}, 'unknown provenance')
        # N8: the checked call starts with what earlier code left below SP: sub sp,#8; ldr r0,[sp];
        # ldr r1,[r0]; movs r2,#0; str r2,[r1] is premised at the first load.
        self.assertEqual(premised({CALLEE: (0xB082, 0x9800, 0x6801, 0x2200, 0x600A, 0xB002, BX_LR)}),
                         {('unset', CALLEE, CALLEE + 2, (0,))})
        # Popped into PC (pop {r0}; bx r0 one word short) it is no return address: refused.
        self.refuses({CALLEE: (0xB500, 0xB083, 0xB002, 0xBC01, 0x4700)}, {5}, 'targets a frame address')
        # A partly overwritten local keeps the rest of what earlier code left: sub sp,#8;
        # movs r1,#0; strb r1,[sp]; ldr r0,[sp]; ldr r1,[r0] is premised at the word load.
        self.assertEqual(premised({CALLEE: (0xB082, 0x2100, 0x4668, 0x7001, 0x9800, 0x6801, 0xB002, BX_LR)}),
                         {('unset', CALLEE, CALLEE + 8, (0,))})

    def test_indexed_stores_that_may_reach_saved_words_are_premised(self):
        # N5: push {r5,lr}; sub sp,#8; ldr r2,[r1]; lsls r2,#2; mov r0,sp; str r3,[r0,r2]
        rom, entries = rom_with({CALLEE: (0xB520, 0xB082, 0x680A, 0x0092, 0x4668, 0x5083, 0xB002, 0xBD20)})
        checker = watch.Checker(rom, entries)
        checker.call(CALLEE, frozenset({5}))
        self.assertEqual(checker.premises, {('index', CALLEE, CALLEE + 10, 'store', (8, 12))})
        # N5b: only LR pushed, R5 live in its register: the return address is the excluded word.
        rom, entries = rom_with({CALLEE: (0xB500, 0xB082, 0x680A, 0x0092, 0x4668, 0x5083, 0xB002, 0xBD00)})
        checker = watch.Checker(rom, entries)
        checker.call(CALLEE, frozenset({5}))
        self.assertEqual(checker.premises, {('index', CALLEE, CALLEE + 10, 'store', (8,))})
        # N7: the same store in a callee reached while R5 is only saved in the caller's frame.
        n7 = {CALLEE: (0xB520, 0x2500, OTHER, 0xBD20),
              OTHER: (0xB500, 0xB082, 0x680A, 0x0092, 0x4668, 0x5083, 0xB002, 0xBD00)}
        rom, entries = rom_with(n7)
        checker = watch.Checker(rom, entries)
        checker.call(CALLEE, frozenset({5}))
        self.assertEqual(checker.premises, {('index', OTHER, OTHER + 10, 'store', (8, 12, 16))})

    def test_a_frame_address_stays_a_frame_address(self):
        # C1: the saved R5 reloaded through an SP-derived pointer, then stored through.
        cases = {
            'mov r0,sp; ldr r1,[r0]': (0xB520, 0x4668, 0x6801, 0x2200, 0x600A, 0xBD20),
            'add r0,sp,#0; ldr r1,[r0]': (0xB520, 0xA800, 0x6801, 0x2200, 0x600A, 0xBD20),
            'mov r0,sp; ldmia r0!,{r1}': (0xB520, 0x4668, 0xC802, 0x2200, 0x600A, 0xBD20),
            'two ldrh reassembled': (0xB520, 0x4668, 0x8801, 0x8843, 0x041B, 0x4319, 0x2200, 0x600A, 0xBD20),
            'ldr r1,[sp] (control)': (0xB520, 0x9900, 0x2200, 0x600A, 0xBD20),
        }
        for name, body in cases.items():
            with self.subTest(name):
                self.refuses({CALLEE: body}, {5})
        # The watched value itself stored there is a use (str r5,[r1]).
        self.refuses({CALLEE: (0xB520, 0x600D, 0xBD20)}, {5}, 'a store')

    def test_an_escaped_frame_address_is_premised_only_where_the_premise_can_hold(self):
        # The code that loads an escaped frame address back is not walked.  Its premise (that it
        # stays inside the object addressed) is stated only where that object holds no saved
        # register, return address, word below SP or dependent word.
        # A4: push {r5,lr}; mov r0,sp; str r0,[r1]: the saved R5's own address escapes.
        self.refuses({CALLEE: (0xB520, 0x4668, 0x6008, 0xBD20)}, {5}, 'escape')
        # push {r5,lr}; sub sp,#8; <address in r0>; movs r1,#0x80; lsls r1,#18; str r0,[r1]
        # (to 0x02000000); <tail>; add sp,#8; pop {r5,pc}.
        def body(address, *tail):
            return (0xB520, 0xB082) + address + (0x2180, 0x0489, 0x6008) + tail + (0xB002, 0xBD20)
        store = CALLEE + 4 + 2 * 3
        # ESC3: add r0,sp,#8, the saved R5's slot.  ESC4: mov r0,sp; ldr r2,[r1]; adds r0,r0,r2,
        # a stack array base plus an unknown index, which may reach the saved words.
        self.refuses({CALLEE: body((0xA802,))}, {5}, 'escape')
        self.refuses({CALLEE: body((0x4668, 0x680A, 0x1880))}, {5}, 'escape')
        # ESC1: mov r0,sp, the 8-byte local, and the global cleared before the return (movs r0,#0;
        # str r0,[r1]): premised, naming the word, the global and the dependent saved word.
        for tail, dangling in (((0x2000, 0x6008), False), ((), True)):
            rom, entries = rom_with({CALLEE: body((0x4668,), *tail)})
            class Proof:
                pass
            proof = Proof()
            proof.rom, proof.entries = rom, entries
            watch.checker_for(proof).call(CALLEE, frozenset({5}))
            lines = [f'{watch.PREMISE_PREFIX} address of the frame word at sp+0 stored to 0x02000000 at '
                     f'0x{store:08X} in 0x{CALLEE:08X}, with the frame word at sp+8 depending on owner stack '
                     f'addresses; {watch.ESCAPE_PREMISE}',
                     f'{watch.PREMISE_PREFIX} code not walked from 0x{store:08X} in 0x{CALLEE:08X} can reach the '
                     f'uninitialised, partly overwritten or unknown-provenance frame words at sp+0,sp+4; '
                     f'{watch.STALE_PREMISE}']
            if dangling:
                # ESC2: the global still holds the address when the frame is released: a fact line.
                lines.insert(0, f'{watch.FACT_PREFIX} 0x02000000 may still hold the frame address stored at '
                                f'0x{store:08X} in 0x{CALLEE:08X} when 0x{CALLEE:08X} returns at '
                                f'0x{store + 4 + 2 * len(tail):08X}, releasing that frame; {watch.DANGLING_FACT}')
            with self.subTest(dangling=dangling):
                self.assertEqual(watch.premise_lines(proof), lines)

    def test_a_nested_callee_sees_its_callers_frame(self):
        # C2: OTHER reads the saved R5 from its caller's frame ([sp,#0] above its entry SP).
        other = (0x9800, 0x2100, 0x6001, BX_LR)            # ldr r0,[sp]; movs r1,#0; str r1,[r0]
        self.refuses({CALLEE: (0xB520, OTHER, 0xBD20), OTHER: other}, {5})
        # ... also when R5 itself was overwritten first, so only the saved copy is live.
        self.refuses({CALLEE: (0xB520, 0x2500, OTHER, 0xBD20), OTHER: other}, {5})
        # agbcc -O2 (an uninitialised local in R5 passed as the 5th, stack, argument): C stores R5 at
        # [sp] and calls D (ldr r1,[sp]; strb r0,[r1]).
        fourth = 0x08014300
        c = (0xB530, 0xB081, 0x1C04, 0x2C00, 0xD102, fourth, 0x1C05, THIRD, 0x9500, 0x1C20, 0x2101, 0x2202,
             0x2303, OTHER, 0xB001, 0xBC30, 0xBC01, 0x4700)
        self.refuses({CALLEE: c, OTHER: (0x9900, 0x7008, BX_LR), THIRD: (BX_LR,), fourth: (BX_LR,)}, {5})
        # An unresolved call with the address only in the frame is premised, stating the word.
        rom, entries = rom_with({CALLEE: (0xB520, 0x2500, 0x6803, VIA_R3, 0xBD20)})
        checker = watch.Checker(rom, entries)
        self.assertEqual(checker.call(CALLEE, frozenset({5})), {})
        self.assertEqual(checker.premises, {('call', CALLEE, CALLEE + 6, (3,), None, (), (0,), False)})

    def test_flag_dependence_is_not_laundered(self):
        # M1: lsls r0,r5,#1 leaves bit 31 of R5 in C; lsls r3,r2 by an unknown amount may keep it.
        self.refuses({CALLEE: (0xB520, 0x680A, 0x0068, 0x2000, 0x4093, 0xD2FF, 0xBD20)}, {5}, 'conditional branch')
        self.refuses({CALLEE: (0xB520, 0x680A, 0x0068, 0x2000, 0x4093, 0x4140, 0x6008, 0xBD20)}, {5}, 'carry')
        # A call to a leaf that leaves the flags as they were (movs r5,#0; bl THIRD; bcs).
        self.refuses({CALLEE: (0xB520, 0x0068, 0x2000, 0x2500, THIRD, 0xD2FF, 0xBD20), THIRD: (BX_LR,)},
                     {5}, 'conditional branch')

    def test_flags_survive_what_does_not_write_them(self):
        # The review's F1-F5 and M1c: push {r5,lr}; lsls r0,r5,#1 (C = R5 bit 31); movs r0,#0;
        # <between>; bcs; pop {r5,pc}.
        pre, post = (0xB520, 0x0068, 0x2000), (0xD2FF, 0xBD20)
        laundering = {
            'tst r1,r1 sets only N and Z': (0x4209,),
            'svc: the BIOS returns the caller its flags': (0xDF05,),
            'rors by a known 0 leaves C': (0x2200, 0x41D1),
            'lsls by an unknown amount may leave C': (0x681A, 0x4091),
            'lsls by a known 0 leaves C': (0x2200, 0x4091),
            'a skipped call leaves them': (0x2500, OTHER),
        }
        for name, between in laundering.items():
            with self.subTest(name), self.assertRaisesRegex(watch.WatchRefusal, 'conditional branch'):
                check({CALLEE: pre + between + post, OTHER: (BX_LR,)}, {5})
        self.assertEqual(check({CALLEE: pre + (0x4289,) + post}, {5}), {})      # cmp r1,r1 sets C
        # F4: a nested callee branches on the flags it was called with.
        with self.assertRaisesRegex(watch.WatchRefusal, f'callee 0x{OTHER:08X}: a conditional branch'):
            check({CALLEE: pre + (OTHER, 0xBD20), OTHER: (0xD2FF, BX_LR)}, {5})
        # F5: flags handed back with no register copy still walk the caller's code after the call
        # (OTHER: bl CALLEE; bcs; bx lr).
        rom, entries = rom_with({CALLEE: (0x0068, 0x2000, BX_LR), OTHER: (CALLEE, 0xD2FF, BX_LR)})
        checker = watch.Checker(rom, entries)
        self.assertEqual(checker.call(CALLEE, frozenset({5})), {})
        self.assertIn('C', next(iter(checker.results.values()))[1])
        with self.assertRaisesRegex(watch.WatchRefusal, f'callee 0x{OTHER:08X}: a conditional branch'):
            watch.Checker(rom, entries).call(CALLEE, frozenset({5}), caller=OTHER, site=OTHER)

    def test_a_call_returns_unless_its_callee_provably_does_not(self):
        # M2: a lone BL prefix after a call is executable ARMv4T code, not data.
        self.refuses({CALLEE: (0xB520, THIRD, 0xF000, 0x6028, 0xBD20), THIRD: (BX_LR,)}, {5},
                     'not an ARMv4T Thumb instruction')
        self.refuses({CALLEE: (0xB520, THIRD, 0x46C0, 0x6028, 0xBD20), THIRD: (BX_LR,)}, {5})
        # A callee that never returns (b .) may be followed by data.
        self.assertEqual(check({CALLEE: (0xB520, THIRD, 0xF000, 0x6028, 0xBD20), THIRD: (0xE7FE,)}, {5}), {})

    def test_mutual_recursion_is_not_summarised_provisionally(self):
        # M3: A calls B while R5 is live, B calls A back, A hands back R0 = R5, B stores through R0.
        self.refuses({CALLEE: (0xB500, 0x2900, 0xD001, OTHER, 0x1C28, 0xBD00),
                      OTHER: (0xB500, CALLEE, 0x2100, 0x6001, 0xBD00)}, {5}, 'nested too deeply|uses a watched')
        self.refuses({OTHER: (0xB500, 0x2900, 0xD001, 0x46C0, 0x46C0, 0x1C28, 0xBD00),
                      CALLEE: (0xB500, OTHER, 0x2100, 0x6001, 0xBD00)}, {5})

    def test_a_watched_register_must_be_returned_unchanged(self):
        # M4: movs r5,#0; bx lr, and R5 restored from R4's save slot.
        self.refuses({CALLEE: (0x2500, BX_LR)}, {5}, 'R5 does not hold its value')
        self.refuses({CALLEE: (0xB530, 0xBC20, 0xBC10, 0xBD00)}, {5}, 'R5 does not hold its value')
        # A merge into R7 without saving it: bits 0-7 replaced.
        self.refuses({CALLEE: (0x4C01, 0x4027, 0x4307, BX_LR, 0xFF00, 0xFFFF)}, {7}, 'R7 does not hold its value')
        self.assertEqual(check({CALLEE: (0xB580, 0x2700, 0xBD80)}, {7}), {})

    def test_owner_reproducers(self):
        # C1/C2/M2 end to end, under both stack-index selectors (ranged R7) and the core (exact R7).
        h1a = (0xB580, 0x4668, 0x6801, 0x2200, 0x600A, 0x2000, 0xBD80)
        h2a = {CALLEE: (0xB580, OTHER, 0xBD80), OTHER: (0x9800, 0x2100, 0x6201, BX_LR)}
        h3 = {CALLEE: (0xB580, 0x2700, OTHER, 0xBD80), OTHER: (0x9800, 0x2100, 0x6201, BX_LR)}
        h5 = {CALLEE: (0xB580, THIRD, 0xF000, 0x2000, 0x6238, 0xBD80), THIRD: (BX_LR,)}
        for selector in sip.SELECTORS:
            for name, callee in {'h1a': h1a, 'h2a': h2a, 'h3': h3, 'h5': h5}.items():
                with self.subTest(selector=selector, case=name), \
                        self.assertRaisesRegex(ValueError, 'uses a watched callee-saved|not an ARMv4T'):
                    verify(RANGED_R7 + (0x2000, CALLEE), callee, selector)
        for name, callee in {'h2a': h2a, 'h3': h3, 'h5': h5}.items():
            with self.subTest(case=f'exact {name}'), \
                    self.assertRaisesRegex(ValueError, 'uses a watched callee-saved|not an ARMv4T'):
                verify(EXACT + (CALLEE,), callee)
        # The callee overwrites the owner's saved LR through the reloaded R7 (exact).
        with self.assertRaisesRegex(ValueError, 'uses a watched callee-saved'):
            verify(EXACT + (CALLEE,), (0xB580, 0x4668, 0x6801, 0x2200, 0x620A, 0x2000, 0xBD80))
        # The handed-back copy spilled by the owner and reloaded through add r1,sp,#8.
        with self.assertRaisesRegex(ValueError, 'uses a watched callee-saved'):
            verify(EXACT + (CALLEE, 0x9002, 0xA902, 0x6809, 0x2200, 0x620A), (0x1C38, BX_LR))
        # A callee that does not preserve the owner's R7, which the owner then reads as its buffer.
        with self.assertRaisesRegex(ValueError, 'R7 does not hold its value'):
            verify(EXACT + (CALLEE, 0x7838), (0x2700, BX_LR))
        manifest, _ = verify(EXACT + (CALLEE, 0x7838), (0xB580, 0x2700, 0xBD80))
        self.assertEqual(manifest['profile'], sip.SCHEMA)


class SummaryTests(unittest.TestCase):
    """Callees reached while only a saved copy is live are skipped with a summary of their
    accesses through their inputs, unless an access reaches something that matters."""

    # push {r5,lr}; movs r5,#0; sub sp,#8; movs r1,#0; str r1,[sp]; <r0>; bl OTHER; ldr r1,[sp];
    # movs r2,#0; str r2,[r1]; add sp,#8; pop {r5,pc}: the saved R5 is at sp+8 while OTHER runs,
    # R0 the given value.
    def body(self, r0=0x4668):                                    # mov r0,sp
        return (0xB520, 0x2500, 0xB082, 0x2100, 0x9100, r0, OTHER, 0x9900, 0x2200, 0x600A, 0xB002, 0xBD20)

    def test_a_callee_writing_a_passed_buffer_is_skipped(self):
        # OTHER: movs r1,#0; str r1,[r0]; bx lr.  R0, the buffer address OTHER returns, is left.
        rom, entries = rom_with({CALLEE: self.body(), OTHER: (0x2100, 0x6001, BX_LR)})
        checker = watch.Checker(rom, entries)
        self.assertEqual(checker.call(CALLEE, frozenset({5})), {0: watch.DEAD})
        self.assertIsNotNone(checker.isolation(OTHER))

    def test_an_access_that_reaches_a_saved_word_is_walked(self):
        # ldr r1,[r0,#8] reads the saved R5: walked, and the store through it refuses.
        with self.assertRaisesRegex(watch.WatchRefusal, f'callee 0x{OTHER:08X}: a memory access base'):
            check({CALLEE: self.body(), OTHER: (0x6881, 0x2200, 0x600A, BX_LR)}, {5})
        # str r1,[r0,#8] overwrites it: walked, and R5 is not restored.
        with self.assertRaisesRegex(watch.WatchRefusal, 'R5 does not hold its value'):
            check({CALLEE: self.body(), OTHER: (0x2100, 0x6081, BX_LR)}, {5})

    def test_an_input_stored_to_memory_is_walked_where_it_is_a_frame_address(self):
        # OTHER: ldr r3,=0x03001000; str r0,[r3]; bx lr.
        other = (0x4B01, 0x6018, BX_LR, 0x46C0, 0x1000, 0x0300)
        rom, entries = rom_with({CALLEE: self.body(), OTHER: other})
        checker = watch.Checker(rom, entries)
        checker.call(CALLEE, frozenset({5}))
        # Walked there; code that loads the address back may store it in the buffer, so the
        # caller's store through the word it then reads is premised as an indexed store.
        # The buffer's second word was never written: what an address built from it may be is
        # premised at the same site.
        # The global still holds the address when CALLEE releases its frame: a fact.
        self.assertEqual(checker.premises, {('escape', OTHER, OTHER + 2, '0x03001000', (0,), (8,)),
                                            ('dangling', OTHER, OTHER + 2, '0x03001000', CALLEE, CALLEE + 24),
                                            ('index', CALLEE, CALLEE + 20, 'store', (8, 12)),
                                            ('stale', OTHER, OTHER + 2, (4,))})
        self.assertEqual(check({CALLEE: self.body(0x2000), OTHER: other}, {5}), {})   # movs r0,#0

    def test_an_unresolved_call_inside_a_summary_is_premised_at_its_own_sp(self):
        # OTHER: push {lr}; ldr r3,[r1]; bl _call_via_r3; pop {pc}: the saved R5 is 12 bytes above
        # the SP at that call, and the buffer R0 passes is not that word.
        rom, entries = rom_with({CALLEE: self.body(), OTHER: (0xB500, 0x680B, VIA_R3, 0xBD00)})
        checker = watch.Checker(rom, entries)
        # The unwalked code may hand the buffer address back (in R0-R3, R12, or stored in the
        # buffer): left in registers, it is a frame address the caller may not use, and a store
        # through the word read back is premised.
        self.assertEqual(checker.call(CALLEE, frozenset({5})), dict.fromkeys((0, 1, 3, 12), watch.DEAD))
        # The word OTHER leaves below SP (its saved LR, perhaps an address the unwalked code hands
        # back) is excluded too, as the walk in context excludes it.
        self.assertEqual(checker.premises, {('call', OTHER, OTHER + 4, (3,), None, (), (12,), False),
                                            ('index', CALLEE, CALLEE + 20, 'store', (-4, 8, 12)),
                                            ('stale', OTHER, OTHER + 4, (8,))})
        # Passing the saved word's own address (add r0,sp,#8) is walked, and refuses there.
        with self.assertRaisesRegex(watch.WatchRefusal, 'address of a frame word'):
            check({CALLEE: self.body(0xA802), OTHER: (0xB500, 0x680B, VIA_R3, 0xBD00)}, {5})

    def test_a_callee_reading_a_stale_word_is_walked(self):
        # push {r5,lr}; push {r5}; add sp,#4 (a stale copy of R5 below SP); movs r5,#0; bl OTHER;
        # pop {r5,pc}.  OTHER: sub sp,#4; ldr r0,[sp] (its uninitialised local: that copy);
        # movs r1,#0; str r1,[r0]; add sp,#4; bx lr.
        with self.assertRaisesRegex(watch.WatchRefusal, f'callee 0x{OTHER:08X}: a memory access base'):
            check({CALLEE: (0xB520, 0xB420, 0xB001, 0x2500, OTHER, 0xBD20),
                   OTHER: (0xB081, 0x9800, 0x2100, 0x6001, 0xB001, BX_LR)}, {5})

    def test_a_recursive_summary_reaches_its_fixpoint(self):
        # OTHER(a, b): if (b) OTHER(b, 0); else *a = 0.  Its store through b only appears once
        # the recursive call's summary includes the store through a.  CALLEE passes b = the
        # address of its saved R5 (push {r5,lr}; movs r5,#0; movs r0,#0; add r1,sp,#0; bl OTHER).
        other = (0xB500, 0x2900, 0xD004, 0x1C08, 0x2100, OTHER, 0xE001, 0x2200, 0x6002, 0xBD00)
        rom, entries = rom_with({CALLEE: (0xB520, 0x2500, 0x2000, 0xA900, OTHER, 0xBD20), OTHER: other})
        checker = watch.Checker(rom, entries)
        self.assertIn(('store', 1, 0, 4), checker.isolation(OTHER)[0])
        with self.assertRaisesRegex(watch.WatchRefusal, 'R5 does not hold its value'):
            checker.call(CALLEE, frozenset({5}))

    def test_a_site_at_every_recursion_depth_names_the_recursion_and_what_it_covers(self):
        # OTHER(n): if (n) { OTHER(n - 1); (*r3)(); } (push {lr}; cmp r0,#0; beq out; subs r0,#1;
        # bl OTHER; bl _call_via_r3; out: pop {r0}; bx r0), from CALLEE with its saved R5 the
        # word above OTHER's entry.  The unresolved call runs at every depth, a frame apart.
        import test_callee_saved_summaries as agreement
        other = (0xB500, 0x2800, 0xD004, 0x3801, OTHER, VIA_R3, 0xBC01, 0x4700)
        rom, entries = rom_with({CALLEE: (0xB520, 0x2500, OTHER, 0xBD20), OTHER: other})

        def walk(induction):
            checker = watch.Checker(rom, entries)
            if induction:                                # only the recursive call summarised
                checker.summarised = lambda callee, chain: callee in chain
            checker.trace = []
            checker.premises = agreement.TracedPremises(checker)
            checker.call(CALLEE, frozenset({5}))
            return checker
        summarised, induction = walk(False), walk(True)
        proof = type('Proof', (), {})()                  # a buffer proof's stand-in
        watch._CHECKERS[proof] = summarised
        line, = watch.premise_lines(proof)
        self.assertIn(f'call at 0x{OTHER + 12:08X} in 0x{OTHER:08X} at every recursion depth of 0x{OTHER:08X} '
                      f'(a frame of 4 bytes) through _call_via_r3', line)
        self.assertIn('with the frame word at sp+4 depending on owner stack addresses', line)
        self.assertTrue(line.endswith(
            "; the claim covers the frame words named, at offsets from the SP of the site's shallowest "
            f"execution, and every word of the stack between the SP of each execution and the entry of "
            f"0x{OTHER:08X} (the callee whose summary states this site), not only the words a walk reached"))
        # Unrolled one level, the walk names the saved R5 from the deeper SP: the same address.
        self.assertIn(('call+', OTHER, OTHER + 12, (3,), None, (), (8,), False), induction.premises)
        for record in watch.merged_premises(induction.premises):
            self.assertEqual(agreement.region_missing(record, induction.trace, summarised.trace), [])
        # A STALE line, which names no depth of its own, gains it after its function.
        stale = watch.recursion_text(f'* code not walked from 0x{OTHER + 12:08X} in 0x{OTHER:08X} can reach the '
                                     f'frame word at sp+4; premise', (OTHER, OTHER + 12), {OTHER}, {OTHER}, {OTHER: -4})
        self.assertTrue(stale.startswith(f'* code not walked from 0x{OTHER + 12:08X} in 0x{OTHER:08X} at every '
                                         f'recursion depth of 0x{OTHER:08X} (a frame of 4 bytes) can reach'), stale)
        # The trace is the test's alone: without it the walk states the same premises.
        plain = watch.Checker(rom, entries)
        plain.call(CALLEE, frozenset({5}))
        self.assertEqual(plain.premises, set(summarised.premises))
        self.assertEqual(watch.premise_lines(proof), [line])

    def test_a_site_inside_two_nested_recursions_names_both(self):
        # OTHER(n): if (n) { OTHER(n - 1); THIRD(...); }  THIRD(n): if (n) { THIRD(n - 1); (*r3)(); }
        # (each push {lr}; cmp r0,#0; beq out; subs r0,#1; bl self; bl next; out: pop {r0}; bx r0).
        # The unresolved call runs at every depth of both; the claim is bounded by the entry of
        # OTHER, the callee whose summary states the site.
        import test_callee_saved_summaries as agreement
        rom, entries = rom_with({CALLEE: (0xB520, 0x2500, OTHER, 0xBD20),
                                 OTHER: (0xB500, 0x2800, 0xD004, 0x3801, OTHER, THIRD, 0xBC01, 0x4700),
                                 THIRD: (0xB500, 0x2800, 0xD004, 0x3801, THIRD, VIA_R3, 0xBC01, 0x4700)})

        def walk(induction):
            checker = watch.Checker(rom, entries)
            if induction:
                checker.summarised = lambda callee, chain: callee in chain
            checker.trace = []
            checker.premises = agreement.TracedPremises(checker)
            checker.call(CALLEE, frozenset({5}))
            return checker
        summarised, induction = walk(False), walk(True)
        proof = type('Proof', (), {})()
        watch._CHECKERS[proof] = summarised
        line, = watch.premise_lines(proof)
        self.assertIn(f'call at 0x{THIRD + 12:08X} in 0x{THIRD:08X} at every recursion depth of 0x{OTHER:08X} '
                      f'(a frame of 4 bytes) and of 0x{THIRD:08X} (a frame of 4 bytes) through', line)
        self.assertIn(f'and the entry of 0x{OTHER:08X} (the callee whose summary states this site)', line)
        for record in watch.merged_premises(induction.premises):
            self.assertEqual(agreement.region_missing(record, induction.trace, summarised.trace), [])

    def test_a_frame_word_handed_to_unwalked_code_keeps_what_it_addresses_reachable(self):
        # OTHER(r0 = &CALLEE's array) keeps r0 in its own local and hands &local to unresolved
        # code, which can find the array through it and write a frame address there.  CALLEE then
        # uses array[0].  With summaries the verdict, lines and copies are the walk in context's.
        # OTHER: push {lr}; sub sp,#8; [ldr r3,=G; ldr r3,[r3]; cmp r3,#0; beq 1f;] str r0,[sp,#4];
        # 1: add r0,sp,#4; ldr r3,=G; ldr r3,[r3]; bl _call_via_r3; add sp,#8; pop {pc}.
        # CALLEE: push {r5,lr}; movs r5,#0; sub sp,#8; movs r2,#0; str r2,[sp]; str r2,[sp,#4];
        # mov r0,sp; bl OTHER; ldr r0,[sp]; <use>; add sp,#8; pop {r5,pc}.
        g = 0x02000100
        every = (0xB500, 0xB082, 0x9001, 0xA801, 0x4B02, 0x681B, VIA_R3, 0xB002, 0xBD00, g & 0xFFFF, g >> 16)
        one_path = (0xB500, 0xB082, 0x4B05, 0x681B, 0x2B00, 0xD000, 0x9001, 0xA801, 0x4B02, 0x681B, VIA_R3,
                    0xB002, 0xBD00, g & 0xFFFF, g >> 16)
        # Or OTHER leaves r0 in its outgoing stack argument and hands over no frame address at all:
        # str r0,[sp]; movs r0,#0; ldr r3,=G; ldr r3,[r3]; bl _call_via_r3.
        argument = (0xB500, 0xB082, 0x9000, 0x2000, 0x4B02, 0x681B, VIA_R3, 0xB002, 0xBD00, g & 0xFFFF, g >> 16)
        head = (0xB520, 0x2500, 0xB082, 0x2200, 0x9200, 0x9201, 0x4668, OTHER, 0x9800)
        uses = {
            'array[0] stored to a global': (0x4901, 0x6008, 0xB002, 0xBD20, g & 0xFFFF, g >> 16),
            'a store through array[0]': (0x2200, 0x6002, 0xB002, 0xBD20),
            'array[0] handed back in R0': (0xB002, 0xBD20),
        }

        def outcome(functions, summaries):
            rom, entries = rom_with(functions)
            checker = watch.Checker(rom, entries)
            if not summaries:
                checker.isolation = lambda callee: None
            try:
                copies = checker.call(CALLEE, frozenset({5}))
            except watch.WatchRefusal as error:
                return 'refused', str(error)
            if summaries:
                self.assertIsNotNone(checker.isolated.get(OTHER), 'OTHER is summarised')
            return copies, sorted(checker.premises)
        for name, use in uses.items():
            for shape, other in (('every path', every), ('one path', one_path), ('stack argument', argument)):
                with self.subTest(use=name, local=shape):
                    functions = {CALLEE: head + use, OTHER: other}
                    in_context = outcome(functions, False)
                    self.assertEqual(outcome(functions, True), in_context)
                    if name == 'array[0] stored to a global' and shape != 'stack argument':
                        self.assertEqual(in_context[0], 'refused')
                        self.assertIn('lets a frame address escape', in_context[1])
                    elif name == 'array[0] handed back in R0':
                        self.assertEqual(in_context[0].get(0), watch.DEAD)

    def test_a_summary_names_a_frame_word_one_path_wrote(self):
        # OTHER writes its local on one path only, then stores through its input at an unknown
        # index (push {lr}; sub sp,#8; cmp r3,#0; beq 1f; str r3,[sp]; 1: strb r3,[r0,r1];
        # add sp,#8; pop {pc}).  The local holds what OTHER stored or what earlier code left, so
        # the INDEX line names it (sp+0) with summaries as in context.
        other = (0xB500, 0xB082, 0x2B00, 0xD000, 0x9300, 0x5443, 0xB002, 0xBD00)
        functions = {CALLEE: (0xB520, 0x2500, 0xB082, 0x4668, 0x6811, OTHER, 0xB002, 0xBD20), OTHER: other}
        found = []
        for summaries in (True, False):
            rom, entries = rom_with(functions)
            checker = watch.Checker(rom, entries)
            if not summaries:
                checker.isolation = lambda callee: None
            checker.call(CALLEE, frozenset({5}))
            found.append([record for record in checker.premises if record[1] == OTHER])
        self.assertEqual(found[0], found[1])
        self.assertEqual(found[1], [('index', OTHER, OTHER + 10, 'store', (0, 8, 20, 24))])

    def test_a_callee_that_reads_back_a_word_one_path_wrote_is_walked_in_context(self):
        # OTHER writes its local on one path only and reads it back (push {lr}; sub sp,#4;
        # mov r1,sp; cmp r1,#0; beq 1f; str r2,[r1]; 1: ldr r0,[sp]; add sp,#4; pop {pc}).  On the
        # other path the word holds what earlier code left there: the walk in context knows it
        # (here plain data THIRD left: push {lr}; sub sp,#4; movs r0,#0; str r0,[sp]; add sp,#4;
        # pop {pc}), a summary would not.  So OTHER has no summary, and the verdict, the lines and
        # the copies are the walk in context's; so too where a second branch joins before the load
        # (2: cmp r3,#0; beq 2f; movs r3,#1; 2: ldr r0,[sp]), and where unresolved code, which may
        # write the local (its stack argument) but need not, runs before it (movs r1,#0; ldr r3,=G;
        # ldr r3,[r3]; bl _call_via_r3; ldr r0,[sp]).  CALLEE: push {r5,lr}; movs r5,#0;
        # [bl THIRD;] movs r2,#0; bl OTHER; <use>.
        g = 0x02000100
        shapes = {
            'one branch': ((0xB500, 0xB081, 0x4669, 0x2900, 0xD000, 0x600A, 0x9800, 0xB001, 0xBD00), 12),
            'a second branch': ((0xB500, 0xB081, 0x4669, 0x2900, 0xD000, 0x600A, 0x2B00, 0xD000, 0x2301,
                                 0x9800, 0xB001, 0xBD00), 18),
            'unresolved code': ((0xB500, 0xB081, 0x4669, 0x2900, 0xD000, 0x600A, 0x2100, 0x4B03, 0x681B, VIA_R3,
                                 0x9800, 0xB001, 0xBD00, g & 0xFFFF, g >> 16), 22),
        }
        third = (0xB500, 0xB081, 0x2000, 0x9000, 0xB001, 0xBD00)
        uses = {
            'a load through it': (0x6800, 0xBD20),                                     # ldr r0,[r0]
            'stored to a global': (0x4901, 0x6008, 0xBD20, 0x46C0, g & 0xFFFF, g >> 16),  # str r0,[G]
        }
        for (name, use), (shape, (other, load)), before in itertools.product(
                uses.items(), shapes.items(), ('plain data', 'nothing')):
            with self.subTest(use=name, other=shape, left=before):
                head = (0xB520, 0x2500) + ((THIRD,) if before == 'plain data' else ()) + (0x2200, OTHER)
                functions = {CALLEE: head + use, OTHER: other, THIRD: third}
                found = []
                for summaries in (True, False):
                    rom, entries = rom_with(functions)
                    checker = watch.Checker(rom, entries)
                    if not summaries:
                        checker.isolation = lambda callee: None
                    found.append((checker.call(CALLEE, frozenset({5})), sorted(checker.premises)))
                self.assertEqual(found[0], found[1])
                unset = [record for record in found[1][1] if record[0] == 'unset']
                self.assertEqual(unset, [] if before == 'plain data' else [('unset', OTHER, OTHER + load, (0,))])
                rom, entries = rom_with(functions)
                self.assertIsNone(watch.Checker(rom, entries).isolation(OTHER))

    def test_a_word_one_path_wrote_and_every_path_rewrote_is_read_from_the_summary(self):
        # As above, but OTHER stores its local again on every path before it reads it (str r2,
        # [sp] after the join): the word holds what OTHER stored, so OTHER has a summary.
        other = (0xB500, 0xB081, 0x4669, 0x2900, 0xD000, 0x600A, 0x9200, 0x9800, 0xB001, 0xBD00)
        rom, entries = rom_with({CALLEE: (0xB520, 0x2500, 0x2200, OTHER, 0x6800, 0xBD20), OTHER: other})
        self.assertIsNotNone(watch.Checker(rom, entries).isolation(OTHER))

    def test_a_premise_stated_inside_a_summarised_callee_is_traced_at_its_own_sp(self):
        # CALLEE: push {r5,lr}; movs r5,#0; sub sp,#8; mov r0,sp; bl OTHER (given its unwritten
        # locals); OTHER: push {lr}; bl _call_via_r3.  The STALE line is stated where the summary is
        # applied, from the SP at OTHER's unresolved call (-20), not the walk's SP at the BL (-16):
        # CALLEE's locals at -16 and -12 are sp+4 and sp+8 there.
        import test_callee_saved_summaries as agreement
        rom, entries = rom_with({CALLEE: (0xB520, 0x2500, 0xB082, 0x4668, OTHER, 0xB002, 0xBD20),
                                 OTHER: (0xB500, VIA_R3, 0xBD00)})
        checker = watch.Checker(rom, entries)
        checker.trace = []
        checker.premises = agreement.TracedPremises(checker)
        checker.call(CALLEE, frozenset({5}))
        self.assertIsNotNone(checker.isolated.get(OTHER))
        stale = ('stale', OTHER, OTHER + 2, (4, 8))
        self.assertIn((stale, -20, ((CALLEE, 0), (OTHER, -16))), checker.trace)

    def test_the_owner_frame_starts_at_the_entry_sp(self):
        # str r5,[sp]; bx lr: the callee's first stack-argument word is the owner's.
        with self.assertRaisesRegex(watch.WatchRefusal, "writes the owner's frame"):
            check({CALLEE: (0x9500, BX_LR)}, {5})

    def test_a_store_above_the_entry_sp_refuses_whatever_it_writes(self):
        # The owner's frame starts at the checked callee's entry SP. No callee writes it, plain
        # data included, as the core's walk refuses the same store: str r3,[sp,#4] and
        # str r3,[sp,#40] with no push; the same behind push {lr}; and a byte store through
        # sp + an index read as a byte, which may reach it.
        for code in ((0x9301, BX_LR), (0x930A, BX_LR), (0xB500, 0x930A, 0xBC01, 0x4700),
                     (0xB082, 0xA900, 0x7802, 0x548B, 0xB002, BX_LR)):
            with self.subTest(code=code):
                with self.assertRaisesRegex(watch.WatchRefusal, "writes the owner's frame above the checked"):
                    check({CALLEE: code}, {4})
        # A stack argument the callee reads and writes back (agbcc's p += 4 on a fifth argument:
        # push {lr}; ldr r2,[sp,#4]; adds r2,#4; str r2,[sp,#4]; pop {r0}; bx r0) is premised.
        rom, entries = rom_with({CALLEE: (0xB500, 0x9A01, 0x3204, 0x9201, 0xBC01, 0x4700)})
        checker = watch.Checker(rom, entries)
        self.assertEqual(checker.call(CALLEE, frozenset({4})), {})
        self.assertEqual(checker.premises, {('args', CALLEE, CALLEE + 6, (0,))})
        # Not when it writes a frame address there (mov r2,sp; str r2,[sp,#4]) or the watched value.
        for code in ((0xB500, 0x9A01, 0x466A, 0x9201, 0xBC01, 0x4700), (0xB500, 0x9A01, 0x9401, 0xBC01, 0x4700)):
            with self.subTest(code=code):
                with self.assertRaisesRegex(watch.WatchRefusal, "writes the owner's frame above the checked"):
                    check({CALLEE: code}, {4})
        # A nested callee writing its caller's frame stays inside the walked frames: push {lr};
        # sub sp,#4; bl OTHER; add sp,#4; pop {r0}; bx r0, with OTHER: movs r3,#0; str r3,[sp]; bx lr.
        rom, entries = rom_with({CALLEE: (0xB500, 0xB081, OTHER, 0xB001, 0xBC01, 0x4700),
                                 OTHER: (0x2300, 0x9300, BX_LR)})
        self.assertEqual(watch.Checker(rom, entries).call(CALLEE, frozenset({4})), {})


FOURTH, NESTED = 0x08014300, 0x08014400
G = 0x02000100


def function(address, items, words=()):
    """Thumb code at ``address`` from ``items``: halfwords, BL targets (>= 0x08000000), or
    ('LIT', reg, n) for ``ldr reg, =words[n]``, with the literal pool after the code."""
    total = sum(4 if isinstance(item, int) and item >= 0x08000000 else 2 for item in items)
    pool = total + total % 4
    out, off = [], 0
    for item in items:
        if isinstance(item, tuple):
            _, reg, index = item
            out.append(0x4800 | reg << 8 | (address + pool + 4 * index - ((address + off + 4) & ~3)) // 4)
        else:
            out.append(item)
        off += 4 if isinstance(item, int) and item >= 0x08000000 else 2
    out += [0x46C0] * (total % 4 // 2)
    for word in words:
        out += [word & 0xFFFF, word >> 16]
    return tuple(out)


# Words of a summarised callee's frame that a path may not have written, read back through every
# alias the walk tracks.  CALLEE: push {r5,lr}; bl THIRD; movs r5,#0; r0 = *G; bl OTHER; [bl FOURTH;]
# pop {r5,pc}, with R5 watched.  THIRD (push {r5,lr}; pop {r5,pc}) is walked in context, R5 being
# live, and leaves R5's value at -16, which is OTHER's sp+4 (OTHER: push {lr}; sub sp,#8).  In
# context a read of that word on a path that has not written it finds R5's value, and a compare or
# a dereference of it refuses.
P, E = [0xB500, 0xB082], [0xB002, 0xBD00]            # push {lr}; sub sp,#8 / add sp,#8; pop {pc}
ONE = [0x2200, 0x2800, 0xD000, 0x9201]               # movs r2,#0; cmp r0,#0; beq +0; str r2,[sp,#4]
CMP = [0x9B01, 0x2B00]                               # ldr r3,[sp,#4]; cmp r3,#0
DEREF = [0x9B01, 0x2200, 0x601A]                     # ldr r3,[sp,#4]; movs r2,#0; str r2,[r3]
FWIDX = [('LIT', 1, 0), 0x6809, 0x466B]              # r1 = *G (an unknown index); mov r3,sp
SOME = [0x4669, 0x2800, 0xD000, 0xA901, 0x2200, 0x600A]  # r1 = sp or sp+4; movs r2,#0; str r2,[r1]
NARROW = [0xA901, 0x2200, 0x800A]                    # add r1,sp,#4; movs r2,#0; strh r2,[r1]
CALLV = [0x4668, ('LIT', 3, 0), 0x681B, VIA_R3]      # mov r0,sp; r3 = *G; bl _call_via_r3
NESTED_ONE_PATH = (0x2900, 0xD000, 0x6001, 0x4770)   # cmp r1,#0; beq +0; str r1,[r0]; bx lr
THIRD2 = (0xB560, 0xBD60)                            # push {r5,r6,lr}: R5's value at -20


def earlier_content_cases():
    """(name, OTHER's items, {address: code} of other functions, CALLEE's items after OTHER, THIRD
    or None, whether the walk in context admits)."""
    cases = []

    def case(name, other, extra=None, after=(), third=None, admits=False):
        cases.append((name, other, extra or {}, after, third, admits))
    for use_name, use in (('cmp', CMP), ('deref', DEREF)):
        case(f'X0 one-path write, exact read-back, {use_name}', P + ONE + use + E)
        case(f'X0n never written, exact read, {use_name}', P + use + E)
        case(f'X1 one-path write, indexed plain store, read-back, {use_name}', P + ONE + FWIDX + [0x2200, 0x505A] + use + E)
        case(f'X1n never written, indexed plain store, read, {use_name}', P + FWIDX + [0x2200, 0x505A] + use + E)
        case(f'X2 one-path write, store through one of two addresses, read-back, {use_name}', P + ONE + SOME + use + E)
        case(f'X2n never written, store through one of two addresses, read, {use_name}', P + SOME + use + E)
        case(f'X3 one-path write, strh low half, word read-back, {use_name}', P + ONE + NARROW + use + E)
        case(f'X3n never written, strh low half, word read, {use_name}', P + NARROW + use + E)
        case(f'X5 one-path write, nested summary stores on one path, read-back, {use_name}',
             P + ONE + [0x1C01, 0xA801, NESTED] + use + E, {NESTED: NESTED_ONE_PATH})
        case(f'X5n never written, nested summary stores on one path, read, {use_name}',
             P + [0x1C01, 0xA801, NESTED] + use + E, {NESTED: NESTED_ONE_PATH})
        case(f'X6 trivial summarised OTHER, then FOURTH reads its unwritten sp+4, {use_name}',
             [0xB500, 0xBD00], {FOURTH: tuple(P + use + E)}, after=(FOURTH,))
        case(f'X11 never written, unresolved code given &sp+0, then sp+4 read, {use_name}', P + CALLV + use + E)
        case(f'X11o one-path write, unresolved code given &sp+0, then sp+4 read, {use_name}',
             P + ONE + CALLV + use + E)
    case('X0b one-path write, read-back through mov r1,sp; ldr r3,[r1,#4]; cmp',
         P + ONE + [0x4669, 0x684B, 0x2B00] + E)
    case('X3h one-path write, strh low half, ldrh upper half, cmp', P + ONE + NARROW + [0x884B, 0x2B00] + E)
    case('X3hn never written, strh low half, ldrh upper half, cmp', P + NARROW + [0x884B, 0x2B00] + E)
    case('X4 sp+0 written, sp+4 one-path, indexed load, cmp',
         P + [0x2200, 0x9200] + ONE + FWIDX + [0x585B, 0x2B00] + E)
    case('X4n sp+0 written, sp+4 never written, indexed load, cmp', P + [0x2200, 0x9200] + FWIDX + [0x585B, 0x2B00] + E)
    case('X7 sp+0 written, sp+4 one-path, ldmia r1!,{r2,r3} from sp, cmp r3',
         P + [0x2200, 0x9200] + ONE + [0x4669, 0xC90C, 0x2B00] + E)
    case('X8 push {r0} on one path, sub sp,#4 on the other, pop {r3}, cmp',
         [0xB500, 0x2800, 0xD001, 0xB401, 0xE000, 0xB081, 0xBC08, 0x2B00, 0xBD00])
    case('X9 one-path write, nested callee loads it through r0 and compares',
         P + ONE + [0xA801, NESTED] + E, {NESTED: (0x6803, 0x2B00, 0x4770)})
    case('X9n never written, nested callee loads it through r0 and compares',
         P + [0xA801, NESTED] + E, {NESTED: (0x6803, 0x2B00, 0x4770)})
    case('X9b never written, a nested summary loads a byte of it through r0 and compares',
         P + [0xA801, NESTED] + E, {NESTED: (0x7803, 0x2B00, 0x4770)})
    # OTHER (push {lr}; sub sp,#4) writes its outgoing stack argument, sp+0 = -16, on one path; a
    # summarised NESTED (ldr r3,[sp]; cmp r3,#0; bx lr) reads it as its stack argument.
    case('X12 one-path write of the outgoing stack argument, a nested summary reads it, cmp',
         [0xB500, 0xB081, 0x2200, 0x2800, 0xD000, 0x9200, NESTED, 0xB001, 0xBD00], {NESTED: (0x9B00, 0x2B00, 0x4770)})
    case('X9i one-path write, nested callee walked inside the probe loads it and compares',
         P + ONE + [0x2101, 0xA801, NESTED] + E, {NESTED: (0x2900, 0xD000, 0x46C0, 0x6803, 0x2B00, 0x4770)})
    # A summarised NESTED writes its own local on one path (or one of two returns, or every path) and
    # returns; OTHER then reads that word as its own unwritten local.
    for use_name, use in (('cmp', [0x9B00, 0x2B00]), ('deref', [0x9B00, 0x2200, 0x601A])):
        case(f'X10 summarised NESTED writes its local on one path; OTHER reads that word, {use_name}',
             [0xB500, NESTED, 0xB082] + use + E,
             {NESTED: (0xB500, 0xB082, 0x2800, 0xD000, 0x9001, 0xB002, 0xBD00)}, third=THIRD2)
        case(f'X10m summarised NESTED writes its local on one of two returns; OTHER reads it, {use_name}',
             [0xB500, NESTED, 0xB082] + use + E,
             {NESTED: (0xB500, 0xB082, 0x2800, 0xD002, 0x9001, 0xB002, 0xBD00, 0xB002, 0xBD00)}, third=THIRD2)
        case(f'X10c NESTED writes its local on every path; OTHER reads it, {use_name}',
             [0xB500, NESTED, 0xB082] + use + E, {NESTED: (0xB500, 0xB082, 0x9001, 0xB002, 0xBD00)},
             third=THIRD2, admits=True)
    return cases


# Round 6 of the review: a store that may hit the callee's input or something else (its own
# local, or a global), and earlier content that is a frame address (THIRD3/THIRD4 leave F(-8), the
# address of CALLEE's saved R5, at -16 or -20).
NEST_MIXED = (0xB500, 0xB082, 0x466A, 0x2900, 0xD000, 0x1C02, 0x2300)   # r2 = own sp, or r0 if r1
THIRD3 = (0xB500, 0xB082, 0xA803, 0x9001, 0xB002, 0xBD00)               # leaves F(-8) at -16
THIRD4 = (0xB500, 0xB082, 0xA803, 0x9000, 0xB002, 0xBD00)               # leaves F(-8) at -20
THIRD6 = (0xB500, 0xB083, 0xB420, 0xBC20, 0xB003, 0xBD00)               # leaves R5's value at -28
THIRD7 = (0xB500, 0xB082, 0x2000, 0x9001, 0xB002, 0xBD00)               # leaves 0 at -16
THIRD8 = (0xB500, 0xB084, 0x2000, 0x9001, 0xB004, 0xBD00)               # leaves 0 at -24
THIRD9 = (0xB500, 0xB084, 0xA805, 0x9001, 0xB004, 0xBD00)               # leaves F(-8) at -24
ESC = [0x9B01, ('LIT', 1, 0), 0x600B]                                     # ldr r3,[sp,#4]; str r3,[G]
FIFTH, SIXTH = 0x08014500, 0x08014600


def round6_cases():
    """As ``earlier_content_cases``, and whether the walk in context refuses because a watched value
    is used (else for another reason: the saved R5 overwritten, or a frame address escaping)."""
    cases = []

    def case(name, other, extra=None, after=(), third=None, admits=False, watched=True):
        cases.append((name, other, extra or {}, after, third, admits, watched))
    case('X13 NESTED stores a word to its input or its own local; OTHER reads sp+4, cmp',
         P + [0x1C01, 0xA801, NESTED] + CMP + E, {NESTED: NEST_MIXED + (0x6013, 0xB002, 0xBD00)})
    case('X13d the same, deref', P + [0x1C01, 0xA801, NESTED] + DEREF + E,
         {NESTED: NEST_MIXED + (0x6013, 0xB002, 0xBD00)})
    case('X13b NESTED strb to its input or its own local; OTHER ldrb sp+4, cmp',
         P + [0x1C01, 0xA801, NESTED, 0xA901, 0x780B, 0x2B00] + E, {NESTED: NEST_MIXED + (0x7013, 0xB002, 0xBD00)})
    case('X13c NESTED stores to its input on every path; OTHER reads sp+4, cmp',
         P + [0x1C01, 0xA801, NESTED] + CMP + E, {NESTED: (0xB500, 0xB082, 0x1C02, 0x2300, 0x6013, 0xB002, 0xBD00)},
         admits=True)
    case('X13g NESTED stores a word to its input or a global; OTHER reads sp+4, cmp',
         P + [0x1C01, 0xA801, NESTED] + CMP + E,
         {NESTED: function(NESTED, [('LIT', 2, 0), 0x2900, 0xD000, 0x1C02, 0x2300, 0x6013, 0x4770], [G])})
    case('X6f trivial summarised OTHER, then FOURTH derefs its unwritten sp+4 (F(-8) there)',
         [0xB500, 0xBD00], {FOURTH: tuple(P + DEREF + E)}, after=(FOURTH,), third=THIRD3, watched=False)
    case('X6fe trivial summarised OTHER, then FOURTH stores its unwritten sp+4 (F(-8)) to a global',
         [0xB500, 0xBD00], {FOURTH: function(FOURTH, P + ESC + E, [G])}, after=(FOURTH,), third=THIRD3,
         watched=False)
    case('X6fc OTHER itself derefs its unwritten sp+4 (F(-8) there)', P + DEREF + E, third=THIRD3, watched=False)
    case('X10f summarised NESTED writes its local on one path; OTHER derefs that word (F(-8) there)',
         [0xB500, NESTED, 0xB082, 0x9B00, 0x2200, 0x601A] + E,
         {NESTED: (0xB500, 0xB082, 0x2800, 0xD000, 0x9001, 0xB002, 0xBD00)}, third=THIRD4, watched=False)
    case('X2f a store through one of two addresses, then deref sp+4 (F(-8) there)', P + SOME + DEREF + E,
         third=THIRD3, watched=False)
    case('X4f sp+0 written, indexed load (sp+4 holds F(-8)), deref',
         P + [0x2200, 0x9200] + FWIDX + [0x585B, 0x2200, 0x601A] + E, third=THIRD3, watched=False)
    # X6p: the X6f shape inside OTHER's probe.  OTHER pushes R5 and LR; NESTED leaves the address of
    # OTHER's saved R5 in a word below OTHER's SP; a trivial summarised callee runs; FOURTH loads that
    # word at an unknown index and lets it escape, or stores through it (lines only: OTHER's R5 is 0).
    t3 = (0xB500, 0xB082, 0xA805, 0x9001, 0xB002, 0xBD00)
    trivial = {NESTED: t3, FIFTH: (0xB500, 0xBD00)}
    case('X6p in OTHER: its saved R5\'s address left below SP, a summarised callee, an indexed load escapes it',
         [0xB520, 0xB082, NESTED, FIFTH, FOURTH, 0xB002, 0xBD20],
         {**trivial, FOURTH: function(FOURTH, P + [0x2200, 0x9200] + FWIDX + [0x585B] + ESC[1:] + E, [G])},
         watched=False)
    case('X6pd the same, stored through',
         [0xB520, 0xB082, NESTED, FIFTH, FOURTH, 0xB002, 0xBD20],
         {**trivial, FOURTH: function(FOURTH, P + [0x2200, 0x9200] + FWIDX + [0x585B, 0x2200, 0x601A] + E, [G])},
         admits=True)
    # A summarised callee that makes an unresolved call (itself, or in a callee) may leave anything
    # below SP: a plain number THIRD7 left there may be stale afterwards (X6fs, X6fn), as in the walk
    # in context; the frame address THIRD3 left is kept (X6fu: stricter than the walk in context,
    # which forgets it at the unresolved call's SP).
    unresolved = [0xB500, ('LIT', 3, 0), 0x681B, VIA_R3, 0xBD00]
    case('X6fs a summarised callee makes an unresolved call; FOURTH derefs the number left there',
         unresolved, {FOURTH: tuple(P + DEREF + E)}, after=(FOURTH,), third=THIRD7, admits=True)
    case('X6fn the same, the unresolved call in a summarised callee of OTHER',
         [0xB500, NESTED, 0xBD00], {NESTED: function(NESTED, unresolved, [G]), FOURTH: tuple(P + DEREF + E)},
         after=(FOURTH,), third=THIRD7, admits=True)
    case('X6fu a summarised callee makes an unresolved call; FOURTH derefs F(-8) left there',
         unresolved, {FOURTH: tuple(P + DEREF + E)}, after=(FOURTH,), third=THIRD3, admits=True)
    # Words above the unresolved call's SP that nothing writes keep what they held, as in the walk:
    # OTHER's own local, above NESTED's unresolved call (X6fk2, X6fk3); inside OTHER's probe, FIFTH's local
    # above its callee's unresolved call (X6pk2); and a word deeper down that only the unresolved
    # call, in a summarised callee of OTHER, may write is stale (X6fn2).
    nested_unresolved = function(NESTED, [0xB500] + unresolved[1:4] + [0xBD00], [G])
    case('X6fk2 OTHER\'s local holds F(-8); NESTED (in OTHER) makes an unresolved call; FOURTH derefs it',
         P + [NESTED] + E, {NESTED: nested_unresolved, FOURTH: tuple(P + DEREF + E)}, after=(FOURTH,),
         third=THIRD3, watched=False)
    case('X6fk3 OTHER\'s local holds the number THIRD7 left; NESTED (in OTHER) makes an unresolved call; FOURTH derefs it',
         P + [NESTED] + E, {NESTED: nested_unresolved, FOURTH: tuple(P + DEREF + E)}, after=(FOURTH,),
         third=THIRD7, admits=True)
    # Unwalked code on one path only: below its SP the walk keeps what the word held on the other
    # path, so the summary keeps it too, beside what that code may leave (X6fj; X6pj inside OTHER's
    # probe).
    one_path = [0xB500, 0x2800, 0xD001, SIXTH, 0xBD00]           # push {lr}; cmp r0,#0; beq; bl SIXTH; pop
    case('X6fj F(-8) left deep below SP; OTHER makes an unresolved call on one path; FOURTH derefs it',
         one_path, {SIXTH: function(SIXTH, [0xB500] + unresolved[1:4] + [0xBD00], [G]),
                    FOURTH: tuple([0xB500, 0xB084] + DEREF + [0xB004, 0xBD00])},
         after=(FOURTH,), third=THIRD9, watched=False)
    case('X6pj in OTHER: its saved R5\'s address deep below SP, FIFTH calls unresolved code on one path, escapes',
         [0xB520, 0xB082, NESTED, FIFTH, FOURTH, 0xB002, 0xBD20],
         {NESTED: (0xB500, 0xB084, 0xA807, 0x9001, 0xB004, 0xBD00), FIFTH: function(FIFTH, one_path),
          SIXTH: function(SIXTH, [0xB500] + unresolved[1:4] + [0xBD00], [G]),
          FOURTH: function(FOURTH, [0xB500, 0xB084, 0x2200, 0x9200] + FWIDX + [0x585B] + ESC[1:] + [0xB004, 0xBD00], [G])},
         third=(0xB500, 0xBD00), watched=False)
    case('X6pk2 in OTHER: its saved R5\'s address below SP, in FIFTH\'s local over an unresolved call, escapes',
         [0xB520, 0xB082, NESTED, FIFTH, FOURTH, 0xB002, 0xBD20],
         {NESTED: t3, FIFTH: function(FIFTH, P + [SIXTH] + E), SIXTH: function(SIXTH, [0xB500] + unresolved[1:4] + [0xBD00], [G]),
          FOURTH: function(FOURTH, P + [0x2200, 0x9200] + FWIDX + [0x585B] + ESC[1:] + E, [G])},
         third=(0xB500, 0xBD00), watched=False)
    case('X6fn2 an unresolved call in NESTED (in OTHER) above a word THIRD8 set to 0; FOURTH derefs it',
         [0xB500, NESTED, 0xBD00], {NESTED: nested_unresolved, FOURTH: tuple([0xB500, 0xB084] + DEREF + [0xB004, 0xBD00])},
         after=(FOURTH,), third=THIRD8, admits=True)
    case('X15 summarised OTHER makes an unresolved call; FOURTH compares its unwritten sp+4',
         [0xB500, ('LIT', 3, 0), 0x681B, VIA_R3, 0xBD00], {FOURTH: tuple(P + CMP + E)}, after=(FOURTH,))
    # OTHER recurses to an unknown depth, loading its own frame at an unknown index each level, with
    # R5's value left below its first frame (-28): refused (deeper than the walk in context goes).
    for use_name, use in (('deref', [0x2200, 0x601A]), ('stored', [('LIT', 2, 0), 0x6013]), ('compared', [0x2B00])):
        case(f'X14 recursion, indexed load, {use_name}; R5 value below the first frame',
             P + [0x2200, 0x9200] + FWIDX + [0x585B] + use + [0x2800, 0xD002, 0x3801, OTHER] + E,
             third=THIRD6, watched=False)
    return cases


def outcome(functions, summaries, watched=frozenset({5})):
    """(copies, premises) of CALLEE's check, or ('refused', text); ``summaries`` False walks every
    callee in context, "induction" only the recursive calls with summaries (as the gate does)."""
    rom, entries = rom_with(functions)
    checker = watch.Checker(rom, entries)
    if summaries == 'induction':
        checker.summarised = lambda callee, chain: callee in chain
    elif not summaries:
        checker.isolation = lambda callee: None
    try:
        return checker.call(CALLEE, watched), sorted(checker.premises)
    except watch.WatchRefusal as error:
        return 'refused', str(error)


class EarlierContentTests(unittest.TestCase):
    """What earlier walked code left in the words a summarised callee uses as its frame (kit #350)."""

    def test_a_summary_never_admits_what_earlier_content_makes_the_walk_in_context_refuse(self):
        # The 42 shapes of the round-5 review (and X9b, X12): a word one path wrote, or none did, then overwritten
        # in part, perhaps, or not at all (an indexed store, a store through one of two addresses, a
        # halfword store, a nested summary's store on one path, unresolved code given its address, a
        # nested summary's local written on one path), and read back (exactly, through an alias, by
        # an indexed load, by LDM or POP, by a nested callee).  In context each refuses but the
        # controls X10c; with summaries each refuses too, or agrees with the walk in context.
        for name, other, extra, after, third, admits in earlier_content_cases():
            with self.subTest(name):
                callee = function(CALLEE, [0xB520, THIRD, 0x2500, ('LIT', 0, 0), 0x6800, OTHER] + list(after) +
                                  [0xBD20], [G])
                functions = {CALLEE: callee, THIRD: third or (0xB520, 0xBD20), OTHER: function(OTHER, other, [G])}
                functions.update(extra)
                in_context = outcome(functions, False)
                if admits:
                    self.assertNotEqual(in_context[0], 'refused')
                else:
                    self.assertEqual(in_context[0], 'refused')
                    self.assertIn("uses a watched callee-saved register's value", in_context[1])
                with_summaries = outcome(functions, True)
                if with_summaries[0] != 'refused':
                    self.assertEqual(with_summaries, in_context)

    def test_a_recursive_summary_states_the_words_its_first_level_leaves(self):
        # OTHER recurses to an unknown depth, each level keeping its own frame address in its local;
        # after it returns, FOURTH reads that word uninitialised and lets it escape, or stores through
        # it.  The walk in context cannot follow the recursion, so the reference is the walk by
        # induction.  The summary states the words the first level leaves, so it gives that walk's
        # verdict, lines and copies, over nothing, a number or R5's value left there before.
        rec = [0xB500, 0xB082, 0xA900, 0x9101, 0x2800, 0xD002, 0x3801, OTHER, 0xB002, 0xBD00]
        for third_name, third in (('nothing', (0xB500, 0xBD00)), ('a number', THIRD7), ('R5', None)):
            for use_name, use in (('escape', ESC), ('deref', DEREF)):
                with self.subTest(third=third_name, use=use_name):
                    callee = function(CALLEE, [0xB520, THIRD, 0x2500, ('LIT', 0, 0), 0x6800, OTHER, FOURTH, 0xBD20], [G])
                    functions = {CALLEE: callee, THIRD: third or (0xB520, 0xBD20), OTHER: function(OTHER, rec, [G]),
                                 FOURTH: function(FOURTH, P + use + E, [G])}
                    by_induction = outcome(functions, 'induction')
                    self.assertNotEqual(by_induction[0], 'refused')
                    self.assertEqual(outcome(functions, True), by_induction)
        # A word the first level wrote below its recursive call's SP holds what the deeper levels
        # leave there: stale.
        rec = [0xB500, 0xB082, 0xA900, 0xB082, 0x9101, 0xB002, 0x2800, 0xD002, 0x3801, OTHER, 0xB002, 0xBD00]
        rom, entries = rom_with({OTHER: function(OTHER, rec, [G])})
        summary = watch.Checker(rom, entries).isolation(OTHER)
        self.assertIsNotNone(summary)
        self.assertEqual(summary[6], 0)                # its deeper levels: anywhere below its entry SP
        left = dict(summary[4])
        self.assertIn(('F', -12), left[-16])           # below the recursive call's SP
        self.assertTrue(left[-16] & watch.STALE)

    def test_a_store_that_may_miss_the_input_or_a_frame_address_left_below_sp_is_kept(self):
        # Round 6 of the review.  A store whose address may be the input or something else (the
        # callee's own local, X13, or a global, X13g) does not surely write the input, so the
        # caller's word keeps what it held; a summarised callee keeps the frame address earlier code
        # left below SP where it does not surely write the word (X6f, X6fe, X10f).  In context each
        # refuses but the control X13c; with summaries each refuses too, or agrees.
        for name, other, extra, after, third, admits, watched in round6_cases():
            with self.subTest(name):
                callee = function(CALLEE, [0xB520, THIRD, 0x2500, ('LIT', 0, 0), 0x6800, OTHER] + list(after) +
                                  [0xBD20], [G])
                functions = {CALLEE: callee, THIRD: third or (0xB520, 0xBD20), OTHER: function(OTHER, other, [G])}
                functions.update(extra)
                in_context = outcome(functions, False)
                if admits:
                    self.assertNotEqual(in_context[0], 'refused')
                else:
                    self.assertEqual(in_context[0], 'refused')
                    if watched:
                        self.assertIn("uses a watched callee-saved register's value", in_context[1])
                with_summaries = outcome(functions, True)
                if with_summaries[0] != 'refused':
                    self.assertEqual(with_summaries, in_context)


    def checked(self, callee, functions, summaries=True):
        rom, entries = rom_with({CALLEE: function(CALLEE, callee, [G]), **functions})
        checker = watch.Checker(rom, entries)
        if not summaries:
            checker.isolation = lambda target: None
        try:
            return checker, (checker.call(CALLEE, frozenset({5})), sorted(checker.premises))
        except watch.WatchRefusal as error:
            return checker, ('refused', str(error))

    def test_a_summary_that_reads_an_unwritten_element_is_used_where_the_word_holds_no_more_than_stale(self):
        # OTHER writes sp+0 and loads its frame at an unknown index (X4n's OTHER), so it may read
        # sp+4, which no path wrote: its summary records that read ("early").  Where the walk has
        # nothing there, or plain data (THIRD: push {r4,lr}; pop {r4,pc}), the summary applies; where
        # it has a frame address (THIRD: push {lr}; mov r1,sp; push {r1}; add sp,#4; movs r1,#0;
        # pop {pc}) or R5's value, OTHER is walked in context.  Every time the outcome is the walk in
        # context's.
        # The word or a byte of it is compared, or stored to a global (ldr r2,=G; str r3,[r2] or
        # strb r3,[r2]), where the walk in context refuses a frame address, or bits of one, that
        # reaches a word below SP.
        lefts = {'nothing': None, 'plain data': (0xB510, 0xBD10),
                 'a frame address': (0xB500, 0x4669, 0xB402, 0xB001, 0x2100, 0xBD00), "R5's value": (0xB520, 0xBD20)}
        loads = {'word': (0x585B, 4, 0x6013), 'byte': (0x5C5B, 1, 0x7013)}      # ldr / ldrb r3,[r3,r1]
        for (left, third), (width, (load, size, store)), use in itertools.product(
                lefts.items(), loads.items(), ('compared', 'stored')):
            with self.subTest(left=left, load=width, use=use):
                tail = [0x2B00] if use == 'compared' else [('LIT', 2, 0), store]
                other = function(OTHER, P + [0x2200, 0x9200] + FWIDX + [load] + tail + E, [G])
                callee = ([THIRD] if third else []) + [0x2500, ('LIT', 0, 0), 0x6800, OTHER, 0xBD20]
                functions = {OTHER: other, **({THIRD: third} if third else {})}
                checker, found = self.checked([0xB520] + callee, functions)
                if width == 'byte' and use == 'stored':        # bits of its own frame's words, stored:
                    self.assertIsNone(checker.isolated[OTHER])  # walked where they are used
                else:
                    self.assertIn(('early', 'sp', -8, size), checker.isolated[OTHER][0])
                in_context = self.checked([0xB520] + callee, functions, summaries=False)[1]
                self.assertEqual(found[0] == 'refused', in_context[0] == 'refused')
                if left in ("R5's value", 'plain data'):
                    self.assertEqual(found[0] == 'refused', left == "R5's value")
                if found[0] != 'refused':
                    # Over plain data the summary reads what earlier code may leave there, so it may
                    # hand back a copy, or state a line, that the walk in context does not; never fewer.
                    self.assertLessEqual(in_context[0].items(), found[0].items())
                    self.assertLessEqual(set(in_context[1]), set(found[1]))
                    if left != 'plain data':
                        self.assertEqual(found, in_context)

    def test_bytes_a_nested_summary_reads_early_are_walked_where_they_are_part_of_an_address(self):
        # OTHER: push {lr}; sub sp,#8; add r0,sp,#4; bl NESTED, where NESTED (ldrb r3,[r0];
        # ldr r2,=G; strb r3,[r2]; bx lr) copies a byte of OTHER's unwritten sp+4 to a global.
        # Over plain data THIRD left there (push {r4,lr}; pop {r4,pc}) the summary applies; over a
        # frame address (push {lr}; mov r1,sp; push {r1}; add sp,#4; movs r1,#0; pop {pc}) those
        # bytes are bits of it, which escape: refused, as in context.
        nested = function(NESTED, [0x7803, ('LIT', 2, 0), 0x7013, 0x4770], [G])
        for left, third in (('plain data', (0xB510, 0xBD10)),
                            ('a frame address', (0xB500, 0x4669, 0xB402, 0xB001, 0x2100, 0xBD00))):
            with self.subTest(left=left):
                functions = {THIRD: third, NESTED: nested, OTHER: tuple(P + [0xA801, NESTED] + E)}
                callee = [0xB520, THIRD, 0x2500, ('LIT', 0, 0), 0x6800, OTHER, 0xBD20]
                checker, found = self.checked(callee, functions)
                self.assertIn(('early', 'sp', -8, 1), checker.isolated[OTHER][0])
                self.assertEqual(found, self.checked(callee, functions, summaries=False)[1])
                self.assertEqual(found[0] == 'refused', left == 'a frame address')

    def test_a_recursion_reads_earlier_content_anywhere_below_its_sp(self):
        # OTHER: push {lr}; sub sp,#8; mov r1,sp; r2 = *G; ldrb r3,[r1,r2]; cmp r3,#0; beq 1f;
        # bl OTHER; 1: add sp,#8; pop {pc}.  Each level reads bytes of its own unwritten frame, so
        # the recursion reads earlier content anywhere below its entry SP: its summary reaches a
        # fixpoint by reading "below" the frame of the first level.  Where nothing is left there it
        # applies; where THIRD (push {lr}; sub sp,#16; push {r5}; pop {r5}; add sp,#16; pop {pc})
        # left R5's value below OTHER's frame, a deeper level reads it: refused.
        other = function(OTHER, [0xB500, 0xB082, 0x4669, ('LIT', 2, 0), 0x6812, 0x5C8B, 0x2B00, 0xD001, OTHER,
                                 0xB002, 0xBD00], [G])
        third = (0xB500, 0xB084, 0xB420, 0xBC20, 0xB004, 0xBD00)
        for deep in (False, True):
            with self.subTest(deep=deep):
                callee = [0xB520] + ([THIRD] if deep else []) + [0x2500, OTHER, 0xBD20]
                checker, found = self.checked(callee, {OTHER: other, THIRD: third})
                self.assertIn(('early', 'sp', ('below', -12), 1), checker.isolated[OTHER][0])
                if deep:
                    self.assertEqual(found[0], 'refused')
                    self.assertIn("uses a watched callee-saved register's value", found[1])
                else:
                    self.assertNotEqual(found[0], 'refused')

    def test_code_that_is_not_walked_leaves_a_watched_value_below_sp(self):
        # THIRD (walked, R5 live) leaves R5's value at -16; unresolved code or a SWI runs; FOURTH
        # (push {lr}; sub sp,#8; ldr r3,[sp,#4]) reads it as its unwritten local.  That code need
        # not overwrite the word (the call's premise says it does not), so the compare refuses.
        fourth = tuple(P + CMP + E)
        for name, unwalked in (('an unresolved call', [('LIT', 3, 0), 0x681B, VIA_R3]), ('a SWI', [0xDF06])):
            for summaries in (True, False):
                with self.subTest(name, summaries=summaries):
                    found = self.checked([0xB520, THIRD, 0x2500] + unwalked + [FOURTH, 0xBD20],
                                         {THIRD: (0xB520, 0xBD20), FOURTH: fourth}, summaries)[1]
                    self.assertEqual(found[0], 'refused')
                    self.assertIn("a comparison at 0x08014306 uses a watched callee-saved register's value", found[1])

    def test_a_word_a_summarised_callee_wrote_on_one_path_keeps_the_watched_value(self):
        # OTHER (summarised: R5 is dead at its call) writes its local over the -16 that THIRD left
        # R5's value in, on one path only (push {lr}; sub sp,#8; movs r2,#0; cmp r0,#0; beq +0;
        # str r2,[sp,#4]; add sp,#8; pop {pc}); FOURTH then reads that word.  On the other path it
        # holds R5's value: refused with summaries as in context.
        functions = {THIRD: (0xB520, 0xBD20), OTHER: tuple(P + ONE + E), FOURTH: tuple(P + CMP + E)}
        callee = [0xB520, THIRD, 0x2500, ('LIT', 0, 0), 0x6800, OTHER, FOURTH, 0xBD20]
        checker, found = self.checked(callee, functions)
        self.assertIsNotNone(checker.isolated[OTHER])
        self.assertEqual(found[0], 'refused')
        self.assertEqual(found, self.checked(callee, functions, summaries=False)[1])

    def test_a_nested_summary_reading_the_half_a_narrow_store_wrote_reads_no_earlier_content(self):
        # OTHER: push {lr}; sub sp,#8; add r1,sp,#4; movs r2,#0; strh r2,[r1]; adds r0,r1,#0;
        # bl NESTED (ldrh r3,[r0] or ldrh r3,[r0,#2]; cmp r3,#0; bx lr).  Over R5's value left in
        # that word, the half OTHER wrote is no earlier content: OTHER is summarised with no early
        # read and admitted, as in context (stating a READ line the walk in context does not: the
        # probe keeps the word's rest as what earlier code left); the other half is an early read,
        # where R5's bits refuse.
        for name, load, admits in (('the half written', 0x8803, True), ('the other half', 0x8843, False)):
            with self.subTest(name):
                functions = {THIRD: (0xB520, 0xBD20), NESTED: (load, 0x2B00, 0x4770),
                             OTHER: tuple(P + NARROW + [0x1C08, NESTED] + E)}
                callee = [0xB520, THIRD, 0x2500, ('LIT', 0, 0), 0x6800, OTHER, 0xBD20]
                checker, found = self.checked(callee, functions)
                in_context = self.checked(callee, functions, summaries=False)[1]
                self.assertEqual(found[0], in_context[0])
                if admits:
                    self.assertLessEqual(set(in_context[1]), set(found[1]))
                self.assertEqual(found[0] != 'refused', admits)
                self.assertEqual(any(access[0] == 'early' for access in checker.isolated[OTHER][0]), not admits)

    def test_a_byte_a_nested_summary_surely_writes_is_read_from_the_summary(self):
        # OTHER: push {lr}; sub sp,#4; mov r1,sp; bl NESTED; mov r0,sp; ldrb r0,[r0,#n]; cmp r0,#0;
        # add sp,#4; pop {pc}, where NESTED (movs r0,#0; strb r0,[r1]; bx lr) writes byte 0 of
        # OTHER's local on every path.  Over R5's value left there, byte 0 is NESTED's: OTHER is
        # summarised and admitted, as in context; byte 1 is still R5's: refused.
        for byte, admits in ((0, True), (1, False)):
            with self.subTest(byte=byte):
                functions = {THIRD: (0xB520, 0xBD20), NESTED: (0x2000, 0x7008, 0x4770),
                             OTHER: (0xB500, 0xB081, 0x4669, NESTED, 0x4668, 0x7800 | byte << 6, 0x2800, 0xB001, 0xBD00)}
                callee = [0xB520, THIRD, 0x2500, ('LIT', 0, 0), 0x6800, OTHER, 0xBD20]
                checker, found = self.checked(callee, functions)
                self.assertEqual(found, self.checked(callee, functions, summaries=False)[1])
                self.assertEqual(found[0] != 'refused', admits)
                self.assertEqual(checker.isolated[OTHER] is not None, admits)

    def test_a_narrow_store_clears_the_mark_of_the_bytes_it_writes_only(self):
        # OTHER: push {lr}; sub sp,#8; add r1,sp,#4; movs r2,#0; strh r2,[r1]; then ldrh r3,[r1]
        # (the half it wrote) or ldrh r3,[r1,#2] (the half it did not); cmp r3,#0.  Over R5's value
        # left there, the first is summarised and admitted, as in context; the second refuses.
        for name, load, admits in (('the half written', 0x880B, True), ('the other half', 0x884B, False)):
            with self.subTest(name):
                functions = {THIRD: (0xB520, 0xBD20), OTHER: tuple(P + NARROW + [load, 0x2B00] + E)}
                callee = [0xB520, THIRD, 0x2500, ('LIT', 0, 0), 0x6800, OTHER, 0xBD20]
                checker, found = self.checked(callee, functions)
                self.assertEqual(found, self.checked(callee, functions, summaries=False)[1])
                self.assertEqual(found[0] != 'refused', admits)
                self.assertEqual(checker.isolated[OTHER] is not None, admits)


class ReplayWithoutBufferProofTests(unittest.TestCase):
    """M5: linked reports replay through verify_leaf_instructions without a buffer proof; a
    callee_saved_watch.Context repeats the check issuance made, and its premise lines."""

    def walk(self, callee):
        owner_at = 0x08013000
        # push {r7,lr}; mov r7,sp; movs r0,#0; bl CALLEE; pop {r7}; pop {r1}; bx r1
        code = (0xB580, 0x466F, 0x2000, CALLEE, 0xBC80, 0xBC02, 0x4708)
        rom, entries = rom_with({owner_at: code, CALLEE: callee})
        data = assemble(owner_at, code)
        context = watch.Context(rom, entries)
        match.verify_leaf_instructions(data, owner_at, True, call_resolver=lambda target: None,
                                       callee_watch=context)
        return context

    def test_the_check_runs_and_records_premises_without_a_buffer_proof(self):
        with self.assertRaisesRegex(watch.WatchRefusal, 'uses a watched callee-saved'):
            self.walk((0x6039, BX_LR))                            # str r1,[r7]
        self.assertEqual(watch.premise_lines(self.walk((BX_LR,))), [])
        context = self.walk((0xB500, 0x6803, VIA_R3, 0xBD00))   # ldr r3,[r0]; bl _call_via_r3
        self.assertEqual(len(watch.premise_lines(context)), 1)
        self.assertIn('with R7 depending on owner stack addresses', watch.premise_lines(context)[0])



# A bare `bx r3` (kit #350 follow-up): MPlayMain at 0x08144B2C ends with `bx r3` at 0x08144D84,
# which six callers BL to as a call through R3.  The function index gives that halfword its own
# row inside MPlayMain's span.  PLAYER is that shape: a body whose ninth halfword is bx r3, with
# a one-instruction row at it.
PLAYER = 0x08014400
BARE = PLAYER + 0x10
PLAYER_BODY = (0xB500, 0x2000, 0x2100, 0x2200, 0x2300, 0x2000, 0x2100, 0x2200, 0x4718, 0x46C0)


def bare_rom(callee, bare_halfword=0x4718, extra=None):
    body = PLAYER_BODY[:8] + (bare_halfword,) + PLAYER_BODY[9:]
    functions = {PLAYER: body, BARE: (bare_halfword,), CALLEE: callee}
    functions.update(extra or {})
    return rom_with(functions)


class BareThunkTests(unittest.TestCase):
    """A BL to an aligned Thumb halfword that is exactly `bx r3` is a call through R3."""

    def lines(self, callee, watched=frozenset({5}), **options):
        rom, entries = bare_rom(callee, **options)
        class Proof:
            pass
        proof = Proof()
        proof.rom, proof.entries = rom, entries
        copies = watch.checker_for(proof).call(CALLEE, frozenset(watched))
        return copies, watch.premise_lines(proof)

    def test_a_call_to_a_bare_bx_r3_is_premised_whatever_span_it_sits_in(self):
        # push {lr}; bl BARE; pop {pc}, with R5 watched: R3 is unknown, so the call is premised.
        copies, lines = self.lines((0xB500, BARE, 0xBD00))
        self.assertEqual(copies, {})
        self.assertEqual(lines, [
            f'{watch.PREMISE_PREFIX} call at 0x{CALLEE + 2:08X} in 0x{CALLEE:08X} through the bx r3 at '
            f'0x{BARE:08X} to an unknown address, with R5 depending on owner stack addresses; {watch.PREMISE}'])

    def test_a_bare_bx_r3_is_walked_at_a_known_destination(self):
        # ldr r3,=OTHER|1; bl BARE: OTHER (cmp r5,#0; bx lr) is walked, and compares R5.
        callee = function(CALLEE, [0xB500, ('LIT', 3, 0), BARE, 0xBD00], [OTHER | 1])
        with self.assertRaisesRegex(watch.WatchRefusal, f"callee 0x{OTHER:08X}: a comparison"):
            self.lines(callee, extra={OTHER: (0x2D00, BX_LR)})
        self.assertEqual(self.lines(callee, extra={OTHER: (BX_LR,)}), ({}, []))
        # Through _call_via_r2 to the bare bx r3 (r2 = BARE|1), and on to an unknown R3.
        callee = function(CALLEE, [0xB500, ('LIT', 2, 0), VIA_R2, 0xBD00], [BARE | 1])
        _, lines = self.lines(callee)
        self.assertEqual(len(lines), 1)
        self.assertIn(f'through _call_via_r2 then the bx r3 at 0x{BARE:08X} to an unknown address', lines[0])

    def test_a_bare_bx_r3_may_not_branch_to_a_watched_value(self):
        # adds r3,r5,#0; bl BARE
        with self.assertRaisesRegex(watch.WatchRefusal, 'the call-via thunk branches to the watched R3'):
            self.lines((0xB500, 0x1C2B, BARE, 0xBD00))

    def test_anything_else_in_an_overlapping_span_still_refuses(self):
        # The same row and span holding bx r2, or a BL to the halfword after the bx r3.
        with self.assertRaisesRegex(watch.WatchRefusal, 'mapping overlaps another span'):
            self.lines((0xB500, BARE, 0xBD00), bare_halfword=0x4710)
        with self.assertRaisesRegex(watch.WatchRefusal, 'mapping overlaps another span'):
            self.lines((0xB500, BARE + 2, 0xBD00), extra={BARE + 2: (0x46C0,)})

    def test_a_bare_bx_r3_at_an_odd_address_or_reached_as_arm_code_refuses(self):
        # ODD's bytes 00 18 47 00 read bx r3 at its odd address ODD + 1, which is no Thumb instruction.
        odd = 0x08014500
        rom, entries = bare_rom((0xB500, BARE, 0xBD00), extra={odd: (0x1800, 0x0047)})
        checker = watch.Checker(rom, entries)
        self.assertTrue(checker.bare_thunk(BARE))
        self.assertEqual(struct.unpack_from('<H', rom, odd + 1 - BASE)[0], 0x4718)
        self.assertFalse(checker.bare_thunk(odd + 1))
        self.assertEqual(checker.resolve(odd + 1, {}, frozenset({5})), odd + 1)
        with self.assertRaisesRegex(watch.WatchRefusal, 'not unique aligned Thumb code'):
            watch.Checker(rom, entries).call(BARE + 1, frozenset({5}))
        # _call_via_r2 to BARE without the Thumb bit branches to ARM code.
        callee = function(CALLEE, [0xB500, ('LIT', 2, 0), VIA_R2, 0xBD00], [BARE])
        with self.assertRaisesRegex(watch.WatchRefusal, 'which is not Thumb code'):
            self.lines(callee)

    def test_a_bare_bx_r3_to_iwram_states_its_destination(self):
        # ldr r3,=0x03000001; bl BARE: code outside ROM, premised with its address.
        callee = function(CALLEE, [0xB500, ('LIT', 3, 0), BARE, 0xBD00], [0x03000001])
        _, lines = self.lines(callee)
        self.assertEqual(len(lines), 1)
        self.assertIn(f'through the bx r3 at 0x{BARE:08X} resolved to 0x03000001 (IWRAM)', lines[0])

    def test_a_summarised_callee_calling_a_bare_bx_r3_agrees_with_the_walk_in_context(self):
        # CALLEE: push {r5,lr}; movs r5,#0; [r3 = ...;] bl OTHER; pop {r5,pc}, so the saved R5 is
        # the watched word and OTHER (push {lr}; bl BARE; pop {pc}) is used by its summary.
        other = (0xB500, BARE, 0xBD00)
        functions = {PLAYER: PLAYER_BODY, BARE: (0x4718,), OTHER: other, CALLEE: (0xB520, 0x2500, OTHER, 0xBD20)}
        rom, entries = rom_with(functions)
        self.assertIsNotNone(watch.Checker(rom, entries).isolation(OTHER))
        in_context = outcome(functions, False)
        self.assertNotEqual(in_context[0], 'refused')
        self.assertEqual(outcome(functions, True), in_context)
        self.assertEqual([premise[3] for premise in in_context[1] if premise[0] == 'call'], [(BARE,)])
        # R3 known at CALLEE's call (ldr r3,=FOURTH|1): the walk goes through the bare bx r3 to
        # FOURTH (ldr r0,[sp,#4]; cmp r0,#0), which compares the saved R5 and refuses.  The
        # summary does not apply where its function pointer is known.
        fourth = 0x08014300
        functions[fourth] = (0x9801, 0x2800, BX_LR)
        functions[CALLEE] = function(CALLEE, [0xB520, 0x2500, ('LIT', 3, 0), OTHER, 0xBD20], [fourth | 1])
        in_context = outcome(functions, False)
        self.assertEqual(in_context[0], 'refused')
        self.assertIn('a comparison', in_context[1])
        self.assertEqual(outcome(functions, True), in_context)
        # R3 a frame address (add r3,sp,#4, the saved LR's word, not the one that depends on R5):
        # the bare bx r3 would branch into the frame.
        functions[CALLEE] = (0xB520, 0x2500, 0xAB01, OTHER, 0xBD20)
        in_context = outcome(functions, False)
        self.assertEqual(in_context[0], 'refused')
        self.assertEqual(outcome(functions, True), in_context)

if __name__ == '__main__':
    unittest.main()
