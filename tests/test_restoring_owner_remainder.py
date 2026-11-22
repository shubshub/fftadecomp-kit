"""The pinned signed remainder inside a restoring owner (restoring-owner-runtime-v1).

A divisor that is a CFG-proven positive signed32 constant excludes a zero divisor
and INT_MIN % -1 for every dividend; otherwise the existing signed16-dividend and
nonzero-divisor facts must hold. The operand walk is tested on exact instruction
streams; the composition on assembled owners whose runtime spans come from the
approved ROM.
"""
import copy
from pathlib import Path
import struct
import sys
import tempfile
import unittest

from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB, CS_GRP_JUMP
from capstone.arm_const import ARM_CC_AL, ARM_INS_BX

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import modsi3_profile as modsi3
import local_long_branch_profile as frame
import owner_admission_profile as owner
import owner_graph_profile as inventory
import owner_runtime_profile as runtime
import test_restoring_owner_optional_runtime as base

A = 0x08010000
CALLEE = 0x08011000
BL = struct.pack('<HH', 0xF000, 0xF800)   # bl to the next instruction; its edge is set below


def walk(tokens, words=()):
    """Run prove_remainders over halfwords; 'remainder', 'call' and 'local' are BLs."""
    data, sites, calls, branches = bytearray(), set(), {}, {}
    for token in tokens:
        site = A + len(data)
        if isinstance(token, str):
            data += BL
            if token == 'remainder':
                sites.add(site)
                calls[site] = modsi3.ADDRESS
            elif token == 'call':
                calls[site] = CALLEE
            else:
                branches[site] = site + 4
        else:
            data += struct.pack('<H', token)
    code_end = A + len(data)
    if words:
        data += bytes(-len(data) % 4)
        for word in words:
            data += struct.pack('<I', word)
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    decoder.detail = True
    instructions, edges = {}, {}
    for instruction in decoder.disasm(bytes(data[:code_end - A]), A):
        instructions[instruction.address] = instruction
    for site, instruction in instructions.items():
        following = site + instruction.size
        if instruction.id == ARM_INS_BX:
            edges[site] = []
        elif site in branches:
            edges[site] = [branches[site]]
        elif instruction.group(CS_GRP_JUMP):
            edges[site] = [instruction.operands[0].imm]
            if instruction.cc != ARM_CC_AL:
                edges[site].append(following)
        else:
            edges[site] = [following]
    return runtime.prove_remainders(instructions, edges, A, branches, calls, sites, bytes(data))


def ldr_pc(register, word_index, site_index, code_halfwords):
    """ldr rN, [pc, #imm] at halfword site_index reading pool word word_index."""
    site = A + 2 * site_index
    pool = A + ((2 * code_halfwords + 3) & ~3)
    return 0x4800 | register << 8 | (pool + 4 * word_index - ((site + 4) & ~3)) // 4


class OperandWalkTests(unittest.TestCase):
    def positive(self, tokens, value, words=()):
        records = walk(tokens, words)
        self.assertEqual([row[1:] for row in records], [[runtime.POSITIVE_DIVISOR, value]])

    def refused(self, tokens, words=()):
        with self.assertRaisesRegex(ValueError, 'signed16 r0 and nonzero r1'):
            walk(tokens, words)

    def test_immediate_and_copies(self):
        self.positive([0x21F0, 'remainder', 0x4770], 240)                   # movs r1,#240
        self.positive([0x2521, 0x1C29, 'remainder', 0x4770], 33)            # movs r5; adds r1,r5,#0
        self.positive([0x2121, 0x4688, 'call', 0x4641, 'remainder', 0x4770], 33)  # r8 survives a call

    def test_shift_and_immediate_arithmetic(self):
        self.positive([0x2178, 0x0049, 'remainder', 0x4770], 240)           # lsls r1,r1,#1
        self.positive([0x2105, 0x3110, 'remainder', 0x4770], 21)            # adds r1,#16
        self.positive([0x2408, 0x1EE1, 'remainder', 0x4770], 5)             # subs r1,r4,#3

    def test_unrelocated_pool_words(self):
        # ldr r1,=0x101 ; and ldr r4,=0x133 ; subs r4,#0x32 ; adds r1,r4,#0 (257).
        self.positive([ldr_pc(1, 0, 0, 4), 'remainder', 0x4770], 0x101, words=(0x101,))
        self.positive([ldr_pc(4, 0, 0, 6), 0x3C32, 0x1C21, 'remainder', 0x4770], 257, words=(0x133,))
        # A load at a halfword that is 2 mod 4 reads from the word-aligned PC.
        self.positive([0x2000, ldr_pc(1, 0, 1, 5), 'remainder', 0x4770], 0x101, words=(0x101,))

    def test_typed_address_domain_word_is_not_a_constant(self):
        for word in (0x02000101, 0x08000101, 0x0A000101):
            with self.subTest(word=hex(word)):
                self.refused([ldr_pc(1, 0, 0, 4), 'remainder', 0x4770], words=(word,))

    def test_local_branch_keeps_and_call_erases_the_divisor(self):
        self.positive([0x2109, 'local', 'remainder', 0x4770], 9)
        self.refused([0x2109, 'call', 'remainder', 0x4770])

    def test_join_requires_one_value_on_every_path(self):
        # cmp r0,#0 ; beq L ; movs r1,#5 ; b M ; L: movs r1,#X ; M: remainder
        prefix = [0x2800, 0xD001, 0x2105, 0xE000]
        self.positive(prefix + [0x2105, 'remainder', 0x4770], 5)
        self.refused(prefix + [0x2107, 'remainder', 0x4770])

    def test_zero_negative_and_minimum_divisors_need_the_signed16_proof(self):
        self.refused([0x2100, 'remainder', 0x4770])                         # 0
        self.refused([0x2100, 0x3901, 'remainder', 0x4770])                 # -1
        self.refused([0x2101, 0x07C9, 'remainder', 0x4770])                 # 0x80000000
        # A signed16 dividend with a nonzero negative divisor keeps the old proof.
        records = walk([0x1400, 0x21FF, 0x0609, 'remainder', 0x4770])
        self.assertEqual([row[1:] for row in records], [[runtime.SIGNED16_OPERANDS]])

    def test_variable_and_guarded_divisors_refused(self):
        self.refused([0x7DE1, 'remainder', 0x4770])                         # ldrb r1,[r4,#0x17]
        # adds r4,r5,#0 ; cmp r5,#1 ; bgt L ; movs r4,#2 ; L: adds r1,r4,#0
        self.refused([0x1C2C, 0x2D01, 0xDC00, 0x2402, 0x1C21, 'remainder', 0x4770])
        self.refused([0xA901, 'remainder', 0x4770])                         # add r1,sp,#4

    def test_sites_must_be_reached_remainder_calls(self):
        with self.assertRaisesRegex(ValueError, 'exact reached canonical sites'):
            runtime.prove_remainders({}, {}, A, {}, {}, set(), b'')


REMAINDER = ['adds r0, r4, #0', 'ldrb r0, [r5]', 'adds r0, #1', 'movs r1, #240',
             'bl __modsi3', 'adds r4, r0, #0']


class RemainderOwnerTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix='restoring_remainder_')
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)

    def fixture(self, middle=REMAINDER, pool=(), objects=b'{}', identities=modsi3.IDENTITIES, **options):
        directory = self.root / f'f{len(list(self.root.iterdir()))}'
        directory.mkdir()
        fixture = base.Fixture(directory, base.owner_assembly(middle=middle, pool=pool, **options),
                               identities=identities)
        fixture.objects = objects
        return fixture

    def test_compiler_remainder_with_positive_constant(self):
        fixture = self.fixture().link()
        manifest, _ = fixture.verify()
        proof = manifest['proof']
        self.assertEqual(manifest['profile'], owner.OPTIONAL_SCHEMA)
        site = next(offset for offset, name in proof['runtime_calls'] if name == '__modsi3')
        self.assertEqual(proof['remainders'], [[site, runtime.POSITIVE_DIVISOR, 240]])
        self.assertEqual(proof['remainder_runtime'], modsi3.RUNTIME)
        self.assertEqual(proof['remainder_dependencies'], [list(row) for row in modsi3.IDENTITIES])
        self.assertIn([site, '__modsi3'], fixture.bindings['calls'])
        self.assertEqual(fixture.verify(manifest=manifest)[0], manifest)
        report = fixture.report(manifest, len(fixture.verify()[1]))
        self.assertEqual(owner.selector_for_report(report), owner.SELECTOR)
        self.assertTrue(owner.selected(report))
        self.assertIn(f'* owner remainder: 0x08142950 at call +0x{site:X}: divisor 240 '
                      f'({runtime.POSITIVE_DIVISOR})', report.splitlines())
        self.assertEqual(owner.remainder_lines([[0x40, runtime.SIGNED16_OPERANDS]]),
                         [f'* owner remainder: 0x08142950 at call +0x40: signed16 dividend, nonzero divisor '
                          f'({runtime.SIGNED16_OPERANDS})'])

    def test_pool_word_divisor(self):
        middle = ['adds r0, r4, #0', 'ldr r1, .Ldivisor', 'bl __modsi3', 'adds r4, r0, #0']
        manifest, _ = self.fixture(middle=middle, pool=['.Ldivisor:', '.word 0x101']).link().verify()
        self.assertEqual([row[1:] for row in manifest['proof']['remainders']],
                         [[runtime.POSITIVE_DIVISOR, 0x101]])

    def test_addressed_name_bound_throughout(self):
        middle = [line.replace('__modsi3', modsi3.ADDRESSED_NAME) for line in REMAINDER]
        fixture = self.fixture(middle=middle).link()
        manifest, _ = fixture.verify()
        self.assertEqual([name for _, name in manifest['proof']['runtime_calls']], [modsi3.ADDRESSED_NAME])
        self.assertEqual(fixture.verify(manifest=manifest)[0], manifest)

    def test_both_names_in_one_owner_refused(self):
        middle = REMAINDER + [line.replace('__modsi3', modsi3.ADDRESSED_NAME) for line in REMAINDER]
        fixture = self.fixture(middle=middle)
        with self.assertRaisesRegex(ValueError, 'incomplete or mixed'):
            owner.original_bindings(fixture.image, A, bytes(fixture.rom), fixture.mapping, b'{}',
                                    selector=owner.SELECTOR)

    def test_stack_address_in_a_remainder_argument_refused(self):
        middle = REMAINDER[:4] + ['mov r2, sp'] + REMAINDER[4:]
        with self.assertRaisesRegex(ValueError, 'carry local stack provenance'):
            self.fixture(middle=middle).link().verify()

    def test_variable_divisor_refused(self):
        middle = REMAINDER[:3] + ['ldrb r1, [r5, #1]'] + REMAINDER[4:]
        with self.assertRaisesRegex(ValueError, 'signed16 r0 and nonzero r1'):
            self.fixture(middle=middle).link().verify()

    def test_relocated_low_word_is_not_an_unrelocated_divisor(self):
        middle = ['adds r0, r4, #0', 'ldr r1, .Ldivisor', 'bl __modsi3', 'adds r4, r0, #0']
        fixture = self.fixture(middle=middle, pool=['.Ldivisor:', '.word low_divisor'],
                               objects=b'{"low_divisor":"0x00000101"}').link()
        self.assertEqual([row[1] for row in fixture.bindings['data']], ['low_divisor'])
        with self.assertRaises(ValueError):
            fixture.verify()

    def test_zero_handler_and_interior_targets_refused(self):
        for name in ('func_0814274C', 'func_08142960'):
            middle = [line.replace('__modsi3', name) for line in REMAINDER]
            fixture = self.fixture(middle=middle)
            with self.subTest(name=name), self.assertRaises(ValueError):
                owner.original_bindings(fixture.image, A, bytes(fixture.rom), fixture.mapping, b'{}',
                                        selector=owner.SELECTOR)

    def test_manifest_tampering_refused(self):
        fixture = self.fixture().link()
        manifest, _ = fixture.verify()
        for change in ('value', 'kind', 'dependencies'):
            altered = copy.deepcopy(manifest)
            if change == 'value':
                altered['proof']['remainders'][0][2] = 241
            elif change == 'kind':
                altered['proof']['remainders'][0][1:] = [runtime.SIGNED16_OPERANDS]
            else:
                del altered['proof']['remainder_dependencies']
            with self.subTest(change=change), self.assertRaisesRegex(ValueError, 'manifest differs'):
                fixture.verify(manifest=altered)

    def test_source_may_not_name_the_compiler_remainder(self):
        with self.assertRaisesRegex(ValueError, 'reserved for compiler emission'):
            self.fixture().link(preprocessed='int __modsi3(int, int);\n')

    def test_runtime_identity_required(self):
        fixture = self.fixture().link()
        rows = [row for row in fixture.rows if int(row['rom'], 16) != modsi3.ADDRESS]
        with self.assertRaises(ValueError):
            fixture.verify(mapping=base.json.dumps(rows).encode())
        rom = bytearray(fixture.rom)
        rom[modsi3.ADDRESS - match.ROM_BASE + 8] ^= 1
        with self.assertRaisesRegex(ValueError, 'identity differs'):
            fixture.verify(rom=bytes(rom))

    def test_all_three_runtimes_compose_outside_the_original_domain(self):
        fixture = self.fixture(thunk=True, division=True,
                               identities=modsi3.IDENTITIES + match.UDIVSI3_IDENTITIES).link()
        manifest, _ = fixture.verify()
        proof = manifest['proof']
        self.assertEqual(manifest['profile'], owner.OPTIONAL_SCHEMA)
        self.assertEqual(sorted({name for _, name in proof['runtime_calls']}),
                         ['__modsi3', '__udivsi3', '_call_via_r3'])
        self.assertTrue({'thunk_dependencies', 'divisors', 'remainders'} <= proof.keys())

    def test_frame_requires_every_remainder_call_once_one_is_named(self):
        middle = REMAINDER + REMAINDER
        fixture = self.fixture(middle=middle, thunk=True).link()
        refinement = owner.refine(fixture.data, A, fixture.mapping)
        instructions, edges, branches, calls, _ = inventory.graph(fixture.data, A, refinement)
        thunk_site = next(site for site, target in calls.items()
                          if target == match.function_thunk.ALIASES['_call_via_r3'])
        remainders = sorted(site for site, target in calls.items() if target == modsi3.ADDRESS)

        def prove(runtime_calls):
            return frame.prove_frame(instructions, edges, A, branches, calls, stack_aliases=True,
                                     buffer_proof=match.BufferCallProof(bytes(fixture.rom), fixture.mapping),
                                     runtime_calls=runtime_calls)
        # Callers that name no remainder keep their old contract: the calls stay ordinary.
        prove({thunk_site: '_call_via_r3'})
        prove({thunk_site: '_call_via_r3', **{site: '__modsi3' for site in remainders}})
        with self.assertRaisesRegex(ValueError, 'exact complete canonical call bindings'):
            prove({thunk_site: '_call_via_r3', remainders[0]: '__modsi3'})
        with self.assertRaisesRegex(ValueError, 'exact complete canonical call bindings'):
            prove({thunk_site: '_call_via_r3', remainders[0]: '__udivsi3', remainders[1]: '__modsi3'})


if __name__ == '__main__':
    unittest.main()
