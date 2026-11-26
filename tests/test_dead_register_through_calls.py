"""dead_register.through_calls: a dead register proved through a callee's own calls and constant branches.

DeadStackRegisters' entry proof refuses a callee that hands the live value to a callee of its
own before writing it, or whose path to the write passes a switch the value never reaches.
The retry follows such a BL into the indexed Thumb callee (nested at most twice), decides a
conditional branch only from the CMP/CMN/TST right before it on exact constants, and refuses
everything else that could observe the value.
"""
from pathlib import Path
import os
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import match
import dead_register
from capstone.arm import ARM_REG_R0

BASE = 0x08010000
R2 = frozenset((ARM_REG_R0 + 2,))
# The shape of the callee that needs it: f(u16 entry) { category = entry ? g(entry, 3) : -1;
# switch (category - 1) { ... default: h(0x7E); } } with r2 live on entry; g and h write r2 first.
CALLEE = """push {r4, lr}
lsls r0, r0, #16
lsrs r4, r0, #16
cmp r4, #0
bne 1f
%(zero)s
b 2f
1: adds r0, r4, #0
movs r1, #3
bl g
2: subs r0, #1
%(guard)s
lsls r0, r0, #2
ldr r1, =table
adds r0, r0, r1
ldr r0, [r0]
mov pc, r0
.align 2
table: .word 3f, 3f
3: movs r0, #0x7e
bl h
pop {r4}
pop {r0}
bx r0
.ltorg
"""
DEFAULTS = dict(zero='movs r0, #1\nrsbs r0, r0, #0', guard='cmp r0, #0x12\nbhi 3f')
# The dispatch edge's first observing instruction is its table load; a bare `mov pc` dispatch is a PC write.
DISPATCH = 'memory read before its killing write'
BARE = ('lsls r0, r0, #2\nldr r1, =table\nadds r0, r0, r1\nldr r0, [r0]\nmov pc, r0', 'mov pc, r0')
ENTRY = 'dead register reaches (a call|a return or an unresolved transfer) before its killing write'
G = 'push {r4, r5, lr}\nlsls r0, r0, #16\nlsrs r5, r0, #16\nlsls r1, r1, #24\nlsrs r2, r1, #24\npop {r4, r5}\npop {r0}\nbx r0'
H = 'push {lr}\nlsls r0, r0, #16\nlsrs r2, r0, #16\npop {r0}\nbx r0'


class FakeProof:
    """span() over assembled, indexed functions; anything else refuses as BufferCallProof.span does."""

    def __init__(self, functions):
        self.functions = functions

    def span(self, address):
        if address not in self.functions:
            raise ValueError('buffer call target is not unique aligned Thumb ROM code')
        return self.functions[address]


class ThroughCallsTests(unittest.TestCase):
    def setUp(self):
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH', ROOT / 'build'))
        scratch.mkdir(parents=True, exist_ok=True)
        self.temporary = tempfile.TemporaryDirectory(prefix='dead_through_', dir=scratch)
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)

    def assemble(self, functions):
        """functions: [(name, body)], each 0x100 apart from BASE; returns ({name: address}, proof)."""
        names = [name for name, _ in functions]
        text = ('.syntax unified\n.arch armv4t\n.thumb\n.text\n' +
                ''.join(f'.global {name}, {name}_end\n' for name in names) +
                ''.join(f'.org 0x{0x100 * index:x}\n.thumb_func\n{name}:\n{body}\n{name}_end:\n'
                        for index, (name, body) in enumerate(functions)))
        (self.root / 'f.s').write_text(text)
        for command in (['arm-none-eabi-as', '-mthumb-interwork', str(self.root / 'f.s'), '-o', str(self.root / 'f.o')],
                        ['arm-none-eabi-ld', f'-Ttext=0x{BASE:08X}', '-e', names[0], str(self.root / 'f.o'),
                         '-o', str(self.root / 'f.elf')],
                        ['arm-none-eabi-objcopy', '-O', 'binary', '--only-section=.text', str(self.root / 'f.elf'),
                         str(self.root / 'f.bin')]):
            subprocess.run(command, check=True, capture_output=True)
        image = match.elf_image((self.root / 'f.elf').read_bytes())
        symbols = {symbol['name']: symbol['value'] & ~1 for symbol in image['symbols']}
        binary = (self.root / 'f.bin').read_bytes()
        spans = {symbols[name]: binary[symbols[name] - BASE:symbols[name + '_end'] - BASE] for name in names}
        return symbols, FakeProof(spans)

    def run_callee(self, functions=None, **change):
        values = dict(DEFAULTS, **change)
        symbols, proof = self.assemble(functions or [('f', CALLEE % values), ('g', G), ('h', H)])
        return symbols, dead_register.through_calls(proof, symbols['f'], R2)

    # -- admitted --------------------------------------------------------
    def test_the_shape_is_admitted_with_its_calls_and_decision(self):
        symbols, (result, followed, decided) = self.run_callee()
        self.assertEqual([(row['callee'], row['depth']) for row in followed], [(symbols['g'], 1), (symbols['h'], 1)])
        self.assertEqual([row['kills'] for row in followed], [[[symbols['g'] + 8, 2]], [[symbols['h'] + 4, 2]]])
        decision, = decided
        self.assertEqual((decision['condition'], decision['edge'], decision['operands']),
                         ('bhi', 'taken', [0xFFFFFFFE, 0x12]))
        # The entry proof refuses it: the first BL comes before any write of r2.
        with self.assertRaisesRegex(ValueError, ENTRY):
            dead_register.prove(symbols['f'], R2, dead_register.thumb_step(symbols['f'], self.assemble(
                [('f', CALLEE % DEFAULTS), ('g', G), ('h', H)])[1].span(symbols['f'])),
                end='end', cycle='cycle', budget='budget')

    def test_signed_and_unsigned_conditions_are_exact(self):
        # r0 = -2 against 0x12: unsigned higher-or-same (taken), signed greater-or-equal (not taken).
        self.run_callee(guard='cmp r0, #0x12\nbhs 3f')
        with self.assertRaisesRegex(ValueError, DISPATCH):
            self.run_callee(guard='cmp r0, #0x12\nbge 3f')
        self.run_callee(guard='cmp r0, #0x12\nblt 3f')
        # Equal operands: carry set, Z set - bhs taken, bhi not.
        self.run_callee(zero='movs r0, #0x13\nnop', guard='cmp r0, #0x12\nbhs 3f')
        with self.assertRaisesRegex(ValueError, DISPATCH):
            self.run_callee(zero='movs r0, #0x13\nnop', guard='cmp r0, #0x12\nbhi 3f')
        # CMN: r0 = -1 after the subs, -1 + -1 = -2, Z clear: bne taken.
        self.run_callee(guard='cmn r0, r0\nbne 3f', zero='movs r0, #0\nnop')
        # TST leaves C and V: a condition on them is not decided.
        with self.assertRaisesRegex(ValueError, DISPATCH):
            self.run_callee(guard='tst r0, r0\nbhi 3f')
        self.run_callee(guard='tst r0, r0\nbne 3f')

    def test_a_merge_of_equal_constants_is_a_constant(self):
        functions = [('f', CALLEE.replace('bne 1f', 'bne 4f').replace('1: adds r0, r4, #0\nmovs r1, #3\nbl g\n',
                      '4: movs r0, #0\nmvns r0, r0\nb 2f\n') % DEFAULTS), ('g', G), ('h', H)]
        self.run_callee(functions)

    # -- the lead's six conditions ---------------------------------------------
    def test_a_reachable_dispatch_edge_refuses(self):
        with self.assertRaisesRegex(ValueError, DISPATCH):
            self.run_callee(zero='movs r0, #5\nnop')   # 4 against 0x12: bhi not taken, the dispatch runs
        # The same edge to a bare `mov pc`: a PC write on a surviving edge.
        functions = [('f', (CALLEE.replace(*BARE)) % dict(DEFAULTS, zero='movs r0, #5\nnop')), ('g', G), ('h', H)]
        with self.assertRaisesRegex(ValueError, 'unresolved transfer'):
            self.run_callee(functions)
        # ... and with the constant making it unreachable, the bare dispatch is never walked.
        self.run_callee([('f', CALLEE.replace(*BARE) % DEFAULTS), ('g', G), ('h', H)])

    def test_a_constant_from_memory_is_no_constant(self):
        with self.assertRaisesRegex(ValueError, 'memory read'):
            self.run_callee(zero='ldr r0, =0xFFFFFFFF\nnop')

    def test_flags_clobbered_before_the_branch_refuse(self):
        with self.assertRaisesRegex(ValueError, DISPATCH):
            self.run_callee(guard='cmp r0, #0x12\nmovs r3, #0\nbhi 3f')
        # A second way into the branch: its flags need not come from the CMP.
        functions = [('f', (CALLEE % DEFAULTS).replace('2: subs r0, #1\n', '2: subs r0, #1\nbeq 5f\n')
                      .replace('cmp r0, #0x12\nbhi 3f', 'cmp r0, #0x12\n5: bhi 3f')), ('g', G), ('h', H)]
        self.assertIn('5: bhi 3f', functions[0][1])
        with self.assertRaisesRegex(ValueError, DISPATCH):
            self.run_callee(functions)

    def test_an_untracked_write_makes_the_register_unknown(self):
        # A shift by a register and an SP-relative add are no tracked forms: r0 is unknown after
        # either, so the bhi is not decided and its dispatch edge survives.
        for write in ('lsls r0, r3', 'add r0, sp, #4'):
            with self.subTest(write=write), self.assertRaisesRegex(ValueError, DISPATCH):
                self.run_callee(zero='movs r0, #1\nrsbs r0, r0, #0\n' + write)

    def run_body(self, body, *extra):
        """A callee `f` with r2 live on entry and the given body, plus extra functions."""
        symbols, proof = self.assemble([('f', body), *extra])
        return dead_register.through_calls(proof, symbols['f'], R2)

    def test_an_unknown_overwrite_clears_the_constant(self):
        # r0 = 5 decides `beq` taken only while it is still 5: after any write the fixpoint cannot
        # compute, the fallthrough (which reads r2) must be walked.  (Reviewer cases.)
        body = 'movs r0, #5\n%s\ncmp r0, #5\nbeq 1f\nadds r3, r2, #0\n1: movs r2, #0\nbx lr'
        self.run_body(body % 'nop')
        for write in ('adds r0, r0, r1', 'adds r0, r1, #0', 'lsls r0, r1', 'add r0, sp, #4', 'adcs r0, r1'):
            with self.subTest(write=write), self.assertRaisesRegex(ValueError, 'read before its killing write'):
                self.run_body(body % write)

    def test_a_writeback_is_a_write(self):
        # STMIA r0! writes r0 (the writeback), so the constant 0 is gone before the compare.
        with self.assertRaises(ValueError):
            self.run_body('movs r0, #0\nstmia r0!, {r1}\ncmp r0, #0\nbeq 1f\nadds r3, r2, #0\n1: movs r2, #0\nbx lr')
        self.run_body('movs r0, #0\nstr r1, [r0]\ncmp r0, #0\nbeq 1f\nadds r3, r2, #0\n1: movs r2, #0\nbx lr')

    def test_a_local_bl_is_no_call(self):
        # A BL into the callee's own body (agbcc's far jump) or to its own entry is never followed.
        for target in ('2f', 'f'):
            with self.subTest(target=target), self.assertRaisesRegex(ValueError, 'follows no local BL'):
                self.run_callee(zero=f'movs r0, #1\nbl {target}')

    def test_a_merge_of_two_constants_refuses(self):
        functions = [('f', CALLEE.replace('bne 1f', 'bne 4f').replace('1: adds r0, r4, #0\nmovs r1, #3\nbl g\n',
                      '4: movs r0, #3\nb 2f\n') % DEFAULTS), ('g', G), ('h', H)]
        with self.assertRaisesRegex(ValueError, DISPATCH):
            self.run_callee(functions)

    def test_a_third_nesting_level_refuses(self):
        def chain(levels):
            functions = [('f', CALLEE % DEFAULTS), ('g', G)]
            names = ['h'] + [f'h{n}' for n in range(1, levels)]
            for here, there in zip(names, names[1:]):
                functions.append((here, f'push {{lr}}\nbl {there}\npop {{r0}}\nbx r0'))
            functions.append((names[-1], H))
            return functions
        self.run_callee(chain(2))              # f -> h -> h1: depth 2
        with self.assertRaisesRegex(ValueError, 'nesting exceeds its bound'):
            self.run_callee(chain(3))          # f -> h -> h1 -> h2: depth 3

    def test_a_read_on_one_branch_only_refuses(self):
        with self.assertRaisesRegex(ValueError, 'read before its killing write'):
            self.run_callee(zero='adds r0, r2, #0\nnop')
        with self.assertRaisesRegex(ValueError, 'read before its killing write'):
            self.run_callee(functions=[('f', CALLEE % DEFAULTS), ('g', G.replace('lsls r1, r1, #24', 'adds r1, r2, #0')),
                                       ('h', H)])

    # -- the rest of the boundary ---------------------------------------------
    def test_a_return_with_the_register_live_refuses(self):
        with self.assertRaisesRegex(ValueError, 'return'):
            self.run_callee(functions=[('f', CALLEE % DEFAULTS), ('g', 'bx lr'), ('h', H)])

    def test_a_memory_read_in_a_nested_callee_refuses(self):
        with self.assertRaisesRegex(ValueError, 'memory read'):
            self.run_callee(functions=[('f', CALLEE % DEFAULTS), ('g', 'ldr r3, [r0]\n' + G), ('h', H)])

    def test_unindexed_targets_and_thunks_refuse(self):
        symbols, proof = self.assemble([('f', CALLEE % DEFAULTS), ('g', G), ('h', H)])
        del proof.functions[symbols['g']]
        with self.assertRaisesRegex(ValueError, 'not unique aligned Thumb ROM code'):
            dead_register.through_calls(proof, symbols['f'], R2)
        thunk = match.RUNTIME_HELPERS['_call_via_r3']
        with self.assertRaisesRegex(ValueError, 'no call thunk'):
            dead_register.through_calls(FakeProof({thunk: b'\x18\x47\xc0\x46'}), thunk, R2)

    def test_an_indirect_transfer_refuses(self):
        with self.assertRaisesRegex(ValueError, 'unresolved transfer'):
            self.run_callee(zero='bx r3\nnop')

    def test_a_cycle_without_the_write_refuses(self):
        with self.assertRaisesRegex(ValueError, 'path without its killing write'):
            self.run_callee(zero='6: movs r0, #1\nb 6b')

    # -- the policy object and its evidence -------------------------------------
    def policy(self, functions=None):
        symbols, proof = self.assemble(functions or [('f', CALLEE % DEFAULTS), ('g', G), ('h', H)])
        return symbols, dead_register.DeadStackRegisters(proof)

    def test_the_record_and_line_state_what_was_followed(self):
        symbols, policy = self.policy()
        entry = policy.entry(symbols['f'], R2)
        self.assertEqual(entry['schema'], dead_register.CALLS_SCHEMA)
        policy.calls[(0x08000300, symbols['f'], ((ARM_REG_R0 + 2, -100),))] = dict(
            site=0x08000300, callee=symbols['f'], registers=[[2, -100]], entry=entry)
        line, = policy.lines()
        self.assertIn(f'`{dead_register.CALLS_SCHEMA}` call 0x08000300 to 0x{symbols["f"]:08X} passes r2=-100', line)
        to_g, to_h = entry['followed']
        self.assertIn(f'BL 0x{to_g["site"]:08X} to 0x{symbols["g"]:08X} (depth 1, {to_g["body_sha256"][:16]}) '
                      f'writes r2@0x{symbols["g"] + 8:08X}', line)
        self.assertIn(f'BL 0x{to_h["site"]:08X} to 0x{symbols["h"]:08X} (depth 1, ', line)
        self.assertEqual(entry['kills'], [[to_g['site'], 2], [to_h['site'], 2]])
        self.assertIn('bhi taken to', line)
        self.assertIn('(flags from ', line)

    def test_an_entry_the_first_proof_admits_keeps_its_record(self):
        symbols, policy = self.policy([('f', H), ('g', G)])
        entry = policy.entry(symbols['f'], R2)
        self.assertNotIn('schema', entry)
        self.assertNotIn('followed', entry)

    def test_disabled_keeps_the_entry_refusal(self):
        symbols, policy = self.policy()
        with patch.object(dead_register.THROUGH_CALLS, 'enabled', False), \
                self.assertRaisesRegex(ValueError, ENTRY):
            policy.entry(symbols['f'], R2)


if __name__ == '__main__':
    unittest.main()
