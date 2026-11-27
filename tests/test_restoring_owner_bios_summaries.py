"""A stack address handed to a BIOS SWI wrapper by a restoring owner (bios_wrapper_summary_profile).

restoring-owner-runtime-v1 walked every callee that received a stack address,
and a walk that reaches `svc` refuses: "non-leaf calls and interrupts require
linked CFG verification".  agbcc's CpuFill16(0, dest, n) passes the address of
a stack halfword to the CpuSet wrapper, so 08076560, 0807E37C and 080802E4
were refused there.  The owner now applies the plain path's BIOS wrapper
summaries at its own calls, discharged at the call over the complete owner
CFG.  The fixtures are assembled, so each shape is exact.
"""
import copy
import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import bios_cpuset_fill_profile as cpuset
import bios_wrapper_summary_profile as bios
import match
import owner_admission_profile as owner
import owner_runtime_profile as runtime
import test_restoring_owner_optional_runtime as base

A = base.A
DIV = 0x08141870
# CpuFill16 from the halfword at sp+4 into an external pointer, with r0 then rewritten.
FILL = ['movs r3, #0', 'add r0, sp, #4', 'strh r3, [r0]', 'adds r1, r4, #0', 'ldr r2, .Lfill',
        'bl func_0814186C', 'movs r0, #0']
POOL = ['.Lfill:', '.word 0x01000004']
# The 08076560 shape: a halfword at sp+2 and a control (u8 * u8) | 0x01000000, bit 26 proved clear.
PRODUCT = ['movs r3, #0', 'mov r0, sp', 'adds r0, #2', 'strh r3, [r0]', 'ldrb r2, [r5]', 'ldrb r3, [r5, #1]',
           'muls r2, r3', 'movs r3, #0x80', 'lsls r3, r3, #17', 'orrs r2, r3', 'adds r1, r4, #0',
           'bl func_0814186C', 'movs r0, #0']
NOT_DISCHARGED = 'not written before any read, call or return'
# A callee walked from the owner that hands its incoming r0 to CpuSet: push {r4, lr};
# movs r1, #0; strh r1, [r0]; adds r1, r5, #0; movs r2, #1; lsls r2, r2, #24; adds r2, #1;
# bl func_0814186C; movs r0, #0; pop {r4}; pop {r1}; bx r1 (hand-encoded Thumb).
CALLEE = 0x08012000


def callee_with_cpuset():
    halfwords = [0xB510, 0x2100, 0x8001, 0x1C29, 0x2201, 0x0612, 0x3201]
    offset = cpuset.ADDRESS - (CALLEE + 2 * len(halfwords) + 4)
    halfwords += [0xF000 | ((offset >> 12) & 0x7FF), 0xF800 | ((offset >> 1) & 0x7FF)]
    halfwords += [0x2000, 0xBC10, 0xBC02, 0x4708]
    return b''.join(value.to_bytes(2, 'little') for value in halfwords)


@unittest.skipUnless(shutil.which(match.DEFAULT_AS) and shutil.which(match.DEFAULT_LD),
                     'the fixed binutils are required')
class OwnerBiosSummaryTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix='owner_bios_summary_')
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)

    def fixture(self, middle=FILL, pool=POOL, *, wrappers=None, align=None, **options):
        for pad in range(2):
            directory = self.root / f'f{len(list(self.root.iterdir()))}'
            directory.mkdir()
            fixture = base.Fixture(directory, base.owner_assembly(pad=pad, middle=middle, pool=pool, **options),
                                   division=options.get('division', False))
            if align is None or fixture.size % 4 == align:
                break
        else:
            raise AssertionError('no fixture size has the requested alignment')
        for address, body in (wrappers or {cpuset.ADDRESS: cpuset.WRAPPER}).items():
            start = address - match.ROM_BASE
            fixture.rom[start:start + len(body)] = body
            fixture.rows.append(dict(rom=f'0x{address:08X}', end=f'0x{address + len(body):08X}',
                                     mode='thumb', instrs=len(body) // 2))
        fixture.mapping = json.dumps(fixture.rows).encode()
        return fixture.link()

    def admitted(self, middle=FILL, pool=POOL, **options):
        fixture = self.fixture(middle, pool, **options)
        manifest, instructions = fixture.verify()
        return fixture, manifest, instructions

    def refused(self, message, middle, pool=POOL, **options):
        with self.assertRaisesRegex(ValueError, message):
            self.fixture(middle, pool, **options).verify()

    @staticmethod
    def sites(manifest):
        return manifest['proof']['bios_summaries']['memory_sites']

    def test_fill_from_a_local_halfword_admitted_and_recorded(self):
        fixture, manifest, instructions = self.admitted()
        self.assertEqual(manifest['profile'], owner.OPTIONAL_SCHEMA)
        proof = manifest['proof']
        self.assertEqual(proof['schema'], runtime.OPTIONAL_SCHEMA)
        summaries = proof['bios_summaries']
        self.assertEqual((summaries['schema'], summaries['contract'], summaries['premises']),
                         (bios.SCHEMA, bios.CONTRACT, list(bios.PREMISES)))
        self.assertEqual(summaries['wrappers'], [[cpuset.ADDRESS, 'CpuSet', 0x0B, cpuset.WRAPPER.hex()]])
        self.assertEqual(summaries['bit_rules'], cpuset.ZERO_EXTENSION_RULES)
        [site] = self.sites(manifest)
        [call] = [item.address for item in instructions if item.mnemonic == 'bl' and
                  item.operands[0].imm == cpuset.ADDRESS]
        # Three saved words and an 8-byte frame: sp+0 is entry SP-20, so sp+4 is -16; one 2-byte unit.
        self.assertEqual({key: site[key] for key in ('site', 'routine', 'source', 'destination', 'unit',
                                                     'count', 'killed')},
                         {'site': call, 'routine': 'CpuSet', 'source': [-16, 2], 'destination': None,
                          'unit': 2, 'count': None, 'killed': [0]})
        self.assertIn(call, proof['frame']['local_aliases']['buffer_calls'])
        self.assertIn([cpuset.ADDRESS, cpuset.hashlib.sha256(cpuset.WRAPPER).hexdigest()],
                      proof['buffer_dependencies'])
        self.assertEqual(fixture.verify(manifest=manifest)[0], manifest)
        report = fixture.report(manifest, len(instructions)).splitlines()
        self.assertEqual([line for line in report if line.startswith('* buffer BIOS')],
                         bios.manifest_lines(summaries))
        for premise in bios.PREMISES:
            self.assertIn(f'* buffer BIOS premise: {premise}', report)
        self.assertTrue(owner.selected('\n'.join(report)))
        self.assertEqual(owner.selector_for_report('\n'.join(report)), owner.SELECTOR)

    def test_product_control_with_bit26_proved_clear_is_one_halfword(self):
        _, manifest, _ = self.admitted(PRODUCT, [])
        [site] = self.sites(manifest)
        ones, zeros = site['control']
        self.assertTrue(ones & bios.FILL and zeros & bios.WORDS)
        self.assertEqual((site['source'], site['unit']), ([-18, 2], 2))

    def test_fill_count_may_differ_between_paths(self):
        # A fill reads one source unit whatever the count; only bits 24 and 26 must agree.
        middle = FILL[:4] + ['ldr r2, .Lfill', 'cmp r4, #0', 'beq .Lcall', 'ldr r2, .Lother', '.Lcall:'] + FILL[5:]
        _, manifest, _ = self.admitted(middle, POOL + ['.Lother:', '.word 0x01000010'])
        [site] = self.sites(manifest)
        self.assertEqual((site['source'], site['count']), ([-16, 2], None))

    def test_copies_into_and_out_of_the_frame(self):
        out = ['mov r0, sp', 'adds r1, r4, #0', 'movs r2, #4', 'bl func_0814186C', 'movs r0, #0']
        _, manifest, _ = self.admitted(out, [])
        [site] = self.sites(manifest)
        self.assertEqual((site['source'], site['destination'], site['count']), ([-20, 8], None, 4))
        into = ['adds r0, r4, #0', 'mov r1, sp', 'movs r2, #1', 'lsls r2, r2, #26', 'adds r2, #2',
                'bl func_0814186C', 'movs r1, #0']
        _, manifest, _ = self.admitted(into, [])
        [site] = self.sites(manifest)
        self.assertEqual((site['source'], site['destination'], site['unit'], site['killed']),
                         (None, [-20, 8], 4, [1]))
        apart = ['mov r0, sp', 'add r1, sp, #4', 'movs r2, #2', 'bl func_0814186C', 'movs r0, #0', 'movs r1, #0']
        _, manifest, _ = self.admitted(apart, [])
        [site] = self.sites(manifest)
        self.assertEqual((site['source'], site['destination'], site['killed']), ([-20, 4], [-16, 4], [0, 1]))

    def test_owner_without_a_summarised_call_has_no_record(self):
        # The same wrapper called with external pointers only stays an ordinary call.
        external = ['adds r0, r4, #0', 'adds r1, r5, #0', 'ldr r2, .Lfill', 'bl func_0814186C']
        _, manifest, instructions = self.admitted(external)
        self.assertNotIn('bios_summaries', manifest['proof'])
        self.assertNotIn(cpuset.ADDRESS, [target for target, _ in manifest['proof']['buffer_dependencies']])
        self.assertEqual([name for _, name in manifest['proof']['calls']], ['func_08011000', 'func_0814186C'])

    def test_original_runtime_domain_records_a_summary_under_the_optional_schema(self):
        manifest, _ = self.fixture(thunk=True, division=True, align=0).verify()
        self.assertEqual(manifest['profile'], owner.OPTIONAL_SCHEMA)
        self.assertEqual(manifest['proof']['schema'], runtime.OPTIONAL_SCHEMA)
        self.assertIn('bios_summaries', manifest['proof'])
        self.assertIn('local_branches', manifest['proof'])
        plain = self.fixture([], [], thunk=True, division=True, align=0)
        manifest, _ = plain.verify()
        self.assertEqual(manifest['profile'], owner.SCHEMA)
        self.assertEqual(set(manifest['proof']), base.ORIGINAL_KEYS)

    def test_unproved_or_oversized_controls_refused(self):
        cases = {
            'control from memory': (FILL[:4] + ['ldr r2, [r5]'] + FILL[5:], [],
                                    'requires the whole control word on every path'),
            'fill bit on one path only': (FILL[:4] + ['ldr r2, .Lfill', 'cmp r4, #0', 'beq .Lcall', 'movs r2, #4',
                                                      '.Lcall:'] + FILL[5:], POOL,
                                          'requires the whole control word on every path'),
            'width unknown at a halfword': (['movs r3, #0', 'mov r0, sp', 'adds r0, #2', 'strh r3, [r0]',
                                            'ldr r2, [r5]', 'movs r3, #1', 'lsls r3, r3, #24', 'orrs r2, r3',
                                            'adds r1, r4, #0', 'bl func_0814186C', 'movs r0, #0'], [],
                                           'unaligned or outside allocated local words'),
            'copy past the frame': (['mov r0, sp', 'adds r1, r4, #0', 'movs r2, #5', 'bl func_0814186C',
                                     'movs r0, #0'], [], 'unaligned or outside allocated local words'),
            'words past the frame': (['adds r0, r4, #0', 'mov r1, sp', 'movs r2, #1', 'lsls r2, r2, #26',
                                      'adds r2, #3', 'bl func_0814186C', 'movs r1, #0'], [],
                                     'unaligned or outside allocated local words'),
            'zero count': (['mov r0, sp', 'adds r1, r4, #0', 'movs r2, #0', 'bl func_0814186C', 'movs r0, #0'], [],
                           'count is zero'),
            'reserved bit': (['mov r0, sp', 'adds r1, r4, #0', 'movs r2, #1', 'lsls r2, r2, #25', 'adds r2, #1',
                              'bl func_0814186C', 'movs r0, #0'], [], 'reserved bit'),
            'local spans overlap': (['mov r0, sp', 'mov r1, sp', 'adds r1, #2', 'movs r2, #2', 'bl func_0814186C',
                                     'movs r0, #0', 'movs r1, #0'], [], 'source and destination overlap'),
        }
        for name, (middle, pool, message) in cases.items():
            with self.subTest(name=name):
                self.refused(message, middle, pool)

    def test_pointer_registers_must_be_rewritten_before_use(self):
        cases = {
            'read after the call': FILL[:-1] + ['ldrh r3, [r0]', 'movs r0, #0'],
            'local branch before the rewrite': FILL[:-1],
            'call before the rewrite': FILL[:-1] + ['bl func_08011000'],
            'destination read': ['adds r0, r4, #0', 'mov r1, sp', 'movs r2, #4', 'bl func_0814186C',
                                 'movs r0, #0', 'str r0, [r1]', 'movs r1, #0'],
        }
        for name, middle in cases.items():
            with self.subTest(name=name):
                self.refused(NOT_DISCHARGED, middle, POOL if '.Lfill' in ' '.join(middle) else [])

    def test_a_call_whose_callee_writes_r0_first_kills_it_and_is_reported(self):
        # The 08023F00 shape: CpuSet, then straight into a callee whose first instruction writes r0.
        wrappers = {cpuset.ADDRESS: cpuset.WRAPPER, CALLEE: bytes.fromhex('00207047')}  # movs r0, #0; bx lr
        middle = FILL[:-1] + ['bl func_08012000']
        fixture, manifest, instructions = self.admitted(middle, wrappers=wrappers)
        summaries = manifest['proof']['bios_summaries']
        [site] = self.sites(manifest)
        [call] = [item.address for item in instructions if item.mnemonic == 'bl' and
                  item.operands[0].imm == CALLEE]
        [kill] = site['call_kills']
        self.assertEqual({key: kill[key] for key in ('site', 'register', 'callee', 'end', 'kills', 'states')},
                         {'site': call, 'register': 0, 'callee': CALLEE, 'end': CALLEE + 4,
                          'kills': [[CALLEE, 0]], 'states': 1})
        report = fixture.report(manifest, len(instructions)).splitlines()
        lines = [line for line in report if line.startswith('* buffer BIOS')]
        self.assertEqual(lines, bios.manifest_lines(summaries))
        self.assertEqual(lines[-1], f'* buffer BIOS call kill: call 0x{call:08X} to 0x{CALLEE:08X} kills r0 (left '
                                    f'by CpuSet at 0x{site["site"]:08X}): the callee writes r0@0x{CALLEE:08X} '
                                    f'before any read, call, interrupt, return or cycle on every path from its '
                                    f'entry (1 states)')
        self.assertTrue(owner.selected('\n'.join(report)))
        # Replay rebuilds the proof and compares the whole rendered report, so the line cannot be dropped,
        # edited or repeated (the rebuild itself is the fixture's, as fixture.report renders it).
        result = (fixture.data, manifest, 'synthetic-source', fixture.mapping, fixture.index, fixture.objects,
                  bytes(fixture.rom), len(instructions), fixture.original)
        text, kill_line = fixture.report(manifest, len(instructions)), lines[-1]
        with mock.patch.object(owner, 'build', lambda *args, **kwargs: result):
            self.assertTrue(owner.report_matches(text, self.root, A))
            for name, edited in (('dropped', text.replace(kill_line + '\n', '')),
                                 ('states edited', text.replace(kill_line, kill_line.replace('(1 states)',
                                                                                             '(2 states)'))),
                                 ('register edited', text.replace(kill_line, kill_line.replace('kills r0',
                                                                                               'kills r1'))),
                                 ('repeated', text.replace(kill_line, kill_line + '\n' + kill_line))):
                with self.subTest(edit=name):
                    self.assertNotEqual(edited, text)
                    self.assertFalse(owner.report_matches(edited, self.root, A))
        altered = copy.deepcopy(manifest)
        del altered['proof']['bios_summaries']['memory_sites'][0]['call_kills']
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            fixture.verify(manifest=altered)
        # A callee that reads r0 first leaves the obligation open.
        self.refused(NOT_DISCHARGED, middle, wrappers={cpuset.ADDRESS: cpuset.WRAPPER,
                                                       CALLEE: bytes.fromhex('011c00207047')})

    def test_frame_words_a_summarised_call_may_write_lose_their_contents(self):
        # r8 is spilled to sp+4 and restored from it; a CpuSet destination over the
        # whole frame may have overwritten it, so the exit no longer restores r8.
        spill, restore = ['mov r3, r8', 'str r3, [sp, #4]'], ['ldr r3, [sp, #4]', 'mov r8, r3']
        self.admitted(spill + restore, [])
        self.refused('restore SP, r4-r11', spill + ['adds r0, r4, #0', 'mov r1, sp', 'movs r2, #4',
                                                    'bl func_0814186C', 'movs r1, #0'] + restore, [])

    def test_cpuset_inside_a_walked_callee_refused(self):
        self.refused("summarised only at the owner's own call", ['mov r0, sp', 'bl func_08012000', 'movs r0, #0'],
                     [], wrappers={cpuset.ADDRESS: cpuset.WRAPPER, CALLEE: callee_with_cpuset()})

    def test_a_dead_local_in_r3_is_admitted_and_reported(self):
        # The 080E0824 shape: external source and destination, a stale local address in R3, rewritten.
        middle = ['adds r0, r4, #0', 'adds r1, r5, #0', 'mov r3, sp', 'ldr r2, .Lfill', 'bl func_0814186C',
                  'movs r3, #0']
        fixture, manifest, instructions = self.admitted(middle)
        summaries = manifest['proof']['bios_summaries']
        [site] = self.sites(manifest)
        self.assertEqual({key: site[key] for key in ('source', 'destination', 'killed', 'non_argument')},
                         {'source': None, 'destination': None, 'killed': [3], 'non_argument': [[3, -20]]})
        self.assertNotIn('call_kills', site)
        self.assertEqual(summaries['premises'], list(bios.PREMISES_NON_ARGUMENT))
        report = fixture.report(manifest, len(instructions)).splitlines()
        lines = [line for line in report if line.startswith('* buffer BIOS')]
        self.assertEqual(lines, bios.manifest_lines(summaries))
        self.assertEqual(len(lines), 6)
        self.assertTrue(lines[-1].startswith(f'* buffer BIOS non-argument register: r3 carried local -20 into '
                                             f'CpuSet at 0x{site["site"]:08X}; no memory routine takes r3 as an '
                                             f'argument (GBATEK: R0-R2), '))
        self.assertIn(f'* buffer BIOS premise: {bios.OUTPUTS_NON_ARGUMENT}', report)
        self.assertNotIn(f'* buffer BIOS premise: {bios.OUTPUTS}', report)
        self.assertTrue(owner.selected('\n'.join(report)))
        result = (fixture.data, manifest, 'synthetic-source', fixture.mapping, fixture.index, fixture.objects,
                  bytes(fixture.rom), len(instructions), fixture.original)
        text, stated = fixture.report(manifest, len(instructions)), lines[-1]
        with mock.patch.object(owner, 'build', lambda *args, **kwargs: result):
            self.assertTrue(owner.report_matches(text, self.root, A))
            for name, edited in (('dropped', text.replace(stated + '\n', '')),
                                 ('offset edited', text.replace(stated, stated.replace('local -20', 'local -16'))),
                                 ('repeated', text.replace(stated, stated + '\n' + stated))):
                with self.subTest(edit=name):
                    self.assertNotEqual(edited, text)
                    self.assertFalse(owner.report_matches(edited, self.root, A))
        for change in ('record', 'killed', 'premises'):
            altered = copy.deepcopy(manifest)
            record = altered['proof']['bios_summaries']
            if change == 'record':
                del record['memory_sites'][0]['non_argument']
            elif change == 'killed':
                record['memory_sites'][0]['killed'] = []
            else:
                record['premises'] = list(bios.PREMISES)
            with self.subTest(change=change), self.assertRaisesRegex(ValueError, 'manifest differs'):
                fixture.verify(manifest=altered)

    def test_pointer_outside_r0_r1_and_scalar_wrappers_refused(self):
        self.refused('local pointer outside R0, R1 and the non-argument R3 and R12',
                     ['adds r0, r4, #0', 'adds r1, r5, #0', 'mov r2, sp', 'bl func_0814186C', 'movs r2, #0'], [])
        # A local address in R3 that is not rewritten before the owner's next call and return.
        self.refused(NOT_DISCHARGED, ['adds r0, r4, #0', 'adds r1, r5, #0', 'mov r3, sp', 'ldr r2, .Lfill',
                                      'bl func_0814186C'])
        self.refused('scalar BIOS wrapper refuses a tracked local pointer',
                     ['mov r0, sp', 'movs r1, #3', 'bl func_08141870', 'movs r0, #0'], [],
                     wrappers={cpuset.ADDRESS: cpuset.WRAPPER, DIV: bios.SCALAR[DIV][2]})

    def test_wrapper_identity_required(self):
        self.refused('BIOS CpuSet summary requires the exact indexed wrapper bytes', FILL,
                     wrappers={cpuset.ADDRESS: bytes.fromhex('0cdf7047')})
        self.refused('buffer callee mapping overlaps another span|buffer callee has no complete mapped span|'
                     'exact indexed wrapper bytes', FILL, wrappers={cpuset.ADDRESS: cpuset.WRAPPER + b'\xc0\x46'})

    def test_manifest_tampering_refused(self):
        fixture, manifest, _ = self.admitted()
        for change in ('source', 'control', 'killed', 'premise', 'dropped'):
            altered = copy.deepcopy(manifest)
            record = altered['proof']['bios_summaries']
            if change == 'source':
                record['memory_sites'][0]['source'] = [-20, 2]
            elif change == 'control':
                record['memory_sites'][0]['control'][0] ^= 1
            elif change == 'killed':
                record['memory_sites'][0]['killed'] = []
            elif change == 'premise':
                record['premises'] = record['premises'][:2]
            else:
                del altered['proof']['bios_summaries']
            with self.subTest(change=change), self.assertRaisesRegex(ValueError, 'manifest differs'):
                fixture.verify(manifest=altered)


class OwnerBindingTests(unittest.TestCase):
    """bind_owner: one complete owner CFG, bound before any call."""

    def graph(self):
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        code = bytes.fromhex('7047')
        instructions = {item.address: item for item in decoder.disasm(code, A)}
        return code, instructions, {A: ()}

    def test_binding_is_single_and_complete(self):
        code, instructions, edges = self.graph()
        summaries = bios.BiosWrapperSummaries()
        with self.assertRaises(ValueError):
            summaries.bind_owner(code, A, instructions, {})
        with self.assertRaises(ValueError):
            summaries.bind_owner(code, A + 2, instructions, edges)
        with self.assertRaises(ValueError):
            summaries.bind_owner(bytearray(code), A, instructions, edges)
        summaries.bind_owner(code, A, instructions, edges)
        with self.assertRaises(ValueError):
            summaries.bind_owner(code, A, instructions, edges)
        unbound = bios.BiosWrapperSummaries()
        unbound.pending[(A, cpuset.ADDRESS, -4, None, (), (), ())] = None
        with self.assertRaises(ValueError):
            unbound.bind_owner(code, A, instructions, edges)


if __name__ == '__main__':
    unittest.main()
