"""The signed16 dividend and bounded odd divisor must reach the real canonical BL."""
from contextlib import redirect_stdout
import hashlib
import io
import json
import os
from pathlib import Path
import struct
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
import match
import report_fixtures
import standing_premise
import match_evidence
import status
import modsi3_profile as remainder
import odd_remainder_profile as odd
import signed_divmod_profile as driver


class OperandTests(unittest.TestCase):
    # LDRH R0,[R0,#24]; LSR R5,R0,#2; LSL R6,R5,#1; BL; ASR R0,#16;
    # ADD R1,R6,#1; BL. The ordinary call kills R0-R3 but preserves R6.
    words = (0x8B00, 0x0885, 0x006E, 0xF000, 0xF800, 0x1400, 0x1C71, 0xF000, 0xF800)

    def prove(self, words, extra_edge=None):
        start = 0x08000100
        decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
        decoder.detail = True
        instructions = {item.address: item for item in decoder.disasm(
            struct.pack('<' + 'H'*len(words), *words), start)}
        last = max(instructions)
        edges = {pc: [pc+item.size] if pc < last else [] for pc, item in instructions.items()}
        if extra_edge:
            edges[start + extra_edge[0]].append(start + extra_edge[1])
        calls = {pc: remainder.ADDRESS if pc == last else 0x08002804
                 for pc, item in instructions.items() if item.mnemonic == 'bl'}
        return odd.operand_proof(instructions, edges, start, calls, last)

    def test_domain_and_callee_saved_path(self):
        proof = self.prove(self.words)
        self.assertEqual(proof['preserved_register'], 'r6')
        self.assertEqual(proof['positive_odd_divisor'], [1, 32767])
        self.assertEqual(proof['signed_dividend'], [-32768, 32767])
        values = {2*(x//4)+1 for x in range(65536)}
        self.assertEqual(values, set(range(1, 32768, 2)))

    def test_wrong_load_shift_add_or_dividend(self):
        for index, word in ((0,0x6800), (1,0x0845), (2,0x00AE), (5,0x1000), (6,0x1C31)):
            with self.subTest(index=index), self.assertRaises(ValueError):
                words = list(self.words)
                words[index] = word
                self.prove(words)

    def test_caller_clobber_overwrite_and_bypass(self):
        words = list(self.words)
        words[2], words[6] = 0x006A, 0x1C51  # R2 across ordinary BL.
        for source, edge in ((words, None), (self.words[:5]+(0x2600,)+self.words[5:],None),
                             (self.words,(2,10)), (self.words,(4,2))):
            with self.subTest(source=source, edge=edge), self.assertRaises(ValueError):
                self.prove(source, edge)


SOURCE = '''struct Unit { unsigned char unknown00[24]; unsigned short value; };
struct State { struct Unit *source, *target; unsigned char unknown08[30]; unsigned short flags; };
extern unsigned char func_080CDA4C(const void *);
extern unsigned int func_08002804(void);
int func_081315F8(struct State *state)
{
    int minimum, range;
    if (func_080CDA4C(state->target))
        return 0;
    minimum = state->target->value / 4;
    range = minimum * 2;
    if (state->flags & 16)
        return minimum + (range >> 1);
    return (short)func_08002804() % (range + 1) + minimum;
}
'''


class NativeTests(unittest.TestCase):
    def test_original_elf_report_replay_and_forgery(self):
        rom = os.environ.get('FFTA_ROM')
        if not rom or not Path(rom).is_file():
            self.skipTest('FFTA_ROM must reference the approved ROM')
        rom = Path(rom).resolve()
        self.assertEqual(hashlib.sha256(rom.read_bytes()).hexdigest(),
                         '43fc8204c6dceee58828aebc7af0c72eb807e99f35ad641c8bb0a4fa8b6edc19')
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH', Path(__file__).resolve().parents[1]/'build/tests'))
        scratch.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='odd_remainder_', dir=scratch) as directory:
            root = Path(directory)
            for name in ('src', 'include', 'config', 'symbols'):
                (root/name).mkdir()
            (root/'baserom.bin').symlink_to(rom)
            src = root/'src/081315F8.c'
            src.write_text(SOURCE)
            spans = [(0x08002804,0x08002824,10), (0x080CDA4C,0x080CDA64,12),
                     (0x081315F8,0x0813163A,30), (0x0814274C,0x0814274E,1),
                     (0x08142950,0x08142A1E,102)]
            (root/'config/functions.json').write_text(json.dumps([
                dict(rom=f'0x{start:08X}', end=f'0x{end:08X}', instrs=count, mode='thumb')
                for start,end,count in spans]))
            (root/'symbols/functions.txt').write_text(''.join(
                f'{start:08X} {end:08X} {end-start:5d} {count:3d} return\n'
                for start,end,count in spans))
            (root/'config/data_symbols.json').write_text('{}')
            address = 0x081315F8
            result = driver.build(root,address,selector=odd.SELECTOR)
            self.assertEqual(result['instructions'],30)
            self.assertEqual(len(result['body']),66)
            options = ['match.py', '081315F8', '--root', str(root), '--signed-runtime-profile', odd.SELECTOR]
            with patch.object(sys, 'argv', options), redirect_stdout(io.StringIO()):
                self.assertEqual(match.main(), 0)
            report = (root/'docs/match/081315F8.md').read_text()
            self.assertEqual(standing_premise.strip(report, root, address), driver.render(result))
            counted = status.collect(str(root), verify=True)
            self.assertEqual((counted[1], counted[3], counted[4]), (1, 66, []))
            with patch.object(sys, 'argv', options+['--switch-profile', 'two-constants-v2']):
                with self.assertRaisesRegex(SystemExit, 'isolated ordinary Thumb'):
                    match.main()
            self.assertTrue(match_evidence.report_matches(report,root,address))
            self.assertEqual(driver.selector_for_report(report),odd.SELECTOR)
            result['manifest']['operands']['positive_odd_divisor'] = [1,65535]
            self.assertFalse(report_fixtures.replay(driver.render(result),root,address))
            src.write_text('extern int func_08142950(int, int);\n'+SOURCE.replace(
                '(short)func_08002804() % (range + 1)', 'func_08142950((short)func_08002804(), range + 1)'))
            self.assertFalse(match_evidence.report_matches(report,root,address))
            with self.assertRaises(ValueError):
                driver.build(root,address,selector=odd.SELECTOR)
