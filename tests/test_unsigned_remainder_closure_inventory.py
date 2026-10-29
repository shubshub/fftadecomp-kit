"""Mixed signed/unsigned remainder proves target-state ABI/effects only."""
import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import shlex
import struct
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import match_evidence as evidence
import owner_admission_profile as owner
import zero_aware_remainder_inventory as pure
import zero_aware_remainder_shift_inventory as shift
import zero_aware_mixed_runtime_inventory as mixed
import umodsi3_profile as unsigned
import unsigned_remainder_closure_inventory as profile

A, ORDINARY = 0x08010000, 0x08020000
SOURCE = '''unsigned func_08010000(int left, int divisor, unsigned value, unsigned modulus)
{
    unsigned x = (unsigned)left + value;
    unsigned y = (unsigned)divisor + modulus;
    unsigned r = (unsigned)(left % divisor);
    return r + (value % modulus) + x * y + (unsigned)left + divisor + value + modulus;
}
'''


class RemainderClosureInventoryTests(unittest.TestCase):
    @staticmethod
    def indexes(rows):
        return ((json.dumps(rows, indent=2) + '\n').encode(),
            ''.join(f'{int(r["rom"],16):08X} {int(r["end"],16):08X} '
                f'{int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n' for r in rows).encode())

    @classmethod
    def setUpClass(cls):
        selected = os.environ.get('FFTA_ROM')
        if not selected or not Path(selected).is_file():
            raise unittest.SkipTest('FFTA_ROM must reference the approved ROM')
        approved = Path(selected).read_bytes()
        assert hashlib.sha256(approved).hexdigest() == '43fc8204c6dceee58828aebc7af0c72eb807e99f35ad641c8bb0a4fa8b6edc19'
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH', Path(__file__).resolve().parents[1] / 'build/tests'))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix='umod_closure_tests_', dir=scratch)
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.root = Path(cls.temporary.name)
        for name in ('src', 'include', 'config', 'symbols', 'build'):
            (cls.root / name).mkdir()
        (cls.root / 'src/08010000.c').write_text(SOURCE)
        cls.retained = Path(os.environ['FFTA_UMOD_CLOSURE_RETAIN']) if os.environ.get('FFTA_UMOD_CLOSURE_RETAIN') else None
        if cls.retained:
            cls.retained.mkdir(parents=True, exist_ok=True)
            (cls.retained / 'caller.c').write_text(SOURCE)
        args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
            objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        runner = match.Runner(match.DEFAULT_CC, root=cls.root, timeout=120)
        with runner.workspace() as workspace:
            cls.raw, _, original = match.compile_object(runner, workspace, args, cls.root, A, 'src/08010000.c')
            # This test-only linker constructs a native fixture, without adding
            # a mixed-runtime source/ELF admission path to match.link_calls.
            targets = profile.OPERATIONS
            undefined = {s['name'] for s in original['symbols'] if not s['section'] and s['bind'] == 1}
            assert undefined == set(targets)
            definitions = ['.syntax unified', '.thumb']
            for name, target in sorted(targets.items()):
                definitions += [f'.global {name}', f'.type {name}, %function',
                    f'.thumb_set {name}, 0x{target | 1:08X}']
            runner.write_text(f'{workspace}/f.known.s', '\n'.join(definitions) + '\n')
            runner.write_text(f'{workspace}/f.ld',
                f'SECTIONS {{ .text 0x{A:08X} : {{ *(.text) }} /DISCARD/ : {{ *(.comment) *(.note.GNU-stack) }} }}')
            q = shlex.quote(workspace)
            runner.sh(f'{args.assembler} -mthumb-interwork {q}/f.known.s -o {q}/f.known.o')
            runner.sh(f'{args.linker} --fatal-warnings --no-undefined --no-relax -T {q}/f.ld '
                f'-e func_08010000 {q}/f.o {q}/f.known.o -o {q}/f.elf')
            linked = match.elf_image(runner.read_binary(f'{workspace}/f.elf'))
            cls.body = linked['text']
            assert len(cls.body) == len(original['text'])
            symbol = next(s for s in original['symbols'] if s['name'] == 'func_08010000')
            assert symbol['type'] == 2 and symbol['value'] == 1 and symbol['size'] > 0
            cls.body = cls.body[:symbol['size']]
            if cls.retained:
                (cls.retained / 'original.o').write_bytes(cls.raw)
                (cls.retained / 'compiler.s').write_bytes(runner.read_binary(f'{workspace}/f.s'))
                (cls.retained / 'linked.elf').write_bytes(runner.read_binary(f'{workspace}/f.elf'))
            cls.original = original
        cls.rows = [{'rom': f'0x{A:08X}', 'end': f'0x{A+len(cls.body):08X}', 'mode': 'thumb', 'instrs': 0},
            {'rom': f'0x{ORDINARY:08X}', 'end': f'0x{ORDINARY+2:08X}', 'mode': 'thumb', 'instrs': 1},
            {'rom': '0x08142B28', 'end': '0x08142BE8', 'mode': 'thumb', 'instrs': 95},
            {'rom': '0x08142950', 'end': '0x08142A1E', 'mode': 'thumb', 'instrs': 102},
            {'rom': '0x0814274C', 'end': '0x0814274E', 'mode': 'thumb', 'instrs': 1}]
        mapping, _ = cls.indexes(cls.rows)
        refinement = owner.refine(cls.body, A, mapping)
        cls.rows[0]['instrs'] = refinement['instrs']
        cls.calls = {int(r['site'], 16): int(r['target'], 16) for r in refinement['calls']}
        assert set(cls.calls.values()) == set(targets.values())
        cls.mapping, cls.index = cls.indexes(cls.rows)
        rom = bytearray(approved); rom[A-match.ROM_BASE:A-match.ROM_BASE+len(cls.body)] = cls.body
        cls.rom = bytes(rom)
        cls.bindings = profile.bind_calls(cls.calls, cls.mapping, A, len(cls.body), len(cls.rom))
        for name, data in (('config/functions.json', cls.mapping), ('symbols/functions.txt', cls.index), ('baserom.bin', cls.rom)):
            (cls.root / name).write_bytes(data)
        cls.manifest, cls.instructions = profile.verify(cls.body, A, cls.rom, cls.mapping, cls.index,
            cls.calls, cls.bindings, selector=profile.SELECTOR)
        if cls.retained:
            for name, data in (('body.bin', cls.body), ('functions.json', cls.mapping), ('functions.txt', cls.index)):
                (cls.retained / name).write_bytes(data)
            (cls.retained / 'native-inventory.json').write_text(json.dumps(cls.manifest, indent=2) + '\n')
            (cls.retained / 'fixture.json').write_text(json.dumps({'ELF_type': original['type'],
                'calls': cls.calls, 'bindings': cls.bindings, 'synthetic_only': True,
                'source_or_ELF_admission': False, 'test_only_linker': True,
                'compiler': [match.DEFAULT_CC, match.DEFAULT_FLAGS]}, indent=2) + '\n')

    def native(self, **changes):
        values = dict(data=self.body, address=A, rom=self.rom, mapping=self.mapping, index=self.index,
            calls=self.calls, bindings=self.bindings, selector=profile.SELECTOR)
        values.update(changes)
        return profile.verify(**values)

    def machine(self, sequence):
        data = bytearray()
        for value in sequence:
            if type(value) is int:
                data += struct.pack('<H', value)
            else:
                target = {'mod': pure.remainder.ADDRESS, 'umod': unsigned.ADDRESS, 'ordinary': ORDINARY}.get(value) if type(value) is str else value[1]
                delta = target - (A + len(data)) - 4
                data += struct.pack('<HH', 0xF000 | ((delta >> 12) & 0x7FF), 0xF800 | ((delta >> 1) & 0x7FF))
        data = bytes(data)
        rows = copy.deepcopy(self.rows); rows[0]['end'] = f'0x{A+len(data):08X}'
        mapping, _ = self.indexes(rows)
        refinement = owner.refine(data, A, mapping); rows[0]['instrs'] = refinement['instrs']
        mapping, index = self.indexes(rows)
        calls = {int(r['site'],16): int(r['target'],16) for r in refinement['calls']}
        bindings = profile.bind_calls(calls, mapping, A, len(data), len(self.rom))
        rom = bytearray(self.rom); rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)] = data
        return self.native(data=data, rom=bytes(rom), mapping=mapping, index=index, calls=calls, bindings=bindings)

    def test_natural_unrestricted_variable_remainders_ET_REL_API_and_CLI(self):
        self.assertEqual(struct.unpack_from('<H',self.raw,16)[0],1)
        self.assertEqual(set(self.bindings.values()),{'__modsi3','__umodsi3'})
        self.assertTrue(self.manifest['complete_native_proof'] and self.manifest['inventory_only'])
        self.assertFalse(self.manifest['source_or_ELF_admission'])
        self.assertFalse(self.manifest['arithmetic_C_equivalence_proved'])
        self.assertFalse(self.manifest['result_ranges_proved'])
        self.assertFalse(self.manifest['universal_termination_proved'])
        self.assertEqual(self.manifest['numeric_operand_preconditions'],[])
        self.assertIsNone(self.manifest['entry_stack_contract'])
        self.assertIsNone(self.manifest['ordinary_call_ABI'])
        self.assertEqual(self.manifest['ordinary_calls'],[])
        closure=dict(self.manifest['native_runtime_closure'])
        self.assertEqual(closure[unsigned.ADDRESS]['returns'],[0x08142B32,0x08142BAE,0x08142BDC,0x08142BE6])
        self.assertTrue(all(not p['writes'] and not p['stack_reads'] for p in closure.values()))
        self.assertEqual(self.manifest['frame']['external_calls'],'complete-native-callee-preservation-v1')
        run=subprocess.run([sys.executable,str(Path(profile.__file__)),'--profile',profile.SELECTOR,
            '--rom',str(self.root/'baserom.bin'),'--mapping',str(self.root/'config/functions.json'),
            '--index',str(self.root/'symbols/functions.txt'),f'{A:08X}'],capture_output=True,text=True)
        self.assertEqual(run.returncode,0,run.stderr)
        self.assertEqual(json.loads(run.stdout),json.loads(json.dumps(self.manifest)))
        if self.retained:(self.retained/'native-inventory-cli.json').write_text(run.stdout)

    def test_arbitrary_scalar_and_zero_divisors_have_no_numeric_gate_or_result_facts(self):
        for prefix in ([],[0x2100],[0x2100,0x2000]):
            with self.subTest(prefix=prefix):
                manifest,_=self.machine([0xB510,0xB081]+prefix+['mod',0x2100,'umod',0xB001,0xBC10,0xBC02,0x4708])
                self.assertEqual(manifest['numeric_operand_preconditions'],[])
                self.assertEqual(manifest['frame']['maximum_frame_bytes'],12)
                self.assertIn('no quotient, remainder, numeric',manifest['caller_facts'])
        # A runtime result cannot supply the caller entry-return token.
        with self.assertRaises(ValueError):
            self.machine([0xB510,0xB081,'mod','umod',0xB001,0xBC10,0xBC02,0x4700])

    def test_only_exact_both_runtime_calls_and_complete_bindings(self):
        for site in self.calls:
            bindings=dict(self.bindings);bindings.pop(site)
            with self.subTest(site=site),self.assertRaises(ValueError):self.native(bindings=bindings)
        for name in ('__modsi3','__umodsi3'):
            site=next(s for s,n in self.bindings.items() if n==name)
            bindings=dict(self.bindings);bindings[site]='func_'+f'{self.calls[site]:08X}'
            with self.subTest(name=name),self.assertRaises(ValueError):self.native(bindings=bindings)
        for suffix in (['mod'],['umod'],['mod','umod','ordinary'],['mod','umod',('call',unsigned.ADDRESS+2)],
                ['mod','umod',('call',0x0814274C)],['mod','umod',('call',0x081426B8)]):
            with self.subTest(suffix=suffix),self.assertRaises(ValueError):
                self.machine([0xB510]+suffix+[0xBC10,0xBC02,0x4708])
        calls=dict(self.calls);calls.pop(next(iter(calls)))
        with self.assertRaises(ValueError):self.native(calls=calls)

    def test_runtime_identity_zero_hook_all_returns_and_dual_indices_exact(self):
        for site in (unsigned.ADDRESS,0x08142BE0,0x08142B32,0x08142BAE,0x08142BDC,0x08142BE6,
                pure.remainder.ADDRESS,0x08142A16,0x08142A12,0x08142A1C,0x0814274C):
            rom=bytearray(self.rom);rom[site-match.ROM_BASE]^=1
            with self.subTest(site=site),self.assertRaises(ValueError):self.native(rom=bytes(rom))
        wrong=self.index.replace(b'08142B28 08142BE8 192 95',b'08142B28 08142BE8 192 96')
        self.assertNotEqual(wrong,self.index)
        with self.assertRaises(ValueError):self.native(index=wrong)
        rows=copy.deepcopy(self.rows);rows[2]['instrs']=96
        mapping,index=self.indexes(rows)
        with self.assertRaises(ValueError):self.native(mapping=mapping,index=index)
        rows=copy.deepcopy(self.rows);rows.append(copy.deepcopy(rows[2]));mapping,index=self.indexes(rows)
        with self.assertRaises(ValueError):self.native(mapping=mapping,index=index)

    def test_frame_local_bounds_saved_slots_SP_alias_and_incoming_words(self):
        for body in ([0x9000], [0xB081,0x9001,0xB001], [0xB081,0x9803,0xB001],
                [0x4668], [0xB081,0xA800], [0x4685], [0xB081]):
            with self.subTest(body=body),self.assertRaises(ValueError):
                self.machine([0xB510]+body+['mod','umod',0xBC10,0xBC02,0x4708])
        self.machine([0xB510,0xB081,0x9000,'mod','umod',0xB001,0xBC10,0xBC02,0x4708])

    def test_fresh_manifest_explicit_selector_and_old_defaults(self):
        for key in ('structural_guarantee','arithmetic_C_equivalence_proved','native_runtime_frames',
                'native_runtime_closure','runtime_spans','frame','calls','numeric_operand_preconditions'):
            changed=copy.deepcopy(self.manifest);changed[key]='forged'
            with self.subTest(key=key),self.assertRaisesRegex(ValueError,'manifest differs'):self.native(manifest=changed)
        with self.assertRaises(ValueError):self.native(selector=pure.SELECTOR)
        with self.assertRaises(ValueError):match.verify_leaf_instructions(self.body,A,True,self.calls)
        with self.assertRaises(ValueError):pure.verify(self.body,A,self.rom,self.mapping,self.index,self.calls,self.bindings,selector=pure.SELECTOR)


if __name__=='__main__':unittest.main()
