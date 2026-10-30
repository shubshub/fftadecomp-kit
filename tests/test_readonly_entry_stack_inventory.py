"""Explicit incoming word0 is read-only and carries no register or numeric provenance."""
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
import zero_aware_unsigned_quotient_inventory as core
import zero_aware_unsigned_framed_inventory as profile
import readonly_entry_stack_profile as entry_stack
import local_long_branch_profile as frame
import owner_graph_profile as graph

A, ORDINARY = 0x08010000, 0x08020000
SOURCE = '''extern int func_08020000(unsigned, int, int, int, int, int, int);
int func_08010000(unsigned value, unsigned divisor, int modulus, int bias, int extra)
{
    return (short)func_08020000(value / divisor, bias, extra, modulus, 3, 4, 5) % modulus;
}
'''


class ReadonlyEntryStackTests(unittest.TestCase):
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
        cls.temporary = tempfile.TemporaryDirectory(prefix='entry_stack_tests_', dir=scratch)
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.root = Path(cls.temporary.name)
        for name in ('src', 'include', 'config', 'symbols', 'build'):
            (cls.root / name).mkdir()
        (cls.root / 'src/08010000.c').write_text(SOURCE)
        cls.retained = Path(os.environ['FFTA_ENTRY_STACK_RETAIN']) if os.environ.get('FFTA_ENTRY_STACK_RETAIN') else None
        if cls.retained:
            cls.retained.mkdir(parents=True, exist_ok=True)
            (cls.retained / 'caller.c').write_text(SOURCE)
        args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
            objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        runner = match.Runner(match.DEFAULT_CC, root=cls.root, timeout=120)
        with runner.workspace() as workspace:
            cls.raw, _, original = match.compile_object(runner, workspace, args, cls.root, A, 'src/08010000.c')
            if cls.retained:
                (cls.retained / 'original.o').write_bytes(cls.raw)
                (cls.retained / 'compiler.s').write_bytes(runner.read_binary(f'{workspace}/f.s'))
            # This test-only linker constructs a native fixture, without adding
            # a mixed-runtime source/ELF admission path to match.link_calls.
            targets = dict(core.OPERATIONS, func_08020000=ORDINARY)
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
            # Section alignment after the complete ELF function symbol is not owned.
            cls.body = cls.body[:symbol['size']]
            if cls.retained:
                (cls.retained / 'original.o').write_bytes(cls.raw)
                (cls.retained / 'compiler.s').write_bytes(runner.read_binary(f'{workspace}/f.s'))
                (cls.retained / 'linked.elf').write_bytes(runner.read_binary(f'{workspace}/f.elf'))
            cls.original = original
        cls.rows = [{'rom': f'0x{A:08X}', 'end': f'0x{A+len(cls.body):08X}', 'mode': 'thumb', 'instrs': 0},
            {'rom': f'0x{ORDINARY:08X}', 'end': f'0x{ORDINARY+2:08X}', 'mode': 'thumb', 'instrs': 1},
            {'rom': '0x08142AB0', 'end': '0x08142B28', 'mode': 'thumb', 'instrs': 59},
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
                target = {'mod': pure.remainder.ADDRESS, 'udiv': core.UDIV, 'ordinary': ORDINARY}.get(value) if type(value) is str else value[1]
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

    @staticmethod
    def asr(destination=0, source=2, amount=16):
        return 0x1000 | ((amount & 31) << 6) | (source << 3) | destination

    def frame_only(self, sequence, policy=True):
        data = b''.join(struct.pack('<H', word) for word in sequence)
        import capstone
        decoder = capstone.Cs(capstone.CS_ARCH_ARM, capstone.CS_MODE_THUMB)
        decoder.detail = True
        instructions = {i.address:i for i in decoder.disasm(data, A)}
        edges = {site: (() if i.mnemonic == 'bx' else (site+i.size,)) for site,i in instructions.items()}
        kwargs = {'entry_stack_policy': {'schema':entry_stack.SCHEMA,'words':[0]}} if policy else {}
        return frame.prove_frame(instructions,edges,A,{}, {},stack_aliases=True,**kwargs)

    def test_natural_five_argument_O2_ET_REL_API_and_CLI(self):
        self.assertEqual(struct.unpack_from('<H', self.raw, 16)[0], 1)
        self.assertEqual(set(self.bindings.values()), {'__udivsi3','__modsi3','func_08020000'})
        self.assertTrue(self.manifest['complete_native_proof'] and self.manifest['inventory_only'])
        self.assertFalse(self.manifest['source_or_ELF_admission'])
        self.assertIn('conditional', self.manifest['ordinary_call_premise'])
        self.assertIsNone(self.manifest['ordinary_call_stack_bound'])
        self.assertTrue(any(match.thumb_stack_adjustment(i) == -3 for i in self.instructions))
        reads = self.manifest['frame']['entry_stack']['reads']
        self.assertEqual(len(reads),1)
        self.assertEqual(reads[0][1:3],[0,4])
        frames = dict(self.manifest['native_runtime_frames'])
        self.assertEqual({site:p['maximum_additional_stack_bytes'] for site,p in frames.items()},
            {0x0814274C:0,core.UDIV:4,pure.remainder.ADDRESS:8})
        self.assertTrue(all(not p['caller_memory_writes'] and not p['caller_stack_reads'] for p in frames.values()))
        run = subprocess.run([sys.executable,str(Path(profile.__file__)),'--profile',profile.SELECTOR,
            '--rom',str(self.root/'baserom.bin'),'--mapping',str(self.root/'config/functions.json'),
            '--index',str(self.root/'symbols/functions.txt'),f'{A:08X}'],capture_output=True,text=True)
        self.assertEqual(run.returncode,0,run.stderr)
        self.assertEqual(json.loads(run.stdout),json.loads(json.dumps(self.manifest)))
        if self.retained:(self.retained/'native-inventory-cli.json').write_text(run.stdout)

    def test_old_default_refusal_and_exact_versioned_optin(self):
        sequence = [0xB510,0xB083,0x9805,0xB003,0xBC10,0xBC02,0x4708]
        with self.assertRaisesRegex(ValueError,'local branch access leaves its established frame'):
            self.frame_only(sequence,False)
        proved = self.frame_only(sequence)
        self.assertEqual(proved['entry_stack']['reads'],[[A+4,0,4,'0598']])
        for policy in ({'schema':entry_stack.SCHEMA,'words':[4]}, {'schema':entry_stack.SCHEMA,'words':[False]},
                {'schema':entry_stack.SCHEMA,'words':[0,4]}, {'schema':'other','words':[0]},True):
            with self.subTest(policy=policy),self.assertRaises(ValueError):entry_stack.validate(policy)
        for module in (core,shift,mixed):
            with self.subTest(module=module.__name__),self.assertRaises(ValueError):
                module.verify(self.body,A,self.rom,self.mapping,self.index,self.calls,self.bindings,selector=module.SELECTOR)
        with self.assertRaises(ValueError):match.verify_leaf_instructions(self.body,A,True,self.calls)

    def test_words_outside_declared_entry_word_and_writes_remain_rejected(self):
        prefix,tail=[0xB510,0xB083],[0xB003,0xBC10,0xBC02,0x4708]
        for access in (0x9806,0x9005,0x9006,0x9003):
            with self.subTest(access=access),self.assertRaises(ValueError):self.frame_only(prefix+[access]+tail)
        # Exact decoder also refuses non-SP/indexed loads, STR, and a below-entry displacement.
        import capstone
        md=capstone.Cs(capstone.CS_ARCH_ARM,capstone.CS_MODE_THUMB);md.detail=True
        for encoded in (0x5808,0x6808,0x9005,0x9804):
            instruction=next(md.disasm(struct.pack('<H',encoded),A))
            with self.subTest(encoded=encoded),self.assertRaises(ValueError):
                entry_stack.read_word(instruction,5,{'schema':entry_stack.SCHEMA,'words':[0]})

    def test_dynamic_SP_saved_slot_return_and_alias_gates_remain_mandatory(self):
        prefix=[0xB510,0xB083,0x9805]
        tail=[0xB003,0xBC10,0xBC02,0x4708]
        for sequence in (prefix+[0x4685]+tail, prefix+[0x4485]+tail,
                prefix+[0x9003]+tail, prefix+[0xB002,0xBC10,0xBC02,0x4708],
                [0xB510,0xB083,0x9805,0xB003,0xBC10,0x4604,0xBC02,0x4708],
                [0xB510,0xB083,0x9805,0xB003,0xBC10,0xBC02,0x4700]):
            with self.subTest(sequence=sequence),self.assertRaises(ValueError):self.frame_only(sequence)
        for sequence in ([0xB510,0xB083,0xA800,'ordinary','udiv',self.asr(),'mod',0xB003,0xBC10,0xBC02,0x4708],):
            with self.assertRaises(ValueError):self.machine(sequence)

    def test_incoming_scalar_has_no_saved_register_or_entry_return_token(self):
        for sequence in ([0xB510,0xB083,0x9805,0x9003,0xB003,0xBC10,0xBC02,0x4708],
                [0xB510,0xB083,0x9805,0xB003,0xBC10,0xBC02,0x4700]):
            with self.subTest(sequence=sequence),self.assertRaises(ValueError):self.frame_only(sequence)
        # An incoming scalar can be used normally; its contents remain unknown.
        proved=self.frame_only([0xB510,0xB083,0x9805,0xB003,0xBC10,0xBC02,0x4708])
        self.assertEqual(proved['entry_stack']['loaded_value'],'unknown scalar; no provenance facts')

    def test_MOD_all_paths_shift_and_call_clobber_are_unchanged(self):
        prefix=[0xB510,0xB083,0x9805,'udiv']
        tail=['mod',0xB003,0xBC10,0xBC02,0x4708]
        for body in ([],[self.asr(),'ordinary'],[0x9805], [self.asr(0,2,15)]):
            with self.subTest(body=body),self.assertRaisesRegex(ValueError,'signed16 r0|actual exact bounded immediate shift'):
                self.machine(prefix+body+tail)
        self.machine(prefix+[self.asr()]+tail)
        with self.assertRaises(ValueError):
            self.machine(prefix+[0x2A00,0xD001,self.asr(),0xE000,0x9805]+tail)

    def test_exact_bindings_canonical_closure_and_fresh_manifest(self):
        for site in self.calls:
            bindings=dict(self.bindings);bindings.pop(site)
            with self.subTest(site=site),self.assertRaises(ValueError):self.native(bindings=bindings)
        for site in (core.UDIV,0x08142B20,0x0814274C,0x08142A16):
            rom=bytearray(self.rom);rom[site-match.ROM_BASE]^=1
            with self.subTest(site=site),self.assertRaises(ValueError):self.native(rom=bytes(rom))
        for key in ('entry_stack_contract','frame','native_runtime_frames','native_runtime_closure','operand_shift_origins'):
            forged=copy.deepcopy(self.manifest);forged[key]='forged'
            with self.subTest(key=key),self.assertRaisesRegex(ValueError,'manifest differs'):self.native(manifest=forged)
        bad_index=self.index.replace(b'08142AB0 08142B28 120 59',b'08142AB0 08142B28 120 60')
        with self.assertRaises(ValueError):self.native(index=bad_index)
        for target in (0x0814274C,0x081426B8,core.UDIV+2):
            with self.subTest(target=target),self.assertRaises(ValueError):
                self.machine([0xB510,0xB083,0x9805,'udiv',self.asr(),'mod',('call',target),0xB003,0xBC10,0xBC02,0x4708])


if __name__ == '__main__':unittest.main()
