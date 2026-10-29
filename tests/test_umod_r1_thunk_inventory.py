"""Natural modulo48/callback compiler evidence and focused fail-closed boundaries."""
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
import umod_r1_thunk_inventory as profile
import function_thunk_profile as thunks
import match
import match_evidence as evidence
import owner_admission_profile as owner
import owner_graph_profile as graph

A = 0x08010000
SOURCE = '''struct Item;
typedef void (*Callback)(struct Item *);
struct Item { Callback callback; unsigned char flags; unsigned char counter; };
void func_08010000(struct Item *item)
{
    unsigned flags = item->flags;
    if (flags & 2)
        item->counter %= 48u;
    if (flags & 1)
        item->callback(item);
}
'''


class UmodR1ThunkInventoryTests(unittest.TestCase):
    @staticmethod
    def indexes(rows):
        return ((json.dumps(rows, indent=2)+'\n').encode(), ''.join(
            f'{int(r["rom"],16):08X} {int(r["end"],16):08X} '
            f'{int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n'
            for r in rows).encode())

    @classmethod
    def setUpClass(cls):
        approved = Path(os.environ['FFTA_ROM']).read_bytes()
        assert hashlib.sha256(approved).hexdigest() == '43fc8204c6dceee58828aebc7af0c72eb807e99f35ad641c8bb0a4fa8b6edc19'
        cls.retained = Path(os.environ['FFTA_UMOD_R1_RETAIN'])
        cls.retained.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix='umod_r1_', dir=os.environ['FFTA_TEST_SCRATCH'])
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.root = Path(cls.temporary.name)
        for directory in ('src', 'include', 'config', 'symbols', 'build'):
            (cls.root/directory).mkdir()
        (cls.root/'src/08010000.c').write_text(SOURCE)
        if os.environ.get('FFTA_UMOD_R1_REUSE') == '1':
            assert (cls.retained/'caller.c').read_text() == SOURCE
            cls.raw = (cls.retained/'original.o').read_bytes()
            cls.body = (cls.retained/'body.bin').read_bytes()
        else:
            assert not (cls.retained/'original.o').exists(), 'natural compiler fixture already exists'
            (cls.retained/'caller.c').write_text(SOURCE)
            args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
            runner = match.Runner(args.cc, root=cls.root, timeout=120)
            with runner.workspace() as workspace:
                cls.raw, _, original = match.compile_object(runner, workspace, args, cls.root, A, 'src/08010000.c')
                (cls.retained/'original.o').write_bytes(cls.raw)
                (cls.retained/'compiler.s').write_bytes(runner.read_binary(workspace+'/f.s'))
                script = f'SECTIONS {{ .text 0x{A:08X} : {{ *(.text) *(.glue_7) *(.glue_7t) }} '
                script += '.data 0 : { *(.data) } .bss 0 : { *(.bss) } .ARM.attributes 0 : { *(.ARM.attributes) } '
                script += '.unexpected 0 : { *(.vfp11_veneer) *(.v4_bx) *(.iplt) *(.igot.plt) } '
                script += '.rel.iplt 0 : { *(.rel.iplt) } ASSERT(SIZEOF(.unexpected)==0,"unexpected stubs") '
                script += 'ASSERT(SIZEOF(.rel.iplt)==0,"unexpected relocations") /DISCARD/ : { *(.comment) *(.note.GNU-stack) } }'
                runner.write_text(workspace+'/f.ld', script)
                # Symbol metadata only. All executable bytes come from the
                # unmodified natural C object and standard linker relocations.
                aliases = {'__umodsi3': profile.remainder.ADDRESS, profile.THUNK: profile.THUNK_ADDRESS}
                known = '.syntax unified\n.thumb\n'+''.join(
                    f'.global {name}\n.type {name}, %function\n.thumb_set {name}, 0x{target|1:08X}\n'
                    for name, target in aliases.items())
                runner.write_text(workspace+'/f.known.s', known)
                q = shlex.quote(workspace)
                runner.sh(f'{args.assembler} -mthumb-interwork {q}/f.known.s -o {q}/f.known.o')
                runner.sh(f'{args.linker} --fatal-warnings --no-undefined --no-relax --orphan-handling=error '
                    f'-T {q}/f.ld -e func_08010000 {q}/f.o {q}/f.known.o -o {q}/f.elf')
                linked = runner.read_binary(workspace+'/f.elf')
                (cls.retained/'linked.elf').write_bytes(linked)
                image = match.elf_image(linked)
                match.allocated_text_only(image)
                symbol, offset = match.function_record(image, 'func_08010000', A, True)
                assert original['type'] == 1 and image['type'] == 2 and not image['relocations'] and offset == 0
                cls.body = image['text'][:symbol['size']]
                assert len(image['text']) == len(original['text'])
                assert image['text'][symbol['size']:] == original['text'][symbol['size']:] in (b'', b'\xc0\x46')
                expected = bytearray(original['text'][:symbol['size']])
                decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
                decoder.detail = True
                relocations = []
                for section_index in original['relocations']:
                    section = original['sections'][section_index]
                    symbols = original['symbol_tables'][section[6]]
                    for position in range(0, section[5], 8):
                        site, info = struct.unpack_from('<II', original['section_data'][section_index], position)
                        target = symbols[info >> 8]
                        assert info & 255 == 10 and target['name'] in aliases and not target['section']
                        instruction = next(decoder.disasm(cls.body[site:site+4], A+site))
                        assert instruction.mnemonic == 'bl' and instruction.size == 4
                        assert instruction.operands[0].imm == aliases[target['name']]
                        expected[site:site+4] = cls.body[site:site+4]
                        relocations.append([site, info & 255, target['name']])
                assert bytes(expected) == cls.body and {r[2] for r in relocations} == set(aliases)
                (cls.retained/'compiler-evidence.json').write_text(json.dumps({
                    'ET_REL': original['type'], 'linked_type': image['type'], 'compiler': args.cc,
                    'flags': args.flags, 'compiler_invocations': 1, 'relocations': relocations,
                    'only_standard_linker_relocations_changed': True, 'unmodified_natural_C': True,
                    'source_or_ELF_admission': False}, indent=2)+'\n')
                (cls.retained/'body.bin').write_bytes(cls.body)
        cls.rows = [
            {'rom': f'0x{A:08X}', 'end': f'0x{A+len(cls.body):08X}', 'mode': 'thumb', 'instrs': 0},
            {'rom': '0x08142B28', 'end': '0x08142BE8', 'mode': 'thumb', 'instrs': 95},
            {'rom': '0x0814274C', 'end': '0x0814274E', 'mode': 'thumb', 'instrs': 1},
            {'rom': f'0x{profile.THUNK_ADDRESS:08X}', 'end': f'0x{profile.THUNK_ADDRESS+4:08X}', 'mode': 'thumb', 'instrs': 2}]
        mapping, _ = cls.indexes(cls.rows)
        cls.rows[0]['instrs'] = owner.refine(cls.body, A, mapping)['instrs']
        cls.mapping, cls.index = cls.indexes(cls.rows)
        refinement = owner.refine(cls.body, A, cls.mapping)
        cls.ins, cls.edges, _, cls.calls, _ = graph.graph(cls.body, A, refinement)
        cls.bindings = profile.bind_calls(cls.calls, cls.mapping, A, len(cls.body), len(approved))
        rom = bytearray(approved[:0x142BE8])
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(cls.body)] = cls.body
        cls.rom = bytes(rom)
        for name, data in (('body.bin', cls.body), ('rom.bin', cls.rom),
                ('functions.json', cls.mapping), ('functions.txt', cls.index)):
            (cls.retained/name).write_bytes(data)
        cls.manifest, cls.instructions = profile.verify(cls.body, A, cls.rom, cls.mapping,
            cls.index, cls.calls, cls.bindings, selector=profile.SELECTOR)
        (cls.retained/'fixture-proof.json').write_text(json.dumps(cls.manifest, indent=2)+'\n')

    def native(self, **changes):
        values = dict(data=self.body, address=A, rom=self.rom, mapping=self.mapping,
            index=self.index, calls=self.calls, bindings=self.bindings, selector=profile.SELECTOR)
        values.update(changes)
        return profile.verify(**values)

    @staticmethod
    def encode(sequence):
        data = bytearray()
        for value in sequence:
            if type(value) is int:
                data += struct.pack('<H', value)
            else:
                target = profile.remainder.ADDRESS if value == 'umod' else profile.THUNK_ADDRESS
                delta = target-A-len(data)-4
                data += struct.pack('<HH', 0xF000|((delta >> 12)&0x7FF), 0xF800|((delta >> 1)&0x7FF))
        return data

    def machine(self, sequence, tail=b''):
        data = bytes(self.encode(sequence))+tail
        rows = copy.deepcopy(self.rows)
        rows[0]['end'] = f'0x{A+len(data):08X}'
        mapping, _ = self.indexes(rows)
        refinement = owner.refine(data, A, mapping)
        rows[0]['instrs'] = refinement['instrs']
        mapping, index = self.indexes(rows)
        calls = {int(r['site'],16):int(r['target'],16) for r in refinement['calls']}
        bindings = profile.bind_calls(calls, mapping, A, len(data), len(self.rom))
        rom = bytearray(self.rom)
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)] = data
        return self.native(data=data, rom=bytes(rom), mapping=mapping, index=index, calls=calls, bindings=bindings)

    def test_natural_O2_ET_REL_modulo48_callback_API_and_CLI(self):
        self.assertEqual(struct.unpack_from('<H', self.raw, 16)[0], 1)
        self.assertEqual(set(self.bindings.values()), {'__umodsi3', '_call_via_r1'})
        self.assertEqual([value for _,value in self.manifest['caller_divisors']], [48])
        self.assertEqual(self.manifest['local_bytes'], 0)
        self.assertEqual(self.manifest['frame']['maximum_frame_bytes'], 12)
        self.assertEqual(self.manifest['frame']['preserved'], 'r4-r11,sp,entry-lr')
        self.assertTrue(self.manifest['complete_native_structural_proof'])
        for key in ('source_or_ELF_admission', 'arithmetic_C_equivalence', 'memory_safety_claim',
                'termination_claim', 'indirect_callee_native_proof', 'indirect_callee_effect_proof'):
            self.assertFalse(self.manifest[key])
        self.assertEqual(self.manifest['numeric_input_preconditions'], [])
        self.assertEqual(self.manifest['ordinary_calls'], [])
        self.assertEqual(set(dict(self.manifest['native_runtime_closure'])), {profile.remainder.ADDRESS, profile.umod.ZERO})
        run = subprocess.run([sys.executable, str(Path(profile.__file__)), '--profile', profile.SELECTOR,
            '--rom', str(self.retained/'rom.bin'), '--mapping', str(self.retained/'functions.json'),
            '--index', str(self.retained/'functions.txt'), f'{A:08X}'], capture_output=True, text=True)
        (self.retained/'fixture-cli-return.json').write_text(json.dumps({'exit':run.returncode,'stderr':run.stderr})+'\n')
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertEqual(json.loads(run.stdout), json.loads(json.dumps(self.manifest)))
        (self.retained/'fixture-cli.json').write_text(run.stdout)

    def test_wrong_runtime_target_alias_and_non_r1_thunk_refuse(self):
        for target in (profile.remainder.ADDRESS+1, profile.remainder.ADDRESS+2,
                profile.umod.ZERO, match.UDIVSI3_ADDRESS, match.divsi3.ADDRESS, match.modsi3.ADDRESS,
                profile.THUNK_ADDRESS+1, thunks.ALIASES['_call_via_r0'], thunks.ALIASES['_call_via_r2'], A+2):
            calls = dict(self.calls)
            site = next(site for site,target in calls.items() if target == profile.remainder.ADDRESS)
            calls[site] = target
            with self.subTest(target=target), self.assertRaises(ValueError):
                profile.bind_calls(calls, self.mapping, A, len(self.body), len(self.rom))

    def test_runtime_zero_hook_and_thunk_actual_identity_refuse(self):
        for site in (profile.remainder.ADDRESS, 0x08142BE0, profile.umod.ZERO, profile.THUNK_ADDRESS):
            rom = bytearray(self.rom);rom[site-match.ROM_BASE] ^= 1
            with self.subTest(site=site), self.assertRaises(ValueError):self.native(rom=bytes(rom))

    def test_non_r1_thunk_refuses_with_actual_UMOD_preserved(self):
        for target in (thunks.ALIASES['_call_via_r0'], thunks.ALIASES['_call_via_r2']):
            calls = dict(self.calls)
            site = next(site for site, destination in calls.items() if destination == profile.THUNK_ADDRESS)
            calls[site] = target
            with self.subTest(target=target), self.assertRaises(ValueError):
                profile.bind_calls(calls, self.mapping, A, len(self.body), len(self.rom))

    def test_zero_unknown_wrong_and_call_killed_divisors_refuse(self):
        for middle in ([], [0x2100], [0x212F], [0x2130, 'thunk']):
            sequence = [0xB530, 0x1C04]+middle+['umod']
            if 'thunk' not in middle:sequence += [0x6821, 0x1C20, 'thunk']
            sequence += [0xBC30, 0xBC01, 0x4700]
            with self.subTest(middle=middle), self.assertRaisesRegex(ValueError, 'constant|divisor'):
                self.machine(sequence)

    def test_bypassed_divisor_definition_refuses(self):
        with self.assertRaisesRegex(ValueError, 'constant'):
            self.machine([0xB530, 0x1C04, 0x2800, 0xD000, 0x2130, 'umod', 0x6821, 0x1C20, 'thunk', 0xBC30, 0xBC01, 0x4700])

    def test_SP_export_entry_access_allocations_and_block_transfer_refuse(self):
        for instruction in (0x4668, 0x9803, 0x9000, 0xB081, 0xC810):
            with self.subTest(instruction=instruction), self.assertRaises(ValueError):
                self.machine([0xB530, 0x1C04, instruction, 0x2130, 'umod', 0x6821, 0x1C20, 'thunk', 0xBC30, 0xBC01, 0x4700])

    def test_unbalanced_return_and_callee_saved_clobber_refuse(self):
        for suffix in ([0xBC10, 0xBC01, 0x4700], [0xBC30, 0x2400, 0xBC01, 0x4700]):
            with self.subTest(suffix=suffix), self.assertRaises(ValueError):
                self.machine([0xB530, 0x1C04, 0x2130, 'umod', 0x6821, 0x1C20, 'thunk']+suffix)

    def test_cycles_interrupts_and_unowned_literal_tail_refuse(self):
        for extra,tail in (([0x2800,0xD0FE],b''), ([0xDF00],b''), ([],b'\x78\x56\x34\x12')):
            with self.subTest(extra=extra,tail=tail.hex()), self.assertRaises(ValueError):
                self.machine([0xB530, 0x1C04, 0x2130, 'umod', 0x6821, 0x1C20, 'thunk']+extra+[0xBC30,0xBC01,0x4700],tail)

    def test_complete_calls_dual_indices_and_explicit_selector_refuse(self):
        calls = dict(self.calls);calls.pop(next(iter(calls)))
        with self.assertRaises(ValueError):self.native(calls=calls)
        bindings = dict(self.bindings);bindings[next(iter(bindings))] = 'func_08142B28'
        with self.assertRaises(ValueError):self.native(bindings=bindings)
        rows = copy.deepcopy(self.rows);rows[0]['instrs'] -= 1
        mapping,index = self.indexes(rows)
        with self.assertRaises(ValueError):self.native(mapping=mapping,index=index)
        for selector in (None, 'canonical-thunks-v1', profile.umod.SELECTOR):
            with self.subTest(selector=selector), self.assertRaises(ValueError):self.native(selector=selector)
        with self.assertRaises(ValueError):self.native(data=bytearray(self.body))

    def test_existing_defaults_and_C_ELF_admission_remain_closed(self):
        with self.assertRaises(ValueError):profile.umod.bind_calls(self.calls,self.mapping,A,len(self.body),len(self.rom))
        with self.assertRaises(ValueError):match.verify_leaf_instructions(self.body,A,True,self.calls)
        report = f'# {A:08X}\n* verification: `{profile.SCHEMA}`\n**MATCH - byte identical**\n'
        self.assertFalse(owner.selected(report))
        self.assertFalse(thunks.selected(report))
        self.assertFalse(evidence.report_matches(report,self.root,A))


if __name__ == '__main__':
    unittest.main()
