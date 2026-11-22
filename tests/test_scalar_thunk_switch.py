"""A distinct scalar switch policy authenticates canonical R3 call boundaries."""
import copy
import json
import os
from pathlib import Path
import struct
import subprocess
import tempfile
import unittest

import match
import owner_admission_profile as owner
import function_thunk_profile as thunk
import framed_switch_inventory as scalar
from test_switch_constants import assemble, fixed_args

A = 0x08010000


class ScalarThunkSwitchTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(dir=os.environ['FFTA_TEST_SCRATCH'])
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)

    def fixture(self, access='', allocate=True, indirect=True):
        allocation = 'sub sp,#4' if allocate else ''
        restoration = 'add sp,#4' if allocate else ''
        callback = 'bl _call_via_r3' if indirect else 'bl func_08001000'
        assembly = f'''.syntax unified
.arch armv4t
.thumb
.text
.global func_08010000
.type func_08010000,%function
.thumb_func
func_08010000:
push {{lr}}
{allocation}
{access}
cmp r0,#1
bhi .Ldefault
lsls r0,r0,#2
ldr r1,.Lpointer
adds r0,r0,r1
ldr r0,[r0]
mov pc,r0
.balign 4,0
.Lpointer:
.word .Ltable
.Ltable:
.word .Lcase0
.word .Lcase1
.Lcase0:
ldr r3,.Lobject
ldr r3,[r3]
{callback}
b .Ldone
.Lcase1:
bl func_08001000
b .Ldone
.Ldefault:
movs r0,#0
.Ldone:
{restoration}
pop {{r1}}
bx r1
.balign 4,0
.Lobject:
.word g_dispatch
.size func_08010000,.-func_08010000
'''
        original = assemble(self.root, assembly)
        known = self.root/'known.s'
        known.write_text('''.syntax unified
.thumb
.global _call_via_r3
.type _call_via_r3,%function
.thumb_set _call_via_r3,0x08142251
.global func_08001000
.type func_08001000,%function
.thumb_set func_08001000,0x08001001
.global g_dispatch
.type g_dispatch,%object
.set g_dispatch,0x02000000
''')
        subprocess.run(['arm-none-eabi-as',str(known),'-o',str(self.root/'known.o')],
                       check=True,capture_output=True)
        subprocess.run(['arm-none-eabi-ld','--no-undefined','--no-relax',
            f'-Ttext=0x{A:08X}','-e','func_08010000',str(self.root/'f.o'),
            str(self.root/'known.o'),'-o',str(self.root/'f.elf')],
            check=True,capture_output=True)
        linked = (self.root/'f.elf').read_bytes()
        image = match.elf_image(linked)
        symbol, offset = match.function_record(image,'func_08010000',A,True)
        data = image['text'][offset:offset+symbol['size']]
        rows = [dict(rom=f'0x{A:08X}',end=f'0x{A+len(data):08X}',mode='thumb',instrs=0),
                dict(rom='0x08001000',end='0x08001002',mode='thumb',instrs=1),
                dict(rom='0x08142250',end='0x08142252',mode='thumb',instrs=1)]
        rows[0]['instrs'] = owner.refine(data,A,json.dumps(rows).encode())['instrs']
        mapping = json.dumps(rows).encode()
        index = ''.join(f'{int(r["rom"],16):08X} {int(r["end"],16):08X} '
            f'{int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n' for r in rows).encode()
        rom = bytearray(0x142254)
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)] = data
        rom[0x1000:0x1002] = b'\x70\x47'
        rom[0x142250:0x142254] = b'\x18\x47\xc0\x46'
        values = dict(data=data,address=A,rom=bytes(rom),mapping=mapping,index=index,
            objects=b'{"g_dispatch":"0x02000000"}',selector=owner.THUNK_SWITCH_SELECTOR)
        bindings = {}
        if indirect:
            bindings,_ = owner.original_bindings(match.elf_image(original),A,values['rom'],
                mapping,values['objects'],selector=values['selector'],index=index)
        return original,linked,values,bindings

    def test_exact_original_frame_dependency_and_report(self):
        original,_,values,bindings = self.fixture()
        manifest,ins = owner.verify(**values,bindings=bindings)
        self.assertEqual(manifest['profile'],owner.THUNK_SWITCH_SCHEMA)
        inventory = manifest['proof']['ordinary_switch_inventory']
        self.assertEqual([name for _,name in inventory['runtime_calls']],['_call_via_r3'])
        self.assertEqual(inventory['canonical_thunks']['dependencies'],
                         thunk.dependencies(['_call_via_r3'],values['rom']))
        self.assertFalse(inventory['termination_claim'])
        self.assertFalse(inventory['ordinary_callee_native_proof'])
        self.assertNotIn('entry_stack',inventory['frame'])
        report = owner.render(A,(values['data'],manifest,'synthetic-source',values['mapping'],
            values['index'],values['objects'],values['rom'],len(ins),original))
        self.assertEqual(owner.selector_for_report(report),owner.THUNK_SWITCH_SELECTOR)
        self.assertIn(owner.THUNK_SWITCH_CONTROL_FLOW,report)
        self.assertIn('original_elf_sha256',report)

    def test_original_object_link_is_unchanged(self):
        original,linked,values,bindings = self.fixture()
        runner = match.Runner(match.DEFAULT_CC,root=self.root,timeout=120)
        with runner.workspace() as workspace:
            runner.write_text(workspace+'/f.i','')
            Path(workspace+'/f.o').write_bytes(original)
            data,actual = owner.object_bytes(runner,workspace,fixed_args(),match.elf_image(original),
                A,values['rom'],values['mapping'],values['objects'],
                selector=values['selector'],index=values['index'])
            self.assertEqual(data,values['data'])
            self.assertEqual(actual,bindings)
            self.assertEqual(runner.read_binary(workspace+'/f.o'),original)
            self.assertEqual(match.elf_image(runner.read_binary(workspace+'/f.elf'))['text'],
                             match.elf_image(linked)['text'])

    def test_old_scalar_and_division_compositions_stay_closed(self):
        original,_,values,bindings = self.fixture()
        for selector in (owner.DIRECT_SWITCH_SELECTOR,owner.ACYCLIC_SELECTOR):
            with self.subTest(selector=selector),self.assertRaises(ValueError):
                owner.original_bindings(match.elf_image(original),A,values['rom'],
                    values['mapping'],values['objects'],selector=selector,index=values['index'])
        _,_,without,_ = self.fixture(indirect=False)
        calls = __import__('owner_graph_profile').graph(without['data'],A,
            owner.refine(without['data'],A,without['mapping']))[3]
        with self.assertRaises(ValueError):
            scalar.verify(without['data'],A,without['rom'],without['mapping'],without['index'],
                calls,scalar.bind_calls(calls,without['mapping'],A,len(without['data']),len(without['rom'])),
                selector=scalar.THUNK_SELECTOR)

    def test_thunk_identity_and_complete_binding_are_authenticated(self):
        _,_,values,bindings = self.fixture()
        rom = bytearray(values['rom']);rom[0x142250] ^= 1
        with self.assertRaises(ValueError):
            owner.verify(**dict(values,rom=bytes(rom)),bindings=bindings)
        for key in ('calls','data','switches'):
            changed = copy.deepcopy(bindings);changed[key] = []
            with self.subTest(key=key),self.assertRaises(ValueError):
                owner.verify(**values,bindings=changed)

    def test_local_alias_entry_reads_and_allocation_do_not_gain_permission(self):
        for access in ('mov r2,sp','ldr r2,[sp,#8]','str r2,[sp,#4]'):
            _,_,values,bindings = self.fixture(access=access)
            with self.subTest(access=access),self.assertRaises(ValueError):
                owner.verify(**values,bindings=bindings)
        _,_,values,bindings = self.fixture(allocate=False)
        with self.assertRaises(ValueError):
            owner.verify(**values,bindings=bindings)

    def test_counts_manifest_and_marker_are_exact(self):
        _,_,values,bindings = self.fixture()
        rows = json.loads(values['mapping']);rows[0]['instrs'] += 1
        with self.assertRaises(ValueError):
            owner.verify(**dict(values,mapping=json.dumps(rows).encode()),bindings=bindings)
        manifest,_ = owner.verify(**values,bindings=bindings)
        manifest['proof']['ordinary_switch_inventory']['termination_claim'] = True
        with self.assertRaises(ValueError):
            owner.verify(**values,bindings=bindings,manifest=manifest)
        marker = f'* verification: `{owner.THUNK_SWITCH_SCHEMA}`\n'
        self.assertEqual(owner.selector_for_report(marker),owner.THUNK_SWITCH_SELECTOR)
        with self.assertRaises(ValueError):owner.selected(marker*2)
