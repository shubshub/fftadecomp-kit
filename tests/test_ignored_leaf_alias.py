"""Exact noncalling leaf summaries discharge only incoming values proved dead."""
import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import unittest

import test_buffer_index as fixtures

match = fixtures.match
BASE = match.ROM_BASE
import ignored_leaf_alias_profile as ignored
import owner_admission_profile as owner
import match_evidence

CALLER = ('push {lr}\nsub sp, #8\nmov r1, sp\nmovs r0, #0\n'
          'bl callee\nadd sp, #8\npop {r1}\nbx r1')
LEAF = 'push {lr}\nmovs r1, #7\nadds r0, r1, #0\npop {r1}\nbx r1'
CALLER_SOURCE = '''typedef unsigned char u8;
extern u8 *func_08010100(u8 selector);
unsigned int func_08010000(unsigned int choose, unsigned int value)
{
    unsigned int samples[2];
    unsigned int *selected;
    u8 *buffer;
    samples[0] = value;
    samples[1] = value + 1;
    if (choose)
        selected = samples;
    else
        selected = samples + 1;
    *selected += 3;
    buffer = func_08010100(0);
    return 2 * *buffer + samples[0] + samples[1];
}
'''
LEAF_SOURCE = '''typedef unsigned char u8;
extern u8 data_02000000[];
u8 *func_08010100(u8 selector)
{
    u8 *buffer = data_02000000;
    if (selector)
        buffer += 0x2000;
    return buffer;
}
'''


class IgnoredLeafTests(unittest.TestCase):
    setUp = fixtures.BufferIndexTests.setUp

    def fixture(self, callee=LEAF, caller=CALLER, mode='thumb'):
        source = self.root / 'fixture.s'
        source.write_text('.syntax unified\n.arch armv5t\n.thumb\n.text\n'
            '.global caller, caller_end, callee, callee_end, child, child_end\n'
            f'caller:\n{caller}\ncaller_end:\n.org 0x100\ncallee:\n{callee}\n'
            'callee_end:\n.org 0x200\nchild:\nbx lr\nchild_end:\n')
        for command in (
            ['arm-none-eabi-as', '-mthumb-interwork', str(source), '-o', str(self.root/'fixture.o')],
            ['arm-none-eabi-ld', '-Ttext=0x08000000', '-e', 'caller', str(self.root/'fixture.o'),
             '-o', str(self.root/'fixture.elf')],
            ['arm-none-eabi-objcopy', '-O', 'binary', '--only-section=.text',
             str(self.root/'fixture.elf'), str(self.root/'baserom.bin')]):
            subprocess.run(command, check=True, capture_output=True)
        self.rom = (self.root/'baserom.bin').read_bytes()
        image = match.elf_image((self.root/'fixture.elf').read_bytes())
        symbols = {item['name']: item['value'] for item in image['symbols']}
        self.rows = [{'rom': f'0x{symbols[name]:08X}', 'end': f'0x{symbols[name+"_end"]:08X}',
            'mode': mode if name == 'callee' else 'thumb', 'instrs': 0}
            for name in ('caller', 'callee', 'child')]
        for row in self.rows:
            start, end = int(row['rom'], 16), int(row['end'], 16)
            # Unsupported fixtures can be structurally partial; their count
            # still records the exact decodable instruction inventory.
            cs = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
            row['instrs'] = len(list(cs.disasm(self.rom[start-BASE:end-BASE], start)))
        self.mapping = json.dumps(self.rows).encode()
        self.index = ''.join(f'{int(row["rom"],16):08X} {int(row["end"],16):08X} '
            f'{int(row["end"],16)-int(row["rom"],16)} {row["instrs"]} return\n'
            for row in self.rows).encode()
        self.body = self.rom[:int(self.rows[0]['end'],16)-BASE]
        cs = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB); cs.detail = True
        self.calls = {item.address: item.operands[0].imm for item in cs.disasm(self.body,BASE)
                      if match.CS_GRP_CALL in item.groups}
        return self.proof()

    def proof(self):
        return ignored.IgnoredLeafAliasProof(self.rom,self.mapping,self.index,b'{}\n',
                                           BASE,len(self.body),self.calls)

    def verify(self, proof):
        return match.verify_leaf_instructions(self.body,BASE,True,self.calls,
            acyclic_state_budget=4096,ignored_leaf_alias_proof=proof)

    def test_positive_requires_explicit_selector_and_exact_instruction_binding(self):
        proof = self.fixture()
        with self.assertRaisesRegex(ValueError, 'stack aliases cannot cross calls'):
            match.verify_leaf_instructions(self.body,BASE,True,self.calls,acyclic_state_budget=4096)
        self.verify(proof)
        record = proof.manifest()
        self.assertEqual(record['discarded_aliases'], [[8,'func_08000100',['r1']]])
        self.assertEqual(record['callees'][0]['body_sha256'],hashlib.sha256(self.rom[256:266]).hexdigest())
        self.assertNotIn('body',record['callees'][0])
        self.assertEqual(record['callees'][0]['owner']['bindings']['calls'], [])
        with self.assertRaisesRegex(ValueError,'exact original BL site'):
            proof.check_call(BASE+10,BASE+256,{match.ARM_REG_R1:-8},{})

    def test_incoming_value_read_before_overwrite_or_on_one_path_is_rejected(self):
        for callee in (
            'push {lr}\nadds r0, r1, #0\nmovs r1, #0\npop {r1}\nbx r1',
            'push {lr}\ncmp r0, #0\nbeq read\nmovs r1, #0\nread:\n'
            'adds r0, r1, #0\npop {r1}\nbx r1'):
            with self.subTest(callee=callee), self.assertRaisesRegex(ValueError,'observes incoming r1'):
                self.verify(self.fixture(callee))

    def test_untouched_and_conditionally_untouched_alias_are_not_discarded(self):
        for callee in ('bx lr', 'cmp r0, #0\nbeq done\nmovs r1, #0\ndone:\nbx lr'):
            with self.subTest(callee=callee), self.assertRaisesRegex(ValueError,'overwrite.*every return'):
                self.verify(self.fixture(callee))

    def test_genuine_r0_pointer_argument_is_rejected_despite_any_prototype(self):
        caller = CALLER.replace('mov r1, sp\nmovs r0, #0','mov r0, sp')
        callee = 'push {lr}\nlsls r0, r0, #1\npop {r1}\nbx r1'
        with self.assertRaisesRegex(ValueError,'observes incoming r0'):
            self.verify(self.fixture(callee,caller))

    def test_implicit_flag_inputs_must_be_independently_overwritten(self):
        for condition in ('beq', 'bcs', 'bvs'):
            callee=f'{condition} done\nmovs r1, #0\ndone:\nmovs r1, #0\nbx lr'
            with self.subTest(condition=condition), self.assertRaisesRegex(ValueError,'implicit condition flags'):
                self.verify(self.fixture(callee))
        # MOV sets only N/Z, so it cannot justify a later carry-dependent edge.
        with self.assertRaisesRegex(ValueError,'implicit condition flags'):
            self.verify(self.fixture('movs r1, #0\nbcs done\nmovs r0, #0\ndone:\nbx lr'))
        self.verify(self.fixture('cmp r0, #0\nbeq done\nmovs r1, #0\ndone:\nmovs r1, #0\nbx lr'))

    def test_indirect_forwarding_recursive_interrupt_and_stack_effects_fail_closed(self):
        for callee in (
            'bx r3', 'push {lr}\nbl child\npop {r1}\nbx r1',
            'bl callee', 'blx r3', 'svc #0\nbx lr',
            'push {lr}\nldr r1, [sp, #4]\npop {r1}\nbx r1',
            'push {lr}\nmovs r1, #0\nstr r1, [r0]\npop {r1}\nbx r1',
            'push {r4, lr}\nmovs r1, #0\npop {r4}\npop {r1}\nbx r1'):
            with self.subTest(callee=callee), self.assertRaises(ValueError):
                self.verify(self.fixture(callee))

    def test_incoming_stack_pointer_slots_are_never_discharged(self):
        proof=self.fixture()
        with self.assertRaisesRegex(ValueError,'incoming stack pointer slots'):
            proof.check_call(BASE+8,BASE+256,{match.ARM_REG_R1:-8},{-4:-8})
        with self.assertRaisesRegex(ValueError,'use or escape'):
            self.verify(self.fixture(caller=CALLER.replace('movs r0, #0',
                                                          'str r1, [sp]\nmovs r0, #0')))

    def test_owner_count_mode_body_and_index_controls(self):
        for mutation in ('overlap','extent','mode','json_count','text_count','text_extent','body'):
            proof=self.fixture()
            with self.subTest(mutation=mutation):
                if mutation == 'overlap':
                    self.rows.append(dict(self.rows[1],rom='0x08000102'))
                elif mutation == 'extent': self.rows[1]['end']='0x0800010C'
                elif mutation == 'mode': self.rows[1]['mode']='arm'
                elif mutation == 'json_count': self.rows[1]['instrs']-=1
                elif mutation == 'text_count': self.index=self.index.replace(b'0800010A 10 5',b'0800010A 10 4')
                elif mutation == 'text_extent': self.index=self.index.replace(b'0800010A 10',b'0800010C 12')
                elif mutation == 'body': self.rom=self.rom[:256]+b'\x08\x1c'+self.rom[258:]
                self.mapping=json.dumps(self.rows).encode()
                with self.assertRaises(ValueError): self.verify(self.proof())

    def test_cycles_budget_unbalanced_stack_and_profile_isolation_preserved(self):
        self.fixture()
        with self.assertRaisesRegex(ValueError,'isolated exact acyclic'):
            match.verify_leaf_instructions(self.body,BASE,True,self.calls,ignored_leaf_alias_proof=self.proof())
        with self.assertRaisesRegex(ValueError,'ordinary isolated'):
            match.verify_leaf_instructions(self.body,BASE,True,self.calls,acyclic_state_budget=4096,
                ignored_leaf_alias_proof=self.proof(),buffer_proof=object())
        with self.assertRaisesRegex(ValueError,'budget exhausted'):
            match.verify_leaf_instructions(self.body,BASE,True,self.calls,acyclic_state_budget=1,
                ignored_leaf_alias_proof=self.proof())
        for callee in ('loop:\nmovs r1, #0\ncmp r0, #0\nbne loop\nbx lr',
                       'push {lr}\nmovs r1, #0\nbx lr'):
            with self.subTest(callee=callee), self.assertRaises(ValueError):
                self.verify(self.fixture(callee))


@unittest.skipUnless(Path(os.path.expandvars(match.DEFAULT_CC)).is_file() and
                     shutil.which('arm-none-eabi-as'), 'fixed compiler required')
class CompilerLifecycleTests(unittest.TestCase):
    setUp = fixtures.BufferIndexTests.setUp
    A = BASE + 0x10000

    def compile(self, root, address, source):
        for name in ('src','include','compile','config','symbols','build'):
            (root/name).mkdir(parents=True,exist_ok=True)
        (root/'src'/f'{address:08X}.c').write_text(source)
        args=argparse.Namespace(cc=match.DEFAULT_CC,cpp=match.DEFAULT_CPP,
            assembler=match.DEFAULT_AS,objcopy=match.DEFAULT_OBJCOPY,
            linker=match.DEFAULT_LD,flags=match.DEFAULT_FLAGS)
        runner=match.Runner(match.DEFAULT_CC,root=root,timeout=120)
        raw,data,image=match.compile_object(runner,str(root/'compile'),args,root,address,
                                          f'src/{address:08X}.c')
        self.assertEqual(image['type'],1)
        return args,runner,raw,image

    def test_natural_fixed_O2_original_elf_report_replay_status_partial_rebuild(self):
        args,runner,raw,image=self.compile(self.root,self.A,CALLER_SOURCE)
        leaf_root=self.root/'leaf'
        _,leaf_runner,leaf_raw,leaf_image=self.compile(leaf_root,self.A+256,LEAF_SOURCE)
        self.assertEqual(len(leaf_image['text']),28)
        rows=[{'rom':f'0x{address:08X}','end':f'0x{address+len(body):08X}',
               'mode':'thumb','instrs':0} for address,body in
              ((self.A,image['text']),(self.A+256,leaf_image['text']))]
        mapping=json.dumps(rows).encode()
        objects=b'{"data_02000000":"0x02000000"}\n'
        rom=bytes(self.A-BASE+256+len(leaf_image['text'])+32)
        leaf_data,_=owner.object_bytes(leaf_runner,str(leaf_root/'compile'),args,leaf_image,
            self.A+256,rom,mapping,objects,selector=owner.ACYCLIC_SELECTOR)
        caller_data,_=owner.object_bytes(runner,str(self.root/'compile'),args,image,
            self.A,rom,mapping,objects,selector=ignored.SELECTOR)
        # No caller opcode was manufactured or altered: the sole BL relocation
        # links the retained original compiler object to the indexed leaf.
        data=bytearray(b'\xA5'*len(rom));offset=self.A-BASE
        data[offset:offset+len(caller_data)]=caller_data
        data[offset+256:offset+256+len(leaf_data)]=leaf_data;rom=bytes(data)
        for row,body in zip(rows,(caller_data,leaf_data)):
            row['instrs']=owner.refine(body,int(row['rom'],16),mapping)['instrs']
        mapping=json.dumps(rows).encode()
        (self.root/'config/functions.json').write_bytes(mapping)
        index=''.join(f'{int(row["rom"],16):08X} {int(row["end"],16):08X} '
            f'{int(row["end"],16)-int(row["rom"],16)} {row["instrs"]} return\n'for row in rows).encode()
        (self.root/'symbols/functions.txt').write_bytes(index)
        (self.root/'config/data_symbols.json').write_bytes(objects)
        (self.root/'baserom.bin').write_bytes(rom)
        structural=owner.refine(caller_data,self.A,mapping)
        self.assertTrue(structural['cfg_closed'],structural)
        command=[sys.executable,str(Path(match.__file__)),'--root',str(self.root),'08010000']
        for selector in (None,owner.ACYCLIC_SELECTOR):
            options=[] if selector is None else ['--owner-runtime-profile',selector]
            default=subprocess.run(command+['--no-write',*options],capture_output=True,text=True)
            self.assertNotEqual(default.returncode,0)
        fresh=subprocess.run(command+['--owner-runtime-profile',ignored.SELECTOR],
                             capture_output=True,text=True)
        self.assertEqual(fresh.returncode,0,fresh.stdout+fresh.stderr)
        self.assertIn('verdict MATCH - byte identical',fresh.stdout)
        (self.root/'match-cli.log').write_text(fresh.stdout+fresh.stderr)
        report=(self.root/'docs/match/08010000.md').read_text()
        self.assertTrue(match_evidence.report_matches(report,self.root,self.A))
        self.assertEqual(owner.selector_for_report(report),ignored.SELECTOR)
        result=owner.build(self.root,self.A,selector=ignored.SELECTOR)
        self.assertEqual(result[8],raw)
        self.assertEqual(owner.render(self.A,result),report)
        discarded=result[1]['proof']['ignored_leaf_aliases']['discarded_aliases']
        self.assertTrue(discarded)
        self.assertTrue(all(record[2]==['r1']for record in discarded))
        wrong=copy.deepcopy(result[1])
        wrong['proof']['ignored_leaf_aliases']['callees'][0]['body_sha256']='0'*64
        with self.assertRaisesRegex(ValueError,'manifest differs'):
            owner.verify(caller_data,self.A,rom,mapping,index,objects,wrong,
                bindings=result[1]['bindings'],selector=ignored.SELECTOR)
        self.assertFalse(owner.report_matches(report.replace(ignored.SCHEMA,owner.ACYCLIC_SCHEMA),
                                              self.root,self.A))
        self.assertFalse(owner.report_matches(report.replace('"r1"','"r0"'),self.root,self.A))
        # Each identity/input can independently stale otherwise exact caller
        # bytes. Restore the original bytes after every negative control.
        controls={self.root/'src/08010000.c':CALLER_SOURCE.encode()+b'\n',
            self.root/'config/functions.json':mapping+b'\n',
            self.root/'symbols/functions.txt':index+b'\n',
            self.root/'config/data_symbols.json':objects+b'\n',
            self.root/'baserom.bin':rom[:offset+256+7]+bytes([rom[offset+256+7]^1])+rom[offset+256+8:]}
        for path,changed in controls.items():
            original=path.read_bytes()
            with self.subTest(stale_input=path.name):
                try:
                    path.write_bytes(changed)
                    self.assertFalse(owner.report_matches(report,self.root,self.A))
                finally:path.write_bytes(original)
        header=self.root/'include/added.h'
        try:
            header.write_text('typedef unsigned int fixture_word;\n')
            self.assertFalse(owner.report_matches(report,self.root,self.A))
        finally:header.unlink()
        import status
        import rebuild
        self.assertEqual(rebuild.saved_profile_arguments(report,self.root,self.A),
                         ['--owner-runtime-profile',ignored.SELECTOR])
        totals=status.collect(str(self.root),True,quiet=True)
        self.assertEqual((totals[1],totals[3],totals[4]),(1,len(caller_data),[]))
        self.assertEqual(rebuild.compiled_rebuild(self.root),0)
        self.assertEqual((self.root/'compile/f.o').read_bytes(),raw)
        self.assertEqual((leaf_root/'compile/f.o').read_bytes(),leaf_raw)
        target=os.environ.get('FFTA_IGNORED_LEAF_TEST_ARTIFACTS')
        if target:
            destination=Path(target)/'compiler-positive'
            if destination.exists():shutil.rmtree(destination)
            shutil.copytree(self.root,destination)
            (destination/'lifecycle.json').write_text(json.dumps({'schema':ignored.SCHEMA,
                'compiler':match.DEFAULT_CC,'flags':match.DEFAULT_FLAGS,
                'caller_bytes':len(caller_data),'callee_bytes':len(leaf_data),
                'original_caller_et_rel_sha256':hashlib.sha256(raw).hexdigest(),
                'original_leaf_et_rel_sha256':hashlib.sha256(leaf_raw).hexdigest(),
                'fresh_cli':fresh.returncode,'fresh_source_report_replay':True,
                'status_compiled_functions':totals[1],'status_compiled_bytes':totals[3],
                'partial_mixed_rebuild_exit':0,'manifest':result[1]},indent=2,sort_keys=True)+'\n')


if __name__ == '__main__':
    unittest.main(verbosity=2)
