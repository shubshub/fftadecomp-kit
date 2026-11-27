"""New synthetic native bridge checks; no ROM, native compiler or game C."""
import argparse
import contextlib
import copy
import io
import json
from pathlib import Path
import struct
import sys
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve()
sys.path.insert(0, str(HERE.parents[1]/'tools'))
sys.dont_write_bytecode = True
import match
import report_fixtures
import owner_admission_profile as owner
import owner_graph_profile as graph
import local_long_branch_profile as frame
import mutable_stack_index_profile as finite
from synthetic_three_call_owner import (
    A, T0, T1, T2, CHILD, OBJECTS, words, bl, assemble, fixture,
)
SELECTOR = 'mutable-four-local-index-three-call-native-v1'



def elf(proof, *, linked=False, names=None, relocations=None):
    """Real little-endian ARM ET_REL/ET_EXEC with canonical Thumb BL REL."""
    calls=sorted(proof.calls.items())
    targets=sorted(set(proof.calls.values()))
    names={} if names is None else names
    data=bytearray(proof.body)
    symbols=[('',0,0,0,0),(f'func_{A:08X}',(A if linked else 0)|1,len(data),0x12,1)]
    symbols += [(names.get(t,f'func_{t:08X}'),t|1 if linked else 0,0,0x12,0xfff1 if linked else 0) for t in targets]
    rel=[]
    if not linked:
        for site,target in calls:
            offset=site-A
            data[offset:offset+4]=bl(site,site)
            rel.append((offset,((2+targets.index(target))<<8)|10))
    if relocations is not None: rel=relocations
    strings=bytearray(b'\0');encoded=bytearray()
    for name,value,size,info,section in symbols:
        offset=len(strings);strings+=name.encode()+b'\0'
        encoded+=struct.pack('<IIIBBH',offset,value,size,info,0,section)
    names=b'\0.text\0.symtab\0.strtab\0.rel.text\0.shstrtab\0'
    parts=[bytes(data),bytes(encoded),bytes(strings),b''.join(struct.pack('<II',*r) for r in rel),names]
    raw=bytearray(b'\0'*52); offsets=[]
    for part in parts:
        while len(raw)%4:raw+=b'\0'
        offsets.append(len(raw));raw+=part
    specs=[(0,0,0,0,0,0,0,0,0,0),
        (1,1,6,A if linked else 0,offsets[0],len(data),0,0,4,0),
        (7,2,0,0,offsets[1],len(encoded),3,1,4,16),
        (15,3,0,0,offsets[2],len(strings),0,0,1,0),
        (23,9,0,0,offsets[3],len(parts[3]),2,1,4,8),
        (33,3,0,0,offsets[4],len(names),0,0,1,0)]
    while len(raw)%4:raw+=b'\0'
    shoff=len(raw);raw+=b''.join(struct.pack('<IIIIIIIIII',*s) for s in specs)
    raw[:16]=b'\x7fELF\x01\x01\x01'+b'\0'*9
    struct.pack_into('<HHIIIIIHHHHHH',raw,16,2 if linked else 1,40,1,A|1 if linked else 0,0,shoff,0,52,0,0,40,len(specs),5)
    return bytes(raw)


def args(**changes):
    result=dict(cc=match.DEFAULT_CC,cpp=match.DEFAULT_CPP,assembler=match.DEFAULT_AS,
        objcopy=match.DEFAULT_OBJCOPY,linker=match.DEFAULT_LD,flags=match.DEFAULT_FLAGS,
        mode='thumb',control_flow_profile='ordinary',software_double_profile=None,
        software_double_remainder_profile=None,function_address_profile=None,switch_profile=None,
        label=None,wsl='Ubuntu',wsl_path=match.DEFAULT_WSL_PATH,signed_quotient_profile=None,
        signed_runtime_profile=None,addressed_signed_runtime_profile=None,switch_data_profile=None,
        owner_runtime_profile=SELECTOR,emit=None,no_write=True)
    result.update(changes);return argparse.Namespace(**result)


def binding(proof, **kwargs):
    return owner.original_bindings(match.elf_image(elf(proof,**kwargs)),A,proof.rom,
        proof.mapping,proof.objects,selector=SELECTOR,index=proof.index)[0]


def native(proof, manifest=None, bindings=None):
    return owner.verify(proof.body,A,proof.rom,proof.mapping,proof.index,proof.objects,manifest,
        bindings=binding(proof) if bindings is None else bindings,selector=SELECTOR)


class RedBridgeTests(unittest.TestCase):
    def test_real_ET_REL_reconstructs_three_proven_roles(self):
        import mutable_three_call_native_profile as bridge
        proof,*_=fixture()
        record,instructions=native(proof)
        self.assertEqual(record['profile'],bridge.SCHEMA)
        self.assertEqual(record['roles']['sites'],proof.sites)
        self.assertEqual(len(instructions),owner.refine(proof.body,A,proof.mapping)['instrs'])
        self.assertTrue(record['roles']['canonical_original_ELF_offsets_required'])
        self.assertTrue(record['inventory']['inventory_only'])
        self.assertFalse(record['inventory']['source_or_ELF_admission'])
        self.assertFalse(record['arithmetic_or_memory_safety_theorem'])

    def test_single_CLI_selector_dispatches_exclusively(self):
        with patch('sys.argv',['match.py','--root',str(HERE.parents[2]),
                '--owner-runtime-profile',SELECTOR,hex(A)]),patch.object(owner,'issue',return_value=9) as issue:
            self.assertEqual(match.main(),9)
        self.assertEqual(issue.call_args.args[2].owner_runtime_profile,SELECTOR)



class RoleBoundaryTests(unittest.TestCase):
    def test_canonical_call_offsets_missing_duplicate_wrong_symbol_refused(self):
        proof,*_=fixture()
        raw=match.elf_image(elf(proof))
        _,targets=owner.original_bindings(raw,A,proof.rom,proof.mapping,proof.objects,selector=SELECTOR,index=proof.index)
        self.assertEqual(len(targets),3)
        for names in ({T0:'__divsi3'},{T1:'arbitrary_alias'},{T2:f'func_{T2+2:08X}'}):
            with self.subTest(names=names),self.assertRaises(ValueError):binding(proof,names=names)
        rows=[(site-A,((2+sorted(set(proof.calls.values())).index(target))<<8)|10)
              for site,target in sorted(proof.calls.items())]
        for rel in (rows+rows[:1],[(rows[0][0]+2,rows[0][1])]+rows[1:]):
            with self.subTest(rel=rel),self.assertRaises(ValueError):binding(proof,relocations=rel)
        good=binding(proof)
        for bad in ({**good,'calls':good['calls'][:-1]},
                    {**good,'functions':[[0,f'func_{T0:08X}']]},
                    {**good,'sites':{'leaf_overwrite':[0,T0]}}):
            with self.subTest(bad=bad),self.assertRaisesRegex(ValueError,'bindings|binding|offset'):
                native(proof,bindings=bad)

    def test_real_consumer_observation_and_extra_alias_call_refused(self):
        for case,fragment in ((dict(bad_consumer=True),'reads live R2'),
                              (dict(extra_call=True),'three disjoint|role')):
            proof,*_=fixture(**case)
            with self.subTest(case=case),self.assertRaisesRegex(ValueError,fragment):native(proof)

    def test_uninitialized_local_and_unrepaired_legacy_count_refused(self):
        proof,*_=fixture(missing_init=True)
        with self.assertRaisesRegex(ValueError,'initializ'):native(proof)
        proof,*_=fixture()
        rows=json.loads(proof.mapping);old=rows[0]['instrs'];rows[0]['instrs']=len(proof.body)//2
        proof.mapping=json.dumps(rows).encode()
        proof.index=proof.index.replace(f' {old} return'.encode(),f' {rows[0]["instrs"]} return'.encode(),1)
        with self.assertRaisesRegex(ValueError,'instruction counts'):native(proof)

    def test_complete_callee_corruption_missing_typed_literal_and_nested_identity_refused(self):
        for target,offset,value in ((T0,10,words(0x7011)),(T1,2,words(0x1c11))):
            proof,*_=fixture();changed=bytearray(proof.rom)
            changed[target-match.ROM_BASE+offset:target-match.ROM_BASE+offset+2]=value
            proof.rom=bytes(changed)
            with self.subTest(target=target),self.assertRaises(ValueError):native(proof)
        proof,*_=fixture()
        proof.mapping=json.dumps([r for r in json.loads(proof.mapping) if int(r['rom'],16)!=CHILD]).encode()
        with self.assertRaises(ValueError):native(proof)
        proof,*_=fixture();proof.objects=b'{}'
        with self.assertRaisesRegex(ValueError,'mapped|object|literal'):native(proof)

    def test_default_entry_and_word_categories_do_not_admit_or_mix(self):
        import entry_recursive_ordinary_call_profile as entry
        import word_result_callback_profile as word
        proof,*_=fixture();b=binding(proof)
        for selector in (owner.SELECTOR,owner.ACYCLIC_SELECTOR,entry.SELECTOR,word.SELECTOR):
            with self.subTest(selector=selector),self.assertRaises(ValueError):
                owner.verify(proof.body,A,proof.rom,proof.mapping,proof.index,proof.objects,bindings=b,selector=selector)
        for field in ('function_address_profile','addressed_signed_runtime_profile','signed_runtime_profile',
                      'signed_quotient_profile','switch_data_profile'):
            with self.subTest(field=field),patch.object(owner,'build') as build,self.assertRaises(ValueError):
                owner.issue(HERE.parents[2],A,args(**{field:'other-policy'}))
            build.assert_not_called()
        with self.assertRaisesRegex(ValueError,'original resident-owner ELF'):
            owner.preflight(proof.body,A,proof.rom,proof.mapping,proof.index,proof.objects,selector=SELECTOR)

    def test_native_frame_type_and_entry_word_cannot_mix(self):
        import mutable_three_call_native_profile as bridge
        proof,ins,edges,branches,calls=fixture()
        for policy,context,extra in ((None,object(),{}),('forged',proof,{}),
                (SELECTOR,proof,{}),(SELECTOR,None,{}),
                (SELECTOR,bridge.NativeRoleProof(proof.rom,proof.mapping,proof.index,proof.objects,
                     A,len(proof.body),calls,binding(proof)),{'entry_stack_policy':{'words':[0]}})):
            with self.subTest(policy=policy,context=type(context)),self.assertRaises(ValueError):
                frame.prove_frame(ins,edges,A,branches,calls,stack_aliases=True,
                    mutable_stack_index_policy=finite.THREE_CALL_SELECTOR,
                    consumer_scratch_proof=context,native_three_call_policy=policy,**extra)


class FakeRunner:
    def __init__(self,linked):self.linked=linked;self.files={};self.commands=[]
    def read_binary(self,path):
        if path.endswith('/f.i'):return b'/* inert mocked preprocessor input */'
        if path.endswith('/f.elf'):return self.linked
        return self.files[path]
    def write_text(self,path,value):self.files[path]=value
    def sh(self,command):self.commands.append(command)


class LifecycleTests(unittest.TestCase):
    @contextlib.contextmanager
    def tree(self,proof):
        import tempfile
        scratch=HERE.parents[2]/'scratch';scratch.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='synthetic_',dir=scratch) as directory:
            root=Path(directory)
            for name in ('src','include','config','symbols'):(root/name).mkdir()
            (root/'src'/f'{A:08X}.c').write_bytes(b'inert synthetic compiler input fixture\n')
            (root/'include/fixture.h').write_bytes(b'inert header fixture\n')
            (root/'baserom.bin').write_bytes(proof.rom)
            (root/'config/functions.json').write_bytes(proof.mapping)
            (root/'config/data_symbols.json').write_bytes(proof.objects)
            (root/'symbols/functions.txt').write_bytes(proof.index)
            yield root

    @contextlib.contextmanager
    def mocks(self,proof,change=None):
        import match_evidence as evidence
        raw=elf(proof);image=match.elf_image(raw);runners=[]
        def factory(*a,**kw):
            runner=FakeRunner(elf(proof,linked=True));runners.append(runner)
            @contextlib.contextmanager
            def workspace():yield '/synthetic'
            runner.workspace=workspace;return runner
        def plausible(command,capture,timeout):
            self.assertIn('plausible.py',command[1]);self.assertIn('--json',command)
            if change:change(Path(capture))
            return object()
        with patch.object(match,'Runner',side_effect=factory), \
             patch.object(match,'compile_object',return_value=(raw,None,image)) as compiler, \
             patch.object(match,'_run_replay_process',side_effect=plausible), \
             patch.object(match,'plausibility_result',return_value=([],False)), \
             patch.object(evidence,'report_rom_path',side_effect=lambda root:str(Path(root)/'baserom.bin')):
            yield runners,compiler

    def test_real_original_ELF_mock_link_preserves_every_nonrelocation_byte(self):
        proof,*_=fixture();raw=match.elf_image(elf(proof));runner=FakeRunner(elf(proof,linked=True))
        data,b=owner.object_bytes(runner,'/synthetic',args(),raw,A,proof.rom,proof.mapping,proof.objects,selector=SELECTOR,index=proof.index)
        self.assertEqual(data,proof.body);self.assertEqual(b,binding(proof));self.assertEqual(len(runner.commands),2)
        for target in (T0,T1,T2):self.assertIn(f'.thumb_set func_{target:08X}',runner.files['/synthetic/f.known.s'])
        changed=copy.copy(proof);body=bytearray(proof.body);body[2:4]=words(0xb08d);changed.body=bytes(body)
        with self.assertRaisesRegex(ValueError,'outside exact original relocations'):
            owner.object_bytes(FakeRunner(elf(changed,linked=True)),'/synthetic',args(),raw,A,
                proof.rom,proof.mapping,proof.objects,selector=SELECTOR,index=proof.index)
        changed=copy.copy(proof);body=bytearray(proof.body);site=sorted(proof.calls)[0]
        body[site-A:site-A+4]=bl(site,T1);changed.body=bytes(body)
        with self.assertRaisesRegex(ValueError,'call target differs'):
            owner.object_bytes(FakeRunner(elf(changed,linked=True)),'/synthetic',args(),raw,A,
                proof.rom,proof.mapping,proof.objects,selector=SELECTOR,index=proof.index)

    def test_full_mock_compiler_link_build_and_fresh_report_roundtrip(self):
        proof,*_=fixture()
        with self.tree(proof) as root,self.mocks(proof) as (runners,compiler):
            result=owner.build(root,A,selector=SELECTOR)
            self.assertEqual(compiler.call_count,1);self.assertEqual(len(runners[0].commands),2)
            self.assertEqual(result[0],proof.body);self.assertEqual(result[-1],elf(proof))
            report=owner.render(A,result)
            self.assertTrue(owner.selected(report));self.assertEqual(owner.selector_for_report(report),SELECTOR)
            self.assertIn('original_elf_sha256',report);self.assertIn('No transitive memory effects',report)
            # This is the new synthetic report replay/freshness behavior, not a game proof replay.
            self.assertTrue(owner.report_matches(report,root,A))
            stale=report.replace('"source_sha256":"','"source_sha256":"0',1)
            self.assertFalse(owner.report_matches(stale,root,A))
            for schema in (owner.entry.NATIVE_SCHEMA,owner.word_buffer.SCHEMA):
                with self.subTest(schema=schema),self.assertRaises(ValueError):
                    owner.selected(report+'* verification: `'+schema+'`\n')
            (root/'include/fixture.h').write_bytes(b'changed synthetic header')
            self.assertFalse(owner.report_matches(report,root,A))

    def test_build_rejects_source_header_maps_ROM_and_producer_transition(self):
        import mutable_three_call_native_profile as bridge
        for kind in ('source','header','mapping','index','objects','rom','captured','producer'):
            proof,*_=fixture()
            with self.subTest(kind=kind),self.tree(proof) as root:
                selected={'source':root/'src'/f'{A:08X}.c','header':root/'include/fixture.h',
                    'mapping':root/'config/functions.json','index':root/'symbols/functions.txt',
                    'objects':root/'config/data_symbols.json','rom':root/'baserom.bin'}
                state={'generation':'initial'}
                def change(capture):
                    if kind=='producer':state['generation']='changed'
                    else:
                        path=capture/'include/fixture.h' if kind=='captured' else selected[kind]
                        path.write_bytes(path.read_bytes()+b'\n')
                with self.mocks(proof,change),patch.object(bridge,'environment_fingerprint',side_effect=lambda:dict(state)),self.assertRaisesRegex(ValueError,'changed|implausible'):
                    owner.build(root,A,selector=SELECTOR)

    def test_status_publisher_and_evidence_preserve_explicit_selector(self):
        import match_evidence as evidence
        import status
        import push
        proof,*_=fixture()
        with self.tree(proof) as root,self.mocks(proof):
            result=owner.build(root,A,selector=SELECTOR);report=owner.render(A,result)
            directory=root/'docs/match';directory.mkdir(parents=True)
            (directory/f'{A:08X}.md').write_text(report)
            with patch.object(owner,'report_matches',return_value=True) as replay:
                self.assertTrue(evidence.report_matches(report_fixtures.carried(report, root, A), root, A));replay.assert_called_once()
            completed=argparse.Namespace(returncode=0,stdout=f'extent    {len(proof.body)} bytes\nverdict MATCH - byte identical\n')
            with patch.object(status,'report_matches',return_value=True),patch.object(status.subprocess,'run',return_value=completed) as command:
                values=status.collect(str(root),True,quiet=True,jobs=1)
                self.assertEqual(values[4],[]);self.assertEqual(values[1],1)
                argv=command.call_args.args[0]
                self.assertEqual(argv[argv.index('--owner-runtime-profile')+1],SELECTOR)
                self.assertIn('--no-write',argv)
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertTrue(push.check_reports(str(root)))

    def test_stale_role_environment_manifest_and_raw_ELF_digest_refused(self):
        import mutable_three_call_native_profile as bridge
        proof,*_=fixture();record,ins=native(proof)
        for key in ('roles','bindings','environment'):
            bad=copy.deepcopy(record);bad[key]={}
            with self.subTest(key=key),self.assertRaisesRegex(ValueError,'fresh source-bound replay'):
                native(proof,manifest=bad)
        result=(proof.body,record,'a'*64,proof.mapping,proof.index,proof.objects,proof.rom,len(ins),elf(proof))
        changed=result[:-1]+(result[-1]+b'extra ELF bytes',)
        self.assertNotEqual(owner.render(A,result),owner.render(A,changed))
        roles=bridge.NativeRoleProof(proof.rom,proof.mapping,proof.index,proof.objects,A,len(proof.body),proof.calls,binding(proof))
        roles.sources['producer']='stale'
        with self.assertRaisesRegex(ValueError,'changed'):roles.fresh()


def changed_root(proof,old,new):
    result=copy.copy(proof)
    assert len(old)==len(new) and proof.body.count(old)==1
    result.body=proof.body.replace(old,new)
    rom=bytearray(proof.rom);rom[A-match.ROM_BASE:A-match.ROM_BASE+len(result.body)]=result.body
    result.rom=bytes(rom)
    return result


class AdditionalBoundaryTests(unittest.TestCase):
    def test_actual_local_lifetime_bounds_and_saved_return_not_exempted(self):
        proof,*_=fixture()
        changes=((words(0x910b),words(0x2100)),
                 (words(0xbc02,0x4708),words(0xbc01,0x4708)))
        for old,new in changes:
            with self.subTest(old=old.hex()),self.assertRaises(ValueError):native(changed_root(proof,old,new))
        data=proof.body.replace(words(0x2d03),words(0x2d04),1)
        bad=copy.copy(proof);bad.body=data;rom=bytearray(proof.rom)
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)]=data;bad.rom=bytes(rom)
        with self.assertRaises(ValueError):native(bad)

    def test_nonleaf_must_kill_alias_before_observation_not_just_have_calls(self):
        proof,*_=fixture();rom=bytearray(proof.rom)
        rom[T2-match.ROM_BASE+6:T2-match.ROM_BASE+8]=words(0x1c10)
        proof.rom=bytes(rom)
        with self.assertRaisesRegex(ValueError,'before|observe|reads|incoming'):native(proof)

    def test_actual_native_environment_binds_all_private_chain_and_fixed_binaries(self):
        import mutable_three_call_native_profile as bridge
        result=bridge.environment_fingerprint()
        import hashlib
        for module in ('match','owner_admission_profile','local_long_branch_profile',
                'mutable_stack_index_profile','mutable_stack_index_inventory','three_call_composition_profile',
                'consumer_scratch_alias_profile','readonly_leaf_overwrite_profile',
                'incoming_scratch_overwrite_profile','ignored_leaf_alias_profile','mutable_three_call_native_profile'):
            path=Path(sys.modules[module].__file__)
            self.assertEqual(result['producers'][path.name],hashlib.sha256(path.read_bytes()).hexdigest())
        self.assertTrue(result['toolchain']);self.assertTrue(result['runtime'])

    def test_duplicate_forged_report_and_recursive_replay_guard_fail_closed(self):
        proof,*_=fixture();record,ins=native(proof)
        result=(proof.body,record,'f'*64,proof.mapping,proof.index,proof.objects,proof.rom,len(ins),elf(proof))
        report=owner.render(A,result)
        duplicate=report.replace('"address":'+str(A),'"address":'+str(A)+',"address":'+str(A),1)
        with patch.object(owner,'build') as build:
            self.assertFalse(owner.report_matches(duplicate,HERE.parents[2],A));build.assert_not_called()
        token=owner._replay.set(True)
        try:
            with patch.object(owner,'build') as build:
                self.assertFalse(owner.report_matches(report,HERE.parents[2],A));build.assert_not_called()
        finally:owner._replay.reset(token)
        with self.assertRaises(ValueError):owner.selected(report+'* function-address: forged\n')
        with self.assertRaises(ValueError):
            owner.fingerprint(A,proof.body,record,'f'*64,proof.mapping,proof.index,proof.objects,proof.rom)


class FinalAdmissionBoundaryTests(unittest.TestCase):
    def test_extra_symbols_sections_relocations_and_overlapping_owner_rejected(self):
        proof,*_=fixture()
        original=match.elf_image(elf(proof))
        for kind in ('symbol','section','relocation'):
            image=copy.deepcopy(original)
            if kind=='symbol':
                extra=dict(image['symbols'][1]);extra['name']='another_function';image['symbols'].append(extra)
            elif kind=='section':
                image['sections'].append((0,1,2,0,0,2,0,0,2,0))
            else:
                for key in image['relocations']:
                    raw=bytearray(image['section_data'][key]);site,info=struct.unpack_from('<II',raw)
                    struct.pack_into('<II',raw,0,site,(info&~255)|3);image['section_data'][key]=bytes(raw);break
            with self.subTest(kind=kind),self.assertRaises(ValueError):
                owner.original_bindings(image,A,proof.rom,proof.mapping,proof.objects,selector=SELECTOR,index=proof.index)
        rows=json.loads(proof.mapping);rows.append({'rom':f'0x{A+2:08X}','end':f'0x{A+4:08X}','mode':'thumb','instrs':1})
        proof.mapping=json.dumps(rows).encode()
        with self.assertRaises(ValueError):native(proof)

    def test_preserved_local_state_and_conditional_scope_are_reported(self):
        proof,*_=fixture();record,_=native(proof)
        restored=record['inventory']['frame']
        self.assertTrue(restored['mutable_local_pointer_slots']['stores'])
        self.assertTrue(restored['mutable_local_pointer_slots']['loads'])
        self.assertTrue(restored['mutable_scalar_word_slots']['stores'])
        self.assertTrue(restored['mutable_halfword_accesses']['writes'])
        self.assertTrue(all(item['local_state_unchanged'] for item in record['roles']['observations']))
        self.assertIn('conditional',record['contract'])
        self.assertIn('No transitive memory effects',record['contract'])
        self.assertFalse(record['inventory']['termination_claim'])
        self.assertFalse(record['inventory']['arithmetic_C_equivalence'])
        self.assertEqual(record['inventory']['numeric_return_facts'],[])
        for role in ('leaf_overwrite','consumer_scratch'):
            self.assertTrue(record['inventory']['frame']['three_call_composition']['contracts'][role])

    def test_changed_toolchain_flags_rejected_before_mock_compiler(self):
        proof,*_=fixture()
        for field,value in (('flags',match.DEFAULT_FLAGS+' -O3'),('cpp','unapproved-cpp'),('assembler','unapproved-as')):
            with self.subTest(field=field),patch.object(match,'Runner') as runner,self.assertRaises(ValueError):
                owner.build(HERE.parents[2],A,args(**{field:value}),selector=SELECTOR)
            runner.assert_not_called()

if __name__=='__main__':unittest.main()
