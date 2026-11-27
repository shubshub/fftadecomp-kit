"""Synthetic compilation lifecycle and strict transport; no real tool execution."""
from contextlib import contextmanager, ExitStack
import copy
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path[:0] = [str(Path(__file__).resolve().parents[1]/'tools')]
import match
import report_fixtures
import match_evidence as evidence
import palette_source_admission_profile as admission
import palette_certificate_authority as authority
import palette_native_closure as closure
import status
from test_palette_native_closure import Fixture, A, H, DATA, elf, pin, symbol


class PaletteSourceTests(unittest.TestCase):
    def setUp(self):
        self.f = Fixture()
        self.tools = [[name, str(i)*64] for i, name in enumerate((match.DEFAULT_CC, match.DEFAULT_CPP,
            match.DEFAULT_AS, match.DEFAULT_OBJCOPY, match.DEFAULT_LD), 1)]
        self.environment = dict(toolchain=self.tools, runtime={'synthetic': True})
        self.prior = dict(address=A, end=A+len(self.f.body), instructions=9,
            source_sha256=admission.sha(self.f.source), ROM_sha256=admission.sha(self.f.rom),
            body_sha256=admission.sha(self.f.body), environment=self.environment,
            bindings=closure.bindings_for(self.f.c['inventory']), conditional_full_owner_closure=True,
            dependency_context=dict(owner=[A,A+len(self.f.body),9,admission.sha(self.f.body)],
                helper=[H,H+2,1,admission.sha(b'\x70\x47')]),
            native_admission=False, source_or_ELF_admission=False, physical_memory_permission=False,
            unconditional_termination=False, required_unproved_conditions=['synthetic target ABI',
                'live typed objects and frame noninterference'],
            retained_obligations={'nested': {'physical_permission': False, 'incoming_words': [0,4]}})
        self.artifacts = dict(original=self.f.original, linked=self.f.linked,
            closure=json.dumps(self.prior,sort_keys=True).encode())
        self.stack = ExitStack(); self.addCleanup(self.stack.close)
        self.stack.enter_context(patch.object(authority,'TRUSTED_PINS',{k:pin(v)for k,v in self.artifacts.items()}))
        self.stack.enter_context(patch.object(admission,'toolchain_fingerprint',return_value=self.tools))
        self.stack.enter_context(patch.object(admission,'runtime_fingerprint',return_value={'synthetic':True}))
        self.stack.enter_context(patch.object(admission,'producer_fingerprint',return_value={'synthetic.py':'a'*64}))
        self.stack.enter_context(patch.object(closure,'environment_fingerprint',return_value=self.environment))
        self.bundle = authority.encode(self.artifacts)
        self.commands, self.writes, self.captures = [], {}, []
        self.original, self.linked = self.f.original, self.f.linked
        self.after_link = None
        self.post_check = None
        self.case_findings = []
        self.bad_dependency = False
        self.fixture = self

    def args(self, **values):
        args=admission.default_arguments(); args.emit=None; args.no_write=True
        for key,value in values.items():setattr(args,key,value)
        return args

    @contextmanager
    def project(self):
        disk = Path(__file__).resolve().parents[1]/'build'
        disk.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='palette_synthetic_',dir=disk) as name:
            root=Path(name)
            for relative,data in {f'src/{A:08X}.c':self.f.source, 'include/types.h':b'/* synthetic */',
                    'src/local.h':b'/* local header */', 'config/functions.json':self.f.mapping,
                    'symbols/functions.txt':self.f.index,'config/data_symbols.json':self.f.objects,
                    'synthetic.rom':self.f.rom,'bundle.json':self.bundle}.items():
                path=root/relative;path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(data)
            case=self
            class Runner:
                def __init__(self,*args,**kwargs):
                    self.root=Path(kwargs['root']);case.captures.append(self.root)
                @contextmanager
                def workspace(self):yield str(self.root/'build/work')
                def sh(self,command):
                    case.commands.append(command)
                    if '--fatal-warnings' in command and case.after_link:case.after_link()
                    return ''
                def write_text(self,path,value):case.writes[Path(path).name]=value
                def read_binary(self,path):
                    basename=Path(path).name
                    return {'f.o':case.original,'f.elf':case.linked,'f.bin':bytes(case.f.original_text),
                        'f.i':(f'# 1 "src/{A:08X}.c"\n# 1 "'+
                            ('external.h' if case.bad_dependency else 'include/types.h')+'"\n').encode()+case.f.source,
                        'f.s':b'/* synthetic assembly, never assembled */'}[basename]
            def plausible(*args,**kwargs):
                if case.post_check:case.post_check(root)
                return subprocess.CompletedProcess(args, int(bool(case.case_findings)), json.dumps(dict(
                    findings=case.case_findings,total=len(case.case_findings),addr=f'0x{A:08X}',
                    hand_asm_allowed=False,allow_entry=None)), '')
            with patch.object(match,'Runner',Runner),patch.object(match,'_run_replay_process',side_effect=plausible), \
                    patch.object(evidence,'report_rom_path',return_value=root/'synthetic.rom'):
                yield root

    def compile(self,root,**kwargs):
        return admission.build(root,A,self.args(palette_closure_bundle='bundle.json'),**kwargs)

    def test_fresh_compile_preserves_every_nested_condition_and_false_flag(self):
        with self.project() as root,patch.object(closure,'verify_original',side_effect=AssertionError('old closure replay')):
            result=self.compile(root)
        manifest=result['manifest']; transport=manifest['transport']
        self.assertEqual(transport['transported_conditional_closure'],self.prior)
        self.assertTrue(manifest['fresh_fixed_compiler_source_origin'])
        self.assertTrue(transport['fresh_fixed_compiler_source_replay_required'])
        for key in ('native_admission','source_or_ELF_admission','physical_memory_permission','unconditional_termination'):
            self.assertIs(manifest[key],False);self.assertIs(transport[key],False)
        self.assertEqual(authority.decode(manifest['artifact_bundle'].encode()),self.artifacts)
        self.assertEqual(result['body'],self.f.body);self.assertEqual(result['instructions'],9)
        self.assertTrue(all(not path.exists() for path in self.captures))
        self.assertEqual(len(self.commands),6)
        self.assertIn('-nostdinc -undef -I include',self.commands[0])
        self.assertIn(match.DEFAULT_CC+' '+match.DEFAULT_FLAGS,self.commands[1])
        self.assertIn('--fatal-warnings --no-undefined --no-relax --orphan-handling=error',self.commands[-1])
        self.assertIn('.type memcpy, %function',self.writes['f.known.s'])
        self.assertEqual(self.writes['f.known.s'].count('%object'),2)

    def test_binding_plan_derives_only_original_typed_identities(self):
        result=admission.binding_plan(self.f.original,A,self.bundle,self.f.objects)
        self.assertEqual(result,dict(memcpy=(H|1,2),**{k:(v,1)for k,v in DATA.items()}))

    def test_authentication_rejects_self_selected_bundle(self):
        values=json.loads(self.bundle);values['closure']=values['original']
        with self.project() as root:
            (root/'bundle.json').write_text(admission.text(values))
            with self.assertRaisesRegex(ValueError,'authority'):self.compile(root)
        self.assertEqual(self.commands,[])

    def test_noncanonical_bundle_rejected_before_compiler(self):
        with self.project() as root:
            (root/'bundle.json').write_bytes(b' '+self.bundle)
            with self.assertRaisesRegex(ValueError,'canonical'):self.compile(root)
        self.assertEqual(self.commands,[])

    def test_wrong_selector_and_all_mixed_profiles_reject(self):
        for key,value in [('owner_runtime_profile','ordinary'),('mode','arm'),('control_flow_profile','inert'),
                ('label','x'),('wsl','x'),('wsl_path','x'),('flags','-O3'),('cc','foreign'),
                ('cpp','foreign'),('assembler','foreign'),('linker','foreign'),('objcopy','foreign')]+[
                (key,'x')for key in ('signed_runtime_profile','unsigned_runtime_profile','signed_quotient_profile',
                'unsigned_quotient_profile','addressed_signed_runtime_profile','software_double_profile',
                'software_double_remainder_profile','function_address_profile','switch_profile','switch_data_profile')]:
            with self.subTest(key=key),self.assertRaises(ValueError):admission.configuration(self.args(**{key:value}))

    def test_unique_source_required_before_compiler(self):
        with self.project() as root:
            (root/'src/sub').mkdir();(root/f'src/sub/{A:08X}.c').write_bytes(self.f.source)
            with self.assertRaisesRegex(ValueError,'unique'):self.compile(root)
        self.assertEqual(self.commands,[])

    def test_changed_source_rejected_before_compiler(self):
        with self.project() as root:
            (root/f'src/{A:08X}.c').write_bytes(self.f.source+b' ')
            with self.assertRaisesRegex(ValueError,'frozen source'):self.compile(root)
        self.assertEqual(self.commands,[])

    def test_changed_full_rom_rejected_before_compiler(self):
        with self.project() as root:
            (root/'synthetic.rom').write_bytes(self.f.rom+b'\0')
            with self.assertRaisesRegex(ValueError,'ROM'):self.compile(root)
        self.assertEqual(self.commands,[])

    def test_current_owner_count_guard_precedes_compilation(self):
        with self.project() as root:
            rows=json.loads(self.f.mapping);rows[0]['instrs']+=1
            (root/'config/functions.json').write_text(json.dumps(rows))
            with self.assertRaises(ValueError):self.compile(root)
        self.assertEqual(self.commands,[])

    def test_current_helper_count_guard_precedes_compilation(self):
        with self.project() as root:
            (root/'symbols/functions.txt').write_bytes(self.f.index.replace(b'2 1\n',b'2 2\n'))
            with self.assertRaises(ValueError):self.compile(root)
        self.assertEqual(self.commands,[])

    def test_current_data_alias_collision_rejected_before_compilation(self):
        with self.project() as root:
            rows=json.loads(self.f.objects);rows['foreign']=rows[next(iter(DATA))]
            (root/'config/data_symbols.json').write_text(json.dumps(rows))
            with self.assertRaises(ValueError):self.compile(root)
        self.assertEqual(self.commands,[])

    def test_fixed_toolchain_authority_checked_before_compiler(self):
        with self.project() as root,patch.object(admission,'toolchain_fingerprint',return_value=[['foreign','b'*64]]):
            with self.assertRaisesRegex(ValueError,'toolchain'):self.compile(root)
        self.assertEqual(self.commands,[])

    def test_original_text_change_refuses_before_link(self):
        data=bytearray(self.f.original_text);data[0]^=1
        self.original=elf(bytes(data),self.f.original_symbols,self.f.relocations)
        with self.assertRaisesRegex(ValueError,'original text'):
            admission.binding_plan(self.original,A,self.bundle,self.f.objects)

    def test_extra_undefined_or_wrong_original_symbol_type_refuses(self):
        for symbols in (self.f.original_symbols+[symbol('foreign',0,0)],
                self.f.original_symbols[:2]+[dict(self.f.original_symbols[2],type=1)]+self.f.original_symbols[3:]):
            with self.subTest(symbols=symbols),self.assertRaises(ValueError):
                admission.binding_plan(elf(bytes(self.f.original_text),symbols,self.f.relocations),A,self.bundle,self.f.objects)

    def test_nonzero_original_call_or_data_addend_refuses(self):
        for site in (6,20):
            raw=bytearray(self.f.original_text);raw[site]^=2
            with self.subTest(site=site),self.assertRaises(ValueError):
                admission.binding_plan(elf(bytes(raw),self.f.original_symbols,self.f.relocations),A,self.bundle,self.f.objects)

    def test_link_cannot_mutate_original_object(self):
        self.after_link=lambda:setattr(self,'original',self.original+b'changed')
        with self.project() as root,self.assertRaisesRegex(ValueError,'object changed'):self.compile(root)

    def test_linked_unrelocated_byte_change_refuses(self):
        raw=bytearray(self.f.body);raw[0]^=1
        self.linked=elf(bytes(raw),self.f.linked_symbols,[],linked=True)
        with self.project() as root,self.assertRaisesRegex(ValueError,'linked body'):self.compile(root)

    def test_linked_data_function_type_swap_refuses(self):
        symbols=copy.deepcopy(self.f.linked_symbols);symbols[2]['type']=1
        self.linked=elf(self.f.body,symbols,[],linked=True)
        with self.project() as root,self.assertRaisesRegex(ValueError,'typed linked'):self.compile(root)

    def test_untracked_preprocessor_dependency_refuses(self):
        self.bad_dependency=True
        with self.project() as root,self.assertRaisesRegex(ValueError,'untracked include'):self.compile(root)
        self.assertEqual(len(self.commands),1)

    def test_plausibility_finding_refuses(self):
        self.case_findings=[dict(file='x.c',rule='asm',severity='error',message='synthetic rejection',line=1)]
        with self.project() as root,self.assertRaisesRegex(ValueError,'implausible'):self.compile(root)

    def test_header_change_during_compile_refuses(self):
        self.post_check=lambda root:(root/'include/types.h').write_bytes(b'changed')
        with self.project() as root,self.assertRaisesRegex(ValueError,'changed'):self.compile(root)

    def test_map_change_during_compile_refuses(self):
        self.post_check=lambda root:(root/'config/functions.json').write_bytes(self.f.mapping+b' ')
        with self.project() as root,self.assertRaisesRegex(ValueError,'changed'):self.compile(root)

    def test_runtime_change_during_compile_refuses(self):
        with self.project() as root,patch.object(admission,'runtime_fingerprint',side_effect=[{'synthetic':True},{'changed':True}]):
            with self.assertRaisesRegex(ValueError,'changed'):self.compile(root)

    def test_producer_change_during_compile_refuses(self):
        with self.project() as root,patch.object(admission,'producer_fingerprint',side_effect=[{'x':'a'},{'x':'b'}]):
            with self.assertRaisesRegex(ValueError,'changed'):self.compile(root)

    def test_report_replay_uses_embedded_bundle_and_exact_manifest(self):
        with self.project() as root:
            result=self.compile(root);report=admission.render(result)
            (root/'bundle.json').unlink()
            with patch.object(admission,'build',return_value=result) as replay:
                self.assertTrue(evidence.report_matches(report_fixtures.carried(report, root, A), root, A))
                self.assertEqual(replay.call_args.kwargs['expected'],result['manifest'])
            self.assertEqual(admission.bundle_for(root,A,self.args(),result['manifest']),self.bundle)

    def test_saved_context_tampering_rejects_without_compile(self):
        with self.project() as root:
            result=self.compile(root)
            for key in ('source_sha256','mapping_sha256','index_sha256','objects_sha256','rom_sha256','toolchain','runtime'):
                changed=copy.deepcopy(result);changed[key]='stale'
                with self.subTest(key=key),patch.object(admission,'build',side_effect=AssertionError('unexpected compile')):
                    self.assertFalse(admission.report_matches(admission.render(changed),root,A))
            result['manifest']['producer_source_sha256']={'stale':'x'}
            with patch.object(admission,'build',side_effect=AssertionError('unexpected compile')):
                self.assertFalse(admission.report_matches(admission.render(result),root,A))

    def test_saved_bundle_replacement_and_nested_premise_tampering_reject(self):
        with self.project() as root:
            result=self.compile(root)
            with self.assertRaisesRegex(ValueError,'replace embedded'):
                admission.bundle_for(root,A,self.args(palette_closure_bundle='bundle.json'),result['manifest'])
            expected=copy.deepcopy(result['manifest']);expected['transport']['physical_memory_permission']=True
            with self.assertRaisesRegex(ValueError,'manifest differs'):
                admission.build(root,A,expected=expected)

    def test_saved_noncanonical_or_duplicate_evidence_refuses(self):
        with self.project() as root:
            report=admission.render(self.compile(root))
            prefix='* palette source evidence: `'
            changed=report.replace(prefix,prefix+' ')
            with self.assertRaisesRegex(ValueError,'canonical'):admission.saved_evidence(changed)
            row=next(line for line in report.splitlines()if line.startswith(prefix))
            with self.assertRaisesRegex(ValueError,'one bounded'):admission.saved_evidence(report+row+'\n')

    def test_cli_isolated_dispatch_and_bundle_without_selector_refuses(self):
        import runpy
        main_path=Path(match.__file__)
        with self.project() as root:
            argv=[str(main_path),'--root',str(root),f'{A:08X}','--owner-runtime-profile',admission.SELECTOR,
                  '--palette-closure-bundle','bundle.json','--no-write']
            with patch.object(sys,'argv',argv),patch.object(admission,'issue',return_value=0) as issue:
                with self.assertRaises(SystemExit) as stopped:runpy.run_path(str(main_path),run_name='__main__')
                self.assertEqual(stopped.exception.code,0);self.assertEqual(issue.call_args.args[1],A)
            argv=[str(main_path),'--root',str(root),f'{A:08X}','--palette-closure-bundle','bundle.json']
            with patch.object(sys,'argv',argv),self.assertRaisesRegex(SystemExit,'requires the isolated'):
                runpy.run_path(str(main_path),run_name='__main__')

    def test_status_propagates_selector_and_reuses_embedded_bundle(self):
        with self.project() as root:
            result=self.compile(root);report=admission.render(result)
            target=root/'docs/match'/f'{A:08X}.md';target.parent.mkdir(parents=True);target.write_text(report)
            calls=[]
            def run(command,*args,**kwargs):
                calls.append(command)
                return subprocess.CompletedProcess(command,0,'verdict MATCH - byte identical','')
            with patch.object(status.subprocess,'run',side_effect=run), \
                    patch.object(status,'report_matches',return_value=True) as checked:
                status.collect(str(root),verify=True,quiet=True)
                checked.assert_called_once_with(report,str(root),A)
            self.assertTrue(calls)
            self.assertIn(admission.SELECTOR,calls[0]);self.assertNotIn('--palette-closure-bundle',calls[0])

    def test_issue_keeps_exact_machine_verdict_and_explicit_conditional_scope(self):
        with self.project() as root:
            args=self.args(palette_closure_bundle='bundle.json',no_write=False)
            with patch.object(sys,'stdout',new_callable=io.StringIO) as output:
                self.assertEqual(admission.issue(root,A,args),0)
            lines=output.getvalue().splitlines()
            self.assertIn('verdict MATCH - byte identical',lines)
            self.assertTrue(any('native admission remains false' in line for line in lines))
            report=(root/'docs/match'/f'{A:08X}.md').read_text()
            self.assertEqual(admission.selector_for_report(report),admission.SELECTOR)
            self.assertFalse(admission.saved_evidence(report)['manifest']['native_admission'])

    def test_status_does_not_accept_cli_success_with_invalid_saved_palette_report(self):
        with self.project() as root:
            report=admission.render(self.compile(root));target=root/'docs/match'/f'{A:08X}.md'
            target.parent.mkdir(parents=True);target.write_text(report)
            with patch.object(status.subprocess,'run',return_value=subprocess.CompletedProcess([],0,
                    'verdict MATCH - byte identical','')),patch.object(status,'report_matches',return_value=False) as checked:
                result=status.collect(str(root),verify=True,quiet=True)
                checked.assert_called_once()
                self.assertIn('DOES NOT MATCH',str(result))

    def test_real_synthetic_report_replay_needs_no_external_certificate_files(self):
        with self.project() as root:
            first=self.compile(root);report=admission.render(first)
            target=root/'docs/match'/f'{A:08X}.md';target.parent.mkdir(parents=True);target.write_text(report)
            (root/'bundle.json').unlink()
            with patch.object(closure,'verify_original',side_effect=AssertionError('old closure replay')):
                self.assertTrue(admission.report_matches(report,root,A))
                # A separate CLI invocation can obtain the same authority from the report.
                self.assertEqual(admission.bundle_for(root,A,self.args(),None),self.bundle)
            self.assertEqual(len(self.commands),12)  # Two synthetic compiler lifecycles, no real command.

    def test_stale_header_before_report_replay_stops_before_compilation(self):
        with self.project() as root:
            report=admission.render(self.compile(root));(root/'src/local.h').write_bytes(b'changed')
            with patch.object(admission,'build',side_effect=AssertionError('unexpected compile')):
                self.assertFalse(admission.report_matches(report,root,A))

    def test_captured_header_change_during_plausibility_is_rejected(self):
        self.post_check=lambda root:(self.captures[-1]/'include/types.h').write_bytes(b'changed')
        with self.project() as root,self.assertRaisesRegex(ValueError,'changed'):self.compile(root)

    def test_full_rom_mutation_after_transport_is_rejected(self):
        self.post_check=lambda root:(root/'synthetic.rom').write_bytes(self.f.rom+b'changed')
        with self.project() as root,self.assertRaisesRegex(ValueError,'changed'):self.compile(root)

    def test_toolchain_mutation_after_transport_is_rejected(self):
        with self.project() as root,patch.object(admission,'toolchain_fingerprint',side_effect=[self.tools,[]]):
            with self.assertRaisesRegex(ValueError,'changed'):self.compile(root)

    def test_canonical_named_data_value_change_is_rejected(self):
        values=dict(DATA);values[next(iter(values))]+=4
        with self.assertRaisesRegex(ValueError,'typed binding'):
            admission.binding_plan(self.f.original,A,self.bundle,
                json.dumps({name:f'0x{point:08X}'for name,point in values.items()}).encode())

    def test_complete_original_section_and_thumb_ownership_guards(self):
        symbols=copy.deepcopy(self.f.original_symbols);symbols[1]['value']=0
        shorter=copy.deepcopy(self.f.original_symbols);shorter[1]['size']-=2
        for original in (elf(bytes(self.f.original_text),self.f.original_symbols,self.f.relocations,extra_allocated=True),
                elf(bytes(self.f.original_text),symbols,self.f.relocations),
                elf(bytes(self.f.original_text),shorter,self.f.relocations)):
            with self.subTest(original=admission.sha(original)),self.assertRaises(ValueError):
                admission.binding_plan(original,A,self.bundle,self.f.objects)

    def test_mixed_report_selector_and_changed_evidence_hash_failclosed(self):
        with self.project() as root:
            result=self.compile(root);report=admission.render(result)
            with self.assertRaisesRegex(ValueError,'mixed'):
                admission.selector_for_report(report+'* verification: `foreign`\n')
            altered=report.replace('* palette source proof SHA-256: `', '* palette source proof SHA-256: `0')
            with patch.object(admission,'build',return_value=result):
                self.assertFalse(admission.report_matches(altered,root,A))

    def test_disabled_palette_selector_keeps_ordinary_dispatch(self):
        with self.assertRaises(FileNotFoundError),self.project() as root:
            admission.bundle_for(root,A,self.args(),None)
        self.assertIsNone(admission.selector_for_report('* verification: `ordinary`\n'))


if __name__ == '__main__':unittest.main()
