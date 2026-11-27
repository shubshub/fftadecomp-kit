"""Synthetic ARM ELF and routing regressions, no game ROM or compiler."""
import argparse
import contextlib
import copy
import io
import json
import struct
import unittest
from pathlib import Path
from unittest.mock import patch
import match
import report_fixtures
import owner_admission_profile as owner
import entry_recursive_ordinary_call_profile as entry
from synthetic_entry_owner import ADDRESS as A, HELPER as H, body, bl, snapshots


def environment(data=None):
    data = body() if data is None else data
    mapping, index = snapshots(data)
    rows = json.loads(mapping)
    rows[0]['instrs'] = len(entry._decode(data, A))
    rows[1]['instrs'] = 1
    index = index.replace(b' 10 bx', (' %d bx' % rows[0]['instrs']).encode())
    rom = bytearray(H - match.ROM_BASE + 2)
    rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)] = data
    rom[H-match.ROM_BASE:] = bytes.fromhex('7047')
    return bytes(rom), json.dumps(rows).encode(), index


def elf(data=None, *, linked=False, self_relocation=True, resolved=False,
        size=None, extra=(), relocations=None, align=4):
    """Small real ELF32 section/symbol serializer for the production reader."""
    data = body() if data is None else data
    size = len(data) if size is None else size
    original = bytearray(data)
    if not linked:
        if self_relocation and not resolved:
            original[8:12] = bl(A+8, A+8)
        original[14:18] = bl(A+14, A+14)
    symbols = [('',0,0,0,0), (f'func_{A:08X}', (A if linked else 0)|1,size,0x12,1),
               (f'func_{H:08X}', H|1 if linked else 0,0,0x12,0xfff1 if linked else 0)]
    symbols += list(extra)
    strings = bytearray(b'\0'); encoded = bytearray()
    for name,value,length,info,section in symbols:
        offset = len(strings); strings += name.encode()+b'\0'
        encoded += struct.pack('<IIIBBH',offset,value,length,info,0,section)
    rel = [] if linked else ([(8, (1<<8)|10)] if self_relocation and not resolved else [])+[(14,(2<<8)|10)]
    if relocations is not None: rel = relocations
    relbytes = b''.join(struct.pack('<II',*row) for row in rel)
    names = b'\0.text\0.symtab\0.strtab\0.rel.text\0.shstrtab\0'
    parts = [b'',bytes(original),bytes(encoded),bytes(strings),relbytes,names]
    specs = [(0,0,0,0,0,0,0,0,0,0)]
    offsets = []; raw = bytearray(b'\0'*52)
    for part in parts[1:]:
        while len(raw)%4:raw+=b'\0'
        offsets.append(len(raw));raw+=part
    specs += [(1,1,6,A if linked else 0,offsets[0],len(original),0,0,align,0),
              (7,2,0,0,offsets[1],len(encoded),3,1,4,16),
              (15,3,0,0,offsets[2],len(strings),0,0,1,0),
              (23,9,0,0,offsets[3],len(relbytes),2,1,4,8),
              (33,3,0,0,offsets[4],len(names),0,0,1,0)]
    while len(raw)%4:raw+=b'\0'
    shoff=len(raw)
    raw += b''.join(struct.pack('<IIIIIIIIII',*row) for row in specs)
    raw[:16]=b'\x7fELF\x01\x01\x01'+b'\0'*9
    struct.pack_into('<HHIIIIIHHHHHH',raw,16,2 if linked else 1,40,1,A|1 if linked else 0,0,shoff,0,52,0,0,40,len(specs),5)
    return bytes(raw)


class EntryNativeTests(unittest.TestCase):
    def test_defined_self_native_binding(self):
        rom,mapping,index=environment()
        image=match.elf_image(elf())
        bindings,targets=owner.original_bindings(image,A,rom,mapping,b'{}',selector=entry.SELECTOR,index=index)
        self.assertEqual(bindings['calls'],[[8,f'func_{A:08X}'],[14,f'func_{H:08X}']])
        self.assertEqual(targets[f'func_{A:08X}'],(A,False))


def args(**changes):
    values=dict(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
        objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS,
        mode='thumb', control_flow_profile='ordinary', software_double_profile=None,
        software_double_remainder_profile=None, function_address_profile=None,
        switch_profile=None, label=None, wsl='Ubuntu', wsl_path=match.DEFAULT_WSL_PATH,
        signed_quotient_profile=None, signed_runtime_profile=None,
        addressed_signed_runtime_profile=None, switch_data_profile=None,
        owner_runtime_profile=entry.SELECTOR, emit=None, no_write=True)
    values.update(changes)
    return argparse.Namespace(**values)


class FakeRunner:
    def __init__(self, linked):
        self.linked=linked; self.files={};self.commands=[]
    def read_binary(self, path):
        if path.endswith('/f.i'):return b'/* synthetic preprocessed fixture */'
        if path.endswith('/f.elf'):return self.linked
        return self.files[path]
    def write_text(self,path,text):self.files[path]=text
    def sh(self, command):self.commands.append(command)


class EntryLifecycleTests(unittest.TestCase):
    def bind(self, raw=None, data=None):
        rom,mapping,index=environment(data)
        image=match.elf_image(elf(data) if raw is None else raw)
        bindings,targets=entry.original_bindings(image,A,rom,mapping,index)
        return image,bindings,targets,rom,mapping,index

    def test_assembler_resolved_and_resident_link(self):
        image,bindings,targets,rom,mapping,index=self.bind(elf(resolved=True))
        self.assertEqual(bindings['entry']['resolved'],[8])
        linked=match.elf_image(elf(linked=True))
        self.assertEqual(entry.linked_bytes(image,linked,A,rom,mapping,index,bindings,targets),body())
        linked['symbols'][1]['section']=0xfff1
        with self.assertRaisesRegex(ValueError,'sized .text function'):
            entry.linked_bytes(image,linked,A,rom,mapping,index,bindings,targets)

    def test_defined_self_linker_emission_and_integrity(self):
        image,bindings,targets,rom,mapping,index=self.bind()
        runner=FakeRunner(elf(linked=True))
        data,observed=owner.object_bytes(runner,'/synthetic',args(),image,A,rom,mapping,b'{}',
            selector=entry.SELECTOR,index=index)
        self.assertEqual(data,body());self.assertEqual(observed,bindings)
        definitions=runner.files['/synthetic/f.known.s']
        self.assertNotIn(f'func_{A:08X}',definitions)
        self.assertIn(f'.thumb_set func_{H:08X}',definitions)
        self.assertEqual(len(runner.commands),2)
        changed=bytearray(body());changed[2:4]=bytes.fromhex('0128')
        with self.assertRaisesRegex(ValueError,'outside exact call'):
            entry.linked_bytes(image,match.elf_image(elf(bytes(changed),linked=True)),A,rom,mapping,index,bindings,targets)

    def test_bad_addend_duplicate_and_unrelocated_external(self):
        raw=match.elf_image(elf());raw['text']=raw['text'][:8]+bl(A+8,A+2)+raw['text'][12:]
        rom,mapping,index=environment()
        with self.assertRaisesRegex(ValueError,'zero-addend'):
            entry.original_bindings(raw,A,rom,mapping,index)
        for relocations in ([(8,(1<<8)|10),(8,(1<<8)|10),(14,(2<<8)|10)], [],[(14,(2<<8)|2)]):
            with self.subTest(relocations=relocations), self.assertRaises(ValueError):
                self.bind(elf(relocations=relocations))
        extra=[(f'func_{A:08X}',1,len(body()),0x12,1)]
        with self.assertRaises(ValueError):self.bind(elf(extra=extra))

    def test_interior_self_and_foreign_ownership_refused(self):
        raw=match.elf_image(elf(resolved=True));raw['text']=raw['text'][:8]+bl(A+8,A+2)+raw['text'][12:]
        rom,mapping,index=environment()
        with self.assertRaisesRegex(ValueError,'exact resident entry'):
            entry.original_bindings(raw,A,rom,mapping,index)
        for extra in ([('another',1,2,0x12,1)],[('object',4,4,0x11,1)],[('$a',0,0,0,1)]):
            with self.subTest(extra=extra),self.assertRaises(ValueError):self.bind(elf(extra=extra))
        entries=json.loads(mapping);entries.append({'rom':f'0x{A+2:08X}','end':f'0x{A+4:08X}','mode':'thumb','instrs':1})
        with self.assertRaisesRegex(ValueError,'nonoverlapping'):
            entry.original_bindings(match.elf_image(elf()),A,rom,json.dumps(entries).encode(),index)

    def test_exact_alignment_lifecycle_and_tail_negatives(self):
        # Insert a reached MOV before the final BX, making the sole FUNC 26 bytes.
        data=body()[:-2]+bytes.fromhex('001c')+body()[-2:]
        rom,mapping,index=environment(data)
        original=match.elf_image(elf(data+bytes.fromhex('c046'),size=len(data)))
        bindings,targets=entry.original_bindings(original,A,rom,mapping,index)
        linked=match.elf_image(elf(data+bytes.fromhex('c046'),linked=True,size=len(data)))
        self.assertEqual(entry.linked_bytes(original,linked,A,rom,mapping,index,bindings,targets),data)
        for tail in (b'\0\0',bytes.fromhex('c046c046'),b'\xc0'):
            with self.subTest(tail=tail),self.assertRaises(ValueError):
                entry.original_bindings(match.elf_image(elf(data+tail,size=len(data))),A,rom,mapping,index)
        for kwargs in ({'align':2},{'extra':[('tail',len(data),0,0,1)]},
                       {'relocations':[(len(data),(2<<8)|10)]}):
            with self.subTest(kwargs=kwargs),self.assertRaises(ValueError):
                entry.original_bindings(match.elf_image(elf(data+bytes.fromhex('c046'),size=len(data),**kwargs)),A,rom,mapping,index)
        changed=copy.deepcopy(linked);changed['text']=data+bytes.fromhex('0046')
        with self.assertRaises(ValueError):entry.linked_bytes(original,changed,A,rom,mapping,index,bindings,targets)

    def test_wrong_link_target_foreign_symbol_and_binding_refused(self):
        image,bindings,targets,rom,mapping,index=self.bind()
        data=bytearray(body());data[14:18]=bl(A+14,H+2)
        with self.assertRaisesRegex(ValueError,'BL differs'):
            entry.linked_bytes(image,match.elf_image(elf(bytes(data),linked=True)),A,rom,mapping,index,bindings,targets)
        for extra in ([('foreign',0x080a0001,0,0x12,0xfff1)],[('veneer',A+1,2,0x12,1)]):
            with self.subTest(extra=extra),self.assertRaises(ValueError):
                entry.linked_bytes(image,match.elf_image(elf(linked=True,extra=extra)),A,rom,mapping,index,bindings,targets)
        stale=copy.deepcopy(bindings);stale['entry']['relocations']=[14]
        with self.assertRaisesRegex(ValueError,'manifest differs'):
            entry.linked_bytes(image,match.elf_image(elf(linked=True)),A,rom,mapping,index,stale,targets)

    def test_native_verify_manifest_pins_and_legacy_count(self):
        image,bindings,targets,rom,mapping,index=self.bind()
        with patch.object(entry,'environment_fingerprint',return_value={'fixture':'pins'}):
            manifest,instructions=owner.verify(body(),A,rom,mapping,index,b'{}',bindings=bindings,selector=entry.SELECTOR)
            self.assertEqual(manifest['profile'],entry.NATIVE_SCHEMA)
            self.assertEqual(manifest['ordinary_dependencies'][0]['address'],H)
            self.assertIn('no termination',manifest['contract'])
            stale=copy.deepcopy(manifest);stale['environment']['fixture']='stale'
            with self.assertRaisesRegex(ValueError,'fresh source-bound replay'):
                owner.verify(body(),A,rom,mapping,index,b'{}',stale,bindings=bindings,selector=entry.SELECTOR)
            rows=json.loads(mapping);old_count=rows[0]['instrs'];rows[0]['instrs']=len(body())//2
            legacy=index.replace((' %d bx'%old_count).encode(),(' %d bx'%(len(body())//2)).encode(),1)
            old,_=owner.verify(body(),A,rom,json.dumps(rows).encode(),legacy,b'{}',bindings=bindings,selector=entry.SELECTOR)
            self.assertEqual(old['index_count']['recorded'],12)
            with self.assertRaises(ValueError):owner.verify(body(),A,rom,mapping,index,b'{}',selector=entry.SELECTOR)
        # No explicit entry profile grants any default call-binding exemption.
        with self.assertRaisesRegex(ValueError,'undefined zero-valued'):
            owner.original_bindings(image,A,rom,mapping,b'{}',selector=owner.ACYCLIC_SELECTOR)

    def result(self):
        image,bindings,targets,rom,mapping,index=self.bind()
        with patch.object(entry,'environment_fingerprint',return_value={'fixture':'pins'}):
            manifest,instructions=owner.verify(body(),A,rom,mapping,index,b'{}',bindings=bindings,selector=entry.SELECTOR)
        return (body(),manifest,'a'*64,mapping,index,b'{}',rom,len(instructions),elf())

    def test_canonical_render_and_exact_replay(self):
        result=self.result();report=owner.render(A,result)
        self.assertTrue(owner.selected(report));self.assertEqual(owner.selector_for_report(report),entry.SELECTOR)
        self.assertIn('original_elf_sha256',report)
        with patch.object(owner,'build',return_value=result) as build:
            self.assertTrue(owner.report_matches(report,Path('/synthetic'),A))
            self.assertEqual(build.call_args.kwargs['selector'],entry.SELECTOR)
        altered=report.replace('"source_sha256":"'+'a'*64,'"source_sha256":"'+'b'*64)
        with patch.object(owner,'build',return_value=result):self.assertFalse(owner.report_matches(altered,Path('/synthetic'),A))
        for text in (report+'* verification: `'+owner.ACYCLIC_SCHEMA+'`\n',
                     report+'* function-address: forged\n'):
            with self.subTest(text=text[-70:]),self.assertRaises(ValueError):owner.selected(text)
        with patch.object(owner,'build',side_effect=lambda *a,**kw: (_ for _ in ()).throw(ValueError('stale manifest'))):
            self.assertFalse(owner.report_matches(report,Path('/synthetic'),A))
        token=owner._replay.set(True)
        try:
            with patch.object(owner,'build') as build:
                self.assertFalse(owner.report_matches(report,Path('/synthetic'),A));build.assert_not_called()
        finally:owner._replay.reset(token)

    def test_issue_selector_exclusivity_and_dispatch(self):
        result=self.result()
        with patch.object(owner,'build',return_value=result) as build,contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(owner.issue(Path('/synthetic'),A,args()),0)
            self.assertEqual(build.call_args.kwargs['selector'],entry.SELECTOR)
        for field in ('function_address_profile','addressed_signed_runtime_profile','signed_runtime_profile','switch_data_profile'):
            with self.subTest(field=field),patch.object(owner,'build') as build,self.assertRaises(ValueError):
                owner.issue(Path('/synthetic'),A,args(**{field:'forged'}))
            build.assert_not_called()
        with patch('sys.argv',['match.py','--root','/synthetic','--owner-runtime-profile',entry.SELECTOR,hex(A)]), \
                patch.object(owner,'issue',return_value=7) as issue:
            self.assertEqual(match.main(),7);self.assertEqual(issue.call_args.args[2].owner_runtime_profile,entry.SELECTOR)


class EntryBuildRoutingTests(unittest.TestCase):
    bind=EntryLifecycleTests.bind
    result=EntryLifecycleTests.result

    @contextlib.contextmanager
    def tree(self):
        import tempfile
        base=Path(__file__).resolve().parents[1]/'scratch';base.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='synthetic_owner_',dir=base) as folder:
            root=Path(folder)
            (root/'src').mkdir();(root/'include').mkdir();(root/'config').mkdir();(root/'symbols').mkdir()
            # Inert synthetic source bytes are consumed by a mocked compiler only.
            (root/'src'/f'{A:08X}.c').write_bytes(b'synthetic compiler input fixture\n')
            (root/'include'/'fixture.h').write_bytes(b'synthetic header input\n')
            rom,mapping,index=environment()
            (root/'baserom.bin').write_bytes(rom)
            (root/'config/functions.json').write_bytes(mapping)
            (root/'config/data_symbols.json').write_bytes(b'{}')
            (root/'symbols/functions.txt').write_bytes(index)
            yield root

    @contextlib.contextmanager
    def build_mocks(self, change=None, environment_change=False):
        import match_evidence as evidence
        raw=elf();image=match.elf_image(raw);runners=[]
        def runner_factory(*a,**kw):
            runner=FakeRunner(elf(linked=True));runners.append(runner)
            @contextlib.contextmanager
            def workspace():yield '/synthetic'
            runner.workspace=workspace
            return runner
        def plausible(command,root,timeout):
            self.assertIn('plausible.py',command[1]);self.assertIn('--json',command)
            if change:change(Path(root))
            return object()
        counter=[0]
        def fingerprint():
            counter[0]+=1
            return {'fixture':'changed' if environment_change and counter[0]>2 else 'pins'}
        with patch.object(match,'Runner',side_effect=runner_factory), \
             patch.object(match,'compile_object',return_value=(raw,None,image)) as compile_object, \
             patch.object(match,'_run_replay_process',side_effect=plausible), \
             patch.object(match,'plausibility_result',return_value=([],False)), \
             patch.object(evidence,'report_rom_path',side_effect=lambda root:str(Path(root)/'baserom.bin')), \
             patch.object(entry,'environment_fingerprint',side_effect=fingerprint):
            yield runners,compile_object

    def test_captured_build_and_environment_lifecycle(self):
        with self.tree() as root,self.build_mocks() as (runners,compiler):
            result=owner.build(root,A,selector=entry.SELECTOR)
            self.assertEqual(result[0],body());self.assertEqual(result[-1],elf())
            self.assertEqual(compiler.call_count,1);self.assertEqual(len(runners),1)
            self.assertEqual(len(runners[0].commands),2)
        with self.tree() as root,self.build_mocks(environment_change=True), \
             self.assertRaisesRegex(ValueError,'runtime changed'):
            owner.build(root,A,selector=entry.SELECTOR)

    def test_captured_build_rejects_source_header_and_map_changes(self):
        for kind in ('source','header','mapping'):
            with self.subTest(kind=kind),self.tree() as root:
                def change(capture):
                    target=(root/'src'/f'{A:08X}.c' if kind=='source' else
                            root/'include/fixture.h' if kind=='header' else root/'config/functions.json')
                    target.write_bytes(target.read_bytes()+b'\n')
                with self.build_mocks(change),self.assertRaisesRegex(ValueError,'source, maps, headers or ROM changed'):
                    owner.build(root,A,selector=entry.SELECTOR)

    def test_actual_evidence_and_status_routing(self):
        import match_evidence as evidence
        import status
        result=self.result();report=owner.render(A,result)
        report_fixtures.rom_image(self,result[6])
        with patch.object(owner,'report_matches',return_value=True) as replay:
            self.assertTrue(evidence.report_matches(report_fixtures.carried(report, Path('/synthetic'), A), Path('/synthetic'), A))
            replay.assert_called_once_with(report,Path('/synthetic'),A)
        with self.tree() as root:
            directory=root/'docs/match';directory.mkdir(parents=True)
            (directory/f'{A:08X}.md').write_text(report)
            completed=argparse.Namespace(returncode=0,stdout=(
                f'extent    {len(body())} bytes (complete ELF symbol; synthetic integration; no relocations)\n'
                'verdict MATCH - byte identical\n'))
            with patch.object(status,'report_matches',return_value=True), \
                 patch.object(status.subprocess,'run',return_value=completed) as command:
                values=status.collect(str(root),True,quiet=True,jobs=1)
                self.assertEqual(values[4],[]);self.assertEqual(values[1],1)
                self.assertEqual(command.call_count,1)
                argv=command.call_args.args[0]
                position=argv.index('--owner-runtime-profile')
                self.assertEqual(argv[position+1],entry.SELECTOR)
                self.assertIn('--no-write',argv)

    def test_duplicate_and_wrong_schema_report_refused_before_build(self):
        report=owner.render(A,self.result())
        duplicate=report.replace('"address":'+str(A),'"address":'+str(A)+',"address":'+str(A),1)
        with patch.object(owner,'build') as build:
            self.assertFalse(owner.report_matches(duplicate,Path('/synthetic'),A));build.assert_not_called()
        with patch.object(owner,'build') as build:
            with self.assertRaises(ValueError):owner.selector_for_report(report.replace(entry.NATIVE_SCHEMA,'unknown-entry-schema'))
            build.assert_not_called()


class EntryNativePolicyTests(unittest.TestCase):
    def test_saved_frame_only_and_exact_core_contract_retained(self):
        data=body();rom,mapping,index=environment(data)
        bindings,_=entry.original_bindings(match.elf_image(elf()),A,rom,mapping,index)
        with patch.object(entry,'environment_fingerprint',return_value={'fixture':'pins'}):
            manifest,_=owner.verify(data,A,rom,mapping,index,b'{}',bindings=bindings,selector=entry.SELECTOR)
        self.assertGreater(manifest['proof']['frame']['maximum_frame_bytes'],0)
        for push in ('11b5','00b5'):
            # R0 spill is forbidden; missing preserved-R4 restoration is rejected.
            changed=bytes.fromhex(push)+body()[2:]
            rom,mapping,index=environment(changed)
            bindings,_=entry.original_bindings(match.elf_image(elf(changed)),A,rom,mapping,index)
            with self.subTest(push=push),self.assertRaises(ValueError):
                owner.verify(changed,A,rom,mapping,index,b'{}',bindings=bindings,selector=entry.SELECTOR)

    TASK=Path(__file__).resolve().parents[1]
    FROZEN=TASK.parent/'matching-entry-recursive-ordinary-call278/staged/tools/entry_recursive_ordinary_call_profile.py'
    R7=TASK.parent/'matching-static-callback-r7-integration280/tools/static_callback_target_preservation_profile.py'

    @unittest.skipUnless(FROZEN.is_file() and R7.is_file(), 'frozen sibling work trees are not present')
    def test_frozen_sibling_trees_are_retained(self):
        task,frozen,r7=self.TASK,self.FROZEN,self.R7
        self.assertTrue(Path(entry.__file__).read_bytes().startswith(frozen.read_bytes()))
        self.assertEqual((task/'tools'/r7.name).read_bytes(),r7.read_bytes())
        original=(r7.parent/'owner_admission_profile.py').read_text()
        a=original.index('    if args.owner_runtime_profile == r7_buffer.SELECTOR and any(')
        b=original.index('    result=build',a)
        self.assertIn(original[a:b],Path(owner.__file__).read_text())


if __name__ == '__main__':unittest.main()



