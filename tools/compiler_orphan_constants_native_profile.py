"""Explicit fixed-O0 compiler-orphan exclusion with unchanged native replay."""
import argparse
from contextvars import ContextVar
import hashlib
import json
from pathlib import Path
import shlex
import struct
import subprocess
import sys
import tempfile

import match
import match_evidence as evidence
import owner_admission_profile as owner
import compiler_orphan_constants_prerequisite as prerequisite
from inert_spin_profile import index_snapshot
from software_double_profile import indices,span_record

SELECTOR = 'compiler-orphan-address-constants-O0-v1'
SCHEMA = 'elf-symbol-thumb-compiler-orphan-address-constants-O0-v1'
FLAGS = '-mthumb-interwork -O0'
POLICY = 'explicit ld /DISCARD/ of original f.o(.rodata) only after complete orphan prerequisite; no GC, ELF rewriting or source rewriting'
_replay = ContextVar('compiler_orphan_constants_replay',default=False)


def text(value):
    return json.dumps(value,sort_keys=True,separators=(',',':'))


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def configuration():
    return argparse.Namespace(cc=match.DEFAULT_CC,cpp=match.DEFAULT_CPP,assembler=match.DEFAULT_AS,
        objcopy=match.DEFAULT_OBJCOPY,linker=match.DEFAULT_LD,flags=FLAGS)


def fixed_configuration(args):
    expected=configuration()
    if any(getattr(args,key,None) != getattr(expected,key) for key in vars(expected)):
        raise ValueError('orphan constants require their fixed approved O0 toolchain configuration')


def environment_fingerprint():
    from addressed_signed_runtime_profile import toolchain_fingerprint,runtime_fingerprint
    return dict(toolchain=toolchain_fingerprint(),runtime=runtime_fingerprint(),flags=FLAGS,
        producers={path.name:sha(path.read_bytes()) for path in Path(__file__).parent.glob('*.py')})


def object_bytes(runner,workspace,args,original_elf,address,mapping,rom,objects,*,selector,policy=POLICY,index=None):
    fixed_configuration(args)
    if selector != SELECTOR or policy != POLICY:
        raise ValueError('orphan constants require their explicit isolated linker policy')
    preprocessed=runner.read_binary(workspace+'/f.i')
    if runner.read_binary(workspace+'/f.o') != original_elf:
        raise ValueError('orphan constants require unchanged actual original compiler object')
    inventory=prerequisite.verify(original_elf,address,objects,preprocessed,selector=prerequisite.SELECTOR,mapping=mapping,index=index,rom=rom)
    original=match.elf_image(original_elf)
    entries=json.loads(mapping)
    names=match.parse_data_symbols(objects)
    calls,targets,literals,functions={}, {}, {}, {}
    bindings=dict(calls=[],data=[],functions=[],switches=[])
    for section_id in original['relocations']:
        section=original['sections'][section_id]
        if section[7] != original['text_index']:
            continue
        symbols=original['symbol_tables'][section[6]]
        payload=original['section_data'][section_id]
        for position in range(0,len(payload),8):
            site,info=struct.unpack_from('<II',payload,position)
            name=symbols[info>>8]['name']
            if info&255 == 10:
                target=match.function_address_target(name,entries,address,len(original['text']),len(rom))
                calls[address+site]=target;targets[name]=target
                bindings['calls'].append([site,name])
            elif name.startswith('func_'):
                target=match.function_address_target(name,entries,address,len(original['text']),len(rom))
                targets[name]=target;functions[site]=(name,target|1)
                bindings['functions'].append([site,name])
            else:
                addend=struct.unpack_from('<i',original['text'],site)[0]
                targets[name]=names[name];literals[site]=(name,names[name]+addend)
                bindings['data'].append([site,name,addend])
    for records in bindings.values():records.sort()
    # This is a separate opt-in original linker invocation. Its input object is
    # never rewritten. The only excluded input section was authenticated above.
    definitions=['.syntax unified','.thumb']
    for name,target in sorted(targets.items()):
        is_data=name in names
        definitions += [f'.global {name}',f'.type {name}, %'+('object' if is_data else 'function'),
            f'.set {name}, 0x{target:08X}' if is_data else f'.thumb_set {name}, 0x{target|1:08X}']
    runner.write_text(workspace+'/f.known.s','\n'.join(definitions)+'\n')
    script=(f'SECTIONS {{ .text 0x{address:08X} : {{ *(.text) *(.glue_7) *(.glue_7t) }} '
        '.data 0 : { *(.data) } .bss 0 : { *(.bss) } '
        '.ARM.attributes 0 : { *(.ARM.attributes) } '
        '.unexpected 0 : { *(.vfp11_veneer) *(.v4_bx) *(.iplt) *(.igot.plt) } '
        '.rel.iplt 0 : { *(.rel.iplt) } ASSERT(SIZEOF(.unexpected)==0,"unexpected stubs") '
        'ASSERT(SIZEOF(.rel.iplt)==0,"unexpected relocations") '
        '/DISCARD/ : { '+json.dumps(workspace+'/f.o')+'(.rodata) } }')
    runner.write_text(workspace+'/f.ld',script)
    quoted=shlex.quote(workspace)
    command=(f'{args.linker} --fatal-warnings --no-undefined --no-relax --orphan-handling=error '
        f'-T {quoted}/f.ld -e func_{address:08X} {quoted}/f.o {quoted}/f.known.o -o {quoted}/f.elf')
    runner.sh(f'{args.assembler} -mthumb-interwork {quoted}/f.known.s -o {quoted}/f.known.o')
    runner.sh(command)
    linked_elf=runner.read_binary(workspace+'/f.elf')
    linked=match.elf_image(linked_elf)
    header=struct.unpack_from('<HHIIIIIHHHHHH',linked_elf,16)
    section_names=linked['section_data'][header[12]]
    if any(section_names[row[0]:section_names.index(b'\0',row[0])] == b'.rodata'
           for row in linked['sections']):
        raise ValueError('orphan linker did not exclude the authenticated section')
    if linked['sections'][linked['text_index']][2] != 6:
        raise ValueError('orphan linker changed executable text flags')
    for name,target in targets.items():
        definitions=[row for row in linked['symbols'] if row['name'] == name]
        is_data=name in names
        if len(definitions) != 1 or definitions[0]['section'] != 0xfff1 or \
                definitions[0]['type'] != (1 if is_data else 2) or definitions[0]['bind'] != 1 or \
                definitions[0]['size'] or definitions[0]['value'] != (target if is_data else target|1):
            raise ValueError('orphan linked identity is not the original unique typed absolute global')
    data=match.linked_function_bytes(original,linked,f'func_{address:08X}',address,calls,targets,literals,function_relocations=functions)
    decoder=match.Cs(match.CS_ARCH_ARM,match.CS_MODE_THUMB);decoder.detail=True
    for site,target in calls.items():
        offset=site-address
        item=next(decoder.disasm(data[offset:offset+4],site,count=1),None)
        if item is None or item.id != match.ARM_INS_BL or item.size != 4 or item.operands[0].imm != target:
            raise ValueError('orphan linked BL target differs from original authenticated identity')
    if runner.read_binary(workspace+'/f.o') != original_elf or runner.read_binary(workspace+'/f.i') != preprocessed:
        raise ValueError('original compiler inputs changed during orphan exclusion link')
    if any(row[2]&2 and row[5] and number != linked['text_index']
           for number,row in enumerate(linked['sections'])):
        raise ValueError('orphan linker retained allocated companion bytes')
    return data,bindings,dict(prerequisite=inventory,original_elf_sha256=sha(original_elf),
        linked_elf_sha256=sha(linked_elf),preprocessed_source_sha256=sha(preprocessed),
        linker_policy=policy,linker_options=['--fatal-warnings','--no-undefined','--no-relax',
            '--orphan-handling=error','-e',f'func_{address:08X}'],linker_script_template=script.replace(workspace,'<workspace>'),
        excluded_bytes=inventory['orphan_section']['bytes'],excluded_ROM_credit=0)


def build(root,address,args=None,expected=None,*,selector=SELECTOR,capture_dir=None):
    if selector != SELECTOR:
        raise ValueError('unknown compiler orphan constants native selector')
    if capture_dir is not None and Path(capture_dir).exists():
        raise ValueError('orphan native artifact capture directory must not exist')
    args=args or configuration()
    fixed_configuration(args)
    root=Path(root)
    capture=Path(capture_dir) if capture_dir is not None else None
    source=evidence.source_fingerprint(root,address)
    mapping=evidence.mapping_snapshot(root);index=index_snapshot(root);objects=evidence.data_snapshot(root)
    rom_path=evidence.report_rom_path(root);rom=Path(rom_path).read_bytes()
    environment=environment_fingerprint()
    entries,rows=indices(mapping,index)
    candidates=list((root/'src').rglob(f'{address:08X}.c'))
    if len(candidates) != 1:
        raise ValueError('orphan native profile requires one unique source')
    (root/'build').mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='orphan_native_',dir=root/'build') as directory:
        captured=Path(directory)
        for path in evidence.source_paths(root,address):
            target=captured/path.relative_to(root);target.parent.mkdir(parents=True,exist_ok=True)
            target.write_bytes(path.read_bytes())
        captured_sources={path.relative_to(captured):path.read_bytes()
            for path in evidence.source_paths(captured,address)}
        if evidence.source_fingerprint(captured,address) != source:
            raise ValueError('orphan native captured source differs')
        commands=[]
        class CapturedRunner(match.Runner):
            def sh(self,command):
                commands.append(command)
                return super().sh(command)
        runner=CapturedRunner(match.DEFAULT_CC,'Ubuntu',match.DEFAULT_WSL_PATH,root=captured,timeout=120)
        with runner.workspace() as workspace:
            try:
                original,_,_=match.compile_object(runner,workspace,args,captured,address,
                    candidates[0].relative_to(root).as_posix())
                data,bindings,transport=object_bytes(runner,workspace,args,original,address,mapping,rom,objects,
                    selector=selector,index=index)
                # No compiler or ELF policy is inherited here. Reuse only the
                # existing full linked-byte native structural/frame/alias proof.
                spans=[]
                for target in sorted({address}|{int(name[5:],16) for _,name in bindings['calls']+bindings['functions']}):
                    candidates=[row for row in entries if int(row['rom'],16) == target]
                    if len(candidates) != 1:
                        raise ValueError('orphan native requires unique dual-index call ownership')
                    end=int(candidates[0]['end'],16)
                    if end % 2:
                        raise ValueError('orphan target extent is not Thumb aligned')
                    row=span_record(target,end,entries,rows,rom)
                    spans.append(dict(address=target,end=end,instructions=row['instrs'],
                        body_sha256=sha(rom[target-match.ROM_BASE:end-match.ROM_BASE])))
                native,instructions=owner.verify(data,address,rom,mapping,index,objects,
                    bindings=bindings,selector=owner.ACYCLIC_SELECTOR,source_fingerprint=source)
            finally:
                if capture is not None:
                    capture.mkdir(parents=True,exist_ok=False)
                    for relative,raw in captured_sources.items():
                        target=capture/'source'/relative;target.parent.mkdir(parents=True,exist_ok=True)
                        target.write_bytes(raw)
                    for name in ('f.i','f.s','f.o','f.known.s','f.known.o','f.ld','f.elf'):
                        try:
                            raw=runner.read_binary(workspace+'/'+name)
                        except FileNotFoundError:
                            continue
                        target=capture/'compiler'/name;target.parent.mkdir(parents=True,exist_ok=True)
                        target.write_bytes(raw)
                    (capture/'commands.txt').write_text('\n'.join(commands)+'\n')
        result=match._run_replay_process([sys.executable,str(Path(__file__).with_name('plausible.py')),
            '--quiet','--addr',f'0x{address:08X}','--json']+
            [str(path) for path in evidence.source_paths(captured,address)],captured,120)
        findings,allowed=match.plausibility_result(result,address)
        if findings or allowed or evidence.source_fingerprint(captured,address) != source:
            raise ValueError('orphan native source is implausible or changed')
    if evidence.source_fingerprint(root,address) != source or evidence.mapping_snapshot(root) != mapping or \
            index_snapshot(root) != index or evidence.data_snapshot(root) != objects or \
            evidence.report_rom_path(root) != rom_path or Path(rom_path).read_bytes() != rom or \
            environment_fingerprint() != environment:
        raise ValueError('orphan native source, maps, ROM, producers or runtime changed')
    manifest=dict(schema=SCHEMA,selector=selector,address=address,bytes=len(data),instructions=len(instructions),
        source_sha256=source,mapping_sha256=sha(mapping),index_sha256=sha(index),objects_sha256=sha(objects),
        rom_sha256=sha(rom),transport=transport,native=native,native_proof_sha256=sha(text(native).encode()),
        invocations=[command.replace(workspace,'<workspace>').replace(str(captured),'<source-capture>')
            for command in commands],
        indexed_spans=spans,environment=environment,
        contract='Only complete linked function text earns ROM credit. Original compiler ELF remains unchanged during linking '
            'and only authenticated orphan .rodata is explicitly excluded by the original linker. '
            'Ordinary calls use conditional compatible returning ABI; native frame, alias and return '
            'provenance checks remain active. Named points grant no physical access, extent, '
            'nonaliasing, C semantic equivalence or termination theorem.')
    if bindings['functions']:
        manifest['typed_function_addresses_version'] = 2
        manifest['callback_body_semantics_proved'] = False
    if expected is not None and text(manifest) != text(expected):
        raise ValueError('orphan native report differs from complete fresh compiler replay')
    if capture is not None:
        (capture/'manifest.json').write_text(text(manifest)+'\n')
    return data,manifest


def selected(report):
    lines=report.splitlines()
    if not any(SCHEMA in line or line.startswith('* orphan constants') for line in lines):
        return False
    if [line for line in lines if line.strip().startswith('* verification')] != [f'* verification: `{SCHEMA}`']:
        raise ValueError('mixed or malformed orphan native report')
    return True


def render(address,result):
    data,manifest=result
    return '\n'.join([f'# Match {address:08X}','',f'* verification: `{SCHEMA}`',
        f'* compiler: `{match.DEFAULT_CC} {FLAGS}`',f'* orphan constants policy: {POLICY}',
        '* verified extent: complete ELF function symbol, including literal pools',
        '* relocations: none','* source plausibility: plausible','* hand-asm allow list: not listed',
        f'* orphan constants evidence: `{text(manifest)}`',f'* compiled : `{data.hex()}`',
        f'* ROM bytes: `{data.hex()}` ({len(data)} bytes)','',
        f'**MATCH - byte identical** - {len(data)}/{len(data)} bytes',''])


def report_matches(report,root,address):
    if _replay.get():
        return False
    token=_replay.set(True)
    try:
        if not selected(report):return False
        lines=[line for line in report.splitlines() if line.startswith('* orphan constants evidence: `')]
        if len(lines) != 1 or not lines[0].endswith('`'):return False
        encoded=lines[0][len('* orphan constants evidence: `'):-1]
        def unique(pairs):
            result={}
            for key,value in pairs:
                if key in result:raise ValueError('duplicate orphan native evidence key')
                result[key]=value
            return result
        manifest=json.loads(encoded,object_pairs_hook=unique)
        if text(manifest) != encoded:return False
        return render(address,build(root,address,expected=manifest)) == report
    except (OSError,ValueError,KeyError,TypeError,IndexError,RuntimeError,subprocess.SubprocessError):
        return False
    finally:
        _replay.reset(token)


def issue(root,address,args):
    fixed_configuration(args)
    if args.mode != 'thumb' or args.label or args.control_flow_profile != 'ordinary' or \
            args.wsl != 'Ubuntu' or args.wsl_path != match.DEFAULT_WSL_PATH or any(
                getattr(args,key,None) for key in ('software_double_profile','software_double_remainder_profile',
                    'function_address_profile','switch_profile','switch_data_profile','signed_quotient_profile',
                    'signed_runtime_profile','unsigned_runtime_profile','addressed_signed_runtime_profile')):
        raise ValueError('orphan constants require isolated fixed Thumb O0 profile')
    result=build(root,address,args,selector=args.owner_runtime_profile)
    report=Path(root)/'docs'/'match'/f'{address:08X}.md'
    if not args.no_write:
        report.parent.mkdir(parents=True,exist_ok=True);report.write_text(render(address,result))
    if args.emit:
        (Path(root)/args.emit).write_bytes(result[0])
    print(f'extent    {len(result[0])} bytes (complete ELF symbol; explicit authenticated orphan exclusion; no relocations)')
    print('verdict MATCH - byte identical')
    return 0
