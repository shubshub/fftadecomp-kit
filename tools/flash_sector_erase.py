"""The FLASH512_V130 sector eraser publishes a reader in its live stack frame."""
from hashlib import sha256
from pathlib import Path
import os
import re
import shlex
import struct
import subprocess
import sys
import tempfile
from types import SimpleNamespace

import flash_program_byte as program
import flash_bank_command as bank
import library_units as units
import match
import standing_premise

BASE = bank.BASE
OWNER, END = 0x08141F2C, 0x08141FC8
NAME, SOURCE = 'func_08141F2C', 'src/08141F2C.c'
INSTALL, READER, WAIT = 0x08141AB0, 0x08141AAC, 0x08141E30
TOOL = bank.TOOL
SCHEMA = 'elf-symbol-thumb-flash-sector-reader-v1'
CONTROL = 'closed sector guard and returning frame with the byte reader executing from the live local buffer, with the reader address retained globally at return'
QUALIFIED = '996f77672c4965e6015579851dd557e904cd99310b6f5a680ded44a1aa90a24c'
STRIPPED = '1311e16f8adeead71cbe5676a9b58911fd718f95d201ca3cb5a8ffe84dd2222a'
CALLS = {0x08141F76: INSTALL, 0x08141F84: 0x08142250}
OBJECTS = {0x78: ('data_0200F370',0x0200F370), 0x84: (program.WAIT,0x0200F368)}
CONTROL_TARGETS = {program.VENEER: 0x08142250, 'func_08141AB0': INSTALL,
                   'data_0200F370': 0x0200F370, program.WAIT: 0x0200F368}
SPANS = {
    OWNER: (END,60), INSTALL: (0x08141AEE,24), READER: (INSTALL,2), WAIT: (0x08141EB8,55),
    0x08142000: (0x08142124,120), 0x08142160: (0x0814220C,66),
}
FLASH_DECLARATIONS = '''struct FlashSector {
    u32 size;
    u8 shift;
    u16 count;
    u16 top;
};

struct FlashType {
    u32 romSize;
    struct FlashSector sector;
    u16 wait[2];
    union {
        struct {
            u8 makerId;
            u8 deviceId;
        } separate;
        u16 joined;
    } ids;
};

extern const struct FlashType *data_0200F370;
extern u16 (*data_0200F368)(u8 phase, u8 *address, u8 lastData);
extern void func_08141AB0(u16 *target);'''

BODY = FLASH_DECLARATIONS + '''

u16 func_08141F2C(u16 sector)
{
    u16 readBuffer[32];
    u8 *address;
    u16 result;

    if (sector >= 16)
        return 0x80FF;

    *(u16 *)0x04000204 = (*(u16 *)0x04000204 & ~3) | data_0200F370->wait[0];
    address = (u8 *)(0x0E000000 + (sector << data_0200F370->sector.shift));
    *(volatile u8 *)0x0E005555 = 0xAA;
    *(volatile u8 *)0x0E002AAA = 0x55;
    *(volatile u8 *)0x0E005555 = 0x80;
    *(volatile u8 *)0x0E005555 = 0xAA;
    *(volatile u8 *)0x0E002AAA = 0x55;
    *address = 0x30;
    func_08141AB0(readBuffer);
    result = data_0200F368(2, address, 0xFF);
    *(u16 *)0x04000204 = (*(u16 *)0x04000204 & ~3) | 3;

    return result;
}'''


def require(ok, message):
    if not ok:
        raise ValueError('flash sector erase: ' + message)


def unit_owner(unit, address, orphan):
    return address == OWNER and reader_unit(unit, orphan)


def reader_unit(unit, orphan):
    return orphan is not None and flash_unit(unit)


def flash_unit(unit):
    return (unit is not None and
            (unit.name,unit.start,unit.end,unit.toolchain,unit.proof) ==
            ('agb_flash FLASH512_V130', bank.OWNER, 0x0814220C, TOOL, 0x0814195C) and
            unit.row['identity'] == [dict(address='0x0836CE28',ascii='FLASH512_V130')])


def provider(rom):
    program.provider(rom)
    require(sha256(rom[OWNER-BASE:END-BASE]).hexdigest() == QUALIFIED,
            'sector guard, frame, flash commands, indirect wait or return changed')
    for p,count,waitcnt in zip(bank.SETUPS,(40,500,2000,40),(1,0,3,3)):
        erase,wait,times = struct.unpack_from('<3I',rom,p-BASE+8)
        require((erase,wait) == (OWNER|1,WAIT|1) and struct.unpack_from('<H',rom,p-BASE+36)[0] == waitcnt and
                struct.unpack_from('<3H',rom,times-BASE+12) == (count,65469,194),
                'changed installed sector eraser, phase-2 wait or timer')


def qualifier_offsets(text, tree, project, closure):
    from rompath import rom_path
    offsets = bank.source_qualifiers(text, tree, closure, OWNER, SOURCE, BODY)
    if offsets:
        bank.verify_unit(project, OWNER, END-OWNER)
        provider(Path(rom_path(project)).read_bytes())
    return offsets


def stripped_build(root):
    return stripped_reader_build(root, OWNER, SOURCE, NAME, 136, STRIPPED,
        ((60,10,'func_08141AB0'),(74,10,program.VENEER),(104,2,'data_0200F370'),(116,2,program.WAIT)))


def stripped_reader_build(root, address, source, name, size, digest, relocations):
    tool = units.resolve(TOOL)
    args = SimpleNamespace(cc=tool['cc'],flags=tool['flags'],cpp=match.DEFAULT_CPP,assembler=match.DEFAULT_AS,
                           linker=match.DEFAULT_LD,objcopy=match.DEFAULT_OBJCOPY)
    runner = match.Runner(args.cc,root=str(root),timeout=match.SIGNED_REPLAY_TIMEOUT)
    with runner.workspace() as workspace:
        _,_,raw = match.compile_object(runner,workspace,args,root,address,source,rewrite=lambda s: re.sub(r'\bvolatile\b','',s))
        signature = units.signature(raw,address)
        require(raw['type'] == 1 and signature[1:] == (
                relocations,0,1,size) and len(signature[0]) == size, 'changed qualifier-stripped ET_REL')
        # The diagnostic excludes unreachable duplicates using GNU section GC. The
        # positive uses the ordinary stricter library-unit orphan prerequisite.
        q = shlex.quote(workspace)
        runner.sh(f'{args.linker} -r --gc-sections -e {name} {q}/f.o -o {q}/f.gc.o && mv {q}/f.gc.o {q}/f.o')
        retained = match.elf_image(runner.read_binary(f'{workspace}/f.o'))
        match.allocated_text_only(retained)
        require(units.signature(retained,address) == signature, 'diagnostic section GC changed the function')
        linked = match.link_typed_targets(runner,workspace,args,name,address,CONTROL_TARGETS,{program.WAIT,'data_0200F370'})
        match.allocated_text_only(linked)
        symbol,offset = match.function_record(linked,name,address,True)
        require(offset == 0 and symbol['size'] == len(linked['text']) == size and not linked['relocations'] and
                sha256(linked['text']).hexdigest() == digest, 'changed linked stripped control')
        return linked['text']


def record(root):
    import plausible
    root = Path(root)
    path = root/SOURCE
    require(list((root/'src').rglob(path.name)) == [path] and
            len(qualifier_offsets(path.read_text(),root,root,plausible.include_closure(root,path))) == 5,
            'expected the five qualified flash command writes')
    stripped_build(root)
    return ('* allowlisted volatile flash sector erase: valid sector 0..15 issues AA/55/80/AA/55 then 30 at '
            'the sector base. Removing five flash qualifiers leaves only AA/55/30. The linked original and '
            'stripped control have SHA-256 '+QUALIFIED+' and '+STRIPPED+'.')


def closure(data, address, mapping, *, count=None):
    from owner_admission_profile import refine
    from owner_graph_profile import graph, partition
    refined = refine(data,address,mapping)
    instructions,edges,branches,calls,words = graph(data,address,refined)
    require(not branches and not words and len(instructions) == (SPANS[address][1] if count is None else count) and
            refined['cfg_closed'] and not refined['partial_reasons'] and
            refined['candidate_extent'] == dict(start=f'0x{address:08X}',end=f'0x{address+len(data):08X}',bytes=len(data)), 'incomplete native CFG or unexpected computed transfer')
    return instructions,edges,calls,partition(data,address,refined,instructions,words)


def reaches(edges, start, target, excluded):
    work,seen = [start],set()
    while work:
        site = work.pop()
        if site in excluded or site in seen:
            continue
        if site == target:
            return True
        seen.add(site)
        work.extend(edges[site])
    return False


class LocalReaderFrame(match.BufferCallProof):
    install_site, frame_offset = 0x08141F76, -84

    def check_call(self,address,aliases,stack,slots=None,*,constants=None,site=None,words=None):
        require(site == self.install_site and address == INSTALL and aliases == {match.ARM_REG_R0:self.frame_offset} and
                len(stack)*4 == -self.frame_offset and all(slot[2] for slot in stack[:16]) and not any(slot[2] for slot in stack[16:]) and
                stack[-1][0] and not slots and not words, 'installer must receive only the 64-byte live local at SP')
        self.access(self.frame_offset,4,stack)
        self.installed = True
        return {}


def native_proof(data,rom,mapping,index,objects,calls,literals,context,orphan):
    from software_double_profile import indices,span_record
    require(unit_owner(context['unit'],OWNER,orphan) and context['tool'] == units.resolve(TOOL) and
            data == rom[OWNER-BASE:END-BASE] and calls == CALLS and literals == OBJECTS and
            all(match.parse_data_symbols(objects).get(name) == address for name,address in OBJECTS.values()),
            'incorrect unit, original text, call site or named-data relocation')
    provider(rom)
    entries,rows = indices(mapping,index)
    graphs = {}
    for address,(end,count) in SPANS.items():
        require(span_record(address,end,entries,rows,rom)['instrs'] == count,'original index count changed')
        graphs[address] = closure(rom[address-BASE:end-BASE],address,mapping)
    instructions,edges,native_calls,partition = graphs[OWNER]
    require(native_calls == CALLS and set(edges[0x08141f3a]) == {0x08141fb4,0x08141f3c} and
            not reaches(edges,0x08141fb4,0x08141f76,set()) and
            not reaches(edges,OWNER,0x08141f84,{0x08141f76}), 'changed invalid-sector or publication-before-wait path')
    frame = LocalReaderFrame(rom,mapping)
    checked = match.verify_leaf_instructions(data,OWNER,True,calls,buffer_proof=frame)
    require(getattr(frame,'installed',False) and sorted(ins.address for ins in checked) == sorted(instructions),
            'native frame and ownership CFG disagree')
    return checked, reader_lifetime(rom,graphs,partition)


def reader_installer(rom, graph):
    """Execute the fixed Thumb loop with an abstract caller-local base and return link."""
    ins,edges,calls,_ = graph
    require(not calls,'reader installer must be a leaf')
    dest,link = ('local',0),('return',0)
    registers = {match.ARM_REG_R0:dest, match.ARM_REG_LR:link}
    saved, writes, visited = [], [], set()
    pc,zero = INSTALL,None
    def value(operand):
        if operand.type == match.ARM_OP_IMM:
            return operand.imm
        require(operand.type == match.ARM_OP_REG and operand.reg in registers,'uninitialized installer operand')
        return registers[operand.reg]
    for _ in range(60):
        instruction = ins[pc]
        visited.add(pc)
        ops = instruction.operands
        mnemonic = instruction.mnemonic
        next_pc = pc+instruction.size
        if mnemonic == 'push':
            require(instruction.op_str == '{lr}' and not saved,'changed installer entry frame')
            saved.append(link)
        elif mnemonic == 'pop':
            require(instruction.op_str == '{r0}' and saved == [link],'changed installer return restore')
            registers[ops[0].reg] = saved.pop()
        elif mnemonic == 'ldr':
            mem = ops[1].mem
            require(mem.base == match.ARM_REG_PC and not mem.index,'unexpected installer literal operand')
            literal = ((pc+4)&~3)+mem.disp
            registers[ops[0].reg] = struct.unpack_from('<I',rom,literal-BASE)[0]
        elif mnemonic == 'movs':
            registers[ops[0].reg] = value(ops[1])
        elif mnemonic in ('adds','subs','eors','lsls','lsrs'):
            left,right = value(ops[-2]),value(ops[-1])
            require(isinstance(right,int),'installer arithmetic consumes an unknown pointer')
            if isinstance(left,tuple):
                require(mnemonic == 'adds' and left[0] == 'local','unexpected arithmetic on installer pointer')
                result = ('local',left[1]+right)
            elif mnemonic == 'adds':
                result = (left+right)&0xffffffff
            elif mnemonic == 'subs':
                result = (left-right)&0xffffffff
            elif mnemonic == 'eors':
                result = left^right
            elif mnemonic == 'lsls':
                result = (left<<right)&0xffffffff
            else:
                result = left>>right
            registers[ops[0].reg] = result
        elif mnemonic in ('ldrh','strh','str'):
            mem = ops[1].mem
            require(not mem.index and mem.disp == 0,'unexpected installer memory offset')
            address = registers[mem.base]
            if mnemonic == 'ldrh':
                require(address in (READER,READER+2),'installer read outside the complete ROM reader')
                registers[ops[0].reg] = struct.unpack_from('<H',rom,address-BASE)[0]
            else:
                writes.append((pc,address,4 if mnemonic == 'str' else 2,value(ops[0])))
        elif mnemonic == 'cmp':
            left,right = value(ops[0]),value(ops[1])
            require(isinstance(left,int) and isinstance(right,int),'copy count depends on caller-local address')
            zero = left == right
        elif mnemonic == 'b':
            next_pc = ops[0].imm
        elif mnemonic == 'bne':
            require(zero is not None,'missing loop guard')
            if not zero:
                next_pc = ops[0].imm
        elif mnemonic == 'bx':
            require(value(ops[0]) == link and not saved and not edges[pc] and visited == set(ins),
                    'unbalanced or incomplete reader installer')
            reader = struct.unpack_from('<2H',rom,READER-BASE)
            require(writes == [(0x08141ab8,0x0200f364,4,('local',1)),
                               (0x08141ada,('local',0),2,reader[0]),
                               (0x08141ada,('local',2),2,reader[1])],
                    'installer failed to publish the Thumb address and then copy exactly two halfwords')
            return dict(publish=0x08141ab8, global_address=0x0200f364,
                        local_writes=[[0,2],[2,2]], reader=[READER,READER+4], code_sha256=sha256(rom[READER-BASE:READER-BASE+4]).hexdigest())
        else:
            raise ValueError('flash reader has unsupported instruction '+mnemonic)
        require(next_pc in edges[pc],'installer left the authentic CFG')
        pc = next_pc
    raise ValueError('flash reader loop failed to finish within its proved range')


def installed_reader_and_wait(rom,graphs):
    installed = reader_installer(rom,graphs[INSTALL])
    reader,reader_edges,reader_calls,_ = graphs[READER]
    require([(reader[pc].mnemonic,reader[pc].op_str) for pc in sorted(reader)] ==
            [('ldrb','r0, [r0]'),('bx','lr')] and not reader_calls and not reader_edges[READER+2],
            'RAM copy is not exactly one byte read and a return')
    wait,edges,calls,pools = graphs[WAIT]
    require(calls == {0x08141e48:0x081419c0,0x08141e80:0x08142248,0x08141e98:0x08142248,0x08141ea4:0x08141a68} and
            [(x['address'],x['load_sites']) for x in pools['words'] if x['value'] == 0x0200f364] == [(0x08141e58,[0x08141e4c])],
            'wait entered a different callee or reader global')
    for pc in (0x08141e80,0x08141e98):
        require((wait[pc-4].mnemonic,wait[pc-4].op_str,wait[pc-2].mnemonic,wait[pc-2].op_str) ==
                ('ldr','r1, [r7]','adds','r0, r5, #0') and not reaches(edges,WAIT,pc,{0x08141e4c}),
                'wait must obtain its reader target from the installed global')
    for pc,end in ((WAIT,0x08141eb8),(0x081419c0,0x08141a68),(0x08141a68,0x08141aac),(0x0814195c,0x08141984)):
        match.verify_leaf_instructions(rom[pc-BASE:end-BASE],pc,True,calls if pc == WAIT else None)
    return installed


def reader_lifetime(rom,graphs,partition):
    installed = installed_reader_and_wait(rom,graphs)
    callers = []
    for address,program_site in ((0x08142000,0x081420f2),(0x08142160,0x081421e0)):
        _,edges,calls,_ = graphs[address]
        installer, = (pc for pc,target in calls.items() if target == INSTALL)
        erase_sites = sorted(pc for pc,target in calls.items() if target == OWNER)
        require(calls[program_site] == program.OWNER and erase_sites and
                not reaches(edges,address,program_site,{installer}) and
                all(not reaches(edges,pc+4,program_site,{installer}) for pc in erase_sites),
                'sector programmer can consume the previous erase frame without replacing its reader')
        callers.append(dict(caller=address,erase_calls=erase_sites,reinstall=installer,program_byte=program_site))
    return dict(partition=partition,installer=installed,frame=dict(bytes=84,local_bytes=64,published_from_entry_sp=-83,
        reader_fetches='first four local bytes only',valid_sector_return='expired reader pointer remains in 0200F364',
        invalid_sector_return='0x80FF, incoming reader global unchanged'),wait=dict(phase=2,expected=255,
        call=0x08141f84,installed=WAIT|1,read_sites=[0x08141e80,0x08141e98]),
        callers=callers,contract='Original identified FLASH512 setup with aligned writable executable stack disjoint from '
        'the SDK globals, cartridge bus and timer I/O. On the ordinary synchronous path the installer publishes '
        'SP+1 before copying the two halfwords. Its caller polls only after both writes. After return the global '
        'still holds the expired local address. Both original sector programmers reinstall before ProgramByte. '
        'The claim covers this live synchronous interval, with compatible returning calls when they return.')


def replay(report, root, address):
    return replay_member(report, root, address, OWNER, SCHEMA)


def replay_member(report, root, address, owner, schema):
    """Reissue the genuine normal unit compilation against an immutable private snapshot."""
    import match_evidence as evidence
    if address != owner or f'* verification: `{schema}`' not in report.splitlines():
        return False
    root = Path(root).resolve()
    def inputs():
        paths = set(evidence.source_paths(root,owner)) | set(evidence.source_paths(root,0x0814195c))
        paths.update(root/name for name in ('config/functions.json','config/data_symbols.json',
                    'config/library_units.json','symbols/functions.txt'))
        return ({p.relative_to(root):p.read_bytes() for p in paths},Path(evidence.report_rom_path(root)).read_bytes())
    try:
        files,rom = inputs()
        (root/'build').mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(dir=root/'build',prefix='flash_sector_replay_') as directory:
            capture = Path(directory)
            for relative,content in files.items():
                dest = capture/relative
                dest.parent.mkdir(parents=True,exist_ok=True)
                dest.write_bytes(content)
            (capture/'baserom.bin').write_bytes(rom)
            (capture/'docs/match').mkdir(parents=True)
            (capture/'build').mkdir()
            env = dict(os.environ,FFTA_ROM=str(capture/'baserom.bin'),TMPDIR=str(capture/'build'),PYTHONDONTWRITEBYTECODE='1')
            checked = subprocess.run([sys.executable,'-B',str(Path(match.__file__).resolve()),'--root',str(capture),
                '--unit-toolchain',TOOL,f'0x{owner:08X}'],cwd=capture,env=env,stdin=subprocess.DEVNULL,
                capture_output=True,timeout=90)
            # match.py carries the standing frame premise line; report_matches has already checked and
            # removed it from `report`, so it is checked and removed from the reissued report too.
            reissued = standing_premise.strip((capture/f'docs/match/{owner:08X}.md').read_text(), capture, owner)
            return (checked.returncode == 0 and reissued == report and inputs() == (files,rom))
    except (OSError,ValueError,RuntimeError,subprocess.SubprocessError):
        return False
