"""FLASH512_V130 ID command, local busy-wait halfword and two executable-reader calls."""
from hashlib import sha256
from pathlib import Path
import re
from types import SimpleNamespace

import flash_bank_command as bank
import flash_program_byte as byte
import flash_sector_erase as erase
import library_units as units
import match
from flash_sector_programmer import block
from rompath import rom_path
from software_double_profile import indices, span_record

OWNER, END, COUNT = 0x081418C0,0x0814195A,58
IDENTIFY = 0x08141D9C
NAME, SOURCE = 'func_081418C0','src/081418C0.c'
VENEER, THUNK = '_call_via_r5',0x08142258
CALLS = {OWNER+6:erase.INSTALL,OWNER+66:THUNK,OWNER+78:THUNK}
TARGETS = {'func_08141AB0':erase.INSTALL,VENEER:THUNK}
SCHEMA = 'elf-symbol-thumb-flash-read-id-v1'
CONTROL = 'complete FLASH512 ID entry, two local delay loops, two reader calls and exit commands'
QUALIFIED = '6e5115774c911bb9c91915c10013f0cefb2e9b2c9f6ff6039908f002925ea5ac'
# Independent controls. Each retains the compiler's native timing behavior:
# removing volatile from the counter leaves a register countdown at this O1.
CONTROLS = {
    'ports':(124,(44,56),'9498bf8cfb11016a5be6e8e6398d0a63eb24834552a4ef8898a4803208dcfa3a'),
    'counter':(142,(62,74),'46a4fb385c3b1040d4346812f89a12dc8400dd2bd550a5b50841f30692e11a90'),
    'ordinary':(112,(40,52),'da60406baad59b6a7444bff6d35bb568afbcbc0225d217330c1239f2519fa66f'),
}
BODY = '''typedef u8 (*FlashReader)(u8 *address);
extern void func_08141AB0(u16 *destination);

u16 func_081418C0(void)
{
    u16 readBuffer[32];
    volatile u16 delay;
    FlashReader read;
    u16 id;

    func_08141AB0(readBuffer);
    read = (FlashReader)((u32)readBuffer + 1);
    *(volatile u8 *)0x0E005555 = 0xAA;
    *(volatile u8 *)0x0E002AAA = 0x55;
    *(volatile u8 *)0x0E005555 = 0x90;
    for (delay = 20000; delay != 0; delay--)
        ;

    id = read((u8 *)0x0E000001) << 8;
    id |= read((u8 *)0x0E000000);
    *(volatile u8 *)0x0E005555 = 0xAA;
    *(volatile u8 *)0x0E002AAA = 0x55;
    *(volatile u8 *)0x0E005555 = 0xF0;
    *(volatile u8 *)0x0E005555 = 0xF0;
    for (delay = 20000; delay != 0; delay--)
        ;

    return id;
}'''


def require(ok,message):
    if not ok:
        raise ValueError('flash ID: '+message)


def unit_owner(unit,address,orphan):
    return address == OWNER and orphan is None and erase.flash_unit(unit)


def provider(rom):
    byte.provider(rom)
    require(sha256(rom[OWNER-bank.BASE:END-bank.BASE]).hexdigest() == QUALIFIED and
            match.thunk_is_call_via(rom,THUNK,5),'changed ID routine or R5 veneer')


def qualifier_offsets(text,tree,project,closure):
    offsets = bank.source_qualifiers(text,tree,closure,OWNER,SOURCE,BODY)
    if offsets:
        bank.verify_unit(project,OWNER,END-OWNER)
        provider(Path(rom_path(project)).read_bytes())
    return offsets


def controls(root):
    tool = units.resolve(erase.TOOL)
    args = SimpleNamespace(cc=tool['cc'],flags=tool['flags'],cpp=match.DEFAULT_CPP,assembler=match.DEFAULT_AS,
                           linker=match.DEFAULT_LD,objcopy=match.DEFAULT_OBJCOPY)
    runner = match.Runner(args.cc,root=root,timeout=match.SIGNED_REPLAY_TIMEOUT)
    rewrites = {'ports':lambda s:s.replace('volatile u16 delay','u16 delay'),
                'counter':lambda s:s.replace('volatile u8','u8'),
                'ordinary':lambda s:re.sub(r'\bvolatile\b','',s)}
    bodies = {}
    for name,(extent,reader_calls,digest) in CONTROLS.items():
        with runner.workspace() as work:
            _,_,original = match.compile_object(runner,work,args,root,OWNER,SOURCE,rewrite=rewrites[name])
            match.allocated_text_only(original)
            _,sites,offset,state,size = units.signature(original,OWNER)
            require(original['type'] == 1 and (offset,state,size) == (0,1,extent) and sites ==
                    ((6,10,'func_08141AB0'),*((pc,10,VENEER) for pc in reader_calls)) and
                    all(original['text'][pc:pc+4] == bytes.fromhex('fff7feff') for pc,_,_ in sites),
                    'unexpected qualifier-control input ELF')
            linked = match.link_typed_targets(runner,work,args,NAME,OWNER,TARGETS,set())
            match.allocated_text_only(linked)
            symbol,offset = match.function_record(linked,NAME,OWNER,True)
            padding = bytes.fromhex('c046') if extent%4 else b''
            require(offset == 0 and symbol['size'] == extent and not linked['relocations'] and
                    linked['text'][extent:] == padding and sha256(linked['text'][:extent]).hexdigest() == digest,
                    'qualifier control changed or alignment was credited')
            bodies[name] = linked['text'][:extent]
    return bodies


def record(root):
    import plausible
    root = Path(root)
    path = root/SOURCE
    require(list((root/'src').rglob(path.name)) == [path] and len(qualifier_offsets(path.read_text(),
            root,root,plausible.include_closure(root,path))) == 8, 'expected seven bus writes and one local delay')
    bodies = controls(root)
    hashes = ', '.join(name+' '+sha256(body).hexdigest() for name,body in bodies.items())
    return ('* allowlisted volatile flash ID: seven command stores AA/55/90 then AA/55/F0/F0, and two '
            '20000-step countdowns in the same local halfword. Removing the port qualifiers leaves 55/90 '
            'then 55/F0. Removing the counter qualifier moves the countdowns into a register. Native controls: '+hashes+'.')


def effects(graph):
    ins,edges,calls,part = graph
    require(calls == CALLS, 'incorrect installer or reader call')
    loads = {site:word['value'] for word in part['words'] for site in word['load_sites']}
    require(loads == {0x081418CE:bank.PORT1,0x081418D4:bank.PORT2,0x081418E0:20000,
            0x08141900:bank.BUS+1,0x08141918:bank.PORT1,0x0814191E:bank.PORT2,0x0814192C:20000},
            'changed bus address or local countdown')
    block(ins,OWNER,[('push','{r4, r5, lr}'),('sub','sp, #0x44'),('mov','r0, sp'),('bl','#0x8141ab0'),
                     ('mov','r5, sp'),('adds','r5, #1')])
    block(ins,0x081418D0,[('movs','r0, #0xaa'),('strb','r0, [r2]'),('ldr','r1, [pc, #0x14]'),
          ('movs','r0, #0x55'),('strb','r0, [r1]'),('movs','r0, #0x90'),('strb','r0, [r2]')])
    block(ins,0x08141902,[('bl','#0x8142258'),('lsls','r0, r0, #0x18'),('lsrs','r4, r0, #0x10'),
          ('movs','r0, #0xe0'),('lsls','r0, r0, #0x14'),('bl','#0x8142258'),('lsls','r0, r0, #0x18'),
          ('lsrs','r0, r0, #0x18'),('orrs','r4, r0')])
    block(ins,0x0814191A,[('movs','r0, #0xaa'),('strb','r0, [r1]'),('ldr','r2, [pc, #0x1c]'),
          ('movs','r0, #0x55'),('strb','r0, [r2]'),('movs','r0, #0xf0'),('strb','r0, [r1]'),('strb','r0, [r1]')])
    block(ins,0x08141950,[('adds','r0, r4, #0'),('add','sp, #0x44'),('pop','{r4, r5}'),('pop','{r1}'),('bx','r1')])
    for setup,first in ((0x081418DE,0x081418F4),(0x0814192A,0x08141944)):
        block(ins,setup,[('add','r1, sp, #0x40')])
        block(ins,setup+4,[('adds','r0, r2, #0'),('b',f'#{first+4:#x}')])
        block(ins,first,[('ldrh','r0, [r1]'),('subs','r0, #1'),('strh','r0, [r1]'),
              ('ldrh','r0, [r1]'),('cmp','r0, #0'),('bne',f'#{first:#x}')])
        require(set(edges[first+10]) == {first,first+12},'changed countdown backedge or fallthrough')
    require({p for p,i in ins.items() if i.mnemonic.startswith('str')} ==
            {0x081418D2,0x081418D8,0x081418DC,0x081418F8,0x0814191C,0x08141922,0x08141926,0x08141928,0x08141948}
            and all(not erase.reaches(edges,OWNER,p,{OWNER+6}) for p in CALLS if p != OWNER+6),
            'unclassified memory store or use before installation')


def native_proof(data,rom,mapping,index,objects,calls,literals,context,orphan):
    require(unit_owner(context['unit'],OWNER,orphan) and context['tool'] == units.resolve(erase.TOOL) and
            data == rom[OWNER-bank.BASE:END-bank.BASE] and calls == CALLS and not literals,
            'wrong original text, normal O1 unit or direct bindings')
    provider(rom)
    entries,rows = indices(mapping,index)
    spans = {OWNER:(END,COUNT),erase.INSTALL:erase.SPANS[erase.INSTALL],erase.READER:erase.SPANS[erase.READER],
             IDENTIFY:(erase.WAIT,53)}
    graphs = {}
    for a,(end,n) in spans.items():
        require(span_record(a,end,entries,rows,rom)['instrs'] == n,'wrong original index or instruction count')
        graphs[a] = erase.closure(rom[a-bank.BASE:end-bank.BASE],a,mapping,count=n)
    effects(graphs[OWNER])
    installed = erase.reader_installer(rom,graphs[erase.INSTALL])
    reader = graphs[erase.READER][0]
    require([(i.mnemonic,i.op_str) for _,i in sorted(reader.items())] == [('ldrb','r0, [r0]'),('bx','lr')],
            'the copied reader must preserve R4/R5 and load exactly one unsigned byte')
    ins,edges,caller_calls,part = graphs[IDENTIFY]
    require(caller_calls == {0x08141DAC:OWNER} and
            {site:w['value'] for w in part['words'] for site in w['load_sites']}.get(0x08141D9E) == 0x04000204,
            'changed IdentifyFlash call or WAITCNT setup')
    block(ins,0x08141DA4,[('ands','r0, r1'),('movs','r1, #3'),('orrs','r0, r1'),('strh','r0, [r2]'),
          ('bl','#0x81418c0'),('lsls','r0, r0, #0x10'),('lsrs','r3, r0, #0x10')])
    return sorted(graphs[OWNER][0].values(),key=lambda i:i.address),dict(partition=graphs[OWNER][3],
        frame=dict(bytes=80,local_reader_bytes=64,delay_offset=64,reader_from_entry_sp=-79,installer=installed),
        delay=dict(initial=20000,writes_per_loop=20001,reads_per_loop=40001),
        commands=dict(enter=[170,85,144],exit=[170,85,240,240]),id_read_order=[bank.BUS+1,bank.BUS],
        caller=IDENTIFY,contract='Exclusive FLASH512 command bus and word-aligned writable executable SDK stack. '
        'The two unsigned reader results form the device byte in bits 15..8 and maker byte in bits 7..0. '
        'The loop counts describe memory accesses to the local halfword, with no wall-clock guarantee. '
        'The owner uses its locally computed R5 Thumb address and leaves the global reader pointer expired on return.')


def replay(report,root,address):
    return erase.replay_member(report,root,address,OWNER,SCHEMA)
