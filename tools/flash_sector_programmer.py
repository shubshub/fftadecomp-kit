"""The FLASH512_V130 1B32/1CC2 sector programmer and its synchronous byte loop."""
from hashlib import sha256
from pathlib import Path
import struct

import flash_bank_command as bank
import flash_program_byte as byte
import flash_sector_erase as erase
import library_units as units
import match
from unit_fpbit_source import reviewed_source

OWNER, END = 0x08142160, 0x0814220C
SCHEMA = 'elf-symbol-thumb-flash-sector-programmer-v1'
CONTROL = 'guarded 4096-byte sector erase/program with a live stack reader and a counted byte loop'
SOURCE = 'src/08142160.c'
SOURCE_DIGEST = 'f4e339e1391fac07e42ceafe76d1993be3f4f1d6002ab4c7935fb9531cbc61ad'
SETUP, REMAINING = 0x0200F370, 0x0200F374
CALLS = {0x08142182:erase.OWNER, 0x08142190:erase.INSTALL, 0x081421E0:byte.OWNER}
OBJECTS = {24:('data_0200F370', SETUP), 100:('data_0200F370', SETUP), 104:('data_0200F374', REMAINING)}
WRAPPER = 0x08141D54
TIMER_START, TIMER_STOP, IRQ = 0x081419C0, 0x08141A68, 0x0814195C


def require(ok, message):
    if not ok:
        raise ValueError('flash sector programmer: '+message)


def unit_owner(unit, address, orphan):
    return address == OWNER and erase.reader_unit(unit, orphan)


def check_source(root):
    reserved = ('FlashSector','FlashType', *(name for name, _ in OBJECTS.values()),
                *(f'func_{a:08X}' for a in (OWNER, *CALLS.values())))
    reviewed_source(Path(root),Path(SOURCE),OWNER,reserved,SOURCE_DIGEST)



class ProgramReaderFrame(erase.LocalReaderFrame):
    install_site, frame_offset = 0x08142190, -84


def block(ins, start, operations):
    for mnemonic, operands in operations:
        instruction = ins[start]
        require((instruction.mnemonic,instruction.op_str) == (mnemonic,operands),
                f'changed {mnemonic} {operands} at {start:08X}')
        start += instruction.size


def loop(graph):
    ins,edges,calls,part = graph
    require(calls == CALLS,'wrong direct erase, installer or byte helper')
    loads = {site:word['value'] for word in part['words'] for site in word['load_sites']}
    require(loads == {0x0814216A:SETUP,0x08142174:0x80FF,0x08142194:0x04000204,
            0x08142198:0xFFFC,0x0814219C:SETUP,0x081421A6:REMAINING,0x081421EC:0x04000204,
            0x081421F0:0xFFFC},'wrong geometry, WAITCNT, counter or invalid-sector literal')
    block(ins,0x08142164,[('adds','r7, r1, #0'),('lsls','r0, r0, #0x10'),('lsrs','r4, r0, #0x10')])
    block(ins,0x0814216C,[('ldr','r0, [r0]'),('ldrh','r0, [r0, #0xa]'),('cmp','r4, r0'),('blo','#0x8142180')])
    block(ins,0x08142180,[('adds','r0, r4, #0'),('bl','#0x8141f2c'),('lsls','r0, r0, #0x10'),
          ('lsrs','r5, r0, #0x10'),('cmp','r5, #0'),('bne','#0x81421fa'),('mov','r0, sp')])
    block(ins,0x0814219E,[('ldr','r2, [r0]'),('ldrh','r0, [r2, #0x10]'),('orrs','r1, r0'),('strh','r1, [r3]')])
    block(ins,0x081421A8,[('ldr','r0, [r2, #4]'),('strh','r0, [r1]'),('ldrb','r0, [r2, #8]'),
          ('lsls','r4, r0'),('movs','r0, #0xe0'),('lsls','r0, r0, #0x14'),('adds','r4, r4, r0'),
          ('adds','r6, r1, #0'),('b','#0x81421d6')])
    block(ins,0x081421CC,[('ldrh','r0, [r6]'),('subs','r0, #1'),('strh','r0, [r6]'),
          ('adds','r7, #1'),('adds','r4, #1'),('ldrh','r0, [r6]'),('cmp','r0, #0'),('beq','#0x81421ec'),
          ('adds','r0, r7, #0'),('adds','r1, r4, #0'),('bl','#0x8141fc8'),('lsls','r0, r0, #0x10'),
          ('lsrs','r5, r0, #0x10'),('cmp','r5, #0'),('beq','#0x81421cc')])
    block(ins,0x081421F2,[('ands','r0, r1'),('movs','r1, #3'),('orrs','r0, r1'),('strh','r0, [r2]'),
                          ('adds','r0, r5, #0')])
    require(not erase.reaches(edges,OWNER,0x081421E0,{0x081421AA}) and
            not erase.reaches(edges,0x08142174,0x08142182,set()) and
            not erase.reaches(edges,0x081421FA,0x08142190,set()),'guard or initializer can be bypassed')


def timer_stores(rom, graph, timer, allowed):
    """Track the base of every non-stack store in the straight-line timer start/stop."""
    ins,edges,calls,_ = graph
    require(not calls and all(len(out) <= 1 for out in edges.values()), 'unexpected timer transfer')
    regs = {}
    slot = 0x03005E44
    timer_pointer = timer
    written = set()
    for pc,i in sorted(ins.items()):
        op = i.mnemonic
        a = i.operands
        if op in ('push','pop','bx'):
            continue  # Pops are in the verified returning epilogue after the stores.
        if op in ('ldr','ldrh','ldrb','str','strh','strb'):
            m = a[1].mem
            require(not m.index,'unexpected indexed timer access')
            base = regs.get(m.base)
            address = base + m.disp if base is not None else None
            if op.startswith('str'):
                width = {'str':4,'strh':2,'strb':1}[op]
                require((address,width) in allowed,'timer can write outside configured registers and SDK state')
                written.add((address,width))
                if address == slot:
                    timer_pointer = regs.get(a[0].reg)
            elif m.base == match.ARM_REG_PC and op == 'ldr':
                regs[a[0].reg] = struct.unpack_from('<I',rom,((pc+4)&~3)+m.disp-bank.BASE)[0]
            else:
                regs[a[0].reg] = timer_pointer if (address,op) == (slot,'ldr') else None
        elif op in ('mov','movs'):
            regs[a[0].reg] = a[1].imm if a[1].type == match.ARM_OP_IMM else regs.get(a[1].reg)
        elif op in ('adds','subs') and a[-1].type == match.ARM_OP_IMM:
            value = regs.get(a[-2].reg)
            regs[a[0].reg] = None if value is None else value + (1 if op == 'adds' else -1)*a[-1].imm
        else:
            require(op in ('adds','lsls','lsrs','orrs','bics'),'unclassified timer operation')
            regs[a[0].reg] = None
    require(timer_pointer == timer and written == allowed,'incomplete timer effects or changed pointer restoration')


def helper_effects(rom,graphs):
    for channel in range(4):
        timer = 0x04000100+4*channel
        both = {(timer,2),(timer+2,2),(0x03005E44,4),(0x04000200,2),(0x04000208,2)}
        timer_stores(rom,graphs[TIMER_START],timer,both | {(0x03005E48,2),(0x0200F360,1),
                     (0x03005E42,2),(0x04000202,2)})
        timer_stores(rom,graphs[TIMER_STOP],timer,both)
    # All remaining loop callees are pinned by the original FLASH512 provider.
    # The IRQ's branches skip stores but introduce no other write base.
    expected = {IRQ:{0x0814196A,0x08141976},erase.WAIT:{0x08141E6A},erase.READER:set(),
                byte.OWNER:{0x08141FCE,0x08141FD4,0x08141FD8,0x08141FDC}}
    for owner,sites in expected.items():
        ins,_,_,_ = graphs[owner]
        require({p for p,i in ins.items() if i.mnemonic.startswith('str')} == sites,'unclassified nested write')
    block(graphs[byte.OWNER][0],0x08141FDA,[('ldrb','r2, [r0]'),('strb','r2, [r1]'),
          ('ldr','r3, [pc, #0x1c]'),('ldrb','r2, [r0]'),('ldr','r3, [r3]'),('movs','r0, #1')])
    require(graphs[byte.OWNER][2] == {0x08141FE6:0x08142250}, 'wrong byte-program wait call')


def native_proof(data,rom,mapping,index,objects,calls,literals,context,orphan):
    from software_double_profile import indices,span_record
    require(unit_owner(context['unit'],OWNER,orphan) and context['tool'] == units.resolve(erase.TOOL) and
            data == rom[OWNER-bank.BASE:END-bank.BASE] and calls == CALLS and literals == OBJECTS and
            all(match.parse_data_symbols(objects).get(name) == address for name,address in OBJECTS.values()),
            'wrong O1 unit, original text or typed relocations')
    erase.provider(rom)
    entries,rows = indices(mapping,index)
    spans = {**erase.SPANS,byte.OWNER:(0x08142000,21),WRAPPER:(0x08141D9C,32),
             TIMER_START:(TIMER_STOP,65),TIMER_STOP:(erase.READER,23),IRQ:(0x08141984,16)}
    graphs = {}
    for a,(end,n) in spans.items():
        require(span_record(a,end,entries,rows,rom)['instrs'] == n,'inconsistent paired function indices')
        graphs[a] = erase.closure(rom[a-bank.BASE:end-bank.BASE],a,mapping,count=n)
    require(rom[0x141DDE:0x141DE6] == bytes.fromhex('0e49106800680860') and
            rom[0x141E06:0x141E0E] == bytes.fromhex('0949106814300860') and
            struct.unpack_from('<I',rom,0x141E2C)[0] == SETUP, 'wrong installed programmer or FlashType member')
    require(sha256(rom[WRAPPER-bank.BASE:0x141D9C]).hexdigest() ==
            '3912ffb41984235603c889ba938c78dbbf708fbb4496ffd0e28ded8149289054' and
            match.thunk_is_call_via(rom,0x0814224C,2) and
            graphs[WRAPPER][2] == {0x08141D74:0x0814224C,0x08141D86:0x08141C78} and
            struct.unpack_from('<I',rom,0x141D98)[0] == struct.unpack_from('<I',rom,0x141E18)[0] == 0x0200F36C,
            'wrong IdentifyFlash slot or program/verify caller')
    block(graphs[WRAPPER][0],0x08141D6E,[('ldr','r2, [r0]'),('adds','r0, r4, #0'),
          ('adds','r1, r5, #0'),('bl','#0x814224c'),('lsls','r0, r0, #0x10'),('lsrs','r3, r0, #0x10')])
    loop(graphs[OWNER])
    helper_effects(rom,graphs)
    for a,frame in ((erase.OWNER,erase.LocalReaderFrame(rom,mapping)),(OWNER,ProgramReaderFrame(rom,mapping))):
        ins,_,direct,_ = graphs[a]
        checked = match.verify_leaf_instructions(rom[a-bank.BASE:spans[a][0]-bank.BASE],a,True,direct,buffer_proof=frame)
        require(getattr(frame,'installed',False) and {i.address for i in checked} == set(ins),
                'local reader does not fit the live returning frame')
    match.verify_leaf_instructions(rom[byte.OWNER-bank.BASE:0x142000],byte.OWNER,True,graphs[byte.OWNER][2])
    lifetime = erase.reader_lifetime(rom,graphs,graphs[erase.OWNER][3])
    return checked,dict(partition=graphs[OWNER][3],setup_ids=[0x1B32,0x1CC2],slot=0x0200F36C,
        caller=WRAPPER,guard=dict(sectors=16,invalid=0x80FF),counter=dict(address=REMAINING,initial=4096,
        success_store=0x081421D0,failure='4096 minus successful bytes, including the failed byte'),
        range=dict(shift=12,first=bank.BUS,last=bank.BUS+65535,source_reads=[0x08141FDA,0x08141FE0]),
        erase=dict(phase=2,timeout=0xC002),byte_program=dict(phase=1,timeout=0xC001),
        frame=dict(bytes=84,local_bytes=64,nested_reader_from_entry_sp=-167,program_reader_from_entry_sp=-83,
                   installer=lifetime['installer']),contract='Original selected setup and configured SDK timer 0..3. '
        'The caller supplies 4096 stable readable bytes disjoint from writable executable stack, SDK state, '
        'MMIO and flash. The controller is exclusive; only the original timeout IRQ may intervene. The invalid '
        'guard and erase failure leave the progress halfword untouched. On erase failure the nested reader '
        'remains expired. After erase success the outer frame replaces it before the first byte. Each zero '
        'byte result advances both pointers and decrements the halfword once. On byte error the current byte '
        'has already been issued to hardware. The owner restores the low WAITCNT bits to 3 after the byte loop. '
        'The installed local reader expires on return. Polling requires a matching read or a serviced timeout.')


def replay(report, root, address):
    return erase.replay_member(report,root,address,OWNER,SCHEMA)
