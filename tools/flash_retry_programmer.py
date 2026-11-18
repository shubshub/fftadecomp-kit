"""The D4BF/fallback FLASH512 sector programmer, including its copied erase verifier."""
from hashlib import sha256
from pathlib import Path

import flash_sector_programmer as simple
import flash_sector_erase as erase
import flash_program_byte as byte
import library_units as units
import match
from unit_fpbit_source import reviewed_source

OWNER, SCAN, CHECK, END = 0x08142000,0x08142124,0x08142148,0x08142160
SOURCE = 'src/08142000.c'
SOURCE_DIGEST = 'b364941700bf6c2a3739dd6d0d2a4b5358825237c8a38712342a6bb9d9ecb3a0'
SCHEMA = 'elf-symbol-thumb-flash-retry-sector-programmer-v1'
CONTROL = 'complete 81-attempt sector erase/scan, 1 or 6 extra erases, and 4096-byte program loop'
CALLS = {0x0814206E:erase.OWNER,0x08142080:CHECK,0x0814209C:erase.OWNER,
         0x081420AC:erase.INSTALL,0x081420F2:byte.OWNER}
OBJECTS = {64:('data_0200F370',simple.SETUP),212:('data_0200F370',simple.SETUP),
           216:('data_0200F374',simple.REMAINING)}
FUNCTIONS = {68:('func_08142124',SCAN|1),72:('func_08142148',CHECK|1)}
BASE = erase.BASE
block = simple.block


def require(ok, message):
    if not ok:
        raise ValueError('flash retry programmer: '+message)


def unit_owner(unit,address,orphan):
    return address == OWNER and erase.reader_unit(unit,orphan)


def check_source(root):
    names = ('FlashSector','FlashType', *(n for n,_ in OBJECTS.values()),
             *(f'func_{a:08X}' for a in (OWNER,SCAN,*CALLS.values())))
    reviewed_source(Path(root),Path(SOURCE),OWNER,names,SOURCE_DIGEST)


def copy_and_scan(rom,graphs):
    ins,edges,_,part = graphs[OWNER]
    pool = {site:word['value'] for word in part['words'] for site in word['load_sites']}
    require(pool == {0x08142016:0x80FF,0x08142020:simple.SETUP,0x08142030:SCAN|1,0x0814203A:CHECK|1,
                     0x081420B0:0x04000204,0x081420B4:0xFFFC,0x081420B8:simple.SETUP,
                     0x081420C2:simple.REMAINING,0x081420FE:0x04000204,0x08142102:0xFFFC},'wrong literal roles')
    block(ins,0x08142030,[('ldr','r1, [pc, #0x10]'),('movs','r0, #1'),('adds','r3, r1, #0'),
          ('eors','r3, r0'),('mov','r2, sp'),('ldr','r0, [pc, #0xc]'),('subs','r0, r0, r1'),('b','#0x8142056')])
    block(ins,0x0814204C,[('ldrh','r0, [r3]'),('strh','r0, [r2]'),('adds','r3, #2'),('adds','r2, #2'),
          ('subs','r0, r1, #2'),('lsls','r0, r0, #0x10'),('lsrs','r1, r0, #0x10'),('cmp','r1, #0'),
          ('bne','#0x814204c')])
    # Execute that bounded copy using offsets in the 96-byte local. The even
    # distance of the two *tagged function symbols* is the count in bytes.
    source = pool[0x08142030]^1
    count = (pool[0x0814203A]-pool[0x08142030]) & 65535
    require(source == SCAN and count == 36 and count <= 96,'copy count or source escapes its storage')
    local = bytearray()
    while count:
        local.extend(rom[source-BASE:source-BASE+2])
        source += 2
        count -= 2
    scan,_,calls,scan_part = graphs[SCAN]
    require(source == CHECK and local == rom[SCAN-BASE:CHECK-BASE] and not calls and
            sha256(local).hexdigest() == 'b5089dea01232e5926bb9e332e6f61a64d947791677ef5808c038f3a9752065e',
            'wrong copied instructions, scan literal or scan boundary')
    word, = scan_part['words']
    require(word['address']-SCAN == 12 and word['load_sites'] == [SCAN+4] and word['value'] == simple.SETUP,
            'copied PC-relative literal escapes or has different alignment')
    # For every word-aligned local, ((local+4+4)&~3)+4 equals local+12.
    # Relative branch destinations have identical offsets after the copy.
    for pc,i in scan.items():
        if i.mnemonic in ('b','beq'):
            require(i.operands[0].imm in scan,'copied scan transfers outside its local text')
    block(scan,0x0814212A,[('ldr','r0, [r0]'),('ldr','r1, [r0, #4]'),('b','#0x8142136')])
    block(scan,0x08142134,[('subs','r1, #1'),('cmp','r1, #0'),('beq','#0x8142142'),
          ('ldrb','r0, [r2]'),('adds','r2, #1'),('cmp','r0, #0xff'),('beq','#0x8142134'),('adds','r0, r1, #0')])
    wrapper,_,calls,wrapper_part = graphs[CHECK]
    require(calls == {CHECK+2:0x08142248} and match.thunk_is_call_via(rom,0x08142248,1) and
            sha256(rom[CHECK-BASE:END-BASE]).hexdigest() ==
            '0d0c2fea25072a78da01e25b53ea242124850a4708aa8a15f2567c418142b8b8' and
            wrapper_part['words'][0]['value'] == 0x8004,'wrong scan call ABI or failure projection')
    block(ins,0x0814207A,[('adds','r0, r7, #0'),('mov','r1, sp'),('adds','r1, #1'),('bl','#0x8142148')])
    require(not erase.reaches(edges,OWNER,0x08142080,{0x0814205E}) and
            not erase.reaches(edges,0x081420AC,0x08142080,set()),'scan executes before copy ends or after replacement')
    for a,end,calls in ((SCAN,CHECK,{}),(CHECK,END,graphs[CHECK][2])):
        match.verify_leaf_instructions(rom[a-BASE:end-BASE],a,True,calls)
    return dict(bytes=len(local),halfword_writes=len(local)//2,pool_offset=12,source=SCAN,call=0x08142080)


def owner_frame(graph):
    ins,edges,calls,_ = graph
    require(calls == CALLS,'wrong erase, scan, install or byte call site')
    block(ins,OWNER,[('push','{r4, r5, r6, r7, lr}'),('mov','r7, sb'),('mov','r6, r8'),('push','{r6, r7}'),
          ('sub','sp, #0x60'),('mov','sb, r1'),('lsls','r0, r0, #0x10'),('lsrs','r0, r0, #0x10'),
          ('mov','r8, r0'),('cmp','r0, #0xf'),('bls','#0x8142020'),('ldr','r0, [pc, #4]'),('b','#0x814210e')])
    block(ins,0x0814210C,[('adds','r0, r5, #0'),('add','sp, #0x60'),('pop','{r3, r4}'),('mov','r8, r3'),
          ('mov','sb, r4'),('pop','{r4, r5, r6, r7}'),('pop','{r1}'),('bx','r1')])
    require({p for p,i in ins.items() if 'sp' in i.op_str or i.mnemonic in ('push','pop','bx')} ==
            {OWNER,OWNER+6,OWNER+8,0x08142038,0x0814207C,0x081420AA,0x0814210E,0x08142110,
             0x08142116,0x08142118,0x0814211A}, 'unclassified stack use or return')
    require({p for p,i in ins.items() if i.mnemonic.startswith('str')} ==
            {0x0814204E,0x081420C0,0x081420C6,0x081420E0,0x0814210A},'unclassified store into caller or state')
    require(not erase.reaches(edges,OWNER,0x081420F2,{0x081420AC}) and
            not erase.reaches(edges,OWNER,0x081420F2,{0x081420C6}), 'byte loop bypasses reinstallation or counter')


def retry_and_program(graph):
    ins,_,_,_ = graph
    block(ins,0x08142022,[('ldr','r0, [r0]'),('ldrb','r0, [r0, #8]'),('mov','r7, r8'),('lsls','r7, r0'),
          ('movs','r0, #0xe0'),('lsls','r0, r0, #0x14'),('adds','r7, r7, r0')])
    block(ins,0x0814205E,[('movs','r4, #0'),('b','#0x814206c'),('adds','r0, r4, #1'),
          ('lsls','r0, r0, #0x18'),('lsrs','r4, r0, #0x18'),('cmp','r4, #0x51'),('beq','#0x814210c'),
          ('mov','r0, r8'),('bl','#0x8141f2c'),('lsls','r0, r0, #0x10'),('lsrs','r5, r0, #0x10'),
          ('cmp','r5, #0'),('bne','#0x8142062')])
    block(ins,0x08142084,[('lsls','r0, r0, #0x10'),('lsrs','r5, r0, #0x10'),('cmp','r5, #0'),
          ('bne','#0x8142062'),('movs','r6, #1'),('cmp','r4, #0'),('beq','#0x8142094'),('movs','r6, #6'),
          ('movs','r4, #1'),('cmp','r4, r6'),('bhi','#0x81420aa'),('mov','r0, r8'),('bl','#0x8141f2c'),
          ('adds','r0, r4, #1'),('lsls','r0, r0, #0x18'),('lsrs','r4, r0, #0x18'),('cmp','r4, r6'),
          ('bls','#0x814209a'),('mov','r0, sp'),('bl','#0x8141ab0')])
    block(ins,0x081420C4,[('ldr','r0, [r2, #4]'),('strh','r0, [r1]'),('adds','r4, r1, #0'),('b','#0x81420e8')])
    block(ins,0x081420DC,[('ldrh','r0, [r4]'),('subs','r0, #1'),('strh','r0, [r4]'),('movs','r0, #1'),
          ('add','sb, r0'),('adds','r7, #1'),('ldrh','r0, [r4]'),('cmp','r0, #0'),('beq','#0x81420fe'),
          ('mov','r0, sb'),('adds','r1, r7, #0'),('bl','#0x8141fc8'),('lsls','r0, r0, #0x10'),
          ('lsrs','r5, r0, #0x10'),('cmp','r5, #0'),('beq','#0x81420dc')])
    block(ins,0x08142104,[('ands','r0, r1'),('movs','r1, #3'),('orrs','r0, r1'),('strh','r0, [r2]')])


def native_proof(data,rom,mapping,index,objects,calls,literals,functions,context,orphan):
    require(unit_owner(context['unit'],OWNER,orphan) and context['tool'] == units.resolve(erase.TOOL) and
            data == rom[OWNER-BASE:SCAN-BASE] and calls == CALLS and literals == OBJECTS and functions == FUNCTIONS and
            all(match.parse_data_symbols(objects).get(n) == a for n,a in OBJECTS.values()),
            'wrong unit, original complete text or original address roles')
    graphs = simple.sdk_graphs(rom,mapping,index,{SCAN:(CHECK,16),CHECK:(END,9)})
    owner_frame(graphs[OWNER])
    copy = copy_and_scan(rom,graphs)
    retry_and_program(graphs[OWNER])
    frame = erase.LocalReaderFrame(rom,mapping)
    match.verify_leaf_instructions(rom[erase.OWNER-BASE:byte.OWNER-BASE],erase.OWNER,True,erase.CALLS,buffer_proof=frame)
    require(getattr(frame,'installed',False),'nested erase frame unproved')
    lifetime = erase.reader_lifetime(rom,graphs,graphs[erase.OWNER][3])
    return sorted(graphs[OWNER][0].values(),key=lambda i:i.address),dict(partition=graphs[OWNER][3],copy=copy,
        setup_ids=[0xD4BF,0],slot=0x0200F36C,frame=dict(bytes=124,local_bytes=96,tagged_scan_from_entry_sp=-123,
        nested_reader_from_entry_sp=-207,reader_installer=lifetime['installer']),erase=dict(max_attempts=81,
        scan_failed=0x8004,timeout=0xC002,extra_on_first=1,extra_on_retry=6,extra_status='discarded'),
        program=dict(phase=1,size=4096,remaining=simple.REMAINING,timeout=0xC001),
        contract='Original D4BF or fallback setup, configured SDK timer, word-aligned writable executable stack, '
        'exclusive controller and 4096 stable readable bytes disjoint from stack, flash, MMIO and SDK state. '
        'The scan reads at most 4096 bytes up to the first non-FF byte. An erase failure skips the scan. '
        'The 81st failed attempt returns the last erase or scan result with the progress halfword untouched. '
        'On success, one or six additional erases run with their returned status discarded. Then the original '
        'installer replaces the beginning of the scan with the four-byte reader. After a byte failure the '
        'remaining count includes the issued byte. The reader in the last used frame expires on return. '
        'Each poll requires matching readback or a serviced timeout IRQ.')


def replay(report,root,address):
    return erase.replay_member(report,root,address,OWNER,SCHEMA)
