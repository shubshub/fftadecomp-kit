"""USA history initializer. Prove the ordinary word-copy prefix of a volatile-field comparison."""
from hashlib import sha256
from pathlib import Path
import re
import struct

import library_units
import volatile_semantics as vs

BASE, OWNER, END = 0x08000000, 0x080C62CC, 0x080C6480
SHADOW, ANIMATION, PALETTE = 0x03000940, 0x02015744, 0x03003A60
SYMBOL = 'g_control_flags_03000940'
BODY = 'fc3923578566eaecaea0d819834e6d979e433cfb36f733d6746fb8cf201f8aa1'
VARIANTS = (
    (436,'1604a5d7cf33a0b5868cdf7d48267f48796fa508d8752ccc1b7c685220d162d3'),
    (432,'8f10f5eb6bb32eae46660f1a9a45c1ddaaa12bbbda788e3ff6f7a7f634e572d1'),
    (436,'035ea07203701bf0341dfc0053b9c48626dcc1790d7d93f0b35334d16057bb3b'),
)
CALLS = ((20,'_call_via_r2'), (286,'func_080CBA3C'), (298,'_call_via_r3'),
         (306,'func_080C95A8'), (360,'_call_via_r2'))
DATA = ((160,'g_callbacks_0836D4B8',0x0836D4B8),(340,'data_0836D4BC',0x0836D4BC),
        (344,'data_03003A60',PALETTE),(348,'data_02015744',ANIMATION),
        (428,'g_callbacks_0836D4B8',0x0836D4B8),(432,SYMBOL,SHADOW))
NATIVE = (
    (OWNER, END, BODY),
    (0x080C6858, 0x080C68EC, '12a56ab7fbd5cd7926b678e0dba8a0e8a2b1c594f555a3dfe7b3d7c198419b1c'),
    (0x080C7484, 0x080C74B4, '8be4f360a2a68fbbe3c719007132da0720c582bce0f8830b0084290e68ac4b87'),
    (0x08124BB4, 0x08124CE8, '7acf827eb40adc2cb23fbab85cb0d63c79e72f043128ad5d002b1b7cb833cc3c'),
    (0x081256D4, 0x0812575E, '110f29ecbf29d8eb7b795868aec7136deaf467ff1670641ffaa298f4eb85a290'),
    (0x080CBA3C, 0x080CBA84, '5dcc51c9675e9be71d6914a099ee116ab73076db5413ae190cbb776b0a9444e9'),
    (0x080C95A8, 0x080C95C0, '1972a08b68f4413fbec69e9c0ceef5227ed3608bb39299597a4de0c061164b84'),
    (0x08000718, 0x08000788, 'd85bea0cb703a088cb7a895f53f83fe423cb279c46c69070b3a3b7db0f4c37bf'),
)


def require(condition, message):
    if not condition:
        raise ValueError('history initializer: ' + message)


def placement(state, items, count, sp, *, from_builder):
    """Physical premises at callee entry, including both sets of saves and the callback scratch."""
    require(type(state) is int and state % 4 == 0 and 0x020159D0+20 <= state <= 0x02040000-180,
            'requires a successful 180-byte root heap allocation')
    limit = 12 if from_builder else 24
    require(type(count) is int and (0 if from_builder else -0x80000000) <= count <= limit,
            'word count exceeds its stack list or state array')
    require(type(sp) is int and sp % 4 == 0 and 0x03000000+28 <= sp <= 0x03008000-(64 if from_builder else 16),
            'expected private canonical IWRAM stack')
    protected = ((state-12,state+180), (SHADOW,SHADOW+80), (ANIMATION,ANIMATION+144),
                 (PALETTE,PALETTE+32),(0x03005E78,0x03005F28))
    frame = (sp-28,sp+(64 if from_builder else 16))
    require(all(hi <= frame[0] or frame[1] <= lo for lo,hi in protected), 'frame aliases live storage')
    if from_builder:
        require(items == sp, 'expected the twelve-word local at entry SP')
    if count <= 0:
        return
    require(type(items) is int and items % 4 == 0 and any(
            low <= items <= high-4*count for low,high in (
                (0x02000000,0x02040000),(0x03000000,0x03008000),(BASE,0x09000000))),
            'requires complete aligned ordinary input words')
    spans = protected if from_builder else (*protected,frame)
    require(all(hi <= items or items+4*count <= lo for lo,hi in spans), 'input aliases protected storage')


def producer_bounds(rom):
    """Derive the filtered and unfiltered stack prefix lengths from the pinned Thumb producer."""
    def at(pc):
        return struct.unpack_from('<H',rom,pc-BASE)[0]

    def immediate(pc,encoding):
        word = at(pc)
        require(word >> 8 == encoding,'changed immediate operation or register')
        return word & 255

    # Both script sites load the same unit base, pass a constant count and BL
    # to the 48-byte-local builder. Its two matched functions include the pools.
    limits = [immediate(site,0x21) for site in (0x08124CC2,0x08125742)]
    require(limits == [12,12] and all(struct.unpack_from('<I',rom,pc-BASE)[0] == 0x02002FC4
            for pc in (0x08124CD0,0x08125750)), 'expected twelve actual unit records')
    slots = immediate(0x080C685A,0xB0) - 128  # SUB SP, #imm7*4
    stride = immediate(0x080C6876,0x26)*2
    require(slots == 12 and stride == 0x108 and at(0x080C6878) == 0x0076
            and immediate(0x080C68AC,0x23)*2 == stride and at(0x080C68AE) == 0x005B,
            'changed record stride or stack extent')
    # The active branch starts selected=0. Each iteration can store the next
    # record once at SP+4*selected, postincrement the cursor and selected,
    # or skip all three. Both arms then advance the record and count down.
    require(tuple(at(pc) for pc in range(0x080C687C,0x080C688E,2)) ==
            (0x7910,0x2800,0xD001,0xC304,0x3501,0x1992,0x3901,0x2900,0xD1F6),
            'changed filtered count or pointer progression')
    counts = {0}
    for processed in range(limits[0]):
        require(max(counts) < slots, 'filter cursor can leave the twelve-word stack list')
        counts |= {selected+1 for selected in counts}
    require(counts == set(range(slots+1)), 'unexpected forwarded filter range')
    # The unfiltered case issues one pointer per record, then passes the
    # original constant count. Its indirect zero is for the separate 3168
    # bytes of unit records, and completes before taking any record address.
    require(tuple(at(pc) for pc in range(0x080C68B2,0x080C68BE,2)) ==
            (0xC201,0x18C0,0x3901,0x2900,0xD1FA,0x1C25),'changed unfiltered progression')
    require(immediate(0x080C68BE,0x20) == immediate(0x080C748A,0x20) == 180
            and at(0x080C68D2) == 0x4669 and at(0x080C68D4) == 0x1C2A
            and at(0x080C749E) == 0x1C29 and at(0x080C74A0) == 0x1C32,
            'changed allocation size, forwarded pointer, or signed count')
    # The ARM boot sequence initializes system-mode SP to 03007EC0. Assume
    # the live stack is still private and has room for the identified saves.
    require(rom[0xCC:0xD8] == bytes.fromhex('1f00a0e300f029e118d09fe5')
            and struct.unpack_from('<I',rom,0xF4)[0] == 0x03007EC0,'changed initial system stack')
    return counts


def aligned_manager_clear(payload, start, size):
    # The owner calls the installed code with a named aligned destination
    # and a positive word multiple. Its prologue takes the word path.
    # 03005E8E is STMIA R2!,{R0}; R0=0. R1 is reduced by four, unsigned
    # BHI loops while >3, then the signed zero test skips the byte tail.
    require(payload[:34] == bytes.fromhex(
        '00b5 021c 0029 12dd 0329 0ad9 0320 1040 0028 06d1 0020 01c2 0439 0329 fbd8 0029 05dd'),
        'changed aligned initialized-word clear loop')
    require(start % 4 == size % 4 == 0 and size > 0 and
            0x02000000 <= start < start+size <= 0x02040000, 'manager clear outside canonical EWRAM')
    # By induction after k stores cursor=start+4*k, count=size-4*k.
    # The final positive iteration has exactly four bytes left.
    return start, start+size, size//4


def provider(rom, mapping, index):
    import installed_copy_effects as copy
    import installed_zero_effects as zero
    import iwram_installation_prerequisite as install
    import scheduler_zero_descriptor as boot
    from scroll_prefix_scene import PROVIDER
    # The shared root manager is initialized by 080227E8 at 0200F434. 08022840
    # makes this 45-word allocation through 08007138, returning header+12.
    allocator = {0x080227E8,0x08022840,0x080070C8,0x08006C88,0x08006D38,0x08006DA0,
                 0x08006E28,0x08006EC0,0x08007138}
    heap = tuple(span for span in PROVIDER if span[0] in allocator)
    require({start for start, _, _ in heap} == allocator, 'incomplete shared root allocator inventory')
    require(isinstance(rom,bytes),'missing original ROM')
    for start,end,digest in (*NATIVE,*heap,*boot.BOOT):
        require(sha256(rom[start-BASE:end-BASE]).hexdigest() == digest, f'changed native body at {start:08X}')
    producer_bounds(rom)
    for word,entry,origin in ((boot.POINTER,boot.DESTINATION,boot.IMAGE),
                              (boot.POINTER+4,boot.DESTINATION+0x70,boot.IMAGE+0x70)):
        plan = install.verify(rom[0x2768:0x27B8],0x08002768,rom,mapping,index,selector=install.SELECTOR,
                              call_site=0x08002796,pointer_address=word)
        require(plan['arguments'] == dict(source=boot.IMAGE,destination=boot.DESTINATION,control=88)
                and plan['copy_plan']['bytes'] == 176 and plan['copy_plan']['width'] == 2
                and plan['source_image']['sha256'] == boot.IMAGE_SHA256
                and plan['entry']['pointer_word'] == entry|1 and plan['entry']['source_address'] == origin,
                'wrong installed image or callback entry')
    payload = bytes.fromhex(plan['source_image']['bytes'])
    require(rom[0xC6894:0xC68A4] == bytes.fromhex('1348 6101 0919 c900 0268 301c 7bf0 d4fc')
            and struct.unpack_from('<I',rom,0xC68E4)[0] == boot.POINTER,
            'unfiltered count*264 or zero callback origin changed')
    # The complete unit array ends before both the animation and the heap.
    # The root manager clears its own separate whole EWRAM arena at boot.
    require(aligned_manager_clear(payload,0x02002FC4,12*0x108) == (0x02002FC4,0x02003C24,792)
            and aligned_manager_clear(payload,0x020159D0,0x02040000-0x020159D0)[1] == 0x02040000,
            'wrong initialized manager region')
    for size in (180,144):
        case = zero.verify_conditional(payload,boot.DESTINATION,boot.DESTINATION,size,
                                       selector=zero.SELECTOR)['cases'][0]
        require(case['reads'] == [('stack',-4,4)] and
                case['writes'] == [('stack',-4,4)]+[('destination',i,4) for i in range(0,size,4)]
                and case['protected_return'] and case['SP_restored'],'changed state or animation clear')
    case = copy.verify_conditional(payload,boot.DESTINATION,boot.DESTINATION+0x70,32,
                                   selector=copy.SELECTOR)['cases'][0]
    require(case['reads'] == [('source',i,4) for i in range(0,32,4)]+[('stack',-8,4),('stack',-4,4)]
            and case['writes'] == [('stack',-8,4),('stack',-4,4)]+[('destination',i,4) for i in range(0,32,4)]
            and case['protected_return'] and case['SP_restored'],'changed 32-byte palette transfer')
    for site,opcode in ((0x0814224C,0x4710),(0x08142250,0x4718)):
        require(struct.unpack_from('<H',rom,site-BASE)[0] == opcode,'changed callback veneer')


def check_object(image, variant, rom, objects):
    import match
    match.allocated_text_only(image)
    raw,relocs,offset,value,size = library_units.signature(image,OWNER)
    length,digest = VARIANTS[variant]
    original,_ = match.function_record(image,'func_080C62CC',OWNER,True)
    require((image['type'],offset,value,size,len(raw),original['type'],original['bind']) ==
            (1,0,1,length,length,2,1) and sha256(raw).hexdigest() == digest, 'changed complete native symbol')
    require(len(image['relocations']) == 1 and image['sections'][image['relocations'][0]][7] == image['text_index'],
            'expected only .rel.text')
    bindings = [(site,10,name) for site,name in CALLS]
    for site,name,address in DATA:
        variant_site = site-4 if variant == 1 and site >= 428 else site
        bindings.append((variant_site,2,name))
        require(objects.get(name) == address and struct.unpack_from('<I',raw,variant_site)[0] == 0
                and struct.unpack_from('<I',rom,OWNER-BASE+site)[0] == address,'changed object binding '+name)
    require(relocs == tuple(sorted(bindings)), 'changed ELF relocation')
    for name in {name for _,_,name in bindings}:
        external = [s for s in image['symbols'] if s['name'] == name]
        require(len(external) == 1 and tuple(external[0][k] for k in ('section','value','size','type','bind'))
                == (0,0,0,0,1),'expected undefined external '+name)


def bounded_copy(assembly):
    funcs,_ = vs.parse_assembly(assembly)
    require(set(funcs) == {'func_080C62CC'},'unexpected translation unit')
    code,labels,_ = funcs['func_080C62CC']
    head,end = labels['.L13'],labels['.L11']
    # At the genuine copy entry, r2 is a positive signed count and decreases
    # by one per iteration. r1/r3 each advance by four. All three are dead on
    # exit before reuse, as are r0 and the compare flags. The only effects
    # of each additional iteration are the two identical ordinary word
    # accesses proved in the caller-separated spans; neither can touch shadow.
    prefix = ('push {r4, r5, r6, r7, lr}|add r6, r0, #0|add r5, r1, #0|add r4, r2, #0|'
              'lsl r3, r3, #24|lsr r7, r3, #24|ldr r0, .L33|ldr r2, [r0]|add r0, r6, #0|'
              'mov r1, #180|bl _call_via_r2|add r0, r6, #0|add r0, r0, #98|strb r4, [r0]|'
              'cmp r4, #0|ble .L11|add r1, r5, #0|add r3, r6, #0|add r2, r4, #0|'
              'ldmia r1!, {r0}|stmia r3!, {r0}|sub r2, r2, #1|cmp r2, #0|bne .L13|'
              'add r1, r6, #0|add r1, r1, #108|mov r0, #15|strh r0, [r1]|add r4, r1, #0|cmp r7, #0|beq .L15')
    actual = [' '.join((op,', '.join(args))).strip() for op,args,_ in code[:end+7]]
    require((head,end) == (19,24) and actual == prefix.split('|'),'changed copy entry, word loop or exit')
    for pc,(op,args,_) in enumerate(code):
        if op.startswith('b') and args and args[0] in labels and labels[args[0]] < end:
            require(pc == head+4 and labels[args[0]] == head,'extra entry into word copy')
    cut, n = re.subn(r'(?m)^([ \t]*bne[ \t]+)\.L13([ \t]+@cond_branch)$',r'\g<1>.L11\2',assembly)
    require(n == 1,'ambiguous word copy backedge')
    return cut


def record(assemblies, images, preprocessed, entry, interfaces, rom, objects, mapping, index):
    require(entry['symbol'] == SYMBOL and len(images) == len(assemblies) == 3,'expected three shadow object variants')
    provider(rom,mapping,index)
    for i,image in enumerate(images):
        check_object(image,i,rom,objects)
    cuts = [bounded_copy(asm) for asm in assemblies]
    result = vs.compare(cuts[0],cuts[1],preprocessed,SYMBOL,entry['declaration'],cuts[2],interfaces)
    return (vs.record(SYMBOL,result,perturbed=True) +
            '. Both 08124CC4 and 08125744 pass 12 records to 080C6858: its 48-byte local holds '
            'all twelve pointers after clearing 3168 record bytes or a filtered prefix. 080C7484 forwards its count unchecked: '
            'this comparison requires at most 24 aligned readable input words disjoint from the state, '
            'display, animation, palette, installed code and private stack saves. A nonpositive signed count '
            'copies nothing; count 25 is outside the 96-byte item field. Both callers require an initialized '
            'root heap and a successful exclusive 180-byte allocation. The resident CpuSet-installed zero '
            'callback clears 180 state bytes and optionally 144 animation bytes; zero depth then permits '
            'at most six history pushes. The installed copy transfers 32 bytes from the selected ROM '
            'palette to 03003A60. The real display halfword is saved then ORed with 0x1000. Three reads '
            'and one write of bldcnt_lo follow +74 to +62 under layout perturbation; the stripped build '
            'drops the redundant third read. Requires stable ordinary memory and no competing mutation.')


def report_body(report, root):
    from match_evidence import report_rom_path
    rom = Path(report_rom_path(root)).read_bytes()
    body = rom[OWNER-BASE:END-BASE]
    if sha256(body).hexdigest() != BODY:
        return False
    expected = ((r'^\* verification:', '* verification: `elf-symbol-thumb-data-v1`'),
                (r'^\* ROM bytes:', f'* ROM bytes: `{body.hex()}` (436 bytes)'),
                (r'^\* compiled\s*:', f'* compiled : `{body.hex()}`'),
                (r'^\*\*MATCH', '**MATCH - byte identical** - 436/436 bytes'))
    return all([line for line in report.splitlines() if re.match(pattern,line.lstrip())] == [value]
               for pattern,value in expected)
