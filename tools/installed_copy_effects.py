"""Conditional exact Thumb image effects on bounded opaque byte spans.

The interpreter proves a relation ONLY under the listed unproved memory/code
premises. It neither installs code nor supplies an allocator, lifetime, alias,
ABI or native-admission theorem. Source bytes are opaque transport tokens, not
initialized scalar values or trusted pointers. All 16 source/destination low
alignment combinations are checked; no library-name semantics are imported.
"""
from dataclasses import dataclass
import hashlib

import iwram_installation_prerequisite as image_plan

SELECTOR = 'conditional-installed-thumb-copy-effects-v1'
MAX_COUNT = 256
MAX_STEPS = 4096
MASK = 0xffffffff


@dataclass(frozen=True)
class Pointer:
    region: str
    offset: int


@dataclass(frozen=True)
class Opaque:
    name: str


@dataclass(frozen=True)
class Word:
    bytes: tuple


def _split(value):
    if type(value) is int:
        return tuple((value >> (8*i)) & 255 for i in range(4))
    if isinstance(value, Word):
        return value.bytes
    return tuple(('part', value, i) for i in range(4))


def _join(values):
    if all(type(value) is int for value in values):
        return sum(value << (8*i) for i, value in enumerate(values))
    if all(type(value) is tuple and len(value) == 3 and value[0] == 'part' and
           value[1] == values[0][1] and value[2] == i for i,value in enumerate(values)):
        return values[0][1]
    return Word(tuple(values))


def _sub_flags(left, right):
    if type(left) is not int or type(right) is not int:
        raise ValueError('copy comparison interprets an opaque value or pointer')
    result=(left-right)&MASK
    return dict(n=bool(result & 0x80000000),z=result==0,c=left>=right,
                v=bool((left^right)&(left^result)&0x80000000))


def _condition(code, flags):
    if flags is None:
        raise ValueError('copy branch observes unproved arithmetic flags')
    n,z,c,v=(flags[k] for k in ('n','z','c','v'))
    return (z,not z,c,not c,n,not n,v,not v,c and not z,
            not c or z,n==v,n!=v,not z and n==v,z or n!=v)[code]


def _add(value, delta):
    if isinstance(value, Pointer):
        return Pointer(value.region,value.offset+delta)
    if type(value) is int:
        return (value+delta)&MASK
    raise ValueError('copy arithmetic interprets an opaque value')


def _case(payload, destination, entry, count, source_alignment, destination_alignment, *, table_index=None):
    registers=[Opaque(f'entry-r{i}') for i in range(16)]
    registers[0]=Pointer('destination',0)
    registers[1]=Pointer('source',0)
    registers[2]=count
    registers[13]=Pointer('stack',0)
    registers[14]=Opaque('entry-thumb-return-address')
    initial=registers[:]
    memory={('source',i):Opaque(f'source-byte-{i}') for i in range(count)}
    if table_index is not None:
        # Both logical cursors refer to the same physical eight-byte local.
        original_table = [Opaque(f'table-byte-{i}') for i in range(8)]
        memory = {('table', i): byte for i, byte in enumerate(original_table)}
    writes,reads,trace=[],[],[]
    table_accesses = []
    flags=None
    alignments={'source':source_alignment,'destination':destination_alignment,'stack':0}
    pc=entry
    returned=False

    def location(pointer,width,write):
        if not isinstance(pointer,Pointer) or pointer.region not in alignments:
            raise ValueError('copy memory access lacks explicit symbolic span provenance')
        lo=pointer.offset; hi=lo+width
        if width==4 and (alignments[pointer.region]+lo)%4:
            raise ValueError('copy word access is not aligned under this premise case')
        if pointer.region=='stack':
            sp=registers[13]
            if not isinstance(sp,Pointer) or sp.region!='stack' or not -8<=sp.offset<=0 \
                    or not sp.offset<=lo<hi<=0:
                raise ValueError('copy stack access escapes the allocated eight-byte frame')
        elif not 0<=lo<hi<=count or (write and pointer.region!='destination') \
                or (not write and pointer.region!='source'):
            raise ValueError('copy read/write escapes its explicit source/destination permissions')
        if table_index is not None and pointer.region != 'stack':
            start = table_index + (pointer.region == 'source') + lo
            if width != 1 or not 0 <= start < start + width <= 8:
                raise ValueError('compaction requires a byte access within the common table')
            table_accesses.append(('write' if write else 'read', start))
            return [('table', start)]
        return [(pointer.region,i) for i in range(lo,hi)]

    def load(pointer,width):
        keys=location(pointer,width,False)
        if any(key not in memory for key in keys):
            raise ValueError('copy reads an uninitialized private/saved byte')
        reads.append((pointer.region,pointer.offset,width))
        values=tuple(memory[key] for key in keys)
        return _join(values) if width==4 else values[0]

    def store(pointer,width,value):
        keys=location(pointer,width,True)
        values=_split(value) if width==4 else (value,)
        if width==1 and type(value) is int: values=(value&255,)
        for key,byte in zip(keys,values): memory[key]=byte
        writes.append((pointer.region,pointer.offset,width))

    for step in range(MAX_STEPS):
        offset=pc-destination
        if pc%2 or not 0<=offset<=len(payload)-2:
            raise ValueError('copy fetch leaves its explicitly assumed installed image')
        raw=int.from_bytes(payload[offset:offset+2],'little')
        trace.append(pc)
        next_pc=pc+2
        if raw&0xfe00==0xb400:  # PUSH low registers, optionally LR.
            selected=[i for i in range(8) if raw>>i&1]+([14] if raw&0x100 else [])
            if not selected: raise ValueError('copy empty push is unsupported')
            registers[13]=_add(registers[13],-4*len(selected))
            for n,reg in enumerate(selected): store(_add(registers[13],4*n),4,registers[reg])
        elif raw&0xfe00==0xbc00:  # POP low registers; PC pops are not inferred.
            if raw&0x100: raise ValueError('copy POP PC is outside the proved endpoint subset')
            selected=[i for i in range(8) if raw>>i&1]
            if not selected: raise ValueError('copy empty pop is unsupported')
            values=[load(_add(registers[13],4*n),4) for n in range(len(selected))]
            for reg,value in zip(selected,values): registers[reg]=value
            registers[13]=_add(registers[13],4*len(selected))
        elif raw&0xff87==0x4700:  # BX only through the actual preserved entry LR token.
            target=registers[(raw>>3)&15]
            if target!=initial[14]: raise ValueError('copy indirect endpoint is not the protected entry return')
            returned=True
            break
        elif raw&0xf800==0xe000:
            delta=(raw&0x7ff)<<1
            if delta&0x800: delta-=0x1000
            next_pc=pc+4+delta
        elif raw&0xf000==0xd000 and ((raw>>8)&15)<14:
            if _condition((raw>>8)&15,flags):
                delta=(raw&255)<<1
                if delta&0x100: delta-=0x200
                next_pc=pc+4+delta
        elif raw&0xf800==0x2000:  # MOVS immediate; C/V unchanged.
            rd=(raw>>8)&7;registers[rd]=raw&255
            flags=None if flags is None else dict(flags,n=False,z=(raw&255)==0)
        elif raw&0xf800==0x2800:  # CMP immediate.
            flags=_sub_flags(registers[(raw>>8)&7],raw&255)
        elif raw&0xf800 in (0x3000,0x3800):
            rd=(raw>>8)&7;old=registers[rd];imm=raw&255
            subtract=raw&0xf800==0x3800
            registers[rd]=_add(old,-imm if subtract else imm)
            flags=_sub_flags(old,imm) if subtract and type(old) is int else None
        elif raw&0xfe00==0x1c00:  # ADDS Rd,Rn,#imm3.
            registers[raw&7]=_add(registers[(raw>>3)&7],(raw>>6)&7)
            flags=None
        elif raw&0xffc0==0x4000:  # ANDS, only exact words or known pointer low bits.
            rd=raw&7;left=registers[rd];right=registers[(raw>>3)&7]
            if type(left) is int and type(right) is int: value=left&right
            elif isinstance(left,Pointer) and type(right) is int and 0<=right<=3:
                value=(alignments[left.region]+left.offset)&right
            else: raise ValueError('copy mask interprets opaque data or unknown pointer bits')
            registers[rd]=value
            flags=None if flags is None else dict(flags,n=bool(value&0x80000000),z=value==0)
        elif raw&0xf000==0xc000:  # Thumb LDM/STM with writeback.
            rn=(raw>>8)&7;selected=[i for i in range(8) if raw>>i&1]
            if not selected or rn in selected: raise ValueError('copy multiple-transfer base/list is ambiguous')
            pointer=registers[rn]
            if raw&0x800:
                values=[load(_add(pointer,4*n),4) for n in range(len(selected))]
                for reg,value in zip(selected,values): registers[reg]=value
            else:
                for n,reg in enumerate(selected): store(_add(pointer,4*n),4,registers[reg])
            registers[rn]=_add(pointer,4*len(selected))
        elif raw&0xf800 in (0x7800,0x7000):  # immediate LDRB/STRB.
            rd=raw&7;pointer=_add(registers[(raw>>3)&7],(raw>>6)&31)
            if raw&0x800: registers[rd]=load(pointer,1)
            else: store(pointer,1,registers[rd])
        else:
            raise ValueError(f'copy unsupported exact Thumb encoding {raw:04X} at {pc:08X}')
        pc=next_pc
    if not returned: raise ValueError('copy bounded execution did not reach a protected return')
    if registers[13]!=initial[13] or any(registers[i]!=initial[i] for i in range(4,13)) \
            or registers[14]!=initial[14] or registers[0]!=initial[14]:
        raise ValueError('copy frame, opaque saved registers or actual R0 return value differ')
    if registers[1]!=Pointer('source',count) or registers[2]!=0 \
            or registers[3]!=Pointer('destination',count):
        raise ValueError('copy final argument/cursor state differs from bounded forward copy')
    if table_index is not None:
        accesses = []
        expected = original_table[:]
        for offset in range(table_index, table_index + count):
            accesses.extend([('read', offset + 1), ('write', offset)])
            expected[offset] = original_table[offset + 1]
        if accesses != table_accesses or any(memory['table', i] != byte for i, byte in enumerate(expected)):
            raise ValueError('compaction must read each original next byte before writing its predecessor')
        return dict(index=table_index, length=count, accesses=[list(access) for access in table_accesses],
                    steps=len(trace), SP_restored=True, preserved_return=True)
    if any(memory.get(('destination',i))!=initial_byte for i,initial_byte in
           ((i,Opaque(f'source-byte-{i}')) for i in range(count))):
        raise ValueError('copy destination does not transport each original opaque source byte')
    return dict(source_alignment=source_alignment,destination_alignment=destination_alignment,
        steps=len(trace),trace=trace,reads=reads,writes=writes,
        protected_return=True,opaque_R4_preserved=True,SP_restored=True,
        source_bytes_interpreted_as_scalar_or_pointer=False)


def verify_adjacent_table(payload, destination, entry, remaining, index):
    """Execute the exact dst=table+index, src=dst+1 relation on one aligned local.

    The two data pointers share memory. Only the helper's protected save words
    are separate. The owner decides whether it actually calls for zero length.
    """
    if type(remaining) is not int or type(index) is not int or not 0 <= index < remaining <= 8:
        raise ValueError('compaction requires a reachable index in the eight-byte table')
    return _case(payload, destination, entry, remaining - index - 1,
                 (index + 1) % 4, index % 4, table_index=index)


def verify_conditional(payload, destination, entry, count, *, selector):
    if selector!=SELECTOR or type(selector) is not str:
        raise ValueError('installed copy requires its explicit conditional selector')
    if type(count) is not int or not 0<=count<=MAX_COUNT:
        raise ValueError('installed copy requires a bounded exact nonnegative count')
    inventory=image_plan.image_inventory(payload,destination,entry)
    cases=[_case(payload,destination,entry,count,sa,da) for sa in range(4) for da in range(4)]
    return dict(schema=SELECTOR,image_sha256=hashlib.sha256(payload).hexdigest(),
        image_destination=destination,entry=entry,count=count,cases=cases,inventory=inventory,
        conditional_conclusion=dict(destination_bytes='original opaque source bytes at matching offsets',
            source_read_span=[0,count],destination_write_span=[0,count],private_stack_span=[-8,0],
            preserved_registers=list(range(4,13))+[14],SP_restored=True,
            return_target='saved entry Thumb LR',R0='saved entry Thumb LR, not destination pointer',
            R1='source+count',R2=0,R3='destination+count',byte_initialization_granted=False),
        unproved_premises=[
            'Actual fetched image bytes equal this source image at the proposed destination throughout execution',
            'Incoming Thumb LR is a valid caller continuation and stack is word-aligned',
            'Allocated stack[-8,0) is readable/writable and disjoint from all caller protected/private words',
            'Source[0,count) is readable as opaque transport bytes; destination[0,count) is writable',
            'Source, destination, allocated stack and executing code are physically disjoint without wraparound',
            'No external agent, interrupt or alias changes code/source/saves during this bounded execution'],
        installed_identity_proved=False,memory_premises_proved=False,
        caller_argument_provenance_proved=False,source_or_native_admission=False,
        limits='A conditional machine relation over explicit disjoint symbolic regions. '
            'Actual pointer values, allocations, read/write permissions, no-alias, lifetime and '
            'installation persistence are not inferred. No entire caller or source-C theorem.')


def callback_facts(data, address, rom, mapping, index, call_site, image_entry, *, selector):
    """Authenticate the actual short call setup in a complete indexed caller.

Only the uninterrupted native suffix is described. Incoming R5/R7-like values,
descriptor loads and memory permissions remain obligations. A ROM pointer to
RAM does not prove that RAM contains the assumed installed image.
"""
    if selector!=SELECTOR or type(selector) is not str:
        raise ValueError('callback facts require the explicit conditional selector')
    if any(type(value) is not bytes for value in (data,rom,mapping,index)) or \
            any(type(value) is not int for value in (address,call_site,image_entry)) \
            or not 2<=len(data)<=4096 or image_entry%2:
        raise ValueError('callback facts require immutable bounded complete inputs')
    owner=image_plan.owner;graph=image_plan.graph;indexed=image_plan.indexed
    owner.validate_span(data,address,rom,mapping,index)
    refined=owner.refine(data,address,mapping)
    ins,edges,branches,calls,words=graph.graph(data,address,refined)
    if branches or words: raise ValueError('callback facts exclude local BL/table dispatch')
    partition=graph.partition(data,address,refined,ins,words)
    entries,rows=indexed.indices(mapping,index)
    row=indexed.span_record(address,address+len(data),entries,rows,rom)
    if row['instrs']!=len(ins): raise ValueError('callback exact instruction count mismatch')
    if call_site not in calls: raise ValueError('callback site is not an actual direct call')
    start=call_site-14
    sites=list(range(start,call_site,2))
    if any(site not in ins or ins[site].size!=2 for site in sites):
        raise ValueError('callback argument suffix is not seven exact Thumb instructions')
    predecessors={site:[] for site in ins}
    for source,targets in edges.items():
        for target in targets: predecessors[target].append(source)
    if any(predecessors[site]!=[site-2] for site in sites[1:]+[call_site]):
        raise ValueError('callback argument suffix has an incoming bypass edge')
    raw=[int.from_bytes(ins[site].bytes,'little') for site in sites]
    if raw[0]&0xf807!=0x6801 or raw[1]&0xf807!=0x6804 \
            or (raw[0]>>3)&7!=(raw[1]>>3)&7 \
            or raw[2]&0xff00!=0x4a00 or raw[3]&0xffc7!=0x1c00 \
            or raw[4]&0xff00!=0x3000 or raw[5]!=0x6813 or raw[6]&0xff00!=0x2200:
        raise ValueError('callback exact source/options/destination/ROM-target/count suffix differs')
    pointer_literal=((sites[2]+4)&~3)+(raw[2]&255)*4
    pointer_address=int.from_bytes(data[pointer_literal-address:pointer_literal-address+4],'little')
    if pointer_address%4 or not image_plan.ROM_BASE<=pointer_address<=image_plan.ROM_BASE+len(rom)-4:
        raise ValueError('callback target pointer is not an aligned complete ROM word')
    pointer=int.from_bytes(rom[pointer_address-image_plan.ROM_BASE:pointer_address-image_plan.ROM_BASE+4],'little')
    if pointer!=image_entry|1:
        raise ValueError('callback actual Thumb pointer differs from proposed image entry')
    thunk=calls[call_site]
    thunk_row=indexed.span_record(thunk,thunk+2,entries,rows,rom)
    if thunk_row['instrs']!=1 or rom[thunk-image_plan.ROM_BASE:thunk-image_plan.ROM_BASE+2]!=bytes.fromhex('1847'):
        raise ValueError('callback requires actual complete indexed BX R3 thunk')
    return dict(caller=dict(address=address,bytes=len(data),sha256=hashlib.sha256(data).hexdigest(),
                           instructions=len(ins),partition=partition),call_site=call_site,thunk=thunk,
        count=raw[6]&255,
        source=dict(kind='unproved descriptor load',base_register=(raw[0]>>3)&7,offset=((raw[0]>>6)&31)*4),
        saved_options_R4=dict(kind='unproved descriptor load',base_register=(raw[1]>>3)&7,offset=((raw[1]>>6)&31)*4),
        destination=dict(kind='unproved incoming pointer plus constant',base_register=(raw[3]>>3)&7,offset=raw[4]&255),
        ROM_pointer=dict(address=pointer_address,word=pointer),
        installed_identity_proved=False,memory_permissions_or_pointer_provenance_proved=False,
        limits='Exact uninterrupted call setup only, conditional on actual incoming state and permitted '
               'loads/arithmetic. The static ROM target does not prove installation or memory effects.')
