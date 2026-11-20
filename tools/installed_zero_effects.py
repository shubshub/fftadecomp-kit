"""Conditional actual Thumb zero-store effects; no installed/allocator authority."""
import hashlib

from installed_copy_effects import Opaque, Pointer, _add, _condition, _join, _split, _sub_flags
import iwram_installation_prerequisite as image_plan

SELECTOR='conditional-installed-thumb-zero-effects-v1'
MAX_COUNT=256
MAX_STEPS=4096


def _case(payload,destination,entry,count,alignment):
    registers=[Opaque(f'entry-r{i}') for i in range(16)]
    registers[0]=Pointer('destination',0)
    registers[1]=count
    registers[13]=Pointer('stack',0)
    registers[14]=Opaque('entry-thumb-return-address')
    initial=registers[:]
    memory={}
    writes,reads,trace=[],[],[]
    flags=None
    pc=entry
    returned=False

    def location(pointer,width,write):
        if not isinstance(pointer,Pointer) or pointer.region not in ('destination','stack'):
            raise ValueError('zero access lacks explicit symbolic span provenance')
        lo=pointer.offset;hi=lo+width
        if width==4 and ((alignment if pointer.region=='destination' else 0)+lo)%4:
            raise ValueError('zero word access is unaligned in this premise case')
        if pointer.region=='stack':
            if registers[13]!=Pointer('stack',-4) or not -4<=lo<hi<=0:
                raise ValueError('zero access escapes its four-byte private save')
        elif not write or not 0<=lo<hi<=count:
            raise ValueError('zero access escapes write-only bounded destination')
        return [(pointer.region,i) for i in range(lo,hi)]

    def store(pointer,width,value):
        keys=location(pointer,width,True)
        values=_split(value) if width==4 else ((value&255) if type(value) is int else value,)
        for key,byte in zip(keys,values):memory[key]=byte
        writes.append((pointer.region,pointer.offset,width))

    def load(pointer):
        keys=location(pointer,4,False)
        if any(key not in memory for key in keys):raise ValueError('zero reads an unwritten private save')
        reads.append((pointer.region,pointer.offset,4))
        return _join(tuple(memory[key] for key in keys))

    for step in range(MAX_STEPS):
        offset=pc-destination
        if pc%2 or not 0<=offset<=len(payload)-2:
            raise ValueError('zero fetch escapes explicitly assumed installed image')
        raw=int.from_bytes(payload[offset:offset+2],'little');trace.append(pc);next_pc=pc+2
        if raw&0xfe00==0xb400:
            selected=[i for i in range(8) if raw>>i&1]+([14] if raw&0x100 else [])
            if len(selected)!=1:raise ValueError('zero requires exactly its four-byte save')
            registers[13]=_add(registers[13],-4)
            store(registers[13],4,registers[selected[0]])
        elif raw&0xfe00==0xbc00:
            selected=[i for i in range(8) if raw>>i&1]
            if raw&0x100 or len(selected)!=1:raise ValueError('zero excludes ambiguous or PC pop')
            registers[selected[0]]=load(registers[13]);registers[13]=_add(registers[13],4)
        elif raw&0xff87==0x4700:
            if registers[(raw>>3)&15]!=initial[14]:raise ValueError('zero indirect endpoint is not protected entryLR')
            returned=True;break
        elif raw&0xf800==0xe000:
            delta=(raw&0x7ff)<<1
            if delta&0x800:delta-=0x1000
            next_pc=pc+4+delta
        elif raw&0xf000==0xd000 and ((raw>>8)&15)<14:
            if _condition((raw>>8)&15,flags):
                delta=(raw&255)<<1
                if delta&0x100:delta-=0x200
                next_pc=pc+4+delta
        elif raw&0xf800==0x2000:
            registers[(raw>>8)&7]=raw&255
            flags=None if flags is None else dict(flags,n=False,z=(raw&255)==0)
        elif raw&0xf800==0x2800:
            flags=_sub_flags(registers[(raw>>8)&7],raw&255)
        elif raw&0xf800 in (0x3000,0x3800):
            rd=(raw>>8)&7;old=registers[rd];imm=raw&255;subtract=raw&0xf800==0x3800
            registers[rd]=_add(old,-imm if subtract else imm)
            flags=_sub_flags(old,imm) if subtract and type(old) is int else None
        elif raw&0xfe00==0x1c00:
            registers[raw&7]=_add(registers[(raw>>3)&7],(raw>>6)&7);flags=None
        elif raw&0xffc0==0x4000:
            rd=raw&7;left=registers[rd];right=registers[(raw>>3)&7]
            if type(left) is int and isinstance(right,Pointer):left,right=right,left
            if type(left) is int and type(right) is int:value=left&right
            elif isinstance(left,Pointer) and left.region=='destination' and type(right) is int and 0<=right<=3:
                value=(alignment+left.offset)&right
            else:raise ValueError('zero mask interprets unknown data/address bits')
            registers[rd]=value
            flags=None if flags is None else dict(flags,n=bool(value&0x80000000),z=value==0)
        elif raw&0xf800==0xc000:
            rn=(raw>>8)&7;selected=[i for i in range(8) if raw>>i&1]
            if not selected or rn in selected:raise ValueError('zero STM base/list is ambiguous')
            pointer=registers[rn]
            for n,reg in enumerate(selected):store(_add(pointer,4*n),4,registers[reg])
            registers[rn]=_add(pointer,4*len(selected))
        elif raw&0xf800==0x7000:
            store(_add(registers[(raw>>3)&7],(raw>>6)&31),1,registers[raw&7])
        else:raise ValueError(f'zero unsupported exact Thumb encoding {raw:04X} at {pc:08X}')
        pc=next_pc
    if not returned:raise ValueError('zero bounded execution fails to return')
    if registers[0]!=initial[14] or registers[1]!=0 or registers[2]!=Pointer('destination',count) \
            or registers[13]!=initial[13] or registers[14]!=initial[14] \
            or any(registers[i]!=initial[i] for i in range(3,13)):
        raise ValueError('zero final cursor/save/register relation differs')
    if any(memory.get(('destination',i))!=0 for i in range(count)):
        raise ValueError('zero final destination is not exactly observed zero stores')
    return dict(alignment=alignment,steps=len(trace),trace=trace,reads=reads,writes=writes,
                protected_return=True,SP_restored=True,destination_read=False)


def verify_conditional(payload,destination,entry,count,*,selector):
    if selector!=SELECTOR or type(selector) is not str:
        raise ValueError('zero effects require the explicit conditional selector')
    if type(count) is not int or not 0<=count<=MAX_COUNT:
        raise ValueError('zero effects require a bounded exact nonnegative count')
    inventory=image_plan.image_inventory(payload,destination,entry)
    cases=[_case(payload,destination,entry,count,alignment) for alignment in range(4)]
    return dict(schema=SELECTOR,image_sha256=hashlib.sha256(payload).hexdigest(),
        destination=destination,entry=entry,count=count,inventory=inventory,cases=cases,
        conditional_conclusion=dict(zero_write_span=[0,count],destination_reads=[],
            private_stack_span=[-4,0],preserved_registers=list(range(3,13))+[14],
            R0='saved entry ThumbLR, not destination pointer',R1=0,R2='destination+count',
            SP_restored=True,return_target='saved entry ThumbLR'),
        unproved_premises=[
            'Actual installed code equals this source image throughout execution',
            'Incoming ThumbLR is a valid caller continuation and SP is word-aligned',
            'Destination[0,count) is ordinary writable little-endian byte-addressed RAM without faults',
            'Stack[-4,0) is ordinary readable/writable memory, newly private and excludes protected caller state',
            'Destination, private save and executing image are physically disjoint and addresses do not wrap',
            'No asynchronous writer, interrupt or alias interferes with code or saved return'],
        installed_identity_proved=False,allocator_or_memory_permissions_proved=False,
        actual_caller_count_proved=False,source_or_native_admission=False,
        limits='Conditional exact instruction effects only. No allocation, initialization of unrelated bytes, '
            'hardware/MMIO memory semantics, installed identity, caller provenance or native theorem.')


def verify_aligned_menu_ring(payload, destination):
    """Execute the one larger original initialization of 32 menu request entries."""
    if destination != 0x03005E78 or len(payload) != 176 or hashlib.sha256(payload).hexdigest() != \
            "ce26dd719323641c1c4cbfa501368306ce6e31e193dabce7e84c7067f7590130":
        raise ValueError("menu allocation requires its original installed Thumb image")
    return _case(payload, destination, destination, 0x394, 0)
