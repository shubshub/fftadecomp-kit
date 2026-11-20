"""Original sprite list/tree, real heap calls and source/ELF refusal cases."""
import copy
import json
import os
from pathlib import Path
import struct
import sys
import tempfile
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import match
import owner_admission_profile as owner
import sprite_tile_selection as sprite


@unittest.skipUnless(os.environ.get('FFTA_SPRITE_SELECTION_ROOT'), 'requires original USA ROM and agbcc')
class SpriteSelectionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_SPRITE_SELECTION_ROOT']).resolve()
        result = owner.build(cls.root,sprite.OWNER,selector=sprite.buffers.THUNK_SELECTOR)
        cls.body,cls.manifest,_,cls.mapping,cls.index,cls.objects,cls.rom,_,cls.elf = result

    def verify(self, **change):
        args = dict(data=self.body,address=sprite.OWNER,rom=self.rom,mapping=self.mapping,
                    index=self.index,objects=self.objects,bindings=sprite.BINDINGS,
                    selector=sprite.buffers.THUNK_SELECTOR)
        return owner.verify(**{**args,**change})

    def test_replay_original_and_refuse_stale_result(self):
        observed, ins = self.verify(manifest=self.manifest)
        proof = observed['proof']
        self.assertEqual(len(ins),90)
        self.assertEqual(proof['traversal']['transitions'],32)
        self.assertEqual(proof['clearer']['effects']['zero_write_span'],[0,28])
        self.assertEqual(len(proof['caller_sites']),3)
        stale = copy.deepcopy(self.manifest)
        stale['proof']['frame']['extracted_key'] = 4
        with self.assertRaisesRegex(ValueError,'manifest differs'):
            self.verify(manifest=stale)

    def test_wrong_rom_index_callback_or_heap(self):
        for address in (sprite.OWNER+8,0x08092C60,0x080A6CD0,0x080BA624,0x0802217A,
                        0x080C7B78,0x080C7D4A,0x08006FCC,0x08A38A2C):
            rom = bytearray(self.rom)
            rom[address-match.ROM_BASE] ^= 1
            with self.subTest(address=hex(address)),self.assertRaises(ValueError):
                self.verify(rom=bytes(rom))
        rows = json.loads(self.mapping)
        next(r for r in rows if r['rom'] == '0x08021854')['instrs'] = 91
        index = self.index.replace(b'08021854 0802192C   216 90 ',b'08021854 0802192C   216 91 ')
        self.assertNotEqual(index,self.index)
        with self.assertRaises(ValueError):
            self.verify(mapping=json.dumps(rows).encode(),index=index)
        with self.assertRaisesRegex(ValueError,'original compiler ELF'):
            owner.preflight(self.body,sprite.OWNER,self.rom,self.mapping,self.index,self.objects,
                            selector=sprite.buffers.THUNK_SELECTOR)

    def test_compiler_elf_and_named_data(self):
        elf = match.elf_image(self.elf)
        bindings,targets = owner.original_bindings(elf,sprite.OWNER,self.rom,self.mapping,self.objects,
                                                  selector=sprite.buffers.THUNK_SELECTOR,index=self.index)
        self.assertEqual(bindings,sprite.BINDINGS)
        for name in (sprite.CLEAR,sprite.TABLE,'func_08022164','func_080C7B78'):
            image = copy.deepcopy(elf)
            next(s for s in image['symbols'] if s['name'] == name)['size'] = 4
            with self.subTest(name=name),self.assertRaises(ValueError):
                owner.original_bindings(image,sprite.OWNER,self.rom,self.mapping,self.objects,
                                        selector=sprite.buffers.THUNK_SELECTOR,index=self.index)
        for role, [offset, name, *rest] in (('calls',bindings['calls'][0]),
                                            ('functions',bindings['functions'][0]),('data',bindings['data'][0])):
            changed = copy.deepcopy(bindings)
            changed[role][0] = [offset+4,name,*rest]
            with self.assertRaises(ValueError):
                sprite.check_original(elf,changed,targets)
        with self.assertRaises(ValueError):
            self.verify(objects=self.objects.replace(b'g_callbacks_0836D4B8',b'g_callbacks_0836D4B0'))

    def test_changed_tree_visit_is_refused_without_rom_hash_shortcut(self):
        codes, originals = {}, {}
        for a in (sprite.COUNT,sprite.EXPORT,sprite.APPEND,sprite.WALK):
            size,count = sprite.SPAN[a]
            body,ins,*unused = sprite.complete(a,size,count,self.rom,self.mapping,self.index)
            originals[a],codes[a] = body,ins
        self.assertEqual(sprite.traversal(codes,originals)['transitions'],32)
        # Redirect BEQ into BNE while retaining the same forward target, then
        # feed those decoded instructions directly to the transition relation.
        for helper,site in ((sprite.COUNT,0x080C7B44),(sprite.WALK,0x080C7D2E)):
            modified = bytearray(originals[helper])
            modified[site-helper+1] ^= 1
            decoder=match.Cs(match.CS_ARCH_ARM,match.CS_MODE_THUMB)
            decoder.detail=True
            changed=dict(codes)
            changed[helper]={x.address:x for x in decoder.disasm(bytes(modified),helper)}
            with self.subTest(helper=hex(helper)),self.assertRaises(ValueError):
                sprite.traversal(changed,originals)

    def test_wrong_source_or_callback_type(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for name in (*sprite.SOURCES,'include/ffta.h'):
                dest=root/name
                dest.parent.mkdir(exist_ok=True)
                dest.write_bytes((self.root/name).read_bytes())
            sprite.check_source(root)
            for name,old,new in (('src/08021854.c','u16 saved_tile','u8 saved_tile'),
                                 ('include/object_list.h','(*ListCallback)','(*WrongCallback)')):
                path=root/name
                original=path.read_text()
                self.assertIn(old,original)
                path.write_text(original.replace(old,new))
                with self.assertRaises(ValueError):
                    sprite.check_source(root)
                path.write_text(original)

    def native_case(self, records, alternate, expected, ranges=(10,20,20,40)):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_CODE
        from unicorn.arm_const import (UC_ARM_REG_R0,UC_ARM_REG_R1,UC_ARM_REG_R2,UC_ARM_REG_R3,
                                      UC_ARM_REG_R4,UC_ARM_REG_R5,UC_ARM_REG_R6,UC_ARM_REG_R7,
                                      UC_ARM_REG_SP,UC_ARM_REG_LR,UC_ARM_REG_PC)
        cpu = Uc(UC_ARCH_ARM,UC_MODE_THUMB)
        cpu.mem_map(match.ROM_BASE,len(self.rom))
        cpu.mem_write(match.ROM_BASE,self.rom)
        cpu.mem_map(0x02000000,0x40000)
        cpu.mem_map(0x03000000,0x8000)
        cpu.mem_write(0x03005E78,self.rom[0xA38A2C:0xA38ADC])
        stop,stack,heap = 0x03000080,0x03005000,0x02001000
        def u32(address):
            return struct.unpack('<I',cpu.mem_read(address,4))[0]
        def put(address,fmt,*values):
            cpu.mem_write(address,struct.pack('<'+fmt,*values))
        def call(entry,*args):
            regs = [UC_ARM_REG_R0,UC_ARM_REG_R1,UC_ARM_REG_R2,UC_ARM_REG_R3]
            for reg,value in zip(regs,args):
                cpu.reg_write(reg,value)
            for i,value in enumerate(args[4:]):
                put(stack+4*i,'I',value)
            preserved=[UC_ARM_REG_R4,UC_ARM_REG_R5,UC_ARM_REG_R6,UC_ARM_REG_R7]
            for i,reg in enumerate(preserved):
                cpu.reg_write(reg,0x51510000+i)
            cpu.reg_write(UC_ARM_REG_SP,stack)
            cpu.reg_write(UC_ARM_REG_LR,stop|1)
            cpu.emu_start(entry|1,stop,count=500000)
            self.assertEqual(cpu.reg_read(UC_ARM_REG_PC),stop)
            self.assertEqual(cpu.reg_read(UC_ARM_REG_SP),stack)
            for i,reg in enumerate(preserved):
                self.assertEqual(cpu.reg_read(reg),0x51510000+i)
            return cpu.reg_read(UC_ARM_REG_R0)

        calls=[]
        def observe(uc,addr,size,unused):
            if addr in (0x08007138,0x08007170,0x080C7B78):
                calls.append((addr,uc.reg_read(UC_ARM_REG_R1),uc.reg_read(UC_ARM_REG_R2)))
        hook=cpu.hook_add(UC_HOOK_CODE,observe)
        heap_bytes=call(0x08022080,0x34)+0x400
        self.assertEqual(heap_bytes,7432)
        call(0x080070C8,heap,heap_bytes)
        manager=call(0x08021A3C,heap,*ranges)
        collection=u32(manager+8)
        objects=[0x02020000+i*0x50 for i in range(len(records))]
        for address,(tile,active) in zip(objects,records):
            put(address+0x12,'HH',tile,0xBEEF)
            put(address+0x38,'I',active)
            call(0x080C7A74,collection,address)
        # Seed the independent temporary tree, even when the linked list is empty.
        stale=call(0x080C7AB4,collection,0x02030000,999)
        calls.clear()
        selected=call(sprite.OWNER,manager,alternate)
        cpu.hook_del(hook)
        self.assertEqual(u32(collection+8),0)
        self.assertEqual(call(0x080C7B08,collection),len(records))
        frees=[arg for addr,arg,_ in calls if addr == 0x08007170]
        self.assertIn(stale,frees)
        allocations=[size for addr,size,_ in calls if addr == 0x08007138]
        self.assertEqual(allocations,([28]+[24]*len(expected)+([4*len(expected)] if expected else []))
                         if records else [])
        self.assertEqual(len(frees),1+(len(expected) if expected else bool(records)))
        if expected:
            self.assertNotEqual(selected,0)
            self.assertEqual(struct.unpack('<HH',cpu.mem_read(selected,4)),ranges[2:] if alternate else ranges[:2])
            values=u32(selected+4)
            self.assertEqual(u32(selected+8),values)
            self.assertEqual(u32(selected+12),0)
            self.assertEqual(u32(selected+16),len(expected))
            self.assertEqual(u32(selected+20),0)
            self.assertEqual(u32(selected+24),manager)
            self.assertEqual([u32(values+4*i) for i in range(len(expected))],[objects[i] for i in expected])
            self.assertEqual([(arg,key) for addr,arg,key in calls if addr == sprite.EXTRACT],
                             [(values+4*i,stack-24) for i in range(len(expected))])
        else:
            self.assertEqual(selected,0)
        for i,address in enumerate(objects):
            self.assertEqual(struct.unpack('<H',cpu.mem_read(address+0x14,2))[0],
                             records[i][0] if i in expected else 0xBEEF)

    def test_rom_paths_real_heap_and_sorted_sprites(self):
        records=[(19,1),(10,1),(19,2),(20,1),(39,1),(40,1),(18,0),(9,1),(11,1)]
        for args in (([],0,[]), ([(9,1),(10,0),(20,1)],0,[]),
                     (records,0,[1,8,0,2]), (records,1,[3,4]), (records,0x80000000,[3,4])):
            with self.subTest(records=args[0],alternate=args[1]):
                self.native_case(*args)
        actual=[(0x11F,1),(0,1),(0x120,1),(0x1E0,1),(0x3FF,1),(0x400,1)]
        self.native_case(actual,0,[1,0],(0,0x120,0x1E0,0x400))
        self.native_case(actual,1,[3,4],(0,0x120,0x1E0,0x400))


if __name__ == '__main__':
    unittest.main()
