"""Secondary camera registry, coordinate projection and the controller's phase transitions."""
import copy
import os
from pathlib import Path
import struct
import sys
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import camera_pan_scene as camera
import match
import match_evidence
import owner_admission_profile as owner
import owner_graph_profile as graph
import scene_coordinate_conversion as transform
from test_battle_action_value import battle_environment


@unittest.skipUnless(os.environ.get('FFTA_CAMERA_PAN_ROOT'), 'requires original USA ROM and recovered camera callback')
class CameraPanTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_CAMERA_PAN_ROOT']).resolve()
        cls.raw, cls.manifest, _, cls.mapping, cls.index, cls.objects, cls.rom, _, elf = owner.build(
            cls.root, camera.OWNER, selector=camera.named.SELECTOR)
        cls.image = match.elf_image(elf)

    def test_report_original_elf_and_relocation_roles(self):
        report = (self.root/'docs/match/0811C2E8.md').read_text()
        self.assertTrue(match_evidence.report_matches(report, self.root, camera.OWNER))
        forged = report.replace('"corrected_kind":81', '"corrected_kind":80')
        self.assertNotEqual(forged,report)
        self.assertFalse(match_evidence.report_matches(forged, self.root, camera.OWNER))
        self.assertEqual(self.raw, self.rom[0x11C2E8:0x11C50C])
        bindings = self.manifest['bindings']
        self.assertEqual(bindings, camera.BINDINGS)
        targets = {f'func_{v:08X}':(v,False) for v in camera.CALLS.values()}
        targets.update({k:(v,True) for k,v in camera.OBJECTS.items()})
        camera.check_original(self.image,bindings,targets)
        for group, row, field, value in (('calls',8,1,'func_080DBDC8'), ('data',2,0,376), ('data',1,2,4)):
            changed = copy.deepcopy(bindings)
            changed[group][row][field] = value
            with self.subTest(group=group), self.assertRaises(ValueError):
                camera.check_original(self.image,changed,targets)
        altered = copy.deepcopy(self.image)
        next(s for s in altered['symbols'] if s['name']=='func_080DC224')['size'] = 2
        with self.assertRaises(ValueError):
            camera.check_original(altered,bindings,targets)
        with self.assertRaisesRegex(ValueError, 'original compiler ELF'):
            owner.preflight(self.raw,camera.OWNER,self.rom,self.mapping,self.index,self.objects,selector=camera.named.SELECTOR)

    def test_changed_map_frame_switch_and_registry(self):
        def flipped(address):
            off = address-match.ROM_BASE
            return self.rom[:off]+bytes((self.rom[off]^1,))+self.rom[off+1:]
        for address in (0x080DC228,0x080DC23E,0x080DC25A,0x080DD6E4,0x080C7EC4,0x080C7FD8):
            with self.subTest(address=hex(address)), self.assertRaises(ValueError):
                transform.verify(flipped(address), self.mapping,self.index)
        changed = self.index.replace(b'080DC224 080DC268    68  33',b'080DC224 080DC268    68  34')
        self.assertNotEqual(changed,self.index)
        with self.assertRaises(ValueError):
            transform.verify(self.rom,self.mapping,changed)
        ins,edges,_,_,_ = graph.graph(self.raw,camera.OWNER,owner.refine(self.raw,camera.OWNER,self.mapping))
        bypass = dict(edges)
        bypass[0x0811C3B4] = [0x0811C3BC]
        with self.assertRaises(ValueError):
            camera.owner_frame(ins,bypass)
        bodies = {a:self.rom[a-match.ROM_BASE:camera.ENDS[a]-match.ROM_BASE] for a in (camera.REGISTRY,camera.RUN)}
        for address in (0x08395388,0x08395394,0x083953A8,0x083A6C28,0x08142250):
            with self.subTest(address=hex(address)), self.assertRaises(ValueError):
                camera.registered(flipped(address),bodies)

    def test_native_nullable_outputs_alias_sign_and_wrap(self):
        from unicorn import UC_HOOK_CODE
        from unicorn import arm_const as reg
        cpu,call,write,allocate = battle_environment(self)
        actor,unit = allocate(12),allocate(12)
        write(actor,'I',unit)
        out = 0x03007604
        routes=[]
        cpu.hook_add(UC_HOOK_CODE,lambda c,p,n,d: routes.append((c.reg_read(reg.UC_ARM_REG_R0),
                     c.reg_read(reg.UC_ARM_REG_R1))),begin=transform.SLOT,end=transform.SLOT)
        for kind in (0,0x51,0xFF):
            write(unit+4,'B',kind)
            for x,y in ((0,0),(-32768,32767),(32767,-32768),(-3,127)):
                for xp,yp in ((0,0),(out,0),(0,out+2),(out,out+2),(out,out)):
                    with self.subTest(kind=kind,point=(x,y),outputs=(xp,yp)):
                        routes.clear()
                        expected=bytearray.fromhex('aa aa bb bb cc cc dd dd')
                        cpu.mem_write(out-2,bytes(expected))
                        # The converter must not dereference the actor if the y destination is null.
                        call(transform.CONVERT,actor if yp else 0,x,y,xp,yp)
                        if xp:
                            struct.pack_into('<H',expected,xp-(out-2),(16-x)&65535)
                        if yp:
                            struct.pack_into('<H',expected,yp-(out-2),(48-y-4*(kind==0x51))&65535)
                        self.assertEqual(bytes(cpu.mem_read(out-2,8)),bytes(expected))
                        self.assertEqual(routes,[(unit,1)] if yp else [])

    def test_native_three_registry_rows_scheduler_and_full_camera_motion(self):
        from unicorn import UC_HOOK_CODE
        from unicorn import arm_const as reg
        for kind,category,point in ((0x178,0x51,(304,280)),(0x179,0,(208,280)),(0x17C,0x52,(176,296))):
            with self.subTest(kind=hex(kind)):
                cpu,call,write,allocate = battle_environment(self)
                for start,size in ((0x05000000,0x1000),(0x06000000,0x20000),(0x07000000,0x1000)):
                    cpu.mem_map(start,size)
                def read(loc,fmt='I'):
                    return struct.unpack('<'+fmt,cpu.mem_read(loc,struct.calcsize('<'+fmt)))[0]
                events=[]
                def trace(c,pc,_,ctx):
                    args=tuple(c.reg_read(reg.UC_ARM_REG_R0+i) for i in range(4))
                    sp=c.reg_read(reg.UC_ARM_REG_SP)
                    events.append((pc,args,sp,read(sp),c.reg_read(reg.UC_ARM_REG_LR)))
                for site in (camera.OWNER,camera.WORLD,transform.CONVERT,camera.LERP,0x080D3CB4,0x080DFB0C,0x080DB00C):
                    cpu.hook_add(UC_HOOK_CODE,trace,begin=site,end=site)
                call(0x080D36B0,0,0x0203B000)
                actor,unit = allocate(0x160),allocate(0x108)
                write(actor,'I',unit)
                write(unit+4,'B',category)
                write(actor+8,'hhh',12,-7,5)
                task=call(camera.REGISTRY,kind,actor,0)
                state=task+24
                self.assertEqual((read(task),read(task+20,'H'),read(state,'B'),read(state+8)),
                                 (camera.OWNER|1,256,kind-0x178,actor))
                entry=next(e for e in events if e[0]==camera.OWNER)
                self.assertEqual((entry[1][0],entry[1][2],entry[-1]),(task,state,0x08005A0D))
                # A harmless phase also reaches this same node through the recurring scheduler.
                manager=read(0x0200F430)
                write(task+20,'H',0x104)
                events.clear()
                call(camera.RUN,manager)
                self.assertEqual([e[-1] for e in events if e[0]==camera.OWNER],[0x08005A75])
                # Recreate the scheduler's active-manager slot for direct per-phase calls; the
                # two graphics children finish asynchronously, independently of this callback.
                write(0x02008FF0,'I',manager)
                desc=allocate(28)
                write(desc,'H',0x100)
                def tick():
                    self.assertEqual(call(camera.OWNER,task,desc,state),0)
                    return read(desc,'H')
                self.assertEqual(tick(),0x101)
                child=read(state+40)
                self.assertEqual((read(child),read(child+12)),(0x080DB00D,task))
                self.assertEqual(tick(),0x101)
                write(child+20,'H',2)
                events.clear()
                self.assertEqual(tick(),0x102)
                camera_args=[e for e in events if e[0]==transform.CONVERT]
                self.assertEqual(len(camera_args),2)
                projected=[e[1] for e in events if e[0]==camera.WORLD][0]
                self.assertEqual(projected[:2],point)
                for event,offset in zip(camera_args,(12,16)):
                    _,args,sp,word,_=event
                    self.assertEqual((args[0],args[3],word),(actor,sp+offset,sp+offset+2))
                def signed(v):
                    return (v+32768)%65536-32768
                originals=[(signed(e[1][1]),signed(e[1][2])) for e in camera_args]
                coords=[(signed(16-x),signed(48-y-4*(category==0x51))) for x,y in originals]
                lerps=[e[1] for e in events if e[0]==camera.LERP]
                self.assertEqual([(p,signed(x),signed(y),n) for p,x,y,n in lerps],
                          [(state+16,coords[0][0],coords[1][0],90),(state+28,coords[0][1]+8,coords[1][1],90)])
                effect,sprite=read(state+12),read(state+44)
                self.assertEqual((read(effect),read(effect+12),read(sprite),read(sprite+12)),
                                 (0x080D3CB5,task,0x080DFB0D,task))
                self.assertEqual((read(effect+24),read(sprite+24+12)),(camera.EFFECT,camera.SPRITE))
                for _ in range(128):
                    self.assertEqual(tick(),0x102)
                self.assertEqual((tick(),read(state+2,'H')),(0x103,40))
                for _ in range(40):
                    self.assertEqual(tick(),0x103)
                write(effect+20,'H',2)
                self.assertEqual((tick(),read(state+12)),(2,0))


if __name__ == '__main__':
    unittest.main()
