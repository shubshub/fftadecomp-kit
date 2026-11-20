"""Replay the released scene pointer list and two original installed clears."""
import copy
import os
from pathlib import Path
import struct
import sys
import tempfile
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import finite_local_word_loop_profile as finite
import match
import match_evidence
import owner_admission_profile as owner
import scene_teardown as scene


@unittest.skipUnless(os.environ.get('FFTA_SCENE_TEARDOWN_ROOT'),'requires USA ROM and reviewed scene teardown C')
class SceneTeardown(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_SCENE_TEARDOWN_ROOT']).resolve()
        cls.raw,cls.manifest,_,cls.mapping,cls.index,cls.objects,cls.rom,_,elf = owner.build(
            cls.root,scene.OWNER,selector=finite.SELECTOR)
        cls.image = match.elf_image(elf)

    def test_source_and_replay(self):
        self.assertEqual(self.rom[0x96cb8:0x96d7c],self.raw)
        proof = self.manifest['proof']
        self.assertFalse(proof['list_bound_proved_from_ROM'])
        self.assertEqual([row['site'] for row in proof['caller_sites']],list(scene.CALLERS))
        self.assertEqual([row['reads'] for row in proof['finite_local_words']['counts']],
                         [[-72+4*i for i in range(n)] for n in range(14)])
        for invalid in (-1,14,True):
            with self.assertRaises(ValueError):
                scene.snapshot(invalid)
        report = (self.root/'docs/match/08096CB8.md').read_text()
        self.assertTrue(match_evidence.report_matches(report,self.root,scene.OWNER))
        for old,new in [(scene.FLOW,finite.CONTROL_FLOW),('"zero_words":3648','"zero_words":3649'),
                        ('"list_bound_proved_from_ROM":false','"list_bound_proved_from_ROM":true')]:
            self.assertIn(old,report)
            self.assertFalse(match_evidence.report_matches(report.replace(old,new),self.root,scene.OWNER))
        source = (self.root/'src/08096CB8.c').read_text()
        with tempfile.TemporaryDirectory() as path:
            root = Path(path)
            (root/'src').mkdir()
            (root/'include').mkdir()
            (root/'include/ffta.h').write_bytes((self.root/'include/ffta.h').read_bytes())
            for old,new in [('entries[13]','entries[12]'),('u32 func_0814913C(u8','u32 func_0814913C(u32'),
                            ('g_callbacks_0836D4B8[0](storage','g_callbacks_0836D4B8[1](storage')]:
                self.assertIn(old,source)
                (root/'src/08096CB8.c').write_text(source.replace(old,new))
                with self.assertRaises(ValueError):
                    scene.check_source(root)
        with self.assertRaisesRegex(ValueError,'original compiler ELF'):
            owner.preflight(self.raw,scene.OWNER,self.rom,self.mapping,self.index,self.objects,selector=finite.SELECTOR)

    def test_original_roles_and_relocations(self):
        original = self.manifest['bindings']
        self.assertEqual(original,scene.BINDINGS)
        for group,i,field,value in [('calls',9,1,'func_0814224C'),('calls',12,1,'func_08022080'),
                                    ('data',0,0,0xb0),('data',1,2,4)]:
            bad = copy.deepcopy(original)
            bad[group][i][field] = value
            with self.assertRaises(ValueError):
                owner.verify(self.raw,scene.OWNER,self.rom,self.mapping,self.index,self.objects,bindings=bad,selector=finite.SELECTOR)
        for name,key,val in [('func_08099CDC','bind',0),('data_0200F4B8','size',4),('_call_via_r2','type',1)]:
            image = copy.deepcopy(self.image)
            next(row for row in image['symbols'] if row['name'] == name)[key] = val
            with self.assertRaises(ValueError):
                owner.original_bindings(image,scene.OWNER,self.rom,self.mapping,self.objects,selector=finite.SELECTOR,index=self.index)

    def test_mutated_operations_bounds_and_caller(self):
        decoder = match.Cs(match.CS_ARCH_ARM,match.CS_MODE_THUMB)
        for site in (0x08096cbe,0x08096cd2,0x08096cda,0x08096ce0,0x08096ce6,
                     0x08096d0a,0x08096d0e,0x08096d32,0x08096d38,0x08096d42,0x08096d54,0x08096d5a):
            data = bytearray(self.raw)
            data[site-scene.OWNER] ^= 1
            ins = {i.address:i for i in decoder.disasm(bytes(data),scene.OWNER)}
            with self.subTest(site=hex(site)),self.assertRaises(ValueError):
                scene.owner_operations(ins)
        for site in (0x08022080,0x08149148,0x08096D74,0x08096BB0,0x08096EF4,0x08096F2C):
            rom = bytearray(self.rom)
            rom[site-scene.BASE] ^= 1
            with self.subTest(site=hex(site)),self.assertRaises(ValueError):
                scene.clear_sizes(rom)
        for a in scene.CALLERS:
            rom = bytearray(self.rom)
            rom[a-scene.BASE] ^= 1
            with self.assertRaises(ValueError):
                scene.spans(rom,self.mapping,self.index)
        for a in (scene.boot.IMAGE+0x16,scene.boot.POINTER,0x08002796):
            rom = bytearray(self.rom)
            rom[a-scene.BASE] ^= 1
            with self.assertRaises(ValueError):
                scene.installed_clears(bytes(rom),self.mapping,self.index,scene.clear_sizes(self.rom))
        for old,new in [(b'080995C0 0809961C    92  38',b'080995C0 0809961C    92  46'),
                        (b'081235E4 0812366E   138  46',b'081235E4 0812366E   138  69')]:
            self.assertIn(old,self.index)
            with self.assertRaises(ValueError):
                scene.spans(self.rom,self.mapping,self.index.replace(old,new))

    def test_native_owner_counts_query_and_clear_boundaries(self):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_CODE, UC_PROT_READ, UC_PROT_EXEC
        from unicorn import arm_const as reg
        from test_bg_affine_rows import NativeAffineRows

        cpu = Uc(UC_ARCH_ARM,UC_MODE_THUMB)
        for base,length in [(scene.BASE,len(self.rom)),(0x02000000,0x40000),(0x03000000,0x8000)]:
            cpu.mem_map(base,length)
        cpu.mem_write(scene.BASE,self.rom)
        cpu.mem_protect(scene.BASE,len(self.rom),UC_PROT_READ|UC_PROT_EXEC)
        plan = scene.boot.initializer_plan(self.rom,self.mapping,self.index)
        cpu.mem_write(scene.boot.DESTINATION,bytes.fromhex(plan['source_image']['bytes']))
        state,child,list_owner,head,nodes = 0x02001000,0x02002000,0x02003000,0x02003200,0x02003400
        heap1,heap2 = 0x02007000,0x02007100
        allocations = [(0x0200F4AC,0x02020000,0x4400,0x4500),(0x0200F4B8,0x02028000,0x3900,0x3d00)]
        scene_aux = 0x02008000
        trace = {}
        def put(address,value):
            cpu.mem_write(address,struct.pack('<I',value))
        def service(machine,pc,width,user):
            first = machine.reg_read(reg.UC_ARM_REG_R0)
            if pc == 0x0809D458:
                self.assertEqual(first,child)
            elif pc == scene.DESTROY:
                trace['destroy'].append(first)
            elif pc == 0x080993F4:
                self.assertEqual(first,list_owner)
                machine.reg_write(reg.UC_ARM_REG_R0,heap1)
            elif pc == 0x08022854:
                trace['free'].append(first)
            machine.reg_write(reg.UC_ARM_REG_PC,machine.reg_read(reg.UC_ARM_REG_LR))
        def record(machine,pc,width,user):
            if pc == scene.GATHER:
                self.assertEqual(machine.reg_read(reg.UC_ARM_REG_R1),0x03007F00-72)
            elif pc == scene.boot.DESTINATION:
                trace['clear'].append((machine.reg_read(reg.UC_ARM_REG_R0),machine.reg_read(reg.UC_ARM_REG_R1)))
            else:
                trace['collect'].append(machine.reg_read(reg.UC_ARM_REG_R0))
        # The query/adapter/collector, both allocation size helpers, both thunks and
        # the installed clearer run natively. External destruction and release consume opaque objects.
        for a in (0x0809D458,scene.DESTROY,0x080993F4,0x08022854):
            cpu.hook_add(UC_HOOK_CODE,service,begin=a,end=a)
        for a in (scene.GATHER,scene.boot.DESTINATION,0x0809AC20):
            cpu.hook_add(UC_HOOK_CODE,record,begin=a,end=a)
        for n in range(14):
            trace = {key:[] for key in ('collect','destroy','clear','free')}
            put(0x0200F4A8,state)
            put(state+0x44,child)
            put(0x0200F4B0,list_owner)
            put(list_owner+16,head)
            put(head+4,nodes if n else 0)
            put(0x0200F458,heap2)
            put(0x020101F0,scene_aux)
            for slot,pointer,size,capacity in allocations:
                put(slot,pointer)
                cpu.mem_write(pointer-4,b'\xA7'*(capacity+8))
            values = [0x02005000+i*16 for i in range(n)]
            for i,value in enumerate(values):
                put(nodes+12*i,value)
                put(nodes+12*i+8,nodes+12*(i+1) if i+1<n else 0)
            saved = {r:0x60000000+r for r in range(reg.UC_ARM_REG_R4,reg.UC_ARM_REG_R11+1)}
            for r,value in saved.items():
                cpu.reg_write(r,value)
            NativeAffineRows.call(self,cpu,scene.OWNER)
            self.assertEqual({r:cpu.reg_read(r) for r in saved},saved)
            self.assertEqual(trace['destroy'],values)
            self.assertEqual(trace['collect'],values)
            self.assertEqual(trace['clear'],[(heap1,4),(heap2,4)]+[(p,s) for _,p,s,_ in allocations])
            self.assertEqual(trace['free'],[allocations[0][1],allocations[1][1],scene_aux])
            for slot,pointer,size,capacity in allocations:
                self.assertEqual(cpu.mem_read(pointer-4,capacity+8),b'\xA7'*4+bytes(size)+b'\xA7'*(capacity+4-size))
            for slot in (0x0200F4A8,0x0200F4B0,0x020101F0):
                self.assertEqual(cpu.mem_read(slot,4),bytes(4))
