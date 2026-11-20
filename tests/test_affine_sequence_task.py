"""ROM effect registrations, both affine kinds, real scheduler allocation and synchronous sequence callback."""
import os
from pathlib import Path
import struct
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import affine_sequence_task as sequence
import test_bg_affine_rows as affine


@unittest.skipUnless(os.getenv('FFTA_AFFINE_SEQUENCE_ROOT'), 'requires the USA ROM and recovered affine sequence owner')
class NativeSequence(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        from rompath import rom_path
        cls.root = Path(os.environ['FFTA_AFFINE_SEQUENCE_ROOT']).resolve()
        cls.rom = Path(rom_path(cls.root)).read_bytes()
        cls.mapping = (cls.root / 'config/functions.json').read_bytes()

    def machine(self):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_CODE, UC_HOOK_INTR
        import unicorn.arm_const as reg
        from scheduler_zero_descriptor import DESTINATION, IMAGE
        u = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        for start, size in ((0x08000000,len(self.rom)),(0x02000000,0x40000),(0x03000000,0x8000),(0x04000000,0x1000)):
            u.mem_map(start,size)
        u.mem_write(0x08000000,self.rom)
        u.mem_write(DESTINATION,self.rom[IMAGE-0x08000000:IMAGE-0x08000000+176])
        events = []
        def record(pc, fn):
            u.hook_add(UC_HOOK_CODE, lambda m, a, n, _: fn(m), begin=pc, end=pc)
        def pack(a, fmt, *args):
            u.mem_write(a, struct.pack('<'+fmt, *args))
        def read(a, fmt='I'):
            return struct.unpack('<'+fmt, u.mem_read(a,struct.calcsize('<'+fmt)))[0]
        def args(machine):
            return tuple(machine.reg_read(reg.UC_ARM_REG_R0+i) for i in range(4))
        def result(machine, value):
            machine.reg_write(reg.UC_ARM_REG_R0, value)
            machine.reg_write(reg.UC_ARM_REG_PC, machine.reg_read(reg.UC_ARM_REG_LR))
        def loader(machine):
            sp = machine.reg_read(reg.UC_ARM_REG_SP)
            events.append(('loader', *args(machine), read(sp), read(sp+4)))
            result(machine, 0x02004200)
        record(0x080E03F8, loader)
        # Unrelated scene/graphics workers. Use native heap, allocator, list
        # walkers, callback thunks, both callbacks, status getters and fade.
        for pc in (0x0800C2C0, 0x080105B8, 0x0801159C, 0x080D49FC, 0x0800BC90, 0x080D4B64):
            record(pc, lambda m: result(m, 0))
        record(sequence.CREATE, lambda m: events.append(('create', *args(m), m.reg_read(reg.UC_ARM_REG_SP))))
        record(sequence.ROOT, lambda m: events.append(('owner', args(m)[0], read(args(m)[1],'H'))))
        record(sequence.CALLBACK, lambda m: events.append(('callback', *args(m)[:3], read(args(m)[1],'H'))))
        record(0x080FA9EA, lambda m: events.append(('returned',args(m)[0])))
        def bios(machine, _, context):
            pc = machine.reg_read(reg.UC_ARM_REG_PC)
            self.assertEqual(bytes(machine.mem_read(pc-2,2)), bytes.fromhex('0edf'))
            src, dst, count, _ = args(machine)
            sp = machine.reg_read(reg.UC_ARM_REG_SP)
            self.assertEqual((src, dst, count), (sp+20, sp+40, 1))
            data = bytes(machine.mem_read(src,20))
            events.append(('affine',src,dst,struct.unpack_from('<iihhhhH',data)))
            machine.mem_write(dst,struct.pack('<hhhhii',*affine.transform(data)))
        u.hook_add(UC_HOOK_INTR,bios)
        def call(pc,*arguments):
            return affine.NativeAffineRows.call(self,u,pc,*arguments)
        call(0x080227E8)
        call(0x080D36B0,0,0x02000100)
        return u, events, record, read, pack, call

    def test_original_registry_and_scheduled_phase103_for_both_kinds(self):
        for effect, flag in ((0x7F,0),(0xB8,8)):
            with self.subTest(effect=effect):
                u, events, _, read, pack, call = self.machine()
                row = 0x083947D8 + 8*(effect-1)
                self.assertEqual((read(row),read(row+4,'H')), (sequence.ROOT|1,80))
                actor = 0x02003000
                pack(actor, 'IH', 0x02003100, flag)
                task = call(0x080D3508, effect, actor, 0xAABBDDCC)
                state, kind, manager = task+24, int(effect==0xB8), read(0x0200F430)
                self.assertEqual((read(manager+4),read(task),read(task+20,'H')), (task,sequence.ROOT|1,256))
                self.assertEqual((read(state,'B'),read(state+2,'B'),read(state+24),read(state+20)),
                                 (kind,flag>>3,actor,0x02004200))
                self.assertIn(('loader',actor,read(0x0839C964+kind*4),0 if flag else 5,0,0,task),events)
                self.assertIn(('owner',task,0),events)
                # Resume the native scheduler at the completed-graphics phase.
                # Construct two completed native task handles, as produced by
                # phase 102. Both status getters must unlink/free them normally.
                descriptor = 0x02004280
                pack(descriptor+4,'I',sequence.SEQUENCE)
                for offset in (44,52):
                    handle = call(0x08005954,manager,sequence.CALLBACK|1,44,descriptor,task)
                    pack(handle+20,'H',2)
                    pack(state+offset,'I',handle)
                events.clear()
                pack(task+20,'H',0x103)
                pack(state+4,'hh',-7,25)
                pack(0x03000940,'H',0x0137)
                call(0x08005A24, manager)
                self.assertIn(('owner',task,0x103),events)
                [(_,src,dst,affine_args)] = [e for e in events if e[0]=='affine']
                self.assertEqual(affine_args, ((16 if kind else 8)*256,24*256,-7,-39,256,256,0))
                [(_,seq,parent,_,r3,sp)] = [e for e in events if e[0]=='create']
                self.assertEqual((seq,parent,r3,src,dst),(sequence.SEQUENCE,task,sp+40,sp+20,sp+40))
                child = read(state+48)
                self.assertEqual((read(task+16),read(child+12),read(child),read(task+20,'H'),read(state+1,'B')),
                                 (child,task,sequence.CALLBACK|1,0x104,30))
                self.assertIn(('returned',child),events)
                self.assertTrue(any(e[0]=='callback' and e[1]==child and e[3]==child+24 and e[4]==0
                                    for e in events))
                self.assertEqual(read(0x03000940,'H'),0x0531)
                self.assertEqual(bytes(u.mem_read(0x03000940+26,16)),struct.pack('<hhhhii',*affine.transform(struct.pack('<iihhhhH',*affine_args))))

    def test_scale_tables_and_both_fade_blocks(self):
        u, events, _, read, pack, call = self.machine()
        task, desc, state = 0x02004100, 0x02004200, 0x02004300
        pack(state,'BB',1,30)
        pack(state+4,'hh',-7,25)
        pack(desc,'H',0x104)
        # The first scale frame falls through from 104. The negative pass
        # reverses the 15-entry table; the other two blocks interpolate y.
        frames = []
        while read(desc,'H') != 0x10A and len(frames)<120:
            phase, timer = read(desc,'H'), read(state+1,'B')
            events.clear()
            self.assertEqual(call(sequence.ROOT,task,desc,state),0)
            frames.append((phase,timer,[e[3] for e in events if e[0]=='affine']))
        self.assertEqual(read(desc,'H'),0x10A)
        scales = list(struct.unpack('<15h',u.mem_read(0x0839C9EC,30)))
        emitted = [(phase,params[0]) for phase,_,params in frames if params]
        self.assertEqual([a[5] for _,a in emitted],
                         scales+[-v for v in reversed(scales)]+[-256]*14)
        self.assertEqual([a[3] for _,a in emitted],
                         [-39]*30+[-39-d for d in (2,4,6,8)]+[-47+4*n for n in range(1,11)])
        self.assertEqual([sum(p==phase for p,_,_ in frames) for phase in range(0x104,0x10A)],
                         [30,14,15,24,4,10])
        self.assertTrue(all((a[0],a[1],a[2],a[4],a[6])==(16*256,24*256,-7,256,0) for _,a in emitted))

    def test_sequence_callback_ignores_scratch_and_descriptor_holes(self):
        import unicorn.arm_const as reg
        from unicorn import UC_HOOK_MEM_READ
        outputs = []
        for fill, scratch in ((0xA5,0x03007F28),(0x2B,0xDEADBEEF)):
            u, events, record, read, pack, call = self.machine()
            manager, parent = read(0x0200F430), 0x02004300
            pack(0x02008FF0,'I',manager)
            pack(manager+12,'H',0x5A)
            u.mem_write(0x03007D00,bytes([fill])*512)
            desc_read = []
            def observe(machine, _, address, width, value, ctx):
                pc = machine.reg_read(reg.UC_ARM_REG_PC)
                if sequence.CALLBACK <= pc < sequence.CREATE and events[-1][0] == 'callback':
                    desc = events[-1][2]
                    if desc <= address < desc+28:
                        desc_read.append((address-desc,width))
            def descriptor(machine):
                desc = machine.reg_read(reg.UC_ARM_REG_R2)
                self.assertEqual(bytes(u.mem_read(desc,28)), bytes([fill])*4+
                    struct.pack('<I',sequence.SEQUENCE)+bytes([fill])*12+bytes(4)+bytes([fill])*4)
            record(sequence.SCHEDULE,descriptor)
            u.hook_add(UC_HOOK_MEM_READ,observe)
            child = call(sequence.CREATE,sequence.SEQUENCE,parent,0xCAFE,scratch)
            self.assertEqual((read(parent+16),read(child+12),read(child),read(child+20,'H'),read(child+22,'H')),
                             (child,parent,sequence.CALLBACK|1,0x100,0x5B))
            calls = [e for e in events if e[0]=='callback']
            self.assertEqual(len(calls),1)
            self.assertEqual((calls[0][1],calls[0][3],calls[0][4]),(child,child+24,0))
            self.assertEqual(desc_read,[(0,2),(4,4),(20,2),(22,2)])
            ctrl,values=struct.unpack('<HH',u.mem_read(sequence.SEQUENCE,4))
            expected=struct.pack('<IBBBBBBH',sequence.SEQUENCE,0,(ctrl&192)>>6,ctrl&255,(ctrl>>8)&63,values&31,(values>>8)&31,1)
            self.assertEqual(bytes(u.mem_read(child+24,12)),expected)
            outputs.append(bytes(u.mem_read(child,72)))
        self.assertEqual(outputs[0],outputs[1])

    def test_reject_changed_native_registration_scheduler_and_callback(self):
        import match
        from inert_spin_profile import index_snapshot
        objects, index = match.data_snapshot(self.root), index_snapshot(self.root)
        for pc in (0x08394BC8, 0x08394D94, 0x080D35AC, 0x08005B8A, 0x08005A02,
                   0x08142250, 0x080D3CE8):
            changed = bytearray(self.rom)
            changed[pc - match.ROM_BASE] ^= 1
            proof = sequence.AffineSequenceProof(bytes(changed), self.mapping, index, objects)
            with self.subTest(pc=hex(pc)), self.assertRaises(ValueError):
                sequence.scheduler_inputs(proof)

    def test_replay_and_refuse_changed_scratch_or_report(self):
        import match_evidence
        report = (self.root/'docs/match/080FA76C.md').read_text()
        self.assertTrue(match_evidence.report_matches(report,str(self.root),sequence.ROOT))
        changed = report.replace('"selected_register":3','"selected_register":2')
        self.assertNotEqual(report,changed)
        self.assertFalse(match_evidence.report_matches(changed,str(self.root),sequence.ROOT))
        at = sequence.CREATE - 0x08000000
        original = self.rom[at:at+36]
        self.assertEqual(sequence.constructor(original,self.mapping)['kill'],sequence.CREATE+4)
        for pos in (0,4,12,20,22,28,32):
            changed = bytearray(original)
            changed[pos] ^= 8
            with self.subTest(pos=pos), self.assertRaises((ValueError,RuntimeError)):
                sequence.constructor(bytes(changed),self.mapping)
