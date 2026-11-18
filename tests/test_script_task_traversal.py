"""Native script command, game pump, fade completion and task-tree release."""
import copy
import os
from pathlib import Path
import struct
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import match_evidence
import owner_admission_profile as owner
import script_task_traversal as walk


@unittest.skipUnless(os.getenv('FFTA_SCRIPT_TRAVERSAL_ROOT'), 'requires USA ROM and native compiler')
class ScriptTraversalTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_SCRIPT_TRAVERSAL_ROOT']).resolve()
        result = owner.build(cls.root,walk.OWNER,selector=walk.SELECTOR)
        cls.body,cls.manifest,_,cls.mapping,cls.index,cls.objects,cls.rom,_,cls.elf = result
        cls.report = owner.render(walk.OWNER,result)

    def test_saved_report_and_source_scope(self):
        self.assertEqual(self.body,self.rom[0x5A24:0x5AFE])
        self.assertTrue(match_evidence.report_matches(self.report,self.root,walk.OWNER))
        proof = self.manifest['proof']['script_traversal']
        self.assertEqual(proof['defined_event_offsets'],[0,1])
        self.assertEqual(proof['registration']['callback'],walk.CALLBACK)
        for old,new in [('"arbitrary_callbacks_proved":false','"arbitrary_callbacks_proved":true'),
                        ('"retained_event_address":false','"retained_event_address":true'),('218/218 bytes','217/218 bytes')]:
            self.assertIn(old,self.report)
            self.assertFalse(match_evidence.report_matches(self.report.replace(old,new),self.root,walk.OWNER))

    def test_changed_owner_callback_constructor_and_fade_routes(self):
        for offset in (0x5A3C,0x5A58,0x5A64,0x5A70,0x5A78,0x5A80,0x5AA4,0x5AB4,0x5ADC,0x5AEC,
                       0x58E0,0x5940,0x5A02,0x122C2C,0x126AEC,0x121B9E,0x1219A2,0x126BD0,
                       0x126BE4,0x126BF0,0x126BF4,0x121928,0x22CEA,0x22CFA,0x364C,0x24234,0x2436A,0x245CC,0x22D5C,0xA38A42):
            changed = bytearray(self.rom)
            changed[offset] ^= 1
            with self.subTest(offset=hex(offset)), self.assertRaises(ValueError):
                owner.verify(bytes(changed[0x5A24:0x5AFE]),walk.OWNER,bytes(changed),self.mapping,self.index,
                             self.objects,bindings=walk.BINDINGS,selector=walk.SELECTOR)

    def test_source_and_elf_binding_mutations(self):
        image = match.elf_image(self.elf)
        bindings,targets = owner.original_bindings(image,walk.OWNER,self.rom,self.mapping,self.objects,
                                                   selector=walk.SELECTOR,index=self.index)
        self.assertEqual(bindings,walk.BINDINGS)
        for group,index,name in [('data',0,'data_020159CC'),('calls',0,'func_08126B9C'),('calls',1,'_call_via_r3')]:
            different = copy.deepcopy(bindings)
            different[group][index][1] = name
            with self.assertRaises(ValueError):
                walk.check_bindings(different,targets,image)
        with self.assertRaises(ValueError):
            owner.preflight(self.body,walk.OWNER,self.rom,self.mapping,self.index,self.objects,selector=walk.SELECTOR)
        path = 'src/08005A24.c'
        s = (self.root/path).read_text()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root/'src').mkdir()
            (root/'include').mkdir()
            (root/'include/ffta.h').write_bytes((self.root/'include/ffta.h').read_bytes())
            for old,new in [('node->flags ^= 1;','node->flags = 1;'),('node->state == 3','node->state == 2'),
                            ('data_02008FF0->current = node;','manager->current = node;')]:
                self.assertIn(old,s)
                (root/path).write_text(s.replace(old,new))
                with self.assertRaises(ValueError): walk.check_source(root,walk.OWNER)

    def call(self,cpu,address,*args):
        from test_bg_affine_rows import NativeAffineRows
        return NativeAffineRows.call(self,cpu,address,*args)

    def application(self, tree):
        from test_packed_transfer_task import TransferTaskTests
        from unicorn import UC_HOOK_CODE, UC_HOOK_MEM_READ, UC_HOOK_MEM_WRITE
        from unicorn.arm_const import UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2

        cpu = TransferTaskTests.cpu(self)
        call = lambda addr,*args: self.call(cpu,addr,*args)
        def value(address,width=4): return int.from_bytes(cpu.mem_read(address,width),'little')
        def put(address,number): cpu.mem_write(address,struct.pack('<I',number))
        context, step = 0x02011400, 0x02012000
        manager = call(0x08005C14,0x02020000,0x10000)
        put(0x020159CC,context)
        put(context,manager)
        cpu.mem_write(step,bytes([2]))
        events, freed, completions, modes = [], [], [], []
        active_event = None
        inside_pump = False
        nodes, scripts = {}, {}

        def visit(machine,pc,size,_):
            nonlocal active_event,inside_pump
            a,b,c = (machine.reg_read(r) for r in (UC_ARM_REG_R0,UC_ARM_REG_R1,UC_ARM_REG_R2))
            if pc == walk.OWNER:
                self.assertEqual(a,manager)
                inside_pump = True
            elif pc == walk.CALLBACK:
                phase = value(b,2)
                if inside_pump:
                    self.assertEqual(value(walk.SLOT),manager)
                    self.assertEqual(value(manager+8),0 if phase==1 else a)
                    self.assertEqual(c,a+24)
                events.append((a,phase,[],[]))
                active_event = b
            elif pc == 0x08126BFA:
                active_event = None
            elif pc == 0x08007170:
                freed.append(b)
                self.assertEqual(a,value(manager))
                self.assertEqual(bytes(cpu.mem_read(b+4,12)),bytes(12))
            elif pc == 0x0802436A:
                modes.append(a)
            elif pc == 0x08126BF0:
                completions.append(a)
            elif pc == 0x08005AFC:
                inside_pump = False
                self.assertEqual(value(walk.SLOT),0)
                self.assertEqual(value(manager+8),0)
        def read(machine,access,address,width,number,_):
            if active_event is not None and active_event <= address < active_event+28:
                events[-1][2].append((address-active_event,width))
        def write(machine,access,address,width,number,_):
            if active_event is not None and active_event <= address < active_event+28:
                events[-1][3].append((address-active_event,width,number))
        for pc in (walk.OWNER,walk.CALLBACK,0x08126BFA,0x08007170,0x0802436A,0x08126BF0,0x08005AFC):
            cpu.hook_add(UC_HOOK_CODE,visit,begin=pc,end=pc)
        cpu.hook_add(UC_HOOK_MEM_READ,read)
        cpu.hook_add(UC_HOOK_MEM_WRITE,write)
        cpu.ctl_flush_tb()

        # Use only the command's genuine registration. No task phase, callback pointer,
        # fade byte, visitation flag or completion byte is patched by this test.
        for i,(name,parent) in enumerate(tree):
            script = 0x02012800 + 16*i
            scripts[name] = script
            put(script+8,nodes.get(parent,0))
            self.assertEqual(call(walk.COMMAND,script,0),0x115)
            node,phase,reads,writes = events[-1]
            self.assertEqual((phase,reads,writes),(0,[(0,2),(4,4)],[]))
            self.assertEqual(value(node),walk.CALLBACK|1)
            self.assertEqual(value(node+24),script)
            nodes[name] = node
        events.clear()
        if not tree:
            for expected in (1,0):
                call(walk.PUMP,0,step)
                self.assertEqual(value(manager+12,2),expected)
            self.assertEqual((events,freed),([],[]))
            return
        for _ in range(19):
            call(walk.PUMP,0,step)
            call(0x080241B4)
        self.assertEqual(modes,[15]*17)
        self.assertEqual(value(0x0200F390,1),0)
        self.assertEqual(value(manager+4),0)
        for _,phase,reads,writes in events:
            self.assertEqual(reads,[(0,2)])
            if phase==258: self.assertEqual(writes,[(0,2,3)])
            elif writes: self.assertEqual((phase,writes),(256,[(0,2,258)]))
        return nodes,scripts,events,freed,completions

    def test_original_empty_frame(self):
        self.application([])

    def test_original_command_pump_and_display_complete(self):
        nodes,scripts,events,freed,completions = self.application([('root',None)])
        self.assertEqual([phase for _,phase,_,_ in events],[256]*18+[258,1])
        self.assertEqual(freed,[nodes['root']])
        self.assertEqual(completions,[scripts['root']])

    def test_original_tree_visits_once_and_releases_subtrees(self):
        registration = [('root',None),('peer',None),('a','root'),('b','root'),('sub','a')]
        nodes,scripts,events,freed,completions = self.application(registration)
        first_order = [nodes[n] for n in ('root','a','sub','b','peer')]
        self.assertEqual([a for a,p,_,_ in events if p==256],first_order*18)
        self.assertEqual([a for a,p,_,_ in events if p==258],[nodes['root'],nodes['peer']])
        cleanup = [nodes[k] for k in ('b','sub','a','root','peer')]
        self.assertEqual([a for a,p,_,_ in events if p==1],cleanup)
        self.assertEqual(freed,cleanup)
        self.assertEqual(completions,[scripts['root'],scripts['peer']])
