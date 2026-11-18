"""Constructor byte provenance, real task lists and original transfer initialization."""
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
import transfer_task_constructor as ctor


@unittest.skipUnless(os.getenv('FFTA_TRANSFER_CONSTRUCTOR_ROOT'), 'requires USA ROM and native compiler')
class TransferConstructorTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_TRANSFER_CONSTRUCTOR_ROOT']).resolve()
        result = owner.build(cls.root, ctor.OWNER, selector=ctor.SELECTOR)
        cls.body, cls.manifest, _, cls.mapping, cls.index, cls.objects, cls.rom, _, cls.elf = result
        cls.report = owner.render(ctor.OWNER, result)

    def test_native_saved_report_and_bounded_contract(self):
        self.assertEqual(self.body, self.rom[0x5954:0x5A22])
        self.assertTrue(match_evidence.report_matches(self.report, self.root, ctor.OWNER))
        proof = self.manifest['proof']['transfer_construction']
        self.assertEqual(proof['transfer']['phase_zero_reads'], [[0,2],[4,4],[20,2]])
        self.assertEqual(proof['transfer']['counts']['max_count'], 5453)
        for old,new in (('"allocation_success_proved":false', '"allocation_success_proved":true'),
                        ('"arbitrary_callback_effects_proved":false', '"arbitrary_callback_effects_proved":true'),
                        ('206/206 bytes', '205/206 bytes')):
            self.assertIn(old, self.report)
            self.assertFalse(match_evidence.report_matches(self.report.replace(old,new), self.root, ctor.OWNER))

    def test_changed_original_providers_and_layouts(self):
        for offset in (0x5966,0x5970,0x5984,0x599C,0x59B0,0x59B8,0x59C2,0x59EA,0x59EE,0x5A02,
                       0x5A04,0x5A10,0x688E,0x68A8,0x5B82,0x5F18,0x5F32,0x5F4C,0x5FBA,
                       0x6D38,0x7138,0x1443FC,0x14224C,0x142250,0x36D4B8,0xA38A42):
            changed = bytearray(self.rom)
            changed[offset] ^= 1
            with self.subTest(offset=hex(offset)), self.assertRaises(ValueError):
                owner.verify(bytes(changed[0x5954:0x5A22]), ctor.OWNER, bytes(changed), self.mapping,
                             self.index, self.objects, selector=ctor.SELECTOR, bindings=ctor.BINDINGS)

    def test_typed_relocations_and_source_required(self):
        image = match.elf_image(self.elf)
        bindings, targets = owner.original_bindings(image, ctor.OWNER, self.rom, self.mapping, self.objects,
                                                   selector=ctor.SELECTOR,index=self.index)
        self.assertEqual(bindings, ctor.BINDINGS)
        for group, index, label in [('calls',1,'_call_via_r3'), ('calls',2,'func_08005EF8'),
                                    ('data',0,'data_03005E78')]:
            altered = copy.deepcopy(bindings)
            altered[group][index][1] = label
            with self.subTest(group=group, label=label), self.assertRaises(ValueError):
                ctor.check_bindings(altered, targets, image)
        with self.assertRaises(ValueError):
            owner.preflight(self.body, ctor.OWNER, self.rom, self.mapping, self.index, self.objects, selector=ctor.SELECTOR)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root/'include').mkdir()
            (root/'src').mkdir()
            (root/'include/ffta.h').write_bytes((self.root/'include/ffta.h').read_bytes())
            path = 'src/08005954.c'
            source = (self.root/path).read_text()
            for old,new in [('typedef u32 (*TaskCallback)', 'typedef void (*TaskCallback)'),
                            ('event.phase = 0;', 'event.phase = 1;'), ('u32 payload[1];', 'u32 payload[2];')]:
                self.assertIn(old, source)
                (root/path).write_text(source.replace(old,new))
                with self.subTest(old=old), self.assertRaises(ValueError):
                    ctor.check_source(root, ctor.OWNER)

    def call(self, cpu, address, *args):
        from test_bg_affine_rows import NativeAffineRows
        return NativeAffineRows.call(self, cpu, address, *args)

    def scenario(self, records, *, small_heap=False):
        from test_packed_transfer_task import TransferTaskTests
        from unicorn import UC_HOOK_CODE, UC_HOOK_MEM_READ, UC_HOOK_MEM_WRITE
        from unicorn.arm_const import UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3, UC_ARM_REG_SP

        cpu = TransferTaskTests.cpu(self)
        manager = self.call(cpu, 0x08005C14, 0x0201A000, 0x600 if small_heap else 0x24000)
        cpu.mem_write(0x02008FF0, struct.pack('<I', manager))
        cpu.mem_write(manager+12, b'\x01\x00')
        def word(address, n=4):
            return int.from_bytes(cpu.mem_read(address, n), 'little')

        # Deliberately different padding bytes demonstrate that only the transferred fields are interpreted.
        cpu.mem_write(0x03007D00, bytes(range(128))*4)
        entries = 0x02009000
        record = struct.pack('<IIHBB', 0x02004000, 0x02004400, 4, 0, 0)
        maximum = max(n for _,_,n in records)
        if maximum:
            cpu.mem_write(entries, record * maximum)
        state, nodes = {}, {}

        def visit(machine, pc, size, _):
            a,b,c,d = (machine.reg_read(r) for r in (UC_ARM_REG_R0,UC_ARM_REG_R1,UC_ARM_REG_R2,UC_ARM_REG_R3))
            if pc == ctor.OWNER:
                self.assertEqual([a,b,c], [manager, ctor.transfer.OWNER|1, 64 + 12*state['n']])
                self.assertEqual(word(machine.reg_read(UC_ARM_REG_SP)), state['parent'])
                state['source'] = d
                state['before'] = bytes(cpu.mem_read(d,28))
            elif pc == 0x0800597A:
                state['node'] = a
                self.assertTrue(a)
            elif pc == 0x08005988:
                self.assertEqual(bytes(cpu.mem_read(state['node'],state['size'])), bytes(state['size']))
            elif pc == 0x03005E78 and a == state.get('node'):
                self.assertEqual(b,state['size'])
                state['clearing'] = True
            elif pc == 0x03005EA6:
                state['clearing'] = False
            elif pc == ctor.transfer.OWNER:
                self.assertEqual(a,state['node'])
                self.assertEqual(c,a+24)
                self.assertEqual(word(a+20,2),0)
                self.assertEqual(word(a+22,2),1)
                self.assertEqual(word(a+12),state['parent'])
                self.assertEqual(word(a+4),state['previous'])
                self.assertEqual(word(a),ctor.transfer.OWNER|1)
                self.assertNotEqual(b,state['source'])
                self.assertEqual(bytes(cpu.mem_read(b,28)), b'\0\0'+state['before'][2:])
                state['event'] = b
            elif pc == 0x08005A0C:
                state['event'] = None
                self.assertEqual(bytes(cpu.mem_read(state['source'],28)), state['before'])

        def read(machine, access, address, size, value, _):
            event = state.get('event')
            if event is not None and event <= address < event+28:
                state['reads'].append((address-event,size))

        def write(machine, access, address, size, value, _):
            if state.get('clearing') and state['node'] <= address < state['node']+state['size']:
                self.assertEqual((address, size, value), (state['node']+state['cleared'],4,0))
                state['cleared'] += size

        for pc in (ctor.OWNER, 0x0800597A, 0x08005988, 0x03005E78, 0x03005EA6, ctor.transfer.OWNER, 0x08005A0C):
            cpu.hook_add(UC_HOOK_CODE,visit,begin=pc,end=pc)
        cpu.hook_add(UC_HOOK_MEM_READ,read)
        cpu.hook_add(UC_HOOK_MEM_WRITE,write)
        cpu.ctl_flush_tb()
        tails = {}
        for name,parent,n in records:
            previous = tails.get(parent,0)
            state.clear()
            state.update(n=n, size=92+12*n, parent=nodes.get(parent,0), previous=previous, cleared=0, reads=[])
            node = self.call(cpu, 0x08006878, entries if n else 0, n, state['parent'])
            self.assertEqual(node, state['node'])
            self.assertEqual(state['cleared'],state['size'])
            self.assertEqual(state['reads'],[(0,2),(4,4),(20,2)])
            self.assertEqual(word(node+20,2),0x100)
            self.assertEqual(word(node+22,2),0)
            self.assertEqual(word(node+24,2),n)
            self.assertEqual(word(node+28,2),0x800)
            self.assertEqual(bool(word(node+32)),not small_heap)
            if n:
                self.assertEqual(bytes(cpu.mem_read(node+76,n*12)),record*n)
            if previous:
                self.assertEqual(word(previous+8),node)
            else:
                self.assertEqual(word(state['parent']+16 if parent else manager+4),node)
            self.assertEqual(word(node+8),0)
            nodes[name] = node
            tails[parent] = node

    def test_real_root_child_and_sibling_appends(self):
        self.scenario([('root',None,0),('peer',None,1),('another',None,2),('child','root',1),
                       ('second','root',3),('third','root',0),('subchild','child',2)])

    def test_last_nonwrapping_transfer_count(self):
        self.scenario([('root',None,5453)])

    def test_successful_task_with_unavailable_optional_buffer(self):
        self.scenario([('root',None,1)],small_heap=True)
