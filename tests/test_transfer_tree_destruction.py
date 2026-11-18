import copy
import os
from pathlib import Path
import struct
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match_evidence
import owner_admission_profile as owner
import transfer_tree_destruction as tree


@unittest.skipUnless(os.getenv('FFTA_TRANSFER_TREE_ROOT'), 'requires USA ROM and native compiler')
class TransferTreeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_TRANSFER_TREE_ROOT']).resolve()
        result = owner.build(cls.root, tree.OWNER, selector=tree.SELECTOR)
        cls.body, cls.manifest, _, cls.mapping, cls.index, cls.objects, cls.rom, _, cls.elf = result
        cls.report = owner.render(tree.OWNER, result)

    def test_native_report_preserves_callback_scope(self):
        self.assertEqual(self.body, self.rom[0x58A4:0x5954])
        self.assertTrue(match_evidence.report_matches(self.report, self.root, tree.OWNER))
        proof = self.manifest['proof']['transfer_tree']
        self.assertEqual(proof['initialized_event_bytes'], [0, 1])
        self.assertEqual(proof['descriptor_read_offsets'], [[0, 2]])
        self.assertFalse(proof['arbitrary_callback_effects_proved'])
        self.assertIn('expired event address', proof['empty_root'])
        for old, new in (('"arbitrary_callback_effects_proved":false', '"arbitrary_callback_effects_proved":true'),
                         ('"initialized_event_bytes":[0,1]', '"initialized_event_bytes":[0,1,2]'),
                         ('176/176 bytes', '175/176 bytes')):
            self.assertIn(old, self.report)
            self.assertFalse(match_evidence.report_matches(self.report.replace(old,new), self.root, tree.OWNER))

    def test_changed_callback_traversal_providers_and_sentinel(self):
        for offset in (0x58B0, 0x58BA, 0x58DA, 0x5908, 0x5936, 0x5950, 0x598A,
                       0x5B84, 0x5EFc, 0x5F50, 0x5F5C, 0x5B42, 0x68A8, 0x7172, 0x142250):
            rom = bytearray(self.rom)
            rom[offset] ^= 1
            with self.subTest(offset=hex(offset)), self.assertRaises(ValueError):
                owner.verify(bytes(rom[0x58A4:0x5954]), tree.OWNER, bytes(rom), self.mapping,
                             self.index, self.objects, bindings=tree.BINDINGS, selector=tree.SELECTOR)

    def test_no_fabricated_address_binding_or_callback_target(self):
        for name, value in (('data',[[0xAC,'data_0202BA50',0]]), ('calls',[[60,'func_08005EF8'],[156,'func_08007170']])):
            bindings = copy.deepcopy(tree.BINDINGS)
            bindings[name] = value
            with self.assertRaises(ValueError):
                owner.verify(self.body, tree.OWNER, self.rom, self.mapping, self.index, self.objects,
                             bindings=bindings, selector=tree.SELECTOR)
        with self.assertRaises(ValueError):
            owner.preflight(self.body, tree.OWNER, self.rom, self.mapping, self.index, self.objects, selector=tree.SELECTOR)

    def test_changed_source_even_when_ignored_callback_result(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root/'src').mkdir()
            (root/'include').mkdir()
            (root/'include/ffta.h').write_bytes((self.root/'include/ffta.h').read_bytes())
            path = 'src/080058A4.c'
            source = (self.root/path).read_text()
            for old, new in (('typedef u32 (*TaskCallback)', 'typedef void (*TaskCallback)'),
                             ('event.phase = 1;', 'event.phase = 0;'),
                             ('node->parent = 0;', 'node->child = 0;')):
                (root/path).write_text(source.replace(old,new))
                with self.assertRaises(ValueError):
                    tree.check_source(root, tree.OWNER)

    def call(self, cpu, address, *arguments):
        from test_bg_affine_rows import NativeAffineRows
        return NativeAffineRows.call(self, cpu, address, *arguments)

    def scenario(self, arena, *, interior=False, leaf=False, empty=False, small_heap=False):
        from test_packed_transfer_task import TransferTaskTests
        from unicorn import UC_HOOK_CODE, UC_HOOK_MEM_READ
        from unicorn.arm_const import UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_SP

        cpu = TransferTaskTests.cpu(self)
        def call(addr, *args):
            return self.call(cpu, addr, *args)
        def word(addr):
            return int.from_bytes(cpu.mem_read(addr,4),'little')
        manager = call(0x08005C14, arena, 0x600 if small_heap else 0xC800)
        cpu.mem_write(0x02008FF0, struct.pack('<I', manager))
        nodes, buffers = {}, {}
        names = [] if empty else [('root', None)]
        if not leaf and not empty:
            names += [('peer', None),('A','root'),('B','root'),('A1','A'),('B1','B'),('B2','B')]
        for name, parent in names:
            node = call(0x08006878,0,0,nodes[parent] if parent else 0)
            self.assertEqual(word(node), tree.transfer.OWNER|1)
            self.assertEqual(word(node+12), nodes[parent] if parent else 0)
            nodes[name] = node
            buffers[node] = word(node+32)
            self.assertEqual(bool(buffers[node]), not small_heap)

        freed, callbacks, accesses, delay = [], [], [], []
        event = None
        def visit(c, addr, size, _):
            nonlocal event
            a,b,d = (c.reg_read(r) for r in (UC_ARM_REG_R0,UC_ARM_REG_R1,UC_ARM_REG_R2))
            if addr == tree.transfer.OWNER:
                self.assertEqual(int.from_bytes(c.mem_read(b,2),'little'),1)
                self.assertEqual(d,a+24)
                callbacks.append(a)
                event = b
            elif addr == 0x080058E4:
                event = None
            elif addr == 0x08007170:
                self.assertEqual(a,word(manager))
                if b in buffers:
                    self.assertEqual(bytes(c.mem_read(b+4,12)), bytes(12))
                freed.append(b)
            else:
                delay.append(a)
        def read(c, access, addr, width, value, _):
            if event is not None and event <= addr < event+28:
                accesses.append((addr-event,width))
        for pc in (tree.transfer.OWNER,0x080058E4,0x08007170,0x08005936):
            cpu.hook_add(UC_HOOK_CODE,visit,begin=pc,end=pc)
        cpu.hook_add(UC_HOOK_MEM_READ,read)
        cpu.ctl_flush_tb()
        call(0x08005B58,nodes.get('B' if interior else 'root',0))
        names = [] if empty else ['root'] if leaf else ['B2','B1','B'] if interior else ['B2','B1','B','A1','A','root']
        expected = [nodes[name] for name in names]
        self.assertEqual(callbacks, expected)
        self.assertEqual(accesses,[(0,2)] * len(expected))
        self.assertEqual(freed,[p for n in expected for p in (buffers[n],n) if p])
        self.assertEqual(delay, [3,2,1,0] if tree.SENTINEL in expected else [])
        if empty:
            # The normal void wrapper propagates the allowed scratch value on this return.
            self.assertEqual(cpu.reg_read(UC_ARM_REG_R1),cpu.reg_read(UC_ARM_REG_SP)-52)
        self.assertEqual(word(manager+4),nodes['root'] if interior else nodes.get('peer',0))
        if interior:
            self.assertEqual((word(nodes['root']+16),word(nodes['A']+8),word(nodes['A']+16)),
                             (nodes['A'],0,nodes['A1']))
        elif 'peer' in nodes:
            self.assertEqual(word(nodes['peer']+4),0)
        return nodes.get('root')

    def test_original_nested_and_partial_subtrees(self):
        for interior in (False, True):
            with self.subTest(interior=interior):
                self.scenario(0x02020000, interior=interior)

    def test_original_empty_tree_and_missing_optional_buffer(self):
        self.scenario(0x02020000, empty=True)
        self.scenario(0x02020000, leaf=True, small_heap=True)

    def test_genuine_allocated_node_takes_compared_address_path(self):
        base = 0x02020000
        root = self.scenario(base,leaf=True)
        self.assertEqual(self.scenario(base+tree.SENTINEL-root,leaf=True),tree.SENTINEL)
