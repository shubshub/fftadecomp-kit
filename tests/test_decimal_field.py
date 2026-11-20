"""Complete fixed-ROM formatter interval, bounded runtime operands and opaque strlen lane."""
import copy
import os
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import decimal_field as field
import match_evidence
import owner_admission_profile as owner


@unittest.skipUnless(os.environ.get('FFTA_DECIMAL_FIELD_ROOT'), 'requires ROM and exact decimal formatter source')
class DecimalField(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_DECIMAL_FIELD_ROOT'])
        cls.built = owner.build(cls.root, field.OWNER, selector=field.buffers.DATAFREE_SELECTOR)
        cls.rom = cls.built[6]

    def test_native_owner_and_stale_receipt(self):
        raw, manifest, _, mapping, index, objects, _, _, original = self.built
        self.assertEqual(raw, self.rom[0x142DC:0x1439C])
        self.assertEqual(manifest['bindings'], field.BINDINGS)
        report = (self.root/'docs/match/080142DC.md').read_text()
        self.assertIn('* control flow: ' + field.buffers.DECIMAL_FIELD_CONTROL_FLOW, report.splitlines())
        self.assertTrue(match_evidence.report_matches(report, self.root, field.OWNER))
        for old, new in (('"opaque_byte":7','"opaque_byte":6'), ('"half_domain":[0,32767]','"half_domain":[0,65535]'),
                         ('"second_word_cases":28160','"second_word_cases":28161')):
            changed = report.replace(old,new)
            self.assertNotEqual(report,changed)
            self.assertFalse(match_evidence.report_matches(changed, self.root, field.OWNER))
        changed = copy.deepcopy(manifest['proof']['environment'])
        changed['sources']['decimal_field.py'] = '0'*64
        with patch.object(field,'environment_fingerprint',return_value=changed):
            self.assertFalse(match_evidence.report_matches(report,self.root,field.OWNER))
        import match
        image = match.elf_image(original)
        for symbol in ('func_08002FB8','func_081444B8'):
            mutated = copy.deepcopy(image)
            next(row for row in mutated['symbols'] if row['name'] == symbol)['size'] = 4
            with self.assertRaises(ValueError):
                owner.original_bindings(mutated,field.OWNER,self.rom,mapping,objects,
                                        selector=field.buffers.DATAFREE_SELECTOR,index=index)

    def test_unwritten_byte_is_not_part_of_a_seven_byte_array(self):
        from tempfile import TemporaryDirectory
        with TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root/'src').mkdir()
            (root/'include').mkdir()
            (root/'include/ffta.h').write_bytes((self.root/'include/ffta.h').read_bytes())
            source = self.root/'src/080142DC.c'
            changed = source.read_text().replace('u8 text[8];','u8 text[7];')
            self.assertNotEqual(changed,source.read_text())
            (root/'src/080142DC.c').write_text(changed)
            with self.assertRaisesRegex(ValueError,'eight-byte local'):
                field.check_source(root)

    def machine(self):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_PROT_READ, UC_PROT_EXEC
        from unicorn import arm_const as arm
        cpu = Uc(UC_ARCH_ARM,UC_MODE_THUMB)
        cpu.mem_map(field.BASE,len(self.rom))
        cpu.mem_write(field.BASE,self.rom)
        cpu.mem_protect(field.BASE,len(self.rom),UC_PROT_READ|UC_PROT_EXEC)
        end, stack = 0x02000000, 0x02003800
        cpu.mem_map(end,0x4000)
        def call(entry, *args):
            for reg,value in enumerate(args,arm.UC_ARM_REG_R0):
                cpu.reg_write(reg,value)
            cpu.reg_write(arm.UC_ARM_REG_SP,stack)
            cpu.reg_write(arm.UC_ARM_REG_LR,end|1)
            cpu.emu_start(entry|1,end,count=30000)
            self.assertEqual(cpu.reg_read(arm.UC_ARM_REG_PC),end)
            self.assertEqual(cpu.reg_read(arm.UC_ARM_REG_SP),stack)
            return cpu.reg_read(arm.UC_ARM_REG_R0)
        return cpu,call,stack

    def test_complete_runtime_operand_domain_and_producer(self):
        cpu,call,_ = self.machine()
        for half in range(32768):
            self.assertEqual(call(field.remainder.ADDRESS,half,5),half%5)
            self.assertEqual(call(field.division.ADDRESS,half,5),half//5)
        dst = 0x02000100
        for number in range(65536):
            cpu.mem_write(dst-1,b'\xa5'*9)
            call(field.DECIMAL,number,dst)
            self.assertEqual(bytes(cpu.mem_read(dst-1,9)), b'\xa5'+str(number).rjust(6).encode()+b'\0\xa5')

    def test_actual_strlen_reads_and_all_padding_values(self):
        from unicorn import UC_HOOK_MEM_READ, UC_HOOK_MEM_WRITE
        from unicorn import arm_const as arm
        cpu,call,stack = self.machine()
        local, dst = stack-32, 0x02000100
        reads, writes = [], []
        def read(machine, access, address, size, value, userdata):
            if field.LENGTH <= machine.reg_read(arm.UC_ARM_REG_PC) < field.PINS[field.LENGTH][0]:
                reads.append((address-local,size))
        def write(machine, access, address, size, value, userdata):
            if field.DECIMAL <= machine.reg_read(arm.UC_ARM_REG_PC) < field.PINS[field.DECIMAL][0]:
                writes.append((address-local,size))
        cpu.hook_add(UC_HOOK_MEM_READ,read,begin=local,end=stack+0x7FF)
        cpu.hook_add(UC_HOOK_MEM_WRITE,write,begin=local,end=local+7)
        for opaque in range(256):
            cpu.mem_write(local+7,bytes([opaque]))
            reads.clear(); writes.clear()
            self.assertEqual(call(field.OWNER,dst,0xFFFF8000|opaque,3),7)
            self.assertEqual(reads,[(0,4),(4,4),(4,1),(5,1),(6,1)])
            self.assertEqual(writes,[(i,1) for i in range(6,-1,-1)])
            self.assertEqual(bytes(cpu.mem_read(local+7,1)),bytes([opaque]))

    def test_caller_stack_output_preserves_neighboring_slots(self):
        cpu,call,stack = self.machine()
        # This synthetic caller layout reserves a writable array between live slots.
        destination = stack + 32
        cpu.mem_write(stack, b'\xa5' * 64)
        self.assertEqual(call(field.OWNER,destination,42,3),7)
        expected = b'\x81\x18\x81\x1c\x81\x1a\x00'
        self.assertEqual(bytes(cpu.mem_read(stack,64)), b'\xa5'*32 + expected + b'\xa5'*25)
        conditions = ' '.join(self.built[1]['proof']['conditions'])
        self.assertIn('designated writable object in a caller frame',conditions)
        self.assertIn('all live protected save and return slots',conditions)

    def test_widths_prefix_truncation_upper_argument_bits_and_guards(self):
        cpu,call,_ = self.machine()
        dst = 0x02000100
        for number in (0,1,9,10,99,100,999,1000,9999,10000,32767,32768,65535,65536,0xffffffff):
            for width in range(256):
                active = width or 1
                decimal = str(number&65535).zfill(active)[:active]
                output = b''.join((0x8000|(ord(c)+0xe8)).to_bytes(2,'big') for c in decimal)+b'\0'
                cpu.mem_write(dst-1,b'\xa5'*(len(output)+2))
                self.assertEqual(call(field.OWNER,dst,number,0xFF00|width),len(output))
                self.assertEqual(bytes(cpu.mem_read(dst-1,len(output)+2)),b'\xa5'+output+b'\xa5')
