"""Synthetic exact adapter semantics and closed dependency boundaries."""
import copy
import json
from pathlib import Path
import struct
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'tools'))
import match
import function_thunk_profile as thunk
import scalar_callback_adapter_inventory as adapter

A, G = 0x08001000, 0x08002000
T = thunk.ALIASES['_call_via_r2']


def bl(site, target):
    delta = target-site-4
    return struct.pack('<HH', 0xF000|((delta>>12)&0x7FF), 0xF800|((delta>>1)&0x7FF))


def fixture(*, context=4, returning=1, changes=None, getter=None):
    code = bytearray(struct.pack('<HH', 0xB500|(1<<context), 0x1C08|context))
    code += bl(A+4,G)
    code += struct.pack('<HH', 0x6801|(context<<3), 0x6842|(context<<3))
    code += bl(A+12,T)
    code += struct.pack('<HHH', 0xBC00|(1<<context), 0xBC00|(1<<returning), 0x4700|(returning<<3))
    for offset, value in (changes or {}).items():
        struct.pack_into('<H', code, offset, value)
    leaf = getter if getter is not None else bytes.fromhex('00687047')
    rom = bytearray(thunk.END-match.ROM_BASE)
    for number, target in enumerate(thunk.ALIASES.values()):
        struct.pack_into('<HH',rom,target-match.ROM_BASE,0x4700+(number<<3),0x46C0)
    bodies = {A:bytes(code),G:leaf,T:bytes(rom[T-match.ROM_BASE:T-match.ROM_BASE+2])}
    counts = {A:9,G:2,T:1}
    rows = []
    for point, body in bodies.items():
        rom[point-match.ROM_BASE:point-match.ROM_BASE+len(body)] = body
        rows.append(dict(rom=f'0x{point:08X}', end=f'0x{point+len(body):08X}',
                         mode='thumb',instrs=counts[point]))
    index = ''.join(f'{int(row["rom"],16):08X} {int(row["end"],16):08X} '
                    f'{int(row["end"],16)-int(row["rom"],16)} {row["instrs"]} return\n' for row in rows).encode()
    return dict(address=A,getter=G,rom=bytes(rom),mapping=json.dumps(rows).encode(),index=index,selector=adapter.SELECTOR)


class AdapterTests(unittest.TestCase):
    def test_exact_complete_relation_and_explicit_conditions(self):
        report = adapter.verify(**fixture())
        self.assertEqual(report['descriptor_reads'], [dict(site=A+8,offset=0,width=4,destination=1),dict(site=A+10,offset=4,width=4,destination=2)])
        self.assertEqual(report['callback']['result'],'unchanged callback R0')
        self.assertFalse(report['callback']['descriptor_address_passed_as_argument'])
        self.assertFalse(report['actual_callback_ABI_established'])
        self.assertFalse(report['numeric_nonalias_proved'])
        self.assertFalse(report['source_or_ELF_admission'])
        self.assertEqual(len(report['explicit_conditions']),4)

    def test_other_saved_context_and_return_registers(self):
        for context in range(4,8):
            for returning in range(1,4):
                with self.subTest(context=context,returning=returning):
                    report=adapter.verify(**fixture(context=context,returning=returning))
                    self.assertEqual(report['descriptor_register'],context)

    def test_zero_add_copy_preserves_descriptor_identity(self):
        report=adapter.verify(**fixture(changes={2:0x1C0C}))
        self.assertEqual(report['descriptor_register'],4)

    def test_nonzero_add_cannot_rebase_descriptor(self):
        with self.assertRaisesRegex(ValueError,'exact getter'):
            adapter.verify(**fixture(changes={2:0x1C4C}))

    def test_wrong_descriptor_offsets_and_argument_transfer_refuse(self):
        for value in (0x68A1,0x6819,0x1C21):
            with self.subTest(value=value), self.assertRaisesRegex(ValueError,'argument word zero'):
                adapter.verify(**fixture(changes={8:value}))

    def test_wrong_target_offset_refuses(self):
        with self.assertRaisesRegex(ValueError,'target word four'):
            adapter.verify(**fixture(changes={10:0x68A2}))

    def test_getter_write_or_different_load_refuses(self):
        for leaf in ('00607047','40687047','01687047'):
            with self.subTest(leaf=leaf), self.assertRaisesRegex(ValueError,'getter must only load'):
                adapter.verify(**fixture(getter=bytes.fromhex(leaf)))

    def test_result_clobber_or_wrong_saved_restore_refuses(self):
        for changes in ({18:0xBC01,20:0x4700},{16:0xBC20}):
            with self.subTest(changes=changes), self.assertRaisesRegex(ValueError,'restore its context'):
                adapter.verify(**fixture(changes=changes))

    def test_unintended_call_target_refuses(self):
        values=fixture(); data=bytearray(values['rom'])
        data[A-match.ROM_BASE+12:A-match.ROM_BASE+16]=bl(A+12,G)
        values['rom']=bytes(data)
        with self.assertRaisesRegex(ValueError,'exact getter'):
            adapter.verify(**values)

    def test_wrong_canonical_thunk_or_padding_refuses(self):
        for offset,value in ((0,0x4708),(2,0)):
            values=fixture(); data=bytearray(values['rom'])
            struct.pack_into('<H',data,T-match.ROM_BASE+offset,value); values['rom']=bytes(data)
            with self.subTest(offset=offset), self.assertRaises(ValueError):
                adapter.verify(**values)

    def test_incomplete_or_overlapping_owner_refuses(self):
        for change in ('short','overlap'):
            values=fixture(); rows=json.loads(values['mapping'])
            if change=='short': rows[0]['end']=f'0x{A+20:08X}'
            else: rows.append(dict(rom=f'0x{A+2:08X}',end=f'0x{A+4:08X}',mode='thumb',instrs=1))
            values['mapping']=json.dumps(rows).encode()
            with self.subTest(change=change), self.assertRaises(ValueError):
                adapter.verify(**values)

    def test_stale_instruction_count_refuses(self):
        values=fixture(); rows=json.loads(values['mapping']); rows[0]['instrs']=10
        values['mapping']=json.dumps(rows).encode()
        with self.assertRaises(ValueError): adapter.verify(**values)

    def test_manifest_exact_and_changed_claim_refuses(self):
        values=fixture(); report=adapter.verify(**values)
        self.assertEqual(adapter.verify(**values,manifest=report),report)
        changed=copy.deepcopy(report); changed['actual_callback_ABI_established']=True
        with self.assertRaisesRegex(ValueError,'manifest differs'):
            adapter.verify(**values,manifest=changed)

    def test_selector_and_immutable_input_contract(self):
        for key,value in (('selector',''),('address',True),('rom',bytearray())):
            values=fixture(); values[key]=value
            with self.subTest(key=key),self.assertRaises(ValueError): adapter.verify(**values)
