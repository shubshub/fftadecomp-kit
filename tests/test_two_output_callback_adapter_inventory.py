"""Closed local-output initialization and indirect-callback boundary cases."""
import copy
import json
from pathlib import Path
import struct
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import match
import function_thunk_profile as thunk
import two_output_callback_adapter_inventory as adapter

A, G = 0x08001000, 0x08002000
T = thunk.ALIASES['_call_via_r2']


def bl(site,target):
    delta=target-site-4
    return struct.pack('<HH',0xF000|((delta>>12)&0x7FF),0xF800|((delta>>1)&0x7FF))


def fixture(*,changes=None,getter=None):
    code=bytearray(bytes.fromhex('10b582b00c1c01aa6946')+bl(A+10,G)+
        bytes.fromhex('009821686268')+bl(A+20,T)+bytes.fromhex('02b010bc02bc0847'))
    for offset,value in (changes or {}).items():struct.pack_into('<H',code,offset,value)
    leaf=bytes.fromhex('43680b60006810607047')if getter is None else getter
    rom=bytearray(thunk.END-match.ROM_BASE)
    for number,target in enumerate(thunk.ALIASES.values()):
        struct.pack_into('<HH',rom,target-match.ROM_BASE,0x4700+(number<<3),0x46C0)
    rows=[]
    for point,body,count in [(A,bytes(code),14),(G,leaf,5),(T,bytes(rom[T-match.ROM_BASE:T-match.ROM_BASE+2]),1)]:
        rom[point-match.ROM_BASE:point-match.ROM_BASE+len(body)]=body
        rows.append(dict(rom=f'0x{point:08X}',end=f'0x{point+len(body):08X}',mode='thumb',instrs=count))
    index=''.join(f'{int(r["rom"],16):08X} {int(r["end"],16):08X} '
        f'{int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n'for r in rows).encode()
    return dict(address=A,getter=G,rom=bytes(rom),mapping=json.dumps(rows).encode(),index=index,selector=adapter.SELECTOR)


class AdapterTests(unittest.TestCase):
    def test_complete_initialized_word_and_result_relation(self):
        r=adapter.verify(**fixture())
        self.assertEqual(r['instructions'],14)
        self.assertEqual(r['conditional_frame']['local_interval'],[-16,-8])
        self.assertEqual(r['callback']['arguments'][0],'word read from entry node offset 4')
        self.assertEqual(r['callback']['result'],'unchanged callback R0')
        self.assertFalse(r['conditional_frame']['local_pointer_escape_to_final_callback'])
        self.assertFalse(r['source_or_ELF_admission'])
        self.assertFalse(r['actual_callback_ABI_established'])

    def test_both_distinct_output_words_and_load_order_retained(self):
        r=adapter.verify(**fixture())
        self.assertEqual(r['getter']['ordered_effects'],[
            ['read','entry R0',4,4],['write','helper R1',0,4],
            ['read','entry R0',0,4],['write','helper R2',0,4]])
        self.assertEqual([v['offset']for v in r['conditional_frame']['local_word_initialization']],[-16,-12])
        self.assertEqual(r['getter']['preserved_output_registers'],[1,2])

    def test_missing_second_output_store_refused(self):
        with self.assertRaises(ValueError):adapter.verify(**fixture(getter=bytes.fromhex('43680b60006800227047')))

    def test_getter_load_swap_refused(self):
        with self.assertRaises(ValueError):adapter.verify(**fixture(getter=bytes.fromhex('03680b60406810607047')))

    def test_getter_output_alias_and_offset_refused(self):
        for value in [0x6013,0x604B]:
            leaf=bytearray.fromhex('43680b60006810607047');struct.pack_into('<H',leaf,2,value)
            with self.subTest(value=value),self.assertRaises(ValueError):adapter.verify(**fixture(getter=bytes(leaf)))

    def test_uninitialized_or_wrong_local_word_read_refused(self):
        for value in [0x9801,0x9802,0x9803]:
            with self.subTest(value=value),self.assertRaises(ValueError):adapter.verify(**fixture(changes={14:value}))

    def test_local_pointer_escape_or_descriptor_address_argument_refused(self):
        for offset,value in [(16,0x4669),(16,0x1C21),(18,0xAA01)]:
            with self.subTest(offset=offset,value=value),self.assertRaisesRegex(ValueError,'exact local initialization'):
                adapter.verify(**fixture(changes={offset:value}))

    def test_wrong_descriptor_target_offset_refused(self):
        with self.assertRaises(ValueError):adapter.verify(**fixture(changes={18:0x68A2}))

    def test_wrong_allocation_or_output_local_address_refused(self):
        for offset,value in [(2,0xB083),(6,0xAA00),(6,0xAA02),(8,0xA902)]:
            with self.subTest(offset=offset,value=value),self.assertRaises(ValueError):adapter.verify(**fixture(changes={offset:value}))

    def test_saved_return_and_result_changes_refused(self):
        for changes in [{24:0xB003},{26:0xBC20},{28:0xBC01,30:0x4700}]:
            with self.subTest(changes=changes),self.assertRaises(ValueError):adapter.verify(**fixture(changes=changes))

    def test_selector_and_mutable_inputs_refused(self):
        for key,value in [('selector',None),('selector','ordinary'),('address',True),('rom',bytearray(fixture()['rom']))]:
            args=fixture();args[key]=value
            with self.subTest(key=key),self.assertRaises(ValueError):adapter.verify(**args)

    def test_full_owner_counts_and_extents_required(self):
        for key,value in [('instrs',16),('end',f'0x{A+30:08X}')]:
            args=fixture();rows=json.loads(args['mapping']);rows[0][key]=value;args['mapping']=json.dumps(rows).encode()
            with self.subTest(key=key),self.assertRaises(ValueError):adapter.verify(**args)

    def test_noncanonical_thunk_and_indexed_padding_refused(self):
        args=fixture();rom=bytearray(args['rom']);struct.pack_into('<H',rom,T-match.ROM_BASE,0x4718);args['rom']=bytes(rom)
        with self.assertRaises(ValueError):adapter.verify(**args)
        args=fixture();rows=json.loads(args['mapping']);rows.append(dict(rom=f'0x{T+2:08X}',end=f'0x{T+4:08X}',mode='thumb',instrs=1));args['mapping']=json.dumps(rows).encode()
        with self.assertRaises(ValueError):adapter.verify(**args)

    def test_manifest_tampering_and_input_immutability(self):
        args=fixture();before=copy.deepcopy(args);r=adapter.verify(**args)
        self.assertEqual(args,before)
        r['conditional_frame']['saved_words_overwritten']=True
        with self.assertRaisesRegex(ValueError,'manifest differs'):adapter.verify(**args,manifest=r)

    def test_consistent_dual_maps_cannot_overstate_instruction_counts(self):
        for selected in range(3):
            args=fixture();rows=json.loads(args['mapping']);rows[selected]['instrs']+=1
            args['mapping']=json.dumps(rows).encode()
            lines=args['index'].decode().splitlines();fields=lines[selected].split()
            fields[3]=str(rows[selected]['instrs']);lines[selected]=' '.join(fields)
            args['index']=('\n'.join(lines)+'\n').encode()
            with self.subTest(owner=selected),self.assertRaises(ValueError):adapter.verify(**args)

    def test_consistent_separate_padding_owner_is_still_refused(self):
        args=fixture();rows=json.loads(args['mapping'])
        rows.append(dict(rom=f'0x{T+2:08X}',end=f'0x{T+4:08X}',mode='thumb',instrs=1))
        args['mapping']=json.dumps(rows).encode();args['index']+=f'{T+2:08X} {T+4:08X} 2 1 return\n'.encode()
        with self.assertRaisesRegex(ValueError,'separate padding'):adapter.verify(**args)

    def test_unindexed_noncanonical_thunk_padding_refused(self):
        args=fixture();rom=bytearray(args['rom']);struct.pack_into('<H',rom,T-match.ROM_BASE+2,0x2000);args['rom']=bytes(rom)
        with self.assertRaises(ValueError):adapter.verify(**args)

    def test_redirected_getter_or_descriptor_callback_call_refused(self):
        for site,target in [(10,T),(20,G)]:
            args=fixture();rom=bytearray(args['rom']);rom[A-match.ROM_BASE+site:A-match.ROM_BASE+site+4]=bl(A+site,target);args['rom']=bytes(rom)
            with self.subTest(site=site),self.assertRaises(ValueError):adapter.verify(**args)


if __name__=='__main__':unittest.main()
