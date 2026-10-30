"""Decoded pack-only inventory cases, without compiler or original-ROM replay."""
import copy
import hashlib
import json
from pathlib import Path
import struct
import sys
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
import private_float_closure_effects_inventory as inventory
import software_float_profile as runtime
from capstone import Cs,CS_ARCH_ARM,CS_MODE_THUMB
BASE=0x08000000
ADDRESS,PACK=BASE+0x100,BASE+0x300


def words(*values):
    return struct.pack('<'+'H'*len(values),*values)


def call(site,target):
    delta=target-site-4
    return words(0xF000|((delta>>12)&0x7FF),0xF800|((delta>>1)&0x7FF))


class PrivateFloatClosureEffectsTests(unittest.TestCase):
    def fixture(self,*,prefix=None,body=None,body_count=None,pack=None):
        if prefix is None:prefix=words(0xB500,0xB084,0x9000,0x2100,0x9101,0x9102,0x9103)
        if body is None:
            prefix+=words(0x4668)
            body=prefix+call(ADDRESS+len(prefix),PACK)+words(0xB004,0xBC02,0x4708)
        if pack is None:pack=words(0xB510,0x1C04,0x6820,0x6861,0x68A2,0x68E3,0xBC10,0xBC02,0x4708)
        count=lambda data,start:len(list(Cs(CS_ARCH_ARM,CS_MODE_THUMB).disasm(data,start)))
        counts={ADDRESS:count(body,ADDRESS) if body_count is None else body_count,PACK:count(pack,PACK)}
        rom=bytearray(0x400);rows=[]
        for start,data in ((ADDRESS,body),(PACK,pack)):
            rom[start-BASE:start-BASE+len(data)]=data
            rows.append({'rom':f'0x{start:08X}','end':f'0x{start+len(data):08X}','mode':'thumb','instrs':counts[start]})
        mapping=json.dumps(rows).encode()
        index=''.join(f"{int(row['rom'],16):08X} {int(row['end'],16):08X} "
            f"{int(row['end'],16)-int(row['rom'],16)} {row['instrs']} return\n" for row in rows).encode()
        helpers=((inventory.HELPERS[0][0],(PACK,PACK+len(pack),counts[PACK],hashlib.sha256(pack).hexdigest()),inventory.HELPERS[0][2]),)
        return body,bytes(rom),mapping,index,helpers

    def verify_fixture(self,*,fixture=None,data=None,rom=None,mapping=None,index=None,
                       helpers=None,selector=None,manifest=None):
        body,original,maps,text,specs=self.fixture() if fixture is None else fixture
        selected=original if rom is None else rom
        with patch.object(inventory,'HELPERS',specs if helpers is None else helpers), \
                patch.object(runtime,'ROM_SHA256',hashlib.sha256(selected).hexdigest()):
            return inventory.verify(body if data is None else data,ADDRESS,selected,
                maps if mapping is None else mapping,text if index is None else index,
                selector=inventory.SELECTOR if selector is None else selector,manifest=manifest)

    def test_pack_only_uses_one_fresh_helper_then_complete_caller(self):
        original=runtime.prove_runtime;calls=[]
        def observe(*args,**kwargs):
            calls.append(args[2]);return original(*args,**kwargs)
        with patch.object(runtime,'prove_runtime',side_effect=observe):
            result,instructions=self.verify_fixture()
        self.assertEqual(calls,[PACK,ADDRESS])
        self.assertEqual(len(instructions),12)
        self.assertEqual(len(result['helper_closure']),1)
        effect=result['helper_closure'][0]['native_proof']['argument_effects']
        self.assertTrue(effect['complete'])
        self.assertEqual(effect['reads'],[[0,0,4],[0,4,4],[0,8,4],[0,12,4]])
        self.assertEqual(effect['writes'],[])
        self.assertEqual(result['external_reads'],[])
        self.assertEqual(result['external_writes'],[])
        self.assertEqual(len(result['caller']['argument_accesses']),4)
        self.assertTrue(all(item[-1][:2]==['stack',0] for item in result['caller']['argument_accesses']))
        self.assertEqual(result['numeric_return_facts'],[])
        self.assertFalse(result['source_or_ELF_admission'])
        self.assertFalse(result['universal_termination_claim'])

    def test_selector_types_exact_callshape_and_manifest_bindings(self):
        body,rom,mapping,index,helpers=self.fixture()
        prefix=body[:16]+call(ADDRESS+16,PACK)+words(0x4668)
        double=prefix+call(ADDRESS+len(prefix),PACK)+words(0xB004,0xBC02,0x4708)
        with self.assertRaises(ValueError):self.verify_fixture(fixture=self.fixture(body=double))
        with self.assertRaisesRegex(ValueError,'explicit inventory'):self.verify_fixture(selector='default')
        with self.assertRaisesRegex(ValueError,'typed inputs'):self.verify_fixture(mapping=bytearray(mapping))
        with self.assertRaisesRegex(ValueError,'manifest differs'):self.verify_fixture(manifest={})

    def test_pinned_pack_identity_unique_dual_indexes_and_complete_span(self):
        _,rom,mapping,index,_=self.fixture();changed=bytearray(rom);changed[0x300]^=1
        with self.assertRaisesRegex(ValueError,'identity'):self.verify_fixture(rom=bytes(changed))
        for key,value in (('instrs',8),('mode','arm'),('end','0x08000310')):
            rows=json.loads(mapping);rows[1][key]=value
            with self.subTest(key=key),self.assertRaises(ValueError):self.verify_fixture(mapping=json.dumps(rows).encode())
        rows=json.loads(mapping);rows.append(rows[1])
        with self.assertRaises(ValueError):self.verify_fixture(mapping=json.dumps(rows).encode())
        with self.assertRaises(ValueError):self.verify_fixture(index=index.replace(b'08000300 08000312 18 9',b'08000300 08000312 18 8'))

    def test_pack_reads_must_remain_live_caller_locals(self):
        body=self.fixture()[0]
        for opcode in (0xA804,0xA805,0x2000,0x4618):
            changed=body[:14]+words(opcode)+body[16:]
            with self.subTest(opcode=opcode),self.assertRaises(ValueError):self.verify_fixture(fixture=self.fixture(body=changed))

    def test_fresh_helper_complete_effect_receipt_cannot_be_dropped_or_forged(self):
        original=runtime.prove_runtime
        for field,value in (('missing',None),('schema','old'),('complete',False),
                            ('body_sha256','0'*64),('address',PACK+2)):
            def corrupt(*args,**kwargs):
                proof=original(*args,**kwargs)
                if args[2]==PACK:
                    if field=='missing':proof.pop('argument_effects')
                    else:proof['argument_effects'][field]=value
                return proof
            with self.subTest(field=field),patch.object(runtime,'prove_runtime',side_effect=corrupt),self.assertRaises(ValueError):
                self.verify_fixture()
        with patch.object(runtime,'EDGES',((PACK+2,ADDRESS),)),self.assertRaisesRegex(ValueError,'closed leaf'):
            self.verify_fixture()

    def test_scalar_loop_complete_graph_reached_return_and_restoration(self):
        prefix=words(0xB500,0xB084,0x9000,0x2100,0x9101,0x9102,0x9103,0x3A01,0x2A00,0xD1FC)
        result,instructions=self.verify_fixture(fixture=self.fixture(prefix=prefix))
        self.assertEqual(len(result['caller']['returns']),1)
        self.assertEqual(len(result['caller']['native_edges']),len(instructions))
        broken=self.fixture()[0][:-2]+words(0x4700)
        with self.assertRaises(ValueError):self.verify_fixture(fixture=self.fixture(body=broken))

    def test_direct_caller_literal_partition_extent_and_unreferenced_tail(self):
        prefix=words(0xB500,0xB084,0x9000,0x2100,0x9101,0x9102,0x9103,0x4A03,0x4668)
        body=prefix+call(ADDRESS+18,PACK)+words(0xB004,0xBC02,0x4708)+struct.pack('<I',0x12345678)
        result,_=self.verify_fixture(fixture=self.fixture(body=body,body_count=13))
        self.assertEqual(result['partition']['code_bytes'],28)
        self.assertEqual(result['partition']['literal_and_table_bytes'],4)
        self.assertEqual(result['partition']['words'][0]['address'],ADDRESS+28)
        self.assertEqual(result['partition']['words'][0]['load_sites'],[ADDRESS+14])
        with self.assertRaises(ValueError):self.verify_fixture(fixture=self.fixture(body=body[:-4],body_count=13))
        with self.assertRaises(ValueError):self.verify_fixture(fixture=self.fixture(body=body+b'\0'*4,body_count=13))


if __name__=='__main__':unittest.main()
