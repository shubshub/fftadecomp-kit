"""Decoded private unpack/pack inventory fixtures, with no compiler or original-ROM proof."""
import copy
import hashlib
import json
from pathlib import Path
import struct
import sys
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import private_float_pack_effects_inventory as inventory
import software_float_profile as runtime
from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB

BASE = 0x08000000
ADDRESS, UNPACK, PACK = BASE+0x100, BASE+0x200, BASE+0x300


def words(*values):
    return struct.pack('<'+'H'*len(values), *values)


def call(site, target):
    delta = target-site-4
    return words(0xF000 | ((delta >> 12) & 0x7FF), 0xF800 | ((delta >> 1) & 0x7FF))


def image(parts, counts):
    rom = bytearray(0x400)
    rows = []
    for start, body in sorted(parts.items()):
        rom[start-BASE:start-BASE+len(body)] = body
        rows.append({'rom':f'0x{start:08X}','end':f'0x{start+len(body):08X}',
                     'mode':'thumb','instrs':counts[start]})
    mapping = json.dumps(rows).encode()
    index = ''.join(f"{int(row['rom'],16):08X} {int(row['end'],16):08X} "
        f"{int(row['end'],16)-int(row['rom'],16)} {row['instrs']} return\n" for row in rows).encode()
    return bytes(rom), rows, mapping, index


class PrivateFloatPackEffectsTests(unittest.TestCase):
    def fixture(self, *, pack=None, pack_count=None, caller=None):
        unpack = words(0xB510,0x6802,0x600A,0x604A,0x608A,0x60CA,0xBC10,0xBC01,0x4700)
        if pack is None:
            pack = words(0xB510,0x1C04,0x6820,0x6861,0x68A2,0x68E3,0xBC10,0xBC02,0x4708)
        if caller is None:
            caller = words(0xB500,0xB085,0x9004,0xA804,0x4669)
            caller += call(ADDRESS+10,UNPACK)
            caller += words(0x2100,0x9801,0x2800,0xD100,0x2101,0x9101,0x4668)
            caller += call(ADDRESS+28,PACK)+words(0xB005,0xBC02,0x4708)
        count = lambda data,start: len(list(Cs(CS_ARCH_ARM,CS_MODE_THUMB).disasm(data,start)))
        counts = {ADDRESS:count(caller,ADDRESS),UNPACK:count(unpack,UNPACK),
                  PACK:count(pack,PACK) if pack_count is None else pack_count}
        parts = {ADDRESS:caller,UNPACK:unpack,PACK:pack}
        rom, entries, mapping, index = image(parts,counts)
        helpers = tuple((name,(start,start+len(parts[start]),counts[start],hashlib.sha256(parts[start]).hexdigest()),bounds)
            for (name,_,bounds),start in zip(inventory.HELPERS,(UNPACK,PACK)))
        return caller,rom,entries,mapping,index,helpers

    def verify_fixture(self, *, fixture=None, data=None, rom=None, mapping=None, index=None,
                       helpers=None, manifest=None, selector=None):
        body,original,_,maps,text,specs = self.fixture() if fixture is None else fixture
        selected = original if rom is None else rom
        with patch.object(inventory,'HELPERS',specs if helpers is None else helpers), \
                patch.object(runtime,'ROM_SHA256',hashlib.sha256(selected).hexdigest()):
            return inventory.verify(body if data is None else data,ADDRESS,selected,
                maps if mapping is None else mapping,text if index is None else index,
                selector=inventory.SELECTOR if selector is None else selector,manifest=manifest)

    def test_complete_unpack_pack_closure_actual_effects_and_unknown_result(self):
        result,instructions = self.verify_fixture()
        self.assertEqual(len(instructions),17)
        self.assertTrue(result['complete_native_structural_proof'])
        self.assertTrue(result['complete_argument_effect_proof'])
        self.assertEqual(result['helper_closure'][0]['native_proof']['argument_effects']['reads'],[[0,0,4]])
        self.assertEqual(result['helper_closure'][0]['native_proof']['argument_effects']['writes'],
                         [[1,0,4],[1,4,4],[1,8,4],[1,12,4]])
        self.assertEqual(result['helper_closure'][1]['native_proof']['argument_effects']['reads'],
                         [[0,0,4],[0,4,4],[0,8,4],[0,12,4]])
        self.assertEqual(result['helper_closure'][1]['native_proof']['writes'],[])
        self.assertEqual(result['external_reads'],[])
        self.assertEqual(result['external_writes'],[])
        self.assertEqual(len(result['caller']['argument_accesses']),9)
        self.assertTrue(all(item[-1][:2]==['stack',0] for item in result['caller']['argument_accesses']))
        self.assertEqual(result['numeric_return_facts'],[])
        self.assertFalse(result['source_or_ELF_admission'])
        self.assertFalse(result['physical_memory_claim'])

    def test_exact_call_sequence_explicit_selector_and_manifest_binding(self):
        body,rom,_,mapping,index,_ = self.fixture()
        changed = bytearray(rom);changed[0x10A:0x10E] = call(ADDRESS+10,PACK)
        with self.assertRaisesRegex(ValueError,'one pinned unpack'):
            self.verify_fixture(data=bytes(changed[0x100:0x100+len(body)]),rom=bytes(changed))
        with self.assertRaisesRegex(ValueError,'explicit inventory'):
            self.verify_fixture(selector='default')
        with self.assertRaisesRegex(ValueError,'manifest differs'):
            self.verify_fixture(manifest={})

    def test_helper_identity_complete_dual_indexes_and_typed_input(self):
        _,rom,_,mapping,index,_ = self.fixture()
        changed = bytearray(rom);changed[0x300] ^= 1
        with self.assertRaisesRegex(ValueError,'identity'):
            self.verify_fixture(rom=bytes(changed))
        for key,value in (('instrs',8),('mode','arm'),('end','0x08000310')):
            rows = json.loads(mapping);rows[2][key] = value
            with self.subTest(key=key),self.assertRaises(ValueError):
                self.verify_fixture(mapping=json.dumps(rows).encode())
        duplicate = json.loads(mapping);duplicate.append(duplicate[-1])
        with self.assertRaises(ValueError):
            self.verify_fixture(mapping=json.dumps(duplicate).encode())
        with self.assertRaises(ValueError):
            self.verify_fixture(index=index.replace(b'08000300 08000312 18 9',b'08000300 08000312 18 8'))
        with self.assertRaisesRegex(ValueError,'typed inputs'):
            self.verify_fixture(mapping=bytearray(mapping))

    def test_pack_actual_reads_are_observed_subset_and_loaded_values_are_unknown(self):
        fixture = self.fixture();specs = copy.deepcopy(fixture[-1])
        specs[1][2]['reads'].append([0,16,4])
        result,_ = self.verify_fixture(fixture=fixture,helpers=specs)
        effects = result['helper_closure'][1]['native_proof']['argument_effects']
        self.assertEqual(len(effects['policy']['reads']),5)
        self.assertEqual(effects['reads'],[[0,0,4],[0,4,4],[0,8,4],[0,12,4]])
        self.assertEqual(effects['loaded_values'],'unknown scalars; no numeric facts')
        missing = copy.deepcopy(fixture[-1]);missing[1][2]['reads'].pop()
        with self.assertRaisesRegex(ValueError,'external read'):
            self.verify_fixture(fixture=fixture,helpers=missing)
        for pack in (words(0x6800,0x6800,0x4770),words(0x2000,0x6800,0x4770),
                     words(0x6900,0x4770)):
            with self.subTest(pack=pack.hex()),self.assertRaisesRegex(ValueError,'external read'):
                self.verify_fixture(fixture=self.fixture(pack=pack))

    def test_caller_pack_reads_cannot_use_saved_or_incoming_stack(self):
        body = self.fixture()[0]
        for opcode,reason in ((0xA805,'saved'),(0xA806,'frame')):
            changed = body[:26]+words(opcode)+body[28:]
            with self.subTest(opcode=opcode),self.assertRaisesRegex(ValueError,reason):
                self.verify_fixture(fixture=self.fixture(caller=changed))

    def test_child_requires_complete_read_effect_schema_hash_and_target(self):
        original = runtime.prove_runtime
        for field,value in (('schema','old'),('complete',False),('body_sha256','0'*64),
                            ('address',PACK+2),('reads',[[0,16,4]]),('missing',None)):
            def corrupt(*args,**kwargs):
                proof = original(*args,**kwargs)
                if args[2] == PACK:
                    if field=='missing':proof.pop('argument_effects')
                    else:proof['argument_effects'][field] = value
                return proof
            with self.subTest(field=field),patch.object(runtime,'prove_runtime',side_effect=corrupt), \
                    self.assertRaisesRegex(ValueError,'receipt|effects differ'):
                self.verify_fixture()

    def test_nested_helper_calls_and_unrestored_return_path_refuse(self):
        with patch.object(runtime,'EDGES',((PACK+2,UNPACK),)), \
                self.assertRaisesRegex(ValueError,'closed leaf'):
            self.verify_fixture()
        pack = words(0xB510,0x2A00,0xD002,0xBC10,0xBC02,0x4708,0xBC10,0xBC02,0x4700)
        with self.assertRaisesRegex(ValueError,'restoration|CFG/closure'):
            self.verify_fixture(fixture=self.fixture(pack=pack))

    def test_pack_literal_words_are_directly_reached_and_no_unowned_tail_is_granted(self):
        pack = words(0xB510,0x1C04,0x6820,0x6861,0x68A2,0x68E3,0x4801,0xBC10,0xBC02,0x4708)
        pack += struct.pack('<I',0x12345678)
        result,_ = self.verify_fixture(fixture=self.fixture(pack=pack,pack_count=10))
        partition = result['helper_closure'][1]['partition']
        self.assertEqual(partition['code_bytes'],20)
        self.assertEqual(partition['literal_and_table_bytes'],4)
        self.assertEqual(partition['words'][0]['load_sites'],[PACK+12])
        self.assertEqual(partition['words'][0]['address'],PACK+20)
        with self.assertRaisesRegex(ValueError,'CFG/closure|gap'):
            self.verify_fixture(fixture=self.fixture(pack=pack+b'\0'*4,pack_count=10))


if __name__=='__main__':
    unittest.main()
