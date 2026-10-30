"""Decoded self-contained argument-effect fixtures; no compiler or original-ROM proof."""
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
import private_float_argument_effects_inventory as inventory
import software_float_profile as runtime
from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB

BASE = 0x08000000


def words(*values):
    return struct.pack('<'+'H'*len(values), *values)


def call(site, target):
    distance = target-site-4
    return words(0xF000 | ((distance >> 12) & 0x7FF), 0xF800 | ((distance >> 1) & 0x7FF))


def image(parts):
    result = bytearray(0x400)
    entries = []
    for address, data in sorted(parts.items()):
        result[address-BASE:address-BASE+len(data)] = data
        count = len(list(Cs(CS_ARCH_ARM, CS_MODE_THUMB).disasm(data, address)))
        entries.append({'rom': f'0x{address:08X}', 'end': f'0x{address+len(data):08X}',
                        'mode': 'thumb', 'instrs': count})
    mapping = json.dumps(entries).encode()
    index = ''.join(f"{int(row['rom'],16):08X} {int(row['end'],16):08X} "
                    f"{int(row['end'],16)-int(row['rom'],16)} {row['instrs']} return\n"
                    for row in entries).encode()
    return bytes(result), entries, mapping, index


class PrivateFloatArgumentEffectsTests(unittest.TestCase):
    def prove(self, code, bounds, *, parts=None, dependencies=None, edges=(), **kwargs):
        address = BASE+0x100
        rom, entries, _, _ = image({**(parts or {}), address: code})
        count = next(row['instrs'] for row in entries if int(row['rom'],16) == address)
        return runtime.prove_runtime(rom, entries, address, address+len(code), count,
            dependencies or {}, call_edges=edges, scalar_entries=(),
            argument_effect_policy=bounds, **kwargs)

    def child_fixture(self):
        target = BASE+0x200
        child = words(0x6800, 0x4770)
        caller = words(0xB500, 0xB081, 0x9100, 0x4668)
        caller += call(BASE+0x108, target)+words(0xB001, 0xBC02, 0x4708)
        rom, entries, _, _ = image({BASE+0x100: caller, target: child})
        proof = runtime.prove_runtime(rom, entries, target, target+len(child), 2, {},
            call_edges=(), scalar_entries=(), argument_effect_policy=inventory.policy(((0,0,4),)))
        return target, child, caller, proof

    def module_fixture(self):
        address = BASE+0x100
        first, second = BASE+0x200, BASE+0x300
        unpack = words(0xB510, 0x6802, 0x600A, 0x604A, 0x608A, 0x60CA, 0xBC10, 0xBC01, 0x4700)
        compare = words(0xB510, 0x1C04, 0x6820, 0x6809, 0x1A40, 0xBC10, 0xBC02, 0x4708)
        caller = words(0xB510, 0xB08A, 0x9008, 0x9109, 0xA808, 0x4669)
        caller += call(address+12, first)+words(0xA809, 0xAC04, 0x1C21)
        caller += call(address+22, first)+words(0x4668, 0x1C21)
        caller += call(address+30, second)+words(0xB00A, 0xBC10, 0xBC02, 0x4708)
        rom, entries, mapping, index = image({address: caller, first: unpack, second: compare})
        helpers = tuple((name, (address, address+len(body), len(list(Cs(CS_ARCH_ARM, CS_MODE_THUMB).disasm(body,address))),
                              hashlib.sha256(body).hexdigest()), bounds)
                        for (name, _, bounds), address, body in zip(inventory.HELPERS, (first,second), (unpack,compare)))
        return caller, rom, mapping, index, helpers

    def verify_fixture(self, *, data=None, rom=None, mapping=None, index=None, helpers=None, manifest=None, selector=None):
        body, original, maps, text, specs = self.module_fixture()
        selected = original if rom is None else rom
        with patch.object(inventory, 'HELPERS', specs if helpers is None else helpers), \
                patch.object(runtime, 'ROM_SHA256', hashlib.sha256(selected).hexdigest()):
            return inventory.verify(body if data is None else data, BASE+0x100, selected,
                maps if mapping is None else mapping, text if index is None else index,
                selector=inventory.SELECTOR if selector is None else selector, manifest=manifest)

    def test_direct_effects_report_actual_sets_and_unknown_loaded_values(self):
        proof = self.prove(words(0xB510,0x6802,0x600A,0xBC10,0xBC01,0x4700),
            inventory.policy(((0,0,4),(0,4,4)), ((1,0,4),(1,4,4))))
        self.assertEqual(proof['argument_effects']['reads'], [[0,0,4]])
        self.assertEqual(proof['argument_effects']['writes'], [[1,0,4]])
        self.assertTrue(proof['argument_effects']['complete'])
        self.assertEqual(proof['argument_effects']['loaded_values'], 'unknown scalars; no numeric facts')
        self.assertTrue(proof['native_edges'])
        # A value read from an argument supplies no pointer origin for another load.
        with self.assertRaisesRegex(ValueError, 'external read'):
            self.prove(words(0x6800,0x6800,0x4770), inventory.policy(((0,0,4),)))

    def test_unknown_constant_other_argument_and_out_of_policy_reads_refused(self):
        for code in (words(0x2000,0x6800,0x4770), words(0x6810,0x4770),
                     words(0x6840,0x4770), words(0x3001,0x6800,0x4770)):
            with self.subTest(code=code.hex()), self.assertRaisesRegex(ValueError, 'external read'):
                self.prove(code, inventory.policy(((0,0,4),)))

    def test_finite_policy_exact_types_keys_alignment_and_write_consistency(self):
        good = inventory.policy(((0,0,4),))
        variants = [None, {}, dict(good, extra=0), dict(good, schema='old'),
            dict(good, reads=((0,0,4),)), dict(good, reads=[[False,0,4]]),
            dict(good, reads=[[0,1,4]]), dict(good, reads=[[0,0,3]]),
            dict(good, reads=[[0,-4,4]]), dict(good, reads=[[4,0,4]]),
            dict(good, reads=[[0,4,4],[0,0,4]]), dict(good, reads=[[0,0,4],[0,0,4]])]
        for policy in variants[1:]:
            with self.subTest(policy=policy), self.assertRaisesRegex(ValueError, 'policy|footprint'):
                self.prove(words(0x6800,0x4770), policy)
        with self.assertRaisesRegex(ValueError, 'write policies differ'):
            self.prove(words(0x6800,0x4770), good, allowed_writes=((1,0,4),))

    def test_byte_halfword_widths_and_unbounded_writes(self):
        for opcode, width in ((0x7800,1),(0x8800,2),(0x6800,4)):
            with self.subTest(width=width):
                proof = self.prove(words(opcode,0x4770), inventory.policy(((0,0,width),)), stack_load_widths=(1,2,4))
                self.assertEqual(proof['argument_effects']['reads'], [[0,0,width]])
        with self.assertRaisesRegex(ValueError, 'external write'):
            self.prove(words(0x6008,0x4770), inventory.policy())

    def test_child_reads_into_live_locals_and_external_effect_propagation(self):
        target, child, caller, proof = self.child_fixture()
        result = self.prove(caller, inventory.policy(), parts={target:child},
            dependencies={target:proof}, edges=((BASE+0x108,target),))
        self.assertEqual(result['argument_effects']['reads'], [])
        self.assertEqual(result['argument_accesses'][0][-1], ['stack',0,-8])
        external = words(0xB500)+call(BASE+0x102,target)+words(0xBC02,0x4708)
        result = self.prove(external, inventory.policy(((0,0,4),)), parts={target:child},
            dependencies={target:proof}, edges=((BASE+0x102,target),))
        self.assertEqual(result['argument_effects']['reads'], [[0,0,4]])

    def test_child_saved_incoming_deallocated_and_unknown_arguments_refused(self):
        target, child, _, proof = self.child_fixture()
        cases = [
            (words(0xB501,0x4668), words(0xBC01,0xBC02,0x4708), 'saved'),
            (words(0xB500,0xA801), words(0xBC02,0x4708), 'frame'),
            (words(0xB500,0xB081,0x4668,0xB001), words(0xBC02,0x4708), 'frame'),
            (words(0xB500,0x2000), words(0xBC02,0x4708), 'external read')]
        for prefix, suffix, reason in cases:
            site = BASE+0x100+len(prefix)
            with self.subTest(reason=reason), self.assertRaisesRegex(ValueError, reason):
                self.prove(prefix+call(site,target)+suffix, inventory.policy(), parts={target:child},
                    dependencies={target:proof}, edges=((site,target),))

    def test_child_missing_unknown_incomplete_hash_and_actual_effect_receipts_refused(self):
        target, child, caller, proof = self.child_fixture()
        variants=[]
        for key, value in (('schema','old'),('complete',False),('body_sha256','0'*64),
                           ('address',target+2),('reads',[[0,4,4]]),('writes',[[1,0,4]])):
            altered=copy.deepcopy(proof);altered['argument_effects'][key]=value;variants.append(altered)
        old=copy.deepcopy(proof);old.pop('argument_effects');variants.append(old)
        extra=copy.deepcopy(proof);extra['argument_effects']['extra']=0;variants.append(extra)
        for altered in variants:
            with self.subTest(effect=altered.get('argument_effects')), self.assertRaisesRegex(ValueError, 'receipt|effects differ'):
                self.prove(caller, inventory.policy(), parts={target:child}, dependencies={target:altered},
                    edges=((BASE+0x108,target),))

    def test_all_branch_returns_and_conflicting_pointer_join(self):
        proof=self.prove(words(0x2A00,0xD001,0x6800,0x4770,0x6808,0x4770),
                         inventory.policy(((0,0,4),(1,0,4))))
        self.assertEqual(len(proof['returns']),2)
        self.assertEqual(proof['argument_effects']['reads'],[[0,0,4],[1,0,4]])
        with self.assertRaisesRegex(ValueError,'external read'):
            self.prove(words(0x2A00,0xD001,0x4608,0xE000,0x4610,0x6800,0x4770),
                       inventory.policy(((1,0,4),(2,0,4))))
        with self.assertRaisesRegex(ValueError,'restoration|CFG/closure'):
            self.prove(words(0x2A00,0xD001,0x6800,0x4770,0x6808,0x4708),
                       inventory.policy(((0,0,4),(1,0,4))))

    def test_inventory_complete_private_closure_and_empty_caller_effects(self):
        result, instructions=self.verify_fixture()
        self.assertEqual(len(instructions),18)
        self.assertTrue(result['complete_argument_effect_proof'])
        self.assertEqual(result['external_reads'],[])
        self.assertEqual(result['external_writes'],[])
        self.assertEqual(result['helper_closure'][0]['native_proof']['argument_effects']['writes'],
                         [[1,0,4],[1,4,4],[1,8,4],[1,12,4]])
        self.assertEqual(len(result['caller']['argument_accesses']),12)
        self.assertFalse(result['source_or_ELF_admission'])
        self.assertEqual(result['numeric_return_facts'],[])

    def test_inventory_binding_identity_indices_and_manifest_fail_closed(self):
        data, rom, mapping, index, helpers=self.module_fixture()
        altered=bytearray(rom);altered[0x10C:0x110]=call(BASE+0x10C,helpers[1][1][0])
        with self.assertRaisesRegex(ValueError,'two pinned unpacks'):
            self.verify_fixture(data=bytes(altered[0x100:0x100+len(data)]),rom=bytes(altered))
        altered=bytearray(rom);altered[0x200]^=1
        with self.assertRaisesRegex(ValueError,'identity'):
            self.verify_fixture(rom=bytes(altered))
        for key,value in (('instrs',10),('mode','arm'),('end','0x08000110')):
            rows=json.loads(mapping);rows[1][key]=value
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.verify_fixture(mapping=json.dumps(rows).encode())
        with self.assertRaises(ValueError):
            self.verify_fixture(index=index.replace(b' 42 18 ',b' 42 19 '))
        with self.assertRaisesRegex(ValueError,'manifest differs'):
            self.verify_fixture(manifest={})
        with self.assertRaisesRegex(ValueError,'explicit inventory'):
            self.verify_fixture(selector='default')

    def test_default_none_outputs_and_public_operation_tables_unchanged(self):
        # Fixed pre-change decoded-fixture output digests keep this test standalone.
        expected = ('197fc2321adde765a01f9f4b5a3da3cda4c940983994d1844507ca86102c01af', 'd25393b0d32b8103603de02c4ec81453c84ae3355ab3526bfdb4050b9e6b13f4')
        self.assertEqual(runtime.OPERATIONS, {'__mulsf3': 0x08143CEC, '__fixunssfsi': 0x081428AC,
                                             '__extendsfdf2': 0x0814432C, '__ltdf2': 0x0814379C})
        self.assertEqual(hashlib.sha256(json.dumps(runtime.IDENTITIES).encode()).hexdigest(),
                         'cff489e0dd3a8008b1a2b8188094749ed87eea76d348a1a1f0deaae964f37a2c')
        for number, code in enumerate((words(0x2000,0x6800,0x4770), words(0xB510,0x6802,0x600A,0xBC10,0xBC01,0x4700))):
            rom, entries, _, _=image({BASE+0x100:code})
            kwargs=dict(call_edges=(),scalar_entries=())
            count=len(list(Cs(CS_ARCH_ARM,CS_MODE_THUMB).disasm(code,BASE+0x100)))
            after=runtime.prove_runtime(rom,entries,BASE+0x100,BASE+0x100+len(code),count,{},argument_effect_policy=None,**kwargs)
            self.assertEqual(hashlib.sha256(json.dumps(after,sort_keys=True).encode()).hexdigest(),expected[number])
            self.assertNotIn('argument_effects',after)


if __name__ == '__main__':
    unittest.main()
