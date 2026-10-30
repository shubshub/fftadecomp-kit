"""Self-contained decoded structural double-effect fixtures, without original-ROM runs."""
import copy
import contextlib
import hashlib
import io
import json
from pathlib import Path
import struct
import sys
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import private_double_argument_effects_inventory as inventory
import software_double_profile as double
import software_float_profile as runtime
from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB

BASE = 0x08000000
ADDRESS, UNPACK, COMPARE = BASE+0x100, BASE+0x300, BASE+0x500


def words(*values):
    return struct.pack('<'+'H'*len(values), *values)


def call(site, target):
    delta = target-site-4
    return words(0xF000 | ((delta >> 12) & 0x7FF), 0xF800 | ((delta >> 1) & 0x7FF))


class PrivateDoubleArgumentEffectsTests(unittest.TestCase):
    def fixture(self, *, unpack=None, compare=None, caller=None, widths=None):
        if unpack is None:
            # Two input words, local byte/halfword reads, and five output words.
            unpack = words(0xB510,0xB082,0x6802,0x6843,0x9300,0x9201,0x466C,
                0x88E2,0x79E3,0x600A,0x604A,0x608A,0x688A,0x60CA,0x610B,
                0xB002,0xBC10,0xBC01,0x4700)
        if compare is None:
            compare = words(0xB530,0x1C04,0x1C0D,
                0x6820,0x6860,0x68A0,0x68E0,0x6920,
                0x6828,0x6868,0x68A8,0x68E8,0x6928,0xBC30,0xBC02,0x4708)
        if caller is None:
            caller = words(0xB510,0xB08E,0x900A,0x910B,0x920C,0x930D,0xA80A,0x4669)
            caller += call(ADDRESS+16,UNPACK)+words(0xA80C,0xAC05,0x1C21)
            caller += call(ADDRESS+26,UNPACK)+words(0x4668,0x1C21)
            caller += call(ADDRESS+34,COMPARE)+words(0xB00E,0xBC10,0xBC02,0x4708)
        parts = {ADDRESS: caller, UNPACK: unpack, COMPARE: compare}
        decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
        counts = {start: len(list(decoder.disasm(body, start))) for start, body in parts.items()}
        rom = bytearray(0x800)
        rows = []
        for start, body in sorted(parts.items()):
            rom[start-BASE:start-BASE+len(body)] = body
            rows.append({'rom': f'0x{start:08X}', 'end': f'0x{start+len(body):08X}',
                         'mode': 'thumb', 'instrs': counts[start]})
        mapping = json.dumps(rows).encode()
        index = ''.join(f"{int(row['rom'],16):08X} {int(row['end'],16):08X} "
            f"{int(row['end'],16)-int(row['rom'],16)} {row['instrs']} return\n" for row in rows).encode()
        helpers = tuple((name,(start,start+len(parts[start]),counts[start],
            hashlib.sha256(parts[start]).hexdigest()),copy.deepcopy(bounds),
            supplied if widths is None else widths)
            for (name,_,bounds,supplied),start in zip(inventory.HELPERS,(UNPACK,COMPARE)))
        return caller,bytes(rom),mapping,index,helpers

    @contextlib.contextmanager
    def configuration(self, fixture, *, helpers=None, rom=None):
        _,original,_,_,specs = fixture
        selected = original if rom is None else rom
        specs = specs if helpers is None else helpers
        identities = tuple(item[1] for item in specs)
        with patch.object(inventory,'HELPERS',specs), \
                patch.object(runtime,'IDENTITIES',identities), \
                patch.object(double,'IDENTITIES',identities), \
                patch.object(runtime,'ROM_SHA256',hashlib.sha256(selected).hexdigest()):
            yield

    def verify_fixture(self, *, fixture=None, helpers=None, data=None, rom=None,
                       mapping=None, index=None, selector=None, manifest=None):
        fixture = self.fixture() if fixture is None else fixture
        body,image,maps,text,_ = fixture
        with self.configuration(fixture,helpers=helpers,rom=rom):
            return inventory.verify(body if data is None else data,ADDRESS,
                image if rom is None else rom,maps if mapping is None else mapping,
                text if index is None else index,
                selector=inventory.SELECTOR if selector is None else selector,manifest=manifest)

    def test_complete_actual_double_effects_and_local_discharge(self):
        result,instructions = self.verify_fixture()
        self.assertEqual(len(instructions),20)
        self.assertTrue(result['inventory_only'])
        self.assertTrue(result['complete_native_structural_proof'])
        self.assertTrue(result['complete_argument_effect_proof'])
        unpack,compare = result['helper_closure']
        self.assertEqual(unpack['native_proof']['argument_effects']['reads'],
                         [[0,0,4],[0,4,4],[1,8,4]])
        self.assertEqual(unpack['native_proof']['writes'],[(1,n,4) for n in range(0,20,4)])
        self.assertEqual(compare['native_proof']['argument_effects']['reads'],
                         [[r,n,4] for r in (0,1) for n in range(0,20,4)])
        self.assertEqual(result['external_reads'],[])
        self.assertEqual(result['external_writes'],[])
        self.assertEqual(result['caller']['stack_reads'],[])
        self.assertEqual(len(result['caller']['argument_accesses']),26)
        self.assertTrue(all(row[-1][:2]==['stack',0] for row in result['caller']['argument_accesses']))
        self.assertTrue(all(row['native_proof']['argument_effects']['loaded_values']==
            'unknown scalars; no numeric facts' for row in result['helper_closure']))
        self.assertEqual(result['numeric_return_facts'],[])
        self.assertFalse(result['source_or_ELF_admission'])
        self.assertFalse(result['physical_memory_claim'])

    def test_cli_selects_same_explicit_private_profile(self):
        fixture=self.fixture();body,rom,mapping,index,_=fixture
        files={'fixture.rom':rom,'fixture.mapping':mapping,'fixture.index':index}
        original=Path.read_bytes
        def read(path):
            return files[str(path)] if str(path) in files else original(path)
        output=io.StringIO()
        with self.configuration(fixture),patch.object(Path,'read_bytes',read), \
                patch.object(sys,'argv',['inventory','--profile',inventory.SELECTOR,
                    '--rom','fixture.rom','--mapping','fixture.mapping','--index','fixture.index',hex(ADDRESS)]), \
                contextlib.redirect_stdout(output):
            inventory.main()
        self.assertEqual(json.loads(output.getvalue())['selector'],inventory.SELECTOR)

    def test_selector_typed_inputs_rom_and_manifest_are_bound(self):
        fixture=self.fixture();_,rom,mapping,_,_=fixture
        with self.assertRaisesRegex(ValueError,'explicit inventory'):
            self.verify_fixture(selector='default')
        with self.assertRaisesRegex(ValueError,'typed inputs'):
            self.verify_fixture(mapping=bytearray(mapping))
        with patch.object(runtime,'ROM_SHA256','0'*64),self.assertRaisesRegex(ValueError,'ROM identity'):
            inventory.verify(fixture[0],ADDRESS,rom,mapping,fixture[3],selector=inventory.SELECTOR)
        with self.assertRaisesRegex(ValueError,'manifest differs'):
            self.verify_fixture(manifest={})

    def test_wrong_private_call_sequence_and_unknown_call_are_refused(self):
        fixture=self.fixture();body,rom,*_=fixture
        for offset,target in [(16,COMPARE),(34,UNPACK),(34,COMPARE+2)]:
            changed=body[:offset]+call(ADDRESS+offset,target)+body[offset+4:]
            with self.subTest(offset=offset,target=target),self.assertRaisesRegex(ValueError,'two pinned unpacks|structural inventory is not closed'):
                self.verify_fixture(fixture=self.fixture(caller=changed))

    def test_dual_indexes_and_unique_helper_ownership_are_mandatory(self):
        fixture=self.fixture();_,_,mapping,index,_=fixture
        for key,value in [('instrs',18),('mode','arm'),('end','0x08000320')]:
            rows=json.loads(mapping);rows[1][key]=value
            with self.subTest(key=key),self.assertRaises(ValueError):
                self.verify_fixture(mapping=json.dumps(rows).encode())
        rows=json.loads(mapping);rows.append(rows[-1])
        with self.assertRaises(ValueError):self.verify_fixture(mapping=json.dumps(rows).encode())
        with self.assertRaises(ValueError):
            self.verify_fixture(index=index.replace(b'38 19',b'38 18'))

    def test_helper_identity_and_reserved_identity_crosscheck_are_mandatory(self):
        fixture=self.fixture();_,rom,_,_,specs=fixture
        changed=bytearray(rom);changed[UNPACK-BASE]^=1
        with self.assertRaisesRegex(ValueError,'identity'):
            self.verify_fixture(rom=bytes(changed))
        with self.configuration(fixture),patch.object(double,'IDENTITIES',()), \
                self.assertRaisesRegex(ValueError,'identities'):
            inventory.verify(fixture[0],ADDRESS,rom,fixture[2],fixture[3],selector=inventory.SELECTOR)

    def test_exact_output_read_policy_and_internal_width_optin_are_required(self):
        fixture=self.fixture();specs=copy.deepcopy(fixture[-1])
        specs[0][2]['reads'].remove([1,8,4])
        with self.assertRaisesRegex(ValueError,'external read'):
            self.verify_fixture(fixture=fixture,helpers=specs)
        expanded=copy.deepcopy(fixture[-1]);expanded[0][2]['reads'].append([1,12,4])
        with self.assertRaisesRegex(ValueError,'exact policy'):
            self.verify_fixture(fixture=fixture,helpers=expanded)
        with self.assertRaisesRegex(ValueError,'memory operation'):
            self.verify_fixture(fixture=self.fixture(widths=(4,)))

    def test_caller_effects_cannot_overlap_saved_or_incoming_stack(self):
        body=self.fixture()[0]
        for offset,opcode,reason in [(12,0xA80E,'saved'),(12,0xA810,'frame'),
                                     (22,0xAC0C,'saved'),(22,0xAC10,'frame')]:
            changed=body[:offset]+words(opcode)+body[offset+2:]
            with self.subTest(offset=offset,opcode=opcode),self.assertRaisesRegex(ValueError,reason):
                self.verify_fixture(fixture=self.fixture(caller=changed))

    def test_unknown_constant_and_loaded_pointer_reads_are_unbounded(self):
        for compare in [words(0x6800,0x6800,0x4770),words(0x2000,0x6800,0x4770),
                        words(0x6940,0x4770)]:
            with self.subTest(compare=compare.hex()),self.assertRaisesRegex(ValueError,'external read'):
                self.verify_fixture(fixture=self.fixture(compare=compare))
        body=self.fixture()[0]
        changed=body[:30]+words(0x980A)+body[32:]
        with self.assertRaisesRegex(ValueError,'external read'):
            self.verify_fixture(fixture=self.fixture(caller=changed))

    def test_out_of_policy_write_and_unrestored_callee_return_are_refused(self):
        unpack=self.fixture()[1][UNPACK-BASE:UNPACK-BASE+38]
        changed=unpack[:28]+words(0x614B)+unpack[30:]
        with self.assertRaisesRegex(ValueError,'external write'):
            self.verify_fixture(fixture=self.fixture(unpack=changed))
        changed=unpack[:34]+words(0x2400)+unpack[34:]
        with self.assertRaisesRegex(ValueError,'restoration'):
            self.verify_fixture(fixture=self.fixture(unpack=changed))

    def test_child_complete_effect_receipt_hash_target_and_policy_are_bound(self):
        original=runtime.prove_runtime
        for field,value in [('complete',False),('body_sha256','0'*64),('address',UNPACK+2),
                            ('schema','unbound')]:
            def corrupt(*args,**kwargs):
                result=original(*args,**kwargs)
                if args[2]==UNPACK:result['argument_effects'][field]=value
                return result
            with self.subTest(field=field),patch.object(runtime,'prove_runtime',side_effect=corrupt), \
                    self.assertRaisesRegex(ValueError,'receipt'):
                self.verify_fixture()

    def test_unknown_nested_helper_dependency_and_unowned_tail_are_refused(self):
        with patch.object(double,'EDGES',((COMPARE+2,UNPACK),)), \
                patch.object(runtime,'EDGES',((COMPARE+2,UNPACK),)), \
                self.assertRaisesRegex(ValueError,'closed leaf'):
            self.verify_fixture()
        compare=self.fixture()[1][COMPARE-BASE:COMPARE-BASE+32]
        with self.assertRaisesRegex(ValueError,'CFG/closure|gap'):
            self.verify_fixture(fixture=self.fixture(compare=compare+b'\0'*4))


if __name__=='__main__':
    unittest.main()
