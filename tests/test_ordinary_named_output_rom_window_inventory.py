"""Decoded positive and decisive negatives for the exact conditional ROM window."""
import copy
import json
import os
from pathlib import Path
import struct
import subprocess
import sys
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
from capstone import Cs,CS_ARCH_ARM,CS_MODE_THUMB
import ordinary_named_output_rom_window_inventory as profile

parent,named = profile.parent,profile.named
A,S,O = 0x08010000,0x08021000,0x08022000
HELPER_WORDS = [0xB5F0,0x4647,0xB480,0x9C06,0x46A0,0x9F07,0x0400,0x1400,
    0x0412,0x1412,0x1A84,0x1064,0x801C,0x4E0A,0x8C35,0x1964,0x801C,
    0x1880,0x1082,0x0409,0x1449,0x1A52,0x4641,0x800A,0x8C71,0x1852,
    0x4644,0x8022,0x8038,0xBC08,0x4698,0xBCF0,0xBC01,0x4700]
PREFIX = [0xB5F0,0xB084,0x1C0E,0x466C,0x340A,0xAD03,0xAB02,0x2100,
    0x8019,0x8021,0x8029,0xA802,0x2100,0x5E40,0x2200,0x5EA1,
    0x2300,0x5EEA,0x9400,0x9501,0xAB02,'named','ordinary',0x2800,('beq','other')]
CHAIN = [('ldr',3,'anchor'),0x78F2,0x3A01,0x18D2,0x7812,'ordinary',('b','done')]
SUFFIX = ['other:',('ldr',0,'scalar'),'done:',0xB004,0xBCF0,0xBC02,0x4708,
    'align','anchor:',('word',profile.ANCHOR),'scalar:',('word',277)]


def machine(sequence):
    labels,cursor = {},A
    for item in sequence:
        if isinstance(item,str) and item.endswith(':'):
            labels[item[:-1]] = cursor
        elif item == 'align':
            cursor = (cursor+3)&~3
        else:
            cursor += 4 if item in ('named','ordinary') or isinstance(item,tuple) and item[0] == 'word' else 2
    data = bytearray()
    for item in sequence:
        site = A+len(data)
        if isinstance(item,str) and item.endswith(':'):
            continue
        if item == 'align':
            data += b'\0'*((-site)&3)
        elif type(item) is int:
            data += struct.pack('<H',item)
        elif item in ('named','ordinary'):
            target = S if item == 'named' else O
            delta = target-site-4
            data += struct.pack('<HH',0xF000|((delta>>12)&0x7FF),0xF800|((delta>>1)&0x7FF))
        elif item[0] == 'word':
            data += struct.pack('<I',item[1])
        elif item[0] == 'ldr':
            displacement = labels[item[2]]-((site+4)&~3)
            assert displacement%4 == 0 and 0 <= displacement <= 1020
            data += struct.pack('<H',0x4800|(item[1]<<8)|(displacement//4))
        else:
            displacement = labels[item[1]]-site-4
            assert displacement%2 == 0
            data += struct.pack('<H',(0xD000|((displacement//2)&255)) if item[0] == 'beq' else
                (0xE000|((displacement//2)&2047)))
    return bytes(data)


def fixture(sequence=None):
    sequence = PREFIX+CHAIN+SUFFIX if sequence is None else sequence
    body = machine(sequence)
    helper = struct.pack('<34H',*HELPER_WORDS)+struct.pack('<I',named.GLOBAL)
    count = sum(not (isinstance(item,str) and item.endswith(':')) and item != 'align' and
        not (isinstance(item,tuple) and item[0] == 'word') for item in sequence)
    rows = [{'rom':f'0x{address:08X}','end':f'0x{address+len(data):08X}','mode':'thumb','instrs':n}
        for address,data,n in ((A,body,count),(S,helper,34),(O,b'\x70\x47',1))]
    mapping = (json.dumps(rows,indent=2)+'\n').encode()
    index = ''.join(f'{int(r["rom"],16):08X} {int(r["end"],16):08X} '
        f'{int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n' for r in rows).encode()
    rom = bytearray(profile.END-parent.match.ROM_BASE)
    for address,data in ((A,body),(S,helper),(O,b'\x70\x47')):
        rom[address-parent.match.ROM_BASE:address-parent.match.ROM_BASE+len(data)] = data
    rom[profile.START-parent.match.ROM_BASE:] = bytes(range(256))
    decoder = Cs(CS_ARCH_ARM,CS_MODE_THUMB);decoder.detail = True
    # BL extraction is bounded to actual emitted instruction words, not pool bytes.
    calls = {item.address:item.operands[0].imm for item in decoder.disasm(body,A) if item.mnemonic == 'bl'}
    return dict(data=body,address=A,rom=bytes(rom),mapping=mapping,index=index,
        data_mapping=(json.dumps({named.NAME:f'0x{named.GLOBAL:08X}',profile.NAME:f'0x{profile.ANCHOR:08X}'})+'\n').encode(),
        calls=calls,bindings={site:f'func_{target:08X}' for site,target in calls.items()},selector=profile.SELECTOR,
        readonly_named_buffer_policy=named.named_policy(),readonly_rom_window_policy=profile.window_policy())


class ROMWindowTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.helper = struct.pack('<34H',*HELPER_WORDS)+struct.pack('<I',named.GLOBAL)
        identity = (S,S+len(cls.helper),34,profile.sha(cls.helper))
        for module in (profile,profile.leaf):
            change = patch.object(module,'LEAF',identity);change.start();cls.addClassCleanup(change.stop)

    def native(self,sequence=None,**changes):
        values = fixture(sequence);values.update(changes)
        return profile.verify(**values)

    def test_complete_API_CLI_distinct_premises_modular_zero_and_actual_effects(self):
        values = fixture();result,instructions = profile.verify(**values)
        self.assertEqual(len(instructions),result['instructions'])
        self.assertEqual(result['partition']['literal_and_table_bytes'],8)
        self.assertEqual(result['frame']['maximum_frame_bytes'],36)
        self.assertEqual(result['frame']['formal_stack_callee']['native_leaf']['effects']['store_event_count'],5)
        self.assertEqual(result['frame']['formal_stack_callee']['calls'][0]['writes_entry_SP_offsets'],
            [[-28,2],[-26,2],[-24,2]])
        read = result['ROM_window_provenance']['reads'][0]
        self.assertEqual(read['addresses'],[profile.START,profile.END])
        self.assertEqual(read['modular_subtract_values'],[[0,254],[0xffffffff,0xffffffff]])
        self.assertFalse(result['ROM_window_provenance']['byte_nonzero_precondition'])
        self.assertFalse(result['readonly_ROM_window']['object_extent_inferred'])
        self.assertEqual(result['numeric_return_facts'],[])
        self.assertEqual(result['readonly_named_buffer_policy'],named.named_policy())
        root = Path(os.environ['FFTA_ROM_WINDOW_RETAIN']);root.mkdir(parents=True,exist_ok=True)
        for name,data in (('caller.bin',values['data']),('helper.bin',self.helper),('rom.bin',values['rom']),
                ('functions.json',values['mapping']),('functions.txt',values['index']),('data_symbols.json',values['data_mapping'])):
            (root/name).write_bytes(data)
        (root/'api.json').write_text(json.dumps(result,indent=2)+'\n')
        code = ('import sys;sys.path.insert(0,sys.argv.pop(1));'
            'import ordinary_named_output_rom_window_inventory as p;'
            f'p.LEAF={profile.LEAF!r};p.leaf.LEAF=p.LEAF;p.main()')
        run = subprocess.run([sys.executable,'-c',code,str(Path(profile.__file__).parent),
            '--profile',profile.SELECTOR,'--rom',str(root/'rom.bin'),'--mapping',str(root/'functions.json'),
            '--index',str(root/'functions.txt'),'--data-mapping',str(root/'data_symbols.json'),
            '--readonly-named-buffer-policy',profile.text(named.named_policy()),
            '--readonly-rom-window-policy',profile.text(profile.window_policy()),f'{A:08X}'],capture_output=True,text=True)
        (root/'cli-stderr.txt').write_text(run.stderr);(root/'cli-stdout.json').write_text(run.stdout)
        self.assertEqual(run.returncode,0,run.stderr)
        self.assertEqual(json.loads(run.stdout),result)

    def test_explicit_selector_and_typed_exact_window_only(self):
        for selector in (None,True,profile.leaf.SELECTOR):
            with self.subTest(selector=selector),self.assertRaises(ValueError):self.native(selector=selector)
        policy = profile.window_policy()
        for changed in (None,{},True,dict(policy,readable=1),dict(policy,initialized=False),
                dict(policy,readonly=False),dict(policy,start=profile.START+1),dict(policy,end=profile.END+1),
                dict(policy,anchor=profile.ANCHOR+4),dict(policy,object_size=256)):
            with self.subTest(policy=changed),self.assertRaises(ValueError):self.native(readonly_rom_window_policy=changed)

    def test_anchor_binding_duplicate_name_and_independent_named_premise(self):
        values = fixture();objects = json.loads(values['data_mapping'])
        wrong = dict(objects);wrong[profile.NAME] = '0x083A8194'
        for data in (b'{}',json.dumps(wrong).encode(),bytearray(values['data_mapping']),
                (values['data_mapping'].decode().rstrip()[:-1]+',"g_table_083A8190":"0x083A8190"}').encode()):
            with self.subTest(data=str(data)),self.assertRaises(ValueError):self.native(data_mapping=data)
        with self.assertRaises(ValueError):self.native(readonly_named_buffer_policy=None)
        with self.assertRaises(ValueError):self.native(readonly_named_buffer_policy=profile.window_policy())

    def test_window_must_fit_actual_immutable_ROM_snapshot(self):
        values = fixture()
        for rom in (values['rom'][:-1],bytearray(values['rom'])):
            with self.subTest(kind=type(rom)),self.assertRaises(ValueError):self.native(rom=rom)

    def test_literal_identity_partition_and_exact_load_encoding(self):
        for old,new in ((('word',profile.ANCHOR),('word',profile.ANCHOR+4)),(('word',277),('word',278)),
                (('ldr',3,'anchor'),('ldr',3,'scalar'))):
            sequence = PREFIX+CHAIN+SUFFIX;sequence[sequence.index(old)] = new
            with self.subTest(old=old),self.assertRaises(ValueError):self.native(sequence)

    def test_byte_read_width_subtract_and_exact_source_chain(self):
        for old,new in ((0x78F2,0x88F2),(0x78F2,0x78B2),(0x3A01,0x3A02),
                (0x18D2,0x1892),(0x7812,0x8812),(0x7812,0x7852)):
            sequence = PREFIX+CHAIN+SUFFIX;sequence[sequence.index(old)] = new
            with self.subTest(old=old,new=new),self.assertRaises(ValueError):self.native(sequence)

    def test_caller_clobber_and_overwrite_destroy_index_or_anchor(self):
        for offset,extra in ((2,['ordinary']),(2,[0x2200]),(4,['ordinary']),(1,[0x2300])):
            chain = CHAIN[:offset]+extra+CHAIN[offset:]
            with self.subTest(offset=offset,extra=extra),self.assertRaises(ValueError):self.native(PREFIX+chain+SUFFIX)

    def test_all_predecessor_join_rejects_bypassed_subtract_and_cycles(self):
        chain = CHAIN[:2]+[0x2800,('beq','join'),0x3A01,'join:']+CHAIN[3:]
        with self.assertRaisesRegex(ValueError,'all-path proved'):self.native(PREFIX+chain+SUFFIX)
        with self.assertRaisesRegex(ValueError,'acyclic'):
            self.native(PREFIX+['loop:']+CHAIN[:4]+[0x2800,('beq','loop')]+CHAIN[4:]+SUFFIX)

    def test_zero_local_index_outgoing_saved_slots_and_unmarked_alias_call(self):
        for position,new in ((12,0x2101),(18,0x9402),(19,0x9502),(20,0xAB04)):
            prefix = list(PREFIX);prefix[position] = new
            with self.subTest(position=position,new=new),self.assertRaises(ValueError):self.native(prefix+CHAIN+SUFFIX)
        with self.assertRaisesRegex(ValueError,'crossing calls'):
            self.native(PREFIX[:22]+[0xA802]+PREFIX[22:]+CHAIN+SUFFIX)

    def test_complete_calls_bindings_runtime_and_forged_manifest(self):
        values = fixture()
        for field in ('calls','bindings'):
            changed = dict(values[field]);changed.pop(min(changed))
            with self.subTest(field=field),self.assertRaises(ValueError):self.native(**{field:changed})
        with self.assertRaisesRegex(ValueError,'manifest differs'):self.native(manifest={'complete':True})
        for target in (0x081426B8,0x08142950,parent.thunks.ALIASES['_call_via_r4']):
            changed = dict(values['calls']);changed[min(changed)] = target
            with self.subTest(target=target),self.assertRaises(ValueError):
                profile.bind_calls(changed,values['mapping'],A,len(values['data']),len(values['rom']))

    def test_helper_body_indices_and_actual_proof_receipt_seal(self):
        values = fixture();rom = bytearray(values['rom']);rom[S-parent.match.ROM_BASE+68] ^= 4
        with self.assertRaisesRegex(ValueError,'body identity'):self.native(rom=bytes(rom))
        with self.assertRaises(ValueError):self.native(index=values['index'].replace(b'72 34 return',b'72 36 return'))
        sites = {s:t for s,t in values['calls'].items() if t == S}
        proof = named.NamedReadonlyFormalLeafProof(self.helper,S,values['rom'],values['mapping'],values['index'],
            values['data_mapping'],sites,named.named_policy())
        proof._record['effects']['store_event_count'] = 3
        with self.assertRaises(ValueError):proof.validate_calls(values['calls'])

    def test_old_profile_and_default_frame_still_refuse_same_unmarked_shape(self):
        values = fixture()
        with self.assertRaisesRegex(ValueError,'materialized literal'):
            parent.complete(values['data'],A,values['rom'],values['mapping'],values['index'])
        ins,edges,calls,_,_ = profile.complete(values['data'],A,values['rom'],values['mapping'],values['index'])
        with self.assertRaisesRegex(ValueError,'crossing calls'):
            parent.frame.prove_frame(ins,edges,A,{},calls,stack_aliases=True,
                local_alias_slot_policy=parent.slots.SELECTOR,zero_index_profile=parent.zero_index.SELECTOR)
        rows = json.loads(values['mapping']);rows[0]['instrs'] += 1
        with self.assertRaises(ValueError):self.native(mapping=json.dumps(rows).encode())


if __name__ == '__main__':
    unittest.main()
