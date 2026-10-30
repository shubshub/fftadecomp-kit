"""Self-contained decoded cases for the two freshly proved output leaves."""
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
import ordinary_two_output_callees_inventory as profile
parent=profile.parent
A,F,S,O=0x08010000,0x08020000,0x08021000,0x08022000
FIRST_WORDS=[0xB530,0x9C03,0x9D04,0x0400,0x12C0,0x3010,0x8018,0x0109,
    0x8021,0x0412,0x12D2,0x3210,0x802A,0xBC30,0xBC01,0x4700]
SECOND_WORDS=[0xB5F0,0x4647,0xB480,0x9C06,0x46A0,0x9F07,0x0400,0x1400,
    0x0412,0x1412,0x1A84,0x1064,0x801C,0x4E0A,0x8C35,0x1964,0x801C,
    0x1880,0x1082,0x0409,0x1449,0x1A52,0x4641,0x800A,0x8C71,0x1852,
    0x4644,0x8022,0x8038,0xBC08,0x4698,0xBCF0,0xBC01,0x4700]
HEAD=[0xB570,0x4646,0xB440,0xB085,0x1C04,0x1C0D,0x0624,0x0E24,
    0x062D,0x0E2D,0x1C20,0x1C29,'ordinary',0x1C01,0x0609,0x0E09]
FIRST_ARGS=[0x200A,0x4468,0x4680,0x9000,0xAE03,0x9601,0x1C20,0x1C2A,0xAB02]
LOADS=[0xA802,0x2100,0x5E40,0x4642,0x2300,0x5ED1,0x2300,0x5EF2]
SECOND_ARGS=[0x466C,0x340E,0xAD04,0x9500,0x466B,0x3312,0x9301,0x1C23]
TAIL=[0x8820,0x3878,0x8020,0x8829,0x3960,0x8029,0x2200,0x5EA0,0x0409,
    0x1409,0x2204,0x9200,0x2310,'ordinary',0x0400,0x0C00,0x4240,0x0FC0,
    0xB005,0xBC08,0x4698,0xBC70,0xBC02,0x4708]
SEQUENCE=HEAD+FIRST_ARGS+['first']+LOADS+SECOND_ARGS+['second']+TAIL


def machine(sequence,address=A):
    data=bytearray()
    for word in sequence:
        if type(word) is int:data+=struct.pack('<H',word)
        else:
            target={'ordinary':O,'first':F,'second':S}[word]
            delta=target-(address+len(data))-4
            data+=struct.pack('<HH',0xF000|((delta>>12)&0x7FF),0xF800|((delta>>1)&0x7FF))
    return bytes(data)


def fixture(sequence=SEQUENCE,second=None):
    first=machine(FIRST_WORDS,F)
    second=machine(SECOND_WORDS,S)+struct.pack('<I',profile.GLOBAL) if second is None else second
    body=machine(sequence)
    decoder=Cs(CS_ARCH_ARM,CS_MODE_THUMB);decoder.detail=True
    rows=[{'rom':f'0x{address:08X}','end':f'0x{address+len(data):08X}','mode':'thumb','instrs':count}
        for address,data,count in ((A,body,len(sequence)),(F,first,16),(S,second,34),(O,b'\x70\x47',1))]
    mapping=(json.dumps(rows,indent=2)+'\n').encode()
    index=''.join(f'{int(row["rom"],16):08X} {int(row["end"],16):08X} '
        f'{int(row["end"],16)-int(row["rom"],16)} {row["instrs"]} return\n' for row in rows).encode()
    rom=bytearray(O-parent.match.ROM_BASE+2)
    for address,data in ((A,body),(F,first),(S,second),(O,b'\x70\x47')):
        rom[address-parent.match.ROM_BASE:address-parent.match.ROM_BASE+len(data)]=data
    calls={item.address:item.operands[0].imm for item in decoder.disasm(body,A) if item.mnemonic=='bl'}
    return dict(data=body,address=A,rom=bytes(rom),mapping=mapping,index=index,
        data_mapping=(json.dumps({profile.NAME:f'0x{profile.GLOBAL:08X}'})+'\n').encode(),
        calls=calls,bindings={site:f'func_{target:08X}' for site,target in calls.items()},
        selector=profile.SELECTOR,readonly_named_buffer_policy=profile.named_policy())


class TwoOutputCalleesTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.first=machine(FIRST_WORDS,F)
        cls.second=machine(SECOND_WORDS,S)+struct.pack('<I',profile.GLOBAL)
        first=patch.object(profile,'FIRST',(F,F+len(cls.first),16,profile.sha(cls.first)))
        second=patch.object(profile,'SECOND',(S,S+len(cls.second),34,profile.sha(cls.second)))
        first.start();cls.addClassCleanup(first.stop)
        second.start();cls.addClassCleanup(second.stop)

    def native(self,sequence=SEQUENCE,**changes):
        values=fixture(sequence);values.update(changes)
        return profile.verify(**values)

    def named(self,second=None,**changes):
        body=self.second if second is None else second
        values=fixture(second=body);values.update(changes)
        return profile.NamedReadonlyFormalLeafProof(body,S,values['rom'],values['mapping'],values['index'],
            values['data_mapping'],{site:target for site,target in values['calls'].items() if target==S},
            values['readonly_named_buffer_policy'])

    def pair(self,values):
        return profile.TwoOutputCalleesProof(self.first,self.second,values['rom'],values['mapping'],values['index'],
            values['data_mapping'],values['calls'],values['readonly_named_buffer_policy'])

    def test_complete_API_CLI_real_event_counts_and_read_premise(self):
        values=fixture();result,instructions=profile.verify(**values)
        self.assertEqual(result['instructions'],67);self.assertEqual(len(instructions),67)
        self.assertEqual(result['partition']['code_bytes'],142)
        self.assertEqual(result['frame']['maximum_frame_bytes'],40)
        pair=result['frame']['formal_stack_callee']
        self.assertEqual(pair['store_events'],8)
        self.assertEqual([row['calls'][0]['writes_entry_SP_offsets'] for row in pair['callees']],
            [[[-32,2],[-30,2],[-28,2]],[[-26,2],[-24,2],[-22,2]]])
        leaf=pair['callees'][1]['native_leaf'];effect=leaf['effects']
        self.assertEqual(leaf['frame']['maximum_frame_bytes'],24)
        self.assertEqual(effect['store_event_count'],5)
        self.assertEqual([row[1] for row in effect['store_events']],[3,3,4,4,5])
        self.assertEqual(effect['writes'],[[3,0,2],[4,0,2],[5,0,2]])
        self.assertEqual([[row[2],row[3]] for row in effect['named_reads']],[[32,2],[34,2]])
        self.assertEqual(leaf['partition']['literal_and_table_bytes'],4)
        self.assertEqual(result['readonly_named_buffer_policy'],profile.named_policy())
        self.assertEqual(result['numeric_return_facts'],[])
        self.assertFalse(result['source_or_ELF_admission'] or result['physical_memory_claim'])
        root=Path(os.environ['FFTA_TWO_OUTPUT_RETAIN']);root.mkdir(parents=True,exist_ok=True)
        for name,data in (('caller.bin',values['data']),('first.bin',self.first),('second.bin',self.second),
                ('synthetic-rom.bin',values['rom']),('functions.json',values['mapping']),('functions.txt',values['index']),
                ('data_symbols.json',values['data_mapping'])):(root/name).write_bytes(data)
        (root/'synthetic-api.json').write_text(json.dumps(result,indent=2)+'\n')
        code=('import sys;sys.path.insert(0,sys.argv.pop(1));import ordinary_two_output_callees_inventory as p;'
            f'p.FIRST={profile.FIRST!r};p.SECOND={profile.SECOND!r};p.main()')
        command=[sys.executable,'-c',code,str(Path(profile.__file__).parent),'--profile',profile.SELECTOR,
            '--rom',str(root/'synthetic-rom.bin'),'--mapping',str(root/'functions.json'),
            '--index',str(root/'functions.txt'),'--data-mapping',str(root/'data_symbols.json'),
            '--readonly-named-buffer-policy',profile.text(profile.named_policy()),f'{A:08X}']
        run=subprocess.run(command,capture_output=True,text=True)
        (root/'cli-stderr.txt').write_text(run.stderr)
        self.assertEqual(run.returncode,0,run.stderr);self.assertEqual(json.loads(run.stdout),result)
        (root/'synthetic-cli.json').write_text(run.stdout)

    def test_missing_malformed_or_wider_named_read_permission(self):
        policies=[None,True,{},dict(profile.named_policy(),readable=False),
            dict(profile.named_policy(),reads=[[32,2],[34,2],[36,2]]),
            dict(profile.named_policy(),reads=[[32,4],[34,2]]),dict(profile.named_policy(),extra=True)]
        for policy in policies:
            with self.subTest(policy=policy),self.assertRaisesRegex(ValueError,'premise'):
                self.native(readonly_named_buffer_policy=policy)

    def test_missing_wrong_duplicate_or_mutable_named_mapping(self):
        for data in (b'{}',b'{"g_state_02007F40":"0x02007F42"}',
                b'{"g_state_02007F40":"0x02007F40","g_state_02007F40":"0x02007F40"}',bytearray(b'{}')):
            with self.subTest(data=str(data)),self.assertRaises(ValueError):self.native(data_mapping=data)

    def test_literal_body_tamper_and_reached_literal_binding(self):
        values=fixture();rom=bytearray(values['rom']);rom[S-parent.match.ROM_BASE+68]^=4
        with self.assertRaisesRegex(ValueError,'body identity'):self.native(rom=bytes(rom))
        body=bytearray(self.second);body[-4:]=struct.pack('<I',profile.GLOBAL+4)
        with self.assertRaisesRegex(ValueError,'literal'):self.named(bytes(body))
        words=list(SECOND_WORDS);words[13]=0x4E09
        with self.assertRaises(ValueError):self.named(machine(words,S)+self.second[-4:])

    def test_named_read_width_offset_base_and_writes_rejected(self):
        for position,replacement in ((14,0x6A35),(24,0x8CB1),(14,0x8C05),(16,0x8034)):
            words=list(SECOND_WORDS);words[position]=replacement
            with self.subTest(position=position,replacement=replacement),self.assertRaises(ValueError):
                self.named(machine(words,S)+self.second[-4:])

    def test_formal_origin_extra_entryword_and_pointer_store_rejected(self):
        for position,replacement in ((5,0x9F08),(22,0x4649),(23,0x800B),(12,0x8004),(27,0x8026)):
            words=list(SECOND_WORDS);words[position]=replacement
            with self.subTest(position=position),self.assertRaises(ValueError):self.named(machine(words,S)+self.second[-4:])

    def test_complete_CFG_and_high_saved_return_restoration(self):
        values=fixture();instructions,edges,partition=profile.complete_named(self.second,S,values['rom'],values['mapping'],values['index'])
        changed=dict(edges);changed[S+2]=(S+6,)
        with self.assertRaisesRegex(ValueError,'CFG'):
            profile.prove_named_origins(instructions,changed,S,self.second,partition,values['data_mapping'],profile.named_policy())
        for position,replacement in ((30,0x4690),(32,0xBC02),(33,0x4708),(0,0xB5F8)):
            words=list(SECOND_WORDS);words[position]=replacement
            with self.subTest(position=position),self.assertRaises(ValueError):self.named(machine(words,S)+self.second[-4:])

    def test_missing_or_wrong_actual_call_binding_and_selector(self):
        for selector in (None,True,'other'):
            with self.subTest(selector=selector),self.assertRaises(ValueError):self.native(selector=selector)
        values=fixture()
        for field in ('calls','bindings'):
            changed=dict(values[field]);changed.pop(next(iter(changed)))
            with self.subTest(field=field),self.assertRaises(ValueError):self.native(**{field:changed})
        with self.assertRaises(ValueError):self.native(manifest={})
        with self.assertRaises(ValueError):self.native(HEAD+FIRST_ARGS+['first']+LOADS+SECOND_ARGS+['first']+TAIL)

    def test_reserved_calls_and_unmarked_pointer_call_stay_rejected(self):
        values=fixture()
        for target in (0x081426B8,0x08142950,0x08142AB0,parent.thunks.ALIASES['_call_via_r4']):
            calls=dict(values['calls']);calls[min(calls)]=target
            with self.subTest(target=target),self.assertRaises(ValueError):
                profile.bind_calls(calls,values['mapping'],A,len(values['data']),len(values['rom']))
        with self.assertRaisesRegex(ValueError,'crossing calls'):
            self.native(HEAD+FIRST_ARGS+['ordinary','first']+LOADS+SECOND_ARGS+['second']+TAIL)

    def test_second_outgoing_missing_scalar_misaligned_saved_and_overlap(self):
        for position,replacement in ((3,(0x2000,0x9000)),(3,0x9000),(1,0x340F),(1,0x3414),(7,0xAB00),(7,0xAB04)):
            arguments=list(SECOND_ARGS)
            # Omitting the second pointer store alone retains the earlier
            # valid pointer. Clear that word before asserting missing origin.
            arguments[position:position+1]=list(replacement) if type(replacement) is tuple else [replacement]
            with self.subTest(position=position,replacement=replacement),self.assertRaises(ValueError):
                self.native(HEAD+FIRST_ARGS+['first']+LOADS+arguments+['second']+TAIL)

    def test_both_helpers_have_independent_body_and_dual_index_identity(self):
        values=fixture()
        for address in (F,S):
            rom=bytearray(values['rom']);rom[address-parent.match.ROM_BASE]^=1
            with self.subTest(address=address),self.assertRaisesRegex(ValueError,'body identity'):self.native(rom=bytes(rom))
        rows=json.loads(values['mapping']);rows[2]['instrs']=33
        with self.assertRaises(ValueError):self.native(mapping=json.dumps(rows).encode())
        rows=json.loads(values['mapping']);rows.append(copy.deepcopy(rows[1]))
        with self.assertRaises(ValueError):self.native(mapping=json.dumps(rows).encode())

    def test_named_partial_output_invalidates_overlapping_pointer_slot(self):
        sequence=HEAD+FIRST_ARGS+['first']+LOADS+SECOND_ARGS+[0x9604,'second',0x9804,0x7800]+TAIL
        with self.assertRaisesRegex(ValueError,'ambiguous or expired'):self.native(sequence)

    def test_forged_fresh_pair_descriptor_sites_or_named_effects(self):
        values=fixture();pair=self.pair(values)
        calls=dict(values['calls']);marked=next(iter(pair._second.sites));calls[marked]=F
        with self.assertRaises(ValueError):pair.validate_calls(calls)
        pair._second._record['effects']['named_reads']=[]
        with self.assertRaises(ValueError):pair.validate_calls(values['calls'])
        pair=self.pair(values);pair.sites[marked+2]=pair.sites.pop(marked)
        with self.assertRaises(ValueError):pair.validate_calls(values['calls'])
        with self.assertRaisesRegex(ValueError,'exclusive fresh native'):
            parent.frame.prove_frame({}, {}, A, {}, {},stack_aliases=True,local_alias_slot_policy=parent.slots.SELECTOR,
                formal_stack_callee_proof={'complete':True,'effects':[[3,0,2],[4,0,2],[5,0,2]]})


if __name__=='__main__':unittest.main()
