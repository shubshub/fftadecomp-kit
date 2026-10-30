"""Decoded cases for two independent native formal-output helpers."""
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
from capstone.arm_const import ARM_REG_R2,ARM_REG_R3
import ordinary_second_formal_output_callees_inventory as profile

parent,named = profile.parent,profile.named
A,F,S,O = 0x08010000,0x08021000,0x08023000,0x08024000
FIRST_WORDS = [0xB5F0,0x4647,0xB480,0x9C06,0x46A0,0x9F07,0x0400,0x1400,
    0x0412,0x1412,0x1A84,0x1064,0x801C,0x4E0A,0x8C35,0x1964,0x801C,
    0x1880,0x1082,0x0409,0x1449,0x1A52,0x4641,0x800A,0x8C71,0x1852,
    0x4644,0x8022,0x8038,0xBC08,0x4698,0xBCF0,0xBC01,0x4700]
SECOND_WORDS = [0xB530,0x4D07,0x8CAC,0x0400,0x1400,0x1B00,0x8010,
    0x8CE8,0x0409,0x1409,0x1A09,0x8019,0xBC30,0xBC01,0x4700,0]
CALLER = [0xB570,0xB084,0x466C,0x340A,0xAD03,0xAB02,0x2100,0x8019,
    0x8021,0x8029,0xA802,0x2100,0x5E40,0x2200,0x5EA1,0x2300,0x5EEA,
    0x9400,0x9501,0xAB02,'first',0xA802,0x2100,0x5E40,0x2200,0x5EA1,
    0xAA02,0x1C23,'second',0xA802,0x8800,0x8821,'ordinary',0xB004,0xBC70,0xBC01,0x4700]


def machine(sequence,address=A):
    data = bytearray()
    for word in sequence:
        if type(word) is int:data += struct.pack('<H',word)
        else:
            target = {'first':F,'second':S,'ordinary':O}[word];delta = target-address-len(data)-4
            data += struct.pack('<HH',0xF000|((delta>>12)&0x7FF),0xF800|((delta>>1)&0x7FF))
    return bytes(data)


def fixture(sequence=CALLER,second_words=SECOND_WORDS):
    body = machine(sequence)
    first,second = machine(FIRST_WORDS,F)+struct.pack('<I',named.GLOBAL),machine(second_words,S)+struct.pack('<I',named.GLOBAL)
    rows = [{'rom':f'0x{address:08X}','end':f'0x{address+len(data):08X}','mode':'thumb','instrs':count}
        for address,data,count in ((A,body,len(sequence)),(F,first,34),(S,second,15),(O,b'\x70\x47',1))]
    mapping = (json.dumps(rows,indent=2)+'\n').encode()
    index = ''.join(f'{int(r["rom"],16):08X} {int(r["end"],16):08X} '
        f'{int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n' for r in rows).encode()
    rom = bytearray(O-parent.match.ROM_BASE+2)
    for address,data in ((A,body),(F,first),(S,second),(O,b'\x70\x47')):
        rom[address-parent.match.ROM_BASE:address-parent.match.ROM_BASE+len(data)] = data
    decoder = Cs(CS_ARCH_ARM,CS_MODE_THUMB);decoder.detail = True
    calls = {i.address:i.operands[0].imm for i in decoder.disasm(body,A) if i.mnemonic == 'bl'}
    return dict(data=body,address=A,rom=bytes(rom),mapping=mapping,index=index,
        data_mapping=(json.dumps({named.NAME:f'0x{named.GLOBAL:08X}'})+'\n').encode(),calls=calls,
        bindings={site:f'func_{target:08X}' for site,target in calls.items()},selector=profile.SELECTOR,
        readonly_named_buffer_policy=named.named_policy(),readonly_second_named_buffer_policy=profile.second_named_policy())


class SecondOutputTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.first = machine(FIRST_WORDS,F)+struct.pack('<I',named.GLOBAL)
        cls.second = machine(SECOND_WORDS,S)+struct.pack('<I',named.GLOBAL)
        identities = ((profile,'FIRST',(F,F+len(cls.first),34,profile.sha(cls.first))),
            (profile.leaf,'LEAF',(F,F+len(cls.first),34,profile.sha(cls.first))),
            (profile,'SECOND',(S,S+len(cls.second),15,profile.sha(cls.second))))
        for module,name,identity in identities:
            changed = patch.object(module,name,identity);changed.start();cls.addClassCleanup(changed.stop)

    def native(self,sequence=CALLER,**changes):
        values = fixture(sequence);values.update(changes)
        return profile.verify(**values)

    def proof(self):
        values = fixture()
        return profile.SecondFormalOutputCalleesProof(self.first,self.second,values['rom'],values['mapping'],
            values['index'],values['data_mapping'],values['calls'],named.named_policy(),profile.second_named_policy())

    def test_full_API_CLI_actual_two_leaf_frames_effects_and_separate_premises(self):
        values = fixture();result,instructions = profile.verify(**values)
        self.assertEqual(result['instructions'],len(CALLER));self.assertEqual(len(instructions),len(CALLER))
        self.assertEqual(result['frame']['maximum_frame_bytes'],32)
        leaves = result['frame']['formal_stack_callee']['callees']
        self.assertEqual([entry['native_leaf']['effects']['store_event_count'] for entry in leaves],[5,2])
        self.assertEqual(leaves[1]['native_leaf']['frame']['maximum_frame_bytes'],12)
        self.assertEqual(leaves[1]['native_leaf']['partition']['code_bytes'],30)
        self.assertEqual(leaves[1]['native_leaf']['partition']['alignment'],[[S+30,S+32]])
        self.assertEqual(leaves[0]['calls'][0]['writes_entry_SP_offsets'],[[-24,2],[-22,2],[-20,2]])
        self.assertEqual(leaves[1]['calls'][0]['writes_entry_SP_offsets'],[[-24,2],[-22,2]])
        self.assertEqual([[r[2],r[3]] for r in leaves[1]['native_leaf']['effects']['named_reads']],[[36,2],[38,2]])
        self.assertEqual(result['numeric_return_facts'],[]);self.assertFalse(result['nonescape_claim'])
        root = Path(os.environ['FFTA_SECOND_OUTPUT_RETAIN']);root.mkdir(parents=True,exist_ok=True)
        for name,data in (('caller.bin',values['data']),('C918.bin',self.first),('C960.bin',self.second),
                ('rom.bin',values['rom']),('functions.json',values['mapping']),('functions.txt',values['index']),
                ('data_symbols.json',values['data_mapping'])):(root/name).write_bytes(data)
        (root/'api.json').write_text(json.dumps(result,indent=2)+'\n')
        code = ('import sys;sys.path.insert(0,sys.argv.pop(1));import ordinary_second_formal_output_callees_inventory as p;'
            f'p.FIRST={profile.FIRST!r};p.SECOND={profile.SECOND!r};p.leaf.LEAF=p.FIRST;p.main()')
        run = subprocess.run([sys.executable,'-c',code,str(Path(profile.__file__).parent),'--profile',profile.SELECTOR,
            '--rom',str(root/'rom.bin'),'--mapping',str(root/'functions.json'),'--index',str(root/'functions.txt'),
            '--data-mapping',str(root/'data_symbols.json'),'--readonly-named-buffer-policy',profile.text(named.named_policy()),
            '--readonly-second-named-buffer-policy',profile.text(profile.second_named_policy()),f'{A:08X}'],capture_output=True,text=True)
        (root/'cli-stdout.json').write_text(run.stdout);(root/'cli-stderr.txt').write_text(run.stderr)
        self.assertEqual(run.returncode,0,run.stderr);self.assertEqual(json.loads(run.stdout),result)

    def test_explicit_selector_and_distinct_exact_named_read_contracts(self):
        for selector in (None,True,profile.leaf.SELECTOR):
            with self.subTest(selector=selector),self.assertRaises(ValueError):self.native(selector=selector)
        expected = profile.second_named_policy()
        for policy in (None,{},True,named.named_policy(),dict(expected,readable=1),dict(expected,initialized=False),
                dict(expected,reads=[[32,2],[38,2]]),dict(expected,reads=[[36,4],[38,2]]),dict(expected,allow_globals=True)):
            with self.subTest(policy=policy),self.assertRaises(ValueError):self.native(readonly_second_named_buffer_policy=policy)
        with self.assertRaises(ValueError):self.native(readonly_named_buffer_policy=expected)
        for data in (b'{}',b'{"g_state_02007F40":"0x02007F42"}',bytearray(b'{}')):
            with self.subTest(data=str(data)),self.assertRaises(ValueError):self.native(data_mapping=data)

    def test_actual_helper_identity_literal_and_both_dual_indices(self):
        values = fixture()
        for address,offset in ((F,0),(S,0),(S,32)):
            rom = bytearray(values['rom']);rom[address-parent.match.ROM_BASE+offset] ^= 4
            with self.subTest(address=address,offset=offset),self.assertRaisesRegex(ValueError,'body identity'):
                self.native(rom=bytes(rom))
        for old,new in ((b'36 15 return',b'36 18 return'),(b'72 34 return',b'72 36 return')):
            with self.subTest(old=old),self.assertRaises(ValueError):self.native(index=values['index'].replace(old,new))

    def test_helper_raw_formal_named_width_offset_and_restored_return(self):
        for position,new in ((2,0x8C6C),(2,0x7CAC),(6,0x8008),(11,0x8011),(14,0x4708),(15,0x2001)):
            words = list(SECOND_WORDS);words[position] = new;values = fixture(second_words=words)
            altered = machine(words,S)+struct.pack('<I',named.GLOBAL)
            with self.subTest(position=position,new=new),patch.object(profile,'SECOND',(S,S+36,15,profile.sha(altered))),self.assertRaises(ValueError):
                profile.verify(**values)

    def test_complete_calls_mapping_runtime_and_manifest(self):
        values = fixture()
        for field in ('calls','bindings'):
            changed = dict(values[field]);changed.pop(min(changed))
            with self.subTest(field=field),self.assertRaises(ValueError):self.native(**{field:changed})
        with self.assertRaisesRegex(ValueError,'manifest differs'):self.native(manifest={'complete':True})
        for target in (0x081426B8,0x08142950,parent.thunks.ALIASES['_call_via_r4']):
            changed = dict(values['calls']);changed[min(changed)] = target
            with self.subTest(target=target),self.assertRaises(ValueError):
                profile.bind_calls(changed,values['mapping'],A,len(values['data']),len(values['rom']))
        sequence = list(CALLER);sequence[sequence.index('second')] = 'ordinary'
        with self.assertRaises(ValueError):self.native(sequence)

    def test_caller_zero_indices_outgoing_pointer_words_and_saved_overlap(self):
        for position,new in ((11,0x2101),(17,0x9402),(18,0x9502),(19,0xAB04),
                (26,0xAA00),(26,0xAA04),(26,0x1C0A),(27,0xAB02)):
            sequence = list(CALLER);sequence[position] = new
            with self.subTest(position=position,new=new),self.assertRaises(ValueError):self.native(sequence)

    def test_unmarked_alias_call_and_partial_pointer_word_write_taint(self):
        position = CALLER.index('second')
        with self.assertRaisesRegex(ValueError,'crossing calls'):
            self.native(CALLER[:position]+['ordinary']+CALLER[position:])
        with self.assertRaisesRegex(ValueError,'partial load from a local alias slot'):
            self.native(CALLER[:position]+[0x9402]+CALLER[position:])

    def test_exact_local_lifetimes_bounds_overlap_and_scalar_registers(self):
        proof = self.proof()._second;site = next(iter(proof.sites))
        stack = [('local',None)]*4+[('saved',None)]*4
        aliases = {ARM_REG_R2:frozenset(((-24,True),)),ARM_REG_R3:frozenset(((-22,True),))}
        self.assertEqual(proof.check_call(site,S,aliases,stack,{}),[(-24,2),(-22,2)])
        for value in (frozenset(((-24,False),)),frozenset(((-24,True),(-22,True))),frozenset(((-23,True),)),
                frozenset(((-22,True),)),frozenset(((-32,True),)),frozenset(((-16,True),))):
            changed = dict(aliases);changed[ARM_REG_R2] = value
            with self.subTest(value=value),self.assertRaises(ValueError):proof.check_call(site,S,changed,stack,{})

    def test_fresh_seals_exact_sites_children_and_forged_proof(self):
        values = fixture();proof = self.proof();proof._second._record['effects']['named_reads'] = []
        with self.assertRaises(ValueError):proof.validate_calls(values['calls'])
        proof = self.proof();proof.sites[max(proof.sites)+2] = proof.sites.pop(max(proof.sites))
        with self.assertRaises(ValueError):proof.validate_calls(values['calls'])
        ins,edges,calls,_ = parent.complete(values['data'],A,values['rom'],values['mapping'],values['index'])
        with self.assertRaisesRegex(ValueError,'exclusive fresh native'):
            parent.frame.prove_frame(ins,edges,A,{},calls,stack_aliases=True,local_alias_slot_policy=parent.slots.SELECTOR,
                zero_index_profile=parent.zero_index.SELECTOR,formal_stack_callee_proof={'complete':True,'writes':[[2,0,2],[3,0,2]]})

    def test_old_single_leaf_and_unmarked_default_refusals_remain(self):
        values = fixture();old = dict(values);old.pop('readonly_second_named_buffer_policy');old['selector'] = profile.leaf.SELECTOR
        with self.assertRaisesRegex(ValueError,'ordinary constant-offset memory access'):profile.leaf.verify(**old)
        ins,edges,calls,_ = parent.complete(values['data'],A,values['rom'],values['mapping'],values['index'])
        with self.assertRaisesRegex(ValueError,'crossing calls'):
            parent.frame.prove_frame(ins,edges,A,{},calls,stack_aliases=True,
                local_alias_slot_policy=parent.slots.SELECTOR,zero_index_profile=parent.zero_index.SELECTOR)


if __name__ == '__main__':unittest.main()
