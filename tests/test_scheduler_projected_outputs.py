"""Fresh raw/helper/caller composition tests; prior successful suites stay frozen."""
import hashlib
import json
from pathlib import Path
import struct
import subprocess
import sys
import unittest
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'tools'))
import match
import conditional_local_buffer_profile as local
import scheduler_projected_outputs_profile as profile
import test_formal_entry_word_halfword_effects as screen_fixture
from test_scheduler_predicates import half, bl, R0, LOCAL, SAVED

# A stand-in for the pinned scheduler that is a function: callers keep stack addresses in
# R4-R11 across it, and the callee-saved check walks it (kit #350). 29 x movs r0,r0; bx lr.
SCHEDULER_STUB = bytes(58) + b'\x70\x47'

A, P, N, T, W, C = (0x08001000, 0x08001200, 0x08001400,
                     0x08001600, 0x08001800, 0x08001A00)
STACK = [LOCAL]*13 + [SAVED]*4
F = profile.layout(STACK)


def decode(data, address):
    cs = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
    cs.detail = True
    instructions = {i.address:i for i in cs.disasm(data, address)}
    edges = {s: (() if i.mnemonic == 'bx' else (s+i.size,)) for s,i in instructions.items()}
    calls = {s:i.operands[0].imm for s,i in instructions.items() if i.mnemonic == 'bl'}
    return instructions, edges, calls


def pair_body(*, base=P, target=N):
    return half(0xB530, 0x1C0C, 0x1C15) + bl(base+6,target) + half(
        0x2106, 0x5641, 0x8021, 0x79C0, 0x0600, 0x1600, 0x8028,
        0xBC30, 0xBC01, 0x4700)


def pair_prove(data=None, *, base=P, child=b'\x70\x47', change_edges=None):
    data = pair_body(base=base) if data is None else data
    ins, edges, calls = decode(data,base)
    if change_edges:change_edges(edges)
    return profile.pair_origins(ins,edges,calls,base,data,N,child)


def table_body():
    return half(0x0600,0x0609,0x0E09,0x4B05,0x7A1A,0x434A,0x0052,
                0x6859,0x1889,0x0DC0,0x1809,0x7808,0x4770,0)+struct.pack('<I',profile.TABLE_POINT)


def table_prove(data=None, *, base=T, objects=None, change_partition=None):
    data = table_body() if data is None else data
    ins,edges,_ = decode(data[:26],base)
    partition=dict(code_bytes=26,alignment_bytes=2,literal_and_table_bytes=4,
        words=[dict(address=base+28,value=profile.TABLE_POINT,switch_word=False,load_sites=[base+6])])
    if change_partition:change_partition(partition)
    objects = json.dumps({profile.TABLE_NAME:f'0x{profile.TABLE_POINT:08X}'}).encode() if objects is None else objects
    return profile.table_origins(ins,edges,base,data,partition,objects)


def context():
    p=object.__new__(local.ConditionalLocalBufferProof)
    p.policy=profile.SELECTOR
    p.calls={10:profile.PAIR[0],20:profile.TABLE[0],30:profile.WORLD[0],
             40:profile.SCREEN[0],50:profile.SCHEDULER}
    p.environment,p.runtime_dependencies,p.observations={},[],{}
    origins=(((2,2),(3,3),(12,12)),((12,12),),((3,3),(12,12)),((3,8),(12,12)))
    p.projected_outputs={identity[0]:dict(structure=dict(effects=dict(return_entry_origins=list(rows))))
        for identity,rows in zip((profile.PAIR,profile.TABLE,profile.WORLD,profile.SCREEN),origins)}
    return p


def arguments(number):
    if number==0:return {R0+1:F['tile'][0],R0+2:F['tile'][1]},{}
    if number==1:return {R0+2:F['tile'][1]},{}
    if number==2:return {R0+3:F['world'][0]},{F['base']:F['world'][1],F['base']+4:F['world'][2]}
    if number==3:return {R0+3:F['screen'][0]},{F['base']:F['screen'][1],F['base']+4:F['world'][2]}
    return {R0+2:F['descriptor']},{F['base']:F['screen'][1],F['base']+4:F['world'][2]}


def invoke(p,number,**changes):
    aliases,slots=arguments(number)
    target=(profile.PAIR[0],profile.TABLE[0],profile.WORLD[0],profile.SCREEN[0],profile.SCHEDULER)[number]
    kwargs=dict(aliases=aliases,stack=list(STACK),slots=slots,site=10*(number+1))
    kwargs.update(changes)
    return p.check_call(target,**kwargs)


def raw_caller(*, corrupt_alias=False, missing_slot=False, highregs=False):
    data=half(0xB570)
    if highregs:data+=half(0x4656,0x464D,0x4644,0xB470)
    data+=half(0xB08D)
    if highregs:data+=half(0x2001,0x4680)
    data+=half(0xAC09,0x466D,0x3526,0x2000,0x1C21,0x1C2A)
    calls={}
    def call(target):
        nonlocal data
        site=A+len(data);calls[site]=target;data+=bl(site,target)
    call(P)
    if corrupt_alias:data+=half(0x32FF,0x8010)
    data+=half(0x7820,0x7829)
    call(T)
    data+=half(0x1C01,0x2200,0x5EA0,0x2300,0x5EEA,0xAD0A,0x466E,
               0x362A,0x9600,0xAC0B,0x9401,0x1C2B)
    call(W)
    data+=half(0x2100,0x5E68,0x2200,0x5EB1,0x2300,0x5EE2,
               0x466C,0x342E,0xAD0C,0x9500,0x1C23)
    call(C)
    data+=half(0xA902,0x8820,0x8288,0x8828,0x82C8,0x2000,0x211C,0xAA02,0x2300)
    if missing_slot:data+=half(0x9301)
    call(profile.SCHEDULER)
    data+=half(0xB00D)
    if highregs:data+=half(0xBC38,0x4698,0x46A1,0x46AA)
    data+=half(0xBC70,0xBC02,0x4708)
    return data,calls


class ProjectedKernelTests(unittest.TestCase):
    def test_pair_complete_noop_and_ordered_effects_keep_R2_R3_R12(self):
        result=pair_prove()
        self.assertEqual(result['return_entry_origins'],[[2,2],[3,3],[12,12]])
        self.assertEqual([(e['kind'],e['formal'],e['offset'],e['bytes']) for e in result['ordered_effects']],
                         [('read',0,6,1),('write',1,0,2),('read',0,7,1),('write',2,0,2)])

    def test_pair_relocated_generic_body(self):
        result=pair_prove(base=P+64)
        self.assertEqual(result['ordered_effects'][0]['site'],P+64+12)

    def test_pair_actual_noop_must_not_be_opaque_or_mutating(self):
        for child in (b'',half(0x2000,0x4770),half(0x4710)):
            with self.subTest(child=child),self.assertRaises(ValueError):pair_prove(child=child)

    def test_pair_control_frame_and_wrong_target_refuse(self):
        for at,word in ((6,0xF001),(24,0xBC10),(28,0x4710)):
            data=bytearray(pair_body());struct.pack_into('<H',data,at,word)
            with self.subTest(at=at),self.assertRaises(ValueError):pair_prove(bytes(data))

    def test_pair_pointer_store_and_extra_output_refuse(self):
        for word in (0x8022,0x8061):
            data=bytearray(pair_body());struct.pack_into('<H',data,14,word)
            with self.subTest(word=word),self.assertRaises(ValueError):pair_prove(bytes(data))

    def test_pair_partial_cfg_trailing_bytes_and_early_exit_refuse(self):
        with self.assertRaises(ValueError):pair_prove(pair_body()+half(0))
        with self.assertRaises(ValueError):pair_prove(change_edges=lambda e:e.update({P:()}))

    def test_valid_mapping_mutations_reach_specific_table_guards(self):
        for at,word in ((8,0x1C12),(22,0x7008),(10,0x400A),(24,0x4700)):
            data=bytearray(table_body());struct.pack_into('<H',data,at,word)
            with self.subTest(at=at),self.assertRaisesRegex(ValueError,'operation or register'):
                table_prove(bytes(data))
        with self.assertRaisesRegex(ValueError,'partition'):
            table_prove(change_partition=lambda p:p.update(alignment_bytes=0))
        objects=json.dumps({profile.TABLE_NAME:f'0x{profile.TABLE_POINT:08X}',
                            'alias':f'0x{profile.TABLE_POINT:08X}'}).encode()
        with self.assertRaisesRegex(ValueError,'unique existing canonical'):
            table_prove(objects=objects)

    def test_table_incoming_R2_R3_are_not_observed(self):
        result=table_prove()
        self.assertEqual(result['incoming_general_reads'],[0,1])
        self.assertEqual(result['overwritten_before_observation'],[2,3])
        self.assertEqual(result['return_entry_origins'],[[12,12]])
        self.assertFalse(result['table_extent_proved'])

    def test_table_relocated_literal_stays_generic(self):
        self.assertEqual(table_prove(base=T+256)['writes'],[])

    def test_table_read_before_overwrite_mutation_refused(self):
        data=bytearray(table_body());struct.pack_into('<H',data,8,0x1C12)
        with self.assertRaises(ValueError):table_prove(bytes(data))

    def test_table_writes_and_unknown_operations_refused(self):
        for at,word in ((22,0x7008),(10,0x400A),(24,0x4700)):
            data=bytearray(table_body());struct.pack_into('<H',data,at,word)
            with self.subTest(at=at),self.assertRaises(ValueError):table_prove(bytes(data))

    def test_table_requires_canonical_identity_and_exact_literal_partition(self):
        for objects in (b'{}',json.dumps({'alias':f'0x{profile.TABLE_POINT:08X}'}).encode(),
                        json.dumps({profile.TABLE_NAME:f'0x{profile.TABLE_POINT:08X}','alias':f'0x{profile.TABLE_POINT:08X}'}).encode()):
            with self.subTest(objects=objects),self.assertRaises(ValueError):table_prove(objects=objects)
        with self.assertRaises(ValueError):table_prove(change_partition=lambda p:p.update(alignment_bytes=0))

    def test_table_full_data_and_alignment_are_authenticated(self):
        for at in (26,28):
            data=bytearray(table_body());data[at]^=1
            with self.subTest(at=at),self.assertRaises(ValueError):table_prove(bytes(data))

    def test_call_sequence_and_cycles_are_not_assumed(self):
        calls={n*2:t for n,t in enumerate((profile.PAIR[0],profile.TABLE[0],profile.WORLD[0],profile.SCREEN[0],profile.SCHEDULER))}
        edges={n*2:(() if n==4 else (n*2+2,)) for n in range(5)}
        profile.phases(edges,calls)
        for changed in (dict(calls,**{}),):
            changed[0]=profile.SCHEDULER
            with self.assertRaises(ValueError):profile.phases(edges,changed)
        with self.assertRaises(ValueError):profile.phases(dict(edges,**{})|{8:(0,)},calls)


class ProjectedCallTests(unittest.TestCase):
    def test_exact_return_aliases_and_persistent_pointer_slots(self):
        p=context()
        self.assertEqual(invoke(p,0),{R0+2:F['tile'][1]})
        self.assertEqual(invoke(p,1),{})
        self.assertEqual(invoke(p,2),{R0+3:F['world'][0]})
        self.assertEqual(invoke(p,3),{})
        self.assertEqual(invoke(p,4),{})
        self.assertEqual(p.observations[40]['pointer_words'],p.observations[50]['pointer_words'])
        self.assertTrue(all(o['pointer_words_preserved'] for o in p.observations.values()))

    def test_screen_returns_actual_entry_R8_alias(self):
        aliases,slots=arguments(3);aliases[R0+8]=F['tile'][0]
        self.assertEqual(invoke(context(),3,aliases=aliases),{R0+3:F['tile'][0]})

    def test_pair_and_table_preserve_untouched_R12_alias(self):
        for number in (0,1):
            aliases,_=arguments(number);aliases[R0+12]=F['world'][0]
            with self.subTest(number=number):
                self.assertEqual(invoke(context(),number,aliases=aliases)[R0+12],F['world'][0])

    def test_scalar_input_aliases_refused(self):
        for number,registers in ((0,(0,)),(1,(0,1)),(2,(0,1,2)),(3,(0,1,2)),(4,(0,1,3,12))):
            for register in registers:
                aliases,_=arguments(number);aliases[R0+register]=F['tile'][0]
                with self.subTest(number=number,register=register),self.assertRaises(ValueError):
                    invoke(context(),number,aliases=aliases)

    def test_missing_stale_or_extra_pointer_slots_refused(self):
        for number in (2,3,4):
            _,valid=arguments(number)
            for slots in ({}, {F['base']:valid[F['base']]},valid|{F['base']+8:F['tile'][0]}):
                with self.subTest(number=number,slots=slots),self.assertRaises(ValueError):
                    invoke(context(),number,slots=slots)

    def test_output_swaps_and_halfword_misalignment_refused(self):
        for number in (0,2,3):
            aliases,_=arguments(number)
            reg=R0+1 if number==0 else R0+3
            aliases[reg]+=1
            with self.subTest(number=number),self.assertRaises(ValueError):invoke(context(),number,aliases=aliases)

    def test_preserved_aliases_cannot_point_outside_private_frame(self):
        for offset in (F['base']-2,F['end'],0):
            aliases,_=arguments(4);aliases[R0+4]=offset
            with self.subTest(offset=offset),self.assertRaises(ValueError):invoke(context(),4,aliases=aliases)

    def test_frame_holes_saved_words_and_unbounded_frames_refused(self):
        for stack in ([LOCAL]*12+[SAVED]*4,[LOCAL]*14+[SAVED]*4,
                      [LOCAL]*4+[SAVED]+[LOCAL]*8+[SAVED]*3,
                      [(True,False,True)]+[LOCAL]*12+[SAVED]*4):
            with self.subTest(stack=stack),self.assertRaises(ValueError):invoke(context(),4,stack=stack)

    def test_word_provenance_wrong_sites_and_control_alias_refused(self):
        with self.assertRaises(ValueError):invoke(context(),4,words={F['base']:('opaque',)})
        with self.assertRaises(ValueError):invoke(context(),4,site=10)
        aliases,_=arguments(4);aliases[match.ARM_REG_LR]=F['tile'][0]
        with self.assertRaises(ValueError):invoke(context(),4,aliases=aliases)

    def test_missing_observation_and_changed_call_state_refused(self):
        p=context()
        with self.assertRaises(ValueError):p.contract_manifest()
        invoke(p,1);aliases,_=arguments(1);aliases[R0+4]=F['tile'][0]
        with self.assertRaises(ValueError):invoke(p,1,aliases=aliases)

    def test_manifest_keeps_all_physical_access_and_lifetime_premises(self):
        p=context()
        for n in range(5):invoke(p,n)
        result=p.contract_manifest();text=' '.join(result['assumptions'])
        for phrase in ('two retained outgoing pointer words','separate from all caller stack words',
                       'ambient original R9','not inferred','initialized and readable'):
            self.assertIn(phrase,text)
        for name in ('actual_callback_effects_proved','nonescape_proved','physical_memory_claim','termination_proved'):
            self.assertFalse(result[name])

    def test_old_scheduler_policy_keeps_additional_pointer_refusal(self):
        p=context();p.policy=local.SCHEDULER
        with self.assertRaisesRegex(ValueError,'pointer-word'):invoke(p,4)

    def test_native_and_report_selector_registration(self):
        self.assertTrue(match._ordinary_call_replay(context(),profile.TABLE[0]))
        self.assertEqual(profile.owner.selector_for_report('* verification: `'+profile.SCHEMA+'`'),profile.SELECTOR)
        run=subprocess.run([sys.executable,'-B',str(Path(match.__file__)),
            '--owner-runtime-profile',profile.SELECTOR,'--help'],capture_output=True,text=True)
        self.assertEqual(run.returncode,0,run.stderr)


class ProjectedFullFrameTests(unittest.TestCase):
    setUp=screen_fixture.FormalEntryWordEffectsTests.setUp

    def bound(self,*,corrupt_alias=False,missing_slot=False,bad_helper=False,highregs=False):
        fixture=screen_fixture.FormalEntryWordEffectsTests.fixture(self)
        caller,calls=raw_caller(corrupt_alias=corrupt_alias,missing_slot=missing_slot,highregs=highregs)
        world=half(0xB530,0x9C03,0x9D04,0x0400,0x12C0,0x3004,0x8018,
                   0x0109,0x8021,0x0412,0x12D2,0x3208,0x802A,0xBC30,0xBC01,0x4700)
        bodies={A:caller,P:pair_body(),N:half(0x4770),T:table_body(),W:world,C:fixture['data'],
                profile.SCHEDULER: SCHEDULER_STUB,0x08005954:bytes(206)}
        identities={name:(a,len(bodies[a]),count,hashlib.sha256(bodies[a]).hexdigest())
            for name,a,count in [('PAIR',P,14),('NOOP',N,1),('TABLE',T,13),('WORLD',W,16),('SCREEN',C,51)]}
        if bad_helper:bodies[P]=half(0xB510)+bodies[P][2:]
        rows=[];lines=[];rom=bytearray(max(a+len(b) for a,b in bodies.items())-match.ROM_BASE)
        for a,b in sorted(bodies.items()):
            rom[a-match.ROM_BASE:a-match.ROM_BASE+len(b)]=b
            rows.append(dict(rom=f'0x{a:08X}',end=f'0x{a+len(b):08X}',mode='thumb',instrs=0))
            lines.append(f'{a:08X} {a+len(b):08X} {len(b)} 0 return\n')
        objects=json.dumps({profile.TABLE_NAME:f'0x{profile.TABLE_POINT:08X}',profile.direct.NAME:f'0x{profile.direct.GLOBAL:08X}'}).encode()
        p=local.ConditionalLocalBufferProof(bytes(rom),json.dumps(rows).encode(),''.join(lines).encode(),objects,policy=profile.SELECTOR)
        original_span=p.span
        p.span=lambda a:half(0x4710) if a in match.function_thunk.ALIASES.values() else original_span(a)
        pins={a:(len(b),hashlib.sha256(b).hexdigest()) for a,b in bodies.items() if a in (profile.SCHEDULER,0x08005954)}
        with mock.patch.multiple(profile,**identities),mock.patch.dict(local.DEPENDENCIES,pins), \
                mock.patch.object(local.thunk,'dependencies',return_value=[]):
            p.bind_root(caller,A,calls)
            match.verify_leaf_instructions(caller,A,True,calls,buffer_proof=p)
            manifest=p.contract_manifest()
        return p,manifest

    def test_complete_synthetic_helpers_and_actual_caller_alias_transport(self):
        p,result=self.bound()
        self.assertEqual(len(p.observations),5)
        table=next(o for o in p.observations.values() if o['target']==T)
        self.assertIn((R0+2,F['tile'][1]),table['aliases'])
        scheduler=next(o for o in p.observations.values() if o['target']==profile.SCHEDULER)
        self.assertEqual(scheduler['pointer_words'],sorted(arguments(4)[1].items()))
        self.assertEqual(len(result['helpers']),5)

    def test_complete_high_register_frame_with_scalar_R8_variant(self):
        p,result=self.bound(highregs=True)
        scheduler=next(o for o in p.observations.values() if o['target']==profile.SCHEDULER)
        self.assertEqual(scheduler['frame']['base'],-80)
        self.assertEqual(scheduler['frame']['end'],-28)
        self.assertEqual(scheduler['pointer_words'],[(-80,-32),(-76,-36)])
        self.assertFalse(result['physical_memory_claim'])

    def test_retained_R2_alias_cannot_escape_after_pair_return(self):
        with self.assertRaisesRegex(ValueError,'arithmetic leaves'):
            self.bound(corrupt_alias=True)

    def test_live_second_slot_cannot_be_silently_erased(self):
        with self.assertRaisesRegex(ValueError,'both retained outgoing'):
            self.bound(missing_slot=True)

    def test_indexed_helper_identity_is_not_an_address_whitelist(self):
        with self.assertRaisesRegex(ValueError,'immutable helper'):
            self.bound(bad_helper=True)


if __name__=='__main__':
    unittest.main(verbosity=2)
