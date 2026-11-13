"""Synthetic typed-literal callback closures, pinned state callback and routing."""
import copy
import json
from pathlib import Path
import struct
import sys
import unittest
from unittest.mock import patch
sys.dont_write_bytecode=True
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import match
import owner_admission_profile as owner
import named_data_buffer_profile as named
import function_thunk_profile as thunk
import owner_graph_profile as graph
import two_word_callback_closure_profile as previous
import literal_callback_closure_profile as closure

A,C,G,X=0x08001000,0x08003000,0x08004000,0x08005000
W,S=0x080C7CC0,0x0809AC20
T1,T2,F,FG=0x080C7D18,0x080C7D70,0x0809AC00,0x080C7B78
# Genuine tree-iterator bodies; their BL words reach the canonical R7 thunk.
TREE={T1:'f0b50f1c161c846801225242251c002c1ed0e168002907d0914205d02069904211d0221c0c1cf2e7206990420bd0201c311c7af089fa00280ad02069002802d0221c041ce3e7ac4202d0221ca468dee7f0bc01bc0047',
      T2:'f0b50f1c161c846801225242251c002c1ed02169002907d0914205d0e068904211d0221c0c1cf2e7e06890420bd0201c311c7af05dfa00280ad0e068002802d0221c041ce3e7ac4202d0221ca468dee7f0bc01bc0047'}
K=0x08006800  # trailing callee: movs r2,#0; bx lr
ROOTS={  # form: (owner-load halfword, callback)
    'private-state':(0x6900,S),'entry-object':(0x6910,X),'null':(0x6900,X),
    'entry-byte':(0x6900,X),'owner-word-trailing-call':(0x6920,X)}


def tree_graph(body,address=T1,count=42):
    rows=[dict(rom=f'0x{address:08X}',end=f'0x{address+len(body):08X}',mode='thumb',instrs=count)]+[
          dict(rom=f'0x{t:08X}',end=f'0x{t+2:08X}',mode='thumb',instrs=1) for t in thunk.ALIASES.values()]
    ins,edges,_,calls,_=graph.graph(body,address,owner.refine(body,address,json.dumps(rows).encode()))
    return ins,edges,calls


def bl(site,target):
    delta=target-site-4
    return struct.pack('<HH',0xF000|((delta>>12)&0x7FF),0xF800|((delta>>1)&0x7FF))


def root(form,callback,iterator=W,adapter=C):
    shape=closure.FORMS[form];code=shape['code']
    load=ROOTS[form][0]
    body=bytearray(bytes.fromhex(code.replace('xx','00')))
    struct.pack_into('<H',body,shape['owner'],load)
    body[shape['call']:shape['call']+4]=bl(A+shape['call'],iterator)
    if 'trailing' in shape:
        struct.pack_into('<H',body,shape['trailing']['reload'],load)
        body[shape['trailing']['call']:shape['trailing']['call']+4]=bl(A+shape['trailing']['call'],K)
    return bytes(body)+struct.pack('<II',callback+1,adapter+1)


def fixture(form='private-state',changes=None,callback=None,iterator=W,framed=False,extra=None):
    callback=ROOTS[form][1] if callback is None else callback
    worker=bytes.fromhex('70b50e1c151c446800e0a468002c05d0201c291c')+bl(W+20,thunk.ALIASES['_call_via_r6'])+bytes.fromhex('0028f6d170bc01bc0047')
    adapter=bytes.fromhex('10b50c1c')+bl(C+4,G)+bytes.fromhex('21686268')+bl(C+12,thunk.ALIASES['_call_via_r2'])+bytes.fromhex('10bc02bc0847')
    used=F if framed else C
    bodies={A:root(form,callback,iterator,used),W:worker,G:bytes.fromhex('00687047'),
            S:bytes.fromhex(closure.STATE_CALLBACKS[S][1]),X:bytes.fromhex('01207047')}
    counts={A:closure.FORMS[form]['count'],W:16,G:2,S:8,X:2}
    if 'trailing' in closure.FORMS[form]:
        bodies[K]=bytes.fromhex('00227047');counts[K]=2
    if framed:
        bodies[F]=bytes.fromhex(closure.FRAMED_ADAPTERS[F]['body']);counts[F]=14
        bodies[FG]=bytes.fromhex(closure.FRAMED_ADAPTERS[F]['getter_body']);counts[FG]=5
    else:
        bodies[C]=adapter;counts[C]=9
    if iterator in TREE:
        bodies[iterator]=bytes.fromhex(TREE[iterator]);counts[iterator]=42
    for target,(body,count) in (extra or {}).items():
        bodies[target]=body;counts[target]=count
    rom=bytearray(thunk.END-match.ROM_BASE)
    for number,target in enumerate(thunk.ALIASES.values()):
        struct.pack_into('<HH',rom,target-match.ROM_BASE,0x4700+(number<<3),0x46C0)
    for target in (thunk.ALIASES['_call_via_r6'],thunk.ALIASES['_call_via_r7'],thunk.ALIASES['_call_via_r2']):
        bodies[target]=bytes(rom[target-match.ROM_BASE:target-match.ROM_BASE+2]);counts[target]=1
    for (target,offset),value in (changes or {}).items():
        code=bytearray(bodies[target]);struct.pack_into('<H',code,offset,value);bodies[target]=bytes(code)
    rows=[]
    for target,body in bodies.items():
        rom[target-match.ROM_BASE:target-match.ROM_BASE+len(body)]=body
        rows.append(dict(rom=f'0x{target:08X}',end=f'0x{target+len(body):08X}',mode='thumb',instrs=counts[target]))
    index=''.join(f'{int(row["rom"],16):08X} {int(row["end"],16):08X} {int(row["end"],16)-int(row["rom"],16)} {row["instrs"]} return\n'for row in rows).encode()
    shape=closure.FORMS[form]
    return dict(data=bodies[A],address=A,rom=bytes(rom),mapping=json.dumps(rows).encode(),index=index,objects=b'{}',selector=closure.SELECTOR,
        bindings=dict(calls=[[shape['call'],f'func_{iterator:08X}']]+(
                          [[shape['trailing']['call'],f'func_{K:08X}']] if 'trailing' in shape else []),data=[],
                      functions=[[shape['callback'],f'func_{callback:08X}'],[shape['adapter'],f'func_{used:08X}']],switches=[]))


class LiteralClosureTests(unittest.TestCase):
    def test_private_state_callback_effects_and_result(self):
        manifest,ins=owner.verify(**fixture())
        self.assertEqual(manifest['profile'],closure.SCHEMA);self.assertEqual(len(ins),17)
        proof=manifest['proof']['literal_callback_closure']
        self.assertEqual(proof['form'],'private-state')
        self.assertEqual(proof['private_state']['offset'],-20)
        self.assertEqual(proof['private_state']['result'],dict(site=A+28,offset=0,width=4,register=0,
            relation='zero plus one per returning callback invocation, modulo 2**32'))
        effects=proof['callback']
        self.assertEqual([row[1] for row in effects['state_reads']],[4,0])
        self.assertEqual([row[1] for row in effects['state_writes']],[0,4])
        self.assertEqual([row[1:] for row in effects['external_writes']],[['state word 4 on entry',0,4,'object']])
        self.assertTrue(effects['private_provenance_passed'])
        self.assertEqual(proof['root_descriptor']['actual_buffer_checks'][0]['pointer_slots'],[[-12,-20]])
        conditions=' '.join(proof['explicit_conditions'])
        self.assertNotIn('Loaded input words carry no tracked private-frame',conditions)
        self.assertIn('not asserted satisfied',conditions)
        for key in ('physical_memory_permission','numeric_nonalias_proved','actual_callback_ABI_established','termination_proved'):
            self.assertIs(proof[key],False)
        self.assertFalse(proof['iterator']['iteration_bound_assumed'])

    def test_opaque_forms_keep_existing_premises(self):
        for form in ('entry-object','null'):
            with self.subTest(form=form):
                manifest,ins=owner.verify(**fixture(form))
                proof=manifest['proof']['literal_callback_closure']
                self.assertEqual(proof['form'],form);self.assertIsNone(proof['private_state'])
                self.assertEqual(proof['callback']['effects'],'opaque')
                self.assertFalse(proof['callback']['private_provenance_passed'])
                self.assertIn('Loaded input words carry no tracked private-frame or saved-return provenance; ordinary memory noninterference remains a premise.',
                              proof['explicit_conditions'])
                self.assertEqual(proof['root_descriptor']['actual_buffer_checks'][0]['pointer_slots'],[])

    def test_native_report_selector_and_replay(self):
        values=fixture();manifest,ins=owner.verify(**values)
        result=(values['data'],manifest,'a'*64,values['mapping'],values['index'],values['objects'],values['rom'],len(ins),b'synthetic-original-ELF')
        report=owner.render(A,result)
        self.assertTrue(owner.selected(report))
        self.assertEqual(owner.selector_for_report(report),closure.SELECTOR)
        self.assertIn('* owner runtime: '+closure.SELECTOR,report)
        self.assertIn('* control flow: '+closure.CONTROL_FLOW,report)

    def test_tampered_manifest_refuses(self):
        values=fixture();report,_=owner.verify(**values)
        for path in (('private_state','result','relation'),('callback','private_provenance_passed'),('termination_proved',)):
            changed=copy.deepcopy(report);target=changed['proof']['literal_callback_closure']
            for key in path[:-1]:target=target[key]
            target[path[-1]]='zero' if path[-1]=='relation' else not target[path[-1]]
            with self.subTest(path=path),self.assertRaisesRegex(ValueError,'manifest differs'):
                owner.verify(**values,manifest=changed)

    def test_existing_and_default_selectors_do_not_gain_permission(self):
        for form in closure.FORMS:
            for selector in (owner.SELECTOR,previous.SELECTOR,named.TREE_CALLBACK_SELECTOR,named.DATAFREE_SELECTOR):
                values=fixture(form);values['selector']=selector
                with self.subTest(form=form,selector=selector),self.assertRaises(ValueError):owner.verify(**values)

    def test_existing_28_byte_root_is_not_a_literal_form(self):
        data=bytes.fromhex('00b582b000920191006903496a46')+bl(A+14,W)+bytes.fromhex('02b001bc0047')+struct.pack('<I',C+1)
        with self.assertRaisesRegex(ValueError,'natural root form'):closure.form_of(data)

    def test_templates_match_independent_genuine_roots(self):
        genuine={'private-state':'00b584b000220092019106496a46029202aa5160006904492df0e4ff009804b002bc084721ac0908e9ab0908',
                 'entry-object':'00b582b0011c80310a68054900900191106904496a462ef02ff902b001bc00476dad0908e9ab0908',
                 'null':'00b582b0054a002100910192006904496a462df0dffa02b001bc0047b5ac0908e9ab0908',
                 'entry-byte':'00b582b00906090e054a00910192006904496a462df0f2fa02b001bc00470000e5ac0908e9ab0908',
                 'owner-word-trailing-call':'10b582b0041c074920690090019106496a462df049fe20692df00afe02b010bc01bc00476dac0908e9ab0908'}
        for form,raw in genuine.items():
            with self.subTest(form=form):self.assertEqual(closure.form_of(bytes.fromhex(raw)),form)

    def test_entry_byte_form(self):
        manifest,ins=owner.verify(**fixture('entry-byte'))
        self.assertEqual(len(ins),14)
        proof=manifest['proof']['literal_callback_closure']
        self.assertEqual(proof['form'],'entry-byte')
        self.assertEqual(manifest['proof']['partition']['alignment_bytes'],2)
        self.assertEqual(proof['root_descriptor']['initialized_words'][0],
                         dict(offset=-12,source='root entry R1 narrowed to its low 8 bits (u8)'))
        self.assertEqual(proof['callback']['arguments'][1],'root entry R1 narrowed to its low 8 bits (u8)')
        self.assertNotIn('trailing_call',proof)
        self.assertEqual(proof['external_read_obligations'][0],dict(base='root entry R0',offset=16,width=4))

    def test_owner_word_trailing_call_form(self):
        manifest,ins=owner.verify(**fixture('owner-word-trailing-call'))
        self.assertEqual(len(ins),16)
        self.assertEqual(manifest['proof']['calls'],[[18,f'func_{W:08X}'],[24,f'func_{K:08X}']])
        proof=manifest['proof']['literal_callback_closure']
        self.assertEqual(proof['root_frame']['saved'],['entry R4','entry LR'])
        self.assertEqual(proof['root_descriptor']['offset'],-16)
        self.assertEqual(proof['root_descriptor']['initialized_words'][0]['source'],
                         'owner word loaded from root entry R0 (the iterator list argument)')
        trailing=proof['trailing_call']
        self.assertEqual((trailing['site'],trailing['target'],trailing['entry_r2_overwritten_at']),(A+24,K,K))
        self.assertEqual(trailing['arguments'],[dict(register=0,source='owner word reloaded from root entry R0',offset=16,site=A+22)])
        self.assertFalse(trailing['descriptor_alias_passed']);self.assertEqual(trailing['effects'],'opaque')
        self.assertEqual(proof['outward_expired_aliases'],[])
        self.assertEqual(proof['live_aliases_to_trailing_callee'],[dict(register=2,origin='root descriptor on the empty-list path',
                                                                        observed_by_trailing_callee=False,overwritten_at=K)])
        self.assertIn('optional pinned opaque trailing call',closure.CONTROL_FLOW)
        self.assertEqual(proof['external_read_obligations'][-1],
                         dict(base='root entry R0, reloaded after the iterator returns',offset=16,width=4))
        self.assertIn('provably overwrites entry R2 before reading it',' '.join(proof['explicit_conditions']))

    def test_new_forms_refuse_wrong_narrowing_and_untrusted_words(self):
        # asrs/lsrs #16 narrowing, a word load in place of the narrowing, an extra
        # store into the frame, a stored R0 copy, and the R4 owner copy from R1.
        for form,offset,value in (('entry-byte',6,0x1609),('entry-byte',6,0x0C09),('entry-byte',4,0x6809),
                                  ('entry-byte',10,0x9102),('entry-byte',30,0x9102),
                                  ('owner-word-trailing-call',10,0x9102),('owner-word-trailing-call',4,0x1C0C)):
            with self.subTest(form=form,offset=offset),self.assertRaisesRegex(ValueError,'natural root form'):
                owner.verify(**fixture(form,changes={(A,offset):value}))
        # Owner word through untrusted R1/R2 instead of the entry-R0 copy.
        for form,offset,value in (('entry-byte',14,0x6908),('entry-byte',14,0x6910),
                                  ('owner-word-trailing-call',8,0x6908),('owner-word-trailing-call',8,0x6900)):
            with self.subTest(form=form,offset=offset),self.assertRaisesRegex(ValueError,'aligned incoming object word load'):
                owner.verify(**fixture(form,changes={(A,offset):value,(A,22):value} if 'trailing' in form else {(A,offset):value}))

    def test_trailing_reload_must_be_the_same_owner_word(self):
        # A different offset, a store of the stale descriptor alias and a read through R2.
        for value in (0x6960,0x6122,0x6810):
            with self.subTest(value=hex(value)),self.assertRaisesRegex(ValueError,'same owner word reload'):
                owner.verify(**fixture('owner-word-trailing-call',changes={(A,22):value}))

    def test_trailing_callee_must_not_observe_the_descriptor(self):
        def killed(body):
            raw=bytes.fromhex(body);rom=bytearray(K+len(raw)-match.ROM_BASE);rom[K-match.ROM_BASE:]=raw
            return closure.entry_r2_killed(bytes(rom),K,K+len(raw))
        # ldr r0,[r2]; push {r2}; a call; a conditional branch; return; a loop on itself; run off the end.
        for body,error in (('10687047','may observe'),('04b47047','may observe'),
                           (bl(K,G).hex()+'0022','may observe'),('00d00022','may observe'),
                           ('70470022','may observe'),('fee70022','overwrite R2 on its entry path'),('00207047','may observe'),
                           ('0020','may observe')):
            with self.subTest(body=body),self.assertRaisesRegex(ValueError,error):killed(body)
        # Not ARMv4T Thumb: IT, NOP hint, UXTH, BKPT, CPSID, UDF, low-low hi-format MOVs.
        for body in ('08bf0022','00bf0022','80b20022','00be0022','72b60022','00de0022','0246','0a46'):
            with self.subTest(body=body),self.assertRaisesRegex(ValueError,'may observe entry R2'):killed(body)
        # The callee's entry SP is the descriptor: SP-derived overwrites at or above it,
        # loads through SP, values loaded after an SP value was stored, and SP moves.
        for body,error in (('6a46','at or above its entry SP'),('00aa','at or above its entry SP'),
                           ('82b002aa','at or above its entry SP'),('009a','at or above its entry SP'),
                           ('04bc','moves SP'),('81b00098021c','at or above its entry SP'),
                           ('684608600a68','at or above its entry SP'),('8546','moves SP')):
            with self.subTest(body=body),self.assertRaisesRegex(ValueError,error):killed(body)
        # An unconditional branch is followed (over R2 reads that would refuse); the write may come after harmless work.
        self.assertEqual(killed('00e0c0461f2201207047'),K+4)
        self.assertEqual(killed('0020009001e0106810680022'),K+10)
        # SP-derived overwrites strictly below entry SP are the callee's own frame (080C7C48's shape).
        self.assertEqual(killed('f0b581b06a46'),K+4)
        self.assertEqual(killed('f0b581b005aa'),K+4)
        with self.assertRaisesRegex(ValueError,'at or above'):killed('f0b581b006aa')
        values=fixture('owner-word-trailing-call',changes={(K,0):0x6810})
        with self.assertRaisesRegex(ValueError,'may observe entry R2'):owner.verify(**values)

    def test_trailing_call_binding_and_context(self):
        values=fixture('owner-word-trailing-call');values['bindings']['calls'].pop()
        with self.assertRaisesRegex(ValueError,'exact typed callback and adapter bindings'):owner.verify(**values)
        context=closure._LiteralContextRead(b'',b'[]',A+18,W,'owner-word-trailing-call')
        context.trailing_site,context.trailing_target=A+24,K
        stack=[(False,False,True)]*4
        self.assertEqual(context.check_call(K,{},stack,site=A+24),{})
        with self.assertRaisesRegex(ValueError,'carries the descriptor'):
            context.check_call(K,{match.ARM_REG_R0+2:-16},stack,site=A+24)
        with self.assertRaisesRegex(ValueError,'carries the descriptor'):
            context.check_call(K,{},stack,{-16:-16},site=A+24)
        with self.assertRaisesRegex(ValueError,'complete initialized root context'):
            context.check_call(G,{},stack,site=A+24)

    def test_callback_must_be_a_mapped_function_literal(self):
        for form in ('entry-byte','owner-word-trailing-call'):
            shape=closure.FORMS[form]
            for value in (0x08007001,X,0x02000001):
                values=fixture(form);body=bytearray(values['data']);struct.pack_into('<I',body,shape['callback'],value)
                values['data']=bytes(body);rom=bytearray(values['rom']);rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)]=body
                values['rom']=bytes(rom);values['bindings']['functions'][0][1]=f'func_{value&~1:08X}'
                with self.subTest(form=form,value=hex(value)),self.assertRaises(ValueError):owner.verify(**values)

    def test_tampered_trailing_record_refuses(self):
        values=fixture('owner-word-trailing-call');report,_=owner.verify(**values)
        for key,value in (('entry_r2_overwritten_at',K+2),('descriptor_alias_passed',True),('target',G)):
            changed=copy.deepcopy(report);changed['proof']['literal_callback_closure']['trailing_call'][key]=value
            with self.subTest(key=key),self.assertRaisesRegex(ValueError,'manifest differs'):
                owner.verify(**values,manifest=changed)

    def test_call_to_other_iterator_refuses(self):
        values=fixture();body=bytearray(values['data']);body[24:28]=bl(A+24,G)
        values['data']=bytes(body);rom=bytearray(values['rom']);rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)]=body
        values['rom']=bytes(rom);values['bindings']['calls']=[[24,f'func_{G:08X}']]
        with self.assertRaisesRegex(ValueError,'exact iterator call'):closure.prove(**{k:v for k,v in values.items() if k not in ('objects','bindings')})

    def test_callback_cannot_be_another_dependency(self):
        for target in (C,G,W):
            with self.subTest(target=hex(target)),self.assertRaisesRegex(ValueError,'distinct complete dependency owners'):
                owner.verify(**fixture('null',callback=target))

    def test_wrong_root_bytes_refuse(self):
        # Initializing stores, descriptor address, result read-back and frame size.
        for offset,value in ((6,0x46C0),(14,0x9201),(16,0xAA01),(28,0x9801),(2,0xB083),(30,0xB003)):
            with self.subTest(offset=offset),self.assertRaisesRegex(ValueError,'natural root form'):
                owner.verify(**fixture(changes={(A,offset):value}))

    def test_owner_load_must_be_aligned_word_from_entry_object(self):
        for value in (0x6901,0x6908,0x8A00,0x5800):
            with self.subTest(value=hex(value)),self.assertRaisesRegex(ValueError,'aligned incoming object word load'):
                owner.verify(**fixture(changes={(A,20):value}))

    def test_state_callback_body_changes_refuse(self):
        # Wrong state offset, store of the state address, extra state word,
        # wrong increment and wrong return value.
        for offset,value in ((0,0x688A),(4,0x6809),(6,0x3002),(8,0x6088),(12,0x2000)):
            with self.subTest(offset=offset),self.assertRaises(ValueError):
                owner.verify(**fixture(changes={(S,offset):value}))
        raw=bytearray.fromhex(closure.STATE_CALLBACKS[S][1]);raw[8:10]=bytes.fromhex('0960')
        with self.assertRaisesRegex(ValueError,'pinned state callback body differs'):
            closure.state_callback_effects(bytes(raw),S)

    def test_interpreter_refuses_state_escape_even_if_pinned(self):
        raw=bytes.fromhex('4a6801c20868013008604a6001207047')
        for edit,error in (((8,'0960'),'stores the private state address'),((2,'08c2'),'getter word'),
                           ((0,'8a68'),'leaves the private two-word state'),((6,'0230'),'effect relation')):
            changed=bytearray(raw);changed[edit[0]:edit[0]+2]=bytes.fromhex(edit[1])
            with self.subTest(edit=edit),self.assertRaisesRegex(ValueError,error),\
                    patch.dict(closure.STATE_CALLBACKS,{S:(8,changed.hex())}):
                closure.state_callback_effects(bytes(changed),S)

    def test_private_state_requires_pinned_callback(self):
        with self.assertRaisesRegex(ValueError,'pinned state callback'):
            owner.verify(**fixture(callback=X))

    def test_pinned_state_callback_refuses_without_private_state(self):
        for form in ('entry-object','null'):
            with self.subTest(form=form),self.assertRaisesRegex(ValueError,'private-state root form'):
                owner.verify(**fixture(form,callback=S))

    def test_state_form_requires_adapter_return_through_R1(self):
        with self.assertRaisesRegex(ValueError,'adapter return through R1'):owner.verify(**fixture(changes={(C,18):0xBC04,(C,20):0x4710}))

    def test_inexact_bindings_refuse(self):
        for change in (lambda b:b['functions'].reverse(),lambda b:b['functions'].pop(),
                       lambda b:b['data'].append([0,'fake',0]),lambda b:b['functions'][0].__setitem__(1,f'func_{X:08X}')):
            values=fixture();change(values['bindings'])
            with self.assertRaisesRegex(ValueError,'exact typed callback and adapter bindings'):owner.verify(**values)

    def test_iterator_and_dependency_changes_refuse(self):
        for target,offset,value in ((W,10,0x60A4),(W,12,0x2C01),(C,8,0x4621),(G,0,0x6840)):
            with self.subTest(target=hex(target),offset=offset),self.assertRaises(ValueError):
                owner.verify(**fixture(changes={(target,offset):value}))
        for target in (W,C,G,S,thunk.ALIASES['_call_via_r6']):
            values=fixture();rows=json.loads(values['mapping'])
            next(row for row in rows if int(row['rom'],16)==target)['instrs']+=1
            values['mapping']=json.dumps(rows).encode()
            with self.subTest(target=hex(target)),self.assertRaises(ValueError):owner.verify(**values)

    def test_even_literal_refuses(self):
        values=fixture();body=bytearray(values['data']);struct.pack_into('<I',body,36,S);values['data']=bytes(body)
        rom=bytearray(values['rom']);rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)]=body;values['rom']=bytes(rom)
        with self.assertRaisesRegex(ValueError,'odd Thumb pointers'):owner.verify(**values)

    def test_opaque_form_owner_loads_and_bytes(self):
        # entry-object loads from the R2 owner pointer; null from entry R0.
        for form,offset,value,error in (('entry-object',16,0x6900,'aligned incoming object word load'),
                                        ('entry-object',16,0x6911,'aligned incoming object word load'),
                                        ('entry-object',16,0x8A10,'aligned incoming object word load'),
                                        ('entry-object',6,0x3140,'natural root form'),
                                        ('entry-object',12,0x9001,'natural root form'),
                                        ('null',12,0x6910,'aligned incoming object word load'),
                                        ('null',12,0x6901,'aligned incoming object word load'),
                                        ('null',6,0x2101,'natural root form'),
                                        ('null',10,0x9202,'natural root form')):
            with self.subTest(form=form,offset=offset,value=hex(value)),self.assertRaisesRegex(ValueError,error):
                owner.verify(**fixture(form,changes={(A,offset):value}))

    def test_private_state_requires_adapter_context_R4(self):
        r5={(C,0):0xB520,(C,2):0x1C0D,(C,8):0x6829,(C,10):0x686A,(C,16):0xBC20}
        manifest,_=owner.verify(**fixture('null',changes=r5))
        self.assertEqual(manifest['proof']['literal_callback_closure']['adapter']['descriptor_register'],5)
        with self.assertRaisesRegex(ValueError,'adapter descriptor in R4'):owner.verify(**fixture(changes=r5))

    def test_missing_callback_index_row_refuses(self):
        values=fixture('null');rows=[row for row in json.loads(values['mapping']) if int(row['rom'],16)!=X]
        values['mapping']=json.dumps(rows).encode()
        with self.assertRaises(ValueError):owner.verify(**values)

    def test_exact_policy_and_immutable_input_contract(self):
        values=fixture()
        for key in('objects','bindings'):values.pop(key)
        for key,value in(('selector',previous.SELECTOR),('address',True),('data',bytearray(values['data']))):
            changed=dict(values);changed[key]=value
            with self.subTest(key=key),self.assertRaises(ValueError):closure.prove(**changed)

    def test_tree_iterators_are_admitted_with_their_own_obligations(self):
        for iterator,first in ((T1,12),(T2,16)):
            for form in closure.FORMS:
                with self.subTest(iterator=hex(iterator),form=form):
                    manifest,ins=owner.verify(**fixture(form,iterator=iterator))
                    proof=manifest['proof']['literal_callback_closure']
                    self.assertEqual(manifest['proof']['calls'][0],[closure.FORMS[form]['call'],f'func_{iterator:08X}'])
                    it=proof['iterator']
                    self.assertEqual((it['address'],it['end'],it['instructions']),(iterator,iterator+86,42))
                    self.assertEqual((it['adapter_register'],it['descriptor_register'],it['call_site']),(7,6,iterator+50))
                    self.assertEqual(it['thunk'][0],'_call_via_r7');self.assertEqual(it['stores'],[])
                    self.assertIn(f'node+{first} subtree visited before',it['kind'])
                    self.assertEqual(sorted(r['offset'] for r in it['reads'] if r['base']=='current node'),[8,12,16])
                    self.assertEqual([r['offset'] for r in it['reads'] if r['base']=='list object'],[8])
                    self.assertEqual(proof['outward_expired_aliases'],[])
                    self.assertFalse(it['termination_proved'])

    def test_list_iterator_record_is_bound(self):
        proof=owner.verify(**fixture())[0]['proof']['literal_callback_closure']
        self.assertEqual(proof['iterator']['thunk'][0],'_call_via_r6')
        self.assertEqual([(r['base'],r['offset']) for r in proof['iterator']['reads']],[('list object',4),('current node',8)])
        self.assertEqual(proof['outward_expired_aliases'][0]['register'],2)
        self.assertEqual(proof['adapter_shape'],'scalar-inventory')

    def test_tampered_iterator_record_refuses(self):
        values=fixture(iterator=T1);report,_=owner.verify(**values)
        for key,value in (('address',T2),('kind','list'),('adapter_register',6)):
            changed=copy.deepcopy(report);changed['proof']['literal_callback_closure']['iterator'][key]=value
            with self.subTest(key=key),self.assertRaisesRegex(ValueError,'manifest differs'):
                owner.verify(**values,manifest=changed)

    def test_wrong_tree_iterator_body_refuses(self):
        # node+12 -> node+20, the R1 entry copy, and the call argument register.
        for iterator in (T1,T2):
            for offset,value in ((18,0x6961),(2,0x1C0E),(48,0x1C29)):
                with self.subTest(iterator=hex(iterator),offset=offset),self.assertRaisesRegex(ValueError,'pinned identity'):
                    owner.verify(**fixture(iterator=iterator,changes={(iterator,offset):value}))

    def test_iterator_structure_is_checked_even_when_pinned(self):
        raw=bytes.fromhex(TREE[T1])
        for edit,error in (((18,0x6061),'must not store'),((58,0x1C26),'overwrites its adapter'),
                           ((36,0x1C0F),'overwrites its adapter'),((18,0x6961),'read set differs'),((18,0x6969),'outside the list object'),
                           ((2,0x1C0E),'entry copies')):
            changed=bytearray(raw);struct.pack_into('<H',changed,*edit)
            entry=dict(closure.ITERATORS[T1],sha256=closure.sha(bytes(changed)))
            with self.subTest(edit=edit),self.assertRaisesRegex(ValueError,error):
                closure.iterator_structure(bytes(changed),T1,entry,*tree_graph(bytes(changed)))

    def test_unlisted_iterator_refuses(self):
        # The tree walk at an unlisted address, and the next indexed function.
        for target in (0x08006000,0x080C7DC8):
            body=bytes.fromhex(TREE[T1])
            values=fixture(iterator=target,extra={target:(body,42)})
            with self.subTest(target=hex(target)),self.assertRaisesRegex(ValueError,'exact iterator call'):
                owner.verify(**values)

    def test_framed_adapter_with_each_iterator(self):
        for iterator in (W,T1,T2):
            for form in closure.FORMS:
                with self.subTest(iterator=hex(iterator),form=form):
                    manifest,_=owner.verify(**fixture(form,iterator=iterator,framed=True))
                    proof=manifest['proof']['literal_callback_closure']
                    self.assertEqual(proof['adapter_shape'],'framed-two-output')
                    self.assertEqual(proof['iterator']['address'],iterator)
                    adapter=proof['adapter']
                    self.assertEqual((adapter['schema'],adapter['address'],adapter['descriptor_register']),(closure.FRAMED_SCHEMA,F,4))
                    self.assertEqual([(w['frame_offset'],w['value']) for w in adapter['getter']['writes']],
                                     [(-16,'node word 4'),(-12,'node word 0')])
                    self.assertEqual(adapter['callback']['arguments'][0],'node word at offset 4, copied through private word -16')
                    getter=[r['offset'] for r in proof['external_read_obligations'] if r['base']=='each nonnull current node passed to getter']
                    self.assertEqual(getter,[4,0])
                    conditions=' '.join(proof['explicit_conditions'])
                    self.assertIn('nonnull',conditions);self.assertIn('out-pointers address only that local area',conditions)
                    if form=='private-state':
                        self.assertNotIn('Loaded input words carry no tracked private-frame',conditions)
                        self.assertEqual(proof['callback']['address'],S)

    def test_framed_adapter_or_getter_byte_change_refuses(self):
        for target,offset,value in ((F,2,0xB083),(F,6,0xAA02),(F,14,0x9801),(F,16,0x6861),
                                    (FG,0,0x6883),(FG,2,0x604B),(FG,6,0x6050)):
            with self.subTest(target=hex(target),offset=offset),self.assertRaisesRegex(ValueError,'pinned framed adapter'):
                owner.verify(**fixture(iterator=T1,framed=True,changes={(target,offset):value}))

    def test_framed_getter_cannot_write_outside_the_frame(self):
        getter=bytes.fromhex(closure.FRAMED_ADAPTERS[F]['getter_body']);body=bytes.fromhex(closure.FRAMED_ADAPTERS[F]['body'])
        # str r3,[r1,#8] (saved R4), str r3,[r0] (the node), str r3,[r1,#4] (twice into word -12).
        for edit,error in (((2,0x608B),'leaves the adapter private frame'),((2,0x6003),'leaves the adapter private frame'),
                           ((2,0x604B),'getter effect relation')):
            changed=bytearray(getter);struct.pack_into('<H',changed,*edit)
            pinned=dict(closure.FRAMED_ADAPTERS[F],getter_body=changed.hex())
            with self.subTest(edit=edit),self.assertRaisesRegex(ValueError,error),patch.dict(closure.FRAMED_ADAPTERS,{F:pinned}):
                closure.framed_adapter_effects(body,F,bytes(changed),FG)

    def test_framed_adapter_interpreter_escapes_refuse(self):
        getter=bytes.fromhex(closure.FRAMED_ADAPTERS[F]['getter_body']);raw=bytes.fromhex(closure.FRAMED_ADAPTERS[F]['body'])
        # Out pointer at saved R4; callback argument from word -12; descriptor word 8;
        # local area of 16 bytes; pop into PC.
        for edit,error in (((6,0xAA03),'leaves the adapter private frame'),((14,0x9801),'effect relation'),
                           ((18,0x68A2),'two descriptor words'),((2,0xB084),'getter effect relation'),((26,0xBD10),'must not pop PC'),((10,0x4770),'return only at its end')):
            changed=bytearray(raw);struct.pack_into('<H',changed,*edit)
            pinned=dict(closure.FRAMED_ADAPTERS[F],body=changed.hex())
            with self.subTest(edit=edit),self.assertRaisesRegex(ValueError,error),patch.dict(closure.FRAMED_ADAPTERS,{F:pinned}):
                closure.framed_adapter_effects(bytes(changed),F,getter,FG)

    def test_framed_adapter_requires_its_table_entry(self):
        # The same bytes at an unlisted address go through the scalar inventory and refuse.
        body=bytes.fromhex(closure.FRAMED_ADAPTERS[F]['body'])
        with self.assertRaises(ValueError):
            closure.framed_adapter_effects(body,0x0809AC02,bytes.fromhex(closure.FRAMED_ADAPTERS[F]['getter_body']),FG)
        values=fixture(iterator=T1,framed=True)
        with patch.dict(closure.FRAMED_ADAPTERS,{},clear=True),self.assertRaises(ValueError):
            owner.verify(**values)

    def test_framed_adapter_report_tampering_refuses(self):
        values=fixture(iterator=T2,framed=True);report,_=owner.verify(**values)
        for path in (('adapter_shape',),('adapter','getter','relation'),('adapter','descriptor_register')):
            changed=copy.deepcopy(report);target=changed['proof']['literal_callback_closure']
            for key in path[:-1]:target=target[key]
            target[path[-1]]=5 if path[-1]=='descriptor_register' else 'scalar-inventory' if path[-1]=='adapter_shape' else 'x'
            with self.subTest(path=path),self.assertRaisesRegex(ValueError,'manifest differs'):
                owner.verify(**values,manifest=changed)

    def test_framed_adapter_cannot_pass_or_return_frame_addresses(self):
        # Review repro: MOV R3,SP before the thunk BL; also MOV R2,SP before the return.
        p=closure.FRAMED_ADAPTERS[F];body=bytes.fromhex(p['body']);getter=bytes.fromhex(p['getter_body'])
        passed=body[:20]+struct.pack('<H',0x466B)+bl(F+22,thunk.ALIASES['_call_via_r2'])+body[24:]
        returned=body[:24]+struct.pack('<H',0x466A)+body[24:]
        for changed,error in ((passed,'passes a private frame address'),(returned,'returns a private frame address')):
            with self.subTest(error=error),self.assertRaisesRegex(ValueError,error),\
                    patch.dict(closure.FRAMED_ADAPTERS,{F:dict(p,body=changed.hex())}):
                closure.framed_adapter_effects(changed,F,getter,FG)

    def test_framed_getter_must_preserve_callee_saved_registers(self):
        p=closure.FRAMED_ADAPTERS[F];changed=bytearray.fromhex(p['getter_body'])
        struct.pack_into('<H',changed,4,0x6804)  # ldr r4,[r0]; then str r0,[r2] stores the stale R0
        with self.assertRaises(ValueError),patch.dict(closure.FRAMED_ADAPTERS,{F:dict(p,getter_body=changed.hex())}):
            closure.framed_adapter_effects(bytes.fromhex(p['body']),F,bytes(changed),FG)
        struct.pack_into('<H',changed,4,0x6805)  # ldr r5,[r0]: preserved-register violation only
        struct.pack_into('<H',changed,6,0x6015)  # str r5,[r2]
        with self.assertRaisesRegex(ValueError,'preserve R4-R11'),patch.dict(closure.FRAMED_ADAPTERS,{F:dict(p,getter_body=changed.hex())}):
            closure.framed_adapter_effects(bytes.fromhex(p['body']),F,bytes(changed),FG)

    def test_framed_descriptor_register_is_derived(self):
        p=closure.FRAMED_ADAPTERS[F];getter=bytes.fromhex(p['getter_body'])
        self.assertEqual(closure.framed_adapter_effects(bytes.fromhex(p['body']),F,getter,FG)['descriptor_register'],4)
        r5=bytes.fromhex('20b582b00d1c01aa6946')+bl(F+10,FG)+bytes.fromhex('009829686a68')+bl(F+20,thunk.ALIASES['_call_via_r2'])+bytes.fromhex('02b020bc02bc0847')
        with patch.dict(closure.FRAMED_ADAPTERS,{F:dict(p,body=r5.hex())}):
            effects=closure.framed_adapter_effects(r5,F,getter,FG)
        self.assertEqual(effects['descriptor_register'],5)
        self.assertEqual({row['base_register'] for row in effects['descriptor_reads']},{5})

    def test_empty_path_descriptor_alias_is_derived(self):
        worker=fixture()['rom'][W-match.ROM_BASE:W-match.ROM_BASE+34]
        self.assertTrue(closure.iterator_structure(worker,W,closure.ITERATORS[W],*tree_graph(worker,W,16))[1])
        for iterator in (T1,T2):
            body=bytes.fromhex(TREE[iterator])
            self.assertFalse(closure.iterator_structure(body,iterator,closure.ITERATORS[iterator],*tree_graph(body,iterator))[1])

    def test_list_object_liveness_follows_the_graph(self):
        # ldr r4,[r0,#8] at the loop's advance precedes R0's write in text order,
        # but is reached after "adds r0, r4, #0" on the loop's back edge.
        worker=bytearray(fixture()['rom'][W-match.ROM_BASE:W-match.ROM_BASE+34])
        struct.pack_into('<H',worker,10,0x6884)
        entry=dict(closure.ITERATORS[W],sha256=closure.sha(bytes(worker)),reads=(('list',4),('list',8)))
        with self.assertRaisesRegex(ValueError,'outside the list object'):
            closure.iterator_structure(bytes(worker),W,entry,*tree_graph(bytes(worker),W,16))


if __name__=='__main__':
    unittest.main()
