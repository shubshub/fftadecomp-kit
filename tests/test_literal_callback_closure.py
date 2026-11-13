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
E,FL=0x0809ACA4,0x0809AD48  # entry-state callback; flag callback (root of the pinned tree)
# Genuine bodies of the pinned flag callback tree, at their own addresses.
FLAGTREE={FL:'00b5021c0b1c1068018d8020c0010840002804d0101c191cfdf726ff00e0012002bc0847',
    0x08098BB0:'30b5041c0d1c20682ff062fb0006002805d0206834f082fe0006002824d0206834f0acfe000600281ed1206835f086f80006002818d1697801200840002805d020682ff035fb000600280dd1697802200840002805d020682ff05afc0006002802d0287801302870012030bc02bc0847',
    0x080C8280:'00b50021002803d0008b002800d10121081c02bc0847',
    0x080CD8CC:'00b5e830042100780840002801d0012000e0002002bc0847',
    0x080CD92C:'00b5e830402100780840002801d0012000e0002002bc0847',
    0x080CDCEC:'00b5ed30402100780840002801d0012000e0002002bc0847',
    0x080C8260:'00b50021002807d0018d8020800108400004000c4042c10f081c02bc0847',
    0x080C84C0:'00b50022002811d00079011c52290cd054290ad0532908d01e2906d01f2904d039380006000e0d2800d80122101c02bc0847'}
ROOTS={  # form: (owner-load halfword, callback)
    'private-state':(0x6900,S),'entry-object':(0x6910,X),'null':(0x6900,X),
    'entry-byte':(0x6900,X),'owner-word-trailing-call':(0x6920,X),
    'entry-state':(0x6900,E),'local-byte-flag':(0x6940,FL)}


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
    if len(body)==shape['size']:  # whole-function template with an interior pool
        struct.pack_into('<II',body,shape['callback'],callback+1,adapter+1)
        return bytes(body)
    return bytes(body)+struct.pack('<II',callback+1,adapter+1)


def fixture(form='private-state',changes=None,callback=None,iterator=W,framed=False,extra=None):
    callback=ROOTS[form][1] if callback is None else callback
    worker=bytes.fromhex('70b50e1c151c446800e0a468002c05d0201c291c')+bl(W+20,thunk.ALIASES['_call_via_r6'])+bytes.fromhex('0028f6d170bc01bc0047')
    adapter=bytes.fromhex('10b50c1c')+bl(C+4,G)+bytes.fromhex('21686268')+bl(C+12,thunk.ALIASES['_call_via_r2'])+bytes.fromhex('10bc02bc0847')
    used=F if framed else C
    bodies={A:root(form,callback,iterator,used),W:worker,G:bytes.fromhex('00687047'),
            X:bytes.fromhex('01207047')}
    counts={A:closure.FORMS[form]['count'],W:16,G:2,X:2}
    for target,pinned in closure.STATE_CALLBACKS.items():
        bodies[target]=bytes.fromhex(pinned['body']);counts[target]=pinned['count']
    for target,body in FLAGTREE.items():
        bodies[target]=bytes.fromhex(body);counts[target]=closure.FLAG_CALLBACKS[FL]['tree'][target][1]
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
        raw=bytearray.fromhex(closure.STATE_CALLBACKS[S]['body']);raw[8:10]=bytes.fromhex('0960')
        with self.assertRaisesRegex(ValueError,'pinned state callback body differs'):
            closure.state_callback_effects(bytes(raw),S)

    def test_interpreter_refuses_state_escape_even_if_pinned(self):
        raw=bytes.fromhex('4a6801c20868013008604a6001207047')
        for edit,error in (((8,'0960'),'stores the private state address'),((2,'08c2'),'getter word'),
                           ((0,'8a68'),'leaves the private two-word state'),((6,'0230'),'effect relation')):
            changed=bytearray(raw);changed[edit[0]:edit[0]+2]=bytes.fromhex(edit[1])
            with self.subTest(edit=edit),self.assertRaisesRegex(ValueError,error),\
                    patch.dict(closure.STATE_CALLBACKS,{S:dict(closure.STATE_CALLBACKS[S],body=changed.hex())}):
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
                    self.assertEqual([row for row in proof['outward_expired_aliases'] if row['register']==2],[])
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
                    if form=='local-byte-flag':
                        with self.assertRaisesRegex(ValueError,'private flag requires the scalar adapter'):
                            owner.verify(**fixture(form,iterator=iterator,framed=True))
                        continue
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

    def test_entry_state_form(self):
        manifest,ins=owner.verify(**fixture('entry-state'))
        self.assertEqual(len(ins),15)
        proof=manifest['proof']['literal_callback_closure']
        self.assertEqual(proof['form'],'entry-state')
        self.assertEqual(proof['private_state'],dict(offset=-20,width=8,result=None,
            initialized=[dict(offset=0,entry_register=1),dict(offset=4,entry_register=2)]))
        self.assertEqual([(w['offset'],w['source']) for w in proof['root_descriptor']['initialized_words']],
                         [(-20,'root entry R1'),(-16,'root entry R2'),(-12,'address of private state'),(-8,'typed callback literal')])
        effects=proof['callback']
        self.assertEqual(effects['address'],E);self.assertTrue(effects['private_provenance_passed'])
        self.assertEqual([row[1] for row in effects['state_reads']],[0,4]);self.assertEqual(effects['state_writes'],[])
        self.assertEqual(effects['external_reads'],[[E+2,'getter object',48,4]])
        self.assertEqual(effects['external_writes'],[[E+10,'getter object',48,4,'((object word 48 & ~state word 0) | state word 4)']])
        conditions=' '.join(proof['explicit_conditions'])
        self.assertIn('getter object word at offset 48',conditions);self.assertNotIn('word-4 cursor',conditions)
        self.assertNotIn('Loaded input words carry no tracked private-frame',conditions)
        # The private-state form keeps its own record and cursor premise.
        state=owner.verify(**fixture())[0]['proof']['literal_callback_closure']
        self.assertNotIn('external_reads',state['callback'])
        self.assertIn('word-4 cursor',' '.join(state['explicit_conditions']))

    def test_local_byte_flag_form(self):
        manifest,ins=owner.verify(**fixture('local-byte-flag'))
        self.assertEqual(len(ins),23)
        self.assertEqual(manifest['proof']['partition']['alignment_bytes'],0)
        proof=manifest['proof']['literal_callback_closure']
        self.assertEqual(proof['form'],'local-byte-flag')
        self.assertEqual(proof['root_frame']['local_bytes'],12)
        self.assertEqual(proof['root_descriptor']['initialized_words'][0],dict(offset=-16,width=1,source='constant zero'))
        self.assertEqual(proof['root_descriptor']['actual_buffer_checks'][0]['pointer_slots'],[[-12,-16]])
        state=proof['private_state']
        self.assertEqual((state['offset'],state['width'],state['initialized'],state['uninitialized_bytes']),
                         (-16,1,[dict(offset=0,width=1,value=0)],[1,2,3]))
        self.assertEqual(state['result']['site'],A+30)
        self.assertIn('1 if flag byte 0 is nonzero',state['result']['relation'])
        self.assertEqual([row['site'] for row in state['indeterminate_reads']],[0x08098BE6,0x08098BFC])
        effects=proof['callback']
        self.assertEqual([row['address'] for row in effects['tree']],sorted(FLAGTREE))
        self.assertEqual(effects['flag_reads'],[[0x08098BE6,1,1],[0x08098BFC,1,1],[0x08098C12,0,1]])
        self.assertEqual([row[:3] for row in effects['flag_writes']],[[0x08098C16,0,1]])
        self.assertEqual((effects['return_value'],effects['external_writes'],effects['flag_address_stored']),(1,[],False))
        self.assertEqual(effects['flag_aliases_on_return'],[3])
        self.assertEqual([row['register'] for row in proof['outward_expired_aliases']],[2,3])
        conditions=' '.join(proof['explicit_conditions'])
        self.assertIn('private flag address',conditions);self.assertIn('interpreted callback tree',conditions)
        self.assertNotIn('its effects are not interpreted',conditions)
        self.assertNotIn('Loaded input words carry no tracked private-frame',conditions)

    def test_new_genuine_roots_and_refined_counts(self):
        for form,raw in (('entry-state','00b584b00091019205496a46029202aa5160006903492df0affb04b001bc0047a5ac0908e9ab0908'),
                         ('local-byte-flag','00b583b0002269460a7007496a46019201aa5160406905492df00afa68460078002805d1002004e049ad0908e9ab0908012003b002bc0847'),
                         ('local-byte-flag','00b583b0002269460a7007496a46019201aa5160806905492df0eef968460078002805d1002004e049ad0908e9ab0908012003b002bc0847')):
            with self.subTest(form=form):self.assertEqual(closure.form_of(bytes.fromhex(raw)),form)
        # The unrefined rows (pool halfwords and both BL halves counted) refuse.
        for form,count in (('entry-state',20),('local-byte-flag',28)):
            values=fixture(form);rows=json.loads(values['mapping'])
            next(row for row in rows if int(row['rom'],16)==A)['instrs']=count
            values['mapping']=json.dumps(rows).encode()
            values['index']=values['index'].replace(f' {closure.FORMS[form]["count"]} return'.encode(),f' {count} return'.encode(),1)
            with self.subTest(form=form),self.assertRaisesRegex(ValueError,'exact complete owner/count'):owner.verify(**values)

    def test_new_root_templates_refuse_other_shapes(self):
        for form,offset,value in (
                ('local-byte-flag',4,0x2201),   # flag initialized to one, not zero
                ('local-byte-flag',8,0x46C0),   # flag never initialized
                ('local-byte-flag',8,0x600A),   # a word store over the flag slot
                ('local-byte-flag',28,0x9800),  # flag word read instead of the byte
                ('local-byte-flag',30,0x8800),  # halfword read
                ('local-byte-flag',34,0xD005),  # beq: inverted result
                ('local-byte-flag',36,0x2001),  # both arms return one
                ('local-byte-flag',38,0xE005),  # branch past the epilogue
                ('local-byte-flag',2,0xB084),   # frame size
                ('local-byte-flag',14,0x9100),  # extra store of the literal over the flag
                ('entry-state',4,0x9300),       # state word zero from R3
                ('entry-state',6,0x9102),       # state word four from R1
                ('entry-state',26,0x9802)):     # result read-back
            with self.subTest(form=form,offset=offset),self.assertRaisesRegex(ValueError,'natural root form'):
                owner.verify(**fixture(form,changes={(A,offset):value}))
        # Reading the flag before the call is not a pinned shape either.
        data=bytearray(fixture('local-byte-flag')['data']);data[22:24]=bytes.fromhex('0078')
        with self.assertRaisesRegex(ValueError,'natural root form'):closure.form_of(bytes(data))

    def test_private_callbacks_pair_with_their_own_root_form(self):
        for form,callback,error in (('local-byte-flag',X,'pinned flag callback'),('local-byte-flag',S,'pinned flag callback'),
                                    ('local-byte-flag',E,'pinned flag callback'),('entry-state',S,'pinned state callback'),
                                    ('entry-state',X,'pinned state callback'),('entry-state',FL,'pinned state callback'),
                                    ('private-state',E,'pinned state callback'),('null',FL,'local-byte-flag root form'),
                                    ('entry-byte',FL,'local-byte-flag root form'),('null',E,'private-state root form')):
            with self.subTest(form=form,callback=hex(callback)),self.assertRaisesRegex(ValueError,error):
                owner.verify(**fixture(form,callback=callback))

    def test_entry_state_callback_changes_refuse(self):
        for offset,value in ((2,0x6A82),(8,0x438A),(2,0x6301),(12,0x2000)):
            with self.subTest(offset=offset),self.assertRaises(ValueError):
                owner.verify(**fixture('entry-state',changes={(E,offset):value}))
        raw=bytes.fromhex(closure.STATE_CALLBACKS[E]['body'])
        # str r1,[r0,#48] stores the state address; ldr r1,[r1,#8] leaves the state;
        # orrs in place of bics; and a second store through the object.
        for edit,error in (((2,0x6301),'stores the private state address'),((6,0x6889),'leaves the private two-word state'),
                           ((4,0x431A),'effect relation'),((10,0x6301),'effect relation'),((12,0x6302),'return/frame differs'),
                           ((4,0x438A),'computes with the private state')):
            changed=bytearray(raw);struct.pack_into('<H',changed,*edit)
            with self.subTest(edit=edit),self.assertRaisesRegex(ValueError,error),\
                    patch.dict(closure.STATE_CALLBACKS,{E:dict(closure.STATE_CALLBACKS[E],body=changed.hex())}):
                closure.state_callback_effects(bytes(changed),E)

    def flag_effects(self,target,offset,value):
        """Interpret the flag tree with one halfword changed and its pin updated."""
        values=fixture('local-byte-flag',changes={(target,offset):value})
        body=values['rom'][target-match.ROM_BASE:target-match.ROM_BASE+len(FLAGTREE[target])//2]
        tree=dict(closure.FLAG_CALLBACKS[FL]['tree']);size,count,_=tree[target];tree[target]=(size,count,closure.sha(body))
        with patch.dict(closure.FLAG_CALLBACKS,{FL:dict(closure.FLAG_CALLBACKS[FL],tree=tree)}):
            return closure.flag_callback_effects(FL,values['rom'],values['mapping'],values['index'])

    def test_flag_tree_pins_and_counts(self):
        effects,aliases=closure.flag_callback_effects(FL,*(fixture('local-byte-flag')[k] for k in ('rom','mapping','index')))
        self.assertEqual(aliases,[3]);self.assertEqual(effects['return_value'],1)
        for target,offset,value in ((FL,6,0x6811),(0x08098BB0,0x64,0x3002),(0x080C84C0,2,0x2201)):
            with self.subTest(target=hex(target)),self.assertRaisesRegex(ValueError,'pinned flag callback tree differs'):
                owner.verify(**fixture('local-byte-flag',changes={(target,offset):value}))
        values=fixture('local-byte-flag');rows=json.loads(values['mapping'])
        next(row for row in rows if int(row['rom'],16)==0x080C8280)['instrs']+=1
        values['mapping']=json.dumps(rows).encode()
        with self.assertRaises(ValueError):owner.verify(**values)

    def test_flag_tree_interpreter_refuses_escapes(self):
        B=0x08098BB0
        for target,offset,value,error in (
                (B,0x66,0x7068,'access through the flag address differs'),   # strb r0,[r5,#1]
                (B,0x36,0x78A9,'access through the flag address differs'),   # ldrb r1,[r5,#2]
                (B,0x66,0x6028,'access through the flag address differs'),   # word store
                (B,0x64,0x3002,'computes with a tracked'),                  # adds r0,#2 on the flag byte
                (B,0x64,0x0000,'access through the flag address differs'),   # stores the byte unchanged
                (FL,6,0x6013,'stores outside the private flag byte'),        # str r3,[r2]: flag address to memory
                (FL,0,0xB502,'stores the flag address'),                     # push {r1,lr}
                (FL,4,0x1C4B,'computes with a tracked'),              # adds r3,r1,#1
                (FL,30,0x1C18,'return/frame differs'),                       # returns the flag address
                (0x080C8280,8,0x8B18,'access through the flag address differs'),  # ldrh r0,[r3,#24]: the R3 alias
                (0x080C8280,2,0x2400,'return/frame differs'),                # clobbers R4
                (0x080C8280,0,0xB410,'return/frame differs'),               # push {r4}: returns through the saved R4, not LR
                # Review attacks: the caller's R5 flag address copied out of a
                # callee-saved register, a callee-saved value returned, and
                # uninitialized flag byte 1 used other than as a tested bit.
                (0x080C8280,10,0x1C2A,'return/frame differs'),              # adds r2,r5,#0 in a leaf
                (0x080C8280,16,0x1C20,'return/frame differs'),              # adds r0,r4,#0: the leaf's own R4 returned
                (B,0x38,0x6808,'computes with a tracked'),                  # ldr r0,[r1]: byte 1 as a load base
                (B,0x3A,0x4308,'computes with a tracked'),                  # orrs r0,r1: byte 1 as data
                (B,0x38,0x4048,'computes with a tracked'),                  # eors r0,r1: byte 1 mixed with a constant
                (B,0x3C,0x1C0A,'return/frame differs'),                     # adds r2,r1,#0: byte 1 left in R2
                (B,0x3E,0x1C0A,'return/frame differs'),                     # same, as the beq is replaced
                (B,0x3C,0x782A,'return/frame differs')):                    # ldrb r2,[r5]: byte 0 left in R2
            with self.subTest(target=hex(target),offset=offset),self.assertRaisesRegex(ValueError,error):
                self.flag_effects(target,offset,value)

    def test_scratch_alias_must_not_reach_a_reader(self):
        def check(body,registers=(3,)):
            rows=json.dumps([dict(rom=f'0x{G:08X}',end=f'0x{G+len(body):08X}',mode='thumb',instrs=len(body)//2),
                             dict(rom=f'0x{X:08X}',end=f'0x{X+4:08X}',mode='thumb',instrs=2)]).encode()
            ins,edges,_,calls,_=graph.graph(body,G,owner.refine(body,G,rows))
            closure.scratch_aliases_unread(ins,edges,calls,G,registers)
        check(bytes.fromhex('00687047'))          # the genuine getter
        check(bytes.fromhex('00231b687047'))      # movs r3,#0 then ldr r3,[r3]: overwritten first
        for body in (bytes.fromhex('18687047'),bytes.fromhex('1846'+'7047'),bytes.fromhex('0023')+bl(G+2,X)+bytes.fromhex('18687047')):
            with self.subTest(body=body.hex()),self.assertRaisesRegex(ValueError,'alias reaches a reader'):check(body)
        with self.assertRaisesRegex(ValueError,'alias reaches a reader'):check(bytes.fromhex('6046'+'7047'),(12,))

    def test_tampered_private_records_refuse(self):
        for form,path,value in (('local-byte-flag',('callback','flag_writes'),[]),
                                ('local-byte-flag',('callback','flag_aliases_on_return'),[]),
                                ('local-byte-flag',('private_state','result','relation'),'zero'),
                                ('local-byte-flag',('private_state','indeterminate_reads'),[]),
                                ('local-byte-flag',('outward_expired_aliases',),[]),
                                ('entry-state',('callback','external_writes'),[]),
                                ('entry-state',('private_state','initialized'),[])):
            values=fixture(form);report,_=owner.verify(**values)
            changed=copy.deepcopy(report);target=changed['proof']['literal_callback_closure']
            for key in path[:-1]:target=target[key]
            target[path[-1]]=value
            with self.subTest(form=form,path=path),self.assertRaisesRegex(ValueError,'manifest differs'):
                owner.verify(**values,manifest=changed)


if __name__=='__main__':
    unittest.main()
