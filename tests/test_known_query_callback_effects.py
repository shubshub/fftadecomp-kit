"""New synthetic formal-query effects; no compiler or old proof producers."""
import copy
import json
from pathlib import Path
import struct
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import known_query_callback_effects as query

A, T, I, AD, G, C, TH6, TH2, ORD = [0x08000000+n for n in (0x100,0x200,0x300,0x400,0x500,0x600,0x700,0x710,0x800)]


def words(*values): return struct.pack('<'+'H'*len(values), *values)


def call(site, destination):
    n=(destination-site-4)&0x7fffff
    return words(0xf000|(n>>12),0xf800|((n>>1)&2047))


def callback():
    # Both flag-preserving and flag-writing paths; local word and materialized
    # rectangle-base accesses; one ordinary call after the local alias dies.
    data=words(0xb570,0xb088,0x1c05,0x1c0e,0x6830,0x42a8,0xd00a,
               0x2001,0x6070,0x9000,0xaa04,0x6090,0x9b00,0x1c28,0x2101,0x2200)
    return data+call(C+32,ORD)+words(0x2001,0xb008,0xbc70,0xbc02,0x4708)


def pin(data): return dict(bytes=len(data),sha256=query.sha(data))


def doc(address,body,count,profile,proof,bindings,rom):
    evidence=dict(address=address,bytes=len(body),instructions=count,rom_sha256=query.sha(rom),
                  manifest=dict(profile=profile,proof=proof,bindings=bindings))
    return ('* owner runtime evidence: `'+json.dumps(evidence)+'`\n* compiled : `'+body.hex()+
            '`\n* ROM bytes: `'+body.hex()+'` ('+str(len(body))+' bytes)\n').encode()


def fixture(cb=None):
    cb=callback() if cb is None else cb
    root=bytes.fromhex('00b582b0021c00290cd00091002001900349101c6a46')+call(A+22,T)
    root+=bytes.fromhex('019803e00000')+struct.pack('<I',C|1)+bytes.fromhex('002002b002bc0847')
    wrap=bytes.fromhex('00b582b000920191006903496a46')+call(T+14,I)+bytes.fromhex('02b001bc0047')+struct.pack('<I',AD|1)
    iterator=bytes.fromhex('70b50e1c151c446800e0a468002c05d0201c291c')+call(I+20,TH6)+bytes.fromhex('0028f6d170bc01bc0047')
    adapter=bytes.fromhex('10b50c1c')+call(AD+4,G)+bytes.fromhex('21686268')+call(AD+12,TH2)+bytes.fromhex('10bc02bc0847')
    getter=bytes.fromhex('00687047')
    bodies={A:root,T:wrap,I:iterator,AD:adapter,G:getter,C:cb,TH6:bytes.fromhex('3047'),TH2:bytes.fromhex('1047')}
    rom=bytearray(0x900)
    for address,body in bodies.items():rom[address-query.ROM_BASE:address-query.ROM_BASE+len(body)]=body
    rom=bytes(rom)
    counts={A:18,T:11,I:16,AD:9,G:2,C:len(cb)//2-1,TH6:1,TH2:1}
    mapping=json.dumps([dict(rom=f'0x{address:08X}',end=f'0x{address+len(body):08X}',mode='thumb',instrs=counts[address])for address,body in bodies.items()]).encode()
    index=''.join(f'{address:08X} {address+len(body):08X} {len(body)} {counts[address]}\n'for address,body in bodies.items()).encode()
    canon6=['_call_via_r6',TH6,TH6+4,query.sha(rom[TH6-query.ROM_BASE:TH6-query.ROM_BASE+4])]
    canon2=['_call_via_r2',TH2,TH2+4,query.sha(rom[TH2-query.ROM_BASE:TH2-query.ROM_BASE+4])]
    closure=dict(iterator=dict(address=I,end=I+len(iterator),instructions=16,body_sha256=query.sha(iterator),thunk=canon6),
        adapter=dict(address=AD,end=AD+len(adapter),instructions=9,body_sha256=query.sha(adapter),
            getter=dict(address=G,end=G+4,frame=dict(instructions=2),body_sha256=query.sha(getter)),
            callback=dict(thunk=TH2,canonical=canon2)))
    cbdoc=doc(C,cb,counts[C],'elf-symbol-thumb-acyclic-stack-alias-v1',{},dict(calls=[[32,f'func_{ORD:08X}']]),rom)
    trdoc=doc(T,wrap,11,'elf-symbol-thumb-conditional-two-word-callback-closure-v1',dict(callback_closure=closure),{},rom)
    return dict(body=root,address=A,rom=rom,mapping=mapping,index=index,callback_report=cbdoc,transport_report=trdoc,
                trusted_pins=dict(callback=pin(cbdoc),transport=pin(trdoc)),selector=query.SELECTOR)


class QueryCallbackTests(unittest.TestCase):
    def prove(self,body=None):return query.effects(callback() if body is None else body,C,selector=query.SELECTOR)
    def mutate(self,offset,code):
        body=bytearray(callback());body[offset:offset+2]=words(code);return bytes(body)

    def test_formal_flag_effect_and_initialized_private_rectangle(self):
        r=self.prove()
        self.assertEqual(r['query_reads'],[(C+8,0,4)])
        self.assertEqual(r['query_writes'],[(C+16,4,4,1)])
        self.assertEqual(r['maximum_frame_bytes'],48)
        self.assertEqual(r['allocated_local_word_offsets'],list(range(-48,-16,4)))
        self.assertEqual(r['protected_saved_word_offsets'],[-16,-12,-8,-4])
        self.assertEqual({tuple(row[1])for row in r['returns']},{query.FLAG,query.const(1)})
        self.assertFalse(r['tracked_query_or_private_alias_passed_to_ordinary_callees'])

    def test_complete_outer_query_composition(self):
        r=query.prove(**fixture())
        self.assertEqual(r['query_initialization']['flag'],0)
        self.assertEqual(r['frame_layout_relative_to_root_entry_SP']['callback_local'],[-96,-64])
        self.assertIn('finite number',r['query_effect'])
        self.assertIn('old unknown-scalar',r['transport_lift'])
        for name in ('iteration_bound_assumed','termination_proved','source_or_ELF_admission','native_admission','ordinary_callee_purity_proved'):
            self.assertIs(r[name],False)

    def test_explicit_selector(self):
        with self.assertRaisesRegex(ValueError,'explicit'):query.effects(callback(),C,selector='default')

    def test_non_one_query_store_refuses(self):
        with self.assertRaisesRegex(ValueError,'constant one'):self.prove(self.mutate(14,0x2002))

    def test_query_record_write_refuses(self):
        with self.assertRaisesRegex(ValueError,'flag word'):self.prove(self.mutate(18,0x6030))

    def test_partial_query_write_refuses(self):
        with self.assertRaisesRegex(ValueError,'flag word'):self.prove(self.mutate(18,0x7130))

    def test_query_flag_read_refuses(self):
        with self.assertRaisesRegex(ValueError,'record word'):self.prove(self.mutate(8,0x6870))

    def test_query_alias_argument_refuses(self):
        with self.assertRaisesRegex(ValueError,'call argument'):self.prove(self.mutate(28,0x1c31))

    def test_private_alias_argument_refuses(self):
        with self.assertRaisesRegex(ValueError,'call argument'):self.prove(self.mutate(30,0x466a))

    def test_query_alias_external_store_refuses(self):
        with self.assertRaisesRegex(ValueError,'tracked pointer'):self.prove(self.mutate(18,0x602e))

    def test_uninitialized_local_read_refuses(self):
        with self.assertRaisesRegex(ValueError,'initialization'):self.prove(self.mutate(24,0x9b01))

    def test_protected_save_write_refuses(self):
        with self.assertRaisesRegex(ValueError,'protected saves'):self.prove(self.mutate(20,0xaa08))

    def test_deallocation_of_save_refuses(self):
        with self.assertRaisesRegex(ValueError,'protected saves'):self.prove(self.mutate(38,0xb009))

    def test_callback_non_one_return_refuses(self):
        with self.assertRaisesRegex(ValueError,'return constant one'):self.prove(self.mutate(36,0x2000))

    def test_callback_wrong_saved_return_refuses(self):
        with self.assertRaisesRegex(ValueError,'restore its frame'):self.prove(self.mutate(44,0x4700))

    def test_backward_edge_refuses(self):
        with self.assertRaisesRegex(ValueError,'forward acyclic'):self.prove(self.mutate(12,0xd0fe))

    def test_internal_call_refuses(self):
        b=bytearray(callback());b[32:36]=call(C+32,C+36)
        with self.assertRaisesRegex(ValueError,'leave owner'):self.prove(bytes(b))

    def test_unsupported_scalar_instruction_refuses(self):
        with self.assertRaisesRegex(ValueError,'unsupported'):self.prove(self.mutate(26,0xbe00))

    def test_published_pin_tamper_refuses(self):
        args=fixture();args['callback_report']+=b' '
        with self.assertRaisesRegex(ValueError,'pin differs'):query.prove(**args)

    def test_root_query_initialization_change_refuses(self):
        args=fixture();body=bytearray(args['body']);body[12:14]=words(0x2001);args['body']=bytes(body)
        rom=bytearray(args['rom']);rom[A-query.ROM_BASE:A-query.ROM_BASE+44]=body;args['rom']=bytes(rom)
        # Preserve original report authority: this fails ROM binding before shape.
        with self.assertRaisesRegex(ValueError,'structural context'):query.prove(**args)

    def test_current_callback_count_mismatch_refuses(self):
        args=fixture();rows=json.loads(args['mapping']);next(row for row in rows if row['rom']==f'0x{C:08X}')['instrs']+=1;args['mapping']=json.dumps(rows).encode()
        with self.assertRaisesRegex(ValueError,'span/count'):query.prove(**args)

    def test_current_owner_overlap_refuses(self):
        args=fixture();rows=json.loads(args['mapping']);rows.append(dict(rom=f'0x{A+2:08X}',end=f'0x{A+4:08X}',mode='thumb',instrs=1));args['mapping']=json.dumps(rows).encode()
        with self.assertRaisesRegex(ValueError,'overlaps'):query.prove(**args)

    def test_ordinary_calls_have_explicit_noninterference_obligation(self):
        r=self.prove()
        self.assertEqual(r['calls'],[[C+32,ORD]])
        self.assertTrue(any('ambient state or hidden alias' in condition for condition in r['explicit_conditions']))
        self.assertFalse(r['ordinary_callee_purity_proved'])
        self.assertFalse(r['physical_memory_permission'])

    def test_signed_record_reads_scalar_rectangle_operations_and_external_write(self):
        extra=words(0x6830,0x2108,0x5e40,0x220a,0x5ea9,0x1a44,0x2c00,0x4264,
                    0x2004,0x7f29,0x4008,0x0600,0x9002,0x9902,0x3110,0x3910,
                    0x1c0a,0x2000,0x7728,0x2001,0x6070)
        body=bytearray(callback()[:36]+extra+callback()[36:])
        body[12:14]=words(0xd000|((36+len(extra)-16)//2))
        r=self.prove(bytes(body))
        self.assertEqual(len(r['query_writes']),2)
        self.assertTrue(any(row[1]=='read' and row[4]==2 for row in r['external_accesses']))
        self.assertTrue(any(row[1]=='write' and row[4]==1 for row in r['external_accesses']))
        self.assertFalse(r['ordinary_callee_purity_proved'])

    def test_query_pointer_scalar_arithmetic_refuses(self):
        with self.assertRaisesRegex(ValueError,'tracked pointer'):
            self.prove(self.mutate(26,0x4030))

    def test_nonconstant_indexed_pointer_offset_refuses(self):
        with self.assertRaisesRegex(ValueError,'exact scalar offset'):
            self.prove(self.mutate(26,0x5e40))

    def test_saved_register_corruption_refuses(self):
        with self.assertRaisesRegex(ValueError,'restore its frame'):
            self.prove(self.mutate(40,0xbc38))

    def test_private_pointer_stored_in_rectangle_refuses(self):
        body=bytearray(callback());body[14:18]=words(0xaa00,0x9200)
        with self.assertRaisesRegex(ValueError,'tracked pointer'):
            self.prove(bytes(body))

    def test_untracked_ordinary_store_is_recorded_not_discarded(self):
        body=bytearray(callback());body[22:24]=words(0x6028)
        r=self.prove(bytes(body))
        self.assertIn((C+22,'write',5,0,4),r['external_accesses'])
        self.assertTrue(any('does not overlap' in condition or 'do not overlap' in condition for condition in r['explicit_conditions']))

    def rebound(self,args,lo,raw):
        rom=bytearray(args['rom']);rom[lo-query.ROM_BASE:lo-query.ROM_BASE+len(raw)]=raw;args['rom']=bytes(rom)
        if lo==A:args['body']=raw
        for name in ('callback','transport'):
            key=name+'_report';record,body=query.published(args[key],args['trusted_pins'][name])
            if lo==record['address']:body=raw
            args[key]=doc(record['address'],body,record['instructions'],record['manifest']['profile'],
                          record['manifest']['proof'],record['manifest']['bindings'],args['rom'])
            args['trusted_pins'][name]=pin(args[key])
        return args

    def test_authenticated_root_nonzero_initial_flag_still_refuses_shape(self):
        args=fixture();body=bytearray(args['body']);body[12:14]=words(0x2001)
        with self.assertRaisesRegex(ValueError,'initialized two-word query'):
            query.prove(**self.rebound(args,A,bytes(body)))

    def test_authenticated_root_wrong_callback_identity_refuses(self):
        args=fixture();body=bytearray(args['body']);body[32:36]=struct.pack('<I',C+3)
        with self.assertRaisesRegex(ValueError,'callback literal'):
            query.prove(**self.rebound(args,A,bytes(body)))

    def test_authenticated_root_wrong_wrapper_target_refuses(self):
        args=fixture();body=bytearray(args['body']);body[22:26]=call(A+22,T+2)
        with self.assertRaisesRegex(ValueError,'wrapper target'):
            query.prove(**self.rebound(args,A,bytes(body)))

    def test_wrapper_query_token_store_change_refuses(self):
        args=fixture();_,body=query.published(args['transport_report'],args['trusted_pins']['transport']);body=bytearray(body);body[4:6]=words(0x9000)
        with self.assertRaisesRegex(ValueError,'wrapper query-token'):
            query.prove(**self.rebound(args,T,bytes(body)))

    def test_changed_iterator_bytes_refuse_against_frozen_dependency(self):
        args=fixture();body=args['rom'][I-query.ROM_BASE:I-query.ROM_BASE+34];body=bytearray(body);body[6]^=1
        with self.assertRaisesRegex(ValueError,'transport dependency body'):
            query.prove(**self.rebound(args,I,bytes(body)))

    def test_extra_indexed_owner_in_thunk_padding_refuses(self):
        args=fixture();rows=json.loads(args['mapping']);rows.append(dict(rom=f'0x{TH2+2:08X}',end=f'0x{TH2+4:08X}',mode='thumb',instrs=1));args['mapping']=json.dumps(rows).encode()
        with self.assertRaisesRegex(ValueError,'indexed padding'):
            query.prove(**args)

    def test_expired_rectangle_R2_is_retained_and_composed(self):
        body=bytearray(callback()[:36]+words(0xaa04)+callback()[36:])
        body[12:14]=words(0xd00b)
        r=query.prove(**fixture(bytes(body)))
        aliases=r['callback_effects']['returned_private_aliases']
        self.assertEqual([(row['register'],row['entry_SP_offset'],row['lifetime'])for row in aliases],
                         [(2,-32,'expired-at-return')])
        stale=r['stale_alias_transport']
        self.assertEqual(stale['callback_R2'][0]['root_entry_SP_offset'],-80)
        self.assertEqual(stale['no_callback_R2']['root_entry_SP_offset'],-24)
        self.assertFalse(stale['outward_aliases_erased'])
        self.assertFalse(stale['caller_use_after_outer_return_proved'])

    def test_returned_query_alias_is_not_laundered_as_stale_local(self):
        body=bytearray(callback()[:36]+words(0x1c32)+callback()[36:]);body[12:14]=words(0xd00b)
        with self.assertRaisesRegex(ValueError,'query alias escapes'):
            self.prove(bytes(body))

    def test_unsupported_returned_local_register_refuses(self):
        body=bytearray(callback()[:36]+words(0xab04)+callback()[36:]);body[12:14]=words(0xd00b)
        with self.assertRaisesRegex(ValueError,'unsupported private alias escapes'):
            self.prove(bytes(body))

    def test_local_address_materialization_cannot_leave_live_allocation(self):
        with self.assertRaisesRegex(ValueError,'materialized local address'):
            self.prove(self.mutate(20,0xaaff))

    def test_stale_R2_observation_in_iterator_refuses_even_if_reauthenticated(self):
        args=fixture();body=bytearray(args['rom'][I-query.ROM_BASE:I-query.ROM_BASE+34]);body[24:26]=words(0x6810)
        self.rebound(args,I,bytes(body))
        record,wrapper=query.published(args['transport_report'],args['trusted_pins']['transport'])
        record['manifest']['proof']['callback_closure']['iterator']['body_sha256']=query.sha(bytes(body))
        args['transport_report']=doc(T,wrapper,11,record['manifest']['profile'],record['manifest']['proof'],record['manifest']['bindings'],args['rom'])
        args['trusted_pins']['transport']=pin(args['transport_report'])
        with self.assertRaisesRegex(ValueError,'iterator query-token'):
            query.prove(**args)

    def test_null_record_preserves_caller_owner_origin_in_R2(self):
        r=query.prove(**fixture())
        self.assertEqual(r['stale_alias_transport']['null_record_R2'],
                         dict(register=2,origin='root-entry-R0',caller_origin_preserved=True))
        self.assertEqual(r['root_return_origins']['R1'],'original root entry LR')
        self.assertIn('entry origins',r['root_return_origins']['R3_R12'])


if __name__=='__main__':unittest.main()
