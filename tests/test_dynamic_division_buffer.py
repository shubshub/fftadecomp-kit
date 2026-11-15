"""New dynamic division closure guards; no existing successful test replay."""
import json
import unittest

import dynamic_division_buffer_profile as dynamic
import dynamic_division_actual_fixtures as actual
import owner_admission_profile as owner
import owner_graph_profile as graph

A = 0x0809D6BC


def inputs(callee=actual.CALLEE, divisor=actual.DIV, zero=actual.ZERO):
    rom = bytearray(dynamic.ZERO + len(zero) - dynamic.match.ROM_BASE)
    rows, lines = [], []
    for a, data, count in ((A, callee, 109), (dynamic.DIV, divisor, 72), (dynamic.ZERO, zero, 1)):
        rom[a-dynamic.match.ROM_BASE:a-dynamic.match.ROM_BASE+len(data)] = data
        rows.append(dict(rom=f'0x{a:08X}', end=f'0x{a+len(data):08X}', mode='thumb', instrs=count))
        lines.append(f'{a:08X} {a+len(data):08X} {len(data)} {count} return\n')
    return dict(data=callee, address=A, rom=bytes(rom), mapping=json.dumps(rows).encode(), index=''.join(lines).encode())


def replay(hexcode, entry=None):
    data = bytes.fromhex(hexcode)
    address = 0x08010000
    mapping = json.dumps([dict(rom=hex(address), end=hex(address+len(data)), mode='thumb', instrs=0)]).encode()
    ins, edges, branches, calls, words = graph.graph(data, address, owner.refine(data,address,mapping))
    assert not branches and not words
    entry = entry or tuple(dynamic.SCALAR if n < 2 else ('entry',n) for n in range(13)) + (('local',0),dynamic.RETURN)
    runner = dynamic.OriginReplay({address:(ins,edges,calls)})
    return runner.run(address,entry)


def caller_fixture(after='00220123', before='6a46'):
    """Independent caller, real complete helpers; no compiler or original ELF."""
    x=inputs();rom=bytearray(x['rom']);rows=json.loads(x['mapping']);lines=x['index'].decode().splitlines()
    root=0x08010000
    data=bytearray.fromhex('50b582b06e46694601aa01ab')
    def bl(target):
        delta=target-(root+len(data)+4)
        data.extend((0xF000|((delta>>12)&0x7FF)).to_bytes(2,'little'))
        data.extend((0xF800|((delta>>1)&0x7FF)).to_bytes(2,'little'))
    bl(dynamic.three.WRAPPER[0]);data.extend(bytes.fromhex('00200121'+before));bl(A)
    data.extend(bytes.fromhex(after+'02b050bc02bc0847'))
    for a,raw in ((root,bytes(data)),(dynamic.three.WRAPPER[0],actual.THREE_WRAPPER),(dynamic.three.LEAF[0],actual.THREE_LEAF)):
        rom[a-dynamic.match.ROM_BASE:a-dynamic.match.ROM_BASE+len(raw)]=raw
        rows.append(dict(rom=f'0x{a:08X}',end=f'0x{a+len(raw):08X}',mode='thumb',instrs=0))
    mapping=json.dumps(rows).encode()
    for row in rows:
        a=int(row['rom'],16)
        if row['instrs']==0:
            raw=bytes(rom[a-dynamic.match.ROM_BASE:int(row['end'],16)-dynamic.match.ROM_BASE])
            row['instrs']=owner.refine(raw,a,mapping)['instrs']
            lines.append(f'{a:08X} {a+len(raw):08X} {len(raw)} {row["instrs"]} return')
    x.update(data=bytes(data),address=root,rom=bytes(rom),mapping=json.dumps(rows).encode(),index=('\n'.join(lines)+'\n').encode())
    return x


class DynamicDivisionTests(unittest.TestCase):
    def test_actual_complete_arbitrary32_zero_and_nonzero_paths(self):
        proof = dynamic.prove(**inputs(), selector=dynamic.SELECTOR)
        self.assertEqual(proof['instructions'],109)
        self.assertEqual(proof['residual_local_scratch'],[(0x0809D798,2,-28)])
        self.assertFalse(proof['caller_composition'])
        self.assertFalse(proof['termination_claim'])
        self.assertEqual(proof['numeric_operand_preconditions'],[])
        self.assertEqual(proof['external_memory_reads'],[])
        self.assertEqual(proof['incoming_stack_reads'],[])
        self.assertEqual({a for a,_ in proof['runtime_closure']},{dynamic.DIV,dynamic.ZERO})
        self.assertEqual(proof['runtime_closure'][0][1]['returns'],[0x0814273E,0x08142748])
        self.assertTrue(all(row[1][6]==('entry',6) for row in proof['returns']))
        self.assertTrue(all(row[1][3]==('entry',8) for row in proof['returns']))

    def test_selector_and_immutable_input_contract(self):
        for selector in (None,True,dynamic.three.SELECTOR,'canonical-integer-discarded-scratch-alias-inventory-v1'):
            with self.subTest(selector=selector), self.assertRaisesRegex(ValueError,'explicit selector'):
                dynamic.prove(**inputs(),selector=selector)
        changed=inputs();changed['data']=bytearray(changed['data'])
        with self.assertRaisesRegex(ValueError,'immutable'):
            dynamic.prove(**changed,selector=dynamic.SELECTOR)

    def test_actual_canonical_runtime_mutation_is_rejected(self):
        changed=bytearray(actual.DIV);changed[0:2]=bytes.fromhex('0020')
        with self.assertRaises(ValueError):
            dynamic.prove(**inputs(divisor=bytes(changed)),selector=dynamic.SELECTOR)

    def test_zero_hook_body_cannot_be_replaced_by_a_summary(self):
        with self.assertRaises(ValueError):
            dynamic.prove(**inputs(zero=bytes.fromhex('7047')),selector=dynamic.SELECTOR)

    def test_complete_callee_count_and_extent_must_agree(self):
        changed=inputs();changed['index']=changed['index'].replace(b'222 109',b'222 108')
        with self.assertRaisesRegex(ValueError,'count'):
            dynamic.prove(**changed,selector=dynamic.SELECTOR)
        changed=inputs();changed['data']=changed['data'][:-2]
        with self.assertRaises(ValueError):
            dynamic.prove(**changed,selector=dynamic.SELECTOR)

    def test_private_byte_initialization_and_zero_index(self):
        # SUB SP,4; MOV R2,SP; MOV R0,0; STRB R0,[R2]; LDRSB R0,[R2,R0]; ADD SP,4; BX LR
        result=replay('81b06a4600201070105601b07047')
        self.assertEqual(result[0][1][0],dynamic.SCALAR)
        self.assertEqual(result[0][1][2],('local',-4))

    def test_uninitialized_private_byte_is_not_an_unknown_scalar(self):
        with self.assertRaisesRegex(ValueError,'uninitialized'):
            replay('81b06a460020105601b07047')

    def test_nonzero_index_cannot_borrow_a_local_bound(self):
        with self.assertRaisesRegex(ValueError,'exact zero'):
            replay('81b06a4601201070105601b07047')

    def test_partial_write_does_not_initialize_a_word(self):
        with self.assertRaisesRegex(ValueError,'uninitialized'):
            replay('81b06a4600201070106801b07047')

    def test_opaque_pointer_cannot_be_observed_or_stored(self):
        for code in ('10687047','002a7047','81b06a46137001b07047'):
            with self.subTest(code=code),self.assertRaisesRegex(ValueError,'memory base|opaque'):
                replay(code)

    def test_protected_saved_word_cannot_be_accessed_through_local_alias(self):
        with self.assertRaisesRegex(ValueError,'protected'):
            replay('00b56a46106800bd')

    def test_allocated_address_cannot_survive_as_live_memory_after_pop(self):
        with self.assertRaisesRegex(ValueError,'dead frame'):
            replay('81b06a4601b010687047')

    def test_opaque_callee_saved_origin_can_only_be_transport(self):
        result=replay('40b5012640bc01bc0047')
        self.assertEqual(result[0][1][6],('entry',6))
        with self.assertRaisesRegex(ValueError,'opaque'):
            replay('40b5013640bc01bc0047')

    def test_zero_hook_returns_exact_scratch_origins(self):
        result=replay('f746')
        self.assertEqual(result[0][1][2],('entry',2))
        self.assertEqual(result[0][1][3],('entry',3))
        self.assertEqual(result[0][1][12],('entry',12))

    def test_pointer_flags_are_not_numeric_branch_facts(self):
        with self.assertRaisesRegex(ValueError,'flags'):
            replay('81b06a46013200d001b07047')

    def test_unsaved_control_or_callee_register_cannot_be_returned(self):
        for code in ('01247047','00207046'):
            with self.subTest(code=code),self.assertRaises(ValueError):
                replay(code)

    def test_exact_consumer_composes_saved_R6_and_private_scratch(self):
        x=caller_fixture()
        _,_,_,calls,_=graph.graph(x['data'],x['address'],owner.refine(x['data'],x['address'],x['mapping']))
        bindings=dict(calls=[[s-x['address'],f'func_{a:08X}'] for s,a in sorted(calls.items())],data=[],functions=[],switches=[])
        manifest,ins=owner.verify(**x,objects=b'{}',bindings=bindings,selector=dynamic.SELECTOR)
        self.assertEqual(manifest['profile'],dynamic.SCHEMA)
        proof=manifest['owner']['buffers']['dynamic_division'] if 'owner' in manifest else manifest['proof']['buffers']['dynamic_division']
        self.assertTrue(proof['observations'][0]['caller_composition'])
        self.assertIn((6,-20),proof['observations'][0]['incoming_aliases'])
        self.assertFalse(proof['numeric_equivalence_claim'])

    def test_actual_consumer_may_not_read_returned_private_pointer(self):
        with self.assertRaisesRegex(ValueError,'observes discarded'):
            owner.verify(**caller_fixture(after='101c'),objects=b'{}',selector=dynamic.SELECTOR)

    def test_dynamic_profile_cannot_assume_pointer_operands_are_scalar(self):
        with self.assertRaisesRegex(ValueError,'scalar operands'):
            owner.verify(**caller_fixture(before='6846'),objects=b'{}',selector=dynamic.SELECTOR)

    def test_existing_positive_constant_selector_remains_strict(self):
        with self.assertRaisesRegex(ValueError,'positive-constant'):
            owner.verify(**caller_fixture(),objects=b'{}',selector=dynamic.three.SELECTOR)

    def test_arbitrary_runtime_scratch_is_preserved_on_real_zero_path(self):
        x=inputs();programs={}
        for a,data in ((dynamic.DIV,actual.DIV),(dynamic.ZERO,actual.ZERO)):
            ins,edges,branches,calls,words=graph.graph(data,a,owner.refine(data,a,x['mapping']))
            programs[a]=ins,edges,calls
        entry=tuple(dynamic.SCALAR if n<2 else ('entry',n) for n in range(13))+(('local',0),dynamic.RETURN)
        result=dynamic.OriginReplay(programs).run(dynamic.DIV,entry)
        zero=[values for site,values in result if site==0x08142748]
        self.assertTrue(zero)
        self.assertTrue(all(v[2]==('entry',2) and v[3]==('entry',3) and v[12]==('entry',12) for v in zero))
        self.assertTrue(all(v[6]==('entry',6) for _,v in result))

    def test_return_address_origin_cannot_be_read_as_scalar(self):
        with self.assertRaisesRegex(ValueError,'returned control origin'):
            owner.verify(**caller_fixture(after='081c'),objects=b'{}',selector=dynamic.SELECTOR)

    def test_return_address_origin_requires_a_kill_before_root_return(self):
        x=caller_fixture()
        # Keep ordinary caller restore valid while its return uses POP PC,
        # leaving the helper's control-origin R1 unoverwritten.
        old=x['data'];new=old[:-4]+bytes.fromhex('00bd')
        rom=bytearray(x['rom']);start=x['address']-dynamic.match.ROM_BASE
        rom[start:start+len(old)]=new+b'\0\0'
        rows=json.loads(x['mapping']);row=next(r for r in rows if int(r['rom'],16)==x['address'])
        row['end']=f'0x{x["address"]+len(new):08X}';row['instrs']-=1
        x.update(data=new,rom=bytes(rom),mapping=json.dumps(rows).encode(),index=x['index'].replace(
            f'{x["address"]:08X} {x["address"]+len(old):08X} {len(old)} {row["instrs"]+1}'.encode(),
            f'{x["address"]:08X} {x["address"]+len(new):08X} {len(new)} {row["instrs"]}'.encode()))
        with self.assertRaisesRegex(ValueError,'before overwrite'):
            owner.verify(**x,objects=b'{}',selector=dynamic.SELECTOR)

    def test_actual_callee_cannot_gain_an_external_load(self):
        data=bytearray(actual.CALLEE);data[0x0809D6CC-A:0x0809D6CE-A]=bytes.fromhex('0268')
        with self.assertRaisesRegex(ValueError,'memory base'):
            dynamic.prove(**inputs(callee=bytes(data)),selector=dynamic.SELECTOR)

    def test_actual_entry_scratch_must_die_before_numeric_use(self):
        data=bytearray(actual.CALLEE);data[0x0809D6CC-A:0x0809D6CE-A]=bytes.fromhex('121c')
        with self.assertRaisesRegex(ValueError,'opaque'):
            dynamic.prove(**inputs(callee=bytes(data)),selector=dynamic.SELECTOR)

    def test_actual_local_write_cannot_be_removed_before_read(self):
        data=bytearray(actual.CALLEE);data[0x0809D756-A:0x0809D758-A]=bytes.fromhex('0020')
        with self.assertRaisesRegex(ValueError,'uninitialized'):
            dynamic.prove(**inputs(callee=bytes(data)),selector=dynamic.SELECTOR)

    def test_other_call_target_cannot_borrow_canonical_division_effects(self):
        data=bytearray(actual.CALLEE);site=0x0809D6F4;delta=dynamic.ZERO-(site+4)
        data[site-A:site-A+4]=(0xF000|((delta>>12)&0x7FF)).to_bytes(2,'little')+(0xF800|((delta>>1)&0x7FF)).to_bytes(2,'little')
        with self.assertRaisesRegex(ValueError,'DIV-only'):
            dynamic.prove(**inputs(callee=bytes(data)),selector=dynamic.SELECTOR)

    def test_complete_frame_bound_includes_actual_runtime_frame(self):
        proof=dynamic.prove(**inputs(),selector=dynamic.SELECTOR)
        self.assertEqual(proof['frame']['maximum_frame_bytes'],28)
        self.assertEqual(proof['maximum_additional_stack_bytes'],32)


if __name__=='__main__':
    unittest.main()
