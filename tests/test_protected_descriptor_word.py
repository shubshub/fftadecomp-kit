"""Natural C descriptor words, nested callback effects and exact fact contexts."""
import copy
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import match
import match_evidence
import owner_admission_profile as owner
import protected_descriptor_word_profile as words
import test_static_callback_buffer as fixtures
from test_static_callback_buffer import A,B,C,D,fixture as callback_fixture

SOURCE = '''struct Descriptor { unsigned char *bytes; void (*callback)(unsigned char *); };
extern void func_08011000(struct Descriptor *);
extern void func_08012000(unsigned char *);
unsigned int func_08010000(unsigned int value)
{
    unsigned char bytes[4];
    struct Descriptor descriptor;
    bytes[0] = value;
    descriptor.bytes = bytes;
    descriptor.callback = func_08012000;
    func_08011000(&descriptor);
    return bytes[0];
}
'''
WORKER = '''struct Descriptor { unsigned char *bytes; void (*callback)(unsigned char *); };
void func_08011000(struct Descriptor *descriptor)
{
    descriptor->callback(descriptor->bytes);
}
'''


def fixture(root, source=SOURCE, worker=WORKER):
    # The common helper uses original ET_REL linking before any semantic proof.
    return callback_fixture(root,source=source,worker=worker)


class SelectionTests(unittest.TestCase):
    def test_explicit_schema(self):
        marker=f'* verification: `{words.SCHEMA}`\n'
        self.assertEqual(owner.selector_for_report(marker),words.SELECTOR)
        for report in (marker*2,marker+f'* verification: `{owner.static_buffer.SCHEMA}`\n'):
            with self.assertRaises(ValueError):owner.selected(report)


@unittest.skipUnless(Path(os.path.expandvars(match.DEFAULT_CC)).is_file() and
                     shutil.which('arm-none-eabi-ld'), 'fixed original compiler required')
class NativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        scratch=Path(os.environ.get('TMPDIR',Path.cwd()/'build/tests'));scratch.mkdir(parents=True,exist_ok=True)
        cls.temporary=tempfile.TemporaryDirectory(prefix='descriptor_word_',dir=scratch)
        cls.root=Path(cls.temporary.name)
        cls.data,cls.bindings,cls.original=fixture(cls.root)
        cls.environment=patch.dict(os.environ,FFTA_ROM=str(cls.root/'baserom.bin'));cls.environment.start()
        cls.result=owner.build(cls.root,A,selector=words.SELECTOR)
        cls.report=owner.render(A,cls.result)

    @classmethod
    def tearDownClass(cls):
        cls.environment.stop();cls.temporary.cleanup()

    def replay(self,**changes):
        r=self.result
        values=dict(data=r[0],address=A,rom=r[6],mapping=r[3],index=r[4],objects=r[5],
                    manifest=r[1],selector=words.SELECTOR);values.update(changes)
        return owner.verify(**values)

    def proof(self):
        r=self.result
        return words.ProtectedDescriptorWordProof(r[6],r[3],r[4],r[5])

    def test_natural_original_elf_pointer_and_function_words(self):
        self.assertEqual(self.result[8],self.original)
        self.assertEqual(match.elf_image(self.original)['type'],1)
        observations=self.result[1]['proof']['buffers']['word_reads']
        self.assertEqual({row['kind'] for row in observations},{'pointer','constant'})
        self.assertTrue(any(row['value']==C+1 for row in observations))
        self.assertTrue(self.replay())

    def test_old_callback_selector_still_refuses_descriptor(self):
        with self.assertRaisesRegex(ValueError,'pointer-bearing argument slot'):
            self.replay(selector=owner.static_buffer.SELECTOR,manifest=None,bindings=self.bindings)

    def test_two_contexts_different_stored_callback_cannot_share_effects(self):
        proof=self.proof();stack=[(False,False,True)]*3
        kwargs=dict(arguments={match.ARM_REG_R0:-12},stack=stack,incoming={},protected=frozenset({-12}),
                    frame_base=-12,root_frame=A,constants={})
        proof.check_arguments(B,words={-12:('pointer',-4),-8:('constant',C+1)},**kwargs)
        with self.assertRaisesRegex(ValueError,'outside allocated local words'):
            proof.check_arguments(B,words={-12:('pointer',-4),-8:('constant',D+1)},**kwargs)
        self.assertEqual({row['target'] for row in proof.observations()},{C,D})

    def test_lost_missing_partial_and_saved_control_word_refuse(self):
        proof=self.proof();stack=[(False,False,True)]*3
        decoder=match.Cs(match.CS_ARCH_ARM,match.CS_MODE_THUMB);decoder.detail=True
        ldr=next(decoder.disasm(b'\x01\x68',B))  # ldr r1, [r0]
        byte=next(decoder.disasm(b'\x01\x78',B))
        args={match.ARM_REG_R0:-12}
        for ins,facts,frame in ((ldr,{},stack),(byte,{-12:('pointer',-4)},stack),
                (ldr,{-12:('pointer',-4)},[(True,True,False)]+stack[1:])):
            with self.subTest(instruction=ins.mnemonic),self.assertRaises(ValueError):
                proof.word_memory(ins,args,{},frame,dict(facts),-12,frozenset({-12}))

    def test_unknown_base_write_kills_all_word_facts(self):
        proof=self.proof();decoder=match.Cs(match.CS_ARCH_ARM,match.CS_MODE_THUMB);decoder.detail=True
        store=next(decoder.disasm(b'\x08\x60',B))  # str r0, [r1], unproved base
        facts={-12:('pointer',-4),-8:('constant',C+1)}
        proof.word_memory(store,{}, {},[(False,False,True)]*3,facts,-12,frozenset({-12}))
        self.assertEqual(facts,{})
        load=next(decoder.disasm(b'\x01\x68',B))
        with self.assertRaisesRegex(ValueError,'exact surviving word value'):
            proof.word_memory(load,{match.ARM_REG_R0:-12},{},[(False,False,True)]*3,
                              facts,-12,frozenset({-12}))

    def test_identical_word_value_survives_both_conditional_paths(self):
        worker='''struct Descriptor { unsigned char *bytes; void (*callback)(unsigned char *); };
extern void func_08012000(unsigned char *);
void func_08011000(struct Descriptor *descriptor)
{
    if (descriptor->bytes[0]) descriptor->callback = func_08012000;
    descriptor->callback(descriptor->bytes);
}
'''
        root=self.root/'equal-join';fixture(root,worker=worker)
        with patch.dict(os.environ,FFTA_ROM=str(root/'baserom.bin')):
            result=owner.build(root,A,selector=words.SELECTOR)
        self.assertEqual({row['target'] for row in result[1]['proof']['buffers']['callbacks']},{C})

    def test_nested_read_only_call_proves_register_and_word_preservation(self):
        worker='''struct Descriptor { unsigned char *bytes; void (*callback)(unsigned char *); };
extern unsigned int func_08013000(unsigned int);
void func_08011000(struct Descriptor *descriptor)
{
    func_08013000(0);
    descriptor->callback(descriptor->bytes);
}
'''
        helper='''unsigned int func_08013000(unsigned int value) { return value + 1; }
'''
        root=self.root/'nested-readonly'
        with patch.object(fixtures,'BAD',helper):fixture(root,worker=worker)
        with patch.dict(os.environ,FFTA_ROM=str(root/'baserom.bin')):
            result=owner.build(root,A,selector=words.SELECTOR)
        self.assertIn(D,{row['address'] for row in result[1]['proof']['buffers']['dependencies']})
        self.assertTrue(any(row['watched'] for row in result[1]['proof']['buffers']['callbacks']))

    def test_nested_possible_clobber_and_conditional_callback_word_refuse(self):
        cases=(
            ('''struct Descriptor { unsigned char *bytes; void (*callback)(unsigned char *); };
extern unsigned int func_08013000(unsigned int);
void func_08011000(struct Descriptor *descriptor)
{
    func_08013000(0);
    descriptor->callback(descriptor->bytes);
}
''', '''unsigned int func_08013000(unsigned int value)
{ *(unsigned char *)value = 1; return value; }
'''),
            ('''struct Descriptor { unsigned char *bytes; void (*callback)(unsigned char *); };
extern void func_08013000(unsigned char *);
void func_08011000(struct Descriptor *descriptor)
{
    if (descriptor->bytes[0]) descriptor->callback = func_08013000;
    descriptor->callback(descriptor->bytes);
}
''',fixtures.BAD))
        for number,(worker,helper) in enumerate(cases):
            root=self.root/f'clobber-{number}'
            with patch.object(fixtures,'BAD',helper):data,bindings,_=fixture(root,worker=worker)
            with self.subTest(number=number),self.assertRaises(ValueError):
                owner.verify(data,A,(root/'baserom.bin').read_bytes(),
                    (root/'config/functions.json').read_bytes(),(root/'symbols/functions.txt').read_bytes(),
                    b'{}',bindings=bindings,selector=words.SELECTOR)

    def test_deallocation_reallocation_never_restores_word_facts(self):
        proof=self.proof();facts={-4:('constant',C+1)}
        proof.prune_words(facts,[]);self.assertEqual(facts,{})
        proof.prune_words(facts,[(False,False,True)]);self.assertEqual(facts,{})
        data=bytes.fromhex('00b581b001b081b001b001bc0047')
        decoder=match.Cs(match.CS_ARCH_ARM,match.CS_MODE_THUMB);decoder.detail=True
        with self.assertRaisesRegex(ValueError,'allocation after deallocation'):
            proof.check_lifetime(data,B,list(decoder.disasm(data,B)))

    def test_actual_unpreserved_alias_register_is_not_trusted(self):
        proof=self.proof();rom=bytearray(self.result[6]);rows=json.loads(self.result[3])
        # Generic malformed ABI callee, independently bounded and mapped.
        rom[D-match.ROM_BASE:D-match.ROM_BASE+4]=bytes.fromhex('00247047')
        row=next(row for row in rows if int(row['rom'],16)==D)
        row.update(end=f'0x{D+4:08X}',instrs=2)
        index=''.join(f'{int(row["rom"],16):08X} {int(row["end"],16):08X} '
                      f'{int(row["end"],16)-int(row["rom"],16)} {row["instrs"]} return\n'for row in rows).encode()
        proof=words.ProtectedDescriptorWordProof(bytes(rom),json.dumps(rows).encode(),index,b'{}')
        with self.assertRaisesRegex(ValueError,'preservation of a live alias register'):
            proof.check_arguments(D,{},[(False,False,True)]*3,{},frozenset(),
                words={-12:('pointer',-4)},frame_base=-12,root_frame=A,
                watched=(match.ARM_REG_R0+4,))

    def test_report_binds_word_values_and_lifetime_context(self):
        for field in ('word_reads','callbacks'):
            manifest=copy.deepcopy(self.result[1]);manifest['proof']['buffers'][field]=[]
            with self.assertRaisesRegex(ValueError,'fresh native replay'):self.replay(manifest=manifest)
        self.assertTrue(match_evidence.report_matches(self.report,self.root,A))
        path=self.root/'src/08010000.c';raw=path.read_bytes()
        try:
            path.write_bytes(raw+b'\n');self.assertFalse(match_evidence.report_matches(self.report,self.root,A))
        finally:path.write_bytes(raw)


if __name__=='__main__':unittest.main(verbosity=2)
