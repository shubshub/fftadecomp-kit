"""Natural compiler switch callees and context-specific watched alias proofs."""
import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import shutil
import struct
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'tools'))
import match
import match_evidence
import owner_admission_profile as owner
import owner_graph_profile as graph
import watched_switch_preservation_profile as profile
import function_thunk_profile as thunk
from test_protected_descriptor_word import SOURCE

WORKER = '''struct Descriptor { unsigned char *bytes; void (*callback)(unsigned char *); };
extern unsigned int func_08013000(unsigned int);
void func_08011000(struct Descriptor *descriptor)
{
    func_08013000(0);
    descriptor->callback(descriptor->bytes);
}
'''

A, B, C, D = 0x08010000, 0x08011000, 0x08012000, 0x08013000
LEAF = '''void func_08012000(unsigned char *bytes) { bytes[0] += 1; }
'''
SWITCH = '''unsigned int func_08013000(unsigned int value)
{
    switch (value) {
    case 0: return 17;
    case 1: return 4;
    case 2: return 29;
    case 3: return 8;
    case 4: return 61;
    case 5: return 3;
    case 6: return 42;
    case 7: return 11;
    default: return 0;
    }
}
'''


def fixture(root):
    root = Path(root)
    for name in ('src', 'include', 'config', 'symbols', 'build', 'original-elf'):
        (root/name).mkdir(parents=True, exist_ok=True)
    args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP,
        assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY,
        linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
    sources = {A: SOURCE, B: WORKER, C: LEAF, D: SWITCH}
    images, raw = {}, {}
    runner = match.Runner(match.DEFAULT_CC, 'Ubuntu', match.DEFAULT_WSL_PATH, root=root, timeout=120)
    with runner.workspace() as workspace:
        for address, source in sources.items():
            path = root/f'src/{address:08X}.c'; path.write_text(source)
            raw[address], _, images[address] = match.compile_object(runner, workspace, args,
                root, address, path.relative_to(root).as_posix())
            (root/f'original-elf/{address:08X}.o').write_bytes(raw[address])
            (root/f'original-elf/{address:08X}.s').write_bytes(runner.read_binary(workspace+'/f.s'))
            (root/f'original-elf/{address:08X}.c').write_text(source)
            if address != A: path.unlink()
        sizes = {address: match.function_record(image,f'func_{address:08X}',address,True)[0]['size']
                 for address,image in images.items()}
        rows = [{'rom': f'0x{address:08X}', 'end': f'0x{address+sizes[address]:08X}',
                 'mode': 'thumb', 'instrs': 0} for address, image in images.items()]
        rows += [{'rom':f'0x{address:08X}', 'end':f'0x{address+2:08X}',
                  'mode':'thumb','instrs':1} for address in thunk.ALIASES.values()]
        mapping = json.dumps(rows).encode()
        rom = bytearray(thunk.END-match.ROM_BASE)
        for register in range(13):
            struct.pack_into('<HH',rom,thunk.START-match.ROM_BASE+4*register,
                             0x4700+(register<<3),0x46c0)
        for address in (C, D, B, A):
            path = root/f'src/{address:08X}.c'; path.write_text(sources[address])
            original, _, image = match.compile_object(runner, workspace, args, root, address,
                path.relative_to(root).as_posix())
            assert original == raw[address]
            if address != A: path.unlink()
            if address == D:
                # Native placement of the unchanged switch ET_REL, retaining the
                # exact function extent separately from section tail alignment.
                runner.sh(f'{args.linker} --no-undefined --no-relax -Ttext=0x{D:08X} '
                          f'-e func_{D:08X} {workspace}/f.o -o {workspace}/f.elf')
                linked = match.elf_image(runner.read_binary(workspace+'/f.elf'))
                assert not linked['relocations']
                size = match.function_record(linked,f'func_{D:08X}',D,True)[0]['size']
                body = linked['text'][:size]
            elif address == B:
                body, _, _, _ = thunk.object_bytes(runner,workspace,args,images[address],
                    address,mapping,bytes(rom),b'{}')
            elif address == C:
                body = images[address]['text'][:match.function_record(images[address],
                    f'func_{address:08X}',address,True)[0]['size']]
            else:
                body, bindings = owner.object_bytes(runner, workspace, args, images[address],
                    address, bytes(rom), mapping, b'{}', selector=profile.SELECTOR)
            rom[address-match.ROM_BASE:address-match.ROM_BASE+len(body)] = body
            next(row for row in rows if int(row['rom'], 16)==address)['instrs'] = \
                owner.refine(body, address, mapping)['instrs']
    for name, data in (('config/functions.json', json.dumps(rows, indent=2).encode()),
            ('symbols/functions.txt', ''.join(f'{int(row["rom"],16):08X} {int(row["end"],16):08X} '
                f'{int(row["end"],16)-int(row["rom"],16)} {row["instrs"]} return\n' for row in rows).encode()),
            ('config/data_symbols.json', b'{}'), ('baserom.bin', bytes(rom))):
        (root/name).write_bytes(data)
    return bytes(rom[A-match.ROM_BASE:A-match.ROM_BASE+len(images[A]['text'])]), bindings, raw[A]


class SelectionTests(unittest.TestCase):
    def test_isolated_schema_and_mixed_markers(self):
        marker = f'* verification: `{profile.SCHEMA}`\n'
        self.assertEqual(owner.selector_for_report(marker), profile.SELECTOR)
        for report in (marker*2, marker+f'* verification: `{owner.descriptor.SCHEMA}`\n'):
            with self.assertRaises(ValueError): owner.selected(report)


@unittest.skipUnless(os.environ.get('FFTA_WATCHED_SWITCH_TEST_ROM'), 'explicit approved original ROM required')
class OriginalTests(unittest.TestCase):
    def test_exact_original_complete_switch_preserves_watched_r6(self):
        rom = Path(os.environ['FFTA_WATCHED_SWITCH_TEST_ROM']).read_bytes()
        self.assertEqual(hashlib.sha256(rom).hexdigest(),
            '43fc8204c6dceee58828aebc7af0c72eb807e99f35ad641c8bb0a4fa8b6edc19')
        address, size = 0x080CCD50, 272
        body = rom[address-match.ROM_BASE:address-match.ROM_BASE+size]
        mapping = json.dumps([{'rom':f'0x{address:08X}', 'end':f'0x{address+size:08X}',
                               'mode':'thumb','instrs':63}]).encode()
        index = f'{address:08X} {address+size:08X} {size} 63 return\n'.encode()
        proof = profile.WatchedSwitchPreservationProof(rom,mapping,index,b'{}')
        result = proof.check_arguments(address,{},[(False,False,True)],{},frozenset(),
            words={-4:('constant',7)},frame_base=-4,root_frame=A,watched=(match.ARM_REG_R0+6,))
        self.assertEqual(dict(result.words),{-4:('constant',7)})
        structure = proof.records[address]['structure']
        self.assertEqual(structure['instructions'],63)
        self.assertEqual(structure['cases'],34)
        self.assertEqual(structure['partition'],dict(code_bytes=126,literal_and_table_bytes=144,alignment_bytes=2))


@unittest.skipUnless(Path(os.path.expandvars(match.DEFAULT_CC)).is_file() and
                     shutil.which('arm-none-eabi-ld'), 'fixed original compiler required')
class NativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        scratch = Path(os.environ.get('TMPDIR', Path.cwd()/'build/tests')); scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix='watched_switch_', dir=scratch)
        cls.root = Path(cls.temporary.name)
        cls.data, cls.bindings, cls.original = fixture(cls.root)
        cls.environment = patch.dict(os.environ, FFTA_ROM=str(cls.root/'baserom.bin')); cls.environment.start()
        cls.result = owner.build(cls.root, A, selector=profile.SELECTOR)
        cls.report = owner.render(A, cls.result)

    @classmethod
    def tearDownClass(cls):
        cls.environment.stop(); cls.temporary.cleanup()

    def proof(self, rom=None):
        r = self.result
        return profile.WatchedSwitchPreservationProof(r[6] if rom is None else rom, r[3], r[4], r[5])

    def switch(self):
        proof = self.proof(); body = proof.span(D)
        refinement = owner.refine(body, D, proof.mapping)
        ins, _, _, _, words = graph.graph(body, D, refinement)
        return body, ins, words, match.switch_layout(body, D, words)

    def check(self, proof, watched=(match.ARM_REG_R0+4), **changes):
        values = dict(arguments={}, stack=[(False,False,True)]*3, incoming={}, protected=frozenset(),
            constants={}, words={-12:('pointer',-4)}, frame_base=-12, root_frame=A,
            watched=(watched,), site=A+8)
        values.update(changes)
        return proof.check_arguments(D, **values)

    def test_natural_original_elf_and_every_finite_case(self):
        self.assertEqual(self.result[8], self.original)
        self.assertEqual(match.elf_image(self.original)['type'], 1)
        buffers = self.result[1]['proof']['buffers']
        switch = next(row for row in buffers['dependencies'] if row['address']==D)
        self.assertEqual(switch['structure']['cases'], 8)
        self.assertTrue(buffers['switch_contexts'])
        self.assertEqual(dict(self.check(self.proof()).words), {-12:('pointer',-4)})
        self.assertTrue(match_evidence.report_matches(self.report, self.root, A))

    def test_old_selector_still_refuses_mov_pc(self):
        with self.assertRaisesRegex(ValueError, 'unresolved|unsupported'):
            owner.verify(self.data, A, self.result[6], self.result[3], self.result[4], self.result[5],
                bindings=self.bindings, selector=owner.descriptor.SELECTOR)

    def test_two_contexts_cannot_reuse_preservation(self):
        proof = self.proof(); self.check(proof)
        with self.assertRaisesRegex(ValueError, 'preservation of a live alias register'):
            self.check(proof, match.ARM_REG_R0)
        self.assertGreaterEqual(len(proof.contexts), 2)

    def test_case_clobber_is_checked_even_when_selector_is_known(self):
        body, _, words, layout = self.switch(); rom = bytearray(self.result[6])
        target = next(value for offset,value in sorted(words.items()) if offset!=layout['literal'])
        rom[D-match.ROM_BASE+target:D-match.ROM_BASE+target+2] = bytes.fromhex('0024')
        with self.assertRaisesRegex(ValueError, 'preservation of a live alias register'):
            self.check(self.proof(bytes(rom)), constants={match.ARM_REG_R0:7})

    def test_unknown_write_is_refused(self):
        _, _, words, layout = self.switch()
        target = next(value for offset,value in sorted(words.items()) if offset!=layout['literal'])
        rom = bytearray(self.result[6])
        rom[D-match.ROM_BASE+target:D-match.ROM_BASE+target+2] = bytes.fromhex('0860')
        with self.assertRaisesRegex(ValueError, 'read-only narrow Thumb effects'):
            self.check(self.proof(bytes(rom)))

    def test_unpassed_watched_alias_cannot_be_read_or_returned(self):
        _, _, words, layout = self.switch()
        target = next(value for offset,value in sorted(words.items()) if offset!=layout['literal'])
        rom = bytearray(self.result[6])
        # mov r0,r4 would preserve r4 while returning its caller-held pointer.
        rom[D-match.ROM_BASE+target:D-match.ROM_BASE+target+2] = bytes.fromhex('2046')
        with self.assertRaisesRegex(ValueError, 'cannot read an unpassed live alias'):
            self.check(self.proof(bytes(rom)))

    def test_escaped_table_target_and_unproved_guard_refuse(self):
        _, _, _, layout = self.switch()
        for offset, encoded in ((layout['table'], struct.pack('<I',D+4096)),
                                (layout['guard'], bytes.fromhex('c046')),
                                (layout['dispatch']+8, bytes.fromhex('9746'))):
            rom = bytearray(self.result[6]); rom[D-match.ROM_BASE+offset:D-match.ROM_BASE+offset+len(encoded)] = encoded
            with self.subTest(offset=offset), self.assertRaises(ValueError):self.check(self.proof(bytes(rom)))

    def test_budget_metadata_and_fresh_manifest_refusals(self):
        proof = self.proof(); proof.requested.update(range(profile.MAX_DEPENDENCIES))
        with self.assertRaisesRegex(ValueError, 'dependency budget'):proof.span(D)
        rows = json.loads(self.result[3]); rows.append(next(row for row in rows if int(row['rom'],16)==D))
        proof = profile.WatchedSwitchPreservationProof(self.result[6],json.dumps(rows).encode(),self.result[4],b'{}')
        with self.assertRaises(ValueError):self.check(proof)
        manifest = copy.deepcopy(self.result[1]); manifest['proof']['buffers']['switch_contexts'] = []
        with self.assertRaisesRegex(ValueError, 'fresh native replay'):
            owner.verify(self.data,A,self.result[6],self.result[3],self.result[4],self.result[5],
                         manifest=manifest,selector=profile.SELECTOR)
        path = self.root/'src/08010000.c'; raw = path.read_bytes()
        try:
            path.write_bytes(raw+b'\n'); self.assertFalse(match_evidence.report_matches(self.report,self.root,A))
        finally:path.write_bytes(raw)


if __name__=='__main__': unittest.main(verbosity=2)
