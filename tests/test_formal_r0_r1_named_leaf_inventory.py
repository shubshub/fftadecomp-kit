"""Strict formal outputs and byte partition tests for the six-instruction leaf."""
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
import formal_r0_r1_named_leaf_inventory as profile

A = 0x08010000
WORDS = [0x4B02,0x8C9A,0x8002,0x8CD8,0x8008,0x4770,0x7F40,0x0200]


def inputs(words=WORDS):
    data = struct.pack('<8H',*words)
    rows = [dict(rom=f'0x{A:08X}',end=f'0x{A+16:08X}',mode='thumb',instrs=6)]
    return dict(data=data,address=A,rom=b'\0'*(A-profile.parent.match.ROM_BASE)+data,
        mapping=json.dumps(rows).encode(),index=f'{A:08X} {A+16:08X} 16 6 return\n'.encode(),
        data_mapping=json.dumps({profile.named.NAME:f'0x{profile.named.GLOBAL:08X}'}).encode(),
        selector=profile.SELECTOR,readonly_named_buffer_policy=profile.second.second_named_policy(),
        formal_output_policy=profile.output_policy())


class FormalR0R1NamedLeafTests(unittest.TestCase):
    def test_original_identity_pin_matches_the_same_machine_bytes(self):
        self.assertEqual(profile.IDENTITY[:3],(0x0801E6F0,0x0801E700,6))
        self.assertEqual(profile.IDENTITY[3],profile.sha(struct.pack('<8H',*WORDS)))

    def native(self,values=None,**changes):
        values = inputs() if values is None else dict(values)
        values.update(changes)
        identity = (A,A+16,6,profile.sha(values['data']))
        with patch.object(profile,'IDENTITY',identity):
            return profile.verify(**values)

    def test_full_API_CLI_actual_partition_origins_frame_and_claim_limits(self):
        values = inputs()
        result,instructions = self.native(values)
        self.assertEqual(len(instructions),6)
        self.assertEqual(result['partition']['code_bytes'],12)
        self.assertEqual(result['partition']['literal_and_table_bytes'],4)
        self.assertEqual(result['partition']['alignment_bytes'],0)
        self.assertEqual(result['frame']['maximum_frame_bytes'],0)
        self.assertEqual(result['effects']['writes'],[[0,0,2],[1,0,2]])
        self.assertEqual([row[2:4] for row in result['effects']['named_reads']],[[36,2],[38,2]])
        self.assertEqual(result['effects']['store_event_count'],2)
        self.assertFalse(result['caller_pointer_discharge'])
        self.assertFalse(result['source_or_ELF_admission'])
        self.assertFalse(result['memory_safety_claim'])
        self.assertEqual(result['numeric_return_facts'],[])
        self.assertEqual(self.native(values,manifest=result)[0],result)
        root = Path(os.environ['FFTA_R0_R1_LEAF_RETAIN'])
        root.mkdir(parents=True,exist_ok=True)
        names = {'rom':'rom.bin','mapping':'functions.json','index':'functions.txt','data_mapping':'data_symbols.json'}
        for key,name in names.items():
            (root/name).write_bytes(values[key])
        (root/'api.json').write_text(json.dumps(result,indent=2)+'\n')
        code = ('import sys;sys.path.insert(0,sys.argv.pop(1));'
                'import formal_r0_r1_named_leaf_inventory as p;'
                f'p.IDENTITY={(A,A+16,6,profile.sha(values["data"]))!r};p.main()')
        command = [sys.executable,'-c',code,str(Path(profile.__file__).parent),'--profile',profile.SELECTOR]
        for key,name in names.items():
            command += ['--'+key.replace('_','-'),str(root/name)]
        command += ['--readonly-named-buffer-policy',profile.text(values['readonly_named_buffer_policy']),
                    '--formal-output-policy',profile.text(values['formal_output_policy'])]
        run = subprocess.run(command,capture_output=True,text=True)
        (root/'cli-stderr.txt').write_text(run.stderr)
        (root/'cli.json').write_text(run.stdout)
        self.assertEqual(run.returncode,0,run.stderr)
        self.assertEqual(json.loads(run.stdout),result)

    def test_exact_explicit_selector_named_and_formal_premises(self):
        for selector in (None,True,profile.second.SELECTOR):
            with self.subTest(selector=selector),self.assertRaises(ValueError):self.native(selector=selector)
        policy = profile.output_policy()
        for value in (None,{},True,dict(policy,writes=[[False,0,2],[1,0,2]]),
                      dict(policy,writes=[[0,0,4],[1,0,2]]),dict(policy,writable=True)):
            with self.subTest(output=value),self.assertRaises(ValueError):self.native(formal_output_policy=value)
        for value in (None,{},dict(profile.second.second_named_policy(),initialized=False)):
            with self.subTest(named=value),self.assertRaises(ValueError):self.native(readonly_named_buffer_policy=value)

    def test_formal_base_offset_width_and_scalar_source(self):
        for replacement in (0x800A,0x8042,0x7002,0x8000):
            words = list(WORDS);words[2] = replacement
            with self.subTest(replacement=replacement),self.assertRaises(ValueError):self.native(inputs(words))

    def test_named_read_width_offset_and_named_write(self):
        for position,replacement in ((1,0x8C5A),(1,0x7C9A),(2,0x801A)):
            words = list(WORDS);words[position] = replacement
            with self.subTest(position=position,replacement=replacement),self.assertRaises(ValueError):
                self.native(inputs(words))

    def test_exact_named_binding_and_literal_ownership(self):
        for mapping in (b'{}',b'{"g_state_02007F40":"0x02007F42"}',
                        b'{"g_state_02007F40":"0x02007F40","g_state_02007F40":"0x02007F40"}'):
            with self.subTest(mapping=mapping),self.assertRaises(ValueError):self.native(data_mapping=mapping)
        words = list(WORDS);words[6] += 4
        with self.assertRaises(ValueError):self.native(inputs(words))

    def test_identity_dual_index_count_extent_and_exact_ROM_bytes(self):
        values = inputs()
        for field,data in [('index',values['index'].replace(b'16 6 return',b'16 8 return')),
                           ('mapping',values['mapping'].replace(b'"instrs": 6',b'"instrs": 8')),
                           ('rom',values['rom'][:-1]+b'\x03')]:
            with self.subTest(field=field),self.assertRaises(ValueError):self.native(values,**{field:data})
        with patch.object(profile,'IDENTITY',(A,A+16,6,'0'*64)),self.assertRaises(ValueError):
            profile.verify(**values)
        rows = json.loads(values['mapping']);rows.append(copy.deepcopy(rows[0]))
        with self.assertRaises(ValueError):self.native(values,mapping=json.dumps(rows).encode())

    def test_return_and_call_free_cfg_remain_strict(self):
        for position,replacement in ((5,0x4700),(5,0xE7FE),(3,0xF000),(4,0xF800)):
            words = list(WORDS);words[position] = replacement
            with self.subTest(position=position,replacement=replacement),self.assertRaises(ValueError):
                self.native(inputs(words))

    def test_manifest_cannot_add_claims_or_rewrite_observed_effects(self):
        result,_ = self.native()
        for changed in (dict(result,caller_pointer_discharge=True),dict(result,memory_safety_claim=True),
                        dict(result,effects={})):
            with self.subTest(changed=changed.keys()),self.assertRaises(ValueError):self.native(manifest=changed)


if __name__ == '__main__':
    unittest.main()
