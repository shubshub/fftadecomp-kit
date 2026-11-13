"""The selective-scratch nested profile retains observed R2/R3 aliases; the old selector still refuses."""
import copy
import json
import subprocess
import unittest
from unittest.mock import patch

import test_nested_formal_output_buffer as base

nested = base.nested
match = base.match
A = base.A
CALLER = 0x08010200


class NestedSelectiveScratchTests(unittest.TestCase):
    setUp = base.NestedOutputTests.setUp
    fixture = base.NestedOutputTests.fixture

    def owner_inputs(self, body, helper='bx lr'):
        inputs, identities = self.fixture()
        context = patch.multiple(nested, **identities)
        context.start()
        self.addCleanup(context.stop)
        (self.root/'helpers.bin').write_bytes(inputs['rom'][A-match.ROM_BASE:])
        (self.root/'caller.s').write_text('.syntax unified\n.arch armv4t\n.thumb\n.text\n'
            '.incbin "' + str(self.root/'helpers.bin') + '"\n.org 0x200\n'
            '.global func_08010200, caller_end\n.thumb_func\nfunc_08010200:\n' + body +
            '\ncaller_end:\n.thumb_set wrapper, func_08010200-0x100\n'
            '.org 0x300\n.global helper, helper_end\n.thumb_func\nhelper:\n' + helper + '\nhelper_end:\n')
        for command in (
            ['arm-none-eabi-as', '-mthumb-interwork', str(self.root/'caller.s'), '-o', str(self.root/'caller.o')],
            ['arm-none-eabi-ld', f'-Ttext=0x{A:08X}', '-e', 'func_08010200',
             str(self.root/'caller.o'), '-o', str(self.root/'caller.elf')],
        ):
            subprocess.run(command, check=True, capture_output=True)
        image = match.elf_image((self.root/'caller.elf').read_bytes())
        end = next(row['value'] for row in image['symbols'] if row['name'] == 'caller_end')
        raw = image['text'][CALLER-A:end-A]
        symbols = {row['name']: row['value'] for row in image['symbols']}
        helper, helper_end = symbols['helper'] & ~1, symbols['helper_end'] & ~1
        rom = b'\0'*(A-match.ROM_BASE) + image['text']
        rows = json.loads(inputs['mapping']) + [dict(rom=hex(CALLER), end=hex(end), mode='thumb', instrs=0),
                                                dict(rom=hex(helper), end=hex(helper_end), mode='thumb', instrs=1)]
        mapping = json.dumps(rows).encode()
        index = (inputs['index'] + f'{CALLER:08X} {end:08X} {len(raw)} 0 return\n'.encode() +
                 f'{helper:08X} {helper_end:08X} {helper_end-helper} 1 return\n'.encode())
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        bindings = dict(calls=[[i.address - CALLER, f'func_{i.operands[0].imm:08X}']
                               for i in decoder.disasm(raw, CALLER) if i.mnemonic == 'bl'],
                        data=[], functions=[], switches=[])
        return (raw, CALLER, rom, mapping, index, inputs['objects']), bindings, (self.root/'caller.o').read_bytes()

    PREFIX = 'push {lr}\nsub sp, #8\nmov r1, sp\nadd r2, sp, #4\nbl wrapper\nmov r3, sp\nbl helper\n'
    SUFFIX = '\nadd sp, #8\npop {r0}\nbx r0'
    SINGLE = PREFIX + 'movs r3, #0' + SUFFIX
    OBSERVED = PREFIX + 'bl helper' + SUFFIX

    def verify(self, body, selector, manifest=None, helper='bx lr'):
        args, bindings, _ = self.owner_inputs(body, helper)
        owner = base.leaf_fixtures.fixtures.owner
        return owner.verify(*args, *( (manifest,) if manifest else ()), bindings=bindings, selector=selector)

    def test_observed_scratch_is_refused_by_old_selector_and_retained_by_new(self):
        with self.assertRaisesRegex(ValueError, 'consumer observes discarded return scratch'):
            self.verify(self.OBSERVED, nested.SELECTOR)
        manifest, _ = self.verify(self.OBSERVED, nested.SELECTIVE_SELECTOR)
        self.assertEqual(manifest['profile'], nested.SELECTIVE_SCHEMA)
        scratch = manifest['proof']['buffers']['normal_return_scratch']
        self.assertEqual(scratch['selection'], 'each R2/R3 independently; observed aliases remain tracked')
        self.assertTrue(any(row['retained'] for row in scratch['observations']))

    def test_saved_lr_read_through_retained_alias_is_refused(self):
        # offset 8 is the saved-LR slot of the caller frame; the exact-type guard must cover this class
        for access in ('ldr r0, [r3, #8]', 'str r0, [r3, #8]'):
            with self.subTest(access=access), self.assertRaisesRegex(ValueError, 'access|escape|outside'):
                self.verify(self.PREFIX + access + '\nmovs r3, #0' + self.SUFFIX, nested.SELECTIVE_SELECTOR)
        self.verify(self.PREFIX + 'ldr r0, [r3, #4]\nmovs r3, #0' + self.SUFFIX, nested.SELECTIVE_SELECTOR)

    def test_unobserved_case_keeps_both_selectors_and_distinct_schemas(self):
        old, _ = self.verify(self.SINGLE, nested.SELECTOR)
        new, _ = self.verify(self.SINGLE, nested.SELECTIVE_SELECTOR)
        self.assertEqual(old['profile'], nested.SCHEMA)
        self.assertEqual(new['profile'], nested.SELECTIVE_SCHEMA)
        self.assertNotIn('selection', old['proof']['buffers']['normal_return_scratch'])

    def test_replay_tamper_and_report_selection(self):
        manifest, instructions = self.verify(self.OBSERVED, nested.SELECTIVE_SELECTOR)
        replay, _ = self.verify(self.OBSERVED, nested.SELECTIVE_SELECTOR, manifest)
        self.assertEqual(replay, manifest)
        for edit in (lambda m: m['proof']['buffers']['normal_return_scratch']['observations'][0].update(retained=[]),
                     lambda m: m['proof']['buffers']['nested_halfword_outputs']['calls'][0].update(writes_entry_SP_offsets=[])):
            forged = copy.deepcopy(manifest)
            edit(forged)
            with self.subTest(), self.assertRaisesRegex(ValueError, 'manifest differs'):
                self.verify(self.OBSERVED, nested.SELECTIVE_SELECTOR, forged)
        # a manifest of one selector never verifies under the other
        with self.assertRaises(ValueError):
            self.verify(self.SINGLE, nested.SELECTOR, self.verify(self.SINGLE, nested.SELECTIVE_SELECTOR)[0])
        args, bindings, obj = self.owner_inputs(self.OBSERVED)
        owner = base.leaf_fixtures.fixtures.owner
        report = owner.render(CALLER, (args[0], manifest, 'synthetic-source', args[3], args[4], args[5],
                                       args[2], len(instructions), obj))
        self.assertTrue(owner.selected(report))
        self.assertEqual(owner.selector_for_report(report), nested.SELECTIVE_SELECTOR)
        self.assertNotEqual(owner.selector_for_report(report), nested.SELECTOR)


if __name__ == '__main__':
    unittest.main(verbosity=2)
