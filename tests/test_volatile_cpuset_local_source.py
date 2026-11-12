"""Only authenticated local CpuSet fill reads may compare frame coordinates."""
import unittest
import json
import named_data_buffer_profile as buffers
import test_volatile_bios_interface as existing
import test_volatile_semantics as fixtures
import volatile_semantics as semantics
import bios_cpuset_fill_profile as bios


class LocalSourceTests(existing.BiosVolatileInterfaceTests):
    def interface(self, **changes):
        f = self.base.fixture()
        f.update(changes)
        return bios.ConditionalVolatileInterfaces(
            semantics.RomInterfaces(f['rom'], json.loads(f['mapping'])),
            f['data'], f['address'], f['rom'], f['mapping'], f['index'], f['objects'],
            selector=buffers.BIOS_LOCAL_FILL_SELECTOR)

    def body(self, saved='r4, lr', value=0, control=0x01000100,
             destination='destination', offset=0, initialize=True, suffix=(),
             second=None, callee=bios.NAME, width=2):
        lines = [f'push\t{{{saved}}}', 'sub\tsp, sp, #8']
        def fill(at, val):
            lines.extend(['mov\tr0, sp', f'add\tr0, r0, #{at}'])
            if initialize:
                lines.extend([f'mov\tr3, #{val}', ('str\tr3, [r0]' if width == 4 else 'strh\tr3, [r0]')])
            lines.extend(['ldr\tr1, .Ldestination', 'ldr\tr2, .Lcontrol', f'bl\t{callee}'])
        fill(offset, value)
        if second is not None:
            fill(second, value)
        lines.extend(suffix)
        lines.extend(['add\tsp, sp, #8'])
        restored = ', '.join(reg.strip() for reg in saved.split(',') if reg.strip() != 'lr')
        if restored:
            lines.append(f'pop\t{{{restored}}}')
        lines.extend(['pop\t{r0}', 'bx\tr0'])
        result = fixtures.assembly(*lines)
        return result.replace('.L4:', f'.Ldestination:\n\t.word\t{destination}\n.Lcontrol:\n\t.word\t{control}\n.L4:')

    def pair(self, real=None, stripped=None, interface=True, returns=False):
        pre = fixtures.PREPROCESSED + f'\nvoid {bios.NAME}(void *, void *, unsigned int);\nvoid unknown(void *, void *, unsigned int);\n'
        if returns:
            pre = pre.replace('void func_08028C34', 'int func_08028C34')
        return semantics._compare_compiles(real or self.body(),
            stripped or self.body(saved='lr'), pre, fixtures.SYMBOL,
            fixtures.DECLARATION, interfaces=self.interface() if interface else None)

    def test_local_fill_accepts_different_save_frames(self):
        result = self.pair()
        self.assertIn('bounded local fill source', semantics.record(fixtures.SYMBOL, result))

    def test_word_fill_and_permuted_compile_keep_policy(self):
        real = self.body(control=0x05000100, width=4)
        stripped = self.body(saved='lr', control=0x05000100, width=4)
        perturbed = self.body(saved='r4, r5, lr', control=0x05000100, width=4)
        pre = fixtures.PREPROCESSED + f'\nvoid {bios.NAME}(void *, void *, unsigned int);\n'
        result = semantics._compare_compiles(real, stripped, pre, fixtures.SYMBOL,
            fixtures.DECLARATION, perturbed_assembly=perturbed, interfaces=self.interface())
        self.assertIn('no numeric source-pointer observation or retention',
                      semantics.record(fixtures.SYMBOL, result, perturbed=True))

    def test_return_value_keeps_raw_source_dependency(self):
        def returning(saved):
            return self.body(saved=saved).replace('pop\tr0', 'pop\tr1').replace(
                'pop\t{r0}\n\tbx\tr0', 'pop\t{r1}\n\tmov\tlr, r1\n\tbx\tlr')
        with self.assertRaises(semantics.SemanticError):
            self.pair(returning('r4, lr'), returning('lr'), returns=True)

    def test_postcall_spill_reload_is_not_assumed_initialized(self):
        def reloaded(saved):
            body = self.body(saved=saved, second=2)
            marker = 'mov\tr0, sp\n\tadd\tr0, r0, #2\n\tmov\tr3, #0'
            return body.replace(marker,
                'mov\tr0, sp\n\tadd\tr0, r0, #2\n\tldr\tr3, [sp, #4]')
        with self.assertRaisesRegex(semantics.SemanticError, 'unknown content'):
            self.pair(reloaded('r4, lr'), reloaded('lr'))

    def test_two_fills_keep_relative_offsets(self):
        self.pair(self.body(second=2), self.body(saved='lr', second=2))
        with self.assertRaises(semantics.SemanticError):
            self.pair(self.body(second=2), self.body(saved='lr', second=4))

    def test_content_control_destination_are_exact(self):
        for changes in ({'value':1}, {'control':0x01000101}, {'destination':'other'}):
            with self.subTest(changes=changes), self.assertRaises(semantics.SemanticError):
                self.pair(stripped=self.body(saved='lr', **changes))

    def test_invalid_source_or_mode_refuses_even_equal_frames(self):
        for changes in ({'initialize':False}, {'offset':8}, {'offset':10},
                        {'offset':-2}, {'offset':1}, {'control':0},
                        {'control':0x01000000}, {'control':0x81000100},
                        {'control':0x05000100}, {'control':'unknown_control'}):
            with self.subTest(changes=changes), self.assertRaises(semantics.SemanticError):
                body = self.body(**changes)
                self.pair(body, body)

    def test_stack_destination_and_unknown_source_forms_refuse(self):
        body = self.body()
        for changed in (
            body.replace('ldr\tr1, .Ldestination', 'mov\tr1, sp'),
            body.replace('add\tr0, r0, #0', 'add\tr0, r0, r7'),
            body.replace('mov\tr3, #0', 'mov\tr3, r5'),
        ):
            with self.subTest(body=changed), self.assertRaises(semantics.SemanticError):
                self.pair(changed, changed)

    def test_unknown_callee_and_unselected_policy_remain_strict(self):
        with self.assertRaises(semantics.SemanticError):
            self.pair(interface=False)
        with self.assertRaises(semantics.SemanticError):
            self.pair(self.body(callee='unknown'), self.body(saved='lr', callee='unknown'))

    def test_opaque_outputs_retain_raw_source_dependency(self):
        for suffix in (('str\tr0, [r4]',), ('str\tr1, [r4]',),
                       ('str\tr2, [r4]',), ('str\tr3, [r4]',),
                       ('mov\tr5, r12', 'str\tr5, [r4]'),
                       ('mov\tr5, lr', 'str\tr5, [r4]'),
                       ('bne\t.Ldone', 'mov\tr5, #1', '.Ldone:')):
            with self.subTest(suffix=suffix), self.assertRaises(semantics.SemanticError):
                self.pair(self.body(suffix=suffix), self.body(saved='lr', suffix=suffix))

    def test_whole_frame_snapshot_is_not_reduced_to_source(self):
        a=self.body().replace('mov\tr0, sp', 'mov\tr3, #1\n\tstr\tr3, [sp, #4]\n\tmov\tr0, sp')
        b=self.body(saved='lr').replace('mov\tr0, sp', 'mov\tr3, #2\n\tstr\tr3, [sp, #4]\n\tmov\tr0, sp')
        with self.assertRaises(semantics.SemanticError):
            self.pair(a,b)


if __name__ == '__main__':
    unittest.main()
