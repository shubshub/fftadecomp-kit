"""Differing join aliases may disappear only after an all-path overwrite proof."""
import subprocess
import unittest

import test_buffer_index as fixtures

match = fixtures.match
BASE = fixtures.BASE


class StackAliasJoinLifetimeTests(unittest.TestCase):
    setUp = fixtures.BufferIndexTests.setUp

    def body(self, source):
        assembly = self.root / 'join.s'
        assembly.write_text('.syntax unified\n.arch armv4t\n.thumb\n.text\n'
                            '.global caller, caller_end\ncaller:\n' + source +
                            '\ncaller_end:\n.org 0x100\ncallee:\nbx lr\n')
        for command in (
            ['arm-none-eabi-as', '-mthumb-interwork', str(assembly), '-o', str(self.root / 'join.o')],
            ['arm-none-eabi-ld', '-Ttext=0x08000000', '-e', 'caller', str(self.root / 'join.o'),
             '-o', str(self.root / 'join.elf')],
            ['arm-none-eabi-objcopy', '-O', 'binary', '--only-section=.text',
             str(self.root / 'join.elf'), str(self.root / 'join.bin')],
        ):
            subprocess.run(command, check=True, capture_output=True)
        image = match.elf_image((self.root / 'join.elf').read_bytes())
        symbols = {row['name']: row['value'] for row in image['symbols']}
        data = (self.root / 'join.bin').read_bytes()[:symbols['caller_end'] - BASE]
        return data

    def joined(self, after='', first='mov r4, sp', second='movs r4, #0'):
        return ('push {r4, lr}\nsub sp, #4\ncmp r0, #0\nbeq scalar\n' + first +
                '\nb joined\nscalar:\n' + second + '\njoined:\n' + after +
                '\nadd sp, #4\npop {r4}\npop {r1}\nbx r1')

    def verify(self, source, engine=match):
        data = self.body(source)
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        calls = {i.address: i.operands[0].imm for i in decoder.disasm(data, BASE)
                 if match.CS_GRP_CALL in i.groups}
        return engine.verify_leaf_instructions(data, BASE, True, calls)

    def kill_proof(self, source, register=match.ARM_REG_R0 + 4):
        data = self.body(source)
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        return match.stack_alias_overwritten_before_use(data, BASE, BASE, register, decoder)

    def test_all_path_scalar_overwrite_and_saved_register_restore(self):
        for after in ('', 'movs r4, #7',
                      'cmp r0, #1\nbeq left\nmovs r4, #2\nb done\n'
                      'left:\nmovs r4, #3\ndone:'):
            with self.subTest(after=after):
                self.verify(self.joined(after))

    def test_differing_offsets_require_overwrite(self):
        self.verify(self.joined('movs r4, #1', second='add r4, sp, #4'))
        with self.assertRaises(ValueError):
            self.verify(self.joined('ldr r0, [r4]', second='add r4, sp, #4'))

    def test_one_unsafe_successor_does_not_erase_other_edge_alias(self):
        for after in ('cmp r0, #1\nbeq read_alias\nmovs r4, #0\nb after_read\n'
                      'read_alias:\nldr r0, [r4]\nafter_read:',
                      'cmp r0, #1\nbeq cleared\nstr r4, [r2]\n'
                      'cleared:\nmovs r4, #0'):
            with self.subTest(after=after), self.assertRaises(ValueError):
                self.verify(self.joined(after))

    def test_reads_stores_calls_and_interrupts_before_kill_are_not_dead(self):
        for before in ('ldr r0, [r4]', 'str r4, [r2]', 'movs r0, r4',
                       'adds r4, #1', 'bl callee', 'svc #0', 'push {r4}'):
            with self.subTest(before=before):
                self.assertFalse(self.kill_proof(before + '\nmovs r4, #0\nbx lr'))
                with self.assertRaises(ValueError):
                    self.verify(self.joined(before + '\nmovs r4, #0'))

    def test_return_unknown_jump_cycle_and_outside_body_refused(self):
        for source in ('bx lr', 'bx r3', 'b outside\nmovs r4, #0\noutside:\nbx lr',
                       'loop:\ncmp r0, #0\nbeq killed\nb loop\nkilled:\nmovs r4, #0',
                       'b .+0x200'):
            with self.subTest(source=source):
                self.assertFalse(self.kill_proof(source))
        for register in (match.ARM_REG_SP, match.ARM_REG_LR, match.ARM_REG_PC):
            self.assertFalse(self.kill_proof('movs r4, #0\nbx lr', register))

    def test_result_register_and_pointer_alias_remain_observed_at_exit(self):
        self.assertFalse(self.kill_proof('bx lr', match.ARM_REG_R0))
        with self.assertRaises(ValueError):
            self.verify(self.joined('movs r0, r4\nmovs r4, #0'))

    def test_equal_alias_joins_and_existing_scalar_cfg_unchanged(self):
        for source in ('movs r0, #1\nbx lr', 'push {lr}\nmovs r0, #2\npop {r1}\nbx r1',
                       self.joined('ldr r0, [r4]', second='mov r4, sp')):
            with self.subTest(source=source):
                self.verify(source)


if __name__ == '__main__':
    unittest.main(verbosity=2)
