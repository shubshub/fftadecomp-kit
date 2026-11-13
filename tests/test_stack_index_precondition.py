"""Variable private-stack-array indices under explicit, reviewed runtime premises."""
import copy
import hashlib
import json
from pathlib import Path
import struct
import sys
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import owner_admission_profile as owner
import rom_table_copy_profile as rtc
import stack_index_precondition_profile as sip
from test_nested_known_query import assemble
from test_rom_table_copy import fixture, HELPER, LEAK, OWNER, TABLE, TABLE_BYTES

SELECTOR = sip.SELECTOR


def owner_code(count=3, index=(0x1c04, 0x0624, 0x0e24), prefix=(0x4668,), access=(0x5d00,),
               post=(0x0600,), tail=()):
    """push {r4,lr}; sub sp,#8; <index into r4>; mov r0,sp; ldr r1,=table; movs r2,#count;
    bl copy; <prefix>; <access>; <post>; add sp,#8; pop {r4}; pop {r1}; bx r1; .word table.

    The default index is `adds r4,r0,#0; lsls r4,#24; lsrs r4,#24`, that is `(entry_R0 & 255)`,
    and the access is `ldrb r0,[r0,r4]` on `mov r0,sp`."""
    head = [0xb510, 0xb082, *index, 0x4668, 0, 0x2200 | count, HELPER]
    body = [*prefix, *access, *post, *tail, 0xb002, 0xbc10, 0xbc02, 0x4708]
    code = head + body
    raw = len(assemble(OWNER, code))
    literal = raw + (-raw % 4)
    ldr = 2 * (2 + len(index) + 1)
    code[2 + len(index) + 1] = 0x4900 | ((literal - ((ldr + 4) & ~3)) // 4)
    return code


REVIEW = 'every caller passes an index below the bound'


def reviewed(entry, address=OWNER):
    return json.dumps({f'0x{address:08X}': dict(entry, review=REVIEW)}).encode()


def admit(code=None, selector=SELECTOR, **kwargs):
    """Admit with the reviewed entry the selector asks for, as a reviewer would after checking."""
    arguments, _ = fixture(code or owner_code(), selector=selector, **kwargs)
    try:
        return arguments, owner.verify(**arguments)
    except sip.PremiseRefusal as refusal:
        arguments['premises'] = reviewed(refusal.entry)
        return arguments, owner.verify(**arguments)


def evidence(manifest):
    return manifest['proof']['buffers']['stack_index_preconditions']


class StackIndexPreconditionTests(unittest.TestCase):
    def test_unproved_index_is_admitted_under_a_recorded_premise(self):
        _, (manifest, _) = admit()
        self.assertEqual(manifest['profile'], sip.SCHEMA)
        found = evidence(manifest)
        self.assertEqual(found['accesses'], [])
        row, = found['preconditions']
        self.assertEqual((row['kind'], row['width'], row['expression'], row['bound'], row['scale']),
                         ('load', 1, '(entry_R0 & 255)', 3, 1))
        self.assertEqual((row['premise_proved'], row['discharged_by'], row['may_be_owner_written']),
                         (False, sip.PREMISES_PATH, False))
        # The array is the three copied bytes at sp+0..+3, in the frame below the two saved words.
        self.assertEqual((row['array_sp'], row['array_entry_sp']), ([0, 3], [-16, -13]))
        self.assertEqual(found['accepted']['rows'],
                         [dict(site=f'0x{row["site"]:08X}', expression='(entry_R0 & 255)', bound=3)])
        line, = sip.precondition_lines(found)
        self.assertIn('index (entry_R0 & 255) < 3', line)
        self.assertIn('unproved runtime premise', line)
        self.assertNotIn('caller', line)

    def test_index_proved_by_value_range_needs_no_premise(self):
        # adds r4,r0,#0; movs r1,#3; ands r4,r1 gives [0,3] against a four-byte copy.
        _, (manifest, _) = admit(owner_code(count=4, index=(0x1c04, 0x2103, 0x400c)))
        found = evidence(manifest)
        self.assertEqual(found['preconditions'], [])
        self.assertIsNone(found['accepted'])
        self.assertEqual(len(found['accesses']), 1)

    def test_store_is_admitted_under_the_object_extent(self):
        # strb r1,[r0,r4]: nothing is read, so the whole eight-byte object is the extent.
        _, (manifest, _) = admit(owner_code(access=(0x5501,), post=(0x2000,)))
        found = evidence(manifest)['preconditions'][0]
        self.assertEqual((found['kind'], found['bound']), ('store', 8))

    def test_scaled_index_states_the_premise_on_the_unscaled_value(self):
        # lsls r4,r4,#1 after the mask: halfword table of three entries is six bytes.
        _, (manifest, _) = admit(owner_code(count=6, index=(0x1c04, 0x0624, 0x0e24, 0x0064),
                                            access=(0x5b00,)))
        found = evidence(manifest)['preconditions'][0]
        self.assertEqual(tuple(found[key] for key in ('kind', 'width', 'expression', 'bound', 'scale')),
                         ('load', 2, '(entry_R0 & 255)', 3, 2))

    def test_index_without_a_defined_source_refuses(self):
        # ldr r4,[sp,#4]: a value read back from the stack has no caller-visible source.
        with self.assertRaisesRegex(sip.Refusal, 'no defined source'):
            admit(owner_code(index=(0x9c01,)))

    def test_rtc_selector_still_refuses_variable_indices(self):
        with self.assertRaisesRegex(ValueError, 'stack-alias index is not a known constant'):
            admit(selector=rtc.SELECTOR)

    def test_unaligned_index_refuses(self):
        # ldrh r0,[r0,r4]: a byte index is not provably even.
        with self.assertRaisesRegex(sip.Refusal, '2-byte aligned'):
            admit(owner_code(count=4, access=(0x5b00,)))

    def test_access_past_the_extent_refuses_even_under_the_premise(self):
        # adds r0,#3 moves the index-zero address to the first byte after the copy.
        with self.assertRaisesRegex(sip.Refusal, 'no array bytes'):
            admit(owner_code(prefix=(0x4668, 0x3003)))
        # Two bytes past the copy would leave the array for the saved words.
        with self.assertRaisesRegex(sip.Refusal, 'index has no defined source|no array bytes|saved register'):
            admit(owner_code(count=8, prefix=(0x4668, 0x3008)))

    def test_array_address_escape_refuses(self):
        # adds r0,r0,r4 produces a variable stack address that is then passed to a call.
        code = owner_code(access=(0x1900, LEAK), post=())
        with self.assertRaisesRegex(sip.Refusal, 'escapes through a call argument register'):
            admit(code)
        # The exact array address still goes through the buffer proof, which refuses the leak.
        code = owner_code(access=(0x5d00, 0x4668, LEAK), post=())
        with self.assertRaisesRegex(ValueError, f'buffer callee 0x{LEAK:08X}'):
            admit(code)

    def test_variable_address_stored_or_returned_refuses(self):
        with self.assertRaisesRegex(sip.Refusal, 'ranged stack address'):
            admit(owner_code(access=(0x1900,), post=()))

    def test_tampered_rom_table_makes_the_manifest_stale(self):
        arguments, (manifest, _) = admit()
        tampered = bytearray(arguments['rom'])
        tampered[TABLE - match.ROM_BASE + 1] ^= 1
        with self.assertRaisesRegex(ValueError, 'differs|stale|mismatch'):
            owner.verify(**dict(arguments, rom=bytes(tampered)), manifest=copy.deepcopy(manifest))

    def test_edited_removed_or_duplicated_premise_makes_the_manifest_stale(self):
        arguments, (manifest, _) = admit()
        original = evidence(manifest)['preconditions']
        edits = {
            'bound': lambda rows: rows[0].__setitem__('bound', 4),
            'expression': lambda rows: rows[0].__setitem__('expression', '(entry_R1 & 255)'),
            'scale': lambda rows: rows[0].__setitem__('scale', 2),
            'proved': lambda rows: rows[0].__setitem__('premise_proved', True),
            'discharge': lambda rows: rows[0].__setitem__('discharged_by', 'caller'),
            'owner-written': lambda rows: rows[0].__setitem__('may_be_owner_written', True),
            'removed': lambda rows: rows.clear(),
            'duplicated': lambda rows: rows.append(copy.deepcopy(rows[0])),
        }
        for name, edit in edits.items():
            with self.subTest(edit=name):
                changed = copy.deepcopy(manifest)
                edit(evidence(changed)['preconditions'])
                self.assertNotEqual(evidence(changed)['preconditions'], original)
                with self.assertRaisesRegex(ValueError, 'differs from complete fresh native replay'):
                    owner.verify(**arguments, manifest=changed)
        owner.verify(**arguments, manifest=copy.deepcopy(manifest))

    def replay(self, arguments, manifest, instructions):
        """Render the report, and route report_matches' fresh build through the fixture."""
        source = hashlib.sha256(b'source').hexdigest()

        def result(found):
            return (arguments['data'], found, source, arguments['mapping'], arguments['index'],
                    arguments['objects'], arguments['rom'], len(instructions), b'elf')

        def build(root, address, args=None, expected=None, *, selector=owner.SELECTOR):
            self.assertEqual((address, selector), (OWNER, SELECTOR))
            found, _ = owner.verify(**arguments, manifest=expected)
            return result(found)
        return owner.render(OWNER, result(manifest)), mock.patch.object(owner, 'build', build)

    def test_report_replay_rejects_every_premise_tamper(self):
        arguments, (manifest, instructions) = admit()
        report, fresh = self.replay(arguments, manifest, instructions)
        line, = sip.precondition_lines(evidence(manifest))
        self.assertEqual(report.splitlines().count(line), 1)
        encoded = report.split('* owner runtime evidence: `')[1].split('`')[0]

        def evidence_edit(edit):
            changed = json.loads(encoded)
            edit(changed['manifest']['proof']['buffers']['stack_index_preconditions'])
            return report.replace(encoded, owner.text(changed))
        tampers = {
            'line removed': report.replace(line + '\n', ''),
            'line duplicated': report.replace(line, line + '\n' + line),
            'line bound': report.replace('< 3,', '< 4,'),
            'line owner-written': report.replace(line, line.replace(', accepted', ', may be owner-written, accepted')),
            'row bound': evidence_edit(lambda found: found['preconditions'][0].__setitem__('bound', 4)),
            'row proved': evidence_edit(lambda found: found['preconditions'][0].__setitem__('premise_proved', True)),
            'accepted bound': evidence_edit(lambda found: found['accepted']['rows'][0].__setitem__('bound', 4)),
            'accepted review': evidence_edit(lambda found: found['accepted'].__setitem__('review', 'other')),
        }
        with fresh:
            self.assertTrue(owner.report_matches(report, '/nonexistent', OWNER))
            for name, tampered in tampers.items():
                with self.subTest(tamper=name):
                    self.assertNotEqual(tampered, report)
                    self.assertFalse(owner.report_matches(tampered, '/nonexistent', OWNER))

    def test_report_replay_rejects_a_changed_reviewed_entry(self):
        arguments, (manifest, instructions) = admit()
        report, fresh = self.replay(arguments, manifest, instructions)
        entry = json.loads(arguments['premises'])[f'0x{OWNER:08X}']
        changes = {
            'review': dict(entry, review='a different review'),
            'bound': dict(entry, rows=[dict(entry['rows'][0], bound=4)]),
        }
        for name, changed in changes.items():
            with self.subTest(change=name):
                arguments['premises'] = json.dumps({f'0x{OWNER:08X}': changed}).encode()
                with fresh:
                    self.assertFalse(owner.report_matches(report, '/nonexistent', OWNER))
        arguments['premises'] = None
        with fresh:
            self.assertFalse(owner.report_matches(report, '/nonexistent', OWNER))

    def test_report_selects_the_new_selector(self):
        arguments, (manifest, instructions) = admit()
        result = (arguments['data'], manifest, hashlib.sha256(b's').hexdigest(), arguments['mapping'],
                  arguments['index'], arguments['objects'], arguments['rom'], len(instructions), b'elf')
        report = owner.render(OWNER, result)
        self.assertTrue(owner.selected(report))
        self.assertEqual(owner.selector_for_report(report), SELECTOR)
        self.assertIn(f'* owner runtime: {SELECTOR}', report)

    def test_premises_without_a_reviewed_entry_refuse_and_print_the_rows(self):
        arguments, _ = fixture(owner_code(), selector=SELECTOR)
        with self.assertRaises(sip.PremiseRefusal) as caught:
            owner.verify(**arguments)
        message = str(caught.exception)
        self.assertIn(sip.PREMISES_PATH, message)
        self.assertIn('"expression": "(entry_R0 & 255)"', message)
        self.assertIn('"bound": 3', message)
        self.assertEqual(json.loads(message[message.index('{'):])[f'0x{OWNER:08X}'], caught.exception.entry)

    def test_reviewed_entry_must_repeat_the_rows_exactly(self):
        arguments, (manifest, _) = admit()
        entry = json.loads(arguments['premises'])[f'0x{OWNER:08X}']
        row = entry['rows'][0]
        refused = {
            'looser bound': dict(entry, rows=[dict(row, bound=4)]),
            'tighter bound': dict(entry, rows=[dict(row, bound=2)]),
            'expression': dict(entry, rows=[dict(row, expression='(entry_R1 & 255)')]),
            'site': dict(entry, rows=[dict(row, site='0x08010018')]),
            'extra row': dict(entry, rows=[row, row]),
        }
        for name, changed in refused.items():
            with self.subTest(entry=name):
                premises = json.dumps({f'0x{OWNER:08X}': changed}).encode()
                with self.assertRaisesRegex(sip.PremiseRefusal, 'the entry differs'):
                    owner.verify(**dict(arguments, premises=premises))
        malformed = {
            'placeholder review': dict(entry, review=sip.suggested_entry(evidence(manifest))['review']),
            'empty review': dict(entry, review=' '),
            'indented placeholder': dict(entry, review='  <to be written>'),
            'scratch review': dict(entry, review='Scratch entry for kit validation'),
            'todo review': dict(entry, review='todo: check the callers'),
            'no rows': dict(entry, rows=[]),
            'extra key': dict(entry, rows=[dict(row, scale=1)]),
        }
        for name, changed in malformed.items():
            with self.subTest(entry=name):
                premises = json.dumps({f'0x{OWNER:08X}': changed}).encode()
                with self.assertRaisesRegex(ValueError, 'premise'):
                    owner.verify(**dict(arguments, premises=premises))
        with self.assertRaisesRegex(sip.PremiseRefusal, 'none found'):
            owner.verify(**dict(arguments, premises=reviewed(entry, OWNER + 4)))
        with self.assertRaisesRegex(ValueError, 'canonical'):
            owner.verify(**dict(arguments, premises=json.dumps({'0x8010000': entry}).encode()))

    def test_entry_for_an_owner_without_premises_refuses(self):
        code = owner_code(count=4, index=(0x1c04, 0x2103, 0x400c))
        arguments, _ = fixture(code, selector=SELECTOR)
        premises = reviewed(dict(rows=[dict(site='0x08010016', expression='x', bound=1)]))
        with self.assertRaisesRegex(ValueError, 'does not need'):
            owner.verify(**dict(arguments, premises=premises))

    def test_spill_slot_bounds_the_array(self):
        # str r3,[sp,#4] spills a scalar right after the four copied bytes and ldr r3,[sp,#4]
        # reloads it. The load's initialised run reaches sp+8, but the spill is its own object.
        _, (manifest, _) = admit(owner_code(count=4, prefix=(0x9301, 0x4668), post=(0x0600, 0x9b01)))
        row, = evidence(manifest)['preconditions']
        self.assertEqual((row['bound'], row['array_sp']), (4, [0, 4]))
        # A direct reload bounds the store extent too, before or after the access.
        _, (manifest, _) = admit(owner_code(count=8, prefix=(0x9b01, 0x4668)))
        self.assertEqual(evidence(manifest)['preconditions'][0]['bound'], 4)
        _, (manifest, _) = admit(owner_code(access=(0x5501,), post=(0x2000, 0x9b01)))
        self.assertEqual(evidence(manifest)['preconditions'][0]['bound'], 4)
        # mov r2,sp; ldr r1,[r2,#4]: a reload through an exact stack alias is a boundary too.
        _, (manifest, _) = admit(owner_code(count=8, post=(0x0600, 0x466A, 0x6851, 0x2200)))
        self.assertEqual(evidence(manifest)['preconditions'][0]['bound'], 4)
        # mov r2,sp; adds r2,#4; ldmia r2!,{r1}: so is a block reload from an exact alias.
        _, (manifest, _) = admit(owner_code(count=8, post=(0x0600, 0x466A, 0x3204, 0xCA02, 0x2200)))
        self.assertEqual(evidence(manifest)['preconditions'][0]['bound'], 4)
        # A store that is never reloaded directly is an element store (a[1] = x) and stays inside.
        _, (manifest, _) = admit(owner_code(count=4, prefix=(0x9301, 0x4668)))
        self.assertEqual(evidence(manifest)['preconditions'][0]['bound'], 8)

    def test_index_misaligned_on_every_path_refuses(self):
        # r4 = R0 << 2; r1 = sp + r4; cmp r3,#2; bne; adds r1,r1,r3 (r3 == 2); ldr r0,[r1].
        # The premise bounds the index from above but every address it admits is sp+4k+2.
        code = owner_code(count=8, index=(0x0084,), access=(0x1901, 0x2B02, 0xD102, 0x18C9, 0x6808, 0x2100),
                          post=(0x2000, 0x2100))
        with self.assertRaisesRegex(sip.Refusal, '4-byte aligned'):
            admit(code)
        # Without the +2 the same word index is admitted.
        _, (manifest, _) = admit(owner_code(count=8, index=(0x0084,), access=(0x1901, 0x6808),
                                            post=(0x2100,)))
        self.assertEqual(evidence(manifest)['preconditions'][0]['bound'], 2)

    def test_field_loads_name_their_site_and_whether_the_owner_may_have_written_them(self):
        # ldrb r4,[r1,#1] before the copy call: nothing in the owner can have written the field.
        _, (manifest, _) = admit(owner_code(index=(0x784C,)))
        row, = evidence(manifest)['preconditions']
        self.assertEqual(row['expression'], f'u8[(entry_R1 + 1)]@0x{OWNER + 4:08X}')
        self.assertFalse(row['may_be_owner_written'])
        self.assertNotIn('owner-written', sip.precondition_lines(evidence(manifest))[0])
        # adds r4,r1,#0 before the call and ldrb r4,[r4,#1] after it: the callee may write the field.
        _, (manifest, _) = admit(owner_code(index=(0x1c0c,), prefix=(0x7864, 0x4668)))
        row, = evidence(manifest)['preconditions']
        self.assertTrue(row['may_be_owner_written'])
        self.assertIn('may be owner-written', sip.precondition_lines(evidence(manifest))[0])

    def test_deferred_store_of_the_return_address_refuses(self):
        # mov r1,sp; mov r2,lr; strb r2,[r1,r4]: the core skips per-slot facts for a deferred
        # access, so a return-carrying value may not be stored through one.
        with self.assertRaisesRegex(ValueError, 'bypass frame-content facts'):
            admit(owner_code(index=(0x1c04, 0x0624, 0x0e24, 0x4669, 0x4672, 0x550A)))
        # The same store of an ordinary scalar is admitted.
        admit(owner_code(index=(0x1c04, 0x0624, 0x0e24, 0x4669, 0x550B)))

    def test_unmodified_rtc_manifest_keeps_its_schema(self):
        arguments, _ = fixture()
        manifest, _ = owner.verify(**arguments)
        self.assertEqual(manifest['profile'], rtc.SCHEMA)
        self.assertNotIn('stack_index_preconditions', manifest['proof']['buffers'])


class ValueDomainTests(unittest.TestCase):
    def test_expression_rendering_and_narrowing(self):
        entry = ('entry', 1)
        self.assertEqual(sip.render(sip.shift_expr('>>', sip.shift_expr('<<', entry, 24), 24)),
                         '(entry_R1 & 255)')
        self.assertEqual(sip.render(sip.shift_expr('>>', sip.shift_expr('<<', entry, 16), 16)),
                         '(entry_R1 & 65535)')
        self.assertEqual(sip.render(sip.make('ld', 1, False, sip.make('bin', 'add', entry, ('c', 1)), 0x08000010)),
                         'u8[(entry_R1 + 1)]@0x08000010')
        self.assertEqual(sip.render(sip.make('ld', 1, False, sip.make('bin', 'add', ('c', 0x02007F40), ('c', 4)),
                                             0x08000020)),
                         'u8[0x02007F44]@0x08000020')
        self.assertIsNone(sip.make('bin', 'add', entry, None))
        deep = entry
        for _ in range(40):
            deep = sip.make('bin', 'add', deep, ('c', 1)) if deep else None
        self.assertIsNone(deep)


if __name__ == '__main__':
    unittest.main()
