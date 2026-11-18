"""The 080DE524 caller lends a bounded configuration through one scheduler descriptor."""
import copy
import json
import os
from pathlib import Path
import sys
from types import SimpleNamespace
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import scheduler_event_definition as event


class EventFrameTests(unittest.TestCase):
    def test_only_one_pointer_word_and_duration_alias(self):
        proof = SimpleNamespace(observations={}, access=match.BufferCallProof.access)
        stack = [(False, False, True)] * 17 + [(False, True, False)] * 8
        aliases = {match.ARM_REG_R2: -96, match.ARM_REG_R0+7: -100}
        slots = {-92: -68}
        event.check_call(proof, aliases, stack, slots, event.CREATE)
        self.assertEqual(proof.observations[event.CREATE]['definition'], [-68, -52])
        for altered_aliases, altered_stack, altered_slots in [
                ({**aliases, match.ARM_REG_R3: -68}, stack, slots),
                ({**aliases, match.ARM_REG_R0+7: -68}, stack, slots),
                ({**aliases, match.ARM_REG_R2: -100}, stack, slots),
                (aliases, stack[:-1], slots),
                (aliases, stack[:16] + [stack[-1]] + stack[17:], slots),
                (aliases, stack, {-92: -100}), (aliases, stack, {-92: -64}),
                (aliases, stack, {-88: -68}), (aliases, stack, {**slots, -64: -100})]:
            with self.subTest(aliases=altered_aliases, slots=altered_slots), self.assertRaises(ValueError):
                event.check_call(proof, altered_aliases, altered_stack, altered_slots, event.CREATE)


@unittest.skipUnless(os.environ.get('FFTA_EVENT_DEFINITION_ROOT'), 'needs indexed USA ROM, source and report')
class NativeEventTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import match_evidence
        cls.root = Path(os.environ['FFTA_EVENT_DEFINITION_ROOT']).resolve()
        cls.rom = Path(match_evidence.report_rom_path(cls.root)).read_bytes()
        cls.mapping = match_evidence.mapping_snapshot(cls.root)
        cls.report = (cls.root / 'docs/match/080DE524.md').read_text()
        line = next(line for line in cls.report.splitlines() if line.startswith('* owner runtime evidence:'))
        cls.manifest = json.loads(line.split('`')[1])['manifest']

    def test_callback_does_not_retain_borrowed_pointers(self):
        start = event.CALLBACK - match.ROM_BASE
        body = self.rom[start:start+388]
        projection = event.callback_phase(body)
        self.assertEqual(projection['field_transfers'][-1], (12, 14, 2))
        # STR R1,[R4] saves the definition pointer. STR R5,[R4] saves the descriptor.
        # R9 is the ambient original descriptor. Its MOV into R0 changes the saved value.
        for site, replacement in [(0x080DDAC4, '2160'), (0x080DDAC4, '2560'),
                (0x080DDAC2, '4846'), (0x080DDAC0, 'a968'), (0x080DDADA, 'c889'),
                (0x080DDADC, 'a081'), (0x080DDAA6, '0bd1'), (0x080DDAE6, '1170'),
                (0x080DDC10, '081c'), (0x080DDC16, '0846')]:
            changed = bytearray(body)
            offset = site-event.CALLBACK
            changed[offset:offset+2] = bytes.fromhex(replacement)
            self.assertNotEqual(changed, body)
            with self.subTest(site=hex(site), replacement=replacement), self.assertRaises(ValueError):
                event.callback_phase(changed)

    def test_constructor_and_scheduler_mutations(self):
        import owner_admission_profile as owner
        import owner_graph_profile as graph
        root_offset = event.OWNER-match.ROM_BASE
        body = self.rom[root_offset:root_offset+248]
        ins, edges, _, calls, _ = graph.graph(body, event.OWNER, owner.refine(body, event.OWNER, self.mapping))
        ends = {event.WRAPPER: 60, event.CORE: 206, event.THUNK: 2, event.CALLBACK: 388}
        def span(at):
            offset = at-match.ROM_BASE
            return self.rom[offset:offset+ends[at]]
        proof = SimpleNamespace(span=span, mapping=self.mapping)
        for site in (0x080DE566, 0x080DE5AE, 0x080DE5D6, 0x080DE5F6, 0x080DE5F8, 0x080DE5FA,
                     0x080DE5FC, 0x080DE600, 0x080DE602, 0x080DE608, 0x080DE618):
            changed = bytearray(body)
            changed[site-event.OWNER] ^= 2
            with self.subTest(site=hex(site)), self.assertRaises(ValueError):
                event.bind(proof, changed, event.OWNER, ins, edges, calls)
        for start, site in [(event.WRAPPER, 0x08005B88), (event.CORE, 0x0800598A),
                            (event.CORE, 0x080059A0), (event.CORE, 0x080059C0),
                            (event.CORE, 0x080059D0), (event.CORE, 0x080059DA),
                            (event.CORE, 0x080059F4), (event.CORE, 0x08005A02),
                            (event.CORE, 0x08005A08), (event.THUNK, event.THUNK)]:
            altered = bytearray(span(start))
            altered[site-start] ^= 2
            with self.subTest(site=hex(site)), self.assertRaises(ValueError):
                event.bind(SimpleNamespace(span=lambda at: bytes(altered) if at == start else span(at),
                                           mapping=self.mapping), body, event.OWNER, ins, edges, calls)
        bad_edges = {**edges, 0x080DE5D2: (0x080DE5FA,)}
        with self.assertRaises(ValueError):
            event.bind(proof, body, event.OWNER, ins, bad_edges, calls)

    def test_typed_relocations_and_native_replay(self):
        import match_evidence
        event.check_bindings(self.manifest['bindings'])
        for key, pos, i, value in [('functions', 0, 1, 'func_080DDA96'), ('functions', 0, 0, 240),
                                    ('calls', 4, 1, 'func_080DE12C')]:
            changed = copy.deepcopy(self.manifest['bindings'])
            changed[key][pos][i] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                event.check_bindings(changed)
        self.assertTrue(match_evidence.report_matches(self.report, str(self.root), event.OWNER))
        for old, new in [('"definition_initialized_bytes":14', '"definition_initialized_bytes":16'),
                         ('"phase_zero_retains_frame_pointer":false', '"phase_zero_retains_frame_pointer":true')]:
            changed = self.report.replace(old, new)
            self.assertNotEqual(changed, self.report)
            with self.subTest(new=new):
                self.assertFalse(match_evidence.report_matches(changed, str(self.root), event.OWNER))


if __name__ == '__main__':
    unittest.main()
