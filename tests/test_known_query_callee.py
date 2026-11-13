"""Buffer owners whose callees run the pinned known list queries."""
import copy
import json
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import owner_admission_profile as owner
import owner_graph_profile as graph
import known_query_stack_buffer_profile as stack
import known_query_callee_profile as callee
from test_nested_known_query import assemble

OWNER, F, LEAF = 0x08010000, 0x08011000, 0x08012000
Q = 0x08099D08
SEARCH, ANY = 0x08099560, 0x08099544
ROM_SIZE = 0x150000

# Owner: push {r4,lr}; sub sp,#8; mov r2,sp; add r3,sp,#4; bl F; movs r3,#0;
#        add sp,#8; pop {r4}; pop {r0}; bx r0
# F returns with R3 unchanged, so the owner's alias is still there after the call.
OWNER_CODE = [0xb510, 0xb082, 0x466a, 0xab01, F, 0x2300, 0xb002, 0xbc10, 0xbc01, 0x4700]


def callee_code(frame=0xb08d, after=(), before=(0x4669,), target=Q):
    """push {r4-r7,lr}; sub sp; adds r7,r2,#0; adds r6,r3,#0; <before>; bl target;
    <after>; strh r0,[r7]; movs r0,#0; strh r0,[r6]; add sp; pop {r4-r7}; pop {r0}; bx r0.

    R2/R3 still hold the owner's halfword pointers at the query call."""
    return [0xb5f0, frame, 0x1c17, 0x1c1e, *before, target, *after,
            0x8038, 0x2000, 0x8030, frame - 0x80, 0xbcf0, 0xbc01, 0x4700]


def family_bodies():
    bodies = {}
    for family in callee.FAMILIES.values():
        for address, (count, code) in family['bodies'].items():
            bodies[address] = (count, bytes.fromhex(code))
    return bodies


def fixture(owner_code=OWNER_CODE, f_code=None, *, patch_rom=None, selector=callee.SELECTOR):
    f_code = callee_code() if f_code is None else f_code
    raw = assemble(OWNER, owner_code)
    f_raw = assemble(F, f_code)
    rom = bytearray(ROM_SIZE)
    rom[OWNER-match.ROM_BASE:OWNER-match.ROM_BASE+len(raw)] = raw
    rom[F-match.ROM_BASE:F-match.ROM_BASE+len(f_raw)] = f_raw
    rom[LEAF-match.ROM_BASE:LEAF-match.ROM_BASE+2] = bytes.fromhex('7047')
    spans = [(OWNER, len(raw), 0), (F, len(f_raw), 0), (LEAF, 2, 1)]
    for address, (count, body) in family_bodies().items():
        rom[address-match.ROM_BASE:address-match.ROM_BASE+len(body)] = body
        spans.append((address, len(body), count))
    for address, padding in stack.THUNK_PADDING.items():
        rom[address+2-match.ROM_BASE:address+4-match.ROM_BASE] = bytes.fromhex(padding)
    for address, value in (patch_rom or {}).items():
        rom[address-match.ROM_BASE] = value
    rows = [dict(rom=f'0x{a:08X}', end=f'0x{a+n:08X}', mode='thumb', instrs=count)
            for a, n, count in sorted(spans)]
    mapping = json.dumps(rows).encode()
    for start, body in ((OWNER, raw), (F, f_raw)):
        row = next(r for r in rows if int(r['rom'], 16) == start)
        row['instrs'] = owner.refine(body, start, mapping)['instrs']
        mapping = json.dumps(rows).encode()
    _, _, _, calls, _ = graph.graph(raw, OWNER, owner.refine(raw, OWNER, mapping))
    return dict(data=raw, address=OWNER, rom=bytes(rom), mapping=mapping,
        index=''.join(f'{int(r["rom"],16):08X} {int(r["end"],16):08X} '
                      f'{int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n' for r in rows).encode(),
        objects=b'{}',
        bindings=dict(calls=[[site-OWNER, f'func_{target:08X}'] for site, target in sorted(calls.items())],
                      data=[], functions=[], switches=[]),
        selector=selector)


def evidence(manifest):
    return manifest['proof']['buffers']['known_query_callees']


class KnownQueryCalleeTests(unittest.TestCase):
    def test_owner_with_known_query_callee_is_admitted(self):
        manifest, _ = owner.verify(**fixture())
        self.assertEqual(manifest['profile'], callee.SCHEMA)
        proof = evidence(manifest)
        self.assertEqual(proof['callees'], [F])
        self.assertEqual(proof['capacity_words'], 13)
        self.assertFalse(proof['list_bound_proved_from_ROM'])
        self.assertIn('at most 13 nodes', proof['premise'])
        self.assertIn('at most 13 nodes', proof['explicit_conditions'][0])
        self.assertEqual(proof['family_calls'], [dict(site=F+10, target=Q, dead=['r2'], retained=[['r3', -12]])])
        record = next(r for r in manifest['proof']['buffers']['dependencies'] if r['address'] == F)
        self.assertEqual(record['structure']['kind'], 'known-query-stack-buffer-callee-v1')
        self.assertEqual(record['structure']['caller']['returned_counts'], list(range(14)))

    def test_every_family_preserves_stale_r3(self):
        manifest, _ = owner.verify(**fixture(f_code=callee_code(after=(0x2000, ANY, 0x2000, 0x2100, SEARCH))))
        calls = evidence(manifest)['family_calls']
        self.assertEqual([(c['target'], c['dead'], c['retained']) for c in calls],
                         [(Q, ['r2'], [['r3', -12]]), (ANY, [], [['r3', -12]]), (SEARCH, [], [['r3', -12]])])
        self.assertEqual(sorted(f['root'] for f in evidence(manifest)['families']), [ANY, SEARCH, Q])

    def test_default_named_buffer_walk_still_refuses(self):
        with self.assertRaisesRegex(ValueError, 'buffer callee 0x08011000'):
            owner.verify(**fixture(selector='named-data-buffer-v1'))

    def test_callee_write_outside_owner_buffer_refuses(self):
        code = callee_code(); code[-7] = 0x8138  # strh r0,[r7,#8]: the owner's saved R4 slot
        with self.assertRaisesRegex(ValueError, 'outside allocated local words'):
            owner.verify(**fixture(f_code=code))

    def test_query_buffer_below_thirteen_words_refuses(self):
        with self.assertRaisesRegex(ValueError, 'smaller than the premised 13-word'):
            owner.verify(**fixture(f_code=callee_code(frame=0xb08c)))

    def test_read_beyond_returned_count_refuses(self):
        # 14 words keep word 13 allocated; only the initialization check refuses.
        with self.assertRaisesRegex(ValueError, 'uninitialized'):
            owner.verify(**fixture(f_code=callee_code(frame=0xb08e, after=(0x980d,))))

    def test_reading_dangling_r2_after_query_refuses(self):
        # The collector leaves R2 = out+4n; the owner alias that was in R2 is gone.
        with self.assertRaisesRegex(ValueError, 'untracked register'):
            owner.verify(**fixture(f_code=callee_code(after=(0x8010,))))  # strh r0,[r2]

    def test_owner_alias_in_live_query_input_refuses(self):
        # adds r1,r3,#0: the owner's pointer becomes the query buffer.
        with self.assertRaisesRegex(ValueError, 'query buffer must be an aligned private stack address|live input'):
            owner.verify(**fixture(f_code=callee_code(before=(0x1c19,))))
        # adds r0,r6,#0 before 08099544: the owner's pointer becomes the list owner.
        with self.assertRaisesRegex(ValueError, 'live input of a pinned list-query family'):
            owner.verify(**fixture(f_code=callee_code(after=(0x1c30, ANY))))

    def test_alias_kept_in_r4_across_query_stays_bounded(self):
        # adds r4,r2,#0 before the query: R4 survives the pinned query unchanged.
        manifest, _ = owner.verify(**fixture(f_code=callee_code(before=(0x1c14, 0x4669), after=(0x8020,))))
        self.assertEqual(evidence(manifest)['callees'], [F])  # strh r0,[r4]: owner word 0
        with self.assertRaisesRegex(ValueError, 'outside allocated local words'):
            owner.verify(**fixture(f_code=callee_code(before=(0x1c14, 0x4669), after=(0x8120,))))  # [r4,#8]

    def proof(self):
        args = fixture()
        return callee.KnownQueryCalleeBufferProof(args['rom'], args['mapping'], args['index'], args['objects'])

    def test_family_call_register_rules(self):
        stack = [(False, False, True)] * 4
        r12, lr = match.ARM_REG_R12, match.ARM_REG_LR
        self.assertEqual(dict(self.proof().check_arguments(ANY, {r12: -8}, stack, {}, frozenset(), site=F)),
                         {r12: -8})
        with self.assertRaisesRegex(ValueError, 'live input of a pinned list-query family'):
            self.proof().check_arguments(ANY, {lr: -8}, stack, {}, frozenset(), site=F)
        with self.assertRaisesRegex(ValueError, 'stack-passed pointer words'):
            self.proof().check_arguments(ANY, {}, stack, {0: -8}, frozenset({0}), site=F)
        with self.assertRaisesRegex(ValueError, 'outside a callee executed'):
            self.proof().check_arguments(Q, {match.ARM_REG_R0 + 3: -8}, stack, {}, frozenset(), site=F)

    def test_query_called_by_the_owner_itself_refuses(self):
        # Owner: mov r1,sp; mov r2,sp; bl Q (stale R2 alias at a query outside an executed callee).
        code = [0xb510, 0xb08e, 0x4669, 0x466a, Q, 0xb00e, 0xbc10, 0xbc01, 0x4700]
        with self.assertRaisesRegex(ValueError, 'live input|outside a callee executed'):
            owner.verify(**fixture(owner_code=code))
        code = [0xb510, 0xb082, 0x466a, 0xab01, Q, 0xb002, 0xbc10, 0xbc01, 0x4700]
        with self.assertRaisesRegex(ValueError, 'outside a callee executed under its contract'):
            owner.verify(**fixture(owner_code=code))

    def test_tampered_pinned_bytes_refuse(self):
        for address in (Q, 0x080C7CC0, 0x0809AC20):
            with self.subTest(address=hex(address)):
                rom = fixture()['rom']
                with self.assertRaisesRegex(ValueError, 'pinned'):
                    owner.verify(**fixture(patch_rom={address+2: rom[address+2-match.ROM_BASE] ^ 1}))
        for address in (0x080C8298, 0x0809AB3C, 0x08099840, 0x0809AB5C):
            with self.subTest(address=hex(address)):
                rom = fixture()['rom']
                with self.assertRaisesRegex(ValueError, 'pinned list-query family bytes'):
                    owner.verify(**fixture(f_code=callee_code(after=(0x2000, ANY, 0x2000, 0x2100, SEARCH)),
                                           patch_rom={address+2: rom[address+2-match.ROM_BASE] ^ 1}))

    def test_manifest_tampering_refuses(self):
        args = fixture()
        manifest, _ = owner.verify(**args)
        edits = [
            lambda p: p['known_query_callees'].__setitem__('capacity_words', 14),
            lambda p: p['known_query_callees'].__setitem__('list_bound_proved_from_ROM', True),
            lambda p: p['known_query_callees']['family_calls'][0].__setitem__('dead', []),
            lambda p: p['known_query_callees']['families'][0].__setitem__('untouched_registers', ['r3']),
        ]
        for edit in edits:
            changed = copy.deepcopy(manifest)
            edit(changed['proof']['buffers'])
            with self.assertRaises(ValueError):
                owner.verify(**args, manifest=changed)


class FamilyFactTests(unittest.TestCase):
    """The register facts are checked on bytes, not asserted."""

    ROOT = 0x08020000

    def facts(self, root_code, extra=None):
        raw = assemble(self.ROOT, root_code)
        bodies = {self.ROOT: (len(root_code), raw.hex()), **(extra or {})}
        rom = bytearray(ROM_SIZE)
        rows = []
        for address, (count, code) in bodies.items():
            body = bytes.fromhex(code)
            rom[address-match.ROM_BASE:address-match.ROM_BASE+len(body)] = body
            rows.append(dict(rom=f'0x{address:08X}', end=f'0x{address+len(body):08X}',
                             mode='thumb', instrs=count))
        mapping = json.dumps(rows).encode()
        index = ''.join(f'{int(r["rom"],16):08X} {int(r["end"],16):08X} '
                        f'{int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n' for r in rows).encode()
        with patch.dict(callee.FAMILIES, {self.ROOT: dict(kind='synthetic', indirect_targets=[], bodies=bodies)}):
            return callee.family_facts(self.ROOT, bytes(rom), mapping, index)

    def test_clean_root_passes(self):
        facts = self.facts([0xb500, 0x2200, 0xbc01, 0x4700])  # movs r2,#0
        self.assertEqual(facts['untouched_registers'], ['r3', 'r12'])

    def test_r3_access_refuses(self):
        with self.assertRaisesRegex(ValueError, 'accesses R3 or R12'):
            self.facts([0xb500, 0x2200, 0x1c18, 0xbc01, 0x4700])  # adds r0,r3,#0

    def test_bics_before_r2_write_is_not_a_branch(self):
        self.facts([0xb500, 0x4388, 0x2200, 0xbc01, 0x4700])  # bics r0,r1; movs r2,#0

    def test_pc_write_before_r2_write_refuses(self):
        with self.assertRaisesRegex(ValueError, 'call or branch before writing R2'):
            self.facts([0xb500, 0x46f7, 0x2200, 0xbc01, 0x4700])  # mov pc,lr

    def test_odd_ram_code_literal_outside_family_refuses(self):
        for word in ('01000003', '01000002'):  # IWRAM 0x03000001, EWRAM 0x02000001
            raw = assemble(self.ROOT, [0xb500, 0x2200, 0xbc01, 0x4700]) + bytes.fromhex(word)
            rom = bytearray(ROM_SIZE)
            rom[self.ROOT-match.ROM_BASE:self.ROOT-match.ROM_BASE+len(raw)] = raw
            rows = [dict(rom=f'0x{self.ROOT:08X}', end=f'0x{self.ROOT+len(raw):08X}', mode='thumb', instrs=4)]
            index = f'{self.ROOT:08X} {self.ROOT+len(raw):08X} {len(raw)} 4 return\n'.encode()
            family = dict(kind='synthetic', indirect_targets=[], bodies={self.ROOT: (4, raw.hex())})
            with patch.dict(callee.FAMILIES, {self.ROOT: family}):
                with self.assertRaisesRegex(ValueError, 'code literal leaves the family'):
                    callee.family_facts(self.ROOT, bytes(rom), json.dumps(rows).encode(), index)

    def test_r12_access_refuses(self):
        with self.assertRaisesRegex(ValueError, 'accesses R3 or R12'):
            self.facts([0xb500, 0x2200, 0x4660, 0xbc01, 0x4700])  # mov r0,r12

    def test_r2_read_before_write_refuses(self):
        with self.assertRaisesRegex(ValueError, 'reads R2 before writing'):
            self.facts([0xb500, 0x1c10, 0x2200, 0xbc01, 0x4700])  # adds r0,r2,#0

    def test_call_before_r2_write_refuses(self):
        with self.assertRaisesRegex(ValueError, 'call or branch before writing R2'):
            self.facts([0xb500, 0x08020100, 0x2200, 0xbc01, 0x4700],
                       {0x08020100: (1, '7047')})

    def test_direct_call_outside_family_refuses(self):
        with self.assertRaisesRegex(ValueError, 'direct call leaves the family'):
            self.facts([0xb500, 0x2200, 0x08020100, 0xbc01, 0x4700])

    def test_code_literal_outside_family_refuses(self):
        raw = assemble(self.ROOT, [0xb500, 0x2200, 0xbc01, 0x4700]) + bytes.fromhex('01010208')
        rom = bytearray(ROM_SIZE)
        rom[self.ROOT-match.ROM_BASE:self.ROOT-match.ROM_BASE+len(raw)] = raw
        rows = [dict(rom=f'0x{self.ROOT:08X}', end=f'0x{self.ROOT+len(raw):08X}', mode='thumb', instrs=4)]
        index = f'{self.ROOT:08X} {self.ROOT+len(raw):08X} {len(raw)} 4 return\n'.encode()
        with patch.dict(callee.FAMILIES, {self.ROOT: dict(kind='synthetic', indirect_targets=[], bodies={self.ROOT: (4, raw.hex())})}):
            with self.assertRaisesRegex(ValueError, 'code literal leaves the family'):
                callee.family_facts(self.ROOT, bytes(rom), json.dumps(rows).encode(), index)

    def test_real_families_hold_on_their_pinned_bytes(self):
        args = fixture()
        for root in callee.FAMILIES:
            with self.subTest(root=hex(root)):
                facts = callee.family_facts(root, args['rom'], args['mapping'], args['index'])
                self.assertEqual(facts['written_before_read'], ['r2'])


if __name__ == '__main__':
    unittest.main()
