"""Buffer owners whose stale argument-register aliases are dead in the callee."""
import copy
import json
from pathlib import Path
import struct
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import owner_admission_profile as owner
import owner_graph_profile as graph
import dead_argument_buffer_profile as dead
from test_nested_known_query import assemble

OWNER, F, G = 0x08010000, 0x08011000, 0x08012000
DATA = 0x02000000
ROM_SIZE = 0x20000

# push {lr}; sub sp,#8; mov r0,sp; add r1,sp,#4; bl F; movs r0,#2; bl G;
# ldr r1,=DATA; strb r0,[r1]; add sp,#8; pop {r1}; bx r1; .word DATA
# F leaves both owner aliases in R0/R1; R1 is still the owner's &b (frame offset -8) at G.
OWNER_CODE = [0xb500, 0xb082, 0x4668, 0xa901, F, 0x2002, G, 0x4902, 0x7008, 0xb002, 0xbc02, 0x4708]
F_CODE = [0x4770]
# push {lr}; sub sp,#8; movs r1,#0; mov r2,sp; adds r0,r2,r0; ldrb r0,[r0];
# add sp,#8; pop {r1}; bx r1 - G's own frame indexed by R0, as func_080035F8 does
G_PREFIX = [0xb500, 0xb082]
G_KILL = [0x2100]
G_BODY = [0x466a, 0x1810, 0x7800, 0xb002, 0xbc02, 0x4708]


def fixture(g_code=None, *, selector=dead.SELECTOR, owner_code=OWNER_CODE):
    g_code = G_PREFIX + G_KILL + G_BODY if g_code is None else g_code
    raw = assemble(OWNER, owner_code) + struct.pack('<I', DATA)
    bodies = {OWNER: raw, F: assemble(F, F_CODE), G: assemble(G, g_code)}
    rom = bytearray(ROM_SIZE)
    for start, body in bodies.items():
        rom[start - match.ROM_BASE:start - match.ROM_BASE + len(body)] = body
    rows = [dict(rom=f'0x{a:08X}', end=f'0x{a + len(b):08X}', mode='thumb', instrs=0)
            for a, b in sorted(bodies.items())]
    mapping = json.dumps(rows).encode()
    for row in rows:
        start = int(row['rom'], 16)
        row['instrs'] = owner.refine(bodies[start], start, mapping)['instrs']
        mapping = json.dumps(rows).encode()
    _, _, _, calls, _ = graph.graph(raw, OWNER, owner.refine(raw, OWNER, mapping))
    return dict(data=raw, address=OWNER, rom=bytes(rom), mapping=mapping,
        index=''.join(f'{int(r["rom"], 16):08X} {int(r["end"], 16):08X} '
                      f'{int(r["end"], 16) - int(r["rom"], 16)} {r["instrs"]} return\n'
                      for r in rows).encode(),
        objects=json.dumps({'data_02000000': '0x02000000'}).encode(),
        bindings=dict(calls=[[site - OWNER, f'func_{target:08X}'] for site, target in sorted(calls.items())],
                      data=[[len(raw) - 4, 'data_02000000', 0]], functions=[], switches=[]),
        selector=selector)


def evidence(manifest):
    return manifest['proof']['buffers']['dead_argument_aliases']


class KillingInstructionTests(unittest.TestCase):
    R1 = match.ARM_REG_R0 + 1

    def kill(self, tokens):
        return dead.killing_instruction(assemble(G, tokens), G, self.R1)

    def test_written_before_read(self):
        self.assertEqual(self.kill(G_PREFIX + G_KILL + G_BODY), 4)
        self.assertEqual(self.kill([0x4900, 0x4770]), 0)          # ldr r1,[pc]: a literal load
        self.assertEqual(self.kill([0xb510, 0x1c01, 0x4770]), 2)  # adds r1,r0,#0

    def test_read_or_control_transfer_first_refuses(self):
        for name, tokens in (
                ('read', [0x1c08, 0x2100, 0x4770]),               # adds r0,r1,#0
                ('read and write', [0x3101, 0x4770]),             # adds r1,#1
                ('load through it', [0x6809, 0x4770]),            # ldr r1,[r1]
                ('pushed', [0xb502, 0x2100, 0x4770]),             # push {r1,lr}
                ('branch', [0xe7ff, 0x2100, 0x4770]),             # b .+2
                ('conditional branch', [0xd0ff, 0x2100, 0x4770]),  # beq .+2
                ('call', [0xb500, 0x08000000, 0x2100, 0x4770]),   # bl
                ('return', [0x4770, 0x2100]),                     # bx lr
                ('never written', [0x2000, 0x2200])):
            with self.subTest(name):
                self.assertIsNone(self.kill(tokens))

    def test_only_armv4t_16_bit_forms_are_stepped_over(self):
        R0 = match.ARM_REG_R0
        # review B1, func_08141874: `svc #6; adds r0,r1,#0` - the BIOS reads R0
        self.assertIsNone(dead.killing_instruction(assemble(G, [0xdf06, 0x1c08, 0x4770]), G, R0))
        for name, tokens in (
                ('svc', [0xdf00, 0x2100, 0x4770]),
                # review B2: Thumb-2 `mov.w r1,#0`; on ARM7TDMI a BL prefix and `lsls r0,r0,#4`
                ('32-bit decode', [0xf04f, 0x0100, 0x4770]),
                ('bkpt', [0xbe00, 0x2100, 0x4770]),
                ('udf', [0xde00, 0x2100, 0x4770]),
                ('mov sp, r0', [0x4685, 0x2100, 0x4770]),
                ('low-low hi-register mov (ARMv6)', [0x4601, 0x4770]),   # mov r1,r0
                ('uxtb (ARMv6)', [0xb2c9, 0x4770]),                      # uxtb r1,r1
                ('pop', [0xbc02, 0x4770]),
                # review L1: ADD SP moves SP up into the owner frame before a PUSH
                ('add sp before the kill', [0xb002, 0xb404, 0x2100, 0x4770])):
            with self.subTest(name):
                self.assertIsNone(self.kill(tokens))
        # the kills agbcc emits stay admitted
        for tokens, offset in (([0xb500, 0xb082, 0x4669, 0x4770], 4),   # push; sub sp; mov r1,sp
                               ([0x4641, 0x4770], 0),                   # mov r1,r8
                               ([0xa901, 0x4770], 0)):                  # add r1,sp,#4
            with self.subTest(tokens=tokens):
                self.assertEqual(self.kill(tokens), offset)
        self.assertIsNone(self.kill([0x4689, 0x2100, 0x4770]))          # mov r9,r1 reads it


class DeadArgumentBufferTests(unittest.TestCase):
    def test_stale_alias_overwritten_by_callee_is_not_passed(self):
        manifest, _ = owner.verify(**fixture())
        self.assertEqual(manifest['profile'], dead.SCHEMA)
        calls = evidence(manifest)['calls']
        self.assertEqual(len(calls), 1)
        call = calls[0]
        self.assertEqual((call['callee'], call['site'], call['dead'], call['passed']),
                         (f'func_{G:08X}', OWNER + 14, [['r1', -8, 4]], []))
        g_raw = assemble(G, G_PREFIX + G_KILL + G_BODY)
        self.assertEqual((call['end'], call['body_sha256']), (G + len(g_raw), dead.sha(g_raw)))
        # G received no alias, so it is not walked; F still is
        walked = [r['address'] for r in manifest['proof']['buffers']['dependencies']]
        self.assertIn(F, walked)
        self.assertNotIn(G, walked)

    def test_default_named_buffer_walk_still_refuses(self):
        with self.assertRaisesRegex(ValueError, 'buffer callee 0x08012000'):
            owner.verify(**fixture(selector='named-data-buffer-v1'))

    def test_live_or_unproved_aliases_are_still_walked(self):
        for name, g_code in (
                ('read first', G_PREFIX + [0x1c08] + G_KILL + G_BODY),     # adds r0,r1,#0
                ('branch first', G_PREFIX + [0xe7ff] + G_KILL + G_BODY),   # b .+2
                ('call first', G_PREFIX + [F] + G_KILL + G_BODY)):
            with self.subTest(name), self.assertRaisesRegex(ValueError, 'buffer callee 0x08012000'):
                owner.verify(**fixture(g_code))

    def test_remaining_live_alias_keeps_the_walk(self):
        # add r0,sp,#0 instead of movs r0,#2: R0 is a live alias of G, R1 is dead,
        # so G is walked with R0 alone and its own frame arithmetic still refuses
        code = list(OWNER_CODE)
        code[5] = 0xa800
        with self.assertRaisesRegex(ValueError, 'buffer callee 0x08012000'):
            owner.verify(**fixture(owner_code=code))

    def test_manifest_tampering_refuses(self):
        args = fixture()
        manifest, _ = owner.verify(**args)
        for name, edit in (
                ('kill offset', lambda p: p['calls'][0]['dead'][0].__setitem__(2, 2)),
                ('body hash', lambda p: p['calls'][0].__setitem__('body_sha256', '0' * 64)),
                ('register', lambda p: p['calls'][0]['dead'][0].__setitem__(0, 'r0')),
                ('dropped call', lambda p: p.__setitem__('calls', []))):
            changed = copy.deepcopy(manifest)
            edit(changed['proof']['buffers']['dead_argument_aliases'])
            with self.subTest(name), self.assertRaises(ValueError):
                owner.verify(**args, manifest=changed)

    def test_profile_requires_a_discounted_alias(self):
        proof = dead.DeadArgumentBufferProof(b'', b'[]', b'', b'{}')
        with self.assertRaisesRegex(ValueError, 'requires a discounted'):
            proof.dead_argument_manifest()


if __name__ == '__main__':
    unittest.main()
