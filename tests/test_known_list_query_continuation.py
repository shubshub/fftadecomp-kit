"""Known query continuation, adversarial frames and an independent raw oracle."""
import copy
import json
from pathlib import Path
import struct
import subprocess
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import owner_admission_profile as owner
import named_data_buffer_profile as named
import known_list_query_continuation_profile as query
import known_list_query_closure_profile as known

A, B = 0x08010000, 0x08011000


def bl(site, target):
    value = target-site-4
    return struct.pack('<HH', 0xf000 | ((value >> 12) & 0x7ff),
                       0xf800 | ((value >> 1) & 0x7ff))


def fixture(extra=(), helper=None, indirect=False, kill=True):
    tokens = [0xb530, 0xb083, 0x1c04, 0x1c0d, 0x9500, 0x2000, 0x9002,
              0x6920, 'callback', 0x466a, query.ITERATOR, *extra]
    if helper is not None:
        tokens.append(B)
    if indirect:
        if kill:
            tokens.append(0x2200)
        tokens.extend(('slot', 0x681b, 0x2000, 0x2100, 0x08142250))
    tokens.extend((0x9802, 0xb003, 0xbc30, 0xbc02, 0x4708))
    raw, loads, calls = bytearray(), {}, []
    for token in tokens:
        if isinstance(token, str):
            loads[token] = len(raw)
            raw += b'\0\0'
        elif token >= 0x08000000:
            calls.append([len(raw), '_call_via_r3' if token == 0x08142250 else f'func_{token:08X}'])
            raw += bl(A+len(raw), token)
        else:
            raw += struct.pack('<H', token)
    if len(raw) % 4:
        raw += b'\0\0'
    functions, objects = [], []
    for name, register, value in [('callback', 1, query.CALLBACK | 1), ('slot', 3, 0x02000020)]:
        if name not in loads:
            continue
        offset = len(raw)
        struct.pack_into('<H', raw, loads[name], 0x4800 | register << 8 |
                         ((offset-((loads[name]+4)&~3))//4))
        raw += struct.pack('<I', value)
        if name == 'callback':
            functions.append([offset, f'func_{query.CALLBACK:08X}'])
        else:
            objects.append([offset, 'callback_slot', 0])
    bodies = {start: bytes.fromhex(encoded) for start, (_, encoded) in known.DEPENDENCIES.items()
              if start != 0x08022194}
    bodies[A] = bytes(raw)
    if helper is not None:
        bodies[B] = struct.pack('<'+'H'*len(helper), *helper)
    if indirect:
        bodies[0x08142250] = bytes.fromhex('1847')
    rom = bytearray(0x142260)
    rows = []
    for start, body in sorted(bodies.items()):
        rom[start-match.ROM_BASE:start-match.ROM_BASE+len(body)] = body
        count = known.DEPENDENCIES[start][0] if start in known.DEPENDENCIES else len(body)//2
        rows.append(dict(rom=f'0x{start:08X}', end=f'0x{start+len(body):08X}',
                         mode='thumb', instrs=count))
    rom[0x14225e:0x142260] = bytes.fromhex('c046')
    if indirect:
        rom[0x142252:0x142254] = bytes.fromhex('c046')
    return dict(data=bytes(raw), address=A, rom=bytes(rom), mapping=json.dumps(rows).encode(),
                index=''.join(f'{r["rom"][2:]} {r["end"][2:]} '
                    f'{int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n'
                    for r in rows).encode(), objects=b'{"callback_slot":"0x02000020"}',
                bindings=dict(calls=calls, data=objects, functions=functions, switches=[]),
                selector=query.SELECTOR)


def changed_root(f, offset, halfword):
    f = copy.deepcopy(f)
    raw, rom = bytearray(f['data']), bytearray(f['rom'])
    struct.pack_into('<H', raw, offset, halfword)
    rom[A-match.ROM_BASE:A-match.ROM_BASE+len(raw)] = raw
    return dict(f, data=bytes(raw), rom=bytes(rom))


def raw_query(rom, keys):
    """Independent concrete Thumb loop; no proof/Capstone operation helpers."""
    memory, reads = {}, []
    def put(address, value):
        for n in range(4):
            memory[address+n] = (value >> (8*n)) & 255
    def get(address):
        reads.append(address)
        if match.ROM_BASE <= address < match.ROM_BASE+len(rom):
            return int.from_bytes(rom[address-match.ROM_BASE:address-match.ROM_BASE+4], 'little')
        return sum(memory[address+n] << (8*n) for n in range(4))
    regs = [0x20000+n for n in range(16)]
    regs[0], regs[1], regs[13], regs[14] = 0x02001000, 0x02004000, 0x03001000, 0x09000001
    saved = tuple(regs[4:12])
    put(regs[0]+16, 0x02002000)
    nodes = [0x02003000+32*n for n in range(len(keys))]
    objects = [0x02005000+32*n for n in range(len(keys))]
    put(0x02002004, nodes[0] if nodes else 0)
    for n, key in enumerate(keys):
        put(nodes[n], objects[n]); put(nodes[n]+8, nodes[n+1] if n+1 < len(nodes) else 0)
        put(objects[n], key)
    opaque_address = regs[13]-20
    put(opaque_address, 0xa5c33ca5)
    pc, equal = A, False
    for _ in range(2000):
        if pc == 0x09000000:
            assert regs[13] == 0x03001000 and tuple(regs[4:12]) == saved
            assert opaque_address not in reads
            return regs[0], regs[2], objects
        code = int.from_bytes(rom[pc-match.ROM_BASE:pc-match.ROM_BASE+2], 'little')
        following = pc+2
        if code & 0xf800 == 0xf000:
            low = int.from_bytes(rom[pc-match.ROM_BASE+2:pc-match.ROM_BASE+4], 'little')
            high = code & 0x7ff
            if high & 0x400:
                high -= 0x800
            following = pc+4+(high << 12)+((low & 0x7ff) << 1)
            regs[14] = (pc+4) | 1
        elif code & 0xfe00 in (0xb400, 0xbc00):
            numbers = [n for n in range(8) if code & 1 << n]
            pushing = code & 0xfe00 == 0xb400
            if code & 0x100:
                numbers.append(14 if pushing else 15)
            if pushing:
                regs[13] -= 4*len(numbers)
                for n, register in enumerate(numbers): put(regs[13]+4*n, regs[register])
            else:
                for n, register in enumerate(numbers): regs[register] = get(regs[13]+4*n)
                regs[13] += 4*len(numbers)
        elif code & 0xff87 == 0x4700:
            following = regs[(code >> 3) & 15] & ~1
        elif code & 0xff00 == 0xb000:
            regs[13] += (-4 if code & 0x80 else 4)*(code & 0x7f)
        elif code & 0xfe00 == 0x1c00:
            regs[code & 7] = regs[(code >> 3) & 7] + ((code >> 6) & 7)
        elif code & 0xff00 == 0x4600:
            regs[(code & 7) | ((code >> 4) & 8)] = regs[(code >> 3) & 15]
        elif code & 0xf800 == 0x2000:
            regs[(code >> 8) & 7] = code & 255
        elif code & 0xf000 == 0x9000:
            register, at = (code >> 8) & 7, regs[13]+4*(code & 255)
            if code & 0x800: regs[register] = get(at)
            else: put(at, regs[register])
        elif code & 0xf800 == 0x4800:
            regs[(code >> 8) & 7] = get(((pc+4)&~3)+4*(code & 255))
        elif code & 0xf000 == 0x6000:
            register, base = code & 7, (code >> 3) & 7
            at = regs[base]+4*((code >> 6) & 31)
            if code & 0x800: regs[register] = get(at)
            else: put(at, regs[register])
        elif code & 0xf800 == 0x2800:
            equal = regs[(code >> 8) & 7] == code & 255
        elif code & 0xffc0 == 0x4280:
            equal = regs[code & 7] == regs[(code >> 3) & 7]
        elif code & 0xf000 == 0xd000:
            condition = (code >> 8) & 15
            assert condition in (0, 1)
            displacement = code & 255
            if displacement & 128: displacement -= 256
            if equal == (condition == 0): following = pc+4+2*displacement
        elif code & 0xf800 == 0xe000:
            displacement = code & 0x7ff
            if displacement & 0x400: displacement -= 0x800
            following = pc+4+2*displacement
        else:
            raise AssertionError(f'raw oracle unsupported {pc:08X}: {code:04X}')
        pc = following
    raise AssertionError('raw oracle instruction bound exhausted')


class QueryContinuationTests(unittest.TestCase):
    def test_cli_exposes_only_registered_query_selector(self):
        command = [sys.executable, '-B', str(Path(match.__file__))]
        good = subprocess.run(command + ['--owner-runtime-profile', query.SELECTOR, '--help'],
                              capture_output=True, text=True)
        self.assertEqual(good.returncode, 0, good.stderr)
        self.assertIn(query.SELECTOR, good.stdout)
        bad = subprocess.run(command + ['--owner-runtime-profile', query.SELECTOR + '-unknown', '--help'],
                             capture_output=True, text=True)
        self.assertEqual(bad.returncode, 2)
        self.assertIn('invalid choice', bad.stderr)

    def test_complete_query_retains_possible_r2_until_normal_root_return(self):
        manifest, _ = owner.verify(**fixture())
        proof = manifest['proof']
        self.assertEqual(manifest['profile'], query.SCHEMA)
        self.assertEqual(proof['query']['calls'][0]['conservative_return_aliases'], [[2, -24]])
        self.assertEqual(proof['query']['root_return_R2'], [(A+32, -24)])
        self.assertEqual(len(proof['buffers']['dependencies']), 4)

    def test_raw_thumb_empty_miss_and_found_paths(self):
        f = fixture()
        for keys, found_index in [([], None), ([0x10], None), ([0x02004000], 0),
                                  ([0x10, 0x02004000, 0x20], 1)]:
            with self.subTest(keys=keys):
                result, scratch, objects = raw_query(f['rom'], keys)
                self.assertEqual(result, 0 if found_index is None else objects[found_index])
                self.assertEqual(scratch, 0x03001000-24 if not keys else
                                 objects[-1 if found_index is None else found_index])

    def test_unknown_key_or_nonzero_result_initialization_is_rejected(self):
        for offset, opcode in [(8, 0x9501), (10, 0x2001), (12, 0x9001)]:
            with self.subTest(offset=offset), self.assertRaisesRegex(ValueError, 'initialized'):
                owner.verify(**changed_root(fixture(), offset, opcode))

    def test_key_cannot_be_private_or_saved_return_provenance(self):
        for opcode in (0x466d, 0x4675):
            with self.subTest(opcode=opcode), self.assertRaises(ValueError):
                owner.verify(**changed_root(fixture(), 6, opcode))

    def test_initialization_must_not_write_saved_frame(self):
        with self.assertRaisesRegex(ValueError, 'protected saves'):
            owner.verify(**changed_root(fixture(), 8, 0x9503))

    def test_prefix_cannot_be_bypassed_or_reentered(self):
        with self.assertRaises(ValueError):
            owner.verify(**changed_root(fixture(), 4, 0xe001))
        with self.assertRaises(ValueError):
            owner.verify(**fixture(extra=(0xe7f4,)))

    def test_canonical_dependency_bytes_count_and_padding_are_required(self):
        for part in ('body', 'count', 'padding', 'missing'):
            f = fixture()
            if part in ('body', 'padding'):
                rom = bytearray(f['rom']);rom[0x9ab5c if part == 'body' else 0x14225e] ^= 1
                f['rom'] = bytes(rom)
            else:
                rows = json.loads(f['mapping'])
                if part == 'count':
                    next(r for r in rows if r['rom'] == '0x0809AB5C')['instrs'] += 1
                else:
                    rows = [r for r in rows if r['rom'] != '0x080C7B74']
                f['mapping'] = json.dumps(rows).encode()
            with self.subTest(part=part), self.assertRaises(ValueError): owner.verify(**f)

    def test_live_r2_local_access_is_bounded(self):
        owner.verify(**fixture(extra=(0x6890,)))
        for opcode in (0x68d0, 0x60d0):
            with self.subTest(opcode=opcode), self.assertRaisesRegex(ValueError, 'allocated local'):
                owner.verify(**fixture(extra=(opcode,)))

    def test_live_r2_ordinary_callee_effects_are_checked(self):
        manifest, _ = owner.verify(**fixture(helper=(0x2200, 0x2000, 0x4770)))
        self.assertIn(B, [r['address'] for r in manifest['proof']['buffers']['dependencies']])
        with self.assertRaises(ValueError):
            owner.verify(**fixture(helper=(0x60d0, 0x2000, 0x4770)))

    def test_indirect_argument_is_rejected_until_real_kill(self):
        owner.verify(**fixture(indirect=True))
        with self.assertRaisesRegex(ValueError, 'local argument aliases'):
            owner.verify(**fixture(indirect=True, kill=False))

    def test_root_return_does_not_discard_r0_alias(self):
        f = fixture()
        with self.assertRaisesRegex(ValueError, 'escapes through a return'):
            owner.verify(**changed_root(f, 24, 0x1C10))

    def test_genuine_callback_binding_and_manifest_cannot_be_substituted(self):
        f = fixture(); manifest, _ = owner.verify(**f)
        f['bindings']['functions'] = []
        with self.assertRaisesRegex(ValueError, 'genuine callback'): owner.verify(**f)
        changed = copy.deepcopy(manifest)
        changed['proof']['query']['calls'][0]['conservative_return_aliases'] = []
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            owner.verify(**dict(fixture(), manifest=changed))

    def test_only_registered_policy_receives_root_scratch_and_guards(self):
        f = fixture()
        with self.assertRaises(ValueError): owner.verify(**dict(f, selector=named.SCRATCH_SELECTOR))
        class Unregistered(query.KnownListQueryContinuationProof):
            pass
        instance = Unregistered(f['rom'], f['mapping'], f['index'], f['objects'])
        aliases = {match.ARM_REG_R0+2: -24}
        self.assertEqual(query.root_return_aliases(instance, f['data'], A, A+34, aliases), aliases)
        self.assertFalse(named.conditional_thunk_replay(instance))

    def test_report_roundtrip_selects_explicit_policy(self):
        f = fixture(); manifest, _ = owner.verify(**f)
        rendered = owner.render(A, (f['data'], manifest, 'synthetic', f['mapping'],
                                   f['index'], f['objects'], f['rom'], 1, b'synthetic'))
        self.assertTrue(owner.selected(rendered))
        self.assertEqual(owner.selector_for_report(rendered), query.SELECTOR)
        self.assertIn('* control flow: '+query.CONTROL_FLOW, rendered)


if __name__ == '__main__':
    unittest.main(verbosity=2)
