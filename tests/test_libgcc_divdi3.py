import argparse
import copy
import json
import os
from pathlib import Path
import random
import struct
import subprocess
import tempfile
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'tools'))
import libgcc_divdi3 as division
import libgcc_divdi3_bounds as bounds
import library_units as units
import match
import match_evidence as evidence
import owner_admission_profile as owner
import owner_graph_profile as graph
from test_unit_double_add_parts import OriginalCPU

A, TABLE = division.ADDRESS, division.TABLE
MASK = (1 << 32)-1


def quotient(n, d):
    return (abs(n)//abs(d)) * (-1 if (n < 0) != (d < 0) else 1)


def machine(case, rom):
    driver = OriginalCPU(case, rom)
    page = TABLE & ~4095
    end = (TABLE + 256 + 4095) & ~4095
    driver.uc.mem_map(page, end-page)
    driver.uc.mem_write(page, rom[page-match.ROM_BASE:end-match.ROM_BASE])
    return driver


@unittest.skipUnless(os.getenv('FFTA_LIBGCC_DIVDI3_ROOT'), 'requires the original USA ROM, both compilers and libgcc2 source')
class SignedWideDivisionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        from rompath import rom_path
        cls.root = Path(os.environ['FFTA_LIBGCC_DIVDI3_ROOT']).resolve()
        cls.rom = Path(rom_path(cls.root)).read_bytes()
        cls.mapping = evidence.mapping_snapshot(cls.root)
        cls.body, cls.report = division.build(cls.root, A)
        old = units.resolve('old-agbcc-O2-v1')
        runner = match.Runner(old['cc'], root=cls.root, timeout=120)
        args = argparse.Namespace(cc=old['cc'], flags=old['flags'], cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                                  linker=match.DEFAULT_LD, objcopy=match.DEFAULT_OBJCOPY)
        with runner.workspace() as workspace:
            _, _, cls.original = match.compile_object(runner, workspace, args, cls.root, A, 'src/08142280.c')
            cls.linked = match.link_typed_targets(runner, workspace, args, 'func_08142280', A, division.TARGETS,
                                                  set(), libgcc_divdi3_table=True)

    def test_elf_section_symbol_and_relocations(self):
        for mutation in ('original-kind','table-size','table-global','section-as-object','helper-target','rel-type',
                         'abs-addend','call-addend','missing-rel','writable','bytes','linked-placement',
                         'linked-thumb','linked-size','linked-bytes','extra-alloc'):
            linked = mutation.startswith('linked-')
            image = copy.deepcopy(self.linked if linked else self.original)
            ro = image['section_names'].index('.rodata')
            tab = next(s for s in image['symbols'] if s['name'] == '__clz_tab')
            helper = next(s for s in image['symbols'] if s['name'] == '__udivsi3')
            if mutation == 'original-kind':
                image['type'] = 2
            elif mutation == 'table-size':
                tab['size'] -= 1
            elif mutation == 'table-global':
                tab['bind'] = 1
            elif mutation in ('writable', 'linked-placement', 'extra-alloc'):
                idx = image['section_names'].index('.ARM.attributes') if mutation == 'extra-alloc' else ro
                sec = list(image['sections'][idx])
                sec[3 if mutation == 'linked-placement' else 2] += 4 if mutation == 'linked-placement' else (
                    2 if mutation == 'extra-alloc' else 1)
                image['sections'][idx] = tuple(sec)
            elif mutation == 'bytes':
                image['section_data'][ro] = bytes(256)
            elif mutation in ('abs-addend', 'call-addend', 'linked-bytes'):
                body = bytearray(image['text'])
                off = 0x12c if mutation == 'abs-addend' else 0xb4 if mutation == 'call-addend' else 0x34
                body[off] ^= 4
                image['text'] = bytes(body)
            elif mutation == 'linked-thumb':
                helper['value'] &= ~1
            elif mutation == 'linked-size':
                helper['size'] = 4
            else:
                rel, = image['relocations']
                syms = image['symbol_tables'][image['sections'][rel][6]]
                rows = list(struct.iter_unpack('<II', image['section_data'][rel]))
                off = 0x12c if mutation in ('section-as-object','rel-type') else 0xb4
                pos = next(i for i, row in enumerate(rows) if row[0] == off)
                info = rows[pos][1]
                if mutation == 'section-as-object':
                    info = syms.index(tab)*256+2
                elif mutation == 'helper-target':
                    info = syms.index(helper)*256+10
                elif mutation == 'rel-type':
                    info = info//256*256+10
                if mutation == 'missing-rel':
                    rows.pop(pos)
                else:
                    rows[pos] = (off, info)
                image['section_data'][rel] = b''.join(struct.pack('<II', *row) for row in rows)
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                if linked:
                    division.linked_member(image, self.rom, self.mapping)
                else:
                    division.original_bindings(image)

    def test_original_table_index_operators_and_all_predecessors(self):
        def parts(body):
            ref = owner.refine(body, A, self.mapping)
            ins, edges, _, _, words = graph.graph(body, A, ref)
            return ins, edges, graph.partition(body, A, ref, ins, words)
        ins, edges, partition = parts(self.body)
        self.assertEqual(len(bounds.table_reads(ins, edges, partition)['reads']), 3)
        for site, code in ((0x081422cc, bytes.fromhex('0f1c')), (0x081422e2, b'\x07\xdc'),
                           (0x081423ca, b'\x01\x22'), (0x08142550, b'\x87\x42'),
                           (0x08142558, b'\x91\x40'), (A+0x12c, struct.pack('<I',TABLE+1))):
            mutant = bytearray(self.body)
            mutant[site-A:site-A+len(code)] = code
            with self.subTest(site=hex(site)), self.assertRaises((ValueError, KeyError)):
                bounds.table_reads(*parts(bytes(mutant)))
        bypass = dict(edges)
        bypass[A] = (*bypass[A], 0x08142558)
        with self.assertRaisesRegex(ValueError, 'no entry'):
            bounds.table_reads(ins, bypass, partition)

    def test_canonical_report_and_selector_scope(self):
        report = (self.root/'docs/match/08142280.md').read_text()
        self.assertEqual(report, self.report)
        self.assertTrue(evidence.report_matches(report, self.root, A))
        for old,new in (('"width":1','"width":4'), ('"old-agbcc-O2-v1":','"other-compiler":'),
                        ('* compiled : `','* compiled : `00')):
            self.assertIn(old, report)
            self.assertFalse(evidence.report_matches(report.replace(old,new), self.root, A))
        self.assertFalse(evidence.report_matches(report, self.root, A+2))
        for extra in (['--control-flow-profile','mixed-return-inert-spin-v1'], ['--mode','arm'], ['--addr','0x08142AB0']):
            target = extra[-1] if extra[0] == '--addr' else hex(A)
            flags = [] if extra[0] == '--addr' else extra
            cmd = [sys.executable, str(Path(match.__file__)), '--root', str(self.root), '--no-write',
                   '--owner-runtime-profile', division.SELECTOR, *flags, target]
            run = subprocess.run(cmd, capture_output=True, text=True)
            self.assertNotEqual(run.returncode, 0)
            self.assertNotIn('verdict MATCH', run.stdout)
            self.assertNotIn('invalid choice', run.stderr)

    def test_status_recompiles_signed_division_from_its_saved_report(self):
        import status
        self.assertTrue((self.root/'src/08142280.c').is_file())
        result = status.collect(str(self.root), verify=True, quiet=True)
        self.assertFalse(any(problem.startswith('08142280:') for problem in result[4]), result[4])

    def test_source_table_and_original_caller_index_negatives(self):
        with tempfile.TemporaryDirectory(dir=self.root/'build') as temp:
            stage = Path(temp)
            for part in ('config', 'symbols', 'include', 'baserom.bin'):
                (stage/part).symlink_to(self.root/part)
            (stage/'src').mkdir()
            path = stage/'src/08142280.c'
            text = (self.root/'src/08142280.c').read_text()
            path.write_text(text.replace('1 / d0;', '0;'))
            with self.assertRaisesRegex(ValueError, 'reviewed libgcc2 arithmetic'):
                division.build(stage, A)
        index = division.runtime.index_snapshot(self.root)
        entry = json.loads(self.mapping)
        next(row for row in entry if int(row['rom'],16)==0x08127458)['instrs'] = 157
        with self.assertRaises(ValueError):
            division.native_context(self.rom, json.dumps(entry).encode(), index)
        damaged = bytearray(self.rom)
        damaged[TABLE-match.ROM_BASE+255] ^= 1
        with self.assertRaisesRegex(ValueError, 'both fully linked ROM sections'):
            division.linked_member(self.linked, bytes(damaged), self.mapping)
        with self.assertRaisesRegex(ValueError, 'original owner and helpers'):
            match.link_typed_targets(None, None, None, 'func_08142280', A+4, division.TARGETS, set(),
                                     libgcc_divdi3_table=True)

    def test_original_signed_quotients_table_accesses_and_abi(self):
        from unicorn import UC_HOOK_CODE, UC_HOOK_MEM_READ
        driver = machine(self, self.rom)
        uc, arm = driver.uc, driver.arm
        visits, indices = set(), set()
        def read(cpu, access, address, size, _, context):
            self.assertEqual(size, 1)
            self.assertTrue(TABLE <= address < TABLE+256)
            visits.add(cpu.reg_read(arm.UC_ARM_REG_PC))
            indices.add(address-TABLE)
        def helper(cpu, address, size, context):
            self.assertNotEqual(cpu.reg_read(arm.UC_ARM_REG_R1), 0)
        page = TABLE & ~4095
        uc.hook_add(UC_HOOK_MEM_READ, read, begin=page, end=(TABLE+255)|4095)
        for target in division.TARGETS.values():
            uc.hook_add(UC_HOOK_CODE, helper, begin=target, end=target)
        lo, hi = -(1<<63), (1<<63)-1
        boundaries = [lo,lo+1,-(1<<62),-(1<<33),-(1<<32),-(1<<31),-65536,-3,-1,
                      0,1,2,3,255,256,65535,65536,(1<<24)-1,1<<24,(1<<32)-1,1<<32,(1<<33)+3,1<<62,hi]
        cases = {(n,d) for n in boundaries for d in boundaries if d and (n,d) != (lo,-1)}
        rng = random.Random(A)
        for bits in (8,16,31,32,33,63):
            for _ in range(30):
                cases.add((rng.randint(lo,hi), rng.randint(-(1<<bits),(1<<bits)-1) or 1))
        for n,d in sorted(cases):
            low,high = driver.invoke(A, tuple(x & MASK for x in (n,n>>32,d,d>>32)))
            self.assertEqual(low | high<<32, quotient(n,d) % (1<<64))
        self.assertEqual(visits, {0x08142304,0x081423e8,0x0814255c})
        self.assertTrue({1,255} <= indices)

    def test_both_original_movement_callers(self):
        from unicorn import UC_HOOK_CODE
        driver = machine(self, self.rom)
        uc, arm = driver.uc, driver.arm
        state, output = 0x02000100, 0x02000700
        arguments = []
        def enter(cpu, address, size, _):
            low, high, dlo, dhi = [cpu.reg_read(r) for r in driver.registers]
            arguments.append((low | high<<32, dlo | dhi<<32))
        uc.hook_add(UC_HOOK_CODE, enter, begin=A, end=A)
        for distance,duration in ((0,1),(7,3),(65535,65534)):
            uc.reg_write(arm.UC_ARM_REG_R2, distance)
            uc.reg_write(arm.UC_ARM_REG_R6, state)
            uc.reg_write(arm.UC_ARM_REG_SP, driver.stack)
            uc.mem_write(state+12, struct.pack('<H', duration))
            uc.emu_start(0x081274cb, 0x081274fa, count=15000)
            self.assertEqual(uc.reg_read(arm.UC_ARM_REG_PC), 0x081274fa)
            self.assertEqual(arguments[-1], (distance<<32, duration<<16))
            self.assertEqual(uc.mem_read(state+0x48,8), struct.pack('<Q', (distance<<16)//duration))
        for position,step,limit in ((2,3,9),(6,3,8),(0,4,4)):
            final = min(position+step, limit)
            index = final//step
            uc.mem_write(state+4, struct.pack('<I', output))
            uc.mem_write(state+0x48, struct.pack('<3q',step,position,limit))
            uc.mem_write(state+0xc0, struct.pack('<4H',0x1810,0x2820,0x3830,0x4840))
            low,_ = driver.invoke(0x08127c94,(state,0,0,0))
            self.assertEqual(arguments[-1], (final<<16, step))
            self.assertEqual(low, int(final == limit))
            self.assertEqual(uc.mem_read(output+10,2), uc.mem_read(state+0xc0+2*index,2))
