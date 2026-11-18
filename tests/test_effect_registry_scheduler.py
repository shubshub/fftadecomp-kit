"""Original USA effect registry lookups, object predicates, scheduler call and returning callbacks."""
import copy
import os
from pathlib import Path
import struct
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'tools'))
import effect_registry_scheduler as registry
import match


class RegistryMachine:
    SP, DONE = 0x03007300, 0x080000D0
    ACTOR, LINK, LEAF = 0x02003000, 0x02003100, 0x02003200
    MANAGER, PARENT, TASK = 0x02004000, 0x02005000, 0x02006000

    def __init__(self, rom):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_CODE
        import unicorn.arm_const as reg
        from scheduler_zero_descriptor import IMAGE, DESTINATION
        self.reg, self.rom = reg, rom
        u = self.u = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        u.mem_map(match.ROM_BASE, len(rom))
        u.mem_write(match.ROM_BASE, rom)
        u.mem_map(0x02000000, 0x40000)
        u.mem_map(0x03000000, 0x8000)
        u.mem_write(DESTINATION, rom[IMAGE-match.ROM_BASE:IMAGE-match.ROM_BASE+176])
        for address in (0x080D3552, 0x080D356A, 0x080D3592, 0x080D3BA6, registry.sites.DIRECT,
                        0x08007138, 0x08142250):
            u.hook_add(UC_HOOK_CODE, self.observe, begin=address, end=address)

    def word(self, address):
        return struct.unpack('<I', self.u.mem_read(address, 4))[0]

    def observe(self, u, pc, size, _):
        r = self.reg
        if pc in (0x080D3552, 0x080D356A, 0x080D3592, 0x080D3BA6):
            reg, offs = {0x080D3552: (r.UC_ARM_REG_R0,0), 0x080D356A: (r.UC_ARM_REG_R1,0),
                         0x080D3592: (r.UC_ARM_REG_R0,6), 0x080D3BA6: (r.UC_ARM_REG_R1,6)}[pc]
            self.reads.append((pc, (u.reg_read(reg)+offs)&0xffffffff))
        elif pc == registry.sites.DIRECT:
            manager, cb, count, descriptor = [u.reg_read(a) for a in
                (r.UC_ARM_REG_R0, r.UC_ARM_REG_R1, r.UC_ARM_REG_R2, r.UC_ARM_REG_R3)]
            self.site = (manager, cb, count, descriptor, self.word(u.reg_read(r.UC_ARM_REG_SP)),
                         bytes(u.mem_read(descriptor,28)))
            if self.stop == 'site':
                u.emu_stop()
        elif pc == 0x08007138:
            self.allocation_size = u.reg_read(r.UC_ARM_REG_R1)
            u.reg_write(r.UC_ARM_REG_R0, self.target)
            u.reg_write(r.UC_ARM_REG_PC, u.reg_read(r.UC_ARM_REG_LR))
        else:
            cb, task, desc, payload = [u.reg_read(a) for a in
                (r.UC_ARM_REG_R3, r.UC_ARM_REG_R0, r.UC_ARM_REG_R1, r.UC_ARM_REG_R2)]
            self.dispatch = (cb, task, bytes(u.mem_read(desc,28)), payload)
            if self.stop == 'dispatch':
                u.emu_stop()

    def run(self, effect, arg, *, category=5, flags=8, parent=0, target=None, seed=0xA5, stop='site'):
        r, u = self.reg, self.u
        self.stop, self.target = stop, self.TASK if target is None else target
        self.reads, self.site, self.dispatch, self.allocation_size = [], None, None, None
        for address in (self.MANAGER, self.PARENT, self.TASK):
            u.mem_write(address, bytes(1024))
        u.mem_write(self.SP-320, bytes([seed])*320)
        for address, value in ((0x0200F430,self.MANAGER), (0x020159C0,parent),
                               (self.ACTOR,self.LINK), (self.LINK,self.LEAF if category is not None else 0)):
            u.mem_write(address, struct.pack('<I',value))
        u.mem_write(self.ACTOR+4, struct.pack('<H',flags))
        u.mem_write(self.LEAF+6, bytes([category or 0]))
        for reg, value in ((r.UC_ARM_REG_R0,effect), (r.UC_ARM_REG_R1,self.ACTOR), (r.UC_ARM_REG_R2,arg),
                           (r.UC_ARM_REG_SP,self.SP), (r.UC_ARM_REG_LR,self.DONE|1)):
            u.reg_write(reg,value)
        u.emu_start(registry.OWNER|1, self.DONE, count=5000)
        return u.reg_read(r.UC_ARM_REG_PC)


@unittest.skipUnless(os.environ.get('FFTA_EFFECT_REGISTRY_ROOT'), 'requires the reviewed game source and USA ROM')
class NativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        from inert_spin_profile import index_snapshot
        from rompath import rom_path
        cls.root = Path(os.environ['FFTA_EFFECT_REGISTRY_ROOT']).resolve()
        cls.rom = Path(rom_path(str(cls.root))).read_bytes()
        cls.mapping = match.mapping_snapshot(cls.root)
        cls.index = index_snapshot(cls.root)
        cls.objects = match.data_snapshot(cls.root)
        cls.report = (cls.root/'docs/match/080D3508.md').read_text()

    def verify(self, rom, *, bindings=None, objects=None):
        import owner_admission_profile as owner
        start = registry.OWNER - match.ROM_BASE
        return owner.verify(rom[start:start+208], registry.OWNER, rom, self.mapping, self.index,
                            self.objects if objects is None else objects, selector=registry.SELECTOR,
                            bindings=registry.BINDINGS if bindings is None else bindings)

    def row(self, address):
        return struct.unpack_from('<IHH', self.rom, address-match.ROM_BASE)

    def test_all_original_rows_and_special_metadata(self):
        m = RegistryMachine(self.rom)
        for idx in range(1, 0x16A):
            for effect, arg in [(idx, 1)] + ([(0x159, idx)] if idx <= 341 else []):
                with self.subTest(effect=effect, arg=arg):
                    address = (registry.PRIMARY+8*(effect-1) if effect <= 341 else
                               registry.EXTENDED+8*(effect-0x156))
                    cb, count, tag = self.row(address)
                    m.run(effect, arg)
                    self.assertEqual(m.site[:5], (m.MANAGER, cb, count, m.SP-48, 0))
                    desc = m.site[-1]
                    self.assertEqual(struct.unpack_from('<II',desc,4),(m.ACTOR,arg))
                    self.assertEqual(struct.unpack_from('<H',desc,20)[0],effect)
                    if effect == 0x159:
                        metadata = registry.PRIMARY+8*(arg-1)
                        tag = self.row(metadata)[2]
                        self.assertEqual(m.reads,[(0x080D356A,address),(0x080D3BA6,metadata+6),(0x080D3592,metadata+6)])
                        self.assertEqual(struct.unpack_from('<HH',desc,22),(tag,arg))
                    elif effect <= 341:
                        self.assertEqual(m.reads,[(0x080D3BA6,address+6),(0x080D3552,address)])
                        self.assertEqual(struct.unpack_from('<HH',desc,22),(1,0))
                    else:
                        self.assertEqual(m.reads,[(0x080D356A,address)])
                        self.assertEqual(desc[22:26],bytes([0xA5])*4)
                    self.assertEqual(struct.unpack_from('<I',desc,12)[0], 2 if tag&255==16 else 0)
                    self.assertEqual(desc[0:4]+desc[16:20]+desc[26:28], bytes([0xA5])*10)

    def test_predicate_boundaries_and_actual_invalid_reads(self):
        m = RegistryMachine(self.rom)
        tagged = next(i for i in range(1,342) if self.row(registry.PRIMARY+8*(i-1))[2]&255==16)
        for category in (None,0,5,6,18,19,255):
            for effect, arg in [(tagged,0),(0x159,tagged)]:
                m.run(effect,arg,category=category,flags=0)
                self.assertEqual(struct.unpack_from('<I',m.site[-1],12)[0],0 if category in (6,18) else 2)
                if effect == tagged:
                    self.assertEqual(struct.unpack_from('<H',m.site[-1],22)[0],0)
        m.run(0,0)
        self.assertIn((0x080D3552,registry.PRIMARY-8),m.reads)
        m.run(0x16A,0)
        self.assertEqual(m.reads,[(0x080D356A,registry.NEXT_TABLE)])
        self.assertEqual(m.site[1],self.row(registry.NEXT_TABLE)[0])
        m.run(0x159,0x10001)
        self.assertEqual(m.reads[-2:],[(0x080D3BA6,registry.PRIMARY+6),(0x080D3592,registry.PRIMARY+0x80006)])
        m.run(0xDB,0,stop='dispatch')
        self.assertEqual((m.allocation_size,m.dispatch[0]),(28,0))

    def test_original_scheduler_and_returning_callbacks(self):
        m = RegistryMachine(self.rom)
        sentinel = next(i for i in range(1,342) if self.row(registry.PRIMARY+8*(i-1))[2]==0x7fff)
        for effect, arg, cb, count in [(0x158,0xAA55BB66,0x080E0C89,4),(0x159,sentinel,0x080E2399,40)]:
            for parent in (m.PARENT,0):
                self.assertEqual(m.run(effect,arg,parent=parent,seed=0x54,stop='return'),m.DONE)
                self.assertEqual(m.u.reg_read(m.reg.UC_ARM_REG_SP),m.SP)
                self.assertEqual(m.u.reg_read(m.reg.UC_ARM_REG_R0),m.TASK)
                self.assertEqual(m.allocation_size,count+28)
                self.assertEqual(m.dispatch,(cb,m.TASK,b'\x00\x00'+m.site[-1][2:],m.TASK+24))
                self.assertEqual(m.word(m.PARENT+16 if parent else m.MANAGER+4),m.TASK)
                self.assertEqual(m.word(m.TASK),cb)
                self.assertEqual(m.u.mem_read(m.TASK+20,2),b'\x00\x01')
                self.assertEqual(m.u.mem_read(m.TASK+24,count),
                                 b'\x66\xbb\x00\x00' if effect==0x158 else bytes(count))
        # When allocator storage aliases the live descriptor, real zero/list writes corrupt its contents.
        m.run(0x158,0xAA55BB66,target=m.SP-48,stop='dispatch')
        self.assertNotEqual(m.dispatch[2][8:12],m.site[-1][8:12])

    def test_replay_and_negative_mutations(self):
        import match_evidence
        self.assertTrue(match_evidence.report_matches(self.report,str(self.root),registry.OWNER))
        for old, new in [('"entries":341','"entries":342'),
                         ('"special_argument_domain":[1,341]','"special_argument_domain":[0,341]'),
                         ('"actual_callback_effects_proved":false','"actual_callback_effects_proved":true')]:
            changed = self.report.replace(old,new)
            self.assertNotEqual(self.report,changed)
            self.assertFalse(match_evidence.report_matches(changed,str(self.root),registry.OWNER))
        for where in (0x080D3566,0x080D3576,0x080D3598,0x080D35AA,0x080D3B40,0x080C8398,0x080059F6,
                      registry.PRIMARY,registry.PRIMARY+4,registry.EXTENDED+6,registry.EXTENDED-8):
            rom = bytearray(self.rom)
            rom[where-match.ROM_BASE] ^= 2
            with self.subTest(where=hex(where)), self.assertRaises(ValueError):
                self.verify(bytes(rom))
        changed = copy.deepcopy(registry.BINDINGS)
        changed['data'][0][1] = 'data_08395280'
        with self.assertRaises(ValueError):
            self.verify(self.rom,bindings=changed)
        with self.assertRaises(ValueError):
            self.verify(self.rom,objects=self.objects.replace(b'data_08395320',b'data_08395324'))
