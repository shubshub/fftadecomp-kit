"""Call-via calls into the boot IWRAM code image (iwram_image_profile).

The fixture is one assembled image linked at 0x08000000 with the boot path at its pinned addresses:
the entry branch, the ARM reset code, MAIN, BOOT, the copier and its CpuSet call, the CpuSet wrapper
and agbcc's call-via thunks, and a small image (a clear and three probes) the copier copies to
0x03005E78.  No game ROM is needed.
"""
import json
import os
from pathlib import Path
import struct
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import match
import iwram_image_profile as iwram
import call_via_target_profile as call_via

BASE = match.ROM_BASE
R2 = match.RUNTIME_HELPERS["_call_via_r2"]
DESTINATION = 0x03005E78
OWNER = 0x08010000
TABLE = 0x08020000
SOURCE = 0x08003000

# The image: a byte clear (the shape the game's clear has), a routine that writes through R3 past
# the owner's local, one that clobbers R4, and one that leaves R4 alone.
IMAGE = """img_start:
img_clear:
    push {lr}
    adds r2, r0, #0
    cmp r1, #0
    ble 2f
1:  movs r0, #0
    strb r0, [r2]
    adds r2, #1
    subs r1, #1
    bgt 1b
2:  pop {r0}
    bx r0
img_far:
    movs r0, #0
    str r0, [r3, #64]
    bx lr
img_r4:
    movs r4, #1
    bx lr
img_quiet:
    movs r0, #0
    bx lr
    .balign 4
img_end:
"""
ENTRIES = ("img_clear", "img_far", "img_r4", "img_quiet")


def owner(entry="img_clear", *, held="r3", after="movs r3, #0\nstr r3, [sp]", load="table"):
    """The 0x08005954 shape: a frame address live in `held` across a call through _call_via_r2 whose
    R2 is read from a ROM table word (or a literal) holding an image routine's Thumb address."""
    index = ENTRIES.index(entry) if entry in ENTRIES else 0
    fetch = (f"ldr r0, =0x{TABLE:08X}\nldr r2, [r0, #{4 * index}]" if load == "table" else
             f"ldr r2, ={load}")
    return (f"push {{r4, lr}}\nsub sp, #8\nmov {held}, sp\n" + ("mov r3, sp\n" if held != "r3" else "") +
            f"{fetch}\nldr r0, =0x02000000\nmovs r1, #8\nbl 0x{R2:08X}\n{after}\n"
            "add sp, #8\npop {r4}\npop {r0}\nbx r0\n.ltorg")


def assembly(owner_body, *, control="((img_end - img_start) / 2)", destination=f"0x{DESTINATION:08X}"):
    table = "".join(f".word 0x{DESTINATION:08X} + ({name} - img_start) + 1\n" for name in ENTRIES)
    return f""".syntax unified
.arch armv4t
.text
.global owner, owner_end, img_start, img_end, leaf, boot, copier
.arm
entry:
    b reset
.org 0xC0
reset:
    mov r0, #0x12
    ldr r1, =0x08000255
    mov lr, pc
    bx r1
    b reset
    .ltorg
.thumb
.org 0x254
main:
    push {{lr}}
    bl leaf
.org 0x276
    bl boot
    pop {{r0}}
    bx r0
.org 0x300
leaf:
    movs r0, #0
    bx lr
.org 0x2710
boot:
    push {{lr}}
    ldr r0, =0x03000930
    ldr r1, [r0]
    cmp r1, #0
    bne 1f
    movs r1, #1
1:  str r1, [r0]
.org 0x2742
    bl copier
    pop {{r0}}
    bx r0
    .ltorg
.org 0x2768
copier:
    push {{lr}}
.org 0x2790
    ldr r0, =img_start
    ldr r1, ={destination}
    ldr r2, copy_control
    bl cpuset
    pop {{r0}}
    bx r0
    .ltorg
    .balign 4
copy_control:
    .word {control}
.org 0x{SOURCE - BASE:x}
{IMAGE}
.org 0x{OWNER - BASE:x}
owner:
{owner_body}
owner_end:
.org 0x{TABLE - BASE:x}
{table}
.org 0x14186C
cpuset:
    svc #0x0b
    bx lr
.org 0x{R2 - BASE - 8:x}
    bx r0
    nop
    bx r1
    nop
    bx r2
    nop
    bx r3
    nop
"""


@unittest.skipUnless(all(subprocess.run(["which", tool], capture_output=True).returncode == 0
                         for tool in ("arm-none-eabi-as", "arm-none-eabi-ld", "arm-none-eabi-objcopy")),
                     "ARM binutils required")
class IwramImageTests(unittest.TestCase):
    def setUp(self):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="iwram_image_", dir=scratch)
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        iwram._CACHE.clear()
        self.addCleanup(iwram._CACHE.clear)

    def build(self, owner_body, **options):
        (self.root / "f.s").write_text(assembly(owner_body, **options))
        self.build_text()

    def build_text(self):
        for command in (
                ["arm-none-eabi-as", "-mthumb-interwork", str(self.root / "f.s"), "-o", str(self.root / "f.o")],
                ["arm-none-eabi-ld", "-Ttext=0x08000000", "-e", "owner", str(self.root / "f.o"),
                 "-o", str(self.root / "f.elf")],
                ["arm-none-eabi-objcopy", "-O", "binary", "--only-section=.text", str(self.root / "f.elf"),
                 str(self.root / "f.bin")]):
            subprocess.run(command, check=True, capture_output=True)
        image = match.elf_image((self.root / "f.elf").read_bytes())
        self.symbols = {symbol["name"]: symbol["value"] for symbol in image["symbols"]}
        self.rom = bytearray((self.root / "f.bin").read_bytes())
        self.entries = [
            {"rom": f"0x{OWNER:08X}", "end": f"0x{self.symbols['owner_end']:08X}", "mode": "thumb"},
            {"rom": f"0x{self.symbols['leaf']:08X}", "end": f"0x{self.symbols['leaf'] + 4:08X}", "mode": "thumb"},
            {"rom": f"0x{self.symbols['boot']:08X}", "end": "0x08002768", "mode": "thumb"},
            {"rom": "0x08002768", "end": "0x080027B0", "mode": "thumb"},
            {"rom": f"0x{iwram.CPUSET:08X}", "end": f"0x{iwram.CPUSET + 4:08X}", "mode": "thumb"}] + [
            {"rom": f"0x{R2 + 4 * (n - 2):08X}", "end": f"0x{R2 + 4 * (n - 2) + 2:08X}", "mode": "thumb"}
            for n in range(4)]

    def prove(self, *, kind=match.BufferCallProof):
        rom, mapping = bytes(self.rom), json.dumps(self.entries).encode()
        body = rom[OWNER - BASE:self.symbols["owner_end"] - BASE]
        proof = kind(rom, mapping, stack_arguments=True, loop_replay=True, bios_wrappers=True,
                     dead_registers=True, call_via_targets=True)
        match.verify_leaf_instructions(body, OWNER, True, buffer_proof=proof, call_resolver=proof.target,
                                       incoming_narrow_reads=True)
        return proof

    def walk(self, owner_body, **options):
        self.build(owner_body, **options)
        return self.prove()

    def refused(self, pattern, owner_body=None, **options):
        if owner_body is not None:
            self.build(owner_body, **options)
        with self.assertRaisesRegex(ValueError, pattern):
            self.prove()

    def site(self):
        """The owner's `bl _call_via_r2`."""
        from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
        body = bytes(self.rom[OWNER - BASE:self.symbols["owner_end"] - BASE])
        (site,) = [instruction.address for instruction in Cs(CS_ARCH_ARM, CS_MODE_THUMB).disasm(body, OWNER)
                   if instruction.mnemonic == "bl" and instruction.op_str == f"#0x{R2:x}"]
        return site

    # The derivation ------------------------------------------------------------

    def test_the_boot_copy_is_derived_from_the_rom(self):
        self.build(owner())
        image = iwram.derive(bytes(self.rom), self.entries)
        length = self.symbols["img_end"] - self.symbols["img_start"]
        self.assertEqual((image.destination, image.source, image.length, image.evidence["unit"]),
                         (DESTINATION, SOURCE, length, 2))
        words = [value for _, value in image.evidence["words"]]
        self.assertIn(DESTINATION, words)
        self.assertEqual(sorted(value for value in words if value & 1),
                         sorted(DESTINATION + self.symbols[name] - SOURCE + 1 for name in ENTRIES))

    def test_every_link_of_the_boot_path_is_checked(self):
        self.build(owner())
        cases = {
            "entry branch": (0, struct.pack("<I", 0xEA00002F)),
            "reset target": (self.symbols["leaf"] - BASE, b""),
            "MAIN calls a non-leaf": (self.symbols["leaf"] - BASE, struct.pack("<H", 0xE7FE)),
            "BOOT returns first": (0x2720, struct.pack("<H", 0x4770)),
            "copier calls first": (0x2780, struct.pack("<HH", 0xF000, 0xF800)),
            "CpuSet bytes": (iwram.CPUSET - BASE, struct.pack("<H", 0xDF0C)),
        }
        reset_literal = next(offset for offset in range(0xC0, 0x100, 4)
                             if struct.unpack_from("<I", self.rom, offset)[0] == 0x08000255)
        cases["reset target"] = (reset_literal, struct.pack("<I", 0x08000257))
        for name, (offset, patch_bytes) in cases.items():
            with self.subTest(name=name):
                rom = bytearray(self.rom)
                rom[offset:offset + len(patch_bytes)] = patch_bytes
                with self.assertRaises(ValueError):
                    iwram.derive(bytes(rom), self.entries)
        with self.assertRaisesRegex(ValueError, "exact indexed CpuSet wrapper"):
            iwram.derive(bytes(self.rom), self.entries[:4])

    def test_no_copy_argument_is_carried_across_a_call(self):
        # The source address held in R4 across the first fill call is not trusted to survive it.
        self.build(owner())
        text = (self.root / "f.s").read_text().replace(
            "copier:\n    push {lr}\n", "copier:\n    push {lr}\n    ldr r4, =img_start\n    bl cpuset\n").replace(
            "    ldr r0, =img_start\n    ldr r1,", "    adds r0, r4, #0\n    ldr r1,")
        (self.root / "f.s").write_text(text)
        self.build_text()
        with self.assertRaisesRegex(ValueError, "not the copier's literal constants"):
            iwram.derive(bytes(self.rom), self.entries)

    def test_the_copy_must_be_a_plain_copy_from_rom_into_iwram(self):
        for options, pattern in ((dict(control="0x01000058"), "not a plain copy"),
                                 (dict(control="0x80000058"), "not a plain copy"),
                                 (dict(destination="0x02005E78"), "ROM source and an IWRAM destination"),
                                 (dict(destination="0x03007FF0"), "ROM source and an IWRAM destination")):
            with self.subTest(options=options):
                self.build(owner(), **options)
                with self.assertRaisesRegex(ValueError, pattern):
                    iwram.derive(bytes(self.rom), self.entries)

    # The rule --------------------------------------------------------------------

    def test_a_call_into_the_image_is_walked_over_its_bytes(self):
        proof = self.walk(owner())
        self.assertEqual(proof.iwram_image_calls, {(self.site(), DESTINATION)})
        length = self.symbols["img_end"] - self.symbols["img_start"]
        self.assertEqual(proof.dependencies[DESTINATION], bytes(self.rom[SOURCE - BASE:SOURCE - BASE + length]))
        line, = iwram.lines(proof)
        self.assertTrue(line.startswith(f"{iwram.FIELD}: `{iwram.POLICY_NAME}` 0x{DESTINATION:08X}-"
                                        f"0x{DESTINATION + length:08X} = ROM 0x{SOURCE:08X} ({length} bytes"), line)
        self.assertIn(f"calls 0x{self.site():08X} -> 0x{DESTINATION:08X}", line)
        self.assertTrue(line.endswith(f"premise: {iwram.PREMISE}"), line)
        self.assertIn(line, proof.loop_replay_lines())
        via, = call_via.lines(proof)
        self.assertIn(f"_call_via_r2 = 0x{DESTINATION + 1:08X} -> 0x{DESTINATION:08X}", via)

    def test_a_literal_target_resolves_the_same_way(self):
        proof = self.walk(owner(load=f"0x{DESTINATION + 1:08X}"))
        self.assertEqual(proof.iwram_image_calls, {(self.site(), DESTINATION)})

    def test_the_fingerprint_binds_the_evidence(self):
        proof = self.walk(owner())
        bound = proof.fingerprint()
        evidence = proof.iwram_image.evidence
        for key, value in (("sha256", "0" * 64), ("words", []), ("source", SOURCE + 2)):
            with self.subTest(key=key), patch.dict(evidence, {key: value}):
                self.assertNotEqual(proof.fingerprint(), bound)
        with patch.object(iwram, "PREMISE", iwram.PREMISE + "."):
            self.assertNotEqual(proof.fingerprint(), bound)
        calls = set(proof.iwram_image_calls)
        proof.iwram_image_calls.clear()
        self.assertIsNone(iwram.fingerprint_payload(proof))
        self.assertEqual(iwram.lines(proof), [])
        proof.iwram_image_calls.update(calls)
        self.assertEqual(proof.fingerprint(), bound)

    def test_the_image_bytes_are_walked_by_the_buffer_rules(self):
        self.refused("outside allocated local words", owner("img_far"))

    def test_the_callee_saved_walk_sees_the_image_bytes(self):
        # R4 holds a frame address across the call: a routine that writes it refuses, one that
        # leaves it alone is admitted.
        self.refused(r"R4|r4|watched", owner("img_r4", held="r4", after="movs r3, #0\nstr r3, [r4]"))
        proof = self.walk(owner("img_quiet", held="r4", after="movs r3, #0\nstr r3, [r4]"))
        self.assertEqual({target for _, target in proof.iwram_image_calls},
                         {DESTINATION + self.symbols["img_quiet"] - SOURCE})

    def with_inner_call(self, entry, fetch=None):
        """The 0x08005B6C -> 0x08005954 shape: the owner keeps its frame in R4 across a call that
        passes no stack address, so only the callee-saved walk follows it; the callee copies R4 into
        R3 and calls an image routine through _call_via_r2 with R2 read from the ROM table."""
        body = ("push {r4, lr}\nsub sp, #8\nmov r4, sp\nbl func_f\nmovs r3, #0\nstr r3, [r4]\n"
                "add sp, #8\npop {r4}\npop {r0}\nbx r0\n.ltorg")
        fetch = fetch or f"ldr r0, =0x{TABLE:08X}\nldr r2, [r0, #{4 * ENTRIES.index(entry)}]"
        inner = (f"push {{lr}}\nadds r3, r4, #0\n{fetch}\n"
                 f"ldr r0, =0x02000000\nmovs r1, #8\nbl 0x{R2:08X}\nmovs r3, #0\npop {{r0}}\nbx r0\n.ltorg")
        text = assembly(body).replace(
            "owner_end:\n", f"owner_end:\n.balign 4\n.global func_f, func_f_end\nfunc_f:\n{inner}\nfunc_f_end:\n", 1)
        (self.root / "f.s").write_text(text)
        self.build_text()
        self.entries.append({"rom": f"0x{self.symbols['func_f']:08X}", "end": f"0x{self.symbols['func_f_end']:08X}",
                             "mode": "thumb"})
        from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
        start, end = self.symbols["func_f"], self.symbols["func_f_end"]
        (site,) = [instruction.address for instruction in Cs(CS_ARCH_ARM, CS_MODE_THUMB).disasm(
            bytes(self.rom[start - BASE:end - BASE]), start) if instruction.op_str == f"#0x{R2:x}"]
        return site

    def test_the_callee_saved_walk_resolves_a_call_into_the_image(self):
        site = self.with_inner_call("img_clear")
        proof = self.prove()
        self.assertEqual(proof.iwram_image_calls, set())            # the buffer walks never met the call
        self.assertEqual(iwram.calls(proof), {(site, DESTINATION)})
        line, = iwram.lines(proof)
        self.assertIn(f"calls 0x{site:08X} -> 0x{DESTINATION:08X}", line)
        self.assertIn(line, proof.loop_replay_lines())
        # It is walked over the image bytes: a routine that writes through R3 or clobbers R4 refuses.
        for entry in ("img_far", "img_r4"):
            with self.subTest(entry=entry):
                self.with_inner_call(entry)
                with self.assertRaises(ValueError):
                    self.prove()
        # An even value or one outside the image is not resolved: the call keeps its refusal.
        for value in (DESTINATION, DESTINATION + 0x1001):
            with self.subTest(value=hex(value)):
                self.with_inner_call("img_clear", fetch=f"ldr r2, =0x{value:08X}")
                with self.assertRaisesRegex(ValueError, "receives an owner stack address in R3"):
                    self.prove()
        # Without the hook the call stays an indirect call that receives an owner stack address.
        self.with_inner_call("img_clear")
        with patch.object(iwram, "watch_target", lambda proof: None), \
                self.assertRaisesRegex(ValueError, "receives an owner stack address in R3"):
            self.prove()

    def test_a_crossed_image_call_is_walked_over_the_image(self):
        # The call-via target rule's crossing check: the callback's fact in R4 crosses an image call the
        # buffer walks do not inspect and is then called with the owner's frame.  The crossed call is
        # checked by a callee-saved walk of its own (call_via_target_profile.crossing_premises), which
        # resolves the image the same way: the routine is walked, not stated as an unresolved call.
        r3 = match.RUNTIME_HELPERS["_call_via_r3"]
        body = (f"push {{r4, lr}}\nsub sp, #8\nldr r4, =callback + 1\nadds r3, r4, #0\nldr r0, =0x{TABLE:08X}\n"
                f"ldr r2, [r0]\nldr r0, =0x02000000\nmovs r1, #8\nbl 0x{R2:08X}\nmov r0, sp\nadds r3, r4, #0\n"
                f"bl 0x{r3:08X}\nadd sp, #8\npop {{r4}}\npop {{r0}}\nbx r0\n.ltorg")
        text = assembly(body).replace("owner_end:\n", "owner_end:\n.balign 4\n.global callback, callback_end\n"
                                      "callback:\nmovs r1, #1\nstrh r1, [r0]\nbx lr\ncallback_end:\n", 1)
        (self.root / "f.s").write_text(text)
        self.build_text()
        self.entries.append({"rom": f"0x{self.symbols['callback']:08X}",
                             "end": f"0x{self.symbols['callback_end']:08X}", "mode": "thumb"})
        site = self.site()
        proof = self.prove()
        self.assertEqual(proof.iwram_image_calls, set())
        self.assertEqual(iwram.calls(proof), {(site, DESTINATION)})
        self.assertIn(self.symbols["callback"], proof.dependencies)
        premised = [line for line in call_via.lines(proof) if line.startswith(call_via.PREMISE_LINE)]
        self.assertFalse([line for line in premised if f"call at 0x{site:08X}" in line], premised)
        # Without the image the crossing checker can only state the image call as an unresolved one.
        with patch.object(iwram, "watch_target", lambda proof: None):
            unresolved = self.prove()
        self.assertEqual(iwram.calls(unresolved), set())
        self.assertTrue([line for line in call_via.lines(unresolved) if line.startswith(call_via.PREMISE_LINE) and
                         f"call at 0x{site:08X}" in line], call_via.lines(unresolved))

    def test_a_crossing_continuation_walks_an_image_call(self):
        # The real path (0x08005954): the callback's fact in R4 crosses a call whose callee hands back a
        # copy of R4 in R3, so the crossing check's own callee-saved walk continues in the caller and
        # meets an image call with R3 holding that copy.  With the image that call is walked; without
        # it the copy reaches an unresolved indirect call and the crossing refuses.
        body = (f"push {{r4, lr}}\nldr r4, =callback + 1\ncrossed:\nbl func_cp\nldr r0, =0x{TABLE:08X}\n"
                f"ldr r2, [r0]\nldr r0, =0x02000000\nmovs r1, #8\nbl 0x{R2:08X}\nmovs r3, #0\npop {{r4, pc}}\n.ltorg")
        text = assembly(body).replace("owner_end:\n", "owner_end:\n.balign 4\n.global callback, func_cp, func_cp_end, crossed\n"
                                      "callback:\nbx lr\nfunc_cp:\nadds r3, r4, #0\nbx lr\nfunc_cp_end:\n", 1)
        (self.root / "f.s").write_text(text)
        self.build_text()
        self.entries.append({"rom": f"0x{self.symbols['func_cp']:08X}", "end": f"0x{self.symbols['func_cp_end']:08X}",
                             "mode": "thumb"})
        rom, mapping = bytes(self.rom), json.dumps(self.entries).encode()
        crossed, image_site = self.symbols["crossed"], self.site()

        def crossing():
            proof = match.BufferCallProof(rom, mapping, stack_arguments=True, call_via_targets=True)
            records = call_via.crossing_premises(proof, call_via.function_of(proof, crossed), crossed,
                                                 self.symbols["func_cp"], 4)
            return proof, records
        proof, records = crossing()
        self.assertEqual(proof.iwram_image_watch_calls, {(image_site, DESTINATION)})
        self.assertFalse([record for record in records if record[0] == "call" and record[2] == image_site], records)
        with patch.object(iwram, "watch_target", lambda proof: None), \
                self.assertRaisesRegex(ValueError, f"indirect call at 0x{image_site:08X} receives an owner stack "
                                                   "address in R3"):
            crossing()

    def test_a_release_by_an_image_routine_marks_its_caller(self):
        # A routine of the image that returns its own frame in R2 (released_scratch_profile): the
        # marker is keyed by the routine the call resolved to, which no literal or ROM word names.
        image = IMAGE.replace("img_quiet:\n", "img_rel:\n    push {lr}\n    sub sp, #8\n    mov r2, sp\n"
                              "    add sp, #8\n    pop {r0}\n    bx r0\nimg_quiet:\n")
        load = f"0x{DESTINATION:08X} + (img_rel - img_start) + 1"
        with patch(f"{__name__}.IMAGE", image):
            self.refused("released callee frame address in r2 is read",
                         owner(load=load, after="adds r0, r2, #0\nmovs r3, #0\nstr r3, [sp]"))
            proof = self.walk(owner(load=load, after="movs r2, #0\nmovs r3, #0\nstr r3, [sp]"))
        self.assertEqual({row[2] for row in proof.released_scratch}, {2})

    def test_values_outside_the_image_or_even_keep_the_refusal(self):
        for value in (DESTINATION, DESTINATION - 1, DESTINATION + 0x1001, 0x03007001):
            with self.subTest(value=hex(value)):
                self.build(owner(load=f"0x{value:08X}"))
                with self.assertRaises(ValueError):
                    self.prove()

    def test_an_unproved_boot_copy_keeps_the_refusal(self):
        self.build(owner())
        self.rom[0:4] = struct.pack("<I", 0xEA00002F)
        with self.assertRaises(ValueError):
            self.prove()

    def test_only_the_two_default_buffer_proofs_take_the_resolver(self):
        self.build(owner())

        class Other(match.BufferCallProof):
            pass
        rom, mapping = bytes(self.rom), json.dumps(self.entries).encode()
        self.assertEqual(Other(rom, mapping, stack_arguments=True).call_via_resolvers, ())
        self.assertEqual(match.FunctionBufferCallProof(rom, mapping, stack_arguments=True).call_via_resolvers,
                         (iwram.resolver,))
        self.assertIsNone(iwram.resolver(Other(rom, mapping, stack_arguments=True), OWNER, 2, DESTINATION + 1))

    def test_the_policy_switch_restores_the_refusal(self):
        self.build(owner())
        with patch.object(iwram.POLICY, "enabled", False), self.assertRaises(ValueError):
            self.prove()

    def test_an_image_address_is_a_target_only_once_resolved(self):
        self.build(owner())
        rom, mapping = bytes(self.rom), json.dumps(self.entries).encode()
        proof = match.BufferCallProof(rom, mapping, stack_arguments=True)
        with self.assertRaisesRegex(ValueError, "not unique aligned Thumb ROM code"):
            proof.target(DESTINATION)
        self.assertEqual(iwram.resolver(proof, OWNER, 2, DESTINATION + 1), DESTINATION)
        self.assertEqual(proof.target(DESTINATION)["end"], f"0x{proof.iwram_image.end:08X}")
        with self.assertRaisesRegex(ValueError, "not unique aligned Thumb ROM code"):
            proof.target(DESTINATION + 2)

    def test_an_aborted_pass_leaves_no_call(self):
        self.build(owner())
        rom, mapping = bytes(self.rom), json.dumps(self.entries).encode()
        proof = match.BufferCallProof(rom, mapping, stack_arguments=True)
        saved = proof._snapshot_ledgers()
        iwram.resolver(proof, OWNER, 2, DESTINATION + 1)
        proof._restore_ledgers(saved)
        self.assertEqual(proof.iwram_image_calls, set())


BUFFER_ONLY = """typedef unsigned short u16;
extern void func_08000400(u16 value, u16 *out);
u16 func_08000200(u16 value)
{
    u16 buffer[4];

    func_08000400(value, buffer);
    return buffer[0] + buffer[3];
}
"""
# The callee keeps the owner's buffer in R3 across a call of the image's clear through _call_via_r2,
# with R2 read from the ROM table: the 0x08005954 shape, reached from natural C.
IMAGE_CALLER = (f"push {{lr}}\nadds r3, r1, #0\nldr r0, =0x{TABLE:08X}\nldr r2, [r0]\nldr r0, =0x02000000\n"
                f"movs r1, #8\nbl 0x{R2:08X}\nmovs r3, #0\npop {{r0}}\nbx r0\n.align 2\n.ltorg")

try:
    from test_data_buffer_calls import A, build as data_buffer_tree, run as run_match, tools_present
    from test_call_via_targets import index_thunks
    import match_evidence
except ImportError:            # pragma: no cover - the sibling fixtures are part of the suite
    tools_present = lambda: False


@unittest.skipUnless(tools_present(), "fixed compiler and ARM tools required")
class SubprocessTests(unittest.TestCase):
    def test_the_rule_applies_at_issuance_and_in_replay(self):
        # match.py as a subprocess issues the report as __main__ and the replay rebuilds the proof:
        # the report states the image and replays, and fails to replay without that line.
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="iwram_image_sub_", dir=scratch) as directory:
            directory = Path(directory)
            image = IwramImageTests("test_the_boot_copy_is_derived_from_the_rom")
            image.root = directory / "image"
            image.root.mkdir()
            image.build("bx lr")
            root = index_thunks(data_buffer_tree(directory / "tree", BUFFER_ONLY,
                                                 [("func_08000400", IMAGE_CALLER)], large=True))
            rom = bytearray((root / "baserom.bin").read_bytes())
            entries = json.loads((root / "config/functions.json").read_text())
            owner_end = max(int(entry["end"], 16) for entry in entries if int(entry["rom"], 16) == A)
            # The boot path, the copier and the image source, and the ROM table, from the fixture.
            for low, high in ((0, A - BASE), (owner_end - BASE, 0x400), (0x2700, SOURCE - BASE + 0x200),
                              (TABLE - BASE, TABLE - BASE + 0x10)):
                rom[low:high] = image.rom[low:high]
            (root / "baserom.bin").write_bytes(bytes(rom))
            entries += [{"rom": f"0x{image.symbols['leaf']:08X}", "end": f"0x{image.symbols['leaf'] + 4:08X}",
                         "mode": "thumb"},
                        {"rom": f"0x{image.symbols['boot']:08X}", "end": "0x08002768", "mode": "thumb"},
                        {"rom": "0x08002768", "end": "0x080027B0", "mode": "thumb"}]
            (root / "config/functions.json").write_text(json.dumps(entries))
            (root / "symbols/functions.txt").write_text("".join(
                f"{int(e['rom'], 16):08X} {int(e['end'], 16):08X} {int(e['end'], 16) - int(e['rom'], 16)} 0 return\n"
                for e in entries))
            self.assertIsNotNone(iwram.derive(bytes(rom), entries))
            code, output, text = run_match(root)
            self.assertEqual(code, 0, output[-2000:])
            lines = [line for line in text.splitlines() if line.startswith(iwram.FIELD + ":")]
            self.assertEqual(len(lines), 1, text)
            self.assertIn(f"-> 0x{DESTINATION:08X}", lines[0])
            with patch.dict(os.environ, FFTA_ROM=str(root / "baserom.bin")):
                self.assertTrue(match_evidence.report_matches(text, root, A))
                edited = "".join(line + "\n" for line in text.splitlines() if not line.startswith(iwram.FIELD))
                self.assertFalse(match_evidence.report_matches(edited, root, A))


class IssuingCopyTests(unittest.TestCase):
    def test_proofs_of_the_issuing_copy_of_match_take_the_rule(self):
        # match.py issues reports as __main__ loaded from its own file and replays them as the imported
        # match: proofs of both count (call_via_target_profile.kit_match).  Only the definitions are run.
        import types
        main = sys.modules["__main__"]
        copy = types.ModuleType("__main__")
        copy.__file__ = match.__file__
        source = Path(match.__file__).read_text().replace('if __name__ == "__main__":', "if False:")
        sys.modules["__main__"] = copy
        try:
            exec(compile(source, match.__file__, "exec"), copy.__dict__)
            for kind in ("BufferCallProof", "FunctionBufferCallProof"):
                with self.subTest(kind):
                    proof = getattr(copy, kind)(bytes(0x1000), "[]", stack_arguments=True, call_via_targets=True)
                    self.assertTrue(iwram.applies(proof))
                    self.assertEqual(proof.call_via_resolvers, (iwram.resolver,))
            derived = type("Derived", (copy.BufferCallProof,), {})
            self.assertEqual(derived(bytes(0x1000), "[]", stack_arguments=True).call_via_resolvers, ())
        finally:
            sys.modules["__main__"] = main

if __name__ == "__main__":
    unittest.main()
