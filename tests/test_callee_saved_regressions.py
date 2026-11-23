"""Kit #350 regressions: owner stack addresses kept in R4-R11 across a walked call.

Each case was admitted on kit main before #350, with no premise line, and must be refused now.

* The stack-index frame-words analysis: R5 holds the address of a local word at a call the
  analysis walks (in both selectors).  Main dropped the callee's read of R5, so it admitted a
  store through it, the address handed on as a stack argument, and a proved access whose index
  the callee had overwritten.
* The buffer-call proof: the owner keeps its local's address in R6 across the calls.  A callee
  that pushes R6 and reloads the pushed word, or a nested callee that never touches R6 and reads
  the word its caller pushed R6 into, stores 8 bytes past the local through it.
"""
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import stack_index_precondition_profile as sip
import test_data_buffer_calls as data_calls
from test_nested_known_query import assemble
from test_stack_index_frame_words import admit, frame_owner

WATCHED = "uses a watched callee-saved register's value"


class FrameWordsRegisterTests(unittest.TestCase):
    CALLEE, LEAF = 0x08014000, 0x08015000
    SPILL = (0x4668, 0x9003)      # mov r0,sp; str r0,[sp,#12]: sp+12 holds a frame address
    USE = (0x9903, 0x5D08)        # ldr r1,[sp,#12]; ldrb r0,[r1,r4]: the reload used as a base
    # LEAF: ldr r1,[sp]; movs r0,#200; strh r0,[r1]; movs r1,#0; bx lr (stores through its
    # stack argument)
    LEAF_CODE = (0x9900, 0x20C8, 0x8008, 0x2100, 0x4770)
    STORE = (0x20C8, 0x8028, 0x4770)          # movs r0,#200; strh r0,[r5]; bx lr
    # push {lr}; sub sp,#4; str r5,[sp]; bl LEAF; add sp,#4; pop {r0}; bx r0
    FORWARD = (0xB500, 0xB081, 0x9500, LEAF, 0xB001, 0xBC01, 0x4700)

    def functions(self, callee):
        patch, spans = {}, []
        for address, code in ((self.CALLEE, callee), (self.LEAF, self.LEAF_CODE)):
            raw = assemble(address, code)
            patch.update({address + offset: value for offset, value in enumerate(raw)})
            spans.append((address, len(raw), len(code)))
        return dict(patch_rom=patch, extra_functions=tuple(spans))

    def test_a_local_word_address_in_r5_at_a_walked_call_is_refused(self):
        # add r5,sp,#12; movs r0,#0; bl CALLEE, then the reload of sp+12 as a base; and
        # movs r0,#1; str r0,[sp,#8]; add r5,sp,#8; bl CALLEE; ldr r0,[sp,#8]; mov r1,sp;
        # ldrb r2,[r1,r0] (the counter the callee overwrites indexes a 3-byte array).
        cases = (
            ("store through r5", self.SPILL + (0xAD03, 0x2000, self.CALLEE) + self.USE, self.STORE, {},
             f"callee 0x{self.CALLEE:08X}: a memory access base at 0x{self.CALLEE + 2:08X} {WATCHED}"),
            ("r5 handed on as a stack argument", self.SPILL + (0xAD03, 0x2000, self.CALLEE) + self.USE,
             self.FORWARD, {}, f"callee 0x{self.LEAF:08X}: a memory access base at 0x{self.LEAF + 4:08X} {WATCHED}"),
            ("the overwritten counter indexes an array", (0x2001, 0x9002, 0xAD02, self.CALLEE, 0x9802, 0x4669, 0x5C0A),
             self.STORE, dict(index=()), f"callee 0x{self.CALLEE:08X}: a memory access base at 0x{self.CALLEE + 2:08X} {WATCHED}"),
        )
        for selector in sip.SELECTORS:
            for name, body, callee, options, message in cases:
                with self.subTest(selector=selector, case=name):
                    with self.assertRaises(ValueError) as caught:
                        admit(frame_owner(body, **options), selector=selector, **self.functions(callee))
                    self.assertIn(message, str(caught.exception))


@unittest.skipUnless(data_calls.tools_present(), "fixed compiler and ARM tools required")
class BufferCallPushedRegisterTests(unittest.TestCase):
    # The owner keeps its local's address in R6 across the calls and passes a copy in R1:
    # push {r4, r5, r6, lr}; sub sp, #8; ...; mov r6, sp; ...; adds r1, r6, #0; bl func_08000400
    OWNER = data_calls.HEADER + """extern void func_08000400(u16 value, u16 *out);
u32 func_08000200(u32 phase)
{
    u16 buffer[4];
    u16 *cursor = buffer;
    u32 i;

    for (i = 0; i < phase; i++)
        func_08000400(i, cursor);
    data_02000000[0] = buffer[1];
    return buffer[0];
}
"""

    def refused(self, callees):
        with tempfile.TemporaryDirectory() as base:
            code, output, report = data_calls.run(data_calls.build(Path(base), self.OWNER, callees))
        self.assertFalse(bool(report), "admitted")
        return output

    def test_a_nested_callee_reading_the_word_its_caller_pushed_r6_into_is_refused(self):
        output = self.refused([("func_08000400", "push {r6, lr}\nbl func_08000500\npop {r6}\npop {r3}\nbx r3"),
                               ("func_08000500", "ldr r2, [sp]\nstrh r0, [r2, #8]\nbx lr")])
        self.assertIn(f"callee 0x08000500: a memory access base at 0x08000502 {WATCHED}", output)

    def test_a_callee_reloading_its_own_pushed_r6_word_is_refused(self):
        output = self.refused([("func_08000400",
                                "push {r6, lr}\nldr r2, [sp]\nstrh r0, [r2, #8]\npop {r6}\npop {r1}\nbx r1")])
        self.assertIn(f"callee 0x08000400: a memory access base at 0x08000404 {WATCHED}", output)


if __name__ == "__main__":
    unittest.main()
