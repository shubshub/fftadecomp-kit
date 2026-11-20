"""Recover the two indexed shadow reads in the GBA scroll-wave initializer."""
import stack_index_precondition_profile as index


OWNER = 0x080D8E00
INIT = 0x080D8EF4
GUARD = 0x080D8EFA
HEADER = 0x080D8EFC
END = 0x080D8F38
READS = (0x080D8F0E, 0x080D8F26)

# R6=1; guard R6<count. The straight-line loop increments/narrows R7, forms
# R4=R8+4*R7, reads both pointers through R4, and increments/narrows R6.
# Its only call is the ordinary returning fill routine at 0800D95C.
INITIALIZER = bytes.fromhex(
    "0126ea7a96421dd2"
    "781c0006070e6868297aa0220092bc00444422680023d25e0192321c002334f71ffd"
    "7000291c0e310918206800880880701c0006060eec7aa642e1d3")


class ScrollWaveAnalysis(index.Analysis):
    """Feed the proved recurrence into the existing frame and premise checks."""

    def bind(self, verified_sites):
        if self.data[INIT - OWNER:END - OWNER] != INITIALIZER:
            index.refuse("scroll-wave parallel counters or fill call differ")
        for site in verified_sites:
            for target in self.successors(site):
                if INIT < target < END and not INIT <= site < END:
                    index.refuse("edge enters the scroll-wave counter initialization or loop")
        self.initial = None
        self.table = None

    def step(self, state, site):
        if self.check and site == GUARD:
            self.initial = self.expr(state, 7)
            self.table = state.regs[8]
            if self.initial is None or state.regs[6] != index.const(1) or \
                    self.table != index.exact_alias(-88):
                index.refuse("scroll-wave preheader lacks its index, row one, or shadow table")
        return super().step(state, site)

    def premise(self, state, site, width, load, c, expr, lo, modulus, disp):
        if self.check and site in READS:
            if self.initial is None or state.regs[8] != self.table or not load or width != 4 or disp:
                index.refuse("scroll-wave read lost its initialized aligned shadow table")
            # At the first body entry R6 is one and R7 is initial. Each
            # backedge advances the byte R6 once. Every continuation is guarded
            # by R6 < a byte, so R6 cannot wrap on a taken backedge. Both loads
            # use R8 + 4 * ((initial + this one-based ordinal) & 255).
            ordinal = ("iteration", HEADER)
            subscript = index.make("bin", "and", index.make("bin", "add", self.initial, ordinal), ("c", 255))
            expr = index.shift_expr("<<", subscript, 2)
            c = self.table[1]
        return super().premise(state, site, width, load, c, expr, lo, modulus, disp)

SPAWNER = 0x080D979C
DYNAMIC = 0x080EA44E
# Complete registering caller, map-layer sources and map save/restore operations.
PRODUCERS = {
    SPAWNER: (0x080D97D4, "85141c60433a791145e395d330634b62ecdbcb07fdb51193facdf87abc4fd368"),
    0x0801E610: (0x0801E620, "95ff1e73d2cab382c16a831dc7882e40089e5022a27f8946080e28f7f9209a9b"),
    0x0801E204: (0x0801E2A4, "f9f705e96043f4714c481a477f0b528c7c001676d126eaba1c713367f5669bd6"),
    0x0801D2B8: (0x0801D494, "0459ce0941f4a4701870a5cad1c203a49e83b797dd2e95cdaef633733533f9b1"),
    0x0801D494: (0x0801D58C, "fd349de9906cbe401240e509c27f225f7ec8afbb595f0da7129482af900b2392"),
}
# Caller start, end, BL, mode, BG, coordinate. The dynamic BG is the lesser
# of two layer bytes, and the physical range of those live bytes is a premise.
CALLERS = (
    (0x080E8D40, 0x080E8F3C, 0x080E8E1A, 0, 2, 0),
    (0x080EA3E8, 0x080EA4A0, DYNAMIC, 2, None, 0),
    (0x080EA4A0, 0x080EA6F2, 0x080EA5C0, 1, 2, 0),
    (0x080F1F1C, 0x080F21E6, 0x080F208A, 0, 2, 0),
    (0x080F21E8, 0x080F244C, 0x080F229A, 0, 3, 0),
    (0x080FD498, 0x080FD6E8, 0x080FD586, 0, 2, 0),
    (0x080FD6E8, 0x080FDAB0, 0x080FD814, 0, 2, 0),
    (0x08105684, 0x0810578C, 0x081056F2, 0, 2, 0),
    (0x0810973C, 0x0810998E, 0x0810988A, 0, 2, 0),
    (0x0811BB08, 0x0811BEC0, 0x0811BD2C, 0, 2, 1),
    (0x0811C018, 0x0811C2E6, 0x0811C11C, 2, 2, 0),
)
MAP_PREMISE = ("At the four-channel call 0x080EA44E, the lesser active layer ID "
               "selects a starting coordinate at most four. The map initializer "
               "sets (1,0), the temporary map substitutes (3,2) for enabled layers, "
               "and the restore copies back the saved pair. Preservation of valid "
               "map state and the callback payload by other code is a runtime premise.")


def producers(rom, mapping, index_text, bindings):
    from hashlib import sha256
    from struct import pack

    from ability_range_local_bytes import block, require
    from owner_admission_profile import refine
    from owner_graph_profile import graph
    from positioned_equipment_chance import direct_sites
    from software_double_profile import indices, span_record

    base = 0x08000000
    entries, rows = indices(mapping, index_text)
    owner = span_record(OWNER, 0x080D916E, entries, rows, rom)
    raw = rom[OWNER-base:0x080D916E-base]
    require(owner["instrs"] == refine(raw, OWNER, mapping)["instrs"] == 423 and sha256(raw).hexdigest() ==
            "9f984781f4d33e8b70db08bb0b422b31e156bfcc9a79b9a2db32a075901f7c63",
            "scroll-wave phase layout or instruction count differs")
    require(bindings["data"] == [[0x144, "data_08149AD4", 0], [0x148, "data_08149AF4", 0]]
            and not bindings["functions"] and not bindings["switches"],
            "scroll-wave register and shadow table bindings differ")
    require(rom[0x149AD4:0x149B14] == pack("<16I", *range(0x04000010, 0x04000020, 2),
                                                    *range(0x0300094A, 0x0300095A, 2)),
            "scroll-wave register and shadow tables differ")
    for start, (end, digest) in PRODUCERS.items():
        span_record(start, end, entries, rows, rom)
        require(sha256(rom[start-base:end-base]).hexdigest() == digest,
                f"scroll-wave producer 0x{start:08X} differs")
    require(direct_sites(rom, SPAWNER) == [row[2] for row in CALLERS]
            and not direct_sites(rom, OWNER), "scroll-wave incoming calls differ")
    for ptr, expected in ((SPAWNER, ()), (SPAWNER | 1, ()), (OWNER, ()), (OWNER | 1, (0x080D97D0,))):
        word = pack("<I", ptr)
        require(rom.count(word) == len(expected) and all(rom[pc-base:pc-base+4] == word for pc in expected),
                "scroll-wave callback or registration pointer references differ")
    arguments = []
    for start, end, site, mode, bg, coordinate in CALLERS:
        span_record(start, end, entries, rows, rom)
        data = rom[start-base:end-base]
        ins, edges, _, calls, _ = graph(data, start, refine(data, start, mapping))
        require([pc for pc, destination in calls.items() if destination == SPAWNER] == [site],
                "scroll-wave spawner caller CFG differs")
        setup = site-6
        if site == DYNAMIC:
            setup = 0x080EA42E
            block(ins, setup, "mov r4, sp", "adds r4, #5", "add r0, sp, #4", "adds r1, r4, #0",
                  "bl #0x801e610", "add r0, sp, #4", "ldrb r1, [r4]", "ldrb r0, [r0]",
                  "cmp r1, r0", "bls #0x80ea446", "adds r1, r0, #0", "ldr r3, [pc, #0x20]",
                  "str r7, [sp]", "movs r0, #2", "movs r2, #0", "bl #0x80d979c")
        else:
            block(ins, setup, f"movs r0, #{mode}", f"movs r1, #{bg}",
                  f"movs r2, #{coordinate}", "bl #0x80d979c")
            require((2*bg | coordinate) + (1 << mode) <= 8, "scroll-wave caller exceeds its tables")
        require(all(not (setup < target <= site) or setup <= pc < site
                    for pc, targets in edges.items() for target in targets),
                "scroll-wave spawner argument setup has a side entry")
        arguments.append([start, site, mode, bg, coordinate])
    return dict(caller_arguments=arguments, callback_literal=0x080D97D0, payload_size=0x16C,
                map_layer_source=0x02007F40, dynamic_site=DYNAMIC, dynamic_layer_premise=MAP_PREMISE,
                dynamic_layer_premise_proved=False)
