"""Original four-byte mode initializer and guarded callback dispatcher at 0807DDB8."""

from collections import defaultdict
from hashlib import sha256
import struct

from capstone.arm import ARM_REG_R0, ARM_REG_SP
import active_entry_shuffle_profile as elf_roles
import owner_graph_profile as graph
import owner_runtime_profile as operations
import rom_table_copy_profile as copy
import stack_index_precondition_profile as index_policy
from software_double_profile import indices, span_record

BASE = 0x08000000
OWNER = 0x0807DDB8
END = 0x0807E2C4
MODES = 0x081499C0
HELPER_SITE = 0x0807DDC4
CHOICE = 0x0807DE64
TRANSFER = 0x0807DDD8
FUNCTIONS = [[0x440, "func_0807C7E8"], [0x458, "func_0807D240"]]
OBJECTS = (0x03002818, 0x03002730, 0x030009E0, 0x03000000, 0x0200F237, 0x0200F238, 0x0200F239)
MODE_BYTES = bytes((1, 2, 3, 5))


def require(ok, message):
    if not ok:
        raise ValueError("menu mode dispatcher: " + message)


def digest(data):
    return sha256(data).hexdigest()


def check_original(image, bindings, targets):
    elf_roles.compiler_symbol_roles(image, targets)
    for section in (image["text_index"], copy.rodata_section(image)[0]):
        matches = [(table, i, s) for table, rows in image["symbol_tables"].items()
                   for i, s in enumerate(rows) if s["section"] == section and s["type"] == 3]
        require(len(matches) == 1, "compiler section symbol is not unique")
        table, i, symbol = matches[0]
        require(not any(symbol[k] for k in ("value","name","size","bind")) and
                image["section_data"][table][16*i+13] == 0, "compiler section symbol differs")
    require(all(not s["size"] for s in image["symbols"] if s["name"] in targets),
            "sized external reference")
    require(bindings["functions"] == FUNCTIONS and bindings["calls"][0] == [12, "memcpy"] and
            all(n.startswith("func_") for _, n in bindings["calls"][1:]) and
            {n for _, n, _ in bindings["data"]} == {f"data_{a:08X}" for a in OBJECTS} and
            all(off == 0 for _, _, off in bindings["data"]), "function/data roles differ")
    for name, (value, obj) in targets.items():
        require((name == "memcpy" and (value, obj) == (copy.HELPER, False)) or
                (name == f"data_{value:08X}" if obj else name == f"func_{value:08X}"),
                "original symbol address differs")


def pointer_words(rom, target):
    references = []
    pos = -1
    while (pos := rom.find(struct.pack("<I", target|1), pos+1)) != -1:
        if pos % 4 == 0:
            references.append(BASE+pos)
    return references


def original_callers(rom, mapping, index):
    from positioned_equipment_chance import direct_sites
    entries, rows = indices(mapping, index)
    def body(a, b):
        span_record(a, b, entries, rows, rom)
        return rom[a-BASE:b-BASE]
    spans = {}
    for a, b, h in (
            (0x08078818, 0x0807968C, "d4ccf7d2dc63a9c24fa57a9bfc1b71db6fa3336cd3f11080a839690c2a55db74"),
            (0x080069F4, 0x08006A7C, "870059083b005c705d9ed3a284ac753f0cb32cb52f1110640bd37b4b31d8e726"),
            (0x08006A7C, 0x08006AB8, "877bd60e35bf7d06ab032e5c96a33ebdb416480ba6ede87050d91f229136bb03")):
        require(digest(body(a, b)) == h, "callback caller or scheduler changed")
        spans[f"0x{a:08X}"] = h
    def words(a, expected):
        require(struct.unpack_from("<"+"H"*len(expected), rom, a-BASE) == tuple(expected), "original operations differ")
    def literals(a, expected):
        require(struct.unpack_from("<"+"I"*len(expected), rom, a-BASE) == tuple(expected), "scheduler literal differs")
    words(0x080704AE, (0x4C29,0x4929,0x4A2A,0x1C20,0x2308,0xF796,0xFAE0))
    literals(0x08070554,(0x03002730,0x03000910,0x03000EC0))
    words(0x08070584,(0x4805,0x2108,0xF796,0xFA34))
    literals(0x0807059C,(0x03002730,))
    words(0x080792D4,(0x4805,0x4A06,0x2103,0xF78D,0xFBFF))
    literals(0x080792EC,(0x03002730,OWNER|1))
    words(0x08006ADC,(0xB510,0x0609,0x0E09,0x6884,0x008B,0x191B,0x601A,0x68C0,0x1840,0x2100,0x7001,0xBC10,0xBC01,0x4700))
    words(0x08006AF8,(0xB530,0x0609,0x0E09,0x6885,0x008C,0x1964,0x6022,0x68C0,0x1840,0x7003,0xBC30,0xBC01,0x4700))
    words(0x0814224C,(0x4710,))
    # These four real writers populate the source choice with each valid
    # value. They do not prove all writers or preservation by later calls.
    setters = []
    for site, pool, disasm, value in (
            (0x080765F0,0x08076608,(0x4805,0x6800,0x4905,0x1840),1),
            (0x08076F64,0x08076F7C,(0x4805,0x6800,0x4D05,0x1940),0),
            (0x08076FC0,0x08076FD8,(0x4805,0x6800,0x4B05,0x18C0),2),
            (0x0807705E,0x08077070,(0x4804,0x6800,0x4C04,0x1900),3)):
        words(site, (*disasm,0x2100|value,0x7001))
        literals(pool,(0x03002818,0x561))
        setters.append([site+10,value])
    literals(0x0807DEE4,(0x03002818,0x561,0xC1F))
    require(digest(body(0x08084DA0,0x08085370)) ==
            "0c6c997b7fde7751dbf4a28d0da32d66f8313ccb85b18941d959ace2c9489bcd",
            "native input query changed")
    words(0x08085324,(0x200B,0xE017))  # MOVS R0,#11; branch to common return.
    words(0x08085356,(0x7800,0xB00B,0xBC38,0x4698,0x46A1,0x46AA,0xBCF0,0xBC02,0x4708))
    words(0x0807DF70,(0x28FF,0xD119))  # CMP R0,#255 directly after BL.
    require(direct_sites(rom,0x08084DA0) == [0x0807DF6C] and not pointer_words(rom,0x08084DA0),
            "input query caller inventory differs")
    references = pointer_words(rom,OWNER)
    require(references == [0x080792F0] and direct_sites(rom, OWNER) == [], "callback references differ")
    return dict(registration=0x080792DA, direct_calls=[], pointer_words=references, dispatcher=0x08070588,
                scheduler=0x03002730, slot=3, dispatch_arguments=[3,0x03000EC3],
                child_slot=7,child_flag=2, initial_choice_stores=setters,checked_bodies=spans,
                input_query=dict(target=0x08084DA0, direct_calls=[0x0807DF6C], pointer_words=[],
                                 full_word_comparison=0x0807DF70, returns=[0x08085324,0x08085356]))


def indexed_access(raw, ins, edges, copies, premises):
    # Reuse the stack-index interpreter. Supply only successors proved by the
    # canonical switch graph. The private address gets used only by this LDRB.
    analysis = index_policy.Analysis(raw, OWNER, {0x0807DE60}, set(), copies)
    analysis.switch_site = TRANSFER
    analysis.switch_edges = tuple(edges[TRANSFER])
    expected = set(ins) | {pc + 2 for pc, item in ins.items() if item.size == 4}
    require(analysis.syntactic_sites() == expected, "raw index CFG differs")
    states = analysis.run()
    require(CHOICE in states and analysis.checked_derivations == {0x0807DE60} and
            not analysis.records and set(analysis.premises) == {CHOICE}, "index analysis did not cover the read")
    row = dict(analysis.premises[CHOICE])
    row["may_be_owner_written"] = any(site in analysis.reaches(analysis.writers) for site in row.pop("loads"))
    require(row["width"] == 1 and row["bound"] == 4 and row["array_sp"] == [8,12] and
            row["array_entry_sp"] == [-24,-20], "indexed load leaves initialized mode bytes")
    evidence = dict(schema=index_policy.SCHEMA, accesses=[],
                    derivations=[[pc-OWNER,*value] for pc,value in sorted(analysis.derived.items())],
                    preconditions=[row])
    return index_policy.accept(evidence, OWNER, index_policy.parse_premises(premises))


def prove(raw, rom, mapping, index, objects, ins, edges, branches, calls, words, refinement,
          bindings, rodata, premises):
    from known_query_native_closure_profile import environment_fingerprint
    require(digest(raw) == "39c58ce76006ca30892f21c210989410eb202c9beb42c62e0ba6247296582da6" and
            raw == rom[OWNER-BASE:END-BASE] and not branches and len(ins) == 434 and len(calls) == 31,
            "complete owner or reachable graph differs")
    entries, rows = indices(mapping, index)
    entry = span_record(OWNER,END,entries,rows,rom)
    require(entry["instrs"] == len(ins), "indexed counts differ from complete reachable code")
    partition = graph.partition(raw, OWNER, refinement, ins, words)
    operations.verify_operations(ins, edges, OWNER, branches, calls, refinement)
    require(rodata == dict(base=MODES,size=4,sha256=digest(MODE_BYTES),sites=[[36,0]]) and
            bindings["functions"] == FUNCTIONS and bindings["switches"] == [list(t) for t in sorted(words.items())] and
            bindings["calls"] == [[pc-OWNER, "memcpy" if pc == HELPER_SITE else f"func_{t:08X}"]
                                  for pc,t in sorted(calls.items())], "original compiler roles or initializer differ")
    switch, = refinement["word_switches"]
    require(switch.get("interposed_words") == 1 and switch["bound"] == 18 and
            (switch["literal"],switch["table"],switch["dispatch"]) == (40,44,24), "switch layout differs")
    incoming = defaultdict(set)
    for pc, successors in edges.items():
        for target in successors:
            incoming[target].add(pc)
    for dest, predecessor in ((0x0807DDCA,0x0807DDC8),(0x0807DDCC,0x0807DDCA),(0x0807DDCE,0x0807DDCC),
                              (0x0807DDD0,0x0807DDCC),(0x0807DDD2,0x0807DDD0),(0x0807DDD4,0x0807DDD2),
                              (0x0807DDD6,0x0807DDD4),(TRANSFER,0x0807DDD6)):
        require(incoming[dest] == {predecessor}, "an edge bypasses the guarded dispatch")
    def block(pc, values):
        for n, op in enumerate(values):
            require(pc+2*n in ins and bytes(ins[pc+2*n].bytes) == struct.pack("<H",op), "native block differs")
    sp_sites = [pc for pc,i in ins.items() if ARM_REG_SP in set().union(*i.regs_access())]
    require(sorted(sp_sites) == [OWNER,OWNER+2,OWNER+8,0x0807DE60,0x0807DEAA,0x0807DEAC,
                                0x0807E2BC,0x0807E2BE,0x0807E2C0], "unexpected stack operation")
    block(OWNER,(0xB5F0,0xB083,0x1C0F,0x4907,0xA802,0x2204))
    block(0x0807DDC8,(0x7838,0x2812,0xD900,0xE275,0x0080,0x4903,0x1840,0x6800,0x4687))
    block(0x0807DE30,(0x4D2C,0x6829,0x4A2C,0x1888,0x7800,0x4C2C,0x1909,0x2600,0x7008,0x2000))
    require(calls[0x0807DE44] == 0x0807DC24, "intervening render call changed")
    block(0x0807DE5A,(0x682A,0x1914,0x7820,0x4468,0x3008,0x7800))
    block(0x0807DEA8,(0x2000,0x9000,0x9001))
    block(0x0807E2BC,(0xB003,0xBCF0,0xBC01,0x4700))
    require([pc for pc,targets in edges.items() if not targets] == [0x0807E2C2] and
            calls[HELPER_SITE] == copy.HELPER and calls[0x0807E1E6] == calls[0x0807E204] == 0x08006AF8,
            "original return, copy or registration callees differ")
    originals = original_callers(rom, mapping, index)
    # PUSH saves five words. SUB SP allocates three private words. ADD R0,SP,#8
    # points to the last one. The following LDRB R0,[R7] kills memcpy's returned
    # address before any successor case or subsequent call can observe it.
    buffers = copy.RomTableCopyBufferProof(rom,mapping,index,objects,rodata=rodata,data=raw,address=OWNER)
    stack = [(None,None,True)]*3 + [(None,None,False)]*5
    restored = buffers.check_arguments(copy.HELPER,{ARM_REG_R0:-24},stack,{},set(),
                                       constants={ARM_REG_R0+1:MODES, ARM_REG_R0+2:4},site=HELPER_SITE)
    require(restored == {ARM_REG_R0:-24}, "copy returned another pointer")
    copies = buffers.copy_manifest()
    premise = indexed_access(raw,ins,edges,{HELPER_SITE:(-24,4)},premises)
    return dict(schema=index_policy.SCHEMA, calls=bindings["calls"], runtime_calls=[],
                instructions=len(ins), partition=partition,
                buffers=dict(rom_table_copies=copies,stack_index_preconditions=premise),
                menu_modes=dict(callback=originals, switch=switch,code_instructions=434,
                                initializer=list(MODE_BYTES),copy_site=HELPER_SITE,
                                outgoing=[-32,-24],initialized=[-24,-20],saves=[-20,0],
                                return_site=0x0807E2C2,
                                conditions=["The original scheduler table, action state and menu storage are live and disjoint from private stack storage.",
                                            "Ordinary calls preserve R4–R11, SP and the owner frame and return to their continuations.",
                                            "The live choice at the indexed read is below four. The scheduler registration alone does not prove this."]),
                environment=environment_fingerprint())
