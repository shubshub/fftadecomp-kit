"""Buffer owners whose bounded-buffer callees run the pinned list queries.

The named-data buffer walk (`named-data-buffer-v1`) follows every callee that
receives one of the owner's stack aliases.  Two things stop it when such a
callee is itself a caller of a pinned known list query:

* the callee's own frame: a 13-word array handed to func_08099CDC,
  func_08099D08 or func_08099D34 and read back by a cursor loop, which the
  ordinary leaf verifier cannot inspect;
* stale owner aliases: agbcc leaves the owner's pointers in R2/R3 when the
  callee calls a list query with fewer arguments, so the walk follows them
  into the query's iterator and stops at its `_call_via_r6` thunk.

This profile keeps the walk and its alias rules and replaces only those two
steps.

1. A callee that directly calls a pinned query root is inspected by the
   `conditional-known-query-stack-buffer-v1` executor instead of the leaf
   verifier, under that selector's pinned contract and its fixed premise that
   every list holds at most 13 nodes.  The executor proves the callee's own
   frame: every query buffer is 13 allocated private words, no private
   address escapes, R1-R3/R12 are not read after any call before being
   redefined, and the entry frame and R4-R11 are restored.  The owner aliases
   the callee received are then walked over the same instructions by the
   unchanged buffer walk, so every access through them is still bounded
   against the owner's frame.
2. A call to the root of a pinned query family while owner aliases sit only in
   R2, R3 or R12 is summarized.  For each family the bytes, extents and
   instruction counts of every body that can run are pinned, and the following
   are checked mechanically on those bytes: no instruction in any body reads
   or writes R3 or R12; the root writes R2 before it reads it and before its
   first call or branch; every direct BL and every code-address literal stays
   inside the family.  The aliases in R3/R12 are therefore returned unchanged
   and the one in R2 is dead.  The memory effects of the family are covered by
   the walk's ordinary premise for callees that receive no alias, which is
   exactly the situation once the dead registers are discounted.

Any owner alias in R0, R1 or LR at a family call, or a stack-passed pointer
word, refuses.  A pinned query call that is not inside a callee executed under
the stack-buffer contract refuses whenever any owner alias is live in an
argument register at the call: only the executor checks the 13-word R1 bound
and forbids reading R1-R3/R12 after the query.

Code-address literals are checked over every code-capable range (EWRAM, IWRAM
and the ROM windows): an odd word there must name a family body.
"""
import hashlib
import json
from pathlib import Path

from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB, CS_GRP_JUMP, CS_GRP_CALL, CS_GRP_RET
from capstone.arm import ARM_OP_IMM

import match
import named_data_buffer_profile as named
import known_query_stack_buffer_profile as stack_query
import known_list_query_closure_profile as closure
import owner_graph_profile as graph
import software_double_profile
from software_double_profile import indices, span_record

SELECTOR = named.QUERY_CALLEE_SELECTOR
SCHEMA = named.QUERY_CALLEE_SCHEMA
CONTROL_FLOW = ('complete Thumb owner with typed data literals and ROM-proved bounded buffer callees; '
                'callees that pass a private 13-word stack array to a pinned known list query are '
                'executed for every returned count 0..13 under the unproved premise n <= 13; '
                'stale owner aliases in R2/R3/R12 at pinned list-query families are dead or preserved '
                'by their pinned bytes; conditional returning ABI and memory noninterference')
MAX_DEPENDENCIES = named.MAX_DEPENDENCIES
R0, R12, LR = match.ARM_REG_R0, match.ARM_REG_R12, match.ARM_REG_LR
R2, R3 = R0 + 2, R0 + 3
PC = match.ARM_REG_PC
CODE_RANGES = ((0x02000000, 0x02040000), (0x03000000, 0x03008000), (0x08000000, 0x0E000000))
UNTOUCHED = (R3, R12)
TRANSPARENT = (R2, R3, R12)


def _closure_root(address):
    kind, count, _, code = closure.ROOTS[address]
    return count, code


# Root -> {body address: (instruction count, exact bytes)}.  Every body that
# can execute once the root is called: the root, its direct BL targets, the
# iterator, the adapter or visitor that the iterator reaches through the
# `_call_via_r6` thunk, and the callback the adapter reaches through
# `_call_via_r2`.  The thunk targets are the code literals of the family
# (checked below to lie inside it); that they are the only targets is the
# hand-derived relation of the pinned bytes, as in the stack-buffer contract.
FAMILIES = {}
for _root in stack_query.QUERIES:
    FAMILIES[_root] = dict(
        kind='known-query-collect',
        indirect_targets=['_call_via_r6 -> func_0809ABE8 (root literal, the iterator visitor)',
                          '_call_via_r2 -> func_0809AC20 (root literal stored in the closure)'],
        bodies={_root: (17, stack_query.query_body(_root).hex()),
                **{a: (c, code) for a, (c, code) in stack_query.DEPENDENCIES.items()}})
FAMILIES[0x08099560] = dict(
    kind='known-list-query-search',
    indirect_targets=['_call_via_r6 -> func_0809AB5C (root literal, the iterator visitor)'],
    bodies={0x08099560: _closure_root(0x08099560),
            **{a: closure.DEPENDENCIES[a] for a in (0x0809AB5C, 0x080C7CC0, 0x080C7B74, 0x0814225C)}})
FAMILIES[0x08099544] = dict(
    kind='known-list-query-any',
    indirect_targets=['_call_via_r6 -> func_0809ABE8 (func_08099840 literal, the iterator visitor)',
                      '_call_via_r2 -> func_0809AB3C (func_08099544 literal passed through func_08099840 '
                      'in the closure)'],
    bodies={0x08099544: (11, '00b581b00021009103496a4600f076f9009801b002bc08473dab0908'),
            0x08099840: (11, '00b582b000920191006903496a462ef037fa02b001bc0047e9ab0908'),
            0x0809AB3C: (15, '30b5041c0d1c20682df0a8fb0006002802d02c60002000e0012030bc02bc0847'),
            0x080C8298: (15, '00b50021002807d0018d8020400108400004000c4042c10f081c02bc0847'),
            **{a: stack_query.DEPENDENCIES[a] for a in (0x0809ABE8, 0x080C7CC0, 0x080C7B74,
                                                       0x0814225C, 0x0814224C)}})
del _root

TRANSPARENCY_CONTRACT = (
    'A pinned list-query family runs only its pinned bodies. No instruction in any body reads or '
    'writes R3 or R12, so an owner alias in either is returned unchanged; the root writes R2 '
    'before reading it, so an owner alias in R2 is dead. The family receives no live owner alias, '
    'so its memory effects are those of an ordinary callee that receives none.')
CALLEE_CONDITIONS = stack_query.EXPLICIT_CONDITIONS + [
    'For a callee executed under the known-query contract, the frames of its callers, including '
    'the owner, are outside its frame: its ordinary direct calls and its external accesses touch '
    'them only through owner aliases, which the buffer walk tracks and bounds.',
]


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def _decoder():
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    decoder.detail = True
    return decoder


def family_facts(root, rom, mapping, index):
    """Pin one family to the current ROM and check its register facts."""
    require(root in FAMILIES, 'call target is not a pinned list-query family root')
    entries, rows = indices(mapping, index)
    family = FAMILIES[root]
    bodies = {}
    identities = []
    for start, (count, code) in sorted(family['bodies'].items()):
        body = bytes.fromhex(code)
        end = start + len(body)
        row = span_record(start, end, entries, rows, rom)
        require(row['mode'] == 'thumb' and row['instrs'] == count and rom[start - 0x08000000:end - 0x08000000] == body,
                'pinned list-query family bytes, extent or count differ')
        bodies[start] = body
        identities.append(dict(address=start, end=end, instructions=count, body_sha256=sha(body)))
    for thunk, padding in stack_query.THUNK_PADDING.items():
        if thunk in bodies:
            lo = thunk + 2
            require(rom[lo - 0x08000000:lo + 2 - 0x08000000] == bytes.fromhex(padding) and
                    not any(int(e['rom'], 16) < lo + 2 and int(e['end'], 16) > lo for e in entries) and
                    not any(int(r[0], 16) < lo + 2 and int(r[1], 16) > lo for r in rows),
                    'pinned family thunk padding must remain separate and unowned')
    decoder = _decoder()
    first = None
    for start, body in sorted(bodies.items()):
        count = family['bodies'][start][0]
        code = list(decoder.disasm(body, start))[:count]
        require(len(code) == count and code[-1].address + code[-1].size - start <= len(body),
                'pinned family body does not decode to its instruction count')
        code_end = code[-1].address + code[-1].size
        for instruction in code:
            read, written = instruction.regs_access()
            require(not (set(read) | set(written)) & set(UNTOUCHED),
                    'pinned family body accesses R3 or R12')
            if instruction.mnemonic == 'bl':
                target = instruction.operands[0].imm
                require(instruction.operands[0].type == ARM_OP_IMM and target in bodies,
                        'pinned family direct call leaves the family')
        for offset in range(((code_end + 3) & ~3) - start, len(body) - 3, 4):
            word = int.from_bytes(body[offset:offset + 4], 'little')
            rom_word = 0x08000000 <= word < 0x0E000000
            if rom_word or word & 1 and any(lo <= word < hi for lo, hi in CODE_RANGES):
                require(word & 1 and word & ~1 in bodies,
                        'pinned family code literal leaves the family')
        if start == root:
            first = code
    written_first = False
    for instruction in first:
        read, written = instruction.regs_access()
        require(R2 not in read, 'pinned family root reads R2 before writing it')
        if R2 in written:
            written_first = True
            break
        require(not {CS_GRP_JUMP, CS_GRP_CALL, CS_GRP_RET} & set(instruction.groups) and
                PC not in written,
                'pinned family root reaches a call or branch before writing R2')
    require(written_first, 'pinned family root never writes R2')
    return dict(root=root, kind=family['kind'], identities=identities,
                indirect_targets=list(family['indirect_targets']),
                untouched_registers=['r3', 'r12'], written_before_read=['r2'],
                contract=TRANSPARENCY_CONTRACT)


class KnownQueryCalleeBufferProof(named.NamedDataBufferProof):
    """Named-data buffer walk with pinned known-query callees summarized."""

    def __init__(self, rom, mapping, index, objects):
        super().__init__(rom, mapping, index, objects)
        self.query_callers = {}
        self.query_sites = set()
        self.families = {}
        self.summaries = {}
        self._contract = None

    def contract(self):
        if self._contract is None:
            self._contract = stack_query.contract(self.rom, self.mapping, self.index)
        return self._contract

    def inspect(self, address, data):
        import owner_admission_profile as owner
        refinement = owner.refine(data, address, self.mapping)
        instructions, edges, local_calls, calls, words = graph.graph(data, address, refinement)
        if not any(target in stack_query.QUERIES for target in calls.values()):
            return super().inspect(address, data)
        require(not local_calls and not words,
                'known-query callee excludes local BL and word switches')
        require(address not in FAMILIES and
                all(address not in family['bodies'] for family in FAMILIES.values()),
                'pinned list-query bodies are not known-query callees')
        for site, target in calls.items():
            match.function_address_target(f'func_{target:08X}', json.loads(self.mapping),
                                          address, len(data), len(self.rom))
        self.contract()
        result = stack_query.execute(data, address, instructions, edges, calls)
        self.query_sites.update(site for site, target in calls.items() if target in stack_query.QUERIES)
        record = {
            'address': address, 'end': address + len(data), 'bytes': len(data),
            'body_sha256': sha(data),
            'structure': {'kind': 'known-query-stack-buffer-callee-v1',
                          'instructions': len(instructions),
                          'partition': graph.partition(data, address, refinement, instructions, words),
                          'calls': [[site - address, f'func_{target:08X}']
                                    for site, target in sorted(calls.items())],
                          'caller': result},
            **self.identities}
        previous = self.records.get(address)
        require(previous is None or previous == record, 'known-query callee record differs between visits')
        self.records[address] = record
        self.query_callers[address] = record
        return [instructions[site] for site in sorted(instructions)], {}

    def check_arguments(self, address, arguments, stack, incoming, protected, *, constants=None,
                        site=None, words=None, frame_base=None, root_frame=None, watched=()):
        if address in FAMILIES and (arguments or incoming or words or watched):
            try:
                require(not incoming and not words and not watched,
                        'stack-passed pointer words cannot reach a pinned list-query family')
                require(set(arguments) <= set(TRANSPARENT),
                        'owner alias reaches a live input of a pinned list-query family')
                require(address not in stack_query.QUERIES or site in self.query_sites,
                        'pinned query call is outside a callee executed under its contract')
                if address not in self.families:
                    self.families[address] = family_facts(address, self.rom, self.mapping, self.index)
                retained = {register: offset for register, offset in arguments.items()
                            if register in UNTOUCHED}
                observation = dict(site=site, target=address,
                                   dead=sorted(f'r{r - R0}' for r in arguments if r not in UNTOUCHED),
                                   retained=sorted([f'r{r - R0}', offset] for r, offset in retained.items()))
                key = (site, tuple(sorted(arguments.items())))
                self.summaries[key] = observation
                return self.word_result(retained, {})
            except ValueError as error:
                raise ValueError(f'buffer callee 0x{address:08X}: {error}') from error
        return super().check_arguments(address, arguments, stack, incoming, protected,
            constants=constants, site=site, words=words, frame_base=frame_base,
            root_frame=root_frame, watched=watched)

    def query_manifest(self):
        import owner_admission_profile
        require(self.query_callers, 'known-query callee profile requires an executed known-query callee')
        return dict(
            selector=SELECTOR,
            query_contract=self.contract(),
            callees=sorted(self.query_callers),
            capacity_words=stack_query.CAPACITY_WORDS,
            premise='every list reached by a pinned query from an executed callee has at most 13 nodes',
            list_bound_proved_from_ROM=False,
            families=[self.families[root] for root in sorted(self.families)],
            family_calls=[self.summaries[key] for key in sorted(self.summaries, key=repr)],
            explicit_conditions=list(CALLEE_CONDITIONS),
            producer_sha256={Path(module.__file__).name: sha(Path(module.__file__).read_bytes())
                             for module in (match, named, stack_query, closure, graph,
                                            owner_admission_profile, software_double_profile,
                                            __import__(__name__))})
