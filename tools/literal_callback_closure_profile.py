"""Initialized local descriptors whose callback word is a typed function literal.

Seven exact root forms reach one of a closed table of pinned read-only node
iterators (the 080C7CC0 list walk or the 080C7D18/080C7D70 in-order tree
walks) and either the two-word scalar adapter admitted by
conditional-two-word-callback-closure-v1 or a pinned framed two-output adapter
whose getter effect is interpreted. Descriptor
word zero is the constant zero, the entry R0 value, the u8 narrowing of entry
R1, the owner word that is also the iterator's list argument, the address of
a private two-word state (initialized to zero and entry R1, or to entry R1 and
entry R2), or the address of a private flag byte initialized to zero. The
owner-word form makes one more opaque typed call
on the reloaded owner word; that callee must provably overwrite entry R2 (the
descriptor address on the empty-list path) before reading it. Only the state
and flag forms pass private-frame provenance, so only an exact pinned callback
is admitted there and its complete effect is interpreted: a state callback is
one straight-line leaf, a flag callback a pinned closed call tree. The
private-state root returns the state word it reads back after the call; the
flag root returns whether the flag byte it reads back is nonzero.
Opaque callbacks retain the explicit compatible returning ABI and memory
noninterference premises. No iteration bound or termination is assumed.
"""
import hashlib
import json
from pathlib import Path
import struct

from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
from capstone.arm_const import (ARM_CC_AL, ARM_INS_ADD, ARM_INS_B, ARM_INS_BL, ARM_INS_BX, ARM_INS_LDM,
    ARM_INS_LDR, ARM_INS_LDRB, ARM_INS_LDRH, ARM_INS_LDRSB, ARM_INS_LDRSH, ARM_INS_MOV, ARM_INS_POP,
    ARM_INS_PUSH, ARM_INS_STM, ARM_INS_STR, ARM_INS_STRB, ARM_INS_STRH, ARM_INS_SUB, ARM_OP_IMM, ARM_OP_REG)

import match
import owner_admission_profile as owner
import callee_preservation_profile as preservation
import owner_graph_profile as graph
import function_thunk_profile as thunk
import local_long_branch_profile as frame
import scalar_callback_adapter_inventory as adapter
from software_double_profile import indices, span_record

SELECTOR = 'conditional-two-word-literal-callback-closure-v1'
SCHEMA = 'elf-symbol-thumb-conditional-two-word-literal-callback-closure-v1'
CONTROL_FLOW = 'complete initialized two-word local descriptor with typed callback literal and read-only callback iterator; private state only through an interpreted pinned callback; compatible returning indirect ABI and memory noninterference conditional; termination unproved; optional pinned opaque trailing call that overwrites R2 before reading it'
PRESERVED = adapter.PRESERVED
# Closed table of read-only callback iterators. Each body is pinned by size,
# refined count and SHA-256; the pin is the admission gate. The structure is
# then re-derived over the instruction graph: the entry copies of the adapter
# (R1) and descriptor (R2) into callee-saved registers, which nothing else
# writes; the one call through the adapter register's thunk with R0 = current
# node and R1 = descriptor; no stores; and exactly the listed word reads, from
# the list object (entry R0 before any path overwrites it) or the current node
# (R4). The two tree walks are the bodies that
# tree_two_word_callback_closure_profile (conditional-two-word-tree-callback-
# closure-v1) admits by template for parameter-callback roots.
ITERATORS = {
    0x080C7CC0: dict(size=34, count=16, call=20, adapter_register=6, descriptor_register=5,
        sha256='47422d610f242091222c8c8e303ea235eede92f9a9c9cc40cd8552e8f44f45d1',
        kind='singly linked list: first node at list+4, next node at node+8',
        reads=(('list', 4), ('node', 8)),
        loop_invariant='R6 is the exact adapter Thumb pointer; R5 is the original initialized descriptor; R4 is null or the current ordinary node. Each returning adapter preserves R4-R11/SP. Only node+8 advances the loop; callback R0 selects continuation.'),
    0x080C7D18: dict(size=86, count=42, call=50, adapter_register=7, descriptor_register=6,
        sha256='ee7686daca5c7774589a5795bd17453d4f109674942402d1a7fcc13296e78da2',
        kind='parent-linked binary tree, in order: root at list+8, parent at node+8, node+12 subtree visited before node+16',
        reads=(('list', 8), ('node', 8), ('node', 12), ('node', 16)),
        loop_invariant='R7 is the exact adapter Thumb pointer; R6 is the original initialized descriptor; R5 is the root node; R4 is null or the current ordinary node; at the loop head R2 is -1 or the previous node (it is reset on every path back to the head, and arbitrary after a returning adapter). Moves are only to node+12, node+16 or the node+8 parent; each returning adapter preserves R4-R11/SP. The adapter is called with the current nonnull node and the descriptor; callback R0 zero stops, as does ascending from the root.'),
    0x080C7D70: dict(size=86, count=42, call=50, adapter_register=7, descriptor_register=6,
        sha256='6af858bb8def974b2ad9e56dce5bc14c3d6a4b8c5a3570e9f6478c9d8ccf07c5',
        kind='parent-linked binary tree, in order: root at list+8, parent at node+8, node+16 subtree visited before node+12',
        reads=(('list', 8), ('node', 8), ('node', 12), ('node', 16)),
        loop_invariant='R7 is the exact adapter Thumb pointer; R6 is the original initialized descriptor; R5 is the root node; R4 is null or the current ordinary node; at the loop head R2 is -1 or the previous node (it is reset on every path back to the head, and arbitrary after a returning adapter). Moves are only to node+16, node+12 or the node+8 parent; each returning adapter preserves R4-R11/SP. The adapter is called with the current nonnull node and the descriptor; callback R0 zero stops, as does ascending from the root.'),
}
# Closed table of framed two-output adapters. The adapter and its getter are
# pinned byte for byte, authenticated again by
# two_output_callback_adapter_inventory.verify, and interpreted by
# framed_adapter_effects. Scalar adapters still go through
# scalar_callback_adapter_inventory unchanged.
FRAMED_ADAPTERS = {
    0x0809AC00: dict(count=14, body='10b582b00c1c01aa69462cf0b5ff009821686268a7f01afb02b010bc02bc0847',
        getter=0x080C7B78, getter_count=5, getter_body='43680b60006810607047'),
}
FRAMED_SCHEMA = 'two-word-framed-two-output-callback-adapter-v1'
# Exact root forms. 'xx' marks the aligned owner word-load halfword(s), the
# BL(s) and the two typed literal words; every other byte is fixed, including
# any zero alignment halfword before the pool. owner_base is the register the
# owner word is loaded through (R0 or R4 are entry R0; R2 is the word at entry
# R0+128). A form with 'trailing' makes one more ordinary typed call after the
# iterator: its R0 is the owner word reloaded by the same pinned halfword, and
# the callee must provably overwrite R2 before reading it (see entry_r2_killed).
FORMS = {
    'private-state': dict(size=44, count=17, call=24, owner=20, callback=36, adapter=40, owner_base=0,
        stack_words=5, frame_bytes=16, descriptor=-12, state=-20, word0='address of private state at entry SP-20',
        code='00b584b000220092019106496a46029202aa5160xxxx0449xxxxxxxx009804b002bc0847'),
    'entry-object': dict(size=40, count=15, call=22, owner=16, callback=32, adapter=36, owner_base=2,
        stack_words=3, frame_bytes=8, descriptor=-12, state=None, word0='root entry R0',
        code='00b582b0011c80310a68054900900191xxxx04496a46xxxxxxxx02b001bc0047'),
    'null': dict(size=36, count=13, call=18, owner=12, callback=28, adapter=32, owner_base=0,
        stack_words=3, frame_bytes=8, descriptor=-12, state=None, word0='constant zero',
        code='00b582b0054a002100910192xxxx04496a46xxxxxxxx02b001bc0047'),
    # lsls r1,r1,#24; lsrs r1,r1,#24: word0 is the u8 narrowing of entry R1.
    'entry-byte': dict(size=40, count=14, call=20, owner=14, callback=32, adapter=36, owner_base=0,
        stack_words=3, frame_bytes=8, descriptor=-12, state=None, word0='root entry R1 narrowed to its low 8 bits (u8)',
        alignment_bytes=2,
        code='00b582b00906090e054a00910192xxxx04496a46xxxxxxxx02b001bc00470000'),
    # adds r4,r0,#0 saves the owner; word0 is the owner word that is also the
    # iterator's list argument, and the owner word is reloaded for one more call.
    'owner-word-trailing-call': dict(size=44, count=16, call=18, owner=8, callback=36, adapter=40, owner_base=4,
        stack_words=4, frame_bytes=8, descriptor=-16, state=None,
        word0='owner word loaded from root entry R0 (the iterator list argument)',
        saved=['entry R4', 'entry LR'], trailing=dict(reload=22, call=24),
        code='10b582b0041c0749xxxx0090019106496a46xxxxxxxxxxxxxxxxxxxx02b010bc01bc0047'),
    # str r1,[sp]; str r2,[sp,#4]: the private state is entry R1 and entry R2;
    # the root returns nothing after the iterator.
    'entry-state': dict(size=40, count=15, call=22, owner=18, callback=32, adapter=36, owner_base=0,
        stack_words=5, frame_bytes=16, descriptor=-12, state=-20, word0='address of private state at entry SP-20',
        state_sources=['root entry R1', 'root entry R2'],
        code='00b584b00091019205496a46029202aa5160xxxx0349xxxxxxxx04b001bc0047'),
    # strb of zero at SP+0: a private flag byte; after the iterator the root
    # returns 1 if the byte it reads back is nonzero, else 0. The literal pool
    # sits between the branch and the `movs r0,#1` arm, so this template spans
    # the whole function with the two literal words masked.
    'local-byte-flag': dict(size=56, count=23, call=24, owner=20, callback=40, adapter=44, owner_base=0,
        stack_words=4, frame_bytes=12, descriptor=-12, state=-16, flag=True,
        word0='address of private flag byte at entry SP-16',
        code='00b583b0002269460a7007496a46019201aa5160xxxx0549xxxxxxxx' +
             '68460078002805d1002004e0xxxxxxxxxxxxxxxx012003b002bc0847'),
}
# The only private-state callbacks admitted: each receives the state address
# in R1, so its complete body is pinned, interpreted below and compared with
# the pinned effect, and it is paired with the one root form whose state it
# was written for.
STATE_CALLBACKS = {
    0x0809AC20: dict(count=8, body='4a6801c20868013008604a6001207047', form='private-state',
        state={0: ('state-word-0-plus', 1), 4: ('cursor-plus', 4)}, reads=[0, 4], writes=[0, 4],
        external=[['state word 4 on entry', 0, 4, ('object',)]], external_reads=None,
        relation='state word 0 becomes its incoming value plus 1 modulo 2**32; the object word is stored at the incoming state word 4 cursor, which then advances by 4; R0 is 1',
        condition='Each callback store through the state word-4 cursor is aligned, live and writable, and does not overlap the private state, descriptor, any active frame, saved return, reached list/node word or code. The incoming entry R1 cursor carries no private-frame provenance.'),
    # flags = (flags & ~state word 0) | state word 4 on the getter object's word +0x30.
    0x0809ACA4: dict(count=8, body='0b68026b9a4349680a43026301207047', form='entry-state',
        state={0: ('state-word', 0), 4: ('state-word', 4)}, reads=[0, 4], writes=[],
        external=[['getter object', 48, 4, ('orr', ('bic', ('object-word', 48), ('state-word', 0)), ('state-word', 4))]],
        external_reads=[['getter object', 48, 4]],
        relation='the getter object word at offset 48 becomes its incoming value with the state word 0 bits cleared and the state word 4 bits set; the state is unchanged; R0 is 1',
        condition='Each callback read and store of the getter object word at offset 48 is aligned, live and writable, and does not overlap the private state, descriptor, any active frame, saved return, reached list/node word or code. Entry R1 and R2 are plain values with no private-frame provenance.'),
}
# The only private-flag callback admitted. It passes the flag address on to
# one more function, so every body of its closed call tree is pinned by size,
# refined count and SHA-256 and interpreted by flag_callback_effects.
FLAG_CALLBACKS = {
    0x0809AD48: dict(form='local-byte-flag', tree={
        0x0809AD48: (36, 17, '18141579ff95f6859544bcdcea3fe138acdf664c73032f5675d426fad69a2c27'),
        0x08098BB0: (112, 50, '4b56b7d9e7ba587ee64a6d4da1eb3b51b2e6eb7cfcb989a8534fa86a7602c3cc'),
        0x080C8280: (22, 11, '33e067dc316794030f84309a4c8d18596a7fe650cb28b690d0492074a005519a'),
        0x080CD8CC: (24, 12, '180dcaecef3658e1414a89afae835b169bdd66126effd096e051010923a0ae20'),
        0x080CD92C: (24, 12, 'c4bfad5ce6d700a044e870c096ac8925ba21c0463ef0cbefdc821f6a2284107f'),
        0x080CDCEC: (24, 12, '21d87689aa4d78d95f69dc245241dc0a9a288d44c410cd9c172fce7ee3c4dd04'),
        0x080C8260: (30, 15, '012eb195abb4b4bc794cee97ed92e2a292332e31b3012d9765ffc822079c4140'),
        0x080C84C0: (50, 25, '27b070e82b5721ceb1acd1a8863b243d1056416caf5474c5026b53689793d874')}),
}


def sha(data): return hashlib.sha256(data).hexdigest()


def require(ok, message):
    if not ok: raise ValueError(message)


def complete(address, size, count, rom, mapping, index):
    # count is the refined reachable-instruction count (literal pools excluded,
    # as analyze.refine_function reports); both indexes must carry it.
    data = rom[address-match.ROM_BASE:address-match.ROM_BASE+size]
    owner.validate_span(data, address, rom, mapping, index)
    entries, rows = indices(mapping, index)
    identity = span_record(address, address+size, entries, rows, rom)
    refinement = owner.refine(data, address, mapping)
    ins, edges, branches, calls, words = graph.graph(data, address, refinement)
    partition = graph.partition(data, address, refinement, ins, words)
    require(not branches and not words and len(ins) == count and identity['instrs'] == count,
            'literal closure requires exact complete owner/count')
    return data, ins, edges, calls, partition


def form_of(data):
    """Return the unique exact root form; masked halfwords are decoded later."""
    found = []
    for name, form in FORMS.items():
        # A template ends before the trailing pool, or spans the whole function
        # with an interior pool masked. A whole-function template must pin
        # every branch that could reach the masked bytes, so that the pool is
        # never executed (the local-byte-flag template pins both).
        code = form['code']
        compared = form['size'] if len(code) == 2*form['size'] else form['size']-8
        if len(data) == form['size'] and len(code) == 2*compared and all(
                code[2*n:2*n+2] == 'xx' or bytes.fromhex(code[2*n:2*n+2])[0] == data[n]
                for n in range(compared)):
            found.append(name)
    require(len(found) == 1, 'literal closure requires one complete natural root form')
    return found[0]


def _token(value):
    """Render a symbolic state-callback value for the report."""
    if value == ('object',):
        return 'object'
    if value[0] in ('bic', 'orr'):
        return f"({_token(value[1])} {'& ~' if value[0] == 'bic' else '| '}{_token(value[2])})"
    return f"{value[0].replace('-', ' ')} {value[1]}"


def state_callback_effects(body, address):
    """Interpret the complete straight-line state callback on symbolic tokens.

    R0 is the getter word (object), R1 the private state address. State words
    0 and 4 hold their entry tokens. Every access through R1 must be an aligned
    word of the two-word state; the only other accesses are word accesses
    through the getter object and a store through the value loaded from state
    word 4. The callback must return 1 by BX LR with R4-R11, SP and LR
    unchanged and no state address stored in memory, and its effect must be
    the one pinned for its address.
    """
    require(type(body) is bytes and type(address) is int and address in STATE_CALLBACKS and
            body == bytes.fromhex(STATE_CALLBACKS[address]['body']), 'pinned state callback body differs')
    pinned = STATE_CALLBACKS[address]
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB); decoder.detail = True
    code = list(decoder.disasm(body, address))
    require(sum(item.size for item in code) == len(body) and len(code) == pinned['count'],
            'complete code-only state callback required')
    regs = {n: ('entry', n) for n in range(13)}
    regs[0], regs[1], regs[14] = ('object',), ('state',), ('return',)
    state = {0: ('state-word', 0), 4: ('state-word', 4)}
    reads, writes, external, external_reads = [], [], [], []
    for number, item in enumerate(code):
        raw = int.from_bytes(item.bytes, 'little')
        last = number == len(code)-1
        require(item.size == 2 and raw != 0x4770 and not last or raw == 0x4770 and last,
                'state callback must be one linear block ending in BX LR')
        if raw == 0x4770:
            break
        if raw & 0xf000 == 0x6000:  # LDR/STR Rd,[Rb,#imm5*4]
            rd, rb, offset = raw & 7, (raw >> 3) & 7, 4*((raw >> 6) & 31)
            require(regs[rd] != ('state',) or raw & 0x800, 'state callback stores the private state address')
            if regs[rb] == ('object',):
                if raw & 0x800:
                    regs[rd] = ('object-word', offset); external_reads.append([item.address, 'getter object', offset, 4])
                else:
                    external.append([item.address, 'getter object', offset, 4, regs[rd]])
                continue
            require(regs[rb] == ('state',) and offset in state,
                    'state callback word access leaves the private two-word state')
            if raw & 0x800:
                regs[rd] = state[offset]; reads.append([item.address, offset, 4])
            else:
                state[offset] = regs[rd]; writes.append([item.address, offset, 4])
        elif raw & 0xf800 == 0xc000:  # STMIA Rb!,{Rlist}
            rb, rlist = (raw >> 8) & 7, raw & 255
            require(regs[rb] == ('state-word', 4) and rlist & ~(1 << rb) == rlist and
                    bin(rlist).count('1') == 1, 'state callback external store requires the loaded cursor')
            rs = rlist.bit_length()-1
            require(regs[rs] == ('object',), 'state callback external store must be the getter word')
            external.append([item.address, 'state word 4 on entry', 0, 4, regs[rs]])
            regs[rb] = ('cursor-plus', 4)
        elif raw & 0xf800 == 0x3000:  # ADDS Rd,#imm8
            rd = (raw >> 8) & 7
            require(regs[rd] == ('state-word', 0), 'state callback arithmetic must update state word 0')
            regs[rd] = ('state-word-0-plus', raw & 255)
        elif raw & 0xf800 == 0x2000:  # MOVS Rd,#imm8
            regs[(raw >> 8) & 7] = ('constant', raw & 255)
        elif raw & 0xffc0 in (0x4380, 0x4300):  # BICS/ORRS Rd,Rm
            rd, rm = raw & 7, (raw >> 3) & 7
            require(('state',) not in (regs[rd], regs[rm]), 'state callback computes with the private state address')
            regs[rd] = ('bic' if raw & 0xffc0 == 0x4380 else 'orr', regs[rd], regs[rm])
        else:
            raise ValueError('unsupported state callback instruction')
    require(regs[0] == ('constant', 1) and regs[14] == ('return',) and
            all(regs[n] == ('entry', n) for n in range(4, 12)),
            'state callback return/frame differs')
    require(state == pinned['state'] and sorted(row[1] for row in reads) == pinned['reads'] and
            sorted(row[1] for row in writes) == pinned['writes'] and
            [row[1:] for row in external] == pinned['external'] and
            [row[1:] for row in external_reads] == (pinned['external_reads'] or []),
            'state callback effect relation differs')
    record = dict(address=address, end=address+len(body), instructions=len(code), body_sha256=sha(body),
        state_reads=reads, state_writes=writes, external_writes=[row[:4]+[_token(row[4])] for row in external])
    if pinned['external_reads'] is not None:
        record['external_reads'] = external_reads
    return dict(record, return_value=1, relation=pinned['relation'],
        frame_bytes=0, protected_registers=[], leaf=True,
        private_state_address_stored=False, all_paths_interpreted=True)


def entry_r2_killed(rom, address, end):
    """Prove a trailing callee overwrites entry R2 before anything can read it.

    The callee is decoded as ARMv4T Thumb (callee_preservation_profile._decode)
    from its entry along its only concrete path. Every instruction up to the
    first R2 write must not read R2 or write PC, and must not be a call,
    return or conditional branch; unconditional B is followed inside the
    indexed span and a revisited address refuses. The callee's entry SP is the
    root's descriptor address, so SP is tracked: only PUSH and SUB/ADD SP,#imm
    may move it, and registers derived from SP (including anything loaded
    through SP, which may be a stale frame word holding the descriptor
    address) are tainted, as is any load after a tainted value was stored.
    An SP-derived overwrite (MOV/ADD R2,SP[,#k]) is admitted only when
    its value is strictly below entry SP, which is the callee's own frame and
    not the descriptor. Returns the overwriting site.
    """
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB); decoder.detail = True
    r2, pc, sp = match.ARM_REG_R0+2, match.ARM_REG_PC, match.ARM_REG_SP
    here, seen, depth, tainted, stored = address, set(), 0, set(), False
    while True:
        require(here not in seen, 'trailing callee must overwrite R2 on its entry path')
        seen.add(here)
        try:
            item = preservation._decode(decoder, rom, here, address, end)
        except ValueError as error:
            raise ValueError(f'trailing callee may observe entry R2: {error}') from None
        read, written = (set(regs) for regs in item.regs_access())
        require(r2 not in read and pc not in written and item.id not in (ARM_INS_BL, ARM_INS_BX) and
                (item.id != ARM_INS_B or item.cc == ARM_CC_AL), 'trailing callee may observe entry R2')
        ops = item.operands
        loads = item.id in (ARM_INS_LDR, ARM_INS_LDRB, ARM_INS_LDRH, ARM_INS_LDRSB, ARM_INS_LDRSH, ARM_INS_LDM, ARM_INS_POP)
        values = [op.reg for op in ops if op.type == ARM_OP_REG] if item.id == ARM_INS_PUSH else \
            [op.reg for op in ops[1:] if op.type == ARM_OP_REG] if item.id == ARM_INS_STM else \
            [ops[0].reg] if item.id in (ARM_INS_STR, ARM_INS_STRB, ARM_INS_STRH) else []
        if set(values) & (tainted | {sp}):
            stored = True  # an SP-derived value is now in memory
        if item.id == ARM_INS_PUSH:
            depth -= 4*len(ops)
        elif sp in written:
            # Only SUB/ADD SP,#imm; capstone lists SP as destination and source.
            require(item.id in (ARM_INS_SUB, ARM_INS_ADD) and ops[0].reg == sp and ops[-1].type == ARM_OP_IMM and
                    all(op.type == ARM_OP_IMM or op.reg == sp for op in ops),
                    'trailing callee moves SP outside PUSH/SUB/ADD SP,#imm')
            depth += ops[-1].imm if item.id == ARM_INS_ADD else -ops[-1].imm
        else:
            # Loads may also return SP-derived values another frame left in memory.
            derived = bool(read & (tainted | {sp})) or loads and stored
            if r2 in written:
                if derived:
                    offset = sum(op.imm for op in ops[1:] if op.type == ARM_OP_IMM)
                    require(item.id in (ARM_INS_MOV, ARM_INS_ADD) and ops[0].reg == r2 and
                            [op.reg for op in ops[1:] if op.type == ARM_OP_REG] == [sp] and depth+offset < 0,
                            'trailing callee overwrites R2 with an SP-derived value at or above its entry SP')
                return here
            tainted = (tainted - written) | (written if derived else set())
        here = ops[0].imm if item.id == ARM_INS_B else here+item.size


OTHER, FLAG, BYTE0, INCREMENT = ('value',), ('flag',), ('flag-byte-0',), ('flag-byte-0-plus-1',)
# Flag byte 1 (never initialized by the root) and its bits masked by a constant:
# these may only feed the condition flags (ANDS with a constant, then CMP/TST).
BYTE1, BITS1 = ('flag-byte-1',), ('flag-byte-1-bits',)
# A flag byte 0 value read before a later store or call: still flag data, but
# no longer the current byte, so it can never feed the increment store.
STALE = ('flag-byte-0-stale',)
FLAG_BYTES = {BYTE0, INCREMENT, BYTE1, BITS1, STALE}
# Tokens that may not be computed with or dereferenced except as admitted
# below: the flag address, its byte values in flight, and the callee-saved and
# return values every interpreted function must give back.
_TRACKED = lambda token: token[0] in ('flag', 'flag-byte-0', 'flag-byte-0-plus-1', 'flag-byte-1',
                                      'flag-byte-1-bits', 'flag-byte-0-stale', 'preserved', 'return',
                                      'expired-return')
_CONSTANT = lambda values: bool(values) and all(token[0] == 'constant' for token in values)


def flag_callback_effects(callback, rom, mapping, index, seeds=()):
    """Interpret the complete pinned call tree of a private-flag callback.

    Entry R1 is the private flag address; R0 and R2 are ordinary values, and
    the scratch registers in seeds may also hold the flag address (left there
    by an earlier invocation). Each pinned body is completed against the index
    and walked over its whole instruction graph with a forward may-analysis;
    calls are only to tree members and are interpreted in their caller's
    context. A callee's R4-R11 start as fresh preserved tokens that also carry
    the flag address when the caller's register may hold it, so the address
    is followed through every copy. The analysis refuses any access through
    the flag address other than a byte read of flag byte 0 or 1 and a byte
    store to flag byte 0 of that byte's value plus one, and any store or push
    of the flag address. The only operation admitted on the flag address or a
    callee-saved or return value is a register copy (which also sets the
    condition flags); any other use, including as a load base, refuses. Flag
    byte 1 may only be masked by a constant with ANDS and the result only
    tested by CMP/TST with a constant, so it only selects paths. Any other
    store, any SP-relative access other than PUSH/POP of the function's own
    frame, any return that does not restore R4-R11 and SP and leave through
    the entry LR, and any callee-saved token of the returning function left
    in R0-R3/R12 also refuses; its return address left there stays tracked.
    A flag byte value read before a later store or call stays tracked as
    stale, and no flag byte value may be left in R0-R3/R12 when the callback
    returns. Returns the effect record and the scratch registers that may
    still hold the flag address on return.
    """
    pinned = FLAG_CALLBACKS[callback]['tree']
    graphs = {}
    for address, (size, count, digest) in pinned.items():
        body, ins, edges, calls, partition = complete(address, size, count, rom, mapping, index)
        require(sha(body) == digest and not partition['literal_and_table_bytes'] and
                not partition['alignment_bytes'] and set(calls.values()) <= set(pinned),
                'pinned flag callback tree differs')
        graphs[address] = (ins, edges, calls)
    reads, writes, external = set(), set(), set()
    active = []

    def run(address, entry):
        require(address not in active, 'flag callback tree must not recurse')
        active.append(address)
        depth = len(active)
        ins, edges, calls = graphs[address]
        caller = entry
        regs = {n: entry[n] for n in (0, 1, 2, 3, 12)}
        # FLAG membership travels with the callee-saved value, so a copy of it
        # out of R4-R11 is still followed.
        regs.update({n: frozenset({('preserved', depth, n)}) | (caller.get(n, frozenset()) & {FLAG})
                     for n in range(4, 12)})
        start = dict(regs)
        regs[14] = frozenset({('return', depth)})
        states, pending, exits = {address: (regs, 0, {})}, [address], []
        while pending:
            site = pending.pop()
            regs, sp, frame = states[site]
            regs, frame = dict(regs), dict(frame)
            item = ins[site]
            raw = struct.unpack_from('<H', item.bytes)[0]
            def value(n):
                require(not any(_TRACKED(token) for token in regs[n]),
                        'flag callback computes with a tracked flag, byte or preserved value')
                return regs[n]
            def forget():
                # A store or call ends every byte value read before it.
                for table in (regs, frame):
                    for key in table:
                        if table[key] & {BYTE0, INCREMENT}:
                            table[key] = (table[key] - {BYTE0, INCREMENT}) | {STALE}
            if site in calls:
                result = run(calls[site], {n: regs[n] for n in (0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12)})
                regs.update(result); regs[14] = frozenset({OTHER})
                forget()
            elif raw & 0xFE00 in (0xB400, 0xBC00):  # PUSH/POP {Rlist[,LR|PC]}
                listed = [n for n in range(8) if raw >> n & 1]
                if raw & 0xFE00 == 0xB400:
                    listed += [14] if raw & 0x100 else []
                    require(not any(FLAG in regs[n] for n in listed), 'flag callback stores the flag address')
                    sp -= 4*len(listed)
                    for number, n in enumerate(listed): frame[sp+4*number] = regs[n]
                else:
                    require(not raw & 0x100, 'flag callback must not pop PC')
                    for n in listed:
                        require(sp in frame, 'flag callback pops a word it did not push')
                        regs[n] = frame.pop(sp); sp += 4
            elif raw & 0xFE00 == 0x1C00 and not raw & 0x1C0 or raw & 0xFFC0 == 0x0000:  # ADDS Rd,Rn,#0 / MOVS Rd,Rm
                regs[raw & 7] = regs[raw >> 3 & 7]
            elif raw & 0xF800 == 0x3000 and regs[raw >> 8 & 7] == frozenset({BYTE0}) and raw & 0xFF == 1:
                regs[raw >> 8 & 7] = frozenset({INCREMENT})  # ADDS Rd,#1 on flag byte 0
            elif raw & 0xF800 == 0x2000:  # MOVS Rd,#imm8
                regs[raw >> 8 & 7] = frozenset({('constant', raw & 0xFF)})
            elif raw & 0xE000 == 0x6000 or raw & 0xF000 == 0x8000:  # LDR/STR(B/H) Rd,[Rb,#imm]
                rd, rb = raw & 7, raw >> 3 & 7
                width = 4 if raw & 0xF000 == 0x6000 else 1 if raw & 0xF000 == 0x7000 else 2
                offset, load = width*(raw >> 6 & 31), bool(raw & 0x800)
                if FLAG in regs[rb]:
                    require(regs[rb] == frozenset({FLAG}) and width == 1 and
                            (offset in (0, 1) if load else offset == 0 and regs[rd] == frozenset({INCREMENT})),
                            'flag callback access through the flag address differs')
                    (reads if load else writes).add((site, offset))
                    if load:
                        regs[rd] = frozenset({BYTE0 if offset == 0 else BYTE1})
                    else:
                        forget()
                else:
                    value(rb)
                    require(load, 'flag callback stores outside the private flag byte')
                    external.add((site, offset, width))
                    regs[rd] = frozenset({OTHER})
            elif raw & 0xF000 == 0xD000 and raw & 0x0E00 != 0x0E00 or raw & 0xF800 == 0xE000:  # B<cond> / B
                pass
            elif raw & 0xFF87 == 0x4700:  # BX Rm
                rm = raw >> 3 & 15
                require(rm in regs and regs[rm] == frozenset({('return', depth)}) and sp == 0 and not frame and
                        all(regs[n] == start[n] for n in range(4, 12)) and
                        not any(token[0] == 'preserved' and token[1] == depth
                                for n in (0, 1, 2, 3, 12) for token in regs[n]),
                        'flag callback return/frame differs')
                # The popped return address (POP {R1}; BX R1) stays tracked in the caller.
                exits.append({n: frozenset(('expired-return',) if token == ('return', depth) else token
                                           for token in regs[n]) for n in regs})
            else:
                # Remaining ARMv4T data processing on ordinary values only.
                if raw & 0xE000 == 0x0000 and raw & 0x1800 != 0x1800:  # LSLS/LSRS/ASRS Rd,Rm,#imm5
                    value(raw >> 3 & 7); regs[raw & 7] = frozenset({OTHER})
                elif raw & 0xF800 == 0x2800 and regs[raw >> 8 & 7] <= {BYTE1, BITS1}:
                    pass  # CMP of flag byte 1 (bits) with a constant: condition flags only
                elif raw & 0xE000 == 0x2000:  # MOVS/CMP/ADDS/SUBS Rd,#imm8
                    value(raw >> 8 & 7)
                    if raw & 0x1800 != 0x0800: regs[raw >> 8 & 7] = frozenset({OTHER})
                elif raw & 0xFC00 == 0x1800 or raw & 0xFC00 == 0x1C00:  # ADDS/SUBS Rd,Rn,Rm|#imm3
                    value(raw >> 3 & 7)
                    if not raw & 0x400: value(raw >> 6 & 7)
                    regs[raw & 7] = frozenset({OTHER})
                elif raw & 0xFC00 == 0x4000 and (raw >> 6 & 15) in (0, 8) and \
                        {regs[raw & 7], regs[raw >> 3 & 7]} & {frozenset({BYTE1}), frozenset({BITS1})} and \
                        any(_CONSTANT(regs[n]) for n in (raw & 7, raw >> 3 & 7)):
                    # ANDS/TST of flag byte 1 with a constant: the result is still flag byte 1 bits.
                    if not raw >> 6 & 15: regs[raw & 7] = frozenset({BITS1})
                elif raw & 0xFC00 == 0x4000:  # ALU Rd,Rm
                    op, rd, rm = raw >> 6 & 15, raw & 7, raw >> 3 & 7
                    value(rm)
                    if op not in (9, 15): value(rd)
                    if op not in (8, 10, 11): regs[rd] = frozenset({OTHER})
                else:
                    raise ValueError('unsupported flag callback instruction')
            for target in edges[site]:
                old = states.get(target)
                if old is None:
                    states[target] = (regs, sp, frame); pending.append(target); continue
                require(old[1] == sp and set(old[2]) == set(frame), 'flag callback frame differs between paths')
                merged = ({n: old[0][n] | regs[n] for n in regs}, sp, {k: old[2][k] | frame[k] for k in frame})
                if merged != old:
                    states[target] = merged; pending.append(target)
        require(exits, 'flag callback tree must return')
        active.pop()
        return {n: frozenset().union(*(state[n] for state in exits)) for n in (0, 1, 2, 3, 12)}

    entry = {n: frozenset({OTHER}) for n in (0, 2, 3, 12)}
    entry[1] = frozenset({FLAG})
    for n in seeds:
        entry[n] = entry[n] | {FLAG}
    result = run(callback, entry)
    # No flag byte value (read, incremented or masked) may leave the tree: the
    # recorded uses of the flag bytes are all the tree makes of them.
    require(result[0] == frozenset({('constant', 1)}) and not any(FLAG in result[n] for n in (0, 1, 2)) and
            not any(result[n] & FLAG_BYTES for n in (0, 1, 2, 3, 12)),
            'flag callback return/frame differs')
    require(writes, 'flag callback effect relation differs')
    tree = [dict(address=address, end=address+size, instructions=count, body_sha256=digest)
            for address, (size, count, digest) in sorted(pinned.items())]
    return dict(address=callback, end=callback+pinned[callback][0], tree=tree, flag_reads=[[site, offset, 1] for site, offset in sorted(reads)],
        flag_writes=[[site, offset, 1, 'flag byte 0 read since the last store or call, plus 1 modulo 2**8']
                     for site, offset in sorted(writes)],
        external_reads=[list(row) for row in sorted(external)], external_writes=[], return_value=1,
        relation='flag byte 0 is only ever replaced by its current value plus 1 modulo 2**8; flag byte 1 is only read, masked by constants and tested, so it only selects paths; nothing else is stored; R0 is 1',
        flag_address_stored=False, all_paths_interpreted=True), \
        sorted(n for n in (3, 12) if FLAG in result[n])


def scratch_aliases_unread(ins, edges, calls, start, registers):
    """No path from start reads a scratch register that may hold the flag address.

    The registers may hold it at start and again after every call (the
    interpreted callback can leave it there); an instruction that writes one
    without reading it ends that register's alias on the path.
    """
    numbers = {match.ARM_REG_R0+n for n in registers}
    live, pending = {start: frozenset(numbers)}, [start]
    while pending:
        site = pending.pop()
        read, written = (set(regs) for regs in ins[site].regs_access())
        require(not read & live[site], 'flag address alias reaches a reader outside the interpreted callback')
        after = numbers if site in calls else live[site] - written
        for target in edges[site]:
            merged = live.get(target, frozenset()) | after
            if target not in live or merged != live[target]:
                live[target] = merged; pending.append(target)


def iterator_structure(body, address, entry, ins, edges, calls):
    """Check one pinned iterator entry and re-derive its structural facts.

    The SHA-256 pin is the admission gate. The checks below run over the
    complete instruction graph from complete() and derive what the report
    records, so a future table entry cannot declare facts its body lacks.
    """
    require(len(body) == entry['size'] and sha(body) == entry['sha256'],
            'literal closure iterator body differs from its pinned identity')
    a, d = entry['adapter_register'], entry['descriptor_register']
    selected = thunk.ALIASES[f'_call_via_r{a}']
    require(calls == {address+entry['call']: selected}, 'literal closure iterator call differs')
    require(len(ins) == entry['count'] and set(edges) == set(ins) and
            all(target in ins for targets in edges.values() for target in targets),
            'literal closure iterator must be one complete instruction graph')
    r0, r2, r4 = match.ARM_REG_R0, match.ARM_REG_R0+2, match.ARM_REG_R0+4
    raw = {site: int.from_bytes(item.bytes[:2], 'little') for site, item in ins.items()}
    preds = {site: set() for site in ins}
    for site, targets in edges.items():
        for target in targets: preds[target].add(site)
    site = address+entry['call']
    exits = {s for s, item in ins.items() if not edges[s]}
    # Entry: PUSH, then the two copies, as one straight-line prefix.
    require(ins[address].mnemonic == 'push' and edges[address] == (address+2,) and
            edges[address+2] == (address+4,) and preds[address+2] == {address} and preds[address+4] == {address+2} and
            raw[address+2] == 0x1C08 | a and raw[address+4] == 0x1C10 | d,
            'literal closure iterator entry copies differ')
    # The call's arguments are set by its only two graph predecessors.
    require(preds[site] == {site-2} and preds[site-2] == {site-4} and
            raw[site-4] == 0x1C20 and raw[site-2] == 0x1C01 | d << 3,
            'literal closure iterator call arguments differ')
    # Exit: every return is BX R0 reached only through POP {R0} after POP of the saved set.
    epilogue = set()
    for done in exits:
        require(ins[done].mnemonic == 'bx' and len(preds[done]) == 1, 'literal closure iterator exit differs')
        restore, = preds[done]
        require(ins[restore].mnemonic == 'pop' and len(preds[restore]) == 1, 'literal closure iterator exit differs')
        saved, = preds[restore]
        require(ins[saved].mnemonic == 'pop', 'literal closure iterator exit differs')
        epilogue |= {saved, restore, done}
    # Forward dataflow: may R0 have been overwritten on some path to here?
    written = {s: set(item.regs_access()[1]) for s, item in ins.items()}
    clobbered_in = {s: False for s in ins}
    changed = True
    while changed:
        changed = False
        for s in sorted(ins):
            value = any(clobbered_in[p] or r0 in written[p] for p in preds[s])
            if value != clobbered_in[s]:
                clobbered_in[s], changed = value, True
    reads = set()
    for s, item in ins.items():
        require(not item.mnemonic.startswith(('str', 'stm')) and (s == address or item.mnemonic != 'push'),
                'literal closure iterator must not store')
        if s not in (address+2, address+4) and s not in epilogue:
            require(not written[s] & {r0+a, r0+d}, 'literal closure iterator overwrites its adapter or descriptor')
        if item.mnemonic == 'ldr':
            mem = item.operands[1]
            require(mem.type == match.ARM_OP_MEM and not mem.mem.index and mem.mem.disp % 4 == 0 and
                    (mem.mem.base == r0 and not clobbered_in[s] or mem.mem.base == r4),
                    'literal closure iterator reads outside the list object and current node')
            reads.add(('list' if mem.mem.base == r0 else 'node', mem.mem.disp))
    require(reads == set(entry['reads']), 'literal closure iterator read set differs')
    # Does entry R2 (the root descriptor) survive to a return that skips the call?
    # Follow the straight-line prefix to the first conditional branch, then the
    # successor that reaches a return without another branch or the call.
    path, here = [], address
    while len(edges[here]) == 1 and here != site:
        path.append(here); here = edges[here][0]
    require(len(edges[here]) == 2, 'literal closure iterator requires an initial conditional exit')
    path.append(here)
    exit_paths = []
    for target in edges[here]:
        chain = []
        while target != site and len(edges[target]) == 1:
            chain.append(target); target = edges[target][0]
        if target in exits:
            exit_paths.append(chain+[target])
    require(len(exit_paths) == 1, 'literal closure iterator requires one direct empty exit')
    r2_survives = not any(r2 in written[s] for s in path+exit_paths[0])
    return selected, r2_survives


def framed_adapter_effects(body, address, getter_body, getter):
    """Interpret the complete pinned framed adapter and its leaf getter.

    Entry R0 is the current node and R1 the descriptor. The adapter saves R4
    and LR, reserves eight private bytes, passes their two word addresses to
    the getter, forwards private word zero and descriptor word zero to the
    descriptor word-four target through the R2 thunk, and returns that
    target's R0 through its saved LR. The getter may only read node words and
    store them into the adapter's private bytes.
    """
    require(type(body) is bytes and type(getter_body) is bytes and address in FRAMED_ADAPTERS and
            body == bytes.fromhex(FRAMED_ADAPTERS[address]['body']) and
            getter == FRAMED_ADAPTERS[address]['getter'] and
            getter_body == bytes.fromhex(FRAMED_ADAPTERS[address]['getter_body']),
            'pinned framed adapter or getter body differs')
    target = thunk.ALIASES['_call_via_r2']
    regs = {n: ('entry', n) for n in range(13)}
    regs[0], regs[1], regs[14] = ('node',), ('descriptor',), ('return',)
    sp, frame, local, getter_record, callback, reads, number = 0, {}, None, None, None, [], 0
    halfwords = struct.unpack(f'<{len(body)//2}H', body)
    while number < len(halfwords):
        raw, here = halfwords[number], address+2*number
        last = number == len(halfwords)-1
        require(raw & 0xFF00 != 0x4700 or last, 'framed adapter must return only at its end')
        if raw & 0xFE00 == 0xB400:  # PUSH {Rlist[,LR]}
            saved = [r for r in range(8) if raw >> r & 1] + ([14] if raw & 0x100 else [])
            sp -= 4*len(saved)
            for n, r in enumerate(saved): frame[sp+4*n] = regs[r]
        elif raw & 0xFF80 == 0xB080:  # SUB SP,#imm7*4
            require(local is None, 'framed adapter allows one private local area')
            sp -= 4*(raw & 0x7F); local = (sp, sp+4*(raw & 0x7F))
        elif raw & 0xFF80 == 0xB000:  # ADD SP,#imm7*4
            sp += 4*(raw & 0x7F)
        elif raw & 0xFFC0 == 0x1C00:  # ADDS Rd,Rn,#0
            regs[raw & 7] = regs[raw >> 3 & 7]
        elif raw & 0xF800 == 0xA800:  # ADD Rd,SP,#imm8*4
            regs[raw >> 8 & 7] = ('frame', sp+4*(raw & 0xFF))
        elif raw & 0xFFF8 == 0x4668:  # MOV Rd,SP
            regs[raw & 7] = ('frame', sp)
        elif raw & 0xF800 == 0x9800:  # LDR Rd,[SP,#imm8*4]
            offset = sp+4*(raw & 0xFF)
            require(local and local[0] <= offset < local[1] and offset in frame,
                    'framed adapter reads an unwritten or nonlocal frame word')
            regs[raw >> 8 & 7] = frame[offset]
        elif raw & 0xF800 == 0x6800:  # LDR Rd,[Rb,#imm5*4]
            offset = 4*(raw >> 6 & 31)
            require(regs[raw >> 3 & 7] == ('descriptor',) and offset in (0, 4),
                    'framed adapter reads outside the two descriptor words')
            regs[raw & 7] = ('descriptor-word', offset)
            reads.append(dict(site=here, offset=offset, width=4, base_register=raw >> 3 & 7))
        elif raw & 0xF800 == 0xF000 and number+1 < len(halfwords) and halfwords[number+1] & 0xF800 == 0xF800:
            low = halfwords[number+1]
            delta = ((raw & 0x7FF) << 12 | (low & 0x7FF) << 1)
            destination = here+4+(delta - (1 << 23) if delta & (1 << 22) else delta)
            if destination == getter and getter_record is None and callback is None:
                getter_record, returned = _framed_getter(getter_body, getter, regs, frame, local)
                for r in (0, 1, 2, 3, 12): regs[r] = returned[r]
            elif destination == target and getter_record is not None and callback is None:
                require(not any(regs[r][0] == 'frame' for r in (0, 1, 2, 3, 12)),
                        'framed adapter passes a private frame address to the callback')
                callback = dict(site=here, thunk=target, target=regs[2], arguments=[regs[0], regs[1]])
                for r in (1, 2, 3, 12): regs[r] = ('clobbered',)
                regs[0] = ('callback-result',)
            else:
                raise ValueError('framed adapter calls differ')
            regs[14] = ('clobbered',)
            number += 2; continue
        elif raw & 0xFE00 == 0xBC00:  # POP {Rlist} without PC
            require(not raw & 0x100, 'framed adapter must not pop PC')
            for r in [r for r in range(8) if raw >> r & 1]:
                regs[r] = frame[sp]; sp += 4
        elif raw & 0xFF87 == 0x4700 and last:  # BX Rm
            require(regs[raw >> 3 & 15] == ('return',), 'framed adapter must return through its saved LR')
            require(not any(regs[r][0] == 'frame' for r in (0, 1, 2, 3, 12)),
                    'framed adapter returns a private frame address')
        else:
            raise ValueError('unsupported framed adapter instruction')
        number += 1
    require(sp == 0 and local == (-16, -8) and regs[0] == ('callback-result',) and
            all(regs[n] == ('entry', n) for n in range(4, 12)), 'framed adapter return/frame differs')
    require(callback == dict(site=callback and callback['site'], thunk=target, target=('descriptor-word', 4),
            arguments=[('node-word', 4), ('descriptor-word', 0)]) and
            sorted(row['offset'] for row in reads) == [0, 4] and
            len({row['base_register'] for row in reads}) == 1, 'framed adapter effect relation differs')
    return dict(schema=FRAMED_SCHEMA, address=address, end=address+len(body), instructions=FRAMED_ADAPTERS[address]['count'],
        body_sha256=sha(body), descriptor_register=reads[0]['base_register'], descriptor_reads=reads,
        frame=dict(saved=['entry R4', 'entry LR'], local_bytes=8, local_offsets=[-16, -12],
                   established_by='pinned bytes and the interpreter, not the frame prover'),
        getter=getter_record,
        callback=dict(site=callback['site'], thunk=target,
            target='descriptor word at offset 4',
            arguments=['node word at offset 4, copied through private word -16', 'descriptor word at offset 0'],
            descriptor_address_passed_as_argument=False, result='unchanged callback R0'),
        private_frame_addresses_passed=['private word -16 to the getter in R1', 'private word -12 to the getter in R2'],
        all_paths_interpreted=True)


def _framed_getter(body, address, caller, frame, local):
    """Interpret the straight-line leaf getter on the adapter's symbolic state."""
    regs = {n: caller[n] for n in range(13)}
    regs[14] = ('getter-return',)
    reads, writes = [], []
    halfwords = struct.unpack(f'<{len(body)//2}H', body)
    for number, raw in enumerate(halfwords):
        here, last = address+2*number, number == len(halfwords)-1
        require((raw == 0x4770) == last, 'framed getter must be one linear block ending in BX LR')
        if raw == 0x4770:
            break
        rd, rb, offset = raw & 7, raw >> 3 & 7, 4*(raw >> 6 & 31)
        if raw & 0xF800 == 0x6800:
            require(regs[rb] == ('node',), 'framed getter reads outside the current node')
            regs[rd] = ('node-word', offset); reads.append(dict(site=here, base='current node', offset=offset, width=4))
        elif raw & 0xF800 == 0x6000:
            base = regs[rb]
            require(base[0] == 'frame' and local and local[0] <= base[1]+offset < local[1],
                    'framed getter store leaves the adapter private frame')
            require(regs[rd][0] == 'node-word', 'framed getter may store only node words')
            frame[base[1]+offset] = regs[rd]
            writes.append(dict(site=here, frame_offset=base[1]+offset, width=4, value=f'node word {regs[rd][1]}'))
        else:
            raise ValueError('unsupported framed getter instruction')
    require(all(regs[n] == caller[n] for n in range(4, 12)), 'framed getter must preserve R4-R11')
    require(sorted(row['frame_offset'] for row in writes) == [-16, -12] and len(writes) == 2 and
            frame.get(-16) == ('node-word', 4) and frame.get(-12) == ('node-word', 0),
            'framed getter effect relation differs')
    return dict(address=address, end=address+len(body), instructions=len(halfwords), body_sha256=sha(body),
        reads=reads, writes=writes, leaf=True, frame_bytes=0,
        relation='private word -16 becomes node word 4 and private word -12 becomes node word 0; nothing else is written'), regs


class _LiteralContextRead(match.BufferCallProof):
    def __init__(self, rom, mapping, site, target, form):
        super().__init__(rom, mapping, stack_arguments=True)
        self.site, self.call_target, self.form = site, target, form
        self.trailing_site = self.trailing_target = None
        self.observed = []

    def check_call(self, address, aliases, stack, slots=None, *, site=None, words=None, **kwargs):
        r2 = match.ARM_REG_R0+2
        form = FORMS[self.form]
        if 'trailing' in form and site == self.trailing_site and address == self.trailing_target:
            # The descriptor is complete and dead here: nothing may point at it.
            if aliases or slots or words or len(stack) != form['stack_words']:
                raise ValueError('literal closure trailing call carries the descriptor')
            self.observed.append(dict(site=site, target=address, descriptor_alias_passed=False))
            return {}
        expected = {} if form['state'] is None else {form['descriptor']: form['state']}
        if site != self.site or address != self.call_target or (slots or {}) != expected or words or \
                aliases != {r2: form['descriptor']} or len(stack) != form['stack_words']:
            raise ValueError('literal closure call differs from its complete initialized root context')
        self.access(form['descriptor'], 4, stack)
        self.access(form['descriptor']+4, 4, stack)
        if form.get('flag'):
            # The interpreted callback tree reads flag bytes 0 and 1 only.
            self.access(form['state'], 1, stack)
            self.access(form['state']+1, 1, stack)
        elif form['state'] is not None:
            self.access(form['state'], 4, stack)
            self.access(form['state']+4, 4, stack)
        self.observed.append(dict(site=site, target=address, descriptor_offset=form['descriptor'], width=8,
                                  pointer_slots=[[offset, value] for offset, value in sorted(expected.items())]))
        return {}


def prove(data, address, rom, mapping, index, *, selector):
    require(type(selector) is str and selector == SELECTOR and type(address) is int and
            all(type(v) is bytes for v in (data, rom, mapping, index)),
            'literal closure requires its exact explicit policy and immutable inputs')
    name = form_of(data); form = FORMS[name]
    body, ins, edges, calls, partition = complete(address, form['size'], form['count'], rom, mapping, index)
    r0, r1, r2 = match.ARM_REG_R0, match.ARM_REG_R0+1, match.ARM_REG_R0+2
    iterator = calls.get(address+form['call'])
    trailing = form.get('trailing')
    require(data == body and len(calls) == (2 if trailing else 1) and iterator in ITERATORS and
            (not trailing or set(calls) == {address+form['call'], address+trailing['call']}) and
            partition['literal_and_table_bytes'] == 8 and
            partition['alignment_bytes'] == form.get('alignment_bytes', 0) and
            sorted(row['address']-address for row in partition['words']) == [form['callback'], form['adapter']],
            'literal closure requires the exact iterator call and two complete literals')
    source = ins[address+form['owner']]
    base = r0+form['owner_base']
    require(len(source.operands) == 2 and source.operands[1].type == match.ARM_OP_MEM and
            adapter.load(source, r0, base, source.operands[1].mem.disp) and
            source.operands[1].mem.disp >= 0 and not source.operands[1].mem.disp % 4,
            'literal closure requires an aligned incoming object word load')
    if trailing:
        # Same halfword, so the trailing argument is the same owner word, read again.
        require(data[trailing['reload']:trailing['reload']+2] == data[form['owner']:form['owner']+2],
                'literal closure trailing call requires the same owner word reload')
    callback_value, adapter_value = (struct.unpack_from('<I', body, form[key])[0] for key in ('callback', 'adapter'))
    require(callback_value % 2 == 1 and adapter_value % 2 == 1,
            'literal closure literals must be typed odd Thumb pointers')
    entries = json.loads(mapping)
    callback = match.function_address_target(f'func_{callback_value&~1:08X}', entries, address, len(data), len(rom))
    adapter_address = match.function_address_target(f'func_{adapter_value&~1:08X}', entries, address, len(data), len(rom))
    shape = ITERATORS[iterator]
    worker, wi, we, wc, wp = complete(iterator, shape['size'], shape['count'], rom, mapping, index)
    require(not wp['literal_and_table_bytes'] and not wp['alignment_bytes'],
            'literal closure requires the complete read-only node iterator')
    selected, r2_survives = iterator_structure(worker, iterator, shape, wi, we, wc)
    selected_name = f"_call_via_r{shape['adapter_register']}"
    index_entries, rows = indices(mapping, index)
    if adapter_address in FRAMED_ADAPTERS:
        pinned = FRAMED_ADAPTERS[adapter_address]
        getter = pinned['getter']
        adapter_data, ai, ae, ac, ap = complete(adapter_address, len(pinned['body'])//2, pinned['count'],
                                                rom, mapping, index)
        gdata, gi, ge, gc, gp = complete(getter, len(pinned['getter_body'])//2, pinned['getter_count'],
                                         rom, mapping, index)
        require(not ap['literal_and_table_bytes'] and not ap['alignment_bytes'] and not gc and
                not gp['literal_and_table_bytes'] and not gp['alignment_bytes'] and
                ac == {adapter_address+10: getter, adapter_address+20: thunk.ALIASES['_call_via_r2']},
                'literal closure requires its complete pinned framed adapter')
        # The existing two-output inventory independently authenticates the
        # same adapter and getter; the interpreter adds the effect relation.
        import two_output_callback_adapter_inventory as two_output
        effects = framed_adapter_effects(adapter_data, adapter_address, gdata, getter)
        inventory = two_output.verify(adapter_address, getter, rom, mapping, index, selector=two_output.SELECTOR)
        adapter_proof = dict(effects, partition=ap, inventory=inventory, explicit_conditions=[
                'Each node passed to the adapter is nonnull and its words 0 and 4 are aligned, live, initialized and readable.',
                'The adapter\'s private eight-byte local area and saved words form a valid frame that does not wrap or alias the node, the descriptor, callback-visible memory or code; the getter\'s two out-pointers address only that local area, as interpreted, and no frame address is retained or returned.',
                'The getter and the descriptor target are compatible returning Thumb code; the target preserves R4-R11 and SP, the private frame and continuation code.',
                'Loaded input words carry no tracked private-frame or saved-return provenance; ordinary memory noninterference remains a premise.'])
        adapter_shape = 'framed-two-output'
        getter_reads = [4, 0]
    else:
        adapter_data = rom[adapter_address-match.ROM_BASE:adapter_address-match.ROM_BASE+22]
        refinement = owner.refine(adapter_data, adapter_address, mapping)
        ai, ae, ab, ac, aw = graph.graph(adapter_data, adapter_address, refinement)
        require(not ab and not aw and len(ac) == 2 and adapter_address+4 in ac,
                'literal closure requires its complete two-call scalar adapter')
        getter = ac[adapter_address+4]
        adapter_proof = adapter.verify(adapter_address, getter, rom, mapping, index, selector=adapter.SELECTOR)
        adapter_shape = 'scalar-inventory'
        getter_reads = [0]
    for thunk_name in (selected_name, '_call_via_r2'):
        target = thunk.ALIASES[thunk_name]
        tdata = rom[target-match.ROM_BASE:target-match.ROM_BASE+2]
        owner.validate_span(tdata, target, rom, mapping, index)
        require(span_record(target, target+2, index_entries, rows, rom)['instrs'] == 1 and not any(
                int(row['rom'], 16) < target+4 and int(row['end'], 16) > target+2 for row in index_entries),
                'literal closure call thunk requires separate indexed padding')
    canonical, = thunk.dependencies([selected_name], rom)
    adapter_canonical, = thunk.dependencies(['_call_via_r2'], rom)
    addresses = [address, iterator, adapter_address, getter, callback, selected, thunk.ALIASES['_call_via_r2']]
    trailing_record = None
    if trailing:
        follower = calls[address+trailing['call']]
        match.function_address_target(f'func_{follower:08X}', entries, address, len(data), len(rom))
        addresses.append(follower)
        end = next((row['end'] for row in index_entries if int(row['rom'], 16) == follower), None)
        require(end is not None, 'literal closure trailing callee requires its complete indexed span')
        entry = span_record(follower, int(end, 16), index_entries, rows, rom)
        fbody = rom[follower-match.ROM_BASE:int(entry['end'], 16)-match.ROM_BASE]
        owner.validate_span(fbody, follower, rom, mapping, index)
        trailing_record = dict(site=address+trailing['call'], target=follower, end=int(entry['end'], 16),
            instructions=entry['instrs'], body_sha256=sha(fbody), effects='opaque',
            arguments=[dict(register=0, source='owner word reloaded from root entry R0',
                            offset=source.operands[1].mem.disp, site=address+trailing['reload'])],
            entry_r2_overwritten_at=entry_r2_killed(rom, follower, int(entry['end'], 16)),
            descriptor_alias_passed=False)
    require(len(set(addresses)) == len(addresses), 'literal closure requires distinct complete dependency owners')
    flag_aliases = []
    if form['state'] is None:
        require(callback not in STATE_CALLBACKS, 'pinned state callback requires the private-state root form')
        require(callback not in FLAG_CALLBACKS, 'pinned flag callback requires the local-byte-flag root form')
        end = next((row['end'] for row in index_entries if int(row['rom'], 16) == callback), None)
        require(end is not None, 'literal closure callback requires its complete indexed span')
        entry = span_record(callback, int(end, 16), index_entries, rows, rom)
        cbody = rom[callback-match.ROM_BASE:int(entry['end'], 16)-match.ROM_BASE]
        callback_record = dict(address=callback, end=int(entry['end'], 16), instructions=entry['instrs'],
            body_sha256=sha(cbody), effects='opaque',
            arguments=['word loaded by getter from each node', form['word0']],
            private_provenance_passed=False)
    elif form.get('flag'):
        require(callback in FLAG_CALLBACKS and FLAG_CALLBACKS[callback]['form'] == name,
                'private flag requires its pinned flag callback')
        # Only the scalar adapter's flow (R1 from descriptor word zero, scratch
        # untouched between invocations) is what the flag records describe.
        require(adapter_shape == 'scalar-inventory', 'private flag requires the scalar adapter')
        # An alias left by one invocation may be live at the next one: iterate
        # the seeded scratch set until it is stable (it only grows within {R3, R12}).
        seeds = []
        while True:
            effects, flag_aliases = flag_callback_effects(callback, rom, mapping, index, seeds=seeds)
            flag_aliases = sorted(set(flag_aliases) | set(seeds))
            if flag_aliases == seeds:
                break
            seeds = flag_aliases
        # Outside the interpreted tree nothing may read a register that may still
        # hold the flag address: the iterator, adapter and getter run between
        # invocations, and the root continuation after the last.
        gend = next((row['end'] for row in index_entries if int(row['rom'], 16) == getter), None)
        require(gend is not None, 'literal closure getter requires its complete indexed span')
        gentry = span_record(getter, int(gend, 16), index_entries, rows, rom)
        _, gins, gedges, gcalls, _ = complete(getter, int(gend, 16)-getter, gentry['instrs'], rom, mapping, index)
        for gins_, gedges_, gcalls_, start in ((wi, we, wc, iterator), (ai, ae, ac, adapter_address),
                                              (gins, gedges, gcalls, getter), (ins, edges, calls, address+form['call'])):
            scratch_aliases_unread(gins_, gedges_, gcalls_, start, flag_aliases)
        callback_record = dict(effects, arguments=['word loaded by getter from each node', form['word0']],
            private_provenance_passed=True, flag_aliases_on_return=flag_aliases,
            alias_erasure='The interpreted tree never stores or pushes the flag address and leaves it only in the listed scratch registers, which the iterator, adapter, getter and root continuation never read before overwriting. No flag address is stored outside the root\'s own expired frame.')
    else:
        require(callback in STATE_CALLBACKS and STATE_CALLBACKS[callback]['form'] == name and
                adapter_data[-4:] == bytes.fromhex('02bc0847'),
                'private state requires a pinned state callback and adapter return through R1')
        require(adapter_proof['descriptor_register'] == 4,
                'private state requires the adapter descriptor in R4')
        count = STATE_CALLBACKS[callback]['count']
        size = len(bytes.fromhex(STATE_CALLBACKS[callback]['body']))
        cbody, _, _, ccalls, cpartition = complete(callback, size, count, rom, mapping, index)
        require(not ccalls and not cpartition['literal_and_table_bytes'], 'state callback must be a code-only leaf')
        callback_record = dict(state_callback_effects(cbody, callback), partition=cpartition,
            arguments=['word loaded by getter from each node', form['word0']],
            private_provenance_passed=True,
            alias_erasure='The adapter restores R4 and overwrites R1 with its saved return before BX R1; the iterator overwrites R0/R1 before any later callback. No private state address is stored outside the root\'s own expired frame.')
    worker_frame = frame.prove_frame(wi, we, iterator, {}, wc, call_preservation={site: PRESERVED for site in wc})
    context = _LiteralContextRead(rom, mapping, address+form['call'], iterator, name)
    if trailing:
        context.trailing_site, context.trailing_target = trailing_record['site'], trailing_record['target']
    verified = match.verify_leaf_instructions(data, address, True, calls, buffer_proof=context)
    require({item.address for item in verified} == set(ins) and context.observed,
            'literal closure requires exact native root and descriptor access evidence')
    stores = ([dict(offset=form['state'], width=1, source='constant zero'),
               dict(offset=form['descriptor'], source='address of private flag byte'),
               dict(offset=form['descriptor']+4, source='typed callback literal')]
              if form.get('flag') else
              [dict(offset=form['state']+4*n, source=value)
               for n, value in enumerate(form.get('state_sources', ['constant zero', 'root entry R1']))] +
              [dict(offset=form['descriptor'], source='address of private state'),
               dict(offset=form['descriptor']+4, source='typed callback literal')]
              if form['state'] is not None else
              [dict(offset=form['descriptor'], source=form['word0']),
               dict(offset=form['descriptor']+4, source='typed callback literal')])
    lifted = 'Loaded input words carry no tracked private-frame or saved-return provenance; ordinary memory noninterference remains a premise.'
    require(lifted in adapter_proof['explicit_conditions'], 'literal closure adapter premise differs')
    private = 'flag' if form.get('flag') else 'state'
    conditions = [condition for condition in adapter_proof['explicit_conditions']
                  if form['state'] is None or condition != lifted] + ([] if form['state'] is None else [
        f'The getter word carries no tracked private-frame or saved-return provenance. Descriptor word zero is the private {private} address: the exact adapter loads it and passes it to the pinned callback in R1 without dereferencing it. The no-private-provenance adapter premise is replaced for that word by the interpreted callback {"tree " if form.get("flag") else ""}effects, not asserted satisfied; ordinary memory noninterference remains a premise.']) + [
        'Every reached list/node load is aligned, live, initialized and physically readable at its recorded width; null is tested only as a word value.',
        'All private root, iterator, adapter and callback frames and continuation code satisfy compatible returning ABI validity and noninterference; external values carry no private-frame/saved-return provenance.']
    if trailing:
        conditions.append('The trailing callee is compatible returning Thumb code preserving R4-R11 and SP, the private frame and continuation code; its identity is pinned and it provably overwrites entry R2 before reading it, but its effects are not interpreted. Its R1 is a code or iterator value (the adapter literal on the empty path, otherwise the adapter\'s return into the iterator); its R3 and R12 are callback scratch or the root caller\'s entry values, assumed to carry no private-frame provenance while the root frame is live.')
    if form['state'] is None:
        conditions.append('The typed literal callback is compatible returning Thumb code preserving R4-R11 and SP, the private frames and continuation code; its identity is pinned but its effects are not interpreted.')
    elif form.get('flag'):
        conditions += [
            'The private flag word is reachable only through descriptor word zero and the scratch registers the interpreted callback tree leaves it in; the iterator, getter and adapter pass it to the pinned callback without dereferencing it, and no ordinary call or external access reads or writes the flag word or descriptor.',
            'Every external load in the interpreted callback tree is aligned, live, initialized and physically readable at its width, and loads no private-frame or saved-return address.']
    else:
        conditions += [
            'The private state is reachable only through descriptor word zero; the iterator, getter and adapter pass it to the pinned callback without dereferencing it, and no ordinary call or external access reads or writes the state or descriptor.',
            STATE_CALLBACKS[callback]['condition']]
    proof = dict(schema=SCHEMA, instructions=len(ins),
        calls=[[site-address, f'func_{target:08X}'] for site, target in sorted(calls.items())], runtime_calls=[], partition=partition,
        literal_callback_closure=dict(schema=SELECTOR, form=name,
            root_frame=dict(saved=form.get('saved', ['entry LR']), local_bytes=form['frame_bytes'],
                            established_by='exact byte template, not the frame prover',
                            template_sha256=sha(form['code'].encode())),
            root_descriptor=dict(offset=form['descriptor'], width=8, initialized_words=stores,
                actual_buffer_checks=context.observed),
            private_state=None if form['state'] is None else dict(offset=form['state'], width=1,
                initialized=[dict(offset=0, width=1, value=0)], uninitialized_bytes=[1, 2, 3],
                indeterminate_reads=[dict(site=row[0], offset=row[1], width=1,
                    effect='the root never initializes this byte; its value only selects among interpreted paths')
                    for row in callback_record['flag_reads'] if row[1]],
                result=dict(site=address+form['call']+6, offset=0, width=1, register=0,
                    relation='1 if flag byte 0 is nonzero after the iterator returns, otherwise 0; flag byte 0 is zero plus one per interpreted increment, modulo 2**8'))
                if form.get('flag') else
                dict(offset=form['state'], width=8,
                initialized=[dict(offset=0, entry_register=1), dict(offset=4, entry_register=2)], result=None)
                if 'state_sources' in form else dict(offset=form['state'], width=8,
                initialized=[dict(offset=0, value=0), dict(offset=4, entry_register=1)],
                result=dict(site=address+form['call']+4, offset=0, width=4, register=0,
                    relation='zero plus one per returning callback invocation, modulo 2**32')),
            callback=callback_record,
            iterator=dict(address=iterator, end=iterator+shape['size'], instructions=shape['count'],
                body_sha256=sha(worker), pinned_sha256=shape['sha256'], kind=shape['kind'],
                adapter_register=shape['adapter_register'], descriptor_register=shape['descriptor_register'],
                call_site=iterator+shape['call'], partition=wp, frame=worker_frame, thunk=canonical,
                reads=[dict(base='list object' if base == 'list' else 'current node', offset=offset, width=4)
                       for base, offset in shape['reads']], stores=[],
                loop_invariant=shape['loop_invariant'],
                iteration_bound_assumed=False, termination_proved=False),
            adapter_shape=adapter_shape,
            adapter=adapter_proof,
            adapter_thunk=adapter_canonical,
            external_read_obligations=[dict(base='root entry R0' if name != 'entry-object' else 'word at root entry R0+128',
                    offset=source.operands[1].mem.disp, width=4)] +
                [dict(base='loaded list object' if base == 'list' else 'each node reached by the iterator',
                      offset=offset, width=4) for base, offset in shape['reads']] +
                [dict(base='each nonnull current node passed to getter', offset=offset, width=4) for offset in getter_reads] +
                ([dict(base='root entry R0', offset=128, width=4)] if name == 'entry-object' else []) +
                ([dict(base='root entry R0, reloaded after the iterator returns', offset=source.operands[1].mem.disp,
                       width=4)] if trailing else []),
            outward_expired_aliases=([dict(register=2, origin='root descriptor on the empty-list path',
                accessible_after_return=False, observed_by_root_continuation=False)]
                if r2_survives else []) + [dict(register=n, origin='private flag address left by the interpreted callback tree',
                accessible_after_return=False, observed_by_root_continuation=False) for n in flag_aliases],
            explicit_conditions=conditions,
            source_sha256={**{Path(module.__file__).name: sha(Path(module.__file__).read_bytes())
                for module in (match, owner, graph, thunk, frame, adapter)},
                Path(__file__).name: sha(Path(__file__).read_bytes())},
            physical_memory_permission=False, numeric_nonalias_proved=False,
            actual_callback_ABI_established=False, termination_proved=False))
    if trailing:
        record = proof['literal_callback_closure']
        record['trailing_call'] = trailing_record
        # The empty-path R2 alias does not expire here: it reaches the live
        # trailing callee, which overwrites it before any read.
        record['live_aliases_to_trailing_callee'] = [dict(register=alias['register'], origin=alias['origin'],
            observed_by_trailing_callee=False, overwritten_at=trailing_record['entry_r2_overwritten_at'])
            for alias in record['outward_expired_aliases']]
        record['outward_expired_aliases'] = []
    return proof
