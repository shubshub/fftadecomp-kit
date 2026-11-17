"""Three bounded outputs through an actual named-read leaf and its wrapper.

The existing two named halfword-read origin proof is reused unchanged. A
separate saved-origin transfer retains the real R3 <- entryR8 return. All
output bounds and callback ABI/noninterference conditions remain explicit.
"""
import hashlib
from pathlib import Path

import match
import named_data_buffer_profile as named
import nested_formal_output_buffer_profile as nested
import local_long_branch_profile as frame

SELECTOR = 'bounded-buffer-named-three-halfword-output-v1'
SCHEMA = 'elf-symbol-thumb-bounded-buffer-named-three-halfword-output-v1'
CONTROL_FLOW = 'complete Thumb owner with three bounded named-state halfword outputs and exact entryR8 return alias'
MAX_DEPENDENCIES = 10
WRAPPER = (0x080DBDA0, 40, '56c13623d40ad18ce969560166b471e986a2e1054499bd75f34b60e7f495906d')
LEAF = (0x0801C918, 72, '691a3b26d9786d76f850b2cab1e5999bac35af0524a17a4f82f8f0f7ea379fcf')


def prove_leaf_origins(instructions, edges, address, data, partition, objects):
    import ordinary_two_output_callees_inventory as named_leaf  # circular at module level
    effects = named_leaf.prove_named_origins(instructions, edges, address, data,
        partition, objects, named_leaf.named_policy())
    restored = frame.prove_frame(instructions, edges, address, {}, {},
        entry_stack_policy=named_leaf.parent.ENTRY_POLICY)
    # The effect checker proves every operation's memory/pointer origin. This
    # complementary transfer records saved entry values that it intentionally
    # leaves out of its public output facts. No incoming scalar value is assumed.
    values = {match.ARM_REG_R0+n: ('entry', n) for n in range(13)}
    values[match.ARM_REG_LR] = ('entry-lr',)
    for n in range(3): values[match.ARM_REG_R0+n] = ('scalar',)
    values[match.ARM_REG_R0+3] = ('formal', 3)
    stack = []
    for site in sorted(instructions):
        item=instructions[site];raw=bytes(item.bytes);code=int.from_bytes(raw,'little')
        if len(raw)!=2 or raw!=data[site-address:site-address+2]:
            raise ValueError('named leaf return transfer requires exact narrow bytes')
        if code & 0xFE00 in (0xB400,0xBC00):
            push=code & 0xFE00==0xB400
            registers=[match.ARM_REG_R0+n for n in range(8)if code & (1<<n)]
            if code & 0x100:registers.append(match.ARM_REG_LR if push else match.ARM_REG_PC)
            if push:stack[:0]=[values.get(r,('scalar',))for r in registers]
            else:
                if len(registers)>len(stack):raise ValueError('named leaf saved-origin underflow')
                for r,v in zip(registers,stack):values[r]=v
                del stack[:len(registers)]
        elif code & 0xFC00==0x4400 and (code>>8)&3==2:
            destination=match.ARM_REG_R0+(code&7)+((code>>4)&8)
            source=match.ARM_REG_R0+((code>>3)&15)
            values[destination]=values.get(source,('scalar',))
        else:
            for r in item.regs_access()[1]:values[r]=('scalar',)
    origins=[[n,values[match.ARM_REG_R0+n][1]]for n in (0,1,2,3,12)
             if values.get(match.ARM_REG_R0+n,('scalar',))[0]=='entry']
    if stack or origins!=[[3,8],[12,12]]:
        raise ValueError('named leaf actual entryR8/R12 return origins differ')
    writes=[]
    for row in effects['store_events']:
        formal=row[1];origin=['formal',3] if formal==3 else ['incoming',4*(formal-4)]
        writes.append([row[0],origin,row[2],row[3]])
    return dict(schema=SCHEMA,formal_writes=writes,return_entry_origins=origins,
        named_effects=effects,frame=restored,physical_nonalias_claim=False,
        numeric_equivalence_claim=False)


def prove_wrapper_origins(instructions, edges, calls, address, data, child):
    """Compose the fresh leaf effect fact with exact wrapper value transport."""
    if child['schema'] != SCHEMA or child['return_entry_origins'] != [[3, 8], [12, 12]] or \
            [r[1:] for r in child['formal_writes']] != [[['formal', 3], 0, 2]]*2 + [[['incoming', 0], 0, 2]]*2 + [[['incoming', 4], 0, 2]]:
        raise ValueError('wrapper requires its exact fresh three-output leaf and retained entryR8 origin')
    values = {n: ('entry', n) for n in range(13)}
    values.update({0: ('object', 0), 1: ('formal', 1), 2: ('formal', 2), 3: ('formal', 3), 14: ('entry-lr',)})
    scalar = ('scalar',)
    constants, stack = {}, []
    reads, stores, transfers, writes = [], [], [], []
    ordered = sorted(instructions)
    if not ordered or ordered[0] != address or set(edges) != set(instructions) or len(calls) != 1:
        raise ValueError('wrapper requires its complete one-call straight-line CFG')

    def assign(n, value=scalar, constant=None):
        values[n] = value
        constants.pop(n, None)
        if constant is not None:
            constants[n] = constant

    for position, site in enumerate(ordered):
        item = instructions[site]
        raw, ops = bytes(item.bytes), item.operands
        code = int.from_bytes(raw, 'little')
        terminal = position + 1 == len(ordered)
        if item.size != len(raw) or raw != data[site-address:site-address+len(raw)] or \
                tuple(edges[site]) != (() if terminal else (site + len(raw),)) or \
                not terminal and ordered[position + 1] != site + len(raw):
            raise ValueError('wrapper instruction bytes or complete edges differ')
        if site in calls:
            if len(raw) != 4 or item.mnemonic != 'bl' or len(ops) != 1 or \
                    ops[0].type != match.ARM_OP_IMM or calls[site] != LEAF[0] or ops[0].imm != LEAF[0] or \
                    [values[n] for n in range(4)] != [scalar, scalar, scalar, ('formal', 1)] or \
                    len(stack) < 2 or stack[:2] != [('local', ('formal', 2)), ('local', ('formal', 3))]:
                raise ValueError('nested call lacks its exact scalar/formal/outgoing-word transport')
            writes.extend([[1, 0, 2], [2, 0, 2], [3, 0, 2]])
            transfers.append(dict(site=site, target=LEAF[0], formal3=['formal', 1],
                                  incoming_word0=['formal', 2], incoming_word1=['formal', 3], incoming_words_initialized=True))
            for n in range(3):
                assign(n)
            assign(3, values[8])
            assign(14)
            # The fresh leaf restores r4-r11/SP, returns entryR8 in R3 and never writes
            # r12. Its entry LR is its own call continuation, not wrapper LR.
            continue
        if len(raw) != 2:
            raise ValueError('wrapper excludes non-call wide instructions')
        if code & 0xFE00 in (0xB400, 0xBC00):
            push = code & 0xFE00 == 0xB400
            numbers = [n for n in range(8) if code & (1 << n)]
            if code & 0x100:
                numbers.append(14 if push else 15)
            if push:
                if any(values[n][0] not in ('entry', 'entry-lr') for n in numbers):
                    raise ValueError('wrapper cannot push an object/formal pointer')
                stack[:0] = [('saved', values[n]) for n in numbers]
            else:
                if 15 in numbers or len(numbers) > len(stack) or any(
                        row[0] != 'saved' for row in stack[:len(numbers)]):
                    raise ValueError('wrapper pop leaves its saved frame')
                for n, row in zip(numbers, stack):
                    assign(n, row[1])
                del stack[:len(numbers)]
        elif code & 0xFF00 == 0xB000:
            count = code & 0x7F
            if count != 2:
                raise ValueError('wrapper requires its two private outgoing pointer words')
            if code & 0x80:
                stack[:0] = [('local', None)] * 2
            else:
                if len(stack) < 2 or any(row[0] != 'local' for row in stack[:2]):
                    raise ValueError('wrapper deallocation overlaps saved frame')
                del stack[:2]
        elif code & 0xFE00 == 0x1C00 and (code >> 6) & 7 == 0:
            source, destination = (code >> 3) & 7, code & 7
            assign(destination, values[source], constants.get(source))
        elif code & 0xF800 == 0x2000:
            assign((code >> 8) & 7, constant=code & 255)
        elif code & 0xFE00 == 0x5E00:
            destination, base, index = code & 7, (code >> 3) & 7, (code >> 6) & 7
            offset = constants.get(index)
            if values[base] != ('object', 0) or values[index] != scalar or offset not in (8, 10, 12):
                raise ValueError('wrapper nonlocal read exceeds its exact conditional input offsets')
            reads.append([site, 0, offset, 2])
            assign(destination)
        elif code & 0xF800 == 0x9000:
            source, offset = (code >> 8) & 7, 4 * (code & 255)
            if offset not in (0, 4) or len(stack) <= offset//4 or stack[offset//4][0] != 'local' or values[source] != ('formal', 2+offset//4):
                raise ValueError('wrapper pointer store leaves its two private outgoing words')
            stack[offset//4] = ('local', values[source])
            stores.append([site, offset, ['formal', 2+offset//4], 4])
        elif code & 0xFF87 == 0x4700:
            source = (code >> 3) & 15
            if not terminal or values.get(source) != ('entry-lr',) or stack or any(
                    values[n] != ('entry', n) for n in range(4, 12)):
                raise ValueError('wrapper return does not restore entry frame/control origins')
        else:
            raise ValueError('unsupported wrapper value operation')
        if terminal and code & 0xFF87 != 0x4700:
            raise ValueError('wrapper requires its authenticated terminal BX')
    if [r[1:] for r in reads] != [[0, 8, 2], [0, 10, 2], [0, 12, 2]] or \
            len(stores) != 2 or len(transfers) != 1 or writes != [[1, 0, 2], [2, 0, 2], [3, 0, 2]] or \
            values[3] != ('entry', 8) or any(v[0] in ('formal', 'object') for n, v in values.items() if n != 3):
        raise ValueError('wrapper observed reads, writes or residual origins differ')
    return dict(nonlocal_input_reads=reads, outgoing_pointer_stores=stores,
        child_argument_transport=transfers, formal_writes=writes,
        return_entry_origins=[[n, v[1]] for n, v in sorted(values.items())
                              if n in (0, 1, 2, 3, 12) and v[0] == 'entry'],
        preserved='r4-r11,sp,entry-lr',
        nonlocal_input_premise='conditional: arg0 halfwords at offsets8/10/12 are readable; loaded values unknown; no physical nonalias claim')


class NamedThreeOutputBufferProof(nested.NestedOutputBufferProof):
    dependency_budget = MAX_DEPENDENCIES

    def _prove(self):
        import ordinary_two_output_callees_inventory as named_leaf  # circular at module level
        if self._native is not None:
            return self._native
        raw, ins, edges, calls, partition = self._body(LEAF)
        if calls:
            raise ValueError('three-output leaf must be call-free')
        leaf = prove_leaf_origins(ins, edges, LEAF[0], raw, partition, self.objects)
        leaf_record = dict(address=LEAF[0], end=LEAF[0]+len(raw), bytes=len(raw),
            body_sha256=hashlib.sha256(raw).hexdigest(), structure=dict(
                kind=SCHEMA, instructions=len(ins), partition=partition, effects=leaf), **self.identities)
        self.dependencies[LEAF[0]] = raw
        self.records[LEAF[0]] = leaf_record
        raw, ins, edges, calls, partition = self._body(WRAPPER)
        wrapper = prove_wrapper_origins(ins, edges, calls, WRAPPER[0], raw, leaf)
        self.dependencies[WRAPPER[0]] = raw
        self.records[WRAPPER[0]] = dict(address=WRAPPER[0], end=WRAPPER[0]+len(raw), bytes=len(raw),
            body_sha256=hashlib.sha256(raw).hexdigest(), structure=dict(
                kind=SCHEMA, instructions=len(ins), partition=partition, effects=wrapper), **self.identities)
        self._native = dict(leaf=leaf_record, wrapper=self.records[WRAPPER[0]],
            producer_sha256={Path(module.__file__).name: hashlib.sha256(Path(module.__file__).read_bytes()).hexdigest()
                for module in (named, nested, named_leaf, named_leaf.parent, frame, __import__(__name__))})
        return self._native

    def check_call(self, address, aliases, stack, slots=None, *, constants=None, site=None, words=None):
        if address != WRAPPER[0]:
            return named.DiscardedReturnScratchProof.check_call(self, address, aliases, stack,
                slots, constants=constants, site=site, words=words)
        proof = self._prove()
        r0 = match.ARM_REG_R0
        if type(site) is not int or site % 2 or slots or words or r0 in aliases or \
                match.ARM_REG_LR in aliases or not {r0+1, r0+2, r0+3} <= set(aliases):
            raise ValueError('three-output caller requires three local outputs, nonlocal arg0 and no pointer slots')
        writes = []
        for formal in (1, 2, 3):
            offset = aliases[r0+formal]
            self.access(offset, 2, stack)
            writes.append([offset, 2])
        result = {}
        for destination, source in proof['wrapper']['structure']['effects']['return_entry_origins']:
            if r0+source in aliases:
                offset = aliases[r0+source]
                self.validate_pointer_value(offset, stack)
                result[r0+destination] = offset
        self._calls.append(dict(site=site, target=address, writes_entry_SP_offsets=writes,
            return_aliases=[[n-r0, o] for n, o in sorted(result.items())],
            helper_frames='fresh saved/local words below callSP; outputs in live caller locals',
            physical_nonalias_claim=False))
        return result

    def nested_manifest(self):
        import ordinary_two_output_callees_inventory as named_leaf  # circular at module level
        if not self._calls or self._native is None:
            raise ValueError('three-output profile requires an actual bounded caller composition')
        return dict(schema=SCHEMA, native_helpers=self._native, calls=self._calls,
                    named_read_policy=named_leaf.named_policy(), physical_nonalias_claim=False)
