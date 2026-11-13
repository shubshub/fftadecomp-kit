"""Bounded local outputs through a private outgoing pointer word and a leaf."""
import hashlib
from pathlib import Path

import match
import owner_graph_profile as graph
import named_data_buffer_profile as named
import formal_entry_word_halfword_effects as effects

SELECTOR = 'bounded-buffer-nested-halfword-output-v1'
SCHEMA = 'elf-symbol-thumb-bounded-buffer-nested-halfword-output-v1'
CONTROL_FLOW = 'complete Thumb owner with bounded nested halfword outputs and exact return entry aliases'
SELECTIVE_SELECTOR = 'bounded-buffer-nested-halfword-output-selective-scratch-v1'
SELECTIVE_SCHEMA = 'elf-symbol-thumb-bounded-buffer-nested-halfword-output-selective-scratch-v1'
SELECTIVE_CONTROL_FLOW = ('complete Thumb owner with bounded nested halfword outputs, exact return entry aliases '
                          'and selectively retained observed R2/R3 scratch aliases')
SELECTORS = (SELECTOR, SELECTIVE_SELECTOR)
SCHEMAS = {SELECTOR: SCHEMA, SELECTIVE_SELECTOR: SELECTIVE_SCHEMA}
CONTROL_FLOWS = {SELECTOR: CONTROL_FLOW, SELECTIVE_SELECTOR: SELECTIVE_CONTROL_FLOW}
SELECTOR_BY_SCHEMA = {schema: selector for selector, schema in SCHEMAS.items()}
MAX_DEPENDENCIES = 10
WRAPPER = (0x080DBDC8, 36, 'eb5caf776705b40cad641d5fa4cdcb434daf87ef4104d1d0905737470b3b8e22')
LEAF = (0x0801C984, 108, '47eb591d35b6ba7c424b639d7ce66e979b48c2c95441cd621ea2869070c596ee')


def prove_wrapper_origins(instructions, edges, calls, address, data, child):
    """Compose the fresh leaf effect fact with exact wrapper value transport."""
    if child['schema'] != effects.SCHEMA or child['return_entry_origins'] != [[3, 8]] or \
            [r[1:] for r in child['formal_writes']] != [[['formal', 3], 0, 2], [['incoming', 0], 0, 2]]:
        raise ValueError('wrapper requires its exact fresh two-output leaf and retained entryR8 alias')
    values = {n: ('entry', n) for n in range(13)}
    values.update({0: ('object', 0), 1: ('formal', 1), 2: ('formal', 2), 14: ('entry-lr',)})
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
                    not stack or stack[0] != ('local', ('formal', 2)):
                raise ValueError('nested call lacks its exact scalar/formal/outgoing-word transport')
            writes.extend([[1, 0, 2], [2, 0, 2]])
            transfers.append(dict(site=site, target=LEAF[0], formal3=['formal', 1],
                                  incoming_word0=['formal', 2], incoming_word_initialized=True))
            for n in range(3):
                assign(n)
            assign(3, values[8])
            # The fresh leaf origin proof restores r4-r11/SP and never writes
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
            if count != 1:
                raise ValueError('wrapper requires its one private outgoing pointer word')
            if code & 0x80:
                stack[:0] = [('local', None)]
            else:
                if not stack or stack[0][0] != 'local':
                    raise ValueError('wrapper deallocation overlaps saved frame')
                del stack[:1]
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
            if offset or not stack or stack[0][0] != 'local' or values[source] != ('formal', 2):
                raise ValueError('wrapper pointer store leaves its one private outgoing word')
            stack[0] = ('local', values[source])
            stores.append([site, 0, ['formal', 2], 4])
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
            len(stores) != 1 or len(transfers) != 1 or writes != [[1, 0, 2], [2, 0, 2]] or \
            any(v[0] in ('formal', 'object') for v in values.values()):
        raise ValueError('wrapper observed reads, writes or residual origins differ')
    return dict(nonlocal_input_reads=reads, outgoing_pointer_stores=stores,
        child_argument_transport=transfers, formal_writes=writes,
        return_entry_origins=[[n, v[1]] for n, v in sorted(values.items())
                              if n in (0, 1, 2, 3, 12) and v[0] == 'entry'],
        preserved='r4-r11,sp,entry-lr',
        nonlocal_input_premise='conditional: arg0 halfwords at offsets8/10/12 are readable; loaded values unknown; no physical nonalias claim')


class NestedOutputBufferProof(named.DiscardedReturnScratchProof):
    dependency_budget = MAX_DEPENDENCIES
    manifest_schema = SCHEMA

    def __init__(self, rom, mapping, index, objects):
        super().__init__(rom, mapping, index, objects)
        self._native = None
        self._calls = []

    def _body(self, identity):
        address, size, digest = identity
        data = self.span(address)
        if len(data) != size or hashlib.sha256(data).hexdigest() != digest:
            raise ValueError('nested output requires each actual complete immutable indexed helper')
        import owner_admission_profile as owner
        refinement = owner.refine(data, address, self.mapping)
        ins, edges, branches, calls, words = graph.graph(data, address, refinement)
        if branches or words or refinement['word_switches']:
            raise ValueError('nested output helpers exclude local control and word switches')
        return data, ins, edges, calls, graph.partition(data, address, refinement, ins, words)

    def _prove(self):
        if self._native is not None:
            return self._native
        raw, ins, edges, calls, partition = self._body(LEAF)
        if calls or len(ins) != 51:
            raise ValueError('nested output leaf must be its actual call-free complete body')
        leaf = effects.prove_origins(ins, edges, LEAF[0], raw, partition,
                                     self.objects, effects.named_policy())
        leaf_record = dict(address=LEAF[0], end=LEAF[0] + len(raw), bytes=len(raw),
            body_sha256=hashlib.sha256(raw).hexdigest(), structure=dict(
                kind=effects.SCHEMA, instructions=len(ins), partition=partition, effects=leaf), **self.identities)
        self.dependencies[LEAF[0]] = raw
        self.records[LEAF[0]] = leaf_record
        raw, ins, edges, calls, partition = self._body(WRAPPER)
        wrapper = prove_wrapper_origins(ins, edges, calls, WRAPPER[0], raw, leaf)
        self.dependencies[WRAPPER[0]] = raw
        self.records[WRAPPER[0]] = dict(address=WRAPPER[0], end=WRAPPER[0] + len(raw), bytes=len(raw),
            body_sha256=hashlib.sha256(raw).hexdigest(), structure=dict(
                kind=SCHEMA, instructions=len(ins), partition=partition, effects=wrapper), **self.identities)
        self._native = dict(leaf=leaf_record, wrapper=self.records[WRAPPER[0]],
            producer_sha256={Path(module.__file__).name: hashlib.sha256(Path(module.__file__).read_bytes()).hexdigest()
                             for module in (effects, __import__(__name__))})
        return self._native

    def check_call(self, address, aliases, stack, slots=None, *, constants=None, site=None, words=None):
        if address != WRAPPER[0]:
            return super().check_call(address, aliases, stack, slots, constants=constants, site=site, words=words)
        proof = self._prove()
        r0 = match.ARM_REG_R0
        if type(site) is not int or site % 2 or slots or words or \
                r0 in aliases or match.ARM_REG_LR in aliases or not {r0 + 1, r0 + 2} <= set(aliases):
            raise ValueError('nested output caller requires local arg1/arg2, nonlocal arg0 and no pointer slots')
        writes = []
        for formal in (1, 2):
            offset = aliases[r0 + formal]
            self.access(offset, 2, stack)
            writes.append([offset, 2])
        result = {}
        for destination, source in proof['wrapper']['structure']['effects']['return_entry_origins']:
            if r0 + source in aliases:
                offset = aliases[r0 + source]
                self.validate_pointer_value(offset, stack)
                result[r0 + destination] = offset
        self._calls.append(dict(site=site, target=address, writes_entry_SP_offsets=writes,
            return_aliases=[[n-r0, o] for n, o in sorted(result.items())],
            helper_frames='fresh saved/local words strictly below actual callSP; formal writes in live caller locals',
            physical_nonalias_claim=False))
        return result

    def nested_manifest(self):
        if not self._calls or self._native is None:
            raise ValueError('nested output profile requires an actual bounded caller composition')
        return dict(schema=self.manifest_schema, native_helpers=self._native, calls=self._calls,
                    named_read_policy=effects.named_policy(), physical_nonalias_claim=False)


class NestedSelectiveOutputBufferProof(NestedOutputBufferProof):
    """Same nested outputs; observed R2/R3 scratch stays tracked instead of being refused."""
    manifest_schema = SELECTIVE_SCHEMA
    # Opt-in: the only nested family whose callees may follow a compiler jump table.
    jump_table_callees = True
    normal_return_aliases = named.ConditionalThunkSelectiveScratchBufferProof.normal_return_aliases

    def scratch_manifest(self):
        manifest = super().scratch_manifest()
        manifest['selection'] = 'each R2/R3 independently; observed aliases remain tracked'
        manifest['contract'] += ('; observed R2/R3 aliases are retained unchanged for every '
            'ordinary buffer bound, nested call, indirect argument and root return check; '
            'root alias memory accesses are limited to allocated local words, excluding saves')
        return manifest
