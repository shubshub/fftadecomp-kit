"""Complete two-word callback adapters, under an explicit returning ABI premise."""
import hashlib
import json
from pathlib import Path

import match
import owner_graph_profile as graph
import function_thunk_profile as thunk
import local_long_branch_profile as frame
from software_double_profile import indices, span_record

SELECTOR = 'two-word-scalar-callback-adapter-inventory-v1'
PRESERVED = frozenset(range(match.ARM_REG_R0+4, match.ARM_REG_R0+12))


def sha(data):
    return hashlib.sha256(data).hexdigest()


def registers(item):
    if any(op.type != match.ARM_OP_REG for op in item.operands):
        return None
    return tuple(op.reg for op in item.operands)


def load(item, destination, base, offset):
    ops = item.operands
    return item.mnemonic == 'ldr' and item.size == 2 and len(ops) == 2 and \
        ops[0].type == match.ARM_OP_REG and ops[0].reg == destination and \
        ops[1].type == match.ARM_OP_MEM and ops[1].mem.base == base and \
        not ops[1].mem.index and ops[1].mem.disp == offset and not item.writeback


def verify(address, getter, rom, mapping, index, *, selector, manifest=None):
    # owner_admission_profile imports this module through the two-word closure
    # profiles; importing it here keeps this module importable first.
    import owner_admission_profile as owner
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('scalar adapter requires its explicit inventory selector')
    if any(type(v) is not int for v in (address, getter)) or \
            any(type(v) is not bytes for v in (rom, mapping, index)):
        raise ValueError('scalar adapter requires exact immutable inputs')
    entries, rows = indices(mapping, index)

    def complete(start, size, count):
        data = rom[start-match.ROM_BASE:start-match.ROM_BASE+size]
        owner.validate_span(data, start, rom, mapping, index)
        identity = span_record(start, start+size, entries, rows, rom)
        refinement = owner.refine(data, start, mapping)
        ins, edges, branches, calls, words = graph.graph(data, start, refinement)
        partition = graph.partition(data, start, refinement, ins, words)
        if branches or words or partition['literal_and_table_bytes'] or \
                partition['alignment_bytes'] or len(ins) != count or identity['instrs'] != count:
            raise ValueError('scalar adapter requires exact complete code-only owner/count')
        ordered = [ins[site] for site in sorted(ins)]
        if any(edges[item.address] != ((ordered[number+1].address,) if number+1 < len(ordered) else ())
                for number, item in enumerate(ordered)):
            raise ValueError('scalar adapter requires one complete linear continuation')
        return data, ordered, ins, edges, calls, partition

    data, code, ins, edges, calls, partition = complete(address, 22, 9)
    leaf, leaf_code, leaf_ins, leaf_edges, leaf_calls, leaf_partition = complete(getter, 4, 2)
    r0, r1, r2 = match.ARM_REG_R0, match.ARM_REG_R0+1, match.ARM_REG_R0+2
    if not load(leaf_code[0], r0, r0, 0) or leaf_code[1].mnemonic != 'bx' or \
            registers(leaf_code[1]) != (match.ARM_REG_LR,) or leaf_calls:
        raise ValueError('scalar adapter getter must only load incoming R0 word zero and return')
    saved = registers(code[0])
    if code[0].mnemonic != 'push' or saved is None or len(saved) != 2 or \
            saved[0] not in range(r0+4, r0+8) or saved[1] != match.ARM_REG_LR:
        raise ValueError('scalar adapter requires one saved low context register and LR')
    context = saved[0]
    copy = code[1]
    copied = copy.mnemonic == 'mov' and registers(copy) == (context, r1)
    if not copied:
        ops = copy.operands
        copied = copy.mnemonic in ('add', 'adds') and len(ops) == 3 and \
            ops[0].type == ops[1].type == match.ARM_OP_REG and \
            ops[0].reg == context and ops[1].reg == r1 and \
            ops[2].type == match.ARM_OP_IMM and ops[2].imm == 0
    selected_thunk = thunk.ALIASES['_call_via_r2']
    if not copied or code[1].size != 2 or \
            calls != {code[2].address: getter, code[5].address: selected_thunk} or \
            code[2].size != 4 or code[5].size != 4 or \
            not load(code[3], r1, context, 0) or not load(code[4], r2, context, 4):
        raise ValueError('scalar adapter requires exact getter, argument word zero and target word four')
    restored, returned = registers(code[6]), registers(code[7])
    if code[6].mnemonic != 'pop' or restored != (context,) or \
            code[7].mnemonic != 'pop' or returned is None or len(returned) != 1 or \
            returned[0] not in (r1, r2, r0+3) or code[8].mnemonic != 'bx' or \
            registers(code[8]) != returned:
        raise ValueError('scalar adapter must restore its context register and original return without changing R0')
    body = rom[selected_thunk-match.ROM_BASE:selected_thunk-match.ROM_BASE+2]
    owner.validate_span(body, selected_thunk, rom, mapping, index)
    identity = span_record(selected_thunk, selected_thunk+2, entries, rows, rom)
    if identity['instrs'] != 1 or any(int(row['rom'],16) < selected_thunk+4 and
            int(row['end'],16) > selected_thunk+2 for row in entries):
        raise ValueError('scalar adapter thunk requires its exact indexed BX and separate padding')
    canonical, = thunk.dependencies(['_call_via_r2'], rom)
    if len({address, getter, selected_thunk}) != 3:
        raise ValueError('scalar adapter dependency owners must be distinct')
    getter_frame = frame.prove_frame(leaf_ins, leaf_edges, getter, {}, {}, call_preservation={})
    conditional_frame = frame.prove_frame(ins, edges, address, {}, calls,
        call_preservation={site: PRESERVED for site in calls})
    observed = dict(schema=SELECTOR, inventory_only=True, address=address,
        end=address+22, instructions=9, body_sha256=sha(data), partition=partition,
        descriptor_register=context-r0, descriptor_reads=[
            dict(site=code[3].address, offset=0, width=4, destination=1),
            dict(site=code[4].address, offset=4, width=4, destination=2)],
        getter=dict(address=getter, end=getter+4, body_sha256=sha(leaf),
                    partition=leaf_partition, frame=getter_frame,
                    read=dict(base='entry R0', offset=0, width=4)),
        callback=dict(site=code[5].address, thunk=selected_thunk, canonical=canonical,
            target='descriptor word at offset 4',
            arguments=['word loaded by getter from entry R0', 'descriptor word at offset 0'],
            descriptor_address_passed_as_argument=False, result='unchanged callback R0'),
        conditional_frame=conditional_frame,
        explicit_conditions=[
            'Entry R0 denotes a readable aligned initialized word; entry R1 denotes two readable aligned initialized words.',
            'The complete private eight-byte saved frame is valid and does not wrap or alias either input read or callback-visible memory.',
            'The descriptor target is compatible returning Thumb code preserving R4-R11 and SP, the private frame and continuation code.',
            'Loaded input words carry no tracked private-frame or saved-return provenance; ordinary memory noninterference remains a premise.'],
        claim='Under all explicit conditions the complete adapter reads the getter word and two descriptor words, calls the descriptor target with those two scalar word values, restores its saved context register and original return, and returns the callback R0 unchanged.',
        actual_callback_ABI_established=False, actual_memory_permissions_established=False,
        numeric_nonalias_proved=False, object_lifetime_established=False,
        initialized_contents_established=False, termination_proved=False,
        source_or_ELF_admission=False,
        ROM_sha256=sha(rom), mapping_sha256=sha(mapping), index_sha256=sha(index),
        producer_source_sha256={Path(module.__file__).name:sha(Path(module.__file__).read_bytes())
            for module in (match, match.armv4t, owner, graph, thunk, frame)})
    observed['producer_source_sha256'][Path(__file__).name] = sha(Path(__file__).read_bytes())
    if manifest is not None and json.dumps(manifest,sort_keys=True) != json.dumps(observed,sort_keys=True):
        raise ValueError('scalar adapter inventory manifest differs')
    return observed
