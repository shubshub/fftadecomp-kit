"""Explicit inventory composition of exact inert self-spins and incoming ABI word0."""
import argparse
import json
from pathlib import Path

from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
from capstone.arm import ARM_OP_IMM, ARM_OP_MEM, ARM_OP_REG, ARM_REG_SP

import analyze
import framed_switch_inventory as ordinary
import inert_spin_profile as inert
import local_long_branch_profile as frame
import match
import owner_admission_profile as owner
import owner_graph_profile as partitioner
import owner_runtime_profile as operations
import readonly_entry_stack_profile as entry

SELECTOR = 'mixed-inert-spin-readonly-entry-word-inventory-v1'
SCHEMA = 'thumb-mixed-inert-spin-readonly-entry-word-inventory-v1'
bind_calls = ordinary.bind_calls
text, sha = ordinary.text, ordinary.sha


def graph(data, address, refinement):
    """Replay native refinement edges, retaining self-spins as edges, never returns."""
    if not refinement['cfg_closed'] or refinement['partial_reasons'] or refinement['word_switches']:
        raise ValueError('entry-word inert inventory requires a closed ordinary direct CFG')
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    decoder.detail = True
    instructions = {}
    for lo, hi in refinement['code_ranges']:
        lo, hi = int(lo, 16), int(hi, 16)
        if not address <= lo < hi <= address + len(data) or lo % 2 or hi % 2:
            raise ValueError('entry-word inert code range leaves its owner')
        cursor = lo
        for item in decoder.disasm(data[lo-address:hi-address], lo):
            if item.address != cursor or cursor in instructions:
                raise ValueError('entry-word inert instruction boundary differs')
            instructions[cursor] = item
            cursor += item.size
        if cursor != hi:
            raise ValueError('entry-word inert code range has an undecoded tail')
    calls = {int(row['site'], 16): int(row['target'], 16) for row in refinement['calls']}
    returns = {int(site, 16) for site in refinement['returns']}
    edges = {}
    for site, item in sorted(instructions.items()):
        info = analyze.Decoder._describe(item)
        if site in returns:
            successors = ()
        elif item.mnemonic == 'bl':
            if len(item.operands) != 1 or item.operands[0].type != ARM_OP_IMM or \
                    calls.get(site) != item.operands[0].imm or address <= calls[site] < address+len(data):
                raise ValueError('entry-word inert excludes local or unresolved calls')
            successors = (site+item.size,)
        elif info['jump'] or info['writes_pc']:
            if info['tgt'] is None or item.mnemonic == 'bx':
                raise ValueError('entry-word inert excludes unproved indirect transfers')
            successors = (match.ROM_BASE+info['tgt'],) + ((site+item.size,) if info['cond'] else ())
        else:
            successors = (site+item.size,)
        if any(target not in instructions for target in successors):
            raise ValueError('entry-word inert edge leaves decoded boundaries')
        edges[site] = successors
    reached, pending = set(), [address]
    while pending:
        site = pending.pop()
        if site not in reached:
            reached.add(site)
            pending.extend(edges[site])
    if reached != set(instructions) or len(instructions) != refinement['instrs'] or not returns:
        raise ValueError('entry-word inert graph differs from complete reachable refinement')
    return instructions, edges, calls, returns


def initialized_locals(instructions, edges, address, restored):
    """Definite byte initialization only, after the existing frame/alias proof.

    Alias reads are restricted to an immediate MOV SP followed by a same-register
    constant-offset load that kills the alias, with no other incoming edge.
    No additional pointer operation or numeric fact is admitted here.
    """
    aliases = restored['local_aliases']
    if aliases['buffer_calls']:
        raise ValueError('entry-word inert excludes stack arguments')
    accesses = {}
    for site in aliases['assignments']:
        item = instructions[site]
        operands = item.operands
        successor = site+item.size
        consumers = [source for source, targets in edges.items() if successor in targets]
        if item.mnemonic != 'mov' or item.size != 2 or len(operands) != 2 or \
                operands[0].type != ARM_OP_REG or operands[1].type != ARM_OP_REG or \
                operands[1].reg != ARM_REG_SP or edges[site] != (successor,) or consumers != [site]:
            raise ValueError('entry-word inert requires a single-use immediate local SP alias')
        load = instructions[successor]
        ops = load.operands
        width = {'ldr': 4, 'ldrh': 2, 'ldrb': 1}.get(load.mnemonic)
        if width is None or len(ops) != 2 or ops[0].type != ARM_OP_REG or \
                ops[1].type != ARM_OP_MEM or ops[0].reg != operands[0].reg or \
                ops[1].mem.base != operands[0].reg or ops[1].mem.index:
            raise ValueError('entry-word inert requires an immediate local load that kills its alias')
        accesses[successor] = (ops[1].mem.disp, width)
    if set(accesses) != set(aliases['accesses']):
        raise ValueError('entry-word inert has unsupported local alias accesses')
    # Offsets are relative to entry SP. Saved bytes never enter the local set.
    states = {address: (0, frozenset(), frozenset())}
    pending, reads = [address], set()
    while pending:
        site = pending.pop()
        depth, local, initialized = states[site]
        local, initialized = set(local), set(initialized)
        item = instructions[site]
        adjustment = match.thumb_stack_adjustment(item)
        if item.mnemonic == 'push':
            depth += 4*len(item.operands)
        elif item.mnemonic == 'pop':
            depth -= 4*len(item.operands)
        elif adjustment is not None:
            previous = depth
            depth -= 4*adjustment
            if adjustment < 0:
                allocated = set(range(-depth, -previous))
                local.update(allocated)
                initialized.difference_update(allocated)
            else:
                local = {offset for offset in local if offset >= -depth}
                initialized.intersection_update(local)
        for operand in item.operands:
            if operand.type != ARM_OP_MEM:
                continue
            if operand.mem.base == ARM_REG_SP:
                offset, width = operand.mem.disp-depth, 4
            elif site in accesses:
                disp, width = accesses[site]
                offset = disp-depth
            else:
                continue
            window = set(range(offset, offset+width))
            if window & local:
                if not window <= local:
                    raise ValueError('entry-word inert local access crosses allocation')
                if item.mnemonic.startswith('str'):
                    initialized.update(window)
                elif not window <= initialized:
                    raise ValueError('entry-word inert local read is not initialized on every path')
                else:
                    reads.add((site, offset, width))
        outgoing = (depth, frozenset(local), frozenset(initialized))
        for successor in edges[site]:
            previous = states.get(successor)
            if previous is not None:
                if previous[:2] != outgoing[:2]:
                    raise ValueError('entry-word inert initialization frame shape differs at join')
                merged = (*outgoing[:2], previous[2] & outgoing[2])
            else:
                merged = outgoing
            if previous != merged:
                states[successor] = merged
                pending.append(successor)
    return {'schema': 'definite-local-byte-initialization-v1',
        'reads': [list(row) for row in sorted(reads)],
        'joins': 'intersection of initialized local bytes on every reaching path',
        'entry_word': 'readable initialized input premise; contents unknown'}


def verify(data, address, rom, mapping, index, calls, bindings, *, selector, manifest=None):
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('entry-word inert inventory requires its explicit selector and input contract')
    if any(type(value) is not bytes for value in (data, rom, mapping, index)) or type(address) is not int:
        raise ValueError('entry-word inert inventory requires immutable exact ROM/index inputs')
    entries = owner.validate_span(data, address, rom, mapping, index)
    refinement = owner.refine(data, address, mapping)
    instructions, edges, actual_calls, returns = graph(data, address, refinement)
    if type(calls) is not dict or calls != actual_calls or \
            type(bindings) is not dict or bindings != bind_calls(calls, mapping, address, len(data), len(rom)):
        raise ValueError('entry-word inert requires every actual centrally bound ordinary call')
    selected = next(row for row in entries if int(row['rom'], 16) == address)
    rows = [line.split() for line in index.decode().splitlines()
            if line.split() and line.split()[0] == f'{address:08X}']
    if type(selected.get('instrs')) is not int or selected['instrs'] != len(instructions) or \
            len(rows) != 1 or len(rows[0]) < 4 or int(rows[0][3]) != len(instructions):
        raise ValueError('entry-word inert requires exact dual-index instruction counts')
    operations.verify_operations(instructions, edges, address, {}, calls, refinement)
    if any(item.mnemonic.startswith(('ldm', 'stm')) for item in instructions.values()):
        raise ValueError('entry-word inert excludes block memory transfers')
    partition = partitioner.partition(data, address, refinement, instructions, {})
    restored = frame.prove_frame(instructions, edges, address, {}, calls, stack_aliases=True,
        entry_stack_policy={'schema': entry.SCHEMA, 'words': [0]})
    if not restored['entry_stack']['reads'] or set(restored['returns']) != returns:
        raise ValueError('entry-word inert requires actual incoming read and identical checked returns')
    initialized = initialized_locals(instructions, edges, address, restored)
    reverse = {site: set() for site in instructions}
    for site, successors in edges.items():
        for target in successors:
            reverse[target].add(site)
    covered, pending = set(returns), list(returns)
    while pending:
        site = pending.pop()
        for previous in reverse[site]-covered:
            covered.add(previous)
            pending.append(previous)
    spins = sorted(set(instructions)-covered)
    native_manifest = {'calls': inert.call_records(calls, address),
        'frame': match.uses_stack_frame(list(instructions.values())), 'spins': [site-address for site in spins]}
    verified = inert.verify(data, address, rom, mapping, index, native_manifest)
    if [(item.address, bytes(item.bytes)) for item in verified] != [
            (site, bytes(item.bytes)) for site, item in sorted(instructions.items())]:
        raise ValueError('native inert and strict frame instruction coverage differ')
    # The same exact instruction bytes, native refinement successors, call map,
    # strict returns and authenticated inert offsets bind both component proofs.
    cfg = [[site, list(edges[site])] for site in sorted(edges)]
    modules = (analyze, ordinary, inert, frame, match, owner, partitioner, operations, entry)
    pins = {Path(module.__file__).name: sha(Path(module.__file__).read_bytes()) for module in modules}
    pins[Path(__file__).name] = sha(Path(__file__).read_bytes())
    observed = {'schema': SCHEMA, 'selector': SELECTOR, 'inventory_only': True,
        'source_or_ELF_admission': False, 'address': address, 'end': address+len(data),
        'instructions': len(instructions), 'calls': [[site-address, name] for site, name in sorted(bindings.items())],
        'runtime_calls': [], 'spins': [site-address for site in spins], 'spin_bytes': 'fee7',
        'native_inert_manifest': native_manifest, 'frame': restored, 'partition': partition,
        'local_initialization': initialized, 'entry_stack_contract': entry.CONTRACT,
        'entry_word_initialization_premise': 'entry SP+0 supplies four readable initialized bytes; contents unknown',
        'ordinary_call_premise': 'conditional: every ordinary callee returns and obeys the existing r4-r11/SP preserving direct-call ABI',
        'ordinary_callee_native_proof': False, 'stack_pointer_arguments': False,
        'claim': 'complete local structural inventory; reached returns restore SP/r4-r11/entry-LR; nonreturn regions are exact inert self-spins',
        'termination_claim': False, 'arithmetic_C_equivalence': False, 'memory_safety_claim': False,
        'numeric_input_preconditions': [], 'graph_sha256': sha(text(cfg).encode()),
        'component_agreement': 'exact body, instructions, graph, calls, returns, inert offsets and input maps',
        'body_sha256': sha(data), 'mapping_sha256': sha(mapping), 'index_sha256': sha(index), 'ROM_sha256': sha(rom),
        'producer_source_sha256': pins, 'complete_native_structural_proof': True}
    if manifest is not None and text(manifest) != text(observed):
        raise ValueError('entry-word inert manifest differs from fresh native proof')
    return observed, verified


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile', required=True, choices=(SELECTOR,))
    for name in ('rom', 'mapping', 'index'):
        parser.add_argument('--'+name, required=True, type=Path)
    parser.add_argument('address', type=lambda value: int(value, 16))
    args = parser.parse_args()
    rom, mapping, index = args.rom.read_bytes(), args.mapping.read_bytes(), args.index.read_bytes()
    rows = [row for row in json.loads(mapping) if int(row['rom'], 16) == args.address]
    if len(rows) != 1:
        raise ValueError('entry-word inert requires one exact mapped owner')
    data = rom[args.address-match.ROM_BASE:int(rows[0]['end'], 16)-match.ROM_BASE]
    refinement = owner.refine(data, args.address, mapping)
    calls = {int(row['site'], 16): int(row['target'], 16) for row in refinement['calls']}
    bindings = bind_calls(calls, mapping, args.address, len(data), len(rom))
    observed, _ = verify(data, args.address, rom, mapping, index, calls, bindings, selector=args.profile)
    print(text(observed))


if __name__ == '__main__':
    main()
