"""Exact closed Thumb owner graph and complete byte partition."""
import struct
from capstone import Cs,CS_ARCH_ARM,CS_MODE_THUMB
import analyze as original_analyze
import local_long_branch_profile as local
import match
def graph(data, address, refinement, *, one_object_word_switch=False):
    """Replay exact decoded boundaries and native switch/local-BL descriptors."""
    if type(one_object_word_switch) is not bool:
        raise ValueError('one-object-word graph opt-in must be Boolean')
    if not refinement['cfg_closed'] or refinement['partial_reasons']:
        raise ValueError('structural inventory is not closed')
    end = address + len(data)
    cs = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    cs.detail = True
    instructions = {}
    code_bytes = set()
    for lo, hi in refinement['code_ranges']:
        lo, hi = int(lo, 16), int(hi, 16)
        if lo % 2 or hi % 2 or not address <= lo < hi <= end:
            raise ValueError('code range escapes its exact complete owner')
        cursor = lo
        for instruction in cs.disasm(data[lo - address:hi - address], lo):
            if instruction.address != cursor or instruction.address in instructions:
                raise ValueError('code ranges have an ambiguous instruction boundary')
            span = set(range(cursor, cursor + instruction.size))
            if code_bytes & span:
                raise ValueError('code ranges overlap')
            instructions[cursor] = instruction
            code_bytes.update(span)
            cursor += instruction.size
        if cursor != hi:
            raise ValueError('code range has an undecoded tail')
    if len(instructions) != refinement['instrs'] or address not in instructions:
        raise ValueError('reachable instruction count differs from refinement')

    transfers, table_words = {}, {}
    for switch in refinement['word_switches']:
        words = dict(switch['relocations'])
        data_words = None
        if one_object_word_switch and switch.get('interposed_words') == 1:
            offset = switch['literal'] - 4
            if offset < 0 or offset + 4 > len(data):
                raise ValueError('one-object-word graph literal escapes owner')
            data_words = {offset: ('inventory_object_word', struct.unpack_from('<I', data, offset)[0])}
        layout = match.switch_layout(data, address, words, data_words)
        if any(layout[key] != switch[key] for key in layout):
            raise ValueError('switch layout differs from native byte-exact replay')
        transfer = address + layout['dispatch'] + 8
        if transfer in transfers:
            raise ValueError('switch transfer has ambiguous descriptors')
        transfers[transfer] = layout
        for offset, destination in words.items():
            if offset in table_words:
                raise ValueError('switches overlap local word ownership')
            table_words[offset] = destination

    returns = {int(site, 16) for site in refinement['returns']}
    calls = {int(row['site'], 16): int(row['target'], 16)
             for row in refinement['calls']}
    edges, branches = {}, {}
    for site, instruction in sorted(instructions.items()):
        info = original_analyze.Decoder._describe(instruction)
        if site in transfers:
            switch = transfers[site]
            successors = sorted({address + target for offset, target in switch['relocations']
                                 if offset != switch['literal']})
        elif site in returns:
            successors = []
        elif instruction.mnemonic == 'bl':
            target = instruction.operands[0].imm
            if address <= target < end:
                branches[site] = local.target(instruction, address, end)
                successors = [branches[site]]
            else:
                if calls.get(site) != target:
                    raise ValueError('external call differs from structural evidence')
                successors = [site + instruction.size]
        elif info['jump'] or info['writes_pc']:
            if info['tgt'] is None or instruction.mnemonic == 'bx':
                raise ValueError('unproved indirect control transfer')
            successors = [match.ROM_BASE + info['tgt']]
            if info['cond']:
                successors.append(site + instruction.size)
        else:
            successors = [site + instruction.size]
        if any(target not in instructions for target in successors):
            raise ValueError('CFG edge is not a decoded instruction boundary')
        edges[site] = tuple(successors)

    # Do not accept arbitrary retained/unreachable decoded ranges.
    reached, pending = set(), [address]
    while pending:
        site = pending.pop()
        if site not in reached:
            reached.add(site)
            pending.extend(edges[site])
    if reached != set(instructions):
        raise ValueError('retained instructions are not exactly entry-reachable')
    reverse = {site: set() for site in instructions}
    for site, successors in edges.items():
        for target in successors:
            reverse[target].add(site)
    covered, pending = set(returns), list(returns)
    while pending:
        site = pending.pop()
        for predecessor in reverse[site] - covered:
            covered.add(predecessor)
            pending.append(predecessor)
    if covered != set(instructions):
        raise ValueError('reachable control-flow region has no path to a verified return')
    return instructions, edges, branches, calls, table_words


def partition(data, address, refinement, instructions, table_words):
    """Exact code + reached words + the existing narrow zero-alignment rule."""
    code = {byte - address for site, item in instructions.items()
            for byte in range(site, site + item.size)}
    loads = {}
    words = set(table_words)
    for site, instruction in sorted(instructions.items()):
        info = original_analyze.Decoder._describe(instruction)
        if info['pcldr'] is None:
            continue
        offset = ((site + 4) & ~3) + info['pcldr'][1] - address
        if (address + offset) % 4 or not 0 <= offset <= len(data) - 4:
            raise ValueError('reached literal leaves its aligned complete owner')
        loads.setdefault(offset, []).append(site)
        words.add(offset)
    literal_bytes = {byte for offset in words for byte in range(offset, offset + 4)}
    if code & literal_bytes:
        raise ValueError('code and literal/table bytes overlap')
    captured_literals = {byte - address for lo, hi in refinement['literal_ranges']
                         for byte in range(int(lo, 16), int(hi, 16))}
    if literal_bytes != captured_literals:
        raise ValueError('literal ownership differs from reached loads and exact tables')
    for offset, target in table_words.items():
        if struct.unpack_from('<I', data, offset)[0] != address + target:
            raise ValueError('table word changed after native replay')
    missing = set(range(len(data))) - code - literal_bytes
    alignment = []
    for offset in sorted(missing):
        if offset - 1 in missing and offset % 2:
            continue
        # Same rule as native switch_constants_profile.complete_partition:
        # exactly one zero halfword immediately before an actually read word.
        if offset % 2 or offset + 1 not in missing or offset + 2 not in loads or \
                (address + offset) % 4 != 2 or data[offset:offset + 2] != b'\0\0':
            raise ValueError('unowned complete-owner bytes are not canonical literal alignment')
        alignment.append([address + offset, address + offset + 2])
    if len(code) + len(literal_bytes) + 2 * len(alignment) != len(data):
        raise ValueError('complete-owner partition has missing or overlapping bytes')
    return {'code_bytes': len(code), 'literal_and_table_bytes': len(literal_bytes),
            'alignment_bytes': 2 * len(alignment), 'alignment': alignment,
            'words': [{'address': address + offset,
                       'value': struct.unpack_from('<I', data, offset)[0],
                       'load_sites': loads.get(offset, []),
                       'switch_word': offset in table_words}
                      for offset in sorted(words)]}

