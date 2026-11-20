"""The two copied WINxH destinations and the initial 160 scanline rows."""
import argparse
from bisect import bisect_right
from collections import defaultdict
from hashlib import sha256
import json
from pathlib import Path
from struct import pack

import match
import plausible
import window_scanline as window
from ability_range_local_bytes import require
from active_entry_shuffle_profile import compiler_symbol_roles
from owner_admission_profile import refine
from owner_graph_profile import graph
from positioned_equipment_chance import direct_sites
from sdk_cpuset_halfword import TOKEN, base_header
from software_float_profile import ROM_SHA256
from unit_equipment_attribute import ops

OWNER, SPAWNER = 0x080D9C58, 0x080DAB84
SOURCE = 'src/080D9C58.c'
TOKENS = '5b7f8187ef4ea8ce235cdc4be3dc9623fee184b0d2ff3a4a5b91ed82764d1348'
QUALIFIED = '0d5b68179a3ba9e8ab2970fc5fe616d4d6c6b119a56db0b23ed092b67ab5da90'
STRIPPED = '9fee76bba6903155aa076d3e1c84052c808275e45d0f098d580329e3b807924c'
TARGETS = (0x0800C3CC, 0x0800C614, 0x0800C668, 0x0800C6C0)
DATA, CALLBACK = 0x08149B2C, 0x080DAE70
SITES = (0x44, 0x4A, 0x76, 0x84)
MANIFEST = dict(calls=[[o, f'func_{t:08X}'] for o, t in zip(SITES, TARGETS)],
                data=[[0x6C, 'data_08149B2C', 0]], functions=[[0x70, 'func_080DAE70']])


def provider(rom):
    from bg_affine_rows import scanline_pipeline
    require(sha256(rom).hexdigest() == ROM_SHA256, 'window task needs the original USA ROM')
    window.provider_evidence(rom, window.RECT)
    scanline_pipeline(rom)
    # The spawner narrows R0 before storing it at descriptor +20. The scheduler
    # copies 28 descriptor bytes, overwrites phase alone, and calls via R3.
    ops(rom, 0x080DAB88, 'lsls r0, r0, #0x18', 'lsrs r0, r0, #0x18',
        'lsls r1, r1, #0x18', 'lsrs r1, r1, #0x18', 'lsls r2, r2, #0x18',
        'lsrs r2, r2, #0x18', 'mov r4, sp', 'strh r0, [r4, #0x14]', 'mov r0, sp',
        'strh r1, [r0, #0x16]', 'strh r2, [r0, #0x18]', 'ldr r0, [pc, #0x10]',
        'movs r1, #8', 'mov r2, sp', 'bl #0x8005b6c')
    ops(rom, 0x080059EE, 'mov r1, sp', 'mov r0, sb', 'ldm r0!, {r3, r4, r5}',
        'stm r1!, {r3, r4, r5}', 'ldm r0!, {r3, r4, r5}', 'stm r1!, {r3, r4, r5}',
        'ldr r0, [r0]', 'str r0, [r1]', 'mov r1, sp', 'movs r0, #0', 'strh r0, [r1]',
        'ldr r3, [r7]', 'adds r0, r7, #0', 'bl #0x8142250')
    ops(rom, 0x0800C6C0, 'ldrh r2, [r0, #0xc]', 'movs r1, #2',
        'orrs r1, r2', 'strh r1, [r0, #0xc]', 'bx lr')


def caller_modes(rom, mapping):
    require(not direct_sites(rom, OWNER), 'unexpected direct window event caller')
    for address, sites in ((SPAWNER, ()), (SPAWNER | 1, ()), (OWNER, ()), (OWNER | 1, (0x080DABB0,))):
        word = pack('<I', address)
        require(rom.count(word) == len(sites) and all(rom[p-window.BASE:p-window.BASE+4] == word
                for p in sites), 'unexpected window task entry reference')
    entries = json.loads(mapping)
    functions = {int(e['rom'], 16): e for e in entries}
    require(len(functions) == len(entries), 'duplicate window caller mapping')
    starts = sorted(functions)
    grouped = defaultdict(list)
    for pc in direct_sites(rom, SPAWNER):
        start = starts[bisect_right(starts, pc)-1]
        grouped[start].append(pc)
    spans = b''.join(pack('<III', start, int(functions[start]['end'], 16), pc)
                     for start, sites in grouped.items() for pc in sites)
    require(sha256(spans).hexdigest() == 'fe30fdcf9a41eb998ce1bf549a72030de1caf0f349c1d14b44070fa60e05f2d3',
            'changed original window caller span or call site')
    modes = []
    for start, sites in grouped.items():
        e = functions[start]
        end = int(e['end'], 16)
        data = rom[start-window.BASE:end-window.BASE]
        ins, edges, _, calls, _ = graph(data, start, refine(data, start, mapping))
        require(e['mode'] == 'thumb' and sorted(pc for pc, target in calls.items() if target == SPAWNER)
                == sites, 'window task caller span or actual calls differ')
        predecessors = defaultdict(list)
        for pc, targets in edges.items():
            for target in targets:
                predecessors[target].append(pc)
        # Walk every incoming path, including the two arms at 0811E304.
        def arg0(site, depth):
            require(depth < 8 and predecessors[site] and site != start, 'unresolved window argument')
            result = set()
            for pc in predecessors[site]:
                i = ins[pc]
                if match.ARM_REG_R0 in i.regs_access()[1]:
                    require(i.mnemonic == 'movs' and i.op_str in ('r0, #0', 'r0, #1'),
                            'window argument is not an immediate selector')
                    result.add(i.operands[1].imm)
                else:
                    require(i.mnemonic != 'bl', 'call clobbers window selector')
                    result |= arg0(pc, depth+1)
            return result
        for site in sites:
            values = arg0(site, 0)
            require(len(values) == 1, 'expected one bank per original window allocation site')
            modes.extend(values)
    require(len(grouped) == 38 and modes.count(0) == 39 and modes.count(1) == 19,
            'changed window task callers')
    return sorted(set(modes))


def frame(data, rom, mapping, calls, manifest):
    provider(rom)
    require(manifest == MANIFEST and len(data) == 156 and sha256(data).hexdigest() == QUALIFIED
            and calls == {OWNER+o:t for o,t in zip(SITES, TARGETS)}, 'changed window task or bindings')
    ops(rom, 0x080D9C80, 'ldr r0, [pc, #0x40]', 'ldr r1, [r0, #4]', 'ldr r0, [r0]',
        'str r0, [sp]', 'str r1, [sp, #4]', 'ldr r0, [pc, #0x3c]', 'movs r1, #0xa0',
        'lsls r1, r1, #1', 'movs r3, #0x14', 'ldrsh r2, [r4, r3]', 'lsls r2, r2, #2',
        'add r2, sp, r2', 'ldr r3, [r2]', 'movs r2, #2', 'bl #0x800c3cc')

    class WindowFrame(match.FunctionBufferCallProof):
        def extra_constant(self, instruction, data, address, constants):
            if instruction.address == 0x080D9C94:
                return self.window * 4
            return None

    # Each authenticated selector receives a separate ordinary frame walk.
    # Both words were initialized; neither local address crosses the allocator BL.
    results = []
    for mode in caller_modes(rom, mapping):
        proof = WindowFrame(rom, mapping)
        proof.window = mode
        ins = match.verify_leaf_instructions(data, OWNER, True, calls, buffer_proof=proof)
        require(not proof.dependencies and len(ins) == 70, 'window table alias escaped or CFG differs')
        results.append(ins)
    require([i.address for i in results[0]] == [i.address for i in results[1]], 'window CFG differs by bank')
    return results[0]


def qualifier_offsets(text, tree, project, closure):
    from rompath import rom_path
    symbols = ('WindowEvent', 'WindowState', 'WindowLine', 'WindowDestinations', 'WindowCopy',
               'data_08149B2C', 'func_080D9C58', 'func_080DAE70', *(f'func_{t:08X}' for t in TARGETS))
    if closure != ({SOURCE, window.HEADER}, []) or not base_header((Path(tree)/window.HEADER).read_bytes(), symbols):
        return set()
    if any(marker in text for marker in (chr(92), '??', '%:', chr(0))):
        return set()
    code = plausible.strip_comments_and_strings_keep_strings(text)
    pair = window.ELEMENT.search(code)
    if not pair or sha256(' '.join(TOKEN.findall(code)).encode()).hexdigest() != TOKENS:
        return set()
    provider(Path(rom_path(project)).read_bytes())
    return {pair.start('left'), pair.start('right')}


def controls(root, rom):
    args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                              objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
    runner = match.Runner(args.cc, root=str(root), timeout=match.SIGNED_REPLAY_TIMEOUT)
    mapping, objects = match.mapping_snapshot(root), match.data_snapshot(root)
    bodies = []
    with runner.workspace() as ws:
        for short, rewrite in ((False, None), (True, window.rewrite_element),
                               (False, lambda s: window.rewrite_element(s, True))):
            _, _, image = match.compile_object(runner, ws, args, str(root), OWNER, SOURCE, rewrite=rewrite)
            match.allocated_text_only(image)
            targets = {name for _, name in MANIFEST['calls']} | {'data_08149B2C', 'func_080DAE70'}
            compiler_symbol_roles(image, targets)
            require({s['name'] for s in image['symbols'] if s['name'] and not s['section']} == targets
                    and all(s['bind'] == 1 and not s['size'] for s in image['symbols'] if s['name'] in targets),
                    'unexpected original window symbols')
            functions = {}
            body, calls, data = match.link_calls(runner, ws, args, image, OWNER, mapping, len(rom),
                                                 rom, objects, functions)
            delta = 4 if short else 0
            require(data == {0x6C-delta: ('data_08149B2C', DATA)} and
                    functions == {0x70-delta: ('func_080DAE70', CALLBACK | 1)} and
                    calls == {OWNER+o-(delta if o > 0x70 else 0):t for o,t in zip(SITES, TARGETS)},
                    'control lost original window literal or call provenance')
            bodies.append(body)
    real, stripped, swapped = bodies
    require(real == rom[OWNER-window.BASE:OWNER-window.BASE+156] and len(stripped) == 152
            and sha256(real).hexdigest() == QUALIFIED and sha256(stripped).hexdigest() == STRIPPED,
            'changed original window task or qualifier-stripped control')
    ops(rom, 0x080D9CA6, 'adds r2, r0, #0', 'movs r3, #0', 'ldrh r0, [r4, #0x16]',
        'ldrb r1, [r2, #1]', 'strb r0, [r2, #1]', 'ldrh r0, [r4, #0x18]', 'ldrb r1, [r2]',
        'strb r0, [r2]', 'adds r2, #2', 'adds r0, r3, #1', 'lsls r0, r0, #0x10',
        'lsrs r3, r0, #0x10', 'cmp r3, #0x9f', 'bls #0x80d9caa')
    decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
    short_loop = list(decoder.disasm(stripped[0x4e:0x66], OWNER+0x4e))
    require([f'{i.mnemonic} {i.op_str}' for i in short_loop] == [
        'adds r1, r0, #0', 'movs r2, #0', 'ldrh r0, [r4, #0x16]', 'strb r0, [r1, #1]',
        'ldrh r0, [r4, #0x18]', 'strb r0, [r1]', 'adds r1, #2', 'adds r0, r2, #1',
        'lsls r0, r0, #0x10', 'lsrs r2, r0, #0x10', 'cmp r2, #0x9f', 'bls #0x80d9caa'],
        'window task ordinary row accesses differ')
    expected = bytearray(real)
    for off in (0x54, 0x56, 0x5a, 0x5c):
        expected[off] ^= 0x40
    require(swapped == expected, 'window field reads and writes must follow the swapped byte lane')
    return [sha256(b).hexdigest() for b in bodies]


def record(root):
    from rompath import rom_path
    root = Path(root)
    path = root / SOURCE
    require(list((root/'src').rglob(path.name)) == [path] and
            qualifier_offsets(path.read_text(), root, root, plausible.include_closure(root, path)),
            'expected reviewed window task source and base header')
    rom = Path(rom_path(root)).read_bytes()
    digests = controls(root, rom)
    return ('* allowlisted volatile scanline: `window-task-byte-rows-v1` original/stripped/swapped '
            f'`{"/".join(digests)}`; 58 original calls in 38 functions select WIN0H/WIN1H (39/19); '
            '080DAB84 passes a 28-byte descriptor with a byte-narrowed window index. On synchronous '
            'event zero the scheduler overwrites only its phase. The two pointers copied from 08149B2C occupy '
            'frame bytes [0,8); the signed selector picks initialized word +0 or +4. '
            'Requires a live exclusive task, a free manager slot, successful 1000-byte allocation '
            'and intact installed clear. Its 320-byte payload is distinct from the two 324-byte banks. '
            'Each of 160 rows reads then writes left (+1) and right (+0). The registered 080DAE70 '
            'copies these halfwords into the back bank before HBlank DMA. Later phases require the '
            'same live object, with no concurrent disposal or reinitialization.')
