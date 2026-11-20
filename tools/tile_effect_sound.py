"""Sound #0x8D never consumes the tile effect routine's residual stack argument."""
from functools import lru_cache
from hashlib import sha256
import json
from pathlib import Path
from struct import unpack_from

from capstone.arm import ARM_REG_R5, ARM_REG_R6, ARM_REG_R7, ARM_REG_SP
import local_long_branch_profile as frame
import ordinary_formal_stack_callee_inventory as formal
import owner_admission_profile as owner
import owner_graph_profile as graph
import runtime_summary_profile as runtime
from unit_equipment_attribute import ops

BASE = 0x08000000
ROOT = 0x080D8858
CALLS = {0x080D8906: 0x08141570, 0x080D890E: 0x08141520}
CALLBACKS = (0x081465E4, 0x08145BF4)
THUNK = 0x08144D84
SONG = 0x08363548
# Each digest covers the complete original code, alignment and literal pools.
BODIES = {
    0x08141520: (0x08141540, 'c2b406f78415f76592f68bce51e60bab1b65fd59b4e9f503b3be1a76031f90b1'),
    0x08141570: (0x081415C0, 'ca2cd542a8e8b61d23f85e52a0fe9d7ba19fffaf8dd6acbb59fee2709456644c'),
    0x081451C0: (0x081451EC, '2cc3c0c32b4559e083d3330d14b0598638c6708fc75b226d4d064d8c74396fe1'),
    0x081458AC: (0x08145990, '26db72827f9e87bd2f408417d96e56075acbfa8d783bf6b0e26ae9c3ac07a1f0'),
    0x08144D94: (0x08144DD8, '42f0896ed58bb911bad7a16413ced7798e23955b043d5f728b5e3385d3ee37e0'),
    0x08145BF4: (0x08145C44, '67a2670376360f300df5a7d18b458792da50002de9bcde7580342dcf8c366fcf'),
    0x081465E4: (0x081465E6, 'c7dfbb7d02759eacb64dbc916c1bb6f21eabaff1c1032ea5c9176abf7fd28df8'),
}
INSTALLERS = {
    0x0814553C: (0x08145608, 'e94a015e3d7b691e0c020e05509c3b94b334005bfc67a3c0c5dbed792bab04d7'),
    0x081453F8: (0x08145510, '0ff9bedc7731c400d639fcdca45671c148fcbede4802fc2afd25a26b2bc849e3'),
}


def require(test, message):
    if not test:
        raise ValueError('tile sound: ' + message)


def environment_fingerprint():
    import multiple_switch_native_profile as native
    import named_data_buffer_profile as named
    import unit_equipment_attribute as units
    result = native.environment_fingerprint()
    for module in (formal, formal.slots, formal.zero_index, formal.incoming, formal.thunks,
                   runtime, named, units):
        path = Path(module.__file__)
        result['producers'][path.name] = sha256(path.read_bytes()).hexdigest()
    result['producers'][Path(__file__).name] = sha256(Path(__file__).read_bytes()).hexdigest()
    return result


def dependencies(rom, mapping, index):
    functions, rows = {}, []
    for address, (end, digest) in {**BODIES, **INSTALLERS}.items():
        body = rom[address-BASE:end-BASE]
        require(sha256(body).hexdigest() == digest, 'original sound body differs')
        owner.validate_span(body, address, rom, mapping, index)
        if address in INSTALLERS:
            continue
        ins, edges, branches, calls, words = graph.graph(body, address, owner.refine(body, address, mapping))
        require(not branches and not words, 'unexpected local call or computed jump')
        restored = frame.prove_frame(ins, edges, address, {}, calls)
        functions[address] = ins, edges, calls
        rows.append(dict(address=address, end=end, sha256=digest, instructions=len(ins),
                         frame_bytes=restored['maximum_frame_bytes'], calls=sorted(calls.items())))
    return functions, rows


def runtime_bindings(rom, mapping, index):
    def word(address):
        return unpack_from('<I', rom, address-BASE)[0]
    # The two wrappers load the immutable song table. The indirect wrapper also
    # indexes the entry's player number into its separate 12-byte player table.
    require(word(0x081415BC) == word(0x081451E8) == 0x0814BB48 and
            word(0x081451E4) == 0x0814BB24 and
            word(0x08141598) == 0x0200F2E0 and word(0x081415B8) == 0x0200F320 and
            word(0x0814BB48+8*0x8D) == SONG and
            word(0x0814BB48+8*0x8D+4) & 0xffff == 2 and
            word(0x0814BB24+12*2) == 0x0200F320 and
            rom[SONG-BASE+3] == 0, 'song row, player, or reverb differs')
    ops(rom, 0x081415A4, 'lsls r0, r4, #3', 'adds r0, r0, r1', 'ldr r1, [r0]',
        'adds r0, r2, #0', 'bl #0x81458ac')
    ops(rom, 0x081451D6, 'ldr r2, [r1]', 'ldr r1, [r0]', 'adds r0, r2, #0',
        'bl #0x81458ac')
    ops(rom, 0x081458B4, 'adds r7, r1, #0')
    ops(rom, 0x0814596E, 'movs r0, #0x80', 'ldrb r1, [r7, #3]',
        'ands r0, r1', 'cmp r0, #0', 'beq #0x814597e')
    # This two-byte alternate entry is also the final return of the preceding
    # mixer routine. Its actual BL edge and entry instruction determine control.
    ops(rom, THUNK, 'bx r3')
    covering = sorted((int(x['rom'], 16), int(x['end'], 16)) for x in json.loads(mapping)
                      if int(x['rom'], 16) <= THUNK < int(x['end'], 16))
    indexed = [line.split() for line in index.decode().splitlines()
               if line.strip() and not line.lstrip().startswith('#')]
    text_covering = sorted((int(r[0], 16), int(r[1], 16)) for r in indexed
                           if int(r[0], 16) <= THUNK < int(r[1], 16))
    require(covering == text_covering == [(0x08144B2C, 0x08144D94), (THUNK, THUNK+2)],
            'alternate entry ownership')
    ops(rom, 0x08144DB6, 'ldr r3, [pc, #0x1c]', 'ldr r3, [r3]',
        'ldr r3, [r3, #0x2c]', 'bl #0x8144d84')
    ops(rom, 0x0814558E, 'ldr r0, [pc, #0x60]', 'str r5, [r0]')
    ops(rom, 0x0814542E, 'ldr r0, [pc, #0x9c]', 'ldr r4, [r0]')
    ops(rom, 0x081455AA, 'ldr r0, [pc, #0x50]', 'str r0, [r5, #0x28]', 'str r0, [r5, #0x2c]')
    ops(rom, 0x08145470, 'ldr r0, [pc, #0x8c]', 'str r0, [r4, #0x2c]')
    require(word(0x08144DD4) == word(0x081455F0) == word(0x081454CC) == 0x03007FF0 and word(0x081455FC) == CALLBACKS[0]+1
            and word(0x08145500) == CALLBACKS[1]+1, 'installed callback literal')


def preserved_aliases(functions):
    """Track the two actual incoming pointers through pushes, pops and every BL.

    An ordinary instruction may overwrite an alias and may never observe one.
    Private saves and plain register moves transport provenance. Sound code must
    never use incoming SP, even to form an address. A return joins all outcomes.
    """
    @lru_cache(None)
    def walk(address, entry):
        require(address in functions, 'unproved external call')
        ins, edges, calls = functions[address]
        seen = set()
        pending = [(address, entry, ())]
        returns = set()
        while pending:
            state = pending.pop()
            if state in seen:
                continue
            seen.add(state)
            require(len(seen) < 4096, 'sound provenance traversal budget')
            pc, tags, stack = state
            i = ins[pc]
            tags = set(tags)
            m = i.mnemonic
            operands = i.operands
            read, written = map(set, i.regs_access())
            if m in ('push', 'pop'):
                regs = tuple(o.reg for o in operands)
                if m == 'push':
                    stack = tuple(r in tags for r in regs) + stack
                else:
                    require(len(stack) >= len(regs), 'incoming stack read')
                    tags.difference_update(regs)
                    tags.update(r for r, tagged in zip(regs, stack) if tagged)
                    stack = stack[len(regs):]
            elif pc in calls:
                destination = calls[pc]
                targets = CALLBACKS if destination == THUNK and pc == 0x08144DBC else (destination,)
                # Each destination returns a possible superset of live aliases.
                tags = set().union(*(walk(t, frozenset(tags)) for t in targets))
            else:
                require(ARM_REG_SP not in read | written, 'explicit SP operation')
                if m == 'mov' and len(operands) == 2:
                    dst, src = (o.reg for o in operands)
                    tagged = src in tags
                    tags.discard(dst)
                    if tagged:
                        tags.add(dst)
                else:
                    require(not read & tags, f'private register observed at {pc:08X}')
                    tags.difference_update(written)
            successors = edges[pc]
            if pc == 0x08145976:
                require(set(successors) == {0x08145978, 0x0814597E}, 'reverb branch destinations')
                successors = (0x0814597E,)
            if not successors:
                require(not stack, 'unbalanced return')
                returns.update(tags)
            for target in successors:
                pending.append((target, frozenset(tags), stack))
        return frozenset(returns)

    # The installed callback bodies and all direct callees preserve R7. Within
    # the player R7 holds its original immutable song header until the test.
    player = functions[0x081458AC][0]
    require(all(ARM_REG_R7 not in i.regs_access()[1] for pc, i in player.items()
                if 0x081458B4 < pc <= 0x08145976), 'song header register overwritten')
    inputs = frozenset((ARM_REG_R5, ARM_REG_R6))
    for target in CALLS.values():
        require(walk(target, inputs) == inputs, 'sound call returned private scratch')


class TileSoundProof(runtime.RuntimeSummaryBufferProof):
    def bind_row(self, data, address, calls, bindings):
        require(address == ROOT and len(data) == 202 and sha256(data).hexdigest() ==
                'c5a8beb9ebaf6f4c0fdd75b2f61d2d26cbe339fb5837759b2bc22bf29503662c',
                'wrong root identity')
        require(all(calls.get(site) == target for site, target in CALLS.items()), 'sound bindings')
        names = formal.bind_calls(calls, self.mapping, address, len(data), len(self.rom))
        require(bindings == dict(calls=[[pc-address, name] for pc, name in sorted(names.items())],
                                 data=[], functions=[], switches=[]), 'source ELF relocations')
        native, _ = formal.verify(data, address, self.rom, self.mapping, self.index, calls,
                                  names, selector=formal.SELECTOR)
        functions, records = dependencies(self.rom, self.mapping, self.index)
        runtime_bindings(self.rom, self.mapping, self.index)
        caller = 0x080D8924
        owner.validate_span(self.rom[caller-BASE:0x080D89D0-BASE], caller, self.rom,
                            self.mapping, self.index)
        ops(self.rom, 0x080D8932, 'lsls r1, r1, #0x10', 'lsrs r1, r1, #0x10',
            'mov r8, r1', 'lsls r2, r2, #0x10', 'lsrs r2, r2, #0x10', 'adds r7, r2, #0',
            'cmp r7, #0', 'bne #0x80d8948', 'bl #0x80d8858', 'b #0x80d89be')
        preserved_aliases(functions)
        self.seen_sound = set()
        self.sound = dict(schema='thumb-tile-sound-8d-private-stack-v1',
            formal_stack_frame=native['frame'], bodies=records, song=SONG, reverb_byte=0,
            environment=environment_fingerprint(), original_caller=caller, caller_site=0x080D8942,
            outgoing_stack_word=4, owner_frame_bytes=48,
            formal_halfword_writes=formal.EFFECTS,
            mixer_slot=0x2c, mixer_pointer=0x03007FF0, alternate_entry=THUNK,
            installer_bodies=[[a,e,h] for a,(e,h) in INSTALLERS.items()],
            installed_targets=list(CALLBACKS),
            initialized_memory_premise='The mixer retains either original installed callback. Player, tracks and their channel lists refer to valid sound objects disjoint from the active stack.',
            call_effect='No explicit SP operand or read of saved local aliases. Each normal return restores entry frame and preserves exactly the two input aliases.')

    def check_call(self, address, aliases, stack, slots=None, *, constants=None, site=None, words=None):
        if site not in CALLS:
            return super().check_call(address, aliases, stack, slots,
                                      constants=constants, site=site, words=words)
        require(not self.active and address == CALLS[site] and
                aliases == {ARM_REG_R5: -32, ARM_REG_R6: -34} and slots == {-44: -32}
                and len(stack) == 12 and not words, 'unexpected owner stack or alias state')
        self.seen_sound.add(site)
        return {}

    def row_manifest(self):
        require(self.seen_sound == set(CALLS), 'incomplete audio-site coverage')
        return self.sound
