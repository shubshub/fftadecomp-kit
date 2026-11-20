"""The five child tasks, mode-six position and map-query scratch of USA 08104AEC."""
from hashlib import sha256
from pathlib import Path
from struct import unpack_from

import match
import cone_stack_footprint as cone
import named_data_buffer_profile as named
import function_thunk_profile as thunk
import scheduler_call_site_profile as sites
import scheduler_descriptor_lifetime as lifetime
import scheduler_event_definition as event
import scene_script_position as scene
import three_halfword_output_buffer_profile as three

SELECTOR = 'conditional-party-effect-scheduler-v1'
OWNER = 0x08104AEC
ROOT_SHA = '26e3b8c555dc9f5f7367f3884fc670b2f5322854a8bad626bf6cafbb98792fde'
REGISTER, CALLBACK = 0x08104F08, 0x0810493C
QUERY = 0x0801CC7C
QUERIES = {0x08104BD2, 0x08104C46, 0x08104DE4, 0x08104E62}
R2 = match.ARM_REG_R2
END = {QUERY: 0x0801CD06, 0x0801CC18: 0x0801CC38, 0x0801CD08: 0x0801CD28}
SCRIPT = 0x08104CEA
SCENE_WORD = 0x0839F720


def require(condition, message):
    if not condition:
        raise ValueError('party effect: ' + message)


def entry_kill(instructions, edges, calls, start):
    pc = start
    prefix = []
    while len(prefix) < 32:
        item = instructions[pc]
        reads, writes = item.regs_access()
        require(pc not in calls and R2 not in reads and
                edges[pc] == (pc + item.size,), 'incoming R2 observed before its overwrite')
        prefix.append(pc)
        if R2 in writes:
            require((item.mnemonic, item.op_str) in (('adds', 'r2, r4, #0'), ('ldrb', 'r2, [r3, #8]')),
                    'unexpected R2 overwrite')
            return prefix
        pc += item.size
    raise ValueError('map helper has no bounded R2 overwrite')


def consumer(instructions, edges, calls, first, entry_kills):
    """Trace both successors, stopping at an actual overwrite, including a proven callee prefix."""
    pending, seen, cuts = [first], set(), {}
    while pending:
        pc = pending.pop()
        if pc in seen:
            continue
        seen.add(pc)
        item = instructions[pc]
        if pc in calls:
            target = calls[pc]
            require(target in entry_kills, 'expired R2 reaches an unchecked call')
            cuts[pc] = entry_kills[target][-1]
            continue
        reads, writes = item.regs_access()
        require(R2 not in reads and edges[pc] and match.CS_GRP_INT not in item.groups,
                'expired query R2 is observed before its overwrite')
        if R2 in writes:
            cuts[pc] = pc
        else:
            pending.extend(edges[pc])
    require(cuts, 'query R2 never reaches a checked overwrite')
    return dict(inspected=sorted(seen), overwrites=sorted(cuts.items()))


def map_scratch(proof, instructions, edges, calls):
    graphs = {addr: cone.native_graph(proof, addr, END) for addr in END}
    kills = {addr: entry_kill(row[1], row[2], row[3], addr) for addr, row in graphs.items()}
    data, _, _, nested = graphs[QUERY]
    verifier = named.RootReturnScratchBufferProof(proof.rom, proof.mapping, proof.index, proof.objects)
    verifier.bind_return_root(QUERY, data)
    match.verify_leaf_instructions(data, QUERY, True, nested, buffer_proof=verifier)
    receipt = verifier.root_scratch_manifest()
    require(sha256(data).hexdigest() == '4525b72830d12a86414a578da0d8ddcc256d25ec0a69c08c84d6b70198fc8690'
            and receipt['observations'] == [[136, 2, -35]] and not receipt['dead_joins']
            and nested == {0x0801CCAA: 0x0801CD4C}, 'query frame certificate changed')
    for address, (_, instructions_, edges_, calls_) in graphs.items():
        accessed, depths, _ = cone.stack_sites(address, instructions_, edges_, calls_)
        require(not any(off >= 0 for _,off in accessed.values()), 'map query reads a caller stack word')
        if address == QUERY:
            require(depths == {0x0801CCAA:-36}, 'map-query local/output frame changed')
    require({pc for pc, target in calls.items() if target == QUERY} == QUERIES, 'map-query BL sites differ')
    return dict(callee=receipt, nested_bodies={a:sha256(b).hexdigest() for a,b in verifier.dependencies.items()},
                entry_overwrites=kills, continuations={pc:consumer(instructions, edges, calls, pc+4, kills)
                                                       for pc in sorted(QUERIES)})


def children(proof, data, edges):
    wrapper, core = proof.span(event.WRAPPER), proof.span(event.CORE)
    require(wrapper[:30] == lifetime.WRAPPER_HEAD and wrapper[34:56] == lifetime.WRAPPER_TAIL
            and core[:34] == lifetime.CALLEE_HEAD and core[154:180] == lifetime.COPY+lifetime.CALL_SETUP
            and core[184:] == lifetime.CALLEE_RETURN and proof.span(event.THUNK) == bytes.fromhex('1847'),
            'scheduler lost its forwarding, seven-word copy or restoration')
    event.sequence(wrapper, event.WRAPPER, event.WRAPPER+30, ['bl #0x8005954'])
    event.sequence(core, event.CORE, event.CORE+180, ['bl #0x8142250'])
    event.check_payload_argument(core, proof.mapping)
    event.sequence(data, OWNER, 0x08104EF4, [
        'movs r4, #0', 'ldr r5, [sp, #0x50]', 'strh r4, [r5, #0x14]', 'mov r3, r8',
        'ldrb r0, [r3, #1]', 'strh r0, [r5, #0x16]', 'ldr r0, [pc, #0x38]', 'movs r1, #0x28',
        'adds r2, r5, #0', 'ldr r3, [sp, #0x44]', 'bl #0x8005b6c', 'lsls r1, r4, #2',
        'ldr r2, [sp, #0x54]', 'adds r1, r2, r1', 'str r0, [r1]', 'adds r0, r4, #1',
        'lsls r0, r0, #0x18', 'lsrs r4, r0, #0x18', 'cmp r4, #4', 'bls #0x8104ef8'])
    require(all(dst == 0x08104EF4 or 0x08104EF4 <= src <= 0x08104F1C
                for src, targets in edges.items() for dst in targets if 0x08104EF4 <= dst <= 0x08104F1C),
            'registration loop bypasses induction initialization')
    cb = proof.span(CALLBACK)
    require(len(cb) == 432 and unpack_from('<I', data, 0x08104F3C-OWNER)[0] == CALLBACK|1,
            'registration callback literal differs')
    event.sequence(cb, CALLBACK, CALLBACK, [
        'push {r4, r5, r6, r7, lr}', 'mov r7, sb', 'mov r6, r8', 'push {r6, r7}', 'sub sp, #0x10',
        'mov r8, r1', 'adds r7, r2, #0', 'ldrh r1, [r1]', 'movs r0, #0x80', 'lsls r0, r0, #1',
        'cmp r1, r0', 'beq #0x8104990', 'cmp r1, r0', 'bgt #0x810495e', 'cmp r1, #0', 'beq #0x8104974'])
    event.sequence(cb, CALLBACK, 0x08104974, [
        'mov r1, r8', 'ldrh r0, [r1, #0x14]', 'strb r0, [r7, #7]', 'ldrh r0, [r1, #0x16]',
        'strb r0, [r7, #6]', 'ldr r1, [pc, #0xc]', 'ldrb r0, [r7, #7]', 'adds r0, r0, r1',
        'ldrb r0, [r0]', 'adds r0, #1', 'strh r0, [r7, #4]', 'b #0x8104adc'])
    event.sequence(cb, CALLBACK, 0x08104ADC, ['movs r0, #0', 'add sp, #0x10', 'pop {r3, r4}',
        'mov r8, r3', 'mov sb, r4', 'pop {r4, r5, r6, r7}', 'pop {r1}', 'bx r1'])
    table = unpack_from('<I', cb, 0x0810498C-CALLBACK)[0]
    require(table == 0x0839F75C, 'unexpected duration table')
    timers = [proof.rom[table-match.ROM_BASE+i]+1 for i in range(5)]
    return dict(site=REGISTER, callback=CALLBACK, callback_sha256=sha256(cb).hexdigest(),
                indices=list(range(5)), descriptor_bytes=28, payload_bytes=40, allocated_bytes=68,
                descriptor_halfword_reads=[0,20,22], payload_writes=[[7,1],[6,1],[4,2]], timers=timers,
                callback_returns=0, callback_retains_descriptor=False, scheduler_disposes_copy=True)


def scene_position(proof, data):
    # R3=6 chooses the same arm for either value of the independent count in R2.
    event.sequence(data, OWNER, 0x08104CD6, [
        'str r0, [sp, #0x40]', 'mov r1, r8', 'ldr r0, [r1, #0x2c]', 'ldr r1, [pc, #0x48]',
        'mov r2, sl', 'str r2, [sp]', 'ldr r3, [sp, #0x44]', 'str r3, [sp, #4]',
        'ldr r2, [sp, #0x4c]', 'movs r3, #6', 'bl #0x80e03f8'])
    require(unpack_from('<I', data, 0x08104D28-OWNER)[0] == SCENE_WORD, 'wrong scene script')
    bodies = {}
    for addr, digest in scene.CALLEES.items():
        body = proof.span(addr)
        require(sha256(body).hexdigest() == digest, 'changed scene native dependency')
        bodies[addr] = body
    b, h = bodies[scene.helper.ADDRESS], scene.helper.ADDRESS
    require(b == scene.common.HELPER, 'changed scene switch or fallthrough')
    event.sequence(b, h, h, ['push {r4, r5, r6, r7, lr}', 'sub sp, #0x34', 'adds r6, r0, #0',
        'adds r4, r1, #0', 'ldr r5, [sp, #0x48]', 'lsls r2, r2, #0x18', 'lsrs r2, r2, #0x18',
        'lsls r3, r3, #0x18', 'lsrs r3, r3, #0x18', 'cmp r2, #0', 'bne #0x80e0416',
        'cmp r3, #7', 'bne #0x80e0416'])
    event.sequence(b, h, 0x080E0430, ['cmp r3, #6', 'bhi #0x80e04f2', 'lsls r0, r3, #2',
        'ldr r1, [pc, #0x10]', 'adds r0, r0, r1', 'ldr r0, [r0]', 'mov pc, r0'])
    require(unpack_from('<I', b, 0x50)[0] == 0x080E044C and
            unpack_from('<I', b, 0x080E044C+24-h)[0] == 0x080E04D4, 'wrong mode-six slot')
    event.sequence(b, h, 0x080E04D4, ['movs r1, #0', 'ldrsh r0, [r5, r1]', 'movs r2, #2',
        'ldrsh r1, [r5, r2]', 'bl #0x80d8b28', 'lsls r0, r0, #0x18', 'cmp r0, #0',
        'beq #0x80e04f2'])
    event.sequence(b, h, 0x080E04F2, ['str r7, [sp, #8]', 'ldr r0, [pc, #0x1c]', 'ldr r0, [r0]',
        'ldr r1, [pc, #0x1c]', 'ldr r2, [sp, #0x4c]', 'str r2, [sp]', 'movs r2, #0xc',
        'add r3, sp, #4', 'bl #0x8005954', 'add sp, #0x34', 'pop {r4, r5, r6, r7}',
        'pop {r1}', 'bx r1'])
    require(unpack_from('<III', b, 280) == (0xFFFF0000, 0x0200F430, scene.CALLBACK|1) and
            scene.thumb_call(bodies[scene.PREDICATE], scene.PREDICATE, 18) == scene.GEOMETRY,
            'scene geometry or direct scheduler callback differs')
    # Use a separate dependency view: the generic named-buffer evidence retains its own records.
    from types import SimpleNamespace
    dispatch = scene.scheduler_callback(SimpleNamespace(span=proof.span, dependencies=bodies))
    return dict(site=SCRIPT, dispatch_value=6, pointer_word=0, parent_word=4,
                helper_frame_bytes=72, signed_halfword_reads=[[0x080E04D6,0],[0x080E04DA,2]],
                scene_script=SCENE_WORD, nested_callback=dispatch, bodies=scene.CALLEES)


def nested_sequence(proof):
    import owner_admission_profile as owner
    target = 0x080DFD8C
    data = proof.span(target)
    bindings = dict(calls=[[60, 'func_08005B6C']], functions=[[72, 'func_080DFB0C']], data=[], switches=[])
    manifest, _ = owner.verify(data, target, proof.rom, proof.mapping, proof.index, proof.objects,
                               bindings=bindings, selector='conditional-scheduler-descriptor-payload-calls-v1')
    event.sequence(data, target, target, ['push {r4, lr}', 'sub sp, #0x28'])
    event.sequence(data, target, 0x080DFDBE, ['str r2, [sp, #4]', 'ldr r0, [pc, #0x10]',
        'movs r1, #0x10', 'mov r2, sp', 'ldr r3, [sp, #0x30]', 'bl #0x8005b6c',
        'add sp, #0x28', 'pop {r4}', 'pop {r1}', 'bx r1'])
    return dict(address=target, sha256=sha256(data).hexdigest(), incoming_parent_word=0,
                registration=manifest['proof']['buffers']['conditional_local_calls'])


MEMBER = 0x080DE268
MATERIALIZING = {0x0801CC7C, 0x080213DC, 0x08021618, 0x08006E28, 0x08006EC0, 0x0809801C}


def member_frame(address, instructions, edges, calls):
    """Track the actual SP at each instruction, exact direct accesses and derived pointers."""
    depths, pending, memory, children, materialized = {address:0}, [address], [], [], []
    while pending:
        pc = pending.pop()
        i, depth = instructions[pc], depths[pc]
        if i.mnemonic in ('push', 'pop'):
            width = 4*len(i.operands)
            require(width and all(op.type == match.ARM_OP_REG for op in i.operands), 'irregular register list')
            start = depth-width if i.mnemonic == 'push' else depth
            memory.append((pc, start, width))
            depth += -width if i.mnemonic == 'push' else width
        elif (adjustment := match.thumb_stack_adjustment(i)) is not None:
            depth += 4*adjustment
        else:
            require(match.ARM_REG_SP not in i.regs_access()[1], 'unknown stack adjustment')
            if pc in calls:
                children.append((pc, calls[pc], depth))
            for op in i.operands:
                if op.type == match.ARM_OP_REG and op.reg == match.ARM_REG_SP:
                    require(address in MATERIALIZING, 'unreviewed materialized local pointer')
                    if i.mnemonic == 'mov' and len(i.operands) == 2 and i.operands[1].reg == match.ARM_REG_SP:
                        displacement = 0
                    elif i.mnemonic == 'add' and len(i.operands) == 3 and i.operands[1].reg == match.ARM_REG_SP:
                        if i.operands[2].type == match.ARM_OP_IMM:
                            displacement = i.operands[2].imm
                        else:
                            require(pc == 0x0801CC96 and i.op_str == 'r0, sp, r0'
                                    and instructions[pc-2].bytes.hex() == '0120'
                                    and all(src == pc-2 for src,out in edges.items() if pc in out),
                                    'unbounded SP-derived register displacement')
                            displacement = 1
                    else:
                        raise ValueError('unreviewed use of SP as a data register')
                    materialized.append((pc, depth+displacement))
                if op.type != match.ARM_OP_MEM:
                    continue
                require(op.mem.index != match.ARM_REG_SP, 'unbounded SP index')
                if op.mem.base == match.ARM_REG_SP:
                    require(not op.mem.index and int.from_bytes(i.bytes, 'little') & 0xf000 == 0x9000
                            and i.mnemonic in ('ldr','str'), 'non-immediate SP access')
                    memory.append((pc, depth+op.mem.disp, 4))
        require(-4096 <= depth <= 0 and (edges[pc] or depth == 0), 'unbalanced member-helper frame')
        for dest in edges[pc]:
            if dest not in depths:
                depths[dest] = depth
                pending.append(dest)
            else:
                require(depths[dest] == depth, 'member-helper frame depth differs at join')
    require(set(depths) == set(instructions), 'incomplete member-helper frame graph')
    return memory, children, materialized


def member_footprint(proof):
    """Check every immediate stack access against the caller's live word at SP."""
    native = named.NamedDataBufferProof(proof.rom, proof.mapping, proof.index, proof.objects)
    entries = {int(row['rom'],16):int(row['end'],16) for row in native.entries}
    summaries, hashes, pending = {}, {}, [MEMBER]
    while pending:
        address = pending.pop()
        if address in summaries or thunk.reserved(address):
            continue
        require(len(summaries) < 75, 'member-helper closure exceeds its actual native bodies')
        body, ins, edges, calls = cone.native_graph(native, address, entries)
        summaries[address] = member_frame(address, ins, edges, calls)
        hashes[address] = sha256(body).hexdigest()
        pending.extend(calls.values())
    require(len(summaries) == 75, 'member-helper closure changed')
    # Use the highest (least deeply stacked) entry to cover every dynamic path, including cycles.
    starts, work = {MEMBER:0}, [MEMBER]
    while work:
        address = work.pop()
        for pc, child, depth in summaries[address][1]:
            candidate = starts[address]+depth
            if child not in starts or candidate > starts[child]:
                starts[child] = candidate
                if child in summaries:
                    work.append(child)
    records, indirect, derived = [], [], []
    for address,(memory, children, materialized) in sorted(summaries.items()):
        base = starts[address]
        high = max((base+offset+width for _,offset,width in memory), default=None)
        require(high is None or high <= 0, 'native SP access overlaps the live outgoing point word')
        derived.extend([pc,base+offset] for pc,offset in materialized)
        indirect.extend([pc,child,base+depth] for pc,child,depth in children if thunk.reserved(child))
        records.append([address,hashes[address],base,high,len(memory)])
    names = {name for name,address in thunk.ALIASES.items() if address in starts}
    runtime = thunk.dependencies(sorted(names), proof.rom)
    require(len(derived) == 18 and len(indirect) == 7 and len(runtime) == 4 and
            all(depth <= -16 for _,depth in derived) and all(depth <= -16 for _,_,depth in indirect),
            'changed transitive stack or thunk boundary')
    return dict(owner=MEMBER, checked_owners=records, native_derived_SP=sorted(derived),
                indirect_sites=sorted(indirect), runtime=runtime, outgoing_word=[0,4],
                obligations=['An address derived inside each identified deeper frame stays within its '
                    'live local storage when used as a data pointer. Non-SP memory operands refer '
                    'to their actual valid objects, disjoint from the root caller frame.',
                    'The seven indirect sites obey returning ARM ABI and do not access the root '
                    'caller through ambient registers, raw RAM aliases, or an unpassed ancestor SP word.'])


def bind(proof, data, address, ins, edges, calls):
    require(address == OWNER and len(data) == 1366 and sha256(data).hexdigest() == ROOT_SHA,
            'requires the complete party-effect owner')
    proof.callee_frames = True
    proof.exact_alias_state_budget = 4096
    proof.dependency_budget = 48
    proof.party_three = three.ThreeOutputBufferProof(proof.rom, proof.mapping, proof.index, proof.objects)
    require(proof.scheduler_call_sites['looped_sites'] == [REGISTER], 'unexpected registration SCC')
    proof.party = dict(map_query=map_scratch(proof, ins, edges, calls), child_tasks=children(proof, data, edges),
                      mode_six=scene_position(proof, data), sequence_constructor=nested_sequence(proof),
                      member_footprint=member_footprint(proof))
    proof.party_sites = set()


def register(proof, aliases, stack, slots, site):
    base = -4*len(stack)
    r = match.ARM_REG_R0
    require(site == REGISTER and base == -124 and [i for i,w in enumerate(stack) if w[2]] == list(range(23)),
            'bad party scheduler frame')
    require(aliases == {r+2:-100,r+5:-100,r+6:-62,r+7:-72,r+9:-64,r+10:-68}
            and slots == {-124:-64,-120:-62,-44:-100,-36:-70}, 'changed preserved or outgoing frame aliases')
    for offset in range(-100,-72,4):
        proof.access(offset,4,stack)
    proof.observations[site] = dict(site=site,target=event.WRAPPER,looped=True,descriptor_offset=-100,
        descriptor_bytes=28,frame_bytes=124,aliases=sorted(aliases.items()),other_pointer_words=sorted(slots.items()),
        scheduler_entry=proof.scheduler_call_sites['sites'][0]['scheduler_entry'],payload_words=[])
    return {}


def check_bindings(bindings):
    names = {0x08104D28: 'data_0839F720', 0x08105008: 'data_0839F738',
             0x08104D84: 'data_0839F74C', 0x08104F40: 'data_0839F754'}
    require(bindings['functions'] == [[0x08104F3C-OWNER,'func_0810493C']] and not bindings['switches']
            and bindings['data'] == [[p-OWNER,n,0] for p,n in sorted(names.items())],
            'source callback or original data relocations differ')


def check_special(proof, address, aliases, stack, slots, constants, site):
    r = match.ARM_REG_R0
    slots = slots or {}
    if site == REGISTER:
        return register(proof, aliases, stack, slots, site)
    if address == three.WRAPPER[0]:
        require(site == 0x08104B88, 'unreviewed three-output call')
        result = proof.party_three.check_call(address, aliases, stack, slots, site=site)
        proof.party_sites.add(site)
        return result
    if site in QUERIES:
        supplied = {reg:value for reg,value in aliases.items() if reg in match.CALLER_CLOBBERED}
        require(supplied in ({},{R2:-100}) and (not slots or slots == {-44:-100,-36:-70}),
                'unexpected pointer flow into map query')
        proof.party_sites.add(site)
        return {}
    if site == SCRIPT:
        require(len(stack)*4 == 124 and slots == {-124:-60} and not set(aliases).intersection(match.CALLER_CLOBBERED)
                and constants.get(r+3) == 6, 'mode-six requires the external parent and private scalar point')
        for offset in (-60,-58):
            proof.access(offset,2,stack)
        proof.party_sites.add(site)
        return {}
    if address == 0x080DFD8C:
        require(site in (0x08104D6E,0x08104F2A) and not set(aliases).intersection(match.CALLER_CLOBBERED)
                and -4*len(stack) not in slots, 'sequence constructor receives a local parent or register')
        proof.party_sites.add(site)
        return {}
    if site == 0x08104D0E:
        require(not set(aliases).intersection(match.CALLER_CLOBBERED) and slots == {-124:-60},
                'unexpected member-helper stack input')
        proof.party_sites.add(site)
        return {}
    return None


def finish(proof, manifest):
    require({SCRIPT, 0x08104B88, 0x08104D0E, 0x08104F2A, 0x08104DE4, 0x08104E62} <= proof.party_sites,
            'missing party-effect native projection')
    manifest['assumptions'] = [line for line in manifest['assumptions']
                               if not line.startswith(('Every scheduler invocation', 'Every other call'))]
    manifest['assumptions'].append('Each of the five child registrations has its own 28-byte descriptor '
        'copy, synchronous phase-zero callback and release as checked below. The scheduler allocator, '
        'parent/list prefix, external object accesses, ordinary and indirect callees require valid '
        'disjoint storage, returning ABI and noninterference with the caller frame. The mode-six '
        'geometry and nested sequence calls retain their named conditional effects. All remaining '
        'calls use the ordinary named-buffer checks.')
    manifest['party_effect'] = dict(**proof.party, three_outputs=proof.party_three.nested_manifest(),
        source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        producer_sha256={module.__name__:sha256(Path(module.__file__).read_bytes()).hexdigest()
                         for module in (cone, named, thunk, sites, lifetime, event, scene, three)})
    return manifest
