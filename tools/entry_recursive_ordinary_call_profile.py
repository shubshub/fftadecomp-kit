"""Explicit proof primitive for an exact-entry ordinary conditional ABI call.

This is not a native admission selector or a termination proof. Original ELF
binding, linking, source recompilation and report replay must still be wired
before any caller can record a match. No DEFAULT call binding changes here.
The narrow owner has saved registers only, no local stack objects, outgoing
words, incoming stack formals, stack-address materialization or memory stores.
Unknown incoming object pointers and ordinary helper effects stay unknown.
"""
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
from refusal import Refusal

from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB, CS_GRP_CALL, CS_GRP_JUMP
from capstone.arm import (ARM_OP_IMM, ARM_OP_MEM, ARM_OP_REG, ARM_CC_AL,
                          ARM_CC_INVALID, ARM_REG_SP, ARM_REG_PC, ARM_REG_R0,
                          ARM_REG_R12)

SELECTOR = 'entry-recursive-ordinary-call-v1'
SCHEMA = 'thumb-exact-entry-ordinary-conditional-call-v1'
CONTRACT = ('conditional ordinary ARM ABI normal return; caller-clobbered results and '
            'helper memory effects unknown; no termination, recursion-depth, physical '
            'stack-capacity, object-readability, nonalias or helper-semantics theorem')


def _digest(data):
    return hashlib.sha256(data).hexdigest()


def _indices(data, address, mapping, index, rom_size):
    from match import ROM_BASE
    if type(data) is not bytes or not data or len(data) % 2 or type(address) is not int or address % 2 or \
            type(mapping) is not bytes or type(index) is not bytes or type(rom_size) is not int or \
            not ROM_BASE <= address < address + len(data) <= ROM_BASE + rom_size:
        raise ValueError('entry call requires its complete even Thumb owner and both raw indexes')
    entries = json.loads(mapping)
    if type(entries) is not list:
        raise ValueError('entry call mapping must be a list')
    owners = [e for e in entries if int(e['rom'], 16) & ~1 == address]
    end = address + len(data)
    if len(owners) != 1 or int(owners[0]['rom'], 16) != address or \
            owners[0].get('mode') != 'thumb' or int(owners[0]['end'], 16) != end or any(
                e is not owners[0] and int(e['rom'], 16) < end and int(e['end'], 16) > address
                for e in entries):
        raise ValueError('entry call owner is not exact, unique and nonoverlapping')
    rows = [line.split() for line in index.decode('utf-8').splitlines()
            if line.strip() and not line.lstrip().startswith('#')]
    owners = [r for r in rows if int(r[0], 16) & ~1 == address]
    if len(owners) != 1 or len(owners[0]) < 3 or int(owners[0][0], 16) != address or \
            int(owners[0][1], 16) != end or int(owners[0][2]) != len(data) or any(
                r is not owners[0] and int(r[0], 16) < end and int(r[1], 16) > address
                for r in rows):
        raise ValueError('entry call text index differs from the complete unique owner')
    return entries


def _decode(data, address):
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    decoder.detail = True
    result = {i.address: i for i in decoder.disasm(data, address)}
    cursor = address
    for site, instruction in result.items():
        if site != cursor:
            raise Refusal('entry owner has an undecoded gap')
        cursor += instruction.size
    if cursor != address + len(data):
        raise Refusal('entry owner has an undecoded tail')
    return result


def _call_target(instruction):
    ops = instruction.operands
    if instruction.mnemonic != 'bl' or instruction.size != 4 or \
            instruction.cc not in (ARM_CC_AL, ARM_CC_INVALID) or len(ops) != 1 or ops[0].type != ARM_OP_IMM:
        raise ValueError('entry owner permits only ordinary direct Thumb BL calls')
    raw = bytes(instruction.bytes)
    first, second = int.from_bytes(raw[:2], 'little'), int.from_bytes(raw[2:], 'little')
    delta = ((first & 0x7ff) << 12) | ((second & 0x7ff) << 1)
    if delta & 0x400000:
        delta -= 0x800000
    if first & 0xf800 != 0xf000 or second & 0xf800 != 0xf800 or \
            instruction.address + 4 + delta != ops[0].imm:
        raise ValueError('entry call requires authentic complete canonical Thumb encoding')
    return ops[0].imm


def _edges(instructions, calls):
    edges = {}
    for site, instruction in instructions.items():
        if site in calls:
            successors = (site + instruction.size,)
        elif instruction.mnemonic == 'bx':
            successors = ()
        elif instruction.group(CS_GRP_JUMP):
            if len(instruction.operands) != 1 or instruction.operands[0].type != ARM_OP_IMM:
                raise ValueError('entry owner excludes indirect nonreturn control flow')
            successors = (instruction.operands[0].imm,)
            if instruction.cc not in (ARM_CC_AL, ARM_CC_INVALID):
                successors += (site + instruction.size,)
        else:
            successors = (site + instruction.size,)
        if any(target not in instructions for target in successors):
            raise ValueError('entry CFG edge leaves a complete decoded boundary')
        edges[site] = successors
    return edges


@dataclass(frozen=True)
class EntryCalls:
    data: bytes
    address: int
    mapping: bytes
    index: bytes
    rom_size: int
    calls: tuple

    def validate_bytes(self, data, address, calls):
        fresh = prepare(self.data, self.address, self.mapping, self.index,
                        self.rom_size, selector=SELECTOR)
        if type(data) is not bytes or data != self.data or address != self.address or \
                self.calls != fresh.calls or type(calls) is not dict or calls != dict(self.calls):
            raise ValueError('entry context differs from exact owner bytes or complete calls')

    def validate_cfg(self, instructions, edges, address, calls):
        fresh = prepare(self.data, self.address, self.mapping, self.index,
                        self.rom_size, selector=SELECTOR)
        if address != self.address or self.calls != fresh.calls or calls != dict(self.calls) or \
                set(instructions) != set(_decode(self.data, self.address)) or any(
                    bytes(i.bytes) != self.data[site-address:site-address+i.size]
                    for site, i in instructions.items()) or edges != _edges(instructions, calls):
            raise ValueError('entry context differs from exact owner bytes, calls or continuation CFG')
        return {site for site, target in self.calls if target == address}

    @staticmethod
    def check_instruction(instruction, registers=None):
        # No stack aliases can be constructed, spilled, passed, or forgotten in
        # this closed saved-only subcase. The existing frame proof checks saves.
        read, written = instruction.regs_access()
        if registers is not None:
            return_reads = {reg for reg in read if registers.get(reg) == ('entry-return',)}
            is_restored_return = (instruction.mnemonic == 'bx' and len(instruction.operands) == 1 and
                                  instruction.operands[0].type == ARM_OP_REG and
                                  return_reads == {instruction.operands[0].reg})
            if return_reads and instruction.mnemonic != 'push' and not is_restored_return:
                raise ValueError('entry-return provenance cannot be transformed or exposed outside saves and final BX')
        if instruction.mnemonic not in ('push', 'pop') and (
                ARM_REG_SP in read or ARM_REG_SP in written or any(
                    op.type == ARM_OP_REG and op.reg == ARM_REG_SP for op in instruction.operands)):
            raise ValueError('entry saved-only owner excludes local frames and stack-address materialization')
        if instruction.mnemonic.startswith(('str', 'stm', 'ldm')):
            raise ValueError('entry saved-only owner excludes memory stores and register-list transfers')
        for op in instruction.operands:
            if op.type == ARM_OP_MEM and (instruction.mnemonic != 'ldr' or instruction.size != 2 or
                    op.mem.base in (ARM_REG_SP, ARM_REG_PC) or op.mem.index or instruction.writeback):
                raise Refusal('entry owner permits only ordinary object-word loads without stack or PC provenance')
        if instruction.mnemonic == 'pop' and any(
                op.type == ARM_OP_REG and op.reg == ARM_REG_PC for op in instruction.operands):
            raise ValueError('entry saved-only owner requires an explicit restored-register BX return')

    @staticmethod
    def check_call(registers, stack):
        argument_registers = (*range(ARM_REG_R0, ARM_REG_R0 + 4), ARM_REG_R12)
        if any(registers.get(reg) == ('entry-return',) for reg in argument_registers) or \
                any(kind != 'saved' for kind, value in stack):
            raise ValueError('entry ordinary call carries entry-return provenance or outgoing local words')

    def record(self):
        return {'schema':SCHEMA, 'selector':SELECTOR, 'address':self.address,
                'size':len(self.data), 'body_sha256':_digest(self.data),
                'mapping_sha256':_digest(self.mapping), 'index_sha256':_digest(self.index),
                'calls':[[site-self.address, target] for site,target in self.calls],
                'contract':CONTRACT, 'native_admission':False}


def prepare(data, address, mapping, index, rom_size, *, selector):
    import match
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('entry calls require their exact explicit selector')
    entries = _indices(data, address, mapping, index, rom_size)
    instructions = _decode(data, address)
    calls = {}
    for site, instruction in instructions.items():
        EntryCalls.check_instruction(instruction)
        if instruction.group(CS_GRP_CALL):
            target = _call_target(instruction)
            if target != address:
                target = match.function_address_target(f'func_{target:08X}', entries, address, len(data), rom_size)
            calls[site] = target
    if sum(target == address for target in calls.values()) != 1:
        raise ValueError('entry owner requires exactly one authentic call to its exact own entry')
    _edges(instructions, calls)
    return EntryCalls(data, address, mapping, index, rom_size, tuple(sorted(calls.items())))


def prove(data, address, mapping, index, rom_size, *, selector):
    """Prove the synthetic/native machine primitive, never record source admission."""
    import match
    import local_long_branch_profile as local
    context = prepare(data, address, mapping, index, rom_size, selector=selector)
    calls = dict(context.calls)
    reached = match.verify_leaf_instructions(data, address, True, calls, entry_recursive_calls=context)
    instructions = {i.address:i for i in reached}
    if sum(i.size for i in reached) != len(data):
        raise ValueError('entry owner must consist exclusively of complete reached instructions')
    frame = local.prove_frame(instructions, _edges(instructions, calls), address, {}, calls,
                              entry_recursive_calls=context)
    result = context.record()
    result['frame'] = frame
    result['producers'] = {Path(path).name:_digest(Path(path).read_bytes())
                           for path in (__file__, match.__file__, local.__file__)}
    return result


# Native source admission is distinct from the unchanged machine primitive above.
NATIVE_SCHEMA = 'elf-symbol-thumb-entry-recursive-ordinary-v1'
CONTROL_FLOW = 'complete saved-only Thumb owner; exact entry call with conditional ordinary ABI continuation'


def environment_fingerprint():
    """Bind current producers, selected binary contents and actual Python runtime."""
    import importlib
    import owner_graph_profile
    from addressed_signed_runtime_profile import toolchain_fingerprint, runtime_fingerprint
    paths = {path.name:path for path in Path(owner_graph_profile.__file__).parent.glob('*.py')}
    for name in ('match', 'match_evidence', 'owner_admission_profile',
                 'local_long_branch_profile', __name__, 'static_callback_target_preservation_profile'):
        path = Path(importlib.import_module(name).__file__)
        paths[path.name] = path
    return {'producers':{name:_digest(path.read_bytes()) for name,path in sorted(paths.items())},
            'toolchain':toolchain_fingerprint(), 'runtime':runtime_fingerprint()}


def function_size(image, address):
    """Only the complete resident FUNC plus optional exact compiler NOP alignment."""
    import re
    import match
    match.allocated_text_only(image)
    symbol, offset = match.function_record(image, f'func_{address:08X}', address, True)
    size = symbol['size']
    section = image['sections'][image['text_index']]
    base = address if image['type'] == 2 else 0
    if offset or size % 2 or symbol['bind'] != 1 or len(image['symbol_tables']) != 1 or \
            section[3] != base or section[5] != len(image['text']):
        raise ValueError('entry admission requires one resident complete Thumb FUNC at section start')
    tail = image['text'][size:]
    if tail and (size % 4 != 2 or address % 4 or tail != b'\xc0\x46' or section[8] != 4):
        raise ValueError('entry admission permits only exact terminal compiler NOP alignment')
    for item in image['symbols']:
        if re.fullmatch(r'\$a(?:\..*)?', item['name']):
            raise ValueError('entry owner excludes ARM mapping symbols')
        if item is symbol or item['section'] != image['text_index']:
            continue
        position = (item['value'] & ~1) - base
        if item['type'] in (1, 2) or position < 0 or position >= size or position + item['size'] > size:
            raise ValueError('entry owner contains foreign function, object or alignment label')
    instructions = _decode(image['text'][:size], address)
    for instruction in instructions.values():
        EntryCalls.check_instruction(instruction)
        if instruction.group(CS_GRP_JUMP) or instruction.group(CS_GRP_CALL):
            if any(op.type == ARM_OP_IMM and address+size <= op.imm < address+len(image['text'])
                   for op in instruction.operands):
                raise ValueError('entry owner references terminal alignment')
    return size


def original_bindings(image, address, rom, mapping, index):
    """Bind defined-self REL or assembler-resolved BL without an absolute alias."""
    import struct
    import match
    from software_double_profile import indices, span_record
    if image['type'] != 1:
        raise ValueError('entry admission requires original relocatable ELF')
    size = function_size(image, address)
    entries, rows = indices(mapping, index)
    span_record(address, address+size, entries, rows, rom)
    instructions = _decode(image['text'][:size], address)
    root = match.function_record(image, f'func_{address:08X}', address, True)[0]
    relocations = {}
    targets = {}
    for section_index in image['relocations']:
        section = image['sections'][section_index]
        if section[1] != 9 or section[7] != image['text_index'] or section[9] != 8 or section[5] % 8:
            raise ValueError('entry admission requires canonical text REL calls only')
        symbols = image['symbol_tables'].get(section[6])
        for position in range(0, section[5], 8):
            site, info = struct.unpack_from('<II', image['section_data'][section_index], position)
            instruction = instructions.get(address+site)
            if symbols is None or info >> 8 >= len(symbols) or info & 255 != 10 or \
                    site % 2 or site+4 > size or site in relocations or instruction is None or \
                    _call_target(instruction) != address+site:
                raise ValueError('entry relocation requires a complete zero-addend canonical BL')
            target = symbols[info >> 8]
            name = target['name']
            if target is root:
                destination = address
            else:
                if target['section'] or target['value'] or target['bind'] != 1 or \
                        target['type'] not in (0, 2) or \
                        sum(item['name'] == name for item in image['symbols']) != 1:
                    raise ValueError('entry external call requires a unique undefined zero-valued global')
                destination = match.function_address_target(name, entries, address, size, len(rom))
            relocations[site] = name
            targets[name] = (destination, False)
    calls = []
    resolved = []
    for site, instruction in instructions.items():
        if not instruction.group(CS_GRP_CALL):
            continue
        offset = site-address
        destination = _call_target(instruction)
        if offset in relocations:
            name = relocations[offset]
        else:
            if destination != address:
                raise ValueError('unrelocated entry owner call must resolve to its exact resident entry')
            name = root['name']
            targets[name] = (address, False)
            resolved.append(offset)
        calls.append([offset, name])
    if sum(name == root['name'] for site,name in calls) != 1:
        raise ValueError('native entry admission requires exactly one self-entry call')
    if any(item['name'] and not item['section'] and item['name'] not in targets or
           item['type'] in (1,2) and item['section'] and item is not root
           for item in image['symbols']):
        raise ValueError('entry ELF has unresolved or foreign defined symbols')
    bindings = {'calls':calls, 'data':[], 'functions':[], 'switches':[],
                'entry':{'resolved':resolved, 'relocations':sorted(relocations),
                         'function_size':size, 'section_size':len(image['text'])}}
    return bindings, targets


def linked_bytes(original, linked, address, rom, mapping, index, bindings, targets):
    """Retain resident root, exact external identities and complete section integrity."""
    import match
    fresh, expected_targets = original_bindings(original, address, rom, mapping, index)
    if bindings != fresh or targets != expected_targets:
        raise ValueError('entry binding manifest differs from the original ELF')
    size = function_size(original, address)
    if linked['type'] != 2 or linked['relocations'] or function_size(linked, address) != size or \
            len(linked['text']) != len(original['text']):
        raise ValueError('linked entry owner extent, residency or relocation ownership differs')
    expected = bytearray(original['text'])
    root_name = f'func_{address:08X}'
    for name,(target,is_object) in targets.items():
        candidates = [item for item in linked['symbols'] if item['name'] == name]
        if len(candidates) != 1:
            raise ValueError('linked entry call symbol is missing or ambiguous')
        item = candidates[0]
        section = linked['text_index'] if name == root_name else 0xfff1
        if item['section'] != section or item['value'] != target|1 or item['type'] != 2 or item['bind'] != 1:
            raise ValueError('linked entry call symbol has incorrect resident or absolute identity')
    for item in linked['symbols']:
        if item['name'] and not item['section'] or item['type'] in (1,2) and \
                item['name'] not in targets:
            raise ValueError('linked entry ELF has unresolved or foreign function/object symbols')
    instructions = _decode(linked['text'][:size], address)
    for site,name in bindings['calls']:
        instruction = instructions.get(address+site)
        if instruction is None or _call_target(instruction) != targets[name][0]:
            raise ValueError('linked entry BL differs from its original binding')
        if site in bindings['entry']['relocations']:
            expected[site:site+4] = linked['text'][site:site+4]
    if bytes(expected) != linked['text']:
        raise ValueError('linked entry ELF changed bytes outside exact call relocations')
    return linked['text'][:size]


def verify_owner(data, address, rom, mapping, index, objects, manifest, bindings):
    """Fresh machine proof, unique root/helper identities, no recursive induction."""
    import match
    from inert_spin_profile import validate_span
    from software_double_profile import indices, span_record
    validate_span(data, address, rom, mapping, index)
    entries, rows = indices(mapping, index)
    root = span_record(address, address+len(data), entries, rows, rom)
    instructions = _decode(data, address)
    # A single entry save cannot double as compiler-emitted outgoing words.
    # Additional pushes and caller-clobbered register spills are outside this
    # native policy, even if the generic saved-frame primitive could track them.
    from capstone.arm import ARM_REG_LR, ARM_REG_R4, ARM_REG_R7
    pushes = [item for item in instructions.values() if item.mnemonic == 'push']
    if len(pushes) != 1 or pushes[0].address != address or not pushes[0].operands or \
            any(op.type != ARM_OP_REG or op.reg not in (*range(ARM_REG_R4,ARM_REG_R7+1),ARM_REG_LR)
                for op in pushes[0].operands) or \
            not any(op.reg == ARM_REG_LR for op in pushes[0].operands):
        raise ValueError('entry native owner permits only one initial preserved-register and LR save')
    proof = prove(data, address, mapping, index, len(rom), selector=SELECTOR)
    # Existing inventories may count legacy halfwords rather than decoded BLs.
    if root['instrs'] not in (len(instructions), len(data)//2):
        raise ValueError('entry index count is neither complete instructions nor legacy halfwords')
    calls = [[site-address, f'func_{target:08X}'] for site,target in prepare(
        data,address,mapping,index,len(rom),selector=SELECTOR).calls]
    if type(bindings) is not dict or set(bindings) != {'calls','data','functions','switches','entry'} or \
            bindings['calls'] != calls or any(bindings[name] for name in ('data','functions','switches')):
        raise ValueError('entry call bindings differ from the complete reached owner')
    binding = bindings['entry']
    self_sites = [site for site,name in calls if name == f'func_{address:08X}']
    if type(binding) is not dict or set(binding) != {'resolved','relocations','function_size','section_size'} or \
            binding['function_size'] != len(data) or binding['section_size'] not in (len(data), len(data)+2) or \
            binding['resolved'] not in ([], self_sites) or \
            binding['relocations'] != [site for site,name in calls if site not in binding['resolved']]:
        raise ValueError('entry binding roles are incomplete or inconsistent')
    dependencies = []
    for target in sorted({target for site,target in prepare(data,address,mapping,index,len(rom),selector=SELECTOR).calls
                          if target != address}):
        candidates = [row for row in entries if int(row['rom'],16) == target]
        if len(candidates) != 1:
            raise ValueError('entry ordinary helper identity is ambiguous')
        end = int(candidates[0]['end'],16)
        record = span_record(target,end,entries,rows,rom)
        dependencies.append({'address':target,'end':end,'instructions':record['instrs'],
                             'body_sha256':_digest(rom[target-match.ROM_BASE:end-match.ROM_BASE]),
                             'contract':CONTRACT})
    observed = {'profile':NATIVE_SCHEMA, 'proof':proof, 'bindings':bindings,
                'ordinary_dependencies':dependencies, 'environment':environment_fingerprint(),
                'index_count':{'actual':len(instructions),'recorded':root['instrs']},
                'contract':CONTRACT}
    if manifest is not None and observed != manifest:
        raise ValueError('entry native manifest differs from fresh source-bound replay')
    return observed,list(instructions.values())
