"""Numeric domain of the Thumb remainder of a signed halfword by 2*(u16/4)+1."""
import hashlib
from pathlib import Path

SELECTOR = 'signed-remainder-u16-quarter-odd-v1'
SCHEMA = 'elf-symbol-thumb-signed-remainder-u16-quarter-odd-v1'


def check_configuration(args, *, operation='bounded odd remainder'):
    other = (value for name, value in vars(args).items() if name.endswith('_profile')
             and name not in ('signed_runtime_profile', 'control_flow_profile'))
    if any(other) or args.unit_toolchain or args.control_flow_profile != 'ordinary' or args.mode != 'thumb':
        raise ValueError(f'{operation} requires its isolated ordinary Thumb selector')


def digest(data):
    return hashlib.sha256(data).hexdigest()


def operand_proof(instructions, edges, address, calls, site):
    """Follow sole reaching definitions. A merge, overwrite or unknown call result fails."""
    from capstone.arm import ARM_REG_R0
    import modsi3_profile as remainder

    if calls.get(site) != remainder.ADDRESS or any(
            target <= pc for pc, targets in edges.items() for target in targets):
        raise ValueError('odd remainder requires an acyclic caller and its actual runtime BL')
    predecessors = {pc: [] for pc in instructions}
    for pc, targets in edges.items():
        for target in targets:
            predecessors[target].append(pc)

    def definition(use, register):
        crossed = []
        while use != address and len(predecessors[use]) == 1:
            use = predecessors[use][0]
            instruction = instructions[use]
            if use in calls:
                # Only R4-R7 can be the ABI-preserved low register in these encodings.
                if register < 4 or calls[use] == remainder.ADDRESS:
                    break
                crossed.append(use - address)
            elif ARM_REG_R0 + register in instruction.regs_access()[1]:
                return instruction, list(reversed(crossed))
        raise ValueError('odd remainder needs one reaching definition preserved on the whole path')

    def defining_instruction(use, register, mask, encoding):
        instruction, crossed = definition(use, register)
        halfword = int.from_bytes(instruction.bytes, 'little')
        if instruction.size != 2 or halfword & mask != encoding or halfword & 7 != register:
            raise ValueError('odd remainder operand definition differs from its Thumb16 encoding')
        return instruction.address, (halfword >> 3) & 7, crossed

    # ASR #16 of any word lies in [-32768,32767]. No call-return fact is assumed.
    signed, _, _ = defining_instruction(site, 0, 0xFFC0, 0x1400)
    # ADD imm3 #1, LSL #1, LSR #2, zero-extending LDRH imm5.
    add, doubled_register, _ = defining_instruction(site, 1, 0xFFC0, 0x1C40)
    double, quarter_register, preserved = defining_instruction(add, doubled_register, 0xFFC0, 0x0040)
    quarter, halfword_register, _ = defining_instruction(double, quarter_register, 0xFFC0, 0x0880)
    load, _, _ = defining_instruction(quarter, halfword_register, 0xF800, 0x8800)
    if len(preserved) != 1:
        raise ValueError('odd remainder requires the doubled value across one ordinary ABI call')
    return dict(site=site-address, signed_asr16=signed-address, unsigned_halfword=load-address,
                quotient_by_four=quarter-address, double=double-address, add_one=add-address,
                preserved_register=f'r{doubled_register}', intervening_call=preserved[0],
                signed_dividend=[-32768, 32767], positive_odd_divisor=[1, 32767])


def build(root, address, args, expected):
    import canonical_integer_native_profile as scalar
    import modsi3_profile as remainder
    import owner_admission_profile as owner
    import owner_graph_profile as graph

    # The existing source bridge authenticates the compiler-emitted ELF calls, the
    # complete caller and restored registers, and both runtime/zero-hook bodies.
    data, native, source, mapping, index, objects, rom, count, original = owner.build(
        root, address, args, selector=scalar.SELECTOR)
    instructions, edges, _, calls, _ = graph.graph(data, address, owner.refine(data, address, mapping))
    aliases = {address+offset: name for offset, name in native['bindings']['calls']}
    runtime = {pc: name for pc, name in aliases.items() if not name.startswith('func_')}
    if len(runtime) != 1 or set(runtime.values()) != {'__modsi3'}:
        raise ValueError('odd remainder requires one canonical compiler remainder and ordinary calls')
    remainder.verify_context(data, address, calls, (rom, mapping, runtime))
    manifest = dict(schema=SCHEMA, canonical_integer=native,
                    operands=operand_proof(instructions, edges, address, calls, next(iter(runtime))),
                    numeric_producers={Path(name).name: digest(Path(name).read_bytes())
                                       for name in (__file__, remainder.__file__)})
    if expected is not None and expected != manifest:
        raise ValueError('odd remainder numeric evidence differs from the fresh native proof')
    return dict(address=address, body=data, manifest=manifest, source_sha256=source,
                mapping_sha256=digest(mapping), index_sha256=digest(index),
                objects_sha256=None if objects is None else digest(objects), rom_sha256=digest(rom), instructions=count, original_elf=original)
