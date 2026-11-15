"""Original-ELF source bridge to the strict canonical integer scalar inventory.

The existing inventory proves structural ABI/effects, including the real zero
hook, without numeric operand assumptions. This bridge adds no arithmetic,
memory-safety, physical separation or termination theorem.
"""
import copy
import hashlib
import importlib
from pathlib import Path

import canonical_integer_scalar_inventory as scalar

SELECTOR = 'canonical-integer-scalar-source-v1'
SCHEMA = 'elf-symbol-thumb-canonical-integer-scalar-source-v1'
CONTROL_FLOW = ('complete Thumb scalar owner; original ELF-bound canonical integer '
                'runtime closure and strict restoring frame; ordinary calls ABI conditional')


def environment_fingerprint():
    from addressed_signed_runtime_profile import toolchain_fingerprint, runtime_fingerprint
    names = {'match', 'armv4t', 'owner_admission_profile', 'canonical_integer_native_profile',
             'owner_graph_profile', 'owner_runtime_profile', 'local_long_branch_profile',
             'function_thunk_profile', 'software_double_profile', 'software_float_profile',
             'analyze'}
    names.update(module.__name__ for module in (scalar, scalar.canonical, scalar.division,
        scalar.quotient, scalar.unsigned_frames, scalar.unsigned_remainder))
    return dict(toolchain=toolchain_fingerprint(), runtime=runtime_fingerprint(),
        producers={name: hashlib.sha256(Path(importlib.import_module(name).__file__).read_bytes()).hexdigest()
                   for name in sorted(names)})


def linked_bytes(original, linked, address, bindings, targets):
    """Bind every linked byte and typed definition to genuine original calls."""
    import match
    match.allocated_text_only(linked)
    name = f'func_{address:08X}'
    root, offset = match.function_record(linked, name, address, True)
    source, _ = match.function_record(original, name, address, True)
    from addressed_signed_runtime_profile import terminal_alignment
    terminal_alignment(linked, root)
    if linked['type'] != 2 or linked['relocations'] or offset or \
            root['size'] != source['size'] or len(linked['text']) != len(original['text']) or any(
                symbol['name'] and not symbol['section'] for symbol in linked['symbols']):
        raise ValueError('canonical integer typed link changed complete owner or has unresolved symbols')
    for key, (value, is_object) in targets.items():
        found = [symbol for symbol in linked['symbols'] if symbol['name'] == key]
        if is_object or len(found) != 1 or found[0]['section'] != 0xfff1 or \
                found[0]['value'] != value | 1 or found[0]['bind'] != 1 or \
                found[0]['type'] != 2 or found[0]['size']:
            raise ValueError('canonical integer link requires exact unique typed absolute functions')
    allowed = set(targets) | {name}
    if any(symbol['name'] not in allowed and symbol['type'] in (1, 2) and symbol['section']
           for symbol in linked['symbols']):
        raise ValueError('canonical integer link adds an unowned object or function')
    expected = bytearray(original['text'])
    decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
    decoder.detail = True
    for at, name in bindings['calls']:
        item = next(decoder.disasm(linked['text'][at:at+4], address+at), None)
        if item is None or item.id != match.ARM_INS_BL or item.size != 4 or \
                item.operands[0].imm != targets[name][0]:
            raise ValueError('canonical integer linked call differs from original symbol identity')
        expected[at:at+4] = linked['text'][at:at+4]
    if bytes(expected) != linked['text']:
        raise ValueError('canonical integer link changed bytes outside original call relocations')
    return linked['text'][:root['size']]


def verify_original(original, linked, address, rom, mapping, index, bindings, manifest=None):
    """Authenticate actual ET_REL/ET_EXEC, then run the unchanged scalar proof."""
    import match
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    if type(address) is not int or any(type(value) is not bytes
            for value in (original, linked, rom, mapping, index)):
        raise ValueError('canonical integer source bridge requires immutable original inputs')
    before = environment_fingerprint()
    image = match.elf_image(original)
    actual, targets = owner.original_bindings(image, address, rom, mapping, b'{}',
                                               selector=SELECTOR, index=index)
    if type(bindings) is not dict or bindings != actual or any(
            actual[role] for role in ('data', 'functions', 'switches')):
        raise ValueError('canonical integer bindings differ from actual original call-only ELF roles')
    if any(symbol['size'] for symbol in image['symbols']
           if symbol['name'] in targets and not symbol['section']):
        raise ValueError('canonical integer calls require zero-sized original undefined functions')
    data = linked_bytes(image, match.elf_image(linked), address, actual, targets)
    _, _, _, calls, _ = graph.graph(data, address, owner.refine(data, address, mapping))
    expected = {address+at: name for at, name in actual['calls']}
    if expected != scalar.bind_calls(calls, mapping, address, len(data), len(rom)):
        raise ValueError('canonical integer actual CFG differs from original compiler call identities')
    checked, instructions = scalar.verify(data, address, rom, mapping, index, calls, expected,
                                           selector=scalar.SELECTOR)
    if before != environment_fingerprint():
        raise ValueError('canonical integer producers, toolchain or runtime changed')
    result = dict(profile=SCHEMA, selector=SELECTOR, bindings=copy.deepcopy(actual),
        prerequisite=checked, environment=before,
        original_ET_REL_sha256=hashlib.sha256(original).hexdigest(),
        linked_ELF_sha256=hashlib.sha256(linked).hexdigest(),
        contract='Plausible fixed-toolchain source and complete original ELF are separately bound '
                 'by compilation and report replay. Canonical integer calls have the existing '
                 'structural runtime and strict frame proofs, including real zero-hook paths; '
                 'no numeric preconditions or return facts are granted. Ordinary calls remain '
                 'conditional returning ABI boundaries. No arithmetic C-equivalence, physical '
                 'memory separation, memory safety or termination theorem is inferred.')
    if manifest is not None and owner.text(manifest) != owner.text(result):
        raise ValueError('canonical integer source manifest differs from fresh original replay')
    return result, len(instructions)
