"""The USA dp-bit __make_dp split argument, original packer and old-agbcc source."""
import sys

import library_units as units
import private_float_extension_effects_inventory as extension
import private_float_pack_admission_profile as private
import unit_fpbit_source as source

ADDRESS, END, COUNT = 0x08143958, 0x0814397E, 18
PACK, PACK_SITE = 0x08142BE8, 0x08143970
CALLER, CALLER_END, CALL_SITE = 0x0814432C, 0x0814435C, 0x08144350
NAME = 'func_08142BE8'
LABEL = 'dp-bit constructor'
SCHEMA = 'elf-symbol-thumb-dp-bit-make-dp-unit-v1'
TOOLCHAIN = 'old-agbcc-O2-v1'
UNIT_DIGEST = source.DP_DIGEST
SOURCE_DIGEST = 'deebae548da5bac2789a019d221e997ec89b48e44c7abf745a2949b91e52418f'
CONTROL = ('* control flow: scalar classification, sign and exponent in R0-R2, fraction low in R3 and high '
           'at entry SP; the private packer reads five initialized local words; the restored LR survives '
           'the final SP adjustment; mixed-word double result in R0/R1')


def unit_owner(unit, address, orphan=None):
    return address == ADDRESS and orphan is None and source.dp_unit(unit)


def check_source(capture, relative):
    names = ('fractype', 'halffractype', 'fp_class_type', 'fp_number_type', NAME, 'func_08143958')
    source.reviewed_source(capture, relative, ADDRESS, names, SOURCE_DIGEST)


def original_bindings(image, rom, mapping, index):
    selector = private.DOUBLE_SCALAR_PACK_SELECTOR
    calls, _ = private.original_bindings(image, ADDRESS, rom, mapping, index, selector=selector)
    undefined = [item for item in image['symbols'] if item['name'] and not item['section']]
    if (calls != [[PACK_SITE-ADDRESS, NAME]] or [item['name'] for item in undefined] != [NAME] or
            undefined[0]['size'] or private.function_size(image, ADDRESS) != END-ADDRESS or
            image['text'][END-ADDRESS:] != bytes.fromhex('c046')):
        raise ValueError('dp-bit constructor requires one original packer call and the excluded alignment NOP')
    return calls


def link_object(runner, workspace, args, original, capture, relative, rom, mapping, index):
    import match
    check_source(capture, relative)
    calls = original_bindings(original, rom, mapping, index)
    targets = {NAME: PACK}
    linked = match.link_typed_targets(runner, workspace, args, 'func_08143958', ADDRESS, targets, set())
    definitions = [item for item in linked['symbols'] if item['name'] == NAME]
    if len(definitions) != 1 or any(definitions[0][key] != value for key, value in (
            ('bind', 1), ('type', 2), ('section', 0xFFF1), ('value', PACK | 1), ('size', 0))):
        raise ValueError('dp-bit constructor requires the exact absolute Thumb packer definition')
    return private.linked_bytes(original, linked, ADDRESS, calls, targets, selector=private.DOUBLE_SCALAR_PACK_SELECTOR)


def native_proof(data, rom, mapping, index, objects):
    import match
    if data != rom[ADDRESS-match.ROM_BASE:END-match.ROM_BASE]:
        raise ValueError('dp-bit constructor differs from the complete USA function')
    # Replay the actual float-to-double caller and its helper closure. This
    # already proves the unusual stack-adjusted return, the caller's one
    # stack argument and every memory effect propagated from the real packer.
    caller = rom[CALLER-match.ROM_BASE:CALLER_END-match.ROM_BASE]
    proof, _ = extension.verify(caller, CALLER, rom, mapping, index, selector=extension.SELECTOR)
    constructor, = (record for record in proof['helper_closure'] if record['address'] == ADDRESS)
    native = constructor['native_proof']
    accesses = [[PACK_SITE, PACK, 'read', 0, offset, 4, ['stack', 0, -32+offset]]
                for offset in range(0, 20, 4)]
    if (proof['private_bindings'][-1] != [CALL_SITE, 'private-double-constructor'] or
            (constructor['end'], constructor['instructions']) != (END, COUNT) or
            constructor['calls'] != [(PACK_SITE, PACK)] or native['argument_accesses'] != accesses or
            native['stack_reads'] != [(0, 4)] or native['returns'] != [END-2] or
            native['writes'] or native['argument_effects']['reads']):
        raise ValueError('dp-bit constructor caller, split argument, local record or return changed')
    return dict(instructions=COUNT, partition=constructor['partition'], pack_call=PACK_SITE, caller=CALL_SITE,
                stack_word=native['stack_reads'], local_word_reads=accesses, returns=native['returns'],
                helper_proofs_sha256=units.sha(units.canonical(proof['helper_closure']).encode()),
                caller_proof_sha256=units.sha(units.canonical(proof['caller']).encode()))


def build(root, address, args=None):
    return source.build(sys.modules[__name__], root, address, args)


def report_matches(report, root, address):
    return address == ADDRESS and report == build(root, address)[1]


def issue(root, address, args):
    return source.issue(sys.modules[__name__], root, address, args)
