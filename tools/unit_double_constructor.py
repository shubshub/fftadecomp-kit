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
UNIT_DIGEST = 'fd4260dbe23fa4058473ccd446851e3aa2a4e6a73ec65eebf4838bf401bcd7f0'
SOURCE_DIGEST = 'deebae548da5bac2789a019d221e997ec89b48e44c7abf745a2949b91e52418f'
CONTROL = ('* control flow: scalar classification, sign and exponent in R0-R2, fraction low in R3 and high '
           'at entry SP; the private packer reads five initialized local words; the restored LR survives '
           'the final SP adjustment; mixed-word double result in R0/R1')


def unit_owner(unit, address, orphan=None):
    return (unit is not None and address == ADDRESS and orphan is None and unit.name == 'libgcc dp-bit' and
            unit.toolchain == TOOLCHAIN and (unit.start, unit.end, unit.proof) == (PACK, 0x081439C8, 0x08142D34) and
            unit.row['identity'] == [dict(address='0x08142BE8', size=3552, sha256=UNIT_DIGEST)])


def check_source(capture, relative):
    import plausible
    from sdk_cpuset_halfword import TOKEN, base_header
    path = capture / relative
    text = path.read_text()
    names = ('fractype', 'halffractype', 'fp_class_type', 'fp_number_type', NAME, 'func_08143958')
    if relative.as_posix() != 'src/08143958.c' or plausible.include_closure(capture, path) != (
            {'src/08143958.c', 'include/ffta.h'}, []) or not base_header((capture/'include/ffta.h').read_bytes(), names):
        raise ValueError('dp-bit constructor requires the original public types and one addressed source')
    tokens = TOKEN.findall(plausible.strip_comments_and_strings_keep_strings(text))
    if any(marker in text for marker in ('\\', '??', '%:', '\0')) or units.sha(' '.join(tokens).encode()) != SOURCE_DIGEST:
        raise ValueError('dp-bit constructor requires its reviewed split-fraction signature and record assignments')


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
