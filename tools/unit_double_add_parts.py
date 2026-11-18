"""Old-agbcc dp-bit _fpadd_parts and both real double addition/subtraction callers."""
import sys

import library_units as units
import private_double_selected_record_inventory as selected
import unit_fpbit_source as source

ADDRESS, END, COUNT = 0x08142E10, 0x08143080, 302
CALLERS = ((0x08143080, 0x081430B4, 0x081430A4), (0x081430B4, 0x081430F0, 0x081430E0))
SCHEMA = 'elf-symbol-thumb-dp-bit-add-parts-unit-v1'
LABEL = 'dp-bit component addition'
TOOLCHAIN = 'old-agbcc-O2-v1'
SOURCE_DIGEST = '0538251e7be3c69f60614327ffea9963bf2451c235ca96c0c97b242e5cfa4002'
DATA, NEGATE = 'data_03005E50', 0x08142A94
TARGETS = {DATA: selected.FIXED_RECORD, '__negdi2': NEGATE}
SITES = {0x58: DATA, 0x174: '__negdi2', 0x1B6: '__negdi2'}
SIGN_TOGGLE = 0x081430D2
CALLS = {ADDRESS+offset: NEGATE for offset in (0x174, 0x1B6)}
CONTROL = ('* control flow: original add and subtract callers use distinct 20-byte local records. '
           'The helper returns an input, the output, or the fixed RAM record. '
           'Packing the fixed record assumes five readable words whose contents are runtime inputs.')


def unit_owner(unit, address, orphan=None):
    return address == ADDRESS and orphan is None and source.dp_unit(unit)


def check_source(capture, relative):
    names = ('fractype', 'halffractype', 'intfrac', 'fp_class_type', 'fp_number_type', DATA, '__negdi2',
             'isnan', 'isinf', 'iszero', 'func_08142E10')
    source.reviewed_source(capture, relative, ADDRESS, names, SOURCE_DIGEST)


def link_object(runner, workspace, args, original, capture, relative, rom, mapping, index):
    import match
    from addressed_signed_runtime_profile import linked_bytes
    check_source(capture, relative)
    source.fixed_bindings(original, ADDRESS, END, TARGETS, SITES, DATA)
    linked = match.link_typed_targets(runner, workspace, args, 'func_08142E10', ADDRESS, TARGETS, {DATA})
    if any(item['size'] for item in linked['symbols'] if item['name'] in TARGETS):
        raise ValueError('dp-bit add parts requires storage-free absolute linker definitions')
    return linked_bytes(original, linked, ADDRESS, CALLS, TARGETS, data_relocations={0x58: (DATA, 0)})


def native_proof(data, rom, mapping, index, objects):
    import match
    if match.parse_data_symbols(objects).get(DATA) != selected.FIXED_RECORD or data != rom[
            ADDRESS-match.ROM_BASE:END-match.ROM_BASE]:
        raise ValueError('dp-bit component addition requires its complete USA owner and mapped RAM record')
    callers = []
    core = None
    for address, end, selection_site in CALLERS:
        proof, decoded = selected.verify(rom[address-match.ROM_BASE:end-match.ROM_BASE], address, rom, mapping, index,
                                   selector=selected.SELECTOR)
        helper, = (record for record in proof['helper_closure'] if record['address'] == ADDRESS)
        native = helper['native_proof']
        if (proof['private_bindings'][2] != [selection_site, 'private-selection'] or
                (helper['end'], helper['instructions']) != (END, COUNT) or helper['calls'] != sorted(CALLS.items()) or
                native['return_pointers']['values'] != selected.RETURN_POINTERS or native['stack_reads'] or
                native['writes'] != [(2, offset, 4) for offset in range(0, 20, 4)] or
                proof['external_reads'] != selected.ABSOLUTE_POLICY['reads'] or proof['external_writes']):
            raise ValueError('dp-bit component addition changed caller, helper, output or return provenance')
        # R4 holds the second unpack destination at SP+20. Only subtraction
        # toggles its sign word at +4 between unpacking and combining.
        if address == CALLERS[1][0]:
            path = {item.address: bytes(item.bytes) for item in decoded}
            for site, encoding in ((0x081430CA, '05ac'), (0x081430CC, '211c'),
                                   (SIGN_TOGGLE, '6068'), (SIGN_TOGGLE+2, '0121'),
                                   (SIGN_TOGGLE+4, '4840'), (SIGN_TOGGLE+6, '6060')):
                if path.get(site) != bytes.fromhex(encoding):
                    raise ValueError('dp-bit subtract caller must toggle the second component sign with one')
        callers.append(dict(address=address, call=selection_site,
                            sign_toggle=SIGN_TOGGLE if address == CALLERS[1][0] else None,
                            frame_proof=units.sha(units.canonical(proof['caller']).encode()),
                            conditional_reads=proof['external_reads']))
        observed = dict(instructions=COUNT, partition=helper['partition'], literal=proof['fixed_record_identity'],
                        return_pointers=native['return_pointers']['values'], reads=native['argument_effects']['reads'],
                        writes=native['writes'], calls=helper['calls'],
                        helper_proofs_sha256=units.sha(units.canonical(proof['helper_closure']).encode()))
        if core is not None and observed != core:
            raise ValueError('dp-bit callers disagree on the shared component helper proof')
        core = observed
    return dict(core, callers=callers)


def build(root, address, args=None):
    return source.build(sys.modules[__name__], root, address, args)


def report_matches(report, root, address):
    return address == ADDRESS and report == build(root, address)[1]


def issue(root, address, args):
    return source.issue(sys.modules[__name__], root, address, args)
