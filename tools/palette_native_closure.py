"""Conditional full-owner composition of independently authenticated receipts.

The caller must obtain ``trusted_pins`` from its reviewed frozen-proof authority,
not compute trust from an untrusted submitted bundle. Hash agreement transports
that premise; it does not prove a certificate. No old producer is invoked here.
This module neither installs a native selector nor discharges physical/C/ABI
conditions. The returned manifest is deliberately ineligible for unconditional
admission. Original artifacts are immutable bytes; no compiler or linker runs.
"""
import hashlib
import json
from pathlib import Path
import re
import struct

import match
import software_double_profile as spans
from addressed_signed_runtime_profile import runtime_fingerprint, toolchain_fingerprint

SELECTOR = 'conditional-palette-full-owner-closure-v1'
SCHEMA = 'elf-symbol-thumb-conditional-palette-full-owner-closure-v1'
CONTROL_FLOW = 'authenticated-complete-owner-with-conditional-frame-value-source-closure'
KEYS = frozenset(('copy', 'numeric', 'frame', 'arithmetic', 'first_use', 'loops',
                  'machine', 'source', 'source_scope', 'inventory', 'lineage', 'compiler'))
MAX_CERTIFICATE_BYTES = 4 * 1024 * 1024
MAX_OWNER_BYTES = 4096
LAYOUT_CONDITION = (
    'Target layout is little-endian with 8-bit bytes, sizeof(short)=2, '
    'sizeof(int)=4, sizeof(s16*)=4 and compatible object alignment. '
    'The 12-byte pointer copy preserves the three live C pointer representations; '
    'literal numeric addresses alone grant no object, lifetime or access permission.')
TRUST_CONDITION = (
    'Each trusted certificate pin is independently authenticated by the integrating '
    'proof authority. Submitted hashes or boolean assertions alone do not establish trust.')


def sha(data):
    return hashlib.sha256(data).hexdigest()


def digest(value):
    return sha(json.dumps(value, sort_keys=True, separators=(',', ':')).encode())


def require(condition, message):
    if not condition:
        raise ValueError(message)


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'duplicate JSON member')
        result[key] = value
    return result


def pinned(data, pin, label):
    require(type(data) is bytes and type(pin) is dict and
            type(pin.get('bytes')) is int and pin['bytes'] == len(data) and
            pin.get('sha256') == sha(data), label + ' bytes/pin differs')


def environment_fingerprint():
    return dict(toolchain=toolchain_fingerprint(), runtime=runtime_fingerprint(),
                modules={Path(m.__file__).name: sha(Path(m.__file__).read_bytes())
                         for m in (match, match.armv4t, spans)},
                producer_sha256=sha(Path(__file__).read_bytes()))


def read_certificates(certificates, trusted_pins):
    require(type(certificates) is dict and type(trusted_pins) is dict and
            set(certificates) == set(trusted_pins) == KEYS,
            'complete exact certificate and independent authority sets required')
    docs = {}
    for name in sorted(KEYS):
        raw = certificates[name]
        require(type(raw) is bytes and len(raw) <= MAX_CERTIFICATE_BYTES,
                'certificate must be bounded immutable JSON bytes')
        pinned(raw, trusted_pins[name], 'certificate ' + name)
        docs[name] = json.loads(raw, object_pairs_hook=unique,
                                parse_constant=lambda value: (_ for _ in ()).throw(
                                    ValueError('nonfinite JSON value')))
        require(type(docs[name]) is dict, 'certificate document must be an object')
    extracted = dict(docs)
    for name in ('copy', 'numeric'):
        extracted[name] = docs[name]['prerequisite']
    for name in ('frame', 'loops', 'machine', 'source'):
        extracted[name] = docs[name]['receipt']
    return docs, extracted


def chain(certificates, docs, c, source, original, linked):
    """Check reuse edges; retain the meaning of the authenticated premises."""
    machine, src, inv = c['machine'], c['source'], c['inventory']
    ma = machine['reused_certificate_authority']
    sa = src['reused_authority']
    require(ma.get('independently_established_frozen_certificates') is True and
            sa.get('independently_established_frozen_certificates') is True and
            sa.get('original_source_and_object_lineage_authenticated') is True,
            'frozen independent authority or original lineage missing')
    for name in ('copy', 'numeric', 'frame', 'arithmetic', 'first_use', 'loops'):
        require(ma.get(name + '_sha256') == digest(c[name]), 'machine reuse edge: ' + name)
    require(sa.get('machine_sha256') == digest(machine) and
            sa.get('inventory_sha256') == digest(inv), 'source reuse edges differ')
    require(c['frame']['reused_certificate_authority']['copy_sha256'] == digest(c['copy']) and
            c['frame']['reused_certificate_authority']['numeric_sha256'] == digest(c['numeric']) and
            c['loops']['reuse_authority']['frame_sha256'] == digest(c['frame']) and
            c['loops']['reuse_authority']['numeric_sha256'] == digest(c['numeric']),
            'frame/loop reuse edges differ')
    require(ma['arithmetic_file_sha256'] == sha(certificates['arithmetic']),
            'arithmetic capture edge differs')
    pinned(certificates['arithmetic'], c['first_use']['actual_arithmetic_capture'], 'first-use capture')
    require(c['first_use']['arithmetic_functions_AST_unchanged'] is True and
            c['first_use']['composer_AST_diff_only_new_guard_and_evidence'] is True,
            'arithmetic strengthening guard missing')
    scope = c['source_scope']
    pinned(certificates['source'], scope['frozen_source_capture'], 'prototype scope capture')
    require(scope['AST_diff_only_added_guard_definition_and_call'] is True and
            scope['original_AST_digest_unchanged'] is True,
            'prototype strengthening guard missing')
    for raw, key in ((source, 'source'), (original, 'original_ET_REL'), (linked, 'linked_ELF')):
        pinned(raw, sa[key], 'source authority ' + key)
    pinned(source, scope['source'], 'prototype scope source')
    require(src['source']['source_sha256'] == sha(source) and
            src['source']['source_bytes'] == len(source), 'source model bytes differ')
    lineage, compiler = c['lineage'], c['compiler']
    pinned(certificates['source_scope'], lineage['source_scope_guard'], 'lineage scope')
    for raw, key in ((source, 'original_source'), (original, 'original_ET_REL'),
                     (linked, 'original_linked_ELF')):
        pinned(raw, lineage[key], 'preprocessed lineage ' + key)
    require(lineage['complete_translation_unit_AST_equal'] is True and
            lineage['preprocessor_directives_other_than_line_markers'] == 0 and
            lineage['preprocessed_AST_sha256'] == lineage['source_AST_sha256'] ==
            src['source']['AST_sha256'], 'complete preprocessed AST lineage differs')
    require(compiler['before_after_current_bytes_equal'] is True and
            compiler['target_semantics_proved'] is False and
            compiler['current_compiler']['sha256'] == lineage['current_compiler_binary']['sha256'] and
            compiler['original_result']['sha256'] == lineage['original_result']['sha256'] ==
            sa['original_result']['sha256'], 'historical compiler identity lineage differs')


def same_owner(c, address, rom):
    inv, machine, src = c['inventory'], c['machine'], c['source']
    end, count = inv['end'], inv['instructions']
    require(type(address) is int and type(end) is int and type(count) is int and
            0 < count <= 2048 and 0 < end - address <= MAX_OWNER_BYTES,
            'invalid bounded complete owner')
    body = rom[address - match.ROM_BASE:end - match.ROM_BASE]
    require(match.ROM_BASE <= address < end <= match.ROM_BASE + len(rom), 'owner outside ROM')
    for proof in (inv, machine, c['frame'], c['numeric'], c['loops'], c['copy']['prefix']):
        require(proof['address'] == address and proof['end'] == end and
                proof['ROM_sha256'] == sha(rom) and
                proof.get('body_sha256', proof.get('linked_text_sha256')) == sha(body),
                'certificate owner/body/ROM differs')
    require(src['machine_address'] == address and src['machine_end'] == end and
            src['machine_body_sha256'] == sha(body) and src['ROM_sha256'] == sha(rom),
            'source machine context differs')
    require(inv['schema'] == 'thumb-compiler-local-copy-elf-inventory-v1' and
            machine['schema'] == 'conditional-palette-owner-value-composition-v1' and
            src['schema'] == 'conditional-palette-source-machine-correspondence-v1',
            'unsupported certificate schemas')
    require(machine['conditional_owner_machine_value_trace'] is True and
            src['conditional_C_AST_value_access_correspondence'] is True and
            inv['inventory_only'] is True, 'conditional proof conclusion missing')
    for proof in (machine, src, c['frame'], c['loops']):
        require(proof.get('source_or_ELF_admission') is False and
                proof.get('physical_memory_permission') is False and
                proof.get('native_admission', False) is False and
                proof.get('unconditional_termination', False) is False,
                'conditional certificate cannot upgrade admission or memory claims')
    require(machine['instructions'] == c['frame']['instructions'] == c['numeric']['instructions'] == count,
            'complete instruction counts differ')
    coverage = machine['complete_instruction_coverage']
    require(type(coverage) is list and len(coverage) == len(set(coverage)) == count and
            all(type(site) is int and address <= site < end and site % 2 == 0 for site in coverage),
            'complete instruction coverage differs')
    partition = inv['partition']
    require(partition == c['frame']['partition'] == c['numeric']['partition'] == c['copy']['prefix']['partition'] and
            sum(partition[key] for key in ('code_bytes', 'literal_and_table_bytes', 'alignment_bytes')) == len(body),
            'full owner partitions differ')
    model = src['source']
    require(model['function'] == f'func_{address:08X}' and
            len(model['parameter_names']) == 6 and len(set(model['parameter_names'])) == 6 and
            model['parameter_types'] == ['u16', 'u16', 's16', 's16', 's16', 'u8'] and
            model['pointer_initializer_order'] == model['parameter_names'][2:5] and
            model['history_stride'] == 12 and model['root_return_type'] == 'void' and
            model['external_calls_in_C_body'] == 0, 'six-argument local-object source shape differs')
    transport = src['entry_argument_transport']
    expected = list(zip(model['parameter_names'], model['parameter_types'],
                        ['R0', 'R1', 'R2', 'R3', 'incoming word at entrySP+0', 'incoming word at entrySP+4'],
                        [16, 16, 16, 16, 16, 8]))
    require(len(transport) == 6 and
            [tuple(row[k] for k in ('parameter', 'C_type', 'machine_bits', 'width')) for row in transport] == expected,
            'six argument register/stack transport differs')
    helper = inv['helper_identity']
    require(type(helper) is list and len(helper) == 4 and
            all(type(x) is int for x in helper[:3]) and helper[2] > 0 and
            match.ROM_BASE <= helper[0] < helper[1] <= match.ROM_BASE + len(rom) and
            not (helper[0] < end and helper[1] > address), 'helper span differs or overlaps owner')
    copy = c['copy']['copy']
    require(copy['canonical_bytes'] == helper[1] - helper[0] and
            copy['canonical_sha256'] == helper[3] == sha(rom[helper[0]-match.ROM_BASE:helper[1]-match.ROM_BASE]) and
            len(copy['observations']) == 1, 'complete copy helper/effect binding differs')
    obs = copy['observations'][0]
    require(obs['address'] == helper[0] and obs['consumer'] == address and
            obs['consumer_sha256'] == sha(body) and obs['count'] == 12 and
            obs['SP_restored'] is True and len(obs['copied_pointer_words']) == 3 and
            obs['transfers'] == [[obs['source']+i, obs['destination']+i] for i in range(12)] and
            sorted(obs['preserved_registers']) == list(range(4, 13)),
            'copy must transport all three initialized local pointer words and restore its frame')
    return body, count, helper, obs


def unique_symbol(image, name):
    found = [symbol for symbol in image['symbols'] if symbol['name'] == name]
    require(len(found) == 1, 'unique ELF symbol required: ' + name)
    return found[0]


def bl_target(raw, site):
    first, second = struct.unpack('<HH', raw)
    require(first & 0xf800 == 0xf000 and second & 0xf800 == 0xf800,
            'original/linked relocation is not Thumb BL')
    offset = ((first & 0x7ff) << 12) | ((second & 0x7ff) << 1)
    if offset & (1 << 22):
        offset -= 1 << 23
    return site + 4 + offset


def bindings_for(inv):
    """Native manifest shape; genuine relocation checks occur in verify_original."""
    return dict(calls=[[site, name] for site, kind, name, _ in inv['relocations'] if kind == 10],
                data=[[site, name, 0] for site, kind, name, _ in inv['relocations'] if kind == 2],
                functions=[], switches=[])


def bind_images(original, linked, address, body, inv, objects, source_model, copy_observation):
    a, b = match.elf_image(original), match.elf_image(linked)
    require(a['type'] == 1 and b['type'] == 2 and not b['relocations'],
            'original ET_REL and fully resolved ET_EXEC required')
    for image in (a, b):
        match.allocated_text_only(image)
        symbol, offset = match.function_record(image, f'func_{address:08X}', address, True)
        require(offset == 0 and symbol['size'] == len(body) == len(image['text']) and
                symbol['bind'] == 1 and (image['type'] != 2 or symbol['value'] == address | 1),
                'complete sized global Thumb FUNC required')
        require(not any(re.fullmatch(r'\$a(?:\..*)?', row['name']) or
                    row['type'] in (1, 2) and row['section'] not in (0, 0xfff1) and row is not symbol
                    for row in image['symbols']), 'extra allocated object/function or ARM mapping')
    require(sha(a['text']) == inv['original_text_sha256'] and
            b['text'] == body and sha(b['text']) == inv['linked_text_sha256'],
            'inventory original/linked full text differs')
    data = match.parse_data_symbols(objects)
    data_names = {source_model['palette'], source_model['history']}
    require(len(data_names) == 2, 'distinct canonical data identities required')
    require(all(name in data and list(data.values()).count(data[name]) == 1 for name in data_names),
            'referenced fixed-map data identity must have one canonical name')
    expected, occupied, records = bytearray(a['text']), set(), []
    for number in a['relocations']:
        section = a['sections'][number]
        require(section[1] == 9 and section[7] == a['text_index'] and
                section[9] == 8 and section[5] % 8 == 0, 'canonical .text REL records required')
        symbols = a['symbol_tables'].get(section[6])
        raw = a['section_data'][number]
        require(symbols is not None and len(raw) == section[5], 'relocation table extent differs')
        for position in range(0, len(raw), 8):
            site, info = struct.unpack_from('<II', raw, position)
            kind, index = info & 255, info >> 8
            require(index < len(symbols) and kind in (2, 10) and site % 2 == 0 and
                    site + 4 <= len(body) and not occupied.intersection(range(site, site+4)),
                    'invalid or overlapping relocation')
            occupied.update(range(site, site+4))
            symbol = symbols[index]
            name = symbol['name']
            require(symbol == unique_symbol(a, name) and symbol['section'] == 0 and
                    symbol['bind'] == 1 and symbol['value'] == symbol['size'] == 0,
                    'genuine original unique zero-valued undefined identity required')
            definition = unique_symbol(b, name)
            require(definition['section'] == 0xfff1 and definition['bind'] == 1 and definition['size'] == 0,
                    'unique global zero-size absolute typed binding required')
            if kind == 10:
                point = inv['helper_identity'][0]
                require(name == 'memcpy' and symbol['type'] in (0, 2) and
                        definition['type'] == 2 and definition['value'] == point | 1 and
                        address+site == copy_observation['site'] and
                        bl_target(a['text'][site:site+4], address+site) == address+site and
                        bl_target(body[site:site+4], address+site) == point,
                        'genuine zero-addend compiler memcpy Thumb target required')
                expected[site:site+4] = body[site:site+4]
            else:
                require(name in data_names and name in data, 'canonical source data binding required')
                point = data[name]
                words = [word for word in inv['partition']['words'] if word['address'] == address+site]
                require(symbol['type'] in (0, 1) and definition['type'] == 1 and
                        definition['value'] == point and (address+site) % 4 == 0 and
                        a['text'][site:site+4] == bytes(4) and len(words) == 1 and
                        words[0]['value'] == point and words[0]['switch_word'] is False and
                        bool(words[0]['load_sites']), 'zero-addend referenced typed data literal required')
                expected[site:site+4] = struct.pack('<I', point)
            records.append([site, kind, name, point])
    require(sorted(records) == inv['relocations'] and
            sum(row[1] == 10 for row in records) == 1 and
            {row[2] for row in records} == data_names | {'memcpy'}, 'complete original relocation inventory differs')
    allowed = data_names | {'memcpy'}
    require(not any(row['name'] and row['section'] == 0 and row['name'] not in allowed for row in a['symbols']) and
            not any(row['name'] and row['section'] == 0 for row in b['symbols']) and
            not any(row['type'] in (1, 2) and row['section'] == 0xfff1 and row['name'] not in allowed for row in b['symbols']),
            'extra undefined or absolute typed symbol')
    require(bytes(expected) == body, 'unrelocated compiler bytes changed')


def verify_original(original, linked, address, rom, mapping, index, bindings, manifest=None,
                    *, objects, source, certificates, trusted_pins, selector):
    """Return (conditional manifest, complete instruction count); never admit natively."""
    require(type(selector) is str and selector == SELECTOR, 'explicit conditional closure selector required')
    require(all(type(raw) is bytes for raw in (original, linked, rom, mapping, index, objects, source)),
            'immutable original/source/context bytes required')
    before = environment_fingerprint()
    try:
        docs, c = read_certificates(certificates, trusted_pins)
        chain(certificates, docs, c, source, original, linked)
        body, count, helper, copy_observation = same_owner(c, address, rom)
        inv, src = c['inventory'], c['source']
        entries, rows = spans.indices(mapping, index)
        for start, end, instructions in ((address, address+len(body), count), tuple(helper[:3])):
            require(spans.span_record(start, end, entries, rows, rom)['instrs'] == instructions,
                    'current complete dependency instruction count differs')
        bind_images(original, linked, address, body, inv, objects, src['source'], copy_observation)
        expected_bindings = bindings_for(inv)
        require(bindings == expected_bindings, 'native binding manifest differs')
        compiler_hash = c['compiler']['current_compiler']['sha256']
        require(before['toolchain'][0][1] == compiler_hash, 'current compiler differs from original authenticated binary')
        conditions = [TRUST_CONDITION, LAYOUT_CONDITION]
        for name, field in (('frame', 'required_unproved_conditions'), ('loops', 'required_unproved_conditions'),
                            ('machine', 'required_unproved_conditions'), ('source', 'required_unproved_conditions'),
                            ('lineage', 'remaining_conditions')):
            values = c[name][field]
            require(type(values) is list and values and all(type(v) is str and v.strip() for v in values),
                    'nonempty explicit conditions required: ' + name)
            conditions.extend(value for value in values if value not in conditions)
        observed = dict(profile=SCHEMA, selector=SELECTOR, control_flow=CONTROL_FLOW,
            address=address, end=address+len(body), instructions=count, bindings=expected_bindings,
            original_ET_REL_sha256=sha(original), linked_ELF_sha256=sha(linked), source_sha256=sha(source),
            body_sha256=sha(body), ROM_sha256=sha(rom), mapping_sha256=sha(mapping),
            index_sha256=sha(index), objects_sha256=sha(objects), environment=before,
            certificate_pins={key: dict(bytes=len(certificates[key]), sha256=sha(certificates[key])) for key in sorted(KEYS)},
            certificate_premise_scope='Conjunction of the full authenticated input certificates and every condition therein; the displayed condition list is not permission to discard nested premises.',
            dependency_context=dict(owner=[address, address+len(body), count, sha(body)], helper=helper,
                scope='Current unique nonoverlapping complete owner/helper counts and canonical referenced data identities; unrelated map rows confer no effects.'),
            entry_argument_transport=src['entry_argument_transport'], C_definedness=src['C_definedness'],
            retained_obligations=dict(incoming_reads=c['frame']['incoming_read_obligations'],
                helper_push=c['frame']['helper_push_obligations'], external_envelopes=c['frame']['external_numerical_envelopes'],
                observation_semantics=src['read_value_quantification']),
            required_unproved_conditions=conditions, conditional_full_owner_closure=True,
            independently_authenticated_certificate_premise=True,
            physical_memory_permission=False, source_or_ELF_admission=False, native_admission=False,
            unconditional_termination=False, old_producer_executions=0, compiler_executions=0)
    except (KeyError, TypeError, IndexError, struct.error, UnicodeError) as error:
        raise ValueError('malformed closure input: ' + str(error)) from error
    require(environment_fingerprint() == before, 'closure environment changed during verification')
    require(manifest is None or digest(manifest) == digest(observed), 'conditional closure manifest differs')
    return observed, count
