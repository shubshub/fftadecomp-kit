"""Complete callback adapters that consume one of two initialized local words.

This inventory records conditional machine effects only. It does not extend
native admission or establish the ABI of the unknown descriptor target.
"""
import hashlib
import json
from pathlib import Path

import match
import owner_admission_profile as owner
import owner_graph_profile as graph
import function_thunk_profile as thunk
import local_long_branch_profile as frame
from software_double_profile import indices, span_record
from two_word_callback_closure_profile import complete

SELECTOR = 'two-output-local-scalar-callback-adapter-inventory-v1'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def verify(address, getter, rom, mapping, index, *, selector, manifest=None):
    if type(selector) is not str or selector != SELECTOR or \
            any(type(value) is not int for value in (address, getter)) or \
            any(type(value) is not bytes for value in (rom, mapping, index)):
        raise ValueError('two-output adapter requires exact explicit selector and immutable inputs')

    def linear(start, size, count):
        data, ins, edges, calls, partition = complete(start, size, count, rom, mapping, index)
        ordered = sorted(ins)
        if partition['literal_and_table_bytes'] or partition['alignment_bytes'] or any(
                edges[site] != ((ordered[number+1],) if number+1 < len(ordered) else ())
                for number, site in enumerate(ordered)):
            raise ValueError('two-output adapter requires complete code-only linear owners')
        return data, ins, edges, calls, partition

    data, ins, edges, calls, partition = linear(address, 32, 14)
    leaf, li, le, lc, lp = linear(getter, 10, 5)
    # The helper preserves R1 and R2. Its stores initialize both different local
    # words in this call context. The read/store/read/store order is significant.
    if leaf != bytes.fromhex('43680b60006810607047') or lc:
        raise ValueError('two-output getter requires exact ordered node+4/R1 then node+0/R2 effects')
    target = thunk.ALIASES['_call_via_r2']
    if data[:10] != bytes.fromhex('10b582b00c1c01aa6946') or \
            data[14:20] != bytes.fromhex('009821686268') or \
            data[24:] != bytes.fromhex('02b010bc02bc0847') or \
            sorted(ins) != [address+offset for offset in (0,2,4,6,8,10,14,16,18,20,24,26,28,30)] or \
            calls != {address+10:getter, address+20:target}:
        raise ValueError('two-output adapter requires exact local initialization, scalar loads and restored return')
    entries, rows = indices(mapping, index)
    tdata = rom[target-match.ROM_BASE:target-match.ROM_BASE+2]
    owner.validate_span(tdata, target, rom, mapping, index)
    identity = span_record(target, target+2, entries, rows, rom)
    if identity['instrs'] != 1 or any(int(row['rom'],16) < target+4 and
            int(row['end'],16) > target+2 for row in entries):
        raise ValueError('two-output thunk requires complete indexed BX and separate padding')
    canonical, = thunk.dependencies(['_call_via_r2'], rom)
    if len({address, getter, target}) != 3:
        raise ValueError('two-output dependency owners must be distinct')
    getter_frame = frame.prove_frame(li, le, getter, {}, {}, call_preservation={})
    # Every frame transition below follows from the complete exact body above.
    # There are no remaining unclassified instructions or control-flow paths.
    transitions = [
        dict(site=address, operation='save entry R4 and LR', sp_after=-8),
        dict(site=address+2, operation='allocate two local words', sp_after=-16),
        dict(site=address+6, operation='R2 = entry SP - 12', sp_after=-16),
        dict(site=address+8, operation='R1 = entry SP - 16', sp_after=-16),
        dict(site=address+10, operation='getter initializes both distinct local words; R1/R2 retained', sp_after=-16),
        dict(site=address+14, operation='R0 = initialized local word at entry SP - 16', sp_after=-16),
        dict(site=address+16, operation='R1 local pointer replaced by descriptor word zero', sp_after=-16),
        dict(site=address+18, operation='R2 local pointer replaced by descriptor word four', sp_after=-16),
        dict(site=address+20, operation='conditional returning callback; no local pointer argument', sp_after=-16),
        dict(site=address+24, operation='release local words', sp_after=-8),
        dict(site=address+26, operation='restore entry R4', sp_after=-4),
        dict(site=address+28, operation='restore entry LR into R1', sp_after=0),
        dict(site=address+30, operation='return through original entry LR; callback R0 retained', sp_after=0),
    ]
    observed = dict(schema=SELECTOR, inventory_only=True, address=address, end=address+32,
        instructions=14, body_sha256=sha(data), partition=partition,
        getter=dict(address=getter, end=getter+10, body_sha256=sha(leaf), partition=lp,
            frame=getter_frame, ordered_effects=[
                ['read','entry R0',4,4], ['write','helper R1',0,4],
                ['read','entry R0',0,4], ['write','helper R2',0,4]],
            preserved_output_registers=[1,2]),
        conditional_frame=dict(local_interval=[-16,-8], saved_words=[[-8,'entry R4'],[-4,'entry LR']],
            transitions=transitions, saved_words_overwritten=False, original_return_restored=True,
            local_word_initialization=[dict(offset=-16,source_offset=4,site=address+10),
                                       dict(offset=-12,source_offset=0,site=address+10)],
            local_pointer_argument_sites=[address+10], local_pointer_escape_to_final_callback=False),
        callback=dict(site=address+20, thunk=target, canonical=canonical,
            target='descriptor word at offset 4',
            arguments=['word read from entry node offset 4', 'descriptor word at offset 0'],
            unused_initialized_word='word read from entry node offset 0 at local entry SP - 12',
            result='unchanged callback R0', descriptor_address_passed_as_argument=False),
        explicit_conditions=[
            'Entry R0 denotes two aligned initialized readable node words; entry R1 denotes two aligned initialized readable descriptor words.',
            'The private16-byte local/saved frame is aligned live writable memory, does not wrap, and does not alias node/descriptor inputs, callback-visible memory or code.',
            'The descriptor target is compatible returning Thumb code preserving R4-R11/SP, the saved frame and continuation code.',
            'Loaded node/descriptor words carry no tracked private-frame or saved-return provenance; ordinary memory noninterference remains a premise.'],
        claim='Under the explicit conditions, the complete helper initializes two distinct local words in recorded order; the adapter consumes the node+4 word, clears both local pointer argument registers before the descriptor callback, restores its frame and original return, and returns callback R0 unchanged.',
        actual_callback_ABI_established=False, actual_memory_permissions_established=False,
        numeric_nonalias_proved=False, object_lifetime_established=False,
        C_initialization_established=False, termination_proved=False, source_or_ELF_admission=False,
        ROM_sha256=sha(rom), mapping_sha256=sha(mapping), index_sha256=sha(index),
        producer_source_sha256={Path(module.__file__).name:sha(Path(module.__file__).read_bytes())
            for module in (match, match.armv4t,owner,graph,thunk,frame)})
    observed['producer_source_sha256'][Path(__file__).name] = sha(Path(__file__).read_bytes())
    observed['producer_source_sha256']['two_word_callback_closure_profile.py'] = sha(
        (Path(__file__).parent/'two_word_callback_closure_profile.py').read_bytes())
    if manifest is not None and json.dumps(observed,sort_keys=True) != json.dumps(manifest,sort_keys=True):
        raise ValueError('two-output adapter inventory manifest differs')
    return observed
