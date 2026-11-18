"""Finite twelve-record stack list passed to the USA history state initializer."""
from hashlib import sha256
import sys
from pathlib import Path

import function_thunk_profile as thunk
import history_word_copy as history
import owner_graph_profile as graph

OWNER, END = 0x080C6858, 0x080C68EC
UNITS, FLAG = 0x02002FC4, 0x030028A0
CALLS = [[72,'_call_via_r2'],[104,'func_08022840'],[126,'func_080C62CC']]
DATA = [[56,'data_030028A0',0],[140,'g_callbacks_0836D4B8',0],[144,'data_030028A0',0]]
DIGEST = '12a56ab7fbd5cd7926b678e0dba8a0e8a2b1c594f555a3dfe7b3d7c198419b1c'


def require(condition, message):
    if not condition:
        raise ValueError('history unit list: ' + message)


def selection(count, active):
    """Offsets from entry SP of initialized words, and the value in each."""
    require(type(count) is int and 0 <= count <= 12, 'unproved producer count')
    require(type(active) is int and 0 <= active < 1 << count, 'mask escapes the input records')
    selected = []
    for index in range(count):
        if active & (1 << index):
            selected.append((-64+4*len(selected), UNITS+0x108*index))
    return selected


def consumer(rom, mapping):
    # The compiled initializer saves the caller's callee-saves, retains the
    # list address in R5, and uses R1 strictly as a word-load cursor. Its
    # own output cursor R3 is freshly based on the independent heap payload.
    # No use outside this prefix observes the incoming list or final cursor:
    # R1/R3 are redefined before use on both paths (R3 is dead on entry to
    # either history arm), and R5 is next assigned the named palette buffer.
    from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
    start,end = history.OWNER,history.END
    require(sha256(rom[start-history.BASE:end-history.BASE]).hexdigest() == history.BODY,
            'changed complete consumer')
    decoder = Cs(CS_ARCH_ARM,CS_MODE_THUMB)
    def block(start,end):
        return [i.mnemonic+' '+i.op_str for i in decoder.disasm(
            rom[start-history.BASE:end-history.BASE],start)]
    require(block(0x080C62EA,0x080C6306) == [
        'cmp r4, #0','ble #0x80c62fe','adds r1, r5, #0','adds r3, r6, #0','adds r2, r4, #0',
        'ldm r1!, {r0}','stm r3!, {r0}','subs r2, #1','cmp r2, #0','bne #0x80c62f4',
        'adds r1, r6, #0','adds r1, #0x6c','movs r0, #0xf','strh r0, [r1]'],
        'changed local list access or destination')
    sites = []
    # Literal pools are interspersed with executable code. Use the original
    # complete graph for the carrier's remaining uses.
    import owner_admission_profile as admission
    raw = rom[start-history.BASE:end-history.BASE]
    refined = admission.refine(raw,start,mapping)
    ops = graph.graph(raw,start,refined)[0]
    for pc,instruction in sorted(ops.items()):
        if pc <= 0x080C63E6 and 'r5' in instruction.op_str:
            sites.append(pc)
    require(sites == [start,start+4,0x080C62EE,0x080C63E6],
            'unexpected use of local-address carrier before palette reload')
    require(ops[0x080C63E6].mnemonic == 'ldr' and '[pc,' in ops[0x080C63E6].op_str,
            'palette pointer must replace input list')
    return {'source_parameter':'R1','first_word_read':0x080C62F4,'heap_word_write':0x080C62F6,
            'source_address_retained':False,'source_values_retained':True}


def prove(data, address, rom, mapping, index, objects, bindings, ins, edges, calls, refinement):
    import finite_local_word_loop_profile as finite
    import match
    import owner_runtime_profile as operations
    from software_double_profile import indices,span_record
    require(address == OWNER and len(data) == END-OWNER and sha256(data).hexdigest() == DIGEST,
            'expected the complete original 148-byte owner')
    require(bindings == dict(calls=CALLS,data=DATA,functions=[],switches=[]) and
            calls == {OWNER+72:thunk.ALIASES['_call_via_r2'],OWNER+104:0x08022840,OWNER+126:history.OWNER},
            'changed complete original relocation set or native BL')
    names = match.parse_data_symbols(objects)
    require(names.get('data_030028A0') == FLAG and names.get('g_callbacks_0836D4B8') == 0x0836D4B8,
            'wrong flag or installed callback manager')
    entries,rows = indices(mapping,index)
    for s,e,count in ((OWNER,END,65),(history.OWNER,history.END,199),(0x08022840,0x08022854,7),
                       (0x0814224C,0x0814224E,1)):
        row = span_record(s,e,entries,rows,rom)
        require(row['instrs'] == count, 'changed caller, allocator, veneer or consumer extent')
    operations.verify_operations(ins,edges,OWNER,{},calls,refinement)
    history.provider(rom,mapping,index)
    from scheduler_zero_descriptor import IMAGE,DESTINATION
    import installed_zero_effects as zero
    payload = rom[IMAGE-history.BASE:IMAGE-history.BASE+176]
    empty = zero.verify_conditional(payload,DESTINATION,DESTINATION,0,selector=zero.SELECTOR)['cases'][0]
    require(empty['writes'] == [('stack',-4,4)] and empty['protected_return'] and empty['SP_restored'],
            'zero-length record clear changed')
    for count in range(1,13):
        require(history.aligned_manager_clear(payload,UNITS,count*0x108) ==
                (UNITS,UNITS+count*0x108,count*66),'unfiltered record clear escapes input')
    # history.provider verifies both authentic call sites, the two word loops,
    # the literal stride, initial selects and the installed aligned clear. On
    # the unfiltered branch each output is written. On the filtered branch
    # the compare/BEQ either skips this record or appends it. In both cases
    # the record cursor advances once and the remaining count drops once.
    # Each prefix has exactly its selected count initialized, with all other
    # slots unread. The initialized array contains unit addresses, never SP.
    expected = {'push {r4, r5, r6, lr}':OWNER,'sub sp, #0x30':OWNER+2,
                'add sp, #0x30':0x080C68DC,'pop {r4, r5, r6}':0x080C68DE,
                'pop {r1}':0x080C68E0,'bx r1':0x080C68E2}
    for op,pc in expected.items():
        require(ins[pc].mnemonic+' '+ins[pc].op_str == op,'changed saved-frame lifetime')
    sink = consumer(rom,mapping)
    return dict(schema=finite.SCHEMA,instructions=len(ins),calls=CALLS,runtime_calls=[],
        partition=graph.partition(data,address,refinement,ins,{}),
        thunk_dependencies=thunk.dependencies(['_call_via_r2'],rom),
        finite_local_words=dict(script_calls=[0x08124CC4,0x08125744],script_count=12,
            records=[UNITS,UNITS+12*0x108],stride=0x108,active_byte=4,
            local_frame=[-64,-16],protected_saves=[-16,0],selected_count=[0,12],
            all_active=selection(12,0xFFF),consumer=sink,
            allocated_bytes=180,returned='same heap state, independent of the expired 48-byte list'),
        premises=['The two script calls pass twelve live, readable unit records at 02002FC4. '
                  'Any other invocation requires the same unit storage and a count in 0..12. '
                  'When the flag is clear the input records must also be writable.',
                  'Both private aligned IWRAM frames are separate from the mode flag at 030028A0. The root heap and frames satisfy the installation '
                  'and noninterference contract of 080C62CC. Allocation succeeds; the initialized '
                  '180-byte state and installed code remain live through return.'],
        producer_sha256={Path(module.__file__).name:sha256(Path(module.__file__).read_bytes()).hexdigest()
                         for module in (sys.modules[__name__],history)})
