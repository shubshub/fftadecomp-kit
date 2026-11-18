"""The MP2K memory command's conditional callback under the installed-track entry ABI."""
import hashlib
from pathlib import Path
import struct
import subprocess
import sys

SELECTOR = 'm4a-engine-track-thunks-v1'
SCHEMA = 'elf-symbol-thumb-m4a-engine-track-thunks-v1'
SUMMARY = ('one guarded 18-case m4a switch and canonical callback, conditional on entry r1 '
           'being an installed engine track and the active stack being disjoint from the callback word')
CONTROL_FLOW = 'guarded local Thumb switch and a canonical r2 thunk under the conditional returning indirect ARM ABI'
ADDRESS = 0x0814636C
END = 0x081464C4
ROM_BASE = 0x08000000
TOOLCHAIN = 'old-agbcc-O2-v1'
UNIT = (0x08145098, 0x081465E6, 'eb1dabb1596575e3beec4fded0c77337efbd1ffd8e67a885d26f601a316bb85e')
CALL = 0x081464AC
CALLBACK = 0x02008E64
BODY_HASH = '6da6f6ccf80d70821afaecba17c6ee11510857218c0a7d1eba25878f7fac2eab'

# Reviewed ROM code fixes the interpretation of the three 12-byte table entries.
# SoundInit passes the ROM table to MPlayOpen; MPlayOpen installs tracks and count.
# MPlayMain reads both at 08144B7C, advances r5 by 0x50 at 08144CA4 and
# passes r5 in r1 at 08144C28. SoundInit and MPlayExtender install the handler
# table and its slot 8 (081455BC and 08145442).
DEPENDENCIES = (
    (0x0814513C, 0x081451B4, '006ed3db573bc9aee356fe171e253024335078859f86b926b586d139fd603f9f'),
    (0x08145834, 0x081458AC, 'f4989def85c55f0450a8d7cc5b1b7aa66c2940d8725d47a1f84b90b75bb62228'),
    (0x08144B2C, 0x08144D94, '4f4cf6bd8dff5e295b0849673abfc547f5de75ed27a700133005158c2d05c37e'),
    (0x0814553C, 0x08145608, 'e94a015e3d7b691e0c020e05509c3b94b334005bfc67a3c0c5dbed792bab04d7'),
    (0x081453F8, 0x08145514, '11f693509230d88f242591b79f657ab1967377583ec4bbb1789f82d347e8290c'),
)
TRACKS = ((0x0200F2A0, 0x03005670, 16), (0x0200F2E0, 0x03005B70, 6),
          (0x0200F320, 0x03005D50, 3))


def unit_owner(unit, address, orphan=None):
    start, end, digest = UNIT
    return (address == ADDRESS and orphan is None and unit is not None and
            (unit.start, unit.end, unit.toolchain, unit.proof) == (start, end, TOOLCHAIN, 0x08146264) and
            unit.row['identity'] == [{'address': f'0x{start:08X}', 'size': end - start, 'sha256': digest}])


def entry_contract(rom, address, data):
    if type(rom) is not bytes or address != ADDRESS or len(data) != END - ADDRESS or \
            hashlib.sha256(data).hexdigest() != BODY_HASH or data != rom[ADDRESS - ROM_BASE:END - ROM_BASE]:
        raise ValueError('m4a track proof requires the exact reviewed memory-command owner')
    for start, end, digest in DEPENDENCIES:
        if hashlib.sha256(rom[start - ROM_BASE:end - ROM_BASE]).hexdigest() != digest:
            raise ValueError('m4a engine entry dependency differs from the reviewed ROM')
    count, table = struct.unpack_from('<II', rom, 0x081451A8 - ROM_BASE)
    records = [struct.unpack_from('<IIB', rom, table - ROM_BASE + i * 12) for i in range(count)]
    if tuple(records) != TRACKS:
        raise ValueError('m4a installed track table differs from the reviewed registrations')
    tracks = [base + i * 0x50 for _, base, n in records for i in range(n)]
    if any(track % 4 or not 0x03000000 <= track <= 0x03008000 - 0x50 or
           track + 0x40 < CALLBACK + 4 and CALLBACK < track + 0x44 for track in tracks):
        raise ValueError('m4a track cursor is unaligned or overlaps the callback word')
    return {'entry_r1': 'one track in the installed ROM table (stride 80); arbitrary external inputs excluded',
            'stack': 'active saved-register stack disjoint from the callback word',
            'indirect_call': 'target returns under the ordinary ARM ABI; target body and effects unproved',
            'registrations': [list(record) for record in records], 'callback_slot': CALLBACK,
            'dependencies': [list(row) for row in DEPENDENCIES]}


def verified_callback(instructions, edges, address, calls, data, rom, objects):
    """Establish the origin of the thunk register on every predecessor of the BL."""
    from capstone.arm import ARM_REG_R6
    entry_contract(rom, address, data)
    if calls != {CALL: 0x0814224C} or objects != {0x148: ('data_02008E60', CALLBACK)}:
        raise ValueError('m4a track proof requires the original r2 thunk and slot-one object relocation')
    predecessors = {site: set() for site in instructions}
    for site, successors in edges.items():
        for target in successors:
            predecessors[target].add(site)
    # Follow the actual linked CFG backwards. The PC-relative load selects the
    # authenticated word, the following dereference writes r2, and neither
    # argument move writes r2. No alternative predecessor can bypass them.
    for site in (CALL, CALL - 2, CALL - 4, CALL - 6):
        if predecessors[site] != {site - 2}:
            raise ValueError('alternative edge into m4a callback load sequence')
    if data[CALL - 8 - address:CALL - address] != bytes.fromhex('03480268201c311c') or \
            struct.unpack_from('<I', data, 0x148)[0] != CALLBACK:
        raise ValueError('m4a callback load sequence differs')
    cone, pending = set(), [CALL]
    while pending:
        site = pending.pop()
        if site not in cone:
            cone.add(site)
            pending.extend(predecessors[site])
    # All non-stack stores that can reach the callback write exactly [r6+64].
    # r6 is the incoming track: the one writer copies entry r1 in the straight
    # prologue before r1 is used for anything else. Cases that store through
    # the player's memory area return without entering the callback cone.
    stores = {site for site in cone if instructions[site].mnemonic.startswith(('str', 'stm'))}
    track_writers = {site for site in cone if ARM_REG_R6 in instructions[site].regs_access()[1]}
    if stores != {0x08146378, 0x08146382, 0x08146388} or track_writers != {address + 4} or \
            data[:6] != bytes.fromhex('70b5041c0e1c') or any(
                int.from_bytes(instructions[site].bytes, 'little') & 0xFFF8 != 0x6430 for site in stores) or \
            any(instructions[site].mnemonic == 'push' for site in cone - {address}):
        raise ValueError('m4a callback predecessor stores or entry track provenance differ')
    return CALL


def replay(root, report, data):
    """Recompile the current source and original ELF bindings with the fixed unit compiler."""
    import match
    import library_units
    if not library_units.report_admitted(report, root, ADDRESS) or \
            library_units.report_toolchain(report) != TOOLCHAIN:
        return False
    root = Path(root).resolve()
    try:
        run = match._run_replay_process([sys.executable, match.__file__, '--root', str(root),
            f'{ADDRESS:08X}', '--unit-toolchain', TOOLCHAIN, '--switch-data-profile', SELECTOR,
            '--no-write'], root, 120)
    except (OSError, subprocess.SubprocessError):
        return False
    lines = run.stdout.splitlines()
    return (run.returncode == 0 and 'verdict MATCH - byte identical' in lines and
            f'got     {data.hex()}' in lines)
