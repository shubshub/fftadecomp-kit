"""A returning CpuSet input contract for the phased scene's three palette copies."""

import argparse

import bios_cpuset_fill_profile as cpuset
import inert_spin_profile as native
import owner_graph_profile as graph
import volatile_semantics as semantics

OWNER, END = 0x08110888, 0x08110FE0
SITES = (0x08110BC8, 0x08110BD4, 0x08110F88)
SELECTOR = 'conditional-scheduler-palette-copy-v1'
SCHEDULER = 'conditional-scheduler-call-site-summaries-v1'
SCHEMA = 'elf-symbol-thumb-' + SCHEDULER
RECORD = '* allowlisted volatile CpuSet copies: '
PREMISE = ('conditional returning GBA BIOS CpuSet consumes only R0-R2; no guaranteed '
           'register overwrite, numeric result, memory preservation or termination')


class CopyInputs:
    """Leave all output, call-site, memory barrier and ordinary call rules intact."""

    def __init__(self, ordinary):
        self.ordinary = ordinary
        self.conditional_premises = {cpuset.NAME: PREMISE}

    def __call__(self, name):
        if name == cpuset.NAME:
            return {'r0', 'r1', 'r2'}, set()
        return self.ordinary(name)


def native_inputs(address, rom, mapping, index):
    import owner_admission_profile as owner
    if address != OWNER or not isinstance(rom, bytes):
        raise ValueError('palette-copy interface requires its indexed scene')
    base = semantics.ROM_BASE
    data = rom[OWNER-base:END-base]
    native.validate_span(data, OWNER, rom, mapping, index)
    native.validate_span(cpuset.WRAPPER, cpuset.ADDRESS, rom, mapping, index)
    refinement = owner.refine(data, address, mapping)
    instructions, edges, branches, calls, words = graph.graph(data, address, refinement)
    graph.partition(data, address, refinement, instructions, words)
    sites = sorted(site for site, target in calls.items() if target == cpuset.ADDRESS)
    if branches or words or tuple(sites) != SITES:
        raise ValueError('expected three direct, reachable palette copies in the scene')
    for site in sites:
        # MOVS R2,#95 immediately dominates the BL, so every call is the
        # documented halfword copy of 95 units without fill or reserved bits.
        if [pc for pc, successors in edges.items() if site in successors] != [site-2] or \
                bytes(instructions[site-2].bytes) != b'\x5f\x22':
            raise ValueError('palette copy requires MOVS R2,#95 on every reaching path')


def records(address, rom, mapping, index, ordinary, real, stripped, perturbed, source, entry):
    native_inputs(address, rom, mapping, index)
    if not isinstance(ordinary, semantics.RomInterfaces):
        raise ValueError('palette copies require ordinary native interfaces')
    results = semantics.compare(real, stripped, source, entry['symbol'],
                                entry['declaration'], perturbed, CopyInputs(ordinary))
    if len(results) != 1 or results[0][0] != f'func_{OWNER:08X}' or \
            not any(getattr(item, 'loop_induction', False) for item in results[0]):
        raise ValueError('expected the complete scene with all three induction compiles')
    return [semantics.record(entry['symbol'], results, perturbed=True),
            RECORD + f'`{SELECTOR}`, exact indexed {cpuset.NAME} (svc #0x0B; bx lr), '
            + '95 halfwords at ' + ', '.join(f'0x{site:08X}' for site in SITES) + '; ' + PREMISE]


def issue(root, address, args):
    """The independently checked owner remains the full scheduler v1 proof."""
    import owner_admission_profile as owner
    if address != OWNER or args.owner_runtime_profile != SELECTOR:
        raise ValueError('palette-copy scheduler selector used outside its scene')
    return owner.issue(root, address, argparse.Namespace(**{**vars(args), 'owner_runtime_profile': SCHEDULER}))
