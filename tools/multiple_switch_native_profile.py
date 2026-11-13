"""Source-bound admission for complete ordinary owners with multiple switches."""
import copy
import hashlib
import importlib
from pathlib import Path

import multiple_switch_owner_prerequisite as prerequisite

SELECTOR = 'ordinary-multiple-switch-source-v1'
SCHEMA = 'elf-symbol-thumb-ordinary-multiple-switch-source-v1'
CONTROL_FLOW = ('complete acyclic Thumb owner; original ELF-bound guarded switches, '
                'ordinary returning-call ABI and restoring frame')


def environment_fingerprint():
    from addressed_signed_runtime_profile import toolchain_fingerprint, runtime_fingerprint
    names = ('match', 'owner_admission_profile', 'multiple_switch_owner_prerequisite',
             'multiple_switch_native_profile', 'owner_graph_profile', 'owner_runtime_profile',
             'framed_switch_inventory', 'local_long_branch_profile',
             'one_constant_scalar_switch_inventory', 'software_double_profile', 'analyze',
             'addressed_signed_runtime_profile')
    return dict(toolchain=toolchain_fingerprint(), runtime=runtime_fingerprint(),
        producers={name: hashlib.sha256(Path(importlib.import_module(name).__file__).read_bytes()).hexdigest()
                   for name in names})


def verify_original(original, linked, address, rom, mapping, index, bindings, manifest=None):
    """Authenticate actual source-produced objects without synthesizing ELF inputs."""
    import owner_admission_profile as owner
    before = environment_fingerprint()
    checked = prerequisite.verify(original, linked, address, rom, mapping, index,
                                  selector=prerequisite.SELECTOR)
    expected = dict(calls=[[site-address, name] for site, name in checked['bindings']],
                    data=[], functions=[], switches=[list(row) for row in checked['local_relocations']])
    if type(bindings) is not dict or bindings != expected:
        raise ValueError('multiple-switch native bindings differ from actual original ELF roles')
    if before != environment_fingerprint():
        raise ValueError('multiple-switch native producers, toolchain or runtime changed')
    result = dict(profile=SCHEMA, selector=SELECTOR, bindings=copy.deepcopy(bindings),
        prerequisite=checked, environment=before,
        contract='Complete plausible fixed-toolchain source and original ELF are separately bound by '
                 'native compilation and report replay. Ordinary callees are conditional returning '
                 'ABI boundaries. No actual callee memory effects, numeric equivalence, arbitrary '
                 'memory permissions, physical separation or termination theorem is inferred.')
    if manifest is not None and owner.text(manifest) != owner.text(result):
        raise ValueError('multiple-switch source manifest differs from fresh original replay')
    return result, checked['instructions']
