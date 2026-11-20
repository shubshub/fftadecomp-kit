"""Explicit source admission for conditional addressed signed-runtime calls.

This authenticates the actual runtime entries and ordinary returning ARM ABI
boundary. It supplies no numeric division/remainder result or domain theorem.
"""
import argparse
from contextvars import ContextVar
import hashlib
import importlib
import json
import os
from pathlib import Path
import platform
import re
import shlex
import shutil
import struct
import subprocess
import sys
import tempfile

import divsi3_profile as quotient
import m4a_max_lines as max_lines
import modsi3_profile as remainder
import rom_mirror
import umodsi3_profile as unsigned_remainder

SELECTOR = 'addressed-signed-runtime-v1'
SCHEMA = 'elf-symbol-thumb-addressed-signed-runtime-v1'
READONLY_SELECTOR = 'addressed-signed-runtime-readonly-word0-v1'
READONLY_SCHEMA = 'elf-symbol-thumb-addressed-signed-runtime-readonly-word0-v1'
READONLY_TWO_SELECTOR = 'addressed-signed-runtime-readonly-two-words-v1'
READONLY_TWO_SCHEMA = 'elf-symbol-thumb-addressed-signed-runtime-readonly-two-words-v1'
DATA_SELECTOR = 'addressed-signed-runtime-data-v1'
DATA_SCHEMA = 'elf-symbol-thumb-addressed-signed-runtime-data-v1'
COMPILER_DATA_SELECTOR = 'compiler-signed-runtime-data-v1'
COMPILER_BIOS_SCALAR_DATA_SELECTOR = 'compiler-signed-runtime-bios-fill-scalar-control-data-v1'
COMPILER_DATA_SCHEMA = 'elf-symbol-thumb-compiler-signed-runtime-data-v1'
COMPILER_TWO_DATA_SELECTOR = 'compiler-signed-runtime-readonly-two-words-data-v1'
COMPILER_TWO_DATA_SCHEMA = 'elf-symbol-thumb-compiler-signed-runtime-readonly-two-words-data-v1'
COMPILER_THREE_DATA_SELECTOR = 'compiler-signed-runtime-readonly-three-words-data-v1'
COMPILER_THREE_DATA_SCHEMA = 'elf-symbol-thumb-compiler-signed-runtime-readonly-three-words-data-v1'
COMPILER_MMIO_DATA_SELECTOR = 'compiler-signed-runtime-numeric-mmio-data-v1'
COMPILER_MMIO_DATA_SCHEMA = 'elf-symbol-thumb-compiler-signed-runtime-numeric-mmio-data-v1'
COMPILER_MMIO_FOUR_DATA_SELECTOR = 'compiler-signed-runtime-readonly-four-words-numeric-mmio-data-v1'
COMPILER_MMIO_FOUR_DATA_SCHEMA = 'elf-symbol-thumb-compiler-signed-runtime-readonly-four-words-numeric-mmio-data-v1'
COMPILER_MMIO_SELECTORS = (COMPILER_MMIO_DATA_SELECTOR, COMPILER_MMIO_FOUR_DATA_SELECTOR)
# Compiler-emitted __divsi3/__modsi3 names beside canonical _call_via_rN thunks.
COMPILER_THUNKS_DATA_SELECTOR = 'compiler-signed-runtime-thunks-data-v1'
COMPILER_THUNKS_DATA_SCHEMA = 'elf-symbol-thumb-compiler-signed-runtime-thunks-data-v1'
COMPILER_SELECTORS = (COMPILER_BIOS_SCALAR_DATA_SELECTOR, COMPILER_DATA_SELECTOR, COMPILER_TWO_DATA_SELECTOR, COMPILER_THREE_DATA_SELECTOR,
                      *COMPILER_MMIO_SELECTORS, COMPILER_THUNKS_DATA_SELECTOR)
READONLY_TWO_DATA_SELECTOR = 'addressed-signed-runtime-readonly-two-words-data-v1'
READONLY_TWO_DATA_SCHEMA = 'elf-symbol-thumb-addressed-signed-runtime-readonly-two-words-data-v1'
READONLY_TWO_DATA_SELECTORS = (READONLY_TWO_DATA_SELECTOR, COMPILER_TWO_DATA_SELECTOR)
CALLBACK_SELECTOR = 'addressed-signed-runtime-r2-callback-data-v1'
CALLBACK_SCHEMA = 'elf-symbol-thumb-addressed-signed-runtime-r2-callback-data-v1'
R3_CALLBACK_SELECTOR = 'addressed-signed-runtime-r3-callback-data-v1'
R3_CALLBACK_SCHEMA = 'elf-symbol-thumb-addressed-signed-runtime-r3-callback-data-v1'
# Any canonical _call_via_rN thunks, each target a word loaded from memory on
# every path; the callee stays opaque.  The data variant requires typed data.
THUNKS_SELECTOR = 'addressed-signed-runtime-thunks-v1'
THUNKS_SCHEMA = 'elf-symbol-thumb-addressed-signed-runtime-thunks-v1'
THUNKS_DATA_SELECTOR = 'addressed-signed-runtime-thunks-data-v1'
THUNKS_DATA_SCHEMA = 'elf-symbol-thumb-addressed-signed-runtime-thunks-data-v1'
THUNK_SELECTORS = (THUNKS_SELECTOR, THUNKS_DATA_SELECTOR, COMPILER_THUNKS_DATA_SELECTOR)
UNSIGNED_SELECTOR = 'addressed-unsigned-runtime-v1'
UNSIGNED_SCHEMA = 'elf-symbol-thumb-addressed-unsigned-runtime-v1'
UNSIGNED_DATA_SELECTOR = 'addressed-unsigned-runtime-data-v1'
UNSIGNED_DATA_SCHEMA = 'elf-symbol-thumb-addressed-unsigned-runtime-data-v1'
UNSIGNED_READONLY_SELECTOR = 'addressed-unsigned-runtime-readonly-word0-v1'
UNSIGNED_BUFFER_SELECTOR = 'addressed-unsigned-runtime-native-buffer-v1'
BUFFER_SELECTOR = 'addressed-signed-runtime-native-buffer-v1'
BUFFER_DATA_SELECTOR = 'addressed-signed-runtime-native-buffer-data-v1'
UNSIGNED_BUFFER_DATA_SELECTOR = 'addressed-unsigned-runtime-native-buffer-data-v1'
BUFFER_SCRATCH_SELECTOR = 'addressed-signed-runtime-native-buffer-zero-index-discarded-scratch-v1'
BIOS_SELECTOR = 'addressed-native-bios-fill-buffer-v1'
BIOS_DATA_SELECTOR = 'addressed-native-bios-fill-buffer-data-v1'
BIOS_SCALAR_DATA_SELECTOR = 'addressed-native-bios-fill-scalar-control-data-v1'
BIOS_ZERO_EXTENDED_DATA_SELECTOR = 'addressed-native-bios-fill-zero-extended-control-data-v1'
BIOS_SCALAR_MMIO_DATA_SELECTOR = 'addressed-native-bios-fill-scalar-control-numeric-mmio-data-v1'
BIOS_SAVED_SCALAR_MMIO_DATA_SELECTOR = 'addressed-native-bios-fill-saved-scalar-control-numeric-mmio-data-v1'
BIOS_SCALAR_MMIO_CODE_IMAGE_SELECTOR = 'addressed-native-bios-fill-scalar-control-numeric-mmio-code-image-data-v1'
BIOS_SCALAR_CODE_IMAGE_SELECTOR = 'addressed-native-bios-fill-scalar-control-code-image-data-v1'
CODE_IMAGE_SELECTORS = (BIOS_SCALAR_MMIO_CODE_IMAGE_SELECTOR, BIOS_SCALAR_CODE_IMAGE_SELECTOR)
NUMERIC_MMIO_SELECTORS = (BIOS_SCALAR_MMIO_DATA_SELECTOR, BIOS_SAVED_SCALAR_MMIO_DATA_SELECTOR,
                          BIOS_SCALAR_MMIO_CODE_IMAGE_SELECTOR)
BIOS_R2_ORDINARY_DATA_SELECTOR = 'addressed-native-bios-ordinary-r2-callback-data-v1'
BIOS_READONLY_DATA_SELECTOR = 'addressed-native-bios-fill-readonly-word0-data-v1'
BIOS_READONLY_TWO_SELECTOR = 'addressed-native-bios-fill-readonly-two-words-v1'
BIOS_READONLY_THREE_DATA_SELECTOR = 'addressed-native-bios-fill-readonly-three-words-data-v1'
BIOS_READONLY_FOUR_DATA_SELECTOR = 'addressed-native-bios-fill-readonly-four-words-data-v1'
MENU_RING_SELECTOR = 'addressed-native-menu-ring-initializer-v1'
BIOS_FUNCTION_DATA_SELECTOR = 'addressed-native-bios-fill-function-literals-data-v1'
BIOS_SCALAR_FUNCTION_DATA_SELECTOR = 'addressed-native-bios-fill-scalar-control-function-literals-data-v1'
BIOS_ORDINARY_FUNCTION_DATA_SELECTOR = 'addressed-native-bios-ordinary-function-literals-data-v1'
SCALAR_CONTROL_SELECTORS = (COMPILER_BIOS_SCALAR_DATA_SELECTOR, max_lines.SELECTOR, BIOS_SCALAR_DATA_SELECTOR, BIOS_SCALAR_FUNCTION_DATA_SELECTOR,
                            BIOS_SCALAR_CODE_IMAGE_SELECTOR, *NUMERIC_MMIO_SELECTORS)
FUNCTION_DATA_SELECTORS = (MENU_RING_SELECTOR, max_lines.SELECTOR, BIOS_FUNCTION_DATA_SELECTOR, BIOS_SCALAR_FUNCTION_DATA_SELECTOR,
                           BIOS_ORDINARY_FUNCTION_DATA_SELECTOR)
BIOS_SELECTORS = (COMPILER_BIOS_SCALAR_DATA_SELECTOR, MENU_RING_SELECTOR, max_lines.SELECTOR, BIOS_SELECTOR, BIOS_READONLY_TWO_SELECTOR, BIOS_DATA_SELECTOR, BIOS_ZERO_EXTENDED_DATA_SELECTOR, BIOS_SCALAR_DATA_SELECTOR, BIOS_SCALAR_CODE_IMAGE_SELECTOR, *NUMERIC_MMIO_SELECTORS, BIOS_READONLY_DATA_SELECTOR, BIOS_READONLY_THREE_DATA_SELECTOR, BIOS_READONLY_FOUR_DATA_SELECTOR, BIOS_FUNCTION_DATA_SELECTOR, BIOS_SCALAR_FUNCTION_DATA_SELECTOR)
BIOS_ORDINARY_SELECTOR = 'addressed-native-bios-ordinary-v1'
BIOS_ORDINARY_DATA_SELECTOR = 'addressed-native-bios-ordinary-data-v1'
BIOS_ORDINARY_READONLY_TWO_DATA_SELECTOR = 'addressed-native-bios-ordinary-readonly-two-words-data-v1'
BIOS_ORDINARY_SELECTORS = (BIOS_ORDINARY_SELECTOR, BIOS_ORDINARY_DATA_SELECTOR, BIOS_R2_ORDINARY_DATA_SELECTOR, BIOS_ORDINARY_READONLY_TWO_DATA_SELECTOR, BIOS_ORDINARY_FUNCTION_DATA_SELECTOR)
BIOS_ORDINARY_CONTRACT = ('exact CpuSet SWI0B returning wrapper under conditional ordinary '
                          'r4-r11/SP preserving ABI; all arguments have no local stack provenance; '
                          'typed named object identity only; no BIOS memory effects, source or '
                          'destination bounds, physical readability/nonalias, numeric results '
                          'or termination theorem')
BUFFER_SELECTORS = (*BIOS_SELECTORS, BUFFER_SCRATCH_SELECTOR, BUFFER_SELECTOR, BUFFER_DATA_SELECTOR, UNSIGNED_BUFFER_SELECTOR,
                    UNSIGNED_BUFFER_DATA_SELECTOR)
UNSIGNED_SELECTORS = (UNSIGNED_SELECTOR, UNSIGNED_DATA_SELECTOR)
INTEGER_SELECTOR = 'addressed-integer-runtime-v1'
INTEGER_DATA_SELECTOR = 'addressed-integer-runtime-data-v1'
INTEGER_READONLY_SELECTOR = 'addressed-integer-runtime-readonly-word0-v1'
INTEGER_THREE_DATA_SELECTOR = 'addressed-integer-runtime-readonly-three-words-data-v1'
INTEGER_FOUR_DATA_SELECTOR = 'addressed-integer-runtime-readonly-four-words-data-v1'
READONLY_THREE_DATA_SELECTORS = (INTEGER_THREE_DATA_SELECTOR, COMPILER_THREE_DATA_SELECTOR)
READONLY_FOUR_DATA_SELECTORS = (INTEGER_FOUR_DATA_SELECTOR, COMPILER_MMIO_FOUR_DATA_SELECTOR)
INTEGER_SELECTORS = (INTEGER_SELECTOR, INTEGER_DATA_SELECTOR, INTEGER_READONLY_SELECTOR,
                     INTEGER_THREE_DATA_SELECTOR, INTEGER_FOUR_DATA_SELECTOR)
UNSIGNED_CAPABLE_SELECTORS = (*BIOS_ORDINARY_SELECTORS, *BIOS_SELECTORS, *UNSIGNED_SELECTORS, *INTEGER_SELECTORS, UNSIGNED_READONLY_SELECTOR, UNSIGNED_BUFFER_SELECTOR,
                             UNSIGNED_BUFFER_DATA_SELECTOR, COMPILER_THUNKS_DATA_SELECTOR)
CALLBACK_SELECTORS = (MENU_RING_SELECTOR, CALLBACK_SELECTOR, R3_CALLBACK_SELECTOR, BIOS_R2_ORDINARY_DATA_SELECTOR)
DATA_SELECTORS = (*FUNCTION_DATA_SELECTORS, BIOS_READONLY_DATA_SELECTOR, BIOS_READONLY_THREE_DATA_SELECTOR, BIOS_READONLY_FOUR_DATA_SELECTOR, BIOS_ORDINARY_DATA_SELECTOR, BIOS_ORDINARY_READONLY_TWO_DATA_SELECTOR, BIOS_SCALAR_DATA_SELECTOR, BIOS_SCALAR_CODE_IMAGE_SELECTOR, BIOS_ZERO_EXTENDED_DATA_SELECTOR, *NUMERIC_MMIO_SELECTORS, BIOS_DATA_SELECTOR, DATA_SELECTOR, READONLY_TWO_DATA_SELECTOR, *CALLBACK_SELECTORS,
                  UNSIGNED_DATA_SELECTOR, INTEGER_DATA_SELECTOR, INTEGER_THREE_DATA_SELECTOR,
                  INTEGER_FOUR_DATA_SELECTOR, BUFFER_DATA_SELECTOR, UNSIGNED_BUFFER_DATA_SELECTOR,
                  *COMPILER_SELECTORS, THUNKS_DATA_SELECTOR)
# The BIOS fill data selectors classify reached untyped hardware-window words as
# owner_admission_profile numeric hardware words: the twelve named
# addressed-native-bios-fill-*-data-v1, the menu ring initializer and the
# MPlayExtender max-lines selector.  Every member is in both BIOS_SELECTORS and
# DATA_SELECTORS, but the set is written out: a selector added to both gains
# this class only when it is also added here.
NUMERIC_HARDWARE_SELECTORS = (
    MENU_RING_SELECTOR, max_lines.SELECTOR, BIOS_DATA_SELECTOR, BIOS_ZERO_EXTENDED_DATA_SELECTOR,
    BIOS_SCALAR_DATA_SELECTOR, BIOS_SCALAR_CODE_IMAGE_SELECTOR, BIOS_SCALAR_MMIO_DATA_SELECTOR,
    BIOS_SAVED_SCALAR_MMIO_DATA_SELECTOR, BIOS_SCALAR_MMIO_CODE_IMAGE_SELECTOR, BIOS_READONLY_DATA_SELECTOR,
    BIOS_READONLY_THREE_DATA_SELECTOR, BIOS_READONLY_FOUR_DATA_SELECTOR, BIOS_FUNCTION_DATA_SELECTOR,
    BIOS_SCALAR_FUNCTION_DATA_SELECTOR)
CALLBACK_ALIAS = '_call_via_r2'
CALLBACK_CONTRACT = ('conditional returning typed source callback via canonical r2; '
                     'r0/r1 are caller arguments, r2 is the target, not a third C formal; '
                     'no callback numeric, buffer, memory or termination equivalence facts')
R3_CALLBACK_CONTRACT = ('conditional returning typed source callback via canonical r3; '
                        'r0/r1/r2 are caller arguments, r3 is the target, not a fourth C formal; '
                        'no callback numeric, buffer, memory or termination equivalence facts')
THUNK_CONTRACT = ('conditional returning opaque callee via canonical _call_via_rN; on every path the '
                  'target register holds a full word loaded from memory through a base other than PC or SP, '
                  'never a constant, literal, stack or entry-return value; no argument reaches the callee '
                  'with stack provenance; the callee returns and obeys the r4-r11/SP preserving ARM ABI; '
                  'no callback identity, numeric, buffer, memory or termination facts')
THUNK_TARGET_POLICY = 'all-path-memory-word-load-target-v1'
DATA_CONTRACT = ('typed named ABS32 object identity only; no physical readability, '
                 'allocation, pointee type, memory safety or C semantic facts')
SCHEMAS = {MENU_RING_SELECTOR: 'elf-symbol-thumb-' + MENU_RING_SELECTOR, max_lines.SELECTOR: max_lines.SCHEMA, COMPILER_DATA_SELECTOR: COMPILER_DATA_SCHEMA,
            COMPILER_THUNKS_DATA_SELECTOR: COMPILER_THUNKS_DATA_SCHEMA,
            COMPILER_TWO_DATA_SELECTOR: COMPILER_TWO_DATA_SCHEMA,
            COMPILER_THREE_DATA_SELECTOR: COMPILER_THREE_DATA_SCHEMA,
            BIOS_SCALAR_MMIO_CODE_IMAGE_SELECTOR: 'elf-symbol-thumb-addressed-native-bios-fill-scalar-control-numeric-mmio-code-image-data-v1',
            BIOS_SCALAR_CODE_IMAGE_SELECTOR: 'elf-symbol-thumb-addressed-native-bios-fill-scalar-control-code-image-data-v1',
            BIOS_READONLY_TWO_SELECTOR: 'elf-symbol-thumb-addressed-native-bios-fill-readonly-two-words-v1',
            COMPILER_MMIO_DATA_SELECTOR: COMPILER_MMIO_DATA_SCHEMA,
            COMPILER_MMIO_FOUR_DATA_SELECTOR: COMPILER_MMIO_FOUR_DATA_SCHEMA,
            BIOS_ORDINARY_FUNCTION_DATA_SELECTOR:'elf-symbol-thumb-addressed-native-bios-ordinary-function-literals-data-v1',
            BIOS_SAVED_SCALAR_MMIO_DATA_SELECTOR:'elf-symbol-thumb-addressed-native-bios-fill-saved-scalar-control-numeric-mmio-data-v1',
            BIOS_SCALAR_MMIO_DATA_SELECTOR:'elf-symbol-thumb-addressed-native-bios-fill-scalar-control-numeric-mmio-data-v1',
            BIOS_READONLY_FOUR_DATA_SELECTOR:'elf-symbol-thumb-addressed-native-bios-fill-readonly-four-words-data-v1',
            BIOS_SCALAR_FUNCTION_DATA_SELECTOR:'elf-symbol-thumb-addressed-native-bios-fill-scalar-control-function-literals-data-v1',
            BIOS_ORDINARY_READONLY_TWO_DATA_SELECTOR:'elf-symbol-thumb-addressed-native-bios-ordinary-readonly-two-words-data-v1',
            BIOS_READONLY_THREE_DATA_SELECTOR:'elf-symbol-thumb-addressed-native-bios-fill-readonly-three-words-data-v1',
            BIOS_FUNCTION_DATA_SELECTOR:'elf-symbol-thumb-addressed-native-bios-fill-function-literals-data-v1',
            BIOS_R2_ORDINARY_DATA_SELECTOR:'elf-symbol-thumb-addressed-native-bios-ordinary-r2-callback-data-v1',
            BIOS_READONLY_DATA_SELECTOR:'elf-symbol-thumb-addressed-native-bios-fill-readonly-word0-data-v1',
            BIOS_ORDINARY_SELECTOR:'elf-symbol-thumb-addressed-native-bios-ordinary-v1',
            BIOS_ORDINARY_DATA_SELECTOR:'elf-symbol-thumb-addressed-native-bios-ordinary-data-v1',
            COMPILER_BIOS_SCALAR_DATA_SELECTOR: 'elf-symbol-thumb-' + COMPILER_BIOS_SCALAR_DATA_SELECTOR,
            BIOS_SCALAR_DATA_SELECTOR:'elf-symbol-thumb-addressed-native-bios-fill-scalar-control-data-v1',
            BIOS_SELECTOR:'elf-symbol-thumb-addressed-native-bios-fill-buffer-v1',
            BIOS_DATA_SELECTOR:'elf-symbol-thumb-addressed-native-bios-fill-buffer-data-v1',
            BIOS_ZERO_EXTENDED_DATA_SELECTOR:'elf-symbol-thumb-addressed-native-bios-fill-zero-extended-control-data-v1',
            SELECTOR: SCHEMA, READONLY_SELECTOR: READONLY_SCHEMA,
            READONLY_TWO_SELECTOR: READONLY_TWO_SCHEMA, DATA_SELECTOR: DATA_SCHEMA,
            READONLY_TWO_DATA_SELECTOR: READONLY_TWO_DATA_SCHEMA,
            CALLBACK_SELECTOR: CALLBACK_SCHEMA, R3_CALLBACK_SELECTOR: R3_CALLBACK_SCHEMA,
            THUNKS_SELECTOR: THUNKS_SCHEMA, THUNKS_DATA_SELECTOR: THUNKS_DATA_SCHEMA,
            UNSIGNED_SELECTOR: UNSIGNED_SCHEMA, UNSIGNED_DATA_SELECTOR: UNSIGNED_DATA_SCHEMA,
            UNSIGNED_READONLY_SELECTOR: 'elf-symbol-thumb-addressed-unsigned-runtime-readonly-word0-v1',
            UNSIGNED_BUFFER_SELECTOR: 'elf-symbol-thumb-addressed-unsigned-runtime-native-buffer-v1',
            BUFFER_SELECTOR: 'elf-symbol-thumb-addressed-signed-runtime-native-buffer-v1',
            BUFFER_SCRATCH_SELECTOR: 'elf-symbol-thumb-addressed-signed-runtime-native-buffer-zero-index-discarded-scratch-v1',
            BUFFER_DATA_SELECTOR: 'elf-symbol-thumb-addressed-signed-runtime-native-buffer-data-v1',
            UNSIGNED_BUFFER_DATA_SELECTOR: 'elf-symbol-thumb-addressed-unsigned-runtime-native-buffer-data-v1',
            INTEGER_SELECTOR: 'elf-symbol-thumb-addressed-integer-runtime-v1',
            INTEGER_DATA_SELECTOR: 'elf-symbol-thumb-addressed-integer-runtime-data-v1',
            INTEGER_READONLY_SELECTOR: 'elf-symbol-thumb-addressed-integer-runtime-readonly-word0-v1',
            INTEGER_THREE_DATA_SELECTOR: 'elf-symbol-thumb-addressed-integer-runtime-readonly-three-words-data-v1',
            INTEGER_FOUR_DATA_SELECTOR: 'elf-symbol-thumb-addressed-integer-runtime-readonly-four-words-data-v1'}
OPERATIONS = {'func_081426B8': quotient.ADDRESS, remainder.ADDRESSED_NAME: remainder.ADDRESS}
COMPILER_ALIASES = {'__divsi3': 'func_081426B8', '__modsi3': remainder.ADDRESSED_NAME}
COMPILER_CONTRACT = ('actual compiler-emitted signed-runtime names at original Thumb BL relocations; '
                     'explicit runtime identifiers excluded from preprocessed C; '
                     'original and linked ELF names preserved; exact canonical runtime identities; '
                     'conditional returning ARM ABI only, no numeric result, definedness, '
                     'termination or arithmetic C equivalence theorem')
UNSIGNED_OPERATIONS = {'func_08142AB0': 0x08142AB0,
                       'func_08142B28': unsigned_remainder.ADDRESS}
# The compiler thunks route also binds the compiler's unsigned runtime names
# beside a signed one, each to its pinned entry and identity.
COMPILER_THUNK_ALIASES = dict(COMPILER_ALIASES, __udivsi3='func_08142AB0', __umodsi3='func_08142B28')
COMPILER_THUNKS_CONTRACT = ('actual compiler-emitted __divsi3/__modsi3, and __udivsi3/__umodsi3 beside them, '
                            'at original Thumb BL relocations; explicit runtime identifiers excluded from '
                            'preprocessed C; original and linked ELF names preserved; exact canonical '
                            'runtime identities; conditional returning ARM ABI only, no numeric result, '
                            'definedness, termination or arithmetic C equivalence theorem')
ABI = 'conditional returning ARM ABI; arbitrary incoming word patterns; no numeric return facts'
_replay = ContextVar('addressed_signed_runtime_replay', default=False)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def text(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def compiler_aliases(selector):
    return COMPILER_THUNK_ALIASES if selector == COMPILER_THUNKS_DATA_SELECTOR or \
        COMPILER_BIOS_FILL.applies(selector) else COMPILER_ALIASES


class CompilerRuntimeBiosFill:
    """Compiler-emitted runtime names under the plain BIOS fill buffer data selector.

    That selector already binds explicit calls of the four pinned runtime
    entries.  For `/` and `%` agbcc emits the same direct BL, naming
    __udivsi3, __umodsi3, __divsi3 or __modsi3 instead.  original_bindings
    binds each such name to the canonical entry the explicit spelling names,
    so the identity pins in prepare, the walk, the buffer proof and the BIOS
    fill proof see the same bindings for either spelling.  The preprocessed C
    may then name no runtime identifier (compiler_namespace), every runtime
    call must be compiler-emitted, and the report prints each such call site
    with its name, entry and pinned identity.  Set ``enabled`` to False to
    keep the plain refusal.
    """

    enabled = True
    selectors = (BIOS_DATA_SELECTOR,)
    aliases = COMPILER_THUNK_ALIASES
    contract = ('compiler-emitted __udivsi3, __umodsi3, __divsi3 and __modsi3 names at original direct '
                'Thumb BL relocations, each bound to the pinned runtime entry of the explicit spelling and '
                'walked as that explicit call; explicit runtime identifiers excluded from preprocessed C; '
                'original and linked ELF names preserved; exact canonical runtime identities; conditional '
                'returning ARM ABI only, no numeric result, definedness, termination or arithmetic C '
                'equivalence theorem')

    def applies(self, selector):
        return self.enabled is True and selector in self.selectors

    def check(self, selector, calls, bindings, address):
        """Every runtime binding is one recorded compiler call of its own alias."""
        from match_evidence import UDIVSI3_RUNTIME
        identities = {'func_08142AB0': UDIVSI3_RUNTIME, 'func_08142B28': unsigned_remainder.RUNTIME,
                      'func_081426B8': quotient.RUNTIME, remainder.ADDRESSED_NAME: remainder.RUNTIME}
        runtime = {site for site, name in bindings.items() if name in self.aliases.values()}
        if not self.applies(selector) or type(calls) is not dict or not calls or set(calls) != runtime or \
                any(type(name) is not str or self.aliases.get(name) != bindings[site]
                    for site, name in calls.items()):
            raise ValueError('compiler runtime names require the BIOS fill buffer data selector '
                             'and every runtime call compiler-emitted')
        return dict(contract=self.contract, calls=[
            [site-address, name, self.aliases[name], identities[self.aliases[name]]]
            for site, name in sorted(calls.items())])

    def premise(self, result):
        rows = result['manifest']['compiler_runtime']
        return '* compiler runtime binding: ' + ', '.join(
            f'0x{result["address"] + offset:08X} {name} -> {entry} ({identity})'
            for offset, name, entry, identity in rows['calls']) + '; ' + rows['contract']


COMPILER_BIOS_FILL = CompilerRuntimeBiosFill()


def compiler_namespace(source, selector=COMPILER_DATA_SELECTOR):
    identifiers = set(re.findall(r'[A-Za-z_][A-Za-z_0-9]*', source))
    aliases = compiler_aliases(selector)
    if identifiers & (set(aliases) | set(aliases.values())):
        raise ValueError('compiler runtime identifiers cannot occur in preprocessed C')


def thunk_namespace(preprocessed, assembly, image, address):
    """The unsigned thunk selectors' source and assembly rules: runtime, call-via,
    asm-label, alias and weak spellings stay compiler-only, and the object
    defines only its caller."""
    import unsigned_thunk_profile as rules
    try:
        rules.namespace(preprocessed)
        rules.compiled(assembly, image, address)
    except ValueError as error:
        raise ValueError('thunk sources reserve runtime, call-via, asm-label, alias and weak '
                         'spellings for compiler emission and define only their caller') from error


def buffer_scratch_policy(selector):
    if selector != BUFFER_SCRATCH_SELECTOR:
        return None
    from local_long_branch_profile import DISCARDED_SCRATCH_SCHEMA
    return {'schema': DISCARDED_SCRATCH_SCHEMA, 'registers': [2, 3]}


def bios_fill_proof(data, address, calls, context):
    if context_selector(context) not in BIOS_SELECTORS:
        return None
    from bios_cpuset_fill_profile import BiosFillProof
    return BiosFillProof(data, address, context[0], context[1], context[2], calls,
                         zero_extension=context_selector(context) == BIOS_ZERO_EXTENDED_DATA_SELECTOR)


def context_selector(context):
    if type(context) is tuple:
        if len(context) == 5:
            return SELECTOR
        if len(context) == 6 and context[5] == READONLY_SELECTOR:
            return READONLY_SELECTOR
        if len(context) == 6 and type(context[5]) is str and context[5] == READONLY_TWO_SELECTOR:
            return READONLY_TWO_SELECTOR
        if len(context) == 6 and type(context[5]) is str and context[5] in (UNSIGNED_SELECTOR, UNSIGNED_BUFFER_SELECTOR, BUFFER_SELECTOR, BUFFER_SCRATCH_SELECTOR, BIOS_SELECTOR, BIOS_READONLY_TWO_SELECTOR, BIOS_ORDINARY_SELECTOR, INTEGER_SELECTOR, INTEGER_READONLY_SELECTOR, UNSIGNED_READONLY_SELECTOR, THUNKS_SELECTOR):
            return context[5]
        if len(context) == 8 and type(context[5]) is str and context[5] in DATA_SELECTORS:
            return context[5]
    raise ValueError('addressed signed runtimes require an exact explicit context')


def operations(selector):
    if selector in (*BIOS_SELECTORS, *BIOS_ORDINARY_SELECTORS):
        from bios_cpuset_fill_profile import NAME, ADDRESS
        if selector == COMPILER_BIOS_SCALAR_DATA_SELECTOR:
            return dict(OPERATIONS, **{NAME: ADDRESS})
        return dict(OPERATIONS, **UNSIGNED_OPERATIONS, **{NAME:ADDRESS})
    if selector in (*INTEGER_SELECTORS, COMPILER_THUNKS_DATA_SELECTOR):
        return dict(OPERATIONS, **UNSIGNED_OPERATIONS)
    return UNSIGNED_OPERATIONS if selector in (*UNSIGNED_SELECTORS, UNSIGNED_READONLY_SELECTOR, UNSIGNED_BUFFER_SELECTOR,
                                               UNSIGNED_BUFFER_DATA_SELECTOR) else OPERATIONS


def local_branches(context):
    """Only the thunk selectors admit same-owner long BL edges; finish re-proves them."""
    return context is not None and context_selector(context) in THUNK_SELECTORS


def binds_unsigned(context, site, target):
    """Only a prepared explicit unsigned context may authorize an exact entry."""
    return context is not None and context_selector(context) in UNSIGNED_CAPABLE_SELECTORS and \
        context[3].get(site) in UNSIGNED_OPERATIONS and \
        UNSIGNED_OPERATIONS[context[3][site]] == target


def object_value(name, addend, objects, entries, address, size, *, image=False):
    """The existing typed-data addend boundary, excluding code-as-data aliases.

    image=True (code-image selectors only) additionally admits a zero-addend object whose value is
    exactly one indexed entry start; the CFG-level proof of its use is cpuset_code_image_profile.
    """
    import match
    if name not in objects or type(addend) is not int or not -0x80000000 <= addend <= 0x7FFFFFFF:
        raise ValueError('addressed data requires a mapped object and signed32 addend')
    base = objects[name]
    value = base + addend
    alias = image and addend == 0 and value % 2 == 0 and \
        sum(int(row['rom'], 16) == value for row in entries) == 1 and \
        sum(int(row['rom'], 16) <= value < int(row['end'], 16) for row in entries) == 1
    if not 0 <= value <= 0xFFFFFFFF or address <= rom_mirror.canonical(value) < address + size or \
            any(match.function_thunk.reserved(target) for target in (base, value)) or not alias and any(
            int(row['rom'], 16) <= (rom_mirror.canonical(target) & ~1) < int(row['end'], 16)
            for row in entries for target in (base, value)):
        raise ValueError('addressed data overflows or aliases indexed code')
    return value


def function_literal(name, selector):
    return selector in FUNCTION_DATA_SELECTORS and isinstance(name, str) and \
        re.fullmatch(r'func_[0-9A-F]{8}', name) is not None


def data_literals(data, address, rom, mapping, objects, records, *, selector=DATA_SELECTOR):
    import match
    if type(objects) is not bytes or type(records) is not list or \
            not records and selector not in COMPILER_MMIO_SELECTORS:
        raise ValueError('addressed data requires an actual typed data snapshot and bindings')
    if not records:
        match.parse_data_symbols(objects)
        return {}  # This distinct selector still requires actual reached MMIO in finish.
    # Calls are authenticated separately by prepare; do not send reserved runtime
    # names through the ordinary function-address validator.
    if selector == max_lines.SELECTOR:
        records = max_lines.split_records(records, rom, address, data, match.parse_data_symbols(objects))
    functions, data_records = [], []
    for row in records:
        if not isinstance(row, (list, tuple)) or len(row) != 3:
            raise ValueError('addressed literal requires its complete typed binding')
        offset, name, addend = row
        if function_literal(name, selector):
            if type(addend) is not int or addend != 0:
                raise ValueError('function literals require their exact Thumb entry without an addend')
            functions.append([offset, name])
        else:
            data_records.append(list(row))
    if selector in FUNCTION_DATA_SELECTORS and not functions:
        raise ValueError('BIOS function-literal selector requires an actual typed function literal')
    calls, literals = match.function_address_bindings(data, address, rom, mapping, objects,
        {'calls': [], 'data': data_records, 'functions': functions}, allow_empty_functions=True)
    parsed, entries = match.parse_data_symbols(objects), json.loads(mapping)
    if any(name in parsed for _, name in functions):
        raise ValueError('function literal cannot also have an object identity')
    for offset, name, addend in data_records:
        value = object_value(name, addend, parsed, entries, address, len(data),
                             image=selector in CODE_IMAGE_SELECTORS)
        if literals[offset] != (name, value):
            raise ValueError('addressed data lost its typed object identity')
    if calls:
        raise ValueError('addressed data cannot introduce function bindings')
    return literals


def data_producer_fingerprint(selector=DATA_SELECTOR):
    """Pin the actual data admission, linker, CFG and source-replay producers."""
    import match
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    import local_long_branch_profile as frame
    modules = (match, match.armv4t, owner, graph, frame, quotient, remainder, match.function_thunk,
               match.software_double, match.software_float, match.ashldi3, match.umodsi3)
    paths = {Path(module.__file__) for module in modules} | {Path(__file__)}
    paths.update(Path(importlib.import_module(name).__file__) for name in
                 ('match_evidence', 'inert_spin_profile', 'analyze', 'plausible'))
    if selector in (*BIOS_SELECTORS, *BIOS_ORDINARY_SELECTORS):
        paths.add(Path(importlib.import_module('bios_cpuset_fill_profile').__file__))
    if selector == MENU_RING_SELECTOR:
        paths.update(Path(importlib.import_module(name).__file__) for name in
                     ('menu_ring_initializer', 'installed_zero_effects', 'installed_copy_effects',
                      'iwram_installation_prerequisite', 'literal_callback_closure_profile',
                      'scheduler_event_definition'))
    if selector == max_lines.SELECTOR:
        paths.add(Path(max_lines.__file__))
    if selector in CODE_IMAGE_SELECTORS:
        paths.update(Path(importlib.import_module(name).__file__) for name in
                     ('cpuset_code_image_profile', 'iwram_installation_prerequisite'))
    if selector == BIOS_READONLY_DATA_SELECTOR:
        paths.add(Path(importlib.import_module('readonly_entry_stack_profile').__file__))
    if selector in THUNK_SELECTORS:
        paths.add(Path(importlib.import_module('unsigned_thunk_profile').__file__))
    if selector in (*READONLY_TWO_DATA_SELECTORS, *READONLY_THREE_DATA_SELECTORS, *READONLY_FOUR_DATA_SELECTORS, BIOS_READONLY_THREE_DATA_SELECTOR, BIOS_READONLY_FOUR_DATA_SELECTOR, BIOS_ORDINARY_READONLY_TWO_DATA_SELECTOR):
        paths.add(Path(importlib.import_module('readonly_entry_stack_words_profile').__file__))
    return {path.name: sha(path.read_bytes()) for path in sorted(paths)}


def callback_alias(selector):
    return '_call_via_r3' if selector == R3_CALLBACK_SELECTOR else CALLBACK_ALIAS


def thunk_alias(selector, target):
    """The canonical thunk name a selector admits at this call target, if any."""
    import match
    if selector in CALLBACK_SELECTORS:
        alias = callback_alias(selector)
        return alias if target == match.function_thunk.ALIASES[alias] else None
    if selector in THUNK_SELECTORS:
        return next((name for name, value in match.function_thunk.ALIASES.items() if value == target), None)
    return None


def thunk_dependencies(rom, mapping, index, aliases):
    """Reuse canonical thunk identity, each with its actual two-byte indexed owner."""
    import match
    import owner_admission_profile as owner
    for alias in sorted(set(aliases)):
        target = match.function_thunk.ALIASES[alias]
        offset = target - match.ROM_BASE
        owner.validate_span(rom[offset:offset+2], target, rom, mapping, index)
    return match.function_thunk.dependencies(aliases, rom)


def callback_dependencies(rom, mapping, index, selector=CALLBACK_SELECTOR):
    return thunk_dependencies(rom, mapping, index, [callback_alias(selector)])


def thunk_target_loads(instructions, edges, calls, address):
    """Every path's last write of each thunk target register is a memory word load.

    A forward must-analysis over the closed CFG: a full-word ``ldr`` whose
    base is neither PC nor SP defines a loaded register; any other write, an
    entry value and every call's caller-clobbered registers do not.  Joins
    keep the union of load sites, and one non-load path removes the register.
    """
    import match
    from function_thunk_profile import ALIASES, START
    clobbered = (*range(match.ARM_REG_R0, match.ARM_REG_R0 + 4), match.ARM_REG_R12, match.ARM_REG_LR)
    states, pending = {address: {}}, [address]
    while pending:
        site = pending.pop()
        state, item = dict(states[site]), instructions[site]
        for register in clobbered if site in calls else item.regs_access()[1]:
            state.pop(register, None)
        operands = item.operands
        if site not in calls and item.mnemonic == 'ldr' and len(operands) == 2 and \
                operands[0].type == match.ARM_OP_REG and operands[1].type == match.ARM_OP_MEM and \
                operands[1].mem.base not in (match.ARM_REG_PC, match.ARM_REG_SP):
            state[operands[0].reg] = frozenset((site,))
        for successor in edges[site]:
            joined = state if successor not in states else {
                register: loads | states[successor][register]
                for register, loads in state.items() if register in states[successor]}
            if states.get(successor) != joined:
                states[successor] = joined
                pending.append(successor)
    result = []
    for site in sorted(site for site, target in calls.items() if target in ALIASES.values()):
        register = match.ARM_REG_R0 + (calls[site] - START) // 4
        loads = states.get(site, {}).get(register)
        if not loads:
            raise ValueError('thunk target requires a memory word load on every path, not a constant, '
                             'literal, stack, entry or copied value')
        result.append([site-address, next(name for name, value in ALIASES.items() if value == calls[site]),
                       sorted(load-address for load in loads)])
    if not result:
        raise ValueError('thunk selector requires an actual canonical thunk call')
    return result


def callback_r0_slot(instructions, edges, reverse, calls, site, address, bindings):
    """One closed R0 slot load, then two explicit register argument assignments."""
    import match
    chain, cursor = [], site
    for _ in range(4):
        if len(reverse[cursor]) != 1:
            return None
        previous = next(iter(reverse[cursor]))
        item = instructions[previous]
        if item.size != 2 or previous + item.size != cursor or \
                edges[previous] != (cursor,) or previous in calls:
            return None
        chain.append(item)
        cursor = previous
    literal_load, slot_load, arg0, arg1 = reversed(chain)

    def register(operand, value):
        return operand.type == match.ARM_OP_REG and operand.reg == value

    def memory(operand, base):
        return operand.type == match.ARM_OP_MEM and operand.mem.base == base and \
            not operand.mem.index and not operand.mem.disp

    operands = literal_load.operands
    if literal_load.mnemonic != 'ldr' or len(operands) != 2 or \
            not register(operands[0], match.ARM_REG_R0) or \
            operands[1].type != match.ARM_OP_MEM or \
            operands[1].mem.base != match.ARM_REG_PC or operands[1].mem.index:
        return None
    literal = ((literal_load.address + 4) & ~3) + operands[1].mem.disp - address
    if literal not in bindings or bindings[literal][1] != 0:
        return None
    operands = slot_load.operands
    if slot_load.mnemonic != 'ldr' or len(operands) != 2 or \
            not register(operands[0], match.ARM_REG_R2) or \
            not memory(operands[1], match.ARM_REG_R0):
        return None
    operands = arg0.operands
    if arg0.mnemonic != 'adds' or len(operands) != 3 or \
            not register(operands[0], match.ARM_REG_R0) or \
            operands[1].type != match.ARM_OP_REG or \
            arg0.reg_name(operands[1].reg) not in ('r4', 'r5', 'r6', 'r7') or \
            operands[2].type != match.ARM_OP_IMM or operands[2].imm != 0:
        return None
    source = arg0.reg_name(operands[1].reg)
    operands = arg1.operands
    if arg1.mnemonic != 'movs' or len(operands) != 2 or \
            not register(operands[0], match.ARM_REG_R1) or \
            operands[1].type != match.ARM_OP_IMM or not 0 <= operands[1].imm <= 255:
        return None
    return [site-address, literal_load.address-address, slot_load.address-address,
            literal, bindings[literal][0], dict(policy='r0-slot-zero-argument-setup-v1',
                base_register='r0', target_register='r2', slot_offset=0,
                argument_setup=[dict(offset=arg0.address-address, bytes=arg0.bytes.hex(),
                                     destination='r0', source=source),
                                dict(offset=arg1.address-address, bytes=arg1.bytes.hex(),
                                     destination='r1', immediate=operands[1].imm)])]


def callback_sites(instructions, edges, calls, address, records):
    """Require an unambiguous straight-line mapped slot-zero load into r2."""
    import match
    target = match.function_thunk.ALIASES[CALLBACK_ALIAS]
    reverse = {site: set() for site in instructions}
    for site, successors in edges.items():
        for successor in successors:
            reverse[successor].add(site)
    bindings = {offset: (name, addend) for offset, name, addend in records}
    result = []
    for site in sorted(site for site, value in calls.items() if value == target):
        cursor = site
        load = None
        for distance in range(8):
            predecessors = reverse[cursor]
            if len(predecessors) != 1:
                break
            previous = next(iter(predecessors))
            item = instructions[previous]
            if previous + item.size != cursor or edges[previous] != (cursor,) or previous in calls:
                break
            operands = item.operands
            if distance == 0:
                if item.mnemonic != 'ldr' or len(operands) != 2 or \
                        operands[0].type != match.ARM_OP_REG or operands[0].reg != match.ARM_REG_R2 or \
                        operands[1].type != match.ARM_OP_MEM or operands[1].mem.base != match.ARM_REG_R2 or \
                        operands[1].mem.index or operands[1].mem.disp:
                    break
                load = previous
            elif item.mnemonic == 'ldr' and len(operands) == 2 and \
                    operands[0].type == match.ARM_OP_REG and operands[0].reg == match.ARM_REG_R2 and \
                    operands[1].type == match.ARM_OP_MEM and operands[1].mem.base == match.ARM_REG_PC and \
                    not operands[1].mem.index:
                literal = ((previous + 4) & ~3) + operands[1].mem.disp - address
                if literal not in bindings or bindings[literal][1] != 0:
                    break
                result.append([site-address, previous-address, load-address,
                               literal, bindings[literal][0]])
                break
            elif match.ARM_REG_R2 in item.regs_access()[1]:
                break
            cursor = previous
        else:
            raise ValueError('r2 callback exceeds its bounded mapped-load chain')
        if not result or result[-1][0] != site-address:
            row = callback_r0_slot(instructions, edges, reverse, calls, site, address, bindings)
            if row is None:
                raise ValueError('r2 callback requires an unambiguous mapped slot-zero target load')
            result.append(row)
    if not result:
        raise ValueError('callback selector requires its actual canonical callback call')
    return result


def r3_callback_sites(instructions, edges, calls, address, records):
    """Two closed slot-zero producer shapes with three genuine argument inputs."""
    import match
    target = match.function_thunk.ALIASES['_call_via_r3']
    reverse = {site: set() for site in instructions}
    for site, successors in edges.items():
        for successor in successors:
            reverse[successor].add(site)
    bindings = {offset: (name, addend) for offset, name, addend in records}

    def register(operand, name):
        return operand.type == match.ARM_OP_REG and operand.reg == getattr(match, 'ARM_REG_' + name.upper())

    def immediate(operand):
        return operand.type == match.ARM_OP_IMM and 0 <= operand.imm <= 255

    def shape(chain):
        literal_load = chain[0]
        base = 'r0' if len(chain) == 5 else 'r2'
        ops = literal_load.operands
        if literal_load.mnemonic != 'ldr' or len(ops) != 2 or not register(ops[0], base) or \
                ops[1].type != match.ARM_OP_MEM or ops[1].mem.base != match.ARM_REG_PC or ops[1].mem.index:
            return None
        literal = ((literal_load.address + 4) & ~3) + ops[1].mem.disp - address
        if literal not in bindings or bindings[literal][1] != 0:
            return None
        source, slot, dest, size = (chain[1], chain[2], chain[3], chain[4]) if len(chain) == 5 else \
                                   (chain[3], chain[4], chain[1], chain[5])
        ops = source.operands
        if source.mnemonic != 'adds' or len(ops) != 3 or not register(ops[0], 'r1') or \
                ops[1].type != match.ARM_OP_REG or source.reg_name(ops[1].reg) not in ('r4','r5','r6','r7') or \
                not register(ops[2], 'r1'):
            return None
        ops = slot.operands
        if slot.mnemonic != 'ldr' or len(ops) != 2 or not register(ops[0], 'r3') or \
                ops[1].type != match.ARM_OP_MEM or slot.reg_name(ops[1].mem.base) != base or \
                ops[1].mem.index or ops[1].mem.disp:
            return None
        ops = dest.operands
        if dest.mnemonic != 'adds' or len(ops) != 3 or not register(ops[0], 'r0') or \
                ops[1].type != match.ARM_OP_REG or dest.reg_name(ops[1].reg) not in ('r4','r5','r6','r7') or \
                ops[2].type != match.ARM_OP_IMM or ops[2].imm != 0:
            return None
        destination = 0
        if len(chain) == 6:
            increment = chain[2]
            ops = increment.operands
            if increment.mnemonic != 'adds' or len(ops) != 2 or not register(ops[0], 'r0') or \
                    not immediate(ops[1]):
                return None
            destination = ops[1].imm
        ops = size.operands
        if size.mnemonic != 'movs' or len(ops) != 2 or not register(ops[0], 'r2') or not immediate(ops[1]):
            return None
        # Every instruction in the producer is bound. No call, branch join or
        # uninspected argument/target write can occur between these operations.
        return [literal_load.address-address, slot.address-address, literal, bindings[literal][0],
                dict(policy='r3-slot-zero-three-argument-setup-v1', base_register=base,
                     target_register='r3', slot_offset=0, destination_offset=destination,
                     producer_instructions=[dict(offset=item.address-address, bytes=item.bytes.hex())
                                            for item in chain],
                     argument_setup=[dict(offset=item.address-address, bytes=item.bytes.hex())
                                     for item in chain[1:] if item is not slot])]

    result = []
    for site in sorted(site for site, value in calls.items() if value == target):
        chain, cursor, row = [], site, None
        for _ in range(6):
            if len(reverse[cursor]) != 1:
                break
            previous = next(iter(reverse[cursor]))
            item = instructions[previous]
            if item.size != 2 or previous + 2 != cursor or edges[previous] != (cursor,) or previous in calls:
                break
            chain.insert(0, item)
            cursor = previous
            if len(chain) in (5, 6):
                row = shape(chain)
                if row is not None:
                    break
        if row is None:
            raise ValueError('r3 callback requires a bounded unambiguous mapped slot-zero three-argument producer')
        result.append([site-address, *row])
    if not result:
        raise ValueError('r3 callback selector requires an actual canonical callback call')
    return result


def prepare(data, address, calls, context):
    import match
    import owner_admission_profile as owner
    selector = context_selector(context)
    if selector == MENU_RING_SELECTOR and (address != 0x0804C8C4 or len(data) != 184):
        raise ValueError('menu ring initializer requires its complete original owner')
    if type(context[3]) is not dict or not context[3] or \
            type(context[4]) is not dict or context[4]:
        raise ValueError('addressed signed runtimes require a fresh exact context')
    rom, mapping, index, bindings, _ = context[:5]
    entries = owner.validate_span(data, address, rom, mapping, index)
    if selector in DATA_SELECTORS:
        data_literals(data, address, rom, mapping, context[6], context[7], selector=selector)
    if selector in CALLBACK_SELECTORS:
        callback_dependencies(rom, mapping, index, selector)
        if match.function_thunk.ALIASES[callback_alias(selector)] not in calls.values():
            raise ValueError('callback selector requires its actual canonical callback call')
    if selector in THUNK_SELECTORS:
        thunk_dependencies(rom, mapping, index,
                           {thunk_alias(selector, target) for target in calls.values()} - {None})
    selected_operations = operations(selector)
    if any(type(site) is not int or type(name) is not str or name not in selected_operations or
           calls.get(site) != selected_operations[name] for site, name in bindings.items()) or \
            set(bindings) != {site for site, target in calls.items() if target in selected_operations.values()}:
        raise ValueError('addressed signed runtimes require complete canonical addressed bindings')
    if selector in INTEGER_SELECTORS and not (
            set(bindings.values()) & set(OPERATIONS) and
            set(bindings.values()) & set(UNSIGNED_OPERATIONS)):
        raise ValueError('mixed integer selector requires actual signed and unsigned calls')
    if selector == COMPILER_BIOS_SCALAR_DATA_SELECTOR and not set(bindings.values()) & set(OPERATIONS):
        raise ValueError('compiler BIOS selector requires an actual signed runtime call')
    if selector == COMPILER_THUNKS_DATA_SELECTOR and not set(bindings.values()) & set(OPERATIONS):
        raise ValueError('compiler runtime thunks require an actual signed runtime call')
    selected = []
    identities = ((match.UDIVSI3_ADDRESS, match.verify_udivsi3_identity, match.UDIVSI3_IDENTITIES),
                  (unsigned_remainder.ADDRESS, unsigned_remainder.verify_identity,
                   unsigned_remainder.IDENTITIES)) if selector in UNSIGNED_CAPABLE_SELECTORS else tuple(
                       (module.ADDRESS, module.verify_identity, module.IDENTITIES)
                       for module in (quotient, remainder))
    if selector in (*INTEGER_SELECTORS, *BIOS_SELECTORS, *BIOS_ORDINARY_SELECTORS, COMPILER_THUNKS_DATA_SELECTOR):
        identities += tuple((module.ADDRESS, module.verify_identity, module.IDENTITIES)
                            for module in (quotient, remainder))
    if selector in BIOS_ORDINARY_SELECTORS:
        import bios_cpuset_fill_profile as bios
        body = rom[bios.ADDRESS-match.ROM_BASE:bios.ADDRESS-match.ROM_BASE+len(bios.WRAPPER)]
        if bios.ADDRESS not in calls.values() or body != bios.WRAPPER:
            raise ValueError('ordinary BIOS boundary requires its actual exact CpuSet wrapper')
        owner.validate_span(body, bios.ADDRESS, rom, mapping, index)
        selected.append((bios.ADDRESS, bios.ADDRESS+len(body), sha(body)))
    for entry, verify_identity, spans in identities:
        if entry not in {calls[site] for site in bindings}:
            continue
        verify_identity(rom, mapping)
        for lo, hi, digest in spans:
            owner.validate_span(rom[lo-match.ROM_BASE:hi-match.ROM_BASE], lo, rom, mapping, index)
            selected.append([lo, hi, digest])
    for site, target in calls.items():
        if site not in bindings:
            if thunk_alias(selector, target) is not None:
                continue
            match.function_address_target(f'func_{target:08X}', entries, address, len(data), len(rom))
    return sorted({tuple(row) for row in selected})


def finish(data, address, calls, context, verified, dependencies, *, buffer_proof=None):
    import match
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    import local_long_branch_profile as frame
    refinement = owner.refine(data, address, context[1])
    instructions, edges, branches, actual_calls, words = graph.graph(data, address, refinement)
    selector = context_selector(context)
    if branches and selector not in THUNK_SELECTORS or words or calls != actual_calls or \
            set(instructions) != {item.address for item in verified}:
        raise ValueError('addressed signed runtimes require the exact closed direct-call CFG')
    partition = graph.partition(data, address, refinement, instructions, words)
    scalar_controls = []
    saved_controls = []
    numeric_mmio = []
    numeric_hardware = []
    code_images = None
    if selector in DATA_SELECTORS:
        literals = data_literals(data, address, context[0], context[1], context[6], context[7], selector=selector)
        match.verify_data_literals(instructions.values(), address, literals)
        if selector in SCALAR_CONTROL_SELECTORS:
            from bios_cpuset_fill_profile import scalar_control_words
            scalar_controls = scalar_control_words(instructions, edges, calls, partition, address)
            if selector == BIOS_SAVED_SCALAR_MMIO_DATA_SELECTOR:
                from bios_cpuset_fill_profile import saved_scalar_control_words
                saved_controls = saved_scalar_control_words(instructions, edges, calls, partition, address)
                if not saved_controls:
                    raise ValueError('saved BIOS scalar selector requires actual saved scalar-only control use')
            if not scalar_controls and not saved_controls:
                raise ValueError('scalar BIOS control selector requires an actual literal control use')
            if set(literals) & {row[0] for row in scalar_controls + saved_controls}:
                raise ValueError('BIOS scalar control cannot also be a typed object binding')
        address_words = {row['address'] - address for row in partition['words']
                         if remainder.address_literal(row['value'])}
        address_words -= {row[0] for row in scalar_controls + saved_controls}
        if selector in (*NUMERIC_MMIO_SELECTORS, *COMPILER_MMIO_SELECTORS):
            numeric_mmio = [[row['address'] - address, row['value'],
                             [site - address for site in row['load_sites']]]
                            for row in partition['words']
                            if 0x04000000 <= row['value'] < 0x04000400 and not row['value'] % 2]
            if not numeric_mmio:
                raise ValueError('numeric MMIO selector requires actual reached MMIO literal words')
            offsets = {row[0] for row in numeric_mmio}
            if offsets & (set(literals) | {row[0] for row in scalar_controls + saved_controls}):
                raise ValueError('numeric MMIO cannot also be a typed object or BIOS scalar control')
            address_words -= offsets
        if selector in NUMERIC_HARDWARE_SELECTORS:
            numeric_hardware = owner.numeric_hardware_words(instructions, edges, calls, partition, address,
                                                            address_words - set(literals))
            address_words -= {row[0] for row in numeric_hardware}
        if address_words != set(literals):
            raise ValueError('addressed data requires exact typed coverage of reached address words')
        if selector in CODE_IMAGE_SELECTORS:
            import cpuset_code_image_profile as code_image
            code_images = code_image.verify(literals, partition, instructions, edges, calls,
                                            address, data, context[0], context[1])
    elif any(remainder.address_literal(row['value']) for row in partition['words']):
        raise ValueError('addressed signed runtimes exclude address literals and data bindings')
    if selector in (READONLY_SELECTOR, READONLY_TWO_SELECTOR, *READONLY_TWO_DATA_SELECTORS, INTEGER_READONLY_SELECTOR, UNSIGNED_READONLY_SELECTOR, *READONLY_THREE_DATA_SELECTORS, *READONLY_FOUR_DATA_SELECTORS, BIOS_ORDINARY_READONLY_TWO_DATA_SELECTOR):
        if selector in (READONLY_TWO_SELECTOR, *READONLY_TWO_DATA_SELECTORS, *READONLY_THREE_DATA_SELECTORS, *READONLY_FOUR_DATA_SELECTORS, BIOS_ORDINARY_READONLY_TWO_DATA_SELECTOR):
            import readonly_entry_stack_words_profile as incoming
            policy = {'schema': incoming.SCHEMA, 'words': ([0, 1, 2, 3] if selector in READONLY_FOUR_DATA_SELECTORS else
                                                           [0, 1, 2] if selector in READONLY_THREE_DATA_SELECTORS else [0, 1])}
        else:
            import readonly_entry_stack_profile as incoming
            policy = {'schema': incoming.SCHEMA, 'words': [0]}
        restored = frame.prove_frame(instructions, edges, address, {}, calls,
            entry_stack_policy=policy)
        if not restored['entry_stack']['reads']:
            raise ValueError('addressed readonly ABI requires actual checked incoming reads')
    elif selector in BUFFER_SELECTORS:
        if type(buffer_proof) is not match.BufferCallProof or buffer_proof.stack_arguments or \
                buffer_proof.rom != context[0] or buffer_proof.entries != json.loads(context[1]) or \
                buffer_proof.discarded_exit_scratch != buffer_scratch_policy(selector):
            raise ValueError('addressed buffers require their fresh exact native buffer proof')
        if selector in BIOS_SELECTORS:
            from bios_cpuset_fill_profile import BiosFillProof
            bios = buffer_proof.bios_fill_proof
            if type(bios) is not BiosFillProof or bios.data != data or bios.address != address or \
                    bios.index != context[2] or bios.calls != calls:
                raise ValueError('BIOS fill requires the exact internally constructed root proof')
        elif buffer_proof.bios_fill_proof is not None:
            raise ValueError('BIOS fill proof requires its separate explicit selector')
        zero_policy = {}
        if selector == BIOS_READONLY_DATA_SELECTOR:
            import readonly_entry_stack_profile as incoming
            zero_policy['entry_stack_policy'] = {'schema': incoming.SCHEMA, 'words': [0]}
        if selector in (BIOS_READONLY_TWO_SELECTOR, BIOS_READONLY_THREE_DATA_SELECTOR, BIOS_READONLY_FOUR_DATA_SELECTOR):
            import readonly_entry_stack_words_profile as incoming
            count = 2 if selector == BIOS_READONLY_TWO_SELECTOR else 4 if selector == BIOS_READONLY_FOUR_DATA_SELECTOR else 3
            zero_policy['entry_stack_policy'] = {'schema': incoming.SCHEMA, 'words': list(range(count))}
        if selector == BUFFER_SCRATCH_SELECTOR:
            import zero_index_stack_profile as zero_index
            zero_policy['zero_index_profile'] = zero_index.SELECTOR
        restored = frame.prove_frame(instructions, edges, address, {}, calls,
            stack_aliases=True, buffer_proof=buffer_proof, **zero_policy)
        if selector == BIOS_READONLY_DATA_SELECTOR and not restored['entry_stack']['reads']:
            raise ValueError('BIOS incoming word selector requires actual checked word0 reads')
        if selector in (BIOS_READONLY_TWO_SELECTOR, BIOS_READONLY_THREE_DATA_SELECTOR, BIOS_READONLY_FOUR_DATA_SELECTOR) and not restored['entry_stack']['reads']:
            raise ValueError('BIOS incoming words selector requires actual checked declared word reads')
        if not buffer_proof.dependencies:
            raise ValueError('addressed buffer selector requires an actual inspected buffer callee')
        for target, body in buffer_proof.dependencies.items():
            owner.validate_span(body, target, context[0], context[1], context[2])
        if selector in BIOS_SELECTORS and not bios.observations:
            raise ValueError('BIOS fill selector requires an actual bounded local fill source')
        if selector == BUFFER_SCRATCH_SELECTOR and not buffer_proof.discarded_exit_scratch_sites:
            raise ValueError('discarded scratch selector requires actual native scratch aliases')
    elif selector in THUNK_SELECTORS:
        # Each target is a fresh memory load, and the frame proof below admits
        # no SP materialization, so no target or argument has stack provenance.
        thunk_sites = thunk_target_loads(instructions, edges, calls, address)
        restored = frame.prove_frame(instructions, edges, address, branches, calls)
    else:
        restored = frame.prove_frame(instructions, edges, address, {}, calls)
    modules = (match, match.armv4t, owner, graph, frame, quotient, remainder)
    if selector in (*BIOS_SELECTORS, *BIOS_ORDINARY_SELECTORS):
        import bios_cpuset_fill_profile
        modules += (bios_cpuset_fill_profile,)
    if selector == BIOS_SELECTOR and address == 0x0813FB7C:
        import plausible
        import sdk_cpuset_halfword
        local = sdk_cpuset_halfword.native_evidence(data, bios.wrapper)
        observed = (local['call'], local['entry_sp_offset'], local['source_bytes'],
                    local['control'], 0xFFFFFFFF ^ local['control'])
        if bios.observations != {observed}:
            raise ValueError('CpuSet arguments disagree with the initialized SDK halfword source')
        context[4]['sdk_halfword_fill'] = local
        modules += (plausible, sdk_cpuset_halfword)
    if selector == BUFFER_SCRATCH_SELECTOR:
        modules += (zero_index,)
    if selector in UNSIGNED_CAPABLE_SELECTORS:
        modules += (unsigned_remainder,)
    if selector in (READONLY_SELECTOR, READONLY_TWO_SELECTOR, INTEGER_READONLY_SELECTOR, UNSIGNED_READONLY_SELECTOR, BIOS_READONLY_TWO_SELECTOR):
        modules += (incoming,)
    pins = {Path(module.__file__).name: sha(Path(module.__file__).read_bytes()) for module in modules}
    pins[Path(__file__).name] = sha(Path(__file__).read_bytes())
    if selector in (*DATA_SELECTORS, *THUNK_SELECTORS):
        pins = data_producer_fingerprint(selector)
    context[4].update(schema=SCHEMAS[selector], calls=[
        [site-address, thunk_alias(selector, target) or context[3].get(site, f'func_{target:08X}')]
        for site, target in sorted(calls.items())], dependencies=[list(row) for row in dependencies],
        runtime_ABI=ABI, runtime_numeric_return_facts=[], arithmetic_C_equivalence=False,
        original_formal_type_certainty=False,
        ordinary_calls='conditional returning r4-r11/SP preserving ABI only; no transitive callee proof',
        termination='every reached region has a checked return path; universal termination unproved',
        frame=restored, partition=partition, producer_source_sha256=pins)
    if selector in COMPILER_SELECTORS:
        aliases = {name: alias for alias, name in compiler_aliases(selector).items()}
        context[4]['compiler_runtime'] = dict(
            contract=COMPILER_THUNKS_CONTRACT if selector == COMPILER_THUNKS_DATA_SELECTOR else COMPILER_CONTRACT,
            calls=[[site-address, aliases[name], name]
                   for site, name in sorted(context[3].items()) if name in aliases])
    if selector in BIOS_ORDINARY_SELECTORS:
        context[4]['bios_ordinary'] = dict(contract=BIOS_ORDINARY_CONTRACT,
            calls=[site-address for site,target in sorted(calls.items())
                   if target == bios_cpuset_fill_profile.ADDRESS],
            dependency=[bios_cpuset_fill_profile.ADDRESS, len(bios_cpuset_fill_profile.WRAPPER),
                        sha(bios_cpuset_fill_profile.WRAPPER)])
    if selector in BUFFER_SELECTORS:
        context[4]['native_buffers'] = dict(
            fingerprint=buffer_proof.fingerprint(),
            dependencies=[[target, len(body), sha(body)]
                          for target, body in sorted(buffer_proof.dependencies.items())],
            contract='existing native bounded local-buffer proof; no pointer spills, '
                     'stack-passed pointers, returned aliases or unproved escapes; '
                     'ordinary callees remain conditional returning ABI; '
                     'no initialization, physical nonalias or numeric result theorem')
    if selector in BIOS_SELECTORS:
        context[4]['native_buffers']['bios_fill'] = bios.manifest()
        context[4]['native_buffers']['contract'] += '; ' + bios_cpuset_fill_profile.CONTRACT
    if selector in SCALAR_CONTROL_SELECTORS:
        context[4]['bios_scalar_control'] = dict(words=scalar_controls,
            contract='Exact native PC literal loaded only into R2 and consumed by '
                     'the next actual CpuSet call without an intervening R2 read, '
                     'write or escape; scalar control identity, not an object '
                     'binding. Existing fill source frame bounds still apply. '
                     'No BIOS effects, initialization, physical readability, '
                     'nonalias, destination bounds, numeric return or termination theorem.')
    if selector == BIOS_SAVED_SCALAR_MMIO_DATA_SELECTOR:
        context[4]['bios_saved_scalar_control'] = dict(words=saved_controls,
            contract='Canonical reached literal loads into r4-r7, followed only through '
                     'a closed linear path of exact register copies, conditional returning '
                     'ABI calls, and overwrites. Scalar aliases may be consumed only in R2 '
                     'by actual CpuSet calls; memory uses, other argument or return escapes, '
                     'arithmetic, joins and alias cycles refuse. Callee-saved retention is '
                     'an explicit ordinary ABI premise. No BIOS effects, initialization, '
                     'physical readability/nonalias, bounds, numeric or termination theorem.')
    if selector in (*NUMERIC_MMIO_SELECTORS, *COMPILER_MMIO_SELECTORS):
        context[4]['numeric_mmio_literals'] = dict(
            schema='reached-halfword-aligned-numeric-mmio-literals-v1', words=numeric_mmio,
            contract='Reached PC-loaded numeric literals in [0x04000000,0x04000400), '
                     'halfword aligned, separately classified from typed ABS32 named objects '
                     'and BIOS scalar controls. Original ELF words have no data relocation; '
                     'the linker must preserve them exactly. Literal identity only, no typed '
                     'symbol, pointee type, hardware access validity, physical readability, '
                     'memory effects, initialization, nonalias, bounds, numeric result, '
                     'termination or C semantic equivalence theorem.')
    if numeric_hardware:
        context[4]['numeric_hardware_words'] = owner.numeric_hardware_record(numeric_hardware)
    if selector == BUFFER_SCRATCH_SELECTOR:
        from local_long_branch_profile import DISCARDED_SCRATCH_CONTRACT
        context[4]['native_buffers'].update(
            discarded_exit_scratch=buffer_scratch_policy(selector),
            discarded_exit_scratch_sites=[list(row) for row in sorted(buffer_proof.discarded_exit_scratch_sites)])
        context[4]['native_buffers']['contract'] = (
            'native bounded local-buffer proof with exact native zero-index signed loads; no pointer spills, stack-passed pointers, '
            'r0/r1 returned aliases or unproved escapes; ' + DISCARDED_SCRATCH_CONTRACT +
            '; explicit conditional ordinary returning ABI; no initialization, '
            'physical nonalias, numeric result or termination theorem')
    if selector in CODE_IMAGE_SELECTORS:
        context[4]['code_image_sources'] = code_image.manifest(code_images)
    if selector in DATA_SELECTORS:
        context[4].update(data_bindings=[list(row) for row in context[7]],
            data_contract=DATA_CONTRACT)
    if selector in FUNCTION_DATA_SELECTORS:
        context[4].update(function_literal_bindings=[list(row[:2]) for row in context[7]
            if function_literal(row[1], selector)],
            data_contract='Separate typed ABS32 named objects and exact unique indexed Thumb function entries; '
                'function literals are not objects or proof of a callback signature, invocation, return, '
                'memory effects, physical readability, allocation or C semantic equivalence.')
    if selector == max_lines.SELECTOR:
        context[4]['data_bindings'] = [list(row) for row in context[7] if row[1] != max_lines.SYMBOL]
        context[4]['linker_absolute'] = max_lines.verify_use(data, instructions, edges, partition, calls, literals)
        context[4]['m4a_callback_rows'] = max_lines.callbacks(context[0], context[1], literals)
    if selector in CALLBACK_SELECTORS:
        resolve_callback = r3_callback_sites if selector == R3_CALLBACK_SELECTOR else callback_sites
        if selector == MENU_RING_SELECTOR:
            import menu_ring_initializer as menu_ring
            resolve_callback = menu_ring.callback_site
            context[4]['menu_ring'] = menu_ring.manifest(context[0], context[1], context[2], data)
        context[4]['callback'] = dict(
            contract=R3_CALLBACK_CONTRACT if selector == R3_CALLBACK_SELECTOR else CALLBACK_CONTRACT,
            sites=resolve_callback(
                instructions, edges, calls, address, context[7]),
            dependencies=callback_dependencies(context[0], context[1], context[2], selector),
            runtime=match.function_thunk.RUNTIME, abi=match.function_thunk.ABI)
    if selector in THUNK_SELECTORS:
        context[4]['local_long_branches'] = frame.record(instructions.values(), address)
        context[4]['thunks'] = dict(contract=THUNK_CONTRACT, target_policy=THUNK_TARGET_POLICY,
            sites=thunk_sites,
            dependencies=thunk_dependencies(context[0], context[1], context[2],
                                            {alias for _, alias, _ in thunk_sites}),
            runtime=match.function_thunk.RUNTIME, abi=match.function_thunk.ABI)


def verify(data, address, rom, mapping, index, calls, bindings, manifest=None, *, selector=SELECTOR,
           data_mapping=None, data_bindings=None, compiler_calls=None):
    import match
    if selector not in SCHEMAS:
        raise ValueError('unknown addressed signed runtime selector')
    observed = {}
    context = (rom, mapping, index, bindings, observed)
    if selector in (READONLY_SELECTOR, READONLY_TWO_SELECTOR, UNSIGNED_SELECTOR, UNSIGNED_BUFFER_SELECTOR, BUFFER_SELECTOR, BUFFER_SCRATCH_SELECTOR, BIOS_SELECTOR, BIOS_READONLY_TWO_SELECTOR, BIOS_ORDINARY_SELECTOR, INTEGER_SELECTOR, INTEGER_READONLY_SELECTOR, UNSIGNED_READONLY_SELECTOR, THUNKS_SELECTOR):
        context += (selector,)
    elif selector in DATA_SELECTORS:
        context += (selector, data_mapping, data_bindings)
    if selector not in DATA_SELECTORS and (data_mapping is not None or data_bindings is not None):
        raise ValueError('typed data requires its separate explicit addressed selector')
    compiler = None if compiler_calls is None else \
        COMPILER_BIOS_FILL.check(selector, compiler_calls, bindings, address)
    instructions = match.verify_leaf_instructions(data, address, True, calls,
        addressed_signed_runtime_context=context)
    if compiler is not None:
        observed['compiler_runtime'] = compiler
    if manifest is not None and text(manifest) != text(observed):
        raise ValueError('addressed signed runtime manifest differs from fresh native verification')
    return observed, instructions


def terminal_alignment(image, symbol):
    """Only the native assembler's two-byte, four-alignment Thumb NOP tail."""
    size = symbol['size']
    padding = image['text'][size:]
    if not padding:
        return
    section = image['sections'][image['text_index']]
    if size <= 0 or size % 4 != 2 or padding != b'\xc0\x46' or symbol['bind'] != 1 or \
            section[1] != 1 or section[2] != 6 or section[3] % 4 or section[4] % 4 or \
            section[5] != len(image['text']) or section[8] != 4 or \
            image['type'] == 1 and section[3] != 0:
        raise ValueError('addressed runtime text has noncanonical terminal alignment')
    for item in image['symbols']:
        if item is symbol or item['section'] != image['text_index']:
            continue
        offset = item['value'] - section[3]
        if not 0 <= offset < size or offset + item['size'] > size:
            raise ValueError('addressed runtime terminal alignment has a symbol owner')


def original_function(image, address):
    import match
    if image['type'] != 1:
        raise ValueError('addressed signed runtimes require original relocatable ELF')
    match.allocated_text_only(image)
    symbol, offset = match.function_record(image, f'func_{address:08X}', address, True)
    if offset or any(
            item is not symbol and item['type'] in (1, 2) and item['section'] or
            re.fullmatch(r'\$a(?:\..*)?', item['name']) for item in image['symbols']):
        raise ValueError('addressed signed runtimes require sole complete original Thumb text')
    terminal_alignment(image, symbol)
    return symbol


def original_bindings(image, address, rom, mapping, *, data_mapping=None, data_relocations=None,
                      selector=SELECTOR, compiler_calls=None):
    """Canonical addressed calls, with separately requested typed original ABS32.

    compiler_calls, a fresh empty dict, receives each compiler runtime name
    COMPILER_BIOS_FILL binds, by call site.
    """
    import match
    if compiler_calls is not None and (type(compiler_calls) is not dict or compiler_calls):
        raise ValueError('compiler runtime call sites require a fresh empty collection')
    with_data = data_mapping is not None or data_relocations is not None
    if with_data and (type(data_mapping) is not bytes or type(data_relocations) is not dict or
                      data_relocations):
        raise ValueError('addressed data linking requires a snapshot and fresh empty binding collection')
    objects = match.parse_data_symbols(data_mapping) if with_data else {}
    if selector not in SCHEMAS or selector in CALLBACK_SELECTORS and not with_data:
        raise ValueError('callback linking requires its exact selector and typed data')
    if selector in (READONLY_TWO_DATA_SELECTOR, INTEGER_THREE_DATA_SELECTOR, INTEGER_FOUR_DATA_SELECTOR,
                    *COMPILER_SELECTORS) and not with_data:
        raise ValueError('addressed readonly data requires actual typed bindings')
    symbol = original_function(image, address)
    entries = json.loads(mapping)
    calls, bindings, targets, occupied = {}, {}, {}, set()
    for section_index in image['relocations']:
        section = image['sections'][section_index]
        if section[1] != 9 or section[7] != image['text_index'] or section[9] != 8 or section[5] % 8:
            raise ValueError('addressed signed runtimes require canonical Thumb call REL sections')
        symbols = image['symbol_tables'].get(section[6])
        for position in range(0, section[5], 8):
            offset, info = struct.unpack_from('<II', image['section_data'][section_index], position)
            if info & 255 not in ((2, 10) if with_data else (10,)) or \
                    symbols is None or info >> 8 >= len(symbols) or offset % 2 or \
                    offset + 4 > symbol['size'] or occupied.intersection(range(offset, offset+4)):
                raise ValueError('addressed signed runtimes exclude data and irregular relocations')
            target_symbol = symbols[info >> 8]
            name = target_symbol['name']
            if info & 255 == 2:
                callable_literal = function_literal(name, selector)
                if (address + offset) % 4 or target_symbol['section'] or target_symbol['value'] or \
                        target_symbol['size'] or target_symbol['bind'] != 1 or \
                        target_symbol['type'] not in ((0, 2) if callable_literal else (0, 1)) or \
                        sum(item['name'] == name for item in image['symbols']) != 1:
                    raise ValueError('addressed ABS32 requires an aligned unique undefined global with its exact type')
                addend = struct.unpack_from('<i', image['text'], offset)[0]
                if selector == max_lines.SELECTOR and name == max_lines.SYMBOL:
                    if target_symbol['type'] != 0 or symbol['size'] != max_lines.SIZE:
                        raise ValueError('m4a original linker absolute must be NOTYPE in its complete owner')
                    target = max_lines.symbol_value(rom, address, offset, addend, objects)
                elif callable_literal:
                    if addend != 0 or name in objects:
                        raise ValueError('function literal cannot have an addend or an object identity')
                    target = match.function_address_target(name, entries, address, symbol['size'], len(rom))
                else:
                    object_value(name, addend, objects, entries, address, symbol['size'],
                                 image=selector in CODE_IMAGE_SELECTORS)
                    target = objects[name]
                data_relocations[offset] = (name, addend)
                targets[name] = target
                occupied.update(range(offset, offset+4))
                continue
            if target_symbol['section'] or target_symbol['value'] or target_symbol['bind'] != 1 or \
                    target_symbol['type'] not in (0, 2) or \
                    sum(item['name'] == name for item in image['symbols']) != 1:
                raise ValueError('addressed calls require unique undefined zero-valued global functions')
            canonical = compiler_aliases(selector).get(name) if selector in COMPILER_SELECTORS or \
                COMPILER_BIOS_FILL.applies(selector) else None
            if canonical is not None and target_symbol['size'] != 0:
                raise ValueError('compiler runtime symbols require zero original size')
            if canonical is not None and selector not in COMPILER_SELECTORS:
                if compiler_calls is None:
                    raise ValueError('compiler runtime names require their recorded call sites')
                compiler_calls[address+offset] = name
            if selector in COMPILER_SELECTORS and name in compiler_aliases(selector).values():
                raise ValueError('compiler runtime linking requires original compiler-emitted names')
            target = operations(selector).get(canonical or name)
            if target is None:
                if name in match.function_thunk.ALIASES and \
                        thunk_alias(selector, match.function_thunk.ALIASES[name]) == name:
                    target = match.function_thunk.ALIASES[name]
                    match.function_thunk.dependencies([name], rom)
                else:
                    target = match.function_address_target(name, entries, address, symbol['size'], len(rom))
            else:
                bindings[address+offset] = canonical or name
            decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
            decoder.detail = True
            instruction = next(decoder.disasm(image['text'][offset:offset+4],address+offset),None)
            if instruction is None or instruction.id != match.ARM_INS_BL or instruction.size != 4 or \
                    len(instruction.operands) != 1 or instruction.operands[0].type != match.ARM_OP_IMM or \
                    instruction.operands[0].imm != address+offset:
                raise ValueError('addressed call relocation requires its canonical zero addend')
            calls[address+offset] = target
            targets[name] = target
            occupied.update(range(offset,offset+4))
    if selector == COMPILER_BIOS_SCALAR_DATA_SELECTOR and not set(targets) & set(COMPILER_ALIASES):
        raise ValueError('compiler BIOS ELF requires an actual compiler-emitted signed runtime call')
    if selector == COMPILER_THUNKS_DATA_SELECTOR and bindings and not data_relocations:
        # The data-free shape (a callback read from an incoming object) is not admitted here.
        raise ValueError('compiler runtime thunks require actual typed data')
    if not bindings or with_data and not data_relocations and selector not in COMPILER_MMIO_SELECTORS or any(
                           item['name'] and not item['section'] and item['name'] not in targets
                           for item in image['symbols']):
        raise ValueError('addressed runtime ELF requires actual addressed calls and no unresolved symbols')
    if selector in CALLBACK_SELECTORS and callback_alias(selector) not in targets:
        raise ValueError('callback ELF requires its actual compiler-emitted canonical call')
    if selector in THUNK_SELECTORS and not set(targets) & set(match.function_thunk.ALIASES):
        raise ValueError('thunk ELF requires an actual compiler-emitted canonical thunk call')
    return calls, bindings, targets


def linked_bytes(original, linked, address, calls, targets, *, data_relocations=None, function_literals=(),
                 selector=SELECTOR):
    import match
    if linked['type'] != 2 or linked['relocations']:
        raise ValueError('addressed runtime link requires executable ELF without relocations')
    match.allocated_text_only(linked)
    name = f'func_{address:08X}'
    before = original_function(original, address)
    after, offset = match.function_record(linked, name, address, True)
    if offset or after['value'] != address | 1 or after['size'] != before['size'] or \
            linked['sections'][linked['text_index']][3] != address or \
            len(linked['text']) != len(original['text']):
        raise ValueError('addressed runtime linker changed extent, mode, placement or text size')
    terminal_alignment(linked, after)
    if data_relocations is not None and (type(data_relocations) is not dict or not data_relocations):
        raise ValueError('addressed data linker requires actual original bindings')
    data_relocations = data_relocations or {}
    function_literals = frozenset(function_literals)
    if not function_literals <= {record[0] for record in data_relocations.values()} or any(
            not re.fullmatch(r'func_[0-9A-F]{8}', name) or name not in targets
            for name in function_literals):
        raise ValueError('linked function literals require their original canonical bindings')
    data_names = {record[0] for record in data_relocations.values()} - function_literals
    scalar_names = set()
    if selector == max_lines.SELECTOR:
        if (address != max_lines.ADDRESS or before['size'] != max_lines.SIZE or
                data_relocations.get(max_lines.OFFSET) != (max_lines.SYMBOL, 0) or
                targets.get(max_lines.SYMBOL) != 80):
            raise ValueError('m4a linked absolute requires its original owner and relocation')
        scalar_names.add(max_lines.SYMBOL)
        data_names -= scalar_names
    functions = [item['name'] for item in linked['symbols'] if item['type'] == 2]
    objects = [item['name'] for item in linked['symbols'] if item['type'] == 1]
    expected_functions = {name} | (set(targets) - data_names - scalar_names)
    if len(functions) != len(expected_functions) or set(functions) != expected_functions or \
            len(objects) != len(data_names) or set(objects) != data_names or any(
            item['name'] and not item['section'] or
            re.fullmatch(r'\$a(?:\..*)?', item['name']) for item in linked['symbols']):
        raise ValueError('addressed runtime linker introduced objects, undefined symbols or veneers')
    for target_name, target in targets.items():
        symbols = [item for item in linked['symbols'] if item['name'] == target_name]
        kind = 1 if target_name in data_names else 2
        if target_name in scalar_names:
            kind = 0
        value = target | 1 if kind == 2 else target
        if len(symbols) != 1 or symbols[0]['type'] != kind or symbols[0]['bind'] != 1 or \
                symbols[0]['section'] != 0xFFF1 or symbols[0]['value'] != value or \
                target_name in scalar_names and symbols[0]['size'] != 0:
            raise ValueError('addressed runtime linked target lost its absolute Thumb identity')
    occupied = set()
    for site, target in calls.items():
        offset = site-address
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB); decoder.detail = True
        instruction = next(decoder.disasm(linked['text'][offset:offset+4],site),None)
        if instruction is None or instruction.id != match.ARM_INS_BL or instruction.size != 4 or \
                instruction.operands[0].imm != target:
            raise ValueError('addressed runtime linked BL target differs')
        occupied.update(range(offset,offset+4))
    for offset, (target_name, addend) in data_relocations.items():
        if type(offset) is not int or (address+offset) % 4 or not 0 <= offset <= before['size']-4 or \
                type(addend) is not int or not -0x80000000 <= addend <= 0x7FFFFFFF or \
                target_name not in targets or occupied.intersection(range(offset,offset+4)) or \
                struct.unpack_from('<i', original['text'], offset)[0] != addend or \
                not 0 <= targets[target_name]+addend <= 0xFFFFFFFF or \
                target_name in function_literals and addend != 0 or \
                struct.unpack_from('<I', linked['text'], offset)[0] != \
                    ((targets[target_name] | 1) if target_name in function_literals else targets[target_name]+addend):
            raise ValueError('addressed linked data differs from its original typed ABS32 addend')
        occupied.update(range(offset,offset+4))
    if any(index not in occupied and first != second for index, (first,second) in
           enumerate(zip(original['text'],linked['text']))):
        raise ValueError('addressed runtime linker changed bytes outside call relocations')
    return linked['text'][:after['size']]


def object_bytes(runner, workspace, args, original, address, rom, mapping, *,
                 selector=SELECTOR, data_mapping=None, compiler_calls=None):
    import match
    from inert_spin_profile import fixed_configuration
    fixed_configuration(args)
    data = {} if selector in DATA_SELECTORS else None
    if selector == max_lines.SELECTOR:
        max_lines.source_use(runner.read_binary(f'{workspace}/f.i').decode('utf-8'))
    if selector in COMPILER_SELECTORS:
        compiler_namespace(runner.read_binary(f'{workspace}/f.i').decode('utf-8'), selector)
    if selector in CALLBACK_SELECTORS:
        match.function_thunk.namespace(runner.read_binary(f'{workspace}/f.i').decode('utf-8'))
    if selector in THUNK_SELECTORS:
        thunk_namespace(runner.read_binary(f'{workspace}/f.i').decode('utf-8'),
                        runner.read_binary(f'{workspace}/f.s').decode('utf-8'), original, address)
    calls, bindings, targets = original_bindings(original,address,rom,mapping,
        data_mapping=data_mapping if data is not None else None, data_relocations=data, selector=selector,
        compiler_calls=compiler_calls)
    if compiler_calls:
        compiler_namespace(runner.read_binary(f'{workspace}/f.i').decode('utf-8'), selector)
    function_literals = {record[0] for record in (data or {}).values()
                         if function_literal(record[0], selector)}
    data_names = {record[0] for record in (data or {}).values()} - function_literals
    definitions = ['.syntax unified','.thumb']
    for name,target in sorted(targets.items()):
        if selector == max_lines.SELECTOR and name == max_lines.SYMBOL:
            definitions += [f'.global {name}', f'.set {name}, {target}']
        elif name in data_names:
            definitions += [f'.global {name}',f'.type {name}, %object',f'.set {name}, 0x{target:08X}']
        else:
            definitions += [f'.global {name}',f'.type {name}, %function',f'.thumb_set {name}, 0x{target|1:08X}']
    runner.write_text(f'{workspace}/f.known.s','\n'.join(definitions)+'\n')
    runner.write_text(f'{workspace}/f.ld',
        f'SECTIONS {{ .text 0x{address:08X} : {{ *(.text) *(.glue_7) *(.glue_7t) }} '
        '.data 0 : { *(.data) } .bss 0 : { *(.bss) } '
        '.ARM.attributes 0 : { *(.ARM.attributes) } '
        '.unexpected 0 : { *(.vfp11_veneer) *(.v4_bx) *(.iplt) *(.igot.plt) } '
        '.rel.iplt 0 : { *(.rel.iplt) } '
        'ASSERT(SIZEOF(.unexpected) == 0, "unexpected linker stubs") '
        'ASSERT(SIZEOF(.rel.iplt) == 0, "unexpected dynamic relocations") '
        '/DISCARD/ : { *(.comment) *(.note.GNU-stack) } }')
    quoted = shlex.quote(workspace)
    runner.sh(f'export TMPDIR={quoted}; {args.assembler} -mthumb-interwork {quoted}/f.known.s -o {quoted}/f.known.o')
    runner.sh(f'export TMPDIR={quoted}; {args.linker} --fatal-warnings --no-undefined --no-relax '
              f'--orphan-handling=error -T {quoted}/f.ld -e func_{address:08X} '
              f'{quoted}/f.o {quoted}/f.known.o -o {quoted}/f.elf')
    runner.sh(f'{args.objcopy} -O binary --only-section=.text {quoted}/f.elf {quoted}/f.linked.bin')
    linked = match.elf_image(runner.read_binary(f'{workspace}/f.elf'))
    if runner.read_binary(f'{workspace}/f.linked.bin') != linked['text']:
        raise ValueError('addressed runtime objcopy differs from linked ELF text')
    result = linked_bytes(original,linked,address,calls,targets,data_relocations=(None if selector in COMPILER_MMIO_SELECTORS and not data else data),
                          function_literals=function_literals, selector=selector),calls,bindings
    if data is not None:
        result += ([[offset,name,addend] for offset,(name,addend) in sorted(data.items())],)
    return result


def toolchain_fingerprint():
    import match
    commands = (match.DEFAULT_CC,match.DEFAULT_CPP,match.DEFAULT_AS,match.DEFAULT_OBJCOPY,match.DEFAULT_LD)
    return [[command,sha(Path(shutil.which(os.path.expandvars(command)) or
                              os.path.expandvars(command)).read_bytes())] for command in commands]


def runtime_fingerprint():
    import capstone
    library = Path(capstone._cs._name)
    if not library.is_absolute():
        # Some bindings load by soname through the dynamic loader. Fingerprint
        # the mapped library rather than interpreting that soname under cwd.
        loaded = set()
        for line in Path('/proc/self/maps').read_text().splitlines():
            fields = line.split(maxsplit=5)
            if len(fields) == 6 and fields[5].startswith('/') and \
                    Path(fields[5]).name == library.name:
                loaded.add(fields[5])
        if len(loaded) != 1:
            raise ValueError('loaded Capstone library identity is unavailable or ambiguous')
        library = Path(loaded.pop())
    return dict(system=platform.system(), kernel=platform.release(), machine=platform.machine(),
        python=platform.python_version(), python_sha256=sha(Path(sys.executable).read_bytes()),
        capstone=capstone.__version__, binding_sha256=sha(Path(capstone.__file__).read_bytes()),
        capstone_native_sha256=sha(library.read_bytes()))


def build(root, address, args=None, expected=None, *, selector=SELECTOR):
    import match
    from inert_spin_profile import fixed_configuration,index_snapshot
    from match_evidence import source_fingerprint,source_paths,mapping_snapshot,data_snapshot,report_rom_path
    root = Path(root)
    args = args or argparse.Namespace(cc=match.DEFAULT_CC,cpp=match.DEFAULT_CPP,assembler=match.DEFAULT_AS,
        objcopy=match.DEFAULT_OBJCOPY,linker=match.DEFAULT_LD,flags=match.DEFAULT_FLAGS)
    fixed_configuration(args)
    if selector not in SCHEMAS:
        raise ValueError('unknown addressed signed runtime selector')
    runtime = runtime_fingerprint() if selector in (READONLY_SELECTOR, READONLY_TWO_SELECTOR, UNSIGNED_SELECTOR, UNSIGNED_BUFFER_SELECTOR, BUFFER_SELECTOR, BUFFER_SCRATCH_SELECTOR, BIOS_SELECTOR, BIOS_READONLY_TWO_SELECTOR, BIOS_ORDINARY_SELECTOR, INTEGER_SELECTOR, INTEGER_READONLY_SELECTOR, UNSIGNED_READONLY_SELECTOR, THUNKS_SELECTOR, *DATA_SELECTORS) else None
    producers = data_producer_fingerprint(selector) if selector in (*DATA_SELECTORS, *THUNK_SELECTORS) else None
    source,mapping,index = source_fingerprint(root,address),mapping_snapshot(root),index_snapshot(root)
    objects,selected_rom = data_snapshot(root),report_rom_path(root)
    rom = Path(selected_rom).read_bytes(); tools = toolchain_fingerprint()
    candidates = list((root/'src').rglob(f'{address:08X}.c'))
    if len(candidates) != 1:
        raise ValueError('addressed signed runtime requires one uniquely addressed source')
    (root/'build').mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='addressed_signed_',dir=root/'build') as directory:
        captured = Path(directory)
        for path in source_paths(root,address):
            destination = captured/path.relative_to(root)
            destination.parent.mkdir(parents=True,exist_ok=True); destination.write_bytes(path.read_bytes())
        if source_fingerprint(captured,address) != source:
            raise ValueError('addressed signed runtime source capture differs')
        runner = match.Runner(match.DEFAULT_CC,'Ubuntu',match.DEFAULT_WSL_PATH,root=captured,timeout=120)
        with runner.workspace() as workspace:
            raw,_,original = match.compile_object(runner,workspace,args,captured,address,
                candidates[0].relative_to(root).as_posix())
            assembly = runner.read_binary(f'{workspace}/f.s')
            compiler_calls = {} if COMPILER_BIOS_FILL.applies(selector) else None
            linked_result = object_bytes(runner,workspace,args,original,address,rom,mapping,
                selector=selector,data_mapping=objects,compiler_calls=compiler_calls)
            body,calls,bindings = linked_result[:3]
            data_options = (dict(data_mapping=objects,data_bindings=linked_result[3])
                            if selector in DATA_SELECTORS else {})
            manifest,instructions = verify(body,address,rom,mapping,index,calls,bindings,expected,
                                           selector=selector,compiler_calls=compiler_calls or None,
                                           **data_options)
            linked = runner.read_binary(f'{workspace}/f.elf')
        check = match._run_replay_process([sys.executable,str(Path(importlib.import_module('plausible').__file__)),
            '--quiet','--addr',f'0x{address:08X}','--json']+
            [str(path) for path in source_paths(captured,address)],captured,120)
        findings,allowed = match.plausibility_result(check,address)
        if findings or allowed or source_fingerprint(captured,address) != source:
            raise ValueError('addressed signed runtime source is implausible or changed')
    if source_fingerprint(root,address) != source or mapping_snapshot(root) != mapping or \
            index_snapshot(root) != index or data_snapshot(root) != objects or \
            report_rom_path(root) != selected_rom or Path(selected_rom).read_bytes() != rom or \
            toolchain_fingerprint() != tools or runtime is not None and runtime_fingerprint() != runtime or \
            producers is not None and (data_producer_fingerprint(selector) != producers or
                manifest['producer_source_sha256'] != producers):
        raise ValueError('addressed signed runtime source, inputs or tools changed during verification')
    result = dict(address=address,body=body,manifest=manifest,source_sha256=source,
        mapping_sha256=sha(mapping),index_sha256=sha(index),objects_sha256=None if objects is None else sha(objects),
        rom_sha256=sha(rom),instructions=len(instructions),toolchain=tools,
        original_elf=raw,assembly=assembly,linked_elf=linked)
    if runtime is not None:
        result['runtime'] = runtime
    return result


def render(result):
    selector = next((key for key,value in SCHEMAS.items() if value == result['manifest']['schema']),None)
    if selector is None:
        raise ValueError('unknown addressed signed runtime manifest schema')
    premise = [] if selector not in (BIOS_READONLY_DATA_SELECTOR, BIOS_READONLY_TWO_SELECTOR, BIOS_READONLY_THREE_DATA_SELECTOR, BIOS_READONLY_FOUR_DATA_SELECTOR, READONLY_SELECTOR, READONLY_TWO_SELECTOR, *READONLY_TWO_DATA_SELECTORS, INTEGER_READONLY_SELECTOR, UNSIGNED_READONLY_SELECTOR, *READONLY_THREE_DATA_SELECTORS, *READONLY_FOUR_DATA_SELECTORS, BIOS_ORDINARY_READONLY_TWO_DATA_SELECTOR) else [
        '* incoming stack ABI: ' + result['manifest']['frame']['entry_stack']['contract']]
    if selector in DATA_SELECTORS:
        premise.append('* named data binding: ' + result['manifest']['data_contract'])
    if selector in CODE_IMAGE_SELECTORS:
        premise.append('* code image source: ' + result['manifest']['code_image_sources']['contract'])
    if selector in BUFFER_SELECTORS:
        premise.append('* local buffer boundary: ' + result['manifest']['native_buffers']['contract'])
    if 'sdk_halfword_fill' in result['manifest']:
        premise.append('* SDK CpuFill16 source: one initialized stack halfword at entry SP-8, '
                       'consumed by CpuSet with a count of 16 under the conditional BIOS fill interface')
    if selector in CALLBACK_SELECTORS:
        register = 'r3' if selector == R3_CALLBACK_SELECTOR else 'r2'
        premise.append(f'* mapped {register} callback ABI: ' + result['manifest']['callback']['contract'])
    if selector in THUNK_SELECTORS:
        premise.append('* canonical thunk callee ABI: ' + result['manifest']['thunks']['contract'])
    if selector in (COMPILER_BIOS_SCALAR_DATA_SELECTOR, COMPILER_THUNKS_DATA_SELECTOR):
        premise.append('* compiler runtime binding: ' + result['manifest']['compiler_runtime']['contract'])
    if selector in COMPILER_BIOS_FILL.selectors and 'compiler_runtime' in result['manifest']:
        premise.append(COMPILER_BIOS_FILL.premise(result))
    evidence = {key:value for key,value in result.items() if key not in
                ('body','original_elf','assembly','linked_elf')}
    for key in ('body','original_elf','assembly','linked_elf'):
        evidence[key+'_sha256'] = sha(result[key])
    encoded = text(evidence)
    return '\n'.join([f'# 0x{result["address"]:08X}','',f'* verification: `{SCHEMAS[selector]}`',
        f'* addressed signed runtime: `{selector}`',f'* control flow: {ABI}',*premise,
        '* source plausibility: plausible',
        '* verified extent: complete original ELF function symbol including referenced literal pools',
        '* numeric division/remainder equivalence: unclaimed; original formal type certainty: unclaimed',
        f'* addressed signed runtime evidence: `{encoded}`',
        f'* addressed signed runtime proof SHA-256: `{sha(encoded.encode())}`',
        f'* compiled : `{result["body"].hex()}`',
        f'* ROM bytes: `{result["body"].hex()}` ({len(result["body"])} bytes)','',
        f'**MATCH - byte identical** - {len(result["body"])}/{len(result["body"])} bytes',''])


def selector_for_report(report):
    from inert_spin_profile import marker_text
    lines = report.splitlines()
    if not any(any(schema in line for schema in SCHEMAS.values()) or
               marker_text(line).startswith('* addressed signed runtime') for line in lines):
        return False
    for selector,schema in SCHEMAS.items():
        if [line for line in lines if marker_text(line).startswith('* verification:')] == [f'* verification: `{schema}`'] and \
                [line for line in lines if marker_text(line).startswith('* addressed signed runtime:')] == \
                [f'* addressed signed runtime: `{selector}`']:
            return selector
    raise ValueError('mixed or malformed addressed signed runtime report')


def selected(report):
    return bool(selector_for_report(report))


def report_matches(report, root, address):
    from match_evidence import source_fingerprint,mapping_snapshot,data_snapshot,report_rom_path,valid_match_verdict
    from inert_spin_profile import index_snapshot
    if _replay.get():
        return False
    token = _replay.set(True)
    try:
        selector = selector_for_report(report)
        if not selector or not valid_match_verdict(report):
            return False
        prefix = '* addressed signed runtime evidence: `'
        rows = [line for line in report.splitlines() if line.startswith(prefix)]
        if len(rows) != 1 or not rows[0].endswith('`'):
            return False
        def unique(pairs):
            result = {}
            for key,value in pairs:
                if key in result: raise ValueError('duplicate addressed signed runtime evidence key')
                result[key] = value
            return result
        encoded = rows[0][len(prefix):-1]; saved = json.loads(encoded,object_pairs_hook=unique)
        objects = data_snapshot(root)
        if text(saved) != encoded or saved['address'] != address or \
                saved['source_sha256'] != source_fingerprint(root,address) or \
                saved['mapping_sha256'] != sha(mapping_snapshot(root)) or \
                saved['index_sha256'] != sha(index_snapshot(root)) or \
                saved['objects_sha256'] != (None if objects is None else sha(objects)) or \
                saved['rom_sha256'] != sha(Path(report_rom_path(root)).read_bytes()) or \
                saved['toolchain'] != toolchain_fingerprint():
            return False
        if selector in (READONLY_SELECTOR, READONLY_TWO_SELECTOR, UNSIGNED_SELECTOR, UNSIGNED_BUFFER_SELECTOR, BUFFER_SELECTOR, BUFFER_SCRATCH_SELECTOR, BIOS_SELECTOR, BIOS_READONLY_TWO_SELECTOR, BIOS_ORDINARY_SELECTOR, INTEGER_SELECTOR, INTEGER_READONLY_SELECTOR, UNSIGNED_READONLY_SELECTOR, THUNKS_SELECTOR, *DATA_SELECTORS) and saved['runtime'] != runtime_fingerprint():
            return False
        return render(build(root,address,expected=saved['manifest'],selector=selector)) == report
    except (OSError,ValueError,KeyError,TypeError,IndexError,RuntimeError,subprocess.SubprocessError):
        return False
    finally:
        _replay.reset(token)


def issue(root, address, args):
    import match
    if args.mode != 'thumb' or args.control_flow_profile != 'ordinary' or args.label or \
            args.wsl != 'Ubuntu' or args.wsl_path != match.DEFAULT_WSL_PATH or any(
                getattr(args,name) is not None for name in ('signed_runtime_profile','signed_quotient_profile',
                'software_double_profile','software_double_remainder_profile','function_address_profile',
                'switch_profile','owner_runtime_profile')):
        raise ValueError('addressed signed runtimes require their isolated explicit Thumb selector')
    result = build(root,address,args,selector=args.addressed_signed_runtime_profile)
    if args.emit:
        output = (Path(root)/args.emit).resolve()
        if (Path(root)/'build').resolve() not in output.parents or output.exists():
            raise ValueError('--emit requires a new file beneath build/')
        output.parent.mkdir(parents=True,exist_ok=True)
        with output.open('xb') as stream:stream.write(result['body'])
    if not args.no_write:
        report = Path(root)/'docs/match'/f'{address:08X}.md'
        report.parent.mkdir(parents=True,exist_ok=True); report.write_text(render(result))
    print(f'extent    {len(result["body"])} bytes (complete ELF symbol; conditional addressed runtime ABI)')
    print('verdict MATCH - byte identical')
    return 0


class CompilerThunksDefaultPath:
    """kit #134: compiler __divsi3/__modsi3 beside canonical _call_via_rN thunks.

    The default path's generic call binding refuses any signed runtime next to
    a thunk, because its leaf walk proves neither a thunk target's provenance
    nor the absence of local arguments.  This policy hands such a refused
    function, unchanged, to COMPILER_THUNKS_DATA_SELECTOR, which proves both:
    the compiler-runtime binding of the compiler selectors (original
    compiler-emitted names, pinned runtime bodies) and the thunk rule of the
    thunks selectors (every target a memory word load on every path, no SP
    materialization, authenticated thunks), with typed named data.  Beside a
    signed runtime it also binds the unsigned runtimes, as the explicit
    integer selectors do.  It routes
    only a run with no selector, the fixed toolchain and no library unit, and
    only an original object that names both a compiler signed runtime and a
    thunk.  Set ``enabled`` to False to keep the plain refusal.
    """

    enabled = True
    selector = COMPILER_THUNKS_DATA_SELECTOR
    runtimes = frozenset(COMPILER_ALIASES)

    def applies(self, args, gate, original):
        import library_units
        import match
        # The refusal may come before compile_object returned a parsed ELF image.
        if not self.enabled or gate is not None or not isinstance(original, dict) or \
                type(original.get('symbols')) is not list or \
                args.mode != 'thumb' or args.control_flow_profile != 'ordinary' or args.label or \
                library_units._selectors(args):
            return False
        names = {item['name'] for item in original['symbols'] if not item['section']}
        return bool(names & self.runtimes) and bool(names & set(match.function_thunk.ALIASES))

    def issue(self, refusal):
        """The selector's own report writer; a refusal keeps the plain one first."""
        def routed(root, address, args):
            selected = argparse.Namespace(**vars(args))
            selected.addressed_signed_runtime_profile = self.selector
            try:
                return issue(root, address, selected)
            except Exception as error:  # noqa: BLE001 - fail closed to the plain refusal
                # A deliberate refusal is a ValueError; anything else is named by
                # its type.  KeyboardInterrupt and SystemExit pass through.
                if os.environ.get('FFTA_TRACEBACK') not in (None, '', '0'):
                    raise
                reason = str(error) if isinstance(error, ValueError) else f'{type(error).__name__}: {error}'
                sys.exit(f'compile failed:\n{refusal}; compiler signed runtime thunks: {reason}')
        return routed


COMPILER_THUNKS_POLICY = CompilerThunksDefaultPath()
