"""Explicit R7 callback fact preservation through complete unwritten-register replay.

This is a separately selected proof API. It assumes no C function-type equivalence
and no general callee-saved restoration theorem. A selected callback must pass
all existing target, owner, buffer-effect and live-alias checks, with R7 watched
at every inspected instruction, including nested inspected dependencies.
"""
import hashlib
import importlib
import json
from pathlib import Path

import match
import function_thunk_profile as thunk
import static_callback_buffer_profile as callback

SELECTOR = 'static-callback-unwritten-r7-v1'
SCHEMA = 'elf-symbol-thumb-static-callback-unwritten-r7-v1'
REGISTER = match.ARM_REG_R0 + 7
THUNK = thunk.ALIASES['_call_via_r7']
MAX_DEPENDENCIES = callback.MAX_DEPENDENCIES
CONTROL_FLOW = 'complete Thumb owner with fully replayed callbacks and exact unwritten R7 target preservation'


def policy_manifest():
    # A report commits to the complete selected policy and its actual producers.
    modules = ('static_callback_target_preservation_profile.py',
               'static_callback_buffer_profile.py', 'named_data_buffer_profile.py',
               'owner_admission_profile.py', 'owner_graph_profile.py',
               'inert_spin_profile.py', 'function_thunk_profile.py', 'analyze.py',
               'local_long_branch_profile.py', 'switch_constants_profile.py', 'match.py', 'armv4t.py')
    return dict(schema='thumb-static-callback-unwritten-r7-policy-v1',
        selector=SELECTOR, register=7, thunk=THUNK,
        preservation='every reached instruction leaves R7 unwritten, including inspected dependencies',
        attestation='proof-instance result identity, exact site/thunk/incoming value, consumed once',
        other_constants='cleared at every call', descriptor_words=False,
        callback_effects='complete fresh existing bounded-buffer replay for every context',
        returning='conditional normal return only',
        source_function_type_compatibility='not established by this native policy',
        source_sha256={name: hashlib.sha256(Path(importlib.import_module(name[:-3]).__file__).read_bytes()).hexdigest()
                       for name in modules})


class _CallbackResult(dict):
    """Unmodified alias result with a proof-instance-owned, one-use attestation."""


class StaticCallbackTargetPreservationProof(callback.StaticCallbackBufferProof):
    # Existing composed R7 policies initialize their own independent bases.
    # Keep their inherited preservation hook on its original R7 policy.
    _target_register = REGISTER
    _target_thunk = THUNK

    def __init__(self, rom, mapping, index, objects, *, policy):
        if policy != SELECTOR:
            raise ValueError('callback target preservation requires its explicit exact policy')
        super().__init__(rom, mapping, index, objects)
        self._target_register = REGISTER
        self._target_thunk = THUNK
        self._completed = {}
        self._preservations = {}

    def word_context(self, words, frame_base, root_frame, watched=()):
        if words:
            raise ValueError('unwritten-R7 policy excludes descriptor word provenance composition')
        if not watched:
            return {}
        # Existing BufferCallProof propagates watched registers through every
        # inspected nested call, even when no local pointer argument is passed.
        return dict(words={}, frame_base=frame_base, root_frame=root_frame,
                    watched=tuple(sorted(set(watched))))

    def check_arguments(self, address, arguments, stack, incoming, protected, *,
                        constants=None, site=None, **word_context):
        if word_context.get('words'):
            raise ValueError('unwritten-R7 policy excludes descriptor word provenance composition')
        if address != self._target_thunk:
            return super().check_arguments(address, arguments, stack, incoming, protected,
                constants=constants, site=site, **word_context)
        if type(site) is not int:
            raise ValueError('preserved callback fact requires an exact caller site')
        facts = dict(constants or {})
        watched = tuple(sorted(set(word_context.get('watched', ())) | {self._target_register}))
        context = dict(word_context, words={},
            frame_base=word_context.get('frame_base'), root_frame=word_context.get('root_frame'),
            watched=watched)
        # No identity-only terminal and no cached effects: the existing exact
        # thunk/target resolver and complete buffer replay must finish first.
        aliases = super().check_arguments(address, arguments, stack, incoming, protected,
            constants=constants, site=site, **context)
        result = _CallbackResult(aliases)
        receipt = dict(site=site, thunk=address, register=self._target_register, value=facts[self._target_register],
            target=facts[self._target_register] & ~1, watched=list(watched),
            precondition=f'no reached instruction writes watched R{self._target_register - match.ARM_REG_R0} in callback or inspected dependencies',
            returning='conditional normal return only')
        # Holding the exact object prevents id reuse and copied/forged aliases
        # from acquiring a preservation fact. It is consumed at the real call.
        self._completed[id(result)] = (result, receipt)
        return result

    def finish_call_constants(self, constants, result, *, site=None, target=None):
        incoming = dict(constants)
        completed = self._completed.pop(id(result), None)
        super().finish_call_constants(constants, result, site=site, target=target)
        if completed is None:
            return
        original, receipt = completed
        if original is not result or receipt['site'] != site or receipt['thunk'] != target or \
                incoming.get(self._target_register) != receipt['value']:
            raise ValueError('preserved callback fact does not match the exact completed call context')
        # The callback entry/return proof forbids every target-register write, rather than
        # inferring restoration from a compatible prototype or a PUSH/POP pair.
        constants[self._target_register] = receipt['value']
        key = json.dumps(receipt, sort_keys=True, separators=(',', ':'))
        self._preservations[key] = receipt

    def preservation_observations(self):
        return [self._preservations[key] for key in sorted(self._preservations)]
