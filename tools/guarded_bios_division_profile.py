"""Guarded buffer aliases with one exact conditional scalar service6 wrapper."""
import hashlib
from pathlib import Path

import match
import named_data_buffer_profile as buffers
import owner_graph_profile as graph
from ordinary_formal_output_spill_profile import BiosRemainderSpillProof

SCHEMA = 'elf-symbol-thumb-bounded-buffer-guarded-bios-division-v1'
SELECTOR = 'bounded-buffer-guarded-bios-division-v1'
CONTROL_FLOW = ('complete guarded buffer alias replay with an exact conditional '
                'scalar BIOS service6 wrapper; no numerical theorem')
MAX_DEPENDENCIES = buffers.GUARDED_ALIAS_MAX_DEPENDENCIES
ADDRESS = 0x08141870
WRAPPER = bytes.fromhex('06df7047')
CONTRACT = BiosRemainderSpillProof.contract


class GuardedBiosDivisionProof(buffers.GuardedAliasBufferProof):
    """Keep every ordinary effect; scalar BIOS calls cannot receive aliases."""

    def __init__(self, *args):
        super().__init__(*args)
        self.bios_calls = {}

    def check_arguments(self, address, arguments, stack, incoming, protected, *,
                        constants=None, site=None, **context):
        if address != ADDRESS:
            return super().check_arguments(address, arguments, stack, incoming,
                protected, constants=constants, site=site, **context)
        if arguments or context.get('words') or type(site) is not int:
            raise ValueError('BIOS division requires an actual scalar call without register aliases or words')
        saved = set(range(match.ARM_REG_R0 + 4, match.ARM_REG_R0 + 12))
        if set(context.get('watched', ())) - saved:
            raise ValueError('BIOS division preserves only ABI callee-saved live aliases')
        for offset in incoming.values():
            self.validate_pointer_value(offset, stack)
        data = self.span(address)
        if data != WRAPPER:
            raise ValueError('BIOS division requires exact complete svc6; bx lr wrapper')
        owners = [row for row in self.entries
                  if int(row['rom'], 16) <= site < int(row['end'], 16)]
        if len(owners) != 1:
            raise ValueError('BIOS division requires one complete actual consumer')
        consumer = int(owners[0]['rom'], 16)
        body = self.span(consumer)
        import owner_admission_profile as owner
        refinement = owner.refine(body, consumer, self.mapping)
        ins, edges, branches, calls, words = graph.graph(body, consumer, refinement)
        item = ins.get(site)
        if item is None or item.id != match.ARM_INS_BL or item.size != 4 or \
                calls.get(site) != address:
            raise ValueError('BIOS division differs from its actual direct call')
        self.dependencies[address] = data
        self.records[address] = dict(address=address, end=address+len(data), bytes=len(data),
            body_sha256=hashlib.sha256(data).hexdigest(), **self.identities,
            structure=dict(kind=SCHEMA, instructions=2, wrapper_hex=data.hex(),
                           conditional_ABI=CONTRACT))
        record = dict(site=site, target=address, consumer=consumer,
            consumer_body_sha256=hashlib.sha256(body).hexdigest(),
            partition=graph.partition(body, consumer, refinement, ins, words),
            untouched_incoming_slots=sorted(incoming.items()),
            protected_slots=sorted(protected),
            preserved_alias_registers=sorted(context.get('watched', ())),
            unknown_results=[0, 1, 2, 3, 12])
        self.bios_calls[repr(record)] = record
        return self.word_result({}, {})

    def bios_manifest(self):
        if not self.bios_calls:
            raise ValueError('BIOS division profile requires an actual checked wrapper call')
        import importlib
        producers = ('guarded_bios_division_profile', 'ordinary_formal_output_spill_profile',
                     'named_data_buffer_profile', 'owner_admission_profile',
                     'owner_graph_profile', 'analyze', 'inert_spin_profile', 'match', 'armv4t')
        return dict(schema=SCHEMA, wrapper_address=ADDRESS, wrapper_hex=WRAPPER.hex(),
            conditional_ABI=CONTRACT,
            source_sha256={name+'.py': hashlib.sha256(
                Path(importlib.import_module(name).__file__).read_bytes()).hexdigest()
                for name in producers},
            observations=[self.bios_calls[key] for key in sorted(self.bios_calls)])
