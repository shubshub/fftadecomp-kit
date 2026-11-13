"""Incoming scratch aliases killed before observation in an ordinary call.

Only a closed, straight-line entry prefix is interpreted. After every incoming
alias is overwritten, the original ordinary returning-ABI premises apply to
the residual body, including its own local pointers and nested calls.
"""
import hashlib
from pathlib import Path

import match
import owner_admission_profile as owner
import owner_graph_profile as graph
import scheduler_leaf_output_profile as leaf

MAX_PREFIX_INSTRUCTIONS = 32


def effects(instruction):
    """Exact full-register effects for a deliberately small Thumb-1 prefix."""
    leaf.require(instruction.size == 2, 'alias kill prefix excludes calls and wide instructions')
    word = int.from_bytes(instruction.bytes, 'little')
    reg = lambda n: match.ARM_REG_R0 + n
    read, written = set(), set()
    if word & 0xFE00 == 0xB400:  # PUSH low registers and optional LR
        read = {reg(n) for n in range(8) if word & (1 << n)} | {match.ARM_REG_SP}
        if word & 0x100:
            read.add(match.ARM_REG_LR)
        written = {match.ARM_REG_SP}
    elif word & 0xFF80 == 0xB080:  # fixed SUB SP,imm7*4
        read, written = {match.ARM_REG_SP}, {match.ARM_REG_SP}
    elif word & 0xF800 == 0x9800:  # full aligned SP-relative word load
        read, written = {match.ARM_REG_SP}, {reg((word >> 8) & 7)}
    elif word & 0xF800 == 0x4800:  # full PC-relative word load
        read, written = {match.ARM_REG_PC}, {reg((word >> 8) & 7)}
    elif word & 0xF800 == 0x2000:  # MOV low register,imm8
        written = {reg((word >> 8) & 7)}
    elif word & 0xFF00 == 0x4600:  # full high/low register MOV
        source, destination = (word >> 3) & 15, (word & 7) | ((word >> 4) & 8)
        leaf.require(source < 13 and destination < 13,
                     'alias kill prefix excludes SP/LR/PC register moves')
        read, written = {reg(source)}, {reg(destination)}
    else:
        raise ValueError('alias kill prefix excludes unsupported, partial or conditional effects')
    actual_read, actual_written = instruction.regs_access()
    leaf.require(set(actual_read) - {match.ARM_REG_CPSR} == read and
                 set(actual_written) - {match.ARM_REG_CPSR} == written,
                 'alias kill prefix has inconsistent implicit register effects')
    return read, written


def overwrite(instructions, edges, address, aliases):
    """No incoming value may be read, copied, saved or passed before its kill."""
    live, prefix, current = set(aliases), [], address
    while live:
        leaf.require(len(prefix) < MAX_PREFIX_INSTRUCTIONS,
                     'alias kill prefix exceeds explicit instruction bound')
        item = instructions[current]
        read, written = effects(item)
        leaf.require(not live & read, 'alias kill prefix observes a live incoming alias')
        killed = live & written
        live -= written
        prefix.append(dict(site=current, encoding=item.bytes.hex(),
            read=sorted(read), written=sorted(written), killed=sorted(killed),
            remaining=sorted(live)))
        leaf.require(edges[current] == (current + item.size,),
                     'alias kill prefix excludes branches, joins and returns')
        current += item.size
    return prefix


def check_call(proof, address, aliases, stack, slots, *, site):
    leaf.require(address in proof.branch_calls['ordinary_targets'] and not slots,
                 'alias kill requires an indexed ordinary call without pointer slots')
    if not aliases:
        return leaf.check_call(proof, address, aliases, stack, slots, site=site)
    leaf.require(set(aliases) <= set(match.CALLER_CLOBBERED) - {match.ARM_REG_LR},
                 'alias kill excludes preserved-register aliases')
    for offset in aliases.values():
        proof.validate_pointer_value(offset, stack)
    body = proof.span(address)
    leaf.require(proof.dependencies[address] == body,
                 'alias kill differs from authenticated complete ordinary body')
    refinement = owner.refine(body, address, proof.mapping)
    instructions, edges, branches, calls, words = graph.graph(body, address, refinement)
    if not calls:
        return leaf.check_call(proof, address, aliases, stack, slots, site=site)
    leaf.require(not branches and not words, 'alias kill excludes local BL and switch owners')
    partition = graph.partition(body, address, refinement, instructions, words)
    prefix = overwrite(instructions, edges, address, aliases)
    observation = dict(site=site, target=address,
        kind='complete-ordinary-entry-alias-overwrite', aliases=sorted(aliases.items()),
        incoming_registers=sorted(aliases), frame=[list(word) for word in stack],
        pointer_words=[], returned_aliases=[], prefix=prefix,
        helper=proof.records[address], partition=partition,
        nested_calls=sorted(calls.items()),
        source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        ordinary_callee_effects_proved=False, nested_execution_proved=False,
        assumptions=[
            'All supplied incoming aliases are overwritten before any read, copy, save, branch or call.',
            'The residual complete ordinary body retains the existing returning ARM ABI, exact SP, '
            'protected caller/saved words and noninterference premises. Its own local pointers and '
            'nested calls have no inferred effects, nonretention, safety or termination proof.'])
    leaf.require(site not in proof.observations or proof.observations[site] == observation,
                 'alias kill differs across incoming call paths')
    proof.observations[site] = observation
    return {}
