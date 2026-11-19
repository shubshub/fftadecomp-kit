"""Complete saved reports for replay fixtures.

A cached replay compares the whole saved report with the text match.py writes
for the evidence it re-verified (match_evidence.closed_report), so a fixture
report must be that text, not a list of the lines a test cares about. These
helpers render it with match.render_report from a fixture's own evidence.
"""

from pathlib import Path
import sys
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import match
import match_evidence as evidence


def complete(root, address, body, schema, instructions, *, thumb=True, source=None, compiler=None,
             mapping=None, data_mapping=None, **parts):
    """The report match.py writes for a MATCH of `body` at `address` with these evidence blocks.

    `instructions` are the verified instructions the schema's replay re-derives
    (its listing); `parts` are render_report's evidence keywords.  The source
    path, digests and snapshots default to what the replay reads from `root`,
    through match_evidence, so a test's patches of those apply here too.
    """
    body = bytes(body)
    listing, _, _ = match.report_listing(instructions, body, address, len(body), thumb)
    return match.render_report(
        addr=address, src_rel=source or evidence.report_source(root, address), schema=schema,
        fingerprint=evidence.source_fingerprint(root, address),
        compiler=compiler or f"{match.DEFAULT_CC} {match.DEFAULT_FLAGS}", want=body, span=len(body),
        got_body=body, verdict="MATCH - byte identical", same_bytes=len(body), listing=listing,
        framed_profile=thumb and match.uses_stack_frame(instructions),
        mapping=evidence.mapping_snapshot(root) if mapping is None else mapping,
        data_mapping=evidence.data_snapshot(root) if data_mapping is None else data_mapping, **parts)


def legacy_report(root, address, body, schema, *, thumb=True, self_sites=frozenset(), **parts):
    """A complete plain, call or data report (cfg-leaf, frame, calls, frame-calls, data, frame-data).

    The listing is the walk verify_leaf_instructions reaches, accepting every
    call target (or the linear decode when the body does not verify, whose
    replay refuses before comparing text); calls are its BLs, as match.py
    derives them.
    """
    body = bytes(body)
    try:
        instructions = match.verify_leaf_instructions(
            body, address, thumb, call_resolver=lambda target: None, self_calls=self_sites or None,
            incoming_narrow_reads=thumb and not self_sites)
    except (ValueError, KeyError, TypeError, AttributeError):
        instructions = decode(body, address, thumb)
    linked = any(instruction.mnemonic == "bl" for instruction in instructions)
    data = schema in (evidence.DATA_SCHEMA, evidence.FRAMED_DATA_SCHEMA)
    parts.setdefault("mapped", linked or data)
    parts.setdefault("control_flow", evidence.CALL_SUMMARY if linked else "closed leaf CFG")
    return complete(root, address, body, schema, instructions, thumb=thumb, data_profile=data,
                    self_sites=self_sites, **parts)


def switch_report(root, address, body, schema, manifest, *, data=True, thunk_switch_selector=None,
                  summary=None, fingerprint=None, **parts):
    """A complete switch report for `manifest`.

    Its listing and control-flow line come from verify_switches when the
    manifest verifies against the fixture's ROM; a manifest that does not
    verify gets the linear decode, since its replay refuses before comparing
    text.  `summary` and `fingerprint` replace the `* switches:` and
    `* switch proof SHA-256:` values the writer derives from the manifest, for
    fixtures that pin them while varying the manifest.
    """
    body = bytes(body)
    mapping = evidence.mapping_snapshot(root)
    objects = evidence.data_snapshot(root) if data else None
    try:
        rom = Path(evidence.report_rom_path(root)).read_bytes()
        instructions, control_flow = match.verify_switches(body, address, rom, mapping, manifest,
                                                           data_mapping=objects)
    except (OSError, ValueError, KeyError, TypeError, AttributeError):
        instructions, control_flow = decode(body, address), "closed leaf CFG"
    parts.setdefault("control_flow", control_flow)
    report = complete(root, address, body, schema, instructions, mapped=True, data_profile=data, switches=True,
                      switch_evidence=manifest, thunk_switch_selector=thunk_switch_selector, **parts)
    lines = report.split("\n")
    for prefix, value in (("* switches: ", summary), ("* switch proof SHA-256: ", fingerprint and f"`{fingerprint}`")):
        if value is not None:
            lines = [prefix + value if line.startswith(prefix) else line for line in lines]
    return "\n".join(lines)


def thunk_report(root, address, body, manifest, selector, *, rom, index, objects, schema=None):
    """A complete function-address-thunk report; the listing is function_thunk_profile.verify's walk
    (the linear decode when the manifest does not verify)."""
    import function_thunk_profile as thunks
    body = bytes(body)
    try:
        instructions = thunks.verify(body, address, rom, evidence.mapping_snapshot(root), index, objects, manifest)
    except (ValueError, KeyError, TypeError, AttributeError, IndexError):
        instructions = decode(body, address)
    return complete(root, address, body, schema or thunks.schema_for(selector), instructions, mapped=True,
                    control_flow=thunks.CONTROL_FLOW, data_profile=bool(manifest.get("data")), data_mapping=objects,
                    function_index=index, rom=rom, thunk_profile=True, function_address_profile=selector,
                    thunk_evidence=manifest)


def decode(body, address, thumb=True):
    """Linear capstone decode with operand detail, as the verifiers decode."""
    from capstone import CS_ARCH_ARM, CS_MODE_ARM, CS_MODE_THUMB, Cs
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB if thumb else CS_MODE_ARM)
    decoder.detail = True
    return list(decoder.disasm(bytes(body), address))


def source_at(test, path):
    """For a fixture whose root holds no source file: the replay names `path`."""
    patcher = mock.patch.object(evidence, "report_source", return_value=path)
    patcher.start()
    test.addCleanup(patcher.stop)
