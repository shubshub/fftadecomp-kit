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
    return carried(match.render_report(
        addr=address, src_rel=source or evidence.report_source(root, address), schema=schema,
        fingerprint=evidence.source_fingerprint(root, address),
        compiler=compiler or f"{match.DEFAULT_CC} {match.DEFAULT_FLAGS}", want=body, span=len(body),
        got_body=body, verdict="MATCH - byte identical", same_bytes=len(body), listing=listing,
        framed_profile=thumb and match.uses_stack_frame(instructions),
        mapping=evidence.mapping_snapshot(root) if mapping is None else mapping,
        data_mapping=evidence.data_snapshot(root) if data_mapping is None else data_mapping, **parts),
        root, address)


def rom_image(test, image):
    """For the rest of `test`: match_evidence.report_rom_path names a file holding `image`, the ROM
    the standing frame premise check compares a fixture report's ROM bytes with, for a fixture that
    replays a report under a root with no ROM of its own (its schema replay mocked or fed the image)."""
    import os
    import tempfile
    scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", Path(__file__).resolve().parents[1] / "build"))
    scratch.mkdir(parents=True, exist_ok=True)
    directory = tempfile.TemporaryDirectory(prefix="premise_rom_", dir=scratch)
    test.addCleanup(directory.cleanup)
    rom = Path(directory.name) / "fixture.bin"
    rom.write_bytes(bytes(image))
    patcher = mock.patch.object(evidence, "report_rom_path", return_value=str(rom))
    patcher.start()
    test.addCleanup(patcher.stop)
    return rom


def rom_holding(test, data, address):
    """rom_image of a ROM holding `data` at `address` and zeros before it."""
    return rom_image(test, bytes(address - match.ROM_BASE) + bytes(data))


def premise_line_checked_elsewhere():
    """A patch under which report_matches passes a report to its schema replay without the standing
    frame premise check, for a synthetic report with no ROM bytes line whose schema replay is itself
    mocked (the check is test_standing_premise's)."""
    import standing_premise
    return mock.patch.object(standing_premise, "strip", side_effect=lambda report, root, address: report)


def replay(report, root, address):
    """match_evidence.report_matches for a fixture report, so that a refusal is the test's own.

    A report without the standing frame premise line gets it first, as match.py would write it,
    where it can carry it.  If the premise check then passes, the whole check decides, and a refusal
    can only be for what the test changed.  If it refuses (the change under test is one the premise
    check also sees: the ROM's bytes, the ROM bytes line or the verification line), the schema replay
    alone must refuse the text without the line; if it accepts it, the negative would be decided by
    the premise check alone, and this raises.

    It serves negatives only.  A positive must replay a text that already carries the line (one
    match.py wrote, or report_fixtures.carried for a fixture render): one that needed the line added
    here raises, so a route that stopped writing the line cannot pass through a positive.  A report
    without the line is given it again, so a test whose change is to the premise line itself (dropping
    it, say) must call match_evidence.report_matches."""
    import standing_premise
    added = False
    if standing_premise.LINE not in report:
        try:
            text = standing_premise.carry(report, root, address)
        except (OSError, ValueError):
            text = report
        added, report = text != report, text
    try:
        standing_premise.strip(report, root, address)
    except (OSError, ValueError, UnicodeError):
        if evidence._report_matches(standing_premise.without(report), root, address):
            raise AssertionError("only the standing frame premise check refuses this report; the replay the "
                                 "test means accepts it")
        return False
    accepted = evidence.report_matches(report, root, address)
    if accepted and added:
        raise AssertionError("a positive on a text without the standing frame premise line: replay the "
                             "report match.py writes, or report_fixtures.carried for a fixture render")
    return accepted


def assert_premise_holds(test, report, root, address):
    """`report` passes the standing frame premise check (standing_premise.strip), so a replay that
    refuses it refuses for a reason of its own, not for the frame premise line."""
    import standing_premise
    try:
        standing_premise.strip(report, root, address)
    except ValueError as error:
        test.fail(f"the standing frame premise check refuses this report: {error}")


def uncarried(report):
    """`report` without the standing frame premise line, as a profile's own replay reads it
    (match_evidence.report_matches removes the line before it calls one)."""
    import standing_premise
    return standing_premise.without(report)


def carried(report, root, address):
    """`report` as match.py writes it: with the standing frame premise line when the function holds a frame.

    A fixture whose ROM does not hold its body (one whose replay must refuse on the bytes) cannot carry
    the line; it is returned as rendered, and its replay still refuses.
    """
    import standing_premise
    try:
        return standing_premise.carry(report, root, address)
    except (OSError, ValueError):
        return report


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
