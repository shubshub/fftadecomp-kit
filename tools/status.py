#!/usr/bin/env python3
"""
status.py - how much of the ROM is actually decompiled.

    python tools/status.py                 # print the block
    python tools/status.py --write         # rewrite it into the decomp README
    python tools/status.py --verify        # recompile every src/*.c first
    python tools/status.py --check         # exit 1 if the README is stale
    python tools/status.py --badges badges # shields.io endpoint JSON

Retains two legacy provisional metrics:

    functions matched / total
    bytes matched / total        (main indexed spans / legacy layout code sizes)

plus a bytes row over the union of main index spans, and matched bytes per
64 KiB region of that union.  The badges read only the two legacy rows.

Additional verified late-ROM functions and complete-body bytes are reported
separately, without a guessed denominator or whole-ROM completion percentage.

A function counts as matched when src/<addr>.c exists *and* its match report
says the bytes are identical.  --verify recompiles instead of trusting the
report, which is what CI should do.
--write --verify also regenerates the reports so offline checks stay current.
--verify alone and --check never rewrite match reports.

--badges writes functions.json and bytes.json in the shields.io *endpoint*
format, to be published on a `badges` branch and rendered with
img.shields.io/endpoint?url=... .
"""

import argparse
from concurrent.futures import ProcessPoolExecutor, ThreadPoolExecutor
from contextlib import nullcontext
import json
import multiprocessing
import os
from pathlib import Path
import re
import subprocess
import sys
from threading import Lock, active_count
from match_evidence import (report_matches, compiler_flags,
                            SWITCH_U16_SCALAR_SCHEMA, SWITCH_U16_SCALAR_SELECTOR,
                            SWITCH_POOL_U16_SCALAR_SCHEMA, SWITCH_POOL_U16_SCALAR_SELECTOR)
import inert_spin_profile as inert_spin
import software_double_profile as software_double
import function_thunk_profile as function_thunk
import switch_constants_profile as switch_constants
import typed_switch_outgoing_frame as typed_switch_frame
import divsi3_profile as divsi3
from rompath import rom_path

# the status block uses block-drawing characters; Windows consoles are cp1252
for _stream in ("stdout", "stderr"):
    try:
        getattr(sys, _stream).reconfigure(encoding="utf-8", errors="replace")
    except (AttributeError, ValueError):
        pass

START = "<!-- ffta-status:start -->"
END = "<!-- ffta-status:end -->"
CODE_END = 0x08150000
ROM_BASE = 0x08000000
ROM_END = 0x09000000

# colour thresholds for a percentage badge
COLOR_THRESHOLDS = [(20, "red"), (40, "orange"), (60, "yellow"),
                    (80, "yellowgreen"), (100, "green")]


def color_for(percent):
    for threshold, color in COLOR_THRESHOLDS:
        if percent < threshold:
            return color
    return "brightgreen"


def badge(label, percent, detail=""):
    return {"schemaVersion": 1,
            "label": label,
            "message": f"{percent:.2f}%",
            "color": color_for(percent)}


def static_badge(label, percent):
    """A shields.io *static* badge URL.

    Static (rather than /endpoint?url=...) because shields.io fetches endpoint
    URLs itself and cannot read a private repository - it renders "resource not
    found".  These render for any repo, and the URL is regenerated from the
    numbers whenever the block is rewritten, so they stay current.
    """
    from urllib.parse import quote
    msg = quote(f"{percent:.2f}%", safe="")
    return (f"https://img.shields.io/badge/{quote(label, safe='')}-{msg}-"
            f"{color_for(percent)}")


def endpoint_badge(label, percent, badge_base):
    """A shields.io *endpoint* badge: self-updating, but only for a public repo.

    shields.io fetches the JSON itself, so this only works when the repository
    holding badge_base is public - and the numbers then come straight from the
    JSON on the badges branch without anyone rewriting the README.
    """
    from urllib.parse import quote
    url = f"{badge_base.rstrip('/')}/{label.split()[-1]}.json"
    return (f"https://img.shields.io/endpoint?"
            f"url={quote(url, safe='')}")


def repo_root(arg=None):
    return os.path.abspath(arg or os.environ.get("FFTA_ROOT") or os.getcwd())


def badge_base_from_remote(root):
    """derive the raw badges URL from the repo's origin remote.

    Without this, --write and --check disagree unless both remember
    FFTA_BADGE_BASE, and a stale block slips in whenever one of them runs
    without it.
    """
    import subprocess
    r = subprocess.run(["git", "-C", root, "remote", "get-url", "origin"],
                       capture_output=True, text=True)
    if r.returncode != 0:
        return ""
    m = re.search(r"github\.com[:/]([^/]+)/([^/\s]+?)(?:\.git)?$", r.stdout.strip())
    if not m:
        return ""
    return f"https://raw.githubusercontent.com/{m.group(1)}/{m.group(2)}/badges"


def bar(frac, width=28):
    filled = int(round(frac * width))
    return "█" * filled + "░" * (width - filled)


def report_extent(report, *, strict=True):
    prefix = "* compiled" if strict else "* compiled : "
    records = [line for line in report.splitlines()
               if (line.lstrip() if strict else line).startswith(prefix)]
    if len(records) != 1:
        raise ValueError("missing or duplicate compiled-body evidence")
    match = re.fullmatch(r"\* compiled : `((?:[0-9a-f]{2})+)`", records[0])
    if match is None:
        raise ValueError("malformed compiled-body evidence")
    return len(match[1]) // 2


def matcher_extent(output, *, strict=True):
    prefix = "extent" if strict else "extent    "
    records = [line for line in output.splitlines()
               if (line.lstrip() if strict else line).startswith(prefix)]
    if len(records) != 1:
        raise ValueError("missing or duplicate matcher extent")
    match = re.fullmatch(
        r"extent    ([1-9][0-9]*) bytes \(complete ELF symbol; [^\r\n]+; no relocations\)",
        records[0])
    if match is None:
        raise ValueError("malformed matcher extent")
    return int(match[1])


def late_mapping(root, address, entries):
    matches = [entry for entry in entries if int(entry["rom"], 16) == address]
    if len(matches) != 1:
        raise ValueError("late source requires one unique indexed function")
    entry = matches[0]
    mode = entry.get("mode")
    if mode not in ("thumb", "arm"):
        raise ValueError("late function mode must be thumb or arm")
    end = int(entry["end"], 16)
    alignment = 2 if mode == "thumb" else 4
    if address % alignment or end <= address or (end - address) % alignment:
        raise ValueError("late function entry/body is not positive and mode-aligned")
    selected_end = min(ROM_END, ROM_BASE + os.path.getsize(rom_path(root)))
    if not CODE_END <= address < end <= selected_end:
        raise ValueError("late function extent is outside the original ROM")
    for other in entries:
        if other is not entry and int(other["rom"], 16) < end and \
                address < int(other["end"], 16):
            raise ValueError("late function extent overlaps another indexed function")
    return end - address, mode


def _initialize_process(check_source):
    # The explicit fork context inherits this invocation's closed checker.
    # Only children receive it; concurrent parent invocations share no state.
    global _process_check_source
    _process_check_source = check_source


def _check_process_group(group):
    return [(index, _process_check_source(path)) for index, path in group]


def _process_results(paths, check_source, workers):
    # A group owns one report destination, including duplicate source names.
    groups = {}
    for index, path in enumerate(paths):
        groups.setdefault(path.stem.upper(), []).append((index, path))
    with ProcessPoolExecutor(max_workers=workers,
                             mp_context=multiprocessing.get_context("fork"),
                             initializer=_initialize_process,
                             initargs=(check_source,)) as executor:
        indexed = [item for group in executor.map(_check_process_group, groups.values())
                   for item in group]
    return [result for _, result in sorted(indexed)]


def collect(root, verify, quiet=False, write_reports=False, jobs=1, worker_processes=0,
            *, progress=None, _publication_results=None):
    """progress, when a dict, receives index_progress() for the matched functions."""
    if not 1 <= jobs <= 64:
        raise ValueError("jobs must be between 1 and 64")
    if not 0 <= worker_processes <= 64:
        raise ValueError("worker_processes must be between 0 and 64")
    if worker_processes:
        if jobs != 1:
            raise ValueError("worker processes require jobs=1")
        if "fork" not in multiprocessing.get_all_start_methods() or active_count() != 1:
            raise ValueError("worker processes require fork and a single-threaded caller")
    cfg = os.path.join(root, "config", "functions.json")
    if not os.path.exists(cfg):
        sys.exit(f"no {cfg} - run analyze first")
    fns = json.load(open(cfg, encoding="utf-8"))

    code = [f for f in fns if int(f["rom"], 16) < CODE_END]
    total_fns = len(code)
    total_bytes = 0
    layout_path = os.path.join(root, "config", "rom_layout.json")
    if os.path.exists(layout_path):
        layout = json.load(open(layout_path, encoding="utf-8"))
        total_bytes = sum(seg["size"] for seg in layout.get("segments", [])
                          if seg.get("name", "").startswith("code"))
    if not total_bytes:
        covered = set()
        for f in code:
            covered.update(range(int(f["rom"], 16), int(f["end"], 16)))
        total_bytes = len(covered)

    src_dir = os.path.join(root, "src")
    matched_f, matched_b, problems = 0, 0, []
    paths = sorted(Path(src_dir).rglob("*.c")) if os.path.isdir(src_dir) else []
    source_counts = {}
    for path in paths:
        identity = path.stem.upper()
        source_counts[identity] = source_counts.get(identity, 0) + 1

    def check_source(path):
        matched_f, matched_b, problems = 0, 0, []
        verified_bodies = []
        name = path.name
        if not name.endswith(".c"):
            return 0, 0, problems, []
        addr = name[:-2].upper()
        late = bool(re.fullmatch(r"[0-9A-F]{8}", addr)) and int(addr, 16) >= CODE_END
        if late:
            try:
                if name != f"{addr}.c" or source_counts[addr] != 1:
                    raise ValueError("late source requires one canonical addressed source")
                span, mode = late_mapping(root, int(addr, 16), fns)
            except (OSError, ValueError, KeyError, TypeError, SystemExit) as error:
                problems.append(f"{addr}: {error}")
                return 0, 0, problems, []
        else:
            span = next((int(f["end"], 16) - int(f["rom"], 16)
                         for f in code if f["rom"][2:].upper() == addr), None)
        if span is None:
            problems.append(f"{addr}: src/{name} does not match a known function")
            return 0, 0, problems, []

        ok = False
        report = None
        rep = os.path.join(root, "docs", "match", f"{addr}.md")
        saved_flags = None
        spin_profile = False
        double_profile = False
        target_remainder_profile = False
        thunk_profile = False
        owner_profile = False
        constants_profile = False
        typed_outgoing_profile = False
        u16_switch_profile = False
        unsigned_quotient_frame = False
        quotient_frame = False
        signed_runtime_profile = False
        unsigned_runtime_profile = False
        addressed_runtime_profile = False
        private_float_profile = False
        palette_source_profile = False
        if os.path.exists(rep):
            with open(rep, encoding="utf-8") as report_file:
                saved_report = report_file.read()
            try:
                import unsigned_divmod_profile
                unsigned_runtime_profile = unsigned_divmod_profile.selector_for_report(saved_report)
                import palette_source_admission_profile
                palette_source_profile = palette_source_admission_profile.selector_for_report(saved_report)
                import private_float_pack_admission_profile
                private_float_profile = private_float_pack_admission_profile.selector_for_report(saved_report)
                import addressed_signed_runtime_profile
                addressed_runtime_profile = addressed_signed_runtime_profile.selector_for_report(saved_report)
                import signed_divmod_profile
                signed_runtime_profile = signed_divmod_profile.selector_for_report(saved_report)
                import owner_admission_profile
                owner_profile = owner_admission_profile.selected(saved_report)
                constants_profile = switch_constants.selected_policy(saved_report)
                typed_outgoing_profile = typed_switch_frame.selector_for_report(saved_report)
                u16_switch_profile = (
                    SWITCH_U16_SCALAR_SELECTOR
                    if f"* verification: `{SWITCH_U16_SCALAR_SCHEMA}`" in saved_report.splitlines() else
                    SWITCH_POOL_U16_SCALAR_SELECTOR
                    if f"* verification: `{SWITCH_POOL_U16_SCALAR_SCHEMA}`" in saved_report.splitlines() else
                    False)
                double_profile = software_double.selected(saved_report)
                if double_profile:
                    target_remainder_profile = software_double.target_remainder_selected(saved_report)
                thunk_profile = function_thunk.selector_for_report(saved_report)
                spin_profile = inert_spin.selected(saved_report)
                from match_evidence import UDIVSI3_FRAMED_SCHEMA
                unsigned_quotient_frame = f"* verification: `{UDIVSI3_FRAMED_SCHEMA}`" in saved_report.splitlines()
                quotient_frame = f"* verification: `{divsi3.FRAMED_SCHEMA}`" in saved_report.splitlines()
                saved_flags = compiler_flags(saved_report)
            except ValueError as error:
                problems.append(f"{addr}: {error}")
                return 0, 0, problems, []
        if verify:
            if u16_switch_profile and not report_matches(saved_report, root, int(addr, 16)):
                problems.append(f"{addr}: invalid saved u16 scalar switch report")
                return 0, 0, problems, []
            if typed_outgoing_profile and not report_matches(saved_report, root, int(addr, 16)):
                problems.append(f"{addr}: invalid saved typed outgoing switch report")
                return 0, 0, problems, []
            if unsigned_runtime_profile and not report_matches(saved_report, root, int(addr, 16)):
                problems.append(f"{addr}: invalid saved unsigned divmod report")
                return 0, 0, problems, []
            if addressed_runtime_profile and not report_matches(saved_report, root, int(addr, 16)):
                problems.append(f"{addr}: invalid saved addressed signed runtime report")
                return 0, 0, problems, []
            if signed_runtime_profile and not report_matches(saved_report, root, int(addr, 16)):
                problems.append(f"{addr}: invalid saved signed divmod report")
                return 0, 0, problems, []
            if unsigned_quotient_frame and not report_matches(saved_report, root, int(addr, 16)):
                problems.append(f"{addr}: invalid saved framed unsigned quotient report")
                return 0, 0, problems, []
            if quotient_frame and not report_matches(saved_report, root, int(addr, 16)):
                problems.append(f"{addr}: invalid saved framed signed quotient report")
                return 0, 0, problems, []
            if owner_profile and not report_matches(saved_report, root, int(addr, 16)):
                problems.append(f"{addr}: invalid saved complete-owner report")
                return 0, 0, problems, []
            if target_remainder_profile and not report_matches(saved_report, root, int(addr, 16)):
                problems.append(f"{addr}: invalid saved target-state remainder report")
                return 0, 0, problems, []
            if thunk_profile and not report_matches(saved_report, root, int(addr, 16)):
                problems.append(f"{addr}: invalid saved function-thunk report")
                return 0, 0, problems, []
            here = os.path.dirname(os.path.abspath(__file__))
            command = [sys.executable, os.path.join(here, "match.py"), "--root", root, addr]
            if late:
                command += ["--mode", mode]
            if spin_profile:
                command += ["--control-flow-profile", inert_spin.SELECTOR]
            if double_profile:
                command += ["--software-double-profile", software_double.SELECTOR]
                if target_remainder_profile:
                    command += ["--software-double-remainder-profile", software_double.REMAINDER_TARGET_SELECTOR]
            if thunk_profile:
                command += ["--function-address-profile", thunk_profile]
            if owner_profile:
                command += ["--owner-runtime-profile", owner_admission_profile.selector_for_report(saved_report)]
            if palette_source_profile:
                command += ["--owner-runtime-profile", palette_source_profile]
            if private_float_profile:
                command += ["--owner-runtime-profile", private_float_profile]
            if constants_profile:
                command += ["--switch-profile", constants_profile.selector]
            if typed_outgoing_profile:
                command += ["--switch-data-profile", typed_outgoing_profile]
            if u16_switch_profile:
                command += ["--switch-data-profile", u16_switch_profile]
            if unsigned_runtime_profile:
                command += ["--unsigned-runtime-profile", unsigned_runtime_profile]
            if signed_runtime_profile:
                command += ["--signed-runtime-profile", signed_runtime_profile]
            if addressed_runtime_profile:
                command += ["--addressed-signed-runtime-profile", addressed_runtime_profile]
            if unsigned_quotient_frame:
                from match_evidence import UDIVSI3_FRAMED_SELECTOR
                command += ["--unsigned-quotient-profile", UDIVSI3_FRAMED_SELECTOR]
            if quotient_frame:
                command += ["--signed-quotient-profile", divsi3.FRAMED_SELECTOR]
            if saved_flags is not None:
                command += ["--flags", saved_flags]
            if not write_reports:
                command.append("--no-write")
            result = subprocess.run(command, capture_output=True, text=True)
            ok = result.returncode == 0 and "verdict MATCH - byte identical" in result.stdout.splitlines()
        if not verify or (write_reports or spin_profile or double_profile or thunk_profile or constants_profile or typed_outgoing_profile or u16_switch_profile or owner_profile or quotient_frame or unsigned_quotient_frame or signed_runtime_profile or unsigned_runtime_profile or addressed_runtime_profile or private_float_profile or palette_source_profile) and ok:
            if os.path.exists(rep):
                with open(rep, encoding="utf-8") as report_file:
                    report = report_file.read()
                    ok = report_matches(report, root, int(addr, 16))
            else:
                ok = False
                problems.append(f"{addr}: no match report in docs/match/")
        if ok:
            extents, extent_errors = [], []
            evidence = [(matcher_extent, result.stdout)] if verify else []
            if report is not None:
                evidence.append((report_extent, report))
            for extract, payload in evidence:
                try:
                    extents.append(extract(payload, strict=late))
                except ValueError as error:
                    extent_errors.append(str(error))
            if late and extent_errors:
                problems.append(f"{addr}: {extent_errors[0]}")
                return 0, 0, problems, []
            if late and any(extent != span for extent in extents):
                problems.append(f"{addr}: complete verified body disagrees with the late indexed extent")
                return 0, 0, problems, []
            body_size = max(extents) if extents else None
            verified_bodies.append((int(addr, 16), body_size, late))
            if not late:
                matched_f += 1
                matched_b += span
        elif not verify:
            problems.append(f"{addr}: no current, source-bound MATCH report; re-run match.py")
        else:
            problems.append(f"{addr}: DOES NOT MATCH")

        return matched_f, matched_b, problems, verified_bodies

    # Duplicate addresses share a report path, so never process them concurrently.
    report_locks = {identity: Lock() for identity, count in source_counts.items() if count > 1}

    def check_locked_source(path):
        with report_locks.get(path.stem.upper(), nullcontext()):
            return check_source(path)

    # Only the live native publication session supplies this private map. It
    # authenticates the complete snapshot/runtime before and after collection.
    prior = _publication_results if _publication_results is not None else {}
    pending = [path for path in paths if str(path.relative_to(root)) not in prior]
    verified_bodies = []
    with ThreadPoolExecutor(max_workers=jobs) if verify and jobs > 1 else nullcontext() as executor:
        if worker_processes:
            results = _process_results(pending, check_source, worker_processes)
        else:
            results = executor.map(check_locked_source, pending) if executor else map(check_source, pending)
        fresh = dict(zip((str(path.relative_to(root)) for path in pending), results))
        if _publication_results is not None:
            _publication_results.update(fresh)
        results = (prior.get(str(path.relative_to(root)), fresh.get(str(path.relative_to(root))))
                   for path in paths)
        # map yields source order even when subprocesses finish out of order.
        for source_f, source_b, source_problems, source_bodies in results:
            matched_f += source_f
            matched_b += source_b
            problems.extend(source_problems)
            verified_bodies.extend(source_bodies)
    if progress is not None:
        progress.update(index_progress(
            fns, [address for address, _, late in verified_bodies if not late]))

    late_f, late_b = 0, 0
    unknown_main_extent = any(size is None and not late for _, size, late in verified_bodies)
    for index, (address, size, late) in enumerate(verified_bodies):
        if not late:
            continue
        if unknown_main_extent:
            problems.append(f"{address:08X}: cannot exclude overlap with an unknown complete main-body extent")
            continue
        if any(other_address < address + size and address < other_address + other_size
               for other_index, (other_address, other_size, _) in enumerate(verified_bodies)
               if other_index != index):
            problems.append(f"{address:08X}: late function overlaps another verified body")
            continue
        late_f += 1
        late_b += size
    return total_fns, matched_f, total_bytes, matched_b, problems, late_f, late_b


REGION = 0x10000


def merge_spans(spans):
    """the union of [start, end) spans, as sorted disjoint spans"""
    merged = []
    for start, end in sorted(spans):
        if merged and start <= merged[-1][1]:
            merged[-1][1] = max(merged[-1][1], end)
        else:
            merged.append([start, end])
    return merged


def clipped(merged, lo, hi):
    return sum(max(0, min(end, hi) - max(start, lo)) for start, end in merged)


def index_progress(fns, matched):
    """union index-span totals below CODE_END, per 64 KiB region and overall.

    fns is config/functions.json; matched holds matched main addresses.
    """
    matched = set(matched)
    entries = [(int(f["rom"], 16), int(f["end"], 16)) for f in fns]
    code = [span for span in entries if span[0] < CODE_END]
    done = [span for span in code if span[0] in matched]
    every, hits = merge_spans(code), merge_spans(done)
    regions = []
    for base in range(ROM_BASE, CODE_END, REGION):
        top = base + REGION
        regions.append((base, clipped(every, base, top), clipped(hits, base, top),
                        sum(base <= rom < top for rom, _ in code),
                        sum(base <= rom < top for rom, _ in done)))
    return {"total": clipped(every, 0, ROM_END), "matched": clipped(hits, 0, ROM_END),
            "regions": regions, "late_entries": len(entries) - len(code)}


def render_progress(progress):
    """the index-span row (with its footnote) and the per-region section"""
    total, done = progress["total"], progress["matched"]
    frac = done / total if total else 0.0
    row = (f"| Bytes matched (index span) | {done:,} / {total:,} | "
           f"**{frac * 100:.2f}%** | `{bar(frac)}` |")
    note = ("Both byte denominators are provisional. Layout labels undercount\n"
            "code; index spans can run long or cover code-like data. Neither\n"
            "denominator is established. The index-span row divides the union\n"
            "of matched entries' spans by the union, overlaps merged, of every\n"
            f"entry span starting below `0x{CODE_END:08X}`.")
    rows = []
    for base, region_total, region_done, count, count_done in progress["regions"]:
        part = region_done / region_total if region_total else 0.0
        rows.append(f"0x{base:08X}  {bar(part, 20)}  {part * 100:5.1f}%  "
                    f"{f'{count_done}/{count}':>9} fns")
    rows.append(f"0x{CODE_END:08X}+ assets and data; "
                f"{progress['late_entries']:,} index entries")
    section = ["Matched bytes per 64 KiB region (of indexed span)", "", "```"] + rows + ["```"]
    return row, note, section


def badge_url(label, percent, badge_base):
    """endpoint badges when the repo is public and a badges branch exists,
    otherwise static ones (which render everywhere, but need a rewrite to
    update)"""
    if badge_base:
        return endpoint_badge(label, percent, badge_base)
    return static_badge(label, percent)


def render(total_f, matched_f, total_b, matched_b, problems, prefix="", badge_base=None,
           *, late_f=0, late_b=0, progress=None):
    """progress, from index_progress(), adds the index-span row and region bars"""
    pf = matched_f / total_f if total_f else 0.0
    pb = matched_b / total_b if total_b else 0.0
    label = f"{prefix} " if prefix else ""
    lines = [
        START,
        "",
        "### Decompilation status",
        "",
        "Legacy provisional metrics (including the two percentage badges):",
        "",
        f"![{label}functions]({badge_url(f'{label}functions', pf * 100, badge_base)}) "
        f"![{label}bytes]({badge_url(f'{label}bytes', pb * 100, badge_base)})",
        "",
        "| Metric | Count | Percent | |",
        "|---|---|---|---|",
        f"| Functions matched | {matched_f:,} / {total_f:,} | **{pf * 100:.2f}%** | "
        f"`{bar(pf)}` |",
        f"| Bytes matched | {matched_b:,} / {total_b:,} | **{pb * 100:.2f}%** | "
        f"`{bar(pb)}` |",
    ]
    if progress is not None:
        span_row, span_note, regions = render_progress(progress)
        lines += [span_row]
    lines += [
        "",
        f"The function denominator counts {total_f:,} provisional index entries\n"
        f"starting below `0x{CODE_END:08X}`; matched main bytes count indexed spans.\n"
        f"The byte denominator sums all legacy layout segments named `code*`,\n"
        f"including late-ROM labels, or falls back to the union of main indexed\n"
        f"spans when that sum is zero or the layout is absent. Labels do not\n"
        f"prove code ownership; index spans can be truncated or overlapping.\n"
        f"Generated by `tools/status.py` from `config/functions.json` and the\n"
        f"match reports in `docs/match/`.",
    ]
    if progress is not None:
        lines += ["", span_note, ""] + regions
    lines += [
        "",
        f"**Legacy credit: {matched_f:,} matched functions and {matched_b:,} indexed bytes.**\n"
        f"Only exact matches are committed - see the rule in *Matching*.",
        "",
        f"**Additional verified late-ROM spans: {late_f:,} functions; "
        f"{late_b:,} complete-body bytes.**\n"
        f"These separately indexed and verified ROM bodies include their internal\n"
        f"literal pools, exclude external alignment and RAM aliases, and do not\n"
        f"alter the legacy metrics. No late-ROM denominator is established;\n"
        f"neither summary certifies exhaustive whole-game coverage.",
    ]
    if problems:
        lines += ["", "```", "needs attention:"] + [f"  {p}" for p in problems] + ["```"]
    lines += ["", END]
    return "\n".join(lines), pf, pb


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=os.environ.get("FFTA_ROOT"))
    ap.add_argument("--verify", action="store_true",
                    help="recompile every src/*.c instead of trusting the reports")
    ap.add_argument("--jobs", type=int, choices=range(1, 65), default=1, metavar="N",
                    help="verify up to N sources concurrently (1..64; default: 1)")
    ap.add_argument("--worker-processes", type=int, choices=range(1, 65), metavar="N",
                    help="recompile or replay reports in N forked processes; requires --jobs 1")
    ap.add_argument("--write", action="store_true",
                    help="update status files; with --verify, regenerate match reports too")
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--badges", metavar="DIR",
                    help="write shields.io endpoint JSON (functions/bytes) here")
    ap.add_argument("--label-prefix", default="",
                    help="prefix each badge label, e.g. USA")
    ap.add_argument("--badge-base", default="",
                    help="raw base URL of the badges branch, e.g. "
                         "https://raw.githubusercontent.com/owner/repo/badges ; "
                         "enables self-updating endpoint badges (public repo only)")
    ap.add_argument("--static-badges", action="store_true",
                    help="always use static badge URLs, even with --badge-base")
    args = ap.parse_args()

    root = repo_root(args.root)
    process_options = {"worker_processes": args.worker_processes} if args.worker_processes else {}
    progress = {}
    tf, mf, tb, mb, problems, late_f, late_b = collect(
        root, args.verify, write_reports=args.verify and args.write and not args.check,
        jobs=args.jobs, progress=progress, **process_options)
    badge_base = None if args.static_badges else (
        args.badge_base or os.environ.get("FFTA_BADGE_BASE")
        or badge_base_from_remote(root))
    block, pf, pb = render(tf, mf, tb, mb, problems, args.label_prefix, badge_base,
                           late_f=late_f, late_b=late_b, progress=progress or None)

    if args.badges:
        out = os.path.abspath(args.badges)
        os.makedirs(out, exist_ok=True)
        for name, pct in (("functions", pf), ("bytes", pb)):
            lbl = f"{args.label_prefix} {name}" if args.label_prefix else name
            data = badge(lbl, pct * 100)
            with open(os.path.join(out, f"{name}.json"), "w",
                      encoding="utf-8", newline="\n") as f:
                json.dump(data, f)
                f.write("\n")
            print(f"{name:<10} {data['message']:>8}  ({data['color']})")
        print(f"wrote {os.path.relpath(out, root) if out.startswith(root) else out}")

    readme = os.path.join(root, "README.md")
    current = open(readme, encoding="utf-8").read() if os.path.exists(readme) else ""

    if args.check:
        if problems:
            print(f"{len(problems)} item(s) need attention:", file=sys.stderr)
            for problem in problems:
                print(f"  {problem}", file=sys.stderr)
        if START not in current or END not in current:
            sys.exit("README has no status markers")
        old = current[current.index(START):current.index(END) + len(END)]
        if old.strip() != block.strip():
            print(f"Verified status: {mf}/{tf} functions; {mb}/{tb} indexed bytes; "
                  f"{late_f} late functions, {late_b} late bytes", file=sys.stderr)
            sys.exit("README status is stale - run: python tools/status.py --write")
        status_path = os.path.join(root, "docs", "status.md")
        if os.path.exists(status_path):
            if open(status_path, encoding="utf-8").read().strip() != block.strip():
                sys.exit("docs/status.md is stale - run: python tools/status.py --write")
        print("README status is up to date")
        return 1 if problems else 0

    if args.write:
        if START not in current:
            sys.exit(f"{readme} has no {START} / {END} markers")
        new = re.sub(re.escape(START) + r".*?" + re.escape(END), block,
                     current, flags=re.S)
        # also keep the block standalone, so CI can check the README against it
        # without needing this tool
        status_path = os.path.join(root, "docs", "status.md")
        os.makedirs(os.path.dirname(status_path), exist_ok=True)
        with open(status_path, "w", encoding="utf-8", newline="\n") as f:
            f.write(block + "\n")
        if new != current:
            with open(readme, "w", encoding="utf-8", newline="\n") as f:
                f.write(new)
            print(f"updated {os.path.relpath(readme, root)}")
        else:
            print("README status already up to date")
        print(f"wrote {os.path.relpath(status_path, root)}")
    else:
        print(block)

    if problems:
        print(f"\n{len(problems)} item(s) need attention:", file=sys.stderr)
        for p in problems:
            print(f"  {p}", file=sys.stderr)
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
