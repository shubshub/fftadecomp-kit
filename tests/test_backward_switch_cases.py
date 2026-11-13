"""Synthetic Thumb checks for default-path switch cases that precede the dispatch.

No game bytes or compiler are used. The function is a shared `adds`/`b` block
placed before the guard and the table, reached by case 0 through the table.
"""

import copy
import hashlib
import json
from pathlib import Path
import struct
import sys
import tempfile
import unittest
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import match
import match_evidence as evidence

BASE = 0x08000000
CALLEE = 0x08001000
TASK = Path(__file__).resolve().parents[1]


def fixture(pool_before=False, framed=False, bl=False):
    body = bytearray()
    labels, fixups = {}, []

    def half(value):
        body.extend(struct.pack("<H", value))

    def label(name):
        labels[name] = len(body)

    def instruction(kind, name, register=0):
        fixups.append((len(body), kind, name, register))
        half(0)

    def word(name):
        fixups.append((len(body), "word", name, 0))
        body.extend(bytes(4))

    if framed:
        label("entry")
        half(0xB510)  # push {r4, lr}
    label("start")
    half(0x2200)  # movs r2, #0
    if bl:
        label("bl")
        half(0xF000)  # bl func_08001000: prefix, offset 0x7FC halfwords
        label("bl2")
        half(0xFFFC)  # bl suffix; a case here lands inside the instruction
    if pool_before:
        instruction("ldr", "early", 3)
    instruction("b", "comparison")
    label("shared")
    half(0x3202)  # adds r2, #2
    instruction("b", "done")
    if pool_before:
        while len(body) % 4:
            half(0)
        label("early")
        body.extend(struct.pack("<I", 0x12345678))
    label("comparison")
    half(0x2801)  # cmp r0, #1
    label("guard")
    instruction("bhi", "default")
    label("dispatch")
    half(0x0080)  # lsls r0, r0, #2
    instruction("ldr", "pointer", 1)
    half(0x1840)  # adds r0, r0, r1
    half(0x6800)  # ldr r0, [r0]
    half(0x4687)  # mov pc, r0
    while len(body) % 4:
        half(0)
    label("pointer")
    word("table")
    label("table")
    word("case0")
    word("case1")
    label("case0")
    half(0x1C10)  # adds r0, r2, #0  (placeholder body, falls to shared via b)
    instruction("b", "shared")
    label("case1")
    half(0x2007)  # movs r0, #7
    instruction("b", "done")
    label("default")
    half(0x2000)  # movs r0, #0
    label("done")
    if framed:
        half(0xBC10)  # pop {r4}
        half(0xBC02)  # pop {r1}
        half(0x4708)  # bx r1
    else:
        half(0x4770)  # bx lr

    for offset, kind, name, register in fixups:
        target = labels[name]
        if kind == "word":
            struct.pack_into("<I", body, offset, BASE + target)
        elif kind == "ldr":
            distance = target - ((offset + 4) & ~3)
            assert 0 <= distance <= 1020 and distance % 4 == 0
            struct.pack_into("<H", body, offset, 0x4800 | register << 8 | distance // 4)
        else:
            displacement = (target - offset - 4) // 2
            value = (0xD800 | displacement & 0xFF) if kind == "bhi" else (
                0xE000 | displacement & 0x7FF)
            struct.pack_into("<H", body, offset, value)
    return body, labels


def manifest_for(body, labels, targets):
    """Manifest for a table whose two cases are the named label offsets."""
    relocations = {labels["pointer"]: labels["table"],
                   labels["table"]: targets[0], labels["table"] + 4: targets[1]}
    descriptor = {name: labels[name] for name in (
        "comparison", "guard", "dispatch", "default", "table")}
    descriptor.update(literal=labels["pointer"], bound=1,
                      relocations=[list(item) for item in relocations.items()])
    mapping = [{"rom": f"0x{BASE:08X}", "end": f"0x{BASE + len(body):08X}", "mode": "thumb"}]
    calls = []
    if "bl" in labels:
        mapping.append({"rom": f"0x{CALLEE:08X}", "end": f"0x{CALLEE + 2:08X}", "mode": "thumb"})
        calls = [[labels["bl"], f"func_{CALLEE:08X}"]]
    return {"calls": calls, "switch": descriptor}, mapping


def with_table(body, labels, targets):
    changed = bytearray(body)
    for slot, target in zip((labels["table"], labels["table"] + 4), targets):
        struct.pack_into("<I", changed, slot, BASE + target)
    return changed


HIGH = 0x08001000  # the CFG inventory refuses entries inside the ROM header


def rebased(body, labels, targets, base=HIGH):
    """The fixture with its pointer and table words linked for an entry at `base`."""
    changed = bytearray(body)
    struct.pack_into("<I", changed, labels["pointer"], base + labels["table"])
    for slot, target in zip((labels["table"], labels["table"] + 4), targets):
        struct.pack_into("<I", changed, slot, base + target)
    return bytes(changed)


def inventory(body, base=HIGH):
    import analyze
    mapping = [{"rom": f"0x{base:08X}", "end": f"0x{base + len(body):08X}", "mode": "thumb",
                "instrs": 0}]
    return lambda **options: analyze.refine_function(body, base, mapping,
                                                     rom_end=base + 0x1000, **options)


def verify(body, manifest, mapping, rom=None):
    rom = bytes(body) if rom is None else bytes(rom)
    if len(mapping) > 1:  # a callee follows the caller in the ROM image
        rom += bytes(CALLEE - BASE + 2 - len(rom))
    return match.verify_switches(bytes(body), BASE, rom,
                                 json.dumps(mapping).encode(), manifest)


class BackwardCaseTests(unittest.TestCase):
    def good(self, **options):
        body, labels = fixture(**options)
        manifest, mapping = manifest_for(body, labels, (labels["shared"], labels["case1"]))
        body = with_table(body, labels, (labels["shared"], labels["case1"]))
        return body, labels, manifest, mapping

    def test_backward_case_is_admitted_and_walked(self):
        body, labels, manifest, mapping = self.good()
        instructions, summary = verify(body, manifest, mapping)
        self.assertEqual(summary, "closed leaf CFG")
        self.assertLess(labels["shared"], labels["comparison"])
        self.assertIn(BASE + labels["shared"], {item.address for item in instructions})
        self.assertEqual(match.switch_layout(bytes(body), BASE, dict(manifest["switch"]["relocations"]),
                                             allow_backward_cases=True),
                         manifest["switch"])

    def test_interleaved_pool_before_guard_is_admitted(self):
        body, labels, manifest, mapping = self.good(pool_before=True)
        verify(body, manifest, mapping)

    def test_default_keeps_the_old_rule(self):
        body, labels, manifest, _ = self.good()
        words = dict(manifest["switch"]["relocations"])
        with self.assertRaisesRegex(ValueError, "forward local cases"):
            match.switch_layout(bytes(body), BASE, words)

    def refuse(self, target, pattern, patch_table=True):
        body, labels, manifest, mapping = self.good()
        targets = (target(labels) if callable(target) else target, labels["case1"])
        manifest, mapping = manifest_for(body, labels, targets)
        if patch_table:
            body = with_table(body, labels, targets)
        with self.assertRaisesRegex(ValueError, pattern):
            verify(body, manifest, mapping)

    def test_target_inside_table_pointer_dispatch_or_guard(self):
        for name, offset in (("table", 0), ("table", 4), ("pointer", 0),
                             ("dispatch", 0), ("dispatch", 2), ("dispatch", 8),
                             ("guard", 0), ("comparison", 0)):
            with self.subTest(name=name, offset=offset):
                self.refuse(lambda labels: labels[name] + offset,
                            "one exact adjacent unsigned guard")

    def test_target_outside_function(self):
        self.refuse(lambda labels: len(fixture()[0]), "invalid local switch word")
        self.refuse(lambda labels: len(fixture()[0]) + 0x100, "invalid local switch word")

    def test_misaligned_target(self):
        self.refuse(lambda labels: labels["shared"] + 1, "invalid local switch word",
                    patch_table=False)

    def test_tampered_table_word(self):
        body, labels, manifest, mapping = self.good()
        struct.pack_into("<I", body, labels["table"], BASE + labels["shared"] + 2)
        with self.assertRaisesRegex(ValueError, "invalid local switch word"):
            verify(body, manifest, mapping)

    def test_table_word_disagreeing_with_manifest(self):
        body, labels, manifest, mapping = self.good()
        manifest = copy.deepcopy(manifest)
        manifest["switch"]["relocations"][1][1] = labels["case1"]
        with self.assertRaisesRegex(ValueError, "invalid local switch word"):
            verify(body, manifest, mapping)

    def test_target_in_pool_word(self):
        body, labels = fixture(pool_before=True)
        targets = (labels["early"], labels["case1"])
        manifest, mapping = manifest_for(body, labels, targets)
        body = with_table(body, labels, targets)
        with self.assertRaisesRegex(ValueError, "overlaps|literal|middle"):
            verify(body, manifest, mapping)

    def test_descriptor_tampering(self):
        body, labels, manifest, mapping = self.good()
        for field, value in (("default", labels["done"]), ("dispatch", labels["dispatch"] + 2),
                             ("comparison", labels["comparison"] - 2), ("bound", 2),
                             ("table", labels["table"] + 4)):
            changed = copy.deepcopy(manifest)
            changed["switch"][field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                verify(body, changed, mapping)

    def test_rom_and_span_must_match(self):
        body, labels, manifest, mapping = self.good()
        rom = bytearray(body)
        rom[0] ^= 1
        with self.assertRaisesRegex(ValueError, "differs from the ROM"):
            verify(body, manifest, mapping, rom=rom)
        mapping[0]["end"] = f"0x{BASE + len(body) - 2:08X}"
        with self.assertRaisesRegex(ValueError, "exact mapped Thumb span"):
            verify(body, manifest, mapping)


class FramedAndBranchTests(unittest.TestCase):
    """The same checks with a push/pop frame and a BL pair, and a guard bypass."""

    def build(self, target, **options):
        body, labels = fixture(**options)
        targets = (labels[target] if isinstance(target, str) else target, labels["case1"])
        manifest, mapping = manifest_for(body, labels, targets)
        return with_table(body, labels, targets), manifest, mapping

    def test_loop_to_the_first_body_instruction_is_admitted(self):
        body, manifest, mapping = self.build("start", framed=True)
        instructions, summary = verify(body, manifest, mapping)
        self.assertEqual(summary, "closed leaf CFG")
        self.assertIn(BASE + 2, {item.address for item in instructions})

    def test_backward_case_into_the_prologue_push_is_refused(self):
        body, manifest, mapping = self.build("entry", framed=True)
        with self.assertRaisesRegex(ValueError, "inconsistent saved stack depth"):
            verify(body, manifest, mapping)

    def test_frameless_case_at_the_function_entry_is_a_loop(self):
        body, manifest, mapping = self.build(0)
        verify(body, manifest, mapping)

    def test_case_in_the_second_half_of_a_bl_pair_is_refused(self):
        body, manifest, mapping = self.build("start", framed=True, bl=True)
        verify(body, manifest, mapping)  # the BL itself verifies with its call binding
        body, manifest, mapping = self.build("bl2", framed=True, bl=True)
        with self.assertRaisesRegex(ValueError, "invalid or truncated reachable instruction"):
            verify(body, manifest, mapping)

    def test_case_block_branching_past_the_guard_is_refused(self):
        body, labels = fixture()
        targets = (labels["shared"], labels["case1"])
        manifest, mapping = manifest_for(body, labels, targets)
        body = with_table(body, labels, targets)
        site = labels["shared"] + 2  # the block's `b done`, retargeted at the dispatch
        struct.pack_into("<H", body, site, 0xE000 | ((labels["dispatch"] - site - 4) // 2) & 0x7FF)
        with self.assertRaisesRegex(ValueError, "selector bound is bypassed"):
            verify(body, manifest, mapping)


def switch_layout_calls(case, operation):
    """Run `operation` with match.switch_layout wrapped; return its error.

    Fails unless the layout was reached and no call opted in to backward cases."""
    error = None
    with mock.patch.object(match, "switch_layout", wraps=match.switch_layout) as spy:
        try:
            operation()
        except ValueError as caught:
            error = caught
    case.assertTrue(spy.call_args_list, "the profile never reached switch_layout")
    for call in spy.call_args_list:
        case.assertIsNot(call.kwargs.get("allow_backward_cases"), True)
    return error


class PinnedProfileTests(unittest.TestCase):
    """Default consumers retain the forward rule; explicit multi-switch qualification is separate."""

    def setUp(self):
        body, labels = fixture()
        targets = (labels["shared"], labels["case1"])
        self.words = {labels["pointer"]: labels["table"], labels["table"]: targets[0],
                      labels["table"] + 4: targets[1]}
        self.body = bytes(with_table(body, labels, targets))
        self.labels = labels

    def refused(self, operation):
        error = switch_layout_calls(self, operation)
        self.assertRegex(str(error), "forward local cases")

    def test_layout_refuses_by_default_and_admits_on_opt_in(self):
        match.switch_layout(self.body, BASE, self.words, allow_backward_cases=True)
        self.refused(lambda: match.switch_layout(self.body, BASE, self.words))

    def test_thunk_pool_layout(self):
        import thunk_pool_switch
        self.refused(lambda: thunk_pool_switch.layout(self.body, BASE, self.words, interposed_words=5))

    def test_software_double_record(self):
        import software_double_profile
        self.refused(lambda: software_double_profile.switch_record(self.body, BASE, self.words))

    def test_multiple_switch_partition(self):
        import multiple_switch_owner_prerequisite as multiple
        words = dict(self.words)
        words.update({max(words) + 4 * (1 + index): 0 for index in range(2)})
        error = switch_layout_calls(self, lambda: multiple.layout(self.body, BASE, words))
        self.assertRegex(str(error), "no unique complete guarded-table partition")

    def test_refinement_word_switch_leaves_an_unresolved_jump(self):
        body, labels = fixture()
        backward = rebased(body, labels, (labels["shared"], labels["case1"]))
        for options in ({}, {"one_object_word_switch": True}, {"one_numeric_word_switch": True}):
            with self.subTest(options=options):
                refinement = []
                error = switch_layout_calls(
                    self, lambda: refinement.append(inventory(backward)(**options)))
                self.assertIsNone(error)
                self.assertFalse(refinement[0]["cfg_closed"])
                self.assertEqual(refinement[0]["word_switches"], [])
                self.assertTrue(any(reason.startswith("unresolved jump")
                                    for reason in refinement[0]["partial_reasons"]))

    def test_refinement_word_switch_still_resolves_the_forward_table(self):
        body, labels = fixture()
        forward = rebased(body, labels, (labels["case0"], labels["case1"]))
        refinement = inventory(forward)()
        self.assertTrue(refinement["cfg_closed"])
        self.assertEqual(len(refinement["word_switches"]), 1)

    def test_owner_graph_replay(self):
        import owner_graph_profile
        body, labels = fixture()
        forward = rebased(body, labels, (labels["case0"], labels["case1"]))
        refinement = inventory(forward)()
        self.assertTrue(refinement["cfg_closed"])
        backward = rebased(body, labels, (labels["shared"], labels["case1"]))
        refinement = copy.deepcopy(refinement)
        for record in refinement["word_switches"][0]["relocations"]:
            if record[0] == labels["table"]:
                record[1] = labels["shared"]
        self.refused(lambda: owner_graph_profile.graph(backward, HIGH, refinement))

    def test_leaf_verifier_refuses_backward_cases_by_default(self):
        self.refused(lambda: match.verify_leaf_instructions(
            self.body, BASE, True, switch_relocations=self.words))
        match.verify_leaf_instructions(self.body, BASE, True, switch_relocations=self.words,
                                       backward_switch_cases=True)

    NAMES = ("switch_layout", "verify_leaf_instructions")
    OPT_IN = ("allow_backward_cases", "backward_switch_cases")

    @classmethod
    def references(cls):
        """Yield (file, function, kind, node) for every mention of the guarded names.

        kind is "call" for a direct call, "import" for a plain import alias, and
        "other" for anything else: assignments, arguments, aliases, getattr or
        partial strings and attribute reads."""
        import ast
        found = []

        def visit(node, parent, function, path):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                function = node.name
            name = None
            if isinstance(node, ast.Name) and node.id in cls.NAMES:
                name = node.id
            elif isinstance(node, ast.Attribute) and node.attr in cls.NAMES:
                name = node.attr
            elif isinstance(node, ast.Constant) and node.value in cls.NAMES:
                name = node.value
            elif isinstance(node, ast.alias) and node.name.split(".")[-1] in cls.NAMES:
                name = node.name
            if name is not None:
                if isinstance(node, ast.alias):
                    kind = "import" if node.asname is None else "other"
                elif isinstance(parent, ast.Call) and parent.func is node:
                    kind = "call"
                elif isinstance(parent, ast.Attribute) and isinstance(node, ast.Name):
                    kind = None  # the module in `match.switch_layout`, counted on the Attribute
                else:
                    kind = "other"
                if kind is not None:
                    found.append((path.name, function, kind, name, parent))
            for child in ast.iter_child_nodes(node):
                visit(child, node, function, path)

        for path in sorted((TASK / "tools").glob("*.py")):
            visit(ast.parse(path.read_text()), None, None, path)
        return found

    def test_no_stray_reference_to_the_guarded_names(self):
        # `layout = switch_layout`, arguments, `as` aliases, getattr and partial all
        # hide a call from a call-only audit; each one must be listed here.
        allowed_other = {("match.py", "verify_leaf_instructions", "switch_layout"): 1}
        counts = {}
        for file, function, kind, name, _ in self.references():
            if kind == "other":
                key = (file, function, name)
                counts[key] = counts.get(key, 0) + 1
        self.assertEqual(counts, allowed_other)

    def test_opt_in_appears_only_at_the_allowed_sites(self):
        import ast
        found = []

        def visit(node, function, path):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                function = node.name
            for keyword in getattr(node, "keywords", ()):
                if keyword.arg in self.OPT_IN:
                    found.append((path.name, function, keyword.arg, ast.unparse(keyword.value)))
            for child in ast.iter_child_nodes(node):
                visit(child, function, path)

        for path in sorted((TASK / "tools").glob("*.py")):
            visit(ast.parse(path.read_text()), None, path)
        # the last site is the switch-data scalar replay in match.main
        self.assertEqual(sorted(found), sorted([
            ("match.py", "selected_switch_layout", "allow_backward_cases", "True"),
            ("match.py", "verify_leaf_instructions", "allow_backward_cases", "backward_switch_cases"),
            ("match.py", "verify_switches", "allow_backward_cases", "True"),
            ("match.py", "verify_switches", "backward_switch_cases", "True"),
            ("match.py", "main", "backward_switch_cases", "True"),
            ("analyze.py", "refinement_word_switch", "allow_backward_cases", "backward"),
            ("multiple_switch_owner_prerequisite.py", "layout", "allow_backward_cases", "backward"),
            ("owner_graph_profile.py", "graph", "allow_backward_cases", "backward")]))

    def test_exact_opt_in_calls_in_the_two_verifiers(self):
        counts = {}
        for file, function, kind, name, parent in self.references():
            if name == "switch_layout" and file == "match.py" and kind == "call" and \
                    function in ("selected_switch_layout", "verify_switches"):
                opted = any(keyword.arg == "allow_backward_cases" for keyword in parent.keywords)
                counts[(function, opted)] = counts.get((function, opted), 0) + 1
        self.assertEqual(counts, {("selected_switch_layout", True): 1, ("verify_switches", True): 1})
        # Other than the three isolated qualified multi-switch calls, defaults stay forward-only.
        for file, function, kind, name, parent in self.references():
            if name == "switch_layout" and kind == "call" and \
                    (file, function) not in (("match.py", "selected_switch_layout"),
                                             ("match.py", "verify_switches"),
                                             ("analyze.py", "refinement_word_switch"),
                                             ("multiple_switch_owner_prerequisite.py", "layout"),
                                             ("owner_graph_profile.py", "graph")):
                with self.subTest(file=file, function=function, line=parent.lineno):
                    self.assertFalse(any(keyword.arg in self.OPT_IN for keyword in parent.keywords))


class ReportTests(unittest.TestCase):
    def setUp(self):
        body, labels = fixture()
        targets = (labels["shared"], labels["case1"])
        self.manifest, mapping = manifest_for(body, labels, targets)
        self.body = with_table(body, labels, targets)
        self.labels = labels
        self.source = hashlib.sha256(b"synthetic source/header identity").hexdigest()
        self.functions = json.dumps(mapping).encode()
        scratch = TASK / "build"
        scratch.mkdir(exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="backward_switch_", dir=scratch)
        self.addCleanup(directory.cleanup)
        self.rom_path = Path(directory.name) / "synthetic-report-image.bin"
        self.rom_path.write_bytes(self.body)
        for name, value in (("mapping_snapshot", self.functions),
                            ("source_fingerprint", self.source),
                            ("report_rom_path", str(self.rom_path))):
            patcher = mock.patch.object(evidence, name, return_value=value)
            patcher.start()
            self.addCleanup(patcher.stop)

    def report(self, body=None, manifest=None):
        body = self.body if body is None else body
        manifest = self.manifest if manifest is None else manifest
        return "\n".join([
            f"* verification: `{evidence.SWITCH_SCHEMA}`",
            f"* source SHA-256: `{self.source}`",
            f"* mapping SHA-256: `{evidence.mapping_fingerprint(self.functions)}`",
            f"* switches: {evidence.SWITCH_SUMMARY}",
            "* source plausibility: plausible", "* relocations: none",
            "* verified extent: complete ELF function symbol, including literal pools",
            f"* compiled : `{bytes(body).hex()}`",
            f"* switch manifest: `{evidence.switch_manifest(manifest)}`",
            "* control flow: closed leaf CFG",
            f"* ROM bytes: `{bytes(body).hex()}` ({len(body)} bytes)",
            f"**MATCH - byte identical** - {len(body)}/{len(body)} bytes",
            f"* switch proof SHA-256: `{evidence.switch_fingerprint(BASE, bytes(body), manifest)}`",
        ])

    def accepted(self, report):
        return evidence.switch_report_matches(report.splitlines(), TASK, BASE)

    def test_backward_report_revalidates(self):
        self.assertTrue(self.accepted(self.report()))

    def test_tampered_reports_are_rejected(self):
        # Table word moved into the table, with a recomputed manifest and digest.
        for target in (self.labels["table"], self.labels["dispatch"] + 2,
                       self.labels["comparison"], len(self.body), self.labels["shared"] + 1):
            body = with_table(self.body, self.labels, (target, self.labels["case1"]))
            manifest = copy.deepcopy(self.manifest)
            manifest["switch"]["relocations"][1][1] = target
            self.rom_path.write_bytes(body)
            with self.subTest(target=target):
                self.assertFalse(self.accepted(self.report(body, manifest)))
        self.rom_path.write_bytes(self.body)

    def test_stale_digest_manifest_and_bytes_are_rejected(self):
        report = self.report()
        digest = evidence.switch_fingerprint(BASE, bytes(self.body), self.manifest)
        self.assertFalse(self.accepted(report.replace(digest, "0" * 64)))
        changed = bytearray(self.body)
        struct.pack_into("<I", changed, self.labels["table"], BASE + self.labels["shared"] + 2)
        self.assertFalse(self.accepted(self.report(changed)))
        manifest = copy.deepcopy(self.manifest)
        manifest["switch"]["relocations"][1][1] = self.labels["case1"]
        self.assertFalse(self.accepted(self.report(manifest=manifest)))


if __name__ == "__main__":
    unittest.main()
