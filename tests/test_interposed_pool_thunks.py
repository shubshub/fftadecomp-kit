"""Synthetic boundaries of canonical-thunks-interposed-pool-v1; never invokes a compiler or GAME proof.

The selector finds the table pointer by the dispatch's own PC-relative load, so
any number of words may sit between the dispatch and the pointer.  Each must be
a reached complete literal word, bound by the canonical-thunk literal rules.
"""
import copy
from contextlib import redirect_stdout
from contextlib import contextmanager, ExitStack
import io
import json
import os
from pathlib import Path
import struct
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

CASE = Path(__file__).resolve().parents[1]
sys.dont_write_bytecode = True
sys.path.insert(0, str(CASE / "tools"))
import match
import function_thunk_profile as profile
import thunk_pool_switch as pool
import match_evidence as evidence
import rebuild
import status

SELECTOR = profile.INTERPOSED_SELECTOR
WORDS = pool.INTERPOSED
A = 0x08000000
NAME = "func_08000000"
OBJECT = 0x02001000


def bl(site, target):
    offset = target - site - 4
    return struct.pack("<HH", 0xF000 | ((offset >> 12) & 0x7FF), 0xF800 | ((offset >> 1) & 0x7FF))


def fixture(*, interposed=2, guard="bls", object_word=None, unread=None, values=None, align=None):
    """A complete R3-thunk caller whose switch pool holds `interposed` words.

    object_word puts the typed object in that pool slot; unread leaves that
    slot without its PC-relative load; values overrides the numeric pool words;
    align forces the dispatch to the given word alignment by a leading NOP.
    """
    data = bytearray()
    labels, branches, loads = {}, [], []
    def word(value): data.extend(struct.pack("<H", value))
    def label(name): labels[name] = len(data)
    def branch(opcode, name): branches.append((len(data), opcode, name)); word(0)
    def load(register, name): loads.append((len(data), register, name)); word(0)
    word(0xB500)
    for n in range(interposed):
        if n != unread:
            load(n % 3, "pool" + str(n))
    word(0x6813)  # LDR r3,[r2]: the thunk target stays an arbitrary conditional call.
    call = len(data); data.extend(bl(A + call, profile.ALIASES["_call_via_r3"]))
    if align is not None and (len(data) + (6 if guard == "bls" else 4) + 10) % 4 != align:
        word(0x46C0)
    label("comparison"); word(0x2801)
    if guard == "bls":
        branch(0xD900, "dispatch"); branch(0xE000, "default")
    else:
        branch(0xD800, "default")
    label("dispatch"); word(0x0080); load(1, "literal"); word(0x1840); word(0x6800); word(0x4687)
    if len(data) % 4:
        label("alignment"); word(0)
    for n in range(interposed):
        label("pool" + str(n))
        value = OBJECT if n == object_word else (values[n] if values else 0x11111111 + n)
        data.extend(struct.pack("<I", value))
    label("literal"); data.extend(b"\0" * 4)
    label("table"); data.extend(b"\0" * 8)
    label("case0"); word(0x2001); branch(0xE000, "default")
    label("case1"); word(0x2002); branch(0xE000, "default")
    label("default"); word(0xBC02); word(0x4708)
    for site, opcode, name in branches:
        shift = (labels[name] - site - 4) // 2
        struct.pack_into("<H", data, site, opcode | (shift & (0xFF if opcode & 0xF000 == 0xD000 else 0x7FF)))
    for site, register, name in loads:
        delta = labels[name] - ((site + 4) & ~3)
        assert delta >= 0 and delta % 4 == 0
        struct.pack_into("<H", data, site, 0x4800 | register << 8 | delta // 4)
    relocations = {labels["literal"]: labels["table"], labels["table"]: labels["case0"],
                   labels["table"] + 4: labels["case1"]}
    for site, target in relocations.items():
        struct.pack_into("<I", data, site, A + target)
    rom = bytearray(profile.END - A)
    rom[:len(data)] = data
    for register in range(13):
        struct.pack_into("<HH", rom, profile.ALIASES[f"_call_via_r{register}"] - A, 0x4700 | register << 3, 0x46C0)
    has_object = object_word is not None
    objects = f'{{"g_synthetic":"0x{OBJECT:08X}"}}'.encode() if has_object else None
    literals = {labels["pool" + str(object_word)]: ("g_synthetic", OBJECT)} if has_object else {}
    mapping = json.dumps([dict(rom=f"0x{A:08X}", end=f"0x{A + len(data):08X}", mode="thumb")]).encode()
    return dict(data=bytes(data), rom=bytes(rom), labels=labels, switches=relocations,
                calls={A + call: profile.ALIASES["_call_via_r3"]}, objects=objects, literals=literals,
                mapping=mapping, index=f"{A:08X} {A + len(data):08X} {len(data)}\n".encode())


def patched(f, offset, value, size=2):
    damaged = copy.deepcopy(f)
    body = bytearray(f["data"])
    struct.pack_into("<H" if size == 2 else "<I", body, offset, value)
    damaged["data"] = bytes(body)
    return damaged


def leaf(f, *, words=WORDS):
    context = {"pool_switch": f["switches"]}
    if words != 5:
        context["interposed_words"] = words
    return match.verify_leaf_instructions(f["data"], A, True, f["calls"], function_thunk_context=context)


def discovered(f, *, words=WORDS):
    context = {} if words == 5 else {"interposed_words": words}
    return match.verify_leaf_instructions(f["data"], A, True, f["calls"], function_thunk_context=context)


def manifest_for(f):
    return profile.make_manifest(f["calls"], {}, f["literals"], A, f["rom"], f["objects"],
                                 discovered(f), selector=SELECTOR)


def images(f):
    """Synthetic ET_REL/ET_EXEC boundaries with genuine Thumb relocation words."""
    def symbol(name, kind, section, bind, value=0, size=0):
        return dict(name=name, type=kind, section=section, bind=bind, value=value, size=size)
    symbols = [symbol("", 0, 0, 0), symbol("", 3, 1, 0), symbol(NAME, 2, 1, 1, 1, len(f["data"])),
               symbol("_call_via_r3", 2, 0, 1)]
    original = bytearray(f["data"]); relocations = []
    for site in f["calls"]:
        offset = site - A; original[offset:offset + 4] = bl(site, site); relocations.append((offset, 3 << 8 | 10))
    for offset, addend in f["switches"].items():
        struct.pack_into("<I", original, offset, addend); relocations.append((offset, 1 << 8 | 2))
    if f["literals"]:
        symbols.append(symbol("g_synthetic", 1, 0, 1))
        for offset in f["literals"]:
            struct.pack_into("<I", original, offset, 0); relocations.append((offset, 4 << 8 | 2))
    encoded = b"".join(struct.pack("<II", *record) for record in relocations)
    sections = [(0, 0, 0, 0, 0, 0, 0, 0, 0, 0), (0, 1, 6, 0, 0, len(original), 0, 0, 4, 0),
                (0, 2, 0, 0, 0, 0, 0, 0, 4, 16), (0, 9, 0, 0, 0, len(encoded), 2, 1, 4, 8)]
    before = dict(type=1, text=bytes(original), text_index=1, symbols=symbols, sections=sections,
                  relocations=[3], symbol_tables={2: symbols}, section_data={3: encoded})
    after = copy.deepcopy(before); after.update(type=2, text=f["data"], relocations=[])
    after["sections"][1] = (0, 1, 6, A, 0, len(original), 0, 0, 4, 0)
    after["symbols"][1]["value"] = A; after["symbols"][2]["value"] = A | 1
    after["symbols"][3].update(section=0xFFF1, value=profile.ALIASES["_call_via_r3"] | 1)
    if f["literals"]:
        after["symbols"][4].update(section=0xFFF1, value=OBJECT)
    return before, after


@contextmanager
def synthetic_environment(**kwargs):
    """Only compiler/ELF/plausibility/subprocess boundaries are mocked."""
    f = fixture(object_word=0, **kwargs); before, after = images(f)
    scratch = CASE / "scratch"; scratch.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="synthetic_", dir=scratch) as directory:
        root = Path(directory)
        for child in ("src", "include", "config", "symbols", "docs/match", "build"):
            (root / child).mkdir(parents=True, exist_ok=True)
        (root / "src/08000000.c").write_text("unsigned func_08000000(void *record) { return *(unsigned *)record; }\n")
        (root / "config/functions.json").write_bytes(f["mapping"])
        (root / "config/data_symbols.json").write_bytes(f["objects"])
        (root / "symbols/functions.txt").write_bytes(f["index"])
        (root / "synthetic.rom").write_bytes(f["rom"])
        commands = []; compiled = []
        class FakeRunner:
            def __init__(self, *args, **kwargs): pass
            @contextmanager
            def workspace(self):
                with tempfile.TemporaryDirectory(prefix="mock_link_", dir=scratch) as work: yield work
            def read_binary(self, path):
                if str(path).endswith("f.elf"): return b"SYNTHETIC_LINKED_ELF_BOUNDARY"
                if str(path).endswith("f.linked.bin"): return f["data"]
                return Path(path).read_bytes()
            def write_text(self, path, value): Path(path).write_text(value)
            def sh(self, command): commands.append(command)
        def compile_boundary(runner, workspace, args, source_root, address, relative, thumb=True):
            assert address == A and thumb and args.flags == match.DEFAULT_FLAGS
            compiled.append(str(source_root))
            (Path(workspace) / "f.i").write_bytes((Path(source_root) / relative).read_bytes())
            return b"SYNTHETIC_ORIGINAL_ELF_BOUNDARY", before["text"], copy.deepcopy(before)
        def elf_boundary(raw):
            if raw != b"SYNTHETIC_LINKED_ELF_BOUNDARY": raise AssertionError("unexpected original or linked ELF")
            return copy.deepcopy(after)
        def plausible_boundary(command, *args):
            assert "--json" in command
            return SimpleNamespace(returncode=0, stdout=json.dumps(dict(findings=[], total=0, addr="0x08000000",
                                   hand_asm_allowed=False, allow_entry=None)), stderr="")
        exists = os.path.exists
        with ExitStack() as stack:
            stack.enter_context(patch.dict(os.environ, {"FFTA_ROM": str(root / "synthetic.rom"), "TMPDIR": str(scratch),
                                                        "TEMP": str(scratch), "TMP": str(scratch)}))
            stack.enter_context(patch.object(match, "Runner", FakeRunner))
            stack.enter_context(patch.object(match, "compile_object", compile_boundary))
            stack.enter_context(patch.object(match, "elf_image", elf_boundary))
            stack.enter_context(patch.object(match, "_run_replay_process", plausible_boundary))
            stack.enter_context(patch.object(os.path, "exists",
                                             lambda p: True if str(p) == str(CASE / "tools/plausible.py") else exists(p)))
            yield SimpleNamespace(root=root, f=f, commands=commands, compiled=compiled, before=before, after=after)


def run_match(env, selector):
    with patch.object(sys, "argv", ["match.py", "--root", str(env.root), "--function-address-profile", selector,
                                    "0x08000000"]), redirect_stdout(io.StringIO()) as output:
        try:
            code = match.main()
        except SystemExit as error:
            code = error.code
    return code, output.getvalue()


class InterposedPoolLayout(unittest.TestCase):
    def test_pools_of_one_to_seven_words_under_both_narrow_guards(self):
        for guard in ("bls", "bhi"):
            for interposed in (1, 2, 3, 5, 7):
                for align in (0, 2):
                    with self.subTest(guard=guard, interposed=interposed, align=align):
                        f = fixture(interposed=interposed, guard=guard, align=align)
                        instructions = leaf(f)
                        record = pool.record(f["data"], A, f["switches"], instructions, interposed_words=WORDS)
                        self.assertEqual(record["schema"], pool.INTERPOSED_SCHEMA)
                        self.assertEqual([entry[0] for entry in record["pool"]],
                                         [f["labels"]["pool" + str(n)] for n in range(interposed)])
                        self.assertEqual(record["layout"]["dispatch"] - record["layout"]["comparison"],
                                         6 if guard == "bls" else 4)
                        self.assertEqual(pool.discover(f["data"], A, list(instructions), interposed_words=WORDS),
                                         f["switches"])
                        self.assertTrue(discovered(f))

    def test_fixed_policies_keep_their_exact_pool_sizes(self):
        three = fixture(interposed=3)
        for words in (0, 5):
            with self.subTest(words=words), self.assertRaises(ValueError):
                leaf(three, words=words)
        with self.assertRaises(ValueError):
            match.verify_leaf_instructions(three["data"], A, True, three["calls"], switch_relocations=three["switches"])
        five = fixture(interposed=5)
        self.assertEqual(pool.record(five["data"], A, five["switches"], leaf(five, words=5))["schema"], pool.SCHEMA)
        bhi = fixture(interposed=5, guard="bhi")
        with self.assertRaises(ValueError):
            leaf(bhi, words=5)

    def test_zero_word_pool_stays_with_the_zero_selector(self):
        zero = fixture(interposed=0)
        with self.assertRaises(ValueError):
            leaf(zero)
        with self.assertRaises(ValueError):
            discovered(zero)
        self.assertTrue(leaf(zero, words=0))

    def test_unread_pool_word_is_refused(self):
        for interposed in (1, 3):
            for unread in range(interposed):
                with self.subTest(interposed=interposed, unread=unread), self.assertRaises(ValueError):
                    discovered(fixture(interposed=interposed, unread=unread))

    def test_table_pointer_must_be_the_dispatch_load(self):
        f = fixture(interposed=3)
        dispatch_load = f["labels"]["dispatch"] + 2
        for target in ("pool0", "pool2", "table"):
            delta = f["labels"][target] - ((dispatch_load + 4) & ~3)
            damaged = patched(f, dispatch_load, 0x4900 | delta // 4)
            with self.subTest(target=target), self.assertRaises(ValueError):
                discovered(damaged)
        for value in (A + f["labels"]["table"] + 4, A + f["labels"]["case0"], 0x11111111):
            damaged = patched(f, f["labels"]["literal"], value, size=4)
            with self.subTest(value=value), self.assertRaises(ValueError):
                discovered(damaged)
            with self.subTest(value=value), self.assertRaises(ValueError):
                leaf(damaged)

    def test_pool_words_that_are_code_are_refused(self):
        f = fixture(interposed=3)
        # A case entry into the pool.
        damaged = patched(f, f["labels"]["table"] + 4, A + f["labels"]["pool1"], size=4)
        damaged["switches"] = dict(f["switches"]); damaged["switches"][f["labels"]["table"] + 4] = f["labels"]["pool1"]
        with self.assertRaises(ValueError):
            leaf(damaged)
        with self.assertRaises(ValueError):
            discovered(damaged)
        # A reached branch into the pool.
        site = f["labels"]["case0"] + 2
        shift = (f["labels"]["pool0"] - site - 4) // 2
        with self.assertRaises(ValueError):
            discovered(patched(f, site, 0xE000 | (shift & 0x7FF)))
        # A nonzero alignment halfword.
        aligned = fixture(interposed=2, align=2)
        self.assertIn("alignment", aligned["labels"])
        with self.assertRaises(ValueError):
            discovered(patched(aligned, aligned["labels"]["alignment"], 0x46C0))

    def test_guard_must_be_exact_and_narrow(self):
        for guard in ("bls", "bhi"):
            f = fixture(interposed=2, guard=guard)
            branch = f["labels"]["comparison"] + 2
            condition = struct.unpack_from("<H", f["data"], branch)[0] & 0xFF
            # Wrong bound, wrong register, and a signed or carry condition.
            for offset, value in ((f["labels"]["comparison"], 0x2802), (f["labels"]["comparison"], 0x2901),
                                  (branch, 0xD300 | condition), (branch, 0xDC00 | condition)):
                with self.subTest(guard=guard, offset=offset, value=value), self.assertRaises(ValueError):
                    discovered(patched(f, offset, value))

    def test_policy_values_and_contexts_are_exact(self):
        self.assertEqual(pool.pool_words(WORDS), WORDS)
        for value in (False, True, 1, 4, 6, None, "dispatch-identified ", b"dispatch-identified", "interposed"):
            with self.subTest(value=value), self.assertRaises(ValueError):
                pool.pool_words(value)
        f = fixture(interposed=2)
        for context in ({"interposed_words": "Dispatch-identified"}, {"interposed_words": 2},
                        {"interposed_words": WORDS, "buffer": {}}):
            with self.subTest(context=context), self.assertRaises(ValueError):
                match.verify_leaf_instructions(f["data"], A, True, f["calls"], function_thunk_context=context)
        profile.check_pool_opt_in(WORDS, True)
        for words, thunks in ((WORDS, False), (WORDS, None), ("other", True)):
            with self.subTest(words=words, thunks=thunks), self.assertRaises(ValueError):
                profile.check_pool_opt_in(words, thunks)
        self.assertEqual(profile.pool_words(SELECTOR), WORDS)
        self.assertEqual(profile.schema_for(SELECTOR), profile.INTERPOSED_SCHEMA)
        self.assertEqual(profile.pool_words(profile.SELECTOR), 5)


class InterposedPoolManifest(unittest.TestCase):
    def test_numeric_and_typed_object_pool_words_bind_through_the_literal_rules(self):
        for object_word in (None, 0, 1):
            with self.subTest(object_word=object_word):
                f = fixture(interposed=2, object_word=object_word)
                manifest = manifest_for(f)
                self.assertEqual(manifest["selector"], SELECTOR)
                self.assertEqual(manifest["pool_switch"]["schema"], pool.INTERPOSED_SCHEMA)
                self.assertEqual(manifest["data"], [[offset, "g_synthetic", 0] for offset in f["literals"]])
                self.assertTrue(profile.verify(f["data"], A, f["rom"], f["mapping"], f["index"], f["objects"], manifest))

    def test_code_entry_pool_word_without_function_provenance_is_refused(self):
        for value in (A | 1, A, profile.ALIASES["_call_via_r2"]):
            f = fixture(interposed=2, values=[0x1424, value])
            with self.subTest(value=value), self.assertRaises(ValueError):
                profile.verify(f["data"], A, f["rom"], f["mapping"], f["index"], f["objects"], manifest_for(f))

    def test_manifest_mutations_and_input_changes_are_refused(self):
        f = fixture(interposed=3, object_word=1, guard="bhi")
        manifest = manifest_for(f)
        self.assertTrue(profile.verify(f["data"], A, f["rom"], f["mapping"], f["index"], f["objects"], manifest))
        for mutation in ("selector_v1", "selector_zero", "no_selector", "source", "pool_schema", "pool_word",
                         "layout", "extra", "data"):
            broken = copy.deepcopy(manifest)
            if mutation == "selector_v1": broken["selector"] = profile.SELECTOR
            elif mutation == "selector_zero": broken["selector"] = profile.ZERO_SELECTOR
            elif mutation == "no_selector": del broken["selector"]
            elif mutation == "source": broken["producer_source_sha256"]["thunk_pool_switch.py"] = "0" * 64
            elif mutation == "pool_schema": broken["pool_switch"]["schema"] = pool.SCHEMA
            elif mutation == "pool_word": broken["pool_switch"]["pool"].pop()
            elif mutation == "layout": broken["pool_switch"]["layout"]["literal"] -= 4
            elif mutation == "extra": broken["buffer"] = []
            else: broken["data"][0][2] = 4
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                profile.verify(f["data"], A, f["rom"], f["mapping"], f["index"], f["objects"], broken)
        for field in ("index", "objects"):
            changed = dict(f)
            changed[field] = f"{A:08X} {A + 2:08X} 2\n".encode() if field == "index" else \
                b'{"g_synthetic":"0x02001004"}'
            with self.subTest(field=field), self.assertRaises(ValueError):
                profile.verify(f["data"], A, f["rom"], f["mapping"], changed["index"], changed["objects"], manifest)

    def test_linking_keeps_original_relocation_identity(self):
        f = fixture(interposed=3, object_word=2); before, after = images(f)
        switches = {}
        calls, functions, literals = profile.original_bindings(before, A, f["mapping"], f["rom"], f["objects"],
                                                                switch_relocations=switches, selector=SELECTOR)
        self.assertEqual(switches, f["switches"]); self.assertEqual(literals, f["literals"])
        targets = {"_call_via_r3": profile.ALIASES["_call_via_r3"], "g_synthetic": OBJECT}
        kwargs = dict(data_relocations=literals, function_relocations=functions, switch_relocations=switches,
                      function_thunks=True, thunk_pool_words=WORDS)
        self.assertEqual(match.linked_function_bytes(before, after, NAME, A, calls, targets, **kwargs), f["data"])
        for mutation in ("pool_word", "data_word", "case_word"):
            broken = copy.deepcopy(after); data = bytearray(broken["text"])
            offset = {"pool_word": f["labels"]["pool0"], "data_word": f["labels"]["pool2"],
                      "case_word": f["labels"]["table"]}[mutation]
            data[offset] ^= 1; broken["text"] = bytes(data)
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                match.linked_function_bytes(before, broken, NAME, A, calls, targets, **kwargs)
        for words in (5, 0):
            with self.subTest(words=words), self.assertRaises(ValueError):
                match.linked_function_bytes(before, after, NAME, A, calls, targets,
                                            **dict(kwargs, thunk_pool_words=words))


class InterposedPoolReports(unittest.TestCase):
    def test_CLI_report_replay_status_and_rebuild_forward_the_selector(self):
        with synthetic_environment(interposed=3, guard="bhi") as env:
            for selector in (profile.SELECTOR, profile.ZERO_SELECTOR):
                with self.subTest(selector=selector):
                    code, output = run_match(env, selector)
                    self.assertNotIn("verdict MATCH", output)
            code, output = run_match(env, SELECTOR)
            self.assertEqual(code, 0)
            self.assertIn("verdict MATCH - byte identical", output)
            report = (env.root / "docs/match/08000000.md").read_text()
            self.assertIn(f"* verification: `{profile.INTERPOSED_SCHEMA}`", report)
            self.assertEqual(profile.selector_for_report(report), SELECTOR)
            self.assertTrue(evidence.report_matches(report, env.root, A))
            self.assertEqual(rebuild.saved_profile_arguments(report, env.root, A),
                             ["--function-address-profile", SELECTOR])
            calls = []
            def status_boundary(command, **kwargs):
                calls.append(command)
                return SimpleNamespace(returncode=0, stdout=f"extent    {len(env.f['data'])} bytes\n"
                                       "verdict MATCH - byte identical\n", stderr="")
            with patch.object(status.subprocess, "run", status_boundary):
                result = status.collect(str(env.root), True, quiet=True)
            self.assertEqual(result[1], 1); self.assertEqual(result[4], [])
            self.assertEqual(calls[0][calls[0].index("--function-address-profile") + 1], SELECTOR)

    def test_forged_reports_are_refused_before_status_execution(self):
        with synthetic_environment(interposed=2) as env:
            self.assertEqual(run_match(env, SELECTOR)[0], 0)
            report_path = env.root / "docs/match/08000000.md"; report = report_path.read_text()
            variants = [report.replace(f"* function-address thunks: {SELECTOR}",
                                       f"* function-address thunks: {profile.SELECTOR}"),
                        report.replace(f"* function-address thunks: {SELECTOR}",
                                       f"* function-address thunks: {profile.ZERO_SELECTOR}"),
                        report.replace(profile.INTERPOSED_SCHEMA, profile.SCHEMA),
                        report.replace(profile.INTERPOSED_SCHEMA, profile.ZERO_SCHEMA),
                        report.replace(pool.INTERPOSED_SCHEMA, pool.SCHEMA),
                        report.replace('"selector":"' + SELECTOR + '"', '"selector":"' + profile.ZERO_SELECTOR + '"'),
                        report + f"\n* function-address thunks: {SELECTOR}\n",
                        report + "\n* switches: forged\n"]
            for damaged in variants:
                self.assertNotEqual(damaged, report)
                self.assertFalse(evidence.report_matches(damaged, env.root, A))
                report_path.write_text(damaged)
                with patch.object(status.subprocess, "run", side_effect=AssertionError("forged report dispatched")):
                    result = status.collect(str(env.root), True, quiet=True)
                self.assertEqual(result[1], 0); self.assertTrue(result[4])
            report_path.write_text(report)
            for relative in ("src/08000000.c", "config/data_symbols.json", "symbols/functions.txt"):
                path = env.root / relative; saved = path.read_bytes(); path.write_bytes(saved + b" ")
                self.assertFalse(evidence.report_matches(report, env.root, A)); path.write_bytes(saved)


if __name__ == "__main__":
    unittest.main()
