import contextlib
import copy
import hashlib
import io
import json
import os
import signal
import struct
import subprocess
from pathlib import Path
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import match
import match_evidence
import switch_constants_profile as profile
import switch_placement as placement
from test_switch_constants import SOURCE, fixed_args, assemble, fixture_assembly
import rebuild
import status


PIPELINE_SOURCE = "\n".join(
    f"extern unsigned int func_{0x08001000 + index * 2:08X}(unsigned int);" for index in range(6))
PIPELINE_SOURCE += "\n" + SOURCE[:SOURCE.index("    switch (selector)")] + "    switch (selector) {\n"
for selector in range(6):
    PIPELINE_SOURCE += f"    case {selector}:\n"
    PIPELINE_SOURCE += (f"        left = func_{0x08001000 + selector * 2:08X}(left ^ right);\n" * 8)
    PIPELINE_SOURCE += "        return left;\n"
PIPELINE_SOURCE += "    default: return right;\n    }\n}\n"


class SnapshotDeadline(Exception):
    pass


def bounded_snapshot(snapshot, path):
    def expired(signum, frame):
        raise SnapshotDeadline("artifact open required the test watchdog")

    previous_handler = signal.signal(signal.SIGALRM, expired)
    previous_timer = signal.setitimer(signal.ITIMER_REAL, 2)
    try:
        return snapshot(path)
    finally:
        signal.setitimer(signal.ITIMER_REAL, *previous_timer)
        signal.signal(signal.SIGALRM, previous_handler)


def record_nonregular_capture(record):
    destination = os.environ.get("FFTA_NONREGULAR_CAPTURE_EVIDENCE")
    if destination:
        path = Path(destination)
        records = json.loads(path.read_text()) if path.exists() else []
        path.write_text(json.dumps(records + [record], indent=2) + "\n")


class PlacementTests(unittest.TestCase):
    policy = profile.LEGACY_POLICY

    def setUp(self):
        scratch = Path(__file__).resolve().parents[1] / "build"
        scratch.mkdir(exist_ok=True)
        self.temporary = tempfile.TemporaryDirectory(prefix="placement_", dir=scratch)
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)

    def prepare(self, address, source=SOURCE, policy=profile.LEGACY_POLICY):
        root = self.root / f"{address:08X}_{len(list(self.root.iterdir()))}"
        (root / "src").mkdir(parents=True)
        relative = f"src/{address:08X}.c"
        source = source.replace("08000000", f"{address:08X}")
        (root / relative).write_text(source)
        runner = match.Runner(match.DEFAULT_CC, root=root, timeout=120)
        with placement.workspace(runner) as workspace:
            original, _, image = placement.compile_object(runner, workspace, fixed_args(), root, address, relative)
            size = next(symbol["size"] for symbol in image["symbols"] if symbol["type"] == 2)
            entries = [{"rom": f"0x{address:08X}", "end": f"0x{address + size:08X}", "mode": "thumb"}]
            entries += [{"rom": f"0x{int(symbol['name'][5:], 16):08X}",
                         "end": f"0x{int(symbol['name'][5:], 16) + 2:08X}", "mode": "thumb"}
                        for symbol in image["symbols"] if symbol["name"].startswith("func_") and not symbol["section"]]
            mapping = json.dumps(entries).encode()
            body, manifest, count, linked_capture = profile._object_bytes(runner, workspace, fixed_args(), image,
                                                                        address, mapping, bytes(8192), policy)
            raw = runner.read_binary(f"{workspace}/f.raw.s")
            placed = runner.read_binary(f"{workspace}/f.s")
            linked = runner.read_binary(f"{workspace}/f.elf")
            self.assertEqual(linked_capture["f.elf"][0], linked)
            self.assertEqual(placed, placement.place(raw, address)[0])
            self.assertEqual(placed == raw, address % 4 == 0)
            self.assertEqual(image["text"][:address % 4], bytes(address % 4))
        rom = bytes(address - 0x08000000) + body
        rom += bytes(max(0, 8192 - len(rom)))
        (root / "fixture.rom").write_bytes(rom)
        (root / "config").mkdir()
        (root / "symbols").mkdir()
        (root / "config/functions.json").write_bytes(mapping)
        (root / "symbols/functions.txt").write_text(f"{address:08X} {address + size:08X} {size}\n")
        return root, rom, {"source": source, "raw": raw.decode(), "placed": placed.decode(),
            "original": original.hex(), "linked": linked.hex(), "body": body.hex(),
            "manifest": manifest, "count": count, "address": address,
            "insertion_position": placement.place(raw, address)[1]}

    @contextlib.contextmanager
    def trusted_fixture(self, root, rom):
        with patch.dict(os.environ, {"FFTA_ROM": str(root / "fixture.rom")}), \
                patch.object(profile, "ROM_SIZE", len(rom)), \
                patch.object(profile, "ROM_SHA1", hashlib.sha1(rom).hexdigest()):
            yield

    def test_natural_switch_issuance_and_replay_at_both_origins(self):
        evidence, guards, dispatches = [], set(), set()
        for source in (SOURCE, PIPELINE_SOURCE):
            for address in (0x08000000, 0x08000002):
                root, rom, captured = self.prepare(address, source)
                arguments = ["match.py", "--root", str(root), "--switch-profile", self.policy.selector, f"{address:08X}"]
                with self.subTest(address=address, pipeline=source == PIPELINE_SOURCE), \
                        self.trusted_fixture(root, rom), patch.object(sys, "argv", arguments), \
                        contextlib.redirect_stdout(io.StringIO()), \
                        patch.object(profile, "_compile_object", wraps=profile._compile_object) as compiled, \
                        patch.object(match, "elf_image", wraps=match.elf_image) as parsed, \
                        patch.object(profile, "_manifest", wraps=profile._manifest) as manifested:
                    self.assertEqual(match.main(), 0)
                    report = (root / f"docs/match/{address:08X}.md").read_text()
                    self.assertTrue(match_evidence.report_matches(report, root, address))
                    self.assertEqual(compiled.call_count, 2)
                    self.assertGreaterEqual(parsed.call_count, 6)
                    self.assertEqual(manifested.call_count, 2)
                    manifest = json.loads(next(line.split("`", 2)[1] for line in report.splitlines()
                                              if line.startswith("* switch constants manifest:")))
                    self.assertEqual(manifest["placement"]["original_elf_sha256"], profile.digest(bytes.fromhex(captured["original"])))
                    self.assertEqual(manifest["placement"]["linked_elf_sha256"], profile.digest(bytes.fromhex(captured["linked"])))
                    self.assertEqual(bool(manifest["calls"]), source == PIPELINE_SOURCE)
                    descriptor = manifest["switch"]
                    guards.add(descriptor["dispatch"] - descriptor["comparison"])
                    dispatches.add((address + descriptor["dispatch"]) % 4)
                    captured["report"] = report
                    captured["fresh_compile_count"] = compiled.call_count
                    captured["fresh_parse_count"] = parsed.call_count
                    captured["fresh_manifest_count"] = manifested.call_count
                    evidence.append(captured)
        self.assertEqual(guards, {4, 6})
        self.assertEqual(dispatches, {0, 2})
        destination = os.environ.get("FFTA_PLACEMENT_EVIDENCE")
        if destination:
            Path(destination).write_text(json.dumps(evidence, indent=2) + "\n")

    def synthetic(self, address, **options):
        assembly = fixture_assembly(**options).replace("08000000", f"{address:08X}")
        if address % 4:
            assembly = assembly.replace(".thumb_func\n", ".balign 4, 0\n.space 2, 0\n.thumb_func\n", 1)
        original = assemble(self.root, assembly)
        image = match.elf_image(original)
        size = next(item["size"] for item in image["symbols"] if item["name"] == f"func_{address:08X}")
        mapping = json.dumps([{"rom": f"0x{address:08X}", "end": f"0x{address + size:08X}", "mode": "thumb"},
                              {"rom": "0x08001000", "end": "0x08001002", "mode": "thumb"}]).encode()
        return original, mapping

    def admit(self, original, address, mapping):
        runner = match.Runner(match.DEFAULT_CC, root=self.root, timeout=120)
        with runner.workspace() as workspace:
            (Path(workspace) / "f.o").write_bytes(original)
            result = profile._object_bytes(runner, workspace, fixed_args(), match.elf_image(original),
                                          address, mapping, bytes(8192), self.policy)
            linked = runner.read_binary(f"{workspace}/f.elf")
        return result[:3], linked

    def test_base_two_guard_dispatch_zero_duplicate_call_matrix(self):
        dispatches = set()
        address = 0x08000002
        for guard in ("bhi", "bls"):
            for extra in (False, True):
                for call in (False, True):
                    for zero in (False, True):
                        with self.subTest(guard=guard, extra=extra, call=call, zero=zero):
                            original, mapping = self.synthetic(address, guard=guard, extra=extra,
                                                                call=call, zero=zero, duplicate=True)
                            (body, manifest, count), linked = self.admit(original, address, mapping)
                            self.assertEqual(body, match.elf_image(linked)["text"][2:2 + len(body)])
                            self.assertGreater(count, 10)
                            self.assertEqual(len(manifest["calls"]), int(call))
                            self.assertEqual([entry[1] for entry in manifest["constants"]],
                                             [0, 0] if zero else [0xFF00FF00, 0x0F0F0F0F])
                            dispatches.add((address + manifest["switch"]["dispatch"]) % 4)
        self.assertEqual(dispatches, {0, 2})

    def test_closed_grammar_and_exact_insertion(self):
        _, _, evidence = self.prepare(0x08000002)
        raw = evidence["raw"].encode()
        placed, position = placement.place(raw, 0x08000002)
        self.assertEqual(placed[:position] + placed[position + len(placement.INSERTION):], raw)
        self.assertEqual(placed[position:position + len(placement.INSERTION)], placement.INSERTION)
        for changed in (
                raw.replace(b"\t.thumb_func\n", b""), raw.replace(b"\t.thumb_func\n", b"\t.thumb_func\n" * 2),
                raw.replace(b".text\n", b".data\n"), raw.replace(b"\t.align\t2, 0\n", b".align 1\n", 1),
                raw.replace(b"\t.thumb_func\n", b".word 0\n\t.thumb_func\n", 1),
                raw.replace(b".text\n", b".text\n.space 4\n", 1),
                raw.replace(b"\t.thumb_func\n", b'@ .thumb_func\n', 1),
                raw.replace(b"\t.thumb_func\n", b'.ascii ".thumb_func"\n', 1),
                raw.replace(b".text\n", b".text\n.include \"file.s\"\n", 1),
                raw.replace(b".text\n", b".macro fake\n.endm\n.text\n", 1),
                raw + b".text\n.thumb_func\nother:\nbx lr\n", raw.replace(b"\tadd\t", b"\tadd.w\t", 1),
                raw.replace(b".word", b".long", 1), raw.replace(b"\tpush", b"\tpush; .word 0;", 1),
                raw.replace(b"@cond_branch", b"@cond_branch .thumb_func", 1),
                raw.replace(b".Lfe1:", b".Lfe1:\n.word 0", 1), raw.replace(b"\n", b"\r\n"),
                raw.replace(b"\t.size", b"\t.unknown", 1), placed):
            with self.subTest(changed=changed[:130]), self.assertRaises(ValueError):
                placement.place(changed, 0x08000002)
        for address in (True, 0x08000001, 0x07000000, 0x09000000, 0x08000000):
            with self.subTest(address=address), self.assertRaises(ValueError):
                placement.place(raw, address)

    def test_identical_linked_bytes_raw_attacks_both_words_and_origins(self):
        evidence = []
        for address in (0x08000000, 0x08000002):
            for word in (0, 1):
                with self.subTest(address=address, word=word):
                    good, mapping = self.synthetic(address, attack_word=word)
                    bad, _ = self.synthetic(address, relocated=word)
                    (body, manifest, _), good_linked = self.admit(good, address, mapping)
                    runner = match.Runner(match.DEFAULT_CC, root=self.root, timeout=120)
                    with runner.workspace() as workspace:
                        (Path(workspace) / "f.o").write_bytes(bad)
                        with self.assertRaises(ValueError):
                            profile._object_bytes(runner, workspace, fixed_args(), match.elf_image(bad),
                                                  address, mapping, bytes(8192), self.policy)
                        bad_linked = runner.read_binary(f"{workspace}/f.elf")
                    self.assertEqual(match.elf_image(good_linked)["text"], match.elf_image(bad_linked)["text"])
                    self.assertEqual(len(profile._original_records(match.elf_image(bad), address, mapping, 8192)),
                                     len(profile._original_records(match.elf_image(good), address, mapping, 8192)) + 1)
                    root, _, _ = self.prepare(address)
                    rom = bytes(address - 0x08000000) + body
                    rom += bytes(8192 - len(rom))
                    (root / "fixture.rom").write_bytes(rom)
                    (root / "config/functions.json").write_bytes(mapping)
                    (root / "symbols/functions.txt").write_text(f"{address:08X} {address + len(body):08X} {len(body)}\n")
                    compile_original = profile._compile_object

                    def inject(raw_object):
                        def compile_fixture(runner, workspace, *args, **kwargs):
                            compile_original(runner, workspace, *args, **kwargs)
                            (Path(workspace) / "f.o").write_bytes(raw_object)
                            image = match.elf_image(raw_object)
                            return raw_object, image["text"], image
                        return compile_fixture

                    with self.trusted_fixture(root, rom):
                        with patch.object(profile, "_compile_object", side_effect=inject(good)):
                            report = profile.render_report(address, profile._build_from_source(root, address, self.policy), self.policy)
                            self.assertTrue(match_evidence.report_matches(report, root, address))
                        with patch.object(profile, "_compile_object", side_effect=inject(bad)), \
                                patch.object(match_evidence, "switch_report_matches") as legacy:
                            self.assertFalse(match_evidence.report_matches(report, root, address))
                            legacy.assert_not_called()
                    evidence.append({"address": address, "word": word, "good_original": good.hex(),
                        "bad_original": bad.hex(), "good_linked": good_linked.hex(), "bad_linked": bad_linked.hex(),
                        "body": body.hex(), "manifest": manifest})
        destination = os.environ.get("FFTA_PLACEMENT_ATTACK_EVIDENCE")
        if destination:
            Path(destination).write_text(json.dumps(evidence, indent=2) + "\n")

    def test_original_and_linked_envelope_mutations(self):
        for address in (0x08000000, 0x08000002):
            original_raw, mapping = self.synthetic(address, call=True)
            (body, manifest, _), linked_raw = self.admit(original_raw, address, mapping)
            original, linked = match.elf_image(original_raw), match.elf_image(linked_raw)
            records = profile._original_records(original, address, mapping, 8192)
            calls = {address + site: int(name[5:], 16) for site, name in manifest["calls"]}
            targets = {name: int(name[5:], 16) for _, name in manifest["calls"]}
            relocations = dict(manifest["switch"]["relocations"])
            for is_linked, image in ((False, original), (True, linked)):
                for change in ("prefix", "length", "suffix", "base", "alignment", "value", "size", "mode", "bind", "extra", "allocated"):
                    changed = copy.deepcopy(image)
                    symbol = next(item for item in changed["symbols"] if item["name"] == f"func_{address:08X}")
                    if change == "prefix":
                        if address % 4 == 0:
                            continue
                        changed["text"] = b"\x01" + changed["text"][1:]
                    elif change == "length":
                        changed["text"] += b"\0\0\0\0"
                    elif change == "suffix":
                        symbol["size"] -= 2
                        changed["text"] = changed["text"][:-2] + b"\x01\x02"
                    elif change in ("base", "alignment"):
                        section = list(changed["sections"][changed["text_index"]])
                        section[3 if change == "base" else 8] += 2
                        changed["sections"][changed["text_index"]] = tuple(section)
                    elif change == "value":
                        symbol["value"] += 2
                    elif change == "size":
                        symbol["size"] += 2
                    elif change == "mode":
                        symbol["value"] &= ~1
                    elif change == "bind":
                        symbol["bind"] = 0
                    elif change == "extra":
                        changed["symbols"].append(dict(symbol, name="helper"))
                    else:
                        changed["sections"].append((0, 1, 2, 0, 0, 4, 0, 0, 4, 0))
                    with self.subTest(address=address, linked=is_linked, change=change), self.assertRaises(ValueError):
                        if is_linked:
                            profile._linked_bytes(original, changed, address, records, calls, targets, relocations)
                        elif change == "size":
                            raw = bytearray(original_raw)
                            for table_index, symbols in original["symbol_tables"].items():
                                for symbol_index, item in enumerate(symbols):
                                    if item["name"] == f"func_{address:08X}":
                                        size_offset = original["sections"][table_index][4] + symbol_index * 16 + 8
                                        struct.pack_into("<I", raw, size_offset, symbol["size"])
                            self.admit(bytes(raw), address, mapping)
                        else:
                            profile._original_records(changed, address, mapping, 8192)

    def test_raw_and_derived_relocation_coordinates_cannot_be_confused(self):
        address = 0x08000002
        original_raw, mapping = self.synthetic(address, zero=True, call=True)
        (body, manifest, _), linked_raw = self.admit(original_raw, address, mapping)
        original, linked = match.elf_image(original_raw), match.elf_image(linked_raw)
        section = original["sections"][original["relocations"][0]]
        raw_records = [struct.unpack_from("<II", original_raw, section[4] + offset) for offset in range(0, section[5], 8)]
        record_index = next(index for index, (_, info) in enumerate(raw_records) if info & 255 == 2)
        site, info = raw_records[record_index]
        text_start = original["sections"][original["text_index"]][4]
        prefix = 2
        constant_sites = [prefix + item[0] for item in manifest["constants"]]
        for position in (0, 1, prefix + len(body) - 2, prefix + len(body), site - prefix,
                         *(offset + delta for offset in constant_sites for delta in (-1, 0, 1, 2))):
            changed = bytearray(original_raw)
            struct.pack_into("<II", changed, section[4] + record_index * 8, position, info)
            with self.subTest(position=position), self.assertRaises(ValueError):
                self.admit(bytes(changed), address, mapping)
        addend = struct.unpack_from("<I", original_raw, text_start + site)[0]
        for changed_addend in (0, 1, addend - prefix, addend + prefix, prefix + len(body)):
            changed = bytearray(original_raw)
            struct.pack_into("<I", changed, text_start + site, changed_addend)
            with self.subTest(addend=changed_addend), self.assertRaises(ValueError):
                self.admit(bytes(changed), address, mapping)
        records = profile._original_records(original, address, mapping, 8192)
        calls = {address + site: int(name[5:], 16) for site, name in manifest["calls"]}
        targets = {name: int(name[5:], 16) for _, name in manifest["calls"]}
        bindings = dict(manifest["switch"]["relocations"])
        wrong = {site + prefix: addend + prefix for site, addend in bindings.items()}
        with self.assertRaises(ValueError):
            profile._linked_bytes(original, linked, address, records, calls, targets, wrong)
        changed = copy.deepcopy(linked)
        text = bytearray(changed["text"])
        struct.pack_into("<I", text, site, address + addend)
        changed["text"] = bytes(text)
        with self.assertRaises(ValueError):
            profile._linked_bytes(original, changed, address, records, calls, targets, bindings)

    def test_base_two_prefix_table_interior_and_load_edges(self):
        address = 0x08000002
        original, mapping = self.synthetic(address, call=True)
        (body, manifest, _), _ = self.admit(original, address, mapping)
        descriptor = manifest["switch"]
        calls = {address + site: int(name[5:], 16) for site, name in manifest["calls"]}
        bindings = dict(descriptor["relocations"])
        for target in (-2, descriptor["table"], descriptor["literal"] - 8,
                       *(descriptor["dispatch"] + delta for delta in range(0, 10, 2))):
            changed = bytearray(body)
            struct.pack_into("<H", changed, 0, 0xE000 | ((target - 4) // 2 & 0x7FF))
            with self.subTest(target=target), self.assertRaises(ValueError):
                profile._manifest(bytes(changed), address, calls, bindings)
        for word, _, loads in manifest["constants"]:
            for change in ("remove", "redirect"):
                changed = bytearray(body)
                site = loads[0]
                if change == "remove":
                    changed[site:site + 2] = bytes.fromhex("c046")
                else:
                    instruction = struct.unpack_from("<H", changed, site)[0]
                    struct.pack_into("<H", changed, site, instruction ^ 1)
                with self.subTest(word=word, change=change), self.assertRaises(ValueError):
                    profile._manifest(bytes(changed), address, calls, bindings)
        site = descriptor["table"]
        for target in (-2, descriptor["literal"], next(iter(calls)) - address + 2):
            changed, wrong = bytearray(body), dict(bindings)
            struct.pack_into("<I", changed, site, address + target)
            wrong[site] = target
            with self.subTest(case=target), self.assertRaises(ValueError):
                profile._manifest(bytes(changed), address, calls, wrong)

    def test_raw_assembly_stage_and_object_drift_reject(self):
        address = 0x08000002
        root, rom, _ = self.prepare(address)
        compile_original = profile._compile_object
        with self.trusted_fixture(root, rom):
            report = profile.render_report(address, profile._build_from_source(root, address, self.policy), self.policy)
            for name in ("f.raw.s", "f.s", "f.o"):
                def corrupt(runner, workspace, *args, **kwargs):
                    result = compile_original(runner, workspace, *args, **kwargs)
                    path = Path(workspace) / name
                    path.write_bytes(path.read_bytes() + b"\n")
                    return result
                with self.subTest(name=name), patch.object(profile, "_compile_object", side_effect=corrupt), \
                        patch.object(match_evidence, "switch_report_matches") as legacy:
                    self.assertFalse(match_evidence.report_matches(report, root, address))
                    legacy.assert_not_called()
            object_bytes = profile._object_bytes
            def late_change(runner, workspace, *args, **kwargs):
                result = object_bytes(runner, workspace, *args, **kwargs)
                path = Path(workspace) / "f.raw.s"
                path.write_bytes(path.read_bytes() + b"\n")
                return result
            with patch.object(profile, "_object_bytes", side_effect=late_change):
                self.assertFalse(match_evidence.report_matches(report, root, address))
        self.assertEqual(list((root / "build").iterdir()), [])

    def linked_capture_drift(self, address, name, change, final_boundary=False):
        root, rom, _ = self.prepare(address)
        arguments = ["match.py", "--root", str(root), "--switch-profile", self.policy.selector,
                     "--emit", "build/rejected.bin", f"{address:08X}"]
        report_path = root / f"docs/match/{address:08X}.md"
        output_path = root / "build/rejected.bin"
        object_bytes = profile._object_bytes
        workspaces, captures = [], []

        def corrupt(workspace):
            path = Path(workspace) / name
            original = path.read_bytes()
            before = path.stat().st_ino
            if change == "replace":
                replacement = path.with_suffix(path.suffix + ".replacement")
                replacement.write_bytes(original)
                replacement.replace(path)
            else:
                path.write_bytes(bytes([original[0] ^ 0x7F]) + original[1:])
            captures.append({"validated_sha256": profile.digest(original),
                             "changed_sha256": profile.digest(path.read_bytes()),
                             "same_inode": before == path.stat().st_ino})

        def after_object(runner, workspace, *args, **kwargs):
            result = object_bytes(runner, workspace, *args, **kwargs)
            workspaces.append(workspace)
            if not final_boundary:
                corrupt(workspace)
            return result

        import inert_spin_profile
        validate_span = inert_spin_profile.validate_span

        def after_span(*args, **kwargs):
            result = validate_span(*args, **kwargs)
            if final_boundary and workspaces:
                corrupt(workspaces.pop())
            return result

        with self.trusted_fixture(root, rom):
            clean_report = profile.render_report(address, profile._build_from_source(root, address, self.policy), self.policy)
            stdout = io.StringIO()
            with patch.object(profile, "_object_bytes", side_effect=after_object), \
                    patch.object(inert_spin_profile, "validate_span", side_effect=after_span), \
                    patch.object(match, "compile_object", side_effect=AssertionError("legacy compile fallback")), \
                    patch.object(match_evidence, "switch_report_matches", side_effect=AssertionError("legacy report fallback")), \
                    patch.object(sys, "argv", arguments), contextlib.redirect_stdout(stdout):
                try:
                    issued = match.main()
                except SystemExit as error:
                    issued = error.code
                emitted = output_path.exists()
                written = report_path.exists()
                replay_report = report_path.read_text() if written else clean_report
                replayed = match_evidence.report_matches(replay_report, root, address)
            record = {"address": address, "artifact": name, "change": change,
                      "final_boundary": final_boundary, "issuance_status": issued,
                      "replay_accepted": replayed, "report_written": written,
                      "output_written": emitted, "stdout": stdout.getvalue(), "captures": captures}
            destination = os.environ.get("FFTA_LINKED_CAPTURE_EVIDENCE")
            if destination:
                path = Path(destination)
                records = json.loads(path.read_text()) if path.exists() else []
                path.write_text(json.dumps(records + [record], indent=2) + "\n")
            if emitted:
                output_path.unlink()
            if written:
                report_path.unlink()
            self.assertEqual(len(captures), 2)
            self.assertNotEqual(issued, 0)
            self.assertFalse(replayed)
            self.assertFalse(written)
            self.assertFalse(emitted)
            self.assertNotIn("MATCH", stdout.getvalue())
            self.assertFalse(profile._active.get())
            self.assertEqual(list((root / "build").iterdir()), [])
            self.assertTrue(match_evidence.report_matches(clean_report, root, address))

    def test_linked_capture_bytes_and_replacement_reject(self):
        for address in (0x08000000, 0x08000002):
            for name in ("f.elf", "f.linked.bin"):
                for change in ("mutate", "replace"):
                    with self.subTest(address=address, name=name, change=change):
                        self.linked_capture_drift(address, name, change)

    def test_linked_capture_final_boundary_rejects(self):
        for name in ("f.elf", "f.linked.bin"):
            with self.subTest(name=name):
                self.linked_capture_drift(0x08000002, name, "mutate", final_boundary=True)

    def test_artifact_snapshot_nonregular_types_reject_without_timeout(self):
        regular = self.root / "regular"
        regular.write_bytes(b"unchanged linked snapshot")
        fifo = self.root / "fifo"
        os.mkfifo(fifo)
        symlink = self.root / "symlink"
        symlink.symlink_to(regular)
        fifo_symlink = self.root / "fifo-symlink"
        fifo_symlink.symlink_to(fifo)
        try:
            for path in (regular, symlink, fifo, fifo_symlink):
                with self.subTest(kind=path.name):
                    started = time.monotonic()
                    result, rejection, timed_out = None, None, False
                    try:
                        result = bounded_snapshot(profile._artifact_snapshot, path)
                    except SnapshotDeadline as error:
                        timed_out, rejection = True, str(error)
                    except (OSError, ValueError) as error:
                        rejection = str(error)
                    record_nonregular_capture({"kind": path.name, "test": "helper",
                        "watchdog_fired": timed_out, "rejection": rejection,
                        "accepted": result is not None, "elapsed_seconds": time.monotonic() - started})
                    self.assertFalse(timed_out)
                    if path == regular:
                        self.assertEqual(result[0], b"unchanged linked snapshot")
                    else:
                        self.assertIsNone(result)
                        self.assertIsNotNone(rejection)
        finally:
            for path in (fifo_symlink, symlink, fifo, regular):
                path.unlink(missing_ok=True)

    def test_artifact_snapshot_nonregular_replacement_at_open_rejects(self):
        path = self.root / "replaced-at-open"
        path.write_bytes(b"regular before acquisition")
        real_open = os.open
        descriptors = []

        def replace_before_open(target, flags, *args, **kwargs):
            self.assertEqual(Path(target), path)
            path.unlink()
            os.mkfifo(path)
            descriptor = real_open(target, flags, *args, **kwargs)
            descriptors.append(descriptor)
            return descriptor

        timed_out, rejection = False, None
        try:
            with patch.object(profile.os, "open", side_effect=replace_before_open):
                try:
                    bounded_snapshot(profile._artifact_snapshot, path)
                except SnapshotDeadline as error:
                    timed_out, rejection = True, str(error)
                except (OSError, ValueError) as error:
                    rejection = str(error)
            closed = []
            for descriptor in descriptors:
                try:
                    os.fstat(descriptor)
                    closed.append(False)
                except OSError:
                    closed.append(True)
            record_nonregular_capture({"test": "replace-at-open", "watchdog_fired": timed_out,
                "rejection": rejection, "opened_descriptors": len(descriptors), "closed": closed})
            self.assertFalse(timed_out)
            self.assertEqual(rejection, "linked artifact is not a regular file")
            self.assertEqual(closed, [True])
        finally:
            path.unlink(missing_ok=True)

    def nonregular_capture(self, name, final_boundary):
        address = 0x08000002
        root, rom, _ = self.prepare(address)
        arguments = ["match.py", "--root", str(root), "--switch-profile", self.policy.selector,
                     "--emit", "build/rejected.bin", f"{address:08X}"]
        report_path = root / f"docs/match/{address:08X}.md"
        output_path = root / "build/rejected.bin"
        snapshot = profile._artifact_snapshot
        captures, fifo_paths = [], []
        calls = 0

        def substitute(path):
            nonlocal calls
            path = Path(path)
            if path.name != name:
                return snapshot(path)
            calls += 1
            if calls != (2 if final_boundary else 1):
                return snapshot(path)
            original_digest = profile.digest(path.read_bytes())
            path.unlink()
            os.mkfifo(path)
            fifo_paths.append(path)
            captures.append({"call": calls, "original_sha256": original_digest})
            return bounded_snapshot(snapshot, path)

        try:
            with self.trusted_fixture(root, rom):
                clean_report = profile.render_report(address, profile._build_from_source(root, address, self.policy), self.policy)
                stdout = io.StringIO()
                issuance_timeout, replay_timeout = False, False
                with patch.object(profile, "_artifact_snapshot", side_effect=substitute), \
                        patch.object(match, "compile_object", side_effect=AssertionError("legacy compile fallback")), \
                        patch.object(match_evidence, "switch_report_matches", side_effect=AssertionError("legacy report fallback")), \
                        patch.object(sys, "argv", arguments), contextlib.redirect_stdout(stdout):
                    try:
                        issued = match.main()
                    except SystemExit as error:
                        issued = error.code
                    except SnapshotDeadline as error:
                        issuance_timeout, issued = True, str(error)
                    calls = 0
                    try:
                        replayed = match_evidence.report_matches(clean_report, root, address)
                    except SnapshotDeadline:
                        replay_timeout, replayed = True, None
                written, emitted = report_path.exists(), output_path.exists()
                cleaned = all(not path.exists() for path in fifo_paths)
                record_nonregular_capture({"test": "public-boundary", "artifact": name,
                    "final_boundary": final_boundary, "issuance_status": issued,
                    "issuance_watchdog_fired": issuance_timeout, "replay_watchdog_fired": replay_timeout,
                    "replay_accepted": replayed, "report_written": written, "output_written": emitted,
                    "stdout": stdout.getvalue(), "captures": captures, "fifo_paths_cleaned": cleaned,
                    "context_active": profile._active.get(), "build_empty": not list((root / "build").iterdir())})
                self.assertEqual(len(captures), 2)
                self.assertTrue(cleaned)
                self.assertFalse(profile._active.get())
                self.assertEqual(list((root / "build").iterdir()), [])
                self.assertFalse(issuance_timeout)
                self.assertFalse(replay_timeout)
                self.assertNotEqual(issued, 0)
                self.assertIs(replayed, False)
                self.assertFalse(written)
                self.assertFalse(emitted)
                self.assertNotIn("MATCH", stdout.getvalue())
                self.assertTrue(match_evidence.report_matches(clean_report, root, address))
        finally:
            for path in fifo_paths:
                path.unlink(missing_ok=True)

    def test_nonregular_initial_capture_rejects_without_fallback(self):
        for name in ("f.elf", "f.linked.bin"):
            with self.subTest(name=name):
                self.nonregular_capture(name, final_boundary=False)

    def test_nonregular_final_capture_rejects_without_fallback(self):
        for name in ("f.elf", "f.linked.bin"):
            with self.subTest(name=name):
                self.nonregular_capture(name, final_boundary=True)

    def test_missing_word_second_dispatch_and_prefix_call_reject(self):
        address = 0x08000002
        initial = fixture_assembly(call=True).replace("08000000", "08000002")
        initial = initial.replace(".thumb_func\n", ".balign 4, 0\n.space 2, 0\n.thumb_func\n", 1)
        variants = (initial.replace(".word 0xFF00FF00\n", ""),
                    initial.replace(".Ldefault:\nmovs r0, #0", ".Ldefault:\nmov pc, r0"),
                    initial.replace("func_08001000", "func_08000000"))
        for assembly in variants:
            original = assemble(self.root, assembly)
            image = match.elf_image(original)
            size = next(item["size"] for item in image["symbols"] if item["name"] == "func_08000002")
            mapping = json.dumps([{"rom": "0x08000002", "end": f"0x{address + size:08X}", "mode": "thumb"},
                                  {"rom": "0x08000000", "end": "0x08000002", "mode": "thumb"},
                                  {"rom": "0x08001000", "end": "0x08001002", "mode": "thumb"}]).encode()
            with self.subTest(assembly=assembly[-110:]), self.assertRaises(ValueError):
                self.admit(original, address, mapping)

    def test_base_two_linked_unrelocated_bytes_remain_immutable(self):
        address = 0x08000002
        original_raw, mapping = self.synthetic(address, extra=True, call=True)
        (_, manifest, _), linked_raw = self.admit(original_raw, address, mapping)
        original, linked = match.elf_image(original_raw), match.elf_image(linked_raw)
        records = profile._original_records(original, address, mapping, 8192)
        calls = {address + site: int(name[5:], 16) for site, name in manifest["calls"]}
        targets = {name: int(name[5:], 16) for _, name in manifest["calls"]}
        bindings = dict(manifest["switch"]["relocations"])
        for site in (2, *(2 + item[0] for item in manifest["constants"]),
                     2 + manifest["switch"]["dispatch"] + 10):
            changed = copy.deepcopy(linked)
            text = bytearray(changed["text"])
            text[site] ^= 1
            changed["text"] = bytes(text)
            with self.subTest(site=site), self.assertRaises(ValueError):
                profile._linked_bytes(original, changed, address, records, calls, targets, bindings)

    def test_placement_manifest_and_v1_markers_are_comparison_only(self):
        address = 0x08000002
        root, rom, _ = self.prepare(address)
        with self.trusted_fixture(root, rom):
            result = profile._build_from_source(root, address)
            report = profile.render_report(address, result)
            manifest = json.loads(result.manifest_json)
            for name, value in (("section_base", address), ("function_offset", 0), ("prefix_size", True),
                                ("rule", "different"), ("original_elf_sha256", "0" * 64),
                                ("linked_elf_sha256", "F" * 64), ("raw_assembly_sha256", "0" * 64),
                                ("placed_assembly_sha256", "0" * 64), ("extra", "unbound")):
                changed = copy.deepcopy(manifest)
                changed["placement"][name] = value
                changed_report = report.replace(result.manifest_json, profile.canonical(changed))
                with self.subTest(name=name), patch.object(match_evidence, "switch_report_matches") as legacy:
                    self.assertFalse(match_evidence.report_matches(changed_report, root, address))
                    legacy.assert_not_called()
            for changed in (report.replace("two-constants-v2", "two-constants-v1"),
                            report + "* verification: `elf-symbol-thumb-switch-two-constants-v1`\n",
                            report + "* switch constants: two-constants-v1\n"):
                self.assertFalse(match_evidence.report_matches(changed, root, address))

    def test_late_status_rebuild_and_external_prefix_exclusion(self):
        address = 0x08150002
        root, rom, fixture = self.prepare(address)
        prefix_offset = address - 0x08000000 - 2
        rom = rom[:prefix_offset] + b"\xAB\xCD" + rom[prefix_offset + 2:] + bytes(8)
        (root / "fixture.rom").write_bytes(rom)
        tools = Path(match.__file__).resolve().parent
        launcher = ("import sys\n" + f"sys.path.insert(0, {str(tools)!r})\n"
                    "import match, switch_constants_profile as profile\n"
                    f"profile.ROM_SIZE = {len(rom)}\n"
                    f"profile.ROM_SHA1 = {hashlib.sha1(rom).hexdigest()!r}\n"
                    f"sys.argv[0] = {str(tools / 'match.py')!r}\n"
                    "sys.exit(match.main())\n")
        run, records = subprocess.run, []
        include_prefix = False
        body = bytes.fromhex(fixture["body"])

        def actual_match(command, **kwargs):
            self.assertEqual(command[:2], [sys.executable, str(tools / "match.py")])
            self.assertIn(self.policy.selector, command)
            result = run([sys.executable, "-c", launcher, *command[2:]], timeout=120, **kwargs)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            record = {"command": command, "stdout": result.stdout, "stderr": result.stderr, "exit": result.returncode}
            if "--emit" in command:
                emitted = Path(command[command.index("--emit") + 1])
                self.assertEqual(emitted.read_bytes(), body)
                record["emitted"] = emitted.read_bytes().hex()
                if include_prefix:
                    emitted.write_bytes(b"\0\0" + body)
            records.append(record)
            return result

        output = root / "build/rebuilt.bin"
        with self.trusted_fixture(root, rom), patch.object(status.subprocess, "run", side_effect=actual_match):
            command = [sys.executable, str(tools / "match.py"), "--root", str(root), f"{address:08X}",
                       "--switch-profile", self.policy.selector]
            actual_match(command, capture_output=True, text=True)
            main_entries = [entry for entry in json.loads((root / "config/functions.json").read_text())
                            if int(entry["rom"], 16) < status.CODE_END]
            main_bytes = sum(int(entry["end"], 16) - int(entry["rom"], 16) for entry in main_entries)
            self.assertEqual(status.collect(str(root), True, quiet=True),
                             (len(main_entries), 0, main_bytes, 0, [], 1, len(body)))
            with contextlib.redirect_stdout(io.StringIO()) as log:
                self.assertEqual(rebuild.compiled_rebuild(root, str(output)), 0)
            self.assertEqual(output.read_bytes(), rom)
            self.assertEqual(output.read_bytes()[prefix_offset:prefix_offset + 2], b"\xAB\xCD")
            output.unlink()
            include_prefix = True
            with contextlib.redirect_stdout(io.StringIO()), self.assertRaisesRegex(ValueError, "compiled byte mismatch"):
                rebuild.compiled_rebuild(root, str(output))
            self.assertFalse(output.exists())
        self.assertEqual(list((root / "build").iterdir()), [])
        destination = os.environ.get("FFTA_PLACEMENT_CONSUMER_EVIDENCE")
        if destination:
            Path(destination).write_text(json.dumps({"address": address, "body": body.hex(),
                "external_prefix": "abcd", "rebuild_log": log.getvalue(), "invocations": records,
                "wrong_prefix_control": "compiled byte mismatch; no output retained"}, indent=2) + "\n")


if __name__ == "__main__":
    unittest.main()
