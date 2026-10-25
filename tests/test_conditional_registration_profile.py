"""S1 foundation tests; fresh synthetic captures, no public MATCH results."""

import copy
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import socket
import struct
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import conditional_registration_profile as profile


SCRATCH = Path("/home/user/.codex-work/ffta-ulw/conditional-registration-public-s1b-sol61/repair-f1-f2")
ADDRESS = 0x08000002
DEPENDENCY_SHA256 = "6edf9439e64096d31aa616fbadf5bb3c684893fb05c7b6ae790f3d0c3a0ba917"


def encoded(record):
    return profile.canonical(record).encode("utf-8") + b"\n"


def bound_socket(path):
    connection = socket.socket(socket.AF_UNIX)
    descriptor = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
    try:
        # Keep AF_UNIX's 108-byte spelling limit independent of the scratch path.
        connection.bind(f"/proc/self/fd/{descriptor}/{path.name}")
    except BaseException:
        connection.close()
        raise
    finally:
        os.close(descriptor)
    return connection


def fixture():
    invocation = "caller-invocation"
    regions = [
        {"id": "heap", "base": {"tag": "concrete", "address": 0x02010000}, "size": 4096,
         "permission": "rw", "kind": "external", "lifetime": "live", "frame": None},
        {"id": "image", "base": {"tag": "concrete", "address": 0x03005E78}, "size": 50,
         "permission": "rx", "kind": "runtime-image", "lifetime": "live", "frame": None},
        {"id": "manager-cell", "base": {"tag": "concrete", "address": 0x0200F430}, "size": 4,
         "permission": "r", "kind": "external", "lifetime": "live", "frame": None},
        {"id": "metadata", "base": {"tag": "concrete", "address": 0x02020000}, "size": 64,
         "permission": "rw", "kind": "external", "lifetime": "live", "frame": None},
        {"id": "stack", "base": {"tag": "symbolic", "anchor": "stack-anchor", "offset": 0}, "size": 4096,
         "permission": "rw", "kind": "stack-domain", "lifetime": "live", "frame": None},
    ]
    values = [{"id": name, "tag": "symbolic", "width": 4,
               "origin": {"tag": "register", "invocation": invocation, "register": name}}
              for name in profile.private.REGISTERS]
    values += [
        {"id": "head", "tag": "constant", "width": 4, "value": 0},
        {"id": "owner", "tag": "pointer", "region": "metadata", "offset": 0},
        {"id": "phase", "tag": "symbolic", "width": 2,
         "origin": {"tag": "memory", "region": "heap", "offset": 12}},
        {"id": "return-control", "tag": "control", "invocation": invocation, "target": None},
        {"id": "stack-pointer", "tag": "pointer", "region": "stack", "offset": 4096},
    ]
    entry = {"invocation": invocation, "frame": "caller-frame",
             "registers": {name: name for name in profile.private.REGISTERS},
             "sp": "stack-pointer", "lr": "return-control", "regions": regions,
             "frames": [{"id": "caller-frame", "invocation": invocation, "parent": None,
                         "entry_sp": "stack-pointer", "allocations": [], "saves": []}],
             "values": sorted(values, key=lambda item: item["id"]), "cells": []}
    token = lambda name: {"call": name}
    slc = profile.private.slc
    parameters = [
        {"domain": slc("stack", 0, 4096), "entry_sp": token("sp"),
         "allocator_window": {"anchor": "allocator-entry-sp", "low": -256, "high": 0}},
        {**{name: token(name) for name in ("descriptor", "parameters", "manager", "parent", "protected", "separation")}, "nodes": []},
        {"manager_cell": slc("manager-cell", 0, 4), "manager_value": token("manager-value"),
         "owner_value": "owner", "phase_value": "phase", "head_value": "head", "chain": []},
        {"binding": "allocator-call", "domain": slc("heap", 0, 4096), "owner_metadata": slc("metadata", 0, 64),
         "stack_window": "B1.allocator_window", "result_role": "task", "result_bytes": 40},
        {"binding": "allocator-call", "result_role": "task"},
        {"binding": "initializer-image", "call": "initializer-call", "image": slc("image", 0, 50)},
        {"data_value": token("data-value"), "source": token("data-source"), "operation": "copy-only"},
        {"binding": "allocator-call", "interference_scope": "registration-call"},
    ]
    conditions = []
    for number, parameter in enumerate(parameters):
        scope = "allocator" if number in (3, 4) else "initializer" if number == 5 else "registration"
        conditions.append({"id": "B" + str(number + 1), "clause": profile.private.CLAUSES[number],
                           "invocation": "each-reached-registration", "source": "declared-invocation",
                           "status": "assumed", "interval": {"begin": scope + "-entry", "end": scope + "-return"},
                           "parameters": parameter})
    return {"schema": profile.CONTEXT_SCHEMA, "policy": profile.POLICY, "operation": profile.OPERATION,
            "address": ADDRESS, "site": ADDRESS + 32, "entry": entry, "conditions": conditions}


def add_ancestor(record):
    entry = record["entry"]
    ancestor = {"id": "ancestor-frame", "invocation": "ancestor-invocation", "parent": None,
                "entry_sp": "ancestor-sp", "allocations": ["saved"],
                "saves": [{"witness": "save-r4", "register": "r4",
                           "location": profile.private.slc("saved", 0, 4), "value": "r4"}]}
    entry["frames"][0]["parent"] = ancestor["id"]
    entry["frames"].insert(0, ancestor)
    entry["values"].insert(0, {"id": "ancestor-sp", "tag": "pointer", "region": "stack", "offset": 4096})
    entry["regions"].append({"id": "saved", "base": {"tag": "relative", "region": "stack", "offset": 4000},
                             "size": 16, "permission": "rw", "kind": "stack-allocation", "lifetime": "live",
                             "frame": "ancestor-frame"})
    entry["regions"].sort(key=lambda item: item["id"])
    next(value for value in entry["values"] if value["id"] == "stack-pointer")["offset"] = 4000
    entry["cells"] = [{"location": profile.private.slc("saved", 0, 4),
                       "bytes": [{"tag": "fragment", "value": "r4", "index": index} for index in range(4)]}]


class RequestTests(unittest.TestCase):
    def parse(self, record=None, **options):
        return profile.parse_request(encoded(fixture() if record is None else record),
                                     address=options.get("address", ADDRESS),
                                     path=options.get("path", profile.context_path(ADDRESS)))

    def reject(self, record, category="identity"):
        with self.assertRaises(profile.Failure) as caught:
            self.parse(record)
        self.assertEqual(caught.exception.category, category)

    def test_valid_entry_and_both_raw_signature_arrangements(self):
        for count, selector in (("r1", "r0"), ("r2", "r3")):
            request = self.parse()
            profile.validate_raw_inputs(request, [{"role": "count", "register": count, "value": count},
                                                  {"role": "selector", "register": selector, "value": selector}])
            self.assertEqual(request.to_dict(), fixture())
            self.assertEqual(request.pin, profile.private.pin(encoded(fixture())))
        self.assertFalse(profile.CANONICAL_REPORT_ELIGIBLE)
        self.assertEqual(len(profile.REMAINING_OBLIGATIONS), 4)

    def test_valid_ancestor_saves_bytes_and_nullable_control(self):
        record = fixture()
        add_ancestor(record)
        self.parse(record)
        next(value for value in record["entry"]["values"] if value["id"] == "return-control")["target"] = 0x08001001
        self.parse(record)

    def test_every_request_field_is_required_and_closed(self):
        for name in fixture():
            with self.subTest(name=name):
                record = fixture()
                del record[name]
                self.reject(record)
        for name in ("raw_inputs", "selector", "range", "effects", "pending_restoration", "fingerprint"):
            record = fixture()
            record[name] = []
            self.reject(record)

    def test_nested_closed_fields_wrong_primitives_and_null(self):
        paths = [("entry",), ("entry", "registers"), ("entry", "regions", 0),
                 ("entry", "regions", 0, "base"), ("entry", "frames", 0),
                 ("entry", "values", 0), ("conditions", 0), ("conditions", 0, "parameters"),
                 ("conditions", 0, "parameters", "entry_sp"),
                 ("conditions", 0, "parameters", "allocator_window")]
        for path in paths:
            for change in ("unknown", "missing", "null", "list"):
                record = fixture()
                target = record
                for key in path[:-1]:
                    target = target[key]
                original = target[path[-1]]
                if change == "unknown":
                    original["extra"] = 0
                elif change == "missing":
                    del original[next(iter(original))]
                else:
                    target[path[-1]] = None if change == "null" else []
                with self.subTest(path=path, change=change):
                    self.reject(record)

    def test_integer_and_enum_domains(self):
        for field in ("address", "site"):
            for value in (True, False, 1.0, "134217730", None, -1, 2 ** 32):
                record = fixture()
                record[field] = value
                self.reject(record)
        for value in (profile.ROM_BASE - 2, profile.ROM_END, ADDRESS + 1):
            record = fixture()
            record["address"] = value
            self.reject(record)
        for value in (ADDRESS - 2, ADDRESS + 1, profile.ROM_END - 2):
            record = fixture()
            record["site"] = value
            self.reject(record)
        record = fixture()
        record["policy"] = profile.POLICY.upper()
        self.reject(record)

    def test_exact_context_path_and_bound_address(self):
        for path in ("config/conditional_registration/08000002.JSON", "config/conditional_registration/08000004.json",
                     "config//conditional_registration/08000002.json", "./config/conditional_registration/08000002.json",
                     "/config/conditional_registration/08000002.json", "config/../08000002.json", "config\\08000002.json"):
            with self.subTest(path=path), self.assertRaises(profile.Failure):
                self.parse(path=path)
        with self.assertRaises(profile.Failure):
            self.parse(address=ADDRESS + 2)

    def test_canonical_request_bytes_and_duplicate_members(self):
        data = encoded(fixture())
        variants = [data[:-1], data + b"\n", b" " + data, b"\xef\xbb\xbf" + data,
                    json.dumps(fixture(), indent=2).encode() + b"\n",
                    data.replace(b'"address":134217730', b'"address":134217730.0'),
                    data.replace(b'"address":134217730', b'"address":1.3421773e8'),
                    data.replace(b'"address":134217730', b'"address":NaN'),
                    data.replace(b'"address":134217730', b'"address":Infinity'),
                    data.replace(b'"address":134217730', b'"address":134217730,"address":134217730'),
                    data.replace(b'"call":"sp"', b'"call":"sp","call":"sp"'),
                    data.replace(b'"caller-frame"', b'"caller-\\u0066rame"'), b"\xff\n"]
        for changed in variants:
            with self.subTest(changed=changed[:60]), self.assertRaises(profile.Failure):
                profile.parse_request(changed, address=ADDRESS, path=profile.context_path(ADDRESS))

    def test_all_template_fields_are_closed_and_exact(self):
        for index, condition in enumerate(fixture()["conditions"]):
            for name in condition:
                record = fixture()
                del record["conditions"][index][name]
                self.reject(record)
            for name in condition["parameters"]:
                record = fixture()
                del record["conditions"][index]["parameters"][name]
                self.reject(record)
            for name in ("invocation", "clause", "status", "source"):
                record = fixture()
                record["conditions"][index][name] = "wrong"
                self.reject(record)
        for index, name in ((0, "entry_sp"), (1, "descriptor"), (1, "parent"), (1, "separation"),
                            (2, "manager_value"), (6, "data_value"), (6, "source")):
            for wrong in (None, "sp", {"call": "unknown"}, {"call": "sp", "offset": 0}):
                record = fixture()
                record["conditions"][index]["parameters"][name] = wrong
                self.reject(record)

    def test_missing_duplicate_extra_and_unsorted_conditions(self):
        for index in range(8):
            record = fixture()
            del record["conditions"][index]
            self.reject(record, "unmet-condition")
        for operation in ("duplicate", "reverse", "unknown"):
            record = fixture()
            if operation == "duplicate":
                record["conditions"].append(copy.deepcopy(record["conditions"][-1]))
            elif operation == "reverse":
                record["conditions"].reverse()
            else:
                record["conditions"][-1]["id"] = "B9"
            self.reject(record)

    def test_template_reference_and_role_invariants(self):
        mutations = [
            (0, "domain", profile.private.slc("missing", 0, 4)),
            (0, "domain", profile.private.slc("heap", 0, 4)),
            (0, "allocator_window", {"anchor": "allocator-entry-sp", "low": 0, "high": 0}),
            (0, "allocator_window", {"anchor": "allocator-entry-sp", "low": -3, "high": 0}),
            (2, "manager_cell", profile.private.slc("manager-cell", 0, 3)),
            (2, "owner_value", "missing"), (2, "owner_value", "r0"),
            (2, "phase_value", "head"), (2, "head_value", "owner"),
            (2, "chain", ["owner", "owner"]),
            (3, "domain", profile.private.slc("stack", 0, 4)),
            (3, "owner_metadata", profile.private.slc("metadata", 65, 4)),
            (3, "result_bytes", True), (3, "result_bytes", 41),
            (5, "image", profile.private.slc("image", 0, 49)),
        ]
        for index, name, value in mutations:
            record = fixture()
            record["conditions"][index]["parameters"][name] = value
            with self.subTest(index=index, name=name):
                with self.assertRaises(profile.Failure):
                    self.parse(record)
        record = fixture()
        record["entry"]["regions"][2]["base"]["address"] = 0x02008FF0
        self.reject(record)

    def test_registry_uniqueness_order_namespaces_and_reference_kinds(self):
        for field in ("regions", "frames", "values"):
            record = fixture()
            record["entry"][field].append(copy.deepcopy(record["entry"][field][0]))
            self.reject(record)
        for field in ("regions", "values"):
            record = fixture()
            record["entry"][field].reverse()
            self.reject(record)
        for prefix in ("derived/", "pub/", "prj/"):
            record = fixture()
            record["entry"]["values"][0]["id"] = prefix + "head"
            record["entry"]["values"].sort(key=lambda value: value["id"])
            self.reject(record)
        for name, value in (("frame", "head"), ("sp", "heap"), ("lr", "r1")):
            record = fixture()
            record["entry"][name] = value
            self.reject(record)
        record = fixture()
        record["entry"]["registers"]["r0"] = "heap"
        self.reject(record)

    def test_entry_only_ancestor_graph_and_no_future_storage(self):
        record = fixture()
        record["entry"]["frames"].append({"id": "sibling", "invocation": "helper", "parent": None,
                                            "entry_sp": "stack-pointer", "allocations": [], "saves": []})
        self.reject(record)
        record = fixture()
        add_ancestor(record)
        record["entry"]["frames"][0]["parent"] = "caller-frame"
        self.reject(record)
        record = fixture()
        add_ancestor(record)
        record["entry"]["frames"][0]["allocations"] = []
        self.reject(record)
        record = fixture()
        add_ancestor(record)
        saved = next(region for region in record["entry"]["regions"] if region["id"] == "saved")
        saved["frame"] = "caller-frame"
        record["entry"]["frames"][0]["allocations"] = []
        record["entry"]["frames"][1]["allocations"] = ["saved"]
        self.reject(record)
        for lifetime in ("retired",):
            record = fixture()
            record["entry"]["regions"][0]["lifetime"] = lifetime
            self.reject(record)
        record = fixture()
        record["entry"]["regions"][0]["base"] = {"tag": "allocated", "domain": profile.private.slc("metadata", 0, 40), "clause": "B4"}
        self.reject(record)

    def test_region_bounds_cycles_and_permission(self):
        mutations = [("size", True), ("size", 0), ("size", 2 ** 32), ("permission", "rx"),
                     ("base", {"tag": "relative", "region": "stack", "offset": 0}),
                     ("base", {"tag": "relative", "region": "missing", "offset": 0}),
                     ("base", {"tag": "concrete", "address": 0xFFFFFF00})]
        for name, value in mutations:
            record = fixture()
            next(region for region in record["entry"]["regions"] if region["id"] == "stack")[name] = value
            with self.subTest(name=name, value=value):
                self.reject(record)

    def test_values_fragments_origins_and_no_output_values(self):
        variants = [
            {"id": "r0", "tag": "constant", "width": 1, "value": 256},
            {"id": "r0", "tag": "pointer", "region": "missing", "offset": 0},
            {"id": "r0", "tag": "pointer", "region": "heap", "offset": 4097},
            {"id": "r0", "tag": "condition-word", "clause": "B5", "register": "r1", "excluded": []},
            {"id": "r0", "tag": "symbolic", "width": 4, "origin": {"tag": "register", "invocation": "missing", "register": "r0"}},
            {"id": "r0", "tag": "symbolic", "width": 4, "origin": {"tag": "memory", "region": "heap", "offset": 4096}},
            {"id": "r0", "tag": "bytes", "width": 4, "bytes": [{"tag": "fragment", "value": "r0", "index": 0}] * 4},
            {"id": "r0", "tag": "bytes", "width": 4, "bytes": [{"tag": "fragment", "value": "phase", "index": 2}] * 4},
            {"id": "r0", "tag": "bytes", "width": 4, "bytes": [{"tag": "constant", "value": 0}]},
        ]
        for value in variants:
            record = fixture()
            record["entry"]["values"] = [value if old["id"] == "r0" else old for old in record["entry"]["values"]]
            self.reject(record)
        record = fixture()
        next(value for value in record["entry"]["values"] if value["id"] == "return-control")["target"] = 0x08001000
        self.reject(record)

    def test_cells_and_save_witnesses_are_exact(self):
        for operation in ("width", "overlap", "unknown-origin", "changed-save", "wrong-frame", "duplicate-witness", "namespace"):
            record = fixture()
            add_ancestor(record)
            entry = record["entry"]
            if operation == "width":
                entry["cells"][0]["bytes"].pop()
            elif operation == "overlap":
                entry["cells"].append(copy.deepcopy(entry["cells"][0]))
            elif operation == "unknown-origin":
                entry["cells"][0]["bytes"][0] = {"tag": "unknown", "origin": {"tag": "memory", "region": "missing", "offset": 0}}
            elif operation == "changed-save":
                entry["cells"][0]["bytes"][0] = {"tag": "constant", "value": 0}
            elif operation == "wrong-frame":
                entry["frames"][0]["saves"][0]["location"]["region"] = "heap"
            elif operation == "duplicate-witness":
                entry["frames"][0]["saves"].append(copy.deepcopy(entry["frames"][0]["saves"][0]))
            else:
                entry["frames"][0]["saves"][0]["witness"] = "caller-invocation"
            with self.subTest(operation=operation), self.assertRaises(profile.Failure):
                self.parse(record)

    def test_raw_input_shapes_order_registers_and_narrowing(self):
        valid = [{"role": "count", "register": "r1", "value": "r1"}, {"role": "selector", "register": "r0", "value": "r0"}]
        variants = [valid[::-1], valid[:1], valid + [valid[0]],
                    [valid[0], {"role": "selector", "register": "r1", "value": "r1"}],
                    [{**valid[0], "extra": 0}, valid[1]],
                    [{**valid[0], "register": "sp"}, valid[1]],
                    [{**valid[0], "value": "head"}, valid[1]],
                    [{**valid[0], "role": None}, valid[1]]]
        for raw in variants:
            with self.subTest(raw=raw), self.assertRaises(profile.Failure):
                profile.validate_raw_inputs(self.parse(), raw)
        for tag in ("constant", "bytes", "pointer", "narrow-width", "wrong-origin"):
            record = fixture()
            value = next(item for item in record["entry"]["values"] if item["id"] == "r1")
            if tag == "constant":
                value.clear()
                value.update(id="r1", tag=tag, width=4, value=7)
            elif tag == "bytes":
                value.clear()
                value.update(id="r1", tag=tag, width=4, bytes=[{"tag": "constant", "value": 0}] * 4)
            elif tag == "pointer":
                value.clear()
                value.update(id="r1", tag=tag, region="heap", offset=0)
            elif tag == "narrow-width":
                value["width"] = 1
            else:
                value["origin"]["register"] = "r2"
            with self.subTest(tag=tag), self.assertRaises(profile.Failure):
                profile.validate_raw_inputs(self.parse(record), valid)

    def test_template_cannot_restrict_raw_origin_through_alias_or_fragments(self):
        raw = [{"role": "count", "register": "r1", "value": "r1"}, {"role": "selector", "register": "r0", "value": "r0"}]
        for tag in ("symbolic", "bytes"):
            record = fixture()
            phase = next(value for value in record["entry"]["values"] if value["id"] == "phase")
            if tag == "symbolic":
                phase["origin"] = {"tag": "register", "invocation": record["entry"]["invocation"], "register": "r1"}
            else:
                phase.clear()
                phase.update(id="phase", tag="bytes", width=2,
                             bytes=[{"tag": "fragment", "value": "r0", "index": index} for index in range(2)])
            with self.subTest(tag=tag), self.assertRaisesRegex(profile.Failure, "template restricts raw input"):
                profile.validate_raw_inputs(self.parse(record), raw)

    def test_template_storage_cannot_narrow_raw_roots(self):
        raw = [{"role": "count", "register": "r1", "value": "r1"}, {"role": "selector", "register": "r0", "value": "r0"}]
        for region in ("manager-cell", "image"):
            record = fixture()
            record["entry"]["cells"] = [{"location": profile.private.slc(region, 0, 1),
                                          "bytes": [{"tag": "unknown", "origin": {"tag": "register",
                                                     "invocation": record["entry"]["invocation"], "register": "r1"}}]}]
            with self.subTest(region=region), self.assertRaisesRegex(profile.Failure, "storage restricts raw input"):
                profile.validate_raw_inputs(self.parse(record), raw)
        record = fixture()
        next(value for value in record["entry"]["values"] if value["id"] == "phase")["origin"] = {
            "tag": "memory", "region": "heap", "offset": 100}
        record["entry"]["cells"] = [{"location": profile.private.slc("heap", 100, 1),
                                      "bytes": [{"tag": "fragment", "value": "r0", "index": 0}]}]
        with self.assertRaisesRegex(profile.Failure, "template restricts raw input"):
            profile.validate_raw_inputs(self.parse(record), raw)

    def test_public_domain_boundaries(self):
        positives = {"U8": [0, 255], "U16": [0, 65535], "U32": [0, 0xFFFFFFFF],
                     "Count": [0], "I32": [-0x80000000, 0x7FFFFFFF], "Text": ["text", "é"],
                     "RelPath": ["src/08000002.c"], "HostPath": ["/usr/bin/tool"],
                     "Hex4": ["000000ff"], "BodyID": ["body/08000002"], "DataRegister": ["r0", "r12"]}
        for spec, values in positives.items():
            for value in values:
                profile.validate(value, spec)
        negatives = {"U8": [256, True], "U16": [65536, 1.0], "Count": [-1], "Text": ["", "a\x00", "a\x7f", "a\n", "a`", "\ud800"],
                     "RelPath": ["a//b", "a/./b", "a/../b", "/a", "a/", "a\\b"],
                     "HostPath": ["a/b", "/", "/a/../b"], "Hex4": ["FF000000", "00", None],
                     "BodyID": ["body/08000003", "body/0800000a", "body/09000000"], "DataRegister": ["sp", "lr"]}
        for spec, values in negatives.items():
            for value in values:
                with self.subTest(spec=spec, value=repr(value)), self.assertRaises(profile.Failure):
                    profile.validate(value, spec)

    def test_private_bytes_and_eligibility_are_unchanged(self):
        path = Path(profile.private.__file__)
        self.assertEqual(hashlib.sha256(path.read_bytes()).hexdigest(), DEPENDENCY_SHA256)
        self.assertFalse(profile.private.CANONICAL_REPORT_ELIGIBLE)

    def test_parsing_never_constructs_or_executes_private_checker(self):
        with patch.object(profile.private.Checker, "__init__", side_effect=AssertionError("private execution")), \
                patch.object(profile.private, "check_registration", side_effect=AssertionError("private bridge")), \
                patch.object(profile.private, "recheck", side_effect=AssertionError("private replay")):
            request = self.parse()
            profile.validate_raw_inputs(request, [{"role": "count", "register": "r1", "value": "r1"},
                                                  {"role": "selector", "register": "r0", "value": "r0"}])


class AcquisitionTests(unittest.TestCase):
    def setUp(self):
        SCRATCH.mkdir(parents=True, exist_ok=True)
        self.directory = tempfile.TemporaryDirectory(prefix="probe-", dir=SCRATCH)
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.game = self.root / "game"
        self.kit = self.root / "kit"
        self.game.mkdir()
        self.kit.mkdir()
        (self.game / "src").mkdir()
        (self.game / "include").mkdir()
        (self.game / "src" / f"{ADDRESS:08X}.c").write_text("void f(void) {}\n")
        (self.game / "include" / "fixture.h").write_text("typedef unsigned int u32;\n")
        (self.game / "item").write_bytes(b"original")
        self.capture = profile.Acquisition(game_root=self.game, kit_root=self.kit)
        self.addCleanup(self.capture.close)

    def acquire(self, name="item"):
        return self.capture.acquire({"root": "game", "path": name})

    def test_regular_capture_pins_validated_bytes_and_final_check(self):
        artifact = self.acquire()
        self.assertEqual(artifact.data, b"original")
        self.assertEqual(artifact.path_pin, {"path": {"root": "game", "path": "item"},
                                           "pin": profile.private.pin(b"original")})
        self.capture.recheck()
        self.assertIs(self.acquire(), artifact)

    def test_cached_identity_preserves_each_requested_path_representation(self):
        source = self.game / "src" / f"{ADDRESS:08X}.c"
        host = {"root": "host", "path": str(source)}
        game = {"root": "game", "path": f"src/{ADDRESS:08X}.c"}
        for first, second in ((host, game), (game, host)):
            with self.subTest(first=first["root"]):
                with profile.Acquisition(game_root=self.game, kit_root=self.kit) as capture:
                    initial = capture.acquire(first)
                    repeated = capture.acquire(second)
                    self.assertEqual(initial.path_pin["path"], first)
                    self.assertEqual(repeated.path_pin["path"], second)
                    self.assertEqual(initial.data, repeated.data)
                    self.assertEqual(len(capture.files), 1)
                    addressed, artifacts = capture.sources(ADDRESS)
                    self.assertEqual(addressed, game["path"])
                    self.assertTrue(all(item.path_pin["path"]["root"] == "game" for item in artifacts))
                    self.assertIn(game, [item.path_pin["path"] for item in artifacts])
                    capture.recheck()

    def test_all_input_and_output_roles_use_same_identity_boundary(self):
        paths = ["context.json", "functions.json", "functions.txt", "ffta.sym", "data_symbols.json",
                 "rom.gba", "engine.py", "capstone-native.so", "allowance.json", "raw.s", "original.o",
                 "linked.elf", "payload.bin", "report.md"]
        for name in paths:
            (self.game / name).write_bytes(b"bound bytes")
        for name in paths:
            artifact = self.acquire(name)
            self.assertEqual(artifact.data, b"bound bytes")
        replacement = self.root / "replacement"
        replacement.write_bytes(b"bound bytes")
        os.replace(replacement, self.game / paths[-1])
        with self.assertRaises(profile.Failure):
            self.capture.recheck()

    def test_nonregular_acquisition_is_bounded(self):
        for kind in ("fifo", "socket", "directory", "symlink"):
            with self.subTest(kind=kind):
                path = self.game / kind
                connection = None
                if kind == "fifo":
                    os.mkfifo(path)
                elif kind == "socket":
                    connection = bound_socket(path)
                elif kind == "directory":
                    path.mkdir()
                else:
                    path.symlink_to("item")
                old_handler = signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(AssertionError("nonregular read blocked")))
                signal.alarm(2)
                try:
                    with profile.Acquisition(game_root=self.game, kit_root=self.kit) as capture:
                        with self.assertRaises(profile.Failure):
                            capture.acquire({"root": "game", "path": kind})
                finally:
                    signal.alarm(0)
                    signal.signal(signal.SIGALRM, old_handler)
                    if connection is not None:
                        connection.close()

    def test_same_byte_inode_replacement_is_drift(self):
        replacement = self.game / "replacement"
        replacement.write_bytes(b"original")
        self.acquire()
        os.replace(replacement, self.game / "item")
        with self.assertRaises(profile.Failure):
            self.capture.recheck()

    def test_descriptor_replacement_during_read_is_drift(self):
        replacement = self.game / "replacement"
        replacement.write_bytes(b"original")
        original_read = self.capture._read

        def replace(descriptor, size):
            data = original_read(descriptor, size)
            os.replace(replacement, self.game / "item")
            return data

        with patch.object(self.capture, "_read", side_effect=replace):
            with self.assertRaises(profile.Failure):
                self.acquire()

    def test_mutation_during_read_and_at_final_boundary(self):
        original_read = self.capture._read

        def mutate(descriptor, size):
            data = original_read(descriptor, size)
            (self.game / "item").write_bytes(b"changed!")
            return data

        with patch.object(self.capture, "_read", side_effect=mutate):
            with self.assertRaises(profile.Failure):
                self.acquire()
        self.capture.close()
        with profile.Acquisition(game_root=self.game, kit_root=self.kit) as capture:
            capture.acquire({"root": "game", "path": "item"})
            (self.game / "item").write_bytes(b"changed again")
            with self.assertRaises(profile.Failure):
                capture.recheck()

    def test_same_byte_replacement_during_final_read_is_drift(self):
        replacement = self.game / "replacement"
        replacement.write_bytes(b"original")
        self.acquire()
        original_read = self.capture._read

        def replace(descriptor, size):
            data = original_read(descriptor, size)
            os.replace(replacement, self.game / "item")
            return data

        with patch.object(self.capture, "_read", side_effect=replace):
            with self.assertRaises(profile.Failure):
                self.capture.recheck()

    def test_later_final_read_mutating_earlier_file_in_place_is_drift(self):
        later = self.game / "later"
        later.write_bytes(b"later bytes")
        self.acquire()
        self.acquire("later")
        self.capture.recheck()  # The no-mutation control remains valid.
        before = (self.game / "item").stat()
        parent_before = self.game.stat()
        last_descriptor = self.capture.files[later][0]
        original_read = self.capture._read

        def mutate_earlier(descriptor, size):
            data = original_read(descriptor, size)
            if descriptor == last_descriptor:
                (self.game / "item").write_bytes(b"changed!")
            return data

        with patch.object(self.capture, "_read", side_effect=mutate_earlier):
            with self.assertRaisesRegex(profile.Failure, "identity drift after final reads"):
                self.capture.recheck()
        after = (self.game / "item").stat()
        self.assertEqual((before.st_dev, before.st_ino, before.st_size),
                         (after.st_dev, after.st_ino, after.st_size))
        self.assertEqual(profile._identity(parent_before), profile._identity(self.game.stat()))

    def test_file_growth_is_bounded_by_acquired_size(self):
        original_read = self.capture._read

        def grow(descriptor, size):
            with (self.game / "item").open("ab") as stream:
                stream.write(b"extra bytes")
            data = original_read(descriptor, size)
            self.assertLessEqual(len(data), size + 1)
            return data

        with patch.object(self.capture, "_read", side_effect=grow):
            with self.assertRaises(profile.Failure):
                self.acquire()

    def test_parent_membership_and_same_byte_directory_replacement(self):
        self.acquire()
        (self.game / "new-candidate").write_text("new\n")
        with self.assertRaises(profile.Failure):
            self.capture.recheck()
        self.capture.close()
        with profile.Acquisition(game_root=self.game, kit_root=self.kit) as capture:
            capture.acquire({"root": "game", "path": "item"})
            moved = self.root / "moved-game"
            self.game.rename(moved)
            shutil.copytree(moved, self.game)
            with self.assertRaises(profile.Failure):
                capture.recheck()

    def test_parent_symlink_is_rejected_initially_and_after_acquisition(self):
        nested = self.game / "nested"
        nested.mkdir()
        (nested / "file").write_text("ordinary\n")
        alias = self.game / "alias"
        alias.symlink_to("nested", target_is_directory=True)
        with self.assertRaises(profile.Failure):
            self.acquire("alias/file")
        self.capture.close()
        with profile.Acquisition(game_root=self.game, kit_root=self.kit) as capture:
            capture.acquire({"root": "game", "path": "nested/file"})
            nested.rename(self.game / "old-nested")
            nested.symlink_to("old-nested", target_is_directory=True)
            with self.assertRaises(profile.Failure):
                capture.recheck()

    def test_source_inventory_is_complete_and_unique(self):
        (self.game / "include" / "extensionless").write_text("included\n")
        (self.game / "src" / "nested").mkdir()
        (self.game / "src" / "nested" / "helper.h").write_text("header\n")
        (self.game / "src" / "unrelated.c").write_text("unrelated\n")
        source, artifacts = self.capture.sources(ADDRESS)
        self.assertEqual(source, f"src/{ADDRESS:08X}.c")
        self.assertEqual([json.loads(item.path_json)["path"] for item in artifacts],
                         ["include/extensionless", "include/fixture.h", f"src/{ADDRESS:08X}.c", "src/nested/helper.h"])
        self.capture.recheck()
        (self.game / "src" / "nested" / f"{ADDRESS:08X}.c").write_text("duplicate\n")
        with self.assertRaises(profile.Failure):
            self.capture.recheck()
        with profile.Acquisition(game_root=self.game, kit_root=self.kit) as capture:
            with self.assertRaisesRegex(profile.Failure, "ambiguous"):
                capture.sources(ADDRESS)

    def test_nonregular_source_and_header_candidates_are_never_filtered(self):
        for directory, name in (("src", f"{ADDRESS:08X}.c"), ("src", "hidden.h"), ("include", "hidden")):
            for kind in ("fifo", "symlink", "socket", "directory"):
                if directory == "include" and kind == "directory":
                    continue  # Include subdirectories are traversed, rather than file candidates.
                with self.subTest(directory=directory, kind=kind):
                    candidate = self.game / directory / name
                    if candidate.exists():
                        candidate.unlink()
                    connection = None
                    if kind == "fifo":
                        os.mkfifo(candidate)
                    elif kind == "symlink":
                        candidate.symlink_to("../item")
                    elif kind == "socket":
                        connection = bound_socket(candidate)
                    else:
                        candidate.mkdir()
                    old_handler = signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(AssertionError("candidate capture blocked")))
                    signal.alarm(2)
                    try:
                        with profile.Acquisition(game_root=self.game, kit_root=self.kit) as capture:
                            with self.assertRaises(profile.Failure):
                                capture.sources(ADDRESS)
                    finally:
                        signal.alarm(0)
                        signal.signal(signal.SIGALRM, old_handler)
                        if connection is not None:
                            connection.close()
                        if kind == "directory":
                            candidate.rmdir()
                        else:
                            candidate.unlink()
                        if name == f"{ADDRESS:08X}.c":
                            candidate.write_text("void f(void) {}\n")

    def test_inventory_detects_header_bytes_replacement_and_membership_drift(self):
        replacement = self.game / "include" / "replacement"
        replacement.write_text("typedef unsigned int u32;\n")
        self.capture.sources(ADDRESS)
        os.replace(replacement, self.game / "include" / "fixture.h")
        with self.assertRaises(profile.Failure):
            self.capture.recheck()

    def test_optional_absence_and_absent_include_are_rechecked(self):
        self.assertIsNone(self.capture.optional({"root": "game", "path": "allowance.json"}))
        (self.game / "allowance.json").write_text("{}\n")
        with self.assertRaises(profile.Failure):
            self.capture.recheck()
        self.capture.close()
        shutil.rmtree(self.game / "include")
        with profile.Acquisition(game_root=self.game, kit_root=self.kit) as capture:
            capture.sources(ADDRESS)
            (self.game / "include").mkdir()
            with self.assertRaises(profile.Failure):
                capture.recheck()

    def test_tool_symlink_chain_is_captured_and_final_drift_rejects(self):
        tools = self.root / "fixed-tools"
        tools.mkdir()
        executable = tools / "compiler-real"
        executable.write_text("#!/bin/sh\nexit 0\n")
        executable.chmod(0o755)
        (tools / "cpp-middle").symlink_to("compiler-real")
        (tools / "cpp").symlink_to("cpp-middle")
        with patch.dict(os.environ, {"PATH": str(tools)}):
            tool = self.capture.tool("cpp")
            self.assertEqual(tool["resolved"], str(executable))
            self.assertEqual(tool["spelling"], "cpp")
            self.assertEqual(tool["resolution"], [{"path": str(tools / "cpp"), "target": "cpp-middle"},
                                                   {"path": str(tools / "cpp-middle"), "target": "compiler-real"}])
            self.capture.recheck()
            (tools / "cpp").unlink()
            (tools / "cpp").symlink_to("compiler-real")
            with self.assertRaises(profile.Failure):
                self.capture.recheck()

    def test_fixed_tool_resolution_or_environment_drift_rejects(self):
        tools = self.root / "tools"
        tools.mkdir()
        for name in ("cpp", "other"):
            (tools / name).write_text("#!/bin/sh\nexit 0\n")
            (tools / name).chmod(0o755)
        with patch.dict(os.environ, {"PATH": str(tools)}):
            self.capture.tool("cpp")
            os.environ["PATH"] = str(tools) + ":/usr/bin"
            with self.assertRaises(profile.Failure):
                self.capture.recheck()
        with self.assertRaises(profile.Failure):
            self.capture.tool("request-selected-command")

    def test_closed_acquisition_and_empty_pin_refuse(self):
        (self.game / "empty").write_bytes(b"")
        with self.assertRaises(profile.Failure):
            self.acquire("empty")
        self.capture.close()
        with self.assertRaises(profile.Failure):
            self.capture.recheck()


class FreshCaptureTests(unittest.TestCase):
    """Every positive invokes all seven commands again from genuine C."""

    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory(prefix="fresh-matrix-", dir=SCRATCH)
        cls.root = Path(cls.temporary.name)
        cls.kit = Path(__file__).resolve().parents[1]
        cls.workspace = cls.root / "work"
        cls.workspace.mkdir()
        cls.cases = []
        fixtures = cls.kit / "tests/fixtures/conditional_registration_profile"
        try:
            for layout, origin, size, call in (("compact", 0, 228, 0xC8), ("compact", 2, 230, 0xCA),
                                               ("expanded", 0, 428, 0x18A), ("expanded", 2, 426, 0x188)):
                address = profile.ROM_BASE + origin
                game = cls.root / f"{layout}-{origin}"
                for path in ("src", "include", "config/conditional_registration", "symbols", "prepare"):
                    (game / path).mkdir(parents=True, exist_ok=True)
                source = (fixtures / (layout + ".c")).read_bytes().replace(b"func_08000000", f"func_{address:08X}".encode())
                (game / f"src/{address:08X}.c").write_bytes(source)
                (game / "include/fixture.h").write_bytes((fixtures / "fixture.h").read_bytes())
                names = sorted(set(profile.re.findall(r"synthetic_[a-z]+(?:_[0-5])?", source.decode())) |
                               {"synthetic_callback", "synthetic_registration"})
                bindings = [{"name": name, "kind": "function", "target": 0x08010000 + index * 0x100}
                            for index, name in enumerate(names)]
                bindings.append({"name": "manager_cell", "kind": "object", "target": 0x0200F430})
                bindings.sort(key=lambda item: item["name"])
                entries = [{"rom": f"0x{address:08X}", "end": f"0x{address + size:08X}", "mode": "thumb"}]
                entries += [{"rom": f"0x{item['target']:08X}", "end": f"0x{item['target'] + 2:08X}", "mode": "thumb"}
                            for item in bindings if item["kind"] == "function"]
                (game / "config/functions.json").write_bytes(encoded(entries))
                (game / "symbols/functions.txt").write_text("".join(
                    f"{entry['rom']} {entry['end']} {int(entry['end'], 16) - int(entry['rom'], 16)}\n" for entry in entries))
                (game / "symbols/ffta.sym").write_text(
                    f"0x{address:08X} {size:06X} func_{address:08X}\n" + "".join(
                        f"0x{item['target']:08X} 000002 {item['name']}\n" for item in bindings if item["kind"] == "function"))
                (game / "config/data_symbols.json").write_bytes(encoded({"manager_cell": "0x0200F430"}))
                request = fixture()
                request.update(address=address, site=address + call)
                (game / profile.context_path(address)).write_bytes(encoded(request))
                # Prepare synthetic trust from a separate, fresh source build.
                # Its binaries are never inputs to the positive capture API.
                prepare = game / "prepare"
                tools = {role: os.path.expandvars(spelling) for role, spelling in profile.TOOL_SPELLINGS}

                def run(role, *arguments):
                    profile._run([tools[role], *map(str, arguments)], game, prepare)

                run("cpp", "-nostdinc", "-undef", "-I", "include", f"src/{address:08X}.c", "-o", prepare / "caller.i")
                run("cc", *profile.FLAGS.split(), prepare / "caller.i", "-o", prepare / "caller.raw.s")
                placed = profile.place_registration((prepare / "caller.raw.s").read_bytes(), address,
                                                    {item["name"]: item for item in bindings})
                (prepare / "caller.s").write_bytes(placed)
                run("assembler", "-mthumb-interwork", prepare / "caller.s", "-o", prepare / "caller.o")
                (prepare / "bindings.s").write_bytes(profile._binding_assembly(bindings))
                run("assembler", "-mthumb-interwork", prepare / "bindings.s", "-o", prepare / "bindings.o")
                (prepare / "caller.ld").write_bytes(profile._linker_script(address))
                run("linker", "--fatal-warnings", "--no-undefined", "--no-relax", "--orphan-handling=error", "-T",
                    prepare / "caller.ld", "-e", f"func_{address:08X}", prepare / "caller.o", prepare / "bindings.o", "-o", prepare / "caller.elf")
                run("objcopy", "-O", "binary", "--only-section=.text", prepare / "caller.elf", prepare / "caller.bin")
                image = (prepare / "caller.bin").read_bytes()
                rom = bytearray(0x20000)
                rom[origin:origin + size] = image[origin:origin + size]
                for item in bindings:
                    if item["kind"] == "function":
                        offset = item["target"] - profile.ROM_BASE
                        rom[offset:offset + 2] = bytes.fromhex("7047")
                (game / "baserom.bin").write_bytes(rom)
                shutil.rmtree(prepare)
                cls.cases.append((layout, address, size, game, bytes(rom)))
        except BaseException:
            cls.temporary.cleanup()
            raise

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def capture(self, case=None):
        layout, address, size, game, rom = case or self.cases[0]
        with patch.object(profile, "ROM_SIZE", len(rom)), patch.object(profile, "ROM_SHA1", hashlib.sha1(rom).hexdigest()), \
                patch.dict(os.environ, {"FFTA_ROM": str(game / "baserom.bin")}, clear=False):
            with profile.Acquisition(game_root=game, kit_root=self.kit) as acquisition:
                return profile.capture_caller(acquisition, address, self.workspace)

    def test_four_fresh_natural_captures(self):
        for case in self.cases:
            layout, address, size, game, rom = case
            with self.subTest(layout=layout, origin=address % 4):
                capture = self.capture(case)
                result = capture.to_dict()
                self.assertEqual(len(capture.commands), 7)
                self.assertTrue(all(command[1] == 0 for command in capture.commands))
                self.assertEqual(result["caller"]["end"] - address, size)
                self.assertEqual(result["switch"]["layout"], "bhi" if layout == "compact" else "bls-b")
                self.assertEqual(len(result["relocations"]), 16 if layout == "compact" else 46)
                self.assertEqual(result["placement"]["prefix_size"], address % 4)
                self.assertEqual(result["placement"]["suffix_size"], 0)
                artifacts = dict(capture.artifacts)
                body = artifacts["linked_binary"][address % 4:address % 4 + size]
                self.assertEqual(body, rom[address - profile.ROM_BASE:address - profile.ROM_BASE + size])
                spans = sorted(
                    (span for key in ("code", "literals", "alignment") for span in result["caller"][key]), key=lambda span: span["start"])
                self.assertEqual([spans[0]["start"], spans[-1]["end"]], [address, address + size])
                self.assertTrue(all(a["end"] == b["start"] for a, b in zip(spans, spans[1:])))
                original = profile._elf(artifacts["original_elf"])
                binding = profile._elf(artifacts["binding_elf"])
                linked = profile._elf(artifacts["linked_elf"])
                for relocation in result["relocations"]:
                    section, index = relocation["section_index"], relocation["entry_index"]
                    self.assertEqual(original["section_data"][section][index * 8:index * 8 + 8].hex(), relocation["raw_record"])
                    symbol = relocation["symbol"]
                    self.assertEqual(profile.raw_symbol(original, symbol["table_section_index"], symbol["index"]), symbol)
                    if symbol["name"]:
                        self.assertEqual(symbol["info"], 0x10)
                for item in result["placement"]["bindings"]:
                    for image, key in ((binding, "symbol"), (linked, "linked_symbol")):
                        symbol = item[key]
                        self.assertEqual(profile.raw_symbol(image, symbol["table_section_index"], symbol["index"]), symbol)
                        self.assertEqual(symbol["info"], 0x11 if item["kind"] == "object" else 0x12)
                self.assertEqual(list(self.workspace.iterdir()), [])
                self.assertFalse(profile.CANONICAL_REPORT_ELIGIBLE)
                destination = os.environ.get("FFTA_REGISTRATION_CAPTURE_EVIDENCE")
                if destination:
                    directory = Path(destination) / f"{layout}-{address:08X}"
                    directory.mkdir(parents=True, exist_ok=False)
                    for name, data in capture.artifacts:
                        (directory / name).write_bytes(data)
                    (directory / "capture.json").write_bytes(encoded(result))
                    (directory / "commands.json").write_bytes(encoded(capture.commands))
                    (directory / "request.json").write_bytes(capture.fixed.request.file_bytes)
                    for role, artifact in capture.fixed.maps:
                        (directory / role).write_bytes(artifact.data)
                    for artifact in capture.fixed.sources:
                        path = directory / profile.private.decode(artifact.path_json)["path"]
                        path.parent.mkdir(parents=True, exist_ok=True)
                        path.write_bytes(artifact.data)

    def fixed(self, acquisition):
        _, address, _, game, rom = self.cases[0]
        with patch.object(profile, "ROM_SIZE", len(rom)), patch.object(profile, "ROM_SHA1", hashlib.sha1(rom).hexdigest()), \
                patch.dict(os.environ, {"FFTA_ROM": str(game / "baserom.bin")}):
            return profile.acquire_fixed_inputs(acquisition, address)

    def test_fixed_inputs_capture_exact_domains_and_selection(self):
        _, address, _, game, _ = self.cases[0]
        with profile.Acquisition(game_root=game, kit_root=self.kit) as acquisition:
            fixed = self.fixed(acquisition)
            result = fixed.to_dict()
            self.assertEqual([item["path"]["path"] for item in result["sources"]],
                             ["include/fixture.h", f"src/{address:08X}.c"])
            self.assertEqual({key: value["path"]["path"] for key, value in result["maps"].items()}, dict(profile.MAP_PATHS))
            self.assertEqual([item["role"] for item in result["tools"]], [role for role, _ in profile.TOOL_SPELLINGS])
            self.assertEqual(result["rom_selection"]["root_names"], ["baserom.bin"])
            self.assertEqual(result["rom_selection"]["chosen"], result["rom"]["path"])
            self.assertEqual(result["rom_selection"]["candidates"], [result["rom"]])
            engine = [item["path"]["path"] for item in result["engine"]]
            for name in ("match.py", "match_evidence.py", "status.py", "rebuild.py", "push.py",
                         "conditional_registration_profile.py", "conditional_registration_effects.py"):
                self.assertIn("tools/" + name, engine)
            self.assertTrue(any("capstone" in path and ".so" in path for path in engine))

    def test_rom_hidden_nonregular_candidates_are_not_skipped(self):
        game = self.cases[0][3]
        for kind in ("fifo", "directory", "symlink", "socket"):
            with self.subTest(kind=kind):
                path = game / "hidden.GbA"
                connection = None
                if kind == "fifo":
                    os.mkfifo(path)
                elif kind == "directory":
                    path.mkdir()
                elif kind == "symlink":
                    path.symlink_to(game / "baserom.bin")
                else:
                    connection = bound_socket(path)
                try:
                    with profile.Acquisition(game_root=game, kit_root=self.kit) as acquisition, \
                            self.assertRaises(profile.Failure):
                        self.fixed(acquisition)
                finally:
                    if connection:
                        connection.close()
                    path.rmdir() if kind == "directory" else path.unlink()

    def test_rom_environment_trust_and_final_selection_drift(self):
        _, address, _, game, rom = self.cases[0]
        with profile.Acquisition(game_root=game, kit_root=self.kit) as acquisition, \
                patch.dict(os.environ, {"FFTA_ROM": str(game / "baserom.bin")}), self.assertRaisesRegex(profile.Failure, "untrusted ROM"):
            profile._rom(acquisition)
        for selection in ("", str(game / "missing.bin")):
            with self.subTest(selection=selection), profile.Acquisition(game_root=game, kit_root=self.kit) as acquisition, \
                    patch.dict(os.environ, {"FFTA_ROM": selection}), self.assertRaises(profile.Failure):
                profile._rom(acquisition)
        with profile.Acquisition(game_root=game, kit_root=self.kit) as acquisition, \
                patch.object(profile, "ROM_SIZE", len(rom)), patch.object(profile, "ROM_SHA1", hashlib.sha1(rom).hexdigest()), \
                patch.dict(os.environ, {"FFTA_ROM": str(game / "baserom.bin")}):
            profile._rom(acquisition)
            os.environ["FFTA_ROM"] = str(game / "different.bin")
            with self.assertRaisesRegex(profile.Failure, "environment selection drift"):
                acquisition.recheck()

    def test_rom_ambiguous_fallback_and_candidate_membership_drift(self):
        with tempfile.TemporaryDirectory(prefix="rom-selection-", dir=SCRATCH) as temporary:
            game = Path(temporary)
            (game / "a.gba").write_bytes(b"a")
            (game / "b.gba").write_bytes(b"b")
            with patch.dict(os.environ, clear=False):
                os.environ.pop("FFTA_ROM", None)
                with profile.Acquisition(game_root=game, kit_root=self.kit) as acquisition, \
                        self.assertRaisesRegex(profile.Failure, "ambiguous"):
                    profile._rom(acquisition)
                (game / "b.gba").unlink()
                with profile.Acquisition(game_root=game, kit_root=self.kit) as acquisition, \
                        patch.object(profile, "ROM_SIZE", 1), patch.object(profile, "ROM_SHA1", hashlib.sha1(b"a").hexdigest()):
                    selected, selection = profile._rom(acquisition)
                    self.assertEqual(selection["chosen"]["path"], "a.gba")
                    self.assertEqual(selected.data, b"a")
                    (game / "b.gba").write_bytes(b"b")
                    with self.assertRaises(profile.Failure):
                        acquisition.recheck()

    def test_present_allowance_and_source_implausibility_refuse(self):
        game = self.cases[0][3]
        with tempfile.TemporaryDirectory(prefix="allowance-", dir=SCRATCH) as temporary:
            path = Path(temporary) / "allow.json"
            path.write_bytes(encoded({"entries": [{"address": "08000000"}]}))
            with patch.dict(os.environ, {"FFTA_ASM_ALLOW": str(path)}), \
                    profile.Acquisition(game_root=game, kit_root=self.kit) as acquisition, \
                    self.assertRaisesRegex(profile.Failure, "assembly allowance"):
                self.fixed(acquisition)
        source = game / "src/08000000.c"
        original = source.read_bytes()
        try:
            source.write_bytes(original + b'\nasm("nop");\n')
            with profile.Acquisition(game_root=game, kit_root=self.kit) as acquisition, \
                    self.assertRaisesRegex(profile.Failure, "implausible"):
                self.fixed(acquisition)
        finally:
            source.write_bytes(original)

    def test_dependency_escape_and_external_word_grammar_refuse(self):
        capture = self.capture()
        fixed = capture.fixed
        with self.assertRaisesRegex(profile.Failure, "untracked"):
            profile._dependencies(b'# 1 "../outside.h"\n', fixed.source, fixed.sources, Path("/captured"))
        with self.assertRaisesRegex(profile.Failure, "source marker"):
            profile._dependencies(b"int x;\n", fixed.source, fixed.sources, Path("/captured"))
        raw = dict(capture.artifacts)["raw_assembly"]
        names = {item["name"]: item for item in capture.to_dict()["placement"]["bindings"]}
        for replacement in (b"unmapped_symbol", b"manager_cell+4", b"manager_cell-4", b"manager_cell@GOT"):
            with self.subTest(replacement=replacement), self.assertRaises(profile.Failure):
                profile.place_registration(raw.replace(b".word\tmanager_cell", b".word\t" + replacement), capture.fixed.address, names)

    def inspection(self, capture):
        artifacts, result = dict(capture.artifacts), capture.to_dict()
        original = profile._elf(artifacts["original_elf"])
        size = result["caller"]["end"] - capture.fixed.address
        labels, records = profile._partition(artifacts["placed_assembly"], original, capture.fixed.address, size)
        named, objects = profile._maps(capture.fixed)
        return artifacts, result, original, size, labels, records, named, objects

    def test_genuine_raw_records_reject_type_info_index_and_patch_mutations(self):
        capture = self.capture()
        artifacts, result, image, size, labels, records, named, objects = self.inspection(capture)
        address = capture.fixed.address
        callback = next(item for item in result["relocations"] if item["resolved"]["tag"] == "function" and item["kind"] == 2)
        symbol = callback["symbol"]
        table_offset = image["sections"][symbol["table_section_index"]][4] + symbol["index"] * 16
        rel_offset = image["sections"][callback["section_index"]][4] + callback["entry_index"] * 8
        mutations = []
        for offset, value in ((table_offset + 12, 0x11), (table_offset + 13, 2)):
            data = bytearray(artifacts["original_elf"])
            data[offset] = value
            mutations.append(bytes(data))
        for field_offset, value in ((rel_offset + 4, callback["raw_info"] ^ 1),
                                    (rel_offset + 4, (0xFFFFFF << 8) | 2), (rel_offset, 0)):
            data = bytearray(artifacts["original_elf"])
            struct.pack_into("<I", data, field_offset, value)
            mutations.append(bytes(data))
        for data in mutations:
            with self.subTest(digest=hashlib.sha256(data).hexdigest()), self.assertRaises(profile.Failure):
                altered = profile._elf(data)
                profile._original_relocations(altered, address, size, labels, records, named, objects, capture.fixed.request.to_dict()["site"])

    def test_missing_duplicate_overlapping_and_wrong_table_relocations_refuse(self):
        capture = self.capture()
        artifacts, result, image, size, labels, records, named, objects = self.inspection(capture)
        section_index = image["relocations"][0]
        section = image["sections"][section_index]
        variants = []
        missing = copy.deepcopy(image)
        missing["section_data"][section_index] = missing["section_data"][section_index][8:]
        variants.append(missing)
        duplicate = copy.deepcopy(image)
        duplicate["section_data"][section_index] += duplicate["section_data"][section_index][:8]
        variants.append(duplicate)
        overlap = copy.deepcopy(image)
        data = bytearray(overlap["section_data"][section_index])
        struct.pack_into("<I", data, 8, struct.unpack_from("<I", data)[0] + 2)
        overlap["section_data"][section_index] = bytes(data)
        variants.append(overlap)
        for field in (6, 7):
            wrong = copy.deepcopy(image)
            changed = list(section)
            changed[field] = 0
            wrong["sections"][section_index] = tuple(changed)
            variants.append(wrong)
        for altered in variants:
            with self.assertRaises(profile.Failure):
                profile._original_relocations(altered, capture.fixed.address, size, labels, records, named, objects,
                                               capture.fixed.request.to_dict()["site"])

    def test_wrong_binding_extra_owner_prefix_suffix_and_nonrelocated_byte_refuse(self):
        capture = self.capture()
        artifacts, result, original, size, labels, records, named, objects = self.inspection(capture)
        bindings = result["placement"]["bindings"]
        binding_image = profile._elf(artifacts["binding_elf"])
        symbol = bindings[0]["symbol"]
        location = binding_image["sections"][symbol["table_section_index"]][4] + symbol["index"] * 16
        for offset, value in ((location + 8, 3), (location + 12, 0x10)):
            data = bytearray(artifacts["binding_elf"])
            if offset == location + 8:
                struct.pack_into("<I", data, offset, value)
            else:
                data[offset] = value
            with self.assertRaises(profile.Failure):
                profile._symbol_ownership(profile._elf(data), capture.fixed.address, size, bindings, records, stage="binding")
        extra = copy.deepcopy(original)
        table = next(iter(extra["symbol_tables"]))
        extra["symbol_tables"][table][-1]["name"] = "unowned_definition"
        with self.assertRaises(profile.Failure):
            profile._symbol_ownership(extra, capture.fixed.address, size, bindings, records, stage="original")
        for suffix in (b"\xc0\x46", b"\x01\x00", b"\x00" * 4):
            altered = copy.deepcopy(original)
            altered["text"] += suffix
            with self.assertRaises(profile.Failure):
                profile._envelope(altered, capture.fixed.address, linked=False)
        padded = copy.deepcopy(original)
        caller = next(symbol for symbol in padded["symbols"] if symbol["name"] == "func_08000000")
        caller["size"] -= 2
        padded["text"] = padded["text"][:-2] + bytes(2)
        self.assertEqual(profile._envelope(padded, capture.fixed.address, linked=False), (size - 2, 2))
        for suffix in (b"\xc0\x46", b"\x01\x00"):
            padded["text"] = padded["text"][:-2] + suffix
            with self.assertRaises(profile.Failure):
                profile._envelope(padded, capture.fixed.address, linked=False)
        linked = profile._elf(artifacts["linked_elf"])
        altered = copy.deepcopy(linked)
        changed = bytearray(altered["text"])
        changed[0] ^= 1
        altered["text"] = bytes(changed)
        with self.assertRaisesRegex(profile.Failure, "nonrelocated"):
            profile._linked_records(original, altered, capture.fixed.address, copy.deepcopy(result["relocations"]), records)
        prefixed = self.capture(self.cases[1])
        image = profile._elf(dict(prefixed.artifacts)["original_elf"])
        image["text"] = b"\xc0\x46" + image["text"][2:]
        with self.assertRaises(profile.Failure):
            profile._envelope(image, prefixed.fixed.address, linked=False)

    def test_failed_tool_and_output_fifo_cleanup_and_final_input_drift(self):
        original_run = profile._run
        game = self.cases[0][3]
        source = game / "src/08000000.c"
        saved = source.read_bytes()
        for attack in ("failure", "fifo", "input-drift", "tail", "original-replacement", "linked-replacement"):
            with self.subTest(attack=attack):
                def hostile(command, root, temporary):
                    if attack == "failure":
                        raise profile.Failure("identity", "injected fixed tool failure")
                    completed = original_run(command, root, temporary)
                    output = Path(command[-1])
                    if attack == "fifo" and output.name == "caller.i":
                        output.unlink()
                        os.mkfifo(output)
                    elif attack == "input-drift" and output.name == "caller.i":
                        source.write_bytes(saved + b"\n")
                    elif attack == "tail" and output.name == "caller.bin" and output.parent.name == "linked-binary":
                        data = bytearray(output.read_bytes())
                        data[-1] ^= 1
                        output.write_bytes(data)
                    elif attack.endswith("-replacement") and "--only-section=.text" in command:
                        incoming = Path(command[-2])
                        stage = "original" if attack == "original-replacement" else "linked"
                        if incoming.parent.name == stage:
                            replacement = incoming.parent / "replacement"
                            replacement.write_bytes(incoming.read_bytes())
                            replacement.replace(incoming)
                    return completed
                try:
                    with patch.object(profile, "_run", hostile), self.assertRaises(profile.Failure):
                        self.capture()
                    self.assertEqual(list(self.workspace.iterdir()), [])
                finally:
                    source.write_bytes(saved)

    def test_context_map_allowance_identity_drift_and_timeout(self):
        game = self.cases[0][3]
        with tempfile.TemporaryDirectory(prefix="final-inputs-", dir=SCRATCH) as temporary:
            allowance = Path(temporary) / "allowance.json"
            allowance.write_bytes(encoded({"entries": []}))
            for path in (game / profile.context_path(self.cases[0][1]), game / "config/functions.json", allowance):
                with self.subTest(path=path.name), patch.dict(os.environ, {"FFTA_ASM_ALLOW": str(allowance)}), \
                        profile.Acquisition(game_root=game, kit_root=self.kit) as acquisition:
                    self.fixed(acquisition)
                    replacement = path.parent / (path.name + ".replacement")
                    replacement.write_bytes(path.read_bytes())
                    replacement.replace(path)
                    with self.assertRaises(profile.Failure):
                        acquisition.recheck()
        with patch.object(profile, "CAPTURE_TIMEOUT", 0.01), self.assertRaisesRegex(profile.Failure, "could not complete"):
            profile._run(["/usr/bin/sleep", "2"], self.workspace, self.workspace)

    def test_all_function_indexes_and_manager_type_are_bound(self):
        game = self.cases[0][3]
        functions = game / "config/functions.json"
        original_functions = functions.read_bytes()
        document = json.loads(original_functions)
        variants = [document + [document[0]], copy.deepcopy(document), copy.deepcopy(document)]
        variants[1][1]["rom"] = "0x08000002"
        variants[1][1]["end"] = "0x08000004"
        variants[2][0]["mode"] = "arm"
        for changed in variants:
            try:
                functions.write_bytes(encoded(changed))
                with self.assertRaises(profile.Failure):
                    self.capture()
            finally:
                functions.write_bytes(original_functions)
        for relative, before, after in (("symbols/functions.txt", b" 228\n", b" 226\n"),
                                         ("symbols/ffta.sym", b"0000E4", b"0000E2"),
                                         ("config/data_symbols.json", b"0200F430", b"0200F434")):
            path = game / relative
            saved = path.read_bytes()
            self.assertIn(before, saved)
            try:
                path.write_bytes(saved.replace(before, after))
                with self.assertRaises(profile.Failure):
                    self.capture()
            finally:
                path.write_bytes(saved)

    def test_complete_caller_rom_tail_corruption_refuses_after_trust(self):
        case = self.cases[0]
        layout, address, size, game, rom = case
        changed = bytearray(rom)
        changed[address - profile.ROM_BASE + size - 1] ^= 1
        path = game / "baserom.bin"
        try:
            path.write_bytes(changed)
            with self.assertRaisesRegex(profile.Failure, "complete body differs from ROM"):
                self.capture((layout, address, size, game, bytes(changed)))
            self.assertEqual(list(self.workspace.iterdir()), [])
        finally:
            path.write_bytes(rom)

    def test_later_generated_final_read_cannot_mutate_earlier_fixed_input(self):
        source = self.cases[0][3] / "src/08000000.c"
        original = source.read_bytes()
        read, switch = profile.Acquisition._read, profile._switch
        armed, fired = False, False

        def arm(*arguments):
            nonlocal armed
            result = switch(*arguments)
            armed = True
            return result

        def hostile(owner, descriptor, size):
            nonlocal fired
            data = read(owner, descriptor, size)
            if armed and not fired and os.readlink(f"/proc/self/fd/{descriptor}").endswith("/linked-binary/caller.bin"):
                fired = True
                with source.open("r+b") as stream:
                    stream.write(bytes([original[0] ^ 1]))
            return data

        try:
            with patch.object(profile, "_switch", arm), patch.object(profile.Acquisition, "_read", hostile), \
                    self.assertRaisesRegex(profile.Failure, "identity drift after final reads"):
                self.capture()
            self.assertTrue(fired)
            self.assertEqual(list(self.workspace.iterdir()), [])
        finally:
            source.write_bytes(original)

    def test_fresh_same_byte_source_declaration_kind_attacks_refuse(self):
        baseline = self.capture()
        expected = dict(baseline.artifacts)["original_binary"]
        game = self.cases[0][3]
        header, source = game / "include/fixture.h", game / "src/08000000.c"
        saved_header, saved_source = header.read_bytes(), source.read_bytes()
        real_run = profile._run
        variants = (
            (b"extern u32 synthetic_callback(void *, struct Descriptor *, void *);", b"extern u32 synthetic_callback;",
             b"synthetic_callback, 12", b"(Callback)&synthetic_callback, 12", "function binding contradicts source declaration"),
            (b"extern void *manager_cell;", b"extern void *manager_cell(void);",
             b"synthetic_registration(manager_cell,", b"synthetic_registration(*(void **)manager_cell,",
             "manager object binding contradicts source declaration"),
        )
        for before, after, old_use, new_use, reason in variants:
            with self.subTest(reason=reason):
                observed, commands = [], []

                def record(command, root, temporary):
                    result = real_run(command, root, temporary)
                    commands.append(command)
                    output = Path(command[-1])
                    if output.parent.name == "original-binary":
                        observed.append(output.read_bytes())
                    return result

                try:
                    self.assertIn(before, saved_header)
                    self.assertIn(old_use, saved_source)
                    header.write_bytes(saved_header.replace(before, after))
                    source.write_bytes(saved_source.replace(old_use, new_use))
                    with patch.object(profile, "_run", record), self.assertRaisesRegex(profile.Failure, reason):
                        self.capture()
                    self.assertEqual(observed, [expected])
                    self.assertEqual(len(commands), 4)
                    self.assertEqual(list(self.workspace.iterdir()), [])
                finally:
                    header.write_bytes(saved_header)
                    source.write_bytes(saved_source)

    def test_supported_explicit_declarations_and_callback_address_preserve_bytes(self):
        baseline = self.capture()
        game = self.cases[0][3]
        header, source = game / "include/fixture.h", game / "src/08000000.c"
        saved_header, saved_source = header.read_bytes(), source.read_bytes()
        try:
            header.write_bytes(saved_header.replace(b"extern void *manager_cell;", b"extern void * const manager_cell;").replace(
                b"extern u32 synthetic_callback(void *, struct Descriptor *, void *);",
                b"extern u32\n synthetic_callback(void *task, struct Descriptor *descriptor, void *parent);"))
            source.write_bytes(saved_source.replace(b"synthetic_callback, 12", b"&synthetic_callback, 12"))
            captured = self.capture()
            self.assertEqual(dict(captured.artifacts)["linked_binary"], dict(baseline.artifacts)["linked_binary"])
            self.assertEqual(len(captured.commands), 7)
            self.assertTrue(all(record["symbol"]["info"] == 0x10 for record in captured.to_dict()["relocations"]
                                if record["symbol"]["name"]))
        finally:
            header.write_bytes(saved_header)
            source.write_bytes(saved_source)

    def test_ambiguous_and_unsupported_declarations_or_indirect_role_uses_refuse(self):
        captured = self.capture()
        preprocessed = dict(captured.artifacts)["preprocessed"]
        bindings = captured.to_dict()["placement"]["bindings"]
        callback = b"extern u32 synthetic_callback(void *, struct Descriptor *, void *);"
        manager = b"extern void *manager_cell;"
        variants = (
            preprocessed.replace(callback, callback + b"\n" + callback),
            preprocessed.replace(callback, b"extern u32 (*synthetic_callback)(void *, struct Descriptor *, void *);"),
            preprocessed.replace(callback, b"extern u32 synthetic_callback();"),
            preprocessed.replace(manager, b"typedef void *Manager; extern Manager manager_cell;"),
            preprocessed.replace(manager, b"extern void *manager_cell[1];"),
            preprocessed.replace(manager, b"extern u32 manager_cell;"),
            preprocessed.replace(b"synthetic_callback, 12", b"(Callback)synthetic_callback, 12"),
            preprocessed.replace(b"synthetic_registration(manager_cell,", b"synthetic_registration((void *)manager_cell,"),
            preprocessed.replace(b"return synthetic_registration", b"Callback alias = synthetic_callback; return synthetic_registration"),
            preprocessed + b"\n#pragma pack(1)\n",
        )
        for altered in variants:
            with self.subTest(digest=hashlib.sha256(altered).hexdigest()), self.assertRaises(profile.Failure):
                profile._source_binding_agreement(altered, bindings)

    def test_fresh_same_byte_mapping_shift_in_original_and_linked_refuses(self):
        baseline = self.capture()
        original_run = profile._run
        for stage in ("original", "linked"):
            with self.subTest(stage=stage):
                shifts, observed = [], []

                def shift(command, root, temporary):
                    result = original_run(command, root, temporary)
                    output = Path(command[-1])
                    if output.parent.name == stage:
                        data = bytearray(output.read_bytes())
                        image = profile._elf(data)
                        symbol = next(symbol for symbol in profile._symbols(image)
                                      if symbol["name"] == "$d" and symbol["value"] > baseline.fixed.address * (stage == "linked"))
                        location = image["sections"][symbol["table_section_index"]][4] + symbol["index"] * 16 + 4
                        struct.pack_into("<I", data, location, symbol["value"] + 4)
                        output.write_bytes(data)
                        shifts.append((symbol["value"], symbol["value"] + 4))
                    if output.parent.name == stage + "-binary":
                        observed.append(output.read_bytes())
                    return result

                with patch.object(profile, "_run", shift), self.assertRaisesRegex(profile.Failure, "mapping intervals"):
                    self.capture()
                self.assertEqual(len(shifts), 1)
                self.assertEqual(observed, [dict(baseline.artifacts)[stage + "_binary"]])
                self.assertEqual(list(self.workspace.iterdir()), [])

    def test_mapping_transitions_cover_alignment_prefix_and_entire_intervals(self):
        for case in self.cases:
            captured = self.capture(case)
            artifacts, result, original, size, labels, records, named, objects = self.inspection(captured)
            for stage in ("original", "linked"):
                image = profile._elf(artifacts[stage + "_elf"])
                symbols = [symbol for symbol in profile._symbols(image) if symbol["name"] in ("$t", "$d")]
                base = 0 if stage == "original" else captured.fixed.address - captured.fixed.address % 4
                first_data = next(symbol for symbol in symbols if symbol["name"] == "$d" and symbol["value"] > base)
                variants = []
                # Move data past the complete first literal/alignment range.
                later = next(record["offset"] for record in records if record["role"] == "literal" and
                             record["offset"] > first_data["value"] - base)
                variants.append((first_data, base + later))
                # A duplicate/redundant or conflicting transition cannot replace
                # the required transition inventory, even at an owned point.
                last_data = next(symbol for symbol in reversed(symbols) if symbol["name"] == "$d")
                variants.append((last_data, first_data["value"]))
                variants.append((next(symbol for symbol in symbols if symbol["name"] == "$t"), first_data["value"]))
                if captured.fixed.address % 4:
                    variants.append((next(symbol for symbol in symbols if symbol["value"] == base), first_data["value"]))
                for symbol, value in variants:
                    data = bytearray(artifacts[stage + "_elf"])
                    location = image["sections"][symbol["table_section_index"]][4] + symbol["index"] * 16 + 4
                    struct.pack_into("<I", data, location, value)
                    with self.subTest(case=case[:2], stage=stage, value=value), self.assertRaisesRegex(profile.Failure, "mapping intervals"):
                        profile._symbol_ownership(profile._elf(data), captured.fixed.address, size,
                                                  result["placement"]["bindings"], records, stage=stage)


if __name__ == "__main__":
    unittest.main()
