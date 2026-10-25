"""Internal input/acquisition and fresh-capture foundation for registration.

This module cannot execute caller semantics, issue or replay a public report.
Raw-input records must eventually come from actual decoded caller dataflow;
validating their shape here does not establish that provenance.
"""

from dataclasses import dataclass
import hashlib
import os
from pathlib import Path
import re
import shutil
import stat
import struct
import subprocess
import signal
import sys
import tempfile

import conditional_registration_effects as private


CONTEXT_SCHEMA = "conditional-registration-caller-context-v1"
POLICY = "conditional-registration-caller-v1"
OPERATION = "descriptor28-phase0-payload12-v1"
SELECTOR = "descriptor28-phase0-v1"
CANONICAL_REPORT_ELIGIBLE = False
ROM_BASE, ROM_END = 0x08000000, 0x09000000
TOOL_SPELLINGS = (
    ("cc", "$HOME/agbcc/gcc/agbcc"), ("cpp", "cpp"),
    ("assembler", "arm-none-eabi-as"), ("objcopy", "arm-none-eabi-objcopy"),
    ("linker", "arm-none-eabi-ld"),
)
FLAGS = "-mthumb-interwork -O2"
ROM_SIZE = 16 * 1024 * 1024
ROM_SHA1 = "4ac05441f4de70a4ec3dd932116346c61b8783d9"
CAPTURE_TIMEOUT = 60
PLACEMENT_RULE = "thumb-entry-typed-registration-context-v1"
REMAINING_OBLIGATIONS = (
    "S1: independent fresh-capture review before downstream integration",
    "P4-P5: decoded raw-input provenance, guarded caller/helper execution, histories and coverage",
    "P6-P7: private bridge, live projection/import, immediate retirement and restoration",
    "P8: complete canonical reports, replay, terminal consumer routing and atomic publication",
)

Failure = private.Failure
require = private.require
canonical = private.canonical
fields, choice, sequence = private.fields, private.choice, private.sequence


def _text(value):
    require(type(value) is str and bool(value), "invalid Text")
    try:
        value.encode("utf-8")
    except UnicodeError as error:
        raise Failure("identity", "invalid UTF-8 Text") from error
    require(all(ord(character) >= 32 and not 127 <= ord(character) <= 159
                and character not in "`\r\n" for character in value), "invalid Text")


def validate(value, spec):
    """Validate the closed P1 records needed by S1a; no output schemas exist."""
    if spec in ("Text", "RelPath", "HostPath"):
        _text(value)
        if spec != "Text":
            absolute = spec == "HostPath"
            require(value.startswith("/") == absolute and "\\" not in value,
                    "invalid " + spec)
            components = value[1:].split("/") if absolute else value.split("/")
            require(all(part and part not in (".", "..") for part in components),
                    "invalid " + spec)
    elif spec == "Path":
        require(type(value) is dict and set(value) == {"root", "path"}, "wrong Path fields")
        private.validate(value["root"], choice("game", "kit", "host"))
        validate(value["path"], "HostPath" if value["root"] == "host" else "RelPath")
    elif spec == "PathPin":
        require(type(value) is dict and set(value) == {"path", "pin"}, "wrong PathPin fields")
        validate(value["path"], "Path")
        private.validate(value["pin"], "Pin")
    elif spec == "RawInput":
        private.validate(value, fields(role=choice("count", "selector"),
                                       register=choice(*private.REGISTERS), value="ID"))
    elif spec == "U16":
        require(type(value) is int and 0 <= value <= 65535, "invalid U16")
    elif spec in ("Offset", "Count"):
        private.validate(value, "U32")
    elif spec == "I32":
        private.validate(value, "SignedOffset")
    elif spec == "DataRegister":
        private.validate(value, choice(*private.REGISTERS))
    elif spec == "Permission":
        private.validate(value, choice("r", "rw", "rx"))
    elif spec in ("Hex", "Hex4", "Hex8", "Encoding", "Name", "BodyID", "PathID"):
        patterns = {
            "Hex": r"(?:[0-9a-f]{2})+", "Hex4": r"[0-9a-f]{8}",
            "Hex8": r"[0-9a-f]{16}", "Encoding": r"(?:[0-9a-f]{4}|[0-9a-f]{8})",
            "Name": r"[A-Za-z_.$][A-Za-z0-9_.$]*", "BodyID": r"body/[0-9A-F]{8}",
            "PathID": r"path/[0-9a-f]{64}",
        }
        require(type(value) is str and re.fullmatch(patterns[spec], value) is not None,
                "invalid " + spec)
        if spec == "BodyID":
            _address(int(value[5:], 16))
    else:
        private.validate(value, spec)


def _address(address):
    private.validate(address, "U32")
    require(ROM_BASE <= address < ROM_END and address % 2 == 0, "invalid ROM address")


def context_path(address):
    _address(address)
    return f"config/conditional_registration/{address:08X}.json"


def _ordered(records, key=canonical, label="set"):
    keys = [key(record) for record in records]
    require(keys == sorted(set(keys)), "duplicate or unsorted " + label)


class _Entry:
    """Read-only S1-S2 validation; no Checker construction or execution."""

    def __init__(self, context):
        private.validate(context, "Context")
        self.context = context
        seen = set()
        for name in ("regions", "frames", "values"):
            _ordered(context[name], lambda item: item["id"], name)
            for item in context[name]:
                self._define(item["id"], seen)
            setattr(self, name, {item["id"]: item for item in context[name]})
        require(context["frame"] in self.frames, "unknown current frame")
        current = self.frames[context["frame"]]
        require(current["invocation"] == context["invocation"], "frame invocation differs")
        ancestry = set()
        while current is not None:
            require(current["id"] not in ancestry, "cyclic frame parents")
            ancestry.add(current["id"])
            parent = current["parent"]
            require(parent is None or parent in self.frames, "unknown parent frame")
            current = self.frames.get(parent)
        require(ancestry == set(self.frames), "entry contains non-ancestor frame")
        require(len(ancestry) <= private.MAX_DEPTH, "entry frame depth limit", "unsupported")
        self.invocations = set()
        for frame in self.frames.values():
            self._define(frame["invocation"], seen)
            self.invocations.add(frame["invocation"])
            _ordered(frame["allocations"], label="frame allocations")
            require(frame["allocations"] == sorted(region["id"] for region in self.regions.values()
                                                  if region["frame"] == frame["id"]),
                    "frame allocation back-reference mismatch")
            _ordered(frame["saves"], lambda item: item["witness"], "save witnesses")
            for save in frame["saves"]:
                self._define(save["witness"], seen)
        current = self.frames[context["frame"]]
        require(not current["allocations"] and not current["saves"],
                "caller-entry contains future storage or saves")
        require(current["entry_sp"] == context["sp"], "caller entry SP differs")
        for region in self.regions.values():
            require(region["lifetime"] == "live", "entry contains retired storage")
            require(region["base"]["tag"] != "allocated", "entry contains allocated result")
            if region["base"]["tag"] == "symbolic":
                self._input_id(region["base"]["anchor"])
            self.base(region["id"])
            if region["kind"] == "stack-allocation":
                require(region["frame"] in self.frames and region["permission"] == "rw",
                        "invalid stack allocation")
            else:
                require(region["frame"] is None, "non-stack region has a frame")
                permission = {"rom": "r", "runtime-image": "rx", "stack-domain": "rw"}.get(region["kind"])
                require(permission is None or permission == region["permission"], "region permission mismatch")
        for value in self.values.values():
            tag = value["tag"]
            require(tag != "condition-word", "entry contains condition-word result")
            if tag == "pointer":
                require(value["region"] in self.regions and
                        value["offset"] <= self.regions[value["region"]]["size"], "invalid pointer")
            elif tag == "constant":
                require(value["value"] < 1 << (private.width(value) * 8), "constant width overflow")
            elif tag == "control":
                require(value["invocation"] in self.invocations, "invalid control invocation")
                require(value["target"] is None or value["target"] & 1, "control target not Thumb")
            elif tag == "symbolic":
                self.origin(value["origin"])
            elif tag == "bytes":
                require(len(value["bytes"]) == value["width"], "byte value width mismatch")
                self.parts(value["bytes"], (value["id"],))
        for reference in [*context["registers"].values(), context["sp"], context["lr"]]:
            require(reference in self.values and private.width(self.values[reference]) == 4,
                    "invalid register value reference")
        self.stack_pointer(context["sp"])
        require(self.values[context["lr"]]["tag"] == "control", "entry LR is not control")
        for frame in self.frames.values():
            self.stack_pointer(frame["entry_sp"])
        self.memory = {}
        _ordered(context["cells"], label="cells")
        for cell in context["cells"]:
            anchor, start, _ = self.interval(cell["location"])
            require(len(cell["bytes"]) == cell["location"]["size"], "cell width mismatch")
            self.parts(cell["bytes"])
            for offset, part in enumerate(cell["bytes"]):
                key = (anchor, start + offset)
                require(key not in self.memory, "overlapping input cells")
                self.memory[key] = part
        allocations = [region for region in self.regions.values() if region["kind"] == "stack-allocation"]
        domains = [region for region in self.regions.values() if region["kind"] == "stack-domain"]
        for index, region in enumerate(allocations):
            extent = private.slc(region["id"], 0, region["size"])
            anchor, start, end = self.interval(extent)
            require(any(anchor == self.base(domain["id"])[0] and
                        self.base(domain["id"])[1] <= start < end <= self.base(domain["id"])[1] + domain["size"]
                        for domain in domains), "stack allocation outside backing")
            require(not any(self.overlap(extent, private.slc(other["id"], 0, other["size"]))
                            for other in allocations[index + 1:]), "live stack allocations overlap")
        for frame in self.frames.values():
            for save in frame["saves"]:
                location = save["location"]
                self.interval(location)
                require(location["size"] == 4 and save["value"] in self.values and
                        private.width(self.values[save["value"]]) == 4, "invalid save value")
                require(self.regions[location["region"]]["kind"] == "stack-allocation" and
                        self.regions[location["region"]]["frame"] == frame["id"], "save belongs to wrong frame")
                anchor, start, _ = self.interval(location)
                require([self.memory.get((anchor, start + offset)) for offset in range(4)] ==
                        private.value_bytes(self.values[save["value"]]), "saved bytes disagree", "contradictory-condition")

    @staticmethod
    def _input_id(identifier):
        require(not identifier.startswith(("derived/", "pub/", "prj/")), "reserved entry identity")

    def _define(self, identifier, seen):
        self._input_id(identifier)
        require(identifier not in seen, "duplicate entry definition or invocation")
        seen.add(identifier)

    # These unchanged helpers only inspect already validated input records.
    base = private.Checker.base
    interval = private.Checker.interval
    overlap = private.Checker.overlap
    equivalent = private.Checker.equivalent
    forbidden = private.Checker.forbidden
    key = private.Checker.key

    def origin(self, origin):
        if origin["tag"] == "register":
            require(origin["invocation"] in self.invocations, "invalid register origin")
        else:
            require(origin["region"] in self.regions and
                    origin["offset"] < self.regions[origin["region"]]["size"], "invalid memory origin")

    def parts(self, parts, active=()):
        for part in parts:
            if part["tag"] == "unknown":
                self.origin(part["origin"])
            elif part["tag"] == "fragment":
                reference = part["value"]
                require(reference in self.values and reference not in active, "invalid or cyclic fragment reference")
                value = self.values[reference]
                require(part["index"] < private.width(value), "fragment index exceeds width")
                if value["tag"] == "bytes":
                    self.parts(value["bytes"], (*active, reference))

    def stack_pointer(self, reference):
        require(reference in self.values, "dangling frame SP")
        value = self.values[reference]
        require(value["tag"] == "pointer" and value["region"] in self.regions and
                self.regions[value["region"]]["kind"] in ("stack-domain", "stack-allocation"),
                "SP is not a live stack pointer")
        require((self.base(value["region"])[1] + value["offset"]) % 4 == 0, "unaligned entry SP")


def _token(name):
    return fields(call=choice(name))


def _templates(records, entry):
    require(type(records) is list, "conditions must be a list")
    parameters = [dict(spec) for spec in private.PARAMETERS]
    parameters[0]["entry_sp"] = _token("sp")
    for name in ("descriptor", "parameters", "manager", "parent", "protected", "separation"):
        parameters[1][name] = _token(name)
    parameters[2]["manager_value"] = _token("manager-value")
    parameters[6]["data_value"] = _token("data-value")
    parameters[6]["source"] = _token("data-source")
    identifiers = []
    for record in records:
        require(type(record) is dict and type(record.get("id")) is str and
                record["id"] in tuple("B" + str(number) for number in range(1, 9)), "invalid template clause")
        number = int(record["id"][1:]) - 1
        scope = "allocator" if number in (3, 4) else "initializer" if number == 5 else "registration"
        private.validate(record, fields(id=choice(record["id"]), clause=choice(private.CLAUSES[number]),
            invocation=choice("each-reached-registration"), source=choice("declared-invocation"),
            status=choice("assumed"), interval=fields(begin=choice(scope + "-entry"), end=choice(scope + "-return")),
            parameters=parameters[number]))
        identifiers.append(record["id"])
    require(identifiers == sorted(set(identifiers)), "duplicate or unsorted conditions")
    require(identifiers == ["B" + str(number) for number in range(1, 9)],
            "required invocation condition missing", "unmet-condition")

    def references(item, key=None):
        if type(item) is dict:
            if set(item) == {"call"}:
                return
            if set(item) == set(private.SPECS["Slice"]):
                entry.interval(item)
            else:
                for name, child in item.items():
                    references(child, name)
        elif type(item) is list:
            for child in item:
                references(child, key)
        elif key in ("owner_value", "phase_value", "head_value", "chain"):
            require(item in entry.values, "dangling template value reference")

    for record in records:
        references(record["parameters"])
    params = {record["id"]: record["parameters"] for record in records}
    first, nodes, manager, allocation = (params[name] for name in ("B1", "B2", "B3", "B4"))
    domain = first["domain"]
    require(entry.regions[domain["region"]]["kind"] == "stack-domain", "B1 domain is not stack backing")
    window = first["allocator_window"]
    require(window["low"] < 0 and window["low"] % 4 == 0, "invalid allocator stack window")
    anchor, start, end = entry.interval(domain)
    sp = entry.values[entry.context["sp"]]
    sp_anchor, sp_base = entry.base(sp["region"])
    require(sp_anchor == anchor and start <= sp_base + sp["offset"] <= end, "entry SP outside B1 domain")
    for region in entry.regions.values():
        if region["kind"] == "stack-allocation":
            a, low, high = entry.interval(private.slc(region["id"], 0, region["size"]))
            require(a == anchor and start <= low < high <= end, "inherited allocation outside B1 domain")
    cell = manager["manager_cell"]
    require(entry.interval(cell) == ("concrete", 0x0200F430, 0x0200F434), "wrong manager cell")
    require(entry.regions[cell["region"]]["permission"] in ("r", "rw"), "manager cell is not readable")
    chain = manager["chain"]
    require(len(chain) == len(set(chain)), "duplicate chain value identity")
    require(len(chain) <= 64, "declared chain exceeds 64 nodes", "unsupported")
    require(len(chain) == len(nodes["nodes"]), "chain/node count differs")
    for reference, location in zip(chain, nodes["nodes"]):
        region, value = entry.regions[location["region"]], entry.values[reference]
        require(location["size"] == 12 and region["kind"] == "external" and region["permission"] == "rw", "invalid node prefix")
        require(value == {"id": reference, "tag": "pointer", "region": location["region"], "offset": location["offset"]}, "chain pointer differs")
    require(not any(entry.overlap(left, right) for index, left in enumerate(nodes["nodes"])
                    for right in nodes["nodes"][index + 1:]), "node prefixes overlap")
    head = entry.values[manager["head_value"]]
    require((not chain and head["tag"] == "constant" and head["value"] == 0 and head["width"] == 4) or
            (chain and entry.equivalent(manager["head_value"], chain[0])), "head differs from chain")
    require(private.width(entry.values[manager["phase_value"]]) == 2, "phase is not two bytes")
    protected = [private.slc(region["id"], 0, region["size"]) for region in entry.regions.values()
                 if region["kind"] == "stack-allocation"]
    require(not entry.forbidden(manager["phase_value"], protected), "phase contains borrowed pointer fragment")
    for name in ("domain", "owner_metadata"):
        location = allocation[name]
        region = entry.regions[location["region"]]
        require(region["kind"] == "external" and region["permission"] == "rw", "invalid allocator domain")
        require(not any(entry.overlap(location, private.slc(stack["id"], 0, stack["size"]))
                        for stack in entry.regions.values() if stack["kind"] == "stack-allocation"), "allocator domain overlaps stack")
    owner = entry.values[manager["owner_value"]]
    metadata = allocation["owner_metadata"]
    require(owner["tag"] == "pointer" and owner["region"] == metadata["region"] and
            metadata["offset"] <= owner["offset"] < metadata["offset"] + metadata["size"], "owner outside metadata")
    image = params["B6"]["image"]
    require(image["size"] == 50 and entry.regions[image["region"]]["kind"] == "runtime-image", "invalid initializer image")
    require(not any(entry.overlap(image, private.slc(region["id"], 0, region["size"]))
                    for region in entry.regions.values() if region["permission"] == "rw"), "image overlaps writable storage")


@dataclass(frozen=True)
class CallerRequest:
    """Parsed entry facts, not evidence that a caller satisfies the profile."""

    encoded: str
    file_bytes: bytes

    def to_dict(self):
        return private.decode(self.encoded)

    @property
    def pin(self):
        return private.pin(self.file_bytes)


def parse_request(data, *, address, path):
    """Parse actual canonical request-file bytes against an engine-bound address."""
    require(type(data) is bytes, "request must be immutable file bytes")
    _address(address)
    validate(path, "RelPath")
    require(path == context_path(address), "noncanonical context path")
    try:
        record = private.decode(data.decode("utf-8"))
        encoded = canonical(record)
        require(data == encoded.encode("utf-8") + b"\n", "noncanonical request bytes")
    except (UnicodeError, ValueError, RecursionError) as error:
        raise Failure("identity", "invalid request encoding") from error
    spec = fields(schema=choice(CONTEXT_SCHEMA), policy=choice(POLICY),
                  operation=choice(OPERATION), address="U32", site="U32", entry="Context")
    require(type(record) is dict and set(record) == set(spec) | {"conditions"}, "wrong request fields")
    for name, child in spec.items():
        private.validate(record[name], child, "request." + name)
    require(record["address"] == address, "request address differs")
    require(record["site"] % 2 == 0 and address <= record["site"] and record["site"] + 4 <= ROM_END,
            "invalid registration site")
    try:
        entry = _Entry(record["entry"])
        _templates(record["conditions"], entry)
    except RecursionError as error:
        raise Failure("unsupported", "entry representation depth limit") from error
    return CallerRequest(encoded, data)


def validate_raw_inputs(request, raw_inputs):
    """Check later engine-derived roles without fixing r2/r3 as universal roles.

    No roles are accepted in request JSON. This check establishes no decoded
    provenance; the later caller engine must derive and regenerate these records.
    """
    require(type(request) is CallerRequest, "wrong request type")
    require(type(raw_inputs) is list and len(raw_inputs) == 2, "exactly two raw inputs required")
    for raw in raw_inputs:
        validate(raw, "RawInput")
    require([raw["role"] for raw in raw_inputs] == ["count", "selector"], "raw inputs out of role order")
    require(raw_inputs[0]["register"] != raw_inputs[1]["register"], "raw inputs share register")
    record = request.to_dict()
    entry = record["entry"]
    view = _Entry(entry)
    values = {value["id"]: value for value in entry["values"]}
    origins = []
    for raw in raw_inputs:
        require(entry["registers"][raw["register"]] == raw["value"], "raw input register reference differs")
        origin = {"tag": "register", "invocation": entry["invocation"], "register": raw["register"]}
        require(values.get(raw["value"]) == {"id": raw["value"], "tag": "symbolic", "width": 4, "origin": origin},
                "raw input is not an unconstrained U32 register root")
        origins.append(origin)

    def origin_depends(origin, size, active):
        if origin["tag"] == "register":
            return origin in origins
        anchor, base = view.base(origin["region"])
        return any(part_depends(view.memory.get((anchor, base + origin["offset"] + offset)), active)
                   for offset in range(size))

    def part_depends(part, active):
        if part is None:
            return False
        if part["tag"] == "fragment":
            return depends(part["value"], active)
        if part["tag"] == "unknown":
            key = canonical(part["origin"])
            return False if key in active else origin_depends(part["origin"], 1, (*active, key))
        return False

    def depends(reference, active=()):
        if reference in active:
            return False
        value = values[reference]
        if value["tag"] == "symbolic":
            return origin_depends(value["origin"], value["width"], (*active, reference))
        if value["tag"] == "bytes":
            return any(part_depends(part, (*active, reference)) for part in value["bytes"])
        return False

    def walk(item, key=None):
        if type(item) is dict:
            for name, child in item.items():
                walk(child, name)
        elif type(item) is list:
            for child in item:
                walk(child, key)
        elif key in ("owner_value", "phase_value", "head_value", "chain"):
            require(not depends(item), "template restricts raw input")

    for template in record["conditions"]:
        walk(template["parameters"])
    params = {template["id"]: template["parameters"] for template in record["conditions"]}
    restricted = [params["B3"]["manager_cell"], params["B6"]["image"]]
    restricted.extend(private.slc(node["region"], node["offset"] + 8, 4) for node in params["B2"]["nodes"])
    for location in restricted:
        anchor, start, end = view.interval(location)
        require(not any(part_depends(view.memory.get((anchor, offset)), ()) for offset in range(start, end)),
                "template storage restricts raw input")


def _identity(info):
    return (info.st_dev, info.st_ino, info.st_mode, info.st_size, info.st_mtime_ns, info.st_ctime_ns)


@dataclass(frozen=True)
class Artifact:
    path_json: str
    data: bytes

    @property
    def path_pin(self):
        return {"path": private.decode(self.path_json), "pin": private.pin(self.data)}


class Acquisition:
    """Invocation-owned descriptors with no-follow reads and explicit rechecks.

    Paths passed to this internal API are chosen by the engine, never by a
    request. All descriptors remain open until close/context-manager exit.
    """

    def __init__(self, *, game_root, kit_root):
        require(os.name == "posix" and hasattr(os, "O_NOFOLLOW"), "POSIX no-follow acquisition required", "unsupported")
        self.roots = {"game": Path(game_root).absolute(), "kit": Path(kit_root).absolute()}
        self.directories = {}
        self.files = {}
        self.absences = set()
        self.links = {}
        self.tool_selections = {}
        self.environment = {}
        self.closed = False

    def __enter__(self):
        return self

    def __exit__(self, *unused):
        self.close()

    def close(self):
        if not self.closed:
            for descriptor, *_ in (*self.files.values(), *self.directories.values()):
                os.close(descriptor)
            self.closed = True

    def _directory(self, path, membership=True):
        require(not self.closed, "acquisition is closed")
        path = Path(path)
        # Trusted-root paths bind their complete ancestor inventories. Host
        # resolution ancestors outside those roots bind namespace identity;
        # the acquired host file/link's immediate parent binds membership too.
        membership = membership or any(path == root or root in path.parents for root in self.roots.values())
        if path in self.directories:
            if membership and self.directories[path][2] is None:
                descriptor, identity, _ = self.directories[path]
                try:
                    require(identity[:3] == _identity(os.fstat(descriptor))[:3], "parent resolution drift")
                    self.directories[path] = (descriptor, _identity(os.fstat(descriptor)), tuple(sorted(os.listdir(descriptor))))
                except OSError as error:
                    raise Failure("identity", "parent directory unavailable") from error
            return self.directories[path][0]
        parent = None if path == Path("/") else self._directory(path.parent, False)
        try:
            descriptor = os.open(str(path) if parent is None else path.name,
                                 os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_NONBLOCK | os.O_CLOEXEC,
                                 dir_fd=parent)
            try:
                before = _identity(os.fstat(descriptor))
                members = tuple(sorted(os.listdir(descriptor))) if membership else None
                require(before == _identity(os.fstat(descriptor)) == _identity(os.stat(
                    str(path) if parent is None else path.name, dir_fd=parent, follow_symlinks=False)),
                    "directory changed during acquisition")
            except BaseException:
                os.close(descriptor)
                raise
        except OSError as error:
            raise Failure("identity", "ordinary parent directory unavailable: " + str(path)) from error
        self.directories[path] = (descriptor, before, members)
        return descriptor

    def _path(self, record):
        validate(record, "Path")
        if record["root"] == "host":
            return Path(record["path"])
        root = self.roots[record["root"]]
        return root / record["path"]

    def _read(self, descriptor, size):
        os.lseek(descriptor, 0, os.SEEK_SET)
        chunks = []
        remaining = size + 1
        while remaining:
            chunk = os.read(descriptor, min(remaining, 1024 * 1024))
            if not chunk:
                return b"".join(chunks)
            chunks.append(chunk)
            remaining -= len(chunk)
        return b"".join(chunks)

    def acquire(self, record):
        path = self._path(record)
        require(not self.closed, "acquisition is closed")
        if path in self.files:
            self.recheck()
            artifact = self.files[path][2]
            path_json = canonical(record)
            return artifact if artifact.path_json == path_json else Artifact(path_json, artifact.data)
        parent = self._directory(path.parent)
        descriptor = None
        try:
            descriptor = os.open(path.name, os.O_RDONLY | os.O_NONBLOCK | os.O_NOFOLLOW | os.O_CLOEXEC, dir_fd=parent)
            before = os.fstat(descriptor)
            require(stat.S_ISREG(before.st_mode), "artifact is not a regular file")
            data = self._read(descriptor, before.st_size)
            identity = _identity(before)
            require(identity == _identity(os.fstat(descriptor)) ==
                    _identity(os.stat(path.name, dir_fd=parent, follow_symlinks=False)), "artifact changed during acquisition")
            require(len(data) == before.st_size, "artifact size changed during acquisition")
            artifact = Artifact(canonical(record), data)
            validate(artifact.path_pin, "PathPin")
        except OSError as error:
            if descriptor is not None:
                os.close(descriptor)
            raise Failure("identity", "ordinary artifact unavailable: " + str(path)) from error
        except BaseException:
            if descriptor is not None:
                os.close(descriptor)
            raise
        self.files[path] = (descriptor, identity, artifact)
        self.recheck()
        return artifact

    def optional(self, record):
        path = self._path(record)
        parent = self._directory(path.parent)
        try:
            os.stat(path.name, dir_fd=parent, follow_symlinks=False)
        except FileNotFoundError:
            self.absences.add(path)
            self.recheck()
            return None
        except OSError as error:
            raise Failure("identity", "optional artifact unavailable") from error
        return self.acquire(record)

    def sources(self, address):
        """Capture the exact source_paths domain, without is_file filtering."""
        _address(address)
        root = self.roots["game"]
        paths, candidates = [], []

        def visit(directory, include):
            descriptor = self._directory(directory)
            try:
                names = sorted(os.listdir(descriptor))
            except OSError as error:
                raise Failure("identity", "source inventory unavailable") from error
            for name in names:
                path = directory / name
                try:
                    info = os.stat(name, dir_fd=descriptor, follow_symlinks=False)
                except OSError as error:
                    raise Failure("identity", "source candidate unavailable") from error
                selected = name == f"{address:08X}.c" or name.endswith(".h")
                if selected and not include:
                    require(stat.S_ISREG(info.st_mode), "source/header candidate is not a regular file")
                if stat.S_ISDIR(info.st_mode):
                    visit(path, include)
                elif include or selected:
                    paths.append(path)
                    if not include and name == f"{address:08X}.c":
                        candidates.append(path)
                else:
                    require(not stat.S_ISLNK(info.st_mode), "symlink in source inventory")

        visit(root / "src", False)
        include = root / "include"
        parent = self._directory(root)
        try:
            info = os.stat("include", dir_fd=parent, follow_symlinks=False)
        except FileNotFoundError:
            self.absences.add(include)
        except OSError as error:
            raise Failure("identity", "include inventory unavailable") from error
        else:
            require(stat.S_ISDIR(info.st_mode), "include is not an ordinary directory")
            visit(include, True)
        require(len(candidates) == 1, "addressed source is missing or ambiguous")
        captured = [self.acquire({"root": "game", "path": path.relative_to(root).as_posix()}) for path in sorted(set(paths))]
        self.recheck()
        return candidates[0].relative_to(root).as_posix(), tuple(captured)

    def _tool_path(self, role):
        spellings = dict(TOOL_SPELLINGS)
        require(role in spellings, "unknown fixed-tool role")
        spelling = spellings[role]
        selected = shutil.which(os.path.expandvars(spelling))
        require(selected is not None, "missing fixed tool: " + role)
        path = Path(selected).absolute()
        validate(str(path), "HostPath")
        return spelling, path

    def tool(self, role):
        """The sole symlink-following acquisition route, for fixed tools only."""
        spelling, selected = self._tool_path(role)
        pending = list(selected.parts[1:])
        resolved = Path("/")
        chain = []
        while pending:
            part = pending.pop(0)
            if part in ("", "."):
                continue
            if part == "..":
                resolved = resolved.parent
                continue
            parent = self._directory(resolved)
            candidate = resolved / part
            try:
                info = os.stat(part, dir_fd=parent, follow_symlinks=False)
                if stat.S_ISLNK(info.st_mode):
                    require(len(chain) < 40, "fixed-tool symlink depth limit", "unsupported")
                    target = os.readlink(part, dir_fd=parent)
                    validate(target, "Text")
                    identity = _identity(info)
                    require(identity == _identity(os.stat(part, dir_fd=parent, follow_symlinks=False)), "tool link changed during resolution")
                    require(candidate not in self.links or self.links[candidate] == (identity, target), "tool resolution drift")
                    self.links[candidate] = (identity, target)
                    chain.append({"path": str(candidate), "target": target})
                    if target.startswith("/"):
                        resolved = Path("/")
                    pending = target.split("/") + pending
                else:
                    resolved = candidate
            except OSError as error:
                raise Failure("identity", "fixed-tool resolution unavailable") from error
        selection = (spelling, selected, os.environ.get("HOME"), os.environ.get("PATH"))
        require(role not in self.tool_selections or self.tool_selections[role] == selection, "fixed-tool selection drift")
        self.tool_selections[role] = selection
        artifact = self.acquire({"root": "host", "path": str(resolved)})
        require(self.files[resolved][1][2] & 0o111, "fixed tool is not executable")
        return {"role": role, "spelling": spelling, "resolved": str(resolved),
                "pin": artifact.path_pin["pin"], "resolution": chain}

    def fixed_tools(self):
        return tuple(self.tool(role) for role, _ in TOOL_SPELLINGS)

    def _recheck_directories(self):
        for path, (descriptor, identity, members) in self.directories.items():
            held, named = _identity(os.fstat(descriptor)), _identity(os.stat(path, follow_symlinks=False))
            require((identity == held == named) if members is not None else
                    (identity[:3] == held[:3] == named[:3]), "parent directory identity drift")
            if members is not None:
                require(tuple(sorted(os.listdir(descriptor))) == members, "parent membership drift")

    def _recheck_metadata(self):
        """Finish a shared read phase without performing another byte read."""
        require(not self.closed, "acquisition is closed")
        for name, value in self.environment.items():
            require(os.environ.get(name) == value, "environment selection drift: " + name)
        for path in self.absences:
            try:
                os.stat(path, follow_symlinks=False)
            except FileNotFoundError:
                continue
            raise Failure("identity", "previously absent path appeared")
        for path, (identity, target) in self.links.items():
            require(identity == _identity(os.stat(path, follow_symlinks=False)) and os.readlink(path) == target,
                    "fixed-tool link drift")
        for role, selection in self.tool_selections.items():
            spelling, selected = self._tool_path(role)
            require((spelling, selected, os.environ.get("HOME"), os.environ.get("PATH")) == selection,
                    "fixed-tool selection drift")
        for path, (descriptor, identity, _) in self.files.items():
            require(identity == _identity(os.fstat(descriptor)) ==
                    _identity(os.stat(path, follow_symlinks=False)), "artifact identity drift after final reads")
        self._recheck_directories()

    def recheck(self):
        """Sequential identity checks, not an atomic filesystem snapshot."""
        require(not self.closed, "acquisition is closed")
        try:
            self._recheck_directories()
            for name, value in self.environment.items():
                require(os.environ.get(name) == value, "environment selection drift: " + name)
            for path, (descriptor, identity, artifact) in self.files.items():
                require(identity == _identity(os.fstat(descriptor)) ==
                        _identity(os.stat(path, follow_symlinks=False)), "artifact identity drift")
                require(self._read(descriptor, len(artifact.data)) == artifact.data and
                        identity == _identity(os.fstat(descriptor)) == _identity(os.stat(path, follow_symlinks=False)),
                        "artifact bytes changed")
            # A later file's read may have changed an earlier file in place,
            # without changing any parent directory. Sweep all identities
            # again after the complete byte-read phase.
            self._recheck_metadata()
        except OSError as error:
            raise Failure("identity", "acquired path unavailable during recheck") from error


MAP_PATHS = (
    ("functions", "config/functions.json"), ("function_text", "symbols/functions.txt"),
    ("symbol_sizes", "symbols/ffta.sym"), ("data_symbols", "config/data_symbols.json"),
)


def _record(path, acquisition):
    path = Path(path).absolute()
    for role, root in acquisition.roots.items():
        if root in path.parents:
            return {"root": role, "path": path.relative_to(root).as_posix()}
    return {"root": "host", "path": str(path)}


def _environment(acquisition, name):
    value = os.environ.get(name)
    require(name not in acquisition.environment or acquisition.environment[name] == value,
            "environment selection drift: " + name)
    acquisition.environment[name] = value
    return value


def _rom(acquisition):
    root = acquisition.roots["game"]
    descriptor = acquisition._directory(root)
    names = sorted(name for name in os.listdir(descriptor)
                   if name == "baserom.bin" or name.lower().endswith(".gba"))
    for name in names:
        validate(name, "Text")
    candidates = [{"root": "game", "path": name} for name in names]
    environment = _environment(acquisition, "FFTA_ROM")
    if environment is not None:
        validate(environment, "Text")
        selected = Path(environment)
        chosen = _record(selected if selected.is_absolute() else root / selected, acquisition)
        validate(chosen, "Path")
        candidates.append(chosen)
    elif "baserom.bin" in names:
        chosen = {"root": "game", "path": "baserom.bin"}
    else:
        gba = [name for name in names if name.lower().endswith(".gba")]
        require(len(gba) == 1, "ROM discovery is missing or ambiguous")
        chosen = {"root": "game", "path": gba[0]}
    unique = {canonical(path): path for path in candidates}
    artifacts = tuple(acquisition.acquire(unique[key]) for key in sorted(unique))
    selected = acquisition.acquire(chosen)
    require(len(selected.data) == ROM_SIZE and hashlib.sha1(selected.data).hexdigest() == ROM_SHA1,
            "untrusted ROM identity")
    acquisition.recheck()
    return selected, {"environment": environment, "candidates": [item.path_pin for item in artifacts],
                      "root_names": names, "chosen": chosen}


def _engine(acquisition):
    # Import only ordinary closed helper modules. Consumer files are pinned,
    # without importing their command-line entry points or invoking replay.
    import capstone
    import inert_spin_profile
    import match
    import plausible
    import switch_constants_profile
    import switch_placement
    del inert_spin_profile, match, plausible, switch_constants_profile, switch_placement
    root = acquisition.roots["kit"]
    paths = {root / "tools" / name for name in (
        "conditional_registration_profile.py", "conditional_registration_effects.py",
        "match.py", "match_evidence.py", "status.py", "rebuild.py", "push.py",
        "switch_placement.py", "switch_constants_profile.py", "inert_spin_profile.py",
        "plausible.py", "rompath.py",
    )}
    for name, module in tuple(sys.modules.items()):
        filename = getattr(module, "__file__", None)
        if filename and (name == "capstone" or name.startswith("capstone.") or
                         root in Path(filename).absolute().parents):
            paths.add(Path(filename).absolute())
    library = Path(capstone._cs._name)
    if not library.is_absolute():
        # Only locate the already-loaded decoder; these bytes are never used
        # as an artifact. The resulting ordinary file is acquired below.
        with open("/proc/self/maps", encoding="ascii") as stream:
            loaded = {line.split()[-1] for line in stream
                      if line.split()[-1].endswith("/" + library.name)}
        require(len(loaded) == 1, "decoder library identity is ambiguous")
        library = Path(next(iter(loaded)))
    paths.add(library)
    records = {_record(path, acquisition)["root"] + ":" + str(path): _record(path, acquisition)
               for path in paths}
    artifacts = tuple(acquisition.acquire(record) for record in
                      sorted(records.values(), key=canonical))
    return artifacts


@dataclass(frozen=True)
class FixedInputs:
    """Captured input bytes; no success certificate or serialized Manifest."""
    address: int
    source: str
    sources: tuple
    maps: tuple
    rom: Artifact
    request: CallerRequest
    encoded: str

    def to_dict(self):
        return private.decode(self.encoded)


def acquire_fixed_inputs(acquisition, address):
    import plausible
    _address(address)
    source, sources = acquisition.sources(address)
    maps = tuple((role, acquisition.acquire({"root": "game", "path": path}))
                 for role, path in MAP_PATHS)
    context = acquisition.acquire({"root": "game", "path": context_path(address)})
    request = parse_request(context.data, address=address, path=context_path(address))
    rom, selection = _rom(acquisition)
    tools = acquisition.fixed_tools()
    _environment(acquisition, "FFTA_ASM_ALLOW")
    allowance = acquisition.optional(_record(plausible.asm_allow_path(), acquisition))
    if allowance is not None:
        document = private.decode(allowance.data.decode("utf-8"))
        require(type(document) is dict and type(document.get("entries")) is list,
                "invalid assembly allowance")
        require(all(type(entry) is dict for entry in document["entries"]), "invalid assembly allowance entry")
        require(not any(str(entry.get("address", "")).upper() in
                        (f"{address:08X}", f"0X{address:08X}") for entry in document["entries"]),
                "caller is on assembly allowance")
    engine = _engine(acquisition)
    for artifact in sources:
        require(not plausible.check_text(artifact.data.decode("utf-8")), "implausible captured source")
    record = {"sources": [artifact.path_pin for artifact in sources],
              "maps": {role: artifact.path_pin for role, artifact in maps},
              "rom": rom.path_pin, "rom_selection": selection, "tools": list(tools),
              "flags": FLAGS, "engine": [artifact.path_pin for artifact in engine],
              "allowlist": None if allowance is None else allowance.path_pin}
    acquisition.recheck()
    return FixedInputs(address, source, sources, maps, rom, request, canonical(record))


def _maps(fixed):
    """Join all three fresh function indexes; do not infer names from addresses."""
    snapshots = dict(fixed.maps)
    document = private.decode(snapshots["functions"].data.decode("utf-8"))
    require(type(document) is list and document, "invalid function mapping")
    entries = {}
    for entry in document:
        require(type(entry) is dict and all(type(entry.get(key)) is str for key in ("rom", "end", "mode")),
                "invalid function mapping row")
        require(re.fullmatch(r"0x[0-9a-fA-F]{8}", entry["rom"]) and
                re.fullmatch(r"0x[0-9a-fA-F]{8}", entry["end"]), "invalid mapped address")
        start, end = int(entry["rom"], 16), int(entry["end"], 16)
        require(ROM_BASE <= start < end <= ROM_BASE + len(fixed.rom.data) and
                entry["mode"] in ("thumb", "arm") and start % (2 if entry["mode"] == "thumb" else 4) == 0,
                "invalid mapped function bounds/mode")
        require(start not in entries, "duplicate mapped function")
        entries[start] = (end, entry["mode"])
    ordered = sorted(entries)
    require(all(entries[a][0] <= b for a, b in zip(ordered, ordered[1:])), "overlapping mapped functions")
    rows = {}
    for line in snapshots["function_text"].data.decode("utf-8").splitlines():
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        row = line.split()
        require(len(row) >= 3 and re.fullmatch(r"(?:0x)?[0-9A-Fa-f]{8}", row[0]) and
                re.fullmatch(r"(?:0x)?[0-9A-Fa-f]{8}", row[1]) and row[2].isdigit(), "invalid function text row")
        start, end = int(row[0], 16), int(row[1], 16)
        require(start not in rows and end - start == int(row[2]), "duplicate/incorrect function text extent")
        rows[start] = end
    require(rows == {start: end for start, (end, _) in entries.items()}, "function indexes disagree")
    named = {}
    covered = set()
    for line in snapshots["symbol_sizes"].data.decode("utf-8").splitlines():
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        row = line.split()
        require(len(row) == 3 and re.fullmatch(r"(?:0x)?[0-9A-Fa-f]{8}", row[0]) and
                re.fullmatch(r"[0-9A-Fa-f]+", row[1]), "invalid symbol-size row")
        start, size, name = int(row[0], 16), int(row[1], 16), row[2]
        validate(name, "Name")
        require(name not in named and start in entries and size == entries[start][0] - start,
                "symbol-size index disagrees")
        require(not name.startswith(("_call_via_", "__")), "runtime/stub binding unsupported")
        if name.startswith("func_"):
            require(name == f"func_{start:08X}", "canonical function name disagrees")
        named[name] = (start, entries[start][0], entries[start][1])
        covered.add(start)
    require(covered == set(entries), "symbol-size index omits a function")
    objects = private.decode(snapshots["data_symbols"].data.decode("utf-8"))
    require(type(objects) is dict, "invalid object index")
    for name, target in objects.items():
        validate(name, "Name")
        require(name not in named and type(target) is str and re.fullmatch(r"0x[0-9a-fA-F]{8}", target),
                "invalid/ambiguous object mapping")
    return named, {name: int(target, 16) for name, target in objects.items()}


def place_registration(raw, address, externals):
    """The closed agbcc grammar, extended only for mapped external words."""
    import switch_placement as placement
    _, prefix = placement.origin(address)
    require(type(raw) is bytes and len(raw) <= 1024 * 1024 and raw.endswith(b"\n"), "invalid raw assembly")
    try:
        text = raw.decode("ascii")
    except UnicodeError as error:
        raise Failure("identity", "non-ASCII assembly") from error
    require(all(character in "\n\t" or 32 <= ord(character) <= 126 for character in text), "invalid assembly character")
    lines = text.splitlines(keepends=True)
    name = f"func_{address:08X}"
    envelope = (r"@ Generated by gcc 2\.9-arm-000512 for Thumb/elf", r"\s*\.code\s+16",
                r"\.gcc2_compiled\.:", r"\.text", r"\s*\.align\s+2, 0", rf"\s*\.globl\s+{name}",
                rf"\s*\.type\s+{name},function", r"\s*\.thumb_func", rf"{name}:")
    require(len(lines) > len(envelope) and all(re.fullmatch(pattern, line.rstrip("\n"))
            for pattern, line in zip(envelope, lines)), "noncanonical compiler entry")
    labels, finished = set(), False
    for index, line in enumerate(lines[len(envelope):], len(envelope)):
        statement = line.strip()
        if not statement:
            continue
        require(not finished, "assembly after complete sized function")
        label = re.fullmatch(r"(\.L(?:fe|CB)?[0-9]+):", statement)
        word = re.fullmatch(r"\.word\s+(.+)", statement)
        end = re.fullmatch(rf"\.size\s+{name},(\.Lfe[0-9]+)-{name}", statement)
        if label:
            require(label[1] not in labels, "duplicate compiler local label")
            labels.add(label[1])
        elif re.fullmatch(r"\.align\s+2, 0", statement):
            continue
        elif word:
            expression = word[1]
            if not re.fullmatch(r"-?[0-9]+|0x[0-9a-fA-F]+|\.L[0-9]+(?:\+[0-9]+)?", expression):
                external = re.fullmatch(r"([A-Za-z_.$][A-Za-z0-9_.$]*)(?:\+([0-9]+))?", expression)
                require(external and external[1] in externals and int(external[2] or 0) == 0,
                        "unmapped or nonzero-addend external word")
        elif end:
            require(end[1] in labels and lines[index - 1].strip() == end[1] + ":", "invalid size label")
            finished = True
        else:
            annotated = re.fullmatch(r"(b(?:eq|ne|cs|cc|mi|pl|vs|vc|hi|ls|ge|lt|gt|le)\s+\.L[0-9]+)\s+@cond_branch", statement)
            annotated = annotated or re.fullmatch(r"(b\s+\.L[0-9]+)\s+@long jump", statement)
            if annotated:
                statement = annotated[1]
            instruction = re.fullmatch(r"([a-z]+)(?:\s+([a-zA-Z0-9_., #+!{}\[\]-]+))?", statement)
            require(instruction and instruction[1] in placement.MNEMONICS, "unsupported compiler statement")
            if instruction[1] == "bl":
                require(instruction[2] in externals and externals[instruction[2]]["kind"] == "function",
                        "unmapped direct callee")
    require(finished, "missing complete function size")
    position = sum(map(len, lines[:7]))
    return raw if not prefix else raw[:position] + placement.INSERTION + raw[position:]


def _elf(data):
    from match import elf_image
    try:
        image = elf_image(data)
        header = struct.unpack_from("<HHIIIIIHHHHHH", data, 16)
        require(header[2] == 1 and header[7] == 52 and header[11] == len(image["sections"]),
                "incorrect ELF header layout")
        require(len(image["symbol_tables"]) == 1, "ambiguous ELF symbol tables")
        names = image["section_data"][header[12]]
        section_names = []
        for index, section in enumerate(image["sections"]):
            section_names.append(names[section[0]:names.index(b"\0", section[0])].decode("ascii"))
            if index == 0:
                require(section == (0,) * 10, "incorrect null ELF section")
            else:
                require(section[8] == 0 or section[8] & (section[8] - 1) == 0, "invalid ELF section alignment")
                require(section[1] == 8 or section[4] >= 52, "ELF section overlaps header")
        require(len(section_names) == len(set(section_names)), "duplicate ELF section names")
        admitted = {"": (0, 0), ".text": (1, 6), ".rel.text": (9, 64), ".data": (1, 3),
                    ".bss": (8, 3), ".ARM.attributes": (0x70000003, 0), ".symtab": (2, 0),
                    ".strtab": (3, 0), ".shstrtab": (3, 0)}
        require(all(name in admitted and section[1:3] == admitted[name]
                    for name, section in zip(section_names, image["sections"])), "unexpected ELF section type/flags")
        extents = sorted((section[4], section[4] + section[5]) for section in image["sections"]
                         if section[1] != 8 and section[5])
        require(all(end <= next_start for (_, end), (next_start, _) in zip(extents, extents[1:])),
                "overlapping ELF section contents")
        for index, symbols in image["symbol_tables"].items():
            section = image["sections"][index]
            require(image["sections"][section[6]][1] == 3 and 0 < section[7] <= len(symbols),
                    "incorrect ELF symbol string/local table")
            require(all((symbol["bind"] == 0) == (position < section[7]) for position, symbol in enumerate(symbols)),
                    "incorrect ELF local/global symbol boundary")
        image["section_names"] = section_names
        return image
    except (ValueError, IndexError, KeyError, struct.error, UnicodeError) as error:
        raise Failure("identity", "malformed captured ELF") from error


def raw_symbol(image, table_index, index):
    symbols = image["symbol_tables"].get(table_index)
    require(symbols is not None and type(index) is int and 0 <= index < len(symbols), "dangling ELF symbol")
    _, value, size, info, other, section = struct.unpack_from("<IIIBBH", image["section_data"][table_index], index * 16)
    return {"table_section_index": table_index, "index": index, "name": symbols[index]["name"],
            "value": value, "size": size, "info": info, "other": other, "section_index": section}


def _symbols(image):
    return [raw_symbol(image, table, index) for table, symbols in image["symbol_tables"].items()
            for index in range(len(symbols))]


def _partition(assembly, image, address, size):
    prefix, offset = address % 4, 0
    labels, records = {}, []
    for line in assembly.decode("ascii").splitlines():
        statement = line.split("@", 1)[0].strip()
        if not statement:
            continue
        if statement.endswith(":"):
            labels[statement[:-1]] = offset
            continue
        if statement.startswith(".align"):
            end, role = (offset + 3) & ~3, "alignment"
        elif statement.startswith(".space"):
            require(statement == ".space\t2, 0" and offset == 0 and prefix == 2, "noncanonical prefix")
            end, role = offset + 2, "prefix"
        elif statement.startswith(".word"):
            end, role = offset + 4, "literal"
        elif statement.startswith("."):
            require(statement.split()[0] in (".code", ".text", ".globl", ".type", ".thumb_func", ".size"),
                    "unknown assembly partition directive")
            continue
        else:
            end, role = offset + (4 if statement.split()[0] == "bl" else 2), "instruction"
        if end > offset:
            records.append({"offset": offset, "size": end - offset, "role": role, "statement": statement})
            if role in ("alignment", "prefix"):
                require(image["text"][offset:end] == bytes(end - offset), "nonzero assembly alignment")
            if role == "literal":
                expression = statement.split(None, 1)[1]
                if re.fullmatch(r"-?[0-9]+|0x[0-9a-fA-F]+", expression):
                    require(struct.unpack_from("<I", image["text"], offset)[0] == int(expression, 0 if expression.startswith("0x") else 10) & 0xFFFFFFFF,
                            "literal differs from raw assembly")
        offset = end
    require(offset == prefix + size and labels.get(f"func_{address:08X}") == prefix,
            "assembly partition does not cover complete sized caller")
    return labels, records


def _envelope(image, address, *, linked):
    from match import allocated_text_only, function_record
    require(image["type"] == (2 if linked else 1), "incorrect ELF stage type")
    allocated_text_only(image)
    base, prefix = address - address % 4, address % 4
    symbol, offset = function_record(image, f"func_{address:08X}", address, True)
    text = image["sections"][image["text_index"]]
    end = prefix + symbol["size"]
    require(symbol["bind"] == 1 and symbol["size"] % 2 == 0 and offset == prefix and
            text[2] == 6 and text[3] == (base if linked else 0) and text[8] == 4 and
            len(image["text"]) == (end + 3) & ~3 and image["text"][:prefix] == bytes(prefix) and
            image["text"][end:] == bytes(len(image["text"]) - end), "incorrect complete caller envelope")
    for index, section in enumerate(image["sections"]):
        name = image["section_names"][index]
        require(name in ("", ".text", ".data", ".bss", ".ARM.attributes", ".symtab", ".strtab", ".shstrtab", ".rel.text"),
                "unexpected ELF section/owner")
        if name in (".data", ".bss"):
            require(section[5] == 0, "extra allocated ownership")
        require(section[1] != 4, "RELA is not admitted")
    return symbol["size"], len(image["text"]) - end


def _original_relocations(image, address, size, labels, records, named, objects, site):
    prefix = address % 4
    words = {record["offset"]: record["statement"].split(None, 1)[1]
             for record in records if record["role"] == "literal"}
    instructions = {record["offset"]: record for record in records if record["role"] == "instruction"}
    result, occupied, bindings = [], set(), {}
    sections = [symbol for symbol in _symbols(image) if symbol["info"] == 3 and
                symbol["section_index"] == image["text_index"]]
    require(len(sections) == 1, "ambiguous text section symbol")
    for section_index in image["relocations"]:
        section = image["sections"][section_index]
        require(section[1] == 9 and section[7] == image["text_index"] and section[9] == 8 and
                section[5] % 8 == 0 and section[6] in image["symbol_tables"], "invalid raw relocation section")
        for entry_index, (offset, info) in enumerate(struct.iter_unpack("<II", image["section_data"][section_index])):
            kind = info & 255
            require(kind in (2, 10) and prefix <= offset and offset + 4 <= prefix + size and
                    not occupied.intersection(range(offset, offset + 4)), "unknown/outside/overlapping raw relocation")
            occupied.update(range(offset, offset + 4))
            symbol = raw_symbol(image, section[6], info >> 8)
            raw = image["text"][offset:offset + 4]
            name = symbol["name"]
            caller_offset = offset - prefix
            common = {"caller_offset": caller_offset, "linked_address": address + caller_offset}
            if kind == 2 and symbol == sections[0]:
                require(not name and symbol["value"] == symbol["size"] == symbol["other"] == 0 and offset in words,
                        "incorrect original local section symbol")
                expression = re.fullmatch(r"(\.L[0-9]+)(?:\+([0-9]+))?", words[offset])
                addend = struct.unpack("<I", raw)[0]
                require(expression and expression[1] in labels and
                        addend == labels[expression[1]] + int(expression[2] or 0) and
                        prefix <= addend <= prefix + size - 2 and offset % 4 == 0,
                        "local raw addend/assembly ownership mismatch")
                resolved = dict(common, tag="local", addend=addend, target=address - prefix + addend)
            else:
                require(name and symbol["section_index"] == symbol["value"] == symbol["size"] == symbol["other"] == 0 and
                        symbol["info"] >> 4 == 1 and sum(item["name"] == name for item in _symbols(image)) == 1,
                        "incorrect original undefined external")
                if kind == 10:
                    require(offset in instructions and instructions[offset]["size"] == 4 and
                            instructions[offset]["statement"] == "bl\t" + name and raw == bytes.fromhex("fff7feff") and
                            name in named and symbol["info"] in (0x10, 0x12), "incorrect raw Thumb call")
                    role = "registration" if address + caller_offset == site else "ordinary-callee"
                    kind_name, addend = "function", -4
                else:
                    require(offset in words and re.fullmatch(re.escape(name) + r"(?:\+0)?", words[offset]) and
                            raw == bytes(4) and offset % 4 == 0, "incorrect external word/addend")
                    if name in objects:
                        require(objects[name] == 0x0200F430 and symbol["info"] in (0x10, 0x11), "incorrect manager-cell binding")
                        role, kind_name = "manager-cell", "object"
                    else:
                        require(name in named and symbol["info"] in (0x10, 0x12), "incorrect callback binding")
                        role, kind_name = "callback", "function"
                    addend = 0
                if kind_name == "function":
                    target, end, mode = named[name]
                    require(mode == "thumb" and (end <= address or target >= address + size),
                            "external function is not a disjoint Thumb body")
                else:
                    target = objects[name]
                binding = {"name": name, "role": role, "kind": kind_name, "target": target}
                require(name not in bindings or bindings[name] == binding, "conflicting external roles")
                bindings[name] = binding
                resolved = dict(common, tag=kind_name, addend=addend, target=target, binding=name,
                                role="callee" if kind == 10 else role)
            result.append({"section_index": section_index, "entry_index": entry_index,
                           "target_section_index": section[7], "raw_offset": offset, "raw_info": info,
                           "raw_record": image["section_data"][section_index][entry_index * 8:entry_index * 8 + 8].hex(),
                           "kind": kind, "symbol": symbol, "raw_bytes": raw.hex(), "resolved": resolved})
    expected = {record["offset"] for record in records if
                (record["role"] == "instruction" and record["statement"].startswith("bl\t")) or
                (record["role"] == "literal" and not re.fullmatch(r"-?[0-9]+|0x[0-9a-fA-F]+", words[record["offset"]]))}
    require({record["raw_offset"] for record in result} == expected, "missing/extra original relocation")
    require([binding["role"] for binding in bindings.values()].count("registration") == 1 and
            [binding["role"] for binding in bindings.values()].count("callback") == 1 and
            [binding["role"] for binding in bindings.values()].count("manager-cell") == 1,
            "incomplete/ambiguous operation external roles")
    return result, sorted(bindings.values(), key=lambda binding: binding["name"])


def _source_binding_agreement(preprocessed, bindings):
    """Closed declaration/use evidence, not a general C or ABI type checker.

    Accept one explicit extern prototype per referenced function and one
    explicit void-pointer manager object. Complex declarators, aliases,
    redeclarations and indirect role uses refuse rather than infer a type.
    The only input is the actual acquired fixed preprocessor output.
    """
    text = re.sub(r'^\s*#\s+\d+\s+"[^"\n]+"[^\n]*$', "", preprocessed.decode("utf-8"), flags=re.MULTILINE)
    tokens = re.findall(r'/\*.*?\*/|//[^\n]*|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|'
                        r'[A-Za-z_][A-Za-z_0-9]*|0[xX][0-9a-fA-F]+|[0-9]+[uUlL]*|->|[^\s]', text, re.DOTALL)
    tokens = [token for token in tokens if not token.startswith(("/*", "//"))]
    require("#" not in tokens, "unsupported preprocessed declaration directive")
    pairs, stack = {}, []
    for index, token in enumerate(tokens):
        if token in ("(", "[", "{"):
            stack.append(index)
        elif token in (")", "]", "}"):
            require(stack and tokens[stack[-1]] == {")": "(", "]": "[", "}": "{"}[token],
                    "unbalanced preprocessed declaration")
            beginning = stack.pop()
            pairs[beginning] = index
    require(not stack, "unbalanced preprocessed declaration")
    # Top-level semicolon units distinguish declarations from local statements
    # and struct fields. Function bodies end a unit without a semicolon.
    units, start, depth, function_body = [], 0, 0, False
    for index, token in enumerate(tokens):
        if token == "{":
            if depth == 0:
                function_body = index > start and tokens[index - 1] == ")" and tokens[start] != "typedef"
            depth += 1
        elif token == "}":
            depth -= 1
            if depth == 0 and function_body:
                start, function_body = index + 1, False
        elif token == ";" and depth == 0:
            units.append((start, index + 1))
            start = index + 1
    declarations = set()
    by_role = {}
    for binding in bindings:
        name, kind = binding["name"], binding["kind"]
        require(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", name), "unsupported C external identifier")
        matches = [(begin, end) for begin, end in units if name in tokens[begin:end]]
        require(len(matches) == 1, "missing/ambiguous source declaration: " + name)
        begin, end = matches[0]
        unit = tokens[begin:end]
        require(unit.count(name) == 1 and unit[0] == "extern", "unsupported source declaration: " + name)
        position = begin + unit.index(name)
        before, after = tokens[begin + 1:position], tokens[position + 1:end]
        if kind == "function":
            require(before and any(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", token) for token in before) and
                    all(token == "*" or re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", token) for token in before) and
                    after and after[0] == "(" and pairs.get(position + 1) == end - 2,
                    "function binding contradicts source declaration: " + name)
            parameters = tokens[position + 2:end - 2]
            require(parameters and all(token in ("*", ",") or re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", token)
                                       for token in parameters), "unsupported function prototype: " + name)
        else:
            require(kind == "object" and binding["role"] == "manager-cell" and after == [";"] and
                    [token for token in before if token not in ("const", "volatile")] == ["void", "*"],
                    "manager object binding contradicts source declaration: " + name)
        declarations.update(range(begin, end))
        by_role.setdefault(binding["role"], []).append(name)
    require(all(len(by_role.get(role, [])) == 1 for role in ("registration", "callback", "manager-cell")),
            "ambiguous source binding roles")
    registration, callback, manager = (by_role[role][0] for role in ("registration", "callback", "manager-cell"))
    uses = {binding["name"]: [index for index, token in enumerate(tokens)
                              if token == binding["name"] and index not in declarations] for binding in bindings}
    approved = set()
    for position in uses[registration]:
        require(position + 1 < len(tokens) and tokens[position + 1] == "(" and
                (position == 0 or tokens[position - 1] not in (".", "->", "&", "*")),
                "unsupported registration source use")
        closing = pairs[position + 1]
        arguments, beginning, index = [], position + 2, position + 2
        while index < closing:
            if tokens[index] in ("(", "[", "{"):
                index = pairs[index] + 1
            elif tokens[index] == ",":
                arguments.append((beginning, index))
                beginning, index = index + 1, index + 1
            else:
                index += 1
        arguments.append((beginning, closing))
        require(len(arguments) == 5 and tokens[slice(*arguments[0])] == [manager] and
                tokens[slice(*arguments[1])] in ([callback], ["&", callback]),
                "source declaration/registration role use disagrees")
        approved.add(position)
        approved.add(arguments[0][0])
        approved.add(arguments[1][1] - 1)
    for binding in bindings:
        positions = uses[binding["name"]]
        require(positions, "source declaration lacks referenced external use: " + binding["name"])
        if binding["role"] == "ordinary-callee":
            require(all(position + 1 < len(tokens) and tokens[position + 1] == "(" and
                        (position == 0 or tokens[position - 1] not in (".", "->", "&", "*"))
                        for position in positions), "unsupported ordinary callee source use")
        else:
            require(all(position in approved for position in positions), "unsupported/ambiguous external role source use")


def _symbol_ownership(image, address, size, bindings, records, *, stage):
    prefix, base = address % 4, address - address % 4
    symbols = _symbols(image)
    expected = {binding["name"]: binding for binding in bindings}
    definitions = {}
    seen_caller = 0
    seen_sections = set()
    mappings = []
    for symbol in symbols:
        name, info, section = symbol["name"], symbol["info"], symbol["section_index"]
        require(symbol["other"] == 0, "unexpected ELF symbol visibility")
        if symbol["index"] == 0:
            require(not name and symbol["value"] == symbol["size"] == info == section == 0, "incorrect null symbol")
        elif name in expected:
            require(name not in definitions, "duplicate external symbol")
            binding = expected[name]
            typed_info = 0x12 if binding["kind"] == "function" else 0x11
            if stage == "original":
                require(info in (0x10, typed_info) and symbol["value"] == symbol["size"] == section == 0,
                        "incorrect raw undefined external ownership")
            else:
                require(info == typed_info and section == 0xFFF1 and
                        symbol["value"] == binding["target"] | (binding["kind"] == "function") and
                        symbol["size"] == (2 if binding["kind"] == "function" else 4), "incorrect typed absolute binding")
            definitions[name] = symbol
        elif stage == "binding" and info == 3 and not name:
            require(0 < section < len(image["sections"]) and symbol["size"] == symbol["value"] == 0,
                    "incorrect binding section symbol")
            require(section not in seen_sections, "duplicate ELF section symbol")
            seen_sections.add(section)
        elif stage == "binding":
            raise Failure("identity", "extra binding definition")
        elif name == f"func_{address:08X}":
            seen_caller += 1
            require(info == 0x12 and section == image["text_index"] and symbol["size"] == size and
                    symbol["value"] == ((address if stage == "linked" else prefix) | 1), "incorrect caller ownership")
        elif info == 3 and not name:
            require(0 < section < len(image["sections"]) and symbol["size"] == 0 and
                    symbol["value"] == (image["sections"][section][3] if stage == "linked" else 0),
                    "incorrect section symbol")
            require(section not in seen_sections, "duplicate ELF section symbol")
            seen_sections.add(section)
        elif name == ".gcc2_compiled.":
            require(info == 0 and section == image["text_index"] and symbol["size"] == 0 and
                    symbol["value"] == (base if stage == "linked" else 0), "incorrect compiler entry tag")
        elif name in ("$t", "$d"):
            offset = symbol["value"] - (base if stage == "linked" else 0)
            require(info == 0 and section == image["text_index"] and symbol["size"] == 0,
                    "incorrect code/data mapping symbol")
            mappings.append((offset, name))
        elif stage == "linked" and name == "caller.o":
            require(info == 4 and section == 0xFFF1 and symbol["size"] == symbol["value"] == 0,
                    "incorrect linker input-file symbol")
        else:
            raise Failure("identity", "unowned ELF symbol: " + name)
    require(set(definitions) == set(expected) and (stage == "binding" or seen_caller == 1),
            "missing/extra ELF ownership")
    if stage != "binding":
        expected_mappings = []
        for record in records:
            name = "$t" if record["role"] == "instruction" else "$d"
            if not expected_mappings or expected_mappings[-1][1] != name:
                expected_mappings.append((record["offset"], name))
        end = prefix + size
        if end < len(image["text"]) and expected_mappings[-1][1] != "$d":
            expected_mappings.append((end, "$d"))
        require(sorted(mappings) == expected_mappings, "code/data mapping intervals disagree with complete partition")
    if stage == "binding":
        require(image["type"] == 1 and not image["relocations"] and
                all(not section[5] for section in image["sections"] if section[2] & 2),
                "binding object contains a body/relocation")
        require(all(name in ("", ".text", ".data", ".bss", ".ARM.attributes", ".symtab", ".strtab", ".shstrtab")
                    for name in image["section_names"]), "unexpected binding object section")
    return definitions


def _linked_records(original, linked, address, relocations, records):
    from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
    from capstone.arm import ARM_OP_IMM
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    decoder.detail = True
    require(not linked["relocations"] and len(original["text"]) == len(linked["text"]), "linked extent/relocation drift")
    changed = set()
    for relocation in relocations:
        offset, kind, resolved = relocation["raw_offset"], relocation["kind"], relocation["resolved"]
        after = linked["text"][offset:offset + 4]
        if kind == 2:
            target = resolved["target"] | (resolved["tag"] == "function")
            require(struct.unpack("<I", after)[0] == target, "incorrect linked ABS32 word")
        else:
            instructions = list(decoder.disasm(after, resolved["linked_address"]))
            require(len(instructions) == 1 and instructions[0].size == 4 and instructions[0].mnemonic == "bl" and
                    len(instructions[0].operands) == 1 and instructions[0].operands[0].type == ARM_OP_IMM and
                    instructions[0].operands[0].imm == resolved["target"], "incorrect linked Thumb call")
        resolved["linked_bytes"] = after.hex()
        changed.update(range(offset, offset + 4))
    require(all(before == after for index, (before, after) in enumerate(zip(original["text"], linked["text"]))
                if index not in changed), "nonrelocated caller byte changed")
    instructions = {}
    base = address - address % 4
    for record in records:
        if record["role"] == "instruction":
            offset, size = record["offset"], record["size"]
            decoded = list(decoder.disasm(linked["text"][offset:offset + size], base + offset))
            require(len(decoded) == 1 and decoded[0].size == size, "instruction ownership/width mismatch")
            instructions[offset - address % 4] = decoded[0]
    return instructions


def _switch(linked, address, size, relocations, records, instructions):
    from capstone.arm import ARM_OP_MEM, ARM_REG_PC, ARM_OP_REG
    from switch_constants_profile import layout
    prefix = address % 4
    body = linked["text"][prefix:prefix + size]
    local = {record["resolved"]["caller_offset"]: record["resolved"]["target"] - address
             for record in relocations if record["resolved"]["tag"] == "local"}
    descriptor = layout(body, address, local)
    literal, table, bound = descriptor["literal"], descriptor["table"], descriptor["bound"]
    literal_sites = {record["offset"] - prefix for record in records if record["role"] == "literal"}
    require(set(local).issubset(literal_sites) and all(offset in instructions for offset in
            (descriptor["comparison"], descriptor["guard"], descriptor["default"],
             *range(descriptor["dispatch"], descriptor["dispatch"] + 10, 2))), "switch leaves owned instructions/literals")
    if descriptor["dispatch"] - descriptor["comparison"] == 6:
        require(descriptor["guard"] + 2 in instructions, "default branch leaves owned instructions")
    loads = {}
    for offset, instruction in instructions.items():
        if instruction.mnemonic == "ldr" and len(instruction.operands) == 2:
            operand = instruction.operands[1]
            if operand.type == ARM_OP_MEM and operand.mem.base == ARM_REG_PC and not operand.mem.index:
                target = ((instruction.address + 4) & ~3) + operand.mem.disp - address
                require(target in literal_sites, "PC-relative load leaves owned literals")
                loads.setdefault(target, []).append(offset)
    constants = []
    for offset in (literal - 8, literal - 4):
        require(offset in literal_sites and offset not in local and loads.get(offset), "missing interposed scalar constant load")
        # This slice establishes actual local mask use. Whole-CFG raw-root and
        # reachability provenance remain the later caller execution obligation.
        for load in loads[offset]:
            instruction = instructions[load]
            register = instruction.operands[0].reg
            used = False
            for next_offset in sorted(site for site in instructions if site > load):
                following = instructions[next_offset]
                if following.mnemonic == "ands" and any(operand.type == ARM_OP_REG and operand.reg == register
                                                          for operand in following.operands):
                    used = True
                    break
                _, written = following.regs_access()
                if register in written or following.mnemonic.startswith("b"):
                    break
            require(used, "interposed constant lacks actual mask use")
        constants.append({"offset": offset, "value": struct.unpack_from("<I", body, offset)[0],
                          "loads": sorted(set(loads[offset]))})
    targets = []
    by_offset = {record["resolved"]["caller_offset"]: record for record in relocations
                 if record["resolved"]["tag"] == "local"}
    for index in range(bound + 1):
        word = table + index * 4
        require(local[word] in instructions, "switch case is not an owned instruction start")
        record = by_offset[word]
        record["resolved"]["role"] = "case-target"
        targets.append({"index": index, "word_offset": word, "target_offset": local[word],
                        "relocation": {"section_index": record["section_index"], "entry_index": record["entry_index"]}})
    by_offset[literal]["resolved"]["role"] = "table-base"
    require(set(local) == {literal, *(table + index * 4 for index in range(bound + 1))}, "extra local relocation")
    return {"layout": "bhi" if descriptor["dispatch"] - descriptor["comparison"] == 4 else "bls-b",
            "comparison_offset": descriptor["comparison"], "guard_offset": descriptor["guard"],
            "default_branch_offset": None if descriptor["dispatch"] - descriptor["comparison"] == 4 else descriptor["guard"] + 2,
            "dispatch_offset": descriptor["dispatch"], "default_offset": descriptor["default"],
            "literal_offset": literal, "table_offset": table, "bound": bound, "targets": targets, "constants": constants}


def _binding_assembly(bindings):
    lines = [".syntax unified", ".thumb"]
    for binding in bindings:
        name, kind, target = binding["name"], binding["kind"], binding["target"]
        lines.extend((f".global {name}", f".type {name}, %{kind}", f".size {name}, {2 if kind == 'function' else 4}",
                      f".{ 'thumb_set' if kind == 'function' else 'set'} {name}, 0x{target | (kind == 'function'):08X}"))
    return ("\n".join(lines) + "\n").encode("ascii")


def _linker_script(address):
    return f'''SECTIONS {{
    .text 0x{address - address % 4:08X} : {{ *(.text) *(.glue_7) *(.glue_7t) }}
    .data 0 : {{ *(.data) }}
    .bss 0 : {{ *(.bss) }}
    .ARM.attributes 0 : {{ *(.ARM.attributes) }}
    .unexpected 0 : {{ *(.vfp11_veneer) *(.v4_bx) *(.iplt) *(.igot.plt) }}
    .rel.iplt 0 : {{ *(.rel.iplt) }}
    ASSERT(SIZEOF(.unexpected) == 0, "unexpected linker stubs")
    ASSERT(SIZEOF(.rel.iplt) == 0, "unexpected dynamic relocations")
    /DISCARD/ : {{ *(.comment) *(.note.GNU-stack) }}
}}
'''.encode("ascii")


def _dependencies(data, source, sources, root):
    allowed = {str((root / private.decode(artifact.path_json)["path"]).absolute()) for artifact in sources}
    observed = set()
    for name in re.findall(r'^#\s+\d+\s+"([^"\n]+)"', data.decode("utf-8"), re.MULTILINE):
        if name in ("<built-in>", "<command-line>"):
            continue
        path = Path(name)
        normalized = str(Path(os.path.normpath(path if path.is_absolute() else root / path)))
        require(normalized in allowed, "escaped/untracked preprocessor dependency")
        observed.add(normalized)
    require(str(root / source) in observed, "preprocessor lacks addressed source marker")


def _run(command, root, temporary):
    # Same process-group/timeout discipline as match._run_replay_process;
    # this small variant supplies a private TMPDIR without mutating os.environ.
    environment = dict(os.environ, TMPDIR=str(temporary), PYTHONDONTWRITEBYTECODE="1")
    try:
        with subprocess.Popen(command, cwd=root, env=environment, stdout=subprocess.PIPE,
                              stderr=subprocess.PIPE, text=True, start_new_session=True) as process:
            try:
                stdout, stderr = process.communicate(timeout=CAPTURE_TIMEOUT)
            except BaseException:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                process.communicate()
                raise
        require(process.returncode == 0, "fixed tool failed: " + command[0] + ": " + stderr[-4096:])
        return tuple(command), process.returncode, stdout, stderr
    except (OSError, subprocess.TimeoutExpired, UnicodeError) as error:
        raise Failure("identity", "fixed tool could not complete: " + command[0]) from error


def _disk_workspace(path, acquisition):
    path = Path(path).absolute()
    validate(str(path), "HostPath")
    require(not any(path == root or root in path.parents for root in acquisition.roots.values()),
            "capture workspace must be outside acquired input roots")
    # The engine owns this location. Refuse tmpfs even through an otherwise
    # ordinary directory spelling; no trust/input selector can override it.
    mounts = []
    with open("/proc/self/mountinfo", encoding="ascii") as stream:
        for line in stream:
            before, after = line.rstrip().split(" - ", 1)
            mount = Path(before.split()[4].replace("\\040", " "))
            if path == mount or mount in path.parents:
                mounts.append((len(mount.parts), after.split()[0]))
    require(mounts and max(mounts)[1] not in ("tmpfs", "ramfs"), "capture workspace is not disk backed")
    require(path.is_dir() and path.resolve() == path, "capture workspace is not an ordinary resolved directory")
    return path


@dataclass(frozen=True)
class BoundCapture:
    """Internal S1 capture only; caller semantics and public admission absent."""
    fixed: FixedInputs
    artifacts: tuple
    encoded: str
    commands: tuple

    def to_dict(self):
        return private.decode(self.encoded)


def capture_caller(acquisition, address, workspace):
    """Acquire, freshly compile/link, and compare the complete mapped caller.

    All captured stage bytes are returned in memory. Owned stage directories
    are removed on both success and refusal. No report or certificate exists.
    Rechecks are sequential; they do not create an atomic filesystem snapshot.
    """
    try:
        return _capture_caller(acquisition, address, _disk_workspace(workspace, acquisition))
    except Failure:
        raise
    except (OSError, ValueError, IndexError, KeyError, TypeError, struct.error, UnicodeError) as error:
        raise Failure("identity", "invalid fixed capture input or ELF: " + str(error)) from error


def _capture_caller(acquisition, address, workspace):
    from inert_spin_profile import validate_span
    fixed = acquire_fixed_inputs(acquisition, address)
    named, objects = _maps(fixed)
    require(f"func_{address:08X}" in named and named[f"func_{address:08X}"][0] == address,
            "caller missing from symbol-size index")
    tools = {tool["role"]: tool["resolved"] for tool in fixed.to_dict()["tools"]}
    externals = {name: {"kind": "function"} for name in named if name != f"func_{address:08X}"}
    externals.update({name: {"kind": "object"} for name, target in objects.items() if target == 0x0200F430})
    commands, captures = [], {}
    with tempfile.TemporaryDirectory(prefix="registration-", dir=workspace) as directory:
        directory = Path(directory)
        stages = {name: directory / name for name in (
            "source", "temporary", "preprocessed", "raw", "placed", "original", "original-binary", "binding-source", "binding",
            "script", "linked", "linked-binary")}
        for path in stages.values():
            path.mkdir()
        for artifact in fixed.sources:
            destination = stages["source"] / private.decode(artifact.path_json)["path"]
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(artifact.data)
        with Acquisition(game_root=stages["source"], kit_root=acquisition.roots["kit"]) as generated:
            staged_source, staged_sources = generated.sources(address)
            require(staged_source == fixed.source and [(item.path_json, item.data) for item in staged_sources] ==
                    [(item.path_json, item.data) for item in fixed.sources], "isolated sources differ")

            def recheck():
                acquisition.recheck()
                generated.recheck()
                # A generated-stage read can mutate an already-read fixed
                # input. Complete the metadata sweep across both owners.
                acquisition._recheck_metadata()
                generated._recheck_metadata()

            def run(role, arguments):
                recheck()
                commands.append(_run([tools[role], *map(str, arguments)], stages["source"], stages["temporary"]))
                recheck()

            def take(label, path):
                artifact = generated.acquire({"root": "host", "path": str(path)})
                captures[label] = artifact.data
                recheck()
                return artifact.data

            preprocessed = stages["preprocessed"] / "caller.i"
            run("cpp", ("-nostdinc", "-undef", "-I", "include", fixed.source, "-o", preprocessed))
            data = take("preprocessed", preprocessed)
            _dependencies(data, staged_source, staged_sources, stages["source"])
            raw = stages["raw"] / "caller.raw.s"
            run("cc", (*FLAGS.split(), preprocessed, "-o", raw))
            data = take("raw_assembly", raw)
            placed = stages["placed"] / "caller.s"
            placed.write_bytes(place_registration(data, address, externals))
            data = take("placed_assembly", placed)
            original_path, original_bin = stages["original"] / "caller.o", stages["original-binary"] / "caller.bin"
            run("assembler", ("-mthumb-interwork", placed, "-o", original_path))
            original = _elf(take("original_elf", original_path))
            run("objcopy", ("-O", "binary", "--only-section=.text", original_path, original_bin))
            require(take("original_binary", original_bin) == original["text"], "original objcopy differs from ELF text")
            size, suffix = _envelope(original, address, linked=False)
            labels, records = _partition(data, original, address, size)
            require(named[f"func_{address:08X}"] == (address, address + size, "thumb"), "caller map extent differs")
            relocations, bindings = _original_relocations(original, address, size, labels, records, named, objects,
                                                         fixed.request.to_dict()["site"])
            _source_binding_agreement(captures["preprocessed"], bindings)
            _symbol_ownership(original, address, size, bindings, records, stage="original")
            binding_source = stages["binding-source"] / "bindings.s"
            binding_source.write_bytes(_binding_assembly(bindings))
            take("binding_assembly", binding_source)
            binding_path = stages["binding"] / "bindings.o"
            run("assembler", ("-mthumb-interwork", binding_source, "-o", binding_path))
            binding_image = _elf(take("binding_elf", binding_path))
            binding_symbols = _symbol_ownership(binding_image, address, size, bindings, records, stage="binding")
            script = stages["script"] / "caller.ld"
            script.write_bytes(_linker_script(address))
            take("linker_script", script)
            linked_path, linked_bin = stages["linked"] / "caller.elf", stages["linked-binary"] / "caller.bin"
            run("linker", ("--fatal-warnings", "--no-undefined", "--no-relax", "--orphan-handling=error",
                           "-T", script, "-e", f"func_{address:08X}", original_path, binding_path, "-o", linked_path))
            linked = _elf(take("linked_elf", linked_path))
            run("objcopy", ("-O", "binary", "--only-section=.text", linked_path, linked_bin))
            require(take("linked_binary", linked_bin) == linked["text"], "linked objcopy differs from ELF text")
            require(_envelope(linked, address, linked=True) == (size, suffix), "linked complete envelope differs")
            linked_symbols = _symbol_ownership(linked, address, size, bindings, records, stage="linked")
            for binding in bindings:
                binding["symbol"] = binding_symbols[binding["name"]]
                binding["linked_symbol"] = linked_symbols[binding["name"]]
            instructions = _linked_records(original, linked, address, relocations, records)
            switch = _switch(linked, address, size, relocations, records, instructions)
            prefix = address % 4
            body = linked["text"][prefix:prefix + size]
            snapshots = dict(fixed.maps)
            validate_span(body, address, fixed.rom.data, snapshots["functions"].data, snapshots["function_text"].data)
            spans = {"instruction": [], "literal": [], "alignment": []}
            for record in records:
                if record["role"] != "prefix":
                    spans[record["role"]].append({"start": address + record["offset"] - prefix,
                                                   "end": address + record["offset"] - prefix + record["size"]})
            caller = {"id": f"body/{address:08X}", "role": "caller", "start": address, "end": address + size,
                      "sha256": hashlib.sha256(body).hexdigest(), "code": spans["instruction"],
                      "literals": spans["literal"], "alignment": spans["alignment"], "runtime_start": None}
            placement = {"rule": PLACEMENT_RULE, "section_base": address - prefix, "function_offset": prefix,
                         "prefix_size": prefix, "suffix_size": suffix, "bindings": bindings,
                         **{label: private.pin(data) for label, data in captures.items()}}
            result = {"inputs": fixed.to_dict(), "caller": caller, "placement": placement,
                      "relocations": relocations, "switch": switch}
            recheck()
            capture = BoundCapture(fixed, tuple(captures.items()), canonical(result), tuple(commands))
        acquisition._recheck_metadata()
    acquisition._recheck_metadata()
    return capture
