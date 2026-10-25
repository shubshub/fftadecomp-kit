"""Inactive registration foundation: capture and decoded execution prefixes.

The retained helper API stops before S3 retirement. The additive restoration
API continues proved corridors to registration entry; both remain incomplete
and supply no completed public history, registration proof or public report.
"""

from dataclasses import dataclass
import copy
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
    "S2b: independent review of bounded decoded helper execution and state facts",
    "P5: lossless schema representation and complete histories/coverage",
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


# These are refusal limits, never widening or successful partial-proof limits.
MAX_CALLER_STATES = 4096
MAX_CALLER_TRANSFERS = 262144
MAX_CALLER_DEPTH = 16
_ZERO_DIGEST = "0" * 64
_BRANCH_CHOICES = (1, 0)


class _CallerBudget:
    def __init__(self):
        self.states = 0
        self.transfers = 0

    def state(self):
        self.states += 1
        require(self.states <= MAX_CALLER_STATES, "caller state budget exhausted", "unsupported")

    def transfer(self):
        self.transfers += 1
        require(self.transfers <= MAX_CALLER_TRANSFERS, "caller transfer budget exhausted", "unsupported")


@dataclass(frozen=True)
class CallerPrefixes:
    """Internal, incomplete execution only; deliberately not a P5 PathHistory.

    The bit sidecar is required to interpret partially known scalar bytes.
    These records cannot be imported as a public State or a certificate.
    """
    encoded: str

    def inspect(self):
        return private.decode(self.encoded)


def _caller_program(capture):
    """Reconstruct the already bound original/linked ownership, then close CFG."""
    require(type(capture) is BoundCapture, "caller execution requires a bound capture")
    record, artifacts = capture.to_dict(), dict(capture.artifacts)
    require(set(record) == {"inputs", "caller", "placement", "relocations", "switch"} and
            record["inputs"] == capture.fixed.to_dict(), "capture fixed inputs differ")
    labels_required = {"preprocessed", "raw_assembly", "placed_assembly", "original_elf", "original_binary",
                       "binding_assembly", "binding_elf", "linker_script", "linked_elf", "linked_binary"}
    require(set(artifacts) == labels_required, "capture stage inventory differs")
    require(len(artifacts) == len(capture.artifacts), "duplicate capture artifact")
    for label, data in artifacts.items():
        require(record["placement"][label] == private.pin(data), "capture artifact pin differs")
    address = capture.fixed.address
    original, linked = _elf(artifacts["original_elf"]), _elf(artifacts["linked_elf"])
    size, suffix = _envelope(original, address, linked=False)
    require(_envelope(linked, address, linked=True) == (size, suffix), "capture envelope differs")
    require(artifacts["original_binary"] == original["text"] and artifacts["linked_binary"] == linked["text"],
            "capture binary differs")
    labels, partition = _partition(artifacts["placed_assembly"], original, address, size)
    named, objects = _maps(capture.fixed)
    relocations, bindings = _original_relocations(original, address, size, labels, partition, named, objects,
                                                  capture.fixed.request.to_dict()["site"])
    _source_binding_agreement(artifacts["preprocessed"], bindings)
    _symbol_ownership(original, address, size, bindings, partition, stage="original")
    bound_symbols = _symbol_ownership(_elf(artifacts["binding_elf"]), address, size, bindings, partition, stage="binding")
    linked_symbols = _symbol_ownership(linked, address, size, bindings, partition, stage="linked")
    for binding in bindings:
        binding.update(symbol=bound_symbols[binding["name"]], linked_symbol=linked_symbols[binding["name"]])
    require(artifacts["binding_assembly"] == _binding_assembly(bindings) and
            artifacts["linker_script"] == _linker_script(address), "capture binding/script bytes differ")
    require(record["placement"] == {"rule": PLACEMENT_RULE, "section_base": address - address % 4,
                                    "function_offset": address % 4, "prefix_size": address % 4, "suffix_size": suffix,
                                    "bindings": bindings, **{label: private.pin(data) for label, data in artifacts.items()}},
            "capture placement differs")
    instructions = _linked_records(original, linked, address, relocations, partition)
    switch = _switch(linked, address, size, relocations, partition, instructions)
    require(relocations == record["relocations"] and switch == record["switch"], "capture resolution differs")
    body = linked["text"][address % 4:address % 4 + size]
    require(body == capture.fixed.rom.data[address - ROM_BASE:address - ROM_BASE + size] and
            hashlib.sha256(body).hexdigest() == record["caller"]["sha256"], "capture caller bytes differ")
    expected = {"instruction": "code", "literal": "literals", "alignment": "alignment"}
    for role, key in expected.items():
        require(record["caller"][key] == [{"start": address + item["offset"] - address % 4,
                                           "end": address + item["offset"] - address % 4 + item["size"]}
                                          for item in partition if item["role"] == role], "capture partition differs")
    require(record["caller"]["start"] == address and record["caller"]["end"] == address + size,
            "capture caller extent differs")
    require(record["caller"]["id"] == f"body/{address:08X}" and record["caller"]["role"] == "caller" and
            record["caller"]["runtime_start"] is None, "capture caller identity differs")
    program = {address + offset: instruction for offset, instruction in instructions.items()}
    calls = {item["resolved"]["linked_address"]: item["resolved"] for item in relocations if item["kind"] == 10}
    _closed_caller_cfg(program, calls, switch, address)
    return record, program, calls


def _closed_caller_cfg(program, calls, switch, address):
    from capstone.arm import ARM_OP_IMM, ARM_OP_REG
    branches = {"beq", "bne", "bhi", "bls", "bhs", "blo"}
    allowed = {"push", "pop", "mov", "movs", "add", "adds", "sub", "subs", "lsls", "lsrs", "asrs",
               "ands", "orrs", "cmp", "ldr", "ldrb", "ldrh", "str", "strb", "strh", "b", "bl", "bx", "nop"} | branches
    edges = {}
    require(address in program, "caller CFG lacks entry instruction")
    for pc, insn in program.items():
        require(pc == insn.address and insn.size in (2, 4), "caller instruction coordinates differ")
        mnemonic, operands = insn.mnemonic, insn.operands
        require(mnemonic in allowed, "unsupported caller instruction: " + mnemonic, "unsupported")
        following = pc + insn.size
        names = [private.Checker.regname(insn, operand.reg) for operand in operands if operand.type == ARM_OP_REG]
        if mnemonic == "bl":
            require(pc in calls and len(operands) == 1 and operands[0].type == ARM_OP_IMM and
                    calls[pc]["target"] == operands[0].imm, "caller call binding differs")
            targets = [following]
        elif mnemonic == "bx" or mnemonic == "pop" and "pc" in names:
            require(mnemonic == "pop" or len(operands) == 1 and operands[0].type == ARM_OP_REG,
                    "malformed caller return")
            targets = []
        elif mnemonic == "mov" and names and names[0] == "pc":
            require(pc == address + switch["dispatch_offset"] + 8, "unclassified computed caller transfer")
            targets = [address + item["target_offset"] for item in switch["targets"]]
        elif mnemonic == "b" or mnemonic in branches:
            require(len(operands) == 1 and operands[0].type == ARM_OP_IMM, "malformed caller branch")
            targets = [operands[0].imm] + ([] if mnemonic == "b" else [following])
        else:
            require("pc" not in names[:1], "unsupported caller PC write")
            targets = [following]
        require(all(target in program for target in targets), "caller edge targets non-instruction bytes")
        edges[pc] = tuple(targets)
    reached, pending = set(), [address]
    while pending:
        pc = pending.pop()
        if pc not in reached:
            reached.add(pc)
            pending.extend(edges[pc])
    require(reached == set(program), "caller CFG omits owned instructions")
    return edges


class _CallerState:
    """Private-shaped provenance records plus exact internal scalar bit facts."""

    base = private.Checker.base
    interval = private.Checker.interval
    overlap = private.Checker.overlap
    key = private.Checker.key
    equivalent = private.Checker.equivalent

    def __init__(self, context, body, rom=b""):
        view = _Entry(context)
        require(len(view.frames) <= MAX_CALLER_DEPTH, "caller frame depth exhausted", "unsupported")
        self.context = copy.deepcopy(context)
        self.values, self.regions, self.frames = copy.deepcopy((view.values, view.regions, view.frames))
        self.memory = copy.deepcopy(view.memory)
        self.memory_bits = {}
        self.registers = dict(context["registers"], sp=context["sp"], lr=context["lr"])
        self.body = body
        self.pc = body["start"]
        self.events, self.decisions, self.edges = [], [], []
        self.bits, self.domains, self.counters = {}, {}, {}
        self.flags = None
        self.switch_choice = None
        self.comparisons = []
        self.conditionals = []
        self.saves = {}
        self.touched = set()
        self.restore_steps = {register: [] for register in private.NONVOLATILE}
        self.restored_by = {}
        self.literal_bindings = {}
        self.literal_values = {}
        self.function_targets = {}
        for frame in self.frames.values():
            for save in frame["saves"]:
                self.saves[save["witness"]] = {"record": save, "created": None, "consumed": None}
        self.stack_region = self.values[context["sp"]]["region"]
        require(self.regions[self.stack_region]["kind"] == "stack-domain", "caller SP requires backing domain", "unsupported")
        self.stack_anchor, self.stack_base = self.base(self.stack_region)
        self.rom = rom
        if rom:
            for region in self.regions.values():
                anchor, start = self.base(region["id"])
                if anchor == "concrete" and max(start, ROM_BASE) < min(start + region["size"], ROM_BASE + len(rom)):
                    require(region["kind"] == "rom" and region["permission"] == "r" and
                            ROM_BASE <= start < start + region["size"] <= ROM_BASE + len(rom),
                            "entry storage contradicts bound ROM ownership", "contradictory-condition")
            for key, part in self.memory.items():
                if key[0] == "concrete" and ROM_BASE <= key[1] < ROM_BASE + len(rom):
                    require(part == {"tag": "constant", "value": rom[key[1] - ROM_BASE]},
                            "entry cell contradicts bound ROM bytes", "contradictory-condition")
        identifier = self.new_id("r")
        self.regions[identifier] = {"id": identifier, "base": {"tag": "concrete", "address": body["start"]},
                                    "size": body["end"] - body["start"], "permission": "r", "kind": "rom",
                                    "lifetime": "live", "frame": None}

    def new_id(self, kind):
        ordinal = self.counters.get(kind, 0)
        require(ordinal < 1000000, "caller identity ordinal exhausted", "unsupported")
        self.counters[kind] = ordinal + 1
        return f"pub/{kind}/{_ZERO_DIGEST}/{ordinal:06d}"

    def event(self, tag, **members):
        self.events.append({"tag": tag, "step": len(self.events),
                            "location": {"body": self.body["id"], "pc": self.pc}, **members})

    def make(self, tag, **members):
        identifier = self.new_id("v")
        self.values[identifier] = {"id": identifier, "tag": tag, **members}
        return identifier

    def constant(self, number):
        require(0 <= number <= 0xffffffff, "wrapping scalar arithmetic", "unsupported")
        return self.make("constant", width=4, value=number)

    def pointer(self, region, offset):
        require(0 <= offset <= self.regions[region]["size"], "caller pointer outside storage", "local-effect")
        return self.make("pointer", region=region, offset=offset)

    def fragments(self, reference, active=()):
        require(reference not in active and len(active) < MAX_CALLER_DEPTH, "caller provenance depth exhausted", "unsupported")
        value = self.values[reference]
        if value["tag"] in ("pointer", "function", "control"):
            return {reference}
        if value["tag"] == "constant" and any(region["kind"] == "stack-allocation" and
                self.base(region["id"])[0] == "concrete" and self.base(region["id"])[1] <= value["value"] <=
                self.base(region["id"])[1] + region["size"] for region in self.regions.values()):
            return {reference}
        if value["tag"] == "bytes":
            return set().union(*(self.fragments(part["value"], (*active, reference))
                                 for part in value["bytes"] if part["tag"] == "fragment"))
        return set()

    def aliases(self, reference):
        result = set()
        for fragment in self.fragments(reference):
            value = self.values[fragment]
            if value["tag"] == "pointer":
                anchor, address = self.key(value["region"], value["offset"])
            elif value["tag"] == "constant":
                anchor, address = "concrete", value["value"]
            else:
                continue
            result.update(region["id"] for region in self.regions.values() if region["kind"] == "stack-allocation" and
                          self.base(region["id"])[0] == anchor and self.base(region["id"])[1] <= address <=
                          self.base(region["id"])[1] + region["size"])
        return result

    def borrowed(self, reference, displacement=0):
        value = self.values[reference]
        if value["tag"] == "pointer" and self.regions[value["region"]]["kind"] == "stack-domain":
            location = self.locate(reference, displacement, 1)
            return self.pointer(location["region"], location["offset"])
        return reference

    def check_live_aliases(self):
        retired = {region["id"] for region in self.regions.values() if region["lifetime"] == "retired"}
        for name, reference in self.registers.items():
            require(name == "sp" or not self.aliases(reference) & retired,
                    "retired caller alias requires S3 restoration proof", "local-effect")
        for key, part in self.memory.items():
            if part["tag"] == "fragment" and self.aliases(part["value"]) & retired:
                require(not any(region["lifetime"] == "live" and region["kind"] != "stack-domain" and
                                self.base(region["id"])[0] == key[0] and self.base(region["id"])[1] <= key[1] < self.base(region["id"])[1] + region["size"]
                                for region in self.regions.values()), "live caller storage retains retired fragment", "local-effect")

    def bitvector(self, reference, active=()):
        require(reference not in active and len(active) < MAX_CALLER_DEPTH, "caller bit provenance depth exhausted", "unsupported")
        if reference not in self.bits:
            value = self.values[reference]
            if value["tag"] == "constant":
                bits = tuple((value["value"] >> index) & 1 for index in range(private.width(value) * 8))
            elif value["tag"] == "bytes":
                bits = []
                for part in value["bytes"]:
                    if part["tag"] == "constant":
                        bits.extend((part["value"] >> index) & 1 for index in range(8))
                    elif part["tag"] == "fragment":
                        bits.extend(self.bitvector(part["value"], (*active, reference))[part["index"] * 8:part["index"] * 8 + 8])
                    else:
                        bits.extend(("byte", canonical(part["origin"]), index) for index in range(8))
                bits = tuple(bits)
            else:
                bits = tuple(("value", reference, index) for index in range(private.width(value) * 8))
            self.bits[reference] = bits
        return self.bits[reference]

    def root(self, reference):
        bits = self.bitvector(reference)
        for name, root in self.context["registers"].items():
            raw = self.bitvector(root)
            if bits == raw:
                return ("u32", root, name)
            if bits == raw[:8] + (0,) * 24:
                return ("low8", root, name)
        return None

    def number(self, reference):
        value = self.values[reference]
        if value["tag"] == "pointer":
            anchor, start = self.base(value["region"])
            return start + value["offset"] if anchor == "concrete" else None
        if value["tag"] == "control":
            return value["target"]
        if value["tag"] == "function":
            return self.function_targets.get(value["body"])
        bits = self.bitvector(reference)
        concrete = []
        for bit in bits:
            if type(bit) is int:
                concrete.append(bit)
            elif bit[0] == "value":
                domain = self.domains.get(("u32", bit[1])) or (self.domains.get(("low8", bit[1])) if bit[2] < 8 else None)
                if domain is None or len(domain) != 1 or domain[0][0] != domain[0][1]:
                    return None
                concrete.append((domain[0][0] >> bit[2]) & 1)
            else:
                return None
        return sum(bit << index for index, bit in enumerate(concrete))

    def transformed(self, bits, sources):
        """Keep origin bytes as an overapproximation; exact bits stay mandatory.

        No known pointer/control/function fragments may enter this operation.
        A partial scalar byte keeps its prior origin, never a fabricated zero.
        """
        require(all(not self.fragments(source) for source in sources), "arithmetic would erase pointer fragments", "local-effect")
        parts = []
        for index in range(4):
            byte = bits[index * 8:index * 8 + 8]
            if all(type(bit) is int for bit in byte):
                parts.append({"tag": "constant", "value": sum(bit << offset for offset, bit in enumerate(byte))})
                continue
            atoms = [bit for bit in byte if type(bit) is not int]
            origins = set((bit[0], bit[1]) for bit in atoms)
            require(len(origins) == 1, "mixed scalar byte origins unsupported", "unsupported")
            tag, origin = next(iter(origins))
            if tag == "value":
                original = self.values[origin]
                require(original["tag"] == "symbolic", "unsupported scalar bit origin", "unsupported")
                parts.append({"tag": "unknown", "origin": original["origin"]})
            else:
                parts.append({"tag": "unknown", "origin": private.decode(origin)})
        result = self.make("bytes", width=4, bytes=parts)
        self.bits[result] = tuple(bits)
        return result

    def assemble(self, parts, bits, extend=False):
        size = len(parts)
        if all(part["tag"] == "fragment" and part["value"] == parts[0]["value"] and part["index"] == index
               for index, part in enumerate(parts)):
            ref = parts[0]["value"]
            if private.width(self.values[ref]) == size and (not extend or size == 4):
                require(self.bitvector(ref) == tuple(bits), "saved fragment bit identity differs", "local-effect")
                return ref
        if extend:
            parts = parts + [{"tag": "constant", "value": 0}] * (4 - size)
            bits = tuple(bits) + (0,) * ((4 - size) * 8)
        ref = self.make("bytes", width=4 if extend else size, bytes=parts)
        self.bits[ref] = tuple(bits)
        return ref

    def loaded(self, location, parts, bits):
        return self.assemble(parts, bits, extend=location["size"] != 4)

    def literal_value(self, address):
        if address not in self.literal_values:
            binding = self.literal_bindings[address]
            if binding["tag"] == "function":
                require(binding["role"] == "callback", "unsupported typed function literal", "unsupported")
                reference = self.make("function", body="callback")
            else:
                storage = self.locate(self.constant(binding["target"]), 0, 1)
                reference = self.pointer(storage["region"], storage["offset"])
            self.literal_values[address] = reference
        return self.literal_values[address]

    def locate(self, reference, displacement, size):
        value = self.values[reference]
        stack_domain = False
        if value["tag"] == "pointer":
            region = self.regions[value["region"]]
            require(region["lifetime"] == "live", "caller uses retired pointer", "local-effect")
            offset = value["offset"] + displacement
            require(0 <= offset and offset + size <= region["size"],
                    "caller access lacks declared live storage within originating region", "local-effect")
            anchor, start = self.key(value["region"], value["offset"])
            require((start + displacement) % size == 0, "unaligned caller memory access", "local-effect")
            # Physical aliases never expand a typed pointer's authority. Only
            # the stack backing domain needs resolution to an actual allocation.
            if region["kind"] != "stack-domain":
                return private.slc(region["id"], offset, size)
            stack_domain = True
        else:
            require(not self.fragments(reference), "fragment used as memory address", "local-effect")
            anchor, start = "concrete", self.number(reference)
            require(start is not None, "unclassified caller memory address", "unsupported")
        start += displacement
        require(start % size == 0, "unaligned caller memory access", "local-effect")
        matches = []
        for region in self.regions.values():
            key, base = self.base(region["id"])
            owned = region["kind"] == "stack-allocation" if stack_domain else region["kind"] != "stack-domain"
            if owned and region["lifetime"] == "live" and key == anchor and base <= start and start + size <= base + region["size"]:
                matches.append(region)
        require(matches, "caller access lacks declared live storage", "local-effect")
        require(not stack_domain or len(matches) == 1, "caller stack access lacks unique live allocation", "local-effect")
        region = min(matches, key=lambda item: (item["size"], item["kind"] != "stack-allocation", item["kind"] != "external", item["id"]))
        return private.slc(region["id"], start - self.base(region["id"])[1], size)

    def read(self, location):
        parts, bits = [], []
        region = self.regions[location["region"]]
        require(region["lifetime"] == "live" and region["permission"] in ("r", "rw", "rx"), "caller read permission/lifetime", "local-effect")
        for index in range(location["size"]):
            key = self.key(location["region"], location["offset"] + index)
            if region["kind"] == "rom" and key[0] == "concrete" and (key[1] & ~3) in self.literal_bindings:
                word = key[1] & ~3
                self.memory[key] = {"tag": "fragment", "value": self.literal_value(word), "index": key[1] - word}
            elif key not in self.memory:
                if region["kind"] == "rom":
                    require(key[0] == "concrete" and ROM_BASE <= key[1] < ROM_BASE + len(self.rom), "caller ROM read outside bound image")
                    self.memory[key] = {"tag": "constant", "value": self.rom[key[1] - ROM_BASE]}
                else:
                    self.memory[key] = {"tag": "unknown", "origin": {"tag": "memory", "region": location["region"], "offset": location["offset"] + index}}
            part = self.memory[key]
            parts.append(part)
            bits.extend(self.memory_bits.get(key, self.part_bits(part)))
        self.reads.append({"location": location, "bytes": parts})
        return parts, tuple(bits)

    def part_bits(self, part):
        if part["tag"] == "constant":
            return tuple((part["value"] >> index) & 1 for index in range(8))
        if part["tag"] == "fragment":
            return self.bitvector(part["value"])[part["index"] * 8:part["index"] * 8 + 8]
        return tuple(("byte", canonical(part["origin"]), index) for index in range(8))

    def write(self, location, reference, *, save=False):
        require(self.regions[location["region"]]["permission"] == "rw", "caller write permission", "local-effect")
        parts = private.value_bytes(self.values[reference])[:location["size"]]
        bits = self.bitvector(reference)
        require(len(parts) == location["size"], "caller store width differs")
        for index, part in enumerate(parts):
            key = self.key(location["region"], location["offset"] + index)
            require(save or not any(item["consumed"] is None and self.overlap(location, item["record"]["location"])
                                    for item in self.saves.values()), "caller write corrupts save witness", "local-effect")
            self.memory[key] = copy.deepcopy(part)
            self.memory_bits[key] = bits[index * 8:index * 8 + 8]
        self.writes.append({"location": location, "bytes": parts})

    def stack_address(self):
        value = self.values[self.registers["sp"]]
        require(value["tag"] == "pointer", "caller SP lost identity", "local-effect")
        anchor, address = self.key(value["region"], value["offset"])
        require(anchor == self.stack_anchor and address % 4 == 0, "caller SP backing/alignment changed", "local-effect")
        return address

    def allocate(self, size):
        previous = self.stack_address()
        address = previous - size
        domain = self.regions[self.stack_region]
        require(size > 0 and size % 4 == 0 and self.stack_base <= address < previous <= self.stack_base + domain["size"],
                "caller stack allocation exceeds backing", "local-effect")
        identifier = self.new_id("r")
        region = {"id": identifier, "base": {"tag": "relative", "region": self.stack_region, "offset": address - self.stack_base},
                  "size": size, "permission": "rw", "kind": "stack-allocation", "lifetime": "live", "frame": self.context["frame"]}
        self.regions[identifier] = region
        location = private.slc(identifier, 0, size)
        require(not any(other["id"] != identifier and other["kind"] == "stack-allocation" and other["lifetime"] == "live" and
                        self.overlap(location, private.slc(other["id"], 0, other["size"])) for other in self.regions.values()),
                "caller stack/save allocation overlap", "local-effect")
        self.frames[self.context["frame"]]["allocations"].append(identifier)
        self.registers["sp"] = self.pointer(self.stack_region, address - self.stack_base)
        self.event("allocate-stack", region=identifier)
        return identifier

    def retire(self, size):
        start = self.stack_address()
        end = start + size
        regions = [region for region in self.regions.values() if region["kind"] == "stack-allocation" and
                   region["lifetime"] == "live" and region["frame"] == self.context["frame"] and
                   start <= self.base(region["id"])[1] < end]
        require(size > 0 and size % 4 == 0 and sum(region["size"] for region in regions) == size and
                all(self.base(region["id"])[1] + region["size"] <= end for region in regions), "partial or unbalanced caller retirement", "local-effect")
        for region in regions:
            require(not any(save["consumed"] is None and save["record"]["location"]["region"] == region["id"] for save in self.saves.values()),
                    "caller retirement leaves live save", "local-effect")
            region["lifetime"] = "retired"
            self.event("retire-stack", region=region["id"])
        self.registers["sp"] = self.pointer(self.stack_region, end - self.stack_base)
        # S3 restoration corridors are unavailable: refuse, never tolerate an alias.
        self.check_live_aliases()

    def domain(self, root):
        return self.domains.get(root[:2], ((0, 255 if root[0] == "low8" else 0xffffffff),))

    def refine(self, root, predicate, number, taken):
        require(not any(reference == root[1] and kind != root[0] for kind, reference in self.domains),
                "mixed full-word/low-byte refinements unsupported", "unsupported")
        maximum = 255 if root[0] == "low8" else 0xffffffff
        ranges = {"beq": [(number, number)], "bne": [(0, number - 1), (number + 1, maximum)],
                  "bhi": [(number + 1, maximum)], "bls": [(0, number)],
                  "bhs": [(number, maximum)], "blo": [(0, number - 1)]}[predicate]
        if not taken:
            complement, cursor = [], 0
            for low, high in ranges:
                low, high = max(0, low), min(maximum, high)
                if low <= high:
                    if cursor < low:
                        complement.append((cursor, low - 1))
                    cursor = high + 1
            if cursor <= maximum:
                complement.append((cursor, maximum))
            ranges = complement
        result = tuple((max(low, lower), min(high, upper)) for low, high in self.domain(root)
                       for lower, upper in ranges if max(low, lower) <= min(high, upper))
        if result:
            self.domains[root[:2]] = result
        return bool(result)

    def decision(self, kind, choice, target):
        self.decisions.append({"location": {"body": self.body["id"], "pc": self.pc}, "kind": kind,
                               "choice": choice, "target": {"body": self.body["id"], "pc": target}})

    def output(self, status, target=None):
        digest = hashlib.sha256(b"conditional-registration-path-v1\0" + canonical(self.decisions).encode()).hexdigest()
        # Only generated reserved IDs change; entry IDs/anchors cannot use pub/.
        replacements = {identifier: identifier.replace(_ZERO_DIGEST, digest) for registry in
                        (self.values, self.regions, self.saves, self.frames) for identifier in registry if identifier.startswith("pub/")}
        replacements.update(self.export_identities(digest))

        def rename(value):
            if type(value) is dict:
                return {key: rename(child) for key, child in value.items()}
            if type(value) in (list, tuple):
                return [rename(child) for child in value]
            return replacements.get(value, value) if type(value) is str else value

        cells = []
        for key, part in self.memory.items():
            matches = [region for region in self.regions.values() if region["kind"] != "stack-domain" and region["lifetime"] == "live" and
                       self.base(region["id"])[0] == key[0] and self.base(region["id"])[1] <= key[1] < self.base(region["id"])[1] + region["size"]]
            if matches:
                region = min(matches, key=lambda item: (item["size"], item["kind"] != "stack-allocation", item["kind"] != "external", item["id"]))
                cells.append({"location": private.slc(region["id"], key[1] - self.base(region["id"])[1], 1), "bytes": [part]})
        cells.sort(key=lambda item: (item["location"]["region"], item["location"]["offset"]))
        output = rename({"path": "path/" + digest, "decisions": self.decisions, "status": status,
                       "site": {"body": self.body["id"], "pc": self.pc}, "target": target,
                       "registers": {name: self.registers[name] for name in private.REGISTERS}, "sp": self.registers["sp"], "lr": self.registers["lr"],
                       "values": sorted(self.values.values(), key=lambda item: item["id"]),
                       "regions": sorted(self.regions.values(), key=lambda item: item["id"]),
                       "frames": sorted(self.frames.values(), key=lambda item: item["id"]),
                       "saves": sorted(self.saves.values(), key=lambda item: item["record"]["witness"]),
                       "touched": sorted(self.touched), "restore_witnesses": self.restored_by,
                       "function_targets": self.function_targets,
                       "register_change_steps": self.restore_steps,
                       "cells": cells, "cell_bits": [{"location": cell["location"], "bits": self.memory_bits.get(
                           self.key(cell["location"]["region"], cell["location"]["offset"]), self.part_bits(cell["bytes"][0]))} for cell in cells],
                       "events": self.events, "edges": self.edges,
                       "bits": [{"value": ref, "bits": self.bitvector(ref)} for ref in sorted(self.values)],
                       "domains": [{"kind": kind, "value": ref, "ranges": ranges} for (kind, ref), ranges in sorted(self.domains.items())],
                       **self.export_members()})
        # Encoded origins occur only in typed bit facts, never ordinary ID lists.
        snapshots = [output]
        for call in output.get("helper_calls", []):
            snapshots.append(call["input"])
            if call["output"] is not None:
                snapshots.append(call["output"])
        for snapshot in snapshots:
            for sidecar in ("bits", "cell_bits"):
                for fact in snapshot[sidecar]:
                    for bit in fact["bits"]:
                        if type(bit) is list and bit[0] == "byte":
                            bit[1] = canonical(rename(private.decode(bit[1])))
        return output

    def export_identities(self, digest):
        return {}

    def export_members(self):
        return {}


def _caller_transfer(state, insn, capture):
    """One actual instruction. Branches and unqualified calls are handled outside."""
    from capstone.arm import ARM_OP_REG, ARM_OP_IMM, ARM_OP_MEM
    operands, mnemonic = insn.operands, insn.mnemonic
    names = [private.Checker.regname(insn, operand.reg) if operand.type == ARM_OP_REG else None for operand in operands]
    before = dict(state.registers)
    before_witnesses = dict(state.restored_by)
    state.reads, state.writes = [], []
    following = insn.address + insn.size

    def source(operand):
        if operand.type == ARM_OP_REG:
            name = private.Checker.regname(insn, operand.reg)
            require(name in state.registers, "unsupported caller source register", "unsupported")
            return state.registers[name]
        require(operand.type == ARM_OP_IMM, "unsupported caller operand", "unsupported")
        return state.constant(operand.imm)

    def assign(name, reference):
        require(name in state.registers, "unsupported caller destination register", "unsupported")
        state.registers[name] = reference
        state.restored_by.pop(name, None)

    if mnemonic in ("mov", "movs"):
        require(len(operands) == 2 and names[0] is not None, "malformed caller MOV")
        if names[0] == "pc":
            following = state.number(source(operands[1]))
            require(following is not None, "unresolved caller dispatch", "unsupported")
        else:
            reference = source(operands[1])
            assign(names[0], state.borrowed(reference) if names[0] != "sp" else reference)
            if names[1] in before_witnesses:
                state.restored_by[names[0]] = before_witnesses[names[1]]
    elif mnemonic in ("adds", "add", "subs", "sub"):
        require(len(operands) in (2, 3) and names[0] is not None, "malformed caller ADD/SUB")
        first = state.registers[names[0]] if len(operands) == 2 else source(operands[1])
        second = source(operands[-1])
        amount = state.number(second)
        require(amount is not None, "caller arithmetic has unknown displacement", "unsupported")
        if mnemonic.startswith("sub"):
            amount = -amount
        if state.values[second]["tag"] == "pointer":
            require(mnemonic.startswith("add") and names[0] != "sp" and not state.fragments(first),
                    "unsupported pointer arithmetic operands", "local-effect")
            displacement = state.number(first)
            require(displacement is not None, "unknown pointer index", "unsupported")
            pointer = state.values[second]
            assign(names[0], state.pointer(pointer["region"], pointer["offset"] + displacement))
        elif state.fragments(second):
            raise Failure("local-effect", "caller arithmetic would erase pointer fragments")
        elif names[0] == "sp":
            require(first == state.registers["sp"] and amount % 4 == 0 and amount != 0, "unsupported caller SP adjustment", "unsupported")
            if amount < 0:
                state.allocate(-amount)
            else:
                state.retire(amount)
        elif amount == 0:
            assign(names[0], state.borrowed(first))
            original_name = names[0] if len(operands) == 2 else names[1]
            if original_name in before_witnesses:
                state.restored_by[names[0]] = before_witnesses[original_name]
        elif state.values[first]["tag"] == "pointer":
            value = state.values[first]
            offset = value["offset"] + amount
            if state.regions[value["region"]]["kind"] == "stack-domain":
                location = state.locate(first, amount, 1)
                assign(names[0], state.pointer(location["region"], location["offset"]))
            else:
                assign(names[0], state.pointer(value["region"], offset))
        else:
            require(not state.fragments(first), "caller arithmetic would erase pointer fragments", "local-effect")
            number = state.number(first)
            require(number is not None, "unsupported unknown scalar addition", "unsupported")
            assign(names[0], state.constant(number + amount))
    elif mnemonic in ("ands", "orrs", "lsls", "lsrs", "asrs"):
        require(names[0] is not None and len(operands) in (2, 3), "malformed caller bit operation")
        first = state.registers[names[0]] if len(operands) == 2 else source(operands[1])
        second = source(operands[-1])
        require(not state.fragments(first) and not state.fragments(second), "arithmetic would erase pointer fragments", "local-effect")
        left = state.bitvector(first)
        if mnemonic in ("ands", "orrs"):
            right = state.bitvector(second)
            bits = []
            for a, b in zip(left, right):
                if mnemonic == "ands":
                    bit = 0 if a == 0 or b == 0 else b if a == 1 else a if b == 1 or a == b else None
                else:
                    bit = 1 if a == 1 or b == 1 else b if a == 0 else a if b == 0 or a == b else None
                require(bit is not None, "mixed unknown bit operation unsupported", "unsupported")
                bits.append(bit)
        else:
            shift = state.number(second)
            require(shift is not None and 0 <= shift <= 32, "unsupported caller shift", "unsupported")
            if mnemonic == "lsls":
                bits = ((0,) * shift + left)[:32]
            else:
                fill = left[-1] if mnemonic == "asrs" else 0
                bits = left[shift:] + (fill,) * shift
        assign(names[0], state.transformed(tuple(bits), (first, second)))
    elif mnemonic == "cmp":
        require(len(operands) == 2, "malformed caller CMP")
        left, right = source(operands[0]), source(operands[1])
        require(not state.fragments(left) and not state.fragments(right), "comparison of pointer fragments unsupported", "unsupported")
        state.flags = (left, right)
        root, number = state.root(left), state.number(right)
        if root is not None and number is not None:
            state.comparisons.append((state.pc, root, number))
    elif mnemonic in ("ldr", "ldrb", "ldrh", "str", "strb", "strh"):
        require(len(operands) == 2 and names[0] is not None and operands[1].type == ARM_OP_MEM,
                "malformed caller memory instruction")
        operand = operands[1].mem
        require(not operand.index, "indexed caller memory access unsupported", "unsupported")
        base = private.Checker.regname(insn, operand.base)
        size = 1 if mnemonic.endswith("b") else 2 if mnemonic.endswith("h") else 4
        if base == "pc":
            require(mnemonic == "ldr", "nonword caller literal access")
            address = ((insn.address + 4) & ~3) + operand.disp
            require(any(span["start"] <= address and address + 4 <= span["end"] for span in state.body["literals"]),
                    "caller literal is not owned")
            location = state.locate(state.constant(address), 0, 4)
            parts, bits = state.read(location)
            assign(names[0], state.loaded(location, parts, bits))
        else:
            require(base in state.registers, "unsupported caller memory base", "unsupported")
            location = state.locate(state.registers[base], operand.disp, size)
            if mnemonic.startswith("ldr"):
                parts, bits = state.read(location)
                assign(names[0], state.loaded(location, parts, bits))
            else:
                # No helper/registration retention assumptions are available.
                require(state.regions[location["region"]]["kind"] == "stack-allocation" or
                        not state.fragments(state.registers[names[0]]), "external caller retention of pointer fragment", "local-effect")
                state.write(location, state.registers[names[0]])
    elif mnemonic == "push":
        require(names and all(name in (*private.REGISTERS[:8], "lr") for name in names), "malformed caller PUSH")
        require(names == sorted(set(names), key=lambda name: 14 if name == "lr" else int(name[1:])), "unordered caller PUSH")
        # Separate words permit exact subsequent partial POP retirement.
        allocated = [state.allocate(4) for _ in names]
        start = state.stack_address()
        for index, name in enumerate(names):
            region = allocated[-1 - index]
            require(state.base(region)[1] == start + index * 4, "caller PUSH allocation order differs")
            reference = before[name]
            state.write(private.slc(region, 0, 4), reference, save=True)
            originals = [register for register in (*private.NONVOLATILE[:-1], "lr")
                         if state.equivalent(reference, state.context["lr"] if register == "lr" else state.context["registers"][register])]
            require(len(originals) == 1, "caller PUSH lacks unique original save value", "unsupported")
            witness = state.new_id("s")
            save = {"witness": witness, "register": originals[0], "location": private.slc(region, 0, 4), "value": reference}
            state.saves[witness] = {"record": save, "created": len(state.events), "consumed": None}
            state.frames[state.context["frame"]]["saves"].append(save)
            state.event("save-create", witness=witness)
    elif mnemonic == "pop":
        require(names and all(name in private.REGISTERS[:8] for name in names), "unsupported caller POP destination", "unsupported")
        require(names == sorted(set(names), key=lambda name: int(name[1:])), "unordered caller POP")
        for index, name in enumerate(names):
            location = state.locate(before["sp"], index * 4, 4)
            matches = [(witness, save) for witness, save in state.saves.items() if save["consumed"] is None and
                       state.interval(save["record"]["location"]) == state.interval(location) and
                       save["record"]["location"]["region"] == location["region"]]
            require(len(matches) == 1, "caller POP lacks exact live save witness", "local-effect")
            witness, save = matches[0]
            parts, bits = state.read(location)
            reference = state.assemble(parts, bits)
            require(state.equivalent(reference, save["record"]["value"]) and
                    parts == private.value_bytes(state.values[save["record"]["value"]]), "caller POP save bytes disagree", "local-effect")
            assign(name, reference)
            save["consumed"] = len(state.events)
            state.event("save-consume", witness=witness, register=name)
            state.restored_by[name] = witness
        state.retire(len(names) * 4)
    elif mnemonic == "b":
        following = operands[0].imm
    elif mnemonic == "bx":
        require(len(names) == 1 and names[0] in state.registers, "malformed caller BX")
        target = state.registers[names[0]]
        require(target == state.context["lr"], "caller return control identity differs", "local-effect")
        for name in private.NONVOLATILE:
            original = state.context["sp"] if name == "sp" else state.context["registers"][name]
            require(state.equivalent(state.registers[name], original), "caller return nonvolatile identity differs: " + name, "local-effect")
            if name != "sp" and name in state.touched:
                witness = state.restored_by.get(name)
                require(witness in state.saves and state.saves[witness]["record"]["register"] == name and
                        state.equivalent(state.saves[witness]["record"]["value"], original) and state.saves[witness]["consumed"] is not None,
                        "touched caller register lacks actual save restoration: " + name, "local-effect")
        require(not any(region["kind"] == "stack-allocation" and region["frame"] == state.context["frame"] and
                        region["lifetime"] == "live" for region in state.regions.values()), "caller return retains local storage", "local-effect")
        address = state.number(target)
        require(address is not None and address & 1, "caller return address is undeclared", "unsupported")
        following = address & ~1
    else:
        require(mnemonic == "nop", "unsupported caller transfer", "unsupported")
    # CMP flags are valid only across instructions that do not alter them.
    if mnemonic in ("adds", "subs", "movs", "ands", "orrs", "lsls", "lsrs", "asrs"):
        state.flags = None
    state.check_live_aliases()
    changes = []
    for name in (*private.REGISTERS, "sp", "lr"):
        if before[name] != state.registers[name]:
            changes.append({"register": name, "before": before[name], "after": state.registers[name]})
            if name in private.NONVOLATILE:
                state.touched.add(name)
                state.restore_steps[name].append(len(state.events))
    state.event("instruction", encoding=bytes(insn.bytes).hex(), registers=changes,
                reads=state.reads, writes=state.writes, next_pc=following)
    return following


def _helper_program(fixed, target):
    """Close one mapped Thumb body over its actual ROM bytes, without summaries."""
    from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
    from capstone.arm import ARM_OP_IMM, ARM_OP_MEM, ARM_OP_REG
    named, _ = _maps(fixed)
    matches = [(name, extent) for name, extent in named.items() if extent[0] == target]
    require(len(matches) == 1 and matches[0][1][2] == "thumb", "helper target lacks unique mapped Thumb body", "unsupported")
    _, (start, end, _) = matches[0]
    require(ROM_BASE <= start < end <= ROM_BASE + len(fixed.rom.data), "helper extent outside bound ROM")
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    decoder.detail = True
    program, occupied, literals, pending = {}, set(), set(), [start]
    branches = {"beq", "bne", "bhi", "bls", "bhs", "blo", "bgt", "ble", "bge", "blt"}
    allowed = {"push", "pop", "mov", "movs", "add", "adds", "sub", "subs", "lsls", "lsrs", "asrs", "muls",
               "ands", "orrs", "cmp", "ldr", "ldrb", "ldrh", "ldrsb", "ldrsh", "str", "strb", "strh", "b", "bl", "bx", "nop"} | branches
    while pending:
        pc = pending.pop()
        if pc in program:
            continue
        require(start <= pc < end and pc % 2 == 0 and pc not in occupied and pc not in literals,
                "helper edge targets non-instruction bytes")
        instruction = next(decoder.disasm(fixed.rom.data[pc - ROM_BASE:min(pc + 4, end) - ROM_BASE], pc, count=1), None)
        require(instruction is not None and instruction.size in (2, 4) and pc + instruction.size <= end,
                "helper instruction is truncated")
        insn_bytes = set(range(pc, pc + instruction.size))
        require(not insn_bytes & (occupied | literals), "helper instruction/literal ownership overlap")
        require(instruction.mnemonic in allowed, "unsupported helper instruction: " + instruction.mnemonic, "unsupported")
        program[pc] = instruction
        occupied.update(insn_bytes)
        operands, mnemonic = instruction.operands, instruction.mnemonic
        names = [private.Checker.regname(instruction, operand.reg) if operand.type == ARM_OP_REG else None for operand in operands]
        for operand in operands:
            if operand.type == ARM_OP_MEM and private.Checker.regname(instruction, operand.mem.base) == "pc":
                require(mnemonic == "ldr" and not operand.mem.index, "unsupported helper PC memory operand", "unsupported")
                word = ((pc + 4) & ~3) + operand.mem.disp
                span = set(range(word, word + 4))
                require(start <= word and word + 4 <= end and not span & occupied, "helper literal ownership differs")
                literals.update(span)
        following = pc + instruction.size
        if mnemonic == "bx":
            require(len(names) == 1 and names[0] not in (None, "pc", "sp"), "unsupported helper return", "unsupported")
            targets = []
        elif mnemonic == "b" or mnemonic in branches:
            require(len(operands) == 1 and operands[0].type == ARM_OP_IMM, "malformed helper branch")
            targets = [operands[0].imm] + ([] if mnemonic == "b" else [following])
        elif mnemonic == "bl":
            require(len(operands) == 1 and operands[0].type == ARM_OP_IMM, "unsupported indirect helper call", "unsupported")
            targets = [following]
        else:
            require(not names or names[0] != "pc", "unsupported computed helper transfer", "unsupported")
            targets = [following]
        pending.extend(targets)
        require(len(program) <= MAX_CALLER_TRANSFERS, "helper decoding budget exhausted", "unsupported")

    def spans(addresses):
        result = []
        for address in sorted(addresses):
            if result and result[-1]["end"] == address:
                result[-1]["end"] += 1
            else:
                result.append({"start": address, "end": address + 1})
        return result

    alignment = spans(set(range(start, end)) - occupied - literals)
    require(all(item["end"] - item["start"] == 2 and item["start"] % 2 == 0 and
                fixed.rom.data[item["start"] - ROM_BASE:item["end"] - ROM_BASE] == b"\0\0" for item in alignment),
            "helper has unclassified mapped bytes", "unsupported")
    body = {"id": f"body/{start:08X}", "role": "helper", "start": start, "end": end,
            "sha256": hashlib.sha256(fixed.rom.data[start - ROM_BASE:end - ROM_BASE]).hexdigest(),
            "code": spans(occupied), "literals": spans(literals), "alignment": alignment, "runtime_start": None}
    return body, program


class _HelperState(_CallerState):
    """Decoded helper scopes; all inherited provenance and liveness rules apply."""

    def __init__(self, context, body, rom):
        super().__init__(context, body, rom)
        self.caller_context = self.context
        self.scopes, self.helper_calls = [], []
        self.identities = {register: register for register in (*private.REGISTERS, "sp", "lr")}
        self.frame_evidence = [{"frame": frame, "call": None, "entered": None, "returned": None, "mode": "entry"}
                               for frame in sorted(self.frames)]
        self.bound_bodies = {body["id"]: body}
        self.invocations = set()

    def root(self, reference):
        current = self.context
        self.context = self.caller_context
        try:
            return super().root(reference)
        finally:
            self.context = current

    def constant(self, number):
        # Actual Thumb scalar arithmetic wraps at 32 bits. Pointer arithmetic
        # still uses the inherited typed extent checks and never wraps.
        return super().constant(number & 0xffffffff if self.scopes else number)

    def snapshot(self):
        # Reuse the accepted complete live-byte canonicalization and bit export.
        # The private snapshot intentionally has sidecars and is not P5 State.
        extra = self.helper_calls
        self.helper_calls = []
        try:
            result = super().output("internal-helper-boundary")
        finally:
            self.helper_calls = extra
        digest = result["path"].split("/")[1]

        def restore(value):
            if type(value) is dict:
                return {key: restore(child) for key, child in value.items()}
            if type(value) is list:
                return [restore(child) for child in value]
            return value.replace(digest, _ZERO_DIGEST) if type(value) is str and value.startswith("pub/") else value

        state = restore({key: result[key] for key in ("registers", "sp", "lr", "cells", "bits", "cell_bits")})
        # Origin atoms contain encoded IDs; undo only those typed atoms.
        for sidecar in ("bits", "cell_bits"):
            for fact in state[sidecar]:
                for bit in fact["bits"]:
                    if type(bit) is list and bit[0] == "byte":
                        bit[1] = canonical(restore(private.decode(bit[1])))
        for lifetime in ("live", "retired"):
            state[lifetime] = sorted(region["id"] for region in self.regions.values()
                                     if region["kind"] in ("stack-allocation", "external") and region["lifetime"] == lifetime)
        state["pending"] = []  # No S3 retirement has executed or opened a corridor.
        return state

    def export_identities(self, digest):
        return {identifier: identifier.replace(_ZERO_DIGEST, digest) for identifier in self.invocations}

    def export_members(self):
        return {"helper_calls": self.helper_calls, "frame_evidence": self.frame_evidence,
                "bodies": sorted(self.bound_bodies.values(), key=lambda body: body["id"]),
                "active_calls": [scope["call"] for scope in self.scopes]}

    def enter(self, body, insn):
        require(len(self.caller_context["frames"]) + len(self.scopes) < MAX_CALLER_DEPTH,
                "helper frame depth exhausted", "unsupported")
        occurrence = len(self.helper_calls)
        input_state = self.snapshot()
        frame, invocation = self.new_id("f"), self.new_id("i")
        self.invocations.add(invocation)
        call = {"occurrence": occurrence, "site": {"body": self.body["id"], "pc": self.pc}, "target": body["id"],
                "kind": "bounded-region", "frame": frame, "input": input_state, "output": None,
                "events": {"begin": len(self.events), "end": None}, "dependencies": []}
        self.helper_calls.append(call)
        scope = {"context": self.context, "body": self.body, "pc": insn.address + insn.size, "call": occurrence,
                 "flags": self.flags, "identities": self.identities, "touched": self.touched,
                 "restored_by": self.restored_by, "restore_steps": self.restore_steps,
                 "literal_bindings": self.literal_bindings, "literal_values": self.literal_values}
        self.scopes.append(scope)
        control = self.make("control", invocation=invocation, target=(insn.address + insn.size) | 1)
        before = self.registers["lr"]
        self.registers["lr"] = control
        self.event("instruction", encoding=bytes(insn.bytes).hex(),
                   registers=[{"register": "lr", "before": before, "after": control}], reads=[], writes=[], next_pc=body["start"])
        self.event("call-enter", occurrence=occurrence, target=body["id"], kind="bounded-region")
        self.frames[frame] = {"id": frame, "invocation": invocation, "parent": self.context["frame"],
                              "entry_sp": self.registers["sp"], "allocations": [], "saves": []}
        self.context = {"invocation": invocation, "frame": frame,
                        "registers": {name: self.registers[name] for name in private.REGISTERS},
                        "sp": self.registers["sp"], "lr": control}
        self.body, self.pc = body, body["start"]
        self.literal_bindings, self.literal_values = {}, {}
        self.identities = {register: register for register in (*private.REGISTERS, "sp", "lr")}
        self.touched, self.restored_by = set(), {}
        self.restore_steps = {register: [] for register in private.NONVOLATILE}
        self.bound_bodies[body["id"]] = body
        identifier = self.new_id("r")
        self.regions[identifier] = {"id": identifier, "base": {"tag": "concrete", "address": body["start"]},
                                    "size": body["end"] - body["start"], "permission": "r", "kind": "rom",
                                    "lifetime": "live", "frame": None}
        entered = len(self.events)
        self.event("frame-enter", frame=frame)
        self.frame_evidence.append({"frame": frame, "call": occurrence, "entered": entered, "returned": None, "mode": "decoded"})

    def leave(self):
        frame = self.context["frame"]
        next(item for item in self.frame_evidence if item["frame"] == frame)["returned"] = len(self.events) - 1
        scope = self.scopes.pop()
        call = self.helper_calls[scope["call"]]
        call["output"] = self.snapshot()
        calls = self.helper_calls[scope["call"]:]
        dependencies = {item["target"] for item in calls}
        call["dependencies"] = [{"body": body, "sha256": self.bound_bodies[body]["sha256"]} for body in sorted(dependencies)]
        self.context, self.body, self.pc = scope["context"], scope["body"], scope["pc"]
        self.identities, self.touched = scope["identities"], scope["touched"]
        self.restored_by, self.restore_steps = scope["restored_by"], scope["restore_steps"]
        self.literal_bindings, self.literal_values = scope["literal_bindings"], scope["literal_values"]
        # Only ABI nonvolatiles have just been proved restored. Volatiles keep
        # their actual callee results and every surviving pointer fragment.
        for register in ("r0", "r1", "r2", "r3", "r12", "lr"):
            self.identities.pop(register, None)
            self.restored_by.pop(register, None)
        # Keep the callee's actual final flags, including preserved CMP facts.
        # A decoded identity helper does not invent ABI flag clobbers.
        self.event("call-return", occurrence=call["occurrence"], target=call["target"], kind="bounded-region")
        call["events"]["end"] = len(self.events)


def _helper_transfer(state, insn, capture):
    """The inherited instruction rules plus actual helper operand forms."""
    from capstone.arm import ARM_OP_REG, ARM_OP_MEM
    names = [private.Checker.regname(insn, operand.reg) if operand.type == ARM_OP_REG else None for operand in insn.operands]
    before, identities = dict(state.registers), dict(state.identities)
    mnemonic = insn.mnemonic
    if mnemonic not in ("push", "pop", "muls", "ldrsb", "ldrsh") and not (
            len(insn.operands) == 2 and insn.operands[1].type == ARM_OP_MEM and insn.operands[1].mem.index):
        following = _caller_transfer(state, insn, capture)
        if mnemonic in ("mov", "movs") and names[1] in identities:
            state.identities[names[0]] = identities[names[1]]
        else:
            for name in (*private.REGISTERS, "sp", "lr"):
                if before[name] != state.registers[name]:
                    state.identities.pop(name, None)
        return following
    state.reads, state.writes = [], []
    if mnemonic == "push":
        require(names and names == sorted(set(names), key=lambda name: 14 if name == "lr" else int(name[1:])) and
                all(name in (*private.REGISTERS[:8], "lr") for name in names), "malformed helper PUSH")
        allocated = [state.allocate(4) for _ in names]
        for index, name in enumerate(names):
            region, reference = allocated[-1 - index], before[name]
            state.write(private.slc(region, 0, 4), reference, save=True)
            witness = state.new_id("s")
            save = {"witness": witness, "register": identities.get(name, name), "location": private.slc(region, 0, 4), "value": reference}
            state.saves[witness] = {"record": save, "created": len(state.events), "consumed": None}
            state.frames[state.context["frame"]]["saves"].append(save)
            state.event("save-create", witness=witness)
    elif mnemonic == "pop":
        require(names and all(name in private.REGISTERS[:8] for name in names) and
                names == sorted(set(names), key=lambda name: int(name[1:])), "unsupported helper POP", "unsupported")
        for index, name in enumerate(names):
            location = state.locate(before["sp"], index * 4, 4)
            matches = [(witness, save) for witness, save in state.saves.items() if save["consumed"] is None and
                       state.interval(save["record"]["location"]) == state.interval(location) and
                       save["record"]["location"]["region"] == location["region"]]
            require(len(matches) == 1, "helper POP lacks exact live save witness", "local-effect")
            witness, save = matches[0]
            parts, bits = state.read(location)
            reference = save["record"]["value"]
            require(parts == private.value_bytes(state.values[reference]) and bits == state.bitvector(reference),
                    "helper POP saved byte/bit identity differs", "local-effect")
            state.registers[name] = reference
            state.identities[name] = save["record"]["register"]
            state.restored_by[name] = witness
            save["consumed"] = len(state.events)
            state.event("save-consume", witness=witness, register=name)
        state.retire(len(names) * 4)
    elif mnemonic == "muls":
        require(len(names) == 3 and all(name in state.registers for name in names), "malformed helper MUL")
        references = [state.registers[name] for name in names[1:]]
        require(not any(state.fragments(ref) for ref in references), "helper MUL would erase pointer fragments", "local-effect")
        numbers = [state.number(ref) for ref in references]
        require(all(number is not None for number in numbers), "unknown helper multiplication cannot be represented faithfully", "unsupported")
        state.registers[names[0]] = state.constant(numbers[0] * numbers[1])
        state.restored_by.pop(names[0], None)
        state.identities.pop(names[0], None)
    else:
        require(len(insn.operands) == 2 and insn.operands[1].type == ARM_OP_MEM and names[0] in state.registers,
                "malformed helper indexed/signed access")
        operand = insn.operands[1].mem
        base = private.Checker.regname(insn, operand.base)
        require(base in state.registers, "unsupported helper indexed base", "unsupported")
        displacement = operand.disp
        if operand.index:
            index = state.registers[private.Checker.regname(insn, operand.index)]
            require(not state.fragments(index), "helper index would erase pointer fragments", "local-effect")
            number = state.number(index)
            require(number is not None, "unknown helper memory index", "unsupported")
            displacement += number
        size = 1 if mnemonic.endswith("b") else 2 if mnemonic.endswith("h") else 4
        location = state.locate(state.registers[base], displacement, size)
        if mnemonic.startswith("ldr"):
            parts, bits = state.read(location)
            reference = state.loaded(location, parts, bits)
            if mnemonic in ("ldrsb", "ldrsh"):
                require(not state.fragments(reference), "signed helper load would erase pointer fragments", "local-effect")
                extended = bits + (bits[-1],) * (32 - len(bits))
                reference = state.transformed(extended, (reference,))
            state.registers[names[0]] = reference
            state.restored_by.pop(names[0], None)
            state.identities.pop(names[0], None)
        else:
            require(state.regions[location["region"]]["kind"] == "stack-allocation" or not state.fragments(state.registers[names[0]]),
                    "external helper retention of pointer fragment", "local-effect")
            state.write(location, state.registers[names[0]])
    if insn.update_flags:
        state.flags = None
    state.check_live_aliases()
    changes = [{"register": name, "before": before[name], "after": state.registers[name]}
               for name in (*private.REGISTERS, "sp", "lr") if before[name] != state.registers[name]]
    for change in changes:
        if change["register"] in private.NONVOLATILE:
            state.touched.add(change["register"])
            state.restore_steps[change["register"]].append(len(state.events))
    following = insn.address + insn.size
    state.event("instruction", encoding=bytes(insn.bytes).hex(), registers=changes, reads=state.reads, writes=state.writes, next_pc=following)
    return following


@dataclass(frozen=True)
class HelperPrefixes:
    """Internal S2b execution with mandatory sidecars; never a full P5 history."""
    encoded: str

    def inspect(self):
        return private.decode(self.encoded)

    def p5_state(self, path):
        """Materialize only a lossless P5 State, within this incomplete result."""
        prefixes = [prefix for prefix in self.inspect()["prefixes"] if prefix["path"] == path]
        require(len(prefixes) == 1, "unknown internal helper path")
        prefix = prefixes[0]
        values = {value["id"]: value for value in prefix["values"]}

        def value_bits(reference, active=()):
            require(reference not in active and len(active) < MAX_CALLER_DEPTH, "P5 representation depth exhausted", "unsupported")
            value = values[reference]
            if value["tag"] == "constant":
                return [(value["value"] >> index) & 1 for index in range(private.width(value) * 8)]
            if value["tag"] == "bytes":
                return [bit for part in value["bytes"] for bit in part_bits(part, (*active, reference))]
            return [["value", reference, index] for index in range(private.width(value) * 8)]

        def part_bits(part, active=()):
            if part["tag"] == "constant":
                return [(part["value"] >> index) & 1 for index in range(8)]
            if part["tag"] == "fragment":
                return value_bits(part["value"], active)[part["index"] * 8:part["index"] * 8 + 8]
            return [["byte", canonical(part["origin"]), index] for index in range(8)]

        for fact in prefix["bits"]:
            require(fact["bits"] == value_bits(fact["value"]),
                    "P5 Value cannot represent mandatory bit facts: " + fact["value"], "unsupported")
        cells = {canonical(cell["location"]): cell["bytes"][0] for cell in prefix["cells"]}
        for fact in prefix["cell_bits"]:
            require(fact["bits"] == part_bits(cells[canonical(fact["location"])]),
                    "P5 Byte cannot represent mandatory bit facts: " + canonical(fact["location"]), "unsupported")
        regions = prefix["regions"]
        state = {key: prefix[key] for key in ("registers", "sp", "lr", "cells")}
        state.update({lifetime: sorted(region["id"] for region in regions if region["kind"] in ("stack-allocation", "external") and
                                      region["lifetime"] == lifetime) for lifetime in ("live", "retired")})
        state["pending"] = []
        return state


def execute_helper_prefixes(capture):
    """Qualify actual helpers, stopping before registration or S3 retirement."""
    try:
        return _execute_caller_prefixes(capture, qualify_helpers=True)
    except RecursionError as error:
        raise Failure("unsupported", "helper representation depth exhausted") from error
    except (KeyError, TypeError, ValueError, struct.error) as error:
        raise Failure("identity", "malformed bound helper capture") from error


class _RestorationState(_HelperState):
    """Internal P7 policy: immediate retirement with proved save restorations."""

    def __init__(self, context, body, rom):
        super().__init__(context, body, rom)
        self.pending, self.pending_restores = {}, {}
        self.corridor = []
        self._trial_aliases = False

    def stack_address(self):
        address = super().stack_address()
        require(self.values[self.registers["sp"]]["region"] == self.stack_region,
                "restoration SP lacks original backing identity", "local-effect")
        return address

    def retired_registers(self):
        retired = {region["id"] for region in self.regions.values() if region["lifetime"] == "retired"}
        return {name: sorted(self.aliases(reference) & retired) for name, reference in self.registers.items()
                if name != "sp" and self.aliases(reference) & retired}

    def check_live_aliases(self):
        # The trial policy changes only register treatment. Live storage never
        # receives an exception, including incidental fragments outside arguments.
        retired = {region["id"] for region in self.regions.values() if region["lifetime"] == "retired"}
        for key, part in self.memory.items():
            if part["tag"] == "fragment" and self.aliases(part["value"]) & retired:
                require(not any(region["lifetime"] == "live" and region["kind"] != "stack-domain" and
                                self.base(region["id"])[0] == key[0] and self.base(region["id"])[1] <= key[1] <
                                self.base(region["id"])[1] + region["size"] for region in self.regions.values()),
                        "live storage retains retired fragment", "local-effect")
        if not self._trial_aliases:
            covered = {obligation["register"]: obligation["retired"] for obligation in self.pending.values()}
            require(self.retired_registers() == covered, "retired alias lacks exact pending restoration", "local-effect")

    def export_identities(self, digest):
        return {**super().export_identities(digest), **{identifier: identifier.replace(_ZERO_DIGEST, digest)
                                                       for identifier in self.pending_restores}}

    def export_members(self):
        return {**super().export_members(), "pending": sorted(self.pending.values(), key=lambda item: item["id"]),
                "pending_restores": sorted(self.pending_restores.values(), key=lambda item: item["id"])}

    def snapshot(self):
        result = super().snapshot()
        result["pending"] = copy.deepcopy(sorted(self.pending.values(), key=lambda item: item["id"]))
        return result

    def guard(self, instruction):
        if self.pending:
            require(self.corridor and self.corridor[0] == {"location": {"body": self.body["id"], "pc": self.pc},
                                                       "encoding": bytes(instruction.bytes).hex()},
                    "unexpected instruction in pending restoration corridor", "local-effect")
        else:
            require(not self.corridor, "restoration corridor outlived its obligations", "local-effect")

    def enter(self, body, instruction):
        require(not self.pending, "pending restoration crosses call", "local-effect")
        return super().enter(body, instruction)

    def leave(self):
        require(not self.pending, "pending restoration crosses return", "local-effect")
        return super().leave()


def _restoration_original(state, register):
    require(register in (*private.NONVOLATILE[:-1], "lr"), "save is not an entry restoration witness", "local-effect")
    return state.context["lr"] if register == "lr" else state.context["registers"][register]


def _restoration_save(state, witness, *, live=True):
    """Bind a real current-frame creation and exact still-readable saved word."""
    require(witness in state.saves, "missing restoration save witness", "local-effect")
    saved = state.saves[witness]
    record = saved["record"]
    frame = state.frames[state.context["frame"]]
    location = record["location"]
    region = state.regions[location["region"]]
    require(record in frame["saves"] and region["frame"] == frame["id"] and location["region"] in frame["allocations"] and
            region["kind"] == "stack-allocation" and location["size"] == 4,
            "restoration witness is not owned by current frame", "local-effect")
    created = saved["created"]
    require(type(created) is int and 0 <= created < len(state.events) and
            state.events[created]["tag"] == "save-create" and state.events[created]["witness"] == witness and
            state.events[created]["location"]["body"] == state.body["id"], "restoration lacks genuine save creation", "local-effect")
    original = _restoration_original(state, record["register"])
    require(state.equivalent(record["value"], original) and state.bitvector(record["value"]) == state.bitvector(original),
            "restoration save is not the helper entry value", "local-effect")
    require(not state.aliases(record["value"]) & {region["id"] for region in state.regions.values() if region["lifetime"] == "retired"},
            "restoration value retains retired storage", "local-effect")
    if live:
        require(saved["consumed"] is None and region["lifetime"] == "live", "restoration source save is consumed or retired", "local-effect")
        parts, bits = [], []
        for index in range(4):
            key = state.key(location["region"], location["offset"] + index)
            require(key in state.memory, "restoration saved byte is absent", "local-effect")
            parts.append(state.memory[key])
            bits.extend(state.memory_bits.get(key, state.part_bits(state.memory[key])))
        require(parts == private.value_bytes(state.values[record["value"]]) and tuple(bits) == state.bitvector(record["value"]),
                "restoration saved bytes or bits differ", "local-effect")
    else:
        consumed = saved["consumed"]
        require(type(consumed) is int and 0 <= consumed < len(state.events) and
                state.events[consumed]["tag"] == "save-consume" and state.events[consumed]["witness"] == witness,
                "restoration shuttle lacks actual save consumption", "local-effect")
    return record


def _restoration_pop(state, instruction):
    from capstone.arm import ARM_OP_REG
    require(instruction.mnemonic == "pop" and instruction.operands and all(operand.type == ARM_OP_REG for operand in instruction.operands),
            "restoration requires decoded POP", "local-effect")
    names = [private.Checker.regname(instruction, operand.reg) for operand in instruction.operands]
    require(all(name in private.REGISTERS[:8] for name in names) and names == sorted(set(names), key=lambda name: int(name[1:])),
            "restoration POP has unsupported destinations", "local-effect")
    state.stack_address()
    result = {}
    for index, name in enumerate(names):
        location = state.locate(state.registers["sp"], index * 4, 4)
        matches = [witness for witness, saved in state.saves.items() if saved["consumed"] is None and saved["record"]["location"] == location]
        require(len(matches) == 1, "restoration POP lacks exact live witness", "local-effect")
        _restoration_save(state, matches[0])
        result[name] = matches[0]
    return result


def _restoration_operation(state, instruction, unresolved):
    """Admit only operations needed by this exact straight-line restoration."""
    from capstone.arm import ARM_OP_REG, ARM_OP_IMM, ARM_OP_MEM
    names = [private.Checker.regname(instruction, operand.reg) if operand.type == ARM_OP_REG else None for operand in instruction.operands]
    if instruction.mnemonic == "pop":
        witnesses = _restoration_pop(state, instruction)
        require(any(name in unresolved or state.saves[witness]["record"]["register"] in unresolved for name, witness in witnesses.items()),
                "unrelated POP in restoration corridor", "local-effect")
        return None
    if instruction.mnemonic in ("mov", "movs"):
        require(len(names) == 2 and names[0] in private.NONVOLATILE[:-1] and
                names[1] in state.registers and names[1] not in state.retired_registers(),
                "pending alias propagation or unrelated MOV", "local-effect")
        witness = state.restored_by.get(names[1])
        record = _restoration_save(state, witness, live=False)
        require(record["register"] == names[0] and state.equivalent(state.registers[names[1]], record["value"]) and
                state.bitvector(state.registers[names[1]]) == state.bitvector(record["value"]),
                "MOV is not the exact saved entry restoration", "local-effect")
        require(names[0] in unresolved or names[0] in state.touched and (state.restored_by.get(names[0]) != witness or
                not state.equivalent(state.registers[names[0]], record["value"])),
                "unnecessary MOV in restoration corridor", "local-effect")
        return None
    if instruction.mnemonic == "ldr":
        require(len(names) == 2 and names[0] in private.REGISTERS[:8] and instruction.operands[1].type == ARM_OP_MEM and
                private.Checker.regname(instruction, instruction.operands[1].mem.base) == "sp" and not instruction.operands[1].mem.index,
                "restoration load is not an exact SP saved word", "local-effect")
        location = state.locate(state.registers["sp"], instruction.operands[1].mem.disp, 4)
        matches = [witness for witness, saved in state.saves.items() if saved["consumed"] is None and saved["record"]["location"] == location]
        require(len(matches) == 1, "restoration load lacks exact save witness", "local-effect")
        record = _restoration_save(state, matches[0])
        require(record["register"] in unresolved, "unrelated save load in restoration corridor", "local-effect")
        return matches[0]
    if instruction.mnemonic == "add" and names[0] == "sp":
        require(len(names) == 2 and instruction.operands[1].type == ARM_OP_IMM and instruction.operands[1].imm > 0,
                "dynamic restoration SP adjustment", "local-effect")
        start, size = state.stack_address(), instruction.operands[1].imm
        regions = [region for region in state.regions.values() if region["kind"] == "stack-allocation" and region["lifetime"] == "live" and
                   region["frame"] == state.context["frame"] and start <= state.base(region["id"])[1] < start + size]
        require(size % 4 == 0 and sum(region["size"] for region in regions) == size and all(
            any(saved["record"]["location"]["region"] == region["id"] and saved["consumed"] is not None for saved in state.saves.values())
            for region in regions), "restoration SP adjustment is not consumed-save retirement", "local-effect")
        return None
    raise Failure("local-effect", "forbidden instruction in restoration corridor: " + instruction.mnemonic)


def _restoration_load(state, instruction, witness):
    destination = private.Checker.regname(instruction, instruction.operands[0].reg)
    record = _restoration_save(state, witness)
    before = state.registers[destination]
    state.reads, state.writes = [], []
    state.read(record["location"])
    state.registers[destination] = record["value"]
    state.identities[destination] = record["register"]
    state.restored_by[destination] = witness
    state.saves[witness]["consumed"] = len(state.events)
    state.event("save-consume", witness=witness, register=destination)
    if destination in private.NONVOLATILE:
        state.touched.add(destination)
        state.restore_steps[destination].append(len(state.events))
    following = instruction.address + instruction.size
    changes = [] if before == record["value"] else [{"register": destination, "before": before, "after": record["value"]}]
    state.event("instruction", encoding=bytes(instruction.bytes).hex(), registers=changes, reads=state.reads, writes=[], next_pc=following)
    state.check_live_aliases()
    return following


def _restoration_plan(state, following, program, capture, budget):
    """Prove from actual decoded operations; the isolated state is discarded."""
    aliases = state.retired_registers()
    require(aliases and all(name in private.REGISTERS[:12] for name in aliases), "retired r12/control has no restoration exception", "local-effect")
    probe = copy.deepcopy(state)
    probe.pc = following
    probe._trial_aliases = True
    require(following in program, "restoration continuation is not owned")
    first = program[following]
    low = {name for name in aliases if name in private.REGISTERS[:4]}
    first_pop = _restoration_pop(probe, first) if low else {}
    require(low <= set(first_pop), "low retired alias requires immediately next POP overwrite", "local-effect")
    kinds = {name: "nonvolatile" for name in aliases}
    for name in low:
        kinds[name] = "next-pop-shuttle"
    if first.mnemonic == "pop" and not first_pop:
        first_pop = _restoration_pop(probe, first)
    for name in set(aliases) & set(first_pop):
        if probe.saves[first_pop[name]]["record"]["register"] != name:
            kinds[name] = "next-pop-shuttle"
    unresolved, records, operations, corridor = set(aliases), {}, [], []
    while unresolved:
        budget.transfer()
        require(probe.pc in program, "restoration leaves owned instructions")
        instruction = program[probe.pc]
        location = {"body": probe.body["id"], "pc": probe.pc}
        witness = _restoration_operation(probe, instruction, unresolved)
        operations.append(location)
        corridor.append({"location": location, "encoding": bytes(instruction.bytes).hex()})
        next_pc = _restoration_load(probe, instruction, witness) if witness is not None else _helper_transfer(probe, instruction, capture)
        remaining = probe.retired_registers()
        require(set(remaining) <= unresolved, "restoration introduced unproved retired alias", "local-effect")
        for name in sorted(unresolved - set(remaining), key=lambda name: int(name[1:])):
            restored = probe.restored_by.get(name)
            record = _restoration_save(probe, restored, live=False)
            if kinds[name] == "nonvolatile":
                require(record["register"] == name and probe.equivalent(probe.registers[name], _restoration_original(probe, name)) and
                        probe.bitvector(probe.registers[name]) == probe.bitvector(_restoration_original(probe, name)),
                        "nonvolatile overwrite is not original-entry restoration", "local-effect")
            else:
                require(len(operations) == 1 and instruction.mnemonic == "pop" and name in first_pop and restored == first_pop[name],
                        "shuttle overwrite is not the immediately next genuine POP", "local-effect")
            records[name] = {"kind": kinds[name], "register": name, "retired": aliases[name], "overwrite": location,
                             "witness": restored, "restored_value": record["value"], "operations": copy.deepcopy(operations)}
        unresolved &= set(remaining)
        probe.pc = next_pc
    return [records[name] for name in sorted(records, key=lambda name: int(name[1:]))], corridor


def _restoration_transfer(state, instruction, capture, program, budget):
    state.guard(instruction)
    retiring = instruction.mnemonic == "pop" or instruction.mnemonic == "add" and instruction.op_str.startswith("sp,")
    trial = copy.deepcopy(state) if retiring or state.pending else state
    trial._trial_aliases = bool(retiring or state.pending)
    unresolved = {obligation["register"] for obligation in state.pending.values()}
    witness = _restoration_operation(trial, instruction, unresolved) if unresolved else None
    following = _restoration_load(trial, instruction, witness) if witness is not None else _helper_transfer(trial, instruction, capture)
    if unresolved:
        trial.corridor.pop(0)
        for identifier, obligation in list(trial.pending.items()):
            if obligation["overwrite"] == {"body": trial.body["id"], "pc": instruction.address}:
                require(trial.restored_by.get(obligation["register"]) == obligation["witness"] and
                        trial.equivalent(trial.registers[obligation["register"]], obligation["restored_value"]) and
                        trial.bitvector(trial.registers[obligation["register"]]) == trial.bitvector(obligation["restored_value"]),
                        "actual restoration disagrees with proved saved identity", "local-effect")
                trial.pending.pop(identifier)
                trial.event("pending-discharge", obligation=identifier)
    elif trial.retired_registers():
        require(retiring and any(region["lifetime"] == "live" and trial.regions[reference]["lifetime"] == "retired"
                                 for reference, region in state.regions.items()),
                "pending restoration requires an actual immediate retirement", "local-effect")
        records, trial.corridor = _restoration_plan(trial, following, program, capture, budget)
        for record in records:
            identifier = trial.new_id("o")
            obligation = {"id": identifier, **record, "opened": len(trial.events)}
            trial.pending[identifier] = obligation
            trial.pending_restores[identifier] = obligation
            trial.event("pending-open", obligation=obligation)
    trial._trial_aliases = False
    trial.check_live_aliases()
    return trial, following


@dataclass(frozen=True)
class RestorationPrefixes:
    """Incomplete internal P7 continuation only; no P5/public proof export."""
    encoded: str

    def inspect(self):
        return private.decode(self.encoded)


def execute_restoration_prefixes(capture):
    """Continue proved retirement corridors, stopping before registration."""
    try:
        return _execute_caller_prefixes(capture, qualify_helpers=True, restore=True)
    except RecursionError as error:
        raise Failure("unsupported", "restoration representation depth exhausted") from error
    except (KeyError, TypeError, ValueError, struct.error) as error:
        raise Failure("identity", "malformed bound restoration capture") from error


def execute_caller_prefixes(capture):
    """Explore decoded caller prefixes; every external call remains unqualified.

    No caller-selected paths, role overrides, effects, budgets or summaries are
    accepted. A returned object is explicitly incomplete and ineligible.
    """
    try:
        return _execute_caller_prefixes(capture)
    except RecursionError as error:
        raise Failure("unsupported", "caller representation depth exhausted") from error
    except (KeyError, TypeError, ValueError, struct.error) as error:
        raise Failure("identity", "malformed bound caller capture") from error


def _execute_caller_prefixes(capture, qualify_helpers=False, restore=False):
    record, program, calls = _caller_program(capture)
    context = capture.fixed.request.to_dict()["entry"]
    state_type = _RestorationState if restore else _HelperState if qualify_helpers else _CallerState
    initial = state_type(context, record["caller"], capture.fixed.rom.data)
    initial.literal_bindings = {item["resolved"]["linked_address"]: item["resolved"]
                               for item in record["relocations"] if item["kind"] == 2}
    initial.function_targets = {item["role"]: item["target"] | 1 for item in record["placement"]["bindings"]
                                if item["role"] == "callback"}
    budget = _CallerBudget()
    budget.state()
    pending, finished = [initial], []
    helper_programs = {}
    selector_roots, count_roots, excluded_seven = set(), set(), set()
    comparison_pc = capture.fixed.address + record["switch"]["comparison_offset"]
    dispatch_pc = capture.fixed.address + record["switch"]["dispatch_offset"]
    branches = {"beq", "bne", "bhi", "bls", "bhs", "blo"}
    while pending:
        state = pending.pop()
        while True:
            budget.transfer()
            in_caller = state.body["id"] == record["caller"]["id"]
            current_program = program if in_caller else helper_programs[state.body["start"]][1]
            require(state.pc in current_program, "execution leaves owned instruction starts")
            insn = current_program[state.pc]
            if restore:
                state.guard(insn)
            if insn.mnemonic == "bl":
                target = calls[state.pc]["target"] if in_caller else insn.operands[0].imm
                role = "registration" if state.pc == capture.fixed.request.to_dict()["site"] else "helper"
                if not qualify_helpers or role == "registration":
                    require(not restore or not state.pending, "registration has pending restoration", "local-effect")
                    finished.append(state.output("suspended-" + role, target))
                    break
                if target not in helper_programs:
                    helper_programs[target] = _helper_program(capture.fixed, target)
                state.edges.append({"from": insn.address, "to": target, "kind": "helper-call"})
                state.enter(helper_programs[target][0], insn)
                continue
            if in_caller and state.pc == comparison_pc:
                register = private.Checker.regname(insn, insn.operands[0].reg)
                root = state.root(state.registers[register])
                require(root is not None and root[0] == "low8", "switch selector lacks decoded low-byte raw provenance", "unsupported")
                selector_roots.add(root)
                candidates = {item_root for item_root, number in state.conditionals if number == 0 and item_root != root and item_root[0] == "low8"}
                count_roots.update(candidates)
                excluded_seven.update(item_root for item_root, number in state.conditionals if number == 7 and item_root == root)
            if in_caller and state.pc == dispatch_pc and state.switch_choice is None:
                shift = insn.operands[1]
                root = state.root(state.registers[private.Checker.regname(insn, shift.reg)])
                require(root is not None and root in selector_roots, "dispatch selector provenance differs")
                for item in reversed(record["switch"]["targets"]):
                    candidate = copy.deepcopy(state)
                    if candidate.refine(root, "beq", item["index"], True):
                        budget.state()
                        candidate.switch_choice = item["index"]
                        pending.append(candidate)
                break
            if insn.mnemonic in branches | ({"bgt", "ble", "bge", "blt"} if qualify_helpers else set()):
                require(state.flags is not None, "caller branch lacks actual CMP flags", "unsupported")
                left, right = state.flags
                root, number = state.root(left), state.number(right)
                if root is not None and number is not None and insn.mnemonic in ("beq", "bne"):
                    state.conditionals.append((root, number))
                following, target = insn.address + insn.size, insn.operands[0].imm
                concrete = state.number(left)
                for taken in _BRANCH_CHOICES:
                    candidate = copy.deepcopy(state)
                    if root is not None and number is not None and insn.mnemonic in branches:
                        feasible = candidate.refine(root, insn.mnemonic, number, bool(taken))
                    else:
                        require(concrete is not None and number is not None, "unsupported caller branch predicate", "unsupported")
                        signed_left = concrete - 0x100000000 if concrete & 0x80000000 else concrete
                        signed_right = number - 0x100000000 if number & 0x80000000 else number
                        outcome = {"beq": concrete == number, "bne": concrete != number, "bhi": concrete > number,
                                   "bls": concrete <= number, "bhs": concrete >= number, "blo": concrete < number,
                                   "bgt": signed_left > signed_right, "ble": signed_left <= signed_right,
                                   "bge": signed_left >= signed_right, "blt": signed_left < signed_right}[insn.mnemonic]
                        feasible = outcome == bool(taken)
                    if feasible:
                        budget.state()
                        destination = target if taken else following
                        candidate.decision("branch", taken, destination)
                        candidate.event("instruction", encoding=bytes(insn.bytes).hex(), registers=[], reads=[], writes=[], next_pc=destination)
                        candidate.edges.append({"from": insn.address, "to": destination,
                                                "kind": "branch-taken" if taken else "branch-fallthrough"})
                        candidate.pc = destination
                        pending.append(candidate)
                break
            if restore:
                state, following = _restoration_transfer(state, insn, capture, current_program, budget)
            elif qualify_helpers:
                retiring = insn.mnemonic == "pop" or insn.mnemonic == "add" and insn.op_str.startswith("sp,")
                trial = copy.deepcopy(state) if retiring else state
                try:
                    following = _helper_transfer(trial, insn, capture)
                except Failure as error:
                    retired = sorted(region for region in state.regions if state.regions[region]["lifetime"] == "live" and
                                     trial.regions[region]["lifetime"] == "retired")
                    if retired and "requires S3 restoration proof" in str(error):
                        finished.append(state.output("suspended-S3-retirement", {"instruction": bytes(insn.bytes).hex(),
                                                                               "would_retire": retired, "obligation": str(error)}))
                        break
                    raise
                state = trial
            else:
                following = _caller_transfer(state, insn, capture)
            if in_caller and insn.mnemonic == "mov" and state.pc == dispatch_pc + 8:
                choice = state.switch_choice
                require(choice is not None and following == capture.fixed.address + record["switch"]["targets"][choice]["target_offset"],
                        "decoded dispatch target differs")
                state.decision("switch", choice, following)
                kind = "switch-case"
            elif insn.mnemonic == "bx":
                if qualify_helpers and state.scopes:
                    state.edges.append({"from": insn.address, "to": following, "kind": "helper-return"})
                    state.leave()
                    continue
                state.edges.append({"from": insn.address, "to": None, "kind": "return"})
                finished.append(state.output("returned-prefix", state.context["lr"]))
                break
            else:
                kind = "branch-taken" if insn.mnemonic == "b" else "fallthrough"
            state.edges.append({"from": insn.address, "to": following, "kind": kind})
            state.pc = following
    require(len(selector_roots) == len(count_roots) == 1 and selector_roots == excluded_seven,
            "caller raw-role normalization/early-return evidence differs", "unsupported")
    count, selector = next(iter(count_roots)), next(iter(selector_roots))
    raw = [{"role": role, "register": root[2], "value": root[1]} for role, root in (("count", count), ("selector", selector))]
    validate_raw_inputs(capture.fixed.request, raw)
    paths = [item["path"] for item in finished]
    require(len(paths) == len(set(paths)), "duplicate completed prefix trace with unmerged states", "unsupported")
    require(finished and any(item["status"] == "returned-prefix" for item in finished) and
            any(item["status"].startswith("suspended-") for item in finished), "incomplete caller prefix exploration", "unsupported")
    result_type = RestorationPrefixes if restore else HelperPrefixes if qualify_helpers else CallerPrefixes
    kind = "internal-incomplete-restoration-prefixes-v1" if restore else "internal-incomplete-helper-prefixes-v1" if qualify_helpers else "internal-incomplete-caller-prefixes-v1"
    return result_type(canonical({"kind": kind, "complete": False,
                                    "raw_inputs": raw, "prefixes": sorted(finished, key=lambda item: item["path"]),
                                    "states": budget.states, "transfers": budget.transfers,
                                    "remaining": (["P6 private bridge/projection/import", "post-registration caller retirement/return", "lossless P5 materialization and complete histories"] if restore else
                                                  ["S3 private bridge/projection/retirement", "lossless P5 materialization and complete histories"] if qualify_helpers else
                                                  ["S2b helper qualification", "S3 private bridge/projection/retirement", "complete P5 histories"])}))
