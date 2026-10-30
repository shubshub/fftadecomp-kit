"""Private conditional descriptor registration; never a canonical match profile."""

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re
import sys

from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
from capstone.arm import ARM_OP_IMM, ARM_OP_REG, ARM_OP_MEM


POLICY = "conditional-registration-effects-private-v1"
SCHEMA = "conditional-registration-effects-evidence-v1"
OPERATION = "descriptor28-phase0-payload12-v1"
CANONICAL_REPORT_ELIGIBLE = False
ROM_BASE = 0x08000000
REGISTERS = tuple("r" + str(number) for number in range(13))
NONVOLATILE = tuple("r" + str(number) for number in range(4, 12)) + ("sp",)
ROLES = ("allocator", "allocator-child", "callback", "callback-thunk",
         "initializer", "initializer-thunk", "registration")
CLAUSES = (
    "stack-domain-v1", "stable-region-roles-v1", "manager-owner-list-v1",
    "allocator40-effects-v1", "allocator-output-roles-v1", "installed-image-v1",
    "external-values-v1", "returning-environment-v1",
)
MAX_STEPS = 4096
MAX_DEPTH = 16


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"),
                      ensure_ascii=False, allow_nan=False)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def pin(data):
    return {"sha256": digest(data), "size": len(data)}


def fingerprint(record):
    fields = {key: value for key, value in record.items() if key != "fingerprint"}
    return digest(SCHEMA.encode() + b"\0" + canonical(fields).encode())


class Failure(Exception):
    def __init__(self, category, reason):
        super().__init__(reason)
        self.category = category


def require(condition, reason, category="identity"):
    if not condition:
        raise Failure(category, reason)


def failure_reason(error):
    return "".join(character if 32 <= ord(character) <= 126 else ascii(character)[1:-1]
                   for character in str(error))[:1024] or "invalid input"


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "duplicate JSON member: " + key)
        result[key] = value
    return result


def decode(text):
    try:
        return json.loads(text, object_pairs_hook=unique_object,
                          parse_constant=lambda value: (_ for _ in ()).throw(
                              Failure("identity", "nonfinite JSON value")))
    except (ValueError, TypeError) as error:
        raise Failure("identity", "invalid JSON: " + str(error)) from error


def fields(**members):
    return members


def choice(*values):
    return ("enum", values)


def sequence(spec):
    return ("list", spec)


def optional(spec):
    return ("optional", spec)


def tagged(**variants):
    return ("tagged", variants)


SPECS = {
    "Span": fields(start="U32", end="U32"),
    "Slice": fields(region="ID", offset="U32", size="Size"),
    "Separation": fields(left="Slice", right="Slice"),
    "Interval": fields(begin="Boundary", end="Boundary"),
    "StackWindow": fields(anchor=choice("allocator-entry-sp"), low="SignedOffset", high=choice(0)),
    "Pin": fields(sha256="Digest", size="Size"),
    "Base": tagged(concrete=fields(tag=choice("concrete"), address="U32"),
                   symbolic=fields(tag=choice("symbolic"), anchor="ID", offset="SignedOffset"),
                   relative=fields(tag=choice("relative"), region="ID", offset="U32"),
                   allocated=fields(tag=choice("allocated"), domain="Slice", clause=choice("B4"))),
    "Region": fields(id="ID", base="Base", size="Size", permission=choice("r", "rw", "rx"),
                     kind=choice("stack-domain", "stack-allocation", "external", "rom", "runtime-image"),
                     lifetime=choice("live", "retired"), frame=optional("ID")),
    "Frame": fields(id="ID", invocation="ID", parent=optional("ID"), entry_sp="ID",
                    allocations=sequence("ID"), saves=sequence("Save")),
    "Save": fields(witness="ID", register="Register", location="Slice", value="ID"),
    "Origin": tagged(register=fields(tag=choice("register"), invocation="ID", register="Register"),
                     memory=fields(tag=choice("memory"), region="ID", offset="U32")),
    "Value": tagged(constant=fields(id="ID", tag=choice("constant"), width="Width", value="U32"),
                    pointer=fields(id="ID", tag=choice("pointer"), region="ID", offset="U32"),
                    function=fields(id="ID", tag=choice("function"), body="BodyRole"),
                    control=fields(id="ID", tag=choice("control"), invocation="ID", target=optional("U32")),
                    symbolic=fields(id="ID", tag=choice("symbolic"), width="Width", origin="Origin"),
                    bytes=fields(id="ID", tag=choice("bytes"), width="Width", bytes=sequence("Byte")),
                    **{"condition-word": fields(id="ID", tag=choice("condition-word"), clause=choice("B5"),
                                                register=choice("r1", "r2", "r3", "r12"), excluded=sequence("Slice"))}),
    "Byte": tagged(constant=fields(tag=choice("constant"), value="U8"),
                   fragment=fields(tag=choice("fragment"), value="ID", index="ByteIndex"),
                   unknown=fields(tag=choice("unknown"), origin="Origin")),
    "Cell": fields(location="Slice", bytes=sequence("Byte")),
    "Registers": {register: "ID" for register in REGISTERS},
    "Context": fields(invocation="ID", frame="ID", registers="Registers", sp="ID", lr="ID",
                      regions=sequence("Region"), frames=sequence("Frame"), values=sequence("Value"), cells=sequence("Cell")),
    "Body": fields(role="BodyRole", start="U32", end="U32", sha256="Digest", code=sequence("Span"),
                   literals=sequence("Span"), alignment=sequence("Span")),
    "Binding": tagged(direct=fields(id="ID", tag=choice("direct"), caller="BodyRole", site="U32", target="BodyRole"),
                      **{"through-thunk": fields(id="ID", tag=choice("through-thunk"), caller="BodyRole", site="U32",
                                                 thunk="BodyRole", register=choice("r2", "r3"), target="BodyRole"),
                         "image": fields(id="ID", tag=choice("image"), slot="U32", target="U32",
                                         source="BodyRole", destination="U32", size="Size")}),
    "Maps": fields(functions="Pin", function_text="Pin", symbol_sizes="Pin", data_symbols="Pin"),
    "EngineFile": fields(name="ID", pin="Pin"),
    "Inputs": fields(rom="Pin", maps="Maps", engine=sequence("EngineFile"), bodies=sequence("Body"),
                     bindings=sequence("Binding"), context="Context"),
    "Location": fields(invocation="ID", body="BodyRole", pc="U32"),
    "RegisterChange": fields(register="Register", before="ID", after="ID"),
    "Access": fields(location="Slice", bytes=sequence("Byte")),
    "Restoration": fields(register=choice(*NONVOLATILE), before="ID", after="ID", witness=optional("ID")),
    "Retention": fields(location="Slice", value="ID", step="U32"),
    "Dependency": fields(body="BodyRole", sha256="Digest"),
    "CompleteReturn": fields(status=choice("conditional-complete"), invocation="ID", site="Location", target="ID",
                             registers="Registers", sp="ID", lr="ID", restorations=sequence("Restoration"),
                             live=sequence("ID"), retired=sequence("ID")),
}
PARAMETERS = (
    fields(domain="Slice", entry_sp="ID", allocator_window="StackWindow"),
    fields(descriptor="Slice", parameters="Slice", manager="Slice", parent=optional("Slice"),
           nodes=sequence("Slice"), protected=sequence("Slice"), separation=sequence("Separation")),
    fields(manager_cell="Slice", manager_value="ID", owner_value="ID", phase_value="ID", head_value="ID", chain=sequence("ID")),
    fields(binding=choice("allocator-call"), domain="Slice", owner_metadata="Slice",
           stack_window=choice("B1.allocator_window"), result_role=choice("task"), result_bytes=choice(40)),
    fields(binding=choice("allocator-call"), result_role=choice("task")),
    fields(binding=choice("initializer-image"), call=choice("initializer-call"), image="Slice"),
    fields(data_value="ID", source="Slice", operation=choice("copy-only")),
    fields(binding=choice("allocator-call"), interference_scope=choice("registration-call")),
)
SPECS["Condition"] = ("condition",)
SPECS["Event"] = tagged(
    instruction=fields(tag=choice("instruction"), step="U32", location="Location", encoding="Encoding",
                       registers=sequence("RegisterChange"), reads=sequence("Access"), writes=sequence("Access"), next_pc="U32"),
    **{tag: fields(tag=choice(tag), step="U32", location="Location", **members) for tag, members in (
        ("frame-enter", {"frame": "ID"}), ("allocate-stack", {"region": "ID"}),
        ("retire-stack", {"region": "ID"}), ("call-enter", {"binding": "ID", "callee": "ID"}),
        ("call-return", {"binding": "ID", "callee": "ID"}), ("assumed-allocator", {"assumption": "ID"}))})
SPECS["AssumedEffect"] = fields(id="ID", tag=choice("allocator"), status=choice("assumed"), binding=choice("allocator-call"),
    interval="Interval", clauses=sequence("ClauseID"), external_domains=sequence("Slice"), stack_window="Slice", task="ID",
    outputs="Registers", lr="ID", return_control="ID", restorations=sequence("Restoration"), subordinate_lifetime=choice("ended"))
SPECS["Effects"] = fields(values=sequence("Value"), regions=sequence("Region"), frames=sequence("Frame"), events=sequence("Event"),
    assumed=sequence("AssumedEffect"), retained=sequence("Retention"), retired=sequence("ID"), assumptions_used=sequence("ClauseID"))
SPECS["Certificate"] = fields(schema=choice(SCHEMA), policy=choice(POLICY), operation=choice(OPERATION), inputs="Inputs",
    conditions=sequence("Condition"), dependencies=sequence("Dependency"), effects="Effects", fingerprint="Digest",
    **{"complete-return": "CompleteReturn"})
SPECS["Refusal"] = fields(status=choice("refused"), category=choice("identity", "unmet-condition", "contradictory-condition", "unsupported", "local-effect"),
    invocation=optional("ID"), site=optional("Location"), path=sequence("Location"), reason="Reason", diagnostic=sequence("Event"))


def validate(value, spec, path="root"):
    if isinstance(spec, str) and spec in SPECS:
        return validate(value, SPECS[spec], path)
    if isinstance(spec, dict):
        require(type(value) is dict and set(value) == set(spec), path + ": wrong fields")
        for key, child in spec.items():
            validate(value[key], child, path + "." + key)
        return
    if isinstance(spec, tuple):
        kind = spec[0]
        if kind == "optional":
            return None if value is None else validate(value, spec[1], path)
        if kind == "list":
            require(type(value) is list, path + ": expected list")
            for index, child in enumerate(value):
                validate(child, spec[1], path + "[" + str(index) + "]")
            return
        if kind == "enum":
            require(any(type(value) is type(member) and value == member for member in spec[1]), path + ": invalid enum")
            return
        if kind == "tagged":
            require(type(value) is dict and type(value.get("tag")) is str and value["tag"] in spec[1], path + ": invalid tag")
            return validate(value, spec[1][value["tag"]], path)
        if kind == "condition":
            require(type(value) is dict and value.get("id") in tuple("B" + str(number) for number in range(1, 9)), path + ": invalid clause")
            number = int(value["id"][1:]) - 1
            return validate(value, fields(id=choice(value["id"]), clause=choice(CLAUSES[number]), invocation="ID",
                source=choice("declared-invocation"), status=choice("assumed"), interval="Interval", parameters=PARAMETERS[number]), path)
    numbers = {"U32": (0, 0xffffffff), "Size": (1, 0xffffffff), "U8": (0, 255),
               "ByteIndex": (0, 3), "SignedOffset": (-0x80000000, 0x7fffffff)}
    if spec in numbers:
        lower, upper = numbers[spec]
        require(type(value) is int and lower <= value <= upper, path + ": invalid integer")
    elif spec == "Width":
        validate(value, choice(1, 2, 4), path)
    elif spec in ("Register", "BodyRole", "ClauseID", "Boundary"):
        options = {"Register": REGISTERS + ("sp", "lr"), "BodyRole": ROLES,
                   "ClauseID": tuple("B" + str(number) for number in range(1, 9)),
                   "Boundary": tuple(scope + "-" + edge for scope in ("registration", "allocator", "initializer") for edge in ("entry", "return"))}
        validate(value, choice(*options[spec]), path)
    else:
        patterns = {"ID": r"[A-Za-z][A-Za-z0-9_./:-]{0,127}", "Digest": r"[0-9a-f]{64}",
                    "Encoding": r"(?:[0-9a-f]{4}|[0-9a-f]{8})", "Reason": r"[ -~]{1,1024}"}
        require(spec in patterns and type(value) is str and re.fullmatch(patterns[spec], value) is not None, path + ": invalid " + str(spec))


@dataclass(frozen=True)
class InvocationContext:
    encoded: str

    @classmethod
    def from_dict(cls, record):
        validate(record, "Context")
        return cls(canonical(record))


@dataclass(frozen=True)
class InvocationConditions:
    encoded: str

    @classmethod
    def from_list(cls, records):
        validate(records, sequence("Condition"))
        return cls(canonical(records))


@dataclass(frozen=True)
class RegistrationEvidence:
    encoded: str
    rom: bytes
    maps: tuple

    @classmethod
    def from_dict(cls, inputs, rom, maps):
        validate(inputs, "Inputs")
        require(type(rom) is bytes and all(type(value) is bytes for value in maps.values()), "trusted images must be immutable bytes")
        require(set(maps) == set(SPECS["Maps"]), "trusted map set differs")
        return cls(canonical(inputs), rom, tuple(sorted(maps.items())))


@dataclass(frozen=True)
class ConditionalEffects:
    encoded: str

    def to_dict(self):
        return decode(self.encoded)


@dataclass(frozen=True)
class Refusal:
    encoded: str

    def to_dict(self):
        return decode(self.encoded)


def engine_files():
    import capstone
    paths = {"conditional_registration_effects.py": Path(__file__)}
    paths.update({name.replace(".", "/"): Path(module.__file__) for name, module in tuple(sys.modules.items())
                  if name.startswith("capstone") and getattr(module, "__file__", None)})
    library = Path(capstone._cs._name)
    if not library.is_file():
        loaded = {line.split()[-1] for line in Path("/proc/self/maps").read_text().splitlines()
                  if line.split()[-1].endswith("/" + library.name)}
        require(len(loaded) == 1, "decoder library identity is ambiguous")
        library = Path(next(iter(loaded)))
    require(library.is_file(), "decoder library identity unavailable")
    paths["capstone-library"] = library
    return [{"name": name, "pin": pin(path.read_bytes())} for name, path in sorted(paths.items())]


def width(value):
    return value.get("width", 4)


def slc(region, offset, size):
    return {"region": region, "offset": offset, "size": size}


def value_bytes(value):
    if value["tag"] == "constant":
        return [{"tag": "constant", "value": (value["value"] >> (index * 8)) & 255} for index in range(width(value))]
    if value["tag"] == "bytes":
        return value["bytes"]
    return [{"tag": "fragment", "value": value["id"], "index": index} for index in range(width(value))]


class Checker:
    def __init__(self, evidence, context, conditions):
        self.inputs = decode(evidence.encoded)
        self.context = decode(context.encoded)
        self.conditions = decode(conditions.encoded)
        self.rom = evidence.rom
        self.maps = dict(evidence.maps)
        self.events = []
        self.location = None
        self.call_path = []
        self.values = {}
        self.regions = {}
        self.frames = {}
        self.memory = {}
        self.restored = {}
        self.saved_at = {}
        self.pointer_limits = {}
        self.output_values = []
        self.output_regions = []
        self.output_frames = []
        self.assumed = []
        self.retained = []
        self.steps = 0
        self.counter = 0
        self.decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
        self.decoder.detail = True

    def new_id(self, kind):
        self.counter += 1
        return "derived/" + self.context["invocation"] + "/" + kind + "/" + str(self.counter)

    def make(self, tag, **members):
        record = {"id": self.new_id("value"), "tag": tag, **members}
        self.values[record["id"]] = record
        self.output_values.append(record)
        return record["id"]

    def constant(self, number, size=4):
        return self.make("constant", width=size, value=number & ((1 << (size * 8)) - 1))

    def pointer(self, region, offset=0):
        require(0 <= offset <= self.regions[region]["size"], "pointer arithmetic outside region", "local-effect")
        return self.make("pointer", region=region, offset=offset)

    def number(self, reference):
        value = self.values[reference]
        if value["tag"] == "constant":
            return value["value"]
        if value["tag"] == "function":
            return self.bodies[value["body"]]["start"] | 1
        if value["tag"] == "control":
            return value["target"]
        if value["tag"] == "pointer":
            anchor, offset = self.base(value["region"])
            return offset + value["offset"] if anchor == "concrete" else None
        if value["tag"] == "bytes" and all(part["tag"] == "constant" for part in value["bytes"]):
            return sum(part["value"] << (8 * index) for index, part in enumerate(value["bytes"]))
        return None

    def base(self, reference, active=()):
        require(reference in self.regions and reference not in active, "invalid region containment")
        region = self.regions[reference]
        base = region["base"]
        if base["tag"] == "concrete":
            require(base["address"] + region["size"] <= 0x100000000, "wrapping concrete region")
            return "concrete", base["address"]
        if base["tag"] == "symbolic":
            require(-0x80000000 <= base["offset"] + region["size"] <= 0xffffffff, "wrapping symbolic region")
            return base["anchor"], base["offset"]
        if base["tag"] == "allocated":
            return reference, 0
        parent = self.regions.get(base["region"])
        require(parent is not None and base["offset"] + region["size"] <= parent["size"], "relative region outside parent")
        anchor, offset = self.base(base["region"], (*active, reference))
        return anchor, offset + base["offset"]

    def interval(self, location):
        require(location["region"] in self.regions, "dangling region reference")
        region = self.regions[location["region"]]
        require(location["offset"] + location["size"] <= region["size"], "slice exceeds region", "contradictory-condition")
        anchor, address = self.base(location["region"])
        return anchor, address + location["offset"], address + location["offset"] + location["size"]

    def overlap(self, left, right):
        left_anchor, left_start, left_end = self.interval(left)
        right_anchor, right_start, right_end = self.interval(right)
        return left_anchor == right_anchor and max(left_start, right_start) < min(left_end, right_end)

    def equivalent(self, left, right):
        if left == right:
            return True
        first, second = self.values[left], self.values[right]
        if first["tag"] == second["tag"] == "pointer":
            return first["region"] == second["region"] and first["offset"] == second["offset"]
        if first["tag"] == second["tag"] == "constant":
            return first["value"] == second["value"] and width(first) == width(second)
        return {key: value for key, value in first.items() if key != "id"} == {key: value for key, value in second.items() if key != "id"}

    def origin_check(self, origin):
        if origin["tag"] == "memory":
            require(origin["region"] in self.regions and origin["offset"] < self.regions[origin["region"]]["size"], "invalid memory origin")
        else:
            require(origin["invocation"] in {frame["invocation"] for frame in self.frames.values()}, "invalid register origin")

    def fragments_check(self, parts, active=()):
        for part in parts:
            if part["tag"] == "unknown":
                self.origin_check(part["origin"])
            elif part["tag"] == "fragment":
                reference = part["value"]
                require(reference in self.values and reference not in active, "invalid or cyclic fragment reference")
                value = self.values[reference]
                require(part["index"] < width(value), "fragment index exceeds value width")
                if value["tag"] == "bytes":
                    self.fragments_check(value["bytes"], (*active, reference))

    def syntax(self):
        validate(self.inputs, "Inputs")
        validate(self.context, "Context")
        validate(self.conditions, sequence("Condition"))
        require(self.inputs["context"] == self.context, "context differs from bound inputs")
        seen = set()
        for field, registry in (("regions", self.regions), ("frames", self.frames), ("values", self.values)):
            records = self.context[field]
            require([record["id"] for record in records] == sorted(record["id"] for record in records), "unsorted registry")
            for record in records:
                identifier = record["id"]
                require(identifier not in seen and not identifier.startswith("derived/"), "duplicate or output-only input identity")
                seen.add(identifier)
                registry[identifier] = record
        require(self.context["frame"] in self.frames, "unknown current frame")
        require(self.frames[self.context["frame"]]["invocation"] == self.context["invocation"], "frame invocation differs")
        for region in self.regions.values():
            require(region["base"]["tag"] != "allocated", "input allocated result forbidden")
            self.base(region["id"])
            if region["kind"] == "stack-allocation":
                require(region["frame"] in self.frames and region["permission"] == "rw", "invalid stack allocation")
            else:
                require(region["frame"] is None and region["lifetime"] == "live", "invalid non-stack lifetime")
                required = {"rom": "r", "runtime-image": "rx", "stack-domain": "rw"}.get(region["kind"])
                require(required is None or region["permission"] == required, "region permission mismatch")
        for frame in self.frames.values():
            require(frame["entry_sp"] in self.values, "invalid frame SP")
            require(frame["allocations"] == sorted(reference for reference, region in self.regions.items() if region["frame"] == frame["id"]), "frame allocation back-reference mismatch")
            ancestry = set()
            current = frame
            while current is not None:
                require(current["id"] not in ancestry, "cyclic frame parents")
                ancestry.add(current["id"])
                parent = current["parent"]
                require(parent is None or parent in self.frames, "unknown parent frame")
                current = self.frames.get(parent)
            require(len(ancestry) <= MAX_DEPTH, "frame depth limit", "unsupported")
            for save in frame["saves"]:
                require(save["witness"] not in seen and not save["witness"].startswith("derived/"), "duplicate save witness")
                seen.add(save["witness"])
                require(save["location"]["size"] == 4 and save["value"] in self.values, "invalid save value")
                require(self.regions.get(save["location"]["region"], {}).get("frame") == frame["id"], "save belongs to wrong frame")
        for value in self.values.values():
            tag = value["tag"]
            require(tag != "condition-word", "input B5 result forbidden")
            if tag == "pointer":
                require(value["region"] in self.regions and value["offset"] <= self.regions[value["region"]]["size"], "invalid pointer")
            elif tag == "constant":
                require(value["value"] < 1 << (8 * width(value)), "constant width overflow")
            elif tag == "symbolic":
                self.origin_check(value["origin"])
            elif tag == "bytes":
                require(len(value["bytes"]) == width(value), "byte value width mismatch")
                self.fragments_check(value["bytes"], (value["id"],))
            elif tag == "control":
                require(value["invocation"] in {frame["invocation"] for frame in self.frames.values()}, "invalid control invocation")
                require(value["target"] is None or value["target"] & 1, "control target not Thumb")
        for reference in list(self.context["registers"].values()) + [self.context["sp"], self.context["lr"]]:
            require(reference in self.values and width(self.values[reference]) == 4, "invalid register value reference")
        require(self.values[self.context["sp"]]["tag"] == "pointer" and self.values[self.context["lr"]]["tag"] == "control", "invalid entry SP/control")
        occupied = set()
        for cell in self.context["cells"]:
            location = cell["location"]
            self.interval(location)
            require(len(cell["bytes"]) == location["size"], "cell width mismatch")
            self.fragments_check(cell["bytes"])
            for index, part in enumerate(cell["bytes"]):
                key = self.key(location["region"], location["offset"] + index)
                require(key not in occupied, "overlapping input cells")
                occupied.add(key)
                self.memory[key] = part
                if self.regions[location["region"]]["kind"] == "rom":
                    require(key[0] == "concrete" and ROM_BASE <= key[1] < ROM_BASE + len(self.rom) and
                            part == {"tag": "constant", "value": self.rom[key[1] - ROM_BASE]}, "input cell contradicts ROM bytes", "contradictory-condition")
        for frame in self.frames.values():
            for save in frame["saves"]:
                require(self.read_bytes(save["location"], event=False) == value_bytes(self.values[save["value"]]), "saved bytes disagree", "contradictory-condition")
        identifiers = [condition["id"] for condition in self.conditions]
        require(identifiers == sorted(set(identifiers)), "duplicate or unsorted conditions")
        for condition in self.conditions:
            require(condition["invocation"] == self.context["invocation"], "condition invocation differs")
            scope = "allocator" if condition["id"] in ("B4", "B5") else "initializer" if condition["id"] == "B6" else "registration"
            require(condition["interval"] == {"begin": scope + "-entry", "end": scope + "-return"}, "invalid condition interval")
            self.reference_walk(condition["parameters"])
        require(len(self.conditions) == 8, "required invocation condition missing", "unmet-condition")
        self.params = {condition["id"]: condition["parameters"] for condition in self.conditions}

    def reference_walk(self, item, key=None):
        if type(item) is dict:
            if set(item) == set(SPECS["Slice"]):
                self.interval(item)
            else:
                for child_key, child in item.items():
                    self.reference_walk(child, child_key)
        elif type(item) is list:
            for child in item:
                self.reference_walk(child, key)
        elif key in ("entry_sp", "manager_value", "owner_value", "phase_value", "head_value", "chain", "data_value"):
            require(item in self.values, "dangling condition value reference")

    def key(self, region, offset):
        anchor, address = self.base(region)
        return anchor, address + offset

    def read_bytes(self, location, event=True):
        self.interval(location)
        region = self.regions[location["region"]]
        require(region["lifetime"] == "live", "read from retired allocation", "local-effect")
        result = []
        for index in range(location["size"]):
            offset = location["offset"] + index
            key = self.key(location["region"], offset)
            if key not in self.memory:
                if region["kind"] == "rom":
                    require(key[0] == "concrete" and ROM_BASE <= key[1] < ROM_BASE + len(self.rom), "ROM address outside image")
                    self.memory[key] = {"tag": "constant", "value": self.rom[key[1] - ROM_BASE]}
                else:
                    self.memory[key] = {"tag": "unknown", "origin": {"tag": "memory", "region": location["region"], "offset": offset}}
            result.append(self.memory[key])
        if event:
            self.reads.append({"location": location, "bytes": result})
        return result

    def restrict(self, location, reference):
        expected = value_bytes(self.values[reference])
        require(len(expected) == location["size"], "condition width mismatch", "contradictory-condition")
        actual = self.read_bytes(location, event=False)
        for old, new in zip(actual, expected):
            require(old["tag"] == "unknown" or old == new, "condition contradicts known field bytes", "contradictory-condition")
        for index, part in enumerate(expected):
            self.memory[self.key(location["region"], location["offset"] + index)] = part

    def forbidden(self, reference, protected, active=()):
        require(reference not in active, "cyclic value provenance")
        value = self.values[reference]
        if value["tag"] == "pointer":
            if self.regions[value["region"]]["lifetime"] == "retired":
                return True
            anchor, address = self.key(value["region"], value["offset"])
            return any(anchor == start_anchor and start <= address <= end for start_anchor, start, end in map(self.interval, protected))
        if value["tag"] == "constant":
            return any(anchor == "concrete" and start <= value["value"] <= end for anchor, start, end in map(self.interval, protected))
        if value["tag"] == "bytes":
            return any(part["tag"] == "fragment" and self.forbidden(part["value"], protected, (*active, reference)) for part in value["bytes"])
        return False

    def premises(self):
        first, roles, chain, allocation = (self.params[key] for key in ("B1", "B2", "B3", "B4"))
        self.stack_domain = first["domain"]
        require(self.regions[self.stack_domain["region"]]["kind"] == "stack-domain", "B1 domain is not stack backing", "contradictory-condition")
        require(first["entry_sp"] == self.context["sp"], "B1 SP differs", "contradictory-condition")
        window = first["allocator_window"]
        require(window["low"] < 0 and window["low"] % 4 == 0, "invalid allocator stack window")
        stack_anchor, stack_start, stack_end = self.interval(self.stack_domain)
        entry = self.values[self.context["sp"]]
        entry_anchor, entry_address = self.key(entry["region"], entry["offset"])
        require(entry_anchor == stack_anchor and stack_start <= entry_address <= stack_end and entry_address % 4 == 0, "entry SP outside aligned domain", "contradictory-condition")
        self.entry_stack = entry_address
        self.stack_anchor = stack_anchor
        self.protected = [slc(region["id"], 0, region["size"]) for region in self.regions.values() if region["kind"] == "stack-allocation"]
        for location in self.protected:
            anchor, start, end = self.interval(location)
            require(anchor == stack_anchor and stack_start <= start < end <= stack_end, "inherited stack allocation outside domain", "contradictory-condition")
        for index, left in enumerate(self.protected):
            for right in self.protected[index + 1:]:
                require(not self.overlap(left, right), "live stack allocations overlap", "contradictory-condition")
        for role, size in (("descriptor", 28), ("parameters", 8), ("manager", 16)):
            location = roles[role]
            region = self.regions[location["region"]]
            require(location["size"] == size and region["lifetime"] == "live", "invalid " + role + " role extent/lifetime", "contradictory-condition")
            require(region["kind"] == ("external" if role == "manager" else "stack-allocation"), "wrong " + role + " storage role", "contradictory-condition")
            if role in ("descriptor", "parameters"):
                for reference, value in self.values.items():
                    if value["tag"] == "pointer" and value["region"] == location["region"] and value["offset"] == location["offset"]:
                        self.pointer_limits[reference] = (role, location)
        require(self.regions[roles["manager"]["region"]]["permission"] == "rw", "manager not writable", "contradictory-condition")
        saves = [save["location"] for frame in self.frames.values() for save in frame["saves"]]
        require(roles["protected"] == sorted(saves, key=canonical), "protected save set differs", "contradictory-condition")
        separated = [roles[key] for key in ("descriptor", "parameters", "manager")]
        if roles["parent"] is not None:
            separated.append(roles["parent"])
            require(roles["parent"]["size"] == 20, "invalid parent prefix", "contradictory-condition")
        separated.extend(roles["nodes"])
        separated.extend(saves)
        pairs = []
        for index, left in enumerate(separated):
            for right in separated[index + 1:]:
                require(not self.overlap(left, right), "required role separation contradicted", "contradictory-condition")
                ordered = sorted((left, right), key=canonical)
                pairs.append({"left": ordered[0], "right": ordered[1]})
        require(roles["separation"] == sorted(pairs, key=canonical), "separation witness set differs", "contradictory-condition")
        for location in roles["nodes"] + ([] if roles["parent"] is None else [roles["parent"]]):
            require(self.regions[location["region"]]["kind"] == "external" and self.regions[location["region"]]["permission"] == "rw", "invalid list object", "contradictory-condition")
        require(len(chain["chain"]) == len(set(chain["chain"])), "duplicate chain value identity")
        require(len(chain["chain"]) == len(roles["nodes"]), "chain/node count differs", "contradictory-condition")
        require(len(chain["chain"]) <= 64, "declared chain exceeds 64 nodes", "unsupported")
        require(self.interval(chain["manager_cell"])[1:] == (0x0200F430, 0x0200F434), "wrong manager cell", "contradictory-condition")
        require(chain["manager_value"] == self.context["registers"]["r0"], "incoming manager differs", "contradictory-condition")
        self.require_pointer(chain["manager_value"], roles["manager"])
        self.require_pointer(self.context["registers"]["r3"], roles["descriptor"])
        require(self.values[self.context["registers"]["r1"]] == {"id": self.context["registers"]["r1"], "tag": "function", "body": "callback"}, "incoming callback differs", "contradictory-condition")
        require(self.number(self.context["registers"]["r2"]) == 12, "payload length differs", "contradictory-condition")
        self.restrict(chain["manager_cell"], chain["manager_value"])
        manager = roles["manager"]
        self.restrict(slc(manager["region"], manager["offset"], 4), chain["owner_value"])
        require(not self.forbidden(chain["phase_value"], self.protected), "phase contains borrowed pointer fragment", "contradictory-condition")
        self.restrict(slc(manager["region"], manager["offset"] + 12, 2), chain["phase_value"])
        parent = roles["parent"]
        parent_location = self.resolve_stack(entry_address, 4)
        parent_bytes = self.read_bytes(parent_location, event=False)
        if parent is None:
            require(parent_bytes == [{"tag": "constant", "value": 0}] * 4, "unknown or nonnull parent", "contradictory-condition")
        else:
            self.require_pointer(self.assemble(parent_bytes, 4), parent)
        head_location = slc(parent["region"], parent["offset"] + 16, 4) if parent else slc(manager["region"], manager["offset"] + 4, 4)
        self.restrict(head_location, chain["head_value"])
        require((not chain["chain"] and self.number(chain["head_value"]) == 0) or
                (chain["chain"] and self.equivalent(chain["head_value"], chain["chain"][0])), "head differs from chain", "contradictory-condition")
        for index, reference in enumerate(chain["chain"]):
            node = roles["nodes"][index]
            require(node["size"] == 12, "invalid node prefix", "contradictory-condition")
            self.require_pointer(reference, node)
            next_location = slc(node["region"], node["offset"] + 8, 4)
            if index + 1 < len(chain["chain"]):
                self.restrict(next_location, chain["chain"][index + 1])
            else:
                parts = self.read_bytes(next_location, event=False)
                require(all(part["tag"] == "unknown" or part == {"tag": "constant", "value": 0} for part in parts), "chain does not terminate in null", "contradictory-condition")
                for offset in range(4):
                    self.memory[self.key(next_location["region"], next_location["offset"] + offset)] = {"tag": "constant", "value": 0}
        for key in ("domain", "owner_metadata"):
            location = allocation[key]
            region = self.regions[location["region"]]
            require(region["kind"] == "external" and region["permission"] == "rw", "invalid allocator domain", "contradictory-condition")
            require(not any(self.overlap(location, protected) for protected in self.protected), "allocator domain overlaps inherited stack", "contradictory-condition")
        owner = self.values[chain["owner_value"]]
        require(owner["tag"] == "pointer" and owner["region"] == allocation["owner_metadata"]["region"] and
                allocation["owner_metadata"]["offset"] <= owner["offset"] < allocation["owner_metadata"]["offset"] + allocation["owner_metadata"]["size"], "owner outside metadata", "contradictory-condition")
        parameters = roles["parameters"]
        data = self.params["B7"]
        require(data["source"] == slc(parameters["region"], parameters["offset"] + 4, 4), "data source differs", "contradictory-condition")
        require(not self.forbidden(data["data_value"], self.protected), "data retains a borrowed address or fragment", "contradictory-condition")
        self.restrict(data["source"], data["data_value"])
        image = self.params["B6"]["image"]
        require(image["size"] == 50 and self.regions[image["region"]]["kind"] == "runtime-image", "invalid initializer image", "contradictory-condition")
        for region in self.regions.values():
            if region["permission"] == "rw":
                require(not self.overlap(image, slc(region["id"], 0, region["size"])), "image overlaps writable storage", "contradictory-condition")

    def require_pointer(self, reference, location):
        value = self.values[reference]
        require(value["tag"] == "pointer" and value["region"] == location["region"] and value["offset"] == location["offset"], "role pointer differs", "contradictory-condition")

    def resolve_stack(self, address, size):
        matches = []
        for region in self.regions.values():
            if region["kind"] != "stack-allocation" or region["lifetime"] != "live":
                continue
            anchor, start = self.base(region["id"])
            if anchor == self.stack_anchor and start <= address and address + size <= start + region["size"]:
                matches.append(slc(region["id"], address - start, size))
        if size == 0:
            interior = [location for location in matches if location["offset"] < self.regions[location["region"]]["size"]]
            if interior:
                matches = interior
        require(len(matches) == 1, "stack access lacks a unique live allocation", "local-effect")
        return matches[0]

    def assemble(self, parts, size, extend=False):
        if all(part["tag"] == "constant" for part in parts):
            return self.constant(sum(part["value"] << (8 * index) for index, part in enumerate(parts)), 4 if extend else size)
        if all(part["tag"] == "fragment" and part["value"] == parts[0]["value"] and part["index"] == index for index, part in enumerate(parts)):
            reference = parts[0]["value"]
            if width(self.values[reference]) == size and (not extend or size == 4):
                return reference
        if extend:
            parts = parts + [{"tag": "constant", "value": 0}] * (4 - size)
            size = 4
        return self.make("bytes", width=size, bytes=parts)

    def identities(self):
        require(self.inputs["rom"] == pin(self.rom), "ROM identity differs")
        require(self.inputs["maps"] == {name: pin(data) for name, data in self.maps.items()}, "map identity differs")
        require(self.inputs["engine"] == engine_files(), "engine identity differs")
        mapping = decode(self.maps["functions"])
        require(type(mapping) is list, "function mapping malformed")
        entries = {}
        for row in mapping:
            address = int(row["rom"], 16)
            entries.setdefault(address, []).append(row)
        self.bodies = {body["role"]: body for body in self.inputs["bodies"]}
        require(tuple(sorted(self.bodies)) == ROLES and len(self.inputs["bodies"]) == 7, "body role registry differs")
        self.instructions = {}
        occupied = set()
        expected_entries = {"registration": 0x08005954, "callback": 0x080DFF04, "allocator": 0x08007138,
                            "allocator-child": 0x08006EC0, "initializer": 0x08A38A2C,
                            "initializer-thunk": 0x0814224C, "callback-thunk": 0x08142250}
        for role, body in self.bodies.items():
            start, end = body["start"], body["end"]
            require(start == expected_entries[role] and start < end and not start & 1 and not end & 1, "wrong complete body entry/span")
            require(ROM_BASE <= start < end <= ROM_BASE + len(self.rom), "body outside ROM")
            require(len(entries.get(start, [])) == 1 and entries[start][0]["mode"] == "thumb" and int(entries[start][0]["end"], 16) == end, "body mapping differs")
            require(not any(start < other < end for other in entries), "another indexed entry overlaps body")
            data = self.rom[start - ROM_BASE:end - ROM_BASE]
            require(digest(data) == body["sha256"], "body bytes differ")
            coverage = {}
            for kind in ("code", "literals", "alignment"):
                for span in body[kind]:
                    require(start <= span["start"] < span["end"] <= end, "partition outside envelope")
                    for address in range(span["start"], span["end"]):
                        require(address not in coverage and address not in occupied, "overlapping partition/body")
                        coverage[address] = kind
            require(len(coverage) == end - start, "incomplete body partition")
            reached = {}
            literals = set()
            pending = [start]
            while pending:
                address = pending.pop()
                if address in reached:
                    continue
                require(start <= address < end and address % 2 == 0, "CFG leaves complete body")
                instruction = next(self.decoder.disasm(self.rom[address - ROM_BASE:address - ROM_BASE + 4], address, count=1), None)
                require(instruction is not None and all(coverage.get(byte) == "code" for byte in range(address, address + instruction.size)), "instruction/data ownership differs")
                require(not any(byte in reached for byte in range(address + 1, address + instruction.size)), "overlapping instruction boundary")
                reached[address] = instruction
                mnemonic = instruction.mnemonic
                operands = instruction.operands
                following = address + instruction.size
                if mnemonic == "ldr" and len(operands) == 2 and operands[1].type == ARM_OP_MEM and instruction.reg_name(operands[1].mem.base) == "pc":
                    literal = ((address + 4) & ~3) + operands[1].mem.disp
                    require(literal % 4 == 0 and all(coverage.get(byte) == "literals" for byte in range(literal, literal + 4)), "literal ownership differs")
                    literals.update(range(literal, literal + 4))
                if mnemonic == "bl":
                    require(len(operands) == 1 and operands[0].type == ARM_OP_IMM and len(entries.get(operands[0].imm, [])) == 1 and entries[operands[0].imm][0]["mode"] == "thumb", "direct call target is not unique Thumb entry")
                    pending.append(following)
                elif mnemonic == "bx":
                    require(len(operands) == 1 and operands[0].type == ARM_OP_REG, "invalid indirect transfer")
                elif mnemonic.startswith("b") and operands and operands[0].type == ARM_OP_IMM:
                    pending.append(operands[0].imm)
                    if mnemonic != "b":
                        pending.append(following)
                else:
                    require(not (mnemonic in ("mov", "pop") and any(operand.type == ARM_OP_REG and instruction.reg_name(operand.reg) == "pc" for operand in operands)), "unsupported structural return")
                    pending.append(following)
            code_bytes = {byte for instruction in reached.values() for byte in range(instruction.address, instruction.address + instruction.size)}
            require(code_bytes == {address for address, kind in coverage.items() if kind == "code"}, "unreached declared code")
            require(literals == {address for address, kind in coverage.items() if kind == "literals"}, "unreferenced literal ownership")
            for span in body["alignment"]:
                require(span["end"] - span["start"] == 2 and self.rom[span["start"] - ROM_BASE:span["end"] - ROM_BASE] in (b"\0\0", b"\xc0\x46"), "unsupported alignment bytes")
            self.instructions[role] = reached
            occupied.update(coverage)
        self.bindings = {binding["id"]: binding for binding in self.inputs["bindings"]}
        require(len(self.inputs["bindings"]) == 4 and set(self.bindings) == {"allocator-call", "initializer-call", "callback-call", "initializer-image"}, "binding registry differs")
        expected = {
            "allocator-call": {"tag": "direct", "caller": "registration", "site": 0x08005976, "target": "allocator"},
            "initializer-call": {"tag": "through-thunk", "caller": "registration", "site": 0x08005984, "target": "initializer", "thunk": "initializer-thunk", "register": "r2"},
            "callback-call": {"tag": "through-thunk", "caller": "registration", "site": 0x08005A08, "target": "callback", "thunk": "callback-thunk", "register": "r3"},
            "initializer-image": {"tag": "image", "slot": 0x0836D4B8, "target": 0x03005E79, "source": "initializer", "destination": 0x03005E78, "size": 50},
        }
        for identifier, expected_binding in expected.items():
            require(self.bindings[identifier] == {"id": identifier, **expected_binding}, "binding fields differ")
            if identifier == "initializer-image":
                slot = expected_binding["slot"] - ROM_BASE
                require(int.from_bytes(self.rom[slot:slot + 4], "little") == expected_binding["target"], "initializer table target differs")
                require(self.interval(self.params["B6"]["image"])[1:] == (expected_binding["destination"], expected_binding["destination"] + 50), "B6 image mapping differs", "contradictory-condition")
            else:
                instruction = self.instructions["registration"].get(expected_binding["site"])
                target = self.bodies[expected_binding.get("thunk", expected_binding["target"])]["start"]
                require(instruction is not None and instruction.mnemonic == "bl" and instruction.operands[0].imm == target, "raw call binding differs")
                if "thunk" in expected_binding:
                    thunk = self.instructions[expected_binding["thunk"]]
                    require(len(thunk) == 1, "thunk is not complete BX")
                    branch = next(iter(thunk.values()))
                    require(branch.mnemonic == "bx" and self.regname(branch, branch.operands[0].reg) == expected_binding["register"], "thunk register differs")

    @staticmethod
    def regname(instruction, register):
        return {"sb": "r9", "sl": "r10", "fp": "r11", "ip": "r12"}.get(instruction.reg_name(register), instruction.reg_name(register))

    def event(self, tag, **members):
        self.events.append({"tag": tag, "step": len(self.events), "location": dict(self.location), **members})

    def locate(self, reference, displacement, size):
        value = self.values[reference]
        if value["tag"] == "constant":
            address = value["value"] + displacement
            matches = []
            for region in self.regions.values():
                anchor, start = self.base(region["id"])
                if anchor == "concrete" and start <= address and address + size <= start + region["size"] and region["kind"] != "stack-domain":
                    matches.append(slc(region["id"], address - start, size))
            require(len(matches) == 1, "constant address lacks unique storage role", "unsupported")
            require(address % size == 0, "unaligned memory access", "local-effect")
            return matches[0]
        require(value["tag"] == "pointer", "unclassified memory base", "unsupported")
        region = self.regions[value["region"]]
        if region["kind"] == "stack-domain":
            anchor, address = self.key(value["region"], value["offset"])
            require(anchor == self.stack_anchor, "wrong stack anchor", "local-effect")
            return self.resolve_stack(address + displacement, size)
        offset = value["offset"] + displacement
        require(offset >= 0 and offset + size <= region["size"], "decoded memory access exceeds region", "local-effect")
        if reference in self.pointer_limits:
            role, borrowed = self.pointer_limits[reference]
            require(borrowed["offset"] <= offset and offset + size <= borrowed["offset"] + borrowed["size"], "access exceeds borrowed " + role + " slice", "local-effect")
        require(region["lifetime"] == "live", "decoded access uses retired region", "local-effect")
        require(self.key(value["region"], offset)[1] % size == 0, "unaligned memory access", "local-effect")
        return slc(region["id"], offset, size)

    def load(self, reference, displacement, size):
        return self.assemble(self.read_bytes(self.locate(reference, displacement, size)), size, extend=size != 4)

    def store(self, reference, displacement, size, source):
        location = self.locate(reference, displacement, size)
        region = self.regions[location["region"]]
        require(region["permission"] == "rw", "write to nonwritable region", "local-effect")
        protected = [slc(item["id"], 0, item["size"]) for item in self.regions.values() if item["kind"] == "stack-allocation"]
        if region["kind"] != "stack-allocation":
            require(not self.forbidden(source, protected), "external retention of borrowed pointer/fragment", "local-effect")
        parts = value_bytes(self.values[source])[:size]
        require(len(parts) == size, "store source width insufficient", "local-effect")
        for index, part in enumerate(parts):
            key = self.key(location["region"], location["offset"] + index)
            require(key not in self.saved_at, "write corrupts protected save", "local-effect")
            self.memory[key] = part
        self.writes.append({"location": location, "bytes": parts})
        if region["kind"] != "stack-allocation" and self.values[source]["tag"] != "constant":
            self.retained.append({"location": location, "value": source, "step": len(self.events)})

    def add(self, reference, amount):
        value = self.values[reference]
        if value["tag"] == "pointer":
            if self.regions[value["region"]]["kind"] == "stack-domain":
                anchor, address = self.key(value["region"], value["offset"] + amount)
                require(anchor == self.stack_anchor, "wrong stack anchor", "local-effect")
                location = self.resolve_stack(address, 0)
                result = self.pointer(location["region"], location["offset"])
            else:
                result = self.pointer(value["region"], value["offset"] + amount)
            if reference in self.pointer_limits:
                self.pointer_limits[result] = self.pointer_limits[reference]
            return result
        number = self.number(reference)
        require(number is not None, "arithmetic on unclassified value", "unsupported")
        return self.constant(number + amount)

    def stack_pointer(self, address):
        domain = self.stack_domain["region"]
        anchor, start = self.base(domain)
        require(anchor == self.stack_anchor, "stack domain changed", "local-effect")
        return self.pointer(domain, address - start)

    def allocate_stack(self, frame, size):
        previous = self.stack_address()
        address = previous - size
        anchor, start, end = self.interval(self.stack_domain)
        require(size > 0 and size % 4 == 0 and start <= address < previous <= end, "stack allocation exceeds domain", "local-effect")
        identifier = self.new_id("stack")
        base_anchor, base_start = self.base(self.stack_domain["region"])
        record = {"id": identifier, "base": {"tag": "relative", "region": self.stack_domain["region"], "offset": address - base_start},
                  "size": size, "permission": "rw", "kind": "stack-allocation", "lifetime": "live", "frame": frame["id"]}
        self.regions[identifier] = record
        location = slc(identifier, 0, size)
        for other in self.regions.values():
            if other["id"] != identifier and other["kind"] == "stack-allocation" and other["lifetime"] == "live":
                require(not self.overlap(location, slc(other["id"], 0, other["size"])), "new stack allocation overlaps live storage", "local-effect")
        self.output_regions.append(record)
        frame["allocations"].append(identifier)
        frame["allocations"].sort()
        self.registers["sp"] = self.stack_pointer(address)
        self.event("allocate-stack", region=identifier)
        return identifier

    def stack_address(self):
        value = self.values[self.registers["sp"]]
        require(value["tag"] == "pointer", "SP lost pointer identity", "local-effect")
        anchor, address = self.key(value["region"], value["offset"])
        require(anchor == self.stack_anchor, "SP moved to different backing", "local-effect")
        return address

    def retire(self, frame, size):
        address = self.stack_address()
        end = address + size
        regions = [self.regions[identifier] for identifier in frame["allocations"] if self.regions[identifier]["lifetime"] == "live"]
        retired = []
        covered = set()
        for region in regions:
            anchor, start = self.base(region["id"])
            if address <= start < end:
                require(start + region["size"] <= end, "partial stack allocation retirement", "local-effect")
                covered.update(range(start, start + region["size"]))
                retired.append(region)
        require(covered == set(range(address, end)), "unbalanced stack retirement", "local-effect")
        for region in retired:
            region["lifetime"] = "retired"
            self.event("retire-stack", region=region["id"])
        self.registers["sp"] = self.stack_pointer(end)

    def restorations(self, entry, witnesses):
        result = []
        for register in NONVOLATILE:
            before, after = entry[register], self.registers[register]
            require(self.equivalent(before, after), "nonvolatile identity not restored: " + register, "local-effect")
            result.append({"register": register, "before": before, "after": after, "witness": witnesses.get(register)})
        return result

    def allocator(self, continuation):
        require(self.number(self.registers["r1"]) == 40 and self.equivalent(self.registers["r0"], self.params["B3"]["owner_value"]), "allocator arguments differ", "local-effect")
        low = self.params["B1"]["allocator_window"]["low"]
        address = self.stack_address()
        domain = self.stack_domain["region"]
        anchor, base = self.base(domain)
        window = slc(domain, address + low - base, -low)
        require(window["offset"] >= 0, "allocator stack window outside domain", "contradictory-condition")
        self.interval(window)
        protected = [slc(region["id"], 0, region["size"]) for region in self.regions.values() if region["kind"] == "stack-allocation" and region["lifetime"] == "live"]
        require(not any(self.overlap(window, item) for item in protected), "allocator window overlaps inherited storage", "contradictory-condition")
        self.allocator_prefix(window)
        task_id = self.new_id("task")
        task = {"id": task_id, "base": {"tag": "allocated", "domain": self.params["B4"]["domain"], "clause": "B4"},
                "size": 40, "permission": "rw", "kind": "external", "lifetime": "live", "frame": None}
        require(self.params["B4"]["domain"]["size"] >= 40, "allocator domain too short", "contradictory-condition")
        self.regions[task_id] = task
        self.output_regions.append(task)
        self.task = task_id
        entry = dict(self.registers)
        self.registers["r0"] = self.pointer(task_id)
        excluded = sorted(protected + [window], key=canonical)
        for register in ("r1", "r2", "r3", "r12"):
            self.registers[register] = self.make("condition-word", clause="B5", register=register, excluded=excluded)
        self.registers["lr"] = self.make("symbolic", width=4, origin={"tag": "register", "invocation": self.context["invocation"], "register": "lr"})
        assumption = {"id": self.new_id("assumption"), "tag": "allocator", "status": "assumed", "binding": "allocator-call",
                      "interval": {"begin": "allocator-entry", "end": "allocator-return"}, "clauses": ["B1", "B4", "B5", "B8"],
                      "external_domains": [self.params["B4"]["domain"], self.params["B4"]["owner_metadata"]], "stack_window": window,
                      "task": task_id, "outputs": {register: self.registers[register] for register in REGISTERS}, "lr": self.registers["lr"],
                      "return_control": continuation, "restorations": self.restorations(entry, {}), "subordinate_lifetime": "ended"}
        self.assumed.append(assumption)
        self.event("assumed-allocator", assumption=assumption["id"])

    def allocator_prefix(self, window):
        call_location = dict(self.location)
        self.known_allocator_return(window)
        self.location = call_location
        starts = {"allocator": [0x08007138], "allocator-child": [0x08006EC0, 0x08006EC2, 0x08006EC4, 0x08006EC6]}
        depth = 0
        for role, addresses in starts.items():
            for address in addresses:
                instruction = self.instructions[role].get(address)
                require(instruction is not None, "allocator known prefix absent")
                if instruction.mnemonic == "push":
                    depth += 4 * len(instruction.operands)
                elif instruction.mnemonic == "sub" and self.regname(instruction, instruction.operands[0].reg) == "sp":
                    depth += instruction.operands[1].imm
                elif instruction.mnemonic != "mov":
                    raise Failure("contradictory-condition", "known allocator prefix differs from declared stack footprint")
                require(depth <= window["size"], "known allocator stack prefix exceeds window", "contradictory-condition")
        call = self.instructions["allocator"].get(0x0800715A)
        require(call is not None and call.mnemonic == "bl" and call.operands[0].imm == self.bodies["allocator-child"]["start"], "allocator child identity differs")

    def known_allocator_return(self, window):
        registers = {register: self.registers[register] for register in REGISTERS + ("sp", "lr")}
        entry = dict(registers)
        observed_memory = {}
        protected = [slc(region["id"], 0, region["size"]) for region in self.regions.values() if region["kind"] == "stack-allocation"] + [window]
        roles = self.params["B2"]
        preserved = [slc(region["id"], 0, region["size"]) for region in self.regions.values()
                     if region["lifetime"] == "live" and region["kind"] in ("stack-allocation", "rom", "runtime-image")]
        preserved += [roles["manager"]] + roles["nodes"] + ([] if roles["parent"] is None else [roles["parent"]])
        domains = [self.params["B4"]["domain"], self.params["B4"]["owner_metadata"]]
        containers = {domain["region"] for domain in domains}
        occupied = [slc(region["id"], 0, region["size"]) for region in self.regions.values()
                    if region["lifetime"] == "live" and region["kind"] != "stack-domain" and region["id"] not in containers]
        occupied += preserved + [self.params["B4"]["owner_metadata"], window]

        def overlaps(anchor, start, size, locations):
            return any(anchor == other and max(start, low) < min(start + size, high)
                       for other, low, high in map(self.interval, locations))

        def representation(reference):
            if type(reference) is tuple and reference[0] == "partial":
                return reference[1]
            return tuple((reference, index) for index in range(4))

        def assembled(parts):
            reference = parts[0][0]
            if parts == representation(reference):
                return reference
            number = 0
            for offset, (source, index) in enumerate(parts):
                if type(source) is str and self.values[source]["tag"] == "constant":
                    value = self.values[source]["value"]
                elif type(source) is tuple and source[0] == "constant":
                    value = source[1]
                else:
                    return "partial", parts
                number |= ((value >> (8 * index)) & 255) << (8 * offset)
            return "constant", number

        def observed_byte(key):
            if key in observed_memory:
                return observed_memory[key]
            part = self.memory.get(key)
            if part is not None and part["tag"] == "fragment":
                return part["value"], part["index"]
            if part is not None and part["tag"] == "constant":
                return ("constant", part["value"]), 0
            return None

        def same_byte(left, right):
            if left == right:
                return True
            if right is None:
                return False
            if left[1] == right[1] and type(left[0]) is type(right[0]) is str and self.equivalent(left[0], right[0]):
                return True

            def constant(part):
                source, index = part
                if type(source) is tuple and source[0] == "constant":
                    return (source[1] >> (8 * index)) & 255
                if type(source) is str and self.values[source]["tag"] == "constant":
                    return (self.values[source]["value"] >> (8 * index)) & 255
                return None

            first, second = constant(left), constant(right)
            return first is not None and first == second

        def borrowed(reference):
            if type(reference) is str:
                return self.forbidden(reference, protected)
            if reference[0] == "subordinate":
                return True
            if reference[0] == "partial":
                return any(borrowed(part[0]) for part in reference[1])
            return any(anchor == "concrete" and start <= reference[1] <= end for anchor, start, end in map(self.interval, protected))

        depth = 0
        equal = None
        address = self.bodies["allocator"]["start"]
        for _ in range(64):
            instruction = self.instructions["allocator"].get(address)
            if instruction is None:
                return
            operands = instruction.operands
            names = [self.regname(instruction, operand.reg) if operand.type == ARM_OP_REG else None for operand in operands]
            mnemonic = instruction.mnemonic
            following = address + instruction.size
            self.location = {"invocation": self.context["invocation"], "body": "allocator", "pc": address}
            if mnemonic in ("mov", "movs"):
                registers[names[0]] = (("subordinate", depth) if names[1] == "sp" else registers[names[1]]) if operands[1].type == ARM_OP_REG else ("constant", operands[1].imm)
            elif mnemonic in ("add", "adds") and len(operands) == 3 and operands[2].type == ARM_OP_IMM and operands[2].imm == 0:
                registers[names[0]] = registers[names[1]]
            elif mnemonic == "push":
                depth += 4 * len(names)
                require(depth <= window["size"], "known allocator access exceeds stack window", "contradictory-condition")
                for index, register in enumerate(names):
                    slot = self.stack_address() - depth + 4 * index
                    for offset, part in enumerate(representation(registers[register])):
                        observed_memory[self.stack_anchor, slot + offset] = part
            elif mnemonic == "pop":
                require(depth >= len(names) * 4, "known allocator POP exceeds allocated stack", "contradictory-condition")
                for index, register in enumerate(names):
                    slot = self.stack_address() - depth + 4 * index
                    parts = tuple(observed_byte((self.stack_anchor, slot + offset)) for offset in range(4))
                    if any(part is None for part in parts):
                        return
                    registers[register] = assembled(parts)
                depth -= len(names) * 4
            elif mnemonic in ("sub", "add") and names[0] == "sp" and operands[1].type == ARM_OP_IMM:
                adjustment = operands[1].imm * (1 if mnemonic == "sub" else -1)
                depth += adjustment
                require(0 <= depth <= window["size"], "known allocator temporary access exceeds stack window", "contradictory-condition")
            elif mnemonic == "ldr" and operands[1].type == ARM_OP_MEM and instruction.reg_name(operands[1].mem.base) == "pc":
                literal = ((address + 4) & ~3) + operands[1].mem.disp
                registers[names[0]] = ("constant", int.from_bytes(self.rom[literal - ROM_BASE:literal - ROM_BASE + 4], "little"))
            elif mnemonic == "cmp":
                left = registers[names[0]]
                right = ("constant", operands[1].imm) if operands[1].type == ARM_OP_IMM else registers[names[1]]
                left_number = self.number(left) if type(left) is str else left[1] if left[0] == "constant" else None
                right_number = self.number(right) if type(right) is str else right[1] if right[0] == "constant" else None
                if left_number is None or right_number is None:
                    return
                equal = left_number == right_number
            elif mnemonic in ("b", "beq", "bne"):
                if mnemonic != "b" and equal is None:
                    return
                if mnemonic == "b" or (equal if mnemonic == "beq" else not equal):
                    following = operands[0].imm
            elif mnemonic in ("str", "strh", "strb", "ldr", "ldrh", "ldrb") and operands[1].type == ARM_OP_MEM:
                memory = operands[1].mem
                if memory.index:
                    return
                base_name = self.regname(instruction, memory.base)
                base = ("subordinate", depth) if base_name == "sp" else registers[base_name]
                if type(base) is tuple and base[0] == "subordinate":
                    target_anchor, target_start = self.stack_anchor, self.stack_address() - base[1]
                elif type(base) is str and self.values[base]["tag"] == "pointer":
                    target_anchor, target_start = self.key(self.values[base]["region"], self.values[base]["offset"])
                else:
                    target_start = self.number(base) if type(base) is str else base[1] if base[0] == "constant" else None
                    if target_start is None:
                        return
                    target_anchor = "concrete"
                target_start += memory.disp
                size = 1 if mnemonic.endswith("b") else 2 if mnemonic.endswith("h") else 4
                domains = [self.params["B4"]["domain"], self.params["B4"]["owner_metadata"], window]
                allowed = []
                for domain in domains:
                    anchor, start, end = self.interval(domain)
                    if anchor == target_anchor and start <= target_start and target_start + size <= end:
                        allowed.append(domain)
                operation = "read" if mnemonic.startswith("ldr") else "store"
                require(allowed, "known allocator " + operation + " outside permitted effect domains", "contradictory-condition")
                if operation == "read":
                    parts = tuple(observed_byte((target_anchor, target_start + offset)) for offset in range(size))
                    if any(part is None for part in parts):
                        return
                    parts += tuple((("constant", 0), index) for index in range(size, 4))
                    registers[names[0]] = assembled(parts)
                else:
                    source = registers[names[0]]
                    if window not in allowed:
                        require(not borrowed(source), "known allocator externally retains borrowed/subordinate representation", "contradictory-condition")
                    for offset, part in enumerate(representation(source)[:size]):
                        key = target_anchor, target_start + offset
                        if overlaps(target_anchor, target_start + offset, 1, preserved):
                            require(same_byte(part, observed_byte(key)), "known allocator store changes preserved storage", "contradictory-condition")
                        observed_memory[target_anchor, target_start + offset] = part
            elif mnemonic == "bx":
                require(registers[names[0]] == entry["lr"] and depth == 0, "known allocator return/stack contradicts B4", "contradictory-condition")
                require(all(registers[register] == entry[register] for register in NONVOLATILE), "known allocator corrupts protected register", "contradictory-condition")
                result = registers["r0"]
                require(result != ("constant", 0), "known allocator returns null despite B4", "contradictory-condition")
                require(not (type(result) is tuple and result[0] == "subordinate"), "known allocator returns subordinate object despite B4", "contradictory-condition")
                require(not (type(result) is tuple and result[0] == "partial" and borrowed(result)),
                        "known allocator returns borrowed fragment despite B4", "contradictory-condition")
                require(result not in entry.values(), "known allocator returns existing identity rather than fresh task", "contradictory-condition")
                known_result = None
                if type(result) is str and self.values[result]["tag"] == "pointer":
                    value = self.values[result]
                    known_result = self.key(value["region"], value["offset"])
                else:
                    number = self.number(result) if type(result) is str else result[1] if result[0] == "constant" else None
                    if number is not None:
                        known_result = "concrete", number
                if known_result is not None:
                    result_anchor, result_start = known_result
                    anchor, start, end = self.interval(self.params["B4"]["domain"])
                    require((result_anchor != "concrete" or result_start % 4 == 0) and
                            (anchor != result_anchor or start <= result_start and result_start + 40 <= end),
                            "known allocator result outside fresh aligned domain", "contradictory-condition")
                    require(not overlaps(result_anchor, result_start, 40, occupied),
                            "known allocator result overlaps existing live storage", "contradictory-condition")
                for register in ("r1", "r2", "r3", "r12"):
                    reference = registers[register]
                    require(not (type(reference) is tuple and reference[0] == "subordinate"), "known allocator output retains subordinate object", "contradictory-condition")
                    require(not borrowed(reference), "known allocator output contradicts B5", "contradictory-condition")
                return
            else:
                return
            if mnemonic != "cmp" and instruction.update_flags:
                equal = None
            address = following

    def run_body(self, role, parent_frame, continuation, depth=0):
        require(depth < MAX_DEPTH, "call depth exceeds limit", "unsupported")
        body = self.bodies[role]
        runtime_delta = 0x03005E78 - body["start"] if role == "initializer" else 0
        address = body["start"]
        invocation = self.context["invocation"] if role == "registration" else self.new_id("invocation")
        self.location = {"invocation": invocation, "body": role, "pc": address + runtime_delta}
        frame = {"id": self.new_id("frame"), "invocation": invocation, "parent": parent_frame,
                 "entry_sp": self.registers["sp"], "allocations": [], "saves": []}
        self.frames[frame["id"]] = frame
        self.output_frames.append(frame)
        self.event("frame-enter", frame=frame["id"])
        entry = dict(self.registers)
        identities = {register: register for register in REGISTERS + ("lr", "sp")}
        witnesses = {}
        flags = None
        self.call_path.append(dict(self.location))
        while True:
            self.location = {"invocation": invocation, "body": role, "pc": address + runtime_delta}
            self.steps += 1
            require(self.steps <= MAX_STEPS, "transition budget exceeded", "unsupported")
            instruction = self.instructions[role].get(address)
            require(instruction is not None, "execution outside owned instruction", "local-effect")
            before = dict(self.registers)
            self.reads, self.writes = [], []
            operands = instruction.operands
            mnemonic = instruction.mnemonic
            following = address + instruction.size
            branch = following
            names = [self.regname(instruction, operand.reg) if operand.type == ARM_OP_REG else None for operand in operands]
            call_action = None
            returning = None
            if mnemonic == "push":
                saved_registers = list(names)
                for register in reversed(saved_registers):
                    region_id = self.allocate_stack(frame, 4)
                    location = slc(region_id, 0, 4)
                    source = self.registers[register]
                    parts = value_bytes(self.values[source])
                    identity = identities.get(register, register)
                    witness = self.new_id("save")
                    save = {"witness": witness, "register": identity, "location": location, "value": source}
                    frame["saves"].append(save)
                    for index, part in enumerate(parts):
                        key = self.key(region_id, index)
                        self.memory[key] = part
                        self.saved_at[key] = (witness, source, identity)
                    self.writes.append({"location": location, "bytes": parts})
                self.writes.sort(key=lambda access: self.interval(access["location"])[1])
            elif mnemonic == "pop":
                for register in names:
                    location = self.resolve_stack(self.stack_address(), 4)
                    parts = self.read_bytes(location)
                    saved = [self.saved_at.get(self.key(location["region"], location["offset"] + index)) for index in range(4)]
                    require(saved[0] is not None and all(item == saved[0] for item in saved), "POP lacks exact save witness", "local-effect")
                    witness, original, identity = saved[0]
                    source = self.assemble(parts, 4)
                    require(self.equivalent(source, original), "POP save value changed", "local-effect")
                    self.registers[register] = source
                    identities[register] = identity
                    witnesses[identity] = witness
                    for index in range(4):
                        self.saved_at.pop(self.key(location["region"], location["offset"] + index))
                    self.retire(frame, 4)
            elif mnemonic in ("sub", "add") and names[0] == "sp":
                require(len(operands) == 2 and operands[1].type == ARM_OP_IMM, "dynamic stack adjustment", "unsupported")
                if mnemonic == "sub":
                    self.allocate_stack(frame, operands[1].imm)
                else:
                    self.retire(frame, operands[1].imm)
            elif mnemonic in ("mov", "movs"):
                if operands[1].type == ARM_OP_REG:
                    source = self.registers[names[1]]
                    value = self.values[source]
                    borrowed = names[0] != "sp" and value["tag"] == "pointer" and self.regions[value["region"]]["kind"] == "stack-domain"
                    self.registers[names[0]] = self.add(source, 0) if borrowed else source
                    identities[names[0]] = identities.get(names[1])
                else:
                    self.registers[names[0]] = self.constant(operands[1].imm)
                    identities.pop(names[0], None)
            elif mnemonic in ("adds", "add", "subs", "sub"):
                source_name = names[0] if len(operands) == 2 else names[1]
                amount_operand = operands[-1]
                amount = amount_operand.imm if amount_operand.type == ARM_OP_IMM else self.number(self.registers[names[-1]])
                require(amount is not None, "unknown arithmetic operand", "unsupported")
                source = self.registers[source_name]
                value = self.values[source]
                borrowed = value["tag"] == "pointer" and self.regions[value["region"]]["kind"] == "stack-domain"
                self.registers[names[0]] = source if amount == 0 and not borrowed else self.add(source, -amount if mnemonic.startswith("sub") else amount)
                if amount == 0:
                    identities[names[0]] = identities.get(source_name)
                else:
                    identities.pop(names[0], None)
            elif mnemonic in ("lsls", "lsrs", "asrs"):
                require(len(operands) == 3 and operands[2].type == ARM_OP_IMM, "unsupported shift", "unsupported")
                number = self.number(self.registers[names[1]])
                require(number is not None, "shift of unclassified representation", "unsupported")
                shift = operands[2].imm
                if mnemonic == "lsls":
                    number <<= shift
                else:
                    if mnemonic == "asrs" and number & 0x80000000:
                        number -= 0x100000000
                    number >>= shift
                self.registers[names[0]] = self.constant(number)
                identities.pop(names[0], None)
            elif mnemonic == "ands":
                left, right = (self.registers[name] for name in names)
                first, second = self.number(left), self.number(right)
                if first is not None and second is not None:
                    result = first & second
                elif first == 3 and self.values[right]["tag"] == "pointer" and self.values[right]["region"] == getattr(self, "task", None):
                    result = self.values[right]["offset"] & 3
                else:
                    raise Failure("unsupported", "bitwise operation lacks scalar/alignment proof")
                self.registers[names[0]] = self.constant(result)
                identities.pop(names[0], None)
            elif mnemonic == "cmp":
                left = self.registers[names[0]]
                right = self.constant(operands[1].imm) if operands[1].type == ARM_OP_IMM else self.registers[names[1]]
                first, second = self.number(left), self.number(right)
                if self.values[left]["tag"] == "pointer" and second == 0:
                    flags = {"eq": False, "ne": True}
                elif first is not None and second is not None:
                    signed_first = first - 0x100000000 if first & 0x80000000 else first
                    signed_second = second - 0x100000000 if second & 0x80000000 else second
                    flags = {"eq": first == second, "ne": first != second, "hi": first > second, "ls": first <= second,
                             "hs": first >= second, "lo": first < second, "gt": signed_first > signed_second,
                             "le": signed_first <= signed_second, "ge": signed_first >= signed_second, "lt": signed_first < signed_second}
                else:
                    raise Failure("unsupported", "branch predicate has unclassified value")
            elif mnemonic in ("ldr", "ldrb", "ldrh", "str", "strb", "strh"):
                require(len(operands) == 2 and operands[1].type == ARM_OP_MEM and operands[1].mem.index == 0, "unsupported indexed memory access", "unsupported")
                size = 1 if mnemonic.endswith("b") else 2 if mnemonic.endswith("h") else 4
                memory = operands[1].mem
                base_name = self.regname(instruction, memory.base)
                if base_name == "pc":
                    require(mnemonic == "ldr", "invalid PC store", "local-effect")
                    literal = ((address + 4) & ~3) + memory.disp
                    value = int.from_bytes(self.rom[literal - ROM_BASE:literal - ROM_BASE + 4], "little")
                    self.registers[names[0]] = self.constant(value)
                    protected = [slc(region["id"], 0, region["size"]) for region in self.regions.values() if region["kind"] == "stack-allocation"]
                    require(not self.forbidden(self.registers[names[0]], protected), "literal aliases tracked stack allocation", "local-effect")
                    location = self.locate(self.constant(literal), 0, 4)
                    self.read_bytes(location)
                elif mnemonic.startswith("ldr"):
                    self.registers[names[0]] = self.load(self.registers[base_name], memory.disp, size)
                else:
                    self.store(self.registers[base_name], memory.disp, size, self.registers[names[0]])
                if mnemonic.startswith("ldr"):
                    identities.pop(names[0], None)
            elif mnemonic in ("ldm", "ldmia", "stm", "stmia"):
                encoding = int.from_bytes(instruction.bytes, "little")
                require(instruction.size == 2 and encoding & 0xf000 == 0xc000 and instruction.writeback and names[0] not in names[1:] and len(names) > 1, "unsupported block transfer", "unsupported")
                base = self.registers[names[0]]
                for index, register in enumerate(names[1:]):
                    if mnemonic.startswith("ldm"):
                        self.registers[register] = self.load(base, index * 4, 4)
                        identities.pop(register, None)
                    else:
                        self.store(base, index * 4, 4, self.registers[register])
                self.registers[names[0]] = self.add(base, (len(names) - 1) * 4)
                identities.pop(names[0], None)
            elif mnemonic == "bl":
                binding = next((binding for binding in self.bindings.values() if binding.get("caller") == role and binding.get("site") == address), None)
                require(binding is not None, "reached call has no conditional binding", "unsupported")
                control = self.make("control", invocation=invocation, target=(following + runtime_delta) | 1)
                self.registers["lr"] = control
                call_action = binding, control
            elif mnemonic == "bx":
                returning = self.registers[names[0]]
                require(self.equivalent(returning, continuation), "return control identity differs", "local-effect")
                require(self.stack_address() == self.pointer_address(entry["sp"]), "return SP depth differs", "local-effect")
                require(all(self.regions[reference]["lifetime"] == "retired" for reference in frame["allocations"]), "return leaves live local allocation", "local-effect")
                require(all(identities.get(register) == register for register in NONVOLATILE if register != "sp"),
                        "protected register restoration witness differs", "local-effect")
                self.restorations(entry, witnesses)
                self.check_live_aliases()
                branch = (self.number(returning) or 0) & ~1
            elif mnemonic == "b" or (mnemonic.startswith("b") and operands and operands[0].type == ARM_OP_IMM):
                if mnemonic == "b":
                    branch = operands[0].imm
                else:
                    condition = {"bhs": "hs", "blo": "lo"}.get(mnemonic, mnemonic[1:])
                    require(flags is not None and condition in flags, "unknown branch condition", "unsupported")
                    if flags[condition]:
                        branch = operands[0].imm
            else:
                raise Failure("unsupported", "unsupported reached instruction: " + mnemonic)
            if mnemonic != "cmp" and instruction.update_flags:
                flags = None
            changes = [{"register": register, "before": before[register], "after": self.registers[register]} for register in REGISTERS + ("sp", "lr") if before[register] != self.registers[register]]
            next_pc = branch + runtime_delta if returning is None else branch
            if call_action:
                binding = call_action[0]
                next_pc = self.bodies[binding.get("thunk", binding["target"])]["start"]
            self.event("instruction", encoding=bytes(instruction.bytes).hex(), registers=changes, reads=self.reads, writes=self.writes, next_pc=next_pc)
            if returning is not None:
                self.call_path.pop()
                return returning, self.restorations(entry, witnesses), dict(self.location)
            if call_action:
                binding, control = call_action
                call_location = dict(self.location)
                self.event("call-enter", binding=binding["id"], callee=binding["target"])
                if binding["target"] == "allocator":
                    self.allocator(control)
                else:
                    if binding["target"] == "initializer":
                        require(self.number(self.registers["r2"]) == 0x03005E79 and self.number(self.registers["r1"]) == 40,
                                "initializer target/count differs", "local-effect")
                        self.require_pointer(self.registers["r0"], slc(self.task, 0, 40))
                    else:
                        require(self.values[self.registers["r3"]]["tag"] == "function" and self.values[self.registers["r3"]]["body"] == "callback", "callback target identity differs", "local-effect")
                        self.callback_entry()
                    thunk = next(iter(self.instructions[binding["thunk"]].values()))
                    self.location = {"invocation": invocation, "body": binding["thunk"], "pc": thunk.address}
                    self.event("instruction", encoding=bytes(thunk.bytes).hex(), registers=[], reads=[], writes=[],
                               next_pc=0x03005E78 if binding["target"] == "initializer" else self.bodies["callback"]["start"])
                    self.run_body(binding["target"], frame["id"], control, depth + 1)
                self.location = call_location
                self.event("call-return", binding=binding["id"], callee=binding["target"])
                for register in ("r0", "r1", "r2", "r3", "r12", "lr"):
                    identities.pop(register, None)
                flags = None
            address = following if call_action else branch

    def pointer_address(self, reference):
        value = self.values[reference]
        require(value["tag"] == "pointer", "expected stack pointer", "local-effect")
        return self.key(value["region"], value["offset"])[1]

    def callback_entry(self):
        require(self.values[self.registers["r1"]]["tag"] == "pointer", "callback descriptor lacks pointer", "local-effect")
        descriptor = self.locate(self.registers["r1"], 0, 4)
        descriptor["size"] = 28
        require(self.regions[descriptor["region"]]["frame"] != self.context["frame"], "callback did not receive copied local descriptor", "local-effect")
        copied = self.read_bytes(descriptor, event=False)
        original = self.read_bytes(self.params["B2"]["descriptor"], event=False)
        require(copied[:2] == [{"tag": "constant", "value": 0}] * 2 and copied[2:] == original[2:], "copy/phase obligation differs", "local-effect")
        source = self.params["B2"]["descriptor"]
        transfers = [event for event in self.events if event["tag"] == "instruction" and event["location"]["body"] == "registration"
                     and 0x080059F2 <= event["location"]["pc"] <= 0x080059FC]
        reads = [access["location"] for event in transfers for access in event["reads"]]
        writes = [access["location"] for event in transfers for access in event["writes"]]
        require(reads == [slc(source["region"], source["offset"] + offset, 4) for offset in range(0, 28, 4)] and
                writes == [slc(descriptor["region"], descriptor["offset"] + offset, 4) for offset in range(0, 28, 4)],
                "complete seven-word transfer order not derived", "local-effect")
        parameters = self.assemble(copied[4:8], 4)
        value = self.values[parameters]
        target = self.params["B2"]["parameters"]
        require(value["tag"] == "pointer" and value["region"] == target["region"] and value["offset"] == target["offset"], "copied parameter pointer differs", "local-effect")
        self.require_pointer(self.registers["r2"], slc(self.task, 24, 12))

    def check_live_aliases(self):
        retired = [slc(region["id"], 0, region["size"]) for region in self.regions.values() if region["kind"] == "stack-allocation" and region["lifetime"] == "retired"]
        for register, reference in self.registers.items():
            value = self.values[reference]
            if register == "sp":
                continue
            require(not self.forbidden(reference, retired), "returned register retains retired allocation", "local-effect")
        for region in self.regions.values():
            if region["lifetime"] != "live" or region["kind"] in ("stack-domain", "rom", "runtime-image"):
                continue
            for offset in range(region["size"]):
                part = self.memory.get(self.key(region["id"], offset))
                if part and part["tag"] == "fragment":
                    require(not self.forbidden(part["value"], retired), "live storage retains retired pointer fragment", "local-effect")

    def run(self):
        self.syntax()
        self.premises()
        self.identities()
        self.registers = {**self.context["registers"], "sp": self.context["sp"], "lr": self.context["lr"]}
        target, restorations, site = self.run_body("registration", self.context["frame"], self.context["lr"])
        callback_events = [event for event in self.events if event["tag"] == "instruction" and event["location"]["body"] == "callback"]
        require(len(callback_events) == 23 and not any(len(event["encoding"]) == 8 for event in callback_events), "phase-zero callback trace differs", "local-effect")
        actual_writes = [access for event in callback_events for access in event["writes"] if access["location"]["region"] == self.task]
        require([access["location"] for access in actual_writes] == [slc(self.task, 26, 1), slc(self.task, 28, 4), slc(self.task, 24, 2)], "callback write order differs", "local-effect")
        require(self.read_bytes(slc(self.task, 32, 4), event=False) == [{"tag": "constant", "value": 0}] * 4, "initializer child zero not derived", "local-effect")
        require(self.read_bytes(slc(self.task, 20, 2), event=False) == [{"tag": "constant", "value": 0}, {"tag": "constant", "value": 1}], "registration final phase differs", "local-effect")
        self.require_pointer(self.registers["r0"], slc(self.task, 0, 40))
        self.require_pointer(self.registers["r2"], slc(self.task, 24, 12))
        require(self.equivalent(self.registers["r3"], self.context["registers"]["r8"]), "final POP residue differs", "local-effect")
        allocations = [region for region in self.regions.values() if region["kind"] in ("stack-allocation", "external")]
        live = sorted(region["id"] for region in allocations if region["lifetime"] == "live")
        retired = sorted(region["id"] for region in allocations if region["lifetime"] == "retired")
        result = {"schema": SCHEMA, "policy": POLICY, "operation": OPERATION, "inputs": self.inputs,
                  "conditions": self.conditions, "dependencies": [{"body": role, "sha256": self.bodies[role]["sha256"]} for role in ROLES],
                  "effects": {"values": sorted(self.output_values, key=lambda item: item["id"]), "regions": sorted(self.output_regions, key=lambda item: item["id"]),
                              "frames": sorted(self.output_frames, key=lambda item: item["id"]), "events": self.events, "assumed": self.assumed,
                              "retained": self.retained, "retired": retired, "assumptions_used": ["B" + str(number) for number in range(1, 9)]},
                  "complete-return": {"status": "conditional-complete", "invocation": self.context["invocation"], "site": site,
                                      "target": target, "registers": {register: self.registers[register] for register in REGISTERS},
                                      "sp": self.registers["sp"], "lr": self.registers["lr"], "restorations": restorations, "live": live, "retired": retired}}
        result["fingerprint"] = fingerprint(result)
        validate(result, "Certificate")
        return ConditionalEffects(canonical(result))


def check_registration(evidence, context, conditions):
    checker = None
    try:
        require(type(evidence) is RegistrationEvidence and type(context) is InvocationContext and type(conditions) is InvocationConditions, "wrong private interface type")
        checker = Checker(evidence, context, conditions)
        return checker.run()
    except (Failure, KeyError, TypeError, ValueError, OverflowError) as error:
        category = error.category if isinstance(error, Failure) else "identity"
        result = {"status": "refused", "category": category, "invocation": checker.context.get("invocation") if checker else None,
                  "site": checker.location if checker else None, "path": checker.call_path if checker else [],
                  "reason": failure_reason(error), "diagnostic": checker.events if checker else []}
        return Refusal(canonical(result))


def recheck(encoded, evidence):
    try:
        require(type(evidence) is RegistrationEvidence, "wrong private evidence type")
        record = decode(encoded)
        require(type(encoded) is str and encoded == canonical(record), "noncanonical private encoding")
        validate(record, "Certificate")
        require(record["fingerprint"] == fingerprint(record), "private fingerprint differs")
        require(record["inputs"] == decode(evidence.encoded), "replay trusted inputs differ")
        result = check_registration(evidence, InvocationContext.from_dict(record["inputs"]["context"]), InvocationConditions.from_list(record["conditions"]))
        require(type(result) is ConditionalEffects and result.encoded == canonical(record), "fresh full replay disagrees with supplied result")
        return result
    except (Failure, KeyError, TypeError, ValueError) as error:
        return Refusal(canonical({"status": "refused", "category": "identity", "invocation": None, "site": None, "path": [], "reason": failure_reason(error), "diagnostic": []}))
