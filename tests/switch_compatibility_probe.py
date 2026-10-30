"""Emit deterministic legacy fixture identities for baseline/private comparison."""

import argparse
import hashlib
import json
from pathlib import Path
import sys
import tempfile

sys.path.insert(0, sys.argv[1])
import match
import match_evidence as evidence


ADDRESS = 0x08000000
ADJACENT = """movs r2, #3
cmp r0, #1
bhi .Ldefault
lsls r0, r0, #2
ldr r1, .Lpointer
adds r0, r0, r1
ldr r0, [r0]
mov pc, r0
.balign 4, 0
EXTRA
.Lpointer:
.word .Ltable
.Ltable:
.word .Lcase0
.word .Lcase1
.Lcase0:
adds r0, r2, #1
bx lr
.Lcase1:
adds r0, r2, #2
bx lr
.Ldefault:
movs r0, #0
bx lr
"""
PRELOADED = """ldr r3, .Lobject
movs r2, #0
ldr r1, .Lpointer
.Lcompare:
cmp r2, #1
bhi .Lcompare
lsls r0, r2, #2
adds r0, r0, r1
ldr r0, [r0]
mov pc, r0
.hword 0
.Lobject:
.word g_value
.Lpointer:
.word .Ltable
.Ltable:
.word .Lcase0
.word .Lcase1
.Lcase0:
movs r0, #1
bx lr
.Lcase1:
movs r0, #2
bx lr
"""


def main():
    scratch = Path(sys.argv[2])
    scratch.mkdir(exist_ok=True)
    results = {}
    for kind in ("ordinary", "adjacent", "data", "preloaded"):
        body = "adds r0, #1\nbx lr\n" if kind == "ordinary" else PRELOADED if kind == "preloaded" else ADJACENT
        if kind == "data":
            body = body.replace("movs r2, #3", "ldr r2, .Lobject").replace("EXTRA", ".Lobject:\n.word g_value")
        else:
            body = body.replace("EXTRA", "")
        assembly = (".syntax unified\n.arch armv4t\n.thumb\n.text\n.global func_08000000\n"
                    ".type func_08000000, %function\n.thumb_func\nfunc_08000000:\n" + body +
                    ".size func_08000000, . - func_08000000\n")
        with tempfile.TemporaryDirectory(prefix="legacy_identity_", dir=scratch) as directory:
            root = Path(directory)
            runner = match.Runner(match.DEFAULT_CC, root=root, timeout=120)
            with runner.workspace() as workspace:
                runner.write_text(f"{workspace}/f.s", assembly)
                runner.sh(f"arm-none-eabi-as -mthumb-interwork {workspace}/f.s -o {workspace}/f.o")
                original = match.elf_image(runner.read_binary(f"{workspace}/f.o"))
                size = next(item["size"] for item in original["symbols"] if item["name"] == "func_08000000")
                mapping = json.dumps([{"rom": "0x08000000", "end": f"0x{ADDRESS + size:08X}", "mode": "thumb"}]).encode()
                objects = b'{"g_value":"0x02000000"}' if kind in ("data", "preloaded") else None
                if kind == "ordinary":
                    data = original["text"][:size]
                    instructions = match.verify_leaf_instructions(data, ADDRESS, True)
                    results[kind] = {"schema": evidence.SCHEMA, "body": data.hex(), "count": len(instructions),
                                     "body_sha256": hashlib.sha256(data).hexdigest()}
                    continue
                switches = {}
                args = argparse.Namespace(assembler=match.DEFAULT_AS, linker=match.DEFAULT_LD, objcopy=match.DEFAULT_OBJCOPY)
                data, calls, literals = match.link_calls(runner, workspace, args, original, ADDRESS, mapping,
                    8192, data_mapping=objects, switch_relocations=switches, allow_switch_data=kind != "adjacent",
                    allow_preloaded_switch=kind == "preloaded")
                descriptor = match.selected_switch_layout(data, ADDRESS, switches, literals or None, kind == "preloaded")
                manifest = {"calls": [], "switch": descriptor}
                if objects:
                    manifest["data"] = [[offset, name, 0] for offset, (name, _) in sorted(literals.items())]
                rom = data + bytes(8192 - len(data))
                if kind == "preloaded":
                    match.verify_preloaded_switches(data, ADDRESS, rom, mapping, objects, manifest)
                    schema, fingerprint = evidence.PRELOADED_SWITCH_SCHEMA, evidence.preloaded_switch_fingerprint
                else:
                    match.verify_switches(data, ADDRESS, rom, mapping, manifest, data_mapping=objects)
                    schema = evidence.SWITCH_DATA_SCHEMA if objects else evidence.SWITCH_SCHEMA
                    fingerprint = evidence.switch_data_fingerprint if objects else evidence.switch_fingerprint
                results[kind] = {"schema": schema, "body": data.hex(), "manifest": manifest,
                                 "proof": fingerprint(ADDRESS, data, manifest), "accepted": True}
    print(json.dumps(results, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
