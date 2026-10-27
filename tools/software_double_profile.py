"""Canonical target-state binary64 conversions, signed conversion, truncation and arithmetic."""

import argparse
from contextvars import ContextVar
import hashlib
import json
from pathlib import Path
import re
import struct
import subprocess
import sys
import tempfile


SCHEMA = "elf-symbol-thumb-df-convert-sub-div-target-v1"
SELECTOR = "convert-sub-div-target-v1"
RUNTIME = "agbcc-thumb-df-convert-add-sub-div-mul-lt-trunc-fix-negdi-fixuns-cmp-negdf-fixunsdi-mod-s16-closure-v9"
ABI = "agbcc-thumb-df-sf-mixed-integer-v2"
SEMANTICS = "target-machine-state-v1"
INERT_SPIN_SCHEMA = "software-double-inert-self-spin-v1"
SUMMARY = ("pinned target binary64 conversion/add/sub/div/mul/lt/trunc, word/wide conversion, signed-wide comparison and integer/double-negation runtime; entry RAM and stack are state inputs; "
           "optional canonical signed remainder requires CFG-proven signed16 dividend and nonzero divisor; "
           "unrestricted IEEE semantics not proved")
OPERATIONS = {"__floatdidf": 0x081428E4, "__floatsidf": 0x0814383C,
              "__subdf3": 0x081430B4, "__divdf3": 0x0814339C,
              "__truncdfsf2": 0x08143980, "__adddf3": 0x08143080,
              "__fixdfsi": 0x081438BC, "__muldf3": 0x081430F0,
              "__ltdf2": 0x0814379C, "__negdi2": 0x08142A94,
              "__fixunsdfsi": 0x08142864, "__cmpdi2": 0x0814435C,
              "__negdf2": 0x08143930, "__fixunsdfdi": 0x0814278C}
# The one runtime owner admitted as authored C must retain this complete
# canonical identity; ordinary runtime owners remain excluded below.
UNSIGNED_WIDE_OWNER = (0x0814278C, 0x08142862, 80,
    "f73dcb3cef4b4139a1a556d79f806d5157e9c5ec9148782cdbb5c8d1194eb436")
IDENTITIES = (
    UNSIGNED_WIDE_OWNER,
    (0x08142864, 0x081428AC, 24,
     "fd5184d8b27f51a2488233b7489aedd3be4912345a47329f6e54feb91c872fd1"),
    (0x081428E4, 0x08142950, 40,
     "a6d6bb1e52f8722074d02e2636c989190539cb12779065909bc2bb61093fe399"),
    (0x08142A20, 0x08142A94, 56,
     "f642a6a21668da428cbb8304f9710064aca75ff16130add649b86ff4b9e73be3"),
    (0x08142A94, 0x08142AAE, 13,
     "6a893c98dc95046692905bc7c4609ee1326b78480597733620dcea235536e4b2"),
    (0x08142BE8, 0x08142D34, 139,
     "38aa6a8e47b81d402a011d733156fc99229f9fdf028aee34f5920b3464a5bb00"),
    (0x08142D34, 0x08142E10, 97,
     "8fb09220b22c69e18dc39f19c8645de020c1d658f48894a5dfe3d68e79f0fb25"),
    (0x08142E10, 0x08143080, 302,
     "22a070699b52b1cb7cf2ab493553e6dab53d87cf3dfe25e3ef10c1968d369537"),
    (0x08143080, 0x081430B4, 22,
     "1b07d08a039cd8e27f726529b9e9456e67856a101882c398cd09d53a8f90a45f"),
    (0x081430B4, 0x081430F0, 26,
     "1d51a3ac118474f7f67a1a4e3654c10efd2c28694da8f9d8e5b50a40e6436bfb"),
    (0x081430F0, 0x0814339C, 323,
     "751f3196c6c084a8d79554ff85b18083f8e0b7e483c36c8dbe2eff90c14bf27d"),
    (0x0814339C, 0x08143528, 188,
     "724ac20cf05719a0fbe4d032862cdc3ba94f1085aa6fbf1d6bc01e598e23adbf"),
    (0x08143528, 0x0814362A, 129,
     "29c2eb0eb1f6a9b824ecfb2bd55d4b006da808992cb6e61f9998057d23c280eb"),
    (0x0814374C, 0x0814379C, 37,
     "decfdbbb0ae65d7944a10157515ae318e66590b609048ecb28c8b3cf604db9fe"),
    (0x0814379C, 0x081437EA, 36,
     "93610c0c0b2e7dd92aba95bfb314fe742a48924abf71d8658d9c01d118af2360"),
    (0x0814383C, 0x081438BC, 56,
     "99b0db82e85f6860b32c8ae93795730b88afaec7134f3ab439db123a7a9f9c0a"),
    (0x081438BC, 0x08143930, 53,
     "327a2c60d3bd9a1ae330269c1ac62adb3632dd975251432fdb36bdacc9e6b2c8"),
    (0x08143930, 0x08143958, 18,
     "98ee9793090fcc62c9eae8bf1730f4299be91132d7ebf5e04ad3febed88a6634"),
    (0x08143980, 0x081439C8, 32,
     "acb4499634230b81e5a935184b68ddda30d9c6eb08041a49ceccab21d05f4223"),
    (0x081439C8, 0x08143A84, 86,
     "765c352080a3d1f6c0da8210a214648596a5486760b3cedf7d6648fef32cae32"),
    (0x08144314, 0x0814432C, 11,
     "1c637e4a2eff2aeb108768d7234baa47f3b4a9cfed810ce28603b3bc29cc5d7f"),
    (0x0814435C, 0x08144378, 14,
     "c50838aadd193e8e629b4854861c6b675502968522e1baa6aa722e884e7a02a0"),
    (0x08144378, 0x081443AE, 27,
     "a2d91a60b907f40dd3bafc448e79c2c4630ba7000195bb54f0f4b26e4e9d9faa"),
)
EDGES = (
    (0x08142798, 0x0814379C),
    (0x081427B8, 0x081430F0),
    (0x081427BC, 0x08142864),
    (0x081427D0, 0x0814435C),
    (0x081427DC, 0x081428E4),
    (0x08142802, 0x081428E4),
    (0x0814280A, 0x08143080),
    (0x08142816, 0x081430B4),
    (0x08142822, 0x0814379C),
    (0x0814282E, 0x08143930),
    (0x08142832, 0x08142864),
    (0x0814284C, 0x08142864),

    (0x0814286E, 0x0814374C),
    (0x0814287A, 0x081438BC),
    (0x08142890, 0x08143080),
    (0x08142894, 0x081438BC),
    (0x0814375C, 0x08142D34),
    (0x08143766, 0x08142D34),
    (0x08143790, 0x08143528),
    (0x0814393C, 0x08142D34),
    (0x0814394E, 0x08142BE8),
    (0x81428EE, 0x814383C),
    (0x81428FA, 0x81430F0),
    (0x8142906, 0x81430F0),
    (0x8142910, 0x814383C),
    (0x8142920, 0x8143080),
    (0x8142930, 0x8143080),
    (0x8142C64, 0x8144378),
    (0x8142F84, 0x8142A94),
    (0x8142FC6, 0x8142A94),
    (0x8143090, 0x8142D34),
    (0x814309A, 0x8142D34),
    (0x81430A4, 0x8142E10),
    (0x81430A8, 0x8142BE8),
    (0x81430C4, 0x8142D34),
    (0x81430CE, 0x8142D34),
    (0x81430E0, 0x8142E10),
    (0x81430E4, 0x8142BE8),
    (0x8143108, 0x8142D34),
    (0x8143112, 0x8142D34),
    (0x81431E0, 0x8142A20),
    (0x81431F0, 0x8142A20),
    (0x8143200, 0x8142A20),
    (0x8143210, 0x8142A20),
    (0x8143376, 0x8142BE8),
    (0x81433AC, 0x8142D34),
    (0x81433B6, 0x8142D34),
    (0x8143512, 0x8142BE8),
    (0x81437AC, 0x8142D34),
    (0x81437B6, 0x8142D34),
    (0x81437DE, 0x8143528),
    (0x81438AC, 0x8142BE8),
    (0x81438C8, 0x8142D34),
    (0x814391A, 0x8144378),
    (0x814398C, 0x8142D34),
    (0x81439B8, 0x8144314),
    (0x8144322, 0x81439C8),
)
# The new conversion reuses the double unpacker and single packer. Only the
# public conversion is a caller operation; the other three bodies stay private.
TRUNCATION_CLOSURE = (0x08142D34, 0x08143980, 0x081439C8, 0x08144314)
# Multiplication receives two binary64 register pairs and returns one pair. Its
# unpacker writes five words only to the caller's real local output record.
# These complete bodies were already pinned private dependencies; exposing the
# canonical compiler entry additionally requires their restoring ABI proof.
MULTIPLICATION_CLOSURE = (0x08142A20, 0x08142BE8, 0x08142D34, 0x081430F0, 0x08144378)
SIGNED_CONVERSION_CLOSURE = (0x08142D34, 0x081438BC, 0x08144378)
ARITHMETIC_COMPARISON_CLOSURE = (
    0x08142A94, 0x08142BE8, 0x08142D34, 0x08142E10, 0x08143080,
    0x081430B4, 0x0814339C, 0x08143528, 0x0814379C, 0x08144378)
# The unsigned word conversion uses a private greater-or-equal entry, the
# already proved signed conversion and addition. Negation uses the pack/unpack
# records. Signed wide comparison is a complete read-only leaf. The wide
# integer-to-double caller also receives its own restoring ABI proof here.
UNSIGNED_CONVERSION_CLOSURE = (
    UNSIGNED_WIDE_OWNER[0],
    0x08142864, 0x081428E4, 0x08142A20, 0x08142A94, 0x08142BE8,
    0x08142D34, 0x08142E10, 0x08143080, 0x081430B4, 0x081430F0,
    0x08143528, 0x0814374C, 0x0814379C, 0x0814383C, 0x081438BC,
    0x08143930, 0x0814435C, 0x08144378)
REPLAY_TIMEOUT = 120
FORBIDDEN_MARKERS = ("* buffer", "* unsigned division", "* signed remainder",
                     "* signed quotient", "* switches", "* switch manifest", "* switch proof",
                     "* function address", "* function buffer", "* inert spin", "* function-address")
_replay_active = ContextVar("software_double_replay_active", default=False)


def reserved(address):
    return any(start <= address & ~1 < end for start, end, _, _ in IDENTITIES)


def shared_float_call(name, target):
    """Only the existing canonical comparison belongs to either isolated profile."""
    return name == "__ltdf2" and target == OPERATIONS[name] == 0x0814379C


def dependency_records():
    return [[start, end, digest] for start, end, _, digest in IDENTITIES]


def marker_text(line):
    return re.sub(r"[ \t]+", " ", line.strip(" \t"))


def selected(report):
    lines = report.splitlines()
    markers = [line for line in lines if marker_text(line).startswith("* verification")]
    relevant = any(SCHEMA in line or marker_text(line).startswith("* software double") for line in lines)
    if not relevant:
        return False
    if markers != [f"* verification: `{SCHEMA}`"] or any(
            marker_text(line).startswith(FORBIDDEN_MARKERS) for line in lines):
        raise ValueError("mixed or malformed software-double profile selection")
    return True


def manifest_text(manifest):
    return json.dumps(manifest, sort_keys=True, separators=(",", ":"))


def compiler_text():
    from match import DEFAULT_CC, DEFAULT_FLAGS
    return f"{DEFAULT_CC} {DEFAULT_FLAGS}"


def index_snapshot(root):
    return (Path(root) / "symbols/functions.txt").read_bytes()


def fingerprint(address, data, manifest, source_digest, mapping, index, rom, *, data_mapping=None):
    from match import DEFAULT_CPP, DEFAULT_AS, DEFAULT_OBJCOPY, DEFAULT_LD
    digest = hashlib.sha256()
    configuration = compiler_text() + repr((DEFAULT_CPP, DEFAULT_AS, DEFAULT_OBJCOPY, DEFAULT_LD))
    for payload in (SCHEMA.encode("ascii"), address.to_bytes(4, "little"), data,
                    manifest_text(manifest).encode("utf-8"), source_digest.encode("ascii"),
                    hashlib.sha256(mapping).digest(), hashlib.sha256(index).digest(),
                    hashlib.sha256(rom).digest(), configuration.encode("ascii")):
        digest.update(len(payload).to_bytes(8, "little"))
        digest.update(payload)
    if "data" in manifest:
        if not isinstance(data_mapping, bytes):
            raise ValueError("software-double data fingerprint requires its exact mapping")
        for payload in (b"software-double-typed-data-v1", data_mapping):
            digest.update(len(payload).to_bytes(8, "little"))
            digest.update(payload)
    return digest.hexdigest()


def fixed_configuration(args):
    from match import DEFAULT_CC, DEFAULT_CPP, DEFAULT_AS, DEFAULT_OBJCOPY, DEFAULT_LD, DEFAULT_FLAGS
    if (args.cc, args.cpp, args.assembler, args.objcopy, args.linker, args.flags) != \
            (DEFAULT_CC, DEFAULT_CPP, DEFAULT_AS, DEFAULT_OBJCOPY, DEFAULT_LD, DEFAULT_FLAGS):
        raise ValueError("software double requires the fixed approved toolchain configuration")


def unique_members(pairs):
    result = {}
    for name, value in pairs:
        if name in result:
            raise ValueError("duplicate software-double JSON member")
        result[name] = value
    return result


def indices(mapping, index):
    if not isinstance(mapping, bytes) or not isinstance(index, bytes):
        raise ValueError("software double requires both index snapshots")
    entries = json.loads(mapping, object_pairs_hook=unique_members)
    if not isinstance(entries, list):
        raise ValueError("software-double mapping must be a list")
    for entry in entries:
        if not isinstance(entry, dict) or not isinstance(entry.get("rom"), str) or \
                not isinstance(entry.get("end"), str) or \
                not re.fullmatch(r"0x[0-9A-Fa-f]{8}", entry["rom"]) or \
                not re.fullmatch(r"0x[0-9A-Fa-f]{8}", entry["end"]) or \
                int(entry["end"], 16) <= int(entry["rom"], 16):
            raise ValueError("malformed software-double function ownership row")
    rows = [line.split() for line in index.decode("utf-8").splitlines()
            if line.strip() and not line.lstrip().startswith("#")]
    for row in rows:
        if len(row) < 4 or not re.fullmatch(r"[0-9A-Fa-f]{8}", row[0]) or \
                not re.fullmatch(r"[0-9A-Fa-f]{8}", row[1]) or \
                int(row[1], 16) <= int(row[0], 16) or int(row[2]) <= 0 or int(row[3]) < 0:
            raise ValueError("malformed software-double text ownership row")
    return entries, rows


def span_record(start, end, entries, rows, rom):
    selected_entries = [entry for entry in entries if int(entry["rom"], 16) & ~1 == start]
    selected_rows = [row for row in rows if int(row[0], 16) & ~1 == start]
    if start % 2 or len(selected_entries) != 1 or len(selected_rows) != 1 or \
            int(selected_entries[0]["rom"], 16) != start or \
            int(selected_entries[0]["end"], 16) != end or selected_entries[0].get("mode") != "thumb" or \
            type(selected_entries[0].get("instrs")) is not int or \
            int(selected_rows[0][0], 16) != start or int(selected_rows[0][1], 16) != end or \
            int(selected_rows[0][2]) != end - start or \
            int(selected_rows[0][3]) != selected_entries[0]["instrs"] or \
            not 0x08000000 <= start < end <= 0x08000000 + len(rom) or \
            any(entry is not selected_entries[0] and int(entry["rom"], 16) < end and
                int(entry["end"], 16) > start for entry in entries) or \
            any(row is not selected_rows[0] and int(row[0], 16) < end and
                int(row[1], 16) > start for row in rows):
        raise ValueError("software double requires exact unique nonoverlapping Thumb spans/counts")
    return selected_entries[0]


def verify_identity(rom, mapping, index):
    if not isinstance(rom, bytes):
        raise ValueError("software double requires a ROM snapshot")
    entries, rows = indices(mapping, index)
    for start, end, count, digest in IDENTITIES:
        entry = span_record(start, end, entries, rows, rom)
        if entry["instrs"] != count or \
                hashlib.sha256(rom[start - 0x08000000:end - 0x08000000]).hexdigest() != digest:
            raise ValueError("software-double complete runtime identity differs")
    for site, target in EDGES:
        first, second = struct.unpack_from("<HH", rom, site - 0x08000000)
        displacement = ((first & 0x7FF) << 12) | ((second & 0x7FF) << 1)
        if displacement & 0x400000:
            displacement -= 0x800000
        if first & 0xF800 != 0xF000 or second & 0xF800 != 0xF800 or site + 4 + displacement != target:
            raise ValueError("software-double dependency edge differs")
    prove_truncation_closure(rom, entries)
    prove_multiplication_closure(rom, entries)
    prove_signed_conversion_closure(rom, entries)
    prove_arithmetic_comparison_closure(rom, entries)
    prove_unsigned_conversion_closure(rom, entries)
    return entries, rows


def prove_truncation_closure(rom, entries):
    """Prove the conversion's complete CFG, bounded writes and restoring ABI.

    Numeric loads remain target-state inputs. The unpacker may write only its
    five-word formal output record; transitive writes must fit each caller's
    real local frame. No unrestricted IEEE conversion semantics are asserted.
    """
    from software_float_profile import prove_runtime
    identities = {start: (end, count) for start, end, count, _ in IDENTITIES
                  if start in TRUNCATION_CLOSURE}
    pending, proofs = set(TRUNCATION_CLOSURE), {}
    while pending:
        ready = [start for start in sorted(pending)
                 if all(target in proofs for site, target in EDGES
                        if start <= site < identities[start][0])]
        if not ready:
            raise ValueError("software-double truncation closure is recursive or incomplete")
        for start in ready:
            end, count = identities[start]
            writes = tuple((1, offset, 4) for offset in range(0, 20, 4)) \
                if start == 0x08142D34 else ()
            proofs[start] = prove_runtime(
                rom, entries, start, end, count, proofs, call_edges=EDGES,
                scalar_entries=(OPERATIONS["__truncdfsf2"],), allowed_writes=writes,
                stack_load_widths=(1, 2, 4))
            pending.remove(start)
    return proofs


def prove_multiplication_closure(rom, entries):
    """Prove every multiplication dependency, frame, bounded write and native return.

    The public entry has no external writes. Unpacked operands and scratch
    records must remain inside its established local frame; no IEEE arithmetic
    model or generic floating-call exception is introduced.
    """
    from software_float_profile import prove_runtime
    identities = {start: (end, count) for start, end, count, _ in IDENTITIES
                  if start in MULTIPLICATION_CLOSURE}
    pending, proofs = set(MULTIPLICATION_CLOSURE), {}
    while pending:
        ready = [start for start in sorted(pending)
                 if all(target in proofs for site, target in EDGES
                        if start <= site < identities[start][0])]
        if not ready:
            raise ValueError("software-double multiplication closure is recursive or incomplete")
        for start in ready:
            end, count = identities[start]
            writes = tuple((1, offset, 4) for offset in range(0, 20, 4)) \
                if start == 0x08142D34 else ()
            proofs[start] = prove_runtime(
                rom, entries, start, end, count, proofs, call_edges=EDGES,
                scalar_entries=(OPERATIONS["__muldf3"],), allowed_writes=writes,
                stack_load_widths=(1, 2, 4),
                stack_store_widths=(1, 2, 4) if start == 0x08142BE8 else (4,))
            pending.remove(start)
    return proofs


def prove_signed_conversion_closure(rom, entries):
    """Prove the pinned double-to-signed-int helper and its private dependencies.

    Runtime numeric loads are machine-state inputs. The unpacker may write
    only its five-word formal result; the public conversion must contain
    those writes in its local frame and restore every native return path.
    """
    from software_float_profile import prove_runtime
    identities = {start: (end, count) for start, end, count, _ in IDENTITIES
                  if start in SIGNED_CONVERSION_CLOSURE}
    pending, proofs = set(SIGNED_CONVERSION_CLOSURE), {}
    while pending:
        ready = [start for start in sorted(pending)
                 if all(target in proofs for site, target in EDGES
                        if start <= site < identities[start][0])]
        if not ready:
            raise ValueError("software-double signed conversion closure is recursive or incomplete")
        for start in ready:
            end, count = identities[start]
            writes = tuple((1, offset, 4) for offset in range(0, 20, 4)) \
                if start == 0x08142D34 else ()
            proofs[start] = prove_runtime(
                rom, entries, start, end, count, proofs, call_edges=EDGES,
                scalar_entries=(OPERATIONS["__fixdfsi"],), allowed_writes=writes,
                stack_load_widths=(1, 2, 4))
            pending.remove(start)
    return proofs


def prove_arithmetic_comparison_closure(rom, entries):
    """Prove the exact native add/sub/div/less-than and integer-negation closure and ABI.

    The unpacker and arithmetic kernel each write five formal output words,
    respectively through R1 and R2. Public binary64 operations must contain
    those writes in their real local frames and restore all saved registers.
    The canonical integer-negation entry consumes and returns the R0/R1 pair.
    Numeric inputs remain target-state values, without an IEEE claim.
    """
    from software_float_profile import prove_runtime
    identities = {start: (end, count) for start, end, count, _ in IDENTITIES
                  if start in ARITHMETIC_COMPARISON_CLOSURE}
    pending, proofs = set(ARITHMETIC_COMPARISON_CLOSURE), {}
    while pending:
        ready = [start for start in sorted(pending)
                 if all(target in proofs for site, target in EDGES
                        if start <= site < identities[start][0])]
        if not ready:
            raise ValueError("software-double arithmetic comparison closure is recursive or incomplete")
        for start in ready:
            end, count = identities[start]
            output = {0x08142D34: 1, 0x08142E10: 2}.get(start)
            writes = () if output is None else tuple((output, n, 4) for n in range(0, 20, 4))
            proofs[start] = prove_runtime(
                rom, entries, start, end, count, proofs, call_edges=EDGES,
                scalar_entries=tuple(OPERATIONS[name] for name in
                                     ("__adddf3", "__subdf3", "__divdf3", "__ltdf2", "__negdi2")),
                allowed_writes=writes, stack_load_widths=(1, 2, 4),
                stack_store_widths=(1, 2, 4) if start == 0x08142BE8 else (4,))
            pending.remove(start)
    return proofs


def prove_unsigned_conversion_closure(rom, entries):
    """Prove the exact unsigned-word conversion, signed comparison and negation.

    Canonical names retain their original ELF provenance. Numeric operands
    remain target-state inputs. Every dependency must have a closed native CFG,
    bounded local/formal writes and restoring register/stack returns; there is
    no opaque-call exception or unrestricted IEEE conversion claim.
    """
    from software_float_profile import prove_runtime
    identities = {start: (end, count) for start, end, count, _ in IDENTITIES
                  if start in UNSIGNED_CONVERSION_CLOSURE}
    pending, proofs = set(UNSIGNED_CONVERSION_CLOSURE), {}
    while pending:
        ready = [start for start in sorted(pending)
                 if all(target in proofs for site, target in EDGES
                        if start <= site < identities[start][0])]
        if not ready:
            raise ValueError("software-double unsigned conversion closure is recursive or incomplete")
        for start in ready:
            end, count = identities[start]
            output = {0x08142D34: 1, 0x08142E10: 2}.get(start)
            writes = () if output is None else tuple((output, n, 4) for n in range(0, 20, 4))
            proofs[start] = prove_runtime(
                rom, entries, start, end, count, proofs, call_edges=EDGES,
                scalar_entries=tuple(OPERATIONS.values()), allowed_writes=writes,
                stack_load_widths=(1, 2, 4),
                stack_store_widths=(1, 2, 4) if start == 0x08142BE8 else (4,))
            pending.remove(start)
    return proofs


def validate_span(data, address, rom, mapping, index):
    entries, rows = verify_identity(rom, mapping, index)
    entry = span_record(address, address + len(data), entries, rows, rom)
    start, end, count, digest = UNSIGNED_WIDE_OWNER
    # The public helper is also authored C. Its exact pinned owner, body and
    # dual-index count are mandatory; fresh fixed-compiler ELF/source replay
    # remains required before any report can credit this reserved owner.
    authored_owner = address == start and address + len(data) == end and \
        entry["instrs"] == count and hashlib.sha256(data).hexdigest() == digest
    if reserved(address) and not authored_owner or not data or len(data) % 2 or \
            data != rom[address - 0x08000000:address - 0x08000000 + len(data)]:
        raise ValueError("software-double complete caller differs from mapped ROM")
    return entries, entry


def call_records(calls, address, bindings):
    return [[site - address, bindings.get(site, f"func_{target:08X}")]
            for site, target in sorted(calls.items())]


def prove_remainder_closure(rom, mapping, index):
    """Re-use the pinned MOD body and prove its exact local scalar ABI."""
    from match import modsi3
    from software_float_profile import prove_runtime
    modsi3.verify_identity(rom, mapping)
    entries, rows = indices(mapping, index)
    for start, end, count in ((modsi3.ADDRESS, 0x08142A1E, 102),
                              (0x0814274C, 0x0814274E, 1)):
        if span_record(start, end, entries, rows, rom)["instrs"] != count:
            raise ValueError("software-double remainder runtime instruction count differs")
    # The exact zero-path MOV PC,LR and MOD MOV PC,LR / POP PC sites reuse
    # the restoring ABI interpreter. Its default BX-only policy is unchanged.
    start = 0x0814274C
    proofs = {start: prove_runtime(
        rom, entries, start, 0x0814274E, 1, {}, call_edges=(),
        scalar_entries=(start,), allowed_writes=(), thumb_pc_returns=(start,))}
    proofs[modsi3.ADDRESS] = prove_runtime(
        rom, entries, modsi3.ADDRESS, 0x08142A1E, 102, proofs,
        call_edges=((0x08142A16, start),), scalar_entries=(modsi3.ADDRESS,), allowed_writes=(),
        thumb_pc_returns=(0x08142A12, 0x08142A1C))
    return proofs


def remainder_record(calls, address, bindings):
    from match import modsi3
    sites = sorted(site - address for site, name in bindings.items() if name == "__modsi3")
    return {"runtime": modsi3.RUNTIME, "dependencies": [list(row) for row in modsi3.IDENTITIES],
            "calls": sites, "dividend": "signed16", "divisor": "nonzero"} if sites else None


def verify_context(data, address, calls, context):
    from match import modsi3
    if not isinstance(context, tuple) or len(context) != 4 or \
            not isinstance(context[3], dict) or not context[3]:
        raise ValueError("software double requires an isolated canonical runtime context")
    rom, mapping, index, bindings = context
    validate_span(data, address, rom, mapping, index)
    operations = dict(OPERATIONS, __modsi3=modsi3.ADDRESS)
    if not any(name in OPERATIONS for name in bindings.values()) or \
            any(type(site) is not int or name not in operations or calls.get(site) != operations[name]
                for site, name in bindings.items()) or \
            set(bindings) != {site for site, target in calls.items()
                              if reserved(target) or modsi3.reserved(target)}:
        raise ValueError("software-double runtime call bindings are incomplete or mixed")
    remainder = {site: name for site, name in bindings.items() if name == "__modsi3"}
    if remainder:
        modsi3.verify_context(data, address, calls, (rom, mapping, remainder))
        prove_remainder_closure(rom, mapping, index)
    return remainder


def verify(data, address, rom, mapping, index, manifest, *, data_mapping=None):
    from match import (function_address_target, uses_stack_frame, verify_leaf_instructions,
                       parse_data_symbols, verify_data_literals, modsi3, ARM_OP_MEM, ARM_REG_PC)
    entries, entry = validate_span(data, address, rom, mapping, index)
    if not isinstance(manifest, dict) or \
            set(manifest) - {"data", "remainder", "inert_spin"} != {"runtime", "abi", "semantics", "dependencies", "frame", "calls"} or \
            manifest["runtime"] != RUNTIME or manifest["abi"] != ABI or manifest["semantics"] != SEMANTICS or \
            type(manifest["dependencies"]) is not list or \
            any(type(record) is not list or len(record) != 3 or \
                type(record[0]) is not int or type(record[1]) is not int or type(record[2]) is not str
                for record in manifest["dependencies"]) or \
            manifest["dependencies"] != dependency_records() or type(manifest["frame"]) is not bool or \
            not isinstance(manifest["calls"], list) or \
            "data" in manifest and (type(manifest["data"]) is not list or not manifest["data"]):
        raise ValueError("invalid software-double manifest")
    calls, bindings = {}, {}
    previous = -4
    for record in manifest["calls"]:
        if not isinstance(record, list) or len(record) != 2:
            raise ValueError("invalid software-double call record")
        offset, name = record
        if type(offset) is not int or not isinstance(name, str) or offset % 2 or \
                offset < previous + 4 or offset < 0 or offset + 4 > len(data):
            raise ValueError("software-double calls must be ordered nonoverlapping instructions")
        if name in OPERATIONS or name == "__modsi3":
            calls[address + offset] = modsi3.ADDRESS if name == "__modsi3" else OPERATIONS[name]
            bindings[address + offset] = name
        else:
            calls[address + offset] = function_address_target(name, entries, address, len(data), len(rom))
        previous = offset
    remainder = remainder_record(calls, address, bindings)
    if ("remainder" in manifest) != (remainder is not None) or \
            remainder is not None and manifest["remainder"] != remainder:
        raise ValueError("software-double signed remainder evidence differs")
    literals, occupied = {}, {byte - address for site in calls for byte in range(site, site + 4)}
    objects = parse_data_symbols(data_mapping) if "data" in manifest else {}
    previous = -1
    for record in manifest.get("data", []):
        if type(record) is not list or len(record) != 3:
            raise ValueError("invalid software-double data binding")
        offset, name, addend = record
        if type(offset) is not int or type(name) is not str or offset <= previous or \
                offset < 0 or offset + 4 > len(data) or (address + offset) % 4 or \
                type(addend) is not int or not -0x80000000 <= addend <= 0x7FFFFFFF or name not in objects:
            raise ValueError("software-double data bindings require ordered aligned mapped words")
        previous = offset
        positions = set(range(offset, offset + 4))
        if occupied & positions:
            raise ValueError("software-double call/data bindings overlap")
        occupied.update(positions)
        value = objects[name] + addend
        parse_data_symbols(json.dumps({name: f"0x{value:08X}"}).encode())
        if not modsi3.supported_data(objects[name], len(rom)) or \
                not modsi3.supported_data(value, len(rom)) or \
                any(int(owner["rom"], 16) <= (pointer & ~1) < int(owner["end"], 16)
                    for owner in entries for pointer in (objects[name], value)) or \
                struct.unpack_from("<I", data, offset)[0] != value:
            raise ValueError("software-double data literal differs or aliases indexed code/forbidden memory")
        literals[offset] = (name, value)
    spin_context = {} if "inert_spin" in manifest else None
    if spin_context is not None:
        record = manifest["inert_spin"]
        if type(record) is not dict or set(record) != {"schema", "spins"} or \
                record["schema"] != INERT_SPIN_SCHEMA or type(record["spins"]) is not list or \
                not record["spins"] or any(type(offset) is not int for offset in record["spins"]):
            raise ValueError("invalid software-double inert-spin evidence")
    instructions = verify_leaf_instructions(data, address, True, calls,
                                            double_context=(rom, mapping, index, bindings),
                                            inert_spin_context=spin_context)
    if spin_context is not None and (not spin_context["spins"] or
            manifest["inert_spin"] != {"schema": INERT_SPIN_SCHEMA, "spins": spin_context["spins"]}):
        raise ValueError("software-double inert-spin evidence differs from the converged CFG")
    if uses_stack_frame(instructions) != manifest["frame"] or len(instructions) != entry["instrs"]:
        raise ValueError("software-double frame/count disagrees with the converged CFG")
    verify_data_literals(instructions, address, literals)
    address_literals = set()
    for instruction in instructions:
        for operand in instruction.operands:
            if instruction.mnemonic == "ldr" and operand.type == ARM_OP_MEM and \
                    operand.mem.base == ARM_REG_PC and not operand.mem.index:
                offset = ((instruction.address + 4) & ~3) + operand.mem.disp - address
                if modsi3.address_literal(struct.unpack_from("<I", data, offset)[0]):
                    address_literals.add(offset)
    if address_literals != set(literals):
        raise ValueError("software-double address-domain literals require exact mapped-data coverage")
    return instructions


def make_manifest(calls, address, bindings, instructions, *, literals=None, data_mapping=None, spins=None):
    from match import uses_stack_frame, parse_data_symbols
    manifest = {"runtime": RUNTIME, "abi": ABI, "semantics": SEMANTICS,
            "dependencies": dependency_records(), "frame": uses_stack_frame(instructions),
            "calls": call_records(calls, address, bindings)}
    remainder = remainder_record(calls, address, bindings)
    if remainder is not None:
        manifest["remainder"] = remainder
    if spins:
        manifest["inert_spin"] = {"schema": INERT_SPIN_SCHEMA, "spins": list(spins)}
    if literals:
        objects = parse_data_symbols(data_mapping)
        manifest["data"] = [[offset, name, value - objects[name]]
                            for offset, (name, value) in sorted(literals.items())]
    return manifest


def object_bytes(runner, workspace, args, original, address, mapping, rom, index, *,
                 data_mapping=None, data_relocations=None):
    from match import (allocated_text_only, function_record, function_address_target,
                       link_calls, parse_data_symbols, modsi3)
    fixed_configuration(args)
    if original["type"] != 1:
        raise ValueError("software double requires a relocatable original ELF")
    allocated_text_only(original)
    symbol, offset = function_record(original, f"func_{address:08X}", address, True)
    definitions = [item for item in original["symbols"] if item["type"] == 2 and item["section"]]
    padding = original["text"][symbol["size"]:]
    if definitions != [symbol] or offset or len(padding) > 3 or \
            any(padding) and not (symbol["size"] % 4 == 2 and padding == b"\xc0\x46") or \
            any(item["type"] == 1 and item["section"] or re.fullmatch(r"\$a(?:\..*)?", item["name"])
                for item in original["symbols"]):
        raise ValueError("software double requires sole-function Thumb text ownership")
    entries, _ = verify_identity(rom, mapping, index)
    if data_relocations is not None and (type(data_relocations) is not dict or data_relocations):
        raise ValueError("software-double data provenance requires an empty collection")
    objects, has_data, has_remainder = None, False, False
    for section_index in original["relocations"]:
        section = original["sections"][section_index]
        if section[1] != 9 or section[7] != original["text_index"] or section[9] != 8 or section[5] % 8:
            raise ValueError("software double requires ordinary Thumb call or mapped data relocations")
        symbols = original["symbol_tables"].get(section[6])
        for position in range(0, section[5], 8):
            _, info = struct.unpack_from("<II", original["section_data"][section_index], position)
            if info & 255 not in (2, 10) or symbols is None or info >> 8 >= len(symbols):
                raise ValueError("software double excludes unsupported relocations")
            target = symbols[info >> 8]
            if info & 255 == 2:
                if data_relocations is None:
                    raise ValueError("software-double data relocation requires explicit provenance capture")
                if objects is None:
                    objects = parse_data_symbols(data_mapping)
                if target["name"] not in objects or target["section"] or target["bind"] != 1 or \
                        target["type"] not in (0, 1) or target["value"] or \
                        sum(item["name"] == target["name"] for item in original["symbols"]) != 1:
                    raise ValueError("software-double data requires one undefined mapped global object")
                has_data = True
                continue
            if target["name"] == "__modsi3":
                has_remainder = True
            elif target["name"] not in OPERATIONS:
                function_address_target(target["name"], entries, address, symbol["size"], len(rom))
            if target["section"] or target["bind"] != 1 or target["type"] not in (0, 2) or \
                    target["value"] or sum(item["name"] == target["name"]
                                           for item in original["symbols"]) != 1:
                raise ValueError("software-double calls require unique undefined global functions")
    if original["relocations"]:
        bindings, remainder_bindings = {}, {}
        data, calls, literals = link_calls(runner, workspace, args, original, address, mapping, len(rom), rom,
                                          data_mapping=data_mapping if has_data else None,
                                          double_bindings=bindings, double_index=index,
                                          modsi3_bindings=remainder_bindings if has_remainder else None,
                                          allow_double_data=has_data)
        if not bindings:
            raise ValueError("software double requires at least one canonical runtime call")
        bindings.update(remainder_bindings)
        if data_relocations is not None:
            data_relocations.update(literals)
        return data, calls, bindings
    if any(item["name"] and not item["section"] for item in original["symbols"]):
        raise ValueError("software-double leaf retains undefined symbols")
    raise ValueError("software double requires at least one canonical runtime call")


def verify_source(root, address, data, rom, mapping, index, source_digest, manifest, *, data_mapping=None):
    from match import (DEFAULT_CC, DEFAULT_CPP, DEFAULT_AS, DEFAULT_OBJCOPY, DEFAULT_LD,
                       DEFAULT_FLAGS, DEFAULT_WSL_PATH, Runner, compile_object,
                       _run_replay_process, plausibility_result)
    from match_evidence import source_paths, source_fingerprint, mapping_snapshot, data_snapshot, report_rom_path
    if _replay_active.get():
        raise ValueError("recursive software-double replay is unsupported")
    token = _replay_active.set(True)
    try:
        root = Path(root)
        candidates = list((root / "src").rglob(f"{address:08X}.c"))
        if len(candidates) != 1 or source_fingerprint(root, address) != source_digest or \
                mapping_snapshot(root) != mapping or index_snapshot(root) != index or \
                "data" in manifest and data_snapshot(root) != data_mapping:
            raise ValueError("software-double replay inputs differ")
        selected_rom = report_rom_path(root)
        if Path(selected_rom).read_bytes() != rom:
            raise ValueError("software-double replay ROM differs")
        validate_span(data, address, rom, mapping, index)
        args = argparse.Namespace(cc=DEFAULT_CC, cpp=DEFAULT_CPP, assembler=DEFAULT_AS,
                                  objcopy=DEFAULT_OBJCOPY, linker=DEFAULT_LD, flags=DEFAULT_FLAGS)
        (root / "build").mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="ffta_double_replay_", dir=root / "build") as directory:
            captured = Path(directory)
            for path in source_paths(root, address):
                destination = captured / path.relative_to(root)
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(path.read_bytes())
            if source_fingerprint(captured, address) != source_digest:
                raise ValueError("software-double source capture differs")
            runner = Runner(DEFAULT_CC, "Ubuntu", DEFAULT_WSL_PATH, root=captured, timeout=REPLAY_TIMEOUT)
            with runner.workspace() as workspace:
                _, _, original = compile_object(runner, workspace, args, captured, address,
                                                 candidates[0].relative_to(root).as_posix())
                literals = {}
                got, calls, bindings = object_bytes(runner, workspace, args, original, address, mapping, rom, index,
                                                    data_mapping=data_mapping, data_relocations=literals)
                instructions = verify(got, address, rom, mapping, index, manifest, data_mapping=data_mapping)
                if got != data or make_manifest(calls, address, bindings, instructions,
                        literals=literals, data_mapping=data_mapping,
                        spins=manifest.get("inert_spin", {}).get("spins")) != manifest:
                    raise ValueError("software-double report lacks fresh original-ELF provenance")
            checker = Path(__file__).resolve().with_name("plausible.py")
            result = _run_replay_process(
                [sys.executable, str(checker), "--quiet", "--addr", f"0x{address:08X}", "--json"] +
                [str(path) for path in source_paths(captured, address)], captured, REPLAY_TIMEOUT)
            findings, allowed = plausibility_result(result, address)
            if findings or allowed or source_fingerprint(captured, address) != source_digest:
                raise ValueError("software-double captured source changed or is implausible")
        if source_fingerprint(root, address) != source_digest or mapping_snapshot(root) != mapping or \
                index_snapshot(root) != index or \
                "data" in manifest and data_snapshot(root) != data_mapping or \
                report_rom_path(root) != selected_rom or \
                Path(selected_rom).read_bytes() != rom:
            raise ValueError("software-double replay inputs changed")
        return instructions
    finally:
        _replay_active.reset(token)


def report_matches(report, root, address):
    from match_evidence import (source_fingerprint, mapping_snapshot, data_snapshot,
                                report_rom_path, STACK_SUMMARY, CALL_SUMMARY)
    lines = report.splitlines()

    def single(prefix):
        marker = prefix.split(":", 1)[0].rstrip()
        matches = [line for line in lines if marker_text(line).split(":", 1)[0].rstrip() == marker]
        if len(matches) != 1 or not matches[0].startswith(prefix):
            raise ValueError("missing, malformed or duplicate software-double evidence")
        return matches[0][len(prefix):]

    def unquote(prefix):
        value = single(prefix)
        if len(value) < 2 or value[0] != "`" or value[-1] != "`":
            raise ValueError("malformed quoted software-double evidence")
        return value[1:-1]

    try:
        if not selected(report):
            return False
        profile_markers = {"* software double", "* software double manifest", "* software double proof SHA-256",
                        "* software double ABI", "* software double runtime", "* software double semantics"}
        if any(marker_text(line).startswith("* software double") and
               line.split(":", 1)[0] not in profile_markers for line in lines):
            return False
        mapping, index = mapping_snapshot(root), index_snapshot(root)
        source_digest = source_fingerprint(root, address)
        if mapping is None or \
                single("* software double: ") != SUMMARY or \
                unquote("* software double ABI: ") != ABI or \
                unquote("* software double runtime: ") != RUNTIME or \
                unquote("* software double semantics: ") != SEMANTICS or \
                unquote("* compiler: ") != compiler_text() or \
                unquote("* source SHA-256: ") != source_digest or \
                unquote("* mapping SHA-256: ") != hashlib.sha256(mapping).hexdigest() or \
                unquote("* function index SHA-256: ") != hashlib.sha256(index).hexdigest() or \
                single("* verified extent: ") != "complete ELF function symbol, including literal pools" or \
                single("* relocations: ") != "none" or single("* source plausibility: ") != "plausible" or \
                single("* hand-asm allow list: ") != "not listed":
            return False
        candidates = list((Path(root) / "src").rglob(f"{address:08X}.c"))
        if len(candidates) != 1 or unquote("* source: ") != candidates[0].relative_to(root).as_posix():
            return False
        encoded = unquote("* compiled : ")
        if re.fullmatch(r"(?:[0-9a-f]{2})+", encoded) is None:
            return False
        data = bytes.fromhex(encoded)
        encoded_manifest = unquote("* software double manifest: ")
        manifest = json.loads(encoded_manifest, object_pairs_hook=unique_members)
        if manifest_text(manifest) != encoded_manifest:
            return False
        from inert_spin_profile import CONTROL_FLOW as SPIN_CONTROL_FLOW
        if single("* control flow: ") != (SPIN_CONTROL_FLOW if "inert_spin" in manifest else CALL_SUMMARY):
            return False
        objects = data_snapshot(root) if "data" in manifest else None
        object_lines = [line for line in lines if marker_text(line).startswith("* data symbols")]
        if object_lines != ([f"* data symbols SHA-256: `{hashlib.sha256(objects).hexdigest()}`"]
                            if manifest.get("data") and objects is not None else []):
            return False
        frames = [line for line in lines if marker_text(line).startswith("* stack frame")]
        if frames != ([f"* stack frame: {STACK_SUMMARY}"] if manifest.get("frame") is True else []):
            return False
        verdicts = [line for line in lines if re.match(
            r"\*\*[ \t]*(?:MATCH|NOT|HAND|IMPLAUSIBLE)\b", marker_text(line))]
        selected_rom = report_rom_path(root)
        rom = Path(selected_rom).read_bytes()
        if unquote("* ROM SHA-256: ") != hashlib.sha256(rom).hexdigest() or \
                single("* ROM bytes: ") != f"`{data.hex()}` ({len(data)} bytes)" or \
                verdicts != [f"**MATCH - byte identical** - {len(data)}/{len(data)} bytes"] or \
                unquote("* software double proof SHA-256: ") != \
                fingerprint(address, data, manifest, source_digest, mapping, index, rom, data_mapping=objects):
            return False
        verify_source(root, address, data, rom, mapping, index, source_digest, manifest, data_mapping=objects)
        return report_rom_path(root) == selected_rom and Path(selected_rom).read_bytes() == rom
    except (OSError, ValueError, KeyError, IndexError, TypeError, AttributeError, OverflowError,
            RecursionError, RuntimeError, subprocess.SubprocessError):
        return False
