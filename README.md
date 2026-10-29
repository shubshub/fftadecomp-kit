# fftadecomp-kit

Tooling for GBA decompilation, kept separate from any particular ROM.

The ROM analysis, the byte-exact split and the matching harness all live here;
the decompiled source, the extracted data and the findings do not. It started
as the toolkit for [fftadecomp](https://github.com/shubshub/fftadecomp) but
nothing in it is FFTA-specific — point it at any GBA image.

## What is here

| tool | what it does |
|---|---|
| `tools/analyze.py` | header validation, ARM + Thumb recursive-descent discovery with literal-pool resolution, verified prologue scanning, code/data segmentation, coverage report |
| `tools/split.py` | writes the splat-style tree: labelled `asm/`, raw runs in `files/`, `symbols/` |
| `tools/rebuild.py` | concatenates the split and checks it reproduces the base ROM byte for byte (also drives armips) |
| `tools/match.py` | compiles a decompiled function and diffs it against the ROM, instruction by instruction |
| `tools/plausible.py` | rejects source that only exists to make bytes match (inline asm, pragma surgery, dead code, `volatile`, steering padding…) |
| `tools/take.py` | **the official way to reserve an address** - claims it in this repo's ledger, refusing anything already reserved, already matched or in review |
| `tools/reserve.py` | submits address requests to the single ledger issue and waits for authenticated broker confirmation |
| `tools/push.py` | validates decompilation or toolkit changes before pushing |
| `tools/bootstrap.sh` | toolchain setup (Linux/WSL, works without root) |

Requires Python 3 and capstone. Nothing else is needed for analysis and
matching-verification.

## Using it against a decomp repo

Every tool takes the **decomp repo root** as an argument, and defaults to the
current directory, so you can run them from inside a decomp repo:

```sh
python ../fftadecomp-kit/tools/analyze.py baserom.bin   # -> config/, symbols/, logs/
python ../fftadecomp-kit/tools/split.py   baserom.bin   # -> asm/, files/
python ../fftadecomp-kit/tools/rebuild.py .             # must print: byte for byte
python ../fftadecomp-kit/tools/match.py 0x08017514      # compile src/… and diff
```

or set `FFTA_ROOT=/path/to/decomp-repo` and call them with no path.

### Bounded function-inventory diagnostics

Normal analysis produces provisional discovery spans, not complete function
boundaries. Inspect an indexed Thumb entry without regenerating that tree:

```sh
python tools/analyze.py ../fftadecomp/baserom.bin ../fftadecomp \
  --refine-address 0x08123A1C --refine-max-bytes 0x100 \
  --refine-max-instructions 128
```

`--refine-address` is repeatable. Defaults are a 4,096-byte window and 1,024
instructions per entry. The diagnostic reads only bounded ROM windows, stops
at indexed neighboring starts, and prints JSON to stdout; it never writes
maps, symbols, segmentation, coverage or source files.

Results separate reachable instruction ranges, literal words and unresolved
gaps. Direct calls contribute their continuation, not the callee's body.
`cfg_closed` describes structural closure under ordinary-call and syntactic
return assumptions, not stack safety, a complete ELF symbol or exhaustive
discovery. `complete` and `inventory_complete` always remain false.

Unsupported ARM entries, unresolved indirect transfers or switches, ambiguous
boundaries, instruction/literal overlap and exhausted budgets produce explicit
partial reasons. Invalid indexed starts with parseable addresses are reported;
affected entry or neighboring boundaries fail closed. Unparseable addresses
reject the index. Existing provisional end fields are not trusted as function
boundaries.

## Reserving an address before you work on it

Several agents can work on the decomp at once, so **every address has to be
claimed first**, and the claim lives in this repository's single **address
ledger** issue. Each address has its own row in the machine-readable table.

```sh
python tools/take.py list                    # read the board first
python tools/take.py check 0x08011040        # then check the address
python tools/take.py claim 0x08011040 --who me --note "four strh pairs"
python tools/take.py ping 0x08011040
python tools/take.py release 0x08011040 --reason "done, moved to src/"
```

The direct `take.py` path requires issue-edit permission. Read-only contributors
use `reserve.py` for authenticated broker requests instead:

```sh
python tools/reserve.py list
python tools/reserve.py check 0x08011040
python tools/reserve.py claim 0x08011040 --who me --note "four strh pairs"
python tools/reserve.py ping 0x08011040 --who me
python tools/reserve.py release 0x08011040 --who me --reason "done, moved to src/"
```

### The rules

1. **Read the ledger, check the address, then claim it.** Never reserve an
   address already reserved, matched on the decomp default branch, or covered
   by an open decomp PR. Both the client and broker check these conditions;
   coordinate with an existing PR's author rather than duplicating work.
   For broker claims, start only after `claim` prints
   `ACCEPTED` and exits zero. A free `check`, a posted request, or a timeout is
   not a reservation. If another agent holds it, pick another address. Multiple
   addresses can be claimed separately in the same issue; each needs acceptance.
2. **A reservation is a lease, not a land grab.** Ping it while you work.
   Release it as soon as you stop, including when you conclude the function
   **cannot** be matched — that is exactly when somebody else should be allowed
   to try. The `reservations` workflow drains requests and expires rows quiet
   for 3 days; a scheduled run also does this every 6 hours.
3. **Release unmatchable addresses, don't hoard them.** Broker `release
   --unmatchable --reason "..." --tried="-O1..-O3"` requests release and leaves
   the evidence in its comment for maintainer review. It does not write
   `known-unmatchable.json`; an accepted database change still needs review.

Broker clients require authenticated `gh` access to post comments, not permission
to edit another person's issue. The trusted workflow writes accepted requests.
It binds ownership to the comment author's numeric GitHub ID and the original
claim request ID, not the display label. Use distinct `--who` labels for agents
sharing an account, and pass `--claim-id <id>` to `ping` or `release` when the
caller needs to guard a specific claim generation. Without `--who`, those
commands infer the current lane only after checking the authenticated account.

Requests wait up to 120 seconds by default (`--wait`, maximum 300). Exit status
is 0 for confirmed acceptance, 1 for a rejected/taken address, 2 for an
operational error, 3 for a locally recorded unmatchable address, 4 for already
matched source, 5 for an open PR, or 6 for an **UNCONFIRMED** submission or
acknowledgement. On exit 6, inspect the ledger
before retrying; the request may still be processed. Do not start matching.

Broker commands attempt a fast-forward pull first; investigate update warnings rather
than trusting a stale client. `--no-pull` skips this update when the checkout has
already been synchronized. When changing reservation protocols, explicitly pull
and restart all clients: an already loaded old process still contains old code.

### Deploying the reservation broker

The updated `reservations` workflow must be merged into this repository's
default branch and enabled before requests can be accepted. It uses
`issues: write`, `contents: write`, and `pull-requests: read`, checks out the trusted default branch,
and handles request comments on the unique open owner-authored `address ledger`
issue, scheduled expiry, and manual runs through one concurrency group. Ledger
rotation does not require editing a workflow issue number. The legacy
`ffta-address-ledger-50` concurrency key stays constant so old and new jobs
serialize together; it does not select the ledger. Each run drains the durable
comment backlog, so replacement of a pending workflow run does not discard its
requests.

Discovery rejects missing, ambiguous or inaccessible ledgers. An explicit
`FFTA_LEDGER_ISSUE` pin must agree with the discovered canonical ledger; a stale
pin fails before posting a request. No client creates a replacement issue.
The canonical ledger author must be the kit repository owner. Organization-
owned repositories need an explicitly reviewed authority policy before use.

Direct writers, including `take.py`, must not run concurrently with the broker.
Legacy and direct-written rows keep their
visible labels and timestamps, but have no authenticated owner: they cannot
be adopted by matching a label. They remain reserved until normal expiry or
maintainer reconciliation. Manual ledger maintenance must pause all writers;
GitHub issue edits do not provide compare-and-swap protection.

The broker retains 64 recent receipts and at most 256 rows, accepts requests up
to 2 KiB, and limits its rendered issue body to 60,000 UTF-8 bytes. Capacity
errors fail closed without dropping rows. An evicted receipt is unconfirmed,
not success. The visible table and hidden state must agree; edit neither while
the broker is running. This protocol does not grant contributors repository
write access or create separate reservation issues.

Rebase contribution branches onto current `origin/main` before opening a PR;
do not merge main into the contribution branch. See `AGENTS.md` for the rules.

## Publishing through the gate

Use `tools/push.py`, not a separate `git push`. Decompilation mode verifies
history, tracked-file restrictions, fresh ROM matches, plausibility and reports.
Use `--check-only` to run the gate without publishing.

For changes to this toolkit checkout:

```sh
python tools/push.py --kit --repo . --remote fork --branch main --check-only
python tools/push.py --kit --repo . --remote fork --branch main
```

Toolkit mode checks history, forbidden game data and tracked Python tool syntax.
It only accepts the executing toolkit checkout; it cannot be used to skip game
verification in a decompilation repository. Run the affected behavioral checks
as well: syntax validation alone does not establish tool correctness.

Toolkit publication requires a clean working tree and index, including no
nonignored untracked files. Decompilation mode verifies an archive of the
captured commit under the checkout's `build/` directory, so unrelated work can
remain in progress. Archive failure stops the gate rather than falling back to
working files. The gate checks that the branch and commit remain unchanged and
pushes that exact commit. `--working-tree --check-only` validates uncommitted
game edits; publication with `--working-tree` requires a clean checkout too.

The archive uses a copy of the selected local ROM. The gate pins `FFTA_ROM`
to that copy during committed-game checks and restores the previous environment
afterward. A failed ROM selection or copy stops publication; the gate never
substitutes a different ROM.

Use `--force` only for an intentional history rewrite. The gate captures the
remote tip before validation and uses an explicit force-with-lease, so a remote
change during verification rejects the push rather than being overwritten.

## Layout it expects

Commands using automatic ROM selection honor a nonempty `FFTA_ROM` first.
An invalid explicit path fails even if another ROM exists. Without an override,
`baserom.bin` takes precedence; otherwise exactly one existing `.gba` file in
the decompilation root is accepted, with a case-insensitive extension. Multiple
candidates are an error. Optional lookup permits true absence, not ambiguity
or an invalid override.

```
<decomp repo>/
  baserom.bin          the base ROM (gitignored, never committed)
  config/              analysis output: coverage runs, functions, layout json
  symbols/             functions.txt, ffta.sym
  asm/  files/         the split
  src/  include/       decompiled C
  docs/match/          per-function match reports
```

## Cartridge header validation

`analyze.py` checks the 156-byte logo field by SHA-256 without embedding logo
data. The reference digest and complement formula agree with
[devkitPro's `gbafix`](https://github.com/devkitPro/gba-tools/blob/master/src/gbafix.c).
The header complement is the negated sum of bytes `0xA0` through `0xBC`, minus
`0x19`, reduced to one byte. Headers shorter than `0xC0` bytes are rejected.

The baseline FFTA USA header passes both checks: its computed and stored
complement are `0x89`. Earlier reports of a scrambled logo and a computed
`0x85` were analyzer defects, not evidence of ROM damage. Header reports retain
`nintendo_logo_ok` and now include `nintendo_logo_sha256` instead of the invalid
byte-difference count. These checks do not alter the ROM or certify its payload.

Automatic code discovery is bounded to FFTA's main code region below
`0x08150000`. Branch/call traversal and prologue scans do not decode beyond
that boundary, and instructions may not straddle it. Literal data can still
be read elsewhere in the ROM. This is a tool boundary, not an exhaustive
code boundary: installer `0x08002768` references the 176-byte executable image
`[0x08A38A2C,0x08A38ADC)` copied to RAM `0x03005E78`. It contains separate
50-, 60- and 62-byte Thumb bodies plus four alignment bytes. Record bounded,
reference-supported ROM entries without counting their RAM aliases as extra
functions or assuming the RAM image cannot change. Generated function spans
and the below-boundary status denominator remain provisional.

During Thumb traversal, the analyzer also recognizes an adjacent immediate
`cmp` / `bls` guard leading to the five-instruction word-table dispatch
`lsls #2; ldr [pc]; adds; ldr; mov pc`. Registers must agree throughout,
the table must immediately follow its pointer literal, and all entries must
be aligned code-region addresses outside the guard/dispatch/table bytes.
The compare bounds the table to at most 256 entries. Recognized targets seed
provisional discovery; table bytes are not decoded as fallthrough instructions.
`recognized_switch_tables` records the count in layout statistics.

This structural recognition is not a proof that the guard dominates every
runtime path, that a default call never returns, or that each case is a
separate function. It does not relax the matching harness's indirect-control-
flow restrictions or certify complete-function extents. Other switch layouts
remain unresolved; the generated inventory remains explicitly incomplete.

## The matching harness

`match.py` exists because "close" is not good enough in a matching decomp: it
compiles `src/<addr>.c`, assembles, strips, and compares against the ROM bytes,
then prints an aligned diff so you can see *which* instruction the compiler
decided differently.

The comparison covers the named ELF function's entire symbol size, including
literal pools, but excludes assembler alignment padding outside that symbol.
The ELF instruction mode and alignment must agree with the ROM address.
Unresolved relocations are rejected rather than compared as placeholder bytes.
The verifier supports local leaf control flow, including immediate conditional
branches and loops. Every reachable instruction is checked; return-address
provenance and balanced saved-stack depth must agree at joins. Branches cannot
leave the symbol or enter instruction interiors or literal pools, and each
reachable region must have a path to a verified return. This does not prove
termination of arbitrary loops. Interrupts, dynamic stack adjustments and
untracked transfers remain unsupported and fail closed.

Unconditional 16-bit Thumb register moves preserve a proven original return
address, including copies restored to LR. Overwrites discard that fact, joins
retain it only when all incoming paths agree, and calls still invalidate
caller-clobbered registers. Arithmetic, unknown inputs and wider or conditional
moves do not establish return-address provenance.

### Archiving closed reservation receipts

Deploy `tools/reserve.py` and the `reservations` workflow together on the trusted
**default branch**, then let older broker jobs finish. The workflow invokes
`broker --archive-closed` under the existing `ffta-address-ledger-50` concurrency
group. Its scheduled/manual runs work even when the ledger already has 2,500
comments; recovery never requires posting another request. Local client updates
provide no archival or deletion authority. The request and ledger schemas,
capacity limits, duplicate guards, and client exit codes are unchanged.

Only the trusted broker writes the dedicated `ledger-receipts-v1` branch using
the repository Git API. It initializes a separate archive tree when absent;
subsequent commits use exactly the captured parent and a non-forced ref update.
Keep this branch permanently, prohibit force pushes/deletion, and restrict its
writers to the serialized broker and trusted maintainers. Permit the workflow's
`contents: write` access to that branch; it never changes the default branch.
Direct ledger/archive maintenance must pause the same writer first.

`issues/<ledger>/pending.json` journals authenticated accepted claim receipts
across the ledger's 64-result retention window. Every 16 processed requests,
and before/after draining, the broker checkpoints receipts. A complete closed
pair is also preserved in immutable `issues/<ledger>/closed/<claim-id>.json`.
Both receipts must be accepted with code 0 and agree on numeric account ID,
lane, address, original claim ID and operation. Original request bodies remain
verbatim, including claim notes and release reason, tried flags and unmatchable
status. Archival does not approve a Parked attempt, alter the unmatchable
registry, or expand MATCHED-only retirement policies in other tools.

Newly processed requests include an acceptance-time body hash only when the
archived body equals the exact request body applied by this broker run. Legacy
bootstrap requires **both** authoritative accepted receipts still retained.
Those bodies are explicitly labelled `snapshot-at-archive`, retain their
created/updated timestamps, and record the acceptance-time hash as `UNPROVEN`.
This preserves current historical evidence without inventing proof of its
original freeform text. Missing receipts are never reconstructed from comments,
labels, published source or an inferred release. Expired receipts without an
earlier durable capture cannot be archived automatically.

Before deletion the broker confirms the published branch/commit/tree and reads
back every changed blob by its Git identity. It then rechecks the ledger and
both complete comment snapshots immediately before retiring a pair. Active
addresses (including newer claim generations), the current cursor comment,
unconfirmed/rejected requests, foreign owners and mismatched control fields
are excluded. At most 16 pairs are retired per pass. A publication failure,
ref conflict, uncertain readback or edited snapshot authorizes no deletion.
There is no automatic retry of a Git mutation. Partial comment deletion is
recoverable from the already-published complete pair; a later broker run checks
remaining snapshots and removes only still-present members. Completed receipts
remain in Git after the pending index is pruned. GitHub has no atomic multi-
comment delete or lock against comment editing; the final snapshot check and
single trusted writer are required, and an external edit/write must halt the
run rather than be reconciled by overwriting evidence.

Focused offline checks (all GitHub responses are fixtures, with no network or
live ledger writes):
`PYTHONDONTWRITEBYTECODE=1 python -m unittest discover -s tests -p 'test_reservation*.py'`.


### Fixed Thumb stack frames

The framed profiles additionally support 16-bit `sub sp, #N` / `add sp, #N`
and direct aligned word `ldr` / `str` accesses through SP. Allocations are
tracked alongside pushed registers. Deallocation cannot cross entry SP, all
returns must restore entry depth, and control-flow joins require equal depths.
Stores update the affected word's return-address provenance; loading an incoming
argument never establishes a return address. Stores outside the tracked frame
are rejected. Calls invalidate return-address facts in allocated local/outgoing
words, retaining pushed-save facts only under the existing ABI call assumption.

Local-array addresses formed by 16-bit register moves and constant additions
or subtractions are tracked relative to entry SP. Aligned byte, halfword and
word accesses through these aliases must stay inside the allocated/pushed
frame. Partial stores invalidate the affected word's return-address fact.
Register-indexed accesses, including signed byte/halfword loads, additionally
require an exact constant established by a 16-bit immediate move or register
copy. Writes and restoring pops discard constant facts; calls discard them for
caller-clobbered registers, and joins retain only identical constants present
on every incoming path. Unknown or arithmetic-derived indices are rejected.
The same exact constants permit the 16-bit `add Rd, sp, Rd` form for low
registers `r0`–`r7`, producing an alias bounded by the existing frame checks.
High-register destinations, shifted or wider additions, and register-controlled
SP writes are not supported by this extension.
Alias facts must agree exactly at control-flow joins. Pushing or storing these
pointers, unsupported pointer arithmetic, and carrying an
alias across a call in a caller-clobbered register are rejected by these
profiles. The separate buffer-call profile below requires additional ROM
verification for that last case. Callee-saved
aliases survive only under the existing ABI assumption and are cleared when
their registers are restored by a pop.

Canonical 16-bit Thumb `cmp r0-r7, #0` may read an already tracked alias into
a current, definitely allocated local word. Pushed-save slots, entry-SP and
one-past addresses, dangling aliases, other comparison operands and encodings
do not qualify. This changes only the permitted read: alias and return-origin
facts remain intact, and both conditional branch successors are checked without
assuming that SP is nonzero. The separate incoming-buffer alias pass is not
expanded. Existing frame schemas, fingerprints and replay checks are unchanged;
the same instruction-derived rule runs during fresh verification and replay.
The fixed-frame exclusions in division, switch and function-address profiles
still apply.

Register-controlled SP writes and untracked stack-pointer transformations
remain rejected. This is a bounded CFG profile, not a general proof of memory
safety, pointer lifetime, or callee behavior. In particular, the existing normal
frame profile can leave a stack alias in a return register after restoring SP;
null-comparison support does not introduce a new pointer-return policy.

Framed reports use `elf-symbol-thumb-frame-v1` or
`elf-symbol-thumb-frame-calls-v1` and require an explicit stack-summary line.
The linked variant also requires the usual mapping fingerprint and call
summary. Existing unframed schemas remain accepted without report churn.

### Direct Thumb calls

A separate linked profile supports unconditional Thumb `BL` relocations to
external `func_XXXXXXXX` symbols. Each target must resolve to one aligned Thumb
entry in `config/functions.json`, inside the ROM code region and outside the
caller. The profile is selected automatically for eligible call relocations;
the linker defaults to `arm-none-eabi-ld` and can be set with `--linker`.
The matcher creates typed absolute Thumb symbols and links at the
caller's exact ROM address. It checks the linked ELF's mode, address, size,
sections and symbols, verifies each patched call target, and rejects changes
outside the approved relocation fields. The complete linked symbol, including
call instructions and literal pools, must still match the ROM byte for byte.
Relocation bytes are never masked or omitted.

This profile uses an **ABI call summary**, not a closed-leaf proof: a call is
assumed to return normally and preserve the saved stack and callee-saved
registers under the ordinary ARM procedure-call contract. Return-address
provenance in `r0`–`r3`, `r12` and `lr` is invalidated at each call. The verifier
checks the caller's fallthrough paths, joins, saved-stack balance and return
provenance; it does not certify the callee's behavior or whole-program return.

Unmapped data relocations, cross-mode/ARM calls, `BLX`, indirect calls, local
helper functions, self/intra-function calls, tail calls, linker veneers and
extra allocated sections remain unsupported. These cases fail closed rather
than receiving a partial match. Existing relocation-free leaf functions retain
their original verification profile.

### Bounded register buffer calls

The `elf-symbol-thumb-frame-buffer-calls-v1` profile permits a stack alias in
`r0`–`r3` or `r12` at a direct Thumb call only after checking its effects against
the current ROM. The caller and each inspected callee must have a unique,
aligned, complete, non-overlapping Thumb span in `config/functions.json`.
The existing CFG verifier checks each inspected callee's reachable paths,
stack balance and return provenance before an additional alias pass runs.

That pass tracks register copies and immediate additions or subtractions.
Aligned byte, halfword and word accesses must fit entirely within the caller's
currently allocated local words. Pushed save slots, including saved return
addresses, cannot be accessed through a passed buffer. Unknown or indexed
accesses, pointer spills, unrecognized uses, inconsistent alias joins and
pointer-bearing returns fail closed. Buffer pointers cannot be supplied through
stack arguments or LR. Combined buffer calls and named data relocations remain
unsupported.

A nested call receiving an alias in a caller-clobbered register requires the
same proof, even when that register contains only a stale argument. Overwriting
the register before use can discharge that obligation. Recursive buffer calls
and nesting beyond sixteen inspected callees are rejected. Calls with aliases
only in callee-saved registers retain the existing ordinary ABI assumption.
Other calls likewise use ordinary ABI summaries; this does not prove arbitrary
callee behavior, termination, or whole-program memory safety. The bounds are
allocated stack words; they do not infer C object sizes within those words.

Reports bind the source, function mapping and complete caller bytes, and include
a fingerprint of the exact ROM spans inspected by the buffer proof. Report
validation reruns that proof against the local ROM and compares the fingerprint;
it does not trust supplied safe-callee declarations or stored effect claims.
Missing ROM, changed dependencies and invalid proof metadata make these reports
uncountable, including during an otherwise offline status check. Existing
verification schemas retain their original evidence requirements.

### Stack-passed buffer arguments

The separate `elf-symbol-thumb-frame-buffer-calls-v2` profile additionally
tracks aligned, full-word pointer stores to definitely allocated local stack
words. The pointer must also target allocated local storage, never a pushed
save slot. Reloading a pointer-bearing word restores its register alias;
partial reads or writes of that word are rejected. A full scalar-word overwrite
clears the slot's pointer provenance. Deallocating and reallocating storage does
not clear that provenance, and a later call with an uncleared pointer slot
outside the current local frame is rejected.

Every still-live pointer slot is checked at each later call, including stale
arguments. Callee SP-relative loads are interpreted relative to its incoming
SP, accounting for all verified pushes, pops and fixed frame adjustments.
Nested calls receive the same known incoming slots at their shifted offsets;
there is no assumed argument count that hides higher stack slots. Buffer reads
or writes overlapping a pointer-bearing argument word are rejected rather than
silently changing its meaning. Spilling an incoming buffer pointer within an
inspected callee remains unsupported.

Register and slot joins conservatively retain a pointer that is present on
either path. Different possible offsets for the same register or slot remain
unsupported. Inspected callees may return buffer aliases in `r0`–`r3` or `r12`;
the caller receives those possible aliases instead of treating those registers
as pointer-free. Subsequent uses require the same bounds and escape checks.
Aliases in unrestored callee-saved registers, local-frame pointer returns,
control-register aliases and unproven return addresses are rejected.

The matcher tries the existing profiles first. A successful version-2 retry
requires an inspected buffer call and uses its own profile and summary; it does
not broaden version-1 evidence. The complete caller and inspected ROM spans are
bound and replayed as above. The ordinary ABI assumptions still apply, and
combined named data relocations, block transfers, interrupts and indirect-call
dependencies remain unsupported. A proved output-buffer call alone does not
admit a caller whose later stale-argument or local-buffer calls cannot be proved.

### Function literals with bounded buffer calls

The separate `elf-symbol-thumb-function-buffer-calls-v1` profile composes the
exact named Thumb function-address bindings below with the existing bounded
register/stack buffer version-2 proof. It requires both a reachable function
literal and an actually inspected buffer dependency. The matcher preserves
function-address version 1 when its frameless proof succeeds; otherwise this
composition must succeed in full or verification fails, without a legacy
buffer-only fallback. Fixed frames and multiple direct calls are supported;
named object relocations, switches, runtime-thunk bindings and indirect-call
dependencies remain excluded. No buffer bounds, escape or provenance check is
relaxed, and block transfers and incoming-pointer spills remain unsupported.
Every reached direct call in an inspected dependency is checked against the
runtime-thunk exclusion, even if the buffer survives only in a callee-saved
register and no borrowed argument is passed to that call. This restriction is
specific to the combined profile; the legacy buffer profiles are unchanged.

The new report retains both binding and buffer evidence and adds a
domain-separated fingerprint covering the profile versions, source/header
digest, exact function mapping, complete caller bytes, canonical binding
manifest and fingerprint of all complete inspected dependency spans. Replay
reruns both proofs against the selected local ROM, recomputes the dependencies
and checks the captured source, mapping and ROM inputs again before accepting.
Live verification likewise rejects input changes before report/byte emission.
Missing, duplicate, malformed or mixed-profile metadata fails closed. Retained
new-profile fields cannot be relabeled as legacy evidence. Legacy profiles are
unchanged: complete erasure of all new metadata is not authenticated history
and may leave a report independently acceptable under an older proof. This
profile does not claim to prevent that complete-erasure downgrade.

Function literals establish address identity, not callback dispatch, compatible
C function types, callback effects or descriptor lifetime. Uninspected calls
retain the ordinary ABI assumption; inspected buffer effects establish bounded
access and alias flow, not initialized C values or whole-program memory safety.
In particular, a partially initialized descriptor is not fully initialized by
copying its representation. A future callback-word no-clobber proof would
protect only that word: descriptor frames and saved control require separate
byte-range proofs or invalidation of affected facts, with no assumed allocator
or frame separation. Those additional capabilities are not part of this profile.

### Named data literals

For a known external object address, add an explicit mapping to the decomp
checkout's `config/data_symbols.json`, for example:

```json
{"g_tbl": "0x02009000"}
```

Names must be ordinary C identifiers, not function or call-helper names;
addresses must be eight-digit hexadecimal strings. Duplicate keys and malformed
mappings are rejected. The map supplies reviewed addresses, not guessed ones.
Only undefined external object/notype symbols with `R_ARM_ABS32` relocations
qualify. Each relocation must occupy a complete aligned word in the function's
trailing literal pool and be loaded by a reachable PC-relative instruction.
Signed addends are supported without address wrapping; self-function references,
overlapping relocations and unconsumed literal words are rejected.

The linker defines typed absolute objects without allocating their contents.
Each relocated word must equal its address plus addend; no other bytes may
change, and the entire linked function must still equal the ROM. This works
with the existing call and fixed-frame profiles. Data reports use
`elf-symbol-thumb-data-v1` or `elf-symbol-thumb-frame-data-v1` and bind both
function and data mappings, source, headers and the applicable control-flow
summary. Mapping changes invalidate cached evidence and interrupt mixed rebuilds.
These checks establish relocation fidelity, not the safety of dereferencing a
mapped address. No game data should be copied into the symbol map.

### Named Thumb function addresses

The separate `elf-symbol-thumb-function-addresses-v1` profile admits
zero-addend `R_ARM_ABS32` literals referring to canonical `func_XXXXXXXX`
names. The undefined symbol must be global and have function or notype ELF
type, with a zero undefined value and no duplicate named symbol. Its even
address must identify exactly one Thumb entry in `config/functions.json`,
fit inside the ROM, and lie outside the caller. Function names cannot be
laundered through `config/data_symbols.json` or an older proof profile.

The linker defines an absolute Thumb function symbol, not an object. Both
the linked symbol value and the complete literal word must equal the mapped
address with bit zero set. Nonzero addends, weak or local symbols, local
functions, ARM targets, runtime call thunks, veneers and unresolved symbols
are rejected. Each function literal must be an aligned word loaded by reachable
PC-relative code and must not overlap code or another relocation. The existing
full-symbol and linker-modification checks still apply.

Version 1 supports frameless callers with ordinary direct Thumb calls and
optional named object literals. It does not admit fixed stack frames, buffer
proofs, indirect calls or jump tables. Push/pop register saves do not by
themselves constitute a fixed stack frame. Existing leaf, call, data, frame
and buffer schemas retain their existing requirements.

Reports bind source and headers, the function mapping, any used object mapping,
and a canonical manifest of call, object and function-address bindings.
The manifest and complete caller bytes carry a versioned proof fingerprint.
Report validation replays the CFG, exact mapped caller extent, literal loads,
target mappings and literal values against the current local ROM. Missing ROM,
stale inputs, malformed or duplicate metadata and changed proof contents reject
the report. New-profile metadata cannot be attached to an older schema.
Verification also rejects input changes before report or byte emission.

This profile proves relocation fidelity, not callback ABI compatibility,
callback behavior or whole-program memory safety. Callback declarations and
registration contracts still require independent source and ROM review.

### Audited unsigned division runtime

The separate `elf-symbol-thumb-udivsi3-v1` profile accepts natural unsigned
32-bit division compiled to `__udivsi3`. This arithmetic runtime is not an
indirect `_call_via_rN` thunk. Version 1 admits only frameless Thumb callers
with one or more such calls and optional ordinary mapped direct calls.
Fixed frames, buffer proofs, runtime thunks, indirect transfers, switches,
callback literals and named object relocations remain excluded. This profile
does not by itself verify a larger caller combining those features.

The accepted runtime identity is `agbcc-thumb-udivsi3-v1`: the entire 120-byte
Thumb function at `[0x08142AB0, 0x08142B28)` and its complete two-byte `__div0`
dependency at `[0x0814274C, 0x0814274E)`. Their pinned SHA-256 digests are,
respectively,
`b01be100af59274950038e7cfbf7d5a68defe1a607369f88634aeb3c9453e408` and
`abd49ec8111be1f55319f91a44d26daaf5abd7567c169a61abf6c0b031d4b31c`.
The only dependency call is the Thumb BL at runtime offset `0x70`.
Both current ROM bodies and exact, unique, nonoverlapping mapped Thumb spans
are checked on compilation and report replay. Report-supplied hashes cannot
substitute a different implementation.

Local `agbcc/libgcc/lib1thumb.asm` selections `L_udivsi3` and `L_dvmd_tls`,
preprocessed and assembled using that tree's libgcc Makefile recipe, produce
complete ELF function symbols identical to those 120-byte and two-byte ROM
bodies when `__div0` is typed-bound to its Thumb address. This establishes
identity for the audited source variant, not the provenance of an arbitrary
installed libgcc archive. Neither runtime body is copied into the caller.

Each runtime relocation must be a canonical zero-expression `R_ARM_THM_CALL`
against one zero-valued undefined global function/notype symbol named
`__udivsi3`. The linked symbol must be global, absolute, function-typed and
equal to `0x08142AB1`. Noncanonical BL addends, alternate names, addressed
aliases, pointer/object forms, extra text, veneers and unexplained linker
changes reject. The existing full-caller-symbol comparison still applies.

At every division site the existing CFG constant analysis must establish
one concrete nonzero `u32` divisor in `r1` on every incoming path. It preserves
MOV constants and register copies, intersects equal constants at joins and
invalidates caller-clobbered values across calls; it is not range analysis.
Unknown, zero or unequal merged divisors reject. The audited runtime consumes
`r0` and `r1`, returns the unsigned quotient in `r0`, preserves its saved
registers and uses no incoming stack arguments. Its zero-divisor path remains
part of the checked identity but does not make C division by zero defined.

Reports contain a canonical exact-key `calls`, `runtime`, `divisors` manifest.
Every reachable BL is accounted for, with exactly one ordered divisor record
per runtime site. Source/headers, mapping, complete caller bytes, manifest and
schema are bound; replay recomputes the CFG facts and checks the current ROM
identities. Missing, duplicate, stale or recomputed-but-invalid evidence
rejects. Reserved runtime addresses cannot be relabeled as ordinary calls
under old schemas, even after all division metadata is removed; the shared
CFG verifier and buffer/function-address routes enforce that exclusion.
Existing non-runtime schemas, fingerprints and default binding APIs are
unchanged. Runtime binding proves identity and ABI compatibility, not that
an arbitrary source spelled `/`; natural source still requires plausibility
and independent review.

### Audited signed remainder runtime

The separate `elf-symbol-thumb-modsi3-s16-v1` profile accepts natural signed
remainder compiled to `__modsi3`. Every runtime call requires a signed-16-range
dividend in `r0` and a nonzero signed-32 divisor in `r1`. This excludes both
division by zero and the `INT_MIN / -1` overflow pair. Ordinary direct Thumb
calls and PUSH/POP saves are supported; explicit stack frames, stack aliases,
buffer proofs, thunks, switches, function-address relocations and unsigned
runtime mixing remain excluded.

The complete runtime at `[0x08142950,0x08142A1E)` is pinned to SHA-256
`e29c5cee2bafd4fcf3d248a70964d363a3222d67d3eac9031acc95247242fc53`.
Its two-byte zero handler at `[0x0814274C,0x0814274E)` has SHA-256
`abd49ec8111be1f55319f91a44d26daaf5abd7567c169a61abf6c0b031d4b31c`.
The dependency BL and exact, unique, nonoverlapping Thumb mappings are checked.
The caller must also match its entire unique mapped ROM span. A runtime alias
requires a unique undefined global zero-valued function/notype symbol and a
canonical zero-expression Thumb BL relocation; typed linking and complete
symbol comparison remain mandatory.

The operand pass intersects facts at CFG joins and converges across backedges
before checking calls. Thumb16 ASR-immediate 16 establishes the signed range;
MOV/MOVS and ADD/ADDS-zero preserve supported facts. Other writes invalidate
them. An adjacent register-zero CMP and BEQ/BNE establishes nonzero only on
the appropriate edge when the comparison is the branch's sole predecessor.
Coincident branch/fallthrough destinations establish no guard. Calls discard
caller-clobbered facts; callee-saved facts survive only under the ordinary ABI
summary. This proves the restricted operand domain, not arbitrary C
definedness, memory safety or termination.

The canonical manifest contains exactly `runtime`, `calls`, `operands` and
`data`. Replay checks current source/headers, mappings, complete caller and
runtime bytes, rederives the CFG facts, and rejects malformed, duplicate,
missing or rehashed-but-invalid evidence. Signed markers under weaker schemas
are rejected.

Named data is a deliberately conservative subset: every reachable PC-relative
literal valued in `[0x02000000,0x10000000)` needs exactly one mapped-data record.
Both its named base and addend result must be in `[0x02000000,0x04000000)` or
the loaded ROM range; runtime and self references are forbidden. I/O, video,
SRAM and unloaded ROM-mirror values therefore fail, as do address-shaped
scalar constants without an eligible binding. This is a restricted literal
contract, not a claim that integer values recover pointer or original
relocation provenance. Fresh compilation separately verifies actual ELF
relocations. Removing data records and recomputing hashes cannot evade this
subset.

Existing explicit `func_08142950` calls retain machine-helper semantics,
including possible zero divisors, rather than acquiring the C `%` contract.
Only legacy calls-v1/frame-calls-v1 reports reaching that runtime trigger
compiler-backed replay. It captures the fingerprinted source/header tree,
preprocesses and checks dependencies, compiles with default toolchain options,
then verifies canonical addressed relocations, complete linked bytes,
plausibility and frame classification. Original and captured inputs are
rechecked, and recursive replay is rejected. No report-supplied object,
compiler command or source regex establishes provenance.

This compatibility path requires the installed default compiler and binutils
during replay and trusts their normal search environment, as fresh compilation
already does; it is not toolchain attestation. Other legacy reports retain
their existing replay path. A byte-identical `%` replacement cannot become an
addressed-helper report merely by deleting signed metadata. Zero-handler
machine behavior does not make C `% 0` defined.

### Guarded local Thumb switches

The separate `elf-symbol-thumb-switches-v1` profile admits one compiler-emitted
local word table. The selector must be checked by adjacent `cmp; bhi default`
instructions before the dispatch, or by `cmp; bls dispatch; b default`.
The unsigned bound is an immediate from 0 through 255. The dispatch is exactly
the five Thumb instructions that shift that selector left two bits, load the
table address from a PC-relative literal, add the index, load a case address,
and move that address into PC. Register relationships and effective word
alignment are checked. The pointer and table are adjacent to the dispatch,
apart from at most one zero alignment halfword.

The pointer word and every table entry require `R_ARM_ABS32` relocations against
the unique unnamed, local, zero-valued `.text` section symbol. No arbitrary
local-label relocation is accepted. Addends are in-symbol section offsets;
linked words must equal the caller address plus that offset. Case addresses
are **even local Thumb instruction addresses**, not odd external function
pointers. The table has exactly bound-plus-one entries, all targeting
instructions after the table inside the complete caller. Duplicate case
targets are allowed.

The CFG reserves the pointer and table as data before decoding cases. It
derives switch successors internally from the verified bytes and relocation
records, never from a trusted target list. Every case and default must satisfy
the existing return and stack-balance checks. Predecessor checks prohibit
entering the guard without its comparison or bypassing the in-range edge into
any dispatch instruction. Every relocation and dispatch must be reachable.
These checks establish bounded local control flow, not termination.

Version 1 permits ordinary mapped direct Thumb calls under the unchanged ABI
summary, but excludes fixed stack frames, buffer proofs, runtime call thunks
(including addressed aliases), indirect calls, multiple switches, callback
literals and object-address relocations. Register push/pop saves are allowed.
Typed linking still rejects extra sections, veneers, altered function
boundaries and changes outside the validated relocation words. The entire
function, including table words and alignment, must equal the ROM.

Reports bind the source and headers, current function mapping and complete ROM
span to a canonical manifest of calls, guard/dispatch locations, bound and
local relocation offsets/addends. Replay reconstructs the structural proof and
CFG against the current ROM; recomputed hashes do not excuse invalid guards,
targets or predecessor edges. Missing, duplicated or malformed evidence fails.
Switch metadata under an older schema is rejected, and older binding APIs
continue rejecting local section relocations without explicit switch support.
This profile does not establish source plausibility or callee behavior; those
retain their existing independent checks.

The distinct `elf-symbol-thumb-switch-data-v1` profile permits one specific
mixed-data layout: exactly one aligned, explicitly mapped object-address word
follows the five-instruction dispatch and only its required word alignment,
followed by the local table pointer and then its adjacent table. For absolute
dispatch address `D`, the object is exactly `align4(D + 10)`: zero or two
alignment bytes, all zero. The pointer is therefore fourteen or sixteen bytes
after the dispatch start. An extra gap, a nonzero alignment halfword, an extra
object relocation or generalized pool placement is not admitted. The original
switches-v1 profile and default binding APIs retain their object-relocation
exclusion.

The object word must have a unique named undefined global binding and a valid
signed addend, and a reachable aligned PC-relative word load must read it.
The object address cannot point inside the caller. Typed linking validates
the complete object word, local pointer, case entries and ordinary direct
calls; it still rejects changes outside those relocation ranges. The CFG
reserves all relocated words as data before decoding and applies the existing
guard, predecessor, return-provenance and stack-balance checks. Frames, buffer
proofs, runtime thunks, callbacks, indirect calls and multiple switches remain
unsupported.

New-profile reports contain canonical `calls`, `data` and `switch` evidence,
including the object's offset, name and signed addend. A separate versioned
fingerprint binds the address, complete bytes and manifest. Replay requires
current source/header, function-map and object-map fingerprints, reconstructs
the proof and compares the complete mapped span against the current ROM.
The required alignment is derived again from the bound addresses and bytes;
it adds no metadata field and leaves existing descriptors and fingerprints
unchanged. Typed linking cannot change those non-relocated alignment bytes.
Missing, duplicate, malformed, stale or mixed-profile evidence is rejected.
This proves relocation and bounded control-flow fidelity, not object bounds,
source plausibility or downstream helper behavior.

Legacy cached reports now also require complete compiled/ROM byte evidence,
the current matching ROM, and a unique mapped caller instruction mode. Their
existing CFG verifier runs without switch support, using mapped direct-call
targets and ROM-checked runtime thunks where the original profile permits
calls. Buffer profiles retain their existing buffer-proof replay. This prevents
stripping switch metadata and relabeling a computed dispatch as an older
profile. Minimal legacy records without body evidence, missing ROM or ambiguous
mode are intentionally no longer accepted. Existing schema names are unchanged;
complete valid Thumb and ARM reports remain supported. Provisional legacy
mapping extents are not substituted for the complete compiled symbol.

### Preloaded guarded Thumb switches

The distinct `elf-symbol-thumb-preloaded-switch-v1` profile supports one
read-only leaf layout without broadening either adjacent-switch profile.
With `D` denoting the shift instruction, its exact narrow Thumb sequence is:

```text
D-6    ldr  table_base, [pc, #16]
D-4    cmp  selector, #bound
D-2    bhi  D-4
D      lsls accumulator, selector, #2
D+2    adds accumulator, accumulator, table_base
D+4    ldr  accumulator, [accumulator]
D+6    mov  pc, accumulator
D+8    two zero alignment bytes
D+10   one mapped external object word
D+14   local pointer to D+18
D+18   bound-plus-one local case words
```

The three registers must be distinct low registers, `D` must be two modulo
four, and the table must contain 1 through 256 words. Canonical instruction
encodings and decoded operands must agree. Cases are even instruction entries
after the table inside the complete symbol. Exactly one reachable PC-relative
word load reads each of the object and table-pointer words. Every remaining
byte must belong to a reachable 16-bit instruction; additional pools, gaps,
unreachable code and code/data overlap are rejected.

The preload has only its immediate predecessor's ordinary fallthrough edge.
The guard and dispatch instructions cannot be entered midway. Comparison
predecessors are the preload, its backward guard, and any verified direct
unconditional case backedges. The preload must dominate the comparison.
Reverse reachability from the comparison must contain no other write to the
base register, including implicit writes and restores. Terminal restoration
outside that region remains subject to the existing stack/return proof.
Non-stack stores, STM, non-push/pop writeback, calls, local frames, incoming
stack accesses, runtime thunks, callbacks, division and buffer proofs are
excluded. This profile cannot be combined with another switch.

The backward default edge is intentional: an out-of-range selector can loop
forever, and case redirection may also cycle. The existing graph requirement
that each reachable instruction has some path to a verified return does not
prove execution termination. Reports explicitly say `termination not proved`.
No allocation bounds, valid selector domain or pointer lifetime is inferred.

Fresh linking retains the strict raw and linked ELF symbol checks. The local
pointer and table use the unique local zero-valued `.text` section symbol and
`R_ARM_ABS32`; the external object uses one named mapped global object binding
and a checked signed addend. Changes outside validated relocation words,
extra text, helper symbols, veneers and altered boundaries remain rejected.
Binding APIs require both `allow_switch_data=True` for mixed object/local
relocations and `allow_preloaded_switch=True` for this exact layout. Their
defaults and all legacy layouts, schemas and fingerprints remain unchanged.
The normal matcher selects this profile only from its exact encoded shape;
a failed new-profile proof cannot fall back to an older profile.

The canonical manifest has exactly `calls`, `data` and `switch` members,
with an empty call list, one object offset/name/addend, and the byte-derived
descriptor including `preload` and `transfer`. A separate versioned digest
binds the address, complete bytes and manifest. Replay checks current
source/header, function-map and data-map fingerprints, full mapped ROM equality,
byte ownership, CFG and base provenance. Missing, malformed, duplicate, stale,
mixed-profile or recomputed-but-invalid evidence fails. Stripping the new
metadata and relabeling the dispatch as any older profile also fails. Replay
reconstructs byte-derived binding and control-flow facts; it does not recreate
the original ELF symbol-table provenance or recompile the source. Source
plausibility and meaningful original C remain separate requirements.

Reports carry a verification schema and a SHA-256 fingerprint of the source
and headers. `status.py` rejects legacy or stale reports; regenerate them with
`match.py`. Shared preprocessing inputs must live under `include/` or be `.h`
files under `src/`; dependencies outside the fingerprinted set are rejected.
`status.py --verify` recompiles against the local ROM and exits nonzero if any
function fails. `status.py --write --verify` also regenerates the match reports
and validates their fingerprints before counting a successful compilation. This
keeps the written status and subsequent offline checks consistent after shared
header or mapping changes. `--verify` alone and `--check` never rewrite reports;
`--check` takes precedence if combined with `--write`. Offline report checks
replay cached evidence against the local ROM; they do not recompile the source.
The existing function index is provisional and includes truncated or overlapping
spans, so its percentages do not establish whole-function or whole-ROM completion.
Linked-profile reports also bind the exact `config/functions.json` mapping
snapshot. A changed mapping invalidates those cached reports, and mapping
freshness is checked before accepting a match or emitting linked bytes. Leaf
report fingerprints remain unchanged. The mixed rebuild separately checks for
mapping changes across compilation and output verification.
Compilation scratch lives under the decomp repo's ignored `build/` directory
and is removed after success or failure.

### Integrating matched C into the ROM

```sh
python tools/rebuild.py ../fftadecomp --compiled
python tools/rebuild.py ../fftadecomp --compiled --output build/ffta-mixed.gba
```

This freshly compiles and verifies every addressed source, overlays its complete
ELF symbol bytes, and streams unchanged baseline bytes only for uncovered gaps.
It rejects overlapping or out-of-range symbols, failed matches, changed inputs,
and mismatched final bytes. The optional output must be a new file under the
decomp repo's `build/` directory; existing files are never overwritten.

The result is explicitly a **partial mixed C/ROM build**, with separate compiled
and original byte counts. An identical full-ROM SHA-1 proves integration of the
currently matched code, not that the remaining original code is decompiled.
Without `--compiled`, the existing manifest-concatenation check is unchanged.

It also gates on \plausible.py\: byte-identical output from source that looks
like a codegen hack (inline asm, pragma surgery, dead code, \olatile\,
steering padding) is reported **IMPLAUSIBLE**, not a match. Exit status is 0
only when the bytes match *and* the source is plausible.

It handles the compiler stage as `cc -> .s`, so it works with a classic cc1
(GCC 2.9 / agbcc), with modern gcc and with clang:

```sh
python tools/match.py 0x08017514 --flags "-mthumb-interwork -O2"
python tools/match.py 0x08017514 --cc clang \
    --flags "--target=arm-none-eabi -mthumb -O2" \
    --assembler arm-none-eabi-as --objcopy arm-none-eabi-objcopy
```

On Windows with WSL, the whole chain runs inside the distro and the bytes are
read back over (`--wsl Ubuntu`, `--wsl-path` for where the toolchain lives).

Note that some old cc1s (agbcc, GCC 2.9) **do not run the preprocessor** — the
tool runs `cpp -nostdinc -undef -I include` first and hands the result over.

## Notes for people extending the analysis

* `analyze.py` treats `pop {r0}; bx r0` as a return. Capstone does not flag the
  Thumb interworking epilogue, and without that every function using it
  swallows the one after it.
* Verified function starts need a prologue *plus* a walk that reaches a return
  or tail branch. A bare prologue scan matches ~16,000 false positives inside
  4bpp tile data, where the byte pair `0xB5xx` looks like `push {rX, lr}`.
* `rebuild.py` is the gate: if the concatenation does not reproduce the ROM, the
  split is wrong and nothing downstream is safe.
