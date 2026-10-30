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

The default diagnostic ceiling remains `0x08150000`. Explicitly add
`--refine-full-rom-inventory` to inspect late provisional indexed entries in
`[0x080000C0, min(actual_ROM_end, 0x09000000))`. Mirrors and RAM aliases remain
excluded. This opt-in changes only diagnostic address bounds; index validation,
neighbor boundaries, byte/instruction budgets and partial reasons still apply.
It grants no actual-function, ABI, match or exhaustive-inventory proof and does
not change matching, status or reservation gates. `complete` and
`inventory_complete` remain false even when a late entry has `cfg_closed: true`.

Results separate reachable instruction ranges, literal words and unresolved
gaps. Direct calls contribute their continuation, not the callee's body.
`literal_reads` records each reached PC-relative word read by `site`, `address`,
`size` and `inside_window`, sorted by instruction address. Repeated reads of one
word remain separate observations. External reads are recorded without fetching
their values or widening the window; they still produce partial reasons.
These read dependencies do not establish ownership or permit matching, and
only valid in-window words contribute to `literal_ranges`.
`cfg_closed` describes structural closure under ordinary-call and syntactic
return assumptions, not stack safety, a complete ELF symbol or exhaustive
discovery. `complete` and `inventory_complete` always remain false.

ARM entries remain unsupported by default. Explicitly add
`--refine-arm-inventory` to enable a conservative ARMv4T diagnostic using the
same finite windows, aligned indexed starts, neighboring boundaries and byte
ownership checks. Combine it with `--refine-full-rom-inventory` for late entries.
Supported edges are direct ARM B/BL and conditional fallthrough; direct calls
require valid unique ARM index targets and assume a returning continuation.
Recognized returns are syntactic `bx lr`, `mov pc, lr` and ordinary `pop {..., pc}`;
conditional returns also require their fallthrough path. Only immediate,
preindexed, aligned PC-relative word loads without writeback can contribute
literal words, wholly inside the window and disjoint from reached instructions.
Other PC uses, indirect or cross-mode transfers, system/extension instructions
and unsupported encodings remain partial. This diagnoses bytes at provisional
starts without establishing real functions, ABI safety or match credit. ARM
results use `bounded-arm-cfg-inventory-v1`; both completeness fields stay false.
Thumb diagnostic results and matching, status and reservation gates are unchanged.

#### ARM register-list writeback

The opt-in ARM diagnostic permits ordinary ARMv4T STM writeback with the base
included only when that base is the lowest numbered listed register. This
defined case stores the original base value, including `stmdb sp!, {sp, lr}`.
All addressing directions use the same register-list constraint. Conditional
stores require the following instruction regardless of whether the condition
holds. Empty lists, ambiguous LDM/base writeback, other STM/base overlaps,
user-bank transfers and PC sources remain partial. Existing syntactic return,
window and literal-ownership checks apply unchanged; no stack contents,
alignment at runtime, balanced frame or ABI contract is proved.

Default ARM entries, unresolved indirect transfers or switches, ambiguous
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

Broker addresses use exactly eight hexadecimal digits after `0x`, with even
alignment inside the original 16 MiB image `[0x08000000,0x09000000)`.
This validates ROM coordinates, not executable ownership: headers, assets and
alignment can also have valid coordinates. Establish the complete function
independently before authoring. RAM aliases and ROM mirrors are not accepted.
The automatic discovery cutoff at `0x08150000` is not the reservation boundary.

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

When the server reports an integer ledger comment count of at least 2,500,
request commands stop before posting and exit 2 with `no request submitted`.
The exact GitHub HTTP 403 refusal, `Commenting is disabled on issues with more
than 2500 comments`, also exits 2 if capacity fills between the read and POST.
Other submission failures remain unconfirmed (exit 6). Read-only `list` and
`check` remain available. Capacity recovery requires maintainer action; the
client never retries, deletes comments, or creates or rotates ledger issues.

Broker commands attempt a fast-forward pull first; investigate update warnings rather
than trusting a stale client. `--no-pull` skips this update when the checkout has
already been synchronized. When changing reservation protocols, explicitly pull
and restart all clients: an already loaded old process still contains old code.

### Deploying the reservation broker

The full-image address parser must reach the trusted default branch, and old
broker jobs must finish, before requests at or above `0x08150000` are submitted.
Update and restart clients too. Old code cannot parse a ledger containing a
late-address row or retained receipt, even after that lease is released; prefer
roll-forward repair rather than reverting the parser. Do not edit receipts or
reset the cursor. An already rejected request stays rejected; after deployment,
inspect current availability and submit a fresh request when appropriate.
Local parser acceptance is not deployment or an authenticated lease.

Reservation coordinates and status accounting are separate gates. Status uses
the full function index, but late sources must independently satisfy the normal
compiler/report gates and strict unique-entry, mode, alignment, bounds,
non-overlap and complete-extent checks. An index row does not establish code
ownership or authorize a reservation. The parser deployment and authenticated
lease requirements above still apply; provisional percentages are not
whole-game coverage.

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
and the main-region function denominator remain provisional. The byte
denominator sums legacy layout segments named `code*`, including segments
beyond the discovery cutoff; those labels are not exhaustive code ownership.

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
High-register destinations and wider additions are not supported by this
extension.
An adjacent narrow `movs Rd, #N; lsls Rd, Rd, #S; add Rd, sp, Rd` sequence
may additionally form a low-register alias. The shift must be nonzero and the
exact unsigned result must fit 32 bits; the existing allocated-frame bounds
then apply. The move and shift must be the unique predecessors of their next
instructions, preventing a branch from supplying another offset. This local
proof creates only the stack alias: shifted values still do not establish
general register-index constants, and other arithmetic-derived offsets fail.
An adjacent 16-bit PC-relative literal load into `r0`–`r7`, followed by the
exact `add Rd, sp, Rd` encoding for that same register, may also form an alias.
The in-symbol aligned literal must contain an unsigned, word-aligned offset
at most 4096 bytes, and the resulting address must pass the existing frame
bounds. The load must be the addition's sole CFG predecessor, and its literal
cannot overlap reachable code. This value supplies only the alias formation;
it does not establish a general register-index constant. Nonadjacent loads,
different registers, dynamic offsets and other encodings remain unsupported.
Alias facts must agree exactly at control-flow joins. Pushing or storing these
pointers, unsupported pointer arithmetic, and carrying an
alias across a call in a caller-clobbered register are rejected by these
profiles. The separate buffer-call profile below requires additional ROM
verification for that last case. Callee-saved
aliases survive only under the existing ABI assumption and are cleared when
their registers are restored by a pop.

An exact 16-bit Thumb STMIA may store scalar low registers through a known,
word-aligned stack alias. Its nonempty register list must exclude the base;
each word must fit the tracked frame. Each store applies the scalar store's
saved-return and pointer-word effects, and the base retains its exact incremented
offset after writeback. Stored stack pointers, other modes and encodings, and
out-of-frame or misaligned spans remain rejected. Writeback does not relax
alias joins: a loop with differing live pointer offsets still fails verification.

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

An adjacent 16-bit PC-relative `ldr r0-r7, literal` followed by the exact
16-bit `add sp, r0-r7` encoding also establishes a fixed adjustment when the
aligned in-symbol literal contains a nonzero signed multiple of four, at most
4096 bytes in magnitude. The load must be the addition's sole CFG predecessor;
no branch may bypass it. A literal allocation cannot grow the tracked frame
beyond 4096 bytes, including saved registers. The existing depth joins, local
access bounds, return provenance and balanced-return checks still apply, and
the literal must not overlap reachable code. This rule introduces no general
register constant, buffer-index or pointer fact. The incoming-buffer pass uses
the same proven adjustment. No new report schema or opt-in is required.

Other register-controlled SP writes and untracked stack-pointer transformations
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

Version 2 also permits unshifted register-indexed byte, halfword and word
accesses, including signed loads, when every reaching path proves the index
constant through immediate/register `mov` instructions. Arithmetic and loads
do not establish constants; writes, pops and caller-clobbered calls invalidate
them. Joins retain only identical constants present on every incoming path.
The existing local-word bounds, alignment, pointer-slot overlap and escape
checks still apply. Version 1 continues to reject all register-indexed accesses.

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

### Engine cutpoint diagnostics

`python tools/engine_cutpoints.py --root PATH_TO_GAME` recomputes two real-ROM
descriptor-copy contexts and the allocator-entry prefixes for sizes40/84.
Results state exact entry premises, exit registers/flags, ordered memory events,
byte definedness/alias fragments, open frames and complete input identities.

These are conditional diagnostics, not MATCH reports or replay inputs. The
copy stops before the callback reload; the kill prefix stops with two frames
still open, before the allocator's first nested call. No allocator return,
freshness, runtime-image identity, preceding descriptor preservation, callback
effect or C type/lifetime property is inferred. Missing premises, unsupported
instructions or exhausted finite budgets fail closed. Results are recomputed;
there is no cache, serialized certificate parser or live-verifier consumer.

The incoming-r3 check ends only after a completed overwrite establishes an
independent value. A retained descriptor value or fragment keeps that check
active; an unknown overwrite fails closed. The narrow supported provenance
case is the inspected, numerically separated SP-relative workspace address.
This does not establish destruction of the separate retained r9 alias.

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
qualify. Each relocation must occupy a complete aligned word inside the function
and be loaded by a reachable PC-relative instruction. The word must be disjoint
from every reachable instruction byte. Trailing pools and branch-skipped middle
pools are supported; entering a pool as code or falling through it is rejected.
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

Fixed-frame callers use `elf-symbol-thumb-frame-function-addresses-v1`.
They must pass the existing constant-frame, bounded-access, stack-alias and
balanced-return checks, as well as the same typed literal checks. Reports bind
the separate schema and require the verified stack-frame summary. Dynamic or
unbalanced frames and stack aliases escaping across calls remain rejected.

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

### Audited signed quotient with positive constant divisor

The `elf-symbol-thumb-divsi3-positive-constant-v1` profile accepts canonical
compiler-generated `__divsi3` calls with a CFG-proven positive signed32 constant
divisor. It allows arbitrary signed32 dividends: a divisor in `1..0x7FFFFFFF`
excludes division by zero and `INT_MIN / -1`. Ordinary mapped direct Thumb
calls and register PUSH/POP saves may coexist. Explicit frames, stack aliases
or arguments, buffers, switches, indirect thunks, callbacks, named object
relocations and other arithmetic runtime profiles remain excluded.

The explicit companion `--signed-quotient-profile positive-constant-frame-v1`
uses schema `elf-symbol-thumb-divsi3-positive-constant-frame-v1`. It requires
an allocated caller SP frame and reuses the complete native CFG, balanced
stack, saved-register/return, stack-alias and literal checks before proving the
same positive constant divisors. Its exact manifest also requires `frame:true`;
source/ELF replay and status verification retain this selector. Default and
standalone quotient behavior stay unchanged. Ordinary calls retain only the
structural returning-call ABI premise. This diagnostic support supplies no
whole-callee, C admission, match, or exhaustive inventory proof; an instruction
count correction alone leaves `inventory_complete` false.

The pinned `agbcc-thumb-divsi3-v1` identity is the complete 146-byte Thumb
function `[0x081426B8,0x0814274A)`, SHA-256
`80b13b14c17b297e6c92a50aeddcacdffbe951729bcb1290e205055950655884`, and its
two-byte handler `[0x0814274C,0x0814274E)`, SHA-256
`abd49ec8111be1f55319f91a44d26daaf5abd7567c169a61abf6c0b031d4b31c`.
Exact unique nonoverlapping Thumb mappings, current ROM bytes and the dependency
BL at helper offset `0x8A` are checked. External alignment is not part of either
symbol. The zero handler's machine behavior does not define C division by zero.

Each canonical zero-expression `R_ARM_THM_CALL` must reference one zero-valued
undefined global FUNC/NOTYPE `__divsi3`. Typed linking binds it only to absolute
Thumb FUNC `0x081426B9`. Addressed/interior aliases, objects/addends, runtime
address literals, extra functions/text, veneers and unexplained byte changes
reject. Old schemas do not grandfather addressed signed-quotient calls.

A profile-local constant pass converges over the validated CFG before testing
call obligations. It supports unconditional Thumb16 MOV/MOVS immediate/copy and
constant LSL immediate with u32 wrap, retaining only equal facts at joins.
Other writes kill facts; calls kill caller-saved facts. This proves both MOV100
and MOV180/LSL1=360 without widening other profiles or assuming a dividend range.
It does not prove general C memory safety, caller termination or callee semantics.

Reports contain exact canonical `runtime`, `calls`, `divisors` metadata. Every
signed-schema replay **freshly compiles captured source/headers** under the fixed
approved `agbcc -mthumb-interwork -O2` configuration, revalidates the original
canonical ELF symbols/relocations and typed complete link, compares the derived
manifest and full body with the saved/current ROM, and rechecks all inputs.
Fingerprints and linked bytes alone cannot distinguish a canonical compiler
alias from a forged report around addressed source. Replay therefore requires
the local toolchain and cannot accept a cache-only result. It is guarded against
reentry, uses 120-second per-command limits with owned POSIX process-group
cleanup, and removes its own disk-backed temporary artifacts on all exits.
Signed-schema replay fails closed on non-POSIX hosts, including native Windows.

Activation requires one immutable selected toolkit/game source-report-map pair
to pass the full joint verification gate. Keep the old selected pair until that
exact new pair is available; separate repository updates are not atomic, and
arbitrary latest-tool/latest-game combinations are not an activation contract. Existing
addressed callers must be explicitly corrected and independently byte-verified;
do not enable these exclusions against an unmigrated selected game snapshot.
There is no signed-quotient addressed-source exception or automatic rewrite.

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
replay evidence against the local ROM. Schema-specific checks can also require
fresh source compilation, as the signed-quotient profile does.
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

The explicit software-double and inert-spin profiles are selected only from a
current saved report using their strict profile parsers and fresh report replay.
The rebuild then passes the corresponding fixed selector to the matcher with
`--no-write --emit`; it never derives compiler options from report text or falls
back after failed verification. Selected reports and the function text index
must remain unchanged through output verification. Ordinary compilation without
an opt-in report retains the default matcher policy, including when no report
exists. Reports are never regenerated by a compiled rebuild.

The result is explicitly a **partial mixed C/ROM build**, with separate compiled
and original byte counts. An identical full-ROM SHA-1 proves integration of the
currently matched code, not that the remaining original code is decompiled.
Without `--compiled`, the existing manifest-concatenation check is unchanged.

### Evidence-bound empty functions

The standalone `plausible.py` checker still rejects empty bodies. `match.py`
can discharge exactly one `empty-body` finding using
`elf-symbol-thumb-empty-v1`: the sole addressed source must contain only
`void func_ADDRESS(void) {}` (comments and whitespace are allowed), and the
default toolchain must emit one ordinary global Thumb function whose complete
ELF symbol is exactly `bx lr` (`7047`, two bytes). Both function indexes must
agree on a unique, nonoverlapping two-byte span and one instruction. The ROM,
ELF mode/alignment, closed return CFG and absence of relocations must agree.
Other findings, placeholder markers even in comments, additional functions,
headers with empty bodies and hand-assembly allowances cannot use this exception.

Reports bind source/header inputs and both indexes. Consuming a report freshly
compiles captured sources with the default toolchain and rechecks the original
ELF and plausibility findings; unavailable replay fails closed. Missing,
duplicated, altered or stale fields fail, including relabeling the report as a
legacy profile. The push plausibility sweep accepts the source only through
this same report verifier. This proves the complete function body, not external
section padding, the historical C signature, or behavior for invalid return
addresses. Other empty C spellings and ARM-mode no-ops remain unsupported.

Focused checks (requires the installed default compiler, binutils and Capstone):
`PYTHONDONTWRITEBYTECODE=1 python tests/test_empty_body.py`.
Test workspaces are created under `build/`, or `FFTA_TEST_SCRATCH` if set.

It also gates on \plausible.py\: byte-identical output from source that looks
like a codegen hack (inline asm, pragma surgery, dead code, \olatile\,
steering padding) is reported **IMPLAUSIBLE**, not a match. Exit status is 0
only when the bytes match *and* the source is plausible.

The documented hardware `volatile` exception requires an adjacent actual
`plausible:` comment and a direct access within `0x04000000..0x040003FF`,
or a pointer initialized to an external symbol mapped into that register
window by `config/data_symbols.json`. Such a pointer may only be used for
member access; retargeting, shadowing and escapes remain rejected. A comment
alone cannot permit volatile RAM or local variables, asm or steering pragmas.

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

## Explicit mixed-return inert spins

`match.py --control-flow-profile mixed-return-inert-spin-v1` selects the
separate `elf-symbol-thumb-mixed-return-inert-spin-v1` report profile. Ordinary
matching and all older schemas keep their existing return-reachability rule.
The new profile requires a normal verified return and at least one reachable
instruction without a graph path to a return. **Every** such instruction must
itself be an unconditional narrow Thumb branch to its own address. Pure-spin
functions, multi-instruction cycles and even branch-only feeders are excluded.

The complete converged instruction, stack/provenance, local-alias, call and
literal checks still run, including checks after return classification. A
fixed frame may remain allocated on the spin arm; actual returns must balance
it. Ordinary typed mapped Thumb calls and fixed frames are supported, but
buffer proofs, switches, function/object relocations, indirect-call thunks and
signed/unsigned division/remainder or software-double profiles cannot be combined with this
profile. No automatic fallback or caller-address exception selects it.

Only the fixed approved agbcc `-mthumb-interwork -O2` configuration is accepted.
The original ELF must own one complete Thumb function and its pools, without
other allocated contents or unresolved relocations. Both function indexes
must agree with that complete extent. Reports bind source/header inputs,
both index snapshots, full bytes and canonical derived call/frame/spin
evidence. Every report replay freshly compiles a captured copy of the entire
existing `source_paths` dependency universe, inspects the original ELF and
typed link, and reruns the CFG and plausibility checks. Rehashed metadata is
not a substitute for this provenance. Replay has bounded subprocesses,
nonrecursive guards and disk-backed cleanup; it fails closed when unavailable.

Status selects this policy only from its explicit saved schema, never from
an address or a failed ordinary verification. Fresh no-write verification
also requires the saved new-schema report to replay successfully; stale
inputs require `--write --verify` to regenerate and replay it. A report header
selects policy but cannot grant a match. Mixed, stripped or downgraded proof
markers do not relax the old verifier. The existing push/status gate uses
these same checks.

This proves a narrow local machine-CFG property, not termination, initialized
locals, general C definedness, arbitrary pointer safety, callback semantics
or external-callee correctness. A conditional loop with an exit already
accepted by the ordinary profile can still run forever. Source contracts,
plausibility and separate semantic review remain required.

## Canonical 64-bit left-shift runtime

Natural C shifts that emit `__ashldi3` automatically select
`elf-symbol-thumb-ashldi3-target-v1`. Only the canonical undefined global
compiler symbol can bind to the complete Thumb runtime at `0x0814220C`.
Both function indexes must agree on its unique nonoverlapping span and
instruction count; its complete body hash and closed-leaf return/stack proof
are checked. A focused test recompiles the local agbcc split-word reference
algorithm and requires the exact pinned body.

The ABI takes the low/high words in `r0`/`r1` and the shift count in `r2`, and
returns the low/high result in `r0`/`r1`. The versioned semantics describe the
actual ARMv4T register shifts. They agree with unsigned C left shift for counts
0 through 63; the profile does not claim that C shifts outside that domain are
defined, or prove a caller's shift-count range. Caller analysis retains the
ordinary conservative register clobbers, fixed-frame checks and return-address
provenance. Mapped data literals and scalar frames are supported; other callees,
runtime profiles, function literals, switches and call thunks are excluded.

Reports bind the source and headers, both function indexes, data mapping,
complete caller bytes, ROM snapshot and fixed toolchain. Cached validation
recompiles and relinks captured source and reruns plausibility. Addressed
aliases, interior/odd runtime addresses, wrong or overlapping owners, modified
runtime bodies, mixed profiles and stale evidence fail closed. The normal
matcher, status verification and publication gate use this same automatic path.

## Canonical 64-bit logical-right-shift runtime

Natural unsigned 64-bit `>>` expressions emitting `__lshrdi3` automatically
select `elf-symbol-thumb-lshrdi3-target-v1`. The complete Thumb runtime at
`0x08144378..0x081443AE` is pinned to the fixed-compiler split-word reference:
54 bytes, 27 instructions, low/high input and result in `r0`/`r1`, count in
`r2`. A conservative CFG proof requires every call's count to be in 0..63;
unknown, negative or excessive counts are rejected. It recognizes bounded
nonwrapping register arithmetic, masks and adjacent comparison guards. Unknown
loads discard numeric facts. Both indexes, complete runtime bytes, typed ELF
relocations, caller stack/return provenance and fresh source replay are checked
as for left shift. Explicit runtime identifiers in preprocessed source, addressed
aliases, mixed operations/profiles and forged or stale evidence are rejected.
Mapped data and fixed scalar frames remain supported. Existing left-shift
reports and count semantics are unchanged.

## Canonical float multiply, unsigned conversion and double comparison

Natural C that emits `__mulsf3`, `__fixunssfsi`, `__extendsfdf2` or `__ltdf2`
automatically selects `elf-symbol-thumb-sf-mul-fixuns-target-v1`. Only these
canonical undefined global symbols bind to `0x08143CEC`, `0x081428AC`,
`0x0814432C` and `0x0814379C`, respectively. The fixed agbcc
`-mthumb-interwork -O2` toolchain is required. Multiply consumes float bits in
`r0`/`r1`; unsigned conversion consumes float bits in `r0`. Both return in
`r0`. Extension consumes float bits in `r0` and returns double high/low words
in `r0`/`r1`. Comparison consumes two double high/low pairs in `r0` through
`r3` and returns the pinned target comparison code in `r0`.

The approved complete ROM SHA-256 is
`43fc8204c6dceee58828aebc7af0c72eb807e99f35ad641c8bb0a4fa8b6edc19`.
All seventeen complete runtime bodies and twenty-three native dependency edges in
`software_float_profile.py` are pinned. Both indexes must agree on exact,
unique, nonoverlapping Thumb owners and reachable instruction counts, including
the helpers' trailing literal pools. Legacy truncated or linearly counted
metadata is rejected.

A runtime-specific check reuses bounded native CFG/body partitioning and then
tracks actual register saves, local stack words, all return paths and bounded
formal output writes. Dependency footprints are applied only after the
dependency itself passes. Every return restores `r4` through `r11`, balances
`sp`, and transfers through the saved entry return address. All four public scalar
helpers have no external writes. The double unpacker may write only its
five-word formal output record; existing single-precision outputs keep their
four-word bound. A private double-construction helper reads exactly one formal
stack word at entry SP. Every call must establish that whole word in its own
local frame on every incoming path, separate from saved registers. Only this
pinned helper enables the adjacent pop-register, add-SP-four, branch-register
return shape, with actual saved-LR provenance and balanced SP independently
proved. The double packer permits bounded byte and halfword local stack stores;
any overlap with a saved register rejects and narrow accesses cannot fabricate
saved-register provenance. Default CFG and runtime stack policies remain
unchanged. These checks do not broaden ordinary call summaries. The semantics describe the pinned target machine, with RAM reads
and uninitialized local values as state inputs; they do not establish general
IEEE arithmetic, C conversion definedness, arbitrary pointer safety or loop
termination.

Mapped object literals, ordinary indexed direct Thumb calls and existing
scalar frame checks can compose with this profile. Ordinary external callees
retain their returning ABI assumption. Other runtime profiles, callbacks,
function literals, switches, buffer proofs and inert spins remain excluded.
Runtime entry/interior/odd addresses cannot be smuggled through addressed
aliases, objects or addends. Helpers require canonical zero-addend Thumb call
relocations; the linker may change only independently checked relocation bytes.

Reports bind both indexes, mapped data, source and headers, the approved ROM,
complete exact caller bytes, dependency identities and fixed compiler setup.
The closure uses runtime ID `agbcc-thumb-sf-mul-fixuns-extend-lt-closure-v2`
and ABI ID `agbcc-thumb-sf-df-mixed-result-r0-r1-v2`; older IDs and dependency
lists reject. Cached validation recompiles captured source, relinks the original
ELF and reruns CFG, runtime ABI and plausibility checks. A non-exact caller, stale
mapping, altered proof, duplicate field or mixed profile fails closed. Focused
tests create synthetic callers in memory using only the local approved runtime;
no ROM bodies, disassembly or game-derived fixtures belong in toolkit history.

## Target binary64 conversions and arithmetic

`match.py --software-double-profile convert-sub-div-target-v1` explicitly
selects `elf-symbol-thumb-df-convert-sub-div-target-v1`. Only the fixed agbcc
`-mthumb-interwork -O2` configuration is supported. At least one fresh original
ELF call relocation must name `__floatdidf`, `__floatsidf`, `__adddf3`, `__subdf3`,
`__divdf3`, `__muldf3`, `__ltdf2`, `__truncdfsf2` or `__fixdfsi`. Private
integer helpers and other floating operations remain unsupported.

All eighteen complete runtime identities in `software_double_profile.py` are
mandatory, including pools, internal alignment and 36 dependency edges.
Both function indexes must contain their exact unique, nonoverlapping Thumb
extents and instruction counts. Legacy truncated metadata cannot substitute
for these spans. Their entire intervals are reserved against addressed-call,
data/base/addend, function-literal, raw-literal and older-report bypasses.
Only the nine canonical double caller entries are exposed; transitive private calls
are justified by the pinned closure, not caller-access exceptions.

The truncation closure adds the complete 72-byte/32-instruction conversion,
188-byte single packer and 24-byte/11-instruction private wrapper, reusing the
existing double unpacker. Native reachable-CFG and machine-state proofs check
all four bodies, their exact call edges, balanced frames, restored callee-saved
registers and returns. The unpacker may write only its five-word formal output
record; transitive writes must fit the actual caller frame and cannot overwrite
saved registers. Subword stack loads are bounded and supply unknown state,
never saved-register provenance. Each runtime closure supplies its exact call
edges, public entries and bounded output policy to the shared interpreter;
word-only stack access remains the default.

The add/subtract/divide/comparison closure checks ten complete native
bodies, their reachable CFGs, actual frames, saved-register restoration and
returns. The unpacker writes exactly five words through formal R1; the
arithmetic kernel writes exactly five words through formal R2. Public entries
must contain those writes inside their real local frames and have no external
writes. Addition returns a register pair; comparison returns its scalar target
result. All numeric operands remain machine-state inputs; unrestricted IEEE
semantics are not asserted.

Canonical symbol identity is independently grounded in the local agbcc runtime
source compiled with the fixed configuration: the complete `__adddf3` object
body matches ROM `08143080` (52 bytes), while `__muldf3` matches `081430F0`
(684 bytes). The multiplication closure proves its five complete native bodies,
bounded unpacker output and restoring public ABI. Canonical ELF names are kept
through linking; addition and multiplication addresses cannot be interchanged.

The existing canonical `__ltdf2` entry may belong to the isolated software-float
or software-double profile. Its exact undefined ELF symbol, address, call-site
binding and active context must agree. This does not combine those profiles:
simultaneous contexts, other single-precision operations in double callers,
addressed aliases, private runtime calls and unproved integer-runtime mixtures
remain refused. Versioned dependency manifests and fresh source/report replay
include the new closure; old runtime manifests cannot assert this capability.

The canonical `__fixunsdfdi` entry is additionally pinned at
`0814278C..08142862` (214 bytes, 80 reachable instructions), with the complete
unsigned-conversion dependency closure and restoring ABI. This exact owner may
also remain authored C: only its full pinned body/hash, exact dual-index owner
and count pass the reserved-caller exception. Other runtime owners, interior or
recursive calls, addressed aliases, forged bodies and stale manifests remain
refused. Credited source still requires fixed-toolchain original ELF provenance,
complete native byte/CFG/ABI checks, plausibility and fresh report/source replay.

The original ELF must contain one complete Thumb function, canonical undefined
global call symbols and canonical BL addends. Typed linking must preserve all
other bytes, with no veneers, residual relocations or unexpected allocated
contents. Ordinary typed direct calls, balanced fixed frames, bounded local
aliases, numeric literals and inherited aligned scalar SP reads are supported.
Direct incoming scalar reads have no verifier-proved argument-count or upper
bound. Compatible C signatures, initialized readable backing, lifetimes and
capacity remain source-review preconditions. Stores outside the tracked frame
still reject. Named data can compose with this profile through original-ELF
`R_ARM_ABS32` relocations in complete aligned literal words referenced by reachable
PC-relative loads. Each undefined global object must have an evidence-backed
`config/data_symbols.json` binding; signed addends, indexed code ownership and
reserved runtime intervals are checked before and after linking. Numeric address
constants cannot substitute for object relocations, even with a rehashed report.
Buffers, stack-argument proof contexts, resolvers, function relocations and
thunks remain excluded. The optional `software-double-guarded-word-switch-v1`
record admits the existing unsigned-guarded local word-table encoding. Its
comparison, guard, dispatch, default, table pointer and every local target must
agree with the complete function and original ELF relocations; table words,
referenced literals, code and alignment remain disjoint and fully covered.
The optional `thumb-same-owner-long-bl-restoring-frame-v1` record admits exact
Thumb BL edges used as local long jumps within the same sole function owner.
These edges overwrite LR, preserve argument registers and have no continuation
edge. Every exit must independently restore entry LR, SP and r4-r11; overlapping
owners, self-entry edges and incomplete frame provenance reject. Original
single-function ELF provenance and fresh source replay remain required.
The explicit software-double selector additionally accepts the optional
`software-double-inert-self-spin-v1` record. Every reachable node without a
return path must be a listed unconditional two-byte Thumb self-branch; at least
one balanced verified return is still required. The complete byte, original-ELF,
runtime, stack, literal and source-replay checks remain in force. Missing, stale
or altered spin records reject; ordinary no-spin manifests keep their format.
The existing bounded remainder composition uses the original compiler
`__modsi3` symbol. Every site in that mode must have a CFG-proven signed16 dividend in r0
and nonzero divisor in r1; loads from unknown memory or locals supply no
operand facts. Its exact 206-byte/102-instruction runtime and two-byte zero
hook require both ownership indexes, pinned bytes and native restoring ABI
proof. The hook's MOV PC,LR and runtime's MOV PC,LR / POP PC returns are
accepted only at explicitly pinned sites, after complete SP and callee-save
restoration checks; the shared runtime interpreter's default remains unchanged.
Balanced fixed frames may compose only after the existing complete double
caller stack/save/return proof. Standalone numeric MOD remains frameless.
A versioned remainder manifest records exact dependencies, sites and domain;
canonical BL relocations, typed data provenance and fresh source replay remain
mandatory. Addressed integer-runtime aliases and unsigned division/remainder
combinations still reject.

Canonical `__divsi3` can additionally compose through its separately versioned
`agbcc-thumb-divsi3-target-state-closure-v1` record. Dynamic signed remainder
requires the explicit additional
`--software-double-remainder-profile target-state-v1` selector and its
`agbcc-thumb-modsi3-target-state-closure-v1` record. These modes pin the complete
original runtime and zero helper, all sign and zero paths, stack/save/return
provenance and absence of external writes. Reports describe target machine
state, including exceptional inputs; they do not assert unrestricted numeric C
quotient or remainder equivalence. The standalone positive-constant quotient
and signed16/nonzero remainder policies retain their operand requirements;
old reports keep their formats. Saved target-state reports retain the explicit
selector during verification and rebuild replay.
Ordinary callees retain entry-only binding and ABI assumptions: their complete
bodies, semantics and return behavior are not proved.

Binary64 values use high-word/low-word register and memory order, with
little-endian bytes within each word. Signed64 conversion instead consumes
integer low/high words; signed32 conversion consumes r0. Truncation consumes
binary64 high/low words in r0/r1 and returns single-precision bits in r0. This is an explicit
target-machine-state contract, not unrestricted IEEE arithmetic or a pure
function of operand values. Entry RAM and stack bytes are state inputs and
persist between calls. Exceptional paths read the mutable private record at
`[0x03005E50,0x03005E64)`: the same operands can yield qNaN or negative zero
under different record states. Private stack reads can precede a write in
the current invocation; per-pack and whole-runtime write epochs differ.
No implicit zero initialization, finite-intermediate assumption, all-state
termination, general C definedness or physical stack-capacity proof is claimed.
The closed helper graph's maximum stack chain is 220 bytes below call-time SP,
in addition to the caller frame and any separately assumed ordinary callee.

The six-key manifest records runtime/ABI/semantics IDs, all dependencies,
derived frame usage and every reachable call. Callers with data relocations add
one ordered `data` list of literal offsets, object names and signed addends;
zero-data manifests keep their existing format and fingerprint. Reports bind
the source and full `source_paths` header universe, both function maps, whole
ROM, fixed configuration and complete caller. Data callers additionally bind
the exact data mapping. Every replay freshly captures and compiles those inputs,
checks original ELF provenance, relinks and reruns CFG/plausibility checks.
Rehashed manifests cannot turn addressed source into canonical provenance.
Subprocesses are bounded, replay is nonrecursive, and temporary disk-backed
workspaces are cleaned. Compilation failure or input/universe/ROM-path drift
fails closed; there is no cache or alternate acceptance fallback.
The conversion closure uses runtime ID
`agbcc-thumb-df-convert-sub-div-trunc-closure-v2` and ABI ID
`agbcc-thumb-df-sf-mixed-integer-v2`; earlier dependency lists and IDs reject.

Status dispatches only the explicit saved schema. Offline checks and fresh
no-write verification require successful saved-report replay; an independent
fresh compile cannot hide stale evidence. Explicit `--write --verify` refreshes
unambiguous evidence. Mixed, malformed, duplicate, downgraded or contradictory
verdict/profile markers reject, including horizontal-whitespace variants.
The normal status and push-match gates use these same rules; no target-address
allowlist, source rewrite or progress exception is introduced.

### Explicit acyclic owner frames

`--owner-runtime-profile restoring-owner-acyclic-v1` selects
`elf-symbol-thumb-acyclic-stack-alias-v1`. It preserves distinct stack, alias,
constant and return-provenance states at joins, with a fixed limit of 4096
distinct instruction/state pairs including entry. Every path must pass the
ordinary native frame, alias-use, escape, call and return checks. Reachable CFG
cycles and exhausted budgets reject. Only ordinary direct Thumb calls compose;
buffer profiles, arithmetic runtimes, indirect thunks, local BL and switches
remain excluded. All syntactic conditional edges are checked.

Complete ownership and instruction counts, original ELF provenance, typed
bindings, fixed compiler flags, plausible source and fresh report replay remain
required. Status and compiled rebuild forward the saved explicit selector.
Default matching and `restoring-owner-runtime-v1` retain their existing behavior.

### Explicit ignored incoming leaf aliases

`--owner-runtime-profile restoring-owner-ignored-leaf-alias-v1` selects
`elf-symbol-thumb-ignored-leaf-alias-v1`. This separate, default-off composition
retains the acyclic owner's 4096-state budget and every caller frame, alias,
ELF, typed-binding, fixed-compiler and source-plausibility check. Earlier
selectors and default matching remain unchanged.

A caller-clobbered stack alias can be discarded only when its exact original
callee is a complete, noncalling Thumb leaf of at most 256 bytes. Fresh ROM
replay proves unique ownership, mode, both indexed instruction counts, closed
CFG, complete byte partition, typed literals and ABI preservation. Every path
must fully overwrite each incoming alias register before any read and before
every return. Conditional instructions may observe only condition flags already
defined inside the callee, including separately tracked N, Z, C and V bits.
The narrow Thumb-1 instruction-effect policy rejects unsupported effects,
incoming stack pointer slots, ordinary memory accesses, and indirect,
forwarding, recursive, unknown or cross-mode calls. C prototypes cannot waive
an actual register input. Reports retain the complete callee proof and body,
ROM, mapping, index and object SHA-256 identities, without serializing the raw
callee body. Fresh source-bound replay, status and compiled rebuild preserve
these bindings.

For original caller `0801B630`, this proof advances past `0801B690` and the
second call at `0801B698` to leaf `0801AD1C`. The actual local-buffer argument
in r0 at `0801B6AA`, calling `0801AF08`, remains refused. This verifier
capability grants zero game C credit and does not admit the complete caller.

## Status accounting

The two existing percentage badges and table rows retain their legacy
provisional bases. The function denominator counts entries starting below
`0x08150000`; matched main bytes count indexed spans. The byte denominator sums
all legacy layout segments named `code*`, including late-ROM labels, falling
back to the union of main indexed spans when that sum is zero or the layout is
absent. Layout labels do not prove executable ownership, and historical index
spans may be truncated or overlapping. These numbers are not whole-game
completion percentages.

Additional verified late-ROM spans are reported separately as absolute
function and complete-body byte counts, without a guessed denominator. Their
complete ELF/report extent must equal the unique indexed extent. Internal
literal pools count; external alignment and installation-time RAM aliases do
not. No late count changes a legacy numerator, denominator or percentage.
This is recovered-code evidence, not an exhaustive late-ROM inventory.

`--verify` performs fresh official matching without rewriting reports;
`--write --verify` also regenerates and replays them. Fresh no-write verification
does not require a pre-existing report for legacy profiles; the explicit
inert-spin, software-double and function-address/thunk profiles require their saved reports as described
above. `--check` takes precedence over
`--write`, and any failed main or late source still makes the status gate fail.
Hosted report/block checks do not substitute for local ROM-backed matching.

## Notes for people extending the analysis

### Explicit function literals with canonical call thunks

`match.py --function-address-profile canonical-thunks-v1` selects
`elf-symbol-thumb-function-address-thunks-v1`; default matching does not select
it automatically. It requires compiler-generated `_call_via_r0` through
`_call_via_r12` calls. The callback may come from a context or an incoming
argument; function-address literals are optional. Any such literals still
require original typed ELF provenance. Ordinary
mapped Thumb calls, mapped objects and fixed scalar frames may coexist. Buffer,
switch, arithmetic-runtime and inert-spin contexts cannot be combined with it.

Each used thunk's four-byte identity includes two executed BX bytes and two
external alignment bytes. Only canonical original ELF names/relocations are
admitted; manually naming `_call_via_` identifiers in preprocessed C, addressed
aliases and thunk-table object/addend substitutes are rejected. Complete original
and final ELF ownership, typed linking, pools, literal uses, fixed-point stack
and return provenance, plausibility and exact ROM bytes remain mandatory. A
tracked stack or saved-return value cannot serve as the thunk target register.

This is conditional caller evidence. It assumes compatible executable indirect
targets, valid argument backing/types, preserved ABI state and returning callees.
Ordinary and retained function bindings establish mapped entries, not full callee
bodies or semantics. It does not prove initialization, argument arity, arbitrary
alias safety, callback lifetime, installed RAM identity or termination. Inherited
scalar incoming-SP reads do not add such proofs.

Strict saved reports freshly compile the entire captured source/header universe
with fixed compiler configuration, check original relocation provenance and
complete typed linking, and recheck source/maps/index/data/ROM snapshots. Exact
typed manifests, reserved-marker detection and contradictory-verdict rejection
apply. Older thunk-caller reports also require fresh default original-ELF proof
that their caller contains no function-address relocations, so stripping new
markers cannot downgrade the composition. Conservative legacy buffer replay
performs this absence proof when it has no direct caller classification.
That fresh replay retains the already-validated register-buffer or stack-buffer
mode, independently re-derives its ROM-backed dependency and complete caller
span, and still checks reachable literal provenance. It does not admit buffers
to the new explicit composition or replace the existing dependency fingerprint
and escape checks.
For every thunk caller, mapped data relocation bases and signed-addend results
must not alias indexed function entries (even or Thumb-tagged) or the reserved
thunk table. Such ambiguous code-as-object bindings require canonical function
provenance; renaming a callback as mapped data cannot bypass the selector.
Reachable PC-relative pool words matching indexed code entries require the
canonical function relocation at that offset; reserved thunk-table literals
are rejected. This is a conservative provenance boundary for ambiguous
code-valued literals, not proof that a numeric value denotes a function. It
does not scan instruction bytes, unreachable pool words or unrelated integers.

Status and compiled rebuild use only the fixed selector derived from a strictly
replayed saved report; stale, malformed or missing reports do not authorize it.
No-write verification does not refresh evidence. Rebuild preserves selected
report and text-index snapshots through output publication and cleans owned
output on failure. No source or Parked promotion follows from installing this
tool capability; source review and the complete publication gates remain separate.

* `analyze.py` treats `pop {r0}; bx r0` as a return. Capstone does not flag the
  Thumb interworking epilogue, and without that every function using it
  swallows the one after it.
* Verified function starts need a prologue *plus* a walk that reaches a return
  or tail branch. A bare prologue scan matches ~16,000 false positives inside
  4bpp tile data, where the byte pair `0xB5xx` looks like `push {rX, lr}`.
* `rebuild.py` is the gate: if the concatenation does not reproduce the ROM, the
  split is wrong and nothing downstream is safe.

# Scalar-frame two-constant switches

The explicit `--switch-profile two-constants-frame-v1` selector and
`elf-symbol-thumb-switch-two-constants-frame-v1` schema compose the guarded
two-constant table with fixed scalar SP frames. This is a separate opt-in:
`two-constants-v2` still rejects frames and retains its exact serialization.
Neither default matching nor failed replay upgrades or falls back to it.

The same converged CFG worklist follows all cases, defaults and backedges,
tracking stack depth, saved-return facts, scalar slots and ordinary ABI call
clobbers. At least one reached nonzero narrow fixed allocation is required.
Narrow fixed SP adjustments, PUSH/POP, direct aligned SP word loads/stores and
ordinary incoming fifth/later argument reads are supported. Every verified
return restores entry depth; joins require equal depth and intersect return
facts. Stable loops are not termination proofs. Every SP-to-register address
formation rejects, even when dead or overwritten; non-PUSH/POP block transfers,
dynamic/wide adjustments, invalid stores and fabricated returns also reject.
Buffer/resolver, function/object literal, runtime/thunk, preloaded-switch and
inert contexts cannot combine with this policy.

Only this schema adds the exact marker `fixed Thumb scalar SP frames; no
stack-address materialization` and a `frame` manifest with policy
`fixed-scalar-sp-v1`, sorted `adjustments` pairs `[instruction_offset,
signed_byte_delta]`, and sorted `accesses` triples `[instruction_offset,
"ldr"|"str",sp_displacement]`. These are instruction-derived facts collected
after successful full-graph verification, not trusted input bounds. Replay
freshly rebuilds the captured source and compares the entire canonical report;
unknown/duplicate keys, altered summaries, mixed schemas and malformed selectors
reject. The fingerprint is domain-separated from v2. Status/rebuild forward the
exact saved selector; frame rebuilds cross-check emitted size against the saved
report and canonical matcher extent, excluding placement-prefix bytes.

Original/linked ELF ownership, all raw relocation extents/addends, two reached
unrelocated words, deterministic placement, regular-file identity capture,
source/header/map/index/ROM bindings, bounded subprocesses and cleanup are
unchanged. Tool identity is checked for drift during fresh capture; no new
persistent tool-hash field is claimed for the old fingerprint.

This is conditional caller evidence under the ordinary returning ABI, not a
proof of scalar initializedness, physical stack capacity, exact r4-r11 value
restoration, pointer-free incoming bits, allocator safety or arbitrary memory
effects. It does not import the private region engine or admit E03F8's buffer,
callback, descriptor and lifetime composition. Synthetic natural-C tests are
not authorization to retry frozen game candidates.

# Two-constant switch placement profile

The opt-in `thumb-entry-context-v1` build stage supports both even
function-origin classes without changing legacy ownership gates. No game
function is admitted merely by installing the capability.

The explicit `--switch-profile two-constants-v2` path supports one unsigned-guarded
five-instruction Thumb dispatch with exactly two reached, unrelocated constant
words between the dispatch and its relocated local pointer/table. Default CLI
and legacy profiles do not select it. It excludes frames, stack buffers,
function/object literals, callbacks, runtime thunks and additional indirect
transfers. Recognizing E03F8's pool placement does not discharge its other
verification obligations or admit a game source.

Issuance and `elf-symbol-thumb-switch-two-constants-v2` report replay each capture
the uniquely addressed C source and all tracked include inputs, compile with the
fixed default tool tuple, inspect every original ELF relocation, link typed
targets, and regenerate the complete CFG/ownership manifest. Both indexes and
the approved 16 MiB ROM identity are required. The ROM is read directly, never
copied into replay scratch. Tool resolution/content and live/captured inputs
are checked for drift. Child processes have a 120-second bound and process-group
cleanup; replay workspaces reside under the selected root's disk-backed `build/`.
The operator must not place that root on tmpfs.

The private assembly parser accepts only the fixed compiler header, Thumb/text
entry envelope, four-byte zero-fill entry alignment, one addressed global sized
function, local numeric/long-branch/end labels, the enumerated Thumb instruction
mnemonics, `.word` expressions and four-byte zero-fill internal alignment. It
accepts only the compiler's exact conditional-branch and long-jump annotations;
arbitrary comments, strings, macros/includes, alternate sections, extra functions,
emitting prefixes and other directives reject. Input is bounded to 1 MiB.

For target A, the stage derives p=A%4 and B=A-p. Zero-origin assembly is unchanged;
base-two assembly inserts exactly `\t.space\t2, 0\n` immediately before the unique
entry `.thumb_func`, after entry alignment. Raw compiler output is retained
unchanged throughout compilation. No result-dependent rewrite or source/flag
selection occurs. Genuine complete original and linked ELF remain in section
coordinates: the function occupies [p,p+N), the section links at B, and its entry
is A|1. Exactly p zero prefix bytes and the separately checked external alignment
suffix earn no function credit. Raw relocations/addends remain section-relative;
only validated manifest offsets are derived by subtracting p. Existing legacy
binders never receive a normalized or stripped object.

The strict `placement` manifest member binds the rule, derived origin/prefix and
raw assembly, placed assembly, original ELF and linked ELF SHA-256 identities.
The linked ELF hash uses the exact byte snapshot parsed and validated, not a
later unvalidated reread. Linked ELF and objcopy output must remain regular
files with unchanged contents and filesystem identities through the final
workspace capture check; mutation or replacement rejects issuance and replay
before any report or emitted body is written.
Artifact descriptors open nonblockingly without following symlinks and must
identify regular files before any read. FIFOs reject without waiting for a
writer; descriptor closure and path/descriptor identity checks remain mandatory.
Every replay regenerates them with stable logical filenames; reports cannot
choose placement or supply objects. Prior private v1 selectors/reports reject
terminally rather than silently selecting the amended build contract.

The new report family has strict canonical fields and JSON; malformed or mixed
markers and failed fresh replay reject terminally. Its source/manifest/input
fingerprint is not a substitute for original-ELF provenance. Status and rebuild
forward only the explicit saved selector. Old schemas and fingerprint algorithms
remain unchanged.

Successful issuance prints the canonical complete-symbol extent from the freshly
verified body. Late-address status verification checks this against both the
indexed span and replayed report; missing, duplicate, malformed or disagreeing
extent output remains a terminal failure.

Focused checks: `python -m unittest discover -s tests -p 'test_switch_*.py' -v`
with the ARM tools on `PATH` and disk-backed `TMPDIR`. The natural-C fixture uses
real fixed tools and fresh report replay. Synthetic fixture ROM trust is patched
only inside tests; production exposes no alternative-ROM or ELF-injection API.
Synthetic assembly/fault-injection tests establish verifier discrimination, not
hand-assembly game matches. `tests/switch_compatibility_probe.py` compares exact
legacy body/schema/manifest/proof identities against an unchanged toolkit.
Natural source positives cover both function origins and dispatch alignment
classes, short and long unsigned guards, and ordinary typed calls. Late status
and rebuild fixtures verify function-only output while preserving nonzero
external prefix bytes. These are finite verifier tests, not game-match credit.

### Explicit named-data buffer composition

`python tools/match.py --root <game> --owner-runtime-profile named-data-buffer-v1 <address>`
selects `elf-symbol-thumb-named-data-buffer-calls-v1`. Ordinary selection and all
older report schemas retain their existing behavior. The new selector requires
actual named object relocations and inspected buffer calls. It excludes caller
switches, local BL transfers, function literals, arithmetic runtimes and indirect
calls. Original sole-function Thumb ET_REL validation, exact typed relocation
linking, complete ROM comparison and fresh fixed-toolchain source/plausibility
replay use the existing complete-owner lifecycle.

The caller and each inspected dependency are at most 4096 bytes. At most eight
distinct dependency owners are inspected. Both indexes must identify each exact,
unique, nonoverlapping complete ROM span. Legacy numeric instruction-count
annotations may include pool words; the complete native CFG establishes the
actual reachable count and every byte's role. Malformed count annotations reject.

Buffer effects retain the existing register/stack alias engine. Its bounds,
alignment, saved-control-word protection, pointer-slot protection, joins,
constant-index rules, recursive-call limits and escape refusals remain active.
Inspected ordinary callees additionally require a complete closed graph and
byte partition. One extra callee form reuses the existing exact preloaded-switch
encoding, layout and complete read-only leaf CFG proof: an adjacent bounded
word table, its backward unsigned guard, verified predecessors, two reached
literal words and every case's complete effect paths. The alias engine follows
all proved table targets. Other indirect transfers still reject. The backward
guard can run indefinitely; termination is not proved.

The preloaded callee's object word is identified by exact ROM bytes and its
literal role. This does not invent a named data symbol or establish nonaliasing
or lifetime. Compiler-authored caller object words still require complete typed
named-data provenance. Callee records contain spans, structural descriptors and
hashes rather than serialized body hex. Reports bind the original caller ELF,
source/headers, both function indexes, object map, full ROM and every inspected
dependency. Fresh report replay, status and rebuild retain the explicit selector.

Focused native checks use `tests/test_named_data_buffer.py`, the fixed agbcc
compiler and `-mthumb-interwork -O2`. Set `FFTA_NAMED_BUFFER_TEST_ROM` to the
approved ROM and put the ARM tools on `PATH`. Its positive source is synthetic
C with a retained original ET_REL object; a dependency is the exact read-only
original switch body. This test proves verifier capability, not authorship or
admission of any actual game owner.

### Exact register callback buffer composition

`python tools/match.py --root <game> --owner-runtime-profile static-callback-buffer-v1 <address>`
selects `elf-symbol-thumb-static-callback-buffer-v1`. This separate selector
retains the complete original ELF, typed relocation, source/plausibility and
fresh report lifecycle. Default selection and earlier schemas are unchanged.
It requires an actual buffer callback resolved through an existing canonical
`_call_via_r0` through `_call_via_r12` identity proof. Exact aligned owner PC
words, register moves and zero-offset register copies can supply the target.
The odd Thumb address must identify a unique exact mapped owner; its actual
buffer effects replay through the existing alias engine. A known target alone
grants no memory, ABI preservation or termination assumption.

Every call clears all target/scalar facts, including callee-saved registers.
Branch joins retain only equal facts. Each callback context contains the target,
register constants, buffer aliases, incoming/protected slots and frame state;
effects are replayed separately without an effect cache. The explicit limits
are ten distinct dependency owners of at most 4096 bytes and 128 distinct call
contexts. Existing frame, alias, recursion and finite-switch limits still apply.
Reports bind all inspected owner hashes and canonical thunk identities, original
caller ELF, compiler configuration, source/headers, ROM and mapping inputs.

Unknown or overwritten targets, changed thunks, ambiguous owners, out-of-bounds
accesses, pointer escapes and protected descriptor-word reads still refuse.
This selector does not recover function targets from descriptor memory or infer
that any stored word survived aliasing writes or frame lifetime changes.
`tests/test_static_callback_buffer.py` uses natural synthetic C compiled with
original agbcc `-mthumb-interwork -O2`; it needs the fixed compiler and ARM tools
on `PATH`, and contains no extracted original ROM bodies or tables.

### Exact protected descriptor words

`--owner-runtime-profile protected-descriptor-word-v1` selects
`elf-symbol-thumb-protected-descriptor-word-v1`. The separate selector extends
the existing buffer states with exact aligned allocated-word pointer/scalar
values. Alias-addressed full-word loads can restore a pointer or static callback
target only from a surviving exact word. Actual verified SP changes translate
facts across nested calls; joins and all returns retain only identical facts.
Unknown-base writes clear word facts; overlapping partial writes cannot restore
them. Partial, unaligned, missing, expired and ambiguous pointer-word loads
refuse. Deallocation removes facts and allocation after deallocation refuses,
so recycled frame offsets cannot resurrect old values.

Every live callee-saved buffer alias must remain unwritten throughout the actual
callee graph, including nested calls. A push/pop restoration of that register is
conservatively outside this narrower identity proof. Callees are inspected even
when only word facts or such watched aliases cross the call. No ordinary ABI
summary supplies descriptor preservation. Register target facts still die at
calls. Contexts and reports bind word values, root frame, actual SP offset,
watched registers, aliases, typed literals, original ELF and existing fingerprints.
The limits are twelve dependency owners of at most 4096 bytes and 128 contexts;
existing profiles and their conditional ordinary-ABI behavior are unchanged.
Unknown block-write bases remain refused rather than granting an output bound.

`tests/test_protected_descriptor_word.py` uses natural original agbcc O2 source
and retained original ET_REL fixtures. Positive cases include nested read-only
calls and equal word values on both branches. Negatives cover changed callback
contexts, possible clobbers, unequal joins, unknown writes, partial/expired words,
frame reuse and unproved register preservation. No original game C or ROM body is
embedded in these tests.

### Watched switch preservation

`--owner-runtime-profile watched-switch-preservation-v1` is an explicit isolated
complete-owner profile, reported as `elf-symbol-thumb-watched-switch-preservation-v1`.
It extends protected descriptor-word replay only for a single call-free, read-only,
narrow Thumb switch callee already proved by the existing native guarded word-table
layout, complete CFG, stack/return verifier and complete byte partition. Every
finite case and default path is replayed by the existing bounded alias/word engine.
Caller-held watched aliases must be both unread and unwritten by that switch;
push/pop control words retain the native frame checks. This does not grant bounds
to implicit arguments or preservation from an ordinary ABI summary.

The profile retains exact word lifetimes, overlap invalidation, callback targets,
context budgets and source/ELF/ROM/map fingerprints. Reports include exact watched
contexts and hash identities for inspected switch tables, without extracted table
contents. It permits at most fourteen distinct inspected dependency owners of at most
4096 bytes each, and requires an actual watched switch context. Unknown transfers,
escaping targets, unknown writes, changed or ambiguous metadata, alias clobbers and
exhausted budgets remain refusals. All previous selectors keep their behavior.

Run `python -m unittest test_watched_switch_preservation -v` from `tests/` with the
fixed original compiler and ARM tools on PATH. The tests generate natural C and
retain original ET_REL objects and compiler assembly in their disk-backed fixture;
they contain no extracted game body or table.

Set `FFTA_WATCHED_SWITCH_TEST_ROM` to the approved ROM to run the one bounded
original-switch test; otherwise that test is explicitly skipped.

### Descriptor output stack origins

`--owner-runtime-profile descriptor-output-alias-v1` selects the isolated schema
`elf-symbol-thumb-descriptor-output-alias-v1`. It carries exact SP-derived aliases
and live allocated/saved-control words through inspected callee frames using the
existing buffer alias and protected descriptor-word engine. Frame metadata is part
of every effect state/join, and existing call contexts retain all words, targets,
origins and watched registers. Only exact aligned full-word stores/reloads restore
pointer provenance; partial, clobbered, expired and invalid-origin facts refuse.

For this selector, a complete closed CFG and byte partition precede actual-context
effects. A separate complete native frame/return check must pass before any
successful callee result is exported. Its structural-only call handling exports no
word or pointer identity; it cannot admit an owner without actual effect replay.
Failed effect prefixes can establish a precise next refusal while native ancestor
frame checks remain pending. Reports require actual callee stack-origin and pointer
word observations, and bind successful native frame replay counts as well as the
original ELF, source, ROM and mappings. The limits remain fourteen dependency
owners of at most 4096 bytes, 128 contexts and 4096 live stack bytes. All prior
selectors and defaults retain their behavior.

The selector does not add append/block-write semantics or infer an iteration count
or output capacity from a stack pointer. A known output base at an append store
still refuses those unproved effects. `tests/test_descriptor_output_alias.py` uses
natural fixed-O2 source with retained original ET_REL/assembly and tests unsafe
actual effects after structural inventory, a real final-native return refusal,
wrong origins, two contexts, partial/clobbered/control words and expired pointers.

### Single-word descriptor output stores

`--owner-runtime-profile descriptor-single-store-v1` selects the separate schema
`elf-symbol-thumb-descriptor-single-store-v1`. It extends descriptor output aliases
with exactly one low-register Thumb STMIA word and writeback. The existing native
STM recognizer validates the encoding, register list and complete aligned four-byte
frame bounds. The descriptor engine additionally requires a live allocated word,
tracks stored pointer/constant values, invalidates unknown overwritten values and
moves the exact base alias by four bytes. Base-in-list and multiple-register forms
refuse. Every context retains its full word, target, frame and alias facts; reports
also bind actual store observations and their before/after values.

Complete CFG/partition inspection precedes actual-context effects, and a complete
native frame/return check remains mandatory before any successful result escapes.
Its separate structural pass exports no memory identity and cannot admit an owner
without actual effect replay. The fourteen dependency owners, 4096-byte owner/live
stack limits and 128 contexts remain unchanged. Previous selectors retain their
behavior. A proved first word supplies no loop count or output capacity: differing
pointer offsets at joins, expired/clobbered origins and later out-of-frame accesses
still refuse. `tests/test_descriptor_single_store.py` uses natural fixed-O2 original
compiler output and tests those limits, exact unknown/pointer/constant word writes,
two contexts, unsupported lists and a successful store followed by a real native
return-proof failure.

### Exact descriptor alias alternatives

`--owner-runtime-profile descriptor-disjunctive-alias-v1` selects the separate
`elf-symbol-thumb-descriptor-disjunctive-alias-v1` schema. It extends single-word
descriptor stores with exact alias, constant, word and frame alternatives at joins.
Every reached alternative replays accesses, escapes, calls and returns; every exact
return alternative is expanded in its caller. Context, state, predecessor-edge and
return records are bound by the existing fresh source/ELF/ROM/map evidence. Complete
native frame/return checks remain mandatory. Reports require an actual unequal
alias join as well as the existing stack-origin, pointer-word and STMIA observations.

Each effects or native-frame replay permits at most 4096 exact states. Existing
owner, stack, dependency and context limits remain in force. Repeated exact states
close a fixed point; changing loop cursors must pass every real access bound or
refuse on the state/context limit. No trip count or termination fact is inferred.
Previous profiles retain their merge behavior and the acyclic profile retains its
DAG requirement. `tests/test_descriptor_disjunctive_alias.py` covers natural fixed-O2
ET_REL match/report/status replay, per-arm bounds and escapes, clobbered words,
saved slots, watched registers, final return proof, budgets and altered evidence.
