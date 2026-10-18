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
`issues: write`, `contents: read`, and `pull-requests: read`, checks out the trusted default branch,
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

Use `--force` only for an intentional history rewrite. The gate captures the
remote tip before validation and uses an explicit force-with-lease, so a remote
change during verification rejects the push rather than being overwritten.

## Layout it expects

```
<decomp repo>/
  baserom.bin          the base ROM (gitignored, never committed)
  config/              analysis output: coverage runs, functions, layout json
  symbols/             functions.txt, ffta.sym
  asm/  files/         the split
  src/  include/       decompiled C
  docs/match/          per-function match reports
```

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

### Fixed Thumb stack frames

The framed profiles additionally support 16-bit `sub sp, #N` / `add sp, #N`
and direct aligned word `ldr` / `str` accesses through SP. Allocations are
tracked alongside pushed registers. Deallocation cannot cross entry SP, all
returns must restore entry depth, and control-flow joins require equal depths.
Stores update the affected word's return-address provenance; loading an incoming
argument never establishes a return address. Stores outside the tracked frame
are rejected. Calls invalidate return-address facts in allocated local/outgoing
words, retaining pushed-save facts only under the existing ABI call assumption.

Register-controlled SP writes, stack-address materialization, indirect stack
aliases and unsupported access widths remain rejected. This is a bounded CFG
profile, not a general proof of memory safety or callee behavior.

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

External data relocations, cross-mode/ARM calls, `BLX`, indirect calls, local
helper functions, self/intra-function calls, tail calls, linker veneers and
extra allocated sections remain unsupported. These cases fail closed rather
than receiving a partial match. Existing relocation-free leaf functions retain
their original verification profile.

Reports carry a verification schema and a SHA-256 fingerprint of the source
and headers. `status.py` rejects legacy or stale reports; regenerate them with
`match.py`. Shared preprocessing inputs must live under `include/` or be `.h`
files under `src/`; dependencies outside the fingerprinted set are rejected.
`status.py --verify` recompiles against the local ROM and exits nonzero if any
function fails. Offline report checks are cached evidence, not fresh ROM checks.
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
