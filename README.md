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

The broker retains up to 64 recent receipts and at most 256 rows, accepts requests
up to 2 KiB, and limits its rendered issue body to 60,000 UTF-8 bytes. It evicts
older receipts as needed to fit that body, always retaining the newest result.
With archival enabled, it durably captures accepted receipts before eviction,
even when body pressure shortens the normal archive interval. Capacity errors
fail closed without dropping rows. An evicted receipt is unconfirmed,
not success. The visible table and hidden state must agree; edit neither while
the broker is running. This protocol does not grant contributors repository
write access or create separate reservation issues.

Rebase contribution branches onto current `origin/main` before opening a PR;
do not merge main into the contribution branch. See `AGENTS.md` for the rules.

## Publishing through the gate

Use `tools/push.py`, not a separate `git push`. `push.py --jobs N` and
`status.py --jobs N` accept 1 through 64 concurrent source checks; the default
remains one. Higher values are opt-in for hosts with sufficient CPU and memory.
Every source and publication check still runs, results retain source order, and
duplicate report destinations remain serialized. Decompilation mode verifies
history, tracked-file restrictions, fresh ROM matches, plausibility and reports.
Use `--check-only` to run the gate without publishing.

On fork-capable hosts, `--worker-processes N` instead runs complete verification
in 1 through 64 separate processes, including saved-report replay. Game publication
also uses these workers for its source and header plausibility checks. This is
opt-in, requires a single-threaded caller and `--jobs 1`, and applies only to
game verification (`status.py --verify` or the game push gate). Duplicate
destinations stay in one sequential group; results and errors retain source
order. Every original check still runs, and worker failures stop publication.
The default sequential and existing thread modes are unchanged.

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

For a new contribution branch, use `--create-from origin/main` with the intended
`--remote` and `--branch`. The destination must be absent. The gate fetches and
pins that named remote base, requires the current branch to contain it without
new merge commits, and retains all ordinary content and publication checks.
Its final push uses an empty expected-tip lease, so even a concurrent creation
at an ancestor commit is refused. This option cannot be combined with `--force`;
once the destination exists, use the ordinary publication command.

For an existing contribution branch repeatedly overtaken by disjoint upstream
matches, an explicit Linux-only live session can retain its own fresh native
results while the operator rebases between candidates:

```sh
python tools/push.py --repo ../fftadecomp --remote fork --branch contribution \
  --force --publication-session --session-base origin/main --worker-processes 4
```

Startup verifies the captured HEAD, then reads `verify FULL_COMMIT`,
`push FULL_COMMIT`, or `quit` from stdin. JSON event lines accompany ordinary
gate diagnostics. `verified` and `progress-stale` events include `status_block`, `status_assets`,
`fresh`, `reused`, and snapshot/runtime/ROM digests. After `progress-stale`, the
operator may write that block to the README and `docs/status.md`, write the
generated files at the paths in `status_assets`, commit them and submit the new HEAD. Only `verified` authorizes the session's `push` command.
The session does not rebase, edit game files, commit, or load saved success JSON.
After a successful real push, the session remains available for subsequent
additive candidates and advances its destination lease only to the exact pushed
commit. Every later push still checks the destination and upstream and uses an
atomic expected-tip lease. Dry runs retain the prior destination lease.
EOF or `quit` discards its memory. A new process verifies everything again.

Every candidate is archived and checks source/index uniqueness, complete-body
overlap, native plausibility, reports, and progress. Added functions compile
freshly. Changing an existing source or report invalidates all retained results;
removing a source/report or changing any shared committed input refuses reuse.
A newly added match may remove only its `Parked/ADDRESS/README.md` and
`Parked/ADDRESS/ADDRESS.c`. Context-dependent preprocessing (file-presence/time
macros and token synthesis) is refused in session mode, including spliced forms.
Headers, both indexes, mappings, profile artifacts, ROM, toolkit, Python,
capstone, selected compiler/binutils and libraries, search paths and environment
are bound before and after verification. Unknown/broad Python search paths,
committed symlinks and build inputs are refused. Pinning never substitutes old
JSON evidence for a current native verifier result.

Publication rechecks the exact branch HEAD, current linear upstream ancestry,
and both remote tips, then uses the original exact destination lease. A racing
destination update is rejected atomically by Git. The separate upstream branch
cannot be locked by that lease; an update after its last check can still require
another rebase and CI run. The ordinary one-shot gate remains unchanged.

## Reference environment for report replay

Reports from the runtime-bound profiles bind the environment that produced
them, not only the source and the ROM. These include addressed signed
runtime, complete-owner, unsigned divmod, palette, and others that embed an
environment block. Ordinary reports only re-check the compiled bytes. For the
runtime-bound profiles, replay (`status.py --verify`, and so the publication
gate) compares these exactly:

* `toolchain`: SHA-256 hashes of the resolved `$HOME/agbcc/gcc/agbcc`, `cpp`
  (which resolves to `x86_64-linux-gnu-cpp-13`), `arm-none-eabi-as`,
  `arm-none-eabi-objcopy` and `arm-none-eabi-ld`;
* `runtime`: the OS, `platform.release()` (the kernel), the machine, the
  Python version and executable hash, and the capstone version, binding and
  native-library hashes;
* for owner-admission profiles, the SHA-256 of the linked `f.elf`, whose
  layout follows the pinned `arm-none-eabi-ld` (for example its default max
  page size);
* the hashes of this toolkit's own tool sources (producer hashes).

A host that differs in any of these refuses otherwise valid reports from
those profiles, for example with `invalid saved ... report`. The frozen
`081475A4` lineage also requires the pinned tool hashes before compiling.
The environment is part of each report's versioned evidence: an older
reference environment does not automatically replay newer reports. See
[#78](https://github.com/shubshub/fftadecomp-kit/issues/78).

### Report environment recorded since 12 November 2026

Ubuntu 24.04.3 LTS (noble), Linux x86_64, with the following packages.
Use a VM or a host booted into the pinned kernel; a container shares its
host's kernel and cannot select the recorded kernel string independently.

| fingerprint | reference package |
|---|---|
| kernel `6.8.0-142-generic` | `linux-image-6.8.0-142-generic` (GA, `6.8.0-142.142`) |
| Python 3.12.3 | `python3.12-minimal 3.12.3-1ubuntu0.17` |
| capstone 5.0.6 | Ubuntu archive packages `python3-capstone` and `libcapstone5`, both `5.0.6-1`, **amd64** |
| `cpp` | `cpp-13-x86-64-linux-gnu 13.3.0-6ubuntu2~24.04.1` |
| `arm-none-eabi-*` | `binutils-arm-none-eabi 2.42-1ubuntu1+23` |
| agbcc | SHA-256 `63deeb6946e16e5add66cc173fcaa925f58ae56983d4d5a4649389bf8a23776f` |

Install the pinned system packages in a dedicated report environment. Keep
them and the boot selection fixed: changing Python or the running kernel
breaks replay. Superseded builds can leave the main archive;
`snapshot.ubuntu.com` keeps them. The agbcc build recipe below is unchanged.

```sh
V=3.12.3-1ubuntu0.17
sudo apt-get install -y linux-image-6.8.0-142-generic=6.8.0-142.142 \
    linux-modules-6.8.0-142-generic=6.8.0-142.142 python3.12-minimal=$V \
    libpython3.12-minimal=$V python3.12=$V libpython3.12-stdlib=$V \
    python3.12-venv=$V cpp cpp-13=13.3.0-6ubuntu2~24.04.1 \
    cpp-13-x86-64-linux-gnu=13.3.0-6ubuntu2~24.04.1 \
    binutils-arm-none-eabi=2.42-1ubuntu1+23
readlink -f "$(command -v cpp)"   # expect /usr/bin/x86_64-linux-gnu-cpp-13
```

Boot that kernel and confirm `uname -r` is `6.8.0-142-generic`.

**Capstone comes from Ubuntu's `.deb` payloads, not PyPI.** Neither the PyPI
5.0.6 wheel nor a local source build reproduces these fingerprints. The
Ubuntu binding loads `libcapstone.so.5` by soname; the library is identified
from the process's actual loaded mappings. Noble's own default Capstone is
4.x. Extract the exact 5.0.6 packages into a separate directory instead of
changing the system's package sources or replacing its libraries:

```sh
CAPSTONE_ROOT="$HOME/ffta-capstone-5.0.6"
set -e
mkdir -p "$CAPSTONE_ROOT"
cd "$CAPSTONE_ROOT"
ARCHIVE=https://archive.ubuntu.com/ubuntu/pool/universe/c/capstone
curl -fLO "$ARCHIVE/libcapstone5_5.0.6-1_amd64.deb"
curl -fLO "$ARCHIVE/python3-capstone_5.0.6-1_amd64.deb"
sha256sum -c <<'EOF'
f3355618bf327291a5e543e6d8c7a22f2afb98b999c09e6a2ba1fae6e6e9af81  libcapstone5_5.0.6-1_amd64.deb
65c0a1d223a7b74eb4833f213925b2d93ebc379b7de3009885ff28d02de715b0  python3-capstone_5.0.6-1_amd64.deb
EOF
dpkg-deb -x libcapstone5_5.0.6-1_amd64.deb "$CAPSTONE_ROOT/root"
dpkg-deb -x python3-capstone_5.0.6-1_amd64.deb "$CAPSTONE_ROOT/root"
export PYTHONPATH="$CAPSTONE_ROOT/root/usr/lib/python3/dist-packages${PYTHONPATH:+:$PYTHONPATH}"
export LD_LIBRARY_PATH="$CAPSTONE_ROOT/root/usr/lib/x86_64-linux-gnu${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
sha256sum -c <<'EOF'
d08add40b3fb7a6d61c649a9cda8d21dcb660f69a1b78e9c75937eee20c4afdb  root/usr/lib/python3/dist-packages/capstone/__init__.py
1b261c94046e905b77baa1ad37d8958f8f8923acdc2aa392568035e9909fa84d  root/usr/lib/x86_64-linux-gnu/libcapstone.so.5
EOF
```

Both packages are `amd64`, including the Python binding. The library declares
only `libc6 (>= 2.14)` as a dependency and runs on noble. These extracted
payloads were compared byte for byte with the report-producing environment;
a fresh Python process using them reproduced every field returned by
`addressed_signed_runtime_profile.runtime_fingerprint()` and
`toolchain_fingerprint()`. This checks environment reproduction, not a new
full-game audit or compatibility with a different toolkit revision.

From the kit checkout, with the variables above exported, inspect the actual
loaded environment before attempting report replay:

```sh
PYTHONPATH="$PWD/tools:$PYTHONPATH" /usr/bin/python3.12 -c \
    'import json; from addressed_signed_runtime_profile import runtime_fingerprint; print(json.dumps(runtime_fingerprint(), indent=2))'
```

The Python executable hash is
`e50d468e8b0adfb05733f5b87b3cff34829c4a8c1aea50c865aa8bdfe4bb150f`.
The binding/native hashes must equal the payload hashes above. Existing
Python dependencies such as pyelftools are still required; keep any venv
based on this exact system Python.

### Historical report environment, 8 November 2026

The previous full `status.py --verify` result (zero problems, decomp
`15092737a7`, kit `630fde57`) used noble with HWE kernel
`6.17.0-14-generic` (`6.17.0-14.14~24.04.1`) and the PyPI
`capstone==5.0.3` manylinux wheel. Python, cpp, ARM binutils and agbcc had
the same pins as above. That historical result remains valid for that
snapshot; it does not establish replay of the newer reports with the old
kernel and Capstone. Preserve old evidence instead of relabeling its runtime.

### Reproducing the reference agbcc

The reference agbcc is **not** what `tools/bootstrap.sh` produces on noble.
Building with `-g` records the host compiler and the absolute build directory,
so the binary differs between hosts. It reproduces bit for bit when built in
Ubuntu 25.10 (questing) from the 2026-10-30 archive snapshot, at
`/home/user/agbcc`. The build host needs `debootstrap` and `ubuntu-keyring`.

```sh
SNAP=https://snapshot.ubuntu.com/ubuntu/20261030T000000Z
sudo debootstrap --variant=buildd questing /srv/questing "$SNAP"
sudo tee /srv/questing/etc/apt/sources.list >/dev/null <<EOF
deb $SNAP questing main universe
deb $SNAP questing-updates main universe
deb $SNAP questing-security main universe
EOF
sudo mount -t proc proc /srv/questing/proc
sudo chroot /srv/questing env DEBIAN_FRONTEND=noninteractive sh -c '
    apt-get update && apt-get -y dist-upgrade &&
    apt-get -y install git build-essential && useradd -m user'
sudo chroot /srv/questing su - user -c '
    git clone https://github.com/pret/agbcc.git ~/agbcc &&
    cd ~/agbcc && git checkout da598c1 && make -C gcc normal -j1 &&
    echo "63deeb6946e16e5add66cc173fcaa925f58ae56983d4d5a4649389bf8a23776f  gcc/agbcc" |
    sha256sum -c'
sudo umount /srv/questing/proc
```

The `old-agbcc-O2-v1` compiler comes from the same chroot, source commit and
path: build it in a fresh clone with `make -C gcc old -j1` and install
`gcc/old_agbcc` at `$HOME/agbcc/gcc/old_agbcc`. Built so, it reproduces bit
for bit as SHA-256
`88ebbb5b6167ab979f1652e599a5fb134eabe9a93f43122ca019da77a32c29f1`; a
following `make -C gcc clean && make -C gcc normal -j1` in that tree gives
the reference `agbcc` above.

That chroot provides `gcc-15 15.2.0-4ubuntu4`, `libc6-dev 2.42-0ubuntu3.1`,
`binutils-x86-64-linux-gnu 2.45-7ubuntu1.2` and `make 4.4.1-2`. The binary
needs only `libc.so.6` and runs on the noble report host. Install it at
`$HOME/agbcc/gcc/agbcc` for whichever user runs the tools. Reports record that
unexpanded string and the binary's hash, so the report host's user name does
not matter. `/home/user` matters only at build time, because `-g` embeds the
build directory.

Producer hashes are environment-independent. Every toolkit change that edits
a tool file invalidates the reports bound to it, on every host, until they
are regenerated with `status.py --write --verify`. Pair kit bumps with that
regeneration.

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

In Thumb mode every reached instruction must also be one the ARM7TDMI
executes (kit `#180`). Capstone's Thumb decoder reads Thumb-2 and ARMv5/v6
encodings too, so the walk refuses a reached instruction that is neither a
16-bit ARMv4T encoding nor a BL pair whose halves are exactly the `11110`
prefix and the `11111` suffix. That excludes `bkpt`, `udf`, `cps`, `setend`,
`rev`, `sxt`/`uxt`, `cbz`, `it`, the hint instructions (the only `nop` is
`46c0`), a hi-register `mov`/`add`/`cmp` encoding of two low registers, `bx`
with a nonzero should-be-zero bit, an `stmia` whose writeback base is in the
list but not lowest, and every other 32-bit decode. `svc` and `blx` keep their
older refusals. The complete-owner graph (`owner_graph_profile.graph`) applies
the same check (`tools/armv4t.py`) to every instruction of its code ranges, so
the admission paths that replay that graph without the base walk are held to
it as well. Limits: the rule is about encodings, so it says nothing about what
an admitted instruction does; it covers these two decodes, the walks that
consume their instructions, and the dead-alias, dead-argument and switch-thunk
scans that call the checker themselves, so a profile that decodes with its own
Capstone handle and neither runs the base walk nor replays the owner graph
over the same bytes must check its own forms; ARM-mode code is not checked;
and bytes no walk reaches are not checked. The checker decides conditions and
flag setting from the encoding bits, because Capstone carries Thumb-2 `it`
state across one multi-instruction decode; an item must still come from a
decode that starts at that instruction, or from a multi-instruction decode
whose preceding items were all checked (the owner graph and the dead-argument
scan decode a range this way; `it` is itself refused, so no such state reaches
a later item).

Unconditional 16-bit Thumb register moves preserve a proven original return
address, including copies restored to LR. Overwrites discard that fact, joins
retain it only when all incoming paths agree, and calls still invalidate
caller-clobbered registers. Arithmetic, unknown inputs and wider or conditional
moves do not establish return-address provenance.

### Plain report fields and labels

The plain schemas are `elf-symbol-cfg-leaf-v2`, `elf-symbol-thumb-frame-v1`,
`elf-symbol-thumb-calls-v1`, `elf-symbol-thumb-frame-calls-v1`,
`elf-symbol-thumb-data-v1`, `elf-symbol-thumb-frame-data-v1` and
`elf-symbol-thumb-frame-buffer-calls-v1`/`-v2`. A saved report for one of them
must hold exactly the field lines that `match.py` writes for that schema (kit
`#247`, `tools/plain_report_fields.py`). A field line is any bullet: a line
whose first non-blank character (Unicode blanks included) is `*`, `-` or `+`
followed by a blank. After the allowlisted volatile records are removed, replay
refuses a report in which:

1. a field line uses a prefix the writer does not emit for the claimed schema.
   Only the writer's own `* name: ` form at the start of a line can match, so
   indented, `-`, `+` and non-breaking-space bullets refuse. A plausible
   report has no findings list, so the writer emits no other bullet;
2. a field is missing, or appears more than once. On the buffer schemas, the
   other `* buffer ` lines (loop replay, and the BIOS, copy-helper and
   switch-callee summary lines) are exempt: they may repeat, because the
   buffer proof requires them to equal its recomputed lines exactly and in
   order. The two self-call lines appear together or not at all.
   `* compiler:` is required, even though `library_units` alone admits a
   report without it;
3. `* source:` does not name the file `match.py` compiles for this address
   (`src/<ADDR>.c`, else the first `<ADDR>.c` under `src/` in sorted order),
   or `* hand-asm allow list:` is neither `not listed` nor `listed (...)`.
   The source fingerprint already binds that path, so moving a source into a
   module folder needs a regenerated report, as before; the regenerated report
   names the new folder. The hand-asm reason is checked for form only;
4. the field lines are out of the writer's order, or any of them follows the
   `**MATCH` verdict line.

Replay also derives each label from the walk it already runs, as `match.py`
does:

* a `frame` schema requires that the reached Thumb code uses the stack frame,
  and any other plain schema requires that it does not;
* a call schema, or the call summary on a data schema, requires a reached BL
  that leaves the function or re-enters its entry, and any other label
  requires that there is none;
* a data schema requires a literal word that a data relocation could occupy:
  a reached `ldr rd, [pc, #imm]` must load a word inside the function whose
  value lies outside it. `match.py` binds data only through such a word, and
  the walk admits no other PC-relative access.

The addressed signed-remainder path compares the frame label in its own source
check.

**Limit:** replay cannot see relocations, so it cannot tell a named data
literal from a raw constant. In both directions, a relabelled data label still
replays:

* **Downgrade.** A data report relabelled to the call or leaf schema, with its
  data-symbol line removed, replays if the bytes also verify without the data
  map.
* **Upgrade.** A call or leaf report relabelled to a data schema, with a
  current data-symbol line added, replays if its body loads a literal word
  from outside the function, such as a hardware address or another constant.
  A body that loads no such word is refused.

The complete fix is for `status.py --verify` to diff the regenerated report
against the saved one; that is follow-up work for kit `#247`.

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
are rejected, and so are stores into pushed words: a direct `str` must land in a
word allocated by `sub sp` on every incoming path, never in a saved register or
the saved return address (`stack-frame store overlaps a saved register or
return-address word`). The walk does not otherwise prove that R4-R11 are
restored: popped registers are not compared with pushed ones. Calls invalidate
return-address facts in allocated local/outgoing words, retaining pushed-save
facts only under the existing ABI call assumption.

Local-array addresses formed by 16-bit register moves and constant additions
or subtractions are tracked relative to entry SP. Aligned byte, halfword and
word loads through these aliases must stay inside the allocated/pushed frame;
stores must stay inside allocated local words, whether the alias was formed in
the owner or returned by an inspected callee (`stack-alias store overlaps a
saved register or return-address word`). Partial stores invalidate the affected
word's return-address fact.
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
each word must be an allocated local word. Each store applies the scalar store's
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

Thumb has no SP-relative byte or halfword load. When a frame is too large for
the `ldrb`/`ldrh` offset range, agbcc reads a narrow fifth or later argument
with `add Rd, sp, #imm; ldrb Rd, [Rd, #imm]` (or `ldrh`). The ordinary
direct-call, data and buffer-call frame profiles accept exactly this pair: a
16-bit `add Rd, sp, #imm` that addresses entry SP or above, immediately followed
by `ldrb` or `ldrh` with that same low register as base and destination. The
load overwrites `Rd`, so the address never becomes an alias and cannot reach a
join, call, store or return. The bytes read must lie in one aligned incoming
word that a direct `ldr Rt, [sp, #imm]` at the same depth could read, which
bounds the read to SP+1020. The pair therefore reads nothing that the existing
direct incoming reads cannot. As for those, the argument count, caller
allocation and value are not proved. Every other use of such an address still
fails with "stack alias arithmetic leaves the tracked frame". That includes a
store, a word or signed load, another destination or base register, an
intervening instruction or arithmetic. Stores into the incoming area are still
rejected. The addressed, owner, switch, function-address, runtime and inventory
profiles keep their existing refusal. Frame schemas are unchanged, and saved
reports replay through the same rule. A verifier without it refuses a report
that uses the pair.

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
helper functions, intra-function and non-entry calls, tail calls, linker veneers
and extra allocated sections remain unsupported. These cases fail closed rather
than receiving a partial match. Existing relocation-free leaf functions retain
their original verification profile.

#### Self calls

A `bl` to the function's own exact entry is admitted on this plain direct-call
path only. The relocation must name the function's own complete defined global
symbol (the one being matched and linked, at offset zero), so the call binds to
the same verified bytes and adds no unproved callee. The linker resolves it
against that symbol and the linked `BL` must still decode to the exact entry.
The call is summarised like any other ordinary call, and the same verifier
proves the body that makes the summary hold. This is partial correctness: there
is no termination or recursion-depth theorem. Refused: a second function in
the object, a self address taken as data (a literal-pool word naming the
function), non-entry self targets, and any combination with the division,
float, switch, function-address, thunk (`_call_via_rN`), buffer or owner
selectors. Mutual or indirect recursion through external or register calls is
not a self call: it is covered only by the ordinary call summary, as before.
Framed functions are not excluded; a self call in a frame-calls profile is
admitted unless another proof (for example a stack alias crossing a call) fails.
A report that uses it keeps its normal schema and adds two
lines, `* self calls:` (a fixed summary) and `* self call sites:` (the sorted
site offsets as canonical JSON). Replay accepts a self call only when both
lines are present and the offsets equal the `bl` sites the bytes reproduce, so a
report that drops or edits them is rejected, and a report without them is
rejected if the bytes contain a self call.

Selector refusals (a `ValueError`; `refusal.Refusal` is the subclass used for
the clean ones) are reported by `match.py` on the command line as
`refused: <reason>` (`error (<type>): <reason>` for any other `ValueError`)
with status 1, not as a traceback. `FFTA_TRACEBACK=1` restores the traceback
(unset, empty and `0` leave it off).

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
stack arguments or LR. A caller that also has named data relocations is
verified by the version-2 proof below together with its typed data literals
(see "Typed named data beside buffer calls"); the explicit
`named-data-buffer-v1` selector is a separate composition.

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
either path. Different possible offsets for the same register cannot be
joined; the callee is then replayed path by path (below). Inspected callees may return buffer aliases in `r0`–`r3` or `r12`;
the caller receives those possible aliases instead of treating those registers
as pointer-free. Subsequent uses require the same bounds and escape checks.
Aliases in unrestored callee-saved registers, local-frame pointer returns,
control-register aliases and unproven return addresses are rejected.

The matcher tries the existing profiles first. A successful version-2 retry
requires an inspected buffer call and uses its own profile and summary; it does
not broaden version-1 evidence. The complete caller and inspected ROM spans are
bound and replayed as above. The ordinary ABI assumptions still apply, and
block transfers, interrupts (other than the summarised BIOS wrappers below) and
indirect-call dependencies remain unsupported.
Named data relocations compose with this proof only under the separate schema
described in "Typed named data beside buffer calls". A proved output-buffer call alone does not
admit a caller whose later stale-argument or local-buffer calls cannot be proved.

### Bounded loop replay of buffer callees

A callee that stores `*out++` inside a loop reaches its loop head with different
offsets for the same pointer register, and the join above refuses it. When that
join conflict is the only obstacle (any difference between the two incoming alias
maps at equal depth, including a register present on only one path), the callee is replayed path by path instead
of joined: every reachable state is kept separately, so each store is checked at
its exact offset against the caller's allocated local words with the same
alignment, saved-slot, overlap and escape rules. A replayed path that reaches a
store outside the allocation refuses, naming the store and caller SP offset:

```
buffer callee 0x0812E4F4: bounded loop replay at 0x0812E540: 2-byte strh at caller sp+4: buffer access is unaligned or outside allocated local words
```

Loops end only through exact facts. The replay tracks R0-R12 values produced by
unconditional 16-bit `mov`, `add` and `sub` of known values and immediates (32-bit
wrap), and the operand pair of the last `cmp` whose operands are both known.
A conditional branch with known flags follows only its taken or fallthrough
side; the other edge is pruned as infeasible, and its instructions are never
analysed, so a store that would be refused there is not. Each pruned edge (site,
condition, flag operands, side) is bound into the evidence. Any other write forgets the register; any other flag-setting instruction,
call or software interrupt forgets the flags; a call forgets R0-R3, R12 and LR.
After a call to an inspected buffer callee, every R4-R11 register that callee,
or an inspected callee of it, writes anywhere (including its restoring pops) is
also forgotten. Values in R4-R11 survive uninspected calls only under the
returning-ABI premise this proof already uses for aliases, so a callee that
breaks the premise (for example by zeroing a counter and never restoring it) is
admitted. This is not proved in general: every un-inspected call target whose R4-R11
survival the replay relied on, and the register, is recorded and bound by the
fingerprint, and the report states it in a `* buffer loop replay:` line (one per
replayed callee) as `proved` or `trusted`. `callee_preservation_profile.py` proves
R7 and R8 for the callees of `0812E4F4` (`080C7EA4`, `080CA7A4` and its callee
`080C95A8`) from pinned bytes: the span is decoded by reachability from the
entry, no reached instruction writes them, code may not reach a literal word, a
dispatch table or the end of the span, and PC is written only by `B`/`BL`,
`bx lr`, `pop {..., pc}`, `pop {rX}` + `bx rX` (after a `push {..., lr}`) and the
agbcc switch idiom, whose `cmp` bound must equal the pinned table length. Any
unpinned call, interrupt or other indirect jump refuses. Everything else stays
`trusted`. A callee left `trusted` is still admitted: only the disclosure line
changes, nothing is refused because of it. The report check requires exactly the
lines the recomputed proof states, refuses an indented or unrecognised `* buffer`
line, and none for a proof without a replay.
Nothing is widened: if no exact counter bounds the loop, the pointer
keeps moving until a store leaves the buffer, or the replay exhausts its budget
(4,096 states per callee, 65,536 per proof) and refuses. The per-proof counter
only increases (states are never refunded) and joined passes, including nested
ones, are not counted. Different stack depths
at the same address still refuse.

Replay is opt-in per class (not inherited) and per construction
(`loop_replay=True`, passed only by the frame-buffer and function-buffer
producers, the two typed-data buffer producers, the `named-data-buffer-v1`
selector and their report checks): only
the plain register and stack buffer proofs (`BufferCallProof`,
`FunctionBufferCallProof`) and the exact named-data buffer proof
(`NamedDataBufferProof`) enable it, and not when they carry a discarded-scratch
or BIOS-fill policy. Every profile subclass keeps the join refusal. Records of
the aborted joined pass are discarded before the replay, including the
named-data proof's own dependency records and budget charges. Only replayed
callees change the evidence: the buffer proof fingerprint
(`bounded-loop-replay-v2`) then also binds each replayed
callee's call site, argument offsets, the trusted (call target, register) pairs,
the pruned branch edges and the exact set of caller-frame bytes written by its own
stores (stores of nested callees that are not replayed are checked but not
listed), so report replay recomputes it. Proofs without a replay keep their
previous fingerprint.

The ROM bounds a loop's trip count, not the data that decides each iteration.
`0812E4F4` runs five iterations and may store up to five halfwords
(`out[0..5)`, ten bytes). Its stack callers pass a `u16[2]`; when that array is
the top allocated word (`0812F5E0`, `0812C8DC`, `080BDECC` and others) the third
store would reach a saved register and the caller is refused. That at most two
entries pass the filter is a property of game data and is not proved here. A
caller with ten allocated bytes from the array (`080BE8E0`, array at `sp+0x14` of
a 44-byte frame) is admitted, and the bound write set then covers its spilled
locals at `sp+0x18` and `sp+0x1C`. As stated above, the bounds are allocated
stack words, not C objects.

### GBA BIOS wrappers in plain buffer walks

The plain register and stack buffer proofs (`elf-symbol-thumb-frame-buffer-calls-v1`
and `-v2`, and their report checks) summarise eight exact BIOS SWI wrappers
instead of walking them; `tools/bios_wrapper_summary_profile.py` holds the rule.
A wrapper is reached by such a walk only when a tracked local pointer is live at
the call, in a register or as a pointer-bearing frame word. Without the summary
the walk reaches the `svc` and refuses (`non-leaf calls and interrupts require
linked CFG verification`). A wrapper call with no live pointer stays an ordinary
ABI call and is not recorded. No owner, addressed, function-literal or switch
selector uses the summary: it is set only by `BufferCallProof(...,
bios_wrappers=True)`, which refuses any subclass.

| entry | bytes | SWI | routine | kind |
|---|---|---|---|---|
| `08141860` | `0adf7047` | 0x0A | ArcTan2 | scalar |
| `08141870` | `06df7047` | 0x06 | Div | scalar |
| `08141874` | `06df081c7047` | 0x06 | Div, remainder in R0 | scalar |
| `0814187C` | `07df081c7047` | 0x07 | DivArm, remainder in R0 | scalar |
| `08141898` | `08df7047` | 0x08 | Sqrt | scalar |
| `0814186C` | `0bdf7047` | 0x0B | CpuSet | memory |
| `08141868` | `0cdf7047` | 0x0C | CpuFastSet | memory |
| `08141864` | `0edf7047` | 0x0E | BgAffineSet | memory |

Every summarised call must meet these obligations; each refusal names the wrapper
(`buffer callee 0x0814186C: ...`):

1. The call has an actual site, and the context is the plain proof (no word
   provenance, callee frames, single-word stores or forwarded slots): `BIOS
   wrapper summary requires an actual direct call site`, `BIOS wrapper summaries
   exclude word-provenance, callee-frame and forwarded-slot contexts`.
2. The target's complete, unique, non-overlapping indexed Thumb row holds exactly
   the bytes above: `BIOS <routine> summary requires the exact indexed wrapper
   bytes`. An interior address, a thunk or a literal is not a wrapper entry and is
   walked (and refused) as before.
3. Scalar wrappers, at any walk depth: no tracked local pointer in R0-R3, R12 or LR
   (`scalar BIOS wrapper refuses a tracked local pointer in R0-R3, R12 or LR`).
   Pointer-bearing frame words are checked to be allocated local words and left
   as they are.
4. Memory wrappers, only at the owner's own call (`BIOS memory wrapper is
   summarised only at the owner's own call`), with local pointers only in R0, the
   source, and R1, the destination (`BIOS memory wrapper refuses a local pointer
   outside R0 and R1`).
5. The memory obligations are discharged when the owner's CFG is complete. R2 is
   known only from `bios_cpuset_fill_profile.prove_bits` over the verifier's own
   owner CFG, with the zero-extension rules of "Zero-extended CpuSet fill
   controls". The spans follow the layout the kit states for CpuSet: count is bits
   0-20, the unit is 4 bytes if bit 26 is set and 2 otherwise, bit 24 is a fill
   from one source unit. CpuFastSet moves 32-bit units in blocks of eight.
   BgAffineSet reads `count` 20-byte records and writes `count` 16-byte records.
   * A local fill source (bit 24 set on every path) with no local destination is
     one unit: 2 bytes when bit 26 is known clear (CpuSet), otherwise one aligned
     word.
   * A local destination, or a local source not proved to be a fill source, needs
     the whole control word (`BIOS copy source or local destination requires the
     whole control word on every path`), no reserved bit (`BIOS control word sets
     a reserved bit`), and a count of at least 1 that, for CpuFastSet, is a
     multiple of 8 (`BIOS control count is zero or not a multiple of eight
     CpuFastSet words`). BgAffineSet needs an exact count in 1..255 (`BgAffineSet
     count is not a proven constant in 1..255`) and word-aligned records.
   * Every unit is an aligned access inside allocated local words (`buffer access
     is unaligned or outside allocated local words`). A source span holds no
     pointer-bearing word; a destination span holds no pointer-bearing word and no
     word carrying the return address (`BIOS source|destination span overlaps a
     pointer-bearing local word`, `... a return-carrying local word`). A local
     source and a local destination are disjoint (`BIOS local source and
     destination overlap`).
   * Each register that carried a local pointer into the call is written before
     any read, call, interrupt or return on every path from the call
     (`match.stack_alias_overwritten_before_use`; `R<n> carried a local pointer
     into BIOS <routine> and is not written before any read, call or return`).
6. The call returns no alias; R0-R3, R12 and the flags are unknown scalars
   afterwards. A destination span holds no word the walk keeps a fact about, so no
   fact is invalidated.

The behaviour of the routines is a premise, as in every BIOS contract of the kit
(GBATEK, "BIOS Functions"): each routine returns to its wrapper, preserves SP, and
reads and writes caller memory only through the spans its documented arguments
describe. Two further premises are trusted, not proved, because GBATEK does not
document them: no routine leaves an address of the caller frame in any register
except, for a memory routine, R0 or R1 when that register carried one in; and
R4-R11 are preserved (a loop replay that relies on that lists the wrapper as
`trusted`). R2's bits are proved, as in `BiosFillProof`, with known R4-R11 bits
surviving the owner's other calls under the conditional returning ABI. No numeric
result, termination, source initialization, physical readability, or extent or
nonalias of a non-local pointer is claimed: an external pointer gets no claim.

Evidence: each applied summary is recorded. The report states, in this order:

```
* buffer BIOS summaries: `gba-bios-swi-wrapper-summaries-v1` <the contract>
* buffer BIOS premise: GBATEK (BIOS Functions): each routine returns to its wrapper, preserves SP, ...
* buffer BIOS premise: no routine leaves an address of the caller frame in any register except, ...
* buffer BIOS premise: R4-R11 are preserved across each summarised call; nothing of the routine is inspected, so this is trusted, not proved
* buffer BIOS manifest: `<canonical JSON>`
```

Each premise is on its own line, verbatim. The manifest holds the wrappers used
and the sites: scalar sites with depth, untouched incoming slots and
pointer-bearing words; memory sites with R2's known bits, the source and
destination spans, unit, count and the killed registers, and then also the bit
rules. The buffer proof fingerprint binds the wrapper bytes as dependencies and
a digest of the manifest, the contract and the premises. Report replay
recomputes the five lines and the fingerprint; a proof that applied no summary
has none of them and keeps its earlier fingerprint, so no existing report
changes. The report checks that refuse `* buffer loop replay` lines also refuse
`* buffer BIOS` lines.

### The pinned copy helper in the default stack buffer walk

A local buffer passed to the 98-byte copy helper `func_081443FC` used to stop
the version-2 walk inside the helper, at its alignment test (`orrs r0, r5` at
`0x0814440A`), which reads the pointer's value. The walk explores that path for
every count, so every call with a local alias in R0 or R1 refused:

```
buffer callee 0x081443FC: unsupported buffer pointer use or escape
```

The version-2 proof that `match.py` builds on its default path, and that report
replay rebuilds, now summarises such a call instead of walking it. Only that
plain proof does: the constructor keyword `copy_helper_index` is refused for any
subclass and for version 1, and no selector or profile proof is changed
(`named-data-buffer-rom-table-copy-v1` keeps its own summary). The summary
applies at a direct `bl` to the helper from a walk of a function's own frame,
the owner's or an inspected callee's, when R0 or R1 holds a local alias, which
is exactly where the walk refused. The alias pass that follows a caller's
pointer into a callee does not carry the count, so a callee that forwards the
caller's pointer to the helper is still walked and refused. A call with no
alias in R0 or R1 is walked as before. Each obligation refuses with
`buffer callee 0x081443FC: ...`:

1. The helper is authenticated as the ROM-table-copy profile does it (the
   indexed 98-byte span in both indexes, its SHA-256, the byte-loop path, the
   closed CFG, no register above R5 written), and the mapped span the walk
   would enter is that body.
2. R2 holds an exact constant count from 1 to 256 (`copy summary count must be
   an exact constant from 1 to 256`); the walk's constants come from `mov`.
3. No alias is in R2 or LR (`copy summary refuses a local pointer in R2 or LR`),
   and every alias argument and pointer-bearing word passes the ordinary
   pointer check.
4. The helper's effect for that count is proved on every run by executing its
   pinned bytes on a symbolic Thumb interpreter, once for each of the 16
   (destination mod 4, source mod 4) pairs. Destination, source and stack are
   separate symbolic regions known only by their low address bits; memory and
   entry registers are opaque. A run refuses if a branch reads data or an
   unknown pointer bit, if an access leaves `[dst, dst+n)`, `[src, src+n)` or
   the helper's own three save words below SP, if a pointer or a non-source
   value is stored, or if the helper does not return through its saved entry
   LR. It must end with each source byte at its destination offset, SP, LR and
   R4-R12 restored, R0 = dst, R1 = the entry LR, R2 = -1 and R3 = src+n, and the
   entry R3 and R12 never read and R12 never written. Each count actually used
   is checked exactly, so neither a cap at 15 nor an inductive argument over the
   16-byte loop is needed. The interpreter decodes only the small subset of
   ARMv4T encodings the pinned bytes use and refuses any other, so a body that
   differs is refused; the kit already executes this helper symbolically for a
   fixed aligned 80-byte copy and for the four small byte-path counts, but not
   for an arbitrary count under every alignment, which the caller-side check
   needs. The test module cross-checks the interpreter against the kit's
   independent concrete executor on concrete inputs.
5. A local destination lies in allocated local words (`buffer access is
   unaligned or outside allocated local words`) and holds no pointer-bearing or
   return-carrying word (`copy destination overlaps a pointer-bearing or
   return-carrying word`).
6. A local source lies in allocated local words and holds no pointer-bearing
   word (`copy source overlaps a pointer-bearing word`), because copying one
   would make an untracked pointer.
7. A local source and destination are disjoint (`copy source and destination
   overlap`).
8. The proof carries no word facts and no word-provenance, callee-frame,
   single-store, forwarded-slot, exact-alternative, BIOS, scratch or runtime
   context (`copy summary excludes word-provenance, callee-frame and other
   summary contexts`).

After the call, R0 is the destination alias, R3 is the alias src+n when the
source is local, and an alias in R12 is kept; all three are then checked like
any alias. An alias in R3 at the call is dropped, since the helper never
reads it. R1, R2 and the flags are unknown, as after any call. Pointer-bearing
words outside the destination keep their facts: the helper reads no caller
stack word.

Every distinct site observation is recorded: count, destination, source,
returned and dropped aliases, pointer-bearing words and stack-passed
pointers, with the helper facts and each count's execution digest. They are
bound into the buffer proof fingerprint only when a call was summarised, so
every other fingerprint is unchanged, and each observation is one report line:

```
* buffer copy summary: `pinned-copy-helper-summary-v1` 0x081443FC at 0x080BDABE: count 4, destination sp+0, source external; returns r0=sp+0; drops none; pointer words 0; contract 16 cases 46288f61e9739efd
```

Report replay recomputes the proof, the lines and the fingerprint, and reads
`symbols/functions.txt` for the helper identity. Not proved: that a source or
destination that is not local is readable or writable, or that it does not
overlap the live frame, the helper's save words or code (the walk's standing
premise for every untracked pointer); physical stack, lifetime and termination
beyond the bounded run are not proved either.

The typed-data proof beside the version-2 walk (`data_buffer_profile`) builds
the same plain proof for its plain path, and takes the same index from
`match.py` and from its own replay, so a caller with typed object words is
summarised the same way; its report carries and replays the same lines. Its
function-literal path builds a `FunctionBufferCallProof` and still refuses
the call.

### Jump-table callees in the default stack buffer walk

A local pointer that reaches a callee dispatching through an agbcc jump table
used to stop the version-2 walk at the dispatch, which it could not resolve:

```
buffer callee 0x080C9208: unresolved program-counter write
```

The layout is already proved by the `bounded-buffer-guarded-switch-v1` family's
`GuardedSwitchBufferProof.inspect`. The version-2 proof that `match.py` builds on
its default path, and that report replay rebuilds, now uses that same proof for
such a callee. Only that plain proof does: the constructor keyword
`switch_callee_index` is refused for any subclass and for version 1, and no
selector or profile proof changes. The rule is the existing one, reused
unchanged: when `analyze.refine_function` finds a word switch in an inspected
callee, inspection is delegated to a `GuardedSwitchBufferProof` built on the same
ROM, mapping and index, as `NamedDataBufferProof.inspect` builds its delegate,
but without that path's refusal of calls: direct calls and two-constant tables
are admitted, as under `bounded-buffer-guarded-switch-v1`. Its `inspect`
requires one table with zero or two interposed
scalar words; the canonical unsigned-guarded dispatch, a bound covering the
table and every case a forward offset inside the callee; no local BL control and
every direct call a canonical indexed function; and the callee CFG verified with
the table words as switch relocations and equal to the complete owner graph. It
supplies the verified instructions and the dispatch's finite successors, and the
plain proof's own alias walk then follows every case under its unchanged access,
escape, join and return rules. The selectors' span checks (owner size,
dependency budget, index-row agreement) are not applied; the plain walk's own
span rules apply, as for every other callee. A callee with no word switch is
walked as before;
every other layout, including the preloaded one, is refused as before.

The rule fires only where the walk refused, so no admitted walk changes. Each
delegated callee's `complete-guarded-buffer-switch-v1` record (table hash,
successors, partition) is bound into the buffer proof fingerprint only when one
exists, so every other fingerprint is unchanged, and is stated in one report
line:

```
* buffer switch callee: `guarded-switch-callee-v1` 0x080C9208: dispatch at 0x080C9226, 9 successors, 0 scalar words, table a07a394809bf6eed
```

Report replay recomputes the proof, the lines and the fingerprint, and reads
`symbols/functions.txt` for the delegate's identities. No premise is added
beyond the plain walk's own: direct calls inside the callee use the ordinary
returning ABI summaries, as in any inspected callee.

The typed-data proof beside the version-2 walk (`data_buffer_profile`) builds
the same plain proof for its plain path, and takes the same index from
`match.py` and from its own replay, so a caller with typed object words reaches
a jump-table callee the same way; its report carries and replays the same
lines. Its function-literal path builds a `FunctionBufferCallProof` and still
refuses such a callee.

### A jump table in the owner of the default typed-data buffer walk

An owner with typed object literals that dispatched through its own agbcc jump
table and passed a local buffer to a callee was never given the version-2 buffer
proof. Its link has switch relocations, so `match.py` sent it to the switch
profiles, whose walk carries no buffer proof and refused at the first stack
alias that reaches a call, as an argument register or as an outgoing stack
argument:

```
stack aliases cannot cross calls in caller-clobbered registers
unsupported stack-alias use or escape
```

The switch profiles were introduced as closed evidence ("switch evidence cannot
combine frame or buffer proof profiles"): a buffer report had no record of a
switch and its replay no way to recover the switch edges. The walk itself was
never the obstacle. It already treats an authenticated switch as one multi-way
branch: every table target is followed with the same abstract state (aliases,
stack, pointer slots, return provenance), the table and its pointer are kept
out of the executed bytes, the guard and the dispatch must be reached only
through the canonical sequence, and runtime call thunks beside a switch are
refused.

On the default path only, when the plain switch-data walk (one or several typed
objects, no selector, no function literals, not the preloaded layout) refuses,
for whatever reason it reports first, the owner is now proved by the typed-data
proof beside the version-2 walk (`data_buffer_profile`), whose
plain proof carries the BIOS wrapper, copy-helper and jump-table callee
summaries. `owner_switch_buffer_profile.OwnerSwitch` binds the owner's switch to
that proof, authenticated from the ROM bytes with the primitives
`GuardedSwitchBufferProof.inspect` uses for a callee:

1. the proof is that plain stack-argument instance, bound to one owner only;
2. `analyze.refine_function` finds exactly one word switch with no interposed
   scalar words;
3. the owner graph closes with no local BL control;
4. the linked switch relocations and direct calls are exactly those the ROM
   bytes give;
5. the walk re-derives the layout from those table words (`switch_layout`: the
   canonical unsigned guard, a bound covering the table, forward in-span cases)
   and refuses any path into the guard or dispatch that bypasses the comparison;
6. the walk's verified instructions are exactly the owner graph's.

Linked bytes that differ from the ROM keep their own refusal alone. If the
proof refuses a matching owner too, both messages are reported:

```
stack aliases cannot cross calls in caller-clobbered registers; owner-switch data-buffer proof: ...
```

The walk runs without incoming narrow reads. The table pointer counts as the
switch's word, not an untyped literal, when the dispatch's load is its only PC
load. As in the switch profiles (#139), what the cases do with the table base or
the case address left in registers after the dispatch is not checked: both are
ROM code addresses, never stack aliases. Each report line states this.

An owner without typed objects, the function-literal path, the switch-data
selectors, and the preloaded and interposed-pool layouts keep their walk and
message. An owner switch beside an untyped literal in the hardware window (the
numeric hardware class) refuses with `numeric hardware words require the exact
complete owner graph`, because that class is defined only over owners without a
table.

The record (layout, transfer, successors, table hash) is bound into the buffer
proof fingerprint only when an owner switch exists, so every other fingerprint
is unchanged, and is stated in one report line:

```
* buffer owner switch: `guarded-switch-owner-v1` 0x080A1600: dispatch at 0x080A161C, bound 6, 7 successors, table c7047304968e7eaa; table pointer: only PC load is the dispatch, case uses of the table registers unchecked
```

The data-buffer replay relinks the captured source with its switch relocations
and recomputes the proof, the line and both fingerprints. As for the other
`* buffer` lines, replay compares the line's text and order among them, not its
position among the other fields. Besides the typed-data proof's own premise,
the one limitation stated in each line (case uses of the table registers are
not checked) is the only addition; no other premise is added.

### Function literals with bounded buffer calls

The separate `elf-symbol-thumb-function-buffer-calls-v1` profile composes the
exact named Thumb function-address bindings below with the existing bounded
register/stack buffer version-2 proof. It requires both a reachable function
literal and an actually inspected buffer dependency. The matcher preserves
function-address version 1 when its frameless proof succeeds; otherwise this
composition must succeed in full or verification fails, without a legacy
buffer-only fallback. Fixed frames and multiple direct calls are supported;
switches, runtime-thunk bindings and indirect-call dependencies remain
excluded. A caller that also has named object relocations uses the separate
`elf-symbol-thumb-function-data-buffer-calls-v1` schema below instead. No buffer bounds, escape or provenance check is
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

### Typed named data beside buffer calls

A caller with named data relocations whose stack buffer reaches a callee is
verified by two schemas, one for each matcher path. Neither needs a selector.

* `elf-symbol-thumb-data-buffer-calls-v1`, on the plain direct-call path. When
  the plain proof inspected a buffer call and the function has data relocations,
  the matcher reruns it as one composed proof: the version-2 register and stack
  buffer proof with bounded loop replay (`BufferCallProof`, exactly as
  `elf-symbol-thumb-frame-buffer-calls-v2` runs it, incoming narrow reads and
  the BIOS wrapper summaries included), the typed object literals of `elf-symbol-thumb-data-v1`, and the
  plain path's call rules: direct calls to indexed Thumb functions and the
  canonical `_call_via_rN` thunks, with the thunk literal and own-span checks.
* `elf-symbol-thumb-function-data-buffer-calls-v1`, on the function-literal
  path. When the frameless function-address proof fails and the function has
  data relocations, the matcher tries the function-buffer proof
  (`FunctionBufferCallProof`, version 2 with pointer slots and loop replay)
  with the canonical function literals and the typed object literals. Runtime
  thunks stay excluded, as on that path without data.

Both require an inspected buffer dependency and an exact complete mapped
caller span. Every typed object word is bound as `elf-symbol-thumb-data-v1`
binds it: an undefined external object with an evidence-backed
`config/data_symbols.json` entry, an `R_ARM_ABS32` relocation occupying a
complete aligned word inside the function, loaded by a reachable PC-relative
instruction, equal to its address plus addend, never inside the caller's own
bytes and never an address reserved for a pinned arithmetic runtime. When the
caller calls a `_call_via_rN` thunk, no object may name an indexed function
entry. All linked bytes are compared with the ROM.

Both also require typed provenance for every reached address-domain literal,
as the complete-owner selectors do: each reached PC-loaded word whose value is
in `[0x02000000,0x09000000)` (RAM, I/O to OAM, ROM), a ROM wait-state mirror
word folded first (see "ROM wait-state mirrors"), must be a typed object or
function literal, and every typed literal must be such a word, spelled at its
canonical address, with one exception. An untyped word in `[0x04000000,0x08000000)` that the owner rule
classes as a numeric hardware word (`reached-numeric-hardware-literals-v1`,
see "Fixed hardware addresses as numbers in BIOS fill owners") is a number;
it is computed over the exact complete owner graph, which must agree with the
reached instructions. These schemas compute no BIOS scalar controls, so a
hardware-window word with bit 24 set (a CpuSet fill control such as
`0x05000080`) any one of whose loads reaches the CpuSet call solely as its R2
argument (directly, or through R4-R7) still needs typed provenance and is
refused. A word none of whose loads is such a control (one only stored as a
number, say) is recorded as a numeric hardware word. The rule refuses an
untyped reached IWRAM, EWRAM or ROM literal-pool word, so such a number cannot
reach a buffer callee as an untracked pointer. It covers literal-pool words
only: an address materialised from immediates (`movs` then `lsls`) is not a
pool word and is not covered, as on the data-free buffer schemas, which have no
coverage rule.

A typed object literal is an absolute address loaded from a relocated word. It
never becomes a tracked stack alias, since aliases come only from SP
arithmetic, so the bounds, alignment, saved-slot, pointer-slot and escape
checks treat it as they treat a pointer parameter, under the existing
returning-ABI premise. That named objects do not overlap any live stack is a
premise, not a check (kit `#196`); it is stated in the report. No buffer rule
is relaxed.

The report keeps the generic buffer lines (`* buffer calls:`,
`* buffer proof SHA-256:`, one `* buffer loop replay:` line per replayed
callee, and the five `* buffer BIOS` lines when a BIOS wrapper was summarised),
the mapping and data-map digests, and adds
`* data buffer calls:` (the summary and the premise),
`* data buffer manifest:` (calls, typed object and function bindings and, when
present, the `numeric_hardware_words` record) and
`* data buffer proof SHA-256:` (a domain-separated digest of the schema, the
version-2 buffer schema, the address, the bytes, the manifest, the source
digest, both maps and the buffer proof fingerprint). Report replay requires exactly these fields and no
other `* ` field, recompiles and relinks the captured source, reruns the
composed proof against the selected ROM, and requires the recomputed manifest,
fingerprints, replay lines and stack-frame line, a plausible source and
unchanged inputs. Library-unit toolchains do not admit these schemas.
`tests/test_data_buffer_calls.py` covers both paths.

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

### Conditional local-buffer interfaces

Issue #73's two interfaces have separate opt-in owner profiles:

```sh
python tools/match.py --root ../fftadecomp 08006970 --owner-runtime-profile conditional-scheduler-descriptor-calls-v1
python tools/match.py --root ../fftadecomp 0809A77C --owner-runtime-profile conditional-local-state-iterator-v1
```

The scheduler profile checks a complete 28-byte local descriptor, exact indexed
scheduler bodies, typed callback literals, and the canonical dependency thunks.
The state profile checks the complete four-byte state/initialized visitor caller,
actual size argument, iterator, adapter, state callback, and canonical thunks.
Its one variable root halfword is the owner-list load `ldr r0, [r4, #imm5*4]`:
any aligned word offset from R4 into R0 is accepted, every other code byte is
fixed, and the report binds the offset as `owner_list_load` (0x18 for
`0809A77C`, 0x14 for `0809A740`).
The `conditional-flagged-local-state-iterator-v1` selector checks three 72-byte
wrappers. Each keeps the address of the four-byte state in R4 across the
initializer, ORs a flag into `state[1]`, passes the updated state through the
same visitor, and returns `state[0]`. The pinned callback `08098BB0` tests bit
0 before `080C8260` and bit 1 before `080C84C0`. The observed owner-list offset
and mask pairs are `(0x14, 1)`, `(0x18, 1)`, and `(0x18, 2)`. The report binds
the load, update, store, mask and register. R4 must name the very same private
state as R0 at initialization and the descriptor's first pointer at iteration.
The scope and nonretention premises apply to this ambient copy as well. The
original 60-byte selector continues to require its original call interface.

These profiles retain exact ELF relocation, full-symbol ROM comparison, plausibility,
source/index binding and report replay. Default buffer rules remain unchanged.

These are **conditional effect contracts**. Reports list their assumptions:
compatible returning calls, protected-frame preservation, bounded local effects,
and no retained or returned local pointers. Scheduler copying exposes both the
copy in R1 and the original pointer in R9; it does not establish nonescape.
Likewise, `n = 4` alone does not establish the installed callback's write bound
or initialization behavior. Allocator/installed callback effects, physical
permissions and termination remain unproved. Select these profiles only under
the stated contracts; they are not an unconditional memory-safety theorem.

A guarded descriptor caller can instead select
`conditional-scheduler-guarded-descriptor-calls-v1`. It permits exactly one
scheduler call preceded by read-only predicate calls, with no calls after the
scheduler on any CFG path. Every predicate's complete indexed Thumb body and
nested calls are checked, with at most eight helpers of 512 bytes each and no
CFG or call cycles. A closed instruction set excludes stores except private
PUSH saves, indirect calls, runtime calls and stack-address materialization.
The frame proof requires restored SP, R4–R11 and the original return address.
No live local-register alias or pointer word may enter a predicate call.
The report retains the scheduler premises above and separately states that
predicate reads require live, defined ordinary memory and valid, nonoverlapping
stack saves. Actual readability and predicate values are not established.
The descriptor and payload profiles keep their existing single-call limit.

Two mutually exclusive calls through `func_08121B8C` have a separate
`conditional-scheduler-entry-branch-descriptor-calls-v1` selector. It accepts
exactly two static calls to that pinned wrapper and no other calls. Acyclic
all-path propagation rejects any call reached after a wrapper return, proving
at most one invocation per path. Both sites retain the existing entry profile's
aligned 28-byte private descriptor, alias, complete dependency and frame/return
checks. Reports retain the same conditional scheduler, parent, callback and
nonretention premises; actual callback effects and termination remain unproved.
The single-entry selector still requires exactly one static call.

Phase branches with ordinary calls have a separate
`conditional-scheduler-branch-descriptor-calls-v1` profile. It authenticates the
complete caller CFG and ordinary indexed helper bodies, allowing at most two
static scheduler sites, eight call sites total and four ordinary helper targets.
Acyclic all-path propagation proves at most one scheduler invocation per root
path and rejects every call reachable after a scheduler return. Each scheduler
site retains the exact 28-byte private descriptor checks. Every ordinary call
must have no tracked local aliases in any register, pointer words or word facts.
Those ordinary calls retain the existing returning ARM ABI summary: body
identity does not establish their memory effects or nested execution. Reports
keep that conditional boundary separate from the read-only predicate proof.
Existing single-call, predicate and payload profiles keep their own guards.

`conditional-scheduler-eight-target-branches-v1` is a separate bounded option
for phase controllers with up to eight ordinary helper targets and twelve call
sites. It preserves the acyclic all-path check, two static scheduler-site limit,
at most one scheduler execution per path, and prohibition on calls after the
scheduler. Every helper has a complete authenticated indexed body, and every
ordinary call still excludes all local aliases, pointer words and word facts.
The larger inventory does not prove callee effects or nested execution. The
original branch selector retains its four-target and eight-site limits.

`conditional-scheduler-three-per-path-calls-v1` keeps the acyclic all-path
walk but counts scheduler invocations: at most four static scheduler sites and
three invocations on any path, with ordinary calls admitted after a scheduler
return. Every ordinary call still excludes all local aliases, pointer words and
word facts. `conditional-scheduler-sequential-leaf-output-calls-v1` and
`conditional-scheduler-sequential-killed-alias-calls-v1` use the same phase
rule with their own ordinary-call rules. All three allow 32 ordinary targets
and 48 call sites. Both numbers are cost bounds, not proof obligations: the
walk visits each site once and bounds invocations per path by itself, each
distinct target body is authenticated once, and the owner replay checks every
call site on its own, so the work grows linearly with the number of sites.

`conditional-scheduler-following-call-v1` permits ordinary calls after exactly
one scheduler site in an acyclic caller, with the original four-target and
eight-site limits. Each following call undergoes the same complete alias/frame
checks; a second scheduler invocation, tracked local alias, pointer word or word
fact refuses. This option is separate from the eight-target profile. Both keep
physical access, protected-frame preservation, synchronous lifetime,
allocation separation, callback effects and termination as explicit conditions.

`conditional-scheduler-entry-descriptor-calls-v1` admits the same single
28-byte descriptor call through one of two other entries in a closed table,
never `func_08005B6C`. `func_08121B8C` (44 bytes, pinned SHA-256) takes the
descriptor in R2 and forwards it with its pool manager to `func_08005954`. A
direct `func_08005954` call takes the descriptor in R3 and the parent in the
caller's outgoing word at SP. That word must be private and hold no tracked
local pointer, and the descriptor must lie wholly above it. The manager in R0
must come from one straight-line `ldr r0,[pc,#k]; ldr r0,[r0]` pair, and the
literal must carry exactly one typed named-data relocation with addend 0.
The descriptor must be word-aligned for either entry, because the scheduler
copies it with LDM. Every other outgoing alias or pointer word is refused. The
report records the entry, its pinned bodies, the manager literal and the
outgoing word. Its premises are those of the descriptor profile plus a valid
manager word separate from the caller frame, a parent that is NULL or a valid
scheduler node addressing no caller stack word (the scheduler stores through
it), and, for direct calls, the scheduler reading the parent only through the
outgoing word. Existing scheduler selectors retain their
`func_08005B6C`-only guards.

The menu constructor at `080253B0` uses
`--owner-runtime-profile conditional-menu-palette-scheduler-v1`. For mode 17
it passes a 28-byte descriptor to the scheduler without initializing any field.
For other modes it stores `mode - 1` at descriptor offset 20 and copies two
palette bytes into `030039F8`. The verifier checks both indexed ROM palettes,
the CpuSet installer and the exact accesses of its installed copy entry.
In both cases the scheduler copies seven words and overwrites the phase halfword
with zero. Callback `08028FF4` reads that phase and initializes six ordering
bytes. Callback `08028DE0` also reads the argument halfword and writes its low
byte, the task and its parent into the fresh payload. The remaining descriptor
bytes stay opaque. This result covers synchronous creation under the installed
image, valid manager, parent, allocation and separate-storage premises.

The constructor at `080D376C` first clears a 28-byte descriptor and passes
it to the same direct scheduler entry. Use
`--owner-runtime-profile conditional-scheduler-zero-descriptor-v1` for
this caller. Its first call loads the Thumb target from the ROM word at
`0836D4B8`. The installer passes 88 halfwords from `08A38A2C` to
`03005E78` through CpuSet. Under the premise that the image remains
installed and executable, its aligned path executes 43 instructions, writes
seven zero words within the descriptor and restores its saved return address.
The caller replaces the resulting one-past pointer in R2 before reading it.
The second call passes the same descriptor in R3, a zero parent word on the
stack, callback `080D3208`, and allocation size `0xB28`. The scheduler's
return, nonretention and frame-isolation premises still apply. The saved
report checks the original ELF bindings, image, both accesses to the local,
and the complete 64-byte owner. Run `tests/test_scheduler_zero_descriptor.py`
with `FFTA_SCHEDULER_ZERO_ROOT` set to the indexed game checkout for the
USA ROM tests.

The 248-byte event dispatcher at `080DE524` uses
`--owner-runtime-profile conditional-scheduler-event-definition-v1`.
Its private frame contains a two-byte dispatch duration, a 28-byte request,
a 16-byte definition and five spilled arguments. Only request offset four
contains a borrowed pointer. The scheduler copies the request and sets its
phase halfword to zero. On every list path that reaches the copy, the state
address in R2 is the fresh allocation plus 24. Callback `080DDA94` copies
seven fields into the state and optionally clears one external result byte.
The two bytes of definition padding are never read. Physical separation,
the allocator, the installed zero helper, and termination retain the
scheduler's ordinary premises. Run `tests/test_scheduler_event_definition.py`
with `FFTA_EVENT_DEFINITION_ROOT` set to the indexed checkout for native
replay and mutation tests.

The scene callbacks at `08118A08`, `08118AC0` and `08118B94` use
`--owner-runtime-profile conditional-scene-mode6-position-v1`. Each fills
two RAM ranges with BIOS CpuSet and passes a four-byte position to the script
helper at `080E03F8` through its fifth argument. The verifier checks both
halfword fill sources. Its helper interpreter follows switch case 6 and
reads two signed halfwords from the position. The geometry predicate consumes
the resulting coordinates. Either predicate outcome reaches the direct scheduler,
with delay 0 or 20, a separate 28-byte descriptor and callback `080DFF04`.
Its phase-zero path copies a delay halfword, count byte and script data pointer
to the payload. The report records the selected instructions, real ELF bindings,
and the physical-isolation, allocator, BIOS and ordinary-return premises.
Run `tests/test_scene_script_position.py` with `FFTA_SCENE_SCRIPT_ROOT` set to
an indexed game checkout containing the saved `08118A08` report.

The movement query at `080989AC` uses
`--owner-runtime-profile conditional-movement-path-prefix-v1`. It rejects an
unreachable or occupied destination, reconstructs the movement path into the
caller's buffer, and scans its four-byte steps backward for an eligible empty
or self-occupied tile. Two action-state callers supply 128 bytes. The provider
requires an initialized grid with a terminating path of up to 24 steps, which
fits the 96-byte IWRAM scratch area. The verifier replays the original tile
callback and checks the installed copy image for each supported byte count.
Set `FFTA_MOVEMENT_PATH_ROOT` to a USA checkout containing the C source to run
`tests/test_movement_path_prefix.py`.

The tile query at `08099FB0` uses
`--owner-runtime-profile conditional-movement-tile-stop-v1`. It divides
movement by ten, checks whether the actor can reach the tile, then walks the
object list. An empty tile or one already occupied by the actor is accepted.
The report checks the callback address against the ROM and the field offsets
against the shared C declarations. Run `tests/test_movement_tile_stop.py`
with `FFTA_MOVEMENT_TILE_ROOT` pointing to the recovered game checkout.

The movement overlay at `08098A88` uses
`--owner-runtime-profile conditional-movement-overlay-v1`. It gates setup
and scanning on grid and display readiness. Its second phase checks all 256
tiles, queries occupants of reachable tiles, and marks empty destinations.
The profile verifies the two unsigned divisions by ten, the tile callback
literal, the twelve-byte local query, and the boot-installed display clear.
The renderer and its buffers must be initialized. Set `FFTA_MOVEMENT_OVERLAY_ROOT`
to an indexed USA checkout with this source to run `tests/test_movement_overlay.py`.

The menu routine at `08027528` uses
`--owner-runtime-profile conditional-unit-entry-output-array-v1`. The producer at
`0809F78C` treats the low 16 count bits as signed. For a positive count it writes
one four-byte entry per iteration. The menu passes an 80-byte stack array and a
count of 20, then dereferences the first word of each returned entry. A separate
caller at `08099A70` supplies an 80-byte heap buffer to the same producer.

The report follows the output cursor through allocator wrappers, private save slots,
and the two word outputs of the heap search. On a normal return, the menu consumes
the same 20 words that the producer initialized. The selected indices must be in
0 through 12 for the observed accesses to stay inside the temporary allocation.
Valid external heap objects, entries that survive the free, and a writable menu
destination remain runtime conditions. Set `FFTA_UNIT_OUTPUT_ROOT` to the indexed
USA game checkout to run `tests/test_unit_entry_output.py`.

The name-entry routine at `0812A878` uses
`--owner-runtime-profile bounded-buffer-conditional-thunks-v1`. It clears a
20-byte local buffer, copies the name starting at the first non-space glyph,
removes trailing spaces and empty cells, then copies ten halfwords to the
destination. The verifier follows the boot-installed clear routine and
checks the length and address range of each BIOS copy. The caller provides
an aligned 20-byte destination. Set `FFTA_NAME_ENTRY_ROOT` to run
`tests/test_name_entry_copy.py`.

The decimal formatter at `080142DC` uses
`--owner-runtime-profile bounded-buffer-datafree-caller-v1`. The game formats
a 16-bit number into six characters and converts them to two-byte glyphs.
Its aligned length routine reads two words, including one byte beyond the
terminator whose value does not affect the result. The caller supplies room
for two bytes per output column and the terminator. Set
`FFTA_DECIMAL_FIELD_ROOT` to run `tests/test_decimal_field.py`.

The 176-byte equipment attribute routine at `0812F5E0` uses
`--owner-runtime-profile conditional-unit-equipment-attribute-v1`. Its caller
must supply a stable, live five-slot loadout with at most two qualifying items.
A nonzero item qualifies when ROM field 6 is 1 or 2 and field 3 differs from 20.
Under this condition, the original collector, sorter and consumer stay within
the two local halfwords. Attribute 10 skips selected items and begins with a
supplied item value or the unit default. Attribute 12 adds every equipped item.
The unit status bit can return zero before any collection.

The verifier checks the installed equipment-copy routine and the initial
loadouts of 42 actor definitions in scene groups 1, 2, 4, 23 and 37. Runtime
edits and the second battle caller retain the same loadout precondition.
Set `FFTA_EQUIPMENT_ATTRIBUTE_ROOT` to an indexed USA game checkout with
the saved report to run `tests/test_unit_equipment_attribute.py`.

The same equipment profile verifies the four original calls and the complete
206-byte battle evaluator at `080BDECC`. The eligibility test collects into
its own two-halfword frame. The evaluator collects a fresh selection at
SP+8, supplies item zero for an empty result and uses only the first item
for action zero. Its other two stack words hold outgoing scalar arguments.
The subtotal and signed adjustment follow the original halfword arithmetic.
All actors inspected by the battle helpers must meet the loadout condition.

Set `FFTA_BATTLE_ACTION_ROOT` to the indexed USA checkout with the saved
report to run `tests/test_battle_action_value.py`. Both original AI callers
execute on map 0, loaded from its three original ROM resources. They observe
the actor initialization, range output, item arguments and returned score.

The 130-byte position-dependent chance calculation at `0812C8DC` takes the
first selected item and the signed coordinates of both units. If the
evaluator returns a nonzero result and the target's flag is set, it returns
100. The verifier checks all 12 direct calls in ten indexed functions. Each
call retains the same two-item precondition after changes to a unit's
equipment. Set `FFTA_POSITIONED_CHANCE_ROOT` to run
`tests/test_positioned_equipment_chance.py`.

The selection-list routine at `0813569C` evaluates entries in order and
returns the first matching index plus one, or zero if none qualify. It
passes the first selected item to the effect evaluator. Its two-item stack
buffer has the same live-loadout requirement. The verifier checks both data
addresses and all eight arguments to the entry predicate. Set
`FFTA_EQUIPMENT_SELECTION_ROOT` to run `tests/test_equipment_selection_list.py`.

The equipment profile also covers the 192-byte eligibility predicate at
`080C48A4`. Its signed halfword temporary receives the collector count
before the action paths assign the Boolean result. Returning that value as
an unsigned byte reproduces both shifts in the original common return.
The verifier checks all ten calls, the action-state pointer, the frame's two
equipment halfwords and the loop over three action variants. It retains the
same five-slot equipment precondition for all three direct callers.

The ROM test runs original actions which succeed on the first, second and
third variant, and others that exhaust all three. It observes the selected
index, target, output halfwords and byte result on initialized scene actors.
Set `FFTA_BATTLE_ELIGIBILITY_ROOT` to the indexed checkout with its saved
report to run `tests/test_battle_eligibility.py`.

Issue #81's single local result word passed to an indexed callee has its own
opt-in profile:

```sh
python tools/match.py --root ../fftadecomp 08080EB8 --owner-runtime-profile conditional-local-output-word-call-v1
```

It requires exactly one actual call, to the indexed output callee
`func_080799C0` with a pinned body size and SHA-256, whose only caller-frame
pointer is R2 naming the frame's single local word, with no other local
register (including callee-saved copies) or pointer-word aliases. The callee's
stores are not alias-analysed; ROM inspection shows two 16-bit stores at R2+0
(0x0807A046, 0x0807A05C). The report states the premises: the callee writes at
most that four-byte word, accesses no other private or saved word, returns
compatibly and retains no local pointer.

Issue #82's scheduler callers pass a descriptor whose second word points at a
separate local parameter block. They have a sibling opt-in profile:

```sh
python tools/match.py --root ../fftadecomp 080DF9AC --owner-runtime-profile conditional-scheduler-descriptor-payload-calls-v1
```

It keeps every scheduler check above and admits exactly one local pointer word:
descriptor+4, addressing the payload. The private frame must hold exactly the
descriptor and one adjacent nonempty payload, in either order. The observation
records `payload_offset` and `payload_frame_bytes` with
`payload_extent: remaining-private-frame`: the extent is an upper bound equal to
the rest of the private frame, not the payload type's size, and every byte of it
is checked as private. Payload initialization is not checked. Any other pointer word, payload placement,
extra argument alias or interleaved saved word is refused, and the descriptor
profile still refuses these callers. The pinned scheduler body copies the
descriptor into its own frame, not the allocation, before one synchronous
phase-0 callback call. The callback's payload read bound, the payload's
initialization (padding is representation only) and the callback not retaining
the payload pointer are listed premises, not proofs.
Callee-saved register aliases to the descriptor or payload are admitted and
recorded, as in the descriptor profile; the read-through-descriptor+4 premise
covers them.

For the interface whose payload pointer is descriptor+8, select
`conditional-scheduler-descriptor-payload8-calls-v1`. It requires exactly one
pointer word at +8 and the same two adjacent private objects and bounded
payload extent. Its report records `payload_pointer_word_offset: 8` and applies
the explicit read-through-payload and synchronous nonretention premises to that
field. The existing payload profile still accepts only +4; neither profile
permits a second pointer word or infers callback effects, initialization or
allocation separation from the field offset.

`conditional-scheduler-two-payload-calls-v1` admits one authenticated scheduler
call with two local pointer words at descriptor offsets +4 and +8. The complete
28-byte descriptor and two distinct, nonempty aligned payload intervals must
partition a contiguous private frame of at most 256 bytes. Pointer provenance,
all private bounds, protected saved words and preserved-register aliases remain
checked; other outgoing aliases or pointer words refuse. Recorded payload bounds
are frame upper bounds, not type sizes or initialization facts. Physical access,
allocator separation, callback read bounds, lifetime and nonretention remain
explicit conditions. Unknown bitfield representation bytes are not promoted to
initialized values. Existing single-payload profiles retain their guards.

`conditional-scheduler-halfword-output-payload-v1` composes the complete indexed
`0801E6F0` two-halfword output leaf with one later scheduler call. The bounded
private frame contains a leading payload, a 28-byte descriptor and a trailing
four-byte output pair. The descriptor+4 pointer addresses only the leading
payload; the output pair is excluded from that extent. The proof authenticates
the leaf's complete body, named loads and ordered formal stores, rejects writes
outside those private halfwords, and retains actual returned aliases such as R1.
Every observed alias state at the scheduler is recorded. Named source halfwords
remain conditionally readable with unknown values. Payload initialization,
physical access, allocation separation, callback read bounds and synchronous
nonretention remain explicit premises. Existing selectors retain their guards.

### Typed-literal two-word callback closures

`conditional-two-word-callback-closure-v1` admits only the 28-byte caller whose
closure callback word comes from a parameter. Callers of a listed callback
iterator that store a **function literal** in that word have a separate opt-in
selector:

```sh
python tools/match.py --root ../fftadecomp 08099CDC --owner-runtime-profile conditional-two-word-literal-callback-closure-v1
```

Seven exact root forms are accepted. Only the aligned owner word load, the
BLs and the two typed literals (callback, then adapter) may vary.
Descriptor word zero is the constant zero (36 bytes), the entry R0 value
(40 bytes), the u8 narrowing of entry R1 (`entry-byte`, 40 bytes with a zero
alignment halfword), the owner word that is also the iterator's list argument
(`owner-word-trailing-call`, 44 bytes, saves R4), the address of a private
two-word state initialized to zero and entry R1 (44 bytes, returns state word
zero) or to entry R1 and entry R2 (`entry-state`, 40 bytes, returns nothing),
or the address of a private flag byte initialized to zero (`local-byte-flag`,
56 bytes). The flag root reads the byte back after the iterator and returns 1
if it is nonzero, else 0; its literal pool sits between that branch and the
`movs r0,#1` arm, so its template spans the whole function with the pool
masked. The owner-word form then reloads the owner word
through the same pinned halfword and makes one ordinary typed call on it. That
callee is opaque, but R2 still holds the descriptor address when the list
iterator returns on an empty list. So the callee is decoded as ARMv4T Thumb
(the `callee_preservation_profile` decoder) along its single entry path, and it
must overwrite R2 before any R2 read, call, return or conditional branch. Its
entry SP is the descriptor address, so SP moves are limited to PUSH and
SUB/ADD SP,#imm. An overwrite derived from SP (directly, through a register,
through an SP-based load, or through a load after an SP value was stored) is
admitted only as MOV/ADD R2,SP[,#k] strictly below entry SP. The report records
the overwriting site under `trailing_call` and `live_aliases_to_trailing_callee`. Bindings must be exactly the root's calls and the
two function literals in pool order, with no data or switches. The iterator, adapter, getter and canonical thunks are
checked as follows. The 28-byte profile's contract is unchanged.

The iterator call must reach one entry of a closed table, `ITERATORS`. Each
entry pins the complete body by size, refined count and SHA-256, and the
structure is re-derived from the bytes. R1 (adapter) and R2 (descriptor) are
copied into callee-saved registers that nothing else writes. The only call goes
through the adapter register's canonical thunk, with R0 = current node and
R1 = descriptor. The body has no stores, and it reads exactly the entry's words
from the list object and the current node. The report records the iterator
address, kind, registers, reads and thunk.

| iterator | walk | reads | adapter thunk |
| --- | --- | --- | --- |
| `080C7CC0` | singly linked list | list+4, node+8 | `_call_via_r6` |
| `080C7D18` | parent-linked binary tree, in order, node+12 first | list+8, node+8/+12/+16 | `_call_via_r7` |
| `080C7D70` | same tree, node+16 first | list+8, node+8/+12/+16 | `_call_via_r7` |

All three are read-only and call the adapter at most once per nonnull node
reached, in walk order, with that node and the original descriptor. An adapter
result of zero stops the walk. No iteration bound is assumed; termination is
unproved. The SHA-256 pin is the admission gate. The structural checks run
over the complete instruction graph and derive the recorded facts, including
whether entry R2 still holds the descriptor on the empty-input return. The two
tree walks are the same bodies that `tools/tree_two_word_callback_closure_profile.py`
(`conditional-two-word-tree-callback-closure-v1`) admits by template for
parameter-callback roots. This profile pins them independently for
typed-literal roots, and the overlap is intentional.

There are two kinds of adapter.

* A 22-byte scalar adapter must pass `two-word-scalar-callback-adapter-inventory-v1`
  unchanged.
* A **framed two-output adapter** must be an entry of the closed table
  `FRAMED_ADAPTERS`. This extends the adapter rules. Today the only entry is
  `0809AC00` with getter `080C7B78`.

Both the framed adapter and its getter are pinned byte for byte. They must
also pass the existing `tools/two_output_callback_adapter_inventory.py`
(`two-output-local-scalar-callback-adapter-inventory-v1`), whose manifest is
embedded as `inventory`. Their effect is interpreted as well. The interpreter
refuses any frame address left in R0-R3 or R12 at the callback or at the
return, and it records the register that held the descriptor. The adapter reserves an eight-byte private local area
and passes its two word addresses to the getter. The getter stores node word 4
and node word 0 there, and writes nothing else. The adapter then passes the
first local word and descriptor word zero to the descriptor word-four target
through `_call_via_r2`, and returns that target's R0. The report states its
premises:

* the node is nonnull with readable words 0 and 4;
* the local area is a valid private frame, and the out-pointers stay inside it;
* the getter and the target use the returning ABI.

In the opaque forms no private address is passed to the callback as
an argument. Its
identity is pinned, but its effects stay opaque under the same compatible
returning ABI and noninterference premises as the 28-byte profile. In the
two state forms and the flag form the callback receives a private-frame
address, so it must be a pinned callback paired with that one root form, and
its effects are interpreted.

* **State callbacks** (`STATE_CALLBACKS`) are complete straight-line leaves
  pinned byte for byte. The interpreter derives the effect and compares it
  with the pinned one. `0809AC20` (private-state form) reads and writes only
  the two state words, increments word zero, and stores the getter word
  through the word-four cursor before advancing it by four; the root's
  read-back of state word zero is reported as zero plus one per returning
  callback, modulo 2^32. `0809ACA4` (`entry-state`) reads the two state words
  without writing them and replaces the getter object's word at +0x30 with
  `(word & ~state[0]) | state[4]`.
* **Flag callbacks** (`FLAG_CALLBACKS`) pass the flag address on, so the whole
  closed call tree is pinned by size, refined count and SHA-256: `0809AD48`,
  `08098BB0` and the six leaf predicates it calls. Every body is completed
  against the index and interpreted over its whole instruction graph, with
  calls interpreted in their caller's context. Through the flag address the
  tree may only read bytes 0 and 1 and store to byte 0 that byte's value, read
  since the last store or call, plus one. Otherwise it may only copy the
  address (a callee-saved copy is followed too); a copy also sets the
  condition flags, so it may select among interpreted paths. It may not store
  or push the address, compute with it or use it as any other base. Byte 0
  may only be copied, incremented and stored back; byte 1 may only be masked
  by a constant and tested. No flag byte value may be left in R0-R3/R12 when
  the callback returns. The tree makes no other store and no SP-relative
  access beyond PUSH/POP of its own frame. Every function restores R4-R11 and
  SP and returns through its entry LR, leaving none of its own callee-saved
  values in scratch registers, and the callback returns 1. The scratch
  registers that may still hold the address on return are iterated to a
  fixed point (re-seeding them at entry until the set is stable; R3 for
  `0809AD48`) and recorded. A graph walk then shows that the iterator,
  adapter, getter and root continuation never read them before overwriting
  them, and they are reported as expired aliases. The flag form admits only
  the scalar adapter. The root's read-back is reported as 1 if flag byte 0 is
  nonzero, flag byte 0 being zero plus one per interpreted increment, modulo
  2^8. The root never initializes flag byte 1. The callback's two reads of it
  are reported as indeterminate reads that only select among interpreted
  paths.

The adapter's no-private-provenance premise is
replaced for that word, not asserted satisfied. Store validity and nonoverlap,
external-read validity and list liveness remain explicit conditions; no
iteration bound is assumed and termination is unproved. The root frame is
fixed by the exact byte template rather than the frame prover.

The profile requires the **refined** instruction count for the root in both
`config/functions.json` and `symbols/functions.txt`: 17 for the 44-byte form,
15 for the 40-byte form and 13 for the 36-byte form (14 for `entry-byte`, 16
for `owner-word-trailing-call`, 15 for `entry-state` and 23 for
`local-byte-flag`). This is the
reachable-instruction count reported by `analyze.refine_function`, which
excludes the literal pool. The analyzer's raw rows count pool halfwords as
instructions (22, 20 and 18). With today's index only `08099CDC` reaches the
proof; `08099D08`, `08099A48` and `0809A6EC` fail closed with `exact complete
owner/count` until the matching decomp commit corrects their rows. The six
tree-walk closures `08099D60`, `08099D8C`, `08099DB8`, `08099DE4`, `08099E10`
and `08099E3C` need the same correction (17).

### Stack arrays passed to the known list queries

`--owner-runtime-profile conditional-known-query-stack-buffer-v1` admits a
caller that passes a private stack array to `08099CDC`, `08099D08` or
`08099D34` and reads it back:

```sh
python tools/match.py --root ../fftadecomp 08023130 --owner-runtime-profile conditional-known-query-stack-buffer-v1
```

The default buffer verifier still refuses these callers, because it re-derives
each callee's CFG and stops at the `_call_via_r6` thunk. This profile instead
applies a contract to the query family, and pins the bytes, extents and refined
counts of the three roots (17 each), the iterator `080C7CC0`, the adapter
`0809ABE8`, the collector `0809AC20`, the getter `080C7B74`, both thunks and
their unowned padding. The contract is: with n list nodes the query stores
node value k at out+4k for k = 0..n-1, returns n, writes no other caller
memory, preserves R4-R11/SP and uses at most 44 bytes below the caller's SP.
The only visitors are the adapter (through `_call_via_r6`) and the collector
(through `_call_via_r2`). `tests/test_known_query_stack_buffer.py` runs the
pinned bytes on a CPU for n = 0..13 against this relation when `unicorn` is
installed.

The ROM does not bound n. The profile takes one fixed premise, at most 13
nodes, and requires every query buffer to be 13 allocated private words (no
saved word inside it). The caller is executed abstractly on every path for each
n from 0 through 13, with the first n buffer words initialized and the others
unchanged. Any read of an uninitialized private word refuses. So do a private
address in any argument register (other than the query's R1 buffer) or stored
anywhere, an unknown private index, sub-word private access, an unbalanced or
unrestored frame, an uncovered instruction, or more than 65,536 abstract
states. After any call only R0 is defined (the query's count or an ordinary
result): reading R1-R3, R12 or LR before redefining it refuses, because the
pinned collector leaves R2 at out+4n, which for n = 13 addresses the word after
the buffer. Ordinary calls and external accesses keep the usual returning ABI
and noninterference premises; an ordinary callee may read the caller frame only
as its own stack-passed arguments (a premise). Because a callee may store into
those slots, the initialized words from SP become unknown after each ordinary
call; the report records how many there were. Direct calls to the pinned
dependencies refuse. The report records the contract identities, each query
site and buffer offset, the counts executed and the private reads and writes.
The list bound, physical memory permission and termination are not proved.

### Buffer owners that copy constant ROM tables to the stack

`--owner-runtime-profile named-data-buffer-rom-table-copy-v1` admits the
natural initialised local array. agbcc lowers `u8 a[3] = {0, 20, 40};` to a
constant in `.rodata` plus a call to its `memcpy`, which is the ROM routine
`func_081443FC`; the explicit spelling `func_081443FC(a, data_XXXX, 3)` is
admitted by the same rules.

```sh
python tools/match.py --root ../fftadecomp 0x0811E618 --owner-runtime-profile named-data-buffer-rom-table-copy-v1
```

It is `named-data-buffer-v1` with one step replaced: a call to the pinned copy
helper is summarised instead of being walked into its word loop, where the
destination alias meets alignment arithmetic. The summary requires

* the helper is the exact indexed 98-byte routine, no instruction of it writes
  a register above R5, and its byte path for counts up to 15 is pinned;
* R0 is a tracked stack alias and the only alias passed, R2 is an exact
  constant from 1 to 15 and R1 is a constant code literal of the owner or of a
  walked callee;
* the whole destination lies in allocated private words and clear of every
  pointer-bearing word;
* the source lies in ROM and is either the compiler's initialiser or a table
  named exactly by a data symbol. Data symbols carry no size, so the next
  named object is the only known end of a named table: a copy that runs into
  it refuses.

For the initialiser, the object may carry one plain `.rodata` section. The
address its literals resolve to must agree over every literal, and the section
bytes must equal the ROM bytes there; the linker places `.rodata` at that
address, the linked text and table are compared with the ROM, and the report
records the base, size, hash and literal sites. A tampered table byte therefore
fails at admission, as does any other allocated section. The compiler's
undefined `memcpy` symbol must be the unique undefined global and is bound to
the pinned helper, as in the compiler-copy profiles.

The destination alias is returned in R0; R1-R3 are dead. Later uses of the
object are ordinary private-frame accesses under the unchanged buffer rules,
and the object may still be passed to callees that the buffer proof bounds.
Variable indexing of the stack object is not admitted by this profile: an
index that is not a known constant still refuses ("unsupported stack-alias use
or escape"); `named-data-buffer-stack-index-v1` below adds it under reviewed,
recorded runtime premises. The report states the conditional premises: immutable source
bytes, live ordinary destination and helper save frame, mutual disjointness and
no asynchronous modification. No physical stack, readability or C lifetime fact
is proved.

### Buffer owners that index private stack arrays under reviewed runtime premises

`--owner-runtime-profile named-data-buffer-stack-index-v1` is
`named-data-buffer-rom-table-copy-v1` plus one rule: a variable index into a
private stack array. Most such indices are a `u8` parameter, a struct field or
a callee result, so only the callers bound them and no in-function value range
can. The ordinary rules refuse them ("unsupported stack-alias use or escape",
"unsupported stack-address materialization"). The precedent is
`local-rom-halfword-table-v1`, which proves its owner under the explicit premise
`(entry_R0 & 255) < 4`. This profile generalises that contract.

```sh
python tools/match.py --root ../fftadecomp 0x080E3E84 --owner-runtime-profile named-data-buffer-stack-index-v1
```

**The bound is an unproved runtime premise.** Nothing is inferred from types,
callers or the callee's contract. For every variable-index access the verifier
tries, in order:

1. **Proof.** Unsigned intervals with a power-of-two congruence, `cmp` plus
   conditional-branch refinement and loop widening (the analysis used by
   `bounded-local-index-v1`) show every byte the access can touch is inside
   the array. Nothing is assumed and the access is listed under `accesses`.
2. **Premise.** Otherwise the index must have a *defined source*: an entry
   register R0-R3, a load through a defined address (a struct field), the value
   a call returned in R0, or a constant, combined by masks, shifts, adds,
   subtracts, ors and multiplies. The verifier then records one premise for the
   site, "whenever this site executes, the unsigned index is below K", and
   proves the access in bounds *under that premise*. An index reached through a
   join of different derivations, through a stack slot or through an unmodelled
   instruction has no defined source and refuses.

A premise constrains the value the index register holds when the site executes.
Its expression records where that value came from: `u8[(entry_R2 + 1)]@0x080E3FBA`
is the byte the instruction at 0x080E3FBA read through the entry R2 plus one.
It is not a claim about memory at any other time, and not necessarily about
the caller: a row is marked `may be owner-written` when a store through a
non-stack address, or a call, in the owner can run before one of its loads, so
the owner itself (or a callee) may have set the value.

**A premise admits nothing until it is reviewed.** The decomp root's
`config/stack_index_premises.json` holds one entry per function address with a
written review and the exact rows (site, expression, bound) the reviewer
checked against the callers:

```json
{
  "0x080E3E84": {
    "review": "phase 0 stores the selector, always 0..2; every caller ...",
    "rows": [
      {"site": "0x080E3FC2", "expression": "u8[(entry_R2 + 1)]@0x080E3FBA", "bound": 3},
      {"site": "0x080E3FD2", "expression": "u8[(entry_R2 + 1)]@0x080E3FCC", "bound": 3}
    ]
  }
}
```

Without an entry, or with one whose rows differ in any way, the selector
refuses and prints the generated entry to review and copy. A review that is
still the `<...>` placeholder, or that says `SCRATCH` or `TODO` in any case,
refuses, so a validation entry cannot ship. An entry for a
function that needs no premise refuses too. The accepted entry is bound in the
evidence and every row carries `premise_proved: false` and
`discharged_by: config/stack_index_premises.json`; replay re-reads the file, so
changing the entry, its review text included, invalidates the report.

The report carries one line per premise and the same rows in the evidence JSON.
Both are part of the fingerprint and replay re-derives them exactly, so a
removed, edited or duplicated line fails:

```
* stack index premise: site 0x080E3FC2 index u8[(entry_R2 + 1)]@0x080E3FBA < 3, array sp+0x10..+0x1c (entry_SP-0x30..-0x24) s=4, load width 4, unproved runtime premise, may be owner-written, accepted by config/stack_index_premises.json
```

The array is the object the compiler addressed. Its start is the
entry-SP-relative address the access has at index zero. Its end is the nearest
of the next origin in the function or the top of the frame's local words and,
for a load, the end of the run of bytes initialised on every path from that
start: a ROM table copy, an `stm` copy or plain stores. Origins are the
address-of-local forms `add Rd,sp,#k` and `mov Rd,sp`, ROM copy destinations,
and every local reloaded at a fixed offset, by `ldr Rd,[sp,#k]`, by a load
through an exact stack alias (`mov r2,sp; ldrh r1,[r2,#4]`) or by an `ldm`
from one: a spilled scalar is its own object and no premise may let an index
range over it. A store alone is not an origin, because agbcc at `-O2` reloads every spill it makes, while
constant-index element stores (`a[1] = x`) and aggregate copy tails write array
words through `str Rd,[sp,#k]`. The index of a scaled access (`lsls #2`) is
stated unscaled with the element size `s`. Every byte of the array must be an
allocated local word (never a saved register, an incoming argument or below
SP), and for loads initialised. Every address an admitted index reaches must be
the index-zero address plus a multiple of the access width, so an access that
is misaligned on every path refuses even when a premise could bound it. Reads
and writes are both allowed under the premise; a write through a variable
address initialises nothing, and it may not store a return-carrying value.

A variable stack address may be copied, moved by an immediate, combined with
further scalar indices or used as the base of one load or store. It may not be
stored, pushed, compared, held in R0-R3 or R12 at a call, or be live in a
return-visible register at a return. R12 is call-clobbered, so the analysis
cannot know its value after the call, yet a callee need not write it: an
address held there could survive the call untracked. As for R0-R3, it is
refused at the call. R4-R11 are carried across a call; that the callee does not
read them as data is the same unproved ABI premise the core's callee walk
makes. R12 is not return-visible, so a ranged address left in it at the
owner's return is admitted, as the core treats IP as ABI scratch at a return.
Escapes of an array's exact address are still the buffer
proof's business and refuse unless a callee is proved to bound them. Functions
with word-provenance or return-carrying local words are outside the policy, and
pointer-bearing local words only under the frame-words rule below. The policy
applies only to the owner itself, never to walked callees.

What the report does not claim: that any caller satisfies a premise (the
review records that a person checked, nothing proves it; discharging rows at
the call sites is future work), that the premise is the C array's declared
length (the extent is the compiler's object, so a source array shorter than its
object is not detected), the physical stack, source readability or
termination. The premise lines are the reviewable list of what must hold
whenever each site runs.

#### Frame words: spilled stack addresses and counters

Under register pressure agbcc spills what the analysis above tracks only in
registers. `func_080E4EB0` keeps the bases of four `s16[6]` arrays and the
element addresses `&x[i]`, `&y[j]` in local words (`mov r2,sp; adds r2,#0x1c;
str r2,[sp,#0x88]`, `str r1,[sp,#0x5c]`), and its `u8` loop counter at
`sp+0x48`, bounded only by `ldr r2,[sp,#0x48]; cmp r2,#2; bhi`. Without frame
words both selectors refuse such a frame: the core refuses every
pointer-bearing local word under a variable-index policy ("variable stack
indices exclude pointer-bearing or return-carrying local words"), the analysis
refuses a stored variable address ("ranged stack address escapes to memory"),
and a reloaded counter has no defined source.

`tools/stack_index_frame_words_profile.py` extends the analysis word by word.
It runs on the default path of both selectors, and only where the plain
analysis cannot be used: when the core deferred an exact stack-address spill to
it, or when the plain analysis refuses. A report the plain analysis admits keeps
its evidence, and a function both refuse keeps the plain refusal. Its
obligations, each with its refusal:

1. **Callee stack reach.** A callee's mapped ROM bytes are walked, with
   everything it calls: every instruction is ARMv4T Thumb (or SWI), SP is used
   only by `push`, `pop`, `add/sub sp,#imm` and `ldr/str Rd,[sp,#imm]`, and
   every return is proved to use the saved LR (a nested callee that may write
   the saved LR word unsaves it). The walk yields the bytes above the entry SP
   the callee may touch, the registers of R0-R3 and R12 it may read before
   writing, and those it writes on every path (a nested call surely writes only
   what every return of the inner callee writes). The only BIOS call the walk
   admits is SWI 6 (`Div`), under a GBATEK premise printed in the report; its
   handler stores R2 below SP, so R2 counts as read.
2. **Unread argument registers.** A variable stack address left in R0-R3 at a
   call is not an escape when the walk proves the callee never reads that
   register before writing it (080E4EB0 leaves `&x[j]` in R3 across the
   division wrapper `0x08141870`). After the call it is unusable unless the
   callee writes it on every path. The rule covers R0-R3 only, never R12.
3. **Pointer words.** A stack address (exact, variable, or a join that may be
   either) is stored only as a whole, aligned, allocated local word at a fixed
   offset; the word becomes pointer-bearing ("stack address stored outside a
   whole allocated local word"). An exact address is accepted only at a
   `str Rd,[sp,#k]` the core deferred, and the core then keeps no pointer slot
   for it ("exact stack address stored to a local word the core did not
   defer"; "deferred stack-address spill ... is not a tracked local word"). A
   word that holds a pointer on one path of a join only is treated as
   pointer-bearing ("mixed provenance").
4. **Reloads.** A whole-word reload yields the stored address as a value the
   analysis owns, so every use is checked here exactly as for a variable
   address: no escape to calls, memory, comparisons or returns, and every
   access through it inside allocated local words. Partial reads and stores
   and block transfers over a pointer word refuse ("partial read of a
   pointer-bearing local word", "partial store over a pointer-bearing local
   word", "block transfer over a pointer-bearing local word").
5. **Variable accesses avoid pointer words.** A proved range or a premise array
   that overlaps a word that may hold a pointer at that point refuses ("index
   range overlaps a pointer-bearing local word at entry-SP-n"). So a pointer word
   in a variable store's value hull is outside the range it may write, and keeps
   its value.
6. **Calls beside pointer words.** At a call while a pointer word exists, the
   callee is walked. A pointer word inside its reach, or any pointer word when
   the walk refuses, refuses the owner ("callee 0x... may reach the
   pointer-bearing local word"). So does a callee that may read a register
   holding a stack address ("receives a stack address"), since the core bounds
   its writes against slots it does not have.
7. **Release.** After `add sp`/`pop` releases a pointer word, a call or any SP
   move down refuses, so no released address is read back while the owner runs.
8. **Possible stack addresses.** The core keeps some registers as exact stack
   aliases that the analysis cannot pin to one value: the aliases a walked
   callee returns (on some return paths, in any alternative), which the core
   reports for every call site, and a join of an exact alias with a scalar or
   with another exact alias. The analysis holds each as the set of entry-SP
   offsets it may be (up to 16, moved by `add`/`sub` immediates and `stmia`/
   `ldmia` write-back), or as "any local word". A load or store through one may
   reach every candidate word, and a pointer-bearing candidate refuses ("store
   through a possible stack address may reach the pointer-bearing local word at
   entry-SP-n", and the same for a load). Spilled, one is a pointer word whose
   reload is unusable as a base.
9. **Element identity.** A load through an owned address is initialised when the
   same address value (one identity per defining instruction) was stored
   through at the same displacement with at least the same width on every path
   since; byte-level initialisation covers everything else.
10. **Scalar words.** A whole scalar word stored at a fixed offset keeps its
    value range but not its derivation. A register loaded from or stored to the
    word mirrors it until either is written, and `cmp` plus branch refinement of
    the register refines the word; a refinement never rewrites a pointer word.
    Every write that may reach a word ends its mirrors, whether the word is
    tracked or not, and forgets the scalar words it may overwrite: a variable
    store those in its value hull, a store through a possible stack address its
    candidates, a callee those inside its reach, or every one when it may read a
    register holding a stack address. A call walks the callee while a word is
    mirrored too, since a mirror held in R4-R11 survives the call. Joins keep a
    scalar word only where both paths track it.
11. **No premise on a constant.** No premise is stated on an index with no
    variable in it ("index is the constant N"): it is the same on every run, so
    the premise would be always true or always false. A reloaded constant word
    makes such an index common.

The report adds one line, bound in the fingerprint and re-derived on replay (080E4EB0's):

```
* stack index frame words: pointer-bearing local words entry_SP-0x68, ...; deferred exact spills 0x080E504C, 0x080E5052, 0x080E5058; 14 identity-initialised loads; 33 calls with ROM-walked callee stack reach (at most 0 bytes above the callee's entry SP), none reaching a pointer-bearing word; stack addresses left in argument registers the callee never reads: R3 at 0x080E50F6, ...; calls this analysis did not walk (0x080E4F58, ...): their results are trusted, as the core trusts every callee it does not walk, to hold no address into this frame; GBATEK premise, not proved from ROM bytes: BIOS SWI 6 (Div) takes R0 and R1 and returns in R0, R1 and R3; the SWI handler saves SPSR, R11, R12 and R14 on the supervisor stack, then switches into System mode so that all further stack operations use the user stack, the caller's, below its SP; it reads and writes no word at or above the caller's SP
```

`stack_index_frame_words_profile.POLICY` is the one switch: disabled, the core
and the plain analysis refuse exactly as before. The walk trusts what every
call in the kit already trusts: callees preserve R4-R11 and SP, and neither they
nor interrupt handlers read a stack word below their entry SP before writing it.
Like the core, the analysis also trusts that a callee it does not walk (other
than the authenticated ROM table copy helper) returns no address into the
caller's frame; the report lists every such call.

#### Version 2: forwarded callee stack arguments and sign-extended indices

`--owner-runtime-profile named-data-buffer-stack-index-v2` is v1 with two
additions. v1 reports keep their meaning: under v1 both stay refused, and a v2
report relabelled as v1 fails replay.

```sh
python tools/match.py --root ../fftadecomp 0x080DE9E0 --owner-runtime-profile named-data-buffer-stack-index-v2
```

At `080268DC`, a nine-case switch selects up to three unit-template slots
before a loop reads them. The verifier checks the switch targets against the
linked jump table and follows all nine cases plus the default. The loop index
must stay within initialized bytes on every incoming path. This leaf needs
no caller-supplied index bound. Run `tests/test_stack_index_owner_switch.py`
for the switch and stack-read regression cases.

**Forwarded stack arguments.** The coordinate wrappers `func_080DBD78`,
`func_080DBDA0` and `func_080DBDC8` take the owner's local `s16` outputs and
pass the last one or two on to their own callee as stack arguments
(`str r2,[sp]; bl func_0801C984`). The buffer walk refuses that store
("unsupported buffer pointer use or escape"). Under v2 an inspected callee may
store a pointer into the owner's frame into one aligned word **of its own
frame**, and the following call receives it as an ordinary incoming stack
argument. Every access through it is still bounded against the owner's frame.
The slot is tracked like a register alias, so joins must agree on its offset
and a slot still live at a return refuses. In addition:

* the store is admitted only in a callee whose every SP use is `push`, `pop`,
  `add/sub sp,#imm` or an immediate-offset `[sp,#imm]` load or store, so
  nothing reads the slot without the walk seeing it;
* a word reload of the slot yields the pointer again, a scalar word store
  kills it, and any other overlapping access refuses;
* a store into the callee's incoming argument area refuses (the callee's own
  core proof refuses it first), and a slot placed in a pushed register word
  refuses when that word is popped into a register;
* the next callee can reach the word only by `ldr [sp,#imm]`, which yields the
  pointer: its core proof refuses reading or writing above its entry SP
  through a materialised SP ("stack-alias access is unaligned or outside the
  tracked frame", "stack-frame write is outside the tracked frame").

**Released words.** The wrappers free the slot with `add sp,#4` in their
epilogue. That frees the word but leaves the pointer in memory below SP, where
anything that later moves SP down over it without writing it could read the
pointer as an unchecked scalar. v2 therefore keeps tracking every released word
until it is written:

* in the forwarder and in every walked callee, a read of a released word, or a
  partial write to it, refuses ("access to a released forwarded pointer word
  before it is written"); a word store or a `push` over it clears it. Moving
  SP down over it with `sub sp,#imm` is allowed only in a function whose every
  SP use is immediate; such a function can reach the word only by an immediate
  SP load or store, which the rule checks, so no read is missed;
* **every callee called while a released word exists is walked, and inherits
  the released words re-based to its entry SP** — even a callee that receives
  no stack pointer, when a released word is at or above its entry SP (its
  incoming argument area). Each callee returns the words it released to its
  caller. This is what makes the walk, not the premise, cover a callee that
  reads a re-covered word in its own frame;
* in the owner, which receives the released words below its SP, the selector
  refuses any SP decrement (`sub sp,#imm`, `add sp,Rm`, `mov sp,Rm`) reachable
  after the call that released them. It also refuses any walked call (one
  passing stack pointers) reachable after that call, because the owner does
  not pass the words down;
* only two kinds of code are left to an **unproved runtime premise**: a callee
  called without any stack pointer while every released word is below the
  caller's SP (so the word is not in the callee's incoming area and the callee
  is not walked), and interrupt handlers. The premise is that they do not read
  a stack word below their entry SP before writing it, and the same holds for
  everything a trusted callee calls. Walking every callee instead was tried: it exceeds the named-data buffer dependency budget on 080F7720, whose chain 080DD760 → 080DE268 → 080DE278 → 0809A2D8 is entered after the release, so these pointer-free callees are trusted rather than walked. It is **accepted without
  a per-owner reviewed entry** — unlike the index premises in
  `config/stack_index_premises.json`, which each need a reviewed row. It is
  recorded in the evidence (`forwarded_stack_arguments.premise`,
  `premise_proved: false`) and as one report line naming the released words and
  the trusted call sites:

```
* forwarded stack argument premise: released words entry_SP-0x54 after call 0x080FDCA0; trusted calls 0x080FDCA6, 0x080FDCD4, ...; unproved runtime premise: a trusted call (a callee called without stack pointer arguments while every released word is below the caller's SP; it is not inspected), including everything it calls, does not read a stack word below the trusted callee's entry SP before writing it, and neither do interrupt handlers, so no released forwarded pointer word is read
```

The evidence also lists every forwarded slot (callee, store site, callee
entry-SP offset, owner offset), the released words per owner call, and each
trusted callee call made while a word was released (`trusted_callee_calls`).

A trusted pointer-free callee that does read below its entry SP would not be
caught; that is exactly what the recorded premise covers, and a reviewer of a
matched function should confirm it for the listed call sites.

The forwarded slot is owned by the inspected callee, not by the owner; the
owner's own pointer words are the frame-words rule's, which refuses a callee
handed a stack address while one exists.

**Sign-extended scaled indices.** `index = (s8)f(); t[index]` with a word
element compiles to `lsls #24; asrs #22`. v1 knows nothing about an `asrs` whose
operand may be negative, so it cannot show the access is word aligned and
refuses. v2 keeps the congruence: the low `m - n` bits of `x asr n` are bits
`n..m-1` of `x`, which a congruence modulo `2^m` fixes. The range is not
narrowed, so the access still needs a premise. Under v2 every premise
expression is prefixed `(u32)`, e.g. `(u32)((ret(0x080FDCA6) << 24) >>s 22)`:
the bound is on the unsigned value of the scaled, signed index. A bound below
the table size therefore also excludes negative indices, and a reviewer has to
check that no negative value occurs.

### Buffer owners with stale aliases a callee overwrites

`--owner-runtime-profile named-data-buffer-dead-argument-aliases-v1` admits a
named-data buffer owner that leaves one of its stack aliases in an argument
register the next callee does not take:

```sh
python tools/match.py --root ../fftadecomp 080EA6F4 --owner-runtime-profile named-data-buffer-dead-argument-aliases-v1
```

`named-data-buffer-v1` follows every callee that receives an owner alias in
R0-R3, whatever its prototype. 080EA6F4 and 080ED4E8 call `0801E610(&a, &b)`,
which returns with `&b` still in R1, and then `080035F8(2)`. That function's
first R1 instruction is `ldr r1, =table`, but the walk enters it with the stale
R1 and refuses its own frame arithmetic.

This profile is `named-data-buffer-v1` with one step changed. Before a callee
is walked, an owner alias in R0-R3 is not passed to it when the callee's
indexed, validated bytes write that register before reading it. The check
scans the callee from its entry and stops at the first instruction that does
one of these:

* reads the register: the alias stays an argument;
* writes it: the alias is dead;
* is not one 16-bit ARMv4T instruction of an allowlisted form: the alias
  stays an argument.

The allowlist is register and immediate data processing, single loads and
stores, PUSH and SUB SP by an immediate. Everything else stops the scan:
* SWI, which capstone reports as reading only PC although the BIOS reads
  R0-R3;
* BKPT and UDF;
* any 32-bit decode. Capstone decodes Thumb-2, but on the ARM7TDMI `f04f 0100`
  is a BL prefix followed by `lsls r0, r0, #4`, not `mov.w r1, #0`;
* post-ARMv4T 16-bit forms;
* POP, LDM and STM;
* branches, calls and returns;
* ADD SP, which could move SP up into the caller's frame before a later
  PUSH, and any other write of PC or SP than SUB SP and PUSH.

So only a straight-line entry prefix that unconditionally overwrites the
register counts, and nothing in the callee can observe the alias. The scan
reads the callee's validated bytes without spending the walk's dependency
budget. When every
alias is dead, the call is a call that receives no alias, which the walk
already admits under its ordinary premise. Otherwise the callee is walked with
the aliases that remain.

The report lists every discounted register with the call site, the callee's
extent and body SHA-256, and the offset of the instruction that kills it. Data
literals are required and function literals refuse, as for
`named-data-buffer-v1`.

### Buffer owners whose callees run the known list queries

`--owner-runtime-profile named-data-buffer-known-query-callee-v1` admits an
owner whose stack buffers reach a callee that itself passes a 13-word array to
`08099CDC`, `08099D08` or `08099D34`:

```sh
python tools/match.py --root ../fftadecomp 0802C270 --owner-runtime-profile named-data-buffer-known-query-callee-v1
```

It is `named-data-buffer-v1` with two steps replaced. Data literals stay
optional; function literals and switches refuse.

* A callee that directly calls a pinned query root is inspected by the
  stack-buffer executor above instead of the leaf verifier, under the same
  pinned contract and the same premise of at most 13 nodes. The owner's
  aliases are then walked over that callee's instructions by the unchanged
  buffer walk, so every access through them is still bounded against the
  owner's frame.
* agbcc leaves the owner's pointers in R2/R3 when such a callee calls a list
  query. A call to a pinned family root (the three queries, the search
  `08099560` and the predicate query `08099544`) is summarized when owner
  aliases sit only in R2, R3 or R12. The bytes, extents and counts of every
  body the family can run are pinned, and four facts are checked on those
  bytes: no instruction reads or writes R3 or R12; the root writes R2 before
  reading it or reaching any jump, call, return or PC write; every direct BL
  stays inside the family; and every pool word is checked: an odd ROM, EWRAM
  or IWRAM word must name a family body, and an even ROM word or any EWRAM or
  IWRAM word refuses. R3/R12 aliases are returned unchanged; the R2
  alias is dead. That the thunks reach only the family's literal visitors is
  the hand-derived relation of the pinned bytes, recorded per family in the
  report, as in the contract above.

An alias in R0, R1 or LR at a family call, or a stack-passed pointer word,
refuses. A query call outside a callee run under the executor refuses whenever
any owner alias is live in an argument register (R0-R3, R12, LR) at the call,
because only the executor checks the 13-word R1 bound and forbids reading
R1-R3/R12 after the query. The report records
the contract, each executed callee, each family's identities and facts, each
summarized call with its dead and retained registers, and the explicit
conditions.


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
A caller whose stack buffer also reaches a callee uses the typed-data buffer
schemas instead (see "Typed named data beside buffer calls").
These checks establish relocation fidelity, not the safety of dereferencing a
mapped address. No game data should be copied into the symbol map.

### ROM wait-state mirrors

The GBA maps the Game Pak ROM three times: at `0x08000000-0x09FFFFFF` and at
its wait-state mirrors `0x0A000000-0x0BFFFFFF` and `0x0C000000-0x0DFFFFFF`.
Only the access timing differs, so a mirror word names the same code or data as
the wait-state-0 address it folds to (`value & ~0x06000000`). Every rule that
classes a literal word as ROM, as code or as an address needing typed
provenance folds it first (`tools/rom_mirror.py`):

- the typed address domain `[0x02000000,0x09000000)` of the complete-owner,
  data-buffer, scratch-overwrite and private-frame callee rules;
- indexed code entries and function spans in the thunk literal rules
  (`verify_literal_bindings`, `verify_data_bindings`, the own-span rule and the
  switch span checks) and in the function-address check of the switch and
  block-copy inventories;
- the reserved runtime identities (the `_call_via_rN` table, `__udivsi3` and the
  other pinned runtimes) and every own-function check on a bound object value.

A mirror word is therefore refused wherever its wait-state-0 word is. An untyped
mirror word needs typed provenance, and a mirror of a function entry needs
canonical function provenance, which is only ever the exact Thumb entry.
`config/data_symbols.json` refuses a mirror address, so a typed object's base
is canonical. An addend can still carry the bound value into a mirror. The
complete-owner, data-buffer, scratch-overwrite and private-frame callee rules
refuse such a literal as outside their typed domain. The addressed
signed-runtime data rule and the plain `elf-symbol-thumb-data-v1` and
`frame-data-v1` relocations keep it as a typed binding, with its name and addend
recorded; the folded span checks still refuse a mirror of indexed code or of the
caller's own bytes. Rules that admit only RAM or the loaded ROM image already
refuse mirror words. A mirror of `0x09000000-0x09FFFFFF`, beyond the 16 MiB
image, folds outside the typed domain, as that range itself does.
`0x0E000000-0x0FFFFFFF` is the SRAM/flash bus, not ROM, and is never folded:
words there, and masks such as `0x0FFFFFFF`, stay numbers.

### Library units

Some library objects in the ROM were prebuilt with settings other than the
game's `agbcc -mthumb-interwork -O2`. The decomp records each such object as a
row of its `config/library_units.json`; the range is a ROM fact, so the table
lives with the decomp, like `config/data_symbols.json`. The kit owns the
closed set of toolchains a row may name and all the checks:

| toolchain | compiler | flags |
|---|---|---|
| `agbcc-O0-v1` | `$HOME/agbcc/gcc/agbcc` | `-mthumb-interwork -O0` |
| `agbcc-O1-v1` | `$HOME/agbcc/gcc/agbcc` | `-mthumb-interwork -O1` |
| `old-agbcc-O2-v1` | `$HOME/agbcc/gcc/old_agbcc` | `-mthumb-interwork -O2` |

```json
{"units": [{"name": "agb_flash FLASH512_V130", "start": "0x0814189C", "end": "0x0814220C",
            "toolchain": "agbcc-O1-v1",
            "identity": [{"address": "0x0836CE28", "ascii": "FLASH512_V130"}],
            "proof": "0x0814195C", "evidence": "why this object was built so"}]}
```

The FLASH512_V130 bank-switch routine at `0814189C` writes four ordered bytes
to the cartridge command bus. Its `agbcc-O1-v1` report recompiles the
qualifier-stripped control, which drops the first unlock write. All three
native sector callers test for a 128-KiB device. IdentifyFlash's three ROM
setup records and its fallback describe 64-KiB devices, so those callers
skip the bank switch with the installed configurations.

SetReadFlash1 at `08141AB0` references its own Thumb entry, the adjacent
four-byte reader and the callback slot. Its unit verifier checks all three
bindings in both O1 literal pools before excluding the duplicate 12 bytes
and the two bytes of terminal alignment. It also replays the sector eraser's
64-byte local buffer, the callback publication and the two halfword writes.
The complete installer accounts for 62 ROM bytes.

Full-sector verification at `08141BE0` copies the 46-byte compare routine at
`08141BB0` and its two following alignment bytes into a 256-byte local.
The initialized 64-KiB flash descriptors select 4096 bytes per sector.
The copied routine returns zero on equality, otherwise the address of the
first differing cartridge byte. The four copied source literals in the O1
duplicate section are excluded from the 152-byte function extent.

The 152-byte size-limited entry at `08141C78` uses the same 48-byte copy.
Its program-and-verify caller preserves the unsigned byte count across the
sector program operation and forwards it to the local comparator. A count
of zero reads neither input. A difference just beyond the prefix is ignored.

ReadFlash at `08141B14` copies the 34-byte cartridge reader and two padding
bytes into a 128-byte local. The installed routine copies one byte per input
and output access, starting at the selected sector plus the caller's byte
offset. The game's header scan uses it to read 128 bytes into its own frame.

The same library unit compiles chip erase at `08141EB8` with
`--unit-toolchain agbcc-O1-v1`. Its six flash byte writes issue the chip-erase
command. All four setup records install the same callback and phase-3 wait.
The callback copies the four-byte reader into its 64-byte local buffer, polls
the first flash byte for `0xFF`, restores the WAITCNT low bits to three and
returns the wait result. The reader address remains published when the local
buffer expires. Stripping the six port qualifiers drops four writes and the
original wait returns `0xC003` on timeout with busy readback.

The sector programmer at `08142160` uses the same O1 library unit. IdentifyFlash
installs it for chip IDs `1B32` and `1CC2`. For sectors 0 through 15 it erases
one sector, reinstalls the local polling reader, and programs 4,096 bytes.
The original counter at `0200F374` decreases after each successful byte.
On byte-program failure it includes the byte whose write was issued and whose
poll failed. Invalid sectors and erase failures leave the incoming counter
untouched. The report assumes stable source bytes and the original exclusively
owned controller, timer and reader state during the synchronous operation.

The D4BF and fallback programmer at `08142000` copies the complete 36-byte
erase scanner into a 96-byte word-aligned stack buffer. It retries failed
erases or nonempty scans up to 81 times. A successful first attempt triggers
one additional erase, and a successful retry triggers six. The code discards
these additional erase results. It then replaces the first four bytes of the
local scan with the polling reader and programs the sector. Its O1 report
binds both copied-code boundary symbols, five direct calls and the progress
halfword. An invalid sector or exhausted retry loop leaves the counter intact.

The 154-byte flash ID reader at `081418C0` installs a four-byte reader in its
stack buffer. It enters ID mode with AA/55/90, reads the device byte followed
by the maker byte, and exits with AA/55/F0/F0. Both delays count 20,000 steps
in the same local halfword. At O1, removing the local qualifier puts the
countdowns in a register. Removing the port qualifiers drops the two initial
AA writes and the repeated F0. The three diagnostic builds and the original
bus and stack access sequences are checked separately.

* A row has exactly these keys. Addresses are canonical `0x%08X` text. The
  range is even, starts and ends on `config/functions.json` boundaries, holds
  at least two index functions (a unit is a library object, never one
  function), and no index function straddles it; every function inside is
  Thumb. Rows never overlap, and names are unique.
* `identity` holds at least one item the tool re-reads from the ROM: an
  `{address, ascii}` string of at least 8 characters, such as a library
  version string, or an `{address, size, sha256}` digest of at least 16
  bytes. An `ascii` item must be a whole C string: followed by a NUL and
  not preceded by a printable character. Two rows may not use
  overlapping identity bytes. A mismatch refuses the table. Neither form is
  checked to belong to the range: an `ascii` item is any such string at that
  address, and a digest of the span binds the row to this ROM. Which library
  a range is remains review evidence.
* `proof` is an index function inside the unit. `status.py` reports the row
  as needing attention unless that function is verified with the unit's
  toolchain and, compiled with the default toolchain, gives a different
  relocatable function (different `.text`, `.text` relocations or symbol).
  A row whose proof also builds under the default toolchain is reported as
  stale.

`match.py --unit-toolchain <id>` verifies an address with its unit's
toolchain. It is refused outside a unit, for a different unit's toolchain,
together with `--cc`/`--flags`, other toolchain options or non-default WSL
options. Unit toolchains support ordinary Thumb leaf, frame, direct-call, named-data
and function-address reports. The dp-bit packer supports its unit-bound logical
right-shift proof. The dp-bit constructor and component adder, fp-bit and dp-bit multiplies, and m4a memory command have their
own unit-bound proofs.
Below `-O2` agbcc also copies every literal-pool word into `.rodata`, where
nothing refers to it. Such a section is first authenticated with the
existing compiler-orphan prerequisite, then removed; the remaining `.text`,
its relocations and the function symbol must be unchanged. The excluded
bytes earn no ROM credit, and the report records the authentication.

The prerequisite admits two shapes of unit objects, and records each in its
inventory:

* A call through a function pointer, `bl _call_via_rN`. The name must be one
  of the ordinary call path's runtime helpers (`match.RUNTIME_HELPERS`,
  `_call_via_r0` to `_call_via_r14`), and the call is bound to the ROM: the
  ROM's BL at the call site lands on that helper's address, and the ordinary
  path's thunk check accepts the code there as `bx rN; mov r8, r8` for the
  same N. `call_thunks` lists each site, helper and thunk address with the
  ROM's SHA-256. Any other call name than `func_XXXXXXXX` or a runtime helper
  is still refused, and an address of a thunk is never data.
* One trailing alignment halfword. `as` pads `.text` to a word, so a function
  whose symbol size is 2 mod 4 is followed by one `c046` (`mov r8, r8`). It is
  admitted only when `.text` is exactly the symbol plus that halfword. It is
  not function bytes: the reached-instruction and literal walk, the text
  relocations and the owner's indexed span all stop at the symbol size, so a
  branch, PC-relative load or relocation that reaches it is refused, and a
  named-data or function address inside it counts as the owner and is
  refused. `alignment_fill` records its offset and bytes;
  `complete_text_bytes` is the symbol size. The ROM is compared over the
  indexed span only, so its own padding after the function is not read.
  Any other trailing bytes, two halfwords, or a halfword after a function
  whose size is a multiple of 4 are refused.

The fixed-O0 selector shares the prerequisite, so the alignment halfword is
admitted there too; its native linker still refuses `_call_via_rN` calls.

Inside a unit the default toolchain still verifies a function, but only when
the unit's toolchain emits the identical relocatable function: the same
`.text`, the same `.text` relocations (to named external symbols or the
function itself) and the same symbol. Otherwise
`match.py` refuses and points to `--unit-toolchain`. This keeps every
function in a unit consistent with its unit's toolchain while the specialised
profiles keep their fixed default toolchain. Outside every unit, any other
toolchain or flags are exploration: `match.py` prints the diff when the
object compiles and links, writes no report, and the verdict is
`NOT VERIFIED`, never a match; a saved report whose
`* compiler:` line names other flags is refused. The explicit fixed-O0
orphan-constant selector keeps its existing evidence scope outside units and
is also admitted inside an `agbcc-O0-v1` unit, never inside another one.

A unit report adds `* library unit:` (the canonical row), `* unit toolchain:`
and `* unit compiler SHA-256:`, and `* unit orphan constants:` when a
`.rodata` was excluded. Validation requires the current row, the same
compiler binary hash and the unit's compiler line. `status.py --verify`
and `rebuild.py --compiled` replay unit reports with their
`--unit-toolchain`, and the status block
lists each unit's functions apart from everything outside units. The
saved-report check recompiles a function that calls through `_call_via_rN`;
for a unit report it compiles with the report's unit toolchain and removes
the authenticated orphan constants first, as `match.py` does, and every
other report keeps the default toolchain. Without a
table, only the default toolchain and the fixed-O0 selector verify.

`old_agbcc` must be pret/agbcc's `-DOLD_COMPILER` build: the tool refuses a
binary that accepts `-fprologue-bugfix`, which only the new compiler has.
`make -C gcc old` in a tree that already built `agbcc` relinks the new
objects, so build it from a clean tree (see "Reproducing the reference
agbcc").

A decomp whose table names `old-agbcc-O2-v1` needs `old_agbcc` installed to
verify any function in that unit. Default-toolchain reports there are
admitted only through the consistency check, which compiles with
`old_agbcc`, so without it they are refused too. Unit reports bind the
compiler binary's hash, so they validate offline only where that binary is
installed. Library units need a POSIX host: the compiler is hashed and
probed on the host, not through WSL.

Other audited runtime calls inside a unit require object agreement with the default
toolchain. The verifier checks identity bytes and boundaries. The maintainer supplies
the evidence that a row covers a whole library object.

For dp-bit `__make_dp` at `0x08143958`, `--unit-toolchain old-agbcc-O2-v1`
authenticates the 3,552-byte library unit and the original 38-byte function.
The float extension at `0x08144350` passes the fraction in R3 and the word at
entry SP. The constructor copies these words, classification, sign and exponent
into its private 20-byte record. The original packer reads those five words.
The return restores LR into R3, adjusts SP and branches to R3. Replay binds the
single Thumb call relocation and excludes the compiler's two-byte alignment NOP
from the function extent. Native numerical tests cover signed zero, NaN payloads,
infinities, normal rounding ties and the original packer's truncated subnormals.

For dp-bit `_fpadd_parts` at `0x08142E10`, the same unit selector verifies
all 624 bytes and 302 reachable instructions. It checks two original Thumb
relocations to `__negdi2` and an ABS32 relocation to the fixed RAM record at
`0x03005E50`. Both original callers unpack into distinct component records,
call the helper and pack the returned record. Subtraction toggles the second
sign before the call. The helper can return either input, the output, or the
fixed record for opposing infinities. Only the output receives writes. When
the packer reads the fixed record, its five words are runtime inputs.

For dp-bit `__muldf3` at `0x081430F0`, the same unit selector checks the
684-byte function, its two unpack calls, four compiler-generated wide integer
products, final pack and fixed RAM literal. Two original conversion functions
contain three calls to the public binary64 entry. Zero times infinity selects
the RAM record at `0x03005E50`; the packer reads fields according to its
runtime class. Finite inputs use the original four-limb multiplication and
guard-bit rounding. The native tests also cover the historical packer's
truncation when a result falls in the subnormal range.

For fp-bit `__mulsf3` at `0x08143CEC`, `--unit-toolchain old-agbcc-O2-v1`
checks the original compiler-generated `__muldi3` call, two unpacks, one
pack and the mapped NaN-record literal. It verifies the 171-instruction CFG,
the frame on reached returns and the callee argument effects. Paths that
read the fixed 16-byte NaN record assume those four words are readable.
The report binds the compiler, unit, indexes, named data and ELF objects
and replays the source. The proof concerns machine behavior on reached paths.

For MusicPlayer2000's memory command at `0x0814636C`, combine
`--unit-toolchain old-agbcc-O2-v1` with `--switch-data-profile m4a-engine-track-thunks-v1`.
The original ELF supplies the 18-case table, mapped callback slot and canonical
r2 thunk. On engine entry, r1 names one of the 25 tracks registered by the
three ROM player descriptors, and the active stack is disjoint from the callback
word. The proof checks all stores on paths to the callback against those premises.
The indirect target must return under the ordinary ARM ABI. The saved report
binds the unit, compiler, registrations and engine code and recompiles the source.
The engine entry premise does not cover arbitrary external calls.

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

The explicit companion `--unsigned-quotient-profile positive-constant-frame-v1`
uses schema `elf-symbol-thumb-udivsi3-positive-constant-frame-v1`. It requires
a real fixed caller allocation, balanced stack/save/return provenance and
the existing bounded stack-alias checks, with unchanged nonzero constant
divisor facts. It admits optional ordinary mapped direct calls, including
outgoing word arguments, while retaining the exclusions above for other
runtime profiles, switches, object relocations and buffer proofs. It requires
the fixed approved Thumb toolchain and fresh source compilation on report
replay; a forged source digest cannot replace canonical ELF provenance.
The default profile remains frameless.

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

One guarded local jump table may coexist, under schema
`elf-symbol-thumb-divsi3-positive-constant-switch-v1` (on the default path) or
`elf-symbol-thumb-divsi3-positive-constant-frame-switch-v1` (with the framed
selector below). The table is the default switch path's guarded dispatch, derived
from the bytes by `switch_layout` with forward cases only. Its case edges are part
of the closed CFG on which the positive-constant divisor pass runs, so a divisor
that joins different constants across cases still refuses. The quotient manifest
gains a `switch` descriptor. Every replay rechecks it against the bytes, source
replay also requires the fresh ELF's switch relocations to equal it, and the
report carries no separate switch evidence. Data, function literals, thunks and
other runtimes still refuse beside a switch, and a frame still needs the framed
selector. `division_switch_profile.POLICY.enabled = False` restores the old
refusals.

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
The default signed-quotient path has no addressed-source exception or automatic
rewrite. The separate explicit addressed-runtime selector below makes no numeric
quotient claim.

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

### Explicit conditional addressed signed-runtime calls

`match.py --addressed-signed-runtime-profile addressed-signed-runtime-v1`
admits actual direct calls named `func_081426B8` and/or `func_08142950`, including
their mixed caller. The source contract is a signed32 word view of the actual
two input registers and returned word, such as
`s32 func_08142950(s32 numerator, s32 denominator);`. The original historical
formal types are not asserted. Every call is conditional on returning and
obeying the ordinary r4-r11/SP preserving ARM ABI. No numeric division or
remainder result theorem, operand-domain theorem, zero-divisor semantics,
universal termination or transitive ordinary-callee equivalence is granted.

This selector checks authentic complete helper and shared zero-hook bytes,
dependency calls, and both exact unique nonoverlapping function indexes. It
retains complete caller CFG and literal ownership, saved-register/SP/entry-LR
restoration, canonical original ELF call relocations, and the linker's exact
modification surface. Ordinary indexed direct calls and scalar fixed frames are
supported. Local stack aliases, buffers, callbacks, address literals, data or
function relocations, switches and other runtime compositions are excluded.
Compiler-generated `__divsi3`/`__modsi3` aliases remain outside this route.
Default and numeric selector restrictions are unchanged.

Reports bind source and headers, ROM, all three input snapshots, producer
sources, original/linked ELF and assembly hashes, and the fixed toolchain's
current executable hashes. Status verification restores the explicit selector;
report acceptance freshly compiles the captured source and reruns all checks.
Stale or mixed reports cannot substitute saved bytes for that replay. These
hashes record the executables used, not a platform attestation.

The separate opt-in
`--addressed-signed-runtime-profile addressed-signed-runtime-readonly-word0-v1`
adds only the existing read-only incoming word0 ABI contract: entry SP+0 must
provide one readable aligned 4-byte incoming ABI word, with unknown contents.
Caller allocation and readability are explicit premises. At least one reached
canonical Thumb word load must read exactly that word after accounting for the
saved and allocated frame. Reports bind the exact read sites/encodings, this
conditional premise, the entry-policy implementation and current Python,
Capstone and native tool hashes. Verification freshly checks the same selector
and runtime. Entry writes, other incoming words, unaligned or narrow entry
accesses, stack-address materialization and alias escapes remain excluded, as
do buffers, callbacks and other runtime compositions. This does not prove the
loaded value, allocation extent, numeric arithmetic or historical formal types.
The base addressed selector retains its incoming-stack-read refusal.

The separate opt-in
`--addressed-signed-runtime-profile addressed-signed-runtime-data-v1`
adds existing typed named-data linking to the conditional addressed-call ABI.
It requires actual original `R_ARM_ABS32` relocations against unique undefined
global object symbols in `config/data_symbols.json`. Original signed32 addends,
alignment, nonoverlap and complete ownership are checked. Linked symbols must
retain their absolute object type and mapped base, and each linked word must
equal that base plus its original addend. Only original call and data relocation
bytes may change during linking; the entire linked body must equal the ROM.
Every data word must be reached by a PC-relative pool load outside code, and
every reached address-domain word must have that typed provenance. Indexed code
and canonical call thunks cannot be relabelled as data.

Data identity supplies no physical readability, allocation, pointee type,
memory safety or C semantic facts. No numeric division/remainder or zero-case
theorem is added. This selector retains the complete CFG and frame/return checks
and excludes local buffers, stack aliases, incoming stack words, callbacks,
function literals, switches and other runtime compositions. It requires actual
data bindings; the base and read-only selectors keep their existing exclusions.
Reports bind the typed original addends, current data snapshot, actual producer
sources, Python/Capstone and native tool hashes. Acceptance rebuilds the original
ELF and rederives the bindings and complete linked body; status and publication
restore this distinct selector. Changes to inputs, tools or producer sources
invalidate the evidence.

The separate opt-in `addressed-unsigned-runtime-readonly-word0-v1` composes the
same word0 contract with the explicit unsigned runtime calls. It admits only
`func_08142AB0`/`func_08142B28`; signed and mixed calls, data, buffers and
callbacks stay with their own selectors. At least one reached canonical Thumb
word load must read entry SP+0. Entry writes, other incoming words, narrow or
unaligned entry accesses, stack-address materialization and alias escapes still
fail, and the base unsigned and unsigned native-buffer selectors keep their
incoming-stack-read refusal. Caller allocation and readability remain explicit
premises; loaded values, numeric results and historical formal types are not
proved.

Two four-word selectors use the existing read-only contiguous incoming-word
contract (`thumb-readonly-entry-stack-words-v1`) with exactly entry SP+0 to
SP+12. `addressed-integer-runtime-readonly-four-words-data-v1` is the four-word
sibling of `addressed-integer-runtime-readonly-three-words-data-v1`: explicit
mixed signed and unsigned runtime calls and actual typed data.
`compiler-signed-runtime-readonly-four-words-numeric-mmio-data-v1` adds the same
contract to `compiler-signed-runtime-numeric-mmio-data-v1`: compiler-emitted
signed runtime names, reached numeric MMIO literals and optional typed data.
Every declared word needs an actual reached canonical `ldr Rt, [sp, #imm]`.
Reads of other words, entry stores, narrow or address-forming entry accesses and
alias escapes fail. Caller allocation and readability are explicit premises, and
the loaded values are unknown. The reports bind the incoming-word implementation
with the other data producers. The base and three-word selectors keep their
boundaries.

The separate opt-ins `addressed-signed-runtime-thunks-v1` and
`addressed-signed-runtime-thunks-data-v1` compose the explicit
`func_081426B8`/`func_08142950` calls with compiler-emitted canonical
`_call_via_rN` callback calls. The data variant adds the typed named-data linking
above and requires actual data; the base variant excludes address literals. Each
selector needs at least one runtime call and one thunk call, and any number of
thunk registers may appear. Each thunk's `bx rN; nop` bytes and its two-byte
indexed owner are authenticated, and the original ELF must name it through the
compiler-emitted relocation. On every CFG path to a thunk call, the last write of
the target register must be a full-word `ldr` from memory through a base other
than PC or SP. This is a must-analysis over the closed CFG, and every call clobbers
r0-r3, r12 and LR. A constant, PC literal, stack word, entry value, register copy
or narrower load refuses. A Thumb `ldr` writes only r0-r7, so only those targets
can pass; `_call_via_r8` to `_call_via_r12` always refuse. The report records
each thunk site with its reaching load sites. No SP materialization is admitted,
so no target or argument carries a local address. The callee stays opaque: it is
assumed to return and to obey the r4-r11/SP preserving ARM ABI, as for the other
thunk selectors, and no callback identity, value or effect is claimed.

These two selectors also admit agbcc's same-owner long `bl` jumps. The
restoring-frame proof re-proves them, and the report records them as
`local_long_branches`; the other addressed selectors still refuse them. Fixed Thumb
frames with direct aligned SP words are admitted, as in the base selector. Sources
follow the `unsigned-divmod-thunks-v1` rules: runtime, call-via, asm-label, alias
and weak spellings are reserved for compiler emission, and the object defines only
its caller. Still excluded: local buffers passed to callbacks, compiler-emitted
`__divsi3`/`__modsi3` names, unsigned runtimes, switches, function literals and
incoming stack words. The r2 and r3 callback selectors keep their fixed producer
shapes.

The default path admits compiler-emitted `__divsi3`/`__modsi3` beside canonical
thunks. Its generic call binding still refuses a signed runtime next to a
`_call_via_rN` call, because that walk proves neither where a thunk's target
came from nor that no local address reaches it. On that refusal, a run with no
selector, the fixed toolchain and no library unit, whose original object names
both a compiler signed runtime and a thunk, is re-verified under
`compiler-signed-runtime-thunks-data-v1` (schema
`elf-symbol-thumb-compiler-signed-runtime-thunks-data-v1`). That proof
composes three existing ones: the compiler-runtime binding of
`compiler-signed-runtime-data-v1` (original compiler-emitted names, explicit
runtime identifiers refused in the preprocessed C, pinned runtime bodies);
everything `addressed-signed-runtime-thunks-data-v1` checks (target loads, no
SP materialization, authenticated thunks, local long branches, source
namespace), with actual typed data; and the unsigned runtime binding of the
explicit integer selectors, which neither of the other two has. Beside at least
one signed runtime, the compiler's `__udivsi3`/`__umodsi3` bind to
`0x08142AB0`/`0x08142B28` with their pinned identities. Unsigned runtimes
alone are neither routed nor admitted, and the other compiler selectors keep
their signed-only names. The data-free shape (a callback read from an incoming
object, as in `080178A4`) stays excluded: it is routed, then refused with
`compiler runtime thunks require actual typed data`. The report prints the
compiler runtime, thunk callee and named data premises. A refused route keeps
the plain refusal first: `<plain refusal>; compiler signed runtime thunks:
<reason>`. Status
replays the report by naming that selector, which also works by hand.
`addressed_signed_runtime_profile.COMPILER_THUNKS_POLICY.enabled = False`
restores the plain refusal.

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
instructions inside the complete caller. A case may precede the dispatch (agbcc
shares a `p += 2` block at a loop top this way) but may not land on or between
the comparison and the table's last word; the CFG still refuses a target in a
literal word or in the middle of an instruction, and walks the reached block like
any other. Exactly eleven schemas admit this, all through `verify_switches`:
`elf-symbol-thumb-switches-v1`, `elf-symbol-thumb-switch-data-v1`,
`elf-symbol-thumb-switch-data-v2` (multiple data), `elf-symbol-thumb-switch-data-u16-scalars-v1`,
`elf-symbol-thumb-switch-data-u16-scalars-fixed-frame-v1`,
`elf-symbol-thumb-switch-typed-outgoing-frame-v1`, the two fixed-pool
function-literal schemas `elf-symbol-thumb-switch-data-u16-scalars-functions-v1`
and `elf-symbol-thumb-switch-data-u16-scalars-functions-frame-v1`, and the three
fixed-pool thunk schemas `elf-symbol-thumb-switch-data-thunks-v1`,
`elf-symbol-thumb-switch-data-thunks-frame-v1` and
`elf-symbol-thumb-m4a-engine-track-thunks-v1`. The opt-in is
`allow_backward_cases=True` in `selected_switch_layout`, `verify_switches` and
`verify_leaf_instructions` (`backward_switch_cases=True`, passed by `verify_switches`
and the u16-scalar replay in `match.py`). `switch_layout` defaults to the forward
rule, so every other consumer keeps it: the inventory and owner-graph discovery in
`analyze.py`, the software-double, thunk-pool, BIOS and named-data buffer,
owner-graph, watched-switch and multiple-switch profiles, and
`verify_leaf_instructions` itself unless a caller passes the flag. The preloaded and
switch-constants profiles have their own layout rules. The schemas are not bumped:
an older kit refuses these inputs rather than accepting them.
Duplicate case targets are allowed.

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

### Dispatch-identified switch pools

`--switch-data-profile u16-scalars-v2` selects the separate
`elf-symbol-thumb-switch-data-u16-scalars-v2` schema. It keeps every rule of
`u16-scalars-v1` and changes only how the table pointer is found: by its use,
not by its position. The pointer is the word loaded by the dispatch's
PC-relative `ldr`, which is then indexed by the guarded, scaled selector. Any
number of words, bounded by the reach of that load, may sit between the
dispatch and the pointer. The layout must still be unique, with the same
exact unsigned guard, five-op dispatch, zero alignment halfword, complete
in-function table and forward local cases.

The interposed words gain nothing from their position. Each one is an
ordinary reached literal and must be bound like any other: a typed object
word through its named data binding, or an exact u16 scalar record under the
existing complete-reachable-u16 policy. At least one interposed word is
required; a word that is neither, or that no reached load reads, rejects. The
dispatch load must be the only reader of the table pointer. The alignment and
interposed words are reserved as data before decoding, so no reachable
instruction may overlap them.

The manifest adds `"pool_policy": "dispatch-identified-table-pointer-v1"`,
and the fingerprint is domain-separated by the v2 schema. Replay requires
both, and status forwards the saved selector. `u16-scalars-v1`, the other
switch profiles and their reports are unchanged: they still accept only their
fixed pool shapes. Frames, function literals, runtime thunks, signed or
32-bit scalar words (apart from the wide switch scalar words below) and
owner-level selectors are not extended by this profile.

### Dispatch-identified switch pools with outgoing-argument frames

`--switch-data-profile u16-scalars-frame-v1` selects the separate
`elf-symbol-thumb-switch-data-u16-scalars-frame-v1` schema. It keeps every
`u16-scalars-v2` layout and literal-binding rule unchanged: the table pointer
found by the dispatch load and read by nothing else, at least one interposed
word, and every reached literal bound as a typed object or an exact u16
scalar. It adds one thing, a fixed Thumb frame that holds only outgoing call
arguments 5 and up:

* exactly one constant `sub sp,#n`, reached before any call or frame access,
  and every return reached only after an `add sp,#n` of the same size. No
  other SP arithmetic, no `add sp,rX`, and no push or pop while the frame is
  live;
* no stack address in a register: any SP register operand (`add rX,sp,#k`,
  `mov rX,sp`, `add rX,sp`, an SP-based `ldm`/`stm`) rejects, as does any
  32-bit encoding other than a bound call;
* the caller only writes the frame, with `str rX,[sp,#k]` for word-aligned
  `0 <= k < n`. A read of the frame, before or after a write, rejects;
* each call consumes the words written since the previous call (or the
  allocation). That set must be a prefix of the frame, the same on every
  path to the call, and is empty again after the call, since a callee may
  overwrite its incoming arguments. A word still pending at the release
  rejects, and some call must consume the whole frame. Later calls are not
  shown to ignore stale frame words: only the frame stores since the previous
  call are attributed to a call, and no proof relies on frame contents;
* the per-path walk is bounded at 65536 `(site, phase, written-words)`
  states, and a function that needs more rejects.

Non-SP block copies keep their ordinary meaning, because no register can hold
a stack address. The ordinary direct-call ABI boundary is unchanged: nothing
is proved about a callee's arity or memory effects. Runtime call thunks stay
excluded. The manifest adds
`"stack_policy": "write-only-outgoing-argument-words-v1"`, the report carries
the stack-frame line, and the fingerprint is domain-separated by the schema.
Replay refuses relabelling between this schema and `u16-scalars-v1`,
`u16-scalars-v2` or `typed-outgoing-six-words-v1`, in either direction, and
status and rebuild forward the saved selector. `u16-scalars-v2` still refuses
every frame.

`--switch-data-profile u16-scalars-fixed-frame-v1` selects the separate
`elf-symbol-thumb-switch-data-u16-scalars-fixed-frame-v1` schema: the same
frame proof, unchanged, on the `u16-scalars-v1` fixed pool, where the table
pointer is the word after the dispatch. Every `u16-scalars-v1` layout and
literal-binding rule applies, with no function literal and no call thunk
(`_call_via_rN` stays refused as a runtime call thunk). It adds the two `#139`
literal rules the framed function-literal selector already applies: no
reached literal names the caller's own bytes except the table pointer, and
the dispatch load is that pointer's only reader. The manifest carries
`stack_policy` and no `pool_policy`; the fingerprint is domain-separated by
the schema, which `pool_policy` selects. Replay refuses relabelling between
this schema and `u16-scalars-v1`, `u16-scalars-frame-v1` or
`u16-scalars-functions-frame-v1` in either direction, and status and rebuild
forward the saved selector. `u16-scalars-v1` still refuses every frame.

### Wide switch scalar words

Every u16 scalar switch policy (the `u16-scalars-*` and `switch-thunks-*`
selectors) also binds a reached literal word whose value is at least
`0x10000000`, such as a binary32 constant (`0.5f` is `0x3F000000`) passed to
a float routine. GBATEK's memory map lists `10000000-FFFFFFFF` as not used,
and reads there return the prefetched opcode rather than mirroring a lower
region, so such a word is not itself a mapped address. One residual is a
stated premise: agbcc folds `sym + 0x80000000` (or `&arr[-0x10000000]`) into
one such literal word, so a source that hard-codes that linked value would be
admitted while its symbolic form is refused. The premise line says such an
offset is assumed absent.
Each word is recorded exactly, apart from the u16 words, as
`"wide_scalars": [[offset, value], ...]` under
`"wide_scalar_policy": "unmapped-bus-scalar-words-v1"`, and only when one
exists; the u16 `scalars` list may then be empty. Replay recomputes both lists
from the bytes. The report prints the premise as
`* switch wide scalar premise: ...`, exactly once and only when the manifest
carries the policy. A word above `0xFFFF` and below `0x10000000` is still
refused, and interposed pool words must still be typed objects or u16
scalars. Nothing is claimed about how the code uses the value.
### Switch function literals

`--switch-data-profile u16-scalars-functions-v1` and
`u16-scalars-functions-v2` select the separate
`elf-symbol-thumb-switch-data-u16-scalars-functions-v1` and `-v2` schemas.
Each keeps every rule of `u16-scalars-v1` or `u16-scalars-v2` respectively
(the fixed or the dispatch-identified pool) and adds one thing: reached
literal words holding plain function addresses, as when a case passes
`func_X` as an argument to an ordinary call. Without one of these selectors a
switch with a function relocation is still refused.

A function word is bound as `canonical-thunks-v1` binds a function literal.
The original ELF must carry a zero-addend `R_ARM_ABS32` against a unique
undefined global `func_<address>` naming one indexed Thumb entry outside the
caller, and the linked word must equal that entry with its Thumb bit. The
manifest records each word as `[offset, name]` under
`"function_policy": "canonical-function-literals-v1"`; replay re-derives the
value from the index and compares the word. Function words must be aligned,
complete, reached, outside the table and pool, and must not overlap a table,
object or scalar word. Interposed pool words must still be objects or u16
scalars. Every reached literal must be the table pointer, a typed object, a
u16 scalar or a bound function word. Neither a typed object's symbol
address nor its bound value (symbol plus addend) may be a reserved call thunk
or fall anywhere inside an indexed function span `[rom, end)`, the caller's
own span included. The two `#139` rules also
apply: no reached literal names the caller's own bytes except the table
pointer, and the dispatch load is the table pointer's only reader, in both
pool shapes.

A function word is a value only. It is never a call or branch target:
`_call_via_*` thunks remain refused, and an indirect branch through a loaded
literal fails the ordinary control-flow proof. Nothing is claimed about the
callee or about what the receiving call does with the pointer. The
fingerprint is domain-separated by the schema, a report under a function-free
schema cannot carry a function manifest (or the reverse), and status.py and
rebuild.py forward the saved selector. Thunks, signed or 32-bit scalars (apart
from the wide switch scalar words above) and
owner selectors are not extended.

`u16-scalars-functions-frame-v1` and `u16-scalars-functions-frame-v2`
(schemas `elf-symbol-thumb-switch-data-u16-scalars-functions-frame-v1` and
`-v2`) add the `u16-scalars-frame-v1` frame proof to the matching
function-literal selector, unchanged: one fixed `sub sp,#n` of write-only
outgoing-argument words, consumed as a prefix by the calls that follow, with
no stack address in a register. The manifest carries both
`function_policy` and `"stack_policy": "write-only-outgoing-argument-words-v1"`.
`-frame-v1` places that frame on the fixed pool layout. The frame proof does
not depend on the pool shape; without function literals, the fixed-pool frame
is `u16-scalars-fixed-frame-v1`. `u16-scalars-frame-v1` itself still
requires the dispatch-identified pool. Unframed function-literal selectors
still refuse a frame, and a framed report cannot be relabelled as an unframed
or function-free one.

### Switch call thunks

`--switch-data-profile switch-thunks-v1` and `switch-thunks-frame-v1`
(schemas `elf-symbol-thumb-switch-data-thunks-v1` and
`elf-symbol-thumb-switch-data-thunks-frame-v1`) admit the compiler's
`_call_via_rN` indirect-call thunks in a function with a guarded switch and
named data, such as a callback table `g_callbacks[0](a, b)` compiled to
`bl _call_via_r2`. Every other selector still refuses such a function with
`switch evidence excludes object, callback and runtime-thunk bindings`, and
`--function-address-profile canonical-thunks-*` still refuses it for want of
its own adjacent guard and five-op dispatch. The two families cannot be
combined on the command line; this selector composes their proofs instead.

Each selector keeps the complete-object-words proof of the switch-data family
on the fixed-gap pool layout: one unsigned-guarded table, every reached
literal word bound as the table pointer, a typed object or, when present, a u16
scalar (`scalar_policy` and `scalars` appear only if such words exist), the
backward-case and predecessor checks, and the ordinary conditional call ABI for
direct calls. `-frame-v1` adds the `u16-scalars-frame-v1` write-only
outgoing-argument frame proof unchanged (manifest key `stack_policy`); the
frameless selector refuses any fixed frame. The dispatch-identified pool
shapes (`-v2`) are not admitted. Function-address words, local buffers, other
runtimes and a second table stay refused.

The thunk binding is the one `canonical-thunks-v1` proves, reused rather than
reimplemented: the ELF symbol is the canonical `_call_via_rN` alias, the BL is
bound to its ROM address and the thunk's two ROM instructions (`bx rN`,
`mov r8, r8`) are hashed into `dependencies`. The manifest carries
`"thunk_policy": "canonical-call-thunks-v1"`, `thunks` as sorted
`[offset, "_call_via_rN"]` pairs and `dependencies`. A thunk BL appears only
in `thunks`; `calls` never names one, so each call is bound exactly once and a
manifest that lists the same site in both is refused. Replay recomputes every
field from the report's bytes, the ROM and the index, and compares
dependencies as canonical JSON, so `4.0` or `true` cannot stand for `4` or
`1`.

Three further rules keep a thunk from becoming an arbitrary jump:

* **Reserved identifiers.** A preprocessed source that names any `_call_via_*`
  identifier is refused before linking, as `canonical-thunks-v1` does. A source
  that calls the thunk's address as `func_08142248(...)` is an ordinary call to
  a runtime helper and is refused by the call binding.
* **No local code address as a target.** A forward pass over the verified CFG
  marks registers that may hold an address in the caller: taint enters through
  every load of the table pointer literal, any other read of PC or SP, the
  entry LR and the LR each BL leaves; it follows register operations and loads
  through a tainted address; no store may use a tainted register, and popped
  registers are tainted, so a local code address cannot be stored or reloaded
  from the stack. Constants are tracked as intervals: `movs`/`mov` immediates
  and every reached non-pointer literal word (its exact bound value, scalar or
  object address) feed add, sub, shifts and logical operations; a result that
  reaches the ROM range, or any other operation on a constant, becomes tainted,
  and a loop that keeps changing a constant is tainted after sixteen revisits.
  Only the registers a revisit changes are tainted: an entry whose joined state
  is unchanged keeps it.
  A constant combined with a loaded value stays constant-derived. At a join the
  interval covers the exact values of every incoming path that has one; a path
  where the constant met a loaded value adds none, so it cannot hide the others
  from the ROM check. `adds/subs rd, rs, #0` (and `movs rd, rs`) are register
  copies and carry the source's state over unchanged. Once a
  constant-derived value has been stored on a path (other than through SP, the
  verified write-only outgoing frame), every later non-literal load on that path
  is constant-derived too, whatever register or address it uses; the flag is
  not cleared by a call and a join is dirty if any incoming path is. Memory
  keeps the exact bytes those stores can leave (kit `#393`). An address is
  exact when its base (and index) hold one value on every path; it is taken
  mod 2^32 and the ARM7TDMI mirrors are folded (EWRAM, IWRAM, palette, VRAM,
  OAM, the I/O mirror and the ROM windows; SRAM, the cartridge GPIO port, the
  0x0D window and unused regions are no fixed byte; on this cartridge, with a
  FLASH512 save and a 16 MiB ROM, the 0x0D window is a plain ROM mirror, as
  kit `#406` folds it, so treating its bytes as unfixed is conservative). The
  cartridge ROM ignores writes, so no store leaves a byte there. A store at an
  exact address, forcibly aligned, replaces its bytes, and a store anywhere
  else may land on any byte, so its bytes and their count are kept apart. A
  load takes the exact values its bytes can hold in every layout the ARM7TDMI
  can produce: a misaligned LDR or LDRH is rotated, LDRSH at an odd
  address is LDRSB, a halfword or word read from SRAM repeats its one byte
  (with the same rotation on top, so LDRH at an odd SRAM address of byte b is
  b, 0, 0, b), and a load through a non-exact address may be at any alignment.
  An 8-bit store to palette RAM or BG VRAM fills both halves of its halfword,
  and one to OAM or OBJ VRAM is ignored (in the mode-dependent part of VRAM,
  either). So a constant stored, loaded back and shifted into the ROM meets
  the ROM check; a byte no constant store can have written makes the load
  constant-derived with no exact value. LDM and STM write their base back, with
  the ROM check on the new base. Interval addition and subtraction that wraps
  whole is taken modulo 2^32.
  **Thunk store premise.** Only where this sound walk refuses, a load through
  an address that is not exact on every path may be assumed to read back no
  byte this function stored as a constant; never a load at an exact address,
  nor one that may overlap a constant store through the same unchanged
  register or a copy of it (registers are matched by name and copy, not by
  value: after `adds r6, r5, #28`, a load through `r6` is not tied to a store
  through `r5`). The smallest set of such loads that admits the function is
  derived in address order, recorded in the manifest as `store_premises`
  (`[[load, [store, ...]], ...]`, offsets from the function) and stated once
  per load:
  `* thunk store premise: the load at 0x... through a non-exact address reads
  back no byte this function stored as a constant (stores at 0x..., ...)`.
  A report whose walk needs no premise has neither; replay re-derives the set
  and refuses a missing, extra or different record or line. When no premise
  helps, the sound walk's reason is reported. Not followed: a constant a DMA
  transfer copies elsewhere, and a constant combined with a loaded value
  (including a word only partly assembled from stored bytes), which is not
  checked against the ROM range. A thunk
  register holding any constant-derived value, including a literal word itself,
  is refused, so a callback must be a plain load from memory and cannot be
  loaded after a constant store on its path. Not followed: a callee copying
  memory, and a callee returning a pointer into the caller's outgoing frame
  (the frame words are exempt from the flag, so a load through such a result
  is a premise: callee results do not point into the caller's frame). A thunk BL whose register is tainted is refused. The
  table pointer literal must also be read only by the dispatch load, the caller's own
  bytes may not be named by any other literal, and no object or literal may name
  an indexed code entry, a byte inside any indexed function span (the caller's
  own included) or a reserved thunk (`verify_data_bindings` /
  `verify_literal_bindings` and the span check).
* **Decode.** The taint pass decodes every reached instruction itself. It
  accepts only the 16-bit ARMv4T Thumb mnemonics (so no `uxtb`, `sxth`, `rev`,
  `cps`, `setend`, hint `nop`, `yield`, `sev`, `blx` register, a hi-register
  `mov`/`cmp`/`add` encoding with two low registers, or an `stmia` whose
  writeback base is in the list but not lowest) and the bound BL pairs, and refuses
  `svc`, `bkpt` and `udf` (kit `#180`).

Premises that stay outside the proof, as for `canonical-thunks-v1`: callees,
including the target reached through a thunk register, follow the ordinary
returning ARM call ABI; a callee reached with no outgoing words takes at most
four register arguments; a callee's result is not a local code address of its
caller; a code address passed to a callee as an argument (r0-r3 or stack) and
kept in callee memory, or a constant-derived value copied by a callee, is not followed; and the callback register is not tied to
a callback object, since any mapped object load is admitted. Callback arity,
memory safety and termination are not proved. The
fingerprint is domain-separated by schema, a report cannot be relabelled across
the two selectors or to or from any thunk-free schema, and `status.py` and
`rebuild.py` forward the saved selector only after a fresh replay.

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

The exception holds for the access, not just the address (kit#357):

* **The direct form.** `*(volatile T *)ADDR` needs a scalar integer `T`
  (u8, u16, u32, s8, s16, s32, or a builtin spelling such as
  `unsigned short`), and the whole access must lie inside the window. A struct
  `T` is refused, since its members can lie past the window.
* **The bound form.** `volatile T *p = &symbol;` needs a scalar `T`, or a
  struct of scalars and pointers defined once in the same file. Its whole
  size, rounded up to 4 bytes as agbcc rounds every struct, must fit in the
  window from the symbol's mapped address. Every later use of `p` must be
  `p->member` or `*p`.
* **The access must stay a value.** The address walk reads tokens outward
  from the access (or from the use of `p`). It passes through what keeps an
  lvalue: parentheses, casts, the comma operator (GNU C lets it stand as an
  lvalue), the conditional operator, and `__extension__`, `__real__` and
  `__imag__`. It admits the access only when it reaches a context that makes
  it a value: an operator, an assignment, a call's argument, a condition, an
  initializer or a statement. A unary `&` on the way is refused, unless the
  address is converted at once to `void *` or an integer, as a DMA source or
  destination is: such a value reaches no memory without a new cast, and a
  new volatile cast is a qualifier of its own. The walk is a whitelist, so a
  context it does not model is refused too: `sizeof`, `__typeof__`, an
  object-like macro or an unknown name before the access. Keeping a
  register's address as a pointer is refused even where that would be safe;
  this is conservative.
* **The names.** The forms judge a type by its name, so the names must mean
  what the rules assume. A scalar name may only be declared as
  `typedef <builtin integer> NAME;` of its size, and in the preprocessed
  unit exactly once. `typedef` is read wherever it stands among the
  specifiers (`unsigned char typedef u8[2];` declares `u8`). A bound struct's
  typedef name must be declared exactly once, and every scalar name its
  members use must hold too.
* **Macros.** With `--addr`, the volatile census (below) gives every
  qualifier this exception admits a marker of its own. Each one must sit in
  cpp's output where the direct or bound form still holds. The binding's
  symbol must be the external data symbol itself: declared `extern`, and
  used only after `&`, so neither a macro nor a block-scope or file-scope
  declaration shadows it. A macro that turns the access into something else
  is refused: a scalar's name redefined as `s8 *)&data_x = 1, *(s8`, a
  binding taken apart by a function-like macro, or `&` before a register
  macro. The justification is checked where the qualifier is written; a macro
  can move a qualifier, but it cannot justify one.

**Line splices (kit#357).** cpp deletes backslash-newline before it reads a
token, so a file with a splice is checked twice: as written and with its
splices joined. A finding of either view is a finding, so an exemption holds
only where both views admit it, and a token split across a splice
(`a\` newline `sm`, `whi\` newline `le (0)`) still meets its rule. A finding
only the joined view makes is reported on its logical line's first physical
line and marked as such. A file without a splice is checked once.

**Every spelling of the qualifier (kit#93).** agbcc reads `volatile`,
`__volatile__` and `__volatile` as the same qualifier (`gcc/c-parse.gperf`).
The `volatile` rule refuses all three. Every exception (the hardware forms
above, the allow list below and the per-file modules) accepts only the plain
spelling, so a compile that strips `volatile` strips the qualifier entirely.
`plausible.VOLATILE` is the one pattern every check uses. Alongside it:

* the `inline-asm` rule refuses each of agbcc's asm keywords (`asm`, `__asm`,
  `__asm__`) as a token, wherever it appears in code: `__asm("")`,
  `asm const ("")` and `register int r __asm("r4");` included;
* a NUL byte is refused anywhere (`nul-byte`): cpp reads it as whitespace, even
  inside a line splice;
* in a file with a line splice, the hardware exception and the statement-macro
  exemption hold only where they also hold with the splices joined, as cpp
  reads the file, and the polling exemption needs no splice anywhere in it;
* `preprocessor-probe` refuses every `__has_` operator (`__has_include`,
  `__has_include_next`, `__has_embed`, ...), `#embed` (also as `%:embed`, or
  with comments before `embed`) and `__TIMESTAMP__`, looked for with
  backslashes and whitespace deleted. No gcc 2.95-era source uses them. This
  is defence in depth, not what makes the census below sound: token pasting
  builds a query that no scan of the text can see (`CAT(__ha, s_include)`).

The rules read source text, but agbcc reads what cpp makes of it. So when the
lint runs with `--addr`, `plausible.py` also takes a **volatile census** of the
addressed source's translation unit. It preprocesses the source as match.py
does. If the unit holds a qualifier, it preprocesses it again from a copy of
the files the unit reads, where every qualifier in the lint's code view is
renamed to a marker of the same length. The markers are drawn at random on
every run, and are redrawn until none occurs in any input (as written, or with
backslashes and whitespace deleted) or in the real unit, so no source can
spell one. That is the census's guarantee. A source that can tell the copy
from the tree, by a pasted query or any other means, can make the copy take
another branch. But it cannot make the copy produce a marker where the real
unit holds a qualifier that the lint did not read, so the comparison below
refuses it. The one exception would be a macro that carries an exempt
qualifier somewhere else, and that needs no detection at all. For the
hardware exception, the placement check above refuses it (kit#357). The
source is refused (`volatile-census`) when:

* the copy still holds a qualifier: token pasting, a line splice, or text the
  lint reads as a comment or literal (kit#129) made it;
* a marker was pasted into a longer token;
* the copy, with each marker mapped back, differs from the real unit in any
  byte;
* the unit reads a file this run does not lint, or one file under two names;
* a candidate input holds a preprocessor query (defence in depth, as above);
* the unit also uses `typeof`, which can copy the qualifier onto an object the
  source never qualifies;
* the census cannot run.

The census also refuses an asm keyword (`asm`, `__asm`, `__asm__`) anywhere
in the unit outside a literal, as `inline-asm`, so a line splice or token
pasting cannot hide one from that rule. Before that scan it refuses a string
or character literal that runs past the end of its line, as
`multiline-literal`: cpp ends one there, with only a warning, but agbcc reads
on into the next line. It is skipped when no file the compile
may read (the source, `src/**/*.h`, `include/**`) holds `volatile`, `asm`,
`##`, `%:`, `??=` or `??/` once backslashes and whitespace are deleted. Its
scratch files live under the tree's `build/`, like match.py's workspaces. It
runs `plausible.CENSUS_CPP`, which a test keeps equal to `match.DEFAULT_CPP`,
from the tree's root. It imports match.py only on Windows, to run through
`match.Runner` without `wsl_path`, so on WSL `cpp` must be on the login
`PATH`. Elsewhere the lint never loads match.py's profile modules.

What the census proves is where each qualifier came from: every qualifier agbcc
compiles is one the lint read, in code, in a file this run lints, and so was
refused or exempted by an exception above. Where a hardware-exempt qualifier
ends up is checked separately, as described above (kit#357). Qualifiers that
the allow list and the per-file modules exempt are placed by their own pins. The census runs
wherever the lint runs with `--addr`: match.py's ordinary path (and so
`status.py --verify`) and every profile that lints a captured copy. It does not
run for 0x08001244 (`oam_list_context`, whose `-include` prefix units it does
not model) or for the reviewed-source selectors (`flash_*`, `unit_double_*`).
Those pin their sources' tokens or digests instead. A word `volatile` in a
string literal or in an input's path counts as a qualifier the copy keeps, so it
is refused. So is a unit that uses `__DATE__` or `__TIME__` if the two runs
straddle a second.

For the m4a function `src/08145CAC.c` (CgbSound), the five channel-register
pointers have a separate check in `tools/cgb_registers.py`. The channel loop
must select all five byte addresses for each of the four channels before the
first access. Every later use must dereference the selected pointer directly.
The check validates the literal register matrix, the base byte type and the
source macros. It permits the qualifiers on those five declarations and
twenty fixed assignments. Direct wave RAM and sound-control accesses still
need their own hardware justifications.

The boot routine at `08000718` programs DMA0 to copy 39 halfwords from
the LCD shadow at `03000942` to BG0CNT through BLDY (`04000008..04000054`).
The `agbcc-O0-v1` frame/data report records the three 32-bit register
writes, the immediate control readback, and a fresh control read on every
iteration. Bit 31 set retries the poll. A clear bit reaches the halfword
copy from the DISPCNT shadow at `03000940` to `03002BBC`. A permanently
busy DMA channel stays in the loop. Replay checks the original two IWRAM
relocations, the complete 112-byte function against the ROM, and the
qualifiers on the two block-local MMIO pointers.
Run `python3 tests/test_boot_dma0_shadow.py` with agbcc installed.

At `0813FB7C`, the palette fill uses the SDK's CpuFill16 idiom. The
qualifier is confined to the halfword initializer in the reviewed source
and base-header closure. The Thumb caller saves the destination, calculates
the low halfword from the eight color bits, stores it once at entry SP-8,
and passes that live address to the returning CpuSet wrapper. The literal
control selects a 16-halfword fill. The conditional BIOS interface supplies
the source read; physical destination validity and BIOS completion remain
caller and platform premises. The existing
`addressed-native-bios-fill-buffer-v1` report records the store and call
sites, local width and control. Replay repeats the source and native checks.
Run `python3 tests/test_sdk_cpuset_halfword.py` with agbcc installed.

At `081457FC`, the mono m4a `m4aSoundVSyncOn` source resets the
historical `volatile u8 dmaCounter` at mixer offset four. The USA VBlank
dispatcher selects slot 2 of the installed callback table and calls
`08144AF0`. The handler reads the byte through the mixer pointer at
`03007FF0`, decrements it, and reloads it from offset eleven when its
counter expires. The foreground owner writes the DMA1 halfword register
and reads the counter immediately before zeroing it. The fixed m4a unit's
`old_agbcc` build with only the counter qualifier removed drops precisely
that read. Both complete instruction streams, literal destinations, and
original mixer-pointer relocations are checked. The report records the
IRQ and owner access sites and both body digests. Replay repeats the
two compilations. These checks establish the accesses under their
respective lock guards. Interrupt timing and interleaving are unspecified.
The register cast still requires the ordinary documented-MMIO rule.
Set `FFTA_M4A_VSYNC_ROOT` to the game checkout to run the native
cases in `tests/test_m4a_dma_counter.py`.

**Allowlisted volatile RAM (kit#90):** volatile RAM is otherwise
allowed only for an object on the maintainer's `tools/volatile_allow.json`
(agents never edit it). An entry names a symbol, its address, one header, the
member types that may be volatile and the object's complete declaration. Only
that header may declare the object, exactly once, as a file-scope anonymous
`extern struct { ... } symbol;` whose tokens equal the pinned declaration, so
any change to the layout needs a maintainer edit of the list. Inside the
braces `volatile` may only begin a full-width bit-field member of a listed
type (`volatile u8 name : 8;` or `volatile u16 name : 16;`; any other width,
or a type the kit has no width for, is refused): bit-fields have no address, and the declaration
holds no nested, tagged or parenthesized types, so the qualifier reaches no
other object. The exemption applies only while `config/data_symbols.json` maps
the symbol to the listed address, and only to the header at its listed project
path or to a replay's byte copy directly under `build/<capture>/`.

Volatile in any `src/` file, elsewhere in the header, in another header, or on
another object still fails. While an entry is active, every linted file is
scanned with line splices joined as cpp joins them (a backslash, optional
spaces or tabs, then a newline) and refuses: form feeds, vertical tabs and
lone carriage returns (cpp treats them as whitespace around directives); token pasting (`##`), digraphs
and trigraphs; `typeof`; `#line`, linemarkers, `#import`, `#include_next` and
computed `#include`; `#define`/`#undef` of any identifier of the pinned
declaration (`u8`, member names, `struct`, ...) or the entry's include
guard; and any `#define` whose
replacement names the symbol; and any `#include` that resolves outside
`include/` or to a non-header under `src/`, which the sweep would never lint.
Other headers may not name the symbol, and every
use must be `symbol.member`, so neither its address nor the whole object reaches pointer
arithmetic, a macro or a copy. Pinned bytes must be reachable only
through their own members. An array member may only be written
`symbol.array[literal]` with the literal inside its bounds, so decay, pointer
arithmetic, `k[symbol.array]`, `(symbol.array)[k]`, `[2]` past the end and
`[-1]` are all refused. Decimal, octal and hex literals are read as C reads
them. No `&` may precede the symbol, through any number of `(`, whether it
is unary or binary. That rules out every way of taking a member's address
(`&symbol.member`, `(u8 *)&symbol.display`, `__extension__ &symbol.x`,
`memcpy(&symbol.display, ...)`), and a bitwise AND must put the member first
(`symbol.x & a`, not `a & symbol.x`). A file that uses the object may not
contain a cast or type name with a struct or union body, or an abstract
`(*)` declarator, since either can reinterpret the object. These member
checks run on C tokens. match.py repeats them on the preprocessed text, so a
macro cannot spell the member or the `&`. As defence in depth, neither a
file that uses the object nor any header in its include closure (other than
the listed one) may define a macro whose replacement contains `&` or any
identifier of the pinned declaration. While an entry is active, no
object-like macro may contain `#`, and no `#` may appear outside a directive
line (after joining splices, outside literals, so `F(#) pragma ...` is
refused). Together these mean a macro cannot forge a linemarker or
directive (`#define H #` then `H 1 "include/x.h"`). In a function-like macro
`#` can only stringize a parameter. The only exemption is a file with its own
file-scope `extern` declarator of the symbol (a parameter name does not
count) whose include closure does not reach the listed header, so a
declaration hidden behind `#if` exempts nothing. The single
listed object is `g_control_flags_03000940` (`0x03000940`,
`include/control_flags.h`, `u8` and `u16`), the game's RAM image of the LCD
registers: `08000718` DMAs `0x03000942` to `0x04000008` (BG0CNT) as 39
halfwords, so its members are named after the registers they shadow. Every
halfword store to `+0x02..+0x39` and every byte store to `+0x3A..+0x4E`
carries a dead load of the same member throughout the ROM and on no other
RAM; the DISPCNT copy at `+0x00` has plain stores and stays non-volatile.

When the addressed source reaches the listed header through its include
closure (an over-approximation of the preprocessor's dependencies, since
computed includes are refused), or names the symbol without declaring it,
match.py also runs a **semantic check**
(`tools/volatile_semantics.py`). It compiles the source a second time with
`volatile` removed from exactly the pinned declaration in the preprocessed
text (which must occur there exactly once; the preprocessor rules above keep
it intact). Removing the qualifier changes register allocation and address
arithmetic, so the two bodies are not diffed as text. Both are executed
symbolically along every path, and the check requires:

* the same observable behaviour: the same non-stack stores with the same
  values in the same order, the same calls with the same arguments, the same
  branch conditions (a condition and its inverse are one decision, since
  agbcc writes a far `beq .L` as `bne .LCB; b .L`) and, for a non-void
  function, the same return value.
  When a stack address escapes (as a call argument or a value stored to
  memory), every local frame byte at that moment, with the stores applied in
  program order, is part of the behaviour too, relative to the first
  escaping pointer and re-snapshotted at each escape. That includes slots
  in the incoming-argument area. Every callee needs a file-scope prototype
  with a fixed argument list. A callee with no prototype, `()` or `...`
  fails closed. An indirect call (`bl _call_via_rN`) is compared like a
  named one only when rN holds a word loaded from an element of a file-scope
  function-pointer object or array whose declared type (a unique direct
  typedef or a direct `R (*name[N])(params)` declarator) is such a
  prototype, every use of that object in a body is a direct call
  `name[K](...)` (or `name(...)`) with a literal index and the prototype's
  argument count, and rN is not one of those argument registers. Casts,
  copies, `(*name[K])`, computed indices, unprototyped or variadic pointer
  types and callback-typed parameters of the pointer's own prototype fail
  closed. A named callee is held to the same use rule: every use of it in
  a body is `name(` with its declared argument count, so a cast or a block
  `extern` redeclaration fails closed, and its prototype must come before the
  body that calls it. match.py also compiles with
  `-Wimplicit-function-declaration -Wnested-externs` (any `-w` dropped) and
  refuses those two warnings; agbcc's output is unchanged. A call-site
  index must be written as digits. Declarations are read from the preprocessed
  text with directive lines and comments blanked and each literal reduced to
  `0`; the object's member checks (whole-object uses, array indices) still read it
  with literals blanked to spaces, so `unknown_48['\x02']` is refused. Digraphs,
  `asm` labels, unbalanced braces and literals that cross a line fail
  closed. A declaration may rely only on typedefs that precede it (before
  its typedef, cc1 reads a type name as an old-style identifier list, and
  match.py also refuses cc1's "parameter names (without types)" warning),
  and a non-keyword scalar typedef name (`u32`, `bool32`, ...) counts as one
  word only through a file-scope typedef to a one-word scalar. The call
  stays opaque and an ordered barrier, and the report adds `indirect calls
  typed by declaration: name as N arguments`. Every parameter and return
  value must be one scalar or pointer word, so `long long`, `double` and
  struct-by-value fail closed. The arguments, stack words included, are
  compared by that count. No prototype is trusted to name every register
  the callee reads: a lying one, or a callee whose own source hides
  parameters behind a macro, would let the qualifier's dead load pass a
  hidden argument. So every call counts as reading r0-r3, and a dead load
  is accepted only if its register is overwritten before the call, unless
  the callee's own ROM code shows otherwise. For `bl func_XXXXXXXX` (the
  name the byte match links to that address) the callee must be an indexed
  Thumb function whose CFG `analyze.refine_function` closes over its indexed
  span. A dataflow pass over that CFG then gives the argument registers some
  path reads before writing (pushes and stores count as reads) and those
  every path overwrites before returning. A call inside the callee reads and
  writes what its own callee does, transitively, up to 8 levels and 64
  callees for each called name (the budget restarts per name, so the budget
  spent on earlier calls no longer cuts later ones short). Recursion,
  a CFG that does not close, a word switch, an unindexed or ARM target and
  anything unmodelled leave the strict rule in place. A
  register the callee never reads carries nothing into it, and one it
  overwrites on every path carries nothing out, so a dead load there is
  dead across the call. A register it leaves alone stays live past the call,
  so a later read of it uses the load. The report lists each interface a
  dead load relied on as `callee interfaces from ROM: func_X reads {...}
  writes {...}`. Only ROM bytes and the function index
  are read, never source. Only the libgcc division helpers have an exact
  interface otherwise;
* every access to the object to be `symbol + constant` inside it: an
  address that adds a variable term (`(&sym)[n].x`, a variable subscript),
  lies outside the object or comes from a multi-register transfer fails
  closed, as does the object's address reaching a call argument or a stored
  value;
* every load of the object in the real compile to be one of:
  - a **read-modify-write load**: an unsigned load of a pinned member at its
    offset and width (`ldrb` of a byte, `ldrh` of a halfword) whose
    destination is overwritten before any use, followed by its store of the
    same width to the same member with nothing in between but constant
    materialisation (immediate `mov`s, and arithmetic on known constants such
    as `mov #128; lsl #1` for a halfword `0x100`, whose result must reach the
    store's value register through copies) and copies or literal loads whose
    result reaches the store's own operand registers through copies. agbcc computes any other stored
    value before the load, and 08028C34, 08050D50, 08050DA0, 08122C6C (bytes)
    and 080034B8, 080032F8 (halfwords) show exactly this shape. The scheduler
    may also move unrelated register operations in (0813F934, 0813F9F8:
    `movs r0, #0; mov r8, r0` for a later value): an operation outside the
    backward slice of the store's operands is admitted if it touches no
    memory beyond a literal pool, is live on every explored path (its
    result reaches a store outside the frame, a named call argument or a
    branch's flags) and writes neither a register the store reads nor sp/pc
    (an immediate `mov`, as before, may write one that the store's own
    operands later overwrite). Nothing in between may read the loaded value,
    and no memory access, call or conditional branch may intervene. The
    scheduler may also finish the stored value after the load (080EA6F4,
    080ED4E8: `ldrb r2, [r3]; orrs r0, r1; strb r0, [r3]` for
    `sym.x = f(2) | 0x40`): a register ALU operation in the store's slice is
    admitted if it feeds only the value register, not the address
    registers, writes neither an address register nor sp/pc, and its flags
    reach no conditional branch. As nothing in the window reads the loaded
    value, its inputs cannot carry it, and the stored value stays the one
    the stripped compile computes. Before
    a store of the member's all-ones value the window keeps only the
    narrower forms: agbcc may fold that store's own load away (081175D4
    keeps it), so a dead load before one may be planted;
  - a **chained re-read** for `a = (b = v)`: a load of the member, at its
    width, whose store is the immediately preceding memory access, with only
    register arithmetic in between, whose value reaches, through copies only,
    the next store, a store to a pinned member at that member's width. Only
    that store's own read-modify-write load may intervene, and the value is
    used nowhere else (08122C6C);
  - a **tested update re-read** (`tested-update-reread-v1`,
    `tools/volatile_tested_update.py`) for `if (sym.x < 16) sym.x++;`: the
    source reads the member twice, for the test and for the update, and only
    the real compile performs both reads (0812BA08, 080BA8E4). The re-read
    is an unsigned load of the member at its width, not forwarded from a
    store. The nearest earlier memory access is a load of the same member
    with the same value in the executor, with only register operations,
    literal loads and branches in between. A conditional branch there reads
    flags set by a comparison (`cmp`, `cmn`, `tst`) of that value or of an
    unchanged copy of it, or by such a copy itself; the flags of a value
    computed from it (`lsl r3, r0, #24; bmi`) are no test. The re-read
    feeds, through copies only, one `add` or `sub` of an immediate that is
    not zero at the member's width. Its result is stored back to the same
    member, with only that store's own read-modify-write load, register
    operations that neither read nor overwrite the value, literal loads and
    unconditional branches in between. Neither the value nor the update's
    flags may be used after the store. Such a load becomes an optional
    counterpart, like a forwarded re-read below, but only where the pairing
    of counterparts without it fails, and it is listed only if it stays
    unpaired. A source that passes without the rule keeps its record, and
    one that no skip pairs up keeps its refusal. The report lists these loads as `tested-update
    re-reads at [...]` and prints the rule's premise: nothing writes the member between
    the update re-read and the read of it just before, which the branch
    tests, so in ordinary memory the stripped compile's reuse of the tested
    value computes the same update. The overwritten-store composition, which
    pairs traces itself, admits no such load.
    `volatile_tested_update.POLICY.enabled = False` restores the refusal;
  - a **counterpart**: matched in order to the stripped compile's loads of
    the object, with the same address, width, signedness and executor value,
    and after the same number of trace events (kit#378). The count covers
    every observable event the traces compare: stores and calls, and also
    escapes, returns and loop markers. So both loads of a pair are the same
    read: they read the same value in ordinary memory, and neither crosses
    such an event to reach the other. Under the
    overwritten-store composition, the events are first renumbered through
    its map of the surviving events.
  - A chained, ordinary-store or same-member constant re-read is an optional
    counterpart. Where paths with different values of the member meet, the
    stripped compile reloads it, and such a re-read pairs with that reload
    when the pairing needs it. Otherwise it stays unpaired, which is what
    explains it as the qualifier's read, and only then is it listed in the
    report. So the reload cannot pair with a different, unexplained read of
    the member instead.
  - Where the loads line up by address and width but a pair does not, the
    check refuses with `... and the stripped compile's load there reads a
    different value; the qualifier added a read`, or with `... lies across a
    store or call from it; ...`;
* every access overlapping a pinned member to be exactly that member, at its
  offset and width (a byte of a halfword, a halfword over two bytes and a
  word over two halfwords are refused), and every such store to carry its
  own read-modify-write load. The one exception is a store of the member's
  all-ones value (`0xFF`, `0xFFFF`): agbcc's combine pass folds the
  bit-field insertion `(ior (mem/v x) 0xFF)` to the constant and drops that
  store's load, depending on register allocation (081175D4 keeps the load
  of its second `0xFF` store and drops the first). Such a store is admitted
  only when the permuted compile is checked and the store follows its
  member there, so an alias all-ones store through another member, the
  base, a cast or an index read back from a typed copy is still refused.
  The report lists such stores as `unloaded all-ones stores at [...]`. When
  register allocation differs so that the permuted compile keeps a load
  that the real compile drops (or the reverse), the object accesses differ
  and the source is refused: a false refusal;
* no store to write back the value just loaded from the same member (an
  `ldrb`/`strb` or `ldrh`/`strh` self-assignment).

**Provenance by layout perturbation.** The real and stripped compiles alone
cannot tell `(void)sym.x; *(sym.unknown_02 + 0x3A) = a;` from `sym.x = a;`,
because both compile to the same instructions. So match.py compiles the
source a third time with the pinned declaration rewritten: the pinned
bit-fields swap places among their own slots, within each declaration form
(bytes with bytes, halfwords with halfwords). Within a form the names are
rotated by half their number, a derangement that does not preserve order.
Because only members whose declarations are identical apart from the name
trade places, the rewrite cannot change any offset agbcc assigns, whatever
its layout rules. Every other member,
the object's size and its alignment stay exactly the same, so nothing a
source can compute from the layout changes between the two compiles: another
member's address, `sizeof` and `__alignof__` all keep their values.

A bit-field has no address, so a pinned member can only be reached through
its own name, which follows the permutation. An access computed from
immediates and literal words has the same address in both compiles and so
cannot follow the move. That covers accesses from another member, from the
base, or through a cast, macro, comma lvalue, `__extension__` or a
size-dependent index. The one other way a pinned offset reaches a value is
memory: a store through the pinned member of another object of the type (a
stack copy declared with `__typeof__`, a union over it) read back at a fixed
offset shows where the member landed, and an alias indexed by that value
would follow the permutation (review probes `p01`, `p04`). So the executor
marks every value read back from memory: any load except a literal word or
a word reloaded from a word store of an unmarked value at an unmarked
address (a register spill; a pinned member is never a word, so no store
through one is). Marks follow arithmetic and copies. An object access whose
address registers are marked is refused, and flags computed from a marked
value never decide a branch by themselves, even when the executor knows
the value: such a branch becomes a decision, imposed alike on all three
compiles and compared there, so no branch can follow the layout. The
permutation therefore shows that each access follows the layout and that
its offset was not computed from a layout-dependent runtime value. On every path, the real
compile's trace, branch conditions and object accesses, with each pinned
offset X mapped to its permuted offset P(X), must equal the perturbed
compile's. In both compiles any access that overlaps a pinned member without
being exactly it is refused, so only an access of the member's own offset
and width can touch one.

The security argument rests on these compiler-enforced checks. For an
alias store paired with a planted read (`(void)sym.bg0cnt; p[1] = 0x100;`
with `p` derived from another member), the permuted compile is the only
compiler-enforced guard: the pair has the shape of a read-modify-write store,
so the real/stripped rules accept it, and only the permutation shows that
the store does not follow `bg0cnt`. On the
preprocessed text, the check also refuses every occurrence of the symbol
that is not `symbol.member`, apart from the pinned declaration itself. It
refuses the plausibility `&` and subscript rules there too. The lexical
rules (array subscripts, `&`, `&(...)` around the symbol, `__extension__` in
users, casts and macros) are cheap defence in depth. With the lexical passes
switched off, every aliasing repro from the review rounds (`revw-old`,
`revw-c`, `revf-c`, as far as they compile against the current header) is
still refused by the permutation, the overlap rule or the read-back rule;
`p01` and `p04` are refused only by the read-back rule. Probes the lexical
rules alone stop and the structural rules do not are not claimed: the
lexical passes remain part of the check.

A planted read either vanishes from the stripped compile, which leaves a load
the rules cannot explain, or stays, which shows the qualifier did not produce
it. Either way it is refused or is ordinary code. The checked spellings are
`(sym.x, 0);`, `sym.x;`, `(void)sym.x;`, `!sym.x;`, `if (sym.x) ;`, an
unused local, `switch (sym.x) { default:; }` and `g(0 * sym.x)`, which are
dead loads; `(void)sym.x;` followed by the value's arithmetic and an
out-of-bounds subscript store, which is not adjacent to its store;
`c ? sym.x : 0;`, which keeps a branch the stripped compile drops;
`g(sym.x - sym.x)` and `sym.y = sym.x` long after `sym.x` was stored, which
add a read; and `sym.x |= 0;`, `sym.x = sym.x;`, `sym.x ^= 0;` and
`sym.x &= 0xFF;`, which are self-assignments. Code the executor does not
model fails closed with a reason: ARM code, computed jumps, untyped indirect calls,
loops whose exit depends on unknown values, more than 1024 paths, and
prototypes that are missing, `()`, variadic, inconsistent, not one word per
parameter, or too complex to read at file scope. The one computed jump it
models is agbcc's switch dispatch (kit#170): `lsl rD, rI, #2; ldr rT, .Lp;
add rD, rD, rT; ldr rD, [rD]; mov pc, rD`, where the pointer word `.Lp` or
`.Lp+4k` (a decimal offset without a leading zero, which GAS would read as
octal; literal loads take the same form) lies in the pool that starts right
after the `mov pc` (agbcc dumps
the literals still pending at the jump there, so it may share that pool
with them) and holds exactly the label of a table that also starts right
after the jump (only labels, alignment and literal words between), every
entry is exactly a local code label of the function, and on the path the index is
either a known constant inside the table or was compared with
`cmp rI, #N` and the `hi` branch not taken, for a table of exactly N+1
entries. Each distinct case label is then a successor, explored like a
conditional branch and counted against the same 1024-path bound; the
decision records the index, N and which entries share a label, so the
stripped and permuted compiles must dispatch on the same value through the
same partition. Any other `mov pc` or `bx` source, an unguarded or
differently guarded index, a pointer word outside that pool or misaligned
in it, a table that is not adjacent, not local or of another size, and
entering the dispatch past its shift still fail closed.
The path and decision bounds are cost bounds (kit#137): every path is
checked in full and a function they cut short is refused, never accepted on
the paths seen. The path bound was 256; holding 1024 paths, measured on
0800C4B4, costs about 300 MB and 5 s (the true ceiling is 1024 paths of
up to 20000 records each). Loops whose exit depends on unknown values stay
refused at any decision bound, unless the relational loop induction below
proves them. Because the
check sees every spelling, the earlier syntactic rule against statements
that only read `symbol.member` is gone.

**Relational loop induction (kit#137).** Only a refusal by one of those
bounds can become an admission, and only for a function with a loop
(`tools/volatile_loop_induction.py`, one policy object). That function is
checked again with each loop cut at the target of a depth-first back edge
(control flow that enters a loop in more than one place refuses): a path
cuts a loop when it first reaches the cut point and ends when it
reaches it again, so each path covers one iteration, and the induction
covers them all. At a cut, a location the loop's strongly connected region
writes (r0-r12, lr, the flags, frame slots it stores at `[sp, #imm]`) that
no path from the cut may read is poisoned; a live one that holds sp, the
object's address or a value loaded from the object keeps its exact value;
every other live one gets a fresh value, the same in the real and the
stripped (or permuted) compile when both held the same value at the cut, and
marked as read back from memory. Memory outside the frame gets a barrier;
when a store it hides may hold a value read from the object, every load it
stops carries the object, so such a value is never laundered into an
ordinary pointer, and a store it hides may not hold a pinned member's
content, nor may a register or frame slot live across the cut (rule 5 would
lose the member's value). The existing comparison then runs on these paths,
with the cut and the back edge as events, and with the cut as a marker in
the lists of object loads (and of permuted object accesses) it compares, so
a load cannot move across a cut: equal lists mean equal counts per
iteration. At every back edge each compile must restore what it kept,
leave unwritten locations alone, hold no address in a fresh location, keep
sp, the escape state and its frame stores inside the region's slots, and
give each shared location its counterpart's value again. The flags must be
dead at the cut, and the region may not push, pop or write sp.

That second run decides functions the bound left undecided, so it does not
inherit the executor's call model, whose gaps (kit#215 and those found
while summarising loops) would otherwise become admissions. In it every
register a callee may read beyond its prototype is compared; afterwards r12,
lr and the flags differ between the compiles; the register a callee's ROM
return sites jump through holds a value named by the call's byte offset in
its compile, and also its earlier value when another return site may
leave it alone (for a callee whose return form the ROM does not show,
every r0-r3 depends on that offset); a register the callee may leave alone keeps
its earlier value; outgoing stack-argument words belong to the callee; and
an access through any of those refuses. Pushes are allowed only in the
prologue, before sp moves; frame accesses below sp, not aligned to their
width or (before an escape) at a variable offset refuse, which also keeps
the shape of kit main's variable-offset frame read out of every loop; every
call and cut sees one word-aligned sp with no frame store below it, and sp
never drops below it; the saved slots join each escape snapshot; and r4-r11
must hold their entry values at every return. Untyped calls stay refused.
The invariants the proof rests on are listed in the module's docstring.

A report that relies on it says so in the semantic record:
`loops by relational induction at instructions [N, ...]
(relational-loop-induction-v1, premise: callees preserve r4-r11 and sp, and
leave their return address only in the register their ROM return sites jump
through)`. A function it cannot prove keeps the bound's message, followed by
`; relational loop induction (kit#137): ` and the reason. The rule is on the
default path because it only turns that refusal into an admission and prints
its premise in each report that uses it; no saved report reaches a bound, so
none changes. The opt-in BIOS fill rules, by contrast, change walks that
already admit.

The match report records `* allowlisted volatile: ...` for each such object,
with the header's SHA-256, and `* allowlisted volatile semantics: ...`, which
lists the paths and the instructions explained as read-modify-write loads and
chained re-reads. Saved reports are refused unless both records equal a fresh
recomputation, which recompiles both versions. match.py runs both checks
once, before any profile selector, so they apply on every path. That
includes the selectors that write their own reports, such as the owner,
addressed and signed runtimes, private float, palette and switch constants.
A failing check makes the source IMPLAUSIBLE and the selector never runs.
Every report puts the records directly after its
`* source plausibility: plausible` line. If a selector's report has no such
line, the report and any `--emit` output are removed and no MATCH is
printed. `report_matches` compares the records centrally and gives each
profile validator the report without them. The premise is that the pinned
declaration is the original program's. The byte comparison, linking and
every other check are unchanged.

The explicit owner selector
`--owner-runtime-profile bounded-buffer-bios-fill-overwritten-control-stores-v1`
adds a conditional ordinary-memory policy for exact overwritten constant stores.
It authenticates the pinned declaration and local CpuSet source contract, then
checks the real, qualifier-stripped and permuted compiler outputs. Load-time
provenance and typed event correspondence preserve every surviving effect's
order, address, width and value. A removed constant store must have a complete
same-member overwrite. Intervening reads qualify only as independently classified
exact-width forwarded constants with a sole copy use; an intervening plain store
qualifies only as a complete scalar member in the same authenticated object with
proven disjoint byte intervals. Unknown effects, live reads, calls, branches,
returns, overlap and unsupported provenance remain barriers.

This policy explicitly assumes stable ordinary memory without asynchronous,
hardware or external observers. It establishes no MMIO equivalence, physical
readability, callee behavior or termination. The ordinary default policy remains
unchanged. Native reports bind the selected policy, producer/runtime pins and
fresh semantic evidence; inventory-only manifests cannot establish admission.
The USA blend-alpha keyframe callback at `0x08006720` uses
`--addressed-signed-runtime-profile compiler-signed-runtime-data-v1`. Its
three native compiles each have a read-only search through four-byte records.
The checker verifies the zero starting index, signed interval boundaries and
one-record increment. A fixed-point analysis over the original CFG proves
that the index is the only loop-modified value live at the next iteration.
The volatile comparison uses a symbolic index and checks every outcome of a
single arbitrary iteration in all three compiles, including both paths that
write the named BLDALPHA bytes. The proof assumes stable ordinary
records and mutually disjoint valid records, event, payload and shadow storage. The callback
writes display shadow RAM at `0x0300098C/D`. Updater `0x08000718` programs DMA0
to upload those bytes to BLDALPHA. A native execution test follows the original
installer and scheduler on a three-keyframe input.

The USA window writer at `0x0811435C` uses the existing
`--owner-runtime-profile bounded-buffer-root-return-scratch-v1` for its
12-byte local interpolator. The two original scene calls at `0x081147F0`
and `0x08114820` use window tasks retained from the WIN1H/WIN0H constructors
and centers at rows 72 and 71. The recovered loop visits each admitted row's
left and right byte. Their packed volatile fields reproduce the four original
reads immediately preceding stores. A qualifier-stripped build retains the
four reads that supply the values. Swapping the field names moves all twelve
accesses to the other byte. Replay checks the caller, live payload getter,
two interpolators, nested geometry and the shared scanline transfer to HBlank DMA.
The row bound assumes the original initialized scene and live exclusive buffers.
For the native controls and 21-frame scene test, set `FFTA_SHIFTED_WINDOW_ROOT`
to the matching game checkout.

The finite local-word verifier also handles the 148-byte caller at
`0x080C6858`. It builds a 48-byte stack list containing pointers to the game's
264-byte unit records. Both script sites pass exactly twelve records. The
active branch selects a prefix of zero through twelve pointers in traversal
order. The other branch clears the records and selects all of them. The list
is read by the history initializer before its caller releases the stack
frame. Only the pointers to units survive in the allocated state.

At `080C68EC` the same finite-local selector uses the existing conditional list
query contract. The installed clearer zeros the entire 196-byte state. The
query writes a pointer for each node before selection begins. The owner reads
the first word of each returned object and keeps the first two pointers that
equal one of the 24 primary scene record addresses. The four history values
are 18, 5, 8 and 2. The final current state is zero.

The existing query contract assumes a finite, acyclic list of at most 13 nodes.
The test executes the original menu call site and all of its callees with a
placed queue for each length from zero through thirteen. It checks the complete
state against the expected record selection, including repeated entries and
early exit. The original boot installer supplies the clear routine; the CPU
test models its three BIOS CpuSet operations.

The USA history initializer at `0x080C62CC` copies an ordinary word list
before reading and updating the display shadow. Two script call sites pass
exactly twelve unit records to a builder with twelve stack slots. Filtering
can reduce the copied count to zero. Another entry at `0x080C7484` forwards
the supplied array and signed count unchecked. Its caller must provide at
most 24 readable, aligned words separate from the allocated state, control
shadow, animation, palette, installed callbacks and private stack saves.
A nonpositive count skips the copy. The native proof checks the root heap
constructor, installed clear and copy routines, and all three compiler objects.
The ordinary semantic comparison covers the three blend-byte reads, its write
and the separate display halfword. It assumes successful allocation, stable
initialized memory and the reviewed callback image resident in IWRAM.

The USA BG3 scroll scene at `0x080EF484` creates a 36-byte scheduler payload
and a 12-byte scroll child. Its graphics and scheduler heaps occupy separate
parts of the same EWRAM scene allocation. The child provides 160 halfwords of
scroll data followed by two separate DMA banks. The ordinary verifier checks
the whole callback after a native proof bounds the variable loop. The first
fill writes all 160 rows. The subsequent calls update even prefix lengths
from 0 through 72 and enter phase `0x103` when the counter reaches 74.
The proof requires normal scheduler entry, live successful allocations, an
available graphics slot, private descriptor frames and stable task ownership.
The original, stripped and layout-perturbed objects have the same 23 typed
relocations. A native test follows the original initializer, allocator and
scheduler and reproduces bank and shadow writes when these premises fail.

**Escaped-local extents (`escaped-local-extents-v1`,
`tools/escaped_local_extents.py`).** Once a stack address escapes, the rule
above makes every frame byte observable, compiler spill slots included. Two
compiles that spill different values to a slot no C code can reach are then
refused although they behave the same (0x0811B3B0 spills a byte in one compile
and an address in the other to `sp+0x30`). When the semantic check refuses on
the default path (not under the CpuSet interface selectors), match.py runs it
once more with each compile's frame layout. Each of the three compiles is
repeated with `-g`; its `.text` and parsed instruction stream must equal the
checked compile's, and its DWARF 2 information gives every named local's frame
slot, size and scope. In that run:

* the function must have agbcc's frame shape: pushes, then at most one `sp`
  decrement, and `sp` changes nowhere else but in epilogues that only pop,
  restore r8-r11 and return;
* every escaping frame address (a call argument, an argument register the
  callee may read, a stored value) must lie strictly inside exactly one named
  local whose scope covers the escaping instruction; a local it is one past
  the end of escapes with it, in any scope. A frame address kept in the frame
  outside an internal slot must sit in an escaped local or a stack-argument
  word, and escapes in turn;
* every consumer of an escaping address is recorded: the callee and register,
  the local or stack word it is kept in, or the store target, which must be
  proven ordinary RAM (never I/O such as a DMA source register, ROM or an
  unknown pointer). A `memcpy` with a constant count inside the local is
  proven when the ROM copy helper it links to (`func_081443FC`) matches its
  pinned SHA-256 and the source defines no `memcpy`; it returns its
  destination. Every other consumer is listed in the report as premised;
* after an escape, a screen (not a proof): a value read back from the frame,
  a result of a call that was given a frame address, or a word of memory read
  straight after such a call may be stored only to proven RAM, and a `memcpy`
  of frame bytes that may hold a frame address may copy only to the frame or
  to proven RAM; a word store of it, or a copy to RAM, is listed. A frame
  address that a premised consumer leaves in memory and this function passes
  on by another route (in pieces, after a later call or store, through a later
  call's result, or by a `memcpy` from non-frame memory) is not screened: it
  rests on premise 1 through that consumer, which the report lists;
* the escaped locals stay observable as before. A slot of the function's own
  frame (between the body `sp` and the saved registers) that no escaped local
  and no stack-argument word overlaps is internal: its stores are not events,
  its loads forward across calls and must be exact, and only a pointer not
  computed from `sp` is disjoint from it;
* a frame load that is not forwarded (it stopped at a call) is refused when an
  untraced store outside the escaped locals may overlap it, so no internal
  value, and no frame address kept in one, comes back as an unknown value. A
  variable frame offset may reach every slot but the saved registers (main,
  before an escape, treats it as disjoint from every constant slot), and an
  escape after such a store also compares the order of the stores that can
  reach the escaped locals.

The report then carries `* allowlisted volatile escaped-local extents
(escaped-local-extents-v1): ...` with, per compile, the escaped locals, the
premised and proven consumers, and the premises: each premised consumer, and
any code reached through a pointer it keeps, stays within the declared extents
of the locals listed with it, the declared types are the original's, and
hardware gets a frame address only through a listed consumer; a pointer not computed from `sp` reaches no frame byte outside the
escaped locals and a variable frame offset no saved-register slot; a callee
reads or writes no stack word beyond its prototype's arguments and takes no
input in r4-r11; and the `-g` twin's DWARF describes the checked compile's
frame. A reviewer audits the premised consumers by name: a length-taking
helper given a frame address (a CpuSet wrapper, an LZ77 decoder) is exactly
where premise 1 can fail. If the second run refuses, the report keeps the
first run's refusal. `escaped_local_extents.POLICY.enabled = False` turns the
rule off. Inlined subroutines in the DWARF are not modelled and refuse.

A passing semantic check still requires plausible source and complete ELF bytes
identical to the ROM before a function earns match credit.

**Residual risk:** the semantic check can refuse genuine code but cannot
accept an unexplained effect of the qualifier, within its model. The model
has these gaps:

* It refuses legitimate volatile semantics that an ordinary declaration would
  optimise differently. Examples are reading a flag twice
  (`if (x) ...; if (x) ...`), spin loops and repeated stores
  (`x &= 0xF0; x |= v;`, 080D4DA0). Such functions cannot use the allowlist.
* The provenance and prototype rules cost some legitimate spellings:
  - a user of the object cannot define macros containing `&` or names of
    the pinned declaration (such as `u8`);
  - `a & symbol.x` must be spelled `symbol.x & a`;
  - users cannot cast through struct or union bodies or `(*)` declarators,
    which also refuses function-pointer prototypes such as
    `void (*)(void)` in such a file;
  - callees need a fixed one-word-per-argument prototype;
  - a dead load into an argument register is refused unless that register
    is overwritten before the next call, whatever the callee's prototype
    says, when the callee is not an indexed Thumb function whose CFG closes
    (indirect calls, BIOS calls, recursion, switches), or when its ROM code
    reads the register.
* The permutation refuses any access to a pinned member that is not made
  through its member's name. A computed offset that happens to equal a
  member's is a false refusal. The check assumes agbcc places full-width
  byte and halfword bit-fields exactly as the layout computes (an agbcc test
  compares the shipped declaration's compiled offsets with the model). It
  needs at least two pinned members of each declaration form, and fails
  closed otherwise. The object's address cannot be taken, so code that
  passes the block's address on (the `08000718` DMA source) cannot use the
  declaration.
* Variable subscripts into the object (`symbol.unknown_48[i]`) are always
  refused. None of the 173 parked and matched sources that reference the
  block uses one. A rough ROM scan finds a register-offset access through a
  block base in about 5 of the 373 functions of 2 KiB or less that load the
  block's address (080917F8, 080D38B4, 080EEB50, 080EFD50, 08112AEC). Those
  would need another member spelling or cannot use the allowlist.
* It is order-sensitive. Stores, calls and object loads must happen in the
  same order in both compiles, and volatile accesses are ordering barriers
  that the stripped compile may schedule across. A function whose stripped
  compile legally reorders a store around a pinned access is refused even
  though both orders compute the same thing. The four recoveries keep their
  order.
* The read-modify-write shape is empirical. It comes from agbcc's output for
  the recoveries, and a genuine store whose value is computed between its
  load and its store would be refused. Only constant arithmetic whose result
  reaches the store's value register through copies, and copies or literal
  loads that reach the store's operands, may sit there.
* Halfword members have further false refusals. A narrow read
  (`(u8)symbol.bg0cnt`, `symbol.bg0cnt & 0xFF`) is refused because the
  stripped compile narrows it to an `ldrb` of the low byte, which the overlap
  rule refuses. A signed read (`(s16)symbol.bg0cnt`) is refused because the
  normaliser does not equate the two compiles' sign extensions. The mixed
  chain `symbol.bg0cnt = (symbol.win0h_lo = a)` is refused, while
  `symbol.win0h_lo = (symbol.bg0cnt = a)` passes.
* It reasons about agbcc's assembly. It assumes cc1's output is what the
  assembler encodes.
* The read-back rule refuses an object offset computed from any byte or
  halfword local read back from memory, and turns branches on such values
  into decisions; the extra, possibly infeasible, paths count against the
  1024-path and 32-decision bounds (080D3CB4 goes from 73 to 79 paths).
* Callee interfaces assume the ARM calling convention for r4-r11 (a callee
  that reads a callee-saved register as a hidden argument is not modelled,
  as before), that capstone reports each Thumb instruction's register reads
  and writes, and that `func_XXXXXXXX` is linked to that address (the byte
  match enforces it). The all-ones exception rests on the permutation:
  without the permuted compile every pinned store still needs its load.
* It does not police reads that stay in both compiles. These are ordinary
  code that any declaration produces, and the general plausibility rules
  apply to them.
* The executor is new modelling code. A modelling error shared by both
  compiles could equate different computations. Unknown instructions,
  addressing forms and transfers fail closed.

Focused checks: `PYTHONDONTWRITEBYTECODE=1 python tests/test_plausible_volatile_allowlist.py` and
`PYTHONDONTWRITEBYTECODE=1 python tests/test_volatile_semantics.py` (the latter compiles with agbcc when it is installed);
`python -m unittest discover -s tests -p 'test_volatile_indirect_calls.py'` covers typed indirect calls,
and `tests/test_volatile_escaped_extents.py` the escaped-local extents.

It handles the compiler stage as `cc -> .s`, so it works with a classic cc1
(GCC 2.9 / agbcc), with modern gcc and with clang. Any toolchain other than
the default, outside a library unit's own, is exploration only: the diff is
printed and the verdict is `NOT VERIFIED`:

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
The new profile requires a normal verified return (with one exception, below)
and at least one reachable instruction without a graph path to a return.
**Every** such instruction must either be an unconditional narrow Thumb branch
to its own address, or belong to a terminal tail: a straight-line chain of
two-byte instructions, each whose only successor is the next instruction, that
ends in such a self-branch. A tail
instruction cannot be a branch, call or interrupt, push or pop, stack
adjustment, or write SP or PC, so a conditional exit, `bl`, frame change or
indirect transfer refuses. Pure-spin functions, multi-instruction cycles other
than the call loop below, and branch feeders remain excluded. Reports list the
tail instructions in an optional `tails` record and then state the tail
summary; reports without one keep the self-branch-only meaning, digest and
summary.

The one exception to the return requirement is a function with **no**
reachable return whose only cycle is a call loop, such as
`for (;;) func_08003398();` after some setup. Its reachable instructions must
be one contiguous run from the entry in which every instruction falls through
to the next, except the last: a narrow unconditional `b` back to the loop
head. So there is exactly one cycle and no exit; a conditional branch, a
second cycle, a pop, an interrupt or an indirect transfer anywhere refuses.
The straight-line prefix before the head may hold the frame setup (push,
fixed SP adjustments), stores and typed calls. Inside the loop every
instruction other than the closing branch is an ordinary typed call to an
indexed Thumb function or a straight-line instruction without a store, push
or SP write, and the loop holds at least one call, so a function whose only
cycle is `b .` stays excluded. Such reports carry an optional `loop` record
(`head`, closing `branch` and the loop's call offsets, with `spins` empty),
state their own control-flow line and summary, and keep every other check
and the data, replay and status rules below. The claim is only that, if each
callee returns, the function never returns and does nothing in the loop but
load, compute and call; it does not prove that the callees return.

The complete converged instruction, stack/provenance, local-alias, call and
literal checks still run on every reachable instruction, tails included,
including checks after return classification. A tail only escapes the
obligations at a return, which it never reaches. A fixed frame may remain
allocated on the spin arm; actual returns must balance it. Ordinary typed
mapped Thumb calls and fixed frames are supported. Typed named data is
admitted exactly as `elf-symbol-thumb-data-v1` admits it: undefined global
object symbols mapped in `config/data_symbols.json`, `R_ARM_ABS32` with signed
addends, each a complete aligned in-function literal word loaded by reachable
PC-relative code. Such reports carry an optional `data` record of offset, name
and addend, bind the data-map digest in the proof and the
`* data symbols SHA-256` line, and replay relinks and rechecks every word.
Buffer proofs, switches, function relocations, indirect-call thunks and
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

For `__pack_d` at `0x08142BE8`, `--unit-toolchain old-agbcc-O2-v1`
selects `elf-symbol-thumb-dp-bit-pack-d-lshrdi3-v1`. The caller covers
332 bytes in the ROM-authenticated 3552-byte dp-bit unit. Its call at
`0x08142C64` passes the same CFG count and frame checks. The report binds
the canonical unit row and compiler binary digest, then replays the
complete source with `old_agbcc -mthumb-interwork -O2`. This schema
requires the original relocatable object with no orphan sections excluded.

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
`__divdf3`, `__muldf3`, `__ltdf2`, `__truncdfsf2` or `__fixdfsi`, or the
wide-integer `__muldi3`/`__divdi3` described below. Private integer helpers
and other floating operations remain unsupported.

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

The unsigned word conversion `__fixunsdfsi` at `08142864..081428AC`
uses the same selector. Its complete 72-byte body contains 24 reachable
instructions and four compiler-generated calls. The comparison at `0814286E`
may bind `__gedf2` to `0814374C` only in this function. The other three calls
must bind `__adddf3` once and `__fixdfsi` twice at their original sites.

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

The same selector admits the complete 108-byte libgcc2 `__floatdidf` owner
at `081428E4`. The signed upper word is scaled by 65536 twice, then the
unsigned lower word is added. The original object has six compiler-generated
Thumb call relocations across `__floatsidf`, `__muldf3` and `__adddf3`. The
selector binds each site to its named helper and replays the original frame
and binary64 call closure. The `L_floatdidf` upstream member under old_agbcc
and the recovered C under the default agbcc both produce the complete ROM
body. The native test compares integer rounding boundaries and ties with
binary64, including both signs and both endpoints of the signed 64-bit range.

Plain `long long` `*` and `/` compose through the separately versioned
`agbcc-thumb-muldi3-divdi3-target-state-closure-v1` record. It binds only the
original compiler symbols `__muldi3` (`08142A20`, 116 bytes/56 instructions)
and `__divdi3` (`08142280..081426B8`, 1,080 bytes/496 reachable instructions,
including its final literal word). A caller with no binary64 operation uses
this selector too, as a caller of only `__negdi2` already does. Both function
indexes must carry those exact extents; the analyzer's truncated
`081426B4`/538 row is refused. Division's closure is pinned too: the canonical
unsigned word quotient and remainder and their shared zero hook, with all 19
call edges. Local `agbcc/libgcc/libgcc2.c` selections `L_muldi3` and
`L_divdi3`, preprocessed with that tree's libgcc Makefile options and compiled
by the fixed agbcc `-mthumb-interwork -O2`, produce complete ELF function
symbols identical to the 116- and 1,080-byte ROM bodies when `__udivsi3` and
`__umodsi3` are typed-bound to their Thumb addresses and the `__clz_tab`
`.rodata` is placed at its literal, `0836CF98`. The `lib1thumb.asm` selections
`L_udivsi3`, `L_umodsi3` and `L_dvmd_tls` likewise reproduce the other three
bodies. A focused test rebuilds all five and requires the pinned digests; it is
a local audit that skips without those sources unless `FFTA_REQUIRE_LIBGCC=1`.
As for the word runtimes, this identifies the audited source variant, not an
arbitrary installed libgcc.

The unchanged runtime interpreter proves every reachable return, balanced
frames, restored r4-r11, no caller-memory writes and no read at or above entry
SP through a tracked stack address. The three computed `__clz_tab` loads
(`08142304`, `081423E8`, `0814255C`) are unconstrained by it; that the code
bounds them to ROM is established by inspection of the pinned bodies. Operands
and those table loads are target-state inputs: no arithmetic, zero-divisor or
termination claim is made. Explicit `func_08142A20` calls, `__moddi3`,
`__udivdi3` and other wide runtimes remain refused in this profile, and neither
wide runtime composes with inert spins. Explicit `func_08142280` calls are a
deliberate tightening: they verified under this selector before, as ordinary
entry-only calls, and are now refused, because inside the selector any call to
`08142280` must be the canonical `__divdi3`. Outside the selector, `__muldi3`
and `__divdi3` stay unbound, and an explicit `func_08142280` keeps its existing
ordinary entry-only binding.

The standalone source of `__divdi3` at `08142280` uses
`--owner-runtime-profile libgcc-divdi3-v1`. Both the default compiler and
the fixed old agbcc build of the historical two-word division algorithm must
reproduce the original 1,080 bytes of text and the private 256-byte
`__clz_tab` at `0836CF98`. The original ELF contains seventeen Thumb calls to
`__udivsi3` and `__umodsi3`, plus three zero-addend ABS32 references to its
local read-only section. Each of the three reached byte loads extracts the
highest occupied byte of a 32-bit divisor limb using shifts of 0, 8, 16 or 24.
The two movement callers pass word pairs in R0:R1 and R2:R3 and consume the
returned pair in R0:R1. The signed quotient truncates toward zero for a
nonzero divisor and a representable result.

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

`--owner-runtime-profile local-rom-halfword-table-v1` admits the closed
40-byte owner that copies eight ROM bytes into a local four-halfword array
and returns one indexed halfword. It binds the complete original ELF,
genuine zero-addend call/data relocations, exact current indices and the
complete 98-byte copy helper. The root, helper and data addresses are derived
from those bindings, not an accepted-root address list.

The relation is conditional on `(entry_R0 & 255) < 4`, valid aligned live
stack access over entry-SP offsets `[-28,0)`, readable immutable source bytes,
source/code/frame separation, noninterference and compatible C/ABI use.
An unsigned-byte parameter does not establish the index bound. A canonical
data point does not grant extent or readability. Reports retain these
conditions; the checker proves the ordered copy, protected saves and local
read under them. Existing selectors retain their guards.

`--owner-runtime-profile local-shadow-halfword-matrix-v1` admits the closed
96-byte owner that initializes eight local halfwords from a named RAM point,
copies the resulting sixteen bytes into a four-by-two local matrix, and
returns one signed halfword. The complete 98-byte copy helper and both exact
instruction counts are required. Only the genuine original compiler `memcpy`
relocation and canonical zero-addend data relocation are transported; this
does not install a global runtime alias.

This relation retains arbitrary source values and requires independent valid
low-byte row/column bounds (`row < 4`, `column < 2`), aligned live stack access
over `[-56,0)`, readable source halfwords, source/frame/code separation and
noninterference. Protected saved words, all four word-copy iterations, the
signed indexed read and the real return are checked on one ordered byte state.
The expired pointer left in R3 remains explicit and grants no later access.
Physical permissions, actual entry SP and historical C/ABI compatibility remain
conditions. Reports bind the original ELF, current source, mappings and proof
producers; ordinary selectors retain their original refusals.

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

Function progress counts verified entries in the main function index, starting below
`0x08150000`. Byte progress divides the union of matched index spans by the
union of all main index spans. Overlapping bytes count once. The README meters,
regional breakdown and badge endpoints use these counts. Index boundaries can
change as more code is recovered.

Late-ROM functions have a separate absolute count. Their complete ELF and
report extent must equal the unique indexed extent. Internal literal pools count.
External alignment and installation-time RAM aliases are excluded. The regional
and library breakdown also lists each recorded library unit and the functions
outside those units.

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
Reachable PC-relative pool words matching indexed code entries, directly or
through a ROM wait-state mirror, require the canonical function relocation at
that offset; reserved thunk-table literals, mirrors included, are rejected. This is a conservative provenance boundary for ambiguous
code-valued literals, not proof that a numeric value denotes a function. It
does not scan instruction bytes, unreachable pool words or unrelated integers.

Status and compiled rebuild use only the fixed selector derived from a strictly
replayed saved report; stale, malformed or missing reports do not authorize it.
No-write verification does not refresh evidence. Rebuild preserves selected
report and text-index snapshots through output publication and cleans owned
output on failure. No source or Parked promotion follows from installing this
tool capability; source review and the complete publication gates remain separate.

### Canonical-thunk callers with dispatch-identified switch pools

`--function-address-profile canonical-thunks-interposed-pool-v1` selects
`elf-symbol-thumb-function-address-thunks-interposed-pool-v1`. It keeps every
rule of `canonical-thunks-v1` and changes only how the caller's one local
switch is found. `canonical-thunks-v1` takes exactly five words between the
dispatch and the table pointer, and the zero-pool selector none; this selector
finds the table pointer by the dispatch's own PC-relative `ldr`, as
`u16-scalars-v2` does, so any nonzero number of words may sit between them.
The guard must be the adjacent `cmp; bhi` or `cmp; bls; b`; the local
long-branch default is not admitted. Cases must lie after the table, and the
layout must be unique.

The interposed words gain nothing from their position. Each must be a complete
word read by a reached PC-relative load, and the halfword before them may only
be zero alignment. They are then bound like every other literal of a thunk
caller: a mapped object word through its typed data relocation, a function
literal through its canonical function relocation, and any other word is a
number, which may not equal an indexed code entry or the thunk table. The
alignment and the words are reserved as data before decoding. The manifest
carries the selector and the producer-source digests, its pool record uses the
`canonical-thunk-interposed-pool-switch-v1` schema, and replay refuses a
report relabelled to or from another thunk selector. Status and rebuild
forward the saved selector.

### Unsigned DIV/MOD with canonical call thunks

`--function-address-profile unsigned-divmod-thunks-v1` selects
`elf-symbol-thumb-function-address-thunks-unsigned-divmod-v1`. It composes
compiler-emitted `__udivsi3`/`__umodsi3` calls (either or both) with
compiler-emitted `_call_via_r0`-`_call_via_r12` calls, ordinary mapped Thumb
calls and typed mapped data. The caller must be acyclic, saved-only (no locals,
entry words, SP exports or block transfers) and switch-free, and every runtime
call must receive an all-path, nonzero unsigned32 constant in r1. The divisor
can be any such constant. The structural inventory
`unsigned-divmod-thunk-ordinary-structural-inventory-v1` reuses the complete
native UDIV/UMOD/zero closure; indirect and ordinary callees keep the
conditional returning ABI above. No callback value or effect and no arithmetic
or memory equivalence is claimed. The divisors are re-proved from the ROM
bytes on every verification and are not stored in the manifest.

Every reached pool word in RAM or ROM needs typed ABS32 provenance. Only fixed
hardware addresses (`0x04000000`-`0x07FFFFFF`) may stay numeric, and the
manifest lists each one. Function literals, switches and other runtimes are
refused. The preprocessed source must not spell `_call_via_`, `__udivsi3`,
`__umodsi3`, `__divsi3` or `__modsi3` anywhere, string literals included, and
must not use an `asm`, `__asm` or `__asm__` keyword, so an asm label cannot give
a declaration a reserved ELF name. No `__attribute`/`__attribute__` list may name
`alias` or `weak` in any underscore spelling. Independently of the C spelling,
the compiler's assembly may not contain `.set`, `.thumb_set`, `.equ`, `.equiv`,
`.eqv`, `.weak` or `.weakref`, and the compiled object may define no global or
weak symbol other than `func_<addr>`. So an alias such as
`__attribute__((__alias__("__udiv" "si3")))` cannot borrow a runtime or thunk
name.

`--function-address-profile unsigned-divmod-thunks-frame-v1` selects
`elf-symbol-thumb-function-address-thunks-unsigned-divmod-frame-v1`, the same
composition for a fixed Thumb frame. Its inventory,
`unsigned-divmod-thunk-ordinary-framed-structural-inventory-v1`, replaces the
saved-only check with the unchanged `prove_frame` policy without stack aliases:
constant `sub`/`add sp` adjustments, direct aligned `ldr`/`str [sp, #imm]`
words inside the allocated frame (locals, and outgoing stack arguments at the
call), and incoming words only under the existing read-only contracts (word0,
or contiguous words 0..n-1 for n up to 6, each read). The narrowest contract
that covers the reads is used. SP materialization, dynamic SP, block transfers,
writes to incoming or saved words and unbalanced exits are refused. The caller
needs an allocated local or an incoming read. The manifest carries a
`stack_frame` record (the fresh frame proof, adjustments and every SP word
access), and each verification re-proves it. `unsigned-divmod-thunks-v1`
reports keep their saved-only meaning.

`--function-address-profile unsigned-divmod-thunks-divisor-choices-v1` selects
`elf-symbol-thumb-function-address-thunks-unsigned-divisor-choices-v1`. This
separate saved-only, acyclic selector allows one or two known nonzero unsigned32
divisor values at each canonical unsigned runtime call. It reuses the finite
must-definition analysis from `udiv_constant_choices_inventory.py`: exact Thumb
immediate MOVs and register copies generate facts; every other register write
kills its fact; calls kill caller-saved facts. A join unions values only for
registers defined on every incoming path, dropping facts exceeding two values.
Unknown incoming paths, zero, call results, and unsupported arithmetic refuse.
The existing `{4,8}` UDIV inventory and single-constant source selectors retain
their original domains.

Its inventory is
`unsigned-divmod-thunk-divisor-choices-structural-inventory-v1`. Runtime and
canonical thunk identities, complete native runtime closure, typed objects,
saved-frame restoration and the conditional callee ABI are unchanged. The
source manifest additionally binds `divisor_choices` as sorted runtime-site
offsets and exact sorted value sets. Both the inventory and source manifest pin
the actual finite-choice producer module. Verification re-derives those sets
from the complete ROM CFG, then fresh source/ELF replay binds the original
compiler relocations. It grants no fixed-frame, switch, arithmetic-equivalence,
memory-safety or indirect-callee proof.

The focused synthetic boundaries run with
`python3 -m unittest discover -s tests -p test_unsigned_divisor_choices.py`.
The parked game caller `080812E8` exercises the `[40,48]` join at runtime-call
offset `0x62`, with the full 132-byte symbol and 59 reachable instructions.

### Analysis and split notes

* `analyze.py` treats `pop {r0}; bx r0` as a return. Capstone does not flag the
  Thumb interworking epilogue, and without that every function using it
  swallows the one after it.
* Verified function starts need a prologue *plus* a walk that reaches a return
  or tail branch. A bare prologue scan matches ~16,000 false positives inside
  4bpp tile data, where the byte pair `0xB5xx` looks like `push {rX, lr}`.
* `rebuild.py` is the gate: if the concatenation does not reproduce the ROM, the
  split is wrong and nothing downstream is safe.

# Scalar-frame one-constant switches

The explicit `--switch-profile one-constant-frame-v1` selector uses the separate
`elf-symbol-thumb-switch-one-constant-frame-v1` source-bound schema. It requires
exactly one unrelocated interposed word before one adjacent forward switch
pointer/table. That word must be a signed scalar bias in `[-65536,-256]`, loaded
exactly once by the reached PC-relative word load immediately before the
three-register addition and canonical unsigned selector comparison. Branches or
table entries bypassing the bias pair reject. The existing complete ELF owner,
alignment, guarded five-operation dispatch, reachable pool use, typed ordinary
call linking, plausibility and fresh source replay checks remain mandatory.

This policy requires a reached nonzero fixed scalar frame and additionally runs
the existing restoring-frame proof for saved registers and entry-LR returns.
It excludes incoming stack arguments, SP address formation, stack aliases,
buffer arguments, dynamic frames and runtime/data/function-pointer profiles.
The sole block-transfer exception is the exact two-byte Thumb-1
`STMIA Rb!, {Rs}` encoding with one low stored register, distinct low base,
writeback, unchanged flags and the exact decoded register effects. Neither
register may carry tracked stack or return-pointer provenance. Its base is
invalidated by the ordinary register writeback transfer; saved registers must
still be restored. Multi-register STM, LDM, base-in-list and control-pointer
stores reject. External pointer validity remains the ordinary caller ABI
precondition, and local loops provide partial correctness, not termination.

The manifest records exactly one constant plus the existing scalar-frame and
placement records. Schema, selector, scalar marker, body, source/headers, maps,
function index and producer artifacts are checked by fresh compilation during
report replay. Neither legacy two-constant selector nor default matching
selects or falls back to this policy. The two-constant formats and boundaries
remain unchanged.

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

This scalar-frame schema adds the exact marker `fixed Thumb scalar SP frames; no
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

### Cone-shaped tile range at `080B48CC`

`--owner-runtime-profile conditional-cone-tile-stack-footprint-v1` verifies the 336-byte cone writer. At its eligibility and height calls, the compiler keeps a local byte pointer at call-site SP+52. The verifier requires empty register aliases at both calls, traces the incoming and outgoing stack offsets across the 29 complete Thumb owners, and replays their native frame checks. Only the map query at `0801CC7C` materializes a stack address. Its private byte pointer can survive in R2 on a false return. The checker follows the known return values through each consumer until the cone loop overwrites R2.

The 132-byte word fill at `08000DBC` and 136-byte halfword fill at `08000E40` use
`--owner-runtime-profile immediate-dma-stack-fill-v1`. The verifier checks
each reachable Thumb instruction, the complete frame, all three original
ELF object bindings and the four hardware register bases in the ROM table.
The first eligible channel gets the address of the local word, destination
and immediate fixed-source DMA control. Exhaustion returns -1. The local
MMIO qualifier must produce the same original ELF when removed. The report
states the effective count rules, hardware completion and stack-use premises,
including replacement of the programmed source before subsequent channel reuse.
The halfword fill initializes and transfers only the low halfword of the
four-byte slot. The verifier follows all four known caller continuations to
where they overwrite the returned channel.

The same selector checks the two fixed DMA3 transfers at `08003410`. The
original C initializes a halfword on the stack before each transfer. DMA3
programming covers 96 KiB of VRAM and 1 KiB of palette RAM. The intervening
call writes all 128 OAM entries and preserves the initializer's stack and
saved registers. Removing the hardware object's qualifier removes exactly
the two control readbacks. Transfer completion, exclusive use of idle DMA3,
hardware-visible stack memory and a writable video access interval are
explicit hardware premises. The single control reads do not poll completion.

`--owner-runtime-profile transfer-masked-stack-argument-v1` verifies the 364-byte transfer setup at 0x08037C84. Its one-bit resource update compiles to a word load, mask and store into the eighth incoming argument, followed by a reload of the same word. The selector authenticates all ten raw Thumb calls in eight indexed caller graphs. Each call allocates four writable argument words and initializes the eighth argument with zero or one. Two phase-byte cases require their taken zero edge to dominate the call. The store therefore preserves the caller's bits, including when another function subsequently uses the outgoing area. The ordinary frame checker still rejects incoming writes. Any additional computed or external caller must supply a writable Boolean word, and non-stack objects must be distinct from active frames.

The cone writer advances its output cursor in incoming stack word 3. Its identified caller `080B4A1C` provides this word inside a 32-byte outgoing area, copies the entry output argument through two exact Thumb MOV instructions, and discards the slot without reading it after return. The initialization dominates the call. A scan of the hash-verified 16 MiB USA ROM finds exactly one encoded Thumb BL targeting the writer and zero literal Thumb pointers to it. Computed indirect targets remain outside this inventory. The report assumes sufficient writable output records, writable outgoing arguments, and ordinary separation between external memory and active private frames. The profile covers only this owner and its specified calls.

### Packed scanline wave samples

The ordinary matcher verifies the packed signed halfword written by `0800C720`. The original compiler emits a byte read before each low and high byte store in its three loops. Stripping the single qualifier removes those six reads. The saved report binds both complete objects, the sine-table call, and the original callback and DMA tables.

The original constructor at `0800CC8C` initializes visible rows 0 through 159 and registers one, two, or four interleaved samples. Its caller is unknown. Given a live task, a valid caller-supplied hardware destination and successful DMA submission, the manager duplicates row zero into row 160 and submits the next row for repeated HBlank transfers. Direct use requires a sufficiently large disjoint bank, valid stride and lane offset, and stable row bounds. An inclusive end row of 255 wraps the byte counter.

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
distinct dependency owners are charged against the budget and recorded. A joined
pass discarded for a loop replay (below) has its charges refunded, so more than
eight owners may be walked in total, but the evidence never lists more than
eight. Both indexes must identify each exact,
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

This selector, and no other named-data selector, uses the bounded loop replay of
buffer callees described above. A joined pass that the replay replaces leaves
nothing behind: the callees it alone inspected are absent from the dependency
records and do not count against the eight-owner budget. When a callee is
replayed, the evidence gains an optional `loop_replay` record in its buffer
proof (`bounded-loop-replay-v2`, the buffer proof fingerprint that binds every
inspected body and each replay's sites, argument offsets, trusted pairs, pruned
edges and caller-frame writes, the report lines and the premise below), and the
report states one `* buffer loop replay:` line per replayed callee before the
evidence line. Reports without a replay are unchanged. Report replay recomputes
the record and the lines and requires both exactly; an edited, missing, extra or
indented line refuses. `tests/test_named_data_buffer_loop_replay.py` checks this
with assembled callees and a natural-C typed-data caller.

Data literals and replay compose under one stated premise. A data literal is a
typed absolute address and never becomes a tracked stack alias, since aliases
come only from SP arithmetic; accesses through it are external-memory accesses
under the returning-ABI premise, exactly as for a pointer parameter. That named
objects do not overlap any live stack is a premise, not a check: the startup
code sets the system-mode SP to 0x03007EC0 and the IRQ SP to 0x03007FA0, both
stacks grow down and their floors are not known statically. An address-class
check on data symbols is the subject of kit `#196`.

Focused native checks use `tests/test_named_data_buffer.py`, the fixed agbcc
compiler and `-mthumb-interwork -O2`. Set `FFTA_NAMED_BUFFER_TEST_ROM` to the
approved ROM and put the ARM tools on `PATH`. Its positive source is synthetic
C with a retained original ET_REL object; a dependency is the exact read-only
original switch body. This test proves verifier capability, not authorship or
admission of any actual game owner.

### Division runtimes as leaf summaries in buffer walks

`--owner-runtime-profile bounded-buffer-runtime-summaries-v1` is
`named-data-buffer-v1` with one change: a direct Thumb BL to the exact entry of
`__divsi3` (0x081426B8), `__modsi3` (0x08142950), `__udivsi3` (0x08142AB0) or
`__umodsi3` (0x08142B28) is a summarised leaf call, in the root and in every
inspected buffer callee. `bounded-buffer-bios-mixed-fast-fill-runtime-summaries-v1`
adds the same summary to `bounded-buffer-bios-mixed-fast-fill-source-v1`.
Their schemas are `elf-symbol-thumb-bounded-buffer-runtime-summaries-v1` and
`elf-symbol-thumb-bounded-buffer-bios-mixed-fast-fill-runtime-summaries-v1`.
Named data is optional; function literals and switches are refused.

What each run proves, for every runtime family actually called:

* the SHA-256-pinned spans of the runtime and of the shared `__div0` hook
  (0x0814274C, a bare `mov pc, lr`), mapped exactly and uniquely as Thumb;
* through the existing native ABI interpreter: every reachable path,
  including divide-by-zero, returns to the entry LR with R4-R11 and SP
  restored; the only call is BL `__div0`; there are no external writes or
  incoming stack reads;
* no instruction has a memory operand or is a block transfer, so the
  runtime's own balanced PUSH/POP is its only memory traffic;
* R2, R3 and R12 are never read before they are written, and a caller's
  R4-R11 or LR is read only to save it (each pushed word keeps its
  provenance, so popping it back does not make it runtime data), so the
  result depends only on R0 and R1; the walk also records which of them are written
  on every path to every return (for the pinned bytes, only R3 of
  `__modsi3`; the divide-by-zero paths leave the others unchanged).

The caller walk applies the summary: R0 is an unconstrained scalar; R1-R3, R12,
LR and the flags are clobbered and every fact about them is dropped. The caller
frame, its pointer slots and aliases in R4-R11 are untouched. A tracked
local pointer in R0, R1 or LR at the call is refused. A dead pointer in R2, R3
or R12 is refused too, unless that register is written on every path to every
return; only then is it discarded, and the report lists each discard. No constant, range
or alias leaves the call, so a quotient used as a buffer index fails the
existing constant-index rules. Other runtime contexts, thunks and self-calls
cannot be combined with the summary.

A source may spell a call as the compiler emits it (`a / b`) or as the exact
addressed entry (`func_08142950(a, b)`). The original ELF relocation name is
bound per site, and a name that does not resolve to that site's entry is
refused. The four compiler names are reserved in preprocessed source. The
report's `runtime_summaries` record lists every site, every discarded scratch
alias, the component hashes, the contract and the producer hashes. It states
no numeric quotient, remainder or range, no definedness of C division by
zero, and no termination (partial correctness only). The existing division
schemas (`divsi3-positive-constant`, `udivsi3`, `modsi3-s16`, `umodsi3-constant`,
the addressed and compiler runtime selectors) are unchanged.

Focused checks: `FFTA_ROM=<approved ROM> python -m unittest test_runtime_summary_profile`
from `tests/`. They include the attack cases: a pointer operand, altered runtime
bytes or spans, interior targets, wrong call names and a quotient used as an
index.

### Explicit BIOS word-switch local buffers

`python3 tools/match.py --root <game> --owner-runtime-profile bios-word-switch-local-buffers-v1 <address>`
selects `elf-symbol-thumb-bios-word-switch-local-buffers-v1`. The structural API
is `owner_admission_profile.preflight(..., selector="bios-word-switch-local-buffers-v1")`;
preflight itself gives no C or ELF admission credit. Native matching still
requires genuine complete original ELF relocations, typed linking, exact ROM
bytes, plausible source and fresh report replay.

This route composes one existing unsigned-guarded word switch with one reached
interposed RAM/ROM object literal, a fixed restoring frame, existing bounded
ordinary-buffer effects and the exact indexed CpuSet `SWI 0x0B; BX LR` wrapper.
Named object and function literals retain their existing typed binding rules.
Every CpuSet call must carry a checked local R0 fill source and no other local
argument alias. Bit24 must select fill on every path; bit26 selects one aligned
halfword or word. Unknown width conservatively requires a complete aligned word.
The count does not expand the one-unit fill source; zero count is permitted.
Destination extent, physical readability/nonalias, initialization, numeric
results and termination are not proved. Returning BIOS semantics and ordinary
returning-call ABI remain explicit premises. There is no ordinary-ABI fallback
for an unchecked CpuSet site.

The exclusive `native-returned-local-aliases-v1` frame policy transports only
actual aliases returned by native bounded-callee replay. Later calls replay
those aliases again until native instructions kill them. Local bounds,
alignment, lifetime, joins, saved-register restoration and escape checks stay
active. No arbitrary return facts, scratch projection, pointer slots, incoming
stack-word permissions, local BL or indirect runtime calls are added. The
4096-byte owner/dependency and eight-dependency limits remain unchanged.
Default and older selectors still refuse this composition and returned aliases
at the strict frame seam. `test_bios_word_switch_buffers.py` and
`test_bios_word_switch_native.py` cover synthetic hostile inputs and real agbcc,
CLI, forged-report and stale-source replay. These tests confer no game credit.

### Explicit BIOS BgAffineSet local buffers

`--owner-runtime-profile bounded-buffer-bios-bg-affine-set-discarded-scratch-v1`
composes the following exact BIOS wrapper and disjoint local-span checks with
`DiscardedReturnScratchProof`. Ordinary helpers may leave local aliases in
R2/R3 only when the complete authenticated consumer continuation never reads
them or calls before a killing write or normal return. R0/R1 return escapes
still fail. Both the BIOS sites and scratch projections are bound into the
source-replayed report; this selector requires an actual projection. The
legacy selector below retains its existing refusal behavior.

`python3 tools/match.py --root <game> --owner-runtime-profile bounded-buffer-bios-bg-affine-set-v1 <address>`
selects `elf-symbol-thumb-bounded-buffer-bios-bg-affine-set-v1`. The owner is a
complete named-data Thumb owner whose ordinary calls keep the existing
bounded-buffer checks; it must contain at least one direct call to the exact
indexed BgAffineSet wrapper `func_08141864` (`SWI 0x0E; BX LR`, bytes
`0edf7047`). Each such call must pass exactly two tracked frame aliases (R0
source, R1 destination), no pointer slots or words, and a count in R2 that the
caller proves as a constant in 1..255 on every reaching path. BgAffineSet reads
`count` 20-byte source records and writes `count` 16-byte destination records
(GBATEK), so the profile requires both spans to be whole, word-aligned,
allocated local frame words (not saved registers or the return slot) and
disjoint. Nothing else is read or written under that premise. Named-data or
external operands are refused: `config/data_symbols.json` carries no object
sizes to bound them. Returning BIOS semantics and the ordinary returning ABI
for r0-r3 remain explicit premises; source initialization, numeric results and
termination are not proved. The profile does not compose with CpuSet fills or
the discarded-return-scratch projection: a local alias left in R3 by an
ordinary callee that is still live across a later call is refused as before.
`test_bios_bg_affine_set.py` covers counts, bounds, overlap, wrapper and index
tampering and manifest forgery on synthetic bytes;
`test_bios_bg_affine_set_native.py` covers real agbcc, CLI and report replay.

### CpuSet and CpuFastSet fills in one owner

`--owner-runtime-profile bounded-buffer-bios-mixed-cpuset-fast-fill-source-v1`
selects `elf-symbol-thumb-bounded-buffer-bios-mixed-cpuset-fast-fill-source-v1`
for a complete named-data Thumb owner that calls both the exact indexed CpuSet
wrapper `func_0814186C` (`0bdf7047`) and the exact indexed CpuFastSet wrapper
`func_08141868` (`0cdf7047`), alongside ordinary calls. Nothing is widened:
each call is checked by the proof that already owns it. A CpuSet site is
checked by `bios_cpuset_fill_profile.BiosFillProof`, exactly as under
`bounded-buffer-bios-fill-source-v1`. Bit24 must be set on every reaching
path, bit26 sets a halfword or word source unit, and an unknown width
needs a whole aligned word. A CpuFastSet site is checked by the
`bounded-buffer-bios-mixed-fast-fill-source-v1` proof: bit24 on every
reaching path and one aligned local word. Each wrapper call must pass only a
local R0 source with an external destination. Every other callee keeps the
unchanged named-data bounded-buffer check. The owner must reach at least one
call to each wrapper, the closed CFG must have no indirect branches or switch
words, and function literals and switches are refused.

The report records both site lists, under `bios_fill` and `bios_fast_fill`,
with the producer digests. Replay recomputes both, and a relabelled report is
refused. Destination extent, source initialization, physical
readability/nonalias, numeric results and termination are not proved.
Returning BIOS semantics and the ordinary returning ABI remain explicit
premises, as in the two component selectors. The pinned-volatile semantic check
uses the default ROM interfaces here, the same as
`bounded-buffer-bios-mixed-fast-fill-source-v1`. The older fill selectors still
refuse an owner that calls both wrappers. `test_bios_mixed_cpuset_fast_fill.py`
covers both proofs, the requirement for both wrappers, each site's own control,
source and destination refusals, stale manifests and swapped wrappers.

### Zero-extended CpuSet fill controls

A direct call to the CpuSet wrapper `func_0814186C` is not refused by the buffer walk as such. The
dead-argument walk treats it as an ordinary callee, and the wrapper's `swi` is
then refused (`buffer callee 0x0814186C: non-leaf calls and interrupts require
linked CFG verification`); the default plain path summarises it (see "GBA BIOS
wrappers in plain buffer walks"); the BIOS fill selectors replace that inspection with
`bios_cpuset_fill_profile.BiosFillProof`, which already checks every site: R0
must be the only local pointer, it is read as one source unit, and bit24 of R2
must be set on every reaching path. Bit26 chooses the unit width, and when it is
not proved clear the source must be a whole aligned word.

`--addressed-runtime-profile addressed-native-bios-fill-zero-extended-control-data-v1`
(schema `elf-symbol-thumb-addressed-native-bios-fill-zero-extended-control-data-v1`)
is `addressed-native-bios-fill-buffer-data-v1` with a stronger bit proof, for
controls the compiler builds from byte or halfword fields, such as
`(width * height) | 0x01000000` with `u8` fields. Besides the existing
authenticated Thumb encodings it knows:

* `LDRB` (immediate or register offset): the result is zero above bit 7,
  whatever the memory holds. `LDRH` is deliberately excluded: on the ARM7TDMI a
  misaligned `LDRH` returns the aligned halfword rotated right by 8, so its
  upper bits are not known zero;
* `MULS`: if both factors are below `2**a` and `2**b` and `a + b <= 32`, the
  product is below `2**(a+b)`; otherwise it carries no fact.

Only the 16-bit Thumb encodings are decoded, each from its bytes and operands,
and every other instruction (including four-byte forms, `svc`, `bkpt`, `udf`
and sign-extending loads) writes an unknown value as before. The facts only add
known-zero bits, each architecturally true, so the narrower halfword source
unit they can select is sound; the destination and the frame checks are
unchanged. A known-zero fact can also keep bit24 set through `BICS`, where the
older proof lost it; that is sound for the same reason. The older selectors
keep their exact bit proof and report text, and the new proof's manifest carries
a `bit_rules` field, so a report cannot be replayed under the other rules.
Source initialization, destination extent, physical readability and
termination remain unproved, and returning BIOS semantics remain a premise.
`test_bios_zero_extended_control.py` covers admitted and refused shapes, the
width arithmetic, wide-encoding refusal, forged and relabelled manifests and CLI
report replay.

### CpuSet copies whose source is a RAM-copied code image

Some routines are copied from ROM to RAM before they run, so the decomp keeps
them as bounded ROM entries (see the `0x08A38A2C` image above). The installer's
literal pool then holds an entry start, which a typed object may not name
(`addressed data overflows or aliases indexed code`) and which a function
literal cannot name (those bind Thumb entries and set bit 0).

Two opt-in selectors admit exactly that literal, and nothing else:

* `--addressed-runtime-profile addressed-native-bios-fill-scalar-control-numeric-mmio-code-image-data-v1`
  is `...-fill-scalar-control-numeric-mmio-data-v1` plus the binding below;
* `--addressed-runtime-profile addressed-native-bios-fill-scalar-control-code-image-data-v1`
  is `...-fill-scalar-control-data-v1` plus the binding below.

Their schemas are `elf-symbol-thumb-` followed by the selector name, so a report
cannot be replayed or relabelled under any older selector, and
`data_producer_fingerprint` additionally pins `cpuset_code_image_profile.py` and
`iwram_installation_prerequisite.py` for them only.

**Binding.** A typed object (`config/data_symbols.json`, e.g.
`data_08005088`) whose value is exactly the `rom` of one indexed row (ARM or
Thumb; zero addend; the value lies in exactly one row) is no longer refused.
Every other aliasing of indexed code is still refused. The CFG proof then
requires, for every load of that literal word:

* it is `ldr r0, [pc, #n]` and nothing else loads the word;
* one linear path reaches an actual CpuSet wrapper call; every instruction on
  it has exactly one predecessor (no joins) and r0 is not written on the way.
  The only read of r0 is `subs r2, rN, r0` (r0 the subtrahend, r2 the
  destination; the `end - start` length of `0x08002768`). Any other `subs`,
  `negs` or other read of r0 is refused, and until r2 is overwritten every read
  of that derived r2 must be an r2-to-r2 shift or add/sub immediate. The flags
  that subtraction and those steps set also carry the alias, so from the `subs`
  to the call only instructions that do not read flags may appear (`adcs`,
  `sbcs`, `rors` and anything conditional are refused), and the same holds after
  the call until a `cmp`/`cmn`/`adds`/`subs`/`negs` recomputes the flags (a later
  call with tainted flags is refused);
* after the call r0 may not be read (the BIOS is assumed to leave source plus
  length there, an unproved register premise) until it is written, a later
  call may not see it live, and no function exit may be reached with it live;
* constant propagation over the exact bytes gives r0, r1 and r2 on every
  reaching path: r0 equals the literal, r2 is a plain copy control (bit 24 clear,
  no reserved bits, 1 to 0x200 bytes; the real images are 0xB0 and 0x140) and r1
  is aligned with the unit width with the whole destination in EWRAM or IWRAM
  below 0x03007E00 (above it is the BIOS-reserved IRQ vector and stacks). The
  destination may overlap typed objects the function itself writes; that is not
  checked.

**What is recorded.** `manifest['code_image_sources']` holds, per call, the
source, destination, control, unit width and count, a SHA-256 of the copied ROM
bytes, every indexed row the span intersects with its mode and covered byte
count, the unindexed gaps and the overrun. The span is bounded: at most 3 rows (the largest real case, `0x08002768`; a reviewed bump is needed to go higher),
gaps of at most 3 bytes (alignment padding), no covered row may be the owner or
the CpuSet wrapper. A copy may read past its image: it is *admitted and
recorded* when the only partially covered row is the last one the span reaches
and at most 0x80 bytes of it are read (`0x08004AC0` reads 68 bytes into the Thumb
function at `0x080051C4`), and the span may not start inside an indexed row. The alternative of refusing an
overrun, or of requiring it to be named, was rejected: the overread is a fact
about the original, the selector only claims static source-span identity, and
the rows are written into the report (and re-derived on replay) either way.
Rows after the first are rows the span covers: they are recorded, not asserted to be part of the image.

**Not proved.** No BIOS effect or return, readability, persistence of the
installed bytes, destination safety, or any property of the installed code; the
literal is not callable, storable or an object bound (any other use of the word
is refused). It does not widen function literals or ordinary objects.
`test_cpuset_code_image.py` covers admitted and refused shapes, overrun, gaps,
forged manifests, relabelling and report replay.

### The m4a scanline limit linker symbol

The USA `MPlayExtender` at `0x081453F8` uses the GBA library's `extern char
gMaxLines[]` and `MAX_LINES ((u32)gMaxLines)`. The selector
`--addressed-signed-runtime-profile addressed-m4a-extender-bios-fill-max-lines-v1`
checks the original undefined global NOTYPE symbol, its single zero-addend
`R_ARM_ABS32` at offset `0x110`, and the linked size-zero NOTYPE absolute with
value 80. The load at `0x08145478` supplies the byte stored at mixer offset 12
at `0x0814547C`; the next assignment to its register ends that value's lifetime.
The ROM supplies the numeric value. The historical library source supplies the
symbol name and its scalar interpretation. A data-map entry for the symbol is
rejected. The report records the linker absolute separately from objects and
callback functions.

The BIOS fill and typed callback checks also run. The owner ELF relocations for
slots 17, 19 and 29 must agree with the independent ROM table at `0x0836D098`
and the callback entry extents in the function index. Saved reports recompile
and relink the original source to replay this evidence.

### Fixed hardware addresses as numbers in BIOS fill owners

A source may name a VRAM, palette, OAM or I/O address as a plain number, such as
`(u32 *)0x0600B1E0`. The compiler puts it in the literal pool with no relocation.
Naming it as a data symbol is not the same source: a symbol is a relocation and
a constant is not, and the register allocation can differ.

The owner selectors `bounded-buffer-bios-fill-source-v1`,
`bounded-buffer-bios-fill-local-source-semantics-v1`,
`bounded-buffer-bios-fill-overwritten-control-stores-v1`,
`bounded-buffer-bios-fast-fill-source-v1`,
`bounded-buffer-bios-mixed-fast-fill-source-v1`,
`bounded-buffer-bios-mixed-cpuset-fast-fill-source-v1` and
`bounded-buffer-bios-mixed-fast-fill-runtime-summaries-v1`, and the addressed
`addressed-native-bios-fill-*-data-v1` selectors, give each reached PC-loaded
pool word the first class that applies:

1. a typed ABS32 object or function literal;
2. a BIOS scalar control, in the selectors that compute controls;
3. a switch word (these selectors have none);
4. in the numeric-MMIO selectors, a halfword-aligned I/O literal in
   `[0x04000000,0x04000400)`, with its existing record;
5. a numeric hardware word: any other word in `[0x04000000,0x08000000)` (the
   window of `unsigned_thunk_profile.HARDWARE`), provided no load of it is
   accepted on its own by the CpuSet scalar-control recognizers (direct R2 or
   saved R4-R7).

Every other reached address word still needs typed provenance. That covers
RAM (`0x02`, `0x03`) and ROM (`0x08`), and also a hardware-window word with a
control load that is not a control in the selector at hand. Examples are a
32-bit CpuSet fill control such as `0x05000100` under a selector that computes
no controls, and a word loaded once as a control and once as an address. So the
classes stay disjoint: a load that the recognizers accept as a control never
makes its word a number.

The recognizers model only direct and saved CpuSet R2 loads. So a CpuSet
control that reaches R2 by another path (say `ldr r3` then `adds r2, r3, #0`)
is recorded as a numeric hardware word in any of these selectors, including
those that compute controls. So is a CpuFastSet control in the window. That is
a label only: the fill proofs read the control from the register value
whatever its pool word's class, and the record claims no control role.

When the class is not empty, the manifest carries `numeric_hardware_words`
(schema `reached-numeric-hardware-literals-v1`). Each row is
`[offset, value, load sites]`. The record is absent when the class is empty,
so existing reports keep their bytes and meaning. Replay recomputes the
classification, and an edited, dropped or extended list is refused.

The record claims literal identity only. The original ELF word has no
relocation, and the linker must preserve it exactly. A register that holds such
a word is a non-local value. Tracked stack aliases come only from SP
arithmetic, and no address in the window lies in the stack, so the existing
buffer, fill-source and frame proofs are unchanged. No typed symbol, pointee
type, hardware access validity or memory effect is claimed. Every other owner
and addressed selector is unchanged, including the ordinary-BIOS, runtime,
callback and native-buffer data selectors.

The pinned-volatile CpuSet interface builds its premise from the owner
preflight, and that path is not changed. The preflight still asks for a name
for every reached address word, as it already does for 32-bit fill controls.
So an owner whose semantic check runs still refuses a numeric hardware word.
`bounded-buffer-bios-fill-overwritten-control-stores-v1` always runs that check.

`test_numeric_hardware_words.py` covers each selector, the window bounds, typed
words, controls, mixed loads, numeric MMIO, other selectors and forged
manifests and reports. `test_numeric_hardware_words_native.py` compiles real
CpuSet and CpuFastSet owners and replays their reports.

### Expired root-frame scratch at the root's own return

`--owner-runtime-profile bounded-buffer-root-return-scratch-v1` (ordinary
bounded buffer calls, named data optional) and
`bounded-buffer-conditional-thunks-root-return-scratch-v1` (the conditional
canonical thunk composition) select
`elf-symbol-thumb-bounded-buffer-root-return-scratch-v1` and
`elf-symbol-thumb-bounded-buffer-conditional-thunks-root-return-scratch-v1`.
They admit one shape the default refuses with `local stack pointer escapes
through a return register`: a root whose own frame address is still in R2 or
R3 when it returns - typically a buffer pointer a callee left there, or a
spilled local address no later instruction reads. Default selection and every
earlier schema are unchanged.

The projection uses the existing `thumb-discarded-exit-scratch-v1` premise
(R2/R3 carry no results under the agbcc Thumb ABI) and only at the bound root:
its exact body, with no inspected callee active, at an exact normal return after
the frame is restored, for addresses strictly inside the expired root frame.
A join whose R2/R3 offsets differ is dropped only when every path from it
reaches such a return, or overwrites the register, with no read and no call in
between. R0/R1, R4-R11 and LR still refuse, as does any inspected callee that
returns its own frame address - there the consumer is a known caller this
policy does not check. Every alias use before the return keeps its existing
bounds, spill, escape and callee-replay checks. Reports bind the root hash,
return sites, each projected `[site, register, offset]` taken from that
return's final fixpoint state, and every dead join drop evaluated during the
fixpoint (intermediate states included). A selection whose final return states
project nothing refuses; a join drop alone never satisfies it. Synthetic boundaries are in
`tests/test_root_return_scratch.py`.

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

### Restoring frames with exact R6 callback targets

`--owner-runtime-profile static-callback-restoring-r6-target-v1` explicitly
selects complete R6 callback and ordinary restoring frames. Every nested call
needs a completed frame certificate and fresh bounded alias/effect replay.
The callback leaves R6 and the R11 replay guard unwritten; other saved registers,
SP and the entry return address must be restored on every normal-return path.
Canonical thunk identity, typed original ELF relocations and full report replay
remain required. Descriptor-word composition remains excluded.

The selector states the compatible normal-return premise that R2/R3 are
discarded scratch. Projecting a returned local alias also requires its actual
unique complete consumer and a continuation that never reads or passes that
register before a killing write or normal return. Reports bind these consumer
bytes, sites and observations. R0/R1 are never projected. Earlier selectors,
including `static-callback-restoring-r6-v1` with its leaf R7 target, retain their
policies. No physical-memory, nominal C type, numeric or termination theorem
follows. Synthetic boundaries are in `tests/test_static_callback_r6_target.py`.

`static-callback-restoring-entry-aliases-aligned-v1` additionally permits watched
R4-R10 entry values to be privately saved and restored. Those opaque values
cannot be read, copied, addressed through the stack, or carried live across a
nested call. A separate complete frame proof and fresh effects replay must
prove restoration; entry values cannot escape through result registers. R11
remains an unwritten replay guard. Earlier selectors retain their policies.

`static-callback-restoring-scratch-prefix-aligned-v1` also permits an actual
consumer call to kill projected R2/R3 scratch in its entry prefix. Every path
must overwrite the incoming values before any observation, save, copy, call or
return; cycles that can avoid the writes refuse. The prefix proof alone grants
nothing: the same proof instance must finish fresh effects and authenticated
frame replay for that exact consumer, call site, target and complete body.
Both selectors retain the existing conditional ABI and memory premises and
do not establish RAM installation identity. Synthetic boundaries are in
`tests/test_r6_nested_entry_alias_restoration.py` and
`tests/test_r6_scratch_prefix_kill.py`.

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

### Menu icon row with a transient decoder output pointer

At `08053E4C`, `--owner-runtime-profile bounded-buffer-runtime-summaries-v1`
binds the original two calls selecting graphics 393 and 394, the unsigned
remainder by five, the named tile base and string table, and the fifth stack
argument. The original decoder reads two fixed streams from `083C83FC`.
Each produces exactly 128 bytes in the live frame. The decoder leaves the
buffer address in `03002BB8`. An append through that global after the frame
expires requires the output to have been reinitialized.

The modeled BIOS calls use a 64-halfword CpuSet copy and a word CpuFastSet
clear. The input contract requires readable text, aligned disjoint tile
storage of the necessary length, and a returning text renderer. Widths zero
and one wrap the clear count, and width two programs zero. The native tests
exercise these descriptors without assigning zero-length BIOS semantics.
A fifth argument of one reaches the text renderer for both icon cases.

The same selector covers the sibling at `08054314`. Its known caller at
`080539F0` passes row zero, a halfword entry and stack style five. The
getter at `08017B68` sign-extends the low row byte, adds the list position,
narrows the sum to a signed halfword and compares it to the signed list count
minus one. A negative sum returns zero. For a nonnegative sum and empty list
the upper clamp returns 65535. The original signed-remainder helper then
receives this zero-extended halfword and a divisor between 1 and 256, taken
from the byte height plus one. The doubled row offset wraps to 16 bits before
adding the base tile. The caller still supplies the physical allocation and
the name pointer within the common renderer contract.

### Complete ordinary owners with multiple guarded switches

The explicit owner selector `ordinary-multiple-switch-source-v1` compiles plausible
source with the fixed toolchain and binds the actual original relocatable ELF,
its typed linked ELF, both indexes, the full ROM and current runtime. It derives
two through eight guarded tables from every original local section relocation.
Unique table partitioning, guard predecessors, complete acyclic CFG, byte
partition and restoring frame checks are mandatory. Source admission and status
replay use the same original-ELF verifier and exact manifest.

The general admission path accepts genuine ordinary zero-addend direct calls
and local switch relocations. Arithmetic runtimes, indirect thunks, extra named data or function
words, local pointer materialization, local cycles and mixed runtime policies
are rejected. Ordinary callee effects remain conditional on the returning ABI;
this does not prove memory safety, physical separation, numeric equivalence or
termination. A data-only owner API cannot select this source profile.

The same selector covers the 306-byte menu query at `0804E224` with one
zero-addend data relocation to the 300-entry halfword table `08529EE4`. Its
eight outer dispatch slots and 21 inner slots account for all 31 local
relocations, including both table pointers. The original task getter returns
the payload at task + 24. Five known call sites pass the full word to a store,
and the sixth sign-extends its low halfword. On dispatch state 2 the caller
checks for a nonzero selection. The caller must supply a readable task and
the backing entries required by its menu type. Type 1 accepts the -1 sentinel;
types 3–6 using the word bank require a valid entry, and type 8 uses one-based
selections 1–300. Zero reads the preceding ROM halfword on type 8; 301 reads
the terminator. A nonzero check alone cannot establish these bounds.

At `08034E88`, the selector verifies the 364-byte menu callback registered
in slot 2 of the five-entry runner at `03002720`. The first guarded table has
one interposed state-pointer word. The second has the state pointer and the
numeric offset `0x4B9`. All 31 local table relocations, three external state
words and 19 ordinary calls must agree with the original object and ROM.
The callback reloads the state pointer for each of its three byte reads.
Each pointer must still address the requested field after the preceding call.

### Two incoming words with canonical integer calls

`--owner-runtime-profile canonical-integer-two-words-aligned-data-source-v1`
adds a separate, explicit transport for the same two incoming word contract
when the original assembler emits exactly one external two-byte Thumb NOP.
Both original and linked ELF must have the canonical four-byte section alignment,
an unchanged complete function, and no symbol or relocation owning the tail.
The tail remains outside the indexed function and byte comparison. Genuine
zero-addend named data identities and the existing CFG, frame, runtime and
incoming-read checks remain mandatory. This does not grant data accessibility,
contents, extent, or physical stack separation. The existing selectors retain
their previous alignment boundaries.

`--owner-runtime-profile canonical-integer-two-words-data-source-v1` is an explicit
source selector for a complete original relocatable function with compiler-emitted
canonical integer calls and zero-addend named data literals. The existing closed
frame proof requires actual direct reads of both incoming words at entry SP+0 and
SP+4; stores, a third incoming word, SP-address escape, or unbalanced frames fail.
The original and typed linked ELF roles, both indexes, full ROM body, producer
pins, source and headers remain authenticated. The default scalar and six-word
selectors retain their existing boundaries. Readable aligned incoming words and
ordinary returning callee ABI contracts are explicit premises; named object
points grant no contents, extents or physical memory permissions.

### Conditional counted scheduler loop

`--owner-runtime-profile conditional-scheduler-u16-counted-loop-v1` admits a
separate closed loop form: actual unsigned 16-bit count narrowing, zero counter,
initial unsigned bypass, exact increment and narrowing, and a strict unsigned
backedge. The counter and bound occupy distinct ABI-preserved low registers;
all body paths reach the update without modifying them. There is one scheduler
site and at most four ordinary targets/eight call sites in a finite body.
The complete prefix and suffix are call-free and the owner has no other cycle.
The rank proves at most 65,535 iterations conditional on instruction completion
and returning calls. It does not prove that any array has that capacity.

Every reached call still passes the full existing frame and pointer-provenance
checks. Ordinary calls reject all tracked local aliases and pointer words.
The 28-byte descriptor contract is reapplied on every abstract incoming path;
allocation separation, physical access, protected-frame preservation and no
retained descriptor pointer remain explicit premises across iterations. No
callback effect, memory permission, actual count, or unconditional termination
claim follows. Existing acyclic scheduler selectors retain their strict guards.

### Sequential live-alias scheduler compositions with counted loops

`--owner-runtime-profile conditional-scheduler-sequential-live-alias-counted-loops-v1`
composes the three-per-path phase rule (at most four scheduler sites, at most
three invocations on any path outside loops, ordinary calls after a scheduler
return), the live private-local alias rule for ordinary calls exactly as in
`conditional-scheduler-live-local-alias-calls-v1`, and the unchanged 28-byte
descriptor contract at every scheduler call; a scheduler site inside a loop
admits no local alias besides the R2 descriptor and copies of its address in
R4-R7. At most 24 ordinary targets leave dependency room for live-alias nested
callees; the owner has at most 256 instructions. It additionally admits CFG cycles,
but only as narrowed counted loops; an owner without cycles is admitted too.

A loop is one strongly connected component with a single entry (its header),
one conditional backward edge into the header and no other cycle. The back
edge closes a straight tail whose instructions each have a sole predecessor:
`adds rT, rC, #1`, `lsls rT, rT, #S`, `lsrs rC, rT, #S` with S = 24 (u8) or
16 (u16), then either a fresh zero-extending `ldrb`/`ldrh` of rL no wider than
the counter, `cmp rC, rL`, `bcc header`, or `cmp rC, #imm` with `bcc` (imm at
most the counter range) or `bls` (imm at most range minus one). rC is R4-R7
and no other instruction of the component writes it. Taking the back edge
therefore implies rC <= 2**W - 2, the next narrowed successor is rC + 1 without
wrap, and the header is entered at most 2**W times per execution, for any
incoming counter value. The bound depends on R4-R7 surviving each call (the
returning ARM ABI premise). A loop with k scheduler sites records at most
k * 2**W invocations (a looped site runs at most once per iteration); each
invocation is passed the same descriptor frame and reapplies every per-invocation premise,
including that no earlier invocation or callback retains the reused descriptor
or any local pointer. The owner may store to the descriptor between
invocations; those stores are checked by the frame and alias replay like any
other store through a local alias. Actual counts, capacities, callee effects and
termination remain unproved.

A copy of the descriptor address in R4-R7 is the one alias besides R2 that a
looped scheduler site admits. Its frame offset must equal R2's at the call, on
every incoming path, and it is recorded in the site's aliases. The invocation
is already handed that address in R2, so the copy names no storage the
scheduler or its callback could not already reach under the descriptor
premise; that it still holds the address after the call is the returning ARM
ABI premise the loop counter already depends on. A different object, an
interior address of the descriptor, R8-R11 and any caller-clobbered register
other than R2 stay refused at a looped site. This is the shape agbcc emits when
a loop stores halfword fields of the descriptor (Thumb has no SP-relative
`strh`) and keeps the base register live across the call.

### Wide three-per-path live-alias scheduler phases

`--owner-runtime-profile conditional-scheduler-three-per-path-live-alias-v1`
applies every rule of
`conditional-scheduler-sequential-live-alias-counted-loops-v1` (per-path
scheduler bound of three outside counted loops, counted-loop shape, live-alias
contract for ordinary calls, unchanged 28-byte descriptor contract, no alias
besides R2 and R4-R7 copies of its address at a looped scheduler call) under
wider cost bounds: at most eight
scheduler sites in total, 32 ordinary targets, 48 call sites and 512 owner
instructions. None of these bounds carries a proof obligation: the per-path
bound still limits how often the scheduler runs, every scheduler site is checked
against the descriptor contract on its own, the CFG checks are linear, and each
call site adds one per-call check that keeps its own replay or walk budget.

It adds two refinements to the live-alias rule for ordinary calls, and only for
this selector:

* An alias in R0-R3 or R12 is dead at callee entry when the complete callee CFG,
  decoded as ARMv4T Thumb, overwrites that register on every path before any
  instruction reads it, before any call or software interrupt and before any
  return (least fixpoint, so any cycle reached before the overwrite keeps it
  live; a callee without a closed CFG overwrites nothing). A dead alias is not an
  argument: the callee is not replayed for it and it does not lower the replay
  bound. It is recorded as `dead_at_entry_aliases`.
* A passed alias in R0-R3 or R12 that the callee returns is handed back to
  the caller only when it is definite: the callee is a closed leaf (no call, no
  software interrupt) that never writes that register, so every return holds
  the passed value. The caller keeps tracking it as a local alias, as the
  ordinary buffer verifier does. Any later read, store, spill, call argument or
  scheduler use of it is checked like any other alias, so a stale returned alias
  reaching a scheduler call is refused. It is recorded as `returned_aliases`.
  Any other returned alias is still refused.

Callee effects, nested execution and termination remain unproved, as for the
other live-alias selectors.

### Scheduler descriptor calls as per-site summaries

`--owner-runtime-profile conditional-scheduler-call-site-summaries-v1` applies
the 28-byte descriptor contract at each scheduler call on its own and puts no
bound on the shape of the caller: any number of scheduler sites, ordinary calls
before and after them, and CFG cycles. The other `conditional-scheduler-*`
selectors bound the whole caller (one scheduler call, at most N sites or
targets, acyclic, no call after a scheduler return); those bounds limit the
cost of their whole-owner proofs and are not part of the frame argument. Here
the complete owner is replayed by the named-data buffer walk: joins, saved
slots, returns, loops and every other call keep the unchanged buffer rules. A
call that receives a local pointer, in a register or as a pointer-bearing
frame word, is inspected as a bounded buffer callee; once such a word is in the
frame every later call receives it. A call that receives none uses the
returning ABI summary. Only a direct call from the owner to one of three
pinned entries is summarised: `func_08005B6C` and `func_08121B8C` (callback R0,
descriptor R2, parent R3) and `func_08005954` called directly (manager R0,
callback R1, descriptor R3, parent in the outgoing word at SP). A pinned entry
reached inside an inspected callee is not summarised: if it receives a local
pointer it is walked like any callee and refused at the callback thunk,
otherwise it takes the returning ABI summary.

At each site, from the walk's state there:

* the descriptor register is the only alias in R0-R3, R12 and LR;
* the descriptor is word aligned and its 28 bytes are allocated local words;
* at a direct `func_08005954` site the outgoing word at SP is an allocated local
  word below the descriptor and holds no tracked local pointer (the callee reads
  it as the parent and may overwrite it). Every definition of R0 that reaches
  the site is a load chain rooted at an owner literal word: a zero-offset word
  load, then at most one word load at an aligned field offset 0-124, through
  exact register copies and joins. These are the chain shapes of the four
  direct-entry selectors. Every chain literal must have one typed zero-addend
  named data binding, and every chain is recorded;
* a pointer-bearing word inside the descriptor is admitted only at
  descriptor+4 or descriptor+8 and must address an allocated local word outside
  the descriptor. It is recorded with an explicit extent: from its target to
  the end of that run of allocated local words, or to the descriptor if that
  comes first (an upper bound, not a type size). The extent must hold no
  pointer-bearing word and, at a direct `func_08005954` site, not the outgoing
  word. Pointer-bearing words elsewhere in the frame are recorded and keep
  their facts; no pinned body reads them;
* preserved-register aliases are recorded. At a site inside a CFG cycle only
  R4-R7 copies of the descriptor address are admitted, and no pointer-bearing
  word, as for the looped sites of the counted-loop selectors;
* every definition of the callback register that reaches the site is a
  PC-relative load of an owner literal word, directly or through exact register
  copies in R0-R12 (`adds rd,rs,#0`, `movs rd,rs`, `mov rd,rs`), and every such
  word must be a typed function binding. A callback loaded from a table or
  memory, passed in, or clobbered by a call is refused;
* the call hands back no alias, and the walk clobbers R0-R3, R12 and LR as at
  any call.

Both register searches walk back over the complete owner CFG. An interrupt or
a call that is not a validated `bl` refuses any value, and a validated call
refuses a value in R0-R3, R12 or LR; a value in R4-R11 held across a validated
call rests on the returning ABI premise, as every preserved-register fact does.

The report lists every site (entry, callback literals, manager chains,
descriptor offset, payload words and extents, other pointer words, aliases,
whether it is in a cycle), the pinned entry bodies and canonical thunks, and
the descriptor premises of the other scheduler selectors, stated per
invocation: compatible returning calls with exact SP and protected words, no
retained or returned local pointer, allocator separation and callback frame
noninterference, the copied R1 descriptor and the original R9 exposed to the
callback, a valid parent, readable chain words and a valid manager at the end
of the recorded chain, and payload reads only through the payload word, within
its recorded extent and before the call returns. Callback effects, nonescape,
manager memory access and termination are not proved.

#### Version 2: forwarded callee stack arguments

`--owner-runtime-profile conditional-scheduler-call-site-summaries-v2` is v1
with the forwarded callee stack arguments of `named-data-buffer-stack-index-v2`
(see "Version 2: forwarded callee stack arguments and sign-extended indices"
above). The coordinate wrappers `func_080DBD78`, `func_080DBDA0` and
`func_080DBDC8` pass the owner's local `s16` outputs on to their own callee as
stack arguments (`str r2,[sp]; bl func_0801C984`), which v1 refuses
("unsupported buffer pointer use or escape"). Under v2 every buffer callee the
walk inspects applies the same rule as stack-index v2, with the same code in
`match.BufferCallProof`. A pointer into the owner's frame may be stored into an
aligned word of the callee's own frame, only in a callee whose every SP use is
`push`, `pop`, `add/sub sp,#imm` or an immediate `[sp,#imm]` access. The next
callee is walked with that word as an incoming stack argument, so every access
through it is still bounded against the owner's frame. A released word is
tracked until it is written, walked callees inherit it, and the calls trusted
while it lies below SP are recorded. A call an inspected callee makes with its
own frame keeps v1's buffer rules, with no forwarding: a slot holding the
callee's own frame would not be in the owner's terms.

The owner rule is also the same. The words a walked root call's callee
released are recorded and removed from the call's result. On every owner CFG
path after that call the selector refuses `sub sp,#imm` (the core walk already
refuses `add sp,Rm` and `mov sp,Rm`). It also refuses every call the walk
inspects there: one that receives a stack pointer in R0-R3, R12 or LR, or while
a frame word holds one, and every scheduler site, whose summary says nothing
about the word. Every other later call is trusted under the forwarded stack argument
premise of stack-index v2, recorded in the evidence
(`forwarded_stack_arguments`: slots, released words, trusted owner and callee
calls, `premise`, `premise_proved: false`) and as the same report line. This
walk never replays loops, so forwarding and replay never meet. v2 requires at
least one forwarded slot, so a function v1 admits stays v1's, and a v2 report
relabelled as v1 fails replay.

### Conditional coordinate outputs before a scheduler call

`--owner-runtime-profile conditional-scheduler-projected-outputs-v1` composes
four complete indexed helpers before one scheduler call: ordered object-byte
reads and two halfword outputs, a read-only indexed table lookup, three world
coordinate outputs, and two screen coordinate outputs. Complete helper bytes,
CFGs, named identities, local frames and returned pointer origins are checked.
A separate scalar-immediate-add opt-in accepts only an already scalar origin;
existing three-output policies retain their default instruction boundary.

The caller must have the exact bounded private layout and straight-line call
order. A stale R2 pointer survives the first helper until the actual table
helper overwrites it before observation. Both outgoing pointer words remain
tracked through the screen helper and scheduler; they are never erased as
unused arguments. Every helper output is checked against its private halfword
bound and the protected saved words.

Physical readability, initialized named halfwords, table access, allocator
separation, scheduler/callback frame preservation and nonretention remain
explicit conditional premises. In particular, the scheduler and callback may
access caller storage only through the bounded descriptor, not through the
recorded outgoing pointer words or preserved-register aliases. The report does
not prove callback effects, physical nonaliasing or unconditional termination.

### Indirect scheduler manager field

The explicit `conditional-scheduler-indirect-manager-v1` owner profile accepts one
direct call to the pinned `08005954` entry when R0 is reached by a typed named
literal followed by exactly two zero-offset word loads. It retains the 28-byte
word-aligned descriptor, separate outgoing parent word, protected frame and
nonretention checks. Both pointer-storage words must be readable, aligned and
separate from caller stack storage; the final manager must satisfy the existing
scheduler contract. Those are explicit conditions, not inferred memory facts.
The existing scheduler-entry selector and default policies are unchanged.

The separate `conditional-scheduler-manager-offset-v1` profile follows the
actual low-register definitions through a finite straight-line load chain.
Its first pointer dereference has offset zero; its final word load can use
an aligned Thumb immediate field offset from 0 through 124 bytes. The report
records both load sites, their registers and the field offset. Branch joins,
intervening calls, overwritten provenance, indexed loads, other access widths
and additional dereferences are rejected. The literal must have one exact
typed zero-addend data binding. Existing descriptor and frame checks still
apply. Readability, address arithmetic without wraparound, storage separation,
the final manager contract and callback effects remain explicit conditions;
intervening writes do not imply that memory values remain unchanged.


The separate `conditional-scheduler-manager-paths-v1` profile authenticates every
syntactic entry-to-call path into one pinned `08005954` call. Each path must
establish R0 from a low-register PC-relative literal, a zero-offset word load,
and an aligned immediate field word load at offset 0 through 124. First reaching
register definitions are checked; paths may share loads but may not contain a
cycle, missing entry origin, intervening call, unsupported load or overwritten
provenance. Traversal is bounded to 4,096 paths, 4,096 instructions per path and
65,536 traversal steps. Every distinct chain is recorded and every literal word
requires an authenticated typed zero-addend data binding. The existing outgoing
parent, aligned 28-byte descriptor, frame and scheduler dependency checks apply.
Readability, separation, arithmetic without wraparound, valid manager, ABI and
callback effects remain explicit premises; no equality of loaded values between
paths follows. Prior straight-line selectors retain their existing boundaries.


The explicit
`--owner-runtime-profile bounded-buffer-bios-bg-affine-set-transparent-leaf-scratch-v1`
composition can continue an R2/R3 nonobservation check across an exact ordinary
call only when the independently authenticated complete callee is a bounded,
acyclic, noncalling Thumb leaf that never reads or writes those registers.
The registers remain live after the call; every later consumer path must still
reach a genuine overwrite or normal return without observing them. Its closed
effect table adds only register-offset LDRSH to the existing restricted leaf
effects. Selected-register writes, nested calls, unknown effects and incoming
flag dependence remain refused. This is conditional on the ordinary returning
ABI and the existing local BgAffineSet contract; it does not prove physical
readability, initialization or termination. The distinct source-replayed report
requires actual transparent-call observations and binds caller/callee bytes,
partitions, exact call sites, input snapshots, all producers, runtime and selected
toolchain binaries. Earlier selectors retain their existing refusal boundaries.

### Bounded odd signed remainder

`--signed-runtime-profile signed-remainder-u16-quarter-odd-v1` accepts one compiler-emitted
`__modsi3` in a complete scalar Thumb caller. It replays the canonical integer source
verifier, including typed original ELF relocations, both runtime bodies, caller frame and
ordinary returning-call ABI premises. The dividend must come from `ASR #16`. The divisor
must come from a zero-extending halfword load, `LSR #2`, `LSL #1` and `ADD #1` on a
single reaching-definition path. The doubled value crosses one ordinary BL in an
ABI-preserved register. Merges in those paths, clobbers, cycles and alternative compiler
or addressed runtime identities fail.

For all 65,536 halfword inputs, the divisor is odd and lies in 1 through 32,767.
The signed dividend lies in −32,768 through 32,767. This rules out division by zero
and signed division overflow. The report records the defining instructions, preserved
register and intervening call. Its acceptance reruns the fixed compiler and both proofs.


### Weighted effect descriptor callback

`--signed-runtime-profile conditional-four-choice-effect-v1` recovers slot 30 at
`081323D0`. The original ELF binds the signed remainder, the R1 call veneer, and
the descriptor table. The picker writes one signed halfword in the caller's
four-byte local. A roll modulo 101 selects one of four ROM records. The caller
uses a second roll modulo 1001 and dispatches a successful choice through the
record's actual Thumb callback.

The report records the picker and scorer stack arguments, the four descriptor
words, the restoring callback bodies, and their leaf callees. Ordinary scorer
calls retain the existing returning ABI premise. The game objects and RNG state
must be accessible and separate from private stack storage. Slot 29 has a
different picker with an additional fallback and remains outside this selector.

### Stat-drain divisor switch

`--signed-runtime-profile stat-drain-divisor-switch-v1` verifies the 514-byte
function at `08128C3C`. The original ELF has one named divisor-table relocation,
eight local switch relocations and thirteen Thumb calls. The assembler's two
alignment bytes follow the end of the function symbol.

The owner indexes the ROM table at `083A8260` with the low three bits of key
byte 2. Its eight divisors are 10, 5, 2, 1, 3, 5, 10 and 20. Six cases call
the stat getter and use unsigned division. The seventh divides ten by the
selected byte using signed division. The complete getter and its read-only
lookup preserve the divisor in R4 on every return. The lookup can follow a
record redirect loop. The report binds the original ELF, linked bytes,
complete DIV/UDIV implementation and both indexes on each replay.

Set `FFTA_STAT_DRAIN_ROOT` to a recovered USA game tree to run
`tests/test_stat_drain_profile.py`. The CPU test executes the original getter
and both division helpers for all 256 key bytes across seven cases and the
default path. It checks the return value, unit writes and preserved registers.

### Active-entry removal shuffle

`--signed-runtime-profile active-entry-shuffle-v1` verifies the 160-byte routine
at `08128E40`. It scans the 20 halfwords at `02001F3C` and appends the indices
of nonzero entries to a 20-byte local. An empty table returns immediately.
For every nonempty prefix, four shuffle passes use the original 15-bit RNG
and signed remainder with the initialized length as divisor. Each exchange
reads and writes two bytes within that prefix. The routine clears the first
`min(requested, length)` selected table entries, then compacts the table.
A zero removal request still shuffles and compacts a nonempty table.

The proof binds all four compiler call relocations, the state-base relocation,
both table helpers and the complete signed remainder implementation. Its private
stack premise keeps the live prefix separate from the table and RNG seed.
Set `FFTA_ACTIVE_SHUFFLE_ROOT` to a recovered USA game tree to run
`tests/test_active_entry_shuffle.py`. Its CPU test compares the original local
accesses, table contents, RNG state and register restoration for every active
length from zero to twenty.

### Active-template selection

`--signed-runtime-profile active-template-selection-v1` verifies the 228-byte
routine at `08128EE0`. It collects physical indices of templates with a nonzero
packed name into a 20-byte local. An empty collection returns the fixed text
pointer from slot 744. For a nonempty collection, mode 2 uses the 15-bit RNG
and signed remainder to select an initialized local byte. Mode 3 selects the
last maximum appearance byte. Other modes select the last minimum at or below
99. When every active appearance exceeds 99, the original clears physical
slot zero, which can be inactive.

The clear helper writes fifteen bytes in the selected 16-byte template and
preserves byte 4. The original lookup then uses the selected physical slot
to fetch the return value. All twenty reachable unit IDs have zero redirect
bytes in the USA records. The verifier checks those rows and their text pointers,
the complete nested lookup, and the original relocations including the state
base plus the appearance-field displacement. The CPU test compares stack reads,
all clear writes, RNG effects and the returned pointer using the original callees.
Set `FFTA_ACTIVE_SELECTION_ROOT` to the recovered game tree to run
`tests/test_active_entry_selection.py`.

For the USA effect-or-delay starter at `080DCFE4`, the opt-in
`conditional-scheduler-descriptor-payload-calls-v1` selector keeps the
two stack layouts distinct at their common BL. It authenticates the
synchronous zero-phase callback for each and the installed 20-byte
copy from the effect record. The record must be readable and separate
from the fresh task. Allocator success, valid independent manager
storage and the IWRAM installation remain explicit premises.

The USA starter at `080D3508` uses `--owner-runtime-profile conditional-effect-registry-scheduler-v1`.
Its two eight-byte registries hold 341 and 20 entries. The owner passes the
callback and size from the same entry to the direct scheduler. ID `0x159`
overrides both, selecting the 40-byte `080E2398` callback and reading primary
metadata using the full third argument. The selector checks both ROM tables,
all 240 distinct non-null callback entry addresses in both function indexes,
the two query routines and their dependencies, and the scheduler's descriptor
and phase-zero dispatch. The normal per-site frame, manager and parent checks
apply. Returning execution requires ID 1 through `0x169` except the empty
dispatch row `0xDB`; special metadata indices range from 1 through 341,
including `0xDB`. The caller supplies the needed readable object references.
The other extended cases leave request halfwords at +22 and +24 uninitialized.
Callback-specific effects and enforcement of these domains by callers remain
premises.

The USA scene renderer at `0809A48C` uses the
`bounded-buffer-conditional-thunks-root-return-scratch-v1` owner profile.
It renders two 16-byte sprite slots, then conditionally visits a list with
an eight-byte local callback descriptor. The verifier checks the four frame
records, the installer and copied IWRAM routines, the activation and expiry
paths, the list iterator and its adapter. An empty list leaves the descriptor
address in discarded R2 until the restored root returns. Active slots require
live sprites and frame indices zero through three. The copied code must remain
installed, and external objects must remain separate from the private frames.
Set `FFTA_SCENE_SPRITE_ROOT` to the game tree for the original-code regressions
in `tests/test_scene_sprite_visitor.py`.

The USA combat action dispatcher selects `08132208` from row 26 of its
12-byte records. Under `bounded-buffer-discarded-return-scratch-v1`, the
coordinate query at `08098E7C` initializes two caller bytes on success.
Its actor-flag failure can leave the address of a released local in R2.
The native proof follows R2 and R3 through the action and original dispatcher
until both are overwritten. It verifies the collector's 13-pointer local
array under the scene contract of at most 13 live list nodes. Actor, scene
and tile data must be initialized, valid for the original accesses, and
separate from active frames. Set `FFTA_ACTION_COORDINATE_ROOT` to the game
tree to run `tests/test_action_coordinate_query.py` against the original ROM
and both coordinate-query callers' match reports.

The USA menu initializer at `0804C8C4` uses the slot-zero routine copied into
IWRAM at boot to clear its 916-byte ring. The
`addressed-native-menu-ring-initializer-v1` selector checks the original
allocation, call through R2, two BIOS halfword fills and three typed handlers
installed in a five-slot runner. The ring holds 32 request records of 28 bytes.
The contract requires the original installed code, a successful aligned
allocation, separate live buffers and private stack, ordinary BIOS behavior,
and exclusive ownership during initialization. Set `FFTA_MENU_RING_ROOT` to
the game tree to run the original boot, dispatch and cleanup tests in
`tests/test_menu_ring_initializer.py`.

### Sprite nodes, actor shadows, and item lists

The sprite node at `080216F8` calls the renderer that builds an OAM affine
matrix. The verifier follows the BIOS write into the renderer's frame and
checks the scratch register through the outer return. The actor visitor at
`08097F04` uses the scene's occupant search and the installed shadow update.
Run their original-ROM tests with `FFTA_SPRITE_NODE_ROOT` and
`FFTA_ACTOR_SHADOW_ROOT` set to the game tree.

The shop routine at `0806ED30` builds a six-byte category list. Its test
checks all 256 selectors against the regular, supplemental and fallback
tables. The inventory routine at `0808CBDC` filters 375 item IDs across
six tabs. The largest tab admits 252 rows. The
`conditional-inventory-item-list-v1` selector verifies that both local
arrays and the destination pane can hold the result. Set
`FFTA_SHOP_CATEGORY_ROOT` and `FFTA_ITEM_LIST_ROOT` to the game tree to
run the corresponding tests.
