# AGENTS.md

Instructions for agents working on the FFTA (AFXE) decompilation.

**This repository is the toolkit.** The decompilation itself lives in
[fftadecomp](https://github.com/shubshub/fftadecomp) — by default a sibling
checkout at `../fftadecomp`, or wherever `$FFTA_ROOT` points. Commands below
assume you are in the kit; pass `--root ../fftadecomp` (or set `FFTA_ROOT`)
when a tool needs the decomp repo.

---

## The rules, in order of importance

### 1. Check the ledger, then claim the address — before you touch a function

Work is parallel, and the ledger is **one issue in this repository** — the
"address ledger" — with a row per claimed address.

```sh
python tools/take.py list                    # read the board first
python tools/take.py check 0x08011040        # then check the address
python tools/take.py claim 0x08011040 --who <you> --note "what you are doing"
```

`take.py` is the direct-writing path and requires permission to edit the
ledger issue. Read-only contributors must use the authenticated broker client:

```sh
python tools/reserve.py list
python tools/reserve.py check 0x08011040
python tools/reserve.py claim 0x08011040 --who <you> --note "what you are doing"
```

An issue-edit permission failure is not a lease. The broker path still needs
an explicit accepted response; it cannot override a taken or rejected claim.

**Never reserve an address already reserved, matched, or in review.** `check`
and `claim` check the decomp repository's default branch and open pull requests
as well as the ledger. The broker repeats these checks before accepting a
claim. Coordinate with an existing PR's author rather than duplicating work.

Broker coordinates cover even addresses in the original 16 MiB ROM image,
`[0x08000000,0x09000000)`, not RAM aliases or mirrors. Coordinate acceptance
does not prove a function exists. Before using addresses beyond the former
`0x08150000` ceiling, deploy the parser on the trusted default branch, let old
broker jobs finish, and update/restart clients. Old parsers cannot read late
rows or retained receipts. A local update alone is not authorization to submit
late requests; follow the rollout and separate status-gate limits in README.

## Before you push

**Do not run `git push`.** Run the gate, which verifies and then pushes — and
pushes nothing if any check fails:

```sh
python ../fftadecomp-kit/tools/push.py                  # verify, then push
python ../fftadecomp-kit/tools/push.py --check-only     # verify only
```

It refuses unless all of these hold:

1. the branch contains the remote tip and has no merge commits (rebase, linear)
2. nothing ROM-derived is tracked — no `baserom.bin`, no `*.gba`, no `asm/`,
   no `files/`. The disassembly and raw runs are generated from the user's own
   ROM by `make init` and **have been purged from this repository's history** —
   do not add them back
3. every function in `src/` recompiles to the ROM bytes exactly, and the README
   progress block agrees with the result
4. no source in `src/` or `include/` is implausible (no inline asm, no steering
   pragmas, no inert control flow)
5. every function in `src/` has a report saying `MATCH - byte identical`, and no
   report says `IMPLAUSIBLE` or an unsanctioned `HAND-ASM`

For toolkit contributions, run `python tools/push.py --kit --repo .` from
this checkout, with `--remote` and `--branch` set to the intended destination.
Toolkit mode keeps history and game-data checks, and checks tracked Python
tool syntax instead of requiring a nonexistent game tree. It is restricted to
the executing toolkit checkout and cannot disable the decompilation gates.
Run relevant behavioral checks separately before publishing toolkit changes.
Toolkit publication requires a clean working tree and index. Decompilation
mode verifies an archive of the captured commit and permits unrelated working
edits. Archive failure stops publication; it never falls back to working files.
The gate checks that the branch and commit remain unchanged and pushes that
exact commit. `--working-tree --check-only` validates uncommitted game edits;
publishing with `--working-tree` requires a clean checkout too.
An intentional history rewrite uses `--force`, which pins the destination tip
before verification and refuses to overwrite a concurrent remote change.

The following exit codes apply to `reserve.py`:

| exit | state |
|---|---|
| 0 | `FREE` from `check`, or confirmed acceptance from a request command |
| 1 | `TAKEN` or rejected request |
| 2 | operational error; no permission to start work |
| 3 | `SKIP` — recorded unmatchable |
| 4 | `MATCHED` — source already on the decomp default branch |
| 5 | `IN PR` — address already covered by an open decomp PR |
| 6 | `UNCONFIRMED` — submission or acknowledgement is uncertain |

**`reserve.py` attempts to pull this repository before every command.** If it
cannot update (dirty checkout, offline), it says so and continues — resolve
the warning before trusting the local rules. `--no-pull` skips the update.
Explicitly pull and restart clients when the reservation protocol changes;
updating files does not replace code already loaded by an old process.

Broker claims are JSON request comments on the single ledger issue. The trusted
workflow, not the contributor, edits its table. **Wait for `ACCEPTED` and exit
0 before starting work.** A posted request, a free `check`, or `UNCONFIRMED`
(exit 6) is not a lease. The workflow must be deployed on the default branch
first. Multiple addresses may share this issue; claim each separately and
wait for each acceptance. Never create a separate reservation issue.

If `claim` refuses because the address is taken, matched, or in review,
**pick a different one.** Do not start work on a function somebody else has
reserved, and do not work around a refusal.

### 2. Release it the moment you stop — especially if you cannot match it

Use the same reservation mechanism that accepted the claim. For direct
`take.py` reservations, the operator needs issue-edit permission:

```sh
python tools/take.py ping    0x08011040
python tools/take.py release 0x08011040 --reason "moved to src/"
```

For authenticated broker reservations:

```sh
python tools/reserve.py ping    0x08011040 --who <you>
python tools/reserve.py release 0x08011040 --who <you> --reason "moved to src/"
python tools/reserve.py release 0x08011040 --who <you> --unmatchable --reason "no flags reproduce this" --tried="-O1..-O3"
```

A reservation is a **lease, not a land grab**. Anything quiet for 3 days is
auto-released by the `reservations` workflow, but you should not wait for that.
When a broker-reserved function cannot be matched, request release with
`--unmatchable`: the comment preserves the reason and flags for maintainer
review. It does not modify `known-unmatchable.json` automatically.

Broker ownership is authenticated by numeric GitHub account ID and original
claim request ID. A `--who` label alone cannot authorize a release. Give parallel
agents distinct labels; `--claim-id <id>` pins a ping or release to a specific
claim generation. Legacy rows remain reserved but cannot be adopted by label;
they need normal expiry or maintainer reconciliation. After an unconfirmed
request, inspect the ledger before retrying. Do not work around the result.

Broker requests are written only by the serialized workflow. Direct writes,
including `take.py` maintenance, must not overlap broker activity: issue edits
are not compare-and-swap operations. Direct rows have no authenticated broker
owner and cannot be adopted by label. Deployment, bounded receipt retention,
capacity limits, and exit codes are detailed in `README.md`.

### 3. Rebase before you open a PR

```sh
git -C ../fftadecomp fetch origin
git -C ../fftadecomp rebase origin/main      # not merge
python tools/push.py --repo ../fftadecomp --remote <remote> --branch <branch>
```

Matches land as small, linear commits on top of current `main`. A PR branch
that has fallen behind gets harder to review and the status block and match
gates in CI are evaluated against a stale base — the `matches` workflow fails
any PR that does not contain the current `origin/main` tip, and flags one that
merged main instead of rebasing.

### 4. Hand matching is done by sub-agents, never by the session that orchestrates

This is a hard rule, not a preference. One session claims a batch of addresses
and spawns **one sub-agent per address**; the session itself does not write the
C, does not iterate on a compiler diff, and does not hold a single function
open in its own context.

Why: matching is a long, narrow, iterative loop — compile, read a diff, adjust
one thing, compile again. Done serially it consumes the orchestrator's context
and starves everything else it is supposed to be doing (reservations, status,
commits, CI). Fan-out keeps each attempt isolated and lets several addresses be
in flight at once.

**How to run a batch**

1. `reserve.py list` / `check` / `claim` the addresses yourself — the ledger is
   the orchestrator's job, not the sub-agent's.
2. Spawn one sub-agent per address, in the background, with a prompt that
   contains:
   * the address, the full ROM disassembly of the function (dump it yourself),
   * the exact command to check the match,
   * the previous attempt's state if there is one (`Parked/<addr>/README.md`),
   * the ground rules: no git, do not edit `include/ffta.h` (declare types in
     the function's own file so parallel agents cannot collide), do not touch
     another address's files, no asm/pragmas/`volatile`/dead code,
   * "report the verdict, the C if it matched, or the exact remaining
     difference and what you ruled out".
3. Collect the reports. Commit the exact matches, park the rest with the
   diagnosis, release each reservation with its reason.
4. Only the orchestrator runs git, `status.py`, or the plausibility sweep.

Give every sub-agent a **disjoint file set** — one `src/<addr>.c` each, no
shared header edits — or they will collide.

### 5. Only byte-exact matches, from plausible source, go in `src/`

Both gates, checked by `tools/match.py`:

- **bytes** — the complete ELF function symbol, including literal pools, is
  identical to the ROM; instruction mode and alignment agree, no unresolved
  relocations remain, and all reachable caller paths satisfy the supported
  local CFG or direct-Thumb-call profile
- **plausibility** — `tools/plausible.py` rejects source that only exists to
  make bytes match: inline asm, optimisation pragmas, dead code, `volatile`,
  empty/placeholder bodies, steering padding, and comments that admit the code
  steers the compiler

```sh
python tools/match.py --root ../fftadecomp 0x08011040      # exit 0 = MATCH
python tools/status.py --write --verify                    # recompiles everything
```

Byte-identical output from implausible source is **IMPLAUSIBLE**, not a match.
Direct Thumb calls require typed linking to unique, aligned function-index
targets and exact comparison of the relocated bytes. That profile uses an ABI
call summary, not a proof that the callee returns or preserves its contract.
It rejects veneers, cross-mode and indirect calls, unmapped data relocations, local
helpers, self/intra-function calls, tail calls and unsupported stack operations.
Fixed Thumb SP allocations and direct aligned word accesses have a separate
framed profile. Bounded constant-offset stack aliases support local-array
accesses, including aligned byte and halfword operations. Register indices must
be proven constants; unknown or arithmetic-derived indices still fail. Alias
escapes, inconsistent alias joins, dynamic adjustments, out-of-frame stores and
unbalanced returns still fail; do not steer source around these checks.
Known external data symbols can be listed in `config/data_symbols.json` for
typed absolute linking. Only reachable trailing `R_ARM_ABS32` literal words
qualify; all relocated bytes are compared. Do not invent addresses to make a
match. Data reports bind both mappings, and stale mappings invalidate evidence.
See `README.md` for the precise boundary; do not work around a rejected relocation.
Do not try to reach a match by trickery — a tricked match is worth nothing and
is rejected by CI. When you cannot match honestly, park it:

```
Parked/<address>/<address>.c     the attempt
Parked/<address>/README.md       what was tried and why it failed
```

Do not commit the ROM, `baserom.bin`, or `files/` (extracted game data — it is
gitignored and generated by `make split`).

---

## Ground truth, so you do not have to rediscover it

- **Compiler:** `agbcc` — GCC **2.9-arm-000512** for Thumb/elf (12 May 2005),
  from <https://github.com/pret/agbcc>. No modern compiler reproduces this ROM.
- **Flags:** `-mthumb-interwork` is **required**; optimisation **is** enabled.
  `-O1`/`-O2`/`-O3`/`-Os` all reproduce the functions matched so far and differ
  only on inlining, so the level is still open — a function that calls a static
  helper will pin it down. `-mthumb`, `-mshort-enums`, `-frestore-iv` are not
  accepted by this compiler.
- **agbcc is a raw cc1** — it does not run the preprocessor. `cpp` first:
  `cpp -nostdinc -undef -I include src/x.c -o x.i && agbcc <flags> x.i -o x.s`,
  then `arm-none-eabi-as -mthumb-interwork` and `objcopy -O binary
  --only-section=.text`. `tools/match.py` does this for you.
- **Compiler quirks worth remembering:** it reads incoming stack arguments
  straight off `sp` with no frame pointer (286 functions in the ROM do this);
  functions return via the interworking `pop {r0}; bx r0`; an address constant
  has to live in a *variable* or every access folds into its own literal pool.
- **The baseline ROM header is valid:** its logo matches the standard GBA logo
  and its computed and stored header complement are both `0x89`. Earlier
  damaged-header warnings came from an incorrect logo constant and checksum
  formula in the analyzer, not the ROM. The main code region is
  `0x08000000`-`0x08150000`, not an exhaustive code boundary. Installer
  `0x08002768` references three executable Thumb bodies in the 176-byte ROM
  image `[0x08A38A2C,0x08A38ADC)` copied to RAM `0x03005E78`. Keep their ROM
  identities distinct from installation-time RAM aliases; later RAM identity
  needs separate evidence. Most later payload is assets, but not all of it.
- **Where the numbers come from:** `status.py` counts functions and bytes over
  the functions in the code region from `config/functions.json`, and a function
  counts only if its report has current verification metadata and a matching
  source/header fingerprint. Use `--verify` for fresh ROM comparisons; failures
  exit nonzero. `--write --verify` also regenerates and validates the reports;
  `--verify` alone and `--check` leave them untouched. The index contains
  provisional, possibly overlapping or truncated spans, not a proof of
  exhaustive coverage. `docs/status.md` must match the
  README block or CI fails.
- **Linked reports:** direct-call verification binds the exact
  `config/functions.json` mapping as well as source and headers. Mapping changes
  invalidate linked reports; the existing leaf-v2 reports are unaffected.

## Tools

| command | what it does |
|---|---|
| `tools/reserve.py {claim,check,list,ping,release}` | authenticated requests to the address ledger; `broker` is workflow-only |
| `tools/match.py <addr>` | compile, assemble, diff against the ROM; exit 0 only on a true match |
| `tools/plausible.py <files>` | the implausibility gate on its own |
| `tools/status.py [--write\|--verify\|--check]` | README progress block |
| `tools/rebuild.py <decomp-root>` | proves the split reproduces the base ROM |
| `tools/analyze.py` / `tools/split.py` | regenerate the analysis and the split |
| `tools/bootstrap.sh` | toolchain setup, no root needed |

On Windows the tools drive WSL automatically; the toolchain lives in the
`Ubuntu` distro (`~/armtc/root/usr/bin` for binutils, `~/agbcc/gcc/agbcc`).

## Finishing

Commit messages should say what matched and what it proves (address, bytes,
what the function does). Keep the ROM out of every commit. If a reservation is
still open when you stop, release it — that is the difference between a ledger
that works and one that lies.
