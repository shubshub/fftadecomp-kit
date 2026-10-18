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
python tools/reserve.py list                    # read the board first
python tools/reserve.py check 0x08011040        # then check the address
python tools/reserve.py claim 0x08011040 --who <you> --note "what you are doing"
```

**Never reserve an address already reserved, matched, or in review.** `check`
and `claim` check the decomp repository's default branch and open pull requests
as well as the ledger. The broker repeats these checks before accepting a
claim. Coordinate with an existing PR's author rather than duplicating work.

| exit | state |
|---|---|
| 0 | `FREE` from `check`, or confirmed acceptance from a request command |
| 1 | `TAKEN` or rejected request |
| 2 | operational error; no permission to start work |
| 3 | `SKIP` — recorded unmatchable |
| 4 | `MATCHED` — source already on the decomp default branch |
| 5 | `IN PR` — address already covered by an open decomp PR |
| 6 | `UNCONFIRMED` — submission or acknowledgement is uncertain |

**The tool attempts to pull this repository before every command.** If it
cannot update (dirty checkout, offline), it says so and continues — resolve
the warning before trusting the local rules. `--no-pull` skips the update.
Explicitly pull and restart clients when the reservation protocol changes;
updating files does not replace code already loaded by an old process.

Claims are JSON request comments on the single ledger issue. The trusted
workflow, not the contributor, edits its table. **Wait for `ACCEPTED` and exit
0 before starting work.** A posted request, a free `check`, or `UNCONFIRMED`
(exit 6) is not a lease. The workflow must be deployed on the default branch
first. Multiple addresses may share this issue; claim each separately and
wait for each acceptance. Never create a separate reservation issue.

If `claim` refuses because the address is taken, matched, or in review,
**pick a different one.** Do not start work on a function somebody else has
reserved, and do not work around a refusal.

### 2. Release it the moment you stop — especially if you cannot match it

```sh
python tools/reserve.py ping    0x08011040 --who <you>
python tools/reserve.py release 0x08011040 --who <you> --reason "moved to src/"
python tools/reserve.py release 0x08011040 --who <you> --unmatchable --reason "no flags reproduce this" --tried="-O1..-O3"
```

A reservation is a **lease, not a land grab**. Anything quiet for 3 days is
auto-released by the `reservations` workflow, but you should not wait for that.
When you conclude a function cannot be matched, request release with
`--unmatchable`: the comment preserves the reason and flags for maintainer
review. It does not modify `known-unmatchable.json` automatically.

Ownership is authenticated by numeric GitHub account ID and original claim
request ID. A `--who` label alone cannot authorize a release. Give parallel
agents distinct labels; `--claim-id <id>` pins a ping or release to a specific
claim generation. Legacy rows remain reserved but cannot be adopted by label;
they need normal expiry or maintainer reconciliation. After an unconfirmed
request, inspect the ledger before retrying. Do not work around the result.

Only the serialized broker writes the ledger. Retire legacy direct-writing
clients and pause all writers for manual maintenance. Deployment, bounded
receipt retention, capacity limits, and exit codes are detailed in `README.md`.

### 3. Rebase before you open a PR

```sh
git -C ../fftadecomp fetch origin
git -C ../fftadecomp rebase origin/main      # not merge
git -C ../fftadecomp push --force-with-lease
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
  relocations remain, and all reachable paths stay within the supported leaf CFG
- **plausibility** — `tools/plausible.py` rejects source that only exists to
  make bytes match: inline asm, optimisation pragmas, dead code, `volatile`,
  empty/placeholder bodies, steering padding, and comments that admit the code
  steers the compiler

```sh
python tools/match.py --root ../fftadecomp 0x08011040      # exit 0 = MATCH
python tools/status.py --write --verify                    # recompiles everything
```

Byte-identical output from implausible source is **IMPLAUSIBLE**, not a match.
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
- **The ROM header is damaged** (logo scrambled, checksum 0x85 vs stored 0x89)
  and the payload beyond `0x08150000` is packed assets, not code. The code
  region is `0x08000000`-`0x08150000`.
- **Where the numbers come from:** `status.py` counts functions and bytes over
  the functions in the code region from `config/functions.json`, and a function
  counts only if its report has current verification metadata and a matching
  source/header fingerprint. Use `--verify` for fresh ROM comparisons; failures
  exit nonzero. The index contains provisional, possibly overlapping or truncated
  spans, not a proof of exhaustive coverage. `docs/status.md` must match the
  README block or CI fails.

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
