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
python tools/reserve.py list                    # 1. read the board first
python tools/reserve.py check 0x08011040        # 2. is this one free?
python tools/reserve.py claim 0x08011040 --who <you> --note "what you are doing"
```

**Never reserve an address that is already reserved, already matched, or
already in review.** Read the ledger before you claim, let `check` tell you the
state of your specific address, and take a free one. `check` reports four
states:

| exit | state |
|---|---|
| 0 | `FREE` — yours to claim |
| 1 | `TAKEN` — another agent holds it in the ledger |
| 4 | `MATCHED` — `src/<addr>.c` is already on the decomp repo's default branch |
| 5 | `IN PR` — an open PR in the decomp repo already matches it |
| 3 | `SKIP` — recorded unmatchable |

`claim` refuses for all of those, so a duplicate cannot happen even if you
skip the check: it re-reads the ledger after writing (so two agents claiming at
the same instant cannot both win), refuses an address already in `src/`, and
refuses one an open PR already covers. Coordinate with whoever opened that PR
rather than duplicating work that is in review.

**The tool pulls this repository before every command**, so you always decide
against the current ledger and the current `known-unmatchable.json`. If it
cannot update (dirty checkout, offline), it says so and continues — check the
message, and if it warned, `git -C ../fftadecomp-kit pull` yourself before
trusting the result. `--no-pull` skips it.

If `claim` refuses, **the address belongs to another agent — pick a different
one.** Do not start work on a function somebody else has reserved, and do not
work around a refusal.

### 2. Release it the moment you stop — especially if you cannot match it

```sh
python tools/reserve.py ping    0x08011040          # still on it; bumps the lease
python tools/reserve.py release 0x08011040 --reason "moved to src/"
python tools/reserve.py release 0x08011040 --unmatchable --reason "no flags reproduce this" --tried "-O1..-O3"
```

A reservation is a **lease, not a land grab**. Anything quiet for 3 days is
auto-released by the `reservations` workflow, but you should not wait for that.
When you conclude a function cannot be matched, release it with
`--unmatchable`: that records the address, the reason and the flags you tried
in `known-unmatchable.json`, so the next agent skips it instead of repeating
your dead end.

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
It rejects veneers, cross-mode and indirect calls, data relocations, local
helpers, self/intra-function calls, tail calls and unsupported stack operations.
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
- **Linked reports:** direct-call verification binds the exact
  `config/functions.json` mapping as well as source and headers. Mapping changes
  invalidate linked reports; the existing leaf-v2 reports are unaffected.

## Tools

| command | what it does |
|---|---|
| `tools/reserve.py {claim,check,list,ping,release,sweep}` | the address ledger |
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
