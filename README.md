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
| `tools/reserve.py` | claims a function address in this repo's issues, so parallel agents do not collide |
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
python tools/reserve.py check 0x08011040          # 0 free, 1 taken, 3 unmatchable
python tools/reserve.py claim 0x08011040 --who me --note "four strh pairs"
python tools/reserve.py list                      # who holds what
python tools/reserve.py ping 0x08011040           # still on it, bumps the lease
python tools/reserve.py release 0x08011040 --reason "done, moved to src/"
python tools/reserve.py sweep --days 3            # release anything quiet
```

### The rules

1. **Claim before you touch a function.** `claim` refuses an address somebody
   else holds — if it refuses you, pick another address. Do not work on a
   function another agent has reserved.
2. **A reservation is a lease, not a land grab.** Ping it while you work.
   Release it as soon as you stop, including when you conclude the function
   **cannot** be matched — that is exactly when somebody else should be allowed
   to try. `sweep` runs every 6 hours via the `reservations` workflow and removes
   rows quiet for 3 days, so a stalled agent cannot hold an address.
3. **Release unmatchable addresses, don't hoard them.** `release
   --unmatchable --reason "..." --tried "<flags>"` releases the reservation *and*
   records the address in `known-unmatchable.json`, with the reason and the
   flags already tried. Later agents get told to skip it instead of repeating
   the same dead end.

`claim` fills in the function's name and size from the decomp repo's analysis
(`config/functions.json`), so the ledger records its size. Commands pull the
kit first; investigate update warnings rather than trusting a stale client.
`--no-pull` skips this update when the checkout has already been synchronized.
The current table-writing commands require permission to edit the ledger issue;
an update failure does not create a reservation.

Rebase contribution branches onto current `origin/main` before opening a PR;
do not merge main into the contribution branch. See `AGENTS.md` for the rules.

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
termination of arbitrary loops. Calls, interrupts, local stack allocation and
untracked transfers remain unsupported and fail closed.

Reports carry a verification schema and a SHA-256 fingerprint of the source
and headers. `status.py` rejects legacy or stale reports; regenerate them with
`match.py`. Shared preprocessing inputs must live under `include/` or be `.h`
files under `src/`; dependencies outside the fingerprinted set are rejected.
`status.py --verify` recompiles against the local ROM and exits nonzero if any
function fails. Offline report checks are cached evidence, not fresh ROM checks.
The existing function index is provisional and includes truncated or overlapping
spans, so its percentages do not establish whole-function or whole-ROM completion.
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
