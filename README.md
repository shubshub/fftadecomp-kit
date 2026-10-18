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
decided differently. Exit status is 0 only on an exact match.

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