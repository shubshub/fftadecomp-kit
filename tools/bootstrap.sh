#!/bin/sh
# bootstrap.sh - install the toolchain (Linux / WSL), without root if needed.
#
#   bash tools/bootstrap.sh
#
# The ROM analysis (tools/analyze.py, split.py, rebuild.py) needs nothing but
# Python 3 + capstone.  Matching C (tools/match.py) needs the compiler that
# built the ROM: agbcc, gcc 2.9-arm-000512 for Thumb/elf.

set -eu

echo "== python side (needed for everything) =="
python3 -m pip install --user capstone || \
    sudo apt-get update && sudo apt-get install -y python3-pip && \
    python3 -m pip install --user capstone

echo
echo "== ARM binutils =="
if command -v arm-none-eabi-as >/dev/null 2>&1; then
    echo "already installed"
elif sudo -n true 2>/dev/null; then
    sudo apt-get install -y gcc-arm-none-eabi binutils-arm-none-eabi
else
    echo "no sudo: unpacking into ~/armtc instead"
    mkdir -p ~/armtc/debs ~/armtc/root
    cd ~/armtc/debs
    apt-get download gcc-arm-none-eabi binutils-arm-none-eabi
    for f in *.deb; do dpkg-deb -x "$f" ~/armtc/root; done
    export PATH=$HOME/armtc/root/usr/bin:$PATH
fi

echo
echo "== agbcc (gcc 2.9-arm-000512, Thumb/elf) =="
if [ -x "$HOME/agbcc/gcc/agbcc" ]; then
    echo "already built at ~/agbcc/gcc/agbcc"
else
    [ -d "$HOME/agbcc" ] || git clone --depth 1 https://github.com/pret/agbcc.git "$HOME/agbcc"
    cd "$HOME/agbcc"
    # -j1 on purpose: with -j the RTL generators race and the build dies on
    # a missing genrtl.h
    make -C gcc normal -j1
    ./gcc/agbcc 2>&1 | head -2 || true
fi

echo
echo "== optional =="
if ! command -v cargo >/dev/null 2>&1; then
    echo "objdiff (progress tracking) needs rustup:"
    echo "  curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y"
fi
echo "armips has no distro package - grab a release from devkitPro/armips"
echo "and drop the binary in tools/bin/."

cat <<'EOF'

--------------------------------------------------------------------------
next:

    export PATH=$HOME/armtc/root/usr/bin:$PATH     # if you unpacked binutils
    python tools/match.py 0x08017514               # must print MATCH
    python tools/rebuild.py                        # split still byte-exact

EOF