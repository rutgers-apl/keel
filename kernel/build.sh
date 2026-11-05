#!/bin/sh
# Build an x86 kernel whose BPF verifier uses the verified checker.
# usage: build.sh <bpf-next checkout at 317a5df78f24> <BCF repo> <work dir>
# Leaves <work>/bzImage and <work>/bpftool/bpftool.
# Set CHECKER=bcf to build the same kernel with BCF's checker instead.
set -eu
src=$1; bcf=$2; w=$3
here=$(cd "$(dirname "$0")" && pwd)
j=${JOBS:-$(nproc)}
mkdir -p "$w/bpftool"
cp -a "$src" "$w/linux"
cd "$w/linux"

# BCF's patch sets 1-5, then the switch between the two checkers.
for p in "$bcf"/patches-kernel/set[1-5]:*/*.patch; do
  case $p in */0000-cover-letter.patch) continue;; esac
  patch -p1 -s --no-backup-if-mismatch < "$p"
done
patch -p1 -s < "$here/bpf-config-vbcf.patch"
cp "$here/../Vbcf/c/vbcf.c" "$here/../Vbcf/c/bcf_check_proof.h" kernel/bpf/

b=$w/build
mkdir -p "$b"
cp "$bcf/scripts/kernel-config" "$b/.config"
if [ "${CHECKER:-keel}" = bcf ]; then f=-d; else f=-e; fi
./scripts/config --file "$b/.config" $f BPF_VBCF
make O="$b" olddefconfig
make O="$b" -j"$j" bzImage
cp "$b/arch/x86/boot/bzImage" "$w/bzImage"
make -C tools/bpf/bpftool -j"$j" feature-llvm=0 feature-libbfd=0 OUTPUT="$w/bpftool/"
