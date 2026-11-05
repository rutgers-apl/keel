#!/bin/sh
# Compare the C checker with the Lean checker, step by step, on every proof
# in a directory.  Run from the repository root after Vbcf/c/build.sh.
#
#   sh Vbcf/c/corpus.sh <proof-dir> [-a] [max-bytes]
#
# -a fills in steps the C checker gets wrong from the Lean trace, so every
# rule is exercised even while some are unfinished.  Prints per-rule totals
# (rule code, steps matching Lean, steps not matching) and a verdict summary.
set -eu
dir=$1
assist=${2:-}
maxb=${3:-999999999}
out=$(mktemp -d)
export assist out
find "$dir" -name '*.bcf' -size -"${maxb}"c | sort > "$out/files"
# TRACES=<dir> uses cached traces (<name>.trace.gz) made by an earlier
# `vbcf trace`, instead of re-running the Lean checker.
traces=${TRACES:-}
export traces
xargs -P "${JOBS:-8}" -n 1 sh Vbcf/c/one.sh < "$out/files"
echo "== per rule: code ok bad"
cat "$out"/*.res | awk '$1=="R" {ok[$2]+=$3; bad[$2]+=$4} END {for (r in ok) print r, ok[r], bad[r]}' | sort
echo "== verdicts"
cat "$out"/*.res | awk '$1=="RESULT" {v[$NF]++} END {for (k in v) print v[k], k}' | sort -rn
echo "== files with bad steps: $(cat "$out"/*.res | awk '$1=="RESULT" && $4!="bad=0"' | wc -l | tr -d ' ') of $(wc -l < "$out/files" | tr -d ' ')"
echo "results in $out"
