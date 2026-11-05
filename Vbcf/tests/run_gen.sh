#!/bin/sh
# Generated test proofs for rules the corpus does not exercise.
# Each case is replayed by the Lean checker and by the C checker, and the two
# must agree step by step (same nodes, same facts, same verdict).
# Run from the repository root after Vbcf/c/build.sh.
#
#   sh Vbcf/tests/run_gen.sh
set -eu
out=$(mktemp -d)
mkdir -p "$out/cases"
for g in Vbcf/tests/*_gen*.py; do
	python3 "$g" "$out/cases" >/dev/null
done
python3 Vbcf/tests/clause_craft.py "$out/cases/clause_craft.bcf"
python3 Vbcf/tests/clause_fuzz.py clause 1 400 "$out/cases" >/dev/null
python3 Vbcf/tests/clause_fuzz.py aci 1 400 "$out/cases" >/dev/null
python3 Vbcf/tests/poly_fuzz.py "$out/poly" 400 >/dev/null
mv "$out"/poly/*.bcf "$out/cases/"
mkdir -p "$out/bb" "$out/shift"
python3 Vbcf/tests/bitblast_fuzz.py "$out/bb" 600 1 >/dev/null
mv "$out"/bb/*.bcf "$out/cases/"
python3 tests/mk_shift_tests.py "$out/shift" >/dev/null 2>&1 && mv "$out"/shift/*.bcf "$out/cases/" || true
# one instance search per rewrite rule (positives and mutated negatives)
mkdir -p "$out/rw"
lake env lean --run Vbcf/tests/rw_gen.lean "$out/rw" 3000 >/dev/null
mv "$out"/rw/*.bcf "$out/cases/"
for f in "$out"/cases/*.bcf; do
	.lake/build/bin/vbcf trace "$f" | Vbcf/c/trace_test "$f" || true
done | awk '$1 == "RESULT" {v[$NF]++; n++} END {for (k in v) print v[k], k; print n, "cases"}' | sort -rn
echo "cases in $out/cases"
