#!/bin/sh
# Compare the C checker with the Lean checker on one proof (used by corpus.sh).
# Environment: out (result dir), assist ("-a" or empty), traces (cache dir or empty).
f=$1
n=$(basename "$f" .bcf)
if [ -n "${traces:-}" ] && [ -f "$traces/$n.trace.gz" ]; then
	gzip -dc "$traces/$n.trace.gz" | Vbcf/c/trace_test "$f" $assist > "$out/$n.res" 2> "$out/$n.err" || true
else
	.lake/build/bin/vbcf trace "$f" | Vbcf/c/trace_test "$f" $assist > "$out/$n.res" 2> "$out/$n.err" || true
fi
