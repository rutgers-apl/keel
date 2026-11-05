#!/bin/sh
# Check that the printed C and the EmbC interpreter agree: same result, and
# every block freed, on each proof in a directory that is smaller than
# <max-bytes>.  Each proof is also run with one environment event failing
# (an allocation, the copy from the caller, or a pending signal), for the
# first <nfail> calls after the copy.  Run from the repository root after
# Vbcf/c/build.sh.
#
#   sh Vbcf/c/interp_test.sh <proof-dir> <max-bytes> [nfail]
set -eu
dir=$1
maxb=$2
nfail=${3:-0}
total=0
bad=0
stuck=0
for f in $(find "$dir" -name '*.bcf' -size -"${maxb}"c | sort); do
	base=2
	set -- "" 0 1
	j=0
	while [ "$j" -lt "$nfail" ]; do
		set -- "$@" $((base + j))
		j=$((j + 1))
	done
	for k in "$@"; do
		total=$((total + 1))
		c=$(Vbcf/c/vbcf_c "$f" $k)
		l=$(.lake/build/bin/vbcf run "$f" $k)
		case "$l" in stuck*) stuck=$((stuck + 1));; esac
		if [ "$c" != "$l" ]; then
			bad=$((bad + 1))
			echo "MISMATCH $f fail=[$k]: C '$c' Lean '$l'"
		fi
	done
done
echo "runs=$total mismatches=$bad stuck=$stuck"
[ "$bad" = 0 ] && [ "$stuck" = 0 ]
