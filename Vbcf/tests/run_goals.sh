#!/bin/sh
# Goal-comparison tests (see goals.py) for every proof in a directory.  Run
# from the repository root after Vbcf/c/build.sh.  With INTERP=1 every case
# also runs in the EmbC interpreter, which must agree with the C.
#
#   sh Vbcf/tests/run_goals.sh <proof-dir> [seed] [max-bytes]
set -eu
dir=$1
seed=${2:-1}
maxb=${3:-999999999}
out=$(mktemp -d)
find "$dir" -name '*.bcf' -size -"${maxb}"c | sort > "$out/files"
xargs python3 Vbcf/tests/goals.py "$out" "$seed" < "$out/files" > "$out/cases"
total=0
bad=0
: > "$out/base"
while read -r proof arena goal expect; do
	base=$(grep -F "$proof " "$out/base" | head -1 | cut -d' ' -f2- || true)
	if [ -z "$base" ]; then
		base=$(Vbcf/c/vbcf_c "$proof")
		echo "$proof $base" >> "$out/base"
	fi
	r=$(Vbcf/c/vbcf_c "$proof" -g "$arena" "$goal")
	total=$((total + 1))
	case "$expect" in
	same) [ "$r" = "$base" ] || { bad=$((bad + 1)); echo "FAIL $arena: got '$r', NULL arena gives '$base'"; } ;;
	reject) case "$r" in "0 "*) bad=$((bad + 1)); echo "FAIL $arena: accepted" ;; esac
		case "$r" in *" live=0") ;; *) bad=$((bad + 1)); echo "FAIL $arena: leak '$r'" ;; esac ;;
	esac
	if [ "${INTERP:-0}" = 1 ]; then
		l=$(.lake/build/bin/vbcf run "$proof" -g "$arena" "$goal")
		[ "$l" = "$r" ] || { bad=$((bad + 1)); echo "MISMATCH $arena: C '$r' interpreter '$l'"; }
	fi
done < "$out/cases"
echo "== by kind"
awk '{n=split($2,a,"."); k=a[n-1]; c[k]++} END {for (k in c) print k, c[k]}' "$out/cases" | sort
echo "cases=$total failures=$bad (files in $out)"
[ "$bad" = 0 ]
