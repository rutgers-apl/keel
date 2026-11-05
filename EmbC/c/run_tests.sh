#!/bin/sh
# Print the stage-1 example as C, compile it, and check that the compiled
# code and the Lean interpreter agree on a set of runs, including runs with
# injected allocation failures.  Run from the repository root.
set -eu
dir=EmbC/c
exe=.lake/build/bin/embc_example
lake build embc_example >/dev/null
"$exe" print > "$dir/vec_example.c"
${CC:-cc} -std=gnu11 -O2 -g -Wall -Wextra -Wconversion -Werror \
	-fsanitize=address,undefined -fno-sanitize-recover=all \
	-o "$dir/test_vec" "$dir/test_vec.c"
fail=0
total=0
while read -r args; do
	total=$((total + 1))
	c=$("$dir/test_vec" $args)
	l=$("$exe" run $args)
	if [ "$c" != "$l" ]; then
		echo "MISMATCH on '$args': C says '$c', Lean says '$l'"
		fail=1
	fi
done <<CASES
0
1
2
3
8
9
40
100
5 0
5 1
5 2
5 1 2
20 3
20 2 4
40 1 3 5
100 4 6
100 5 6 7 8
CASES
if [ "$fail" = 0 ]; then
	echo "ok: C and the Lean interpreter agree on $total runs"
fi
exit "$fail"
