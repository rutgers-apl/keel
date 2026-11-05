#!/bin/sh
# Print the checker as C and build the userspace test programs.
# Run from the repository root.  SAN=1 builds with sanitizers.
set -eu
dir=Vbcf/c
lake build vbcf >/dev/null
.lake/build/bin/vbcf print > "$dir/vbcf.c"
flags="-std=gnu11 -O2 -g -Wall -Wextra -Wconversion -Werror -Wno-unused-function -Wno-unused-parameter -IEmbC/c"
if [ "${SAN:-0}" = 1 ]; then
	flags="$flags -fsanitize=address,undefined -fno-sanitize-recover=all"
fi
${CC:-cc} $flags -o "$dir/vbcf_c" "$dir/vbcf_main.c"
${CC:-cc} $flags -o "$dir/trace_test" "$dir/trace_test.c"
