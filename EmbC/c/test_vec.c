/* Test harness for the printed stage-1 example (vec_example.c). */
#include <stdio.h>
#include "embc_user.h"

unsigned long embc_alloc_count;
long embc_live_blocks;

static unsigned long fails[64];
static int nfails;

int embc_alloc_fails(unsigned long k)
{
	for (int i = 0; i < nfails; i++)
		if (fails[i] == k)
			return 1;
	return 0;
}

#include "vec_example.c"

int main(int argc, char **argv)
{
	u32 n, h;

	if (argc < 2)
		return 2;
	n = (u32)strtoul(argv[1], NULL, 10);
	for (int i = 2; i < argc && nfails < 64; i++)
		fails[nfails++] = strtoul(argv[i], NULL, 10);
	h = test_driver(n);
	printf("%u live=%ld\n", h, embc_live_blocks);
	return 0;
}
