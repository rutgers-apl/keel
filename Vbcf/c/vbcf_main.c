/*
 * Userspace driver for the printed checker (vbcf.c).
 * usage: vbcf_c <file.bcf> [-g <arena> <goal>] [failing-call-index]*
 * With -g, the verifier's goal is node <goal> of the word file <arena>;
 * without, the arena is NULL.
 * Prints "<result> live=<blocks still allocated>", like `vbcf run`.
 */
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

#include "vbcf.c"

static u32 *read_file(const char *path, long *size)
{
	FILE *f = fopen(path, "rb");
	u32 *words;

	if (!f)
		return NULL;
	fseek(f, 0, SEEK_END);
	*size = ftell(f);
	fseek(f, 0, SEEK_SET);
	words = malloc((size_t)*size + 4);
	if (!words || fread(words, 1, (size_t)*size, f) != (size_t)*size)
		return NULL;
	fclose(f);
	return words;
}

int main(int argc, char **argv)
{
	long size, asize;
	u32 *words, *arena = NULL;
	u32 goal = 0;
	u32 r;
	int i = 2;

	if (argc < 2)
		return 2;
	if (argc >= 5 && strcmp(argv[2], "-g") == 0) {
		arena = read_file(argv[3], &asize);
		if (!arena)
			return 2;
		goal = (u32)strtoul(argv[4], NULL, 10);
		i = 5;
	}
	for (; i < argc && nfails < 64; i++)
		fails[nfails++] = strtoul(argv[i], NULL, 10);
	words = read_file(argv[1], &size);
	if (!words)
		return 2;
	r = vbcf_check_proof(arena, goal, (bpfptr_t){ words }, (u32)size);
	printf("%u live=%ld\n", r, embc_live_blocks);
	free(words);
	free(arena);
	return 0;
}
