/*
 * Userspace stand-ins for the kernel interfaces EmbC programs call.
 * For testing printed code outside the kernel only; not part of any proof.
 *
 * Calls whose outcome the environment decides (allocations, the copy from
 * the caller, signal_pending) are numbered from 0 in the order they happen.
 * Call number k fails (or reports a signal) when embc_alloc_fails(k) says
 * so, which lets a test replay the same schedule it gave the Lean
 * interpreter's oracle.
 */
#ifndef EMBC_USER_H
#define EMBC_USER_H

#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

typedef unsigned int u32;
typedef unsigned long long u64;

_Static_assert(sizeof(u32) == 4, "u32 must be 32 bits");
_Static_assert(sizeof(u64) == 8, "u64 must be 64 bits");
_Static_assert(sizeof(size_t) == 8, "EmbC passes u64 counts as size_t");

#define GFP_KERNEL_ACCOUNT 0

extern int embc_alloc_fails(unsigned long k);
extern unsigned long embc_alloc_count;
extern long embc_live_blocks;

static inline size_t array_size(size_t a, size_t b)
{
	size_t r;

	if (__builtin_mul_overflow(a, b, &r))
		return SIZE_MAX;
	return r;
}

static inline void *kvcalloc(size_t n, size_t size, int flags)
{
	void *p;

	(void)flags;
	if (embc_alloc_fails(embc_alloc_count++))
		return NULL;
	p = calloc(n, size);
	if (p)
		embc_live_blocks++;
	return p;
}

static inline void *kzalloc(size_t size, int flags)
{
	return kvcalloc(1, size, flags);
}

static inline void *kvrealloc(void *old, size_t size, int flags)
{
	void *p;

	(void)flags;
	if (embc_alloc_fails(embc_alloc_count++))
		return NULL;
	p = realloc(old, size);
	if (p && !old)
		embc_live_blocks++;
	return p;
}

static inline void kvfree(void *p)
{
	if (p)
		embc_live_blocks--;
	free(p);
}

/* The caller's memory is independent of the fault-injection call counter. */
typedef struct { const void *ptr; } bpfptr_t;

static inline int copy_from_bpfptr(void *dst, bpfptr_t src, size_t size)
{
	if (embc_alloc_fails(embc_alloc_count++))
		return -14;
	memcpy(dst, src.ptr, size);
	return 0;
}

#define current 0

static inline int signal_pending(int task)
{
	(void)task;
	return embc_alloc_fails(embc_alloc_count++);
}

static inline int cond_resched(void)
{
	return 0;
}

#endif
