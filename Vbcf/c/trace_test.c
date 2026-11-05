/*
 * Step-by-step comparison of the printed C checker against the Lean checker.
 *
 *   vbcf trace f.bcf | trace_test f.bcf [-a] [-v]
 *
 * The trace lists, in the C pool's encoding, every node the Lean checker
 * creates ("N hdr word...", children as node ordinals) and the fact each
 * step concludes ("S ordinal").  This program runs the C checker one step at
 * a time and checks that it creates exactly the same nodes in the same
 * order and concludes the same fact.
 *
 * With -a (assist), a step the C checker gets wrong or cannot do is undone
 * and replaced by the Lean checker's result, so that the remaining steps can
 * still be tested.  Output: one "R <rule> <ok> <bad>" line per rule code,
 * then "RESULT <file> steps=<n> bad=<n> <verdict>".
 *
 * With -c (compact), the pool is reclaimed between steps exactly as ck_run
 * does it.  Ids then differ from the Lean checker's, so nodes are identified
 * by a structural fingerprint instead: after each compaction every Lean
 * ordinal is re-mapped to the C node with its fingerprint (or marked dead),
 * and a node the C checker creates that Lean created earlier (a dead node
 * being re-interned) is accepted as a "resurrection".  Facts are still
 * compared one for one.  The RESULT line then also reports the number of
 * compactions and resurrections.  Not combined with -a.
 *
 * Test code only; not part of any proof.
 */
#include <stdio.h>
#include <string.h>
#include "embc_user.h"

unsigned long embc_alloc_count;
long embc_live_blocks;
int embc_alloc_fails(unsigned long k) { (void)k; return 0; }

#include "vbcf.c"

static int assist, verbose, compact;
static u32 max_work;
static unsigned long ncompact, nresurrect;

/* ordinal -> pool offset (NOID: dead, compacted away) */
static u32 *ord2off;
static size_t nord, ordcap;
static u32 walked; /* pool words already matched against the trace */

/* -c: structural fingerprints.  fpo[off] for the C node at off (recomputed
 * after each compaction), fp[ord] for a Lean ordinal, and an open-addressing
 * table fingerprint -> ordinal. */
static unsigned long long *fpo, *fp;
static size_t fpocap;
static unsigned long long *tab_fp;
static u32 *tab_ord;
static size_t tabcap, tabcnt;

static unsigned long long fp_mix(unsigned long long h, unsigned long long v)
{
	h ^= v + 0x9e3779b97f4a7c15ull + (h << 6) + (h >> 2);
	h *= 0xff51afd7ed558ccdull;
	return h ^ (h >> 33);
}

static int is_leaf(u32 code);

/* Fingerprint of the C node at off from its children's (already computed). */
static unsigned long long fp_of(struct ck *st, u32 off)
{
	u32 hdr = st->pool[off], vlen = (hdr >> 8) & 0xff;
	unsigned long long h = fp_mix(0x12345678abcdefull, hdr);

	for (u32 i = 0; i < vlen; i++) {
		u32 w = st->pool[off + 1 + i];

		h = fp_mix(h, is_leaf(hdr & 0xff) ? (unsigned long long)w : fpo[w]);
	}
	return h ? h : 1;
}

static void fpo_set(u32 off, unsigned long long h)
{
	if (off >= fpocap) {
		size_t nc = fpocap ? fpocap : 65536;

		while (nc <= off)
			nc *= 2;
		fpo = realloc(fpo, nc * sizeof(*fpo));
		fpocap = nc;
	}
	fpo[off] = h;
}

static void tab_put(unsigned long long h, u32 ord)
{
	size_t i;

	if ((tabcnt + 1) * 2 > tabcap) {
		size_t oc = tabcap, nc = oc ? oc * 2 : 1 << 16;
		unsigned long long *of = tab_fp;
		u32 *oo = tab_ord;

		tab_fp = calloc(nc, sizeof(*tab_fp));
		tab_ord = calloc(nc, sizeof(*tab_ord));
		tabcap = nc;
		tabcnt = 0;
		for (size_t k = 0; k < oc; k++)
			if (of[k])
				tab_put(of[k], oo[k]);
		free(of);
		free(oo);
	}
	i = (size_t)h & (tabcap - 1);
	while (tab_fp[i] && tab_fp[i] != h)
		i = (i + 1) & (tabcap - 1);
	if (!tab_fp[i])
		tabcnt++;
	tab_fp[i] = h;
	tab_ord[i] = ord;
}

/* The ordinal with fingerprint h, or (u32)-1. */
static u32 tab_get(unsigned long long h)
{
	size_t i;

	if (!tabcap)
		return (u32)-1;
	i = (size_t)h & (tabcap - 1);
	while (tab_fp[i] && tab_fp[i] != h)
		i = (i + 1) & (tabcap - 1);
	return tab_fp[i] ? tab_ord[i] : (u32)-1;
}

/* After ck_compact: recompute fpo over the new pool and re-map every ordinal. */
static void remap_after_compact(struct ck *st)
{
	u32 off = 0;

	for (size_t k = 0; k < nord; k++)
		ord2off[k] = NOID;
	while (off < st->plen) {
		unsigned long long h = fp_of(st, off);
		u32 ord = tab_get(h);

		fpo_set(off, h);
		if (ord != (u32)-1)
			ord2off[ord] = off;
		off += 1 + ((st->pool[off] >> 8) & 0xff);
	}
	walked = st->plen;
}

static char *line;
static size_t linecap;
static int have_line;

static int next_line(void)
{
	if (have_line)
		return 1;
	if (getline(&line, &linecap, stdin) <= 0)
		return 0;
	have_line = 1;
	return 1;
}

static struct ck *g_st;

static void add_ord(u32 off)
{
	if (nord == ordcap) {
		ordcap = ordcap ? ordcap * 2 : 4096;
		ord2off = realloc(ord2off, ordcap * sizeof(u32));
		if (compact)
			fp = realloc(fp, ordcap * sizeof(*fp));
	}
	if (compact) {
		unsigned long long h = fp_of(g_st, off);

		fpo_set(off, h);
		fp[nord] = h;
		tab_put(h, (u32)nord);
	}
	ord2off[nord++] = off;
}

static int is_leaf(u32 code)
{
	return code == BV_VAR || code == BOOL_VAR || code == BV_VAL || code == BOOL_VAL;
}

/* Parse "N hdr w..." into buf; returns the number of words including hdr. */
static int parse_node(const char *s, unsigned long long *buf)
{
	int n = 0;
	char *end;

	s++;
	for (;;) {
		unsigned long long v = strtoull(s, &end, 10);

		if (end == s)
			break;
		buf[n++] = v;
		s = end;
		if (n >= 300)
			break;
	}
	return n;
}

/* Does the C node at `off` equal the traced node? */
static int node_matches(struct ck *st, u32 off, unsigned long long *buf, int n)
{
	u32 hdr = st->pool[off];
	u32 vlen = (hdr >> 8) & 0xff;

	if (buf[0] != hdr || (u32)n != vlen + 1)
		return 0;
	for (u32 i = 0; i < vlen; i++) {
		u32 want;

		if (is_leaf(hdr & 0xff)) {
			want = (u32)buf[1 + i];
		} else {
			if (buf[1 + i] >= nord || ord2off[buf[1 + i]] == NOID)
				return 0;
			want = ord2off[buf[1 + i]];
		}
		if (st->pool[off + 1 + i] != want)
			return 0;
	}
	return 1;
}

/* The N lines of the current step, buffered so a step can be checked and then redone. */
static int wide_node;
static char **nbuf;
static size_t nn, nbufcap;

static void read_nodes(void)
{
	nn = 0;
	while (next_line() && line[0] == 'N') {
		if (nn == nbufcap) {
			nbufcap = nbufcap ? nbufcap * 2 : 64;
			nbuf = realloc(nbuf, nbufcap * sizeof(char *));
			memset(nbuf + nn, 0, (nbufcap - nn) * sizeof(char *));
		}
		free(nbuf[nn]);
		nbuf[nn++] = strdup(line);
		have_line = 0;
	}
}

/*
 * Handle the buffered N lines of one step.  If `check`, compare them with
 * the nodes the C checker appended (from `walked` to st->plen); on a mismatch
 * nothing is recorded.  Otherwise add them to the C pool.  Returns 1 on success.
 */
static int sync_nodes(struct ck *st, int check)
{
	unsigned long long buf[300];
	size_t nord0 = nord;
	u32 walked0 = walked;

	for (size_t k = 0; k < nn; k++) {
		int n = parse_node(nbuf[k], buf);

		if (check) {
			while (compact && walked < st->plen && !node_matches(st, walked, buf, n)) {
				/* a node Lean created earlier, compacted away and re-interned now? */
				unsigned long long h = fp_of(st, walked);
				u32 ord = tab_get(h);

				if (ord == (u32)-1 || ord2off[ord] != NOID)
					break;
				fpo_set(walked, h);
				ord2off[ord] = walked;
				nresurrect++;
				walked += 1 + ((st->pool[walked] >> 8) & 0xff);
			}
			if (walked >= st->plen || !node_matches(st, walked, buf, n)) {
				if (verbose)
					fprintf(stderr, "  node mismatch at offset %u: lean %s", walked, nbuf[k]);
				nord = nord0;
				walked = walked0;
				return 0;
			}
			add_ord(walked);
			walked += (u32)n;
		} else {
			u32 id;

			if (n - 1 > 255) {
				/* Lean built a node with more arguments than the encoding holds */
				wide_node = 1;
				return 0;
			}
			if (!ck_room(st, (u32)n)) {
				fprintf(stderr, "inject: out of memory\n");
				exit(3);
			}
			st->pool[st->plen] = (u32)buf[0];
			for (int i = 1; i < n; i++) {
				if (is_leaf((u32)buf[0] & 0xff))
					st->pool[st->plen + (u32)i] = (u32)buf[i];
				else
					st->pool[st->plen + (u32)i] = ord2off[buf[i]];
			}
			id = st->plen;
			if (ck_intern(st) != id) {
				/* e.g. a width over 255: the Lean node has no C encoding */
				if (verbose)
					fprintf(stderr, "inject: C pool refuses a Lean node: %s", nbuf[k]);
				wide_node = 2;
				return 0;
			}
			add_ord(id);
			walked = st->plen;
		}
	}
	while (check && compact && walked < st->plen) {
		unsigned long long h = fp_of(st, walked);
		u32 ord = tab_get(h);

		if (ord == (u32)-1 || ord2off[ord] != NOID)
			break;
		fpo_set(walked, h);
		ord2off[ord] = walked;
		nresurrect++;
		walked += 1 + ((st->pool[walked] >> 8) & 0xff);
	}
	if (check && walked != st->plen) {
		if (verbose)
			fprintf(stderr, "  C created %u extra words\n", st->plen - walked);
		nord = nord0;
		walked = walked0;
		return 0;
	}
	return 1;
}

/* Did the Lean checker build a node with more than 255 arguments in this step? */
static int step_has_wide(void)
{
	for (size_t k = 0; k < nn; k++) {
		int n = 0;
		char *p = nbuf[k] + 1, *end;

		for (;;) {
			(void)strtoull(p, &end, 10);
			if (end == p)
				break;
			n++;
			p = end;
		}
		if (n - 1 > 255)
			return 1;
	}
	return 0;
}

/* Undo everything the C checker appended after `plen`. */
static void rollback(struct ck *st, u32 plen)
{
	u32 off = 0;

	st->err = 0;
	st->sp = 0;
	if (st->plen == plen)
		return;
	st->plen = plen;
	memset(st->htab, 0, (size_t)st->hcap * sizeof(u32));
	st->hcnt = 0;
	while (off < plen) {
		ck_hput(st, off);
		off += 1 + ((st->pool[off] >> 8) & 0xff);
	}
}

#define NRULE 0xc1
static unsigned long rule_ok[NRULE], rule_bad[NRULE];
static unsigned rule_slot(u32 rule)
{
	unsigned cls = (rule >> 13) & 7, idx = rule & 0x1fff;

	return cls > 2 || idx >= 0x40 ? NRULE - 1 : cls * 0x40 + idx;
}
static u32 slot_rule(unsigned s)
{
	return s == NRULE - 1 ? 0xffff : ((s / 0x40) << 13) | (s % 0x40);
}

int main(int argc, char **argv)
{
	struct ck *st;
	FILE *f;
	long size;
	u32 *words, nwords, ns, off = 0;
	unsigned long steps = 0, bad = 0;
	const char *verdict = "?";

	if (argc < 2)
		return 2;
	for (int i = 2; i < argc; i++) {
		if (!strcmp(argv[i], "-a"))
			assist = 1;
		if (!strcmp(argv[i], "-v"))
			verbose = 1;
		if (!strcmp(argv[i], "-c"))
			compact = 1;
	}
	if (assist && compact) {
		fprintf(stderr, "-a and -c cannot be combined\n");
		return 2;
	}
	f = fopen(argv[1], "rb");
	if (!f)
		return 2;
	fseek(f, 0, SEEK_END);
	size = ftell(f);
	fseek(f, 0, SEEK_SET);
	words = malloc((size_t)size + 4);
	if (!words || fread(words, 1, (size_t)size, f) != (size_t)size)
		return 2;
	fclose(f);
	nwords = (u32)(size / 4);

	st = calloc(1, sizeof(*st));
	g_st = st;
	if (!next_line()) {
		printf("RESULT %s empty-trace\n", argv[1]);
		return 1;
	}
	if (line[0] == 'D') {
		/* Lean rejects before any step: C must reject too. */
		int ok = ck_init(st, nwords, 0) && ck_load(st, words, nwords) && ck_scan(st);

		printf("RESULT %s steps=0 bad=%d %s\n", argv[1], ok ? 1 : 0,
		       ok ? "C-LOADS-WHAT-LEAN-REJECTS" : "both-reject-input");
		return ok ? 1 : 0;
	}
	if (!ck_init(st, nwords, 0) || !ck_load(st, words, nwords)) {
		printf("RESULT %s steps=0 bad=1 C-REJECTS-INPUT\n", argv[1]);
		return 1;
	}
	read_nodes();
	if (!sync_nodes(st, 1)) {
		printf("RESULT %s steps=0 bad=1 CANON-MISMATCH\n", argv[1]);
		return 1;
	}
	/* remap lines */
	while (next_line() && line[0] == 'M') {
		unsigned long pos, ord;

		sscanf(line + 1, "%lu %lu", &pos, &ord);
		have_line = 0;
		if (pos >= st->nexpr || st->proof[3 + pos] != ord2off[ord] + 1) {
			printf("RESULT %s steps=0 bad=1 REMAP-MISMATCH\n", argv[1]);
			return 1;
		}
	}
	if (!next_line() || line[0] != 'C') {
		printf("RESULT %s steps=0 bad=1 bad-trace\n", argv[1]);
		return 1;
	}
	have_line = 0;
	if (!ck_scan(st)) {
		next_line();
		printf("RESULT %s steps=0 bad=%d %s\n", argv[1], line[0] == 'D' ? 0 : 1,
		       line[0] == 'D' ? "both-reject-goal" : "C-REJECTS-GOAL");
		return line[0] == 'D' ? 0 : 1;
	}
	if (next_line() && line[0] == 'D') {
		printf("RESULT %s steps=0 bad=1 C-ACCEPTS-GOAL-LEAN-REJECTS\n", argv[1]);
		return 1;
	}

	ns = words[2];
	while (off < ns) {
		u32 hdr = words[3 + st->nexpr + off];
		u32 rule = hdr & 0xffff;
		u32 before = st->plen;
		u32 w0 = st->work;
		u32 fact = ck_step(st, off);

		if (fact != NOID && w0 - st->work > max_work)
			max_work = w0 - st->work;
		unsigned long want;
		int good;

		read_nodes();
		if (!next_line())
			break;
		if (line[0] == 'X') {
			/* Lean rejects this step. */
			if (fact != NOID) {
				bad++;
				rule_bad[rule_slot(rule)]++;
				verdict = "C-ACCEPTS-STEP-LEAN-REJECTS";
			} else {
				verdict = "both-reject";
			}
			goto done;
		}
		if (line[0] != 'S' || sscanf(line + 1, "%lu", &want) != 1) {
			verdict = "bad-trace";
			goto done;
		}
		good = fact != NOID && sync_nodes(st, 1) && want < nord && ord2off[want] != NOID && ord2off[want] == fact;
		if (!good) {
			bad++;
			rule_bad[rule_slot(rule)]++;
			if (verbose)
				fprintf(stderr, "step %lu rule 0x%04x: %s\n", steps, rule,
					fact == NOID ? "C rejects" : "differs from Lean");
			if (fact == NOID && step_has_wide()) {
				verdict = "lean-needs-node-over-255-args";
				goto done;
			}
			if (!assist) {
				verdict = fact == NOID ? "C-REJECTS-STEP" : "STEP-MISMATCH";
				goto done;
			}
			/* undo the C step and take the Lean checker's result instead */
			rollback(st, before);
			walked = before;
			while (nord && ord2off[nord - 1] >= before)
				nord--;
			if (!sync_nodes(st, 0) && wide_node) {
				verdict = wide_node == 1 ? "lean-needs-node-over-255-args"
							 : "LEAN-NODE-REFUSED-BY-C-POOL";
				goto done;
			}
			fact = ord2off[want];
		} else {
			rule_ok[rule_slot(rule)]++;
		}
		have_line = 0;
		st->facts[st->flen++] = fact;
		steps++;
		off += 1 + ((hdr >> 16) & 0xff) + (hdr >> 24);
		if (compact && off < ns &&
		    (u64)st->plen > 2ull * st->lo + 2ull * st->live + (u64)st->flen + (u64)COMPACT_GAP) {
			if (!ck_compact(st)) {
				verdict = "C-COMPACT-FAILS";
				goto done;
			}
			ncompact++;
			remap_after_compact(st);
		}
	}
	if (next_line() && (line[0] == 'A' || line[0] == 'R')) {
		int c_accepts = st->flen && st->facts[st->flen - 1] == st->ff;

		if ((line[0] == 'A') != c_accepts) {
			bad++;
			verdict = "FINAL-VERDICT-DIFFERS";
		} else {
			verdict = c_accepts ? "accept" : "reject";
		}
	} else {
		verdict = "bad-trace";
	}
done:
	for (unsigned s = 0; s < NRULE; s++)
		if (rule_ok[s] || rule_bad[s])
			printf("R 0x%04x %lu %lu\n", slot_rule(s), rule_ok[s], rule_bad[s]);
	if (verbose)
		fprintf(stderr, "stats: max work in a step %u, work left %u, input %u words (%u expr), pool %u of %u words, %u nodes, hash %u slots, %u facts, stack %u\n",
			max_work, st->work, nwords, st->nexpr, st->plen, st->pcap, st->hcnt, st->hcap, st->flen, st->scap);
	if (compact)
		printf("RESULT %s steps=%lu bad=%lu %s compactions=%lu resurrections=%lu\n", argv[1], steps, bad, verdict, ncompact, nresurrect);
	else
		printf("RESULT %s steps=%lu bad=%lu %s\n", argv[1], steps, bad, verdict);
	return bad ? 1 : 0;
}
