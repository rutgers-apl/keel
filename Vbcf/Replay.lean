import Vbcf.Rules.Basic

/-!
# Vbcf: loading the proof, replaying its steps, and the entry point

`ck_load` is `Bcf.decode` followed by `Bcf.canonicalize`: it walks the
expression section, validates each node, renumbers its arguments to
canonical ids, and interns it.  It then overwrites the expression in the
input with its position-to-node mapping: the header word becomes one more
than the canonical id, the other words 0.  (The raw expression is not needed
again, and this saves a table the size of the input.)

`ck_scan` validates the step section, finds the goal (`Bcf.findGoal`) and
records for each step the last step that cites it, which `ck_compact` uses
to reclaim the pool between steps (see `Vbcf/Defs.lean`, "Reclamation").
`ck_goal` compares that goal with the verifier's (see below).  `ck_step` is
one iteration of `Bcf.replay`.  `vbcf_check` is `Bcf.check` plus the goal
comparison: it returns 0 exactly when the proof is accepted.
`vbcf_check_proof` is the kernel-facing entry, with the arguments of BCF's
`bcf_check_proof` (less the logger): it copies the proof from the caller once
and checks the copy.  Between steps the loop yields the CPU and stops if a
signal is pending, as the BCF checker does.

**The verifier's goal.**  As in BCF, the verifier passes its expression arena
`goal_exprs` (BCF's `struct bcf_expr` array, read here as words) and the
position `goal` of the goal node in it; a variable is identified by its
position.  A `NULL` arena skips the comparison, as in BCF.  The proof's goal
must be the verifier's goal up to a bijective renaming of variables.

`ck_goal` needs no recursion and no allocation of its own.  It reserves
`goal + 1 + nexpr` words of scratch at the pool's tail: `mark[q]` is one more
than the pool node that arena node `q` must equal (0: none yet), and
`vmap[p]` is one more than the arena variable matched with the proof variable
at input position `p`.  Arena arguments point to earlier nodes, so one sweep
from `goal` down to 0 visits every node after all the nodes that refer to it:
it checks each marked node against its pool node and marks the arguments.
Each arena node is checked at most once, so the work is linear in `goal`
whatever the sharing.  An argument must also end before the node that uses it
starts, which keeps every read inside the arena given only that the goal node
itself lies inside it.
-/

namespace Vbcf
open EmbC

c_const% BCF_MAGIC := 0x0BCF
c_const% E_INVAL := 22
c_const% E_NOMEM := 12
c_const% E_FAULT := 14
c_const% E_AGAIN := 11
c_const% ERR_INTR := 3
c_const% MAX_PROOF_BYTES := 0x2000000

/-- Allocate the hash table and the premise buffer, set the work budget for
an input of `nwords` words and a goal at position `goal` of the verifier's
arena (an input so large that the budget would exceed `MAX_POOL` is
rejected), and make the two boolean literals. -/
def ckInit : Fn := c_fn% u32 ck_init(struct ck *st, u32 nwords, u32 goal) {
  u32 *t; u32 *q; u32 r; u64 b;
  t = kvcalloc(1024ull, sizeof(u32));
  if (t == NULL) { st->err = ERR_NOMEM; return 0; }
  st->htab = t;
  st->hcap = 1024;
  q = kvcalloc(256ull, sizeof(u32));
  if (q == NULL) { st->err = ERR_NOMEM; return 0; }
  st->prem = q;
  b = (u64)WORK_PER_WORD * ((u64)nwords + (u64)goal) + (u64)WORK_BASE;
  if (b > (u64)MAX_POOL) { st->err = ERR_LIMIT; return 0; }
  st->work = (u32)b;
  b = (u64)MEM_PER_WORD * ((u64)nwords + (u64)goal) + (u64)MEM_BASE;
  if (b > (u64)MAX_POOL) { st->err = ERR_LIMIT; return 0; }
  st->mem = (u32)b;
  r = mk0(st, HDR_TRUE);
  if (r == NOID) { return 0; }
  st->tt = r;
  r = mk0(st, HDR_FALSE);
  if (r == NOID) { return 0; }
  st->ff = r;
  return 1;
}

def ckFree : Fn := c_fn% void ck_free(struct ck *st) {
  kvfree(st->pool);
  kvfree(st->htab);
  kvfree(st->facts);
  kvfree(st->stk);
  kvfree(st->prem);
  kvfree(st->lr);
}

def ckLoad : Fn := c_fn% u32 ck_load(struct ck *st, u32 *proof, u32 nwords) {
  u32 ne; u32 ns; u32 p; u32 hdr; u32 code; u32 vlen; u32 i; u32 a; u32 id; u32 ok;
  if (nwords < 3) { return 0; }
  if (proof[0] != BCF_MAGIC) { return 0; }
  ne = proof[1];
  ns = proof[2];
  if (ne == 0 || ns < 2) { return 0; }
  if ((u64)ne + (u64)ns + 3ull != (u64)nwords) { return 0; }
  st->proof = proof;
  st->nexpr = ne;
  while (p < ne) {
    hdr = proof[3 + p];
    code = hdr & 0xff;
    vlen = (hdr >> 8) & 0xff;
    if (vlen > ne - p - 1) { return 0; }
    ok = ck_room(st, 2 + vlen);
    if (ok == 0) { return 0; }
    if (code == BV_VAR || code == BOOL_VAR) {
      if (vlen != 0) { return 0; }
      st->pool[st->plen] = hdr | (1 << 8);
      st->pool[st->plen + 1] = p;
    } else if (code == BV_VAL) {
      st->pool[st->plen] = hdr;
      i = 0;
      while (i < vlen) {
        st->pool[st->plen + 1 + i] = proof[4 + p + i];
        i = i + 1;
      }
    } else {
      st->pool[st->plen] = hdr;
      i = 0;
      while (i < vlen) {
        a = proof[4 + p + i];
        if (a >= p) { return 0; }
        if (proof[3 + a] == 0) { return 0; }
        st->pool[st->plen + 1 + i] = proof[3 + a] - 1;
        i = i + 1;
      }
    }
    id = ck_intern(st);
    if (id == NOID) { return 0; }
    proof[3 + p] = id + 1;
    i = 0;
    while (i < vlen) {
      proof[4 + p + i] = 0;
      i = i + 1;
    }
    p = p + 1 + vlen;
  }
  st->lo = st->plen;
  return 1;
}

def ckScan : Fn := c_fn% u32 ck_scan(struct ck *st) {
  u32 base; u32 ns; u32 p; u32 hdr; u32 pc; u32 ac; u32 cnt; u32 nassume; u32 bad; u32 gpos;
  u32 g; u32 *f; u32 *l; u32 k; u32 i; u32 q;
  base = 3 + st->nexpr;
  ns = st->proof[2];
  g = spend(st, ns);
  if (g == 0) { return 0; }
  while (p < ns) {
    hdr = st->proof[base + p];
    pc = (hdr >> 16) & 0xff;
    ac = hdr >> 24;
    if (pc + ac > ns - p - 1) { return 0; }
    if ((hdr & 0xffff) == 1) {
      nassume = nassume + 1;
      if (ac == 1) { gpos = st->proof[base + p + 1 + pc]; } else { bad = 1; }
    }
    cnt = cnt + 1;
    p = p + 1 + pc + ac;
  }
  if (nassume != 1 || bad != 0) { return 0; }
  g = expr_at(st, gpos);
  if (g == NOID) { return 0; }
  st->goal = g;
  if (st->mem < cnt) { st->err = ERR_LIMIT; return 0; }
  st->mem = st->mem - cnt;
  f = kvcalloc((u64)cnt, sizeof(u32));
  if (f == NULL) { st->err = ERR_NOMEM; return 0; }
  st->facts = f;
  st->fcap = cnt;
  if (st->mem < cnt) { st->err = ERR_LIMIT; return 0; }
  st->mem = st->mem - cnt;
  l = kvcalloc((u64)cnt, sizeof(u32));
  if (l == NULL) { st->err = ERR_NOMEM; return 0; }
  st->lr = l;
  g = spend(st, ns);
  if (g == 0) { return 0; }
  p = 0;
  while (p < ns) {
    hdr = st->proof[base + p];
    pc = (hdr >> 16) & 0xff;
    ac = hdr >> 24;
    if (pc + ac > ns - p - 1) { return 0; }
    if (k < cnt) {
      i = 0;
      while (i < pc) {
        q = st->proof[base + p + 1 + i];
        if (q < k) { st->lr[q] = k; }
        i = i + 1;
      }
    }
    k = k + 1;
    p = p + 1 + pc + ac;
  }
  return 1;
}

/-- Compare the proof's goal `st->goal` with node `goal` of the verifier's
arena `gx`; 1 if they are equal up to a bijective renaming of variables. -/
def ckGoal : Fn := c_fn% u32 ck_goal(struct ck *st, u32 *gx, u32 goal) {
  u32 n; u32 base; u32 sbase; u32 j; u32 q; u32 m; u32 ci; u32 ah; u32 ph; u32 code; u32 vlen;
  u32 k; u32 a; u32 pa; u32 pv; u32 ok;
  if ((u64)goal + 1ull + (u64)st->nexpr > (u64)MAX_POOL) { st->err = ERR_LIMIT; return 0; }
  n = goal + 1 + st->nexpr;
  ok = ck_room(st, n);
  if (ok == 0) { return 0; }
  ok = spend(st, n);
  if (ok == 0) { return 0; }
  base = st->plen;
  sbase = base + goal + 1;
  while (j < n) {
    st->pool[base + j] = 0;
    j = j + 1;
  }
  st->pool[base + goal] = st->goal + 1;
  q = goal + 1;
  while (q > 0) {
    q = q - 1;
    m = st->pool[base + q];
    if (m != 0) {
      ci = m - 1;
      ah = gx[q];
      ph = st->pool[ci];
      code = ph & 0xff;
      if (code == BV_VAR || code == BOOL_VAR) {
        if (ah != (ph & 0xffff00ff)) { return 0; }
        pv = st->pool[ci + 1];
        if (pv >= st->nexpr) { return 0; }
        if (st->pool[sbase + pv] != 0) { return 0; }
        st->pool[sbase + pv] = q + 1;
      } else {
        if (ah != ph) { return 0; }
        vlen = (ah >> 8) & 0xff;
        k = 0;
        if (code == BV_VAL) {
          while (k < vlen) {
            if (gx[q + 1 + k] != st->pool[ci + 1 + k]) { return 0; }
            k = k + 1;
          }
        } else {
          while (k < vlen) {
            a = gx[q + 1 + k];
            if (a >= q) { return 0; }
            if ((u64)a + 1ull + (u64)((gx[a] >> 8) & 0xff) > (u64)q) { return 0; }
            pa = st->pool[ci + 1 + k];
            m = st->pool[base + a];
            if (m == 0) { st->pool[base + a] = pa + 1; }
            else if (m != pa + 1) { return 0; }
            k = k + 1;
          }
        }
      }
    }
  }
  return 1;
}

/-- `Bcf.applyRule`: dispatch on the rule code. -/
def ckRule : Fn := c_fn% u32 ck_rule(struct ck *st, u32 rule, u32 np, u32 na) {
  u32 r;
  r = NOID;
  if (rule == 0x0001) { r = r_assume(st, np, na); }
  else if (rule == 0x0002) { r = r_evaluate(st, np, na); }
  else if (rule == 0x0003) { r = r_distinct_values(st, np, na); }
  else if (rule == 0x0004) { r = r_aci_norm(st, np, na); }
  else if (rule == 0x0005) { r = r_absorb(st, np, na); }
  else if (rule == 0x0006) { r = r_rewrite(st, np, na); }
  else if (rule == 0x0007) { r = r_refl(st, np, na); }
  else if (rule == 0x0008) { r = r_symm(st, np, na); }
  else if (rule == 0x0009) { r = r_trans(st, np, na); }
  else if (rule == 0x000a) { r = r_cong(st, np, na); }
  else if (rule == 0x000b) { r = r_true_intro(st, np, na); }
  else if (rule == 0x000c) { r = r_true_elim(st, np, na); }
  else if (rule == 0x000d) { r = r_false_intro(st, np, na); }
  else if (rule == 0x000e) { r = r_false_elim(st, np, na); }
  else if (rule == 0x2001) { r = r_resolution(st, np, na); }
  else if (rule == 0x2002) { r = r_factoring(st, np, na); }
  else if (rule == 0x2003) { r = r_reordering(st, np, na); }
  else if (rule == 0x2004) { r = r_split(st, np, na); }
  else if (rule == 0x2005) { r = r_eq_resolve(st, np, na); }
  else if (rule == 0x2006) { r = r_modus_ponens(st, np, na); }
  else if (rule == 0x2007) { r = r_not_not_elim(st, np, na); }
  else if (rule == 0x2008) { r = r_contra(st, np, na); }
  else if (rule == 0x2009) { r = r_and_elim(st, np, na); }
  else if (rule == 0x200a) { r = r_and_intro(st, np, na); }
  else if (rule == 0x200b) { r = r_not_or_elim(st, np, na); }
  else if (rule == 0x200c) { r = r_implies_elim(st, np, na); }
  else if (rule == 0x200d) { r = r_not_implies_elim(st, np, na); }
  else if (rule == 0x200e) { r = r_equiv_elim(st, np, na); }
  else if (rule == 0x200f) { r = r_not_equiv_elim(st, np, na); }
  else if (rule == 0x2010) { r = r_xor_elim(st, np, na); }
  else if (rule == 0x2011) { r = r_not_xor_elim(st, np, na); }
  else if (rule == 0x2012) { r = r_ite_elim(st, np, na); }
  else if (rule == 0x2013) { r = r_not_ite_elim(st, np, na); }
  else if (rule == 0x2014) { r = r_not_and(st, np, na); }
  else if (rule == 0x2015) { r = r_cnf_and_pos(st, np, na); }
  else if (rule == 0x2016) { r = r_cnf_and_neg(st, np, na); }
  else if (rule == 0x2017) { r = r_cnf_or_pos(st, np, na); }
  else if (rule == 0x2018) { r = r_cnf_or_neg(st, np, na); }
  else if (rule == 0x2019) { r = r_cnf_implies_pos(st, np, na); }
  else if (rule == 0x201a) { r = r_cnf_implies_neg(st, np, na); }
  else if (rule == 0x201b) { r = r_cnf_equiv_pos(st, np, na); }
  else if (rule == 0x201c) { r = r_cnf_equiv_neg(st, np, na); }
  else if (rule == 0x201d) { r = r_cnf_xor_pos(st, np, na); }
  else if (rule == 0x201e) { r = r_cnf_xor_neg(st, np, na); }
  else if (rule == 0x201f) { r = r_cnf_ite_pos(st, np, na); }
  else if (rule == 0x2020) { r = r_cnf_ite_neg(st, np, na); }
  else if (rule == 0x2021) { r = r_ite_eq(st, np, na); }
  else if (rule == 0x4001) { r = r_bitblast(st, np, na); }
  else if (rule == 0x4002) { r = r_poly_norm(st, np, na); }
  else if (rule == 0x4003) { r = r_poly_norm_eq(st, np, na); }
  return r;
}

/-- Replay the step at offset `off` of the step section: returns the id of
its conclusion, or `NOID`. -/
def ckStep : Fn := c_fn% u32 ck_step(struct ck *st, u32 off) {
  u32 base; u32 hdr; u32 pc; u32 ac; u32 i; u32 k; u32 r;
  base = 3 + st->nexpr + off;
  hdr = st->proof[base];
  pc = (hdr >> 16) & 0xff;
  ac = hdr >> 24;
  while (i < pc) {
    k = st->proof[base + 1 + i];
    if (k >= st->flen) { return NOID; }
    if (st->lr[k] < st->flen) { return NOID; }
    st->prem[i] = st->facts[k];
    i = i + 1;
  }
  st->par = st->proof +> (base + 1 + pc);
  st->sp = 0;
  r = spend(st, 1 + pc + ac);
  if (r == 0) { return NOID; }
  r = ck_rule(st, hdr & 0xffff, pc, ac);
  return r;
}

/-- Reclaim the pool between steps.  A fact `j` is still needed if a later
step cites it (`lr[j] ≥ flen`).  Mark every node reachable from a needed
fact (an explicit worklist on the scratch stack; leaves have no child ids),
slide the marked nodes of `pool[lo..plen)` down in place (children precede
their parents, so a child's new id is known when its parent is copied),
remap `facts[]` (a dead fact becomes `NOID`; `ck_step` never reads one) and
rebuild the hash table at load factor at most 1/4.  `fw[o - lo]` is 0 for a
dead node, `NOID` while marked and then the node's new id.  Work and memory
are paid from the budgets; `ck_run` calls this only when the pool has grown
by more than `lo + live + flen + COMPACT_GAP` words since the last call, so
the total cost of compaction is linear in the words ever interned. -/
def ckCompact : Fn := c_fn% u32 ck_compact(struct ck *st) {
  u32 lo; u32 plen; u32 n; u32 *fw; u32 j; u32 r; u32 o; u32 hdr; u32 code; u32 ar; u32 i; u32 c;
  u32 cur; u32 nodes; u32 ok; u32 *nt; u64 hc;
  lo = st->lo;
  plen = st->plen;
  n = plen - lo;
  ok = spend(st, n + lo + st->flen);
  if (ok == 0) { return 0; }
  if (st->mem < n) { st->err = ERR_LIMIT; return 0; }
  st->mem = st->mem - n;
  fw = kvcalloc((u64)n, sizeof(u32));
  if (fw == NULL) { st->err = ERR_NOMEM; return 0; }
  st->sp = 0;
  while (j < st->flen) {
    if (st->lr[j] >= st->flen) {
      r = st->facts[j];
      if (r >= lo && r < plen) {
        if (fw[r - lo] == 0) {
          fw[r - lo] = NOID;
          ok = push(st, r);
          if (ok == 0) { kvfree(fw); return 0; }
        }
      }
    }
    j = j + 1;
  }
  while (st->sp > 0) {
    st->sp = st->sp - 1;
    o = st->stk[st->sp];
    hdr = st->pool[o];
    code = hdr & 0xff;
    if (code != BV_VAR && code != BOOL_VAR && code != BV_VAL && code != BOOL_VAL) {
      ar = (hdr >> 8) & 0xff;
      if (plen - o - 1 < ar) { st->err = ERR_LIMIT; kvfree(fw); return 0; }
      i = 0;
      while (i < ar) {
        c = st->pool[o + 1 + i];
        if (c >= lo && c < o) {
          if (fw[c - lo] == 0) {
            fw[c - lo] = NOID;
            ok = push(st, c);
            if (ok == 0) { kvfree(fw); return 0; }
          }
        }
        i = i + 1;
      }
    }
  }
  cur = lo;
  o = lo;
  while (o < plen) {
    hdr = st->pool[o];
    ar = (hdr >> 8) & 0xff;
    if (plen - o - 1 < ar) { st->err = ERR_LIMIT; kvfree(fw); return 0; }
    if (fw[o - lo] != 0) {
      st->pool[cur] = hdr;
      code = hdr & 0xff;
      i = 0;
      while (i < ar) {
        c = st->pool[o + 1 + i];
        if (code != BV_VAR && code != BOOL_VAR && code != BV_VAL && code != BOOL_VAL && c >= lo && c < o) {
          c = fw[c - lo];
        }
        st->pool[cur + 1 + i] = c;
        i = i + 1;
      }
      fw[o - lo] = cur;
      cur = cur + 1 + ar;
      nodes = nodes + 1;
    }
    o = o + 1 + ar;
  }
  st->plen = cur;
  st->live = cur - lo;
  j = 0;
  while (j < st->flen) {
    r = st->facts[j];
    if (r >= lo && r < plen) {
      c = fw[r - lo];
      if (c == 0) { c = NOID; }
      st->facts[j] = c;
    }
    j = j + 1;
  }
  o = 0;
  while (o < lo) {
    ar = (st->pool[o] >> 8) & 0xff;
    if (lo - o - 1 < ar) { st->err = ERR_LIMIT; kvfree(fw); return 0; }
    o = o + 1 + ar;
    nodes = nodes + 1;
  }
  hc = 1024ull;
  while (hc < 4ull * (u64)nodes) {
    ok = tick(st);
    if (ok == 0) { kvfree(fw); return 0; }
    hc = hc * 2ull;
  }
  if (hc > (u64)MAX_POOL) { st->err = ERR_LIMIT; kvfree(fw); return 0; }
  ok = spend(st, (u32)hc);
  if (ok == 0) { kvfree(fw); return 0; }
  if (st->mem < (u32)hc) { st->err = ERR_LIMIT; kvfree(fw); return 0; }
  st->mem = st->mem - (u32)hc;
  kvfree(st->htab);
  st->htab = NULL;
  st->hcap = 0;
  st->hcnt = 0;
  nt = kvcalloc(hc, sizeof(u32));
  if (nt == NULL) { st->err = ERR_NOMEM; kvfree(fw); return 0; }
  st->htab = nt;
  st->hcap = (u32)hc;
  o = 0;
  while (o < cur) {
    ok = ck_hput(st, o);
    if (ok == 0) { kvfree(fw); return 0; }
    o = o + 1 + ((st->pool[o] >> 8) & 0xff);
  }
  kvfree(fw);
  return 1;
}

def ckRun : Fn := c_fn% u32 ck_run(struct ck *st, u32 *proof, u32 nwords, u32 *gx, u32 goal) {
  u32 ok; u32 off; u32 ns; u32 f; u32 hdr; u32 sig;
  ok = ck_init(st, nwords, goal);
  if (ok == 0) { return 0; }
  ok = ck_load(st, proof, nwords);
  if (ok == 0) { return 0; }
  ok = ck_scan(st);
  if (ok == 0) { return 0; }
  if (gx != NULL) {
    ok = ck_goal(st, gx, goal);
    if (ok == 0) { return 0; }
  }
  ns = proof[2];
  if (ns >= nwords) { return 0; }
  while (off < ns) {
    cond_resched();
    sig = signal_pending();
    if (sig != 0) { st->err = ERR_INTR; return 0; }
    f = ck_step(st, off);
    if (f == NOID) { return 0; }
    st->facts[st->flen] = f;
    st->flen = st->flen + 1;
    hdr = proof[3 + st->nexpr + off];
    off = off + 1 + ((hdr >> 16) & 0xff) + (hdr >> 24);
    if (off < ns) {
      if ((u64)st->plen > 2ull * (u64)st->lo + 2ull * (u64)st->live + (u64)st->flen + (u64)COMPACT_GAP) {
        ok = ck_compact(st);
        if (ok == 0) { return 0; }
      }
    }
  }
  if (st->flen == 0) { return 0; }
  return st->facts[st->flen - 1] == st->ff;
}

/-- 0 if the proof in `proof[0..nwords)` is accepted (and refutes node `goal`
of `goal_exprs`, unless that is `NULL`), else an error number. -/
def vbcfCheck : Fn := c_fn% u32 vbcf_check(u32 *goal_exprs, u32 goal, u32 *proof, u32 nwords) {
  struct ck *st; u32 ok; u32 err;
  st = kzalloc(sizeof(struct ck));
  if (st == NULL) { return E_NOMEM; }
  ok = ck_run(st, proof, nwords, goal_exprs, goal);
  err = st->err;
  ck_free(st);
  kvfree(st);
  if (ok != 0) { return 0; }
  if (err == ERR_NOMEM) { return E_NOMEM; }
  if (err == ERR_INTR) { return E_AGAIN; }
  return E_INVAL;
}

/-- The kernel-facing entry point, BCF's `bcf_check_proof` less the logger:
copy the proof in once, then check the copy.  Returns 0 if accepted, else an
error number. -/
def vbcfCheckProof : Fn := c_fn% u32 vbcf_check_proof(u32 *goal_exprs, u32 goal, bpfptr_t proof, u32 proof_size) {
  u32 *buf; u32 nwords; u32 r;
  if (proof_size < 12 || (proof_size & 3) != 0 || proof_size >= MAX_PROOF_BYTES) {
    return E_INVAL;
  }
  nwords = proof_size / 4;
  buf = kvcalloc((u64)nwords, sizeof(u32));
  if (buf == NULL) { return E_NOMEM; }
  r = copy_from_bpfptr(buf, proof, (u64)nwords);
  if (r != 0) {
    kvfree(buf);
    return E_FAULT;
  }
  r = vbcf_check(goal_exprs, goal, buf, nwords);
  kvfree(buf);
  return r;
}

def replayFns : List Fn :=
  [ckInit, ckFree, ckLoad, ckScan, ckGoal, ckRule, ckStep, ckCompact, ckRun, vbcfCheck, vbcfCheckProof]

end Vbcf
