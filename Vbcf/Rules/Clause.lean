import Vbcf.Rules.Basic

/-!
# Vbcf rules: RESOLUTION, FACTORING, REORDERING

These mirror `ruleResolution`, `ruleFactoring` and `ruleReordering` of
`Bcf/Check.lean`.  A Lean `List Nat` of literals is a range of the scratch
stack; a Lean `Option Nat` pivot is a `u32` that is `NOID` for `none` (no
node id equals `NOID`, so comparing a literal with a `NOID` pivot never
succeeds, which is `eraseOpt l none = l` and `some p = none` being false).

None of the three rules creates a node before its final `mkDisj`, so a
rejection part-way leaves the pool as the Lean rule's `none` does.
-/

namespace Vbcf
open EmbC

/-- Push `litsOf st p pivot` on the scratch stack: the disjuncts of `p` if it
is a disjunction other than the pivot, else `p` itself.  Returns 0 on
allocation failure. -/
def clLits : Fn := c_fn% u32 cl_lits(struct ck *st, u32 p, u32 pivot) {
  u32 ok;
  if ((st->pool[p] & 0xff) == BOOL_DISJ && p != pivot) {
    ok = push_args(st, p);
    return ok;
  }
  ok = push(st, p);
  return ok;
}

/-- `eraseOpt` on the list `stk[base..sp)`: remove the first occurrence of
`pivot`, if there is one, keeping the order of the rest. -/
def clErase : Fn := c_fn% void cl_erase(struct ck *st, u32 base, u32 pivot) {
  u32 i;
  i = base;
  while (i < st->sp && st->stk[i] != pivot) { i = i + 1; }
  if (i == st->sp) { return; }
  while (i + 1 < st->sp) {
    st->stk[i] = st->stk[i + 1];
    i = i + 1;
  }
  st->sp = st->sp - 1;
}

/-- `ruleResolution` (with `resolveChain`, `testPol`, `mkClause`).  The
clause being built is `stk[base..sp)`; iteration `i` of the loop is one step
of `resolveChain`, and for `i = 0` it first pushes the literals of the first
premise.  `mapOpt ei` is checked as the loop goes: no node is created before
the end, so failing late is the same as failing early. -/
def rResolution : Fn := c_fn% u32 r_resolution(struct ck *st, u32 np, u32 na) {
  u32 n; u32 pw; u32 i; u32 lit; u32 nl; u32 piv0; u32 piv1; u32 base; u32 mid; u32 ok;
  u32 len; u32 r;
  if (np < 2) { return NOID; }
  n = np - 1;
  pw = (n + 31) / 32;
  if (na != pw + n) { return NOID; }
  base = st->sp;
  while (i < n) {
    lit = expr_at(st, st->par[pw + i]);
    if (lit == NOID) { return NOID; }
    nl = find_not(st, lit);
    if (st->err != 0) { return NOID; }
    if (((st->par[i / 32] >> (i % 32)) & 1) == 1) {
      piv0 = lit;
      piv1 = nl;
    } else {
      piv0 = nl;
      piv1 = lit;
    }
    if (i == 0) {
      ok = cl_lits(st, st->prem[0], piv0);
      if (ok == 0) { return NOID; }
    }
    ok = spend(st, st->sp - base);
    if (ok == 0) { return NOID; }
    cl_erase(st, base, piv0);
    mid = st->sp;
    ok = cl_lits(st, st->prem[i + 1], piv1);
    if (ok == 0) { return NOID; }
    ok = spend(st, st->sp - mid);
    if (ok == 0) { return NOID; }
    cl_erase(st, mid, piv1);
    i = i + 1;
  }
  len = st->sp - base;
  if (len == 0) { return st->ff; }
  if (len == 1) { return st->stk[base]; }
  r = mkn(st, BOOL_DISJ, base, len);
  return r;
}

/-- `paramByte`: byte `k` of the parameter words, `k < 4 * na`. -/
def clByte : Fn := c_fn% u32 cl_byte(struct ck *st, u32 k) {
  return (st->par[k / 4] >> (8 * (k % 4))) & 0xff;
}

/-- `parseDupPairs` for the `n` disjuncts of `p`.  The duplicate positions are
recorded in the mark table `stk[mb..mb+n)` (`stk[mb + d] = 1` iff `d` is in
Lean's `dups`).  Returns 1 if Lean returns `some`, else 0. -/
def clDups : Fn := c_fn% u32 cl_dups(struct ck *st, u32 p, u32 n, u32 na, u32 mb) {
  u32 vlen; u32 idx; u32 pl; u32 uniq; u32 haspre; u32 pre; u32 j; u32 d; u32 cnt; u32 b;
  vlen = na * 4;
  while (idx < vlen) {
    pl = cl_byte(st, idx);
    idx = idx + 1;
    if (pl == 0) { break; }
    if (pl < 2 || idx + pl > vlen) { return 0; }
    uniq = cl_byte(st, idx);
    if (uniq >= n) { return 0; }
    if (haspre != 0 && uniq <= pre) { return 0; }
    haspre = 1;
    pre = uniq;
    j = 1;
    while (j < pl) {
      d = cl_byte(st, idx + j);
      if (d >= n || d <= uniq) { return 0; }
      if (st->pool[p + 1 + uniq] != st->pool[p + 1 + d]) { return 0; }
      st->stk[mb + d] = 1;
      cnt = cnt + 1;
      j = j + 1;
    }
    idx = idx + pl;
  }
  if (cnt == 0) { return 0; }
  while (idx < vlen) {
    b = cl_byte(st, idx);
    if (b != 0) { return 0; }
    idx = idx + 1;
  }
  return 1;
}

/-- `ruleFactoring`.  `stk[mb..mb+n)` is the mark table of duplicate
positions and `stk[kb..kb+m)` is `keptLits`.  `subsetB args kept`: a literal
at an unmarked position is in `kept` by construction, so only the literals at
marked positions are searched for. -/
def rFactoring : Fn := c_fn% u32 r_factoring(struct ck *st, u32 np, u32 na) {
  u32 p; u32 n; u32 mb; u32 kb; u32 m; u32 i; u32 j; u32 x; u32 ok; u32 r;
  if (np != 1) { return NOID; }
  p = st->prem[0];
  if ((st->pool[p] & 0xff) != BOOL_DISJ) { return NOID; }
  if (na == 0) { return NOID; }
  n = (st->pool[p] >> 8) & 0xff;
  mb = st->sp;
  while (i < n) {
    ok = push(st, 0);
    if (ok == 0) { return NOID; }
    i = i + 1;
  }
  ok = cl_dups(st, p, n, na, mb);
  if (ok == 0) { return NOID; }
  kb = st->sp;
  i = 0;
  while (i < n) {
    if (st->stk[mb + i] == 0) {
      ok = push(st, st->pool[p + 1 + i]);
      if (ok == 0) { return NOID; }
    }
    i = i + 1;
  }
  m = st->sp - kb;
  ok = spend(st, (n - m) * m);
  if (ok == 0) { return NOID; }
  i = 0;
  while (i < n) {
    if (st->stk[mb + i] != 0) {
      x = st->pool[p + 1 + i];
      j = 0;
      while (j < m && st->stk[kb + j] != x) { j = j + 1; }
      if (j == m) { return NOID; }
    }
    i = i + 1;
  }
  if (m == 1) { return st->stk[kb]; }
  r = mkn(st, BOOL_DISJ, kb, m);
  return r;
}

/-- Half-word `t` of the parameter words (`u16` in `applySwaps`), `t < 2 * na`. -/
def clHalf : Fn := c_fn% u32 cl_half(struct ck *st, u32 t) {
  return (st->par[t / 2] >> (16 * (t % 2))) & 0xffff;
}

/-- `ruleReordering` (with `applySwaps`).  The two `subsetB` tests of the Lean
rule are not computed: `applySwaps` only swaps entries of the argument array
at in-bounds positions, so its result is a permutation of the arguments and
both tests are true whenever `applySwaps` returns `some`. -/
def rReordering : Fn := c_fn% u32 r_reordering(struct ck *st, u32 np, u32 na) {
  u32 p; u32 n; u32 cnt; u32 vec; u32 t; u32 sw; u32 j; u32 k; u32 x; u32 base; u32 ok; u32 r;
  if (np != 1) { return NOID; }
  p = st->prem[0];
  if ((st->pool[p] & 0xff) != BOOL_DISJ) { return p; }
  if (na == 0) { return p; }
  n = (st->pool[p] >> 8) & 0xff;
  cnt = cl_half(st, 0);
  if (cnt > n) { return NOID; }
  vec = (cnt + 1) * 2;
  if ((vec + 3) / 4 != na) { return NOID; }
  if (vec % 4 != 0) {
    sw = cl_half(st, cnt + 1);
    if (sw != 0) { return NOID; }
  }
  base = st->sp;
  ok = push_args(st, p);
  if (ok == 0) { return NOID; }
  t = 1;
  while (t <= cnt) {
    sw = cl_half(st, t);
    j = sw & 0xff;
    k = (sw >> 8) & 0xff;
    if (j >= n || k >= n) { return NOID; }
    x = st->stk[base + j];
    st->stk[base + j] = st->stk[base + k];
    st->stk[base + k] = x;
    t = t + 1;
  }
  r = mkn(st, BOOL_DISJ, base, n);
  return r;
}

def clauseFns : List Fn :=
  [clLits, clErase, rResolution, clByte, clDups, rFactoring, clHalf, rReordering]

end Vbcf
