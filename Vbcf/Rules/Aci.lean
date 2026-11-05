import Vbcf.Rules.Eval

/-!
# Vbcf rules: ABSORB and ACI_NORM

These mirror `ruleAbsorb` and `ruleAciNorm` of `Bcf/Check.lean`.

A Lean `Op` is the header of a node without its arity: `hdr & ACI_OPMASK`
(code and params).  Two nodes have the same `Op` exactly when these agree
(none of the operators concerned is a variable or a literal).

`absorbF` and `flattenF` recurse over the pool.  The C versions carry a depth
counter starting at `MAX_DEPTH`; when it runs out they report "cannot tell"
and the step is rejected, whatever the Lean functions would have answered.
-/

namespace Vbcf
open EmbC

c_const% ACI_OPMASK := 0xffff00ff

/-- Is node `id` the literal `bvVal w v`?  (`n.op == .bvVal w v`, for `v < 2^64`.) -/
def aciIsVal : Fn := c_fn% u32 aci_is_val(struct ck *st, u32 id, u32 w, u64 v) {
  u32 hdr; u64 x;
  hdr = st->pool[id];
  if ((hdr & 0xff) != BV_VAL || ((hdr >> 16) & 0xff) != w) { return 0; }
  x = (u64)st->pool[id + 1];
  if (((hdr >> 8) & 0xff) == 2) { x = x | ((u64)st->pool[id + 2] << 32ull); }
  return x == v;
}

/-- Is node `id` the literal `bvVal w (2^w - 1)`?  No literal is wider than 64 bits. -/
def aciIsOnes : Fn := c_fn% u32 aci_is_ones(struct ck *st, u32 id, u32 w) {
  u64 m; u32 r;
  if (w == 0 || w > 64) { return 0; }
  m = mask64(w);
  r = aci_is_val(st, id, w, m);
  return r;
}

/-- `isZeroElem root n`: is node `id` the absorbing element of operator `rop`? -/
def aciZero : Fn := c_fn% u32 aci_zero(struct ck *st, u32 rop, u32 id) {
  u32 code; u32 r;
  code = rop & 0xff;
  if (code == BOOL_DISJ) { return st->pool[id] == HDR_TRUE; }
  if (code == BOOL_CONJ) { return st->pool[id] == HDR_FALSE; }
  if (code == BV_AND) {
    r = aci_is_val(st, id, (rop >> 16) & 0xff, 0ull);
    return r;
  }
  if (code == BV_OR) {
    r = aci_is_ones(st, id, (rop >> 16) & 0xff);
    return r;
  }
  return 0;
}

/-- `isNilElem root n`: is node `id` the identity element of operator `rop`? -/
def aciNil : Fn := c_fn% u32 aci_nil(struct ck *st, u32 rop, u32 id) {
  u32 code; u32 r;
  code = rop & 0xff;
  if (code == BOOL_DISJ) { return st->pool[id] == HDR_FALSE; }
  if (code == BOOL_CONJ) { return st->pool[id] == HDR_TRUE; }
  if (code == BV_AND) {
    r = aci_is_ones(st, id, (rop >> 16) & 0xff);
    return r;
  }
  if (code == BV_OR || code == BV_XOR) {
    r = aci_is_val(st, id, (rop >> 16) & 0xff, 0ull);
    return r;
  }
  return 0;
}

/-- `absorbF pool root _ i`: 1 if an absorbing element occurs in the
same-operator tree below `i`, 0 if not, `NOID` if the tree is deeper than
`depth` before one is found (the caller rejects). -/
def aciAbsorb : Fn := c_fn% u32 aci_absorb(struct ck *st, u32 rop, u32 i, u32 depth) {
  u32 r; u32 n; u32 k;
  if (depth == 0) { return NOID; }
  r = tick(st);
  if (r == 0) { return NOID; }
  r = aci_zero(st, rop, i);
  if (r != 0) { return 1; }
  if ((st->pool[i] & ACI_OPMASK) != rop) { return 0; }
  n = (st->pool[i] >> 8) & 0xff;
  while (k < n) {
    r = aci_absorb(st, rop, st->pool[i + 1 + k], depth - 1);
    if (r != 0) { return r; }
    k = k + 1;
  }
  return 0;
}

/-- `ruleAbsorb`. -/
def rAbsorb : Fn := c_fn% u32 r_absorb(struct ck *st, u32 np, u32 na) {
  u32 e; u32 r; u32 z; u32 rop; u32 ok;
  if (np != 0 || na != 1) { return NOID; }
  e = expr_at(st, st->par[0]);
  if (e == NOID) { return NOID; }
  if ((st->pool[e] & 0xff) != BOOL_EQ) { return NOID; }
  r = st->pool[e + 1];
  z = st->pool[e + 2];
  rop = st->pool[r] & ACI_OPMASK;
  ok = aci_zero(st, rop, z);
  if (ok == 0) { return NOID; }
  ok = aci_absorb(st, rop, r, MAX_DEPTH);
  if (ok != 1) { return NOID; }
  return e;
}

/-- `isAssocOp`, on a header. -/
def aciAssoc : Fn := c_fn% u32 aci_assoc(u32 hdr) {
  u32 code;
  code = hdr & 0xff;
  return code == BOOL_CONJ || code == BOOL_DISJ || code == BV_AND || code == BV_OR
    || code == BV_XOR || code == BV_CONCAT;
}

/-- `sameAssoc op o`: `rop` is the root operator, `hdr` the header of the other node. -/
def aciSame : Fn := c_fn% u32 aci_same(u32 rop, u32 hdr) {
  if ((rop & 0xff) == BV_CONCAT) { return (hdr & 0xff) == BV_CONCAT; }
  return (hdr & ACI_OPMASK) == rop;
}

/-- `flattenF pool op _ i`: push the leaves of the same-operator tree below
`i`, identity elements dropped, in left-to-right order.  Returns 1, or 0 if
the tree is deeper than `depth` or memory ran out (the caller rejects). -/
def aciFlat : Fn := c_fn% u32 aci_flat(struct ck *st, u32 rop, u32 i, u32 depth) {
  u32 r; u32 n; u32 k;
  if (depth == 0) { return 0; }
  r = tick(st);
  if (r == 0) { return 0; }
  r = aci_same(rop, st->pool[i]);
  if (r != 0) {
    n = (st->pool[i] >> 8) & 0xff;
    while (k < n) {
      r = aci_flat(st, rop, st->pool[i + 1 + k], depth - 1);
      if (r == 0) { return 0; }
      k = k + 1;
    }
    return 1;
  }
  r = aci_nil(st, rop, i);
  if (r != 0) { return 1; }
  r = push(st, i);
  return r;
}

/-- `sortNat` on `stk[base..sp)`: insertion sort, ascending. -/
def aciSort : Fn := c_fn% void aci_sort(struct ck *st, u32 base) {
  u32 i; u32 j; u32 x;
  i = base + 1;
  while (i < st->sp) {
    x = st->stk[i];
    j = i;
    while (j > base && st->stk[j - 1] > x) {
      st->stk[j] = st->stk[j - 1];
      j = j - 1;
    }
    st->stk[j] = x;
    i = i + 1;
  }
}

/-- Remove adjacent duplicates from the sorted list `stk[base..sp)`.  After
sorting this yields `sortNat (dedupNat l)`: the distinct elements, ascending. -/
def aciUniq : Fn := c_fn% void aci_uniq(struct ck *st, u32 base) {
  u32 i; u32 j;
  if (st->sp == base) { return; }
  i = base + 1;
  j = base + 1;
  while (i < st->sp) {
    if (st->stk[i] != st->stk[j - 1]) {
      st->stk[j] = st->stk[i];
      j = j + 1;
    }
    i = i + 1;
  }
  st->sp = j;
}

/-- `aciNF pool i`: 0 if node `i` is not an associative operator (`none`);
1 if it is, with `aciLeaves` pushed on the scratch stack; `NOID` if the
leaves cannot be computed (the caller rejects). -/
def aciNf : Fn := c_fn% u32 aci_nf(struct ck *st, u32 i) {
  u32 hdr; u32 code; u32 r; u32 base; u32 n;
  hdr = st->pool[i];
  r = aci_assoc(hdr);
  if (r == 0) { return 0; }
  base = st->sp;
  r = aci_flat(st, hdr & ACI_OPMASK, i, MAX_DEPTH);
  if (r == 0) { return NOID; }
  code = hdr & 0xff;
  if (code == BV_CONCAT) { return 1; }
  n = st->sp - base;
  if (n > MAX_SORT) { st->err = ERR_LIMIT; return NOID; }
  if (base > MAX_POOL) { st->err = ERR_LIMIT; return NOID; }
  if (st->sp < base) { st->err = ERR_LIMIT; return NOID; }
  r = spend(st, n * (n - 1) / 2);
  if (r == 0) { return NOID; }
  aci_sort(st, base);
  if (code != BV_XOR) { aci_uniq(st, base); }
  return 1;
}

/-- `ruleAciNorm` (with `aciEq`, `aciReduces`).  Both normal forms are
computed before any of the tests that use them; `ra`/`rb` say whether they
exist, and the leaf lists are `stk[ba..ba+la)` and `stk[bb..bb+lb)`. -/
def rAciNorm : Fn := c_fn% u32 r_aci_norm(struct ck *st, u32 np, u32 na) {
  u32 e; u32 a; u32 b; u32 ra; u32 rb; u32 ba; u32 bb; u32 la; u32 lb; u32 i; u32 r;
  if (np != 0 || na != 1) { return NOID; }
  e = expr_at(st, st->par[0]);
  if (e == NOID) { return NOID; }
  if ((st->pool[e] & 0xff) != BOOL_EQ) { return NOID; }
  a = st->pool[e + 1];
  b = st->pool[e + 2];
  if (a == b) { return e; }
  ba = st->sp;
  ra = aci_nf(st, a);
  if (ra == NOID) { return NOID; }
  la = st->sp - ba;
  r = spend(st, la);
  if (r == 0) { return NOID; }
  bb = st->sp;
  rb = aci_nf(st, b);
  if (rb == NOID) { return NOID; }
  lb = st->sp - bb;
  if (ra != 0 && rb != 0 && (st->pool[a] & ACI_OPMASK) == (st->pool[b] & ACI_OPMASK)
      && la == lb) {
    while (i < la && st->stk[ba + i] == st->stk[bb + i]) { i = i + 1; }
    if (i == la) { return e; }
  }
  if (ra != 0) {
    if (la == 1 && st->stk[ba] == b) { return e; }
    if (la == 0) {
      r = aci_nil(st, st->pool[a] & ACI_OPMASK, b);
      if (r != 0) { return e; }
    }
  }
  if (rb != 0) {
    if (lb == 1 && st->stk[bb] == a) { return e; }
    if (lb == 0) {
      r = aci_nil(st, st->pool[b] & ACI_OPMASK, a);
      if (r != 0) { return e; }
    }
  }
  return NOID;
}

def aciFns : List Fn :=
  [aciIsVal, aciIsOnes, aciZero, aciNil, aciAbsorb, rAbsorb, aciAssoc, aciSame, aciFlat,
   aciSort, aciUniq, aciNf, rAciNorm]

end Vbcf
