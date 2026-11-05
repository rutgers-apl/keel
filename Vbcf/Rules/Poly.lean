import Vbcf.Rules.Eval

/-!
# Vbcf rules: POLY_NORM and POLY_NORM_EQ

Mirrors the section "POLY_NORM: linear normal forms over bit-vectors" of
`Bcf/Check.lean`.

## Representation of `Lin w`

A Lean `Lin w` (a constant and a list of `(atom, coefficient)` pairs) is a
range of the scratch stack:

    stk[b]   stk[b+1]      the constant, low word then high word
    stk[b+2+3k]            atom (node id) of term k
    stk[b+3+3k], [b+4+3k]  its coefficient, low word then high word

Coefficients are `BitVec w` with `w ≤ 64`, held in a `u64` reduced modulo
`2^w` (mask `m = mask64(w)`).  `rulePolyNorm` rejects in C when `w > 64`.

Node ids in C (pool offsets) are ordered like the Lean node indices, so the
`a < b` comparisons of `mergeTerms`, and therefore the normal forms, agree,
and two C ranges are word-for-word equal exactly when the Lean `Lin`s are equal.

A function that "pushes a `Lin`" appends its range at `st->sp`; the caller
remembers `st->sp` before the call as the base of the range, and the range
ends at the new `st->sp`.
-/

namespace Vbcf
open EmbC

/-- Push a 64-bit value on the scratch stack, low word first.  0 on failure. -/
def linPush64 : Fn := c_fn% u32 lin_push64(struct ck *st, u64 v) {
  u32 ok;
  ok = push(st, (u32)v);
  if (ok == 0) { return 0; }
  ok = push(st, (u32)(v >> 32ull));
  return ok;
}

/-- The 64-bit value at `stk[i]`, `stk[i + 1]`. -/
def linGet64 : Fn := c_fn% u64 lin_get64(struct ck *st, u32 i) {
  return (u64)st->stk[i] | ((u64)st->stk[i + 1] << 32ull);
}

/-- Push the term `(a, c)`.  0 on failure. -/
def linTerm : Fn := c_fn% u32 lin_term(struct ck *st, u32 a, u64 c) {
  u32 ok;
  ok = push(st, a);
  if (ok == 0) { return 0; }
  ok = lin_push64(st, c);
  return ok;
}

/-- `Lin.atom a`: push `⟨0, [(a, 1)]⟩`.  0 on failure. -/
def linAtom : Fn := c_fn% u32 lin_atom(struct ck *st, u32 a, u64 m) {
  u32 ok;
  ok = lin_push64(st, 0ull);
  if (ok == 0) { return 0; }
  ok = lin_term(st, a, 1ull & m);
  return ok;
}

/-- `Lin.add p q` (with `Lin.mergeTerms p.terms q.terms`), where `q` is
`stk[b0..b1)` and `p` is `stk[b1..sp)`: both are replaced by the sum, which
then occupies `stk[b0..sp)`.  A term whose coefficient becomes 0 is dropped,
as in `mergeTerms`.  0 on failure (out of memory). -/
def linAdd : Fn := c_fn% u32 lin_add(struct ck *st, u32 b0, u32 b1, u64 m) {
  u32 e; u32 i; u32 j; u32 a; u32 b; u32 n; u32 ok; u64 c; u64 d;
  e = st->sp;
  if (b1 < b0 || e < b1 || e > MAX_POOL) { return 0; }
  ok = spend(st, e - b0);
  if (ok == 0) { return 0; }
  c = lin_get64(st, b1);
  d = lin_get64(st, b0);
  ok = lin_push64(st, (c + d) & m);
  if (ok == 0) { return 0; }
  i = b1 + 2;
  j = b0 + 2;
  while (i < e && j < b1) {
    a = st->stk[i];
    b = st->stk[j];
    if (a < b) {
      c = lin_get64(st, i + 1);
      ok = lin_term(st, a, c);
      if (ok == 0) { return 0; }
      i = i + 3;
    } else if (b < a) {
      d = lin_get64(st, j + 1);
      ok = lin_term(st, b, d);
      if (ok == 0) { return 0; }
      j = j + 3;
    } else {
      c = lin_get64(st, i + 1);
      d = lin_get64(st, j + 1);
      c = (c + d) & m;
      if (c != 0ull) {
        ok = lin_term(st, a, c);
        if (ok == 0) { return 0; }
      }
      i = i + 3;
      j = j + 3;
    }
  }
  while (i < e) {
    ok = push(st, st->stk[i]);
    if (ok == 0) { return 0; }
    i = i + 1;
  }
  while (j < b1) {
    ok = push(st, st->stk[j]);
    if (ok == 0) { return 0; }
    j = j + 1;
  }
  n = st->sp - e;
  ok = spend(st, n);
  if (ok == 0) { return 0; }
  i = 0;
  while (i < n) {
    st->stk[b0 + i] = st->stk[e + i];
    i = i + 1;
  }
  st->sp = b0 + n;
  return 1;
}

/-- `Lin.scale k p` in place, where `p` is `stk[b0..sp)`: every coefficient is
multiplied by `k`, and terms whose coefficient becomes 0 are removed.
`Lin.neg` is `lin_scale(st, b0, m, m)`, since `-1` is `m`. -/
def linScale : Fn := c_fn% void lin_scale(struct ck *st, u32 b0, u64 k, u64 m) {
  u32 e; u32 i; u32 j; u64 c;
  e = st->sp;
  c = lin_get64(st, b0);
  c = (k * c) & m;
  st->stk[b0] = (u32)c;
  st->stk[b0 + 1] = (u32)(c >> 32ull);
  i = b0 + 2;
  j = b0 + 2;
  while (i < e) {
    c = lin_get64(st, i + 1);
    c = (k * c) & m;
    if (c != 0ull) {
      st->stk[j] = st->stk[i];
      st->stk[j + 1] = (u32)c;
      st->stk[j + 2] = (u32)(c >> 32ull);
      j = j + 3;
    }
    i = i + 3;
  }
  st->sp = j;
}

/-- `litVal pool w id`: 1 if node `id` is a bit-vector literal of width `w`,
with its value in `st->val`; else 0.  (A literal in the pool has width at
most 64, so `w > 64` gives 0.) -/
def polyLitVal : Fn := c_fn% u32 poly_lit_val(struct ck *st, u32 w, u32 id) {
  u32 hdr; u64 x; u64 m;
  hdr = st->pool[id];
  if ((hdr & 0xff) != BV_VAL) { return 0; }
  if ((hdr >> 16) != w) { return 0; }
  x = (u64)st->pool[id + 1];
  if (((hdr >> 8) & 0xff) == 2) { x = x | ((u64)st->pool[id + 2] << 32ull); }
  m = mask64(w);
  st->val = x & m;
  return 1;
}

/-- `linF pool w depth id`: push the linear normal form of node `id` at width
`w` (`1 ≤ w ≤ 64`).  Returns 1 on success.  Returns 0 if the nesting is deeper
than `depth` or memory runs out; the step must then be rejected (the Lean
function never runs out of fuel, so a cut-off must not yield a normal form). -/
def linF : Fn := c_fn% u32 lin_f(struct ck *st, u32 w, u32 id, u32 depth) {
  u32 hdr; u32 code; u32 n; u32 wn; u32 a; u32 b; u32 base; u32 mid; u32 i; u32 ok;
  u64 m; u64 k;
  if (depth == 0) { return 0; }
  ok = tick(st);
  if (ok == 0) { return 0; }
  hdr = st->pool[id];
  code = hdr & 0xff;
  n = (hdr >> 8) & 0xff;
  wn = hdr >> 16;
  m = mask64(w);
  base = st->sp;
  if (code == BV_VAL) {
    ok = poly_lit_val(st, w, id);
    if (ok != 0) {
      ok = lin_push64(st, st->val);
      return ok;
    }
  }
  if (code == BV_ADD && wn == w) {
    ok = lin_push64(st, 0ull);
    if (ok == 0) { return 0; }
    i = n;
    while (i > 0) {
      i = i - 1;
      a = st->pool[id + 1 + i];
      mid = st->sp;
      if (a < id) {
        ok = lin_f(st, w, a, depth - 1);
      } else {
        ok = lin_atom(st, a, m);
      }
      if (ok == 0) { return 0; }
      ok = lin_add(st, base, mid, m);
      if (ok == 0) { return 0; }
    }
    return 1;
  }
  if (code == BV_SUB && n == 2) {
    a = st->pool[id + 1];
    b = st->pool[id + 2];
    if (wn == w && a < id && b < id) {
      ok = lin_f(st, w, b, depth - 1);
      if (ok == 0) { return 0; }
      if (st->sp < base || st->sp > MAX_POOL) { return 0; }
      ok = spend(st, st->sp - base);
      if (ok == 0) { return 0; }
      lin_scale(st, base, m, m);
      mid = st->sp;
      ok = lin_f(st, w, a, depth - 1);
      if (ok == 0) { return 0; }
      ok = lin_add(st, base, mid, m);
      return ok;
    }
  }
  if (code == BV_NEG && n == 1) {
    a = st->pool[id + 1];
    if (wn == w && a < id) {
      ok = lin_f(st, w, a, depth - 1);
      if (ok == 0) { return 0; }
      if (st->sp < base || st->sp > MAX_POOL) { return 0; }
      ok = spend(st, st->sp - base);
      if (ok == 0) { return 0; }
      lin_scale(st, base, m, m);
      return 1;
    }
  }
  if (code == BV_MUL && n == 2) {
    a = st->pool[id + 1];
    b = st->pool[id + 2];
    if (wn == w && a < id && b < id) {
      ok = poly_lit_val(st, w, a);
      if (ok != 0) {
        k = st->val;
        ok = lin_f(st, w, b, depth - 1);
        if (ok == 0) { return 0; }
        if (st->sp < base || st->sp > MAX_POOL) { return 0; }
        ok = spend(st, st->sp - base);
        if (ok == 0) { return 0; }
        lin_scale(st, base, k, m);
        return 1;
      }
      ok = poly_lit_val(st, w, b);
      if (ok != 0) {
        k = st->val;
        ok = lin_f(st, w, a, depth - 1);
        if (ok == 0) { return 0; }
        if (st->sp < base || st->sp > MAX_POOL) { return 0; }
        ok = spend(st, st->sp - base);
        if (ok == 0) { return 0; }
        lin_scale(st, base, k, m);
        return 1;
      }
    }
  }
  ok = lin_atom(st, id, m);
  return ok;
}

/-- `rulePolyNorm`: the parameter names an equation `a = b` between
bit-vectors whose linear normal forms (`lin`) are equal; conclude it.
Creates no node.  Rejects when the width exceeds 64 or the nesting of the
arithmetic exceeds `MAX_DEPTH` (Lean has neither limit). -/
def rPolyNorm : Fn := c_fn% u32 r_poly_norm(struct ck *st, u32 np, u32 na) {
  u32 e; u32 a; u32 b; u32 w; u32 base; u32 mid; u32 n; u32 i; u32 ok;
  if (np != 0 || na != 1) { return NOID; }
  e = expr_at(st, st->par[0]);
  if (e == NOID) { return NOID; }
  if ((st->pool[e] & 0xff) != BOOL_EQ) { return NOID; }
  a = st->pool[e + 1];
  b = st->pool[e + 2];
  w = ty_of(st->pool[a]);
  if (w == 0 || w > 64) { return NOID; }
  base = st->sp;
  ok = lin_f(st, w, a, MAX_DEPTH);
  if (ok == 0) { return NOID; }
  mid = st->sp;
  ok = lin_f(st, w, b, MAX_DEPTH);
  if (ok == 0) { return NOID; }
  n = mid - base;
  if (st->sp - mid != n) { return NOID; }
  ok = spend(st, n);
  if (ok == 0) { return NOID; }
  while (i < n) {
    if (st->stk[base + i] != st->stk[mid + i]) { return NOID; }
    i = i + 1;
  }
  return e;
}

/-- `oddMulSub st m`: if node `m` is `c * (x0 - x1)` with `c` an odd literal,
the id of the subtraction node (whose arguments are `x0`, `x1`); else `NOID`. -/
def oddMulSub : Fn := c_fn% u32 odd_mul_sub(struct ck *st, u32 m) {
  u32 hdr; u32 c; u32 s; u32 ok;
  hdr = st->pool[m];
  if ((hdr & 0xff) != BV_MUL) { return NOID; }
  if (((hdr >> 8) & 0xff) != 2) { return NOID; }
  c = st->pool[m + 1];
  s = st->pool[m + 2];
  ok = poly_lit_val(st, hdr >> 16, c);
  if (ok == 0) { return NOID; }
  if ((st->pool[s] & 0xff) != BV_SUB) { return NOID; }
  if (((st->pool[s] >> 8) & 0xff) != 2) { return NOID; }
  if ((st->val & 1ull) != 1ull) { return NOID; }
  return s;
}

/-- `rulePolyNormEq`: from `c0 * (x0 - x1) = c1 * (y0 - y1)` with odd literals
`c0`, `c1`, conclude `(x0 = x1) = (y0 = y1)`.  Nodes, in order: `x0 = x1`,
`y0 = y1`, then the conclusion. -/
def rPolyNormEq : Fn := c_fn% u32 r_poly_norm_eq(struct ck *st, u32 np, u32 na) {
  u32 p; u32 s0; u32 s1; u32 e0; u32 e1; u32 r;
  if (np != 1 || na != 0) { return NOID; }
  p = st->prem[0];
  if ((st->pool[p] & 0xff) != BOOL_EQ) { return NOID; }
  s0 = odd_mul_sub(st, st->pool[p + 1]);
  if (s0 == NOID) { return NOID; }
  s1 = odd_mul_sub(st, st->pool[p + 2]);
  if (s1 == NOID) { return NOID; }
  e0 = mk_eq(st, st->pool[s0 + 1], st->pool[s0 + 2]);
  if (e0 == NOID) { return NOID; }
  e1 = mk_eq(st, st->pool[s1 + 1], st->pool[s1 + 2]);
  if (e1 == NOID) { return NOID; }
  r = mk_eq(st, e0, e1);
  return r;
}

def polyFns : List Fn :=
  [linPush64, linGet64, linTerm, linAtom, linAdd, linScale, polyLitVal, linF, rPolyNorm,
   oddMulSub, rPolyNormEq]

end Vbcf
