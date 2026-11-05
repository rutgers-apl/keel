import Vbcf.Core

/-!
# Vbcf rules: core equality and propositional rules

Each rule is `u32 r_x(struct ck *st, u32 np, u32 na)`.  The `np` premises
(ids of earlier facts) are `st->prem[0..np)`; the `na` raw parameter words
are `st->par[0..na)`.  The result is the id of the concluded formula, or
`NOID` to reject.  Each function mirrors the Lean `rule…` of the same name
in `Bcf/Check.lean`, including the order in which it creates nodes.
-/

namespace Vbcf
open EmbC

/-- A rule that is not implemented yet: rejects. -/
def stubRule (name : String) : Fn :=
  { name, params := [("st", .ptr (.struct "ck")), ("np", .u32), ("na", .u32)], ret := some .u32,
    locals := [], body := .ret (some NOID) }

def rAssume : Fn := c_fn% u32 r_assume(struct ck *st, u32 np, u32 na) {
  u32 g; u32 t;
  if (np != 0 || na != 1) { return NOID; }
  g = expr_at(st, st->par[0]);
  if (g == NOID || g != st->goal) { return NOID; }
  t = ty_of(st->pool[g]);
  if (t != TY_BOOL) { return NOID; }
  return g;
}

def rRefl : Fn := c_fn% u32 r_refl(struct ck *st, u32 np, u32 na) {
  u32 a; u32 t; u32 r;
  if (np != 0 || na != 1) { return NOID; }
  a = expr_at(st, st->par[0]);
  if (a == NOID) { return NOID; }
  t = ty_of(st->pool[a]);
  if (t >= TY_LIST) { return NOID; }
  r = mk_eq(st, a, a);
  return r;
}

def rSymm : Fn := c_fn% u32 r_symm(struct ck *st, u32 np, u32 na) {
  u32 p; u32 q; u32 r;
  if (np != 1 || na != 0) { return NOID; }
  p = st->prem[0];
  if ((st->pool[p] & 0xff) == BOOL_EQ) {
    r = mk_eq(st, st->pool[p + 2], st->pool[p + 1]);
    return r;
  }
  if ((st->pool[p] & 0xff) != BOOL_NOT) { return NOID; }
  q = st->pool[p + 1];
  if ((st->pool[q] & 0xff) != BOOL_EQ) { return NOID; }
  r = mk_eq(st, st->pool[q + 2], st->pool[q + 1]);
  if (r == NOID) { return NOID; }
  r = mk_not(st, r);
  return r;
}

def rTrans : Fn := c_fn% u32 r_trans(struct ck *st, u32 np, u32 na) {
  u32 p; u32 lhs; u32 rhs; u32 i; u32 r;
  if (np == 0 || na != 0) { return NOID; }
  p = st->prem[0];
  if ((st->pool[p] & 0xff) != BOOL_EQ) { return NOID; }
  lhs = st->pool[p + 1];
  rhs = st->pool[p + 2];
  i = 1;
  while (i < np) {
    p = st->prem[i];
    if ((st->pool[p] & 0xff) != BOOL_EQ) { return NOID; }
    if (st->pool[p + 1] != rhs) { return NOID; }
    rhs = st->pool[p + 2];
    i = i + 1;
  }
  r = mk_eq(st, lhs, rhs);
  return r;
}

def rCong : Fn := c_fn% u32 r_cong(struct ck *st, u32 np, u32 na) {
  u32 hdr; u32 code; u32 i; u32 p; u32 ok; u32 l; u32 r; u32 base;
  if (na != 1) { return NOID; }
  hdr = st->par[0];
  code = hdr & 0xff;
  if (code == BV_VAR || code == BV_VAL || code == BOOL_VAR || code == BOOL_VAL) { return NOID; }
  base = st->sp;
  while (i < np) {
    p = st->prem[i];
    if ((st->pool[p] & 0xff) != BOOL_EQ) { return NOID; }
    ok = push(st, st->pool[p + 1]);
    if (ok == 0) { return NOID; }
    i = i + 1;
  }
  i = 0;
  while (i < np) {
    p = st->prem[i];
    ok = push(st, st->pool[p + 2]);
    if (ok == 0) { return NOID; }
    i = i + 1;
  }
  hdr = code | (hdr & 0xffff0000);
  l = mkn(st, hdr, base, np);
  if (l == NOID) { return NOID; }
  r = mkn(st, hdr, base + np, np);
  if (r == NOID) { return NOID; }
  r = mk_eq(st, l, r);
  return r;
}

def rTrueIntro : Fn := c_fn% u32 r_true_intro(struct ck *st, u32 np, u32 na) {
  u32 r;
  if (np != 1 || na != 0) { return NOID; }
  r = mk_eq(st, st->prem[0], st->tt);
  return r;
}

def rTrueElim : Fn := c_fn% u32 r_true_elim(struct ck *st, u32 np, u32 na) {
  u32 p;
  if (np != 1 || na != 0) { return NOID; }
  p = st->prem[0];
  if ((st->pool[p] & 0xff) != BOOL_EQ) { return NOID; }
  if (st->pool[p + 2] != st->tt) { return NOID; }
  return st->pool[p + 1];
}

def rFalseIntro : Fn := c_fn% u32 r_false_intro(struct ck *st, u32 np, u32 na) {
  u32 p; u32 r;
  if (np != 1 || na != 0) { return NOID; }
  p = st->prem[0];
  if ((st->pool[p] & 0xff) != BOOL_NOT) { return NOID; }
  r = mk_eq(st, st->pool[p + 1], st->ff);
  return r;
}

def rFalseElim : Fn := c_fn% u32 r_false_elim(struct ck *st, u32 np, u32 na) {
  u32 p; u32 r;
  if (np != 1 || na != 0) { return NOID; }
  p = st->prem[0];
  if ((st->pool[p] & 0xff) != BOOL_EQ) { return NOID; }
  if (st->pool[p + 2] != st->ff) { return NOID; }
  r = mk_not(st, st->pool[p + 1]);
  return r;
}

def rEqResolve : Fn := c_fn% u32 r_eq_resolve(struct ck *st, u32 np, u32 na) {
  u32 q;
  if (np != 2 || na != 0) { return NOID; }
  q = st->prem[1];
  if ((st->pool[q] & 0xff) != BOOL_EQ) { return NOID; }
  if (st->pool[q + 1] != st->prem[0]) { return NOID; }
  return st->pool[q + 2];
}

def rModusPonens : Fn := c_fn% u32 r_modus_ponens(struct ck *st, u32 np, u32 na) {
  u32 q;
  if (np != 2 || na != 0) { return NOID; }
  q = st->prem[1];
  if ((st->pool[q] & 0xff) != BOOL_IMPLIES) { return NOID; }
  if (st->pool[q + 1] != st->prem[0]) { return NOID; }
  return st->pool[q + 2];
}

def rNotNotElim : Fn := c_fn% u32 r_not_not_elim(struct ck *st, u32 np, u32 na) {
  u32 p; u32 q;
  if (np != 1 || na != 0) { return NOID; }
  p = st->prem[0];
  if ((st->pool[p] & 0xff) != BOOL_NOT) { return NOID; }
  q = st->pool[p + 1];
  if ((st->pool[q] & 0xff) != BOOL_NOT) { return NOID; }
  return st->pool[q + 1];
}

def rContra : Fn := c_fn% u32 r_contra(struct ck *st, u32 np, u32 na) {
  u32 q;
  if (np != 2 || na != 0) { return NOID; }
  q = st->prem[1];
  if ((st->pool[q] & 0xff) != BOOL_NOT) { return NOID; }
  if (st->pool[q + 1] != st->prem[0]) { return NOID; }
  return st->ff;
}

def rAndElim : Fn := c_fn% u32 r_and_elim(struct ck *st, u32 np, u32 na) {
  u32 p; u32 k;
  if (np != 1 || na != 1) { return NOID; }
  p = st->prem[0];
  if ((st->pool[p] & 0xff) != BOOL_CONJ) { return NOID; }
  k = st->par[0];
  if (k >= ((st->pool[p] >> 8) & 0xff)) { return NOID; }
  return st->pool[p + 1 + k];
}

def rAndIntro : Fn := c_fn% u32 r_and_intro(struct ck *st, u32 np, u32 na) {
  u32 i; u32 ok; u32 r; u32 base;
  if (na != 0) { return NOID; }
  if (np == 1) { return st->prem[0]; }
  if (np < 2) { return NOID; }
  base = st->sp;
  while (i < np) {
    ok = push(st, st->prem[i]);
    if (ok == 0) { return NOID; }
    i = i + 1;
  }
  r = mkn(st, BOOL_CONJ, base, np);
  return r;
}

def rNotOrElim : Fn := c_fn% u32 r_not_or_elim(struct ck *st, u32 np, u32 na) {
  u32 p; u32 q; u32 k; u32 r;
  if (np != 1 || na != 1) { return NOID; }
  p = st->prem[0];
  if ((st->pool[p] & 0xff) != BOOL_NOT) { return NOID; }
  q = st->pool[p + 1];
  if ((st->pool[q] & 0xff) != BOOL_DISJ) { return NOID; }
  k = st->par[0];
  if (k >= ((st->pool[q] >> 8) & 0xff)) { return NOID; }
  r = mk_not(st, st->pool[q + 1 + k]);
  return r;
}

def rSplit : Fn := c_fn% u32 r_split(struct ck *st, u32 np, u32 na) {
  u32 a; u32 r;
  if (np != 0 || na != 1) { return NOID; }
  a = expr_at(st, st->par[0]);
  if (a == NOID) { return NOID; }
  r = mk_not(st, a);
  if (r == NOID) { return NOID; }
  r = mk2(st, BOOL_DISJ, a, r);
  return r;
}

def basicFns : List Fn :=
  [rAssume, rRefl, rSymm, rTrans, rCong, rTrueIntro, rTrueElim, rFalseIntro, rFalseElim,
   rEqResolve, rModusPonens, rNotNotElim, rContra, rAndElim, rAndIntro, rNotOrElim, rSplit]

end Vbcf
