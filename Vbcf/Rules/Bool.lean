import Vbcf.Rules.Basic

/-!
# Vbcf rules: boolean elimination and CNF rules

Each function mirrors the Lean rule of the corresponding name in
`Bcf/Check.lean` (section "More boolean rules" and "CNF tautologies"),
creating the same nodes in the same order.  `mk_not` / `mk_eq` / `mk2` /
`mk3` / `mkn` are `pushNode`, so a literal of the wrong type (for example the
sides of a bit-vector equation in `EQUIV_ELIM`) is rejected by the type check
exactly where the Lean `mkNot` / `mkDisj` returns `none`.

The only place the C is stricter than Lean is the 255-argument limit of a
node: `CNF_AND_NEG` and `CNF_OR_POS` on a 255-ary operand would build a
256-ary clause, which `mkn` rejects.
-/

namespace Vbcf
open EmbC

/-- `Bcf.equivElimClause`: `(¬a ∨ b)` for form 0, `(a ∨ ¬b)` for form 1. -/
def blEquivElimClause : Fn := c_fn% u32 bl_equiv_elim_clause(struct ck *st, u32 a, u32 b, u32 form) {
  u32 r;
  if (form == 0) {
    r = mk_not(st, a);
    if (r == NOID) { return NOID; }
    r = mk2(st, BOOL_DISJ, r, b);
    return r;
  }
  if (form == 1) {
    r = mk_not(st, b);
    if (r == NOID) { return NOID; }
    r = mk2(st, BOOL_DISJ, a, r);
    return r;
  }
  return NOID;
}

/-- `Bcf.notEquivElimClause`: `(a ∨ b)` for form 0, `(¬a ∨ ¬b)` for form 1. -/
def blNotEquivElimClause : Fn := c_fn% u32 bl_not_equiv_elim_clause(struct ck *st, u32 a, u32 b, u32 form) {
  u32 na; u32 nb; u32 r;
  if (form == 0) {
    r = mk2(st, BOOL_DISJ, a, b);
    return r;
  }
  if (form == 1) {
    na = mk_not(st, a);
    if (na == NOID) { return NOID; }
    nb = mk_not(st, b);
    if (nb == NOID) { return NOID; }
    r = mk2(st, BOOL_DISJ, na, nb);
    return r;
  }
  return NOID;
}

/-- `Bcf.mkNots` on the arguments of node `id`: negate each argument in order
and push the negations on the scratch stack.  Returns 0 on failure. -/
def blMkNots : Fn := c_fn% u32 bl_mk_nots(struct ck *st, u32 id) {
  u32 n; u32 i; u32 r; u32 ok;
  n = (st->pool[id] >> 8) & 0xff;
  while (i < n) {
    r = mk_not(st, st->pool[id + 1 + i]);
    if (r == NOID) { return 0; }
    ok = push(st, r);
    if (ok == 0) { return 0; }
    i = i + 1;
  }
  return 1;
}

/-- `Bcf.headOf`: the head literal of a CNF clause, `¬e` if `neg` else `e`. -/
def blHeadOf : Fn := c_fn% u32 bl_head_of(struct ck *st, u32 e, u32 neg) {
  u32 r;
  if (neg != 0) {
    r = mk_not(st, e);
    return r;
  }
  return e;
}

/-- `Bcf.cnfPosClause`: `h ∨ ¬a ∨ b` (form 0) or `h ∨ a ∨ ¬b` (form 1), with
`h = ¬e` if `neg` else `e`.  The head is built first, as in Lean. -/
def blCnfPosClause : Fn := c_fn% u32 bl_cnf_pos_clause(struct ck *st, u32 e, u32 a, u32 b, u32 form, u32 neg) {
  u32 h; u32 r;
  h = bl_head_of(st, e, neg);
  if (h == NOID) { return NOID; }
  if (form == 0) {
    r = mk_not(st, a);
    if (r == NOID) { return NOID; }
    r = mk3(st, BOOL_DISJ, h, r, b);
    return r;
  }
  if (form == 1) {
    r = mk_not(st, b);
    if (r == NOID) { return NOID; }
    r = mk3(st, BOOL_DISJ, h, a, r);
    return r;
  }
  return NOID;
}

/-- `Bcf.cnfNegClause`: `h ∨ a ∨ b` (lit 0) or `h ∨ ¬a ∨ ¬b` (lit 1), with
`h = ¬e` if `neg` else `e`.  The head is built first, as in Lean. -/
def blCnfNegClause : Fn := c_fn% u32 bl_cnf_neg_clause(struct ck *st, u32 e, u32 a, u32 b, u32 lit, u32 neg) {
  u32 h; u32 na; u32 nb; u32 r;
  h = bl_head_of(st, e, neg);
  if (h == NOID) { return NOID; }
  if (lit == 0) {
    r = mk3(st, BOOL_DISJ, h, a, b);
    return r;
  }
  if (lit == 1) {
    na = mk_not(st, a);
    if (na == NOID) { return NOID; }
    nb = mk_not(st, b);
    if (nb == NOID) { return NOID; }
    r = mk3(st, BOOL_DISJ, h, na, nb);
    return r;
  }
  return NOID;
}

/-- `Bcf.iteEqBody`: `ite c (e = a) (e = b)`. -/
def blIteEqBody : Fn := c_fn% u32 bl_ite_eq_body(struct ck *st, u32 e, u32 c, u32 a, u32 b) {
  u32 e1; u32 e2; u32 r;
  e1 = mk_eq(st, e, a);
  if (e1 == NOID) { return NOID; }
  e2 = mk_eq(st, e, b);
  if (e2 == NOID) { return NOID; }
  r = mk3(st, BOOL_ITE, c, e1, e2);
  return r;
}

/-- `Bcf.ruleImpliesElim`: from `a → b` conclude `¬a ∨ b`. -/
def rImpliesElim : Fn := c_fn% u32 r_implies_elim(struct ck *st, u32 np, u32 na) {
  u32 p; u32 r;
  if (np != 1 || na != 0) { return NOID; }
  p = st->prem[0];
  if ((st->pool[p] & 0xff) != BOOL_IMPLIES) { return NOID; }
  r = mk_not(st, st->pool[p + 1]);
  if (r == NOID) { return NOID; }
  r = mk2(st, BOOL_DISJ, r, st->pool[p + 2]);
  return r;
}

/-- `Bcf.ruleNotImpliesElim`: from `¬(a → b)` conclude `a` (idx 0) or `¬b` (idx 1). -/
def rNotImpliesElim : Fn := c_fn% u32 r_not_implies_elim(struct ck *st, u32 np, u32 na) {
  u32 p; u32 q; u32 idx; u32 r;
  if (np != 1 || na != 1) { return NOID; }
  p = st->prem[0];
  if ((st->pool[p] & 0xff) != BOOL_NOT) { return NOID; }
  q = st->pool[p + 1];
  if ((st->pool[q] & 0xff) != BOOL_IMPLIES) { return NOID; }
  idx = st->par[0];
  if (idx == 0) { return st->pool[q + 1]; }
  if (idx == 1) {
    r = mk_not(st, st->pool[q + 2]);
    return r;
  }
  return NOID;
}

/-- `Bcf.ruleEquivElim`: from `a = b` conclude `equivElimClause a b form`. -/
def rEquivElim : Fn := c_fn% u32 r_equiv_elim(struct ck *st, u32 np, u32 na) {
  u32 p; u32 r;
  if (np != 1 || na != 1) { return NOID; }
  p = st->prem[0];
  if ((st->pool[p] & 0xff) != BOOL_EQ) { return NOID; }
  r = bl_equiv_elim_clause(st, st->pool[p + 1], st->pool[p + 2], st->par[0]);
  return r;
}

/-- `Bcf.ruleNotEquivElim`: from `¬(a = b)` conclude `notEquivElimClause a b form`. -/
def rNotEquivElim : Fn := c_fn% u32 r_not_equiv_elim(struct ck *st, u32 np, u32 na) {
  u32 p; u32 q; u32 r;
  if (np != 1 || na != 1) { return NOID; }
  p = st->prem[0];
  if ((st->pool[p] & 0xff) != BOOL_NOT) { return NOID; }
  q = st->pool[p + 1];
  if ((st->pool[q] & 0xff) != BOOL_EQ) { return NOID; }
  r = bl_not_equiv_elim_clause(st, st->pool[q + 1], st->pool[q + 2], st->par[0]);
  return r;
}

/-- `Bcf.ruleXorElim`: from `a xor b` (binary) conclude `notEquivElimClause a b form`. -/
def rXorElim : Fn := c_fn% u32 r_xor_elim(struct ck *st, u32 np, u32 na) {
  u32 p; u32 r;
  if (np != 1 || na != 1) { return NOID; }
  p = st->prem[0];
  if ((st->pool[p] & 0xff) != BOOL_XOR) { return NOID; }
  if (((st->pool[p] >> 8) & 0xff) != 2) { return NOID; }
  r = bl_not_equiv_elim_clause(st, st->pool[p + 1], st->pool[p + 2], st->par[0]);
  return r;
}

/-- `Bcf.ruleNotXorElim`: from `¬(a xor b)` (binary) conclude
`equivElimClause a b form`, where lit 0 is form 1 and lit 1 is form 0. -/
def rNotXorElim : Fn := c_fn% u32 r_not_xor_elim(struct ck *st, u32 np, u32 na) {
  u32 p; u32 q; u32 lit; u32 form; u32 r;
  if (np != 1 || na != 1) { return NOID; }
  p = st->prem[0];
  if ((st->pool[p] & 0xff) != BOOL_NOT) { return NOID; }
  q = st->pool[p + 1];
  if ((st->pool[q] & 0xff) != BOOL_XOR) { return NOID; }
  if (((st->pool[q] >> 8) & 0xff) != 2) { return NOID; }
  lit = st->par[0];
  if (lit == 0) { form = 1; } else if (lit == 1) { form = 0; } else { form = 2; }
  r = bl_equiv_elim_clause(st, st->pool[q + 1], st->pool[q + 2], form);
  return r;
}

/-- `Bcf.ruleIteElim`: from `ite c a b` conclude `c ∨ b` (lit 1) or `¬c ∨ a` (lit 0). -/
def rIteElim : Fn := c_fn% u32 r_ite_elim(struct ck *st, u32 np, u32 na) {
  u32 p; u32 lit; u32 r;
  if (np != 1 || na != 1) { return NOID; }
  p = st->prem[0];
  if ((st->pool[p] & 0xff) != BOOL_ITE) { return NOID; }
  lit = st->par[0];
  if (lit == 1) {
    r = mk2(st, BOOL_DISJ, st->pool[p + 1], st->pool[p + 3]);
    return r;
  }
  if (lit == 0) {
    r = mk_not(st, st->pool[p + 1]);
    if (r == NOID) { return NOID; }
    r = mk2(st, BOOL_DISJ, r, st->pool[p + 2]);
    return r;
  }
  return NOID;
}

/-- `Bcf.ruleNotIteElim`: from `¬(ite c a b)` conclude `c ∨ ¬b` (lit 1) or
`¬c ∨ ¬a` (lit 0). -/
def rNotIteElim : Fn := c_fn% u32 r_not_ite_elim(struct ck *st, u32 np, u32 na) {
  u32 p; u32 q; u32 lit; u32 nc; u32 r;
  if (np != 1 || na != 1) { return NOID; }
  p = st->prem[0];
  if ((st->pool[p] & 0xff) != BOOL_NOT) { return NOID; }
  q = st->pool[p + 1];
  if ((st->pool[q] & 0xff) != BOOL_ITE) { return NOID; }
  lit = st->par[0];
  if (lit == 1) {
    r = mk_not(st, st->pool[q + 3]);
    if (r == NOID) { return NOID; }
    r = mk2(st, BOOL_DISJ, st->pool[q + 1], r);
    return r;
  }
  if (lit == 0) {
    nc = mk_not(st, st->pool[q + 1]);
    if (nc == NOID) { return NOID; }
    r = mk_not(st, st->pool[q + 2]);
    if (r == NOID) { return NOID; }
    r = mk2(st, BOOL_DISJ, nc, r);
    return r;
  }
  return NOID;
}

/-- `Bcf.ruleNotAnd`: from `¬(a₁ ∧ … ∧ aₙ)` conclude `¬a₁ ∨ … ∨ ¬aₙ`.
As in Lean, the parameters are ignored, whatever their number. -/
def rNotAnd : Fn := c_fn% u32 r_not_and(struct ck *st, u32 np, u32 na) {
  u32 p; u32 q; u32 base; u32 ok; u32 r;
  if (np != 1) { return NOID; }
  p = st->prem[0];
  if ((st->pool[p] & 0xff) != BOOL_NOT) { return NOID; }
  q = st->pool[p + 1];
  if ((st->pool[q] & 0xff) != BOOL_CONJ) { return NOID; }
  base = st->sp;
  ok = bl_mk_nots(st, q);
  if (ok == 0) { return NOID; }
  r = mkn(st, BOOL_DISJ, base, (st->pool[q] >> 8) & 0xff);
  return r;
}

/-- `Bcf.ruleCnfAndPos`: `¬e ∨ aₖ` for `e = a₁ ∧ … ∧ aₙ`. -/
def rCnfAndPos : Fn := c_fn% u32 r_cnf_and_pos(struct ck *st, u32 np, u32 na) {
  u32 e; u32 lit; u32 r;
  if (np != 0 || na != 2) { return NOID; }
  e = expr_at(st, st->par[0]);
  if (e == NOID) { return NOID; }
  if ((st->pool[e] & 0xff) != BOOL_CONJ) { return NOID; }
  lit = st->par[1];
  if (lit >= ((st->pool[e] >> 8) & 0xff)) { return NOID; }
  r = mk_not(st, e);
  if (r == NOID) { return NOID; }
  r = mk2(st, BOOL_DISJ, r, st->pool[e + 1 + lit]);
  return r;
}

/-- `Bcf.ruleCnfAndNeg`: `e ∨ ¬a₁ ∨ … ∨ ¬aₙ` for `e = a₁ ∧ … ∧ aₙ`.
Rejects when `n = 255` (the clause would have 256 literals). -/
def rCnfAndNeg : Fn := c_fn% u32 r_cnf_and_neg(struct ck *st, u32 np, u32 na) {
  u32 e; u32 base; u32 ok; u32 r;
  if (np != 0 || na != 1) { return NOID; }
  e = expr_at(st, st->par[0]);
  if (e == NOID) { return NOID; }
  if ((st->pool[e] & 0xff) != BOOL_CONJ) { return NOID; }
  base = st->sp;
  ok = push(st, e);
  if (ok == 0) { return NOID; }
  ok = bl_mk_nots(st, e);
  if (ok == 0) { return NOID; }
  r = mkn(st, BOOL_DISJ, base, 1 + ((st->pool[e] >> 8) & 0xff));
  return r;
}

/-- `Bcf.ruleCnfOrPos`: `¬e ∨ a₁ ∨ … ∨ aₙ` for `e = a₁ ∨ … ∨ aₙ`.
Rejects when `n = 255` (the clause would have 256 literals). -/
def rCnfOrPos : Fn := c_fn% u32 r_cnf_or_pos(struct ck *st, u32 np, u32 na) {
  u32 e; u32 base; u32 ok; u32 r;
  if (np != 0 || na != 1) { return NOID; }
  e = expr_at(st, st->par[0]);
  if (e == NOID) { return NOID; }
  if ((st->pool[e] & 0xff) != BOOL_DISJ) { return NOID; }
  r = mk_not(st, e);
  if (r == NOID) { return NOID; }
  base = st->sp;
  ok = push(st, r);
  if (ok == 0) { return NOID; }
  ok = push_args(st, e);
  if (ok == 0) { return NOID; }
  r = mkn(st, BOOL_DISJ, base, 1 + ((st->pool[e] >> 8) & 0xff));
  return r;
}

/-- `Bcf.ruleCnfOrNeg`: `e ∨ ¬aₖ` for `e = a₁ ∨ … ∨ aₙ`. -/
def rCnfOrNeg : Fn := c_fn% u32 r_cnf_or_neg(struct ck *st, u32 np, u32 na) {
  u32 e; u32 lit; u32 r;
  if (np != 0 || na != 2) { return NOID; }
  e = expr_at(st, st->par[0]);
  if (e == NOID) { return NOID; }
  if ((st->pool[e] & 0xff) != BOOL_DISJ) { return NOID; }
  lit = st->par[1];
  if (lit >= ((st->pool[e] >> 8) & 0xff)) { return NOID; }
  r = mk_not(st, st->pool[e + 1 + lit]);
  if (r == NOID) { return NOID; }
  r = mk2(st, BOOL_DISJ, e, r);
  return r;
}

/-- `Bcf.ruleCnfImpliesPos`: `¬e ∨ ¬a ∨ b` for `e = (a → b)`. -/
def rCnfImpliesPos : Fn := c_fn% u32 r_cnf_implies_pos(struct ck *st, u32 np, u32 na) {
  u32 e; u32 ne; u32 r;
  if (np != 0 || na != 1) { return NOID; }
  e = expr_at(st, st->par[0]);
  if (e == NOID) { return NOID; }
  if ((st->pool[e] & 0xff) != BOOL_IMPLIES) { return NOID; }
  ne = mk_not(st, e);
  if (ne == NOID) { return NOID; }
  r = mk_not(st, st->pool[e + 1]);
  if (r == NOID) { return NOID; }
  r = mk3(st, BOOL_DISJ, ne, r, st->pool[e + 2]);
  return r;
}

/-- `Bcf.ruleCnfImpliesNeg`: `e ∨ a` (lit 0) or `e ∨ ¬b` (lit 1) for `e = (a → b)`. -/
def rCnfImpliesNeg : Fn := c_fn% u32 r_cnf_implies_neg(struct ck *st, u32 np, u32 na) {
  u32 e; u32 lit; u32 r;
  if (np != 0 || na != 2) { return NOID; }
  e = expr_at(st, st->par[0]);
  if (e == NOID) { return NOID; }
  if ((st->pool[e] & 0xff) != BOOL_IMPLIES) { return NOID; }
  lit = st->par[1];
  if (lit == 0) {
    r = mk2(st, BOOL_DISJ, e, st->pool[e + 1]);
    return r;
  }
  if (lit == 1) {
    r = mk_not(st, st->pool[e + 2]);
    if (r == NOID) { return NOID; }
    r = mk2(st, BOOL_DISJ, e, r);
    return r;
  }
  return NOID;
}

/-- `Bcf.ruleCnfEquivPos`: `cnfPosClause e a b form true` for `e = (a = b)`. -/
def rCnfEquivPos : Fn := c_fn% u32 r_cnf_equiv_pos(struct ck *st, u32 np, u32 na) {
  u32 e; u32 r;
  if (np != 0 || na != 2) { return NOID; }
  e = expr_at(st, st->par[0]);
  if (e == NOID) { return NOID; }
  if ((st->pool[e] & 0xff) != BOOL_EQ) { return NOID; }
  r = bl_cnf_pos_clause(st, e, st->pool[e + 1], st->pool[e + 2], st->par[1], 1);
  return r;
}

/-- `Bcf.ruleCnfEquivNeg`: `cnfNegClause e a b lit false` for `e = (a = b)`. -/
def rCnfEquivNeg : Fn := c_fn% u32 r_cnf_equiv_neg(struct ck *st, u32 np, u32 na) {
  u32 e; u32 r;
  if (np != 0 || na != 2) { return NOID; }
  e = expr_at(st, st->par[0]);
  if (e == NOID) { return NOID; }
  if ((st->pool[e] & 0xff) != BOOL_EQ) { return NOID; }
  r = bl_cnf_neg_clause(st, e, st->pool[e + 1], st->pool[e + 2], st->par[1], 0);
  return r;
}

/-- `Bcf.ruleCnfXorPos`: `cnfNegClause e a b lit true` for `e = (a xor b)` (binary). -/
def rCnfXorPos : Fn := c_fn% u32 r_cnf_xor_pos(struct ck *st, u32 np, u32 na) {
  u32 e; u32 r;
  if (np != 0 || na != 2) { return NOID; }
  e = expr_at(st, st->par[0]);
  if (e == NOID) { return NOID; }
  if ((st->pool[e] & 0xff) != BOOL_XOR) { return NOID; }
  if (((st->pool[e] >> 8) & 0xff) != 2) { return NOID; }
  r = bl_cnf_neg_clause(st, e, st->pool[e + 1], st->pool[e + 2], st->par[1], 1);
  return r;
}

/-- `Bcf.ruleCnfXorNeg`: `cnfPosClause e a b form false` for `e = (a xor b)` (binary). -/
def rCnfXorNeg : Fn := c_fn% u32 r_cnf_xor_neg(struct ck *st, u32 np, u32 na) {
  u32 e; u32 r;
  if (np != 0 || na != 2) { return NOID; }
  e = expr_at(st, st->par[0]);
  if (e == NOID) { return NOID; }
  if ((st->pool[e] & 0xff) != BOOL_XOR) { return NOID; }
  if (((st->pool[e] >> 8) & 0xff) != 2) { return NOID; }
  r = bl_cnf_pos_clause(st, e, st->pool[e + 1], st->pool[e + 2], st->par[1], 0);
  return r;
}

/-- `Bcf.ruleCnfItePos`: for `e = ite c a b`, `¬e ∨ ¬c ∨ a` (lit 0),
`¬e ∨ c ∨ b` (lit 1) or `¬e ∨ a ∨ b` (lit 2).  `¬e` is built first, even
when `lit` is out of range, as in Lean. -/
def rCnfItePos : Fn := c_fn% u32 r_cnf_ite_pos(struct ck *st, u32 np, u32 na) {
  u32 e; u32 lit; u32 ne; u32 r;
  if (np != 0 || na != 2) { return NOID; }
  e = expr_at(st, st->par[0]);
  if (e == NOID) { return NOID; }
  if ((st->pool[e] & 0xff) != BOOL_ITE) { return NOID; }
  lit = st->par[1];
  ne = mk_not(st, e);
  if (ne == NOID) { return NOID; }
  if (lit == 0) {
    r = mk_not(st, st->pool[e + 1]);
    if (r == NOID) { return NOID; }
    r = mk3(st, BOOL_DISJ, ne, r, st->pool[e + 2]);
    return r;
  }
  if (lit == 1) {
    r = mk3(st, BOOL_DISJ, ne, st->pool[e + 1], st->pool[e + 3]);
    return r;
  }
  if (lit == 2) {
    r = mk3(st, BOOL_DISJ, ne, st->pool[e + 2], st->pool[e + 3]);
    return r;
  }
  return NOID;
}

/-- `Bcf.ruleCnfIteNeg`: for `e = ite c a b`, `e ∨ ¬c ∨ ¬a` (lit 0),
`e ∨ c ∨ ¬b` (lit 1) or `e ∨ ¬a ∨ ¬b` (lit 2). -/
def rCnfIteNeg : Fn := c_fn% u32 r_cnf_ite_neg(struct ck *st, u32 np, u32 na) {
  u32 e; u32 lit; u32 n1; u32 r;
  if (np != 0 || na != 2) { return NOID; }
  e = expr_at(st, st->par[0]);
  if (e == NOID) { return NOID; }
  if ((st->pool[e] & 0xff) != BOOL_ITE) { return NOID; }
  lit = st->par[1];
  if (lit == 0) {
    n1 = mk_not(st, st->pool[e + 1]);
    if (n1 == NOID) { return NOID; }
    r = mk_not(st, st->pool[e + 2]);
    if (r == NOID) { return NOID; }
    r = mk3(st, BOOL_DISJ, e, n1, r);
    return r;
  }
  if (lit == 1) {
    r = mk_not(st, st->pool[e + 3]);
    if (r == NOID) { return NOID; }
    r = mk3(st, BOOL_DISJ, e, st->pool[e + 1], r);
    return r;
  }
  if (lit == 2) {
    n1 = mk_not(st, st->pool[e + 2]);
    if (n1 == NOID) { return NOID; }
    r = mk_not(st, st->pool[e + 3]);
    if (r == NOID) { return NOID; }
    r = mk3(st, BOOL_DISJ, e, n1, r);
    return r;
  }
  return NOID;
}

/-- `Bcf.ruleIteEq`: `ite c (e = a) (e = b)` for `e = ite c a b`, boolean or
bit-vector.  The arity test is `Bcf.three`. -/
def rIteEq : Fn := c_fn% u32 r_ite_eq(struct ck *st, u32 np, u32 na) {
  u32 e; u32 code; u32 r;
  if (np != 0 || na != 1) { return NOID; }
  e = expr_at(st, st->par[0]);
  if (e == NOID) { return NOID; }
  code = st->pool[e] & 0xff;
  if (code != BOOL_ITE && code != BV_ITE) { return NOID; }
  if (((st->pool[e] >> 8) & 0xff) != 3) { return NOID; }
  r = bl_ite_eq_body(st, e, st->pool[e + 1], st->pool[e + 2], st->pool[e + 3]);
  return r;
}

def boolFns : List Fn :=
  [blEquivElimClause, blNotEquivElimClause, blMkNots, blHeadOf, blCnfPosClause, blCnfNegClause,
   blIteEqBody,
   rImpliesElim, rNotImpliesElim, rEquivElim, rNotEquivElim, rXorElim, rNotXorElim, rIteElim,
   rNotIteElim, rNotAnd, rCnfAndPos, rCnfAndNeg, rCnfOrPos, rCnfOrNeg, rCnfImpliesPos,
   rCnfImpliesNeg, rCnfEquivPos, rCnfEquivNeg, rCnfXorPos, rCnfXorNeg, rCnfItePos, rCnfIteNeg,
   rIteEq]

end Vbcf
