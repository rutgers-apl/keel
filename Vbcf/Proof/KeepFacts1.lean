import Bcf.Check
import Lean

/-!
# The Lean rules keep the fact array (generic over the rewrite table)

Every rule of `Bcf.applyRule` builds nodes only through `pushNode` (directly or
through the builders `mkEq`, `mkNot`, `mkDisj`, …, the CNF clause helpers,
`mkNots`, and the rewrite instantiation `instE`/`instA`); none calls
`St.addFact`.  So the fact array of the returned state is the input's.

The proofs are mechanical: unfold the rule, `split` every `match`/`if` in the
hypothesis, and close each branch by chaining the `_keep` lemmas of the
builders that occur in it (the `kf_fwd` tactic below adds `L h` for every
hypothesis `h` and every known `_keep` lemma `L` that applies).
-/

namespace Vbcf.Proof.KF
open Bcf

/-! ## A forward-chaining helper tactic -/

/-- The `_keep` lemmas `kf_fwd` tries (those not yet declared are skipped). -/
def keepLemmas : List Lean.Name :=
  [``Bcf.pushNode_facts, `Vbcf.Proof.KF.mkEq_keep, `Vbcf.Proof.KF.mkNot_keep,
   `Vbcf.Proof.KF.mkConj_keep, `Vbcf.Proof.KF.mkDisj_keep, `Vbcf.Proof.KF.mkNots_keep,
   `Vbcf.Proof.KF.headOf_keep, `Vbcf.Proof.KF.cnfPosClause_keep, `Vbcf.Proof.KF.cnfNegClause_keep,
   `Vbcf.Proof.KF.equivElimClause_keep, `Vbcf.Proof.KF.notEquivElimClause_keep,
   `Vbcf.Proof.KF.iteEqBody_keep, `Vbcf.Proof.KF.mkClause_keep, `Vbcf.Proof.KF.pushLit_keep,
   `Vbcf.Proof.KF.pushApp_keep, `Vbcf.Proof.KF.instE_keep, `Vbcf.Proof.KF.instA_keep,
   `Vbcf.Proof.KF.rwConclude_keep]

open Lean Elab Tactic Meta in
/-- For every equation hypothesis `h` and every `_keep` lemma `L` (a global one from
`keepLemmas`, or a local hypothesis such as an induction hypothesis) with `L h` well typed,
add the hypothesis `L h : s'.facts = s.facts`. -/
elab "kf_fwd" : tactic => withMainContext do
  let env ← getEnv
  let lemmas := keepLemmas.filter env.contains
  let lctx ← getLCtx
  let mut locals : Array Expr := #[]
  for d in lctx do
    if !d.isImplementationDetail && (← whnfR (← instantiateMVars d.type)).isForall then
      locals := locals.push d.toExpr
  let mut found : Array Expr := #[]
  for ldecl in lctx do
    if ldecl.isImplementationDetail then continue
    let ty ← instantiateMVars ldecl.type
    unless ty.isAppOfArity ``Eq 3 do continue
    for c in lemmas do
      try
        let e ← withReducible <| mkAppM c #[ldecl.toExpr]
        found := found.push e
      catch _ => pure ()
    for l in locals do
      try
        let e ← withReducible <| mkAppM' l #[ldecl.toExpr]
        let t ← instantiateMVars (← inferType e)
        if t.isAppOfArity ``Eq 3 && (t.getArg! 1).isAppOfArity ``Bcf.St.facts 1 &&
            !t.hasExprMVar then
          found := found.push e
      catch _ => pure ()
  liftMetaTactic fun g => do
    let mut g := g
    for e in found do
      let t ← instantiateMVars (← inferType e)
      let (_, g') ← (← g.assert `kf t e).intro1P
      g := g'
    return [g]

set_option hygiene false in
/-- Close a leaf: a contradiction `none = some _`, a direct `some (s, x) = some (st', f)`,
or a builder call whose `_keep` lemma applies, chaining the facts equations. -/
macro "kf_leaf" : tactic => `(tactic| first
  | (simp at h; done)
  | (obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); rfl)
  | (obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); kf_fwd; simp only [*])
  | (kf_fwd; simp only [*]))

set_option hygiene false in
/-- Split every `match`/`if` in `h`, then close each branch with `kf_leaf`. -/
macro "kf_auto" : tactic => `(tactic| (repeat' split at h) <;> kf_leaf)

/-! ## Builders -/

theorem mkEq_keep {st st' : St} {a b r : Nat} (h : mkEq st a b = some (st', r)) :
    st'.facts = st.facts :=
  pushNode_facts h
theorem mkNot_keep {st st' : St} {a r : Nat} (h : mkNot st a = some (st', r)) :
    st'.facts = st.facts :=
  pushNode_facts h
theorem mkConj_keep {st st' : St} {a : Array Nat} {r : Nat} (h : mkConj st a = some (st', r)) :
    st'.facts = st.facts :=
  pushNode_facts h
theorem mkDisj_keep {st st' : St} {a : Array Nat} {r : Nat} (h : mkDisj st a = some (st', r)) :
    st'.facts = st.facts :=
  pushNode_facts h

theorem mkNots_keep {st st' : St} {l r : List Nat} (h : mkNots st l = some (st', r)) :
    st'.facts = st.facts := by
  induction l generalizing st st' r with
  | nil =>
    simp only [mkNots, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl
  | cons a rest ih => unfold mkNots at h; kf_auto

theorem headOf_keep {st st' : St} {e r : Nat} {negE : Bool} (h : headOf st e negE = some (st', r)) :
    st'.facts = st.facts := by
  unfold headOf at h; kf_auto

theorem cnfPosClause_keep {st st' : St} {e a b form r : Nat} {negE : Bool}
    (h : cnfPosClause st e a b form negE = some (st', r)) : st'.facts = st.facts := by
  unfold cnfPosClause at h; kf_auto

theorem cnfNegClause_keep {st st' : St} {e a b lit r : Nat} {negE : Bool}
    (h : cnfNegClause st e a b lit negE = some (st', r)) : st'.facts = st.facts := by
  unfold cnfNegClause at h; kf_auto

theorem equivElimClause_keep {st st' : St} {a b form r : Nat}
    (h : equivElimClause st a b form = some (st', r)) : st'.facts = st.facts := by
  unfold equivElimClause at h; kf_auto

theorem notEquivElimClause_keep {st st' : St} {a b form r : Nat}
    (h : notEquivElimClause st a b form = some (st', r)) : st'.facts = st.facts := by
  unfold notEquivElimClause at h; kf_auto

theorem iteEqBody_keep {st st' : St} {e c a b r : Nat}
    (h : iteEqBody st e c a b = some (st', r)) : st'.facts = st.facts := by
  unfold iteEqBody at h; kf_auto

theorem mkClause_keep {bi : Builtins} {st st' : St} {l : List Nat} {r : Nat}
    (h : mkClause bi st l = some (st', r)) : st'.facts = st.facts := by
  unfold mkClause at h; kf_auto

theorem pushLit_keep {st st' : St} {sz v r : Nat} (h : pushLit st sz v = some (st', r)) :
    st'.facts = st.facts := by
  unfold pushLit at h; kf_auto

theorem pushApp_keep {st st' : St} {op : RwOp} {is : List Nat} {r : Nat}
    (h : pushApp st op is = some (st', r)) : st'.facts = st.facts := by
  unfold pushApp at h; kf_auto

/-! ## Rewrite instantiation (mutual structural recursion) -/

mutual
theorem instE_keep' (bi : Builtins) (args : Array Nat) (e : RwExpr) :
    ∀ {st st' : St} {r : Nat}, instE bi args e st = some (st', r) → st'.facts = st.facts :=
  match e with
  | .var i => by intro h; simp only [instE] at h; kf_auto
  | .tt => by intro h; simp only [instE] at h; kf_auto
  | .ff => by intro h; simp only [instE] at h; kf_auto
  | .lit v => by intro h; simp only [instE] at h; kf_auto
  | .symVal val sz => by
    have i1 := @instE_keep' bi args val
    have i2 := @instE_keep' bi args sz
    intro h; simp only [instE] at h; kf_auto
  | .bvmax sz => by
    have i1 := @instE_keep' bi args sz
    intro h; simp only [instE] at h; kf_auto
  | .app op as => by
    have i1 := @instA_keep' bi args as
    intro h; simp only [instE] at h; kf_auto
  | .ite c t e => by
    have i1 := @instE_keep' bi args c
    have i2 := @instE_keep' bi args t
    have i3 := @instE_keep' bi args e
    intro h; simp only [instE] at h; kf_auto
  | .extract hi lo x => by
    have i1 := @instE_keep' bi args hi
    have i2 := @instE_keep' bi args lo
    have i3 := @instE_keep' bi args x
    intro h; simp only [instE] at h; kf_auto
  | .zext e x => by
    have i1 := @instE_keep' bi args e
    have i2 := @instE_keep' bi args x
    intro h; simp only [instE] at h; kf_auto
  | .sext e x => by
    have i1 := @instE_keep' bi args e
    have i2 := @instE_keep' bi args x
    intro h; simp only [instE] at h; kf_auto
  | .repeat n x => by
    have i1 := @instE_keep' bi args n
    have i2 := @instE_keep' bi args x
    intro h; simp only [instE] at h; kf_auto

theorem instA_keep' (bi : Builtins) (args : Array Nat) (as : RwArgs) :
    ∀ {st st' : St} {is : List Nat}, instA bi args as st = some (st', is) →
      st'.facts = st.facts :=
  match as with
  | .nil => by intro h; simp only [instA] at h; kf_auto
  | .cons a rest => by
    have i1 := @instE_keep' bi args a
    have i2 := @instA_keep' bi args rest
    intro h; simp only [instA] at h; kf_auto
end

theorem instE_keep {bi : Builtins} {args : Array Nat} {e : RwExpr} {st st' : St} {r : Nat}
    (h : instE bi args e st = some (st', r)) : st'.facts = st.facts := instE_keep' bi args e h

theorem instA_keep {bi : Builtins} {args : Array Nat} {as : RwArgs} {st st' : St} {is : List Nat}
    (h : instA bi args as st = some (st', is)) : st'.facts = st.facts := instA_keep' bi args as h

theorem rwConclude_keep {bi : Builtins} {args : Array Nat} {rr : RwRule} {st st' : St} {r : Nat}
    (h : rwConclude bi args rr st = some (st', r)) : st'.facts = st.facts := by
  unfold rwConclude at h; kf_auto

/-! ## The rules -/

section Rules
variable {st st' : St} {prems params : List Nat} {f : Nat}

theorem ruleAssume_keep {goal : Nat} {ei : EI}
    (h : ruleAssume goal ei st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleAssume at h; kf_auto

theorem ruleRefl_keep {ei : EI}
    (h : ruleRefl ei st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleRefl at h; kf_auto

theorem ruleSymm_keep
    (h : ruleSymm st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleSymm at h; kf_auto

theorem ruleTrans_keep
    (h : ruleTrans st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleTrans at h; kf_auto

theorem ruleCong_keep
    (h : ruleCong st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleCong at h; kf_auto

theorem ruleTrueIntro_keep {bi : Builtins}
    (h : ruleTrueIntro bi st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleTrueIntro at h; kf_auto

theorem ruleTrueElim_keep {bi : Builtins}
    (h : ruleTrueElim bi st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleTrueElim at h; kf_auto

theorem ruleFalseIntro_keep {bi : Builtins}
    (h : ruleFalseIntro bi st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleFalseIntro at h; kf_auto

theorem ruleFalseElim_keep {bi : Builtins}
    (h : ruleFalseElim bi st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleFalseElim at h; kf_auto

theorem ruleEqResolve_keep
    (h : ruleEqResolve st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleEqResolve at h; kf_auto

theorem ruleModusPonens_keep
    (h : ruleModusPonens st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleModusPonens at h; kf_auto

theorem ruleNotNotElim_keep
    (h : ruleNotNotElim st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleNotNotElim at h; kf_auto

theorem ruleContra_keep {bi : Builtins}
    (h : ruleContra bi st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleContra at h; kf_auto

theorem ruleAndElim_keep
    (h : ruleAndElim st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleAndElim at h; kf_auto

theorem ruleAndIntro_keep
    (h : ruleAndIntro st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleAndIntro at h; kf_auto

theorem ruleNotOrElim_keep
    (h : ruleNotOrElim st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleNotOrElim at h; kf_auto

theorem ruleSplit_keep {ei : EI}
    (h : ruleSplit ei st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleSplit at h; kf_auto

theorem ruleEvaluate_keep {ei : EI}
    (h : ruleEvaluate ei st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleEvaluate at h; kf_auto

theorem ruleImpliesElim_keep
    (h : ruleImpliesElim st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleImpliesElim at h; kf_auto

theorem ruleNotImpliesElim_keep
    (h : ruleNotImpliesElim st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleNotImpliesElim at h; kf_auto

theorem ruleEquivElim_keep
    (h : ruleEquivElim st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleEquivElim at h; kf_auto

theorem ruleNotEquivElim_keep
    (h : ruleNotEquivElim st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleNotEquivElim at h; kf_auto

theorem ruleXorElim_keep
    (h : ruleXorElim st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleXorElim at h; kf_auto

theorem ruleNotXorElim_keep
    (h : ruleNotXorElim st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleNotXorElim at h; kf_auto

theorem ruleIteElim_keep
    (h : ruleIteElim st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleIteElim at h; kf_auto

theorem ruleNotIteElim_keep
    (h : ruleNotIteElim st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleNotIteElim at h; kf_auto

theorem ruleNotAnd_keep
    (h : ruleNotAnd st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleNotAnd at h; kf_auto

theorem ruleCnfAndPos_keep {ei : EI}
    (h : ruleCnfAndPos ei st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleCnfAndPos at h; kf_auto

theorem ruleCnfAndNeg_keep {ei : EI}
    (h : ruleCnfAndNeg ei st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleCnfAndNeg at h; kf_auto

theorem ruleCnfOrPos_keep {ei : EI}
    (h : ruleCnfOrPos ei st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleCnfOrPos at h; kf_auto

theorem ruleCnfOrNeg_keep {ei : EI}
    (h : ruleCnfOrNeg ei st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleCnfOrNeg at h; kf_auto

theorem ruleCnfImpliesPos_keep {ei : EI}
    (h : ruleCnfImpliesPos ei st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleCnfImpliesPos at h; kf_auto

theorem ruleCnfImpliesNeg_keep {ei : EI}
    (h : ruleCnfImpliesNeg ei st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleCnfImpliesNeg at h; kf_auto

theorem ruleCnfEquivPos_keep {ei : EI}
    (h : ruleCnfEquivPos ei st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleCnfEquivPos at h; kf_auto

theorem ruleCnfEquivNeg_keep {ei : EI}
    (h : ruleCnfEquivNeg ei st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleCnfEquivNeg at h; kf_auto

theorem ruleCnfXorPos_keep {ei : EI}
    (h : ruleCnfXorPos ei st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleCnfXorPos at h; kf_auto

theorem ruleCnfXorNeg_keep {ei : EI}
    (h : ruleCnfXorNeg ei st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleCnfXorNeg at h; kf_auto

theorem ruleCnfItePos_keep {ei : EI}
    (h : ruleCnfItePos ei st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleCnfItePos at h; kf_auto

theorem ruleCnfIteNeg_keep {ei : EI}
    (h : ruleCnfIteNeg ei st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleCnfIteNeg at h; kf_auto

theorem ruleIteEq_keep {ei : EI}
    (h : ruleIteEq ei st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleIteEq at h; kf_auto

theorem ruleDistinctValues_keep {ei : EI}
    (h : ruleDistinctValues ei st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleDistinctValues at h; kf_auto

theorem ruleResolution_keep {bi : Builtins} {ei : EI}
    (h : ruleResolution bi ei st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleResolution at h; kf_auto

theorem ruleFactoring_keep
    (h : ruleFactoring st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleFactoring at h; kf_auto

theorem ruleReordering_keep
    (h : ruleReordering st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleReordering at h; kf_auto

theorem ruleAbsorb_keep {ei : EI}
    (h : ruleAbsorb ei st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleAbsorb at h; kf_auto

theorem ruleAciNorm_keep {ei : EI}
    (h : ruleAciNorm ei st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleAciNorm at h; kf_auto

theorem rulePolyNorm_keep {ei : EI}
    (h : rulePolyNorm ei st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold rulePolyNorm at h; kf_auto

theorem rulePolyNormEq_keep
    (h : rulePolyNormEq st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold rulePolyNormEq at h; kf_auto

theorem ruleRewrite_keep {tbl : Nat → Option RwRule} {bi : Builtins} {ei : EI}
    (h : ruleRewrite tbl bi ei st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleRewrite at h; kf_auto

theorem ruleBitblast_keep {bi : Builtins} {ei : EI}
    (h : ruleBitblast bi ei st prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold ruleBitblast at h; kf_auto

end Rules

/-! ## The dispatch -/

theorem applyRule_keep (tbl : Nat → Option RwRule) (g : Nat) (bi : Builtins) (ei : EI) (st : St)
    (r : Rule) (prems params : List Nat) (st' : St) (f : Nat)
    (h : applyRule tbl g bi ei st r prems params = some (st', f)) :
    st'.facts = st.facts := by
  unfold applyRule at h
  split at h
  all_goals first
    | (simp at h; done)
    | exact ruleAssume_keep h
    | exact ruleRefl_keep h
    | exact ruleSymm_keep h
    | exact ruleTrans_keep h
    | exact ruleCong_keep h
    | exact ruleTrueIntro_keep h
    | exact ruleTrueElim_keep h
    | exact ruleFalseIntro_keep h
    | exact ruleFalseElim_keep h
    | exact ruleEqResolve_keep h
    | exact ruleModusPonens_keep h
    | exact ruleNotNotElim_keep h
    | exact ruleContra_keep h
    | exact ruleAndElim_keep h
    | exact ruleAndIntro_keep h
    | exact ruleNotOrElim_keep h
    | exact ruleSplit_keep h
    | exact ruleEvaluate_keep h
    | exact ruleImpliesElim_keep h
    | exact ruleNotImpliesElim_keep h
    | exact ruleEquivElim_keep h
    | exact ruleNotEquivElim_keep h
    | exact ruleXorElim_keep h
    | exact ruleNotXorElim_keep h
    | exact ruleIteElim_keep h
    | exact ruleNotIteElim_keep h
    | exact ruleNotAnd_keep h
    | exact ruleCnfAndPos_keep h
    | exact ruleCnfAndNeg_keep h
    | exact ruleCnfOrPos_keep h
    | exact ruleCnfOrNeg_keep h
    | exact ruleCnfImpliesPos_keep h
    | exact ruleCnfImpliesNeg_keep h
    | exact ruleCnfEquivPos_keep h
    | exact ruleCnfEquivNeg_keep h
    | exact ruleCnfXorPos_keep h
    | exact ruleCnfXorNeg_keep h
    | exact ruleCnfItePos_keep h
    | exact ruleCnfIteNeg_keep h
    | exact ruleIteEq_keep h
    | exact ruleDistinctValues_keep h
    | exact ruleResolution_keep h
    | exact ruleFactoring_keep h
    | exact ruleReordering_keep h
    | exact ruleAbsorb_keep h
    | exact ruleAciNorm_keep h
    | exact rulePolyNorm_keep h
    | exact rulePolyNormEq_keep h
    | exact ruleRewrite_keep h
    | exact ruleBitblast_keep h

end Vbcf.Proof.KF
