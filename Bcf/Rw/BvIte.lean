import Bcf.Rw.Bv

/-!
# Bit-vector `ite` rewrites (`BV_ITE_*`)
-/
namespace Bcf

open RwExpr

/-! ## Helpers (width-1 conditions, `bvIteEval`) -/

theorem bvite_bv1 (k : BitVec 1) : k = 0#1 ∨ k = 1#1 := by
  revert k; decide

theorem bvite_lit11 : bvValEval 1 1 [] = .bv 1 1#1 := by simp [bvValEval]
theorem bvite_lit10 : bvValEval 1 0 [] = .bv 1 0#1 := by simp [bvValEval]

theorem bvite_not1 (k : BitVec 1) : appVal .bvnot [.bv 1 k] = .bv 1 (~~~k) := by
  simp [appVal, RwOp.reducible, RwOp.node, RwOp.widthV, RwOp.width, firstBv, Val.tys, Op.eval, bvUn, Val.asBv]

theorem bvite_and1 (a b : BitVec 1) : appVal .bvand [.bv 1 a, .bv 1 b] = .bv 1 (a &&& b) := by
  simp [appVal, RwOp.node, RwOp.widthV, RwOp.width, firstBv, Val.tys, Op.eval, bvN, Val.bvs, Val.asBv]
  rcases bvite_bv1 a with rfl | rfl <;> rcases bvite_bv1 b with rfl | rfl <;> decide

theorem bvite_eq1 {w : Nat} (x : BitVec w) (y : BitVec 1) :
    appVal .eq [.bv w x, .bv 1 y] = if h : 1 = w then .bool (decide (x = y.cast h)) else .bad := by
  by_cases h : 1 = w
  · subst h; simp [appVal, RwOp.node, Op.eval, eqEval, Val.eqv]
  · simp [appVal, RwOp.node, Op.eval, eqEval, Val.eqv, h]

theorem bvite_ite_cases (w : Nat) (c y : Val) (x : BitVec w) :
    bvIteEval w [c, .bv w x, y] = .bad ∨
    ∃ (cb : Bool) (yv : BitVec w), Val.asCond c = some cb ∧ y = .bv w yv ∧ w ≠ 0 ∧
      bvIteEval w [c, .bv w x, y] = .bv w (if cb then x else yv) := by
  cases hc : Val.asCond c with
  | none => left; simp [bvIteEval, hc]
  | some cb =>
    cases y with
    | bv m yv =>
      by_cases h : m = w
      · subst m
        by_cases hw : w = 0
        · left; simp [bvIteEval, hc, hw]
        · right; exact ⟨cb, yv, rfl, rfl, hw, by simp [bvIteEval, hc, hw]⟩
      · left; simp [bvIteEval, hc, h]
    | bool _ => left; simp [bvIteEval, hc]
    | list _ _ => left; simp [bvIteEval, hc]
    | bad => left; simp [bvIteEval, hc]

theorem bvite_ite_val {w : Nat} {c : Val} {cb : Bool} (hc : Val.asCond c = some cb) (hw : w ≠ 0) (x y : BitVec w) :
    bvIteEval w [c, .bv w x, .bv w y] = .bv w (if cb then x else y) := by
  simp [bvIteEval, hc, hw]

theorem bvite_cond1 (k : BitVec 1) : Val.asCond (.bv 1 k) = some (k.getLsbD 0) := by simp [Val.asCond]

/-- Structural unfolding: `bvIteEval` stays folded, width-1 `bvnot`/`bvand` and the width-1 literals are evaluated. -/
syntax "bvite_pat" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| bvite_pat $[$loc]?) => `(tactic| simp only [RwExpr.eq', RwExpr.bvnot', RwExpr.bvand', RwExpr.l0, RwExpr.l1,
      RwExpr.mk, RwArgs.ofList, denoteE, denoteA, spliceVal_bv, spliceVal_bool, spliceVal_bad, spliceVal_list,
      List.append_nil, List.singleton_append, List.cons_append, List.nil_append,
      l0_val, l1_val, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, bvite_lit11, bvite_lit10,
      bvite_not1, bvite_and1, bvite_eq1, spliceVal_eqEval, spliceVal_bvValEval,
      spliceVal_appVal_nonred (rfl : RwOp.reducible .eq = false),
      spliceVal_appVal_nonred (rfl : RwOp.reducible .bvnot = false),
      spliceVal_appVal_two] $[$loc]?)

-- rewrite id 83
theorem sound_BV_ITE_WIDTH_ONE :
    (RwRule.mk [.bvq]
      (none)
      (ite (eq' (var 0) (symVal (l1) (l1))) (symVal (l1) (l1)) (symVal (l0) (l1)))
      (var 0)).Sound := by
  intro env henv _ hl hr
  obtain ⟨w, x, hx, _⟩ := henv 0 .bvq rfl
  bvite_pat at hl hr ⊢
  simp only [hx] at hl hr ⊢
  bvite_pat at hl hr ⊢
  by_cases hw : w = 1
  · subst hw
    simp only [↓reduceDIte, BitVec.cast_eq] at hl ⊢
    rw [bvite_ite_val (cb := decide (x = 1#1)) rfl (by decide)]
    rcases bvite_bv1 x with rfl | rfl <;> rfl
  · simp [Ne.symm hw, bvIteEval, Val.asCond] at hl

-- rewrite id 84
theorem sound_BV_ITE_WIDTH_ONE_NOT :
    (RwRule.mk [.bvq]
      (none)
      (ite (eq' (var 0) (symVal (l0) (l1))) (symVal (l1) (l1)) (symVal (l0) (l1)))
      (bvnot' (var 0))).Sound := by
  intro env henv _ hl hr
  obtain ⟨w, x, hx, _⟩ := henv 0 .bvq rfl
  bvite_pat at hl hr ⊢
  simp only [hx] at hl hr ⊢
  bvite_pat at hl hr ⊢
  by_cases hw : w = 1
  · subst hw
    simp only [↓reduceDIte, BitVec.cast_eq, bvite_not1] at hl ⊢
    rw [bvite_ite_val (cb := decide (x = 0#1)) rfl (by decide)]
    rcases bvite_bv1 x with rfl | rfl <;> rfl
  · simp [Ne.symm hw, bvIteEval, Val.asCond] at hl

-- rewrite id 94
theorem sound_BV_ITE_EQUAL_CHILDREN :
    (RwRule.mk [.bv 1, .bvq]
      (none)
      (ite (var 0) (var 1) (var 1))
      (var 1)).Sound := by
  intro env henv _ hl hr
  obtain ⟨k, hk⟩ := henv 0 (.bv 1) rfl
  obtain ⟨w, x, hx, _⟩ := henv 1 .bvq rfl
  bvite_pat at hl hr ⊢
  simp only [hk, hx] at hl hr ⊢
  rcases bvite_ite_cases w (.bv 1 k) (.bv w x) x with hI | ⟨cb, yv, hc, hy, hw, hI⟩
  · exact absurd hI hl
  · injection hy with _ hy; subst hy
    rw [hI]; cases cb <;> rfl

-- rewrite id 95
theorem sound_BV_ITE_CONST_CHILDREN_1 :
    (RwRule.mk [.bv 1]
      (none)
      (ite (var 0) (symVal (l0) (l1)) (symVal (l1) (l1)))
      (bvnot' (var 0))).Sound := by
  intro env henv _ hl hr
  obtain ⟨k, hk⟩ := henv 0 (.bv 1) rfl
  bvite_pat at hl hr ⊢
  simp only [hk] at hl hr ⊢
  bvite_pat at hl hr ⊢
  rw [bvite_ite_val (bvite_cond1 k) (by decide)]
  rcases bvite_bv1 k with rfl | rfl <;> rfl

-- rewrite id 96
theorem sound_BV_ITE_CONST_CHILDREN_2 :
    (RwRule.mk [.bv 1]
      (none)
      (ite (var 0) (symVal (l1) (l1)) (symVal (l0) (l1)))
      (var 0)).Sound := by
  intro env henv _ hl hr
  obtain ⟨k, hk⟩ := henv 0 (.bv 1) rfl
  bvite_pat at hl hr ⊢
  simp only [hk] at hl hr ⊢
  rw [bvite_ite_val (bvite_cond1 k) (by decide)]
  rcases bvite_bv1 k with rfl | rfl <;> rfl

-- rewrite id 97
theorem sound_BV_ITE_EQUAL_COND_1 :
    (RwRule.mk [.bv 1, .bvq, .bvq, .bvq]
      (none)
      (ite (var 0) (ite (var 0) (var 1) (var 2)) (var 3))
      (ite (var 0) (var 1) (var 3))).Sound := by
  intro env henv _ hl hr
  obtain ⟨k, hk⟩ := henv 0 (.bv 1) rfl
  obtain ⟨w1, x1, hx1, _⟩ := henv 1 .bvq rfl
  obtain ⟨w2, x2, hx2, _⟩ := henv 2 .bvq rfl
  obtain ⟨w3, x3, hx3, _⟩ := henv 3 .bvq rfl
  bvite_pat at hl hr ⊢
  simp only [hk, hx1, hx2, hx3] at hl hr ⊢
  rcases bvite_ite_cases w1 (.bv 1 k) (.bv w2 x2) x1 with hI | ⟨cb, yv, hc, hy, hw, hI⟩
  · simp [hI] at hl
  · simp only [hI] at hl ⊢
    injection hy with hw2 hy; subst w2; obtain rfl := eq_of_heq hy
    rcases bvite_ite_cases w1 (.bv 1 k) (.bv w3 x3) (if cb then x1 else x2) with hJ | ⟨cb', yv', hc', hy', _, hJ⟩
    · exact absurd hJ hl
    · injection hy' with hw3 hy'; subst w3; obtain rfl := eq_of_heq hy'
      rw [hJ, bvite_ite_val hc' hw]
      rw [hc] at hc'; injection hc' with hcb; subst hcb
      cases cb <;> rfl

-- rewrite id 98
theorem sound_BV_ITE_EQUAL_COND_2 :
    (RwRule.mk [.bv 1, .bvq, .bvq, .bvq]
      (none)
      (ite (var 0) (var 1) (ite (var 0) (var 2) (var 3)))
      (ite (var 0) (var 1) (var 3))).Sound := by
  intro env henv _ hl hr
  obtain ⟨k, hk⟩ := henv 0 (.bv 1) rfl
  obtain ⟨w1, x1, hx1, _⟩ := henv 1 .bvq rfl
  obtain ⟨w2, x2, hx2, _⟩ := henv 2 .bvq rfl
  obtain ⟨w3, x3, hx3, _⟩ := henv 3 .bvq rfl
  bvite_pat at hl hr ⊢
  simp only [hk, hx1, hx2, hx3] at hl hr ⊢
  rcases bvite_ite_cases w2 (.bv 1 k) (.bv w3 x3) x2 with hI | ⟨cb, yv, hc, hy, hw, hI⟩
  · rw [hI] at hl; simp [bvIteEval] at hl
  · simp only [hI] at hl ⊢
    injection hy with hw3 hy; subst w3; obtain rfl := eq_of_heq hy
    rcases bvite_ite_cases w1 (.bv 1 k) (.bv w2 (if cb then x2 else x3)) x1 with hJ | ⟨cb', yv', hc', hy', hw1, hJ⟩
    · exact absurd hJ hl
    · injection hy' with hw2 hy'; subst w2; obtain rfl := eq_of_heq hy'
      rw [hJ, bvite_ite_val hc' hw1]
      rw [hc] at hc'; injection hc' with hcb; subst hcb
      cases cb <;> rfl

-- rewrite id 99
theorem sound_BV_ITE_EQUAL_COND_3 :
    (RwRule.mk [.bv 1, .bvq, .bvq, .bvq, .bvq]
      (none)
      (ite (var 0) (ite (var 0) (var 1) (var 2)) (ite (var 0) (var 3) (var 4)))
      (ite (var 0) (var 1) (var 4))).Sound := by
  intro env henv _ hl hr
  obtain ⟨k, hk⟩ := henv 0 (.bv 1) rfl
  obtain ⟨w1, x1, hx1, _⟩ := henv 1 .bvq rfl
  obtain ⟨w2, x2, hx2, _⟩ := henv 2 .bvq rfl
  obtain ⟨w3, x3, hx3, _⟩ := henv 3 .bvq rfl
  obtain ⟨w4, x4, hx4, _⟩ := henv 4 .bvq rfl
  bvite_pat at hl hr ⊢
  simp only [hk, hx1, hx2, hx3, hx4] at hl hr ⊢
  rcases bvite_ite_cases w1 (.bv 1 k) (.bv w2 x2) x1 with hI | ⟨cb, yv, hc, hy, hw, hI⟩
  · simp [hI] at hl
  · simp only [hI] at hl ⊢
    injection hy with hw2 hy; subst w2; obtain rfl := eq_of_heq hy
    rcases bvite_ite_cases w3 (.bv 1 k) (.bv w4 x4) x3 with hK | ⟨cb'', yv'', hc'', hy'', hw3, hK⟩
    · rw [hK] at hl; simp [bvIteEval] at hl
    · simp only [hK] at hl ⊢
      injection hy'' with hw4 hy''; subst w4; obtain rfl := eq_of_heq hy''
      rcases bvite_ite_cases w1 (.bv 1 k) (.bv w3 (if cb'' then x3 else x4)) (if cb then x1 else x2)
        with hJ | ⟨cb', yv', hc', hy', _, hJ⟩
      · exact absurd hJ hl
      · injection hy' with hw3 hy'; subst w3; obtain rfl := eq_of_heq hy'
        rw [hJ, bvite_ite_val hc' hw]
        rw [hc] at hc' hc''; injection hc' with hcb; injection hc'' with hcb'; subst hcb hcb'
        cases cb <;> rfl

-- rewrite id 100
theorem sound_BV_ITE_MERGE_THEN_IF :
    (RwRule.mk [.bv 1, .bv 1, .bvq, .bvq]
      (none)
      (ite (var 0) (ite (var 1) (var 2) (var 3)) (var 2))
      (ite (bvand' [var 0, bvnot' (var 1)]) (var 3) (var 2))).Sound := by
  intro env henv _ hl hr
  obtain ⟨k0, hk0⟩ := henv 0 (.bv 1) rfl
  obtain ⟨k1, hk1⟩ := henv 1 (.bv 1) rfl
  obtain ⟨w2, x2, hx2, _⟩ := henv 2 .bvq rfl
  obtain ⟨w3, x3, hx3, _⟩ := henv 3 .bvq rfl
  bvite_pat at hl hr ⊢
  simp only [hk0, hk1, hx2, hx3] at hl hr ⊢
  bvite_pat at hl hr ⊢
  rcases bvite_ite_cases w2 (.bv 1 k1) (.bv w3 x3) x2 with hI | ⟨cb, yv, hc, hy, hw, hI⟩
  · simp [hI] at hl
  · simp only [hI] at hl ⊢
    injection hy with hw3 hy; subst w3; obtain rfl := eq_of_heq hy
    rw [bvite_ite_val (bvite_cond1 k0) hw, bvite_ite_val (bvite_cond1 _) hw]
    rw [bvite_cond1] at hc; injection hc with hcb; subst hcb
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not]
    cases k0.getLsbD 0 <;> cases k1.getLsbD 0 <;> rfl

-- rewrite id 101
theorem sound_BV_ITE_MERGE_ELSE_IF :
    (RwRule.mk [.bv 1, .bv 1, .bvq, .bvq]
      (none)
      (ite (var 0) (ite (var 1) (var 2) (var 3)) (var 3))
      (ite (bvand' [var 0, var 1]) (var 2) (var 3))).Sound := by
  intro env henv _ hl hr
  obtain ⟨k0, hk0⟩ := henv 0 (.bv 1) rfl
  obtain ⟨k1, hk1⟩ := henv 1 (.bv 1) rfl
  obtain ⟨w2, x2, hx2, _⟩ := henv 2 .bvq rfl
  obtain ⟨w3, x3, hx3, _⟩ := henv 3 .bvq rfl
  bvite_pat at hl hr ⊢
  simp only [hk0, hk1, hx2, hx3] at hl hr ⊢
  bvite_pat at hl hr ⊢
  rcases bvite_ite_cases w2 (.bv 1 k1) (.bv w3 x3) x2 with hI | ⟨cb, yv, hc, hy, hw, hI⟩
  · simp [hI] at hl
  · simp only [hI] at hl ⊢
    injection hy with hw3 hy; subst w3; obtain rfl := eq_of_heq hy
    rw [bvite_ite_val (bvite_cond1 k0) hw, bvite_ite_val (bvite_cond1 _) hw]
    rw [bvite_cond1] at hc; injection hc with hcb; subst hcb
    simp only [BitVec.getLsbD_and]
    cases k0.getLsbD 0 <;> cases k1.getLsbD 0 <;> rfl

-- rewrite id 102
theorem sound_BV_ITE_MERGE_THEN_ELSE :
    (RwRule.mk [.bv 1, .bv 1, .bvq, .bvq]
      (none)
      (ite (var 0) (var 2) (ite (var 1) (var 2) (var 3)))
      (ite (bvand' [bvnot' (var 0), bvnot' (var 1)]) (var 3) (var 2))).Sound := by
  intro env henv _ hl hr
  obtain ⟨k0, hk0⟩ := henv 0 (.bv 1) rfl
  obtain ⟨k1, hk1⟩ := henv 1 (.bv 1) rfl
  obtain ⟨w2, x2, hx2, _⟩ := henv 2 .bvq rfl
  obtain ⟨w3, x3, hx3, _⟩ := henv 3 .bvq rfl
  bvite_pat at hl hr ⊢
  simp only [hk0, hk1, hx2, hx3] at hl hr ⊢
  bvite_pat at hl hr ⊢
  rcases bvite_ite_cases w2 (.bv 1 k1) (.bv w3 x3) x2 with hI | ⟨cb, yv, hc, hy, hw, hI⟩
  · rw [hI] at hl; simp [bvIteEval] at hl
  · simp only [hI] at hl ⊢
    injection hy with hw3 hy; subst w3; obtain rfl := eq_of_heq hy
    rw [bvite_ite_val (bvite_cond1 k0) hw, bvite_ite_val (bvite_cond1 _) hw]
    rw [bvite_cond1] at hc; injection hc with hcb; subst hcb
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not]
    cases k0.getLsbD 0 <;> cases k1.getLsbD 0 <;> rfl

-- rewrite id 103
theorem sound_BV_ITE_MERGE_ELSE_ELSE :
    (RwRule.mk [.bv 1, .bv 1, .bvq, .bvq]
      (none)
      (ite (var 0) (var 3) (ite (var 1) (var 2) (var 3)))
      (ite (bvand' [bvnot' (var 0), var 1]) (var 2) (var 3))).Sound := by
  intro env henv _ hl hr
  obtain ⟨k0, hk0⟩ := henv 0 (.bv 1) rfl
  obtain ⟨k1, hk1⟩ := henv 1 (.bv 1) rfl
  obtain ⟨w2, x2, hx2, _⟩ := henv 2 .bvq rfl
  obtain ⟨w3, x3, hx3, _⟩ := henv 3 .bvq rfl
  bvite_pat at hl hr ⊢
  simp only [hk0, hk1, hx2, hx3] at hl hr ⊢
  bvite_pat at hl hr ⊢
  rcases bvite_ite_cases w2 (.bv 1 k1) (.bv w3 x3) x2 with hI | ⟨cb, yv, hc, hy, hw, hI⟩
  · rw [hI] at hl; simp [bvIteEval] at hl
  · simp only [hI] at hl ⊢
    injection hy with hw3 hy; subst w3; obtain rfl := eq_of_heq hy
    rw [bvite_ite_val (bvite_cond1 k0) hw, bvite_ite_val (bvite_cond1 _) hw]
    rw [bvite_cond1] at hc; injection hc with hcb; subst hcb
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not]
    cases k0.getLsbD 0 <;> cases k1.getLsbD 0 <;> rfl

end Bcf
