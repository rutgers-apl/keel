import Bcf.Rw.Bv

/-!
# `BV_MULT_SLT_MULT_1/2`

Proved under the added condition `an ≤ n` (with `tn + n = an + m` from typing, the products fit); without it BCF's rules are unsound.
-/
namespace Bcf

open RwExpr

/-! ## Helpers (prefix `mul_`) -/

syntax "mul_pat" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| mul_pat $[$loc]?) => `(tactic| simp only [RwExpr.sgt', RwExpr.eq', RwExpr.not', RwExpr.ult', RwExpr.ule',
      RwExpr.slt', RwExpr.sle', RwExpr.sge', RwExpr.conj', RwExpr.bvsub', RwExpr.bvadd', RwExpr.bvmul',
      RwExpr.bvshl', RwExpr.bvashr', RwExpr.bvand', RwExpr.bvor', RwExpr.concat', RwExpr.bvsize', RwExpr.l0,
      RwExpr.l1, RwExpr.V, RwExpr.mk, RwArgs.ofList, denoteE, denoteA, spliceVal_bv, spliceVal_bool, spliceVal_list,
      List.append_nil, List.singleton_append, List.cons_append, List.nil_append, List.append_assoc,
      l0_val, l1_val, BitVec.toNat_ofNat, Nat.zero_mod, spliceVal_bvExtractEval, spliceVal_bvExtEval,
      spliceVal_bvRepeatEval, spliceVal_bvValEval, spliceVal_appVal_snoc, spliceVal_appVal_cons,
      spliceVal_appVal_two, spliceVal_appVal_append2,
      spliceVal_appVal_nonred (rfl : RwOp.reducible .eq = false),
      spliceVal_appVal_nonred (rfl : RwOp.reducible .bvsize = false),
      spliceVal_appVal_nonred (rfl : RwOp.reducible .bvsub = false),
      spliceVal_appVal_nonred (rfl : RwOp.reducible .slt = false),
      spliceVal_appVal_nonred (rfl : RwOp.reducible .sgt = false),
      spliceVal_appVal_nonred (rfl : RwOp.reducible .ult = false),
      spliceVal_appVal_nonred (rfl : RwOp.reducible .not = false),
      appVal_concat_single] $[$loc]?)

theorem mul_sext_val {n : Nat} (y : BitVec n) (k : Nat) (hn : n ≠ 0) :
    bvExtEval true (n + k) k [.bv n y] = .bv (n + k) (y.signExtend (n + k)) := by
  simp only [bvExtEval]; rw [ite_eq_left ⟨by omega, trivial⟩]; rfl

theorem mul_mul_eval {w m : Nat} (x : BitVec w) (y : BitVec m) :
    appVal .bvmul [.bv w x, .bv m y] = if h : m = w then (if w ≠ 0 then .bv w (x * y.cast h) else .bad) else .bad := by
  rw [appVal_bin2]
  simp only [RwOp.width, firstBv, RwOp.node, Op.eval, bvN, Val.bvs, Val.asBv_bv, dite_true]
  by_cases h : m = w
  · subst h; simp [BitVec.one_mul]
  · simp [h]

theorem mul_sub_eval {w m : Nat} (x : BitVec w) (y : BitVec m) :
    appVal .bvsub [.bv w x, .bv m y] = if h : m = w then (if w ≠ 0 then .bv w (x - y.cast h) else .bad) else .bad := by
  rw [appVal_bin2]
  simp only [RwOp.width, firstBv, RwOp.node, Op.eval, bvBin, Val.asBv_bv, dite_true]
  by_cases h : m = w
  · subst h; simp
  · simp [h]

theorem mul_slt_eval {w m : Nat} (x : BitVec w) (y : BitVec m) :
    appVal .slt [.bv w x, .bv m y] = if h : m = w then .bool (x.slt (y.cast h)) else .bad := by
  simp [appVal, RwOp.node, Op.eval, bvCmp]

theorem mul_sgt_eval {w m : Nat} (x : BitVec w) (y : BitVec m) :
    appVal .sgt [.bv w x, .bv m y] = if h : m = w then .bool ((y.cast h).slt x) else .bad := by
  simp [appVal, RwOp.node, Op.eval, bvCmp]

theorem mul_eq_bv_eval {w m : Nat} (x : BitVec w) (y : BitVec m) :
    appVal .eq [.bv w x, .bv m y] = if h : m = w then .bool (decide (x = y.cast h)) else .bad := by
  simp only [appVal, RwOp.node, Op.eval, eqEval, Val.eqv]
  by_cases h : m = w
  · subst h; simp
  · simp [h]

theorem mul_eq_bool_eval (a b : Bool) : appVal .eq [.bool a, .bool b] = .bool (decide (a = b)) := by
  simp [appVal, RwOp.node, Op.eval, eqEval, Val.eqv]

theorem mul_not_eval (a : Bool) : appVal .not [.bool a] = .bool (!a) := by
  simp [appVal, RwOp.reducible, RwOp.node, Op.eval, boolNotEval]

theorem mul_conj3_eval (a b c : Bool) : appVal .conj [.bool a, .bool b, .bool c] = .bool (a && b && c) := by
  simp [appVal, RwOp.node, Op.eval, boolN, Val.bools, Bool.and_assoc]

/-- The integer core: `X·A < Y·A ↔ X ≠ Y ∧ A ≠ 0 ∧ (X < Y ↔ 0 < A)`. -/
theorem mul_core (X Y A : Int) : X * A < Y * A ↔ (X ≠ Y ∧ A ≠ 0 ∧ (X < Y ↔ 0 < A)) := by
  rcases Int.lt_trichotomy 0 A with hA | hA | hA
  · rw [Int.mul_lt_mul_right hA]; omega
  · subst hA; simp
  · have h1 : X * A = -(X * -A) := by rw [Int.mul_neg, Int.neg_neg]
    have h2 : Y * A = -(Y * -A) := by rw [Int.mul_neg, Int.neg_neg]
    rw [h1, h2, Int.neg_lt_neg_iff, Int.mul_lt_mul_right (by omega)]; omega

theorem mul_sub_eq_zero {w : Nat} (x y : BitVec w) : (x - y = 0#w) ↔ x = y := by
  constructor
  · intro h; have := BitVec.sub_add_cancel x y; rw [h, BitVec.zero_add] at this; exact this.symm
  · intro h; subst h; exact BitVec.sub_self x


theorem mul_toInt_cast {w v : Nat} (h : w = v) (x : BitVec w) : (x.cast h).toInt = x.toInt := by
  subst h; simp

theorem mul_sprod_small {p q W : Nat} (y : BitVec p) (a : BitVec q) (hp : 1 ≤ p) (hq : 1 ≤ q) (h : p + q ≤ W) :
    (y.toInt * a.toInt).bmod (2 ^ W) = y.toInt * a.toInt := by
  have hy1 := @BitVec.toInt_lt p y
  have hy2 := BitVec.le_toInt y
  have ha1 := @BitVec.toInt_lt q a
  have ha2 := BitVec.le_toInt a
  have ep : (2 : Int) ^ (p - 1) = ((2 ^ (p - 1) : Nat) : Int) := by simp
  have eq : (2 : Int) ^ (q - 1) = ((2 ^ (q - 1) : Nat) : Int) := by simp
  rw [ep] at hy1 hy2; rw [eq] at ha1 ha2
  have hyN : y.toInt.natAbs ≤ 2 ^ (p - 1) := by omega
  have haN : a.toInt.natAbs ≤ 2 ^ (q - 1) := by omega
  have hPN : (y.toInt * a.toInt).natAbs ≤ 2 ^ (p - 1) * 2 ^ (q - 1) := by
    rw [Int.natAbs_mul]; exact Nat.mul_le_mul hyN haN
  have hpow : 2 ^ (p - 1) * 2 ^ (q - 1) * 4 ≤ 2 ^ W := by
    have : (4 : Nat) = 2 ^ 2 := by decide
    rw [this, ← Nat.pow_add, ← Nat.pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hWpos : 0 < 2 ^ W := Nat.two_pow_pos W
  apply Int.bmod_eq_of_le_mul_two
  · generalize 2 ^ W = M at *; generalize 2 ^ (p - 1) * 2 ^ (q - 1) = K at *
    generalize y.toInt * a.toInt = P at *; omega
  · generalize 2 ^ W = M at *; generalize 2 ^ (p - 1) * 2 ^ (q - 1) = K at *
    generalize y.toInt * a.toInt = P at *; omega

-- rewrite id 73
theorem sound_BV_MULT_SLT_MULT_1 :
    (RwRule.mk [.bvq, .bvq, .bvq, .bv 32, .bv 32, .bv 32, .bv 32]
      (some (conj' [eq' (var 5) (bvsize' (var 0)), eq' (var 6) (bvsize' (var 2)), ule' (var 6) (var 3)]))
      (slt' (bvmul' [sext (var 3) (var 1), sext (var 4) (var 2)]) (bvmul' [sext (var 3) (var 0), sext (var 4) (var 2)]))
      (conj' [not' (eq' (bvsub' (var 1) (var 0)) (symVal (l0) (var 5))), not' (eq' (var 2) (symVal (l0) (var 6))), eq' (slt' (var 1) (var 0)) (sgt' (var 2) (symVal (l0) (var 6)))])).Sound := by
  intro env henv hcond hl hr
  obtain ⟨w0, x0, h0, hw0⟩ := henv 0 .bvq rfl
  obtain ⟨w1, x1, h1, hw1⟩ := henv 1 .bvq rfl
  obtain ⟨w2, x2, h2, hw2⟩ := henv 2 .bvq rfl
  obtain ⟨k3, h3⟩ := henv 3 (.bv 32) rfl
  obtain ⟨k4, h4⟩ := henv 4 (.bv 32) rfl
  obtain ⟨k5, h5⟩ := henv 5 (.bv 32) rfl
  obtain ⟨k6, h6⟩ := henv 6 (.bv 32) rfl
  have hc := hcond _ rfl
  mul_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3, h4, h5, h6] at hc hl hr ⊢
  mul_pat at hc hl hr ⊢
  simp only [appVal_ule32] at hc
  obtain ⟨hc1, hc2, hg⟩ := conj_all3 hc
  simp only [Val.bool.injEq, BitVec.ule] at hg
  obtain ⟨hk5, _⟩ := toNat_of_bvsize hc1
  obtain ⟨hk6, _⟩ := toNat_of_bvsize hc2
  simp only [decide_eq_true_eq] at hg
  rw [hk5, hk6] at hr ⊢
  -- the two zero literals
  rcases lit_cases w0 0 with hL0 | ⟨hw0n, _, _, hL0⟩
  · rw [hL0] at hr; simp [appVal, RwOp.node, Op.eval, eqEval, Val.eqv, boolNotEval, boolN, Val.bools] at hr
  rcases lit_cases w2 0 with hL2 | ⟨hw2n, _, _, hL2⟩
  · rw [hL2] at hr; simp [appVal, RwOp.node, Op.eval, eqEval, Val.eqv, boolNotEval, boolN, Val.bools] at hr
  rw [hL0, hL2] at hr ⊢
  -- x and y have the same width
  have hw01 : w0 = w1 := by
    by_cases hw : w0 = w1
    · exact hw
    · rw [mul_sub_eval, dite_eq_right hw] at hr; simp [appVal, RwOp.node, Op.eval, eqEval, Val.eqv, boolNotEval, boolN, Val.bools] at hr
  subst hw01
  simp only [mul_sub_eval, mul_eq_bv_eval, mul_slt_eval, mul_sgt_eval, dite_true, BitVec.cast_eq, ne_eq, hw0n,
    not_false_eq_true, ite_true, mul_not_eval, mul_eq_bool_eval, mul_conj3_eval] at hr ⊢
  rw [mul_sext_val x1 _ hw0n, mul_sext_val x0 _ hw0n, mul_sext_val x2 _ hw2n] at hl ⊢
  have hW : w2 + k4.toNat = w0 + k3.toNat := by
    by_cases hW : w2 + k4.toNat = w0 + k3.toNat
    · exact hW
    · rw [mul_mul_eval, dite_eq_right hW] at hl; simp [appVal, RwOp.node, Op.eval, bvCmp] at hl
  simp only [mul_mul_eval, dite_eq_left hW, ite_eq_left (show w0 + k3.toNat ≠ 0 by omega)]
  rw [mul_slt_eval, dite_eq_left rfl, BitVec.cast_eq]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [BitVec.slt_iff_toInt_lt, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq, mul_sub_eq_zero, BitVec.toInt_mul, mul_toInt_cast, BitVec.toInt_signExtend_of_le (Nat.le_add_right _ _)]
  rw [mul_sprod_small x1 x2 (by omega) (by omega) (by omega), mul_sprod_small x0 x2 (by omega) (by omega) (by omega), ← BitVec.toInt_inj,
    ← BitVec.toInt_inj, Bool.eq_iff_iff, BitVec.slt_iff_toInt_lt, BitVec.slt_iff_toInt_lt, BitVec.toInt_zero]
  rw [mul_core, and_assoc]


theorem mul_toInt_setWidth {p W : Nat} (y : BitVec p) (h : p < W) : (y.setWidth W).toInt = y.toNat := by
  rw [BitVec.toInt_setWidth]
  have hy := y.isLt
  have hpow : 2 ^ p * 2 ≤ 2 ^ W := by rw [← Nat.pow_succ]; exact Nat.pow_le_pow_right (by decide) h
  apply Int.bmod_eq_of_le_mul_two <;>
  · generalize 2 ^ W = M at *; generalize 2 ^ p = K at *; omega

theorem mul_uprod_small {p q W : Nat} (y : BitVec p) (a : BitVec q) (hq : 1 ≤ q) (h : p + q ≤ W) :
    ((y.toNat : Int) * a.toInt).bmod (2 ^ W) = y.toNat * a.toInt := by
  have hy := y.isLt
  have ha1 := @BitVec.toInt_lt q a
  have ha2 := BitVec.le_toInt a
  have eq : (2 : Int) ^ (q - 1) = ((2 ^ (q - 1) : Nat) : Int) := by simp
  rw [eq] at ha1 ha2
  have haN : a.toInt.natAbs ≤ 2 ^ (q - 1) := by omega
  have hA := Nat.mul_le_mul hy haN
  rw [Nat.succ_mul] at hA
  have hPN : ((y.toNat : Int) * a.toInt).natAbs = y.toNat * a.toInt.natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_natCast]
  have hpow : 2 ^ p * 2 ^ (q - 1) * 2 ≤ 2 ^ W := by
    rw [← Nat.pow_add, ← Nat.pow_succ]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have hWpos := Nat.two_pow_pos W
  rcases Nat.eq_zero_or_pos a.toInt.natAbs with hz | hz
  · rw [Int.natAbs_eq_zero.mp hz]; simp
  · apply Int.bmod_eq_of_le_mul_two <;>
    · generalize 2 ^ W = M at *; generalize 2 ^ p * 2 ^ (q - 1) = K at *
      generalize (y.toNat : Int) * a.toInt = P at *; generalize y.toNat * a.toInt.natAbs = Q at *; omega

-- rewrite id 74
theorem sound_BV_MULT_SLT_MULT_2 :
    (RwRule.mk [.bvq, .bvq, .bvq, .bv 32, .bv 32, .bv 32, .bv 32]
      (some (conj' [eq' (var 5) (bvsize' (var 0)), eq' (var 6) (bvsize' (var 2)), ule' (var 6) (var 3)]))
      (slt' (bvmul' [zext (var 3) (var 1), sext (var 4) (var 2)]) (bvmul' [zext (var 3) (var 0), sext (var 4) (var 2)]))
      (conj' [not' (eq' (bvsub' (var 1) (var 0)) (symVal (l0) (var 5))), not' (eq' (var 2) (symVal (l0) (var 6))), eq' (ult' (var 1) (var 0)) (sgt' (var 2) (symVal (l0) (var 6)))])).Sound := by
  intro env henv hcond hl hr
  obtain ⟨w0, x0, h0, hw0⟩ := henv 0 .bvq rfl
  obtain ⟨w1, x1, h1, hw1⟩ := henv 1 .bvq rfl
  obtain ⟨w2, x2, h2, hw2⟩ := henv 2 .bvq rfl
  obtain ⟨k3, h3⟩ := henv 3 (.bv 32) rfl
  obtain ⟨k4, h4⟩ := henv 4 (.bv 32) rfl
  obtain ⟨k5, h5⟩ := henv 5 (.bv 32) rfl
  obtain ⟨k6, h6⟩ := henv 6 (.bv 32) rfl
  have hc := hcond _ rfl
  mul_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3, h4, h5, h6] at hc hl hr ⊢
  mul_pat at hc hl hr ⊢
  simp only [appVal_ule32] at hc
  obtain ⟨hc1, hc2, hg⟩ := conj_all3 hc
  simp only [Val.bool.injEq, BitVec.ule] at hg
  obtain ⟨hk5, _⟩ := toNat_of_bvsize hc1
  obtain ⟨hk6, _⟩ := toNat_of_bvsize hc2
  simp only [decide_eq_true_eq] at hg
  rw [hk5, hk6] at hr ⊢
  -- the two zero literals
  rcases lit_cases w0 0 with hL0 | ⟨hw0n, _, _, hL0⟩
  · rw [hL0] at hr; simp [appVal, RwOp.node, Op.eval, eqEval, Val.eqv, boolNotEval, boolN, Val.bools] at hr
  rcases lit_cases w2 0 with hL2 | ⟨hw2n, _, _, hL2⟩
  · rw [hL2] at hr; simp [appVal, RwOp.node, Op.eval, eqEval, Val.eqv, boolNotEval, boolN, Val.bools] at hr
  rw [hL0, hL2] at hr ⊢
  -- x and y have the same width
  have hw01 : w0 = w1 := by
    by_cases hw : w0 = w1
    · exact hw
    · rw [mul_sub_eval, dite_eq_right hw] at hr; simp [appVal, RwOp.node, Op.eval, eqEval, Val.eqv, boolNotEval, boolN, Val.bools] at hr
  subst hw01
  simp only [mul_sub_eval, mul_eq_bv_eval, ult_eval, mul_sgt_eval, dite_true, BitVec.cast_eq, ne_eq, hw0n,
    not_false_eq_true, ite_true, mul_not_eval, mul_eq_bool_eval, mul_conj3_eval] at hr ⊢
  rw [zext_val x1 _ hw0n, zext_val x0 _ hw0n, mul_sext_val x2 _ hw2n] at hl ⊢
  have hW : w2 + k4.toNat = w0 + k3.toNat := by
    by_cases hW : w2 + k4.toNat = w0 + k3.toNat
    · exact hW
    · rw [mul_mul_eval, dite_eq_right hW] at hl; simp [appVal, RwOp.node, Op.eval, bvCmp] at hl
  simp only [mul_mul_eval, dite_eq_left hW, ite_eq_left (show w0 + k3.toNat ≠ 0 by omega)]
  rw [mul_slt_eval, dite_eq_left rfl, BitVec.cast_eq]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [BitVec.slt_iff_toInt_lt, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq, mul_sub_eq_zero, BitVec.toInt_mul, mul_toInt_cast, BitVec.toInt_signExtend_of_le (Nat.le_add_right _ _),
    mul_toInt_setWidth _ (show w0 < w0 + k3.toNat by omega)]
  rw [mul_uprod_small x1 x2 (by omega) (by omega), mul_uprod_small x0 x2 (by omega) (by omega), ← BitVec.toNat_inj,
    ← BitVec.toInt_inj, Bool.eq_iff_iff, BitVec.slt_iff_toInt_lt, BitVec.toInt_zero, BitVec.ult, decide_eq_true_eq,
    mul_core, and_assoc]
  omega

end Bcf
