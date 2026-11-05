import Bcf.Rw.Bv

/-!
# Extraction, extension and shift-by-constant rewrites

`BV_EXTRACT_NOT`, `BV_EXTRACT_SIGN_EXTEND_2`, `BV_EQ_EXTRACT_ELIM*`,
`BV_MERGE_SIGN_EXTEND_*`, and the `BV_{SHL,LSHR,ASHR}_BY_CONST_*` rewrites
not already covered in `Rw/Bv.lean`.
-/
namespace Bcf

open RwExpr

/-! ## Helpers (all names prefixed `extr_`) -/

/-- Structural unfolding of patterns (as `rw_pat`), also unfolding `bvlshr'`, `bvnot'`, `sgt'`. -/
syntax "extr_pat" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| extr_pat $[$loc]?) => `(tactic| simp only [RwExpr.bvlshr', RwExpr.bvnot', RwExpr.sgt', RwExpr.eq', RwExpr.not', RwExpr.ult', RwExpr.ule',
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
      spliceVal_appVal_nonred (rfl : RwOp.reducible .bvnot = false),
      spliceVal_appVal_nonred (rfl : RwOp.reducible .bvshl = false),
      spliceVal_appVal_nonred (rfl : RwOp.reducible .bvlshr = false),
      spliceVal_appVal_nonred (rfl : RwOp.reducible .bvashr = false),
      appVal_concat_single] $[$loc]?)


theorem extr_lshr_eval {w m : Nat} (x : BitVec w) (y : BitVec m) :
    appVal .bvlshr [.bv w x, .bv m y] = if h : m = w then (if w ≠ 0 then .bv w (x >>> (y.cast h)) else .bad) else .bad := by
  rw [appVal_bin2]
  simp only [RwOp.width, firstBv, RwOp.node, Op.eval, bvBin, Val.asBv_bv, dite_true]
  by_cases h : m = w
  · subst h; simp
  · simp [h]

theorem extr_shift_bad {op : RwOp} {w : Nat} (x : BitVec w) : appVal op [.bv w x, .bad] = .bad := by
  cases op <;> simp [appVal, RwOp.node, Op.eval, bvBin, bvN, Val.bvs, Val.asBv, bvCmp, eqEval, Val.eqv, boolNotEval, bvUn,
    boolN, Val.bools, impliesEval, bvConcatEval, Val.concatVals, bvSizeEval]

theorem extr_not_eval {w : Nat} (x : BitVec w) :
    appVal .bvnot [.bv w x] = if w ≠ 0 then .bv w (~~~x) else .bad := by
  simp [appVal, RwOp.reducible, RwOp.node, RwOp.widthV, Val.tys, Val.ty, RwOp.width, firstBv, Op.eval, bvUn, Val.asBv]

theorem extr_sext_val {n : Nat} (y : BitVec n) (k : Nat) (hn : n ≠ 0) :
    bvExtEval true (n + k) k [.bv n y] = .bv (n + k) (y.signExtend (n + k)) := by
  simp only [bvExtEval]; rw [ite_eq_left ⟨by omega, trivial⟩]; rfl

theorem extr_eq_eval {n m : Nat} (x : BitVec n) (y : BitVec m) :
    appVal .eq [.bv n x, .bv m y] = if h : m = n then .bool (decide (x = y.cast h)) else .bad := by
  simp only [appVal, RwOp.node, Op.eval, eqEval, Val.eqv]
  by_cases h : m = n
  · subst h; simp
  · simp [h]

theorem extr_eq_bad_l (v : Val) : appVal .eq [.bad, v] = .bad := by
  simp [appVal, RwOp.node, Op.eval, eqEval, Val.eqv]

theorem extr_eq_bad_r (v : Val) : appVal .eq [v, .bad] = .bad := by
  cases v <;> simp [appVal, RwOp.node, Op.eval, eqEval, Val.eqv]

theorem extr_sgt32 (a b : BitVec 32) : appVal .sgt [.bv 32 a, .bv 32 b] = .bool (b.slt a) := by
  simp [appVal, RwOp.node, Op.eval, bvCmp]

theorem extr_conj_all5 {a b c d e : Val} (h : appVal .conj [a, b, c, d, e] = .bool true) :
    a = .bool true ∧ b = .bool true ∧ c = .bool true ∧ d = .bool true ∧ e = .bool true :=
  ⟨conjN_true h a (by simp), conjN_true h b (by simp), conjN_true h c (by simp), conjN_true h d (by simp),
   conjN_true h e (by simp)⟩

theorem extr_sext_val' {n : Nat} (y : BitVec n) (k : Nat) :
    bvExtEval true (n + k) k [.bv n y] = if n + k ≠ 0 then .bv (n + k) (y.signExtend (n + k)) else .bad := by
  simp only [bvExtEval]
  by_cases h : n + k ≠ 0
  · rw [ite_eq_left ⟨h, trivial⟩, ite_eq_left h]; rfl
  · rw [ite_eq_right (fun hh => h hh.1), ite_eq_right h]

theorem extr_zext_val' {n : Nat} (y : BitVec n) (k : Nat) :
    bvExtEval false (n + k) k [.bv n y] = if n + k ≠ 0 then .bv (n + k) (y.setWidth (n + k)) else .bad := by
  simp only [bvExtEval]
  by_cases h : n + k ≠ 0
  · rw [ite_eq_left ⟨h, trivial⟩, ite_eq_left h]; rfl
  · rw [ite_eq_right (fun hh => h hh.1), ite_eq_right h]

/-- The added conjunct `ule' (var 1) (var 3)` with `k3 = k1 + k2` says the 32-bit sum did not wrap. -/
theorem extr_add_no_wrap {k1 k2 k3 : BitVec 32} (h3 : k3 = k1 + k2) (hg : k1.ule k3 = true) :
    k3.toNat = k1.toNat + k2.toNat := by
  have hadd := BitVec.toNat_add k1 k2
  have h1 := k1.isLt
  have h2 := k2.isLt
  rw [two32] at hadd h1 h2
  simp only [BitVec.ule, decide_eq_true_eq] at hg
  rw [h3] at hg ⊢
  rw [hadd] at hg ⊢
  omega

-- rewrite id 61
theorem sound_BV_EXTRACT_NOT :
    (RwRule.mk [.bvq, .bv 32, .bv 32]
      (none)
      (extract (var 2) (var 1) (bvnot' (var 0)))
      (bvnot' (extract (var 2) (var 1) (var 0)))).Sound := by
  intro env henv _ hl hr
  obtain ⟨w0, x0, h0, hw0⟩ := henv 0 .bvq rfl
  obtain ⟨k1, h1⟩ := henv 1 (.bv 32) rfl
  obtain ⟨k2, h2⟩ := henv 2 (.bv 32) rfl
  extr_pat at hl hr ⊢
  simp only [h0, h1, h2] at hl hr ⊢
  extr_pat at hl hr ⊢
  rw [extr_not_eval] at hl ⊢
  have hw : w0 ≠ 0 := by
    intro hw; rw [ite_eq_right (by simpa using hw)] at hl; simp [bvExtractEval] at hl
  rw [ite_eq_left hw] at hl ⊢
  obtain ⟨m, y, hy, hlo, hhi, hlv⟩ := extract_of_ne_bad hl
  injection hy with e1 e2; subst e1; have := eq_of_heq e2; subst this
  rw [hlv]
  have hE : bvExtractEval k2.toNat k1.toNat [.bv w0 x0] = .bv (k2.toNat - k1.toNat + 1)
      (BitVec.extractLsb k2.toNat k1.toNat x0) := by simp [bvExtractEval, hlo, hhi]
  rw [hE, extr_not_eval, ite_eq_left (by omega)]
  congr 1
  apply bv_ext
  intro i hi
  rw [BitVec.getLsbD_extractLsb, BitVec.getLsbD_not, BitVec.getLsbD_not, BitVec.getLsbD_extractLsb,
    decide_eq_true hi, decide_eq_true (show k1.toNat + i < w0 by omega)]
  simp

-- rewrite id 63
theorem sound_BV_EXTRACT_SIGN_EXTEND_2 :
    (RwRule.mk [.bvq, .bv 32, .bv 32, .bv 32, .bv 32, .bv 32]
      (some (conj' [slt' (var 1) (bvsize' (var 0)), sge' (var 2) (bvsize' (var 0)), eq' (var 4) (bvsub' (bvsize' (var 0)) (l1)), eq' (var 5) (bvadd' [l1, bvsub' (var 2) (bvsize' (var 0))])]))
      (extract (var 2) (var 1) (sext (var 3) (var 0)))
      (sext (var 5) (extract (var 4) (var 1) (var 0)))).Sound := by
  intro env henv hcond hl hr
  obtain ⟨w0, x0, h0, hw0⟩ := henv 0 .bvq rfl
  obtain ⟨k1, h1⟩ := henv 1 (.bv 32) rfl
  obtain ⟨k2, h2⟩ := henv 2 (.bv 32) rfl
  obtain ⟨k3, h3⟩ := henv 3 (.bv 32) rfl
  obtain ⟨k4, h4⟩ := henv 4 (.bv 32) rfl
  obtain ⟨k5, h5⟩ := henv 5 (.bv 32) rfl
  have hc := hcond _ rfl
  extr_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3, h4, h5] at hc hl hr ⊢
  extr_pat at hc hl hr ⊢
  simp only [appVal_bvsize_small x0 hw0, appVal_bvsub32, appVal_bvadd32, appVal_slt32, appVal_sge32] at hc
  obtain ⟨hslt, hsge, he4, he5⟩ := conj_all4 hc
  simp only [Val.bool.injEq] at hslt hsge
  have hk4 := eq_bv32 he4
  have hk5 := eq_bv32 he5
  have hw0' : (BitVec.ofNat 32 w0).toNat = w0 := toNat_ofNat_small hw0
  obtain ⟨hw0k2, hk2s⟩ := sle_true_of_small (by rw [hw0', two31]; omega) hsge
  rw [hw0'] at hw0k2
  have hw0z : w0 ≠ 0 := by
    intro hz
    have hb : bvExtractEval k4.toNat k1.toNat [Val.bv w0 x0] = .bad := extract_bad (by omega)
    rw [hb] at hr; exact hr rfl
  -- the sign extension on the left
  rw [extr_sext_val _ _ hw0z] at hl ⊢
  obtain ⟨m1, y1, hy1, hk12, hk2w, hlv⟩ := extract_of_ne_bad hl
  injection hy1 with e1 e2; subst e1; have := eq_of_heq e2; subst this
  have hk1w : k1.toNat < w0 := by
    rw [slt_small (a := k1) (b := BitVec.ofNat 32 w0) (by omega) (by rw [hw0', two31]; omega), hw0'] at hslt
    simpa using hslt
  have h1n : (1#32 : BitVec 32).toNat = 1 := by decide
  have hk4n : k4.toNat = w0 - 1 := by rw [hk4, toNat_sub_one32 (by omega) (by omega)]
  have hsub : (k2 - BitVec.ofNat 32 w0).toNat = k2.toNat - w0 := by
    rw [toNat_sub32 (by rw [hw0']; exact hw0k2), hw0']
  have hk5n : k5.toNat = 1 + (k2.toNat - w0) := by
    rw [hk5, toNat_add32 _ _ (by rw [hsub, h1n, two32]; omega), hsub, h1n]
  -- the extraction on the right
  have hE : bvExtractEval k4.toNat k1.toNat [.bv w0 x0] = .bv (k4.toNat - k1.toNat + 1)
      (BitVec.extractLsb k4.toNat k1.toNat x0) := by simp [bvExtractEval]; omega
  rw [hE] at hr ⊢
  extr_pat at hr ⊢
  rw [extr_sext_val _ _ (by omega)]
  rw [hlv]
  apply val_ext (by omega)
  intro i hi
  rw [BitVec.getLsbD_extractLsb, decide_eq_true hi, Bool.true_and, BitVec.getLsbD_signExtend,
    BitVec.getLsbD_signExtend, decide_eq_true (show k1.toNat + i < w0 + k3.toNat by omega), Bool.true_and,
    decide_eq_true (show i < k4.toNat - k1.toNat + 1 + k5.toNat by omega), Bool.true_and]
  simp only [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_extractLsb]
  by_cases hlt : k1.toNat + i < w0
  · rw [ite_eq_left hlt, ite_eq_left (by omega), decide_eq_true (by omega)]; simp
  · rw [ite_eq_right hlt, ite_eq_right (by omega), decide_eq_true (by omega), hk4n,
      show k1.toNat + (w0 - 1 - k1.toNat + 1 - 1) = w0 - 1 by omega]; simp

-- rewrite id 104
theorem sound_BV_SHL_BY_CONST_0 :
    (RwRule.mk [.bvq, .bv 32]
      (none)
      (bvshl' (var 0) (symVal (l0) (var 1)))
      (var 0)).Sound := by
  intro env henv _ hl hr
  obtain ⟨w0, x0, h0, hw0⟩ := henv 0 .bvq rfl
  obtain ⟨k1, h1⟩ := henv 1 (.bv 32) rfl
  extr_pat at hl hr ⊢
  simp only [h0, h1] at hl hr ⊢
  extr_pat at hl hr ⊢
  rcases lit_cases k1.toNat 0 with hL | ⟨hk1, hk164, _, hL⟩
  · rw [hL, extr_shift_bad] at hl; exact absurd rfl hl
  rw [hL] at hl ⊢
  have hkw : k1.toNat = w0 := by
    by_cases hkw : k1.toNat = w0
    · exact hkw
    · rw [shl_eval, dite_eq_right hkw] at hl; exact absurd rfl hl
  rw [shl_eval, dite_eq_left hkw, ite_eq_left (by omega)]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp

-- rewrite id 106
theorem sound_BV_SHL_BY_CONST_2 :
    (RwRule.mk [.bvq, .bv 32, .bv 32, .bv 32]
      (some (conj' [sge' (var 1) (bvsize' (var 0)), eq' (var 3) (bvsize' (var 0))]))
      (bvshl' (var 0) (symVal (var 1) (var 2)))
      (symVal (l0) (var 3))).Sound := by
  intro env henv hcond hl hr
  obtain ⟨w0, x0, h0, hw0⟩ := henv 0 .bvq rfl
  obtain ⟨k1, h1⟩ := henv 1 (.bv 32) rfl
  obtain ⟨k2, h2⟩ := henv 2 (.bv 32) rfl
  obtain ⟨k3, h3⟩ := henv 3 (.bv 32) rfl
  have hc := hcond _ rfl
  extr_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3] at hc hl hr ⊢
  extr_pat at hc hl hr ⊢
  simp only [appVal_bvsize_small x0 hw0, appVal_sge32] at hc
  obtain ⟨hsge, he3⟩ := conj_all2 hc
  simp only [Val.bool.injEq] at hsge
  have hk3 := eq_bv32 he3
  have hw0' : (BitVec.ofNat 32 w0).toNat = w0 := toNat_ofNat_small hw0
  obtain ⟨hw0k1, _⟩ := sle_true_of_small (by rw [hw0', two31]; omega) hsge
  rw [hw0'] at hw0k1
  have hk3n : k3.toNat = w0 := by rw [hk3, hw0']
  rcases lit_cases k2.toNat k1.toNat with hL | ⟨hk2, hk264, hk1lt, hL⟩
  · rw [hL, extr_shift_bad] at hl; exact absurd rfl hl
  rw [hL] at hl ⊢
  have hkw : k2.toNat = w0 := by
    by_cases hkw : k2.toNat = w0
    · exact hkw
    · rw [shl_eval, dite_eq_right hkw] at hl; exact absurd rfl hl
  rw [shl_eval, dite_eq_left hkw, ite_eq_left (by omega)]
  rcases lit_cases k3.toNat 0 with hZ | ⟨_, _, _, hZ⟩
  · rw [hZ] at hr; exact absurd rfl hr
  rw [hZ]
  apply val_ext hk3n.symm
  intro i hi
  rw [BitVec.getLsbD_shiftLeft', BitVec.toNat_cast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk1lt,
    decide_eq_true (show i < k1.toNat by omega), BitVec.getLsbD_ofNat]
  simp

-- rewrite id 107
theorem sound_BV_LSHR_BY_CONST_0 :
    (RwRule.mk [.bvq, .bv 32]
      (none)
      (bvlshr' (var 0) (symVal (l0) (var 1)))
      (var 0)).Sound := by
  intro env henv _ hl hr
  obtain ⟨w0, x0, h0, hw0⟩ := henv 0 .bvq rfl
  obtain ⟨k1, h1⟩ := henv 1 (.bv 32) rfl
  extr_pat at hl hr ⊢
  simp only [h0, h1] at hl hr ⊢
  extr_pat at hl hr ⊢
  rcases lit_cases k1.toNat 0 with hL | ⟨hk1, hk164, _, hL⟩
  · rw [hL, extr_shift_bad] at hl; exact absurd rfl hl
  rw [hL] at hl ⊢
  have hkw : k1.toNat = w0 := by
    by_cases hkw : k1.toNat = w0
    · exact hkw
    · rw [extr_lshr_eval, dite_eq_right hkw] at hl; exact absurd rfl hl
  rw [extr_lshr_eval, dite_eq_left hkw, ite_eq_left (by omega)]
  simp [BitVec.ushiftRight_eq']

-- rewrite id 109
theorem sound_BV_LSHR_BY_CONST_2 :
    (RwRule.mk [.bvq, .bv 32, .bv 32]
      (some (sge' (var 1) (bvsize' (var 0))))
      (bvlshr' (var 0) (symVal (var 1) (var 2)))
      (symVal (l0) (var 2))).Sound := by
  intro env henv hcond hl hr
  obtain ⟨w0, x0, h0, hw0⟩ := henv 0 .bvq rfl
  obtain ⟨k1, h1⟩ := henv 1 (.bv 32) rfl
  obtain ⟨k2, h2⟩ := henv 2 (.bv 32) rfl
  have hc := hcond _ rfl
  extr_pat at hc hl hr ⊢
  simp only [h0, h1, h2] at hc hl hr ⊢
  extr_pat at hc hl hr ⊢
  simp only [appVal_bvsize_small x0 hw0, appVal_sge32, Val.bool.injEq] at hc
  have hw0' : (BitVec.ofNat 32 w0).toNat = w0 := toNat_ofNat_small hw0
  obtain ⟨hw0k1, _⟩ := sle_true_of_small (by rw [hw0', two31]; omega) hc
  rw [hw0'] at hw0k1
  rcases lit_cases k2.toNat k1.toNat with hL | ⟨hk2, hk264, hk1lt, hL⟩
  · rw [hL, extr_shift_bad] at hl; exact absurd rfl hl
  rw [hL] at hl ⊢
  have hkw : k2.toNat = w0 := by
    by_cases hkw : k2.toNat = w0
    · exact hkw
    · rw [extr_lshr_eval, dite_eq_right hkw] at hl; exact absurd rfl hl
  rw [extr_lshr_eval, dite_eq_left hkw, ite_eq_left (by omega)]
  rcases lit_cases k2.toNat 0 with hZ | ⟨_, _, _, hZ⟩
  · rw [hZ] at hr; exact absurd rfl hr
  rw [hZ]
  apply val_ext hkw.symm
  intro i hi
  rw [BitVec.ushiftRight_eq', BitVec.getLsbD_ushiftRight, BitVec.toNat_cast, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hk1lt, BitVec.getLsbD_of_ge _ _ (by omega), BitVec.getLsbD_ofNat]
  simp

-- rewrite id 110
theorem sound_BV_ASHR_BY_CONST_0 :
    (RwRule.mk [.bvq, .bv 32]
      (none)
      (bvashr' (var 0) (symVal (l0) (var 1)))
      (var 0)).Sound := by
  intro env henv _ hl hr
  obtain ⟨w0, x0, h0, hw0⟩ := henv 0 .bvq rfl
  obtain ⟨k1, h1⟩ := henv 1 (.bv 32) rfl
  extr_pat at hl hr ⊢
  simp only [h0, h1] at hl hr ⊢
  extr_pat at hl hr ⊢
  rcases lit_cases k1.toNat 0 with hL | ⟨hk1, hk164, _, hL⟩
  · rw [hL, extr_shift_bad] at hl; exact absurd rfl hl
  rw [hL] at hl ⊢
  have hkw : k1.toNat = w0 := by
    by_cases hkw : k1.toNat = w0
    · exact hkw
    · rw [ashr_eval, dite_eq_right hkw] at hl; exact absurd rfl hl
  rw [ashr_eval, dite_eq_left hkw, ite_eq_left (by omega)]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp

-- rewrite id 112
theorem sound_BV_ASHR_BY_CONST_2 :
    (RwRule.mk [.bvq, .bv 32, .bv 32, .bv 32, .bv 32]
      (some (conj' [sge' (var 1) (bvsize' (var 0)), eq' (var 3) (bvsub' (bvsize' (var 0)) (l1)), eq' (var 4) (bvsize' (var 0))]))
      (bvashr' (var 0) (symVal (var 1) (var 2)))
      («repeat» (var 4) (extract (var 3) (var 3) (var 0)))).Sound := by
  intro env henv hcond hl hr
  obtain ⟨w0, x0, h0, hw0⟩ := henv 0 .bvq rfl
  obtain ⟨k1, h1⟩ := henv 1 (.bv 32) rfl
  obtain ⟨k2, h2⟩ := henv 2 (.bv 32) rfl
  obtain ⟨k3, h3⟩ := henv 3 (.bv 32) rfl
  obtain ⟨k4, h4⟩ := henv 4 (.bv 32) rfl
  have hc := hcond _ rfl
  extr_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3, h4] at hc hl hr ⊢
  extr_pat at hc hl hr ⊢
  simp only [appVal_bvsize_small x0 hw0, appVal_bvsub32, appVal_sge32] at hc
  obtain ⟨hsge, he3, he4⟩ := conj_all3 hc
  simp only [Val.bool.injEq] at hsge
  have hk3 := eq_bv32 he3
  have hk4 := eq_bv32 he4
  have hw0' : (BitVec.ofNat 32 w0).toNat = w0 := toNat_ofNat_small hw0
  obtain ⟨hw0k1, _⟩ := sle_true_of_small (by rw [hw0', two31]; omega) hsge
  rw [hw0'] at hw0k1
  have hk4n : k4.toNat = w0 := by rw [hk4, hw0']
  -- the shift amount
  rcases lit_cases k2.toNat k1.toNat with hL | ⟨hk2, hk264, hk1lt, hL⟩
  · rw [hL, extr_shift_bad] at hl; exact absurd rfl hl
  rw [hL] at hl ⊢
  have hkw : k2.toNat = w0 := by
    by_cases hkw : k2.toNat = w0
    · exact hkw
    · rw [ashr_eval, dite_eq_right hkw] at hl; exact absurd rfl hl
  rw [ashr_eval, dite_eq_left hkw, ite_eq_left (by omega)]
  -- the sign-bit extraction
  have hk3w : k3.toNat < w0 := by
    by_cases hk3w : k3.toNat < w0
    · exact hk3w
    · rw [extract_bad (by omega)] at hr; exact absurd rfl hr
  have hE33 : bvExtractEval k3.toNat k3.toNat [.bv w0 x0] = .bv (k3.toNat - k3.toNat + 1)
      (BitVec.extractLsb k3.toNat k3.toNat x0) := by simp [bvExtractEval, hk3w]
  rw [hE33] at hr ⊢
  simp only at hr ⊢
  obtain ⟨n, rv, hrv⟩ := repeat_isBv hr
  obtain ⟨hn, hrbits⟩ := repeat_bits hrv
  simp only [Nat.sub_self, Nat.zero_add, Nat.one_mul] at hn hrbits
  have hk3n : k3.toNat = w0 - 1 := by rw [hk3, toNat_sub_one32 (by omega) (by omega)]
  rw [hrv]
  apply val_ext (by omega)
  intro i hi
  rw [BitVec.toNat_cast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk1lt, BitVec.getLsbD_sshiftRight, hrbits,
    decide_eq_false (show ¬ w0 ≤ i by omega), Bool.not_false, Bool.true_and,
    ite_eq_right (show ¬ k1.toNat + i < w0 by omega), decide_eq_true (show i < k4.toNat by omega), Bool.true_and,
    Nat.mod_one, BitVec.getLsbD_extractLsb, BitVec.msb_eq_getLsbD_last, hk3n]
  simp

-- rewrite id 58
theorem sound_BV_EQ_EXTRACT_ELIM1 :
    (RwRule.mk [.bvq, .bvq, .bv 32, .bv 32, .bv 32, .bv 32, .bv 32]
      (some (conj' [eq' (var 4) (bvsub' (bvsize' (var 0)) (l1)), eq' (var 5) (bvadd' [var 3, l1]), eq' (var 6) (bvsub' (var 2) (l1)), sgt' (var 4) (var 3), sgt' (var 2) (l0)]))
      (eq' (extract (var 3) (var 2) (var 0)) (var 1))
      (eq' (var 0) (concat' [extract (var 4) (var 5) (var 0), var 1, extract (var 6) (l0) (var 0)]))).Sound := by
  intro env henv hcond hl hr
  obtain ⟨w0, x0, h0, hw0⟩ := henv 0 .bvq rfl
  obtain ⟨w1, y1, h1, hw1⟩ := henv 1 .bvq rfl
  obtain ⟨k2, h2⟩ := henv 2 (.bv 32) rfl
  obtain ⟨k3, h3⟩ := henv 3 (.bv 32) rfl
  obtain ⟨k4, h4⟩ := henv 4 (.bv 32) rfl
  obtain ⟨k5, h5⟩ := henv 5 (.bv 32) rfl
  obtain ⟨k6, h6⟩ := henv 6 (.bv 32) rfl
  have hc := hcond _ rfl
  extr_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3, h4, h5, h6] at hc hl hr ⊢
  extr_pat at hc hl hr ⊢
  simp only [appVal_bvsize_small x0 hw0, appVal_bvsub32, appVal_bvadd32, extr_sgt32] at hc
  obtain ⟨he4, he5, he6, hs43, hs20⟩ := extr_conj_all5 hc
  simp only [Val.bool.injEq] at hs43 hs20
  have hk4 := eq_bv32 he4
  have hk5 := eq_bv32 he5
  have hk6 := eq_bv32 he6
  have hw0' : (BitVec.ofNat 32 w0).toNat = w0 := toNat_ofNat_small hw0
  -- left-hand side
  obtain ⟨m, y, hy, hk23, hk3w, hlv⟩ := extract_of_ne_bad (v := Val.bv w0 x0) (hi := k3.toNat) (lo := k2.toNat)
    (by intro hb; rw [hb, extr_eq_bad_l] at hl; exact hl rfl)
  injection hy with e1 e2; subst e1; have := eq_of_heq e2; subst this
  rw [hlv] at hl ⊢
  have hw1e : w1 = k3.toNat - k2.toNat + 1 := by
    by_cases h : w1 = k3.toNat - k2.toNat + 1
    · exact h
    · rw [extr_eq_eval, dite_eq_right h] at hl; exact absurd rfl hl
  rw [extr_eq_eval, dite_eq_left hw1e]
  -- arithmetic
  have hk4n : k4.toNat = w0 - 1 := by rw [hk4, toNat_sub_one32 (by omega) (by omega)]
  have hk3s : k3.toNat < w0 - 1 := by
    rw [slt_small (a := k3) (b := k4) (by omega) (by omega), hk4n] at hs43; simpa using hs43
  have hk2p : 0 < k2.toNat := by
    rw [slt_small (a := BitVec.ofNat 32 0) (b := k2) (by simp) (by omega)] at hs20; simpa using hs20
  have h1n : (1#32 : BitVec 32).toNat = 1 := by decide
  have hk5n : k5.toNat = k3.toNat + 1 := by rw [hk5, toNat_add32 _ _ (by rw [h1n, two32]; omega), h1n]
  have hk6n : k6.toNat = k2.toNat - 1 := by rw [hk6, toNat_sub32 (by rw [h1n]; omega), h1n]
  -- right-hand side
  have hcne : appVal .concat [bvExtractEval k4.toNat k5.toNat [Val.bv w0 x0], Val.bv w1 y1,
      bvExtractEval k6.toNat 0 [Val.bv w0 x0]] ≠ .bad := by
    intro hb; rw [hb, extr_eq_bad_r] at hr; exact hr rfl
  obtain ⟨n, cx, hC, hall, hn, hcbits⟩ := appVal_concat_bits hcne (fun v hv => by simp at hv)
  obtain ⟨nA, a, hA⟩ := hall _ (by apply List.mem_cons_self)
  obtain ⟨nB, b, hB⟩ := hall _ (by simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨m0, y0, hy0, hk54, hk4w, hAv⟩ := extract_of_ne_bad (by rw [hA]; simp : bvExtractEval k4.toNat k5.toNat _ ≠ .bad)
  injection hy0 with e1 e2; subst e1; have := eq_of_heq e2; subst this
  obtain ⟨m0, y0, hy0, _, hk6w, hBv⟩ := extract_of_ne_bad (by rw [hB]; simp : bvExtractEval k6.toNat 0 _ ≠ .bad)
  injection hy0 with e1 e2; subst e1; have := eq_of_heq e2; subst this
  rw [hAv, hBv] at hC hn hcbits hr ⊢
  rw [hC] at hr ⊢
  have hnw : n = w0 := by
    by_cases h : n = w0
    · exact h
    · rw [extr_eq_eval, dite_eq_right h] at hr; exact absurd rfl hr
  rw [extr_eq_eval, dite_eq_left hnw]
  congr 1
  apply decide_eq_decide.mpr
  simp only [catW, catBit, Nat.add_zero, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero] at hcbits hn
  constructor
  · intro hE
    have hy : ∀ j, y1.getLsbD j = (decide (j < k3.toNat - k2.toNat + 1) && x0.getLsbD (k2.toNat + j)) := by
      intro j
      have := congrArg (fun z => z.getLsbD j) hE
      simp only [BitVec.getLsbD_cast, BitVec.getLsbD_extractLsb] at this
      exact this.symm
    apply bv_ext
    intro i hi
    rw [BitVec.getLsbD_cast, hcbits]
    simp only [BitVec.getLsbD_extractLsb, hy, Nat.zero_add]
    split
    · rename_i h1
      split
      · rename_i h2; rw [decide_eq_true (by omega)]; simp
      · rename_i h2; rw [decide_eq_true (by omega), show k2.toNat + (i - (k6.toNat + 1)) = i by omega]; simp
    · rename_i h1; rw [decide_eq_true (by omega), show k5.toNat + (i - (w1 + (k6.toNat + 1))) = i by omega]; simp
  · intro hx
    apply bv_ext
    intro j hj
    have := congrArg (fun z => z.getLsbD (k2.toNat + j)) hx
    simp only [BitVec.getLsbD_cast, hcbits] at this
    rw [ite_eq_left (by omega), ite_eq_right (by omega), show k2.toNat + j - (k6.toNat + 1) = j by omega] at this
    rw [BitVec.getLsbD_cast, BitVec.getLsbD_extractLsb, decide_eq_true hj, Bool.true_and, this]

-- rewrite id 59
theorem sound_BV_EQ_EXTRACT_ELIM2 :
    (RwRule.mk [.bvq, .bvq, .bv 32, .bv 32, .bv 32]
      (some (conj' [eq' (var 3) (bvsub' (bvsize' (var 0)) (l1)), eq' (var 4) (bvadd' [var 2, l1]), sgt' (var 3) (var 2)]))
      (eq' (extract (var 2) (l0) (var 0)) (var 1))
      (eq' (var 0) (concat' [extract (var 3) (var 4) (var 0), var 1]))).Sound := by
  intro env henv hcond hl hr
  obtain ⟨w0, x0, h0, hw0⟩ := henv 0 .bvq rfl
  obtain ⟨w1, y1, h1, hw1⟩ := henv 1 .bvq rfl
  obtain ⟨k2, h2⟩ := henv 2 (.bv 32) rfl
  obtain ⟨k3, h3⟩ := henv 3 (.bv 32) rfl
  obtain ⟨k4, h4⟩ := henv 4 (.bv 32) rfl
  have hc := hcond _ rfl
  extr_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3, h4] at hc hl hr ⊢
  extr_pat at hc hl hr ⊢
  simp only [appVal_bvsize_small x0 hw0, appVal_bvsub32, appVal_bvadd32, extr_sgt32] at hc
  obtain ⟨he3, he4, hs32⟩ := conj_all3 hc
  simp only [Val.bool.injEq] at hs32
  have hk3 := eq_bv32 he3
  have hk4 := eq_bv32 he4
  have hw0' : (BitVec.ofNat 32 w0).toNat = w0 := toNat_ofNat_small hw0
  -- left-hand side
  obtain ⟨m, y, hy, _, hk2w, hlv⟩ := extract_of_ne_bad (v := Val.bv w0 x0) (hi := k2.toNat) (lo := 0)
    (by intro hb; rw [hb, extr_eq_bad_l] at hl; exact hl rfl)
  injection hy with e1 e2; subst e1; have := eq_of_heq e2; subst this
  rw [hlv] at hl ⊢
  have hw1e : w1 = k2.toNat - 0 + 1 := by
    by_cases h : w1 = k2.toNat - 0 + 1
    · exact h
    · rw [extr_eq_eval, dite_eq_right h] at hl; exact absurd rfl hl
  rw [extr_eq_eval, dite_eq_left hw1e]
  -- arithmetic
  have hk3n : k3.toNat = w0 - 1 := by rw [hk3, toNat_sub_one32 (by omega) (by omega)]
  have hk2s : k2.toNat < w0 - 1 := by
    rw [slt_small (a := k2) (b := k3) (by omega) (by omega), hk3n] at hs32; simpa using hs32
  have h1n : (1#32 : BitVec 32).toNat = 1 := by decide
  have hk4n : k4.toNat = k2.toNat + 1 := by rw [hk4, toNat_add32 _ _ (by rw [h1n, two32]; omega), h1n]
  -- right-hand side
  have hcne : appVal .concat [bvExtractEval k3.toNat k4.toNat [Val.bv w0 x0], Val.bv w1 y1] ≠ .bad := by
    intro hb; rw [hb, extr_eq_bad_r] at hr; exact hr rfl
  obtain ⟨n, cx, hC, hall, hn, hcbits⟩ := appVal_concat_bits hcne (fun v hv => by simp at hv)
  obtain ⟨nA, a, hA⟩ := hall _ (by apply List.mem_cons_self)
  obtain ⟨m0, y0, hy0, hk43, hk3w, hAv⟩ := extract_of_ne_bad (by rw [hA]; simp : bvExtractEval k3.toNat k4.toNat _ ≠ .bad)
  injection hy0 with e1 e2; subst e1; have := eq_of_heq e2; subst this
  rw [hAv] at hC hn hcbits hr ⊢
  rw [hC] at hr ⊢
  have hnw : n = w0 := by
    by_cases h : n = w0
    · exact h
    · rw [extr_eq_eval, dite_eq_right h] at hr; exact absurd rfl hr
  rw [extr_eq_eval, dite_eq_left hnw]
  congr 1
  apply decide_eq_decide.mpr
  simp only [catW, catBit, Nat.add_zero, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero] at hcbits hn
  constructor
  · intro hE
    have hy : ∀ j, y1.getLsbD j = (decide (j < k2.toNat - 0 + 1) && x0.getLsbD (0 + j)) := by
      intro j
      have := congrArg (fun z => z.getLsbD j) hE
      simp only [BitVec.getLsbD_cast, BitVec.getLsbD_extractLsb] at this
      exact this.symm
    apply bv_ext
    intro i hi
    rw [BitVec.getLsbD_cast, hcbits]
    simp only [BitVec.getLsbD_extractLsb, hy, Nat.zero_add, Nat.sub_zero]
    split
    · rename_i h1; rw [decide_eq_true (by omega)]; simp
    · rename_i h1; rw [decide_eq_true (by omega), show k4.toNat + (i - w1) = i by omega]; simp
  · intro hx
    apply bv_ext
    intro j hj
    have := congrArg (fun z => z.getLsbD j) hx
    simp only [BitVec.getLsbD_cast, hcbits] at this
    rw [ite_eq_left (by omega)] at this
    rw [BitVec.getLsbD_cast, BitVec.getLsbD_extractLsb, decide_eq_true hj, Bool.true_and, Nat.zero_add, this]

-- rewrite id 60
theorem sound_BV_EQ_EXTRACT_ELIM3 :
    (RwRule.mk [.bvq, .bvq, .bv 32, .bv 32, .bv 32]
      (some (conj' [eq' (var 3) (bvsub' (bvsize' (var 0)) (l1)), eq' (var 4) (bvsub' (var 2) (l1)), sgt' (var 2) (l0)]))
      (eq' (extract (var 3) (var 2) (var 0)) (var 1))
      (eq' (var 0) (concat' [var 1, extract (var 4) (l0) (var 0)]))).Sound := by
  intro env henv hcond hl hr
  obtain ⟨w0, x0, h0, hw0⟩ := henv 0 .bvq rfl
  obtain ⟨w1, y1, h1, hw1⟩ := henv 1 .bvq rfl
  obtain ⟨k2, h2⟩ := henv 2 (.bv 32) rfl
  obtain ⟨k3, h3⟩ := henv 3 (.bv 32) rfl
  obtain ⟨k4, h4⟩ := henv 4 (.bv 32) rfl
  have hc := hcond _ rfl
  extr_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3, h4] at hc hl hr ⊢
  extr_pat at hc hl hr ⊢
  simp only [appVal_bvsize_small x0 hw0, appVal_bvsub32, extr_sgt32] at hc
  obtain ⟨he3, he4, hs20⟩ := conj_all3 hc
  simp only [Val.bool.injEq] at hs20
  have hk3 := eq_bv32 he3
  have hk4 := eq_bv32 he4
  have hw0' : (BitVec.ofNat 32 w0).toNat = w0 := toNat_ofNat_small hw0
  -- left-hand side
  obtain ⟨m, y, hy, hk23, hk3w, hlv⟩ := extract_of_ne_bad (v := Val.bv w0 x0) (hi := k3.toNat) (lo := k2.toNat)
    (by intro hb; rw [hb, extr_eq_bad_l] at hl; exact hl rfl)
  injection hy with e1 e2; subst e1; have := eq_of_heq e2; subst this
  rw [hlv] at hl ⊢
  have hw1e : w1 = k3.toNat - k2.toNat + 1 := by
    by_cases h : w1 = k3.toNat - k2.toNat + 1
    · exact h
    · rw [extr_eq_eval, dite_eq_right h] at hl; exact absurd rfl hl
  rw [extr_eq_eval, dite_eq_left hw1e]
  -- arithmetic
  have hk3n : k3.toNat = w0 - 1 := by rw [hk3, toNat_sub_one32 (by omega) (by omega)]
  have hk2p : 0 < k2.toNat := by
    rw [slt_small (a := BitVec.ofNat 32 0) (b := k2) (by simp) (by omega)] at hs20; simpa using hs20
  have h1n : (1#32 : BitVec 32).toNat = 1 := by decide
  have hk4n : k4.toNat = k2.toNat - 1 := by rw [hk4, toNat_sub32 (by rw [h1n]; omega), h1n]
  -- right-hand side
  have hcne : appVal .concat [Val.bv w1 y1, bvExtractEval k4.toNat 0 [Val.bv w0 x0]] ≠ .bad := by
    intro hb; rw [hb, extr_eq_bad_r] at hr; exact hr rfl
  obtain ⟨n, cx, hC, hall, hn, hcbits⟩ := appVal_concat_bits hcne (fun v hv => by simp at hv)
  obtain ⟨nB, b, hB⟩ := hall _ (by simp only [List.mem_cons]; exact Or.inr (Or.inl rfl))
  obtain ⟨m0, y0, hy0, _, hk4w, hBv⟩ := extract_of_ne_bad (by rw [hB]; simp : bvExtractEval k4.toNat 0 _ ≠ .bad)
  injection hy0 with e1 e2; subst e1; have := eq_of_heq e2; subst this
  rw [hBv] at hC hn hcbits hr ⊢
  rw [hC] at hr ⊢
  have hnw : n = w0 := by
    by_cases h : n = w0
    · exact h
    · rw [extr_eq_eval, dite_eq_right h] at hr; exact absurd rfl hr
  rw [extr_eq_eval, dite_eq_left hnw]
  congr 1
  apply decide_eq_decide.mpr
  simp only [catW, catBit, Nat.add_zero, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero] at hcbits hn
  constructor
  · intro hE
    have hy : ∀ j, y1.getLsbD j = (decide (j < k3.toNat - k2.toNat + 1) && x0.getLsbD (k2.toNat + j)) := by
      intro j
      have := congrArg (fun z => z.getLsbD j) hE
      simp only [BitVec.getLsbD_cast, BitVec.getLsbD_extractLsb] at this
      exact this.symm
    apply bv_ext
    intro i hi
    rw [BitVec.getLsbD_cast, hcbits]
    simp only [BitVec.getLsbD_extractLsb, hy, Nat.zero_add, Nat.sub_zero]
    split
    · rename_i h1; rw [decide_eq_true (by omega)]; simp
    · rename_i h1; rw [decide_eq_true (by omega), show k2.toNat + (i - (k4.toNat + 1)) = i by omega]; simp
  · intro hx
    apply bv_ext
    intro j hj
    have := congrArg (fun z => z.getLsbD (k2.toNat + j)) hx
    simp only [BitVec.getLsbD_cast, hcbits] at this
    rw [ite_eq_right (by omega), show k2.toNat + j - (k4.toNat + 1) = j by omega] at this
    rw [BitVec.getLsbD_cast, BitVec.getLsbD_extractLsb, decide_eq_true hj, Bool.true_and, this]

-- rewrite id 140
-- conjunct added: the condition computes `V3 = V1 + V2` in 32 bits; when the sum wraps the two
-- sides have different widths (e.g. V1 = V2 = 2^31, V3 = 0).  `V1 ≤u V3` says the sum did not wrap.
theorem sound_BV_MERGE_SIGN_EXTEND_1 :
    (RwRule.mk [.bvq, .bv 32, .bv 32, .bv 32]
      (some (conj' [eq' (var 3) (bvadd' [var 1, var 2]), ule' (var 1) (var 3)]))
      (sext (var 1) (sext (var 2) (var 0)))
      (sext (var 3) (var 0))).Sound := by
  intro env henv hcond hl hr
  obtain ⟨w0, x0, h0, hw0⟩ := henv 0 .bvq rfl
  obtain ⟨k1, h1⟩ := henv 1 (.bv 32) rfl
  obtain ⟨k2, h2⟩ := henv 2 (.bv 32) rfl
  obtain ⟨k3, h3⟩ := henv 3 (.bv 32) rfl
  have hc := hcond _ rfl
  extr_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3] at hc hl hr ⊢
  extr_pat at hc hl hr ⊢
  simp only [appVal_bvadd32, appVal_ule32] at hc
  obtain ⟨hce, hgd⟩ := conj_all2 hc
  simp only [Val.bool.injEq] at hgd
  have hk3 := extr_add_no_wrap (eq_bv32 hce) hgd
  rw [extr_sext_val' x0 k2.toNat] at hl ⊢
  rw [extr_sext_val' x0 k3.toNat] at hr ⊢
  by_cases hz : w0 + k2.toNat ≠ 0
  · rw [ite_eq_left hz] at hl ⊢
    extr_pat at hl ⊢
    rw [extr_sext_val', ite_eq_left (by omega)] at hl ⊢
    rw [ite_eq_left (show w0 + k3.toNat ≠ 0 by omega)]
    apply val_ext (by omega)
    intro i hi
    simp only [BitVec.getLsbD_signExtend, BitVec.msb_eq_getLsbD_last]
    rw [decide_eq_true hi, decide_eq_true (show i < w0 + k3.toNat by omega), Bool.true_and, Bool.true_and]
    by_cases hi0 : i < w0
    · rw [ite_eq_left (by omega), ite_eq_left hi0, decide_eq_true (show i < w0 + k2.toNat by omega), Bool.true_and]
    · rw [ite_eq_right hi0]
      by_cases hi1 : i < w0 + k2.toNat
      · rw [ite_eq_left hi1, decide_eq_true hi1, Bool.true_and]
      · rw [ite_eq_right hi1, decide_eq_true (show w0 + k2.toNat - 1 < w0 + k2.toNat by omega), Bool.true_and]
        by_cases hk2z : k2.toNat = 0
        · rw [ite_eq_left (by omega), hk2z, Nat.add_zero]
        · rw [ite_eq_right (by omega)]
  · rw [ite_eq_right hz] at hl
    exact absurd rfl hl

-- rewrite id 141
-- conjunct added for the same reason as rewrite 140 (e.g. V1 = 2^32 - 1, V2 = 1, V3 = 0).
theorem sound_BV_MERGE_SIGN_EXTEND_2 :
    (RwRule.mk [.bvq, .bv 32, .bv 32, .bv 32]
      (some (conj' [sgt' (var 2) (l0), eq' (var 3) (bvadd' [var 1, var 2]), ule' (var 1) (var 3)]))
      (sext (var 1) (zext (var 2) (var 0)))
      (zext (var 3) (var 0))).Sound := by
  intro env henv hcond hl hr
  obtain ⟨w0, x0, h0, hw0⟩ := henv 0 .bvq rfl
  obtain ⟨k1, h1⟩ := henv 1 (.bv 32) rfl
  obtain ⟨k2, h2⟩ := henv 2 (.bv 32) rfl
  obtain ⟨k3, h3⟩ := henv 3 (.bv 32) rfl
  have hc := hcond _ rfl
  extr_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3] at hc hl hr ⊢
  extr_pat at hc hl hr ⊢
  simp only [appVal_bvadd32, appVal_ule32, extr_sgt32] at hc
  obtain ⟨hs20, he3, hgd⟩ := conj_all3 hc
  simp only [Val.bool.injEq] at hs20 hgd
  have hk3 := extr_add_no_wrap (eq_bv32 he3) hgd
  have hk2p : 0 < k2.toNat := by
    have hk2s : k2.toNat < 2 ^ 31 := by
      by_cases hs : k2.toNat < 2 ^ 31
      · exact hs
      · exfalso
        have hm : k2.msb = true := by rw [BitVec.msb_eq_decide]; simp; omega
        have h0m : (0#32 : BitVec 32).msb = false := by decide
        simp only [BitVec.slt, BitVec.toInt_eq_msb_cond, hm, h0m, Bool.false_eq_true, ↓reduceIte] at hs20
        simp at hs20
        omega
    rw [slt_small (a := 0#32) (b := k2) (by simp) hk2s] at hs20; simpa using hs20
  rw [extr_zext_val' x0 k2.toNat, ite_eq_left (by omega)] at hl ⊢
  rw [extr_zext_val' x0 k3.toNat, ite_eq_left (by omega)] at hr ⊢
  extr_pat at hl ⊢
  rw [extr_sext_val', ite_eq_left (by omega)] at hl ⊢
  apply val_ext (by omega)
  intro i hi
  simp only [BitVec.getLsbD_signExtend, BitVec.getLsbD_setWidth, BitVec.msb_setWidth]
  rw [decide_eq_true hi, decide_eq_true (show i < w0 + k3.toNat by omega), Bool.true_and, Bool.true_and]
  by_cases hi1 : i < w0 + k2.toNat
  · rw [ite_eq_left hi1, decide_eq_true hi1, Bool.true_and]
  · rw [ite_eq_right hi1, BitVec.getLsbD_of_ge _ _ (by omega), BitVec.getLsbD_of_ge _ _ (by omega)]
    simp

/-! # Rewrite soundness, group G9: `BV_LSHR_BY_CONST_1` -/



-- rewrite id 108
theorem sound_BV_LSHR_BY_CONST_1 :
    (RwRule.mk [.bvq, .bv 32, .bv 32, .bv 32]
      (some (conj' [slt' (var 1) (bvsize' (var 0)), eq' (var 3) (bvsub' (bvsize' (var 0)) (l1))]))
      (bvlshr' (var 0) (symVal (var 1) (var 2)))
      (concat' [symVal (l0) (var 1), extract (var 3) (var 1) (var 0)])).Sound := by
  intro env henv hcond hl hr
  obtain ⟨w0, x0, h0, hw0⟩ := henv 0 .bvq rfl
  obtain ⟨k1, h1⟩ := henv 1 (.bv 32) rfl
  obtain ⟨k2, h2⟩ := henv 2 (.bv 32) rfl
  obtain ⟨k3, h3⟩ := henv 3 (.bv 32) rfl
  have hc := hcond _ rfl
  extr_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3] at hc hl hr ⊢
  extr_pat at hc hl hr ⊢
  simp only [appVal_bvsize_small x0 hw0, appVal_bvsub32, appVal_slt32] at hc
  obtain ⟨hslt, he3⟩ := conj_all2 hc
  simp only [Val.bool.injEq] at hslt
  have hk3 := eq_bv32 he3
  have hw0' : (BitVec.ofNat 32 w0).toNat = w0 := toNat_ofNat_small hw0
  -- the shift amount
  rcases lit_cases k2.toNat k1.toNat with hL | ⟨hk2, hk264, hk1lt, hL⟩
  · rw [hL, extr_shift_bad] at hl; exact absurd rfl hl
  rw [hL] at hl ⊢
  have hkw : k2.toNat = w0 := by
    by_cases hkw : k2.toNat = w0
    · exact hkw
    · rw [extr_lshr_eval, dite_eq_right (by simpa using hkw)] at hl; exact absurd rfl hl
  rw [extr_lshr_eval, dite_eq_left hkw, ite_eq_left (by omega)] at hl ⊢
  -- the right-hand side
  obtain ⟨n, rv, hrv, hall, hn, hrbits⟩ := appVal_concat_bits hr (fun v hv => by simp at hv)
  obtain ⟨nZ, z, hZ⟩ := hall _ (by apply List.mem_cons_self)
  obtain ⟨nE, e, hE⟩ := hall _ (by simp only [List.mem_cons]; exact Or.inr (Or.inl rfl))
  obtain ⟨w0, y0, hy0, hk13, hk3w, hEv⟩ := extract_of_ne_bad (by rw [hE]; simp : bvExtractEval k3.toNat k1.toNat _ ≠ .bad)
  injection hy0 with e1 e2; subst e1; have := eq_of_heq e2; subst this
  rcases lit_cases k1.toNat 0 with hZ' | ⟨hk10, hk164, _, hZv⟩
  · rw [hZ'] at hZ; simp at hZ
  rw [hEv] at hE; rw [hZv] at hZ
  injection hE with hnE he; subst hnE; have := eq_of_heq he; subst this
  injection hZ with hnZ hz; subst hnZ; have := eq_of_heq hz; subst this
  rw [hEv, hZv] at hn hrbits
  -- arithmetic
  have hk1w : k1.toNat < w0 := by
    rw [slt_small (by omega) (by rw [hw0', two31]; omega), hw0'] at hslt; simpa using hslt
  have hk3n : k3.toNat = w0 - 1 := by rw [hk3, toNat_sub_one32 (by omega) (by omega)]
  rw [hrv]
  apply val_ext (by rw [hn]; simp only [catW]; omega)
  intro i hi
  have hcast : ((BitVec.ofNat k2.toNat k1.toNat).cast hkw).toNat = k1.toNat := by
    simp only [BitVec.toNat_cast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk1lt]
  rw [BitVec.ushiftRight_eq', hcast, BitVec.getLsbD_ushiftRight, hrbits]
  simp only [catW, catBit, Nat.add_zero, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
  by_cases hik : i < k3.toNat - k1.toNat + 1
  · rw [ite_eq_left hik, BitVec.getLsbD_extractLsb, decide_eq_true hik]; simp [Nat.add_comm]
  · rw [ite_eq_right hik, BitVec.getLsbD_ofNat, BitVec.getLsbD_of_ge x0 _ (by omega)]; simp

end Bcf
