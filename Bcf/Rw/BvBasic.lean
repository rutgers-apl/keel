import Bcf.Rw.Bv

/-!
# Basic bit-vector rewrites

Commutativity, self-comparisons, shifts of zero, `bvnot`/`bvxor` identities,
the `*_ELIMINATE` comparison rewrites and the `EQ_*_SOLVE` rules.
-/
namespace Bcf

open RwExpr

/-! ## Helpers -/

/-- Structural unfolding of patterns, keeping operator applications folded
(`rw_pat` extended with the helper names the shared macros leave alone). -/
syntax "basic_pat" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| basic_pat $[$loc]?) => `(tactic| simp only [RwExpr.eq', RwExpr.neq', RwExpr.not', RwExpr.ult', RwExpr.ule',
      RwExpr.slt', RwExpr.sle', RwExpr.sge', RwExpr.conj', RwExpr.bvsub', RwExpr.bvadd', RwExpr.bvmul',
      RwExpr.bvshl', RwExpr.bvashr', RwExpr.bvand', RwExpr.bvor', RwExpr.concat', RwExpr.bvsize', RwExpr.l0,
      RwExpr.l1, RwExpr.implies', RwExpr.disj', RwExpr.ugt', RwExpr.uge', RwExpr.sgt', RwExpr.bvneg',
      RwExpr.bvnot', RwExpr.bvlshr', RwExpr.bvxor', RwExpr.bvudiv', RwExpr.bvurem',
      RwExpr.V, RwExpr.mk, RwArgs.ofList, denoteE, denoteA, spliceVal_bv, spliceVal_bool, spliceVal_list,
      List.append_nil, List.singleton_append, List.cons_append, List.nil_append, List.append_assoc,
      l0_val, l1_val, BitVec.toNat_ofNat, Nat.zero_mod, spliceVal_bvExtractEval, spliceVal_bvExtEval,
      spliceVal_bvRepeatEval, spliceVal_bvValEval, spliceVal_appVal_snoc, spliceVal_appVal_cons,
      spliceVal_appVal_two, spliceVal_appVal_append2,
      spliceVal_appVal_nonred (rfl : RwOp.reducible .eq = false),
      spliceVal_appVal_nonred (rfl : RwOp.reducible .neq = false),
      spliceVal_appVal_nonred (rfl : RwOp.reducible .not = false),
      spliceVal_appVal_nonred (rfl : RwOp.reducible .bvsize = false),
      spliceVal_appVal_nonred (rfl : RwOp.reducible .bvsub = false),
      spliceVal_appVal_nonred (rfl : RwOp.reducible .bvneg = false),
      spliceVal_appVal_nonred (rfl : RwOp.reducible .bvnot = false),
      spliceVal_appVal_nonred (rfl : RwOp.reducible .bvshl = false),
      spliceVal_appVal_nonred (rfl : RwOp.reducible .bvlshr = false),
      spliceVal_appVal_nonred (rfl : RwOp.reducible .bvashr = false),
      spliceVal_appVal_nonred (rfl : RwOp.reducible .bvudiv = false),
      spliceVal_appVal_nonred (rfl : RwOp.reducible .bvurem = false),
      spliceVal_appVal_nonred (rfl : RwOp.reducible .ult = false),
      spliceVal_appVal_nonred (rfl : RwOp.reducible .ule = false),
      spliceVal_appVal_nonred (rfl : RwOp.reducible .ugt = false),
      spliceVal_appVal_nonred (rfl : RwOp.reducible .uge = false),
      spliceVal_appVal_nonred (rfl : RwOp.reducible .slt = false),
      spliceVal_appVal_nonred (rfl : RwOp.reducible .sle = false),
      spliceVal_appVal_nonred (rfl : RwOp.reducible .sgt = false),
      spliceVal_appVal_nonred (rfl : RwOp.reducible .sge = false),
      appVal_concat_single] $[$loc]?)

/-- Any operator applied to a `bad` argument is `bad`. -/
theorem basic_bad1 (op : RwOp) : appVal op [.bad] = .bad := by
  cases op <;> simp [appVal, RwOp.reducible, RwOp.node, Op.eval, bvUn, bvBin, bvCmp, eqEval,
    boolNotEval, impliesEval, bvSizeEval]

theorem basic_bad2l (op : RwOp) (v : Val) : appVal op [.bad, v] = .bad := by
  cases op <;> cases v <;> simp [appVal, RwOp.node, Op.eval, bvUn, bvBin, bvN, bvCmp, eqEval, Val.eqv,
    boolNotEval, impliesEval, boolN, Val.bools, Val.bvs, bvConcatEval, Val.concatVals, bvSizeEval]

theorem basic_bad2r (op : RwOp) (v : Val) : appVal op [v, .bad] = .bad := by
  cases op <;> cases v <;> simp [appVal, RwOp.node, Op.eval, bvUn, bvBin, bvN, bvCmp, eqEval, Val.eqv,
    boolNotEval, impliesEval, boolN, Val.bools, Val.bvs, bvConcatEval, Val.concatVals, bvSizeEval]

/-- Unary bit-vector operators on a value. -/
theorem basic_bvnot_val {w : Nat} (x : BitVec w) :
    appVal .bvnot [.bv w x] = if w ≠ 0 then .bv w (~~~x) else .bad := by
  simp [appVal, RwOp.reducible, RwOp.node, Op.eval, bvUn, RwOp.widthV, RwOp.width, firstBv]

theorem basic_bvneg_val {w : Nat} (x : BitVec w) :
    appVal .bvneg [.bv w x] = if w ≠ 0 then .bv w (-x) else .bad := by
  simp [appVal, RwOp.reducible, RwOp.node, Op.eval, bvUn, RwOp.widthV, RwOp.width, firstBv]

/-- Binary bit-vector operators on two values. -/
theorem basic_bvxor_val {w m : Nat} (x : BitVec w) (y : BitVec m) :
    appVal .bvxor [.bv w x, .bv m y] =
      if h : m = w then (if w ≠ 0 then .bv w (x ^^^ y.cast h) else .bad) else .bad := by
  rw [appVal_bin2]
  simp only [RwOp.width, firstBv, RwOp.node, Op.eval, bvN, Val.bvs, Val.asBv_bv, dite_true]
  by_cases h : m = w
  · subst h; simp
  · simp [h]

theorem basic_bvadd_val {w m : Nat} (x : BitVec w) (y : BitVec m) :
    appVal .bvadd [.bv w x, .bv m y] =
      if h : m = w then (if w ≠ 0 then .bv w (x + y.cast h) else .bad) else .bad := by
  rw [appVal_bin2]
  simp only [RwOp.width, firstBv, RwOp.node, Op.eval, bvN, Val.bvs, Val.asBv_bv, dite_true]
  by_cases h : m = w
  · subst h; simp
  · simp [h]

theorem basic_bvsub_val {w m : Nat} (x : BitVec w) (y : BitVec m) :
    appVal .bvsub [.bv w x, .bv m y] =
      if h : m = w then (if w ≠ 0 then .bv w (x - y.cast h) else .bad) else .bad := by
  rw [appVal_bin2]
  simp only [RwOp.width, firstBv, RwOp.node, Op.eval, bvBin, Val.asBv_bv, dite_true]
  by_cases h : m = w
  · subst h; simp
  · simp [h]

theorem basic_lshr_val {w m : Nat} (x : BitVec w) (y : BitVec m) :
    appVal .bvlshr [.bv w x, .bv m y] =
      if h : m = w then (if w ≠ 0 then .bv w (x >>> y.cast h) else .bad) else .bad := by
  rw [appVal_bin2]
  simp only [RwOp.width, firstBv, RwOp.node, Op.eval, bvBin, Val.asBv_bv, dite_true]
  by_cases h : m = w
  · subst h; simp
  · simp [h]

theorem basic_udiv_val {w m : Nat} (x : BitVec w) (y : BitVec m) :
    appVal .bvudiv [.bv w x, .bv m y] =
      if h : m = w then (if w ≠ 0 then .bv w (x.smtUDiv (y.cast h)) else .bad) else .bad := by
  rw [appVal_bin2]
  simp only [RwOp.width, firstBv, RwOp.node, Op.eval, bvBin, Val.asBv_bv, dite_true]
  by_cases h : m = w
  · subst h; simp
  · simp [h]

theorem basic_urem_val {w m : Nat} (x : BitVec w) (y : BitVec m) :
    appVal .bvurem [.bv w x, .bv m y] =
      if h : m = w then (if w ≠ 0 then .bv w (x % y.cast h) else .bad) else .bad := by
  rw [appVal_bin2]
  simp only [RwOp.width, firstBv, RwOp.node, Op.eval, bvBin, Val.asBv_bv, dite_true]
  by_cases h : m = w
  · subst h; simp
  · simp [h]

/-- Equality of two bit-vector values / two boolean values. -/
theorem basic_eq_val {w m : Nat} (x : BitVec w) (y : BitVec m) :
    appVal .eq [.bv w x, .bv m y] = if h : m = w then .bool (decide (x = y.cast h)) else .bad := by
  simp only [appVal, Bool.false_eq_true, ↓reduceIte, RwOp.node, Op.eval, eqEval, Val.eqv]
  by_cases h : m = w
  · subst h; simp
  · simp [h]

theorem basic_neq_val {w m : Nat} (x : BitVec w) (y : BitVec m) :
    appVal .neq [.bv w x, .bv m y] = if h : m = w then .bool (!decide (x = y.cast h)) else .bad := by
  simp only [appVal, ↓reduceIte, RwOp.node, Op.eval, eqEval, Val.eqv]
  by_cases h : m = w
  · subst h; simp
  · simp [h]

theorem basic_eq_bool (a b : Bool) : appVal .eq [.bool a, .bool b] = .bool (decide (a = b)) := by
  simp [appVal, RwOp.node, Op.eval, eqEval, Val.eqv]

/-- Comparisons on two bit-vector values. -/
theorem basic_cmp_val {w m : Nat} (op : RwOp) (f : {n : Nat} → BitVec n → BitVec n → Bool)
    (hop : ∀ n vs, Op.eval (fun _ => 0) (op.node n) vs = bvCmp f vs)
    (x : BitVec w) (y : BitVec m) :
    appVal op [.bv w x, .bv m y] = if h : m = w then .bool (f x (y.cast h)) else .bad := by
  simp only [appVal, hop, bvCmp]

theorem basic_ult_val {w m : Nat} (x : BitVec w) (y : BitVec m) :
    appVal .ult [.bv w x, .bv m y] = if h : m = w then .bool (x.ult (y.cast h)) else .bad :=
  basic_cmp_val .ult BitVec.ult (fun _ _ => rfl) x y
theorem basic_ule_val {w m : Nat} (x : BitVec w) (y : BitVec m) :
    appVal .ule [.bv w x, .bv m y] = if h : m = w then .bool (x.ule (y.cast h)) else .bad :=
  basic_cmp_val .ule BitVec.ule (fun _ _ => rfl) x y
theorem basic_slt_val {w m : Nat} (x : BitVec w) (y : BitVec m) :
    appVal .slt [.bv w x, .bv m y] = if h : m = w then .bool (x.slt (y.cast h)) else .bad :=
  basic_cmp_val .slt BitVec.slt (fun _ _ => rfl) x y
theorem basic_sle_val {w m : Nat} (x : BitVec w) (y : BitVec m) :
    appVal .sle [.bv w x, .bv m y] = if h : m = w then .bool (x.sle (y.cast h)) else .bad :=
  basic_cmp_val .sle BitVec.sle (fun _ _ => rfl) x y
theorem basic_ugt_val {w m : Nat} (x : BitVec w) (y : BitVec m) :
    appVal .ugt [.bv w x, .bv m y] = if h : m = w then .bool ((y.cast h).ult x) else .bad :=
  basic_cmp_val .ugt (fun x y => y.ult x) (fun _ _ => rfl) x y
theorem basic_uge_val {w m : Nat} (x : BitVec w) (y : BitVec m) :
    appVal .uge [.bv w x, .bv m y] = if h : m = w then .bool ((y.cast h).ule x) else .bad :=
  basic_cmp_val .uge (fun x y => y.ule x) (fun _ _ => rfl) x y
theorem basic_sgt_val {w m : Nat} (x : BitVec w) (y : BitVec m) :
    appVal .sgt [.bv w x, .bv m y] = if h : m = w then .bool ((y.cast h).slt x) else .bad :=
  basic_cmp_val .sgt (fun x y => y.slt x) (fun _ _ => rfl) x y
theorem basic_sge_val {w m : Nat} (x : BitVec w) (y : BitVec m) :
    appVal .sge [.bv w x, .bv m y] = if h : m = w then .bool ((y.cast h).sle x) else .bad :=
  basic_cmp_val .sge (fun x y => y.sle x) (fun _ _ => rfl) x y

/-- Bit-vector facts. -/
theorem basic_ult_allOnes {w : Nat} (x : BitVec w) :
    x.ult (BitVec.allOnes w) = !decide (x = BitVec.allOnes w) := by
  by_cases h : x = BitVec.allOnes w
  · subst h; simp [BitVec.ult]
  · simp only [h, decide_false, Bool.not_false]
    exact BitVec.ult_iff_lt.mpr (BitVec.lt_allOnes_iff.mpr h)

theorem basic_ofNat_allOnes (w : Nat) : BitVec.ofNat w (2 ^ w - 1) = BitVec.allOnes w := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_allOnes]
  exact Nat.mod_eq_of_lt (by have := Nat.two_pow_pos w; omega)

theorem basic_not_xor_not {w : Nat} (x y : BitVec w) : ~~~x ^^^ ~~~y = x ^^^ y := by
  apply bv_ext; intro i hi; simp [hi]

theorem basic_ne_not {w : Nat} (hw : w ≠ 0) (x : BitVec w) : decide (x = ~~~x) = false := by
  simp only [decide_eq_false_iff_not]
  intro h
  have := congrArg (·.getLsbD 0) h
  simp [hw] at this

theorem basic_xor_solve {w : Nat} (x y z : BitVec w) : decide (x ^^^ y = z) = decide (x = z ^^^ y) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro h; rw [← h, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  · intro h; rw [h, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem basic_not_solve {w : Nat} (x y : BitVec w) : decide (~~~x = y) = decide (x = ~~~y) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro h; rw [← h, BitVec.not_not]
  · intro h; rw [h, BitVec.not_not]

/-! ## The rules -/

-- rewrite id 75
theorem sound_BV_COMMUTATIVE_XOR :
    (RwRule.mk [.bvq, .bvq]
      (none)
      (bvxor' [var 0, var 1])
      (bvxor' [var 1, var 0])).Sound := by
  intro env henv _ hl hr
  obtain ⟨w, x, hx, hwb⟩ := henv 0 .bvq rfl
  obtain ⟨w', y, hy, hwb'⟩ := henv 1 .bvq rfl
  basic_pat at hl hr ⊢
  simp only [hx, hy] at hl hr ⊢
  basic_pat at hl hr ⊢
  by_cases h : w' = w
  · subst w'
    by_cases hw : w = 0
    · subst hw; simp [basic_bvxor_val] at hl
    · simp [basic_bvxor_val, hw, BitVec.xor_comm]
  · simp [basic_bvxor_val, h] at hl

-- rewrite id 76
theorem sound_BV_ZERO_EXTEND_ELIMINATE_0 :
    (RwRule.mk [.bvq]
      (none)
      (zext (l0) (var 0))
      (var 0)).Sound := by
  intro env henv _ hl hr
  obtain ⟨w, x, hx, hwb⟩ := henv 0 .bvq rfl
  basic_pat at hl hr ⊢
  simp only [hx] at hl hr ⊢
  basic_pat at hl hr ⊢
  by_cases hw : w = 0
  · subst hw; simp [bvExtEval] at hl
  · simp [bvExtEval, hw]

-- rewrite id 77
theorem sound_BV_SIGN_EXTEND_ELIMINATE_0 :
    (RwRule.mk [.bvq]
      (none)
      (sext (l0) (var 0))
      (var 0)).Sound := by
  intro env henv _ hl hr
  obtain ⟨w, x, hx, hwb⟩ := henv 0 .bvq rfl
  basic_pat at hl hr ⊢
  simp only [hx] at hl hr ⊢
  basic_pat at hl hr ⊢
  by_cases hw : w = 0
  · subst hw; simp [bvExtEval] at hl
  · simp [bvExtEval, hw]

-- rewrite id 78
theorem sound_BV_NOT_NEQ :
    (RwRule.mk [.bvq]
      (some (sgt' (bvsize' (var 0)) (l0)))
      (eq' (var 0) (bvnot' (var 0)))
      (ff)).Sound := by
  intro env henv hcond hl hr
  obtain ⟨w, x, hx, hwb⟩ := henv 0 .bvq rfl
  have hc := hcond _ rfl
  basic_pat at hc hl hr ⊢
  simp only [hx] at hc hl hr ⊢
  basic_pat at hc hl hr ⊢
  rw [appVal_bvsize_small x hwb, basic_sgt_val] at hc
  simp only [↓reduceDIte, BitVec.cast_eq, Val.bool.injEq] at hc
  rw [slt_small (by simp) (by rw [toNat_ofNat_small hwb]; omega)] at hc
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, toNat_ofNat_small hwb, decide_eq_true_eq] at hc
  have hw : w ≠ 0 := by omega
  simp only [basic_bvnot_val, ne_eq, hw, not_false_eq_true, ↓reduceIte, basic_eq_val, ↓reduceDIte, BitVec.cast_eq,
    basic_ne_not hw]

-- rewrite id 79
theorem sound_BV_ULT_ONES :
    (RwRule.mk [.bvq, .bv 32, .bv 32]
      (some (eq' (var 1) (bvmax (var 2))))
      (ult' (var 0) (symVal (var 1) (var 2)))
      (neq' (var 0) (symVal (var 1) (var 2)))).Sound := by
  intro env henv hcond hl hr
  obtain ⟨w, x, hx, hwb⟩ := henv 0 .bvq rfl
  obtain ⟨k1, hk1⟩ := henv 1 (.bv 32) rfl
  obtain ⟨k2, hk2⟩ := henv 2 (.bv 32) rfl
  have hc := hcond _ rfl
  basic_pat at hc hl hr ⊢
  simp only [hx, hk1, hk2] at hc hl hr ⊢
  basic_pat at hc hl hr ⊢
  have e := eq_true hc
  generalize hn : k2.toNat = n at e hl hr ⊢
  lit_cases hlit : bvValEval n (2 ^ n - 1) []
  · obtain rfl := bvValEval_width hlit
    rw [hlit] at e
    injection e with hw32 e
    subst hw32
    obtain ⟨rfl, _, _, _⟩ := bvValEval_val hlit
    have e := eq_of_heq e
    subst e
    have hv : (2 ^ 32 - 1) % 2 ^ 32 = 2 ^ 32 - 1 := Nat.mod_eq_of_lt (by decide)
    simp only [BitVec.toNat_ofNat, hv] at hl hr ⊢
    simp only [hlit, basic_ult_val, basic_neq_val] at hl hr ⊢
    by_cases h : 32 = w
    · subst h
      simp only [↓reduceDIte, BitVec.cast_eq, basic_ofNat_allOnes, basic_ult_allOnes]
    · simp [h] at hl
  · rw [hlit] at e; exact absurd e (by simp)

-- rewrite id 81
theorem sound_BV_COMMUTATIVE_ADD :
    (RwRule.mk [.bvq, .bvq]
      (none)
      (bvadd' [var 0, var 1])
      (bvadd' [var 1, var 0])).Sound := by
  intro env henv _ hl hr
  obtain ⟨w, x, hx, hwb⟩ := henv 0 .bvq rfl
  obtain ⟨w', y, hy, hwb'⟩ := henv 1 .bvq rfl
  basic_pat at hl hr ⊢
  simp only [hx, hy] at hl hr ⊢
  basic_pat at hl hr ⊢
  by_cases h : w' = w
  · subst w'
    by_cases hw : w = 0
    · subst hw; simp [basic_bvadd_val] at hl
    · simp [basic_bvadd_val, hw, BitVec.add_comm]
  · simp [basic_bvadd_val, h] at hl

-- rewrite id 82
theorem sound_BV_SUB_ELIMINATE :
    (RwRule.mk [.bvq, .bvq]
      (none)
      (bvsub' (var 0) (var 1))
      (bvadd' [var 0, bvneg' (var 1)])).Sound := by
  intro env henv _ hl hr
  obtain ⟨w, x, hx, hwb⟩ := henv 0 .bvq rfl
  obtain ⟨w', y, hy, hwb'⟩ := henv 1 .bvq rfl
  basic_pat at hl hr ⊢
  simp only [hx, hy] at hl hr ⊢
  basic_pat at hl hr ⊢
  by_cases h : w' = w
  · subst w'
    by_cases hw : w = 0
    · subst hw; simp [basic_bvsub_val] at hl
    · simp [basic_bvsub_val, basic_bvneg_val, basic_bvadd_val, hw, BitVec.sub_eq_add_neg]
  · simp [basic_bvsub_val, h] at hl

-- rewrite id 85
theorem sound_BV_EQ_XOR_SOLVE :
    (RwRule.mk [.bvq, .bvq, .bvq]
      (none)
      (eq' (eq' (bvxor' [var 0, var 1]) (var 2)) (eq' (var 0) (bvxor' [var 2, var 1])))
      (tt)).Sound := by
  intro env henv _ hl hr
  obtain ⟨w, x, hx, hwb⟩ := henv 0 .bvq rfl
  obtain ⟨w', y, hy, hwb'⟩ := henv 1 .bvq rfl
  obtain ⟨w'', z, hz, hwb''⟩ := henv 2 .bvq rfl
  basic_pat at hl hr ⊢
  simp only [hx, hy, hz] at hl hr ⊢
  basic_pat at hl hr ⊢
  by_cases h1 : w' = w
  · subst w'
    by_cases hw : w = 0
    · subst hw; simp [basic_bvxor_val, basic_bad2l] at hl
    · by_cases h2 : w'' = w
      · subst w''
        simp only [basic_bvxor_val, ↓reduceDIte, BitVec.cast_eq, ne_eq, hw, not_false_eq_true, ↓reduceIte,
          basic_eq_val, basic_eq_bool, basic_xor_solve, decide_true]
      · simp [basic_bvxor_val, hw, basic_eq_val, h2, basic_bad2l] at hl
  · simp [basic_bvxor_val, h1, basic_bad2l] at hl

-- rewrite id 86
theorem sound_BV_EQ_NOT_SOLVE :
    (RwRule.mk [.bvq, .bvq]
      (none)
      (eq' (eq' (bvnot' (var 0)) (var 1)) (eq' (var 0) (bvnot' (var 1))))
      (tt)).Sound := by
  intro env henv _ hl hr
  obtain ⟨w, x, hx, hwb⟩ := henv 0 .bvq rfl
  obtain ⟨w', y, hy, hwb'⟩ := henv 1 .bvq rfl
  basic_pat at hl hr ⊢
  simp only [hx, hy] at hl hr ⊢
  basic_pat at hl hr ⊢
  by_cases hw : w = 0
  · subst hw; simp [basic_bvnot_val, basic_bad2l] at hl
  · by_cases h1 : w' = w
    · subst w'
      simp only [basic_bvnot_val, ne_eq, hw, not_false_eq_true, ↓reduceIte, basic_eq_val, ↓reduceDIte,
        BitVec.cast_eq, basic_eq_bool, basic_not_solve, decide_true]
    · simp [basic_bvnot_val, hw, basic_eq_val, h1, basic_bad2l] at hl

-- rewrite id 87
theorem sound_BV_UGT_ELIMINATE :
    (RwRule.mk [.bvq, .bvq]
      (none)
      (ugt' (var 0) (var 1))
      (ult' (var 1) (var 0))).Sound := by
  intro env henv _ hl hr
  obtain ⟨w, x, hx, hwb⟩ := henv 0 .bvq rfl
  obtain ⟨w', y, hy, hwb'⟩ := henv 1 .bvq rfl
  basic_pat at hl hr ⊢
  simp only [hx, hy] at hl hr ⊢
  basic_pat at hl hr ⊢
  by_cases h : w' = w
  · subst w'; simp [basic_ugt_val, basic_ult_val]
  · simp [basic_ugt_val, h] at hl

-- rewrite id 88
theorem sound_BV_UGE_ELIMINATE :
    (RwRule.mk [.bvq, .bvq]
      (none)
      (uge' (var 0) (var 1))
      (ule' (var 1) (var 0))).Sound := by
  intro env henv _ hl hr
  obtain ⟨w, x, hx, hwb⟩ := henv 0 .bvq rfl
  obtain ⟨w', y, hy, hwb'⟩ := henv 1 .bvq rfl
  basic_pat at hl hr ⊢
  simp only [hx, hy] at hl hr ⊢
  basic_pat at hl hr ⊢
  by_cases h : w' = w
  · subst w'; simp [basic_uge_val, basic_ule_val]
  · simp [basic_uge_val, h] at hl

-- rewrite id 89
theorem sound_BV_SGT_ELIMINATE :
    (RwRule.mk [.bvq, .bvq]
      (none)
      (sgt' (var 0) (var 1))
      (slt' (var 1) (var 0))).Sound := by
  intro env henv _ hl hr
  obtain ⟨w, x, hx, hwb⟩ := henv 0 .bvq rfl
  obtain ⟨w', y, hy, hwb'⟩ := henv 1 .bvq rfl
  basic_pat at hl hr ⊢
  simp only [hx, hy] at hl hr ⊢
  basic_pat at hl hr ⊢
  by_cases h : w' = w
  · subst w'; simp [basic_sgt_val, basic_slt_val]
  · simp [basic_sgt_val, h] at hl

-- rewrite id 90
theorem sound_BV_SGE_ELIMINATE :
    (RwRule.mk [.bvq, .bvq]
      (none)
      (sge' (var 0) (var 1))
      (sle' (var 1) (var 0))).Sound := by
  intro env henv _ hl hr
  obtain ⟨w, x, hx, hwb⟩ := henv 0 .bvq rfl
  obtain ⟨w', y, hy, hwb'⟩ := henv 1 .bvq rfl
  basic_pat at hl hr ⊢
  simp only [hx, hy] at hl hr ⊢
  basic_pat at hl hr ⊢
  by_cases h : w' = w
  · subst w'; simp [basic_sge_val, basic_sle_val]
  · simp [basic_sge_val, h] at hl

-- rewrite id 122
theorem sound_BV_XOR_DUPLICATE :
    (RwRule.mk [.bvq, .bv 32]
      (some (eq' (var 1) (bvsize' (var 0))))
      (bvxor' [var 0, var 0])
      (symVal (l0) (var 1))).Sound := by
  intro env henv hcond hl hr
  obtain ⟨w, x, hx, hwb⟩ := henv 0 .bvq rfl
  obtain ⟨k, hk⟩ := henv 1 (.bv 32) rfl
  have hc := hcond _ rfl
  basic_pat at hc hl hr ⊢
  simp only [hx, hk] at hc hl hr ⊢
  basic_pat at hc hl hr ⊢
  obtain ⟨hkw, _⟩ := toNat_of_bvsize hc
  rw [hkw] at hr ⊢
  lit_cases hlit : bvValEval w 0 []
  · obtain rfl := bvValEval_width hlit
    obtain ⟨rfl, hw0, _, _⟩ := bvValEval_val hlit
    rw [basic_bvxor_val]
    simp [hw0, BitVec.xor_self]
  · exact absurd hlit hr

-- rewrite id 125
theorem sound_BV_XOR_NOT :
    (RwRule.mk [.bvq, .bvq]
      (none)
      (bvxor' [bvnot' (var 0), bvnot' (var 1)])
      (bvxor' [var 0, var 1])).Sound := by
  intro env henv _ hl hr
  obtain ⟨w, x, hx, hwb⟩ := henv 0 .bvq rfl
  obtain ⟨w', y, hy, hwb'⟩ := henv 1 .bvq rfl
  basic_pat at hl hr ⊢
  simp only [hx, hy] at hl hr ⊢
  basic_pat at hl hr ⊢
  by_cases h : w' = w
  · subst w'
    by_cases hw : w = 0
    · subst hw; simp [basic_bvxor_val] at hr
    · simp only [basic_bvxor_val, basic_bvnot_val, ne_eq, hw, not_false_eq_true, ↓reduceIte, ↓reduceDIte,
        BitVec.cast_eq, basic_not_xor_not]
  · simp [basic_bvxor_val, h] at hr

-- rewrite id 126
theorem sound_BV_NOT_IDEMP :
    (RwRule.mk [.bvq]
      (none)
      (bvnot' (bvnot' (var 0)))
      (var 0)).Sound := by
  intro env henv _ hl hr
  obtain ⟨w, x, hx, hwb⟩ := henv 0 .bvq rfl
  basic_pat at hl hr ⊢
  simp only [hx] at hl hr ⊢
  basic_pat at hl hr ⊢
  by_cases hw : w = 0
  · subst hw; simp [basic_bvnot_val, basic_bad1] at hl
  · simp [basic_bvnot_val, hw]

-- rewrite id 129
theorem sound_BV_ULT_SELF :
    (RwRule.mk [.bvq]
      (none)
      (ult' (var 0) (var 0))
      (ff)).Sound := by
  intro env henv _ hl hr
  obtain ⟨w, x, hx, hwb⟩ := henv 0 .bvq rfl
  basic_pat at hl hr ⊢
  simp only [hx] at hl hr ⊢
  basic_pat at hl hr ⊢
  simp [basic_ult_val, BitVec.ult]

-- rewrite id 130
theorem sound_BV_LT_SELF :
    (RwRule.mk [.bvq]
      (none)
      (slt' (var 0) (var 0))
      (ff)).Sound := by
  intro env henv _ hl hr
  obtain ⟨w, x, hx, hwb⟩ := henv 0 .bvq rfl
  basic_pat at hl hr ⊢
  simp only [hx] at hl hr ⊢
  basic_pat at hl hr ⊢
  simp [basic_slt_val, BitVec.slt]

-- rewrite id 131
theorem sound_BV_ULE_SELF :
    (RwRule.mk [.bvq]
      (none)
      (ule' (var 0) (var 0))
      (tt)).Sound := by
  intro env henv _ hl hr
  obtain ⟨w, x, hx, hwb⟩ := henv 0 .bvq rfl
  basic_pat at hl hr ⊢
  simp only [hx] at hl hr ⊢
  basic_pat at hl hr ⊢
  simp [basic_ule_val, BitVec.ule]

-- rewrite id 133
theorem sound_BV_ZERO_ULE :
    (RwRule.mk [.bvq, .bv 32]
      (none)
      (ule' (symVal (l0) (var 1)) (var 0))
      (tt)).Sound := by
  intro env henv _ hl hr
  obtain ⟨w, x, hx, hwb⟩ := henv 0 .bvq rfl
  obtain ⟨k, hk⟩ := henv 1 (.bv 32) rfl
  basic_pat at hl hr ⊢
  simp only [hx, hk] at hl hr ⊢
  basic_pat at hl hr ⊢
  lit_cases hlit : bvValEval k.toNat 0 []
  · simp only [hlit] at hl ⊢
    obtain rfl := bvValEval_width hlit
    obtain ⟨rfl, _, _, _⟩ := bvValEval_val hlit
    rw [basic_ule_val] at hl ⊢
    by_cases h : w = k.toNat
    · subst h; simp [BitVec.ule]
    · simp [h] at hl
  · simp [hlit, basic_bad2l] at hl

-- rewrite id 134
theorem sound_BV_SLE_SELF :
    (RwRule.mk [.bvq]
      (none)
      (sle' (var 0) (var 0))
      (tt)).Sound := by
  intro env henv _ hl hr
  obtain ⟨w, x, hx, hwb⟩ := henv 0 .bvq rfl
  basic_pat at hl hr ⊢
  simp only [hx] at hl hr ⊢
  basic_pat at hl hr ⊢
  simp [basic_sle_val, BitVec.sle]

-- rewrite id 136
theorem sound_BV_SHL_ZERO :
    (RwRule.mk [.bvq, .bv 32]
      (none)
      (bvshl' (symVal (l0) (var 1)) (var 0))
      (symVal (l0) (var 1))).Sound := by
  intro env henv _ hl hr
  obtain ⟨w, x, hx, hwb⟩ := henv 0 .bvq rfl
  obtain ⟨k, hk⟩ := henv 1 (.bv 32) rfl
  basic_pat at hl hr ⊢
  simp only [hx, hk] at hl hr ⊢
  basic_pat at hl hr ⊢
  lit_cases hlit : bvValEval k.toNat 0 []
  · simp only [hlit] at hl ⊢
    obtain rfl := bvValEval_width hlit
    obtain ⟨rfl, hw0, _, _⟩ := bvValEval_val hlit
    rw [shl_eval] at hl ⊢
    by_cases h : w = k.toNat
    · subst h; simp [hw0]
    · simp [h] at hl
  · simp [hlit, basic_bad2l] at hl

-- rewrite id 137
theorem sound_BV_LSHR_ZERO :
    (RwRule.mk [.bvq, .bv 32]
      (none)
      (bvlshr' (symVal (l0) (var 1)) (var 0))
      (symVal (l0) (var 1))).Sound := by
  intro env henv _ hl hr
  obtain ⟨w, x, hx, hwb⟩ := henv 0 .bvq rfl
  obtain ⟨k, hk⟩ := henv 1 (.bv 32) rfl
  basic_pat at hl hr ⊢
  simp only [hx, hk] at hl hr ⊢
  basic_pat at hl hr ⊢
  lit_cases hlit : bvValEval k.toNat 0 []
  · simp only [hlit] at hl ⊢
    obtain rfl := bvValEval_width hlit
    obtain ⟨rfl, hw0, _, _⟩ := bvValEval_val hlit
    rw [basic_lshr_val] at hl ⊢
    by_cases h : w = k.toNat
    · subst h; simp [hw0]
    · simp [h] at hl
  · simp [hlit, basic_bad2l] at hl

-- rewrite id 138
theorem sound_BV_ASHR_ZERO :
    (RwRule.mk [.bvq, .bv 32]
      (none)
      (bvashr' (symVal (l0) (var 1)) (var 0))
      (symVal (l0) (var 1))).Sound := by
  intro env henv _ hl hr
  obtain ⟨w, x, hx, hwb⟩ := henv 0 .bvq rfl
  obtain ⟨k, hk⟩ := henv 1 (.bv 32) rfl
  basic_pat at hl hr ⊢
  simp only [hx, hk] at hl hr ⊢
  basic_pat at hl hr ⊢
  lit_cases hlit : bvValEval k.toNat 0 []
  · simp only [hlit] at hl ⊢
    obtain rfl := bvValEval_width hlit
    obtain ⟨rfl, hw0, _, _⟩ := bvValEval_val hlit
    rw [ashr_eval] at hl ⊢
    by_cases h : w = k.toNat
    · subst h; simp [hw0]
    · simp [h] at hl
  · simp [hlit, basic_bad2l] at hl

-- rewrite id 161
theorem sound_BV_UDIV_ONE :
    (RwRule.mk [.bvq, .bv 32]
      (none)
      (bvudiv' (var 0) (symVal (l1) (var 1)))
      (var 0)).Sound := by
  intro env henv _ hl hr
  obtain ⟨w, x, hx, hwb⟩ := henv 0 .bvq rfl
  obtain ⟨k, hk⟩ := henv 1 (.bv 32) rfl
  basic_pat at hl hr ⊢
  simp only [hx, hk] at hl hr ⊢
  basic_pat at hl hr ⊢
  lit_cases hlit : bvValEval k.toNat 1 []
  · simp only [hlit] at hl ⊢
    obtain rfl := bvValEval_width hlit
    obtain ⟨rfl, hw0, _, _⟩ := bvValEval_val hlit
    rw [basic_udiv_val] at hl ⊢
    by_cases h : k.toNat = w
    · subst h; simp [hw0, BitVec.smtUDiv]
    · simp [h] at hl
  · simp [hlit, basic_bad2r] at hl

-- rewrite id 162
theorem sound_BV_UDIV_ZERO :
    (RwRule.mk [.bvq, .bv 32]
      (none)
      (bvudiv' (var 0) (symVal (l0) (var 1)))
      (bvnot' (symVal (l0) (var 1)))).Sound := by
  intro env henv _ hl hr
  obtain ⟨w, x, hx, hwb⟩ := henv 0 .bvq rfl
  obtain ⟨k, hk⟩ := henv 1 (.bv 32) rfl
  basic_pat at hl hr ⊢
  simp only [hx, hk] at hl hr ⊢
  basic_pat at hl hr ⊢
  lit_cases hlit : bvValEval k.toNat 0 []
  · simp only [hlit] at hl hr ⊢
    obtain rfl := bvValEval_width hlit
    obtain ⟨rfl, hw0, _, _⟩ := bvValEval_val hlit
    rw [basic_udiv_val] at hl ⊢
    rw [basic_bvnot_val]
    by_cases h : k.toNat = w
    · subst h; simp [hw0, BitVec.smtUDiv]
    · simp [h] at hl
  · simp [hlit, basic_bad2r] at hl

-- rewrite id 163
theorem sound_BV_UREM_ONE :
    (RwRule.mk [.bvq, .bv 32]
      (none)
      (bvurem' (var 0) (symVal (l1) (var 1)))
      (symVal (l0) (var 1))).Sound := by
  intro env henv _ hl hr
  obtain ⟨w, x, hx, hwb⟩ := henv 0 .bvq rfl
  obtain ⟨k, hk⟩ := henv 1 (.bv 32) rfl
  basic_pat at hl hr ⊢
  simp only [hx, hk] at hl hr ⊢
  basic_pat at hl hr ⊢
  lit_cases hlit : bvValEval k.toNat 1 []
  · simp only [hlit] at hl ⊢
    obtain rfl := bvValEval_width hlit
    obtain ⟨rfl, hw0, _, _⟩ := bvValEval_val hlit
    rcases lit_cases k.toNat 0 with hZ | ⟨_, _, _, hZ⟩
    · rw [hZ] at hr; exact absurd rfl hr
    rw [basic_urem_val] at hl ⊢
    rw [hZ]
    by_cases h : k.toNat = w
    · subst h; simp [hw0]
    · simp [h] at hl
  · simp [hlit, basic_bad2r] at hl

-- rewrite id 164
theorem sound_BV_UREM_SELF :
    (RwRule.mk [.bvq, .bv 32]
      (some (eq' (var 1) (bvsize' (var 0))))
      (bvurem' (var 0) (var 0))
      (symVal (l0) (var 1))).Sound := by
  intro env henv hcond hl hr
  obtain ⟨w, x, hx, hwb⟩ := henv 0 .bvq rfl
  obtain ⟨k, hk⟩ := henv 1 (.bv 32) rfl
  have hc := hcond _ rfl
  basic_pat at hc hl hr ⊢
  simp only [hx, hk] at hc hl hr ⊢
  basic_pat at hc hl hr ⊢
  rw [appVal_bvsize_small x hwb] at hc
  have hkw : k.toNat = w := by rw [eq_bv32 hc, toNat_ofNat_small hwb]
  rw [hkw] at hr ⊢
  rcases lit_cases w 0 with hZ | ⟨hw0, _, _, hZ⟩
  · rw [hZ] at hr; exact absurd rfl hr
  rw [hZ, basic_urem_val]
  simp [hw0]

-- rewrite id 165
theorem sound_BV_UGT_UREM :
    (RwRule.mk [.bvq, .bvq, .bv 32]
      (some (eq' (var 2) (bvsize' (var 0))))
      (ugt' (bvurem' (var 0) (var 1)) (var 1))
      (conj' [eq' (var 1) (symVal (l0) (var 2)), ugt' (var 0) (symVal (l0) (var 2))])).Sound := by
  intro env henv hcond hl hr
  obtain ⟨w, y, hy, hwb⟩ := henv 0 .bvq rfl
  obtain ⟨m, x, hx, _⟩ := henv 1 .bvq rfl
  obtain ⟨k, hk⟩ := henv 2 (.bv 32) rfl
  have hc := hcond _ rfl
  basic_pat at hc hl hr ⊢
  simp only [hx, hy, hk] at hc hl hr ⊢
  basic_pat at hc hl hr ⊢
  rw [appVal_bvsize_small y hwb] at hc
  have hkw : k.toNat = w := by rw [eq_bv32 hc, toNat_ofNat_small hwb]
  rw [hkw] at hr ⊢
  rcases lit_cases w 0 with hZ | ⟨hw0, _, _, hZ⟩
  · rw [hZ] at hr; simp [basic_bad2r] at hr
  rw [hZ]
  rw [basic_urem_val] at hl ⊢
  by_cases h : m = w
  · subst h
    simp only [↓reduceDIte, ne_eq, hw0, not_false_eq_true, ↓reduceIte, BitVec.cast_eq, basic_ugt_val,
      basic_eq_val]
    simp only [appVal, RwOp.node, Op.eval, boolN, Val.bools, Val.asBool]
    by_cases hx0 : x = 0#m
    · subst hx0; simp [BitVec.umod_zero, BitVec.ult]
    · have hpos : 0 < x.toNat := by
        rcases Nat.eq_zero_or_pos x.toNat with h0 | h0
        · exact absurd (BitVec.eq_of_toNat_eq (by simp [h0])) hx0
        · exact h0
      have hlt := BitVec.umod_lt y (y := x) (BitVec.lt_def.mpr (by simpa using hpos))
      simp only [BitVec.lt_def, BitVec.toNat_umod] at hlt
      simp [hx0, BitVec.ult]
      omega
  · simp [h, basic_bad2l] at hl

end Bcf
