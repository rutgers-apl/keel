import Bcf.Rw.Bv

/-!
# Extended terms compared with constants

`BV_SIGN_EXTEND_EQ_CONST_*`, `BV_ZERO_EXTEND_EQ_CONST_*` (vacuous: ill-typed as
transcribed by BCF) and `BV_SIGN_EXTEND_ULT_CONST_*`.
-/
namespace Bcf

open RwExpr

/-! ## G6 helpers -/

theorem extc_conj2 {a b : Val} (h : appVal .conj [a, b] ≠ .bad) :
    ∃ p q, a = .bool p ∧ b = .bool q ∧ appVal .conj [a, b] = .bool (p && q) := by
  cases a <;> cases b <;> simp [appVal, RwOp.node, Op.eval, boolN, Val.bools] at h ⊢

theorem extc_disj2 {a b : Val} (h : appVal .disj [a, b] ≠ .bad) :
    ∃ p q, a = .bool p ∧ b = .bool q ∧ appVal .disj [a, b] = .bool (p || q) := by
  cases a <;> cases b <;> simp [appVal, RwOp.node, Op.eval, boolN, Val.bools] at h ⊢

theorem extc_conj_val (p q : Bool) : appVal .conj [.bool p, .bool q] = .bool (p && q) := by
  simp [appVal, RwOp.node, Op.eval, boolN, Val.bools]

theorem extc_disj_val (p q : Bool) : appVal .disj [.bool p, .bool q] = .bool (p || q) := by
  simp [appVal, RwOp.node, Op.eval, boolN, Val.bools]

theorem extc_disj_true {a b : Val} (h : appVal .disj [a, b] = .bool true) : a = .bool true ∨ b = .bool true := by
  obtain ⟨p, q, ha, hb, hv⟩ := extc_disj2 (by rw [h]; simp)
  rw [hv] at h
  simp only [Val.bool.injEq, Bool.or_eq_true] at h
  rcases h with h | h <;> subst h <;> simp [ha, hb]

theorem extc_eq_bv {n m : Nat} (x : BitVec n) (y : BitVec m) :
    appVal .eq [.bv n x, .bv m y] = if h : m = n then .bool (decide (x = y.cast h)) else .bad := by
  by_cases h : m = n
  · subst h; simp [appVal, RwOp.node, Op.eval, eqEval, Val.eqv]
  · simp [appVal, RwOp.node, Op.eval, eqEval, Val.eqv, h]

theorem extc_eq_width {n m : Nat} {x : BitVec n} {y : BitVec m} (h : appVal .eq [.bv n x, .bv m y] ≠ .bad) : m = n := by
  by_cases hne : m = n
  · exact hne
  · rw [extc_eq_bv, dite_eq_right hne] at h; exact absurd rfl h

theorem extc_eq_bits {n m : Nat} (x : BitVec n) (y : BitVec m) (h : m = n) :
    appVal .eq [.bv n x, .bv m y] = .bool (decide (∀ i, i < n → x.getLsbD i = y.getLsbD i)) := by
  subst h; rw [extc_eq_bv, dite_eq_left rfl, BitVec.cast_eq]; congr 1
  exact decide_eq_decide.mpr BitVec.eq_of_getLsbD_eq_iff

theorem extc_eq_bad_l (b : Val) : appVal .eq [.bad, b] = .bad := by
  cases b <;> simp [appVal, RwOp.node, Op.eval, eqEval, Val.eqv]

theorem extc_eq_bad_r (a : Val) : appVal .eq [a, .bad] = .bad := by
  cases a <;> simp [appVal, RwOp.node, Op.eval, eqEval, Val.eqv]

theorem extc_cmp_bv (f : {w : Nat} → BitVec w → BitVec w → Bool) {n m : Nat} (x : BitVec n) (y : BitVec m) :
    bvCmp f [.bv n x, .bv m y] = if h : m = n then .bool (f x (y.cast h)) else .bad := rfl

theorem extc_cmp_width {f : {w : Nat} → BitVec w → BitVec w → Bool} {n m : Nat} {x : BitVec n} {y : BitVec m}
    (h : bvCmp f [.bv n x, .bv m y] ≠ .bad) : m = n := by
  by_cases hne : m = n
  · exact hne
  · rw [extc_cmp_bv, dite_eq_right hne] at h; exact absurd rfl h

theorem extc_cmp_bad_r (f : {w : Nat} → BitVec w → BitVec w → Bool) (a : Val) : bvCmp f [a, .bad] = .bad := by
  cases a <;> rfl

theorem extc_cmp_bad_l (f : {w : Nat} → BitVec w → BitVec w → Bool) (b : Val) : bvCmp f [.bad, b] = .bad := by
  cases b <;> rfl

theorem extc_ult_def (a b : Val) : appVal .ult [a, b] = bvCmp BitVec.ult [a, b] := rfl

theorem extc_ule_def (a b : Val) : appVal .ule [a, b] = bvCmp BitVec.ule [a, b] := rfl

theorem extc_ugt_def (a b : Val) : appVal .ugt [a, b] = bvCmp (fun x y => y.ult x) [a, b] := rfl

theorem extc_uge_def (a b : Val) : appVal .uge [a, b] = bvCmp (fun x y => y.ule x) [a, b] := rfl

theorem extc_ult {n m : Nat} (x : BitVec n) (y : BitVec m) (h : m = n) :
    appVal .ult [.bv n x, .bv m y] = .bool (decide (x.toNat < y.toNat)) := by
  subst h; rw [extc_ult_def, extc_cmp_bv, dite_eq_left rfl, BitVec.cast_eq]; rfl

theorem extc_ule {n m : Nat} (x : BitVec n) (y : BitVec m) (h : m = n) :
    appVal .ule [.bv n x, .bv m y] = .bool (decide (x.toNat ≤ y.toNat)) := by
  subst h; rw [extc_ule_def, extc_cmp_bv, dite_eq_left rfl, BitVec.cast_eq]; rfl

theorem extc_uge {n m : Nat} (x : BitVec n) (y : BitVec m) (h : m = n) :
    appVal .uge [.bv n x, .bv m y] = .bool (decide (y.toNat ≤ x.toNat)) := by
  subst h; rw [extc_uge_def, extc_cmp_bv, dite_eq_left rfl, BitVec.cast_eq]; rfl

theorem extc_bool_true {p : Prop} [Decidable p] (h : Val.bool (decide p) = .bool true) : p := by
  simp only [Val.bool.injEq, decide_eq_true_eq] at h; exact h

theorem extc_extract_val {hi lo n : Nat} (x : BitVec n) (h : lo ≤ hi ∧ hi < n) :
    bvExtractEval hi lo [.bv n x] = .bv (hi - lo + 1) (x.extractLsb hi lo) := by
  simp [bvExtractEval, h]

theorem extc_extract_ok {hi lo n : Nat} {x : BitVec n} (h : bvExtractEval hi lo [.bv n x] ≠ .bad) :
    lo ≤ hi ∧ hi < n := by
  by_cases hne : lo ≤ hi ∧ hi < n
  · exact hne
  · exact absurd (extract_bad hne) h

theorem extc_extract_bad (hi lo : Nat) : bvExtractEval hi lo [.bad] = .bad := rfl

theorem extc_toNat_extractLsb {n hi lo : Nat} (x : BitVec n) :
    (x.extractLsb hi lo).toNat = x.toNat / 2 ^ lo % 2 ^ (hi - lo + 1) := by
  simp [BitVec.extractLsb, BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]

theorem extc_sext_val {n : Nat} (y : BitVec n) (k : Nat) (hn : n + k ≠ 0) :
    bvExtEval true (n + k) k [.bv n y] = .bv (n + k) (y.signExtend (n + k)) := by
  simp only [bvExtEval]; rw [ite_eq_left ⟨hn, trivial⟩]; rfl

theorem extc_lit {w v : Nat} (h0 : w ≠ 0) (h64 : w ≤ 64) (hv : v < 2 ^ w) :
    bvValEval w v [] = .bv w (BitVec.ofNat w v) := by
  simp [bvValEval, h0, h64, hv]

theorem extc_bvnot_val {w : Nat} (y : BitVec w) (h : w ≠ 0) : appVal .bvnot [.bv w y] = .bv w (~~~y) := by
  simp [appVal, RwOp.reducible, RwOp.node, RwOp.widthV, RwOp.width, Val.tys, Val.ty, firstBv, Op.eval, bvUn, h]

theorem extc_bvnot_bad : appVal .bvnot [.bad] = .bad := rfl

theorem extc_shl_val {w : Nat} (x y : BitVec w) (h : w ≠ 0) : appVal .bvshl [.bv w x, .bv w y] = .bv w (x <<< y) := by
  rw [shl_eval, dite_eq_left rfl, ite_eq_left h, BitVec.cast_eq]

theorem extc_toNat_shl_one {w k : Nat} (hk : k < w) : (BitVec.ofNat w 1 <<< BitVec.ofNat w k).toNat = 2 ^ k := by
  have hkw : k < 2 ^ w := Nat.lt_trans hk Nat.lt_two_pow_self
  have h1 : 1 < 2 ^ w := Nat.lt_of_le_of_lt (by omega) (Nat.lt_two_pow_self (n := w))
  rw [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hkw,
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt h1, Nat.one_mul]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hk)

theorem extc_allOnes_mul {A B : Nat} (hB : 1 ≤ B) (hBA : B ≤ A) : (A - 1) * B % A = A - B := by
  have h1 : A * 1 ≤ A * B := Nat.mul_le_mul_left A hB
  have h2 : 1 * B ≤ A * B := Nat.mul_le_mul_right B (by omega)
  have : (A - 1) * B = A * (B - 1) + (A - B) := by rw [Nat.sub_one_mul, Nat.mul_sub_one]; omega
  rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

theorem extc_toNat_shl_allOnes {w k : Nat} (hk : k < w) :
    ((~~~BitVec.ofNat w 0) <<< BitVec.ofNat w k).toNat = 2 ^ w - 2 ^ k := by
  have hkw : k < 2 ^ w := Nat.lt_trans hk Nat.lt_two_pow_self
  rw [BitVec.not_zero, BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, BitVec.toNat_allOnes, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hkw, Nat.shiftLeft_eq]
  exact extc_allOnes_mul (Nat.two_pow_pos k) (Nat.pow_le_pow_right (by decide) (by omega))

theorem extc_sext_toNat {n m : Nat} (x : BitVec n) :
    (x.signExtend (n + m)).toNat = x.toNat + if x.msb = true then 2 ^ (n + m) - 2 ^ n else 0 := by
  rw [BitVec.toNat_signExtend, toNat_setWidth_up _ (Nat.le_add_right _ _)]

theorem extc_mod_hi {n m : Nat} (cN : Nat) (hc : cN < 2 ^ (n + m)) (hge : 2 ^ (n + m) - 2 ^ n ≤ cN) :
    cN % 2 ^ n = cN - (2 ^ (n + m) - 2 ^ n) := by
  have hK : 2 ^ (n + m) = 2 ^ n * 2 ^ m := Nat.pow_add 2 n m
  have h2 : 2 ^ n * 1 ≤ 2 ^ n * 2 ^ m := Nat.mul_le_mul_left _ (Nat.two_pow_pos m)
  have hsplit : cN = (cN - (2 ^ (n + m) - 2 ^ n)) + 2 ^ n * (2 ^ m - 1) := by
    rw [Nat.mul_sub_one, ← hK]; omega
  have key := Nat.add_mul_mod_self_left (cN - (2 ^ (n + m) - 2 ^ n)) (2 ^ n) (2 ^ m - 1)
  rw [← hsplit] at key
  rw [key, Nat.mod_eq_of_lt]; omega

theorem extc_pow_cases (n m : Nat) : 2 ^ (n + m) = 2 ^ n ∨ 2 * 2 ^ n ≤ 2 ^ (n + m) := by
  cases m with
  | zero => left; rfl
  | succ k =>
    right
    have : 2 ^ n ≤ 2 ^ (n + k) := Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _)
    rw [← Nat.add_assoc, Nat.pow_succ]; omega

theorem extc_sext_bad {n k : Nat} (y : BitVec n) (h : n + k = 0) : bvExtEval true (n + k) k [.bv n y] = .bad := by
  simp [bvExtEval, h]

theorem extc_bits142 {n m nm nm1 nmm1 mp1 : Nat} (x : BitVec n) (c : BitVec nm) (hnm : nm = n + m)
    (h1 : nm1 + 1 = n) (h2 : nmm1 + 1 = nm) (h3 : mp1 = m + 1) :
    decide (∀ i, i < n + m → (x.signExtend (n + m)).getLsbD i = c.getLsbD i) =
    ((decide (∀ i, i < nmm1 - nm1 + 1 → (c.extractLsb nmm1 nm1).getLsbD i = (BitVec.ofNat mp1 0).getLsbD i) ||
      decide (∀ i, i < nmm1 - nm1 + 1 → (c.extractLsb nmm1 nm1).getLsbD i = (~~~BitVec.ofNat mp1 0).getLsbD i)) &&
     decide (∀ i, i < n → x.getLsbD i = (c.extractLsb nm1 0).getLsbD i)) := by
  subst hnm h3
  have hn1 : n - 1 = nm1 := by omega
  have hmsb : x.msb = x.getLsbD nm1 := by rw [BitVec.msb_eq_getLsbD_last, hn1]
  have hw : nmm1 - nm1 + 1 = m + 1 := by omega
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, BitVec.getLsbD_signExtend,
    BitVec.getLsbD_extractLsb, BitVec.getLsbD_not, BitVec.getLsbD_ofNat, Nat.zero_testBit, Bool.and_false,
    Bool.not_false, Bool.and_true, hmsb, hw, Nat.sub_zero, Nat.zero_add]
  constructor
  · intro hP
    have hc : ∀ j, j < m + 1 → c.getLsbD (nm1 + j) = x.getLsbD nm1 := by
      intro j hj
      have := hP (nm1 + j) (by omega)
      rw [decide_eq_true (by omega : nm1 + j < n + m), Bool.true_and] at this
      rw [← this]
      split
      · have : j = 0 := by omega
        subst this; rfl
      · rfl
    refine ⟨?_, fun i hi => ?_⟩
    · cases hx : x.getLsbD nm1
      · left; intro i hi; rw [decide_eq_true hi, Bool.true_and, hc i hi, hx]
      · right; intro i hi; rw [decide_eq_true hi, Bool.true_and, hc i hi, hx]
    · have := hP i (by omega)
      rw [decide_eq_true (by omega : i < n + m), Bool.true_and, ite_eq_left hi] at this
      rw [decide_eq_true (by omega : i < nm1 + 1), Bool.true_and, this]
  · rintro ⟨hQ, hQ3⟩ i hi
    rw [decide_eq_true hi, Bool.true_and]
    have hlow : ∀ i, i < n → x.getLsbD i = c.getLsbD i := by
      intro i hi; have := hQ3 i hi
      rw [decide_eq_true (by omega : i < nm1 + 1), Bool.true_and] at this; exact this
    split
    · exact hlow i ‹_›
    · rename_i hni
      rw [hlow nm1 (by omega)]
      have hj : ∀ j, j < m + 1 → c.getLsbD (nm1 + j) = c.getLsbD nm1 := by
        intro j hj
        rcases hQ with hQ1 | hQ2
        · have e1 := hQ1 0 (by omega); have e2 := hQ1 j hj
          rw [decide_eq_true (by omega : 0 < m + 1), Bool.true_and, Nat.add_zero] at e1
          rw [decide_eq_true hj, Bool.true_and] at e2
          rw [e1, e2]
        · have e1 := hQ2 0 (by omega); have e2 := hQ2 j hj
          rw [decide_eq_true (by omega : 0 < m + 1), Bool.true_and, Nat.add_zero] at e1
          rw [decide_eq_true hj, Bool.true_and] at e2
          rw [e1, e2]
      have := hj (i - nm1) (by omega)
      rw [show nm1 + (i - nm1) = i by omega] at this
      exact this.symm

theorem extc_ult_width {n m : Nat} {x : BitVec n} {y : BitVec m} (h : appVal .ult [.bv n x, .bv m y] ≠ .bad) : m = n := by
  rw [extc_ult_def] at h; exact extc_cmp_width h

theorem extc_arith148 {n m nm nm1 : Nat} (x : BitVec n) (c : BitVec nm) (hnm : nm = n + m) (h1 : nm1 + 1 = n)
    (hcond : c.toNat ≤ 2 ^ nm1 ∨ 2 ^ nm - 2 ^ nm1 ≤ c.toNat) :
    decide ((x.signExtend (n + m)).toNat < c.toNat) = decide (x.toNat < (c.extractLsb nm1 0).toNat) := by
  subst hnm
  rw [extc_sext_toNat, extc_toNat_extractLsb, Nat.pow_zero, Nat.div_one, Nat.sub_zero, h1]
  have hP : 0 < 2 ^ nm1 := Nat.two_pow_pos _
  have hN : 2 ^ n = 2 * 2 ^ nm1 := by rw [← h1, Nat.pow_succ]; omega
  have hM : 2 ^ n ≤ 2 ^ (n + m) := Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _)
  have hx := x.isLt
  have hc := c.isLt
  have hmsb := BitVec.msb_eq_decide x
  rw [show n - 1 = nm1 by omega] at hmsb
  have hr := Nat.mod_lt c.toNat (Nat.two_pow_pos n)
  have hlo : c.toNat < 2 ^ n → c.toNat % 2 ^ n = c.toNat := Nat.mod_eq_of_lt
  have hhi := extc_mod_hi c.toNat hc
  apply decide_eq_decide.mpr
  generalize c.toNat % 2 ^ n = r at *
  rw [hmsb]
  simp only [decide_eq_true_eq]
  rcases hcond with hcd | hcd
  · have := hlo (by omega)
    split <;> omega
  · have := hhi (by omega)
    split <;> omega

theorem extc_arith149 {n m nm nm1 : Nat} (x : BitVec n) (c : BitVec nm) (hnm : nm = n + m) (h1 : nm1 + 1 = n)
    (hlo : 2 ^ nm1 < c.toNat) (hhi : c.toNat ≤ 2 ^ nm - 2 ^ nm1) :
    decide ((x.signExtend (n + m)).toNat < c.toNat) =
      decide (∀ i, i < nm1 - nm1 + 1 → (x.extractLsb nm1 nm1).getLsbD i = (BitVec.ofNat 1 0).getLsbD i) := by
  subst hnm
  have hbit : (∀ i, i < nm1 - nm1 + 1 → (x.extractLsb nm1 nm1).getLsbD i = (BitVec.ofNat 1 0).getLsbD i) ↔
      x.msb = false := by
    rw [BitVec.msb_eq_getLsbD_last, show n - 1 = nm1 by omega]
    simp only [Nat.sub_self, Nat.zero_add, Nat.lt_one_iff, forall_eq, BitVec.getLsbD_extractLsb,
      BitVec.getLsbD_ofNat, Nat.zero_testBit, Bool.and_false, Nat.add_zero, decide_true, Bool.true_and]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  rw [hbit, extc_sext_toNat]
  have hP : 0 < 2 ^ nm1 := Nat.two_pow_pos _
  have hN : 2 ^ n = 2 * 2 ^ nm1 := by rw [← h1, Nat.pow_succ]; omega
  have hM : 2 ^ n ≤ 2 ^ (n + m) := Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _)
  have hx := x.isLt
  have hc := c.isLt
  have hmsb := BitVec.msb_eq_decide x
  rw [show n - 1 = nm1 by omega] at hmsb
  rw [hmsb]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  split <;> omega

theorem extc_arith150 {n m nm nm1 : Nat} (x : BitVec n) (c : BitVec nm) (hnm : nm = n + m) (h1 : nm1 + 1 = n)
    (hcond : c.toNat < 2 ^ nm1 ∨ 2 ^ nm - 1 - 2 ^ nm1 ≤ c.toNat) :
    decide (c.toNat < (x.signExtend (n + m)).toNat) = decide ((c.extractLsb nm1 0).toNat < x.toNat) := by
  subst hnm
  rw [extc_sext_toNat, extc_toNat_extractLsb, Nat.pow_zero, Nat.div_one, Nat.sub_zero, h1]
  have hP : 0 < 2 ^ nm1 := Nat.two_pow_pos _
  have hN : 2 ^ n = 2 * 2 ^ nm1 := by rw [← h1, Nat.pow_succ]; omega
  have hM := extc_pow_cases n m
  have hx := x.isLt
  have hc := c.isLt
  have hmsb := BitVec.msb_eq_decide x
  rw [show n - 1 = nm1 by omega] at hmsb
  have hr := Nat.mod_lt c.toNat (Nat.two_pow_pos n)
  have hlo : c.toNat < 2 ^ n → c.toNat % 2 ^ n = c.toNat := Nat.mod_eq_of_lt
  have hhi := extc_mod_hi c.toNat hc
  apply decide_eq_decide.mpr
  generalize c.toNat % 2 ^ n = r at *
  rw [hmsb]
  simp only [decide_eq_true_eq]
  rcases hcond with hcd | hcd
  · have := hlo (by omega)
    split <;> omega
  · rcases hM with hM | hM
    · have := hlo (by omega)
      split <;> omega
    · have := hhi (by omega)
      split <;> omega

theorem extc_arith151 {n m nm nm1 : Nat} (x : BitVec n) (c : BitVec nm) (hnm : nm = n + m) (h1 : nm1 + 1 = n)
    (hlo : 2 ^ nm - 1 - (2 ^ nm - 2 ^ nm1) ≤ c.toNat) (hhi : c.toNat ≤ 2 ^ nm - 1 - 2 ^ nm1) :
    decide (c.toNat < (x.signExtend (n + m)).toNat) =
      decide (∀ i, i < nm1 - nm1 + 1 → (x.extractLsb nm1 nm1).getLsbD i = (BitVec.ofNat 1 1).getLsbD i) := by
  subst hnm
  have e : (BitVec.ofNat 1 1).getLsbD 0 = true := by decide
  have hbit : (∀ i, i < nm1 - nm1 + 1 → (x.extractLsb nm1 nm1).getLsbD i = (BitVec.ofNat 1 1).getLsbD i) ↔
      x.msb = true := by
    rw [BitVec.msb_eq_getLsbD_last, show n - 1 = nm1 by omega]
    simp only [Nat.sub_self, Nat.zero_add, Nat.lt_one_iff, forall_eq, BitVec.getLsbD_extractLsb, e,
      Nat.add_zero, decide_true, Bool.true_and]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  rw [hbit, extc_sext_toNat]
  have hP : 0 < 2 ^ nm1 := Nat.two_pow_pos _
  have hN : 2 ^ n = 2 * 2 ^ nm1 := by rw [← h1, Nat.pow_succ]; omega
  have hM : 2 ^ n ≤ 2 ^ (n + m) := Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _)
  have hx := x.isLt
  have hc := c.isLt
  have hmsb := BitVec.msb_eq_decide x
  rw [show n - 1 = nm1 by omega] at hmsb
  rw [hmsb]
  simp only [decide_eq_true_eq]
  split <;> omega

theorem extc_bits143 {n m nm nm1 nmm1 mp1 : Nat} (x : BitVec n) (c : BitVec nm) (hnm : n + m = nm)
    (h1 : nm1 + 1 = n) (h2 : nmm1 + 1 = nm) (h3 : mp1 = m + 1) :
    decide (∀ i, i < nm → c.getLsbD i = (x.signExtend (n + m)).getLsbD i) =
    ((decide (∀ i, i < nmm1 - nm1 + 1 → (c.extractLsb nmm1 nm1).getLsbD i = (BitVec.ofNat mp1 0).getLsbD i) ||
      decide (∀ i, i < nmm1 - nm1 + 1 → (c.extractLsb nmm1 nm1).getLsbD i = (~~~BitVec.ofNat mp1 0).getLsbD i)) &&
     decide (∀ i, i < n → x.getLsbD i = (c.extractLsb nm1 0).getLsbD i)) := by
  rw [← extc_bits142 x c hnm.symm h1 h2 h3]
  subst hnm
  congr 1
  apply propext
  constructor <;> intro h i hi <;> exact (h i hi).symm

-- rewrite id 142
theorem sound_BV_SIGN_EXTEND_EQ_CONST_1 :
    (RwRule.mk [.bvq, .bv 32, .bv 32, .bv 32, .bv 32, .bv 32, .bv 32]
      (some (conj' [eq' (var 4) (bvadd' [var 1, l1]), eq' (var 5) (bvsub' (bvsize' (var 0)) (l1)), eq' (var 6) (bvsub' (var 3) (l1))]))
      (eq' (sext (var 1) (var 0)) (symVal (var 2) (var 3)))
      (conj' [disj' [eq' (extract (var 6) (var 5) (symVal (var 2) (var 3))) (symVal (l0) (var 4)), eq' (extract (var 6) (var 5) (symVal (var 2) (var 3))) (bvnot' (symVal (l0) (var 4)))], eq' (var 0) (extract (var 5) (l0) (symVal (var 2) (var 3)))])).Sound := by
  intro env henv hcond hl hr
  obtain ⟨w0, x0, h0, hw0⟩ := henv 0 .bvq rfl
  obtain ⟨k1, h1⟩ := henv 1 (.bv 32) rfl
  obtain ⟨k2, h2⟩ := henv 2 (.bv 32) rfl
  obtain ⟨k3, h3⟩ := henv 3 (.bv 32) rfl
  obtain ⟨k4, h4⟩ := henv 4 (.bv 32) rfl
  obtain ⟨k5, h5⟩ := henv 5 (.bv 32) rfl
  obtain ⟨k6, h6⟩ := henv 6 (.bv 32) rfl
  have hc := hcond _ rfl
  simp only [RwExpr.disj', RwExpr.bvnot'] at hr ⊢
  rw_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3, h4, h5, h6] at hc hl hr ⊢
  rw_pat at hc hl hr ⊢
  simp only [spliceVal_appVal_nonred (rfl : RwOp.reducible .bvnot = false)] at hr ⊢
  simp only [appVal_bvsize_small x0 hw0, appVal_bvsub32, appVal_bvadd32] at hc
  obtain ⟨he4, he5, he6⟩ := conj_all3 hc
  have hk4 := eq_bv32 he4
  have hk5 := eq_bv32 he5
  have hk6 := eq_bv32 he6
  rcases lit_cases k3.toNat k2.toNat with hC | ⟨hk30, hk364, hk2lt, hC⟩
  · rw [hC, extc_eq_bad_r] at hl; exact absurd rfl hl
  rw [hC] at hl hr ⊢
  generalize BitVec.ofNat k3.toNat k2.toNat = c at hl hr ⊢
  obtain ⟨p, q, hD, hE3, _⟩ := extc_conj2 hr
  have hx5 : 0 ≤ k5.toNat ∧ k5.toNat < k3.toNat :=
    extc_extract_ok (fun h => by rw [h, extc_eq_bad_r] at hE3; cases hE3)
  rw [extc_extract_val _ hx5] at hE3 ⊢
  have hw : k5.toNat - 0 + 1 = w0 := extc_eq_width (by rw [hE3]; simp)
  obtain ⟨p1, p2, hE1, hE2, _⟩ := extc_disj2 (by rw [hD]; simp)
  rcases lit_cases k4.toNat 0 with hL | ⟨hk40, hk464, _, hL⟩
  · rw [hL, extc_eq_bad_r] at hE1; cases hE1
  rw [hL] at hE1 hE2 ⊢
  have hx6 : k5.toNat ≤ k6.toNat ∧ k6.toNat < k3.toNat :=
    extc_extract_ok (fun h => by rw [h, extc_eq_bad_l] at hE1; cases hE1)
  rw [extc_extract_val _ hx6] at hE1 hE2 ⊢
  have hw4 : k4.toNat = k6.toNat - k5.toNat + 1 := extc_eq_width (by rw [hE1]; simp)
  rw [extc_sext_val _ _ (by omega)] at hl ⊢
  have hnm : k3.toNat = w0 + k1.toNat := extc_eq_width hl
  have h1n : (1#32 : BitVec 32).toNat = 1 := by decide
  have hk5n : k5.toNat = w0 - 1 := by rw [hk5, toNat_sub_one32 (by omega) (by rw [two32]; omega)]
  have hk6n : k6.toNat = k3.toNat - 1 := by rw [hk6, toNat_sub32 (by omega), h1n]
  have hk4n : k4.toNat = k1.toNat + 1 := by rw [hk4, toNat_add32 _ _ (by rw [h1n, two32]; omega), h1n]
  rw [extc_bvnot_val _ hk40, extc_eq_bits _ _ hnm, extc_eq_bits _ _ hw4, extc_eq_bits _ _ hw4, extc_eq_bits _ _ hw,
    extc_disj_val, extc_conj_val]
  congr 1
  exact extc_bits142 x0 c hnm (by omega) (by omega) (by omega)

-- rewrite id 143
theorem sound_BV_SIGN_EXTEND_EQ_CONST_2 :
    (RwRule.mk [.bvq, .bv 32, .bv 32, .bv 32, .bv 32, .bv 32, .bv 32]
      (some (conj' [eq' (var 4) (bvadd' [var 1, l1]), eq' (var 5) (bvsub' (bvsize' (var 0)) (l1)), eq' (var 6) (bvsub' (var 3) (l1))]))
      (eq' (symVal (var 2) (var 3)) (sext (var 1) (var 0)))
      (conj' [disj' [eq' (extract (var 6) (var 5) (symVal (var 2) (var 3))) (symVal (l0) (var 4)), eq' (extract (var 6) (var 5) (symVal (var 2) (var 3))) (bvnot' (symVal (l0) (var 4)))], eq' (var 0) (extract (var 5) (l0) (symVal (var 2) (var 3)))])).Sound := by
  intro env henv hcond hl hr
  obtain ⟨w0, x0, h0, hw0⟩ := henv 0 .bvq rfl
  obtain ⟨k1, h1⟩ := henv 1 (.bv 32) rfl
  obtain ⟨k2, h2⟩ := henv 2 (.bv 32) rfl
  obtain ⟨k3, h3⟩ := henv 3 (.bv 32) rfl
  obtain ⟨k4, h4⟩ := henv 4 (.bv 32) rfl
  obtain ⟨k5, h5⟩ := henv 5 (.bv 32) rfl
  obtain ⟨k6, h6⟩ := henv 6 (.bv 32) rfl
  have hc := hcond _ rfl
  simp only [RwExpr.disj', RwExpr.bvnot'] at hr ⊢
  rw_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3, h4, h5, h6] at hc hl hr ⊢
  rw_pat at hc hl hr ⊢
  simp only [spliceVal_appVal_nonred (rfl : RwOp.reducible .bvnot = false)] at hr ⊢
  simp only [appVal_bvsize_small x0 hw0, appVal_bvsub32, appVal_bvadd32] at hc
  obtain ⟨he4, he5, he6⟩ := conj_all3 hc
  have hk4 := eq_bv32 he4
  have hk5 := eq_bv32 he5
  have hk6 := eq_bv32 he6
  rcases lit_cases k3.toNat k2.toNat with hC | ⟨hk30, hk364, hk2lt, hC⟩
  · rw [hC, extc_eq_bad_l] at hl; exact absurd rfl hl
  rw [hC] at hl hr ⊢
  generalize BitVec.ofNat k3.toNat k2.toNat = c at hl hr ⊢
  obtain ⟨p, q, hD, hE3, _⟩ := extc_conj2 hr
  have hx5 : 0 ≤ k5.toNat ∧ k5.toNat < k3.toNat :=
    extc_extract_ok (fun h => by rw [h, extc_eq_bad_r] at hE3; cases hE3)
  rw [extc_extract_val _ hx5] at hE3 ⊢
  have hw : k5.toNat - 0 + 1 = w0 := extc_eq_width (by rw [hE3]; simp)
  obtain ⟨p1, p2, hE1, hE2, _⟩ := extc_disj2 (by rw [hD]; simp)
  rcases lit_cases k4.toNat 0 with hL | ⟨hk40, hk464, _, hL⟩
  · rw [hL, extc_eq_bad_r] at hE1; cases hE1
  rw [hL] at hE1 hE2 ⊢
  have hx6 : k5.toNat ≤ k6.toNat ∧ k6.toNat < k3.toNat :=
    extc_extract_ok (fun h => by rw [h, extc_eq_bad_l] at hE1; cases hE1)
  rw [extc_extract_val _ hx6] at hE1 hE2 ⊢
  have hw4 : k4.toNat = k6.toNat - k5.toNat + 1 := extc_eq_width (by rw [hE1]; simp)
  rw [extc_sext_val _ _ (by omega)] at hl ⊢
  have hnm : w0 + k1.toNat = k3.toNat := extc_eq_width hl
  have h1n : (1#32 : BitVec 32).toNat = 1 := by decide
  have hk5n : k5.toNat = w0 - 1 := by rw [hk5, toNat_sub_one32 (by omega) (by rw [two32]; omega)]
  have hk6n : k6.toNat = k3.toNat - 1 := by rw [hk6, toNat_sub32 (by omega), h1n]
  have hk4n : k4.toNat = k1.toNat + 1 := by rw [hk4, toNat_add32 _ _ (by rw [h1n, two32]; omega), h1n]
  rw [extc_bvnot_val _ hk40, extc_eq_bits _ _ hnm, extc_eq_bits _ _ hw4, extc_eq_bits _ _ hw4, extc_eq_bits _ _ hw,
    extc_disj_val, extc_conj_val]
  congr 1
  exact extc_bits143 x0 c hnm (by omega) (by omega) (by omega)

-- rewrite id 144
theorem sound_BV_ZERO_EXTEND_EQ_CONST_1 :
    (RwRule.mk [.bvq, .bv 32, .bv 32, .bv 32, .bv 32, .bv 32]
      (some (conj' [eq' (var 4) (bvsub' (bvsize' (var 0)) (l1)), eq' (var 5) (bvsub' (var 3) (l1))]))
      (eq' (zext (var 1) (var 0)) (symVal (var 2) (var 3)))
      (conj' [eq' (extract (var 5) (var 4) (symVal (var 2) (var 3))) (symVal (l0) (var 1)), eq' (var 0) (extract (var 4) (l0) (symVal (var 2) (var 3)))])).Sound := by
  intro env henv hcond hl hr
  obtain ⟨w0, x0, h0, hw0⟩ := henv 0 .bvq rfl
  obtain ⟨k1, h1⟩ := henv 1 (.bv 32) rfl
  obtain ⟨k2, h2⟩ := henv 2 (.bv 32) rfl
  obtain ⟨k3, h3⟩ := henv 3 (.bv 32) rfl
  obtain ⟨k4, h4⟩ := henv 4 (.bv 32) rfl
  obtain ⟨k5, h5⟩ := henv 5 (.bv 32) rfl
  have hc := hcond _ rfl
  rw_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3, h4, h5] at hc hl hr ⊢
  rw_pat at hc hl hr ⊢
  simp only [appVal_bvsize_small x0 hw0, appVal_bvsub32] at hc
  obtain ⟨he4, he5⟩ := conj_all2 hc
  have hk5 := eq_bv32 he5
  rcases lit_cases k3.toNat k2.toNat with hC | ⟨hk30, hk364, hk2lt, hC⟩
  · rw [hC, extc_eq_bad_r] at hl; exact absurd rfl hl
  rw [hC] at hl hr
  generalize BitVec.ofNat k3.toNat k2.toNat = c at hl hr
  obtain ⟨p, q, hE1, hE2, _⟩ := extc_conj2 hr
  have hx4 : 0 ≤ k4.toNat ∧ k4.toNat < k3.toNat :=
    extc_extract_ok (fun h => by rw [h, extc_eq_bad_r] at hE2; cases hE2)
  rw [extc_extract_val _ hx4] at hE2
  have hw : k4.toNat - 0 + 1 = w0 := extc_eq_width (by rw [hE2]; simp)
  rcases lit_cases k1.toNat 0 with hL | ⟨hk10, hk164, _, hL⟩
  · rw [hL, extc_eq_bad_r] at hE1; cases hE1
  rw [hL] at hE1
  have hx5 : k4.toNat ≤ k5.toNat ∧ k5.toNat < k3.toNat :=
    extc_extract_ok (fun h => by rw [h, extc_eq_bad_l] at hE1; cases hE1)
  rw [extc_extract_val _ hx5] at hE1
  have hw1 : k1.toNat = k5.toNat - k4.toNat + 1 := extc_eq_width (by rw [hE1]; simp)
  rw [zext_val _ _ (by omega)] at hl
  have hnm : k3.toNat = w0 + k1.toNat := extc_eq_width hl
  have h1n : (1#32 : BitVec 32).toNat = 1 := by decide
  have hk5n : k5.toNat = k3.toNat - 1 := by rw [hk5, toNat_sub32 (by omega), h1n]
  omega

-- rewrite id 145
theorem sound_BV_ZERO_EXTEND_EQ_CONST_2 :
    (RwRule.mk [.bvq, .bv 32, .bv 32, .bv 32, .bv 32, .bv 32]
      (some (conj' [eq' (var 4) (bvsub' (bvsize' (var 0)) (l1)), eq' (var 5) (bvsub' (var 3) (l1))]))
      (eq' (symVal (var 2) (var 3)) (zext (var 1) (var 0)))
      (conj' [eq' (extract (var 5) (var 4) (symVal (var 2) (var 3))) (symVal (l0) (var 1)), eq' (var 0) (extract (var 4) (l0) (symVal (var 2) (var 3)))])).Sound := by
  intro env henv hcond hl hr
  obtain ⟨w0, x0, h0, hw0⟩ := henv 0 .bvq rfl
  obtain ⟨k1, h1⟩ := henv 1 (.bv 32) rfl
  obtain ⟨k2, h2⟩ := henv 2 (.bv 32) rfl
  obtain ⟨k3, h3⟩ := henv 3 (.bv 32) rfl
  obtain ⟨k4, h4⟩ := henv 4 (.bv 32) rfl
  obtain ⟨k5, h5⟩ := henv 5 (.bv 32) rfl
  have hc := hcond _ rfl
  rw_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3, h4, h5] at hc hl hr ⊢
  rw_pat at hc hl hr ⊢
  simp only [appVal_bvsize_small x0 hw0, appVal_bvsub32] at hc
  obtain ⟨he4, he5⟩ := conj_all2 hc
  have hk5 := eq_bv32 he5
  rcases lit_cases k3.toNat k2.toNat with hC | ⟨hk30, hk364, hk2lt, hC⟩
  · rw [hC, extc_eq_bad_l] at hl; exact absurd rfl hl
  rw [hC] at hl hr
  generalize BitVec.ofNat k3.toNat k2.toNat = c at hl hr
  obtain ⟨p, q, hE1, hE2, _⟩ := extc_conj2 hr
  have hx4 : 0 ≤ k4.toNat ∧ k4.toNat < k3.toNat :=
    extc_extract_ok (fun h => by rw [h, extc_eq_bad_r] at hE2; cases hE2)
  rw [extc_extract_val _ hx4] at hE2
  have hw : k4.toNat - 0 + 1 = w0 := extc_eq_width (by rw [hE2]; simp)
  rcases lit_cases k1.toNat 0 with hL | ⟨hk10, hk164, _, hL⟩
  · rw [hL, extc_eq_bad_r] at hE1; cases hE1
  rw [hL] at hE1
  have hx5 : k4.toNat ≤ k5.toNat ∧ k5.toNat < k3.toNat :=
    extc_extract_ok (fun h => by rw [h, extc_eq_bad_l] at hE1; cases hE1)
  rw [extc_extract_val _ hx5] at hE1
  have hw1 : k1.toNat = k5.toNat - k4.toNat + 1 := extc_eq_width (by rw [hE1]; simp)
  rw [zext_val _ _ (by omega)] at hl
  have hnm : w0 + k1.toNat = k3.toNat := extc_eq_width hl
  have h1n : (1#32 : BitVec 32).toNat = 1 := by decide
  have hk5n : k5.toNat = k3.toNat - 1 := by rw [hk5, toNat_sub32 (by omega), h1n]
  omega

-- rewrite id 148
theorem sound_BV_SIGN_EXTEND_ULT_CONST_1 :
    (RwRule.mk [.bvq, .bv 32, .bv 32, .bv 32, .bv 32]
      (some (conj' [disj' [ule' (symVal (var 2) (var 3)) (bvshl' (symVal (l1) (var 3)) (symVal (bvsub' (bvsize' (var 0)) (l1)) (var 3))), uge' (symVal (var 2) (var 3)) (bvshl' (bvnot' (symVal (l0) (var 3))) (symVal (bvsub' (bvsize' (var 0)) (l1)) (var 3)))], eq' (var 4) (bvsub' (bvsize' (var 0)) (l1))]))
      (ult' (sext (var 1) (var 0)) (symVal (var 2) (var 3)))
      (ult' (var 0) (extract (var 4) (l0) (symVal (var 2) (var 3))))).Sound := by
  intro env henv hcond hl hr
  obtain ⟨w0, x0, h0, hw0⟩ := henv 0 .bvq rfl
  obtain ⟨k1, h1⟩ := henv 1 (.bv 32) rfl
  obtain ⟨k2, h2⟩ := henv 2 (.bv 32) rfl
  obtain ⟨k3, h3⟩ := henv 3 (.bv 32) rfl
  obtain ⟨k4, h4⟩ := henv 4 (.bv 32) rfl
  have hc := hcond _ rfl
  simp only [RwExpr.disj', RwExpr.uge', RwExpr.bvnot'] at hc
  rw_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3, h4] at hc hl hr ⊢
  rw_pat at hc hl hr ⊢
  simp only [spliceVal_appVal_nonred (rfl : RwOp.reducible .bvnot = false)] at hc
  simp only [appVal_bvsize_small x0 hw0, appVal_bvsub32] at hc
  rw_pat at hc
  have h1m : (1 : Nat) % 2 ^ 32 = 1 := by decide
  simp only [h1m] at hc
  obtain ⟨hd, he4⟩ := conj_all2 hc
  have hk4 := eq_bv32 he4
  rw [← hk4] at hd
  rcases lit_cases k3.toNat k2.toNat with hC | ⟨hk30, hk364, hk2lt, hC⟩
  · rw [hC, extc_ult_def, extc_cmp_bad_r] at hl; exact absurd rfl hl
  rw [hC] at hd hl hr ⊢
  generalize BitVec.ofNat k3.toNat k2.toNat = c at hd hl hr ⊢
  have hx4 : 0 ≤ k4.toNat ∧ k4.toNat < k3.toNat :=
    extc_extract_ok (fun h => by rw [h, extc_ult_def, extc_cmp_bad_r] at hr; exact absurd rfl hr)
  rw [extc_extract_val _ hx4] at hr ⊢
  have hw : k4.toNat - 0 + 1 = w0 := extc_ult_width hr
  rw [extc_sext_val _ _ (by omega)] at hl ⊢
  have hnm : k3.toNat = w0 + k1.toNat := extc_ult_width hl
  have hk4n : k4.toNat < k3.toNat := hx4.2
  rw [extc_lit (v := 1) hk30 hk364 (Nat.one_lt_two_pow hk30),
    extc_lit (v := k4.toNat) hk30 hk364 (Nat.lt_trans hk4n Nat.lt_two_pow_self),
    extc_lit (v := 0) hk30 hk364 (Nat.two_pow_pos _),
    extc_bvnot_val _ hk30, extc_shl_val _ _ hk30, extc_shl_val _ _ hk30, extc_ule _ _ rfl, extc_uge _ _ rfl,
    extc_toNat_shl_one hk4n, extc_toNat_shl_allOnes hk4n] at hd
  have hcd : c.toNat ≤ 2 ^ k4.toNat ∨ 2 ^ k3.toNat - 2 ^ k4.toNat ≤ c.toNat := by
    rcases extc_disj_true hd with hcd | hcd
    · exact Or.inl (extc_bool_true hcd)
    · exact Or.inr (extc_bool_true hcd)
  rw [extc_ult _ _ hnm, extc_ult _ _ hw]
  congr 1
  exact extc_arith148 x0 c hnm (by omega) hcd

-- rewrite id 149
theorem sound_BV_SIGN_EXTEND_ULT_CONST_2 :
    (RwRule.mk [.bvq, .bv 32, .bv 32, .bv 32, .bv 32]
      (some (conj' [ult' (bvshl' (symVal (l1) (var 3)) (symVal (bvsub' (bvsize' (var 0)) (l1)) (var 3))) (symVal (var 2) (var 3)), ule' (symVal (var 2) (var 3)) (bvshl' (bvnot' (symVal (l0) (var 3))) (symVal (bvsub' (bvsize' (var 0)) (l1)) (var 3))), eq' (var 4) (bvsub' (bvsize' (var 0)) (l1))]))
      (ult' (sext (var 1) (var 0)) (symVal (var 2) (var 3)))
      (eq' (extract (var 4) (var 4) (var 0)) (symVal (l0) (l1)))).Sound := by
  intro env henv hcond hl hr
  obtain ⟨w0, x0, h0, hw0⟩ := henv 0 .bvq rfl
  obtain ⟨k1, h1⟩ := henv 1 (.bv 32) rfl
  obtain ⟨k2, h2⟩ := henv 2 (.bv 32) rfl
  obtain ⟨k3, h3⟩ := henv 3 (.bv 32) rfl
  obtain ⟨k4, h4⟩ := henv 4 (.bv 32) rfl
  have hc := hcond _ rfl
  simp only [RwExpr.bvnot'] at hc
  rw_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3, h4] at hc hl hr ⊢
  rw_pat at hc hl hr ⊢
  simp only [spliceVal_appVal_nonred (rfl : RwOp.reducible .bvnot = false)] at hc
  simp only [appVal_bvsize_small x0 hw0, appVal_bvsub32] at hc
  rw_pat at hc
  have h1m : (1 : Nat) % 2 ^ 32 = 1 := by decide
  simp only [h1m] at hc hr ⊢
  obtain ⟨hd1, hd2, he4⟩ := conj_all3 hc
  have hk4 := eq_bv32 he4
  rw [← hk4] at hd1 hd2
  rcases lit_cases k3.toNat k2.toNat with hC | ⟨hk30, hk364, hk2lt, hC⟩
  · rw [hC, extc_ult_def, extc_cmp_bad_r] at hl; exact absurd rfl hl
  rw [hC] at hd1 hd2 hl ⊢
  generalize BitVec.ofNat k3.toNat k2.toNat = c at hd1 hd2 hl ⊢
  rw [extc_lit (v := 0) (by decide) (by decide) (by decide)] at hr ⊢
  have hx4 : k4.toNat ≤ k4.toNat ∧ k4.toNat < w0 :=
    extc_extract_ok (fun h => by rw [h, extc_eq_bad_l] at hr; exact absurd rfl hr)
  rw [extc_extract_val _ hx4] at hr ⊢
  rw [extc_sext_val _ _ (by omega)] at hl ⊢
  have hnm : k3.toNat = w0 + k1.toNat := extc_ult_width hl
  have hk4n : k4.toNat < k3.toNat := by omega
  have hk4e : k4.toNat = w0 - 1 := by rw [hk4, toNat_sub_one32 (by omega) (by rw [two32]; omega)]
  rw [extc_lit (v := 1) hk30 hk364 (Nat.one_lt_two_pow hk30),
    extc_lit (v := k4.toNat) hk30 hk364 (Nat.lt_trans hk4n Nat.lt_two_pow_self),
    extc_shl_val _ _ hk30, extc_ult _ _ rfl, extc_toNat_shl_one hk4n] at hd1
  rw [extc_lit (v := k4.toNat) hk30 hk364 (Nat.lt_trans hk4n Nat.lt_two_pow_self),
    extc_lit (v := 0) hk30 hk364 (Nat.two_pow_pos _),
    extc_bvnot_val _ hk30, extc_shl_val _ _ hk30, extc_ule _ _ rfl, extc_toNat_shl_allOnes hk4n] at hd2
  rw [extc_ult _ _ hnm, extc_eq_bits _ _ (by omega)]
  congr 1
  exact extc_arith149 x0 c hnm (by omega) (extc_bool_true hd1) (extc_bool_true hd2)

-- rewrite id 150
theorem sound_BV_SIGN_EXTEND_ULT_CONST_3 :
    (RwRule.mk [.bvq, .bv 32, .bv 32, .bv 32, .bv 32]
      (some (conj' [disj' [ult' (symVal (var 2) (var 3)) (bvshl' (symVal (l1) (var 3)) (symVal (bvsub' (bvsize' (var 0)) (l1)) (var 3))), uge' (symVal (var 2) (var 3)) (bvnot' (bvshl' (symVal (l1) (var 3)) (symVal (bvsub' (bvsize' (var 0)) (l1)) (var 3))))], eq' (var 4) (bvsub' (bvsize' (var 0)) (l1))]))
      (ult' (symVal (var 2) (var 3)) (sext (var 1) (var 0)))
      (ult' (extract (var 4) (l0) (symVal (var 2) (var 3))) (var 0))).Sound := by
  intro env henv hcond hl hr
  obtain ⟨w0, x0, h0, hw0⟩ := henv 0 .bvq rfl
  obtain ⟨k1, h1⟩ := henv 1 (.bv 32) rfl
  obtain ⟨k2, h2⟩ := henv 2 (.bv 32) rfl
  obtain ⟨k3, h3⟩ := henv 3 (.bv 32) rfl
  obtain ⟨k4, h4⟩ := henv 4 (.bv 32) rfl
  have hc := hcond _ rfl
  simp only [RwExpr.disj', RwExpr.uge', RwExpr.bvnot'] at hc
  rw_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3, h4] at hc hl hr ⊢
  rw_pat at hc hl hr ⊢
  simp only [spliceVal_appVal_nonred (rfl : RwOp.reducible .bvnot = false)] at hc
  simp only [appVal_bvsize_small x0 hw0, appVal_bvsub32] at hc
  rw_pat at hc
  have h1m : (1 : Nat) % 2 ^ 32 = 1 := by decide
  simp only [h1m] at hc
  obtain ⟨hd, he4⟩ := conj_all2 hc
  have hk4 := eq_bv32 he4
  rw [← hk4] at hd
  rcases lit_cases k3.toNat k2.toNat with hC | ⟨hk30, hk364, hk2lt, hC⟩
  · rw [hC, extc_ult_def, extc_cmp_bad_l] at hl; exact absurd rfl hl
  rw [hC] at hd hl hr ⊢
  generalize BitVec.ofNat k3.toNat k2.toNat = c at hd hl hr ⊢
  have hx4 : 0 ≤ k4.toNat ∧ k4.toNat < k3.toNat :=
    extc_extract_ok (fun h => by rw [h, extc_ult_def, extc_cmp_bad_l] at hr; exact absurd rfl hr)
  rw [extc_extract_val _ hx4] at hr ⊢
  have hw : w0 = k4.toNat - 0 + 1 := extc_ult_width hr
  rw [extc_sext_val _ _ (by omega)] at hl ⊢
  have hnm : w0 + k1.toNat = k3.toNat := extc_ult_width hl
  have hk4n : k4.toNat < k3.toNat := hx4.2
  rw [extc_lit (v := 1) hk30 hk364 (Nat.one_lt_two_pow hk30),
    extc_lit (v := k4.toNat) hk30 hk364 (Nat.lt_trans hk4n Nat.lt_two_pow_self),
    extc_shl_val _ _ hk30, extc_bvnot_val _ hk30, extc_ult _ _ rfl, extc_uge _ _ rfl,
    BitVec.toNat_not, extc_toNat_shl_one hk4n] at hd
  have hcd : c.toNat < 2 ^ k4.toNat ∨ 2 ^ k3.toNat - 1 - 2 ^ k4.toNat ≤ c.toNat := by
    rcases extc_disj_true hd with hcd | hcd
    · exact Or.inl (extc_bool_true hcd)
    · exact Or.inr (extc_bool_true hcd)
  rw [extc_ult _ _ hnm, extc_ult _ _ hw]
  congr 1
  exact extc_arith150 x0 c hnm.symm (by omega) hcd

-- rewrite id 151
theorem sound_BV_SIGN_EXTEND_ULT_CONST_4 :
    (RwRule.mk [.bvq, .bv 32, .bv 32, .bv 32, .bv 32]
      (some (conj' [ule' (bvnot' (bvshl' (bvnot' (symVal (l0) (var 3))) (symVal (bvsub' (bvsize' (var 0)) (l1)) (var 3)))) (symVal (var 2) (var 3)), ule' (symVal (var 2) (var 3)) (bvnot' (bvshl' (symVal (l1) (var 3)) (symVal (bvsub' (bvsize' (var 0)) (l1)) (var 3)))), eq' (var 4) (bvsub' (bvsize' (var 0)) (l1))]))
      (ult' (symVal (var 2) (var 3)) (sext (var 1) (var 0)))
      (eq' (extract (var 4) (var 4) (var 0)) (symVal (l1) (l1)))).Sound := by
  intro env henv hcond hl hr
  obtain ⟨w0, x0, h0, hw0⟩ := henv 0 .bvq rfl
  obtain ⟨k1, h1⟩ := henv 1 (.bv 32) rfl
  obtain ⟨k2, h2⟩ := henv 2 (.bv 32) rfl
  obtain ⟨k3, h3⟩ := henv 3 (.bv 32) rfl
  obtain ⟨k4, h4⟩ := henv 4 (.bv 32) rfl
  have hc := hcond _ rfl
  simp only [RwExpr.bvnot'] at hc
  rw_pat at hc hl hr ⊢
  simp only [h0, h1, h2, h3, h4] at hc hl hr ⊢
  rw_pat at hc hl hr ⊢
  simp only [spliceVal_appVal_nonred (rfl : RwOp.reducible .bvnot = false)] at hc
  simp only [appVal_bvsize_small x0 hw0, appVal_bvsub32] at hc
  rw_pat at hc
  have h1m : (1 : Nat) % 2 ^ 32 = 1 := by decide
  simp only [h1m] at hc hr ⊢
  obtain ⟨hd1, hd2, he4⟩ := conj_all3 hc
  have hk4 := eq_bv32 he4
  rw [← hk4] at hd1 hd2
  rcases lit_cases k3.toNat k2.toNat with hC | ⟨hk30, hk364, hk2lt, hC⟩
  · rw [hC, extc_ult_def, extc_cmp_bad_l] at hl; exact absurd rfl hl
  rw [hC] at hd1 hd2 hl ⊢
  generalize BitVec.ofNat k3.toNat k2.toNat = c at hd1 hd2 hl ⊢
  rw [extc_lit (v := 1) (by decide) (by decide) (by decide)] at hr ⊢
  have hx4 : k4.toNat ≤ k4.toNat ∧ k4.toNat < w0 :=
    extc_extract_ok (fun h => by rw [h, extc_eq_bad_l] at hr; exact absurd rfl hr)
  rw [extc_extract_val _ hx4] at hr ⊢
  rw [extc_sext_val _ _ (by omega)] at hl ⊢
  have hnm : w0 + k1.toNat = k3.toNat := extc_ult_width hl
  have hk4n : k4.toNat < k3.toNat := by omega
  have hk4e : k4.toNat = w0 - 1 := by rw [hk4, toNat_sub_one32 (by omega) (by rw [two32]; omega)]
  rw [extc_lit (v := k4.toNat) hk30 hk364 (Nat.lt_trans hk4n Nat.lt_two_pow_self),
    extc_lit (v := 0) hk30 hk364 (Nat.two_pow_pos _),
    extc_bvnot_val _ hk30, extc_shl_val _ _ hk30, extc_bvnot_val _ hk30, extc_ule _ _ rfl, BitVec.toNat_not,
    extc_toNat_shl_allOnes hk4n] at hd1
  rw [extc_lit (v := 1) hk30 hk364 (Nat.one_lt_two_pow hk30),
    extc_lit (v := k4.toNat) hk30 hk364 (Nat.lt_trans hk4n Nat.lt_two_pow_self),
    extc_shl_val _ _ hk30, extc_bvnot_val _ hk30, extc_ule _ _ rfl, BitVec.toNat_not, extc_toNat_shl_one hk4n] at hd2
  rw [extc_ult _ _ hnm, extc_eq_bits _ _ (by omega)]
  congr 1
  exact extc_arith151 x0 c hnm.symm (by omega) (extc_bool_true hd1) (extc_bool_true hd2)

end Bcf
