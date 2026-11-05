/-!
# Bit-vector identities used by the rewrite and trusted-shape proofs

Pure `BitVec` facts, proved bitwise.
-/

namespace Bcf

open BitVec

theorem bv_ext {w : Nat} {x y : BitVec w} (h : ∀ i, i < w → x.getLsbD i = y.getLsbD i) : x = y :=
  BitVec.eq_of_getLsbD_eq_iff.mpr h

/-- `x & y` split at bit `k`. -/
theorem and_split {w : Nat} (x y : BitVec w) (k : Nat) (hk1 : 1 ≤ k) (hk2 : k ≤ w - 1) :
    x &&& y = ((extractLsb (w - 1) k x &&& extractLsb (w - 1) k y) ++
               (extractLsb (k - 1) 0 x &&& extractLsb (k - 1) 0 y)).cast (by omega) := by
  apply bv_ext
  intro i hi
  simp only [getLsbD_and, getLsbD_cast, getLsbD_append, getLsbD_extractLsb]
  split
  · rename_i h
    simp only [Nat.zero_add]
    have : i < k - 1 + 1 := by omega
    simp [this]
  · rename_i h
    have h1 : i - (k - 1 + 1) < w - 1 - k + 1 := by omega
    have h2 : k + (i - (k - 1 + 1)) = i := by omega
    simp [h1, h2]

/-- `repeat` as iterated concatenation (`List.replicate` folded MSB-first). -/
theorem replicate_succ_cast {w : Nat} (x : BitVec w) (n : Nat) :
    x.replicate (n + 1) = (x ++ x.replicate n).cast (by rw [Nat.mul_succ, Nat.add_comm]) := by
  apply bv_ext
  intro i hi
  simp only [getLsbD_replicate, getLsbD_cast, getLsbD_append]
  split
  · rename_i h
    rw [decide_eq_true hi, decide_eq_true h]
  · rename_i h
    have h1 : i - w * n < w := by rw [Nat.mul_succ] at hi; omega
    have h2 : i % w = i - w * n := by
      have : i = (i - w * n) + w * n := by omega
      conv => lhs; rw [this]
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt h1
    rw [decide_eq_true hi, Bool.true_and, h2]

theorem ult_zero {w : Nat} (x : BitVec w) : x.ult 0#w = false := by
  simp [BitVec.ult]

theorem toNat_ne_zero_of_ne {w : Nat} {x : BitVec w} (h : x ≠ 0#w) : x.toNat ≠ 0 :=
  fun h0 => h (BitVec.toNat_eq.mpr (by simpa using h0))

theorem zero_ult {w : Nat} (x : BitVec w) : (0#w).ult x = !decide (x = 0#w) := by
  by_cases h : x = 0#w
  · subst h; simp [BitVec.ult]
  · simp [BitVec.ult, h, Nat.pos_of_ne_zero (toNat_ne_zero_of_ne h)]

theorem ule_zero {w : Nat} (x : BitVec w) : x.ule 0#w = decide (x = 0#w) := by
  by_cases h : x = 0#w
  · subst h; simp [BitVec.ule]
  · simp [BitVec.ule, h, toNat_ne_zero_of_ne h]

theorem ult_one {w : Nat} (hw : 0 < w) (x : BitVec w) : x.ult (BitVec.ofNat w 1) = decide (x = 0#w) := by
  have h1 : (BitVec.ofNat w 1).toNat = 1 := by
    rw [toNat_ofNat]; exact Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))
  by_cases h : x = 0#w
  · subst h; simp [BitVec.ult, h1]
  · simp [BitVec.ult, h, h1, Nat.lt_one_iff, toNat_ne_zero_of_ne h]

theorem ule_allOnes' {w : Nat} (x : BitVec w) : x.ule (BitVec.ofNat w (2 ^ w - 1)) = true := by
  have h1 : (2 ^ w - 1) % 2 ^ w = 2 ^ w - 1 := Nat.mod_eq_of_lt (by have := Nat.two_pow_pos w; omega)
  have := x.isLt
  simp [BitVec.ule, h1]
  omega

end Bcf
