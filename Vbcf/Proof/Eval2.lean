import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Eval1

/-!
# Vbcf proofs: the Eval family, part 2 — the arithmetic of `cval`

Pure lemmas: what `cval` computes on 64-bit words represents `Op.eval` of the
represented children (`CvRep`), for each operator.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

theorem CvW.bool {w : BitVec 32} (h : CvW .bool w) : w = 100#32 := by
  rcases h with ⟨-, h⟩ | ⟨k, h, -⟩
  · exact h
  · cases h

theorem CvW.bv {w : BitVec 32} {k : Nat} (h : CvW (.bv k) w) :
    1 ≤ k ∧ k ≤ 64 ∧ w = BitVec.ofNat 32 k := by
  rcases h with ⟨h, -⟩ | ⟨k', h, h1, h2, h3⟩
  · cases h
  · cases h; exact ⟨h1, h2, h3⟩

theorem CvRep.bool_iff {r : BitVec 32} {vl : BitVec 64} {b : Bool} :
    CvRep r vl (.bool b) ↔ r = 100#32 ∧ vl = (if b then 1#64 else 0#64) := Iff.rfl

theorem CvRep.bv_iff {r : BitVec 32} {vl : BitVec 64} {w : Nat} {x : BitVec w} :
    CvRep r vl (.bv w x) ↔ r.toNat = w ∧ 1 ≤ w ∧ w ≤ 64 ∧ vl.toNat = x.toNat := Iff.rfl

/-- A represented value is a boolean or a bit-vector. -/
theorem CvRep.cases {r : BitVec 32} {vl : BitVec 64} {v : Bcf.Val} (h : CvRep r vl v) :
    (∃ b, v = .bool b) ∨ (∃ w x, v = .bv w x) := by
  cases v with
  | bool b => exact Or.inl ⟨b, rfl⟩
  | bv w x => exact Or.inr ⟨w, x, rfl⟩
  | list => exact h.elim
  | bad => exact h.elim

/-! ## if-then-else -/

theorem cvsem_ite {ρ : Assign} {op : Op} (hop : op = .boolIte ∨ ∃ k, op = .bvIte k)
    {v1 v2 v3 : Bcf.Val} {r1 r2 r3 w : BitVec 32} {x y z : BitVec 64} {t : Bcf.Ty}
    (h1 : CvRep r1 x v1) (h2 : CvRep r2 y v2) (h3 : CvRep r3 z v3)
    (hty : (Op.eval ρ op [v1, v2, v3]).ty = some t) (hw : CvW t w) :
    CvRep w (if x ≠ 0#64 then y else z) (Op.eval ρ op [v1, v2, v3]) := by
  rcases hop with rfl | ⟨k, rfl⟩
  · rcases h1.cases with ⟨c, rfl⟩ | ⟨w1, x1, rfl⟩ <;>
    rcases h2.cases with ⟨a, rfl⟩ | ⟨w2, x2, rfl⟩ <;>
    rcases h3.cases with ⟨b, rfl⟩ | ⟨w3, x3, rfl⟩ <;>
    simp [Op.eval, boolIteEval] at hty ⊢
    subst hty
    rw [hw.bool]
    simp only [CvRep] at h1 h2 h3 ⊢
    obtain ⟨-, rfl⟩ := h1; obtain ⟨-, rfl⟩ := h2; obtain ⟨-, rfl⟩ := h3
    cases c <;> simp
  · rcases h1.cases with ⟨c, rfl⟩ | ⟨w1, x1, rfl⟩ <;>
    rcases h2.cases with ⟨a, rfl⟩ | ⟨w2, x2, rfl⟩ <;>
    rcases h3.cases with ⟨b, rfl⟩ | ⟨w3, x3, rfl⟩ <;>
    simp [Op.eval, bvIteEval, Val.asCond] at hty ⊢
    · by_cases e2 : w2 = k
      · subst w2
        by_cases e3 : w3 = k
        · subst w3
          by_cases hk : k = 0
          · simp [hk] at hty
          simp [hk] at hty ⊢
          subst hty
          obtain ⟨hk1, hk2, rfl⟩ := hw.bv
          simp only [CvRep] at h1 h2 h3 ⊢
          obtain ⟨-, rfl⟩ := h1
          refine ⟨bv_toNat_ofNat (by omega), hk1, hk2, ?_⟩
          cases c <;> simp [h2.2.2.2, h3.2.2.2]
        · simp [e3] at hty
      · simp [e2] at hty
    · by_cases e1 : w1 = 1
      · subst w1
        by_cases e2 : w2 = k
        · subst w2
          by_cases e3 : w3 = k
          · subst w3
            by_cases hk : k = 0
            · simp [hk] at hty
            simp [hk] at hty ⊢
            subst hty
            obtain ⟨hk1, hk2, rfl⟩ := hw.bv
            simp only [CvRep] at h1 h2 h3 ⊢
            refine ⟨bv_toNat_ofNat (by omega), hk1, hk2, ?_⟩
            have hx : x = 0#64 ↔ x1.getLsbD 0 = false := by
              have := h1.2.2.2
              have hx1 := x1.isLt
              rw [← BitVec.toNat_inj, this]
              rw [BitVec.getLsbD, Nat.testBit_zero]
              simp; omega
            by_cases hx0 : x = 0#64
            · have : x1[0] = false := by have := hx.mp hx0; simpa using this
              simp [hx0, this, h3.2.2.2]
            · have : x1[0] = true := by simpa [hx0] using hx
              simp [hx0, this, h2.2.2.2]
          · simp [e3] at hty
        · simp [e2] at hty
      · simp [e1] at hty

end Vbcf.Proof
