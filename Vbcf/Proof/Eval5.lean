import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Eval4

/-!
# Vbcf proofs: the Eval family, part 5 — the arithmetic of the two-argument group
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf


theorem cv_bw64_eq (p : Prop) [Decidable p] : BitVec.setWidth 64 (bw p) = if p then 1#64 else 0#64 := by
  unfold bw; split <;> rfl

theorem cv_bvBin_inv {w' : Nat} {f : BitVec w' → BitVec w' → BitVec w'} {v1 v2 : Bcf.Val}
    {t : Bcf.Ty} {r1 r2 : BitVec 32} {vl1 vl2 : BitVec 64} (h1 : CvRep r1 vl1 v1)
    (h2 : CvRep r2 vl2 v2) (hty : (bvBin w' f [v1, v2]).ty = some t) :
    ∃ x y : BitVec w', v1 = .bv w' x ∧ v2 = .bv w' y ∧ t = .bv w' ∧
      bvBin w' f [v1, v2] = .bv w' (f x y) ∧ vl1.toNat = x.toNat ∧ vl2.toNat = y.toNat ∧
      r2 = BitVec.ofNat 32 w' := by
  rcases h1.cases with ⟨b1, rfl⟩ | ⟨n, x, rfl⟩
  · simp [bvBin] at hty
  rcases h2.cases with ⟨b2, rfl⟩ | ⟨m, y, rfl⟩
  · simp [bvBin] at hty
  by_cases hn : n = w'
  · subst hn
    by_cases hm : m = n
    · subst hm
      by_cases h0 : m = 0
      · simp [bvBin, h0] at hty
      · simp [bvBin, h0] at hty ⊢
        exact ⟨hty.symm, h1.2.2.2, h2.2.2.2, by rw [← h2.1, bv_ofNat_toNat]⟩
    · simp [bvBin, hm] at hty
  · simp [bvBin, hn] at hty

theorem cvsem_sub {ρ : Assign} {w' : Nat} {v1 v2 : Bcf.Val} {r1 r2 w : BitVec 32}
    {vl1 vl2 : BitVec 64} {t : Bcf.Ty} (h1 : CvRep r1 vl1 v1) (h2 : CvRep r2 vl2 v2)
    (hty : (Op.eval ρ (.bvSub w') [v1, v2]).ty = some t) (hw : CvW t w) :
    CvRep w (vl1 - vl2 &&& mW w) (Op.eval ρ (.bvSub w') [v1, v2]) := by
  simp only [Op.eval] at hty ⊢
  obtain ⟨x, y, rfl, rfl, rfl, he, hx, hy, -⟩ := cv_bvBin_inv h1 h2 hty
  rw [he]
  obtain ⟨hk1, hk2, rfl⟩ := hw.bv
  apply CvRep.of_bv hw
  rw [cv_and_mW hk1 hk2, cv_setWidth_sub hk2, cv_trunc_of hk2 hx, cv_trunc_of hk2 hy]

/-- Equality of represented scalars is equality of words. -/
theorem cvsem_eqv {neg : Bool} {ρ : Assign} {op : Op} (hop : Op.eval ρ op = eqEval neg)
    {v1 v2 : Bcf.Val} {r1 r2 w : BitVec 32} {vl1 vl2 : BitVec 64} {t : Bcf.Ty}
    (h1 : CvRep r1 vl1 v1) (h2 : CvRep r2 vl2 v2)
    (hty : (Op.eval ρ op [v1, v2]).ty = some t) (hw : CvW t w) :
    CvRep w (if (if neg then ¬ vl1 = vl2 else vl1 = vl2) then 1#64 else 0#64) (Op.eval ρ op [v1, v2]) := by
  rw [hop] at hty ⊢
  rcases h1.cases with ⟨b1, rfl⟩ | ⟨n, x, rfl⟩ <;>
  rcases h2.cases with ⟨b2, rfl⟩ | ⟨m, y, rfl⟩
  · simp [eqEval, Val.eqv] at hty ⊢
    subst hty
    apply CvRep.of_bool hw
    rw [h1.2, h2.2]
    cases b1 <;> cases b2 <;> cases neg <;> decide
  · simp [eqEval, Val.eqv] at hty
  · simp [eqEval, Val.eqv] at hty
  · by_cases hm : m = n
    · subst hm
      simp [eqEval, Val.eqv] at hty ⊢
      subst hty
      apply CvRep.of_bool hw
      have e : vl1 = vl2 ↔ x = y := by
        rw [← BitVec.toNat_inj, h1.2.2.2, h2.2.2.2, BitVec.toNat_inj]
      cases neg <;> simp [e]
    · simp [eqEval, Val.eqv, hm] at hty

theorem cvsem_implies {ρ : Assign} {v1 v2 : Bcf.Val} {r1 r2 w : BitVec 32}
    {vl1 vl2 : BitVec 64} {t : Bcf.Ty} (h1 : CvRep r1 vl1 v1) (h2 : CvRep r2 vl2 v2)
    (hty : (Op.eval ρ .implies [v1, v2]).ty = some t) (hw : CvW t w) :
    CvRep w (1#64 - vl1 ||| vl2) (Op.eval ρ .implies [v1, v2]) := by
  simp only [Op.eval] at hty ⊢
  rcases h1.cases with ⟨b1, rfl⟩ | ⟨n, x, rfl⟩ <;>
  rcases h2.cases with ⟨b2, rfl⟩ | ⟨m, y, rfl⟩ <;> simp [impliesEval] at hty ⊢
  subst hty
  apply CvRep.of_bool hw
  rw [h1.2, h2.2]
  cases b1 <;> cases b2 <;> decide

/-- Unsigned comparisons. -/
theorem cvsem_cmpU {ρ : Assign} {op : Op} {f : {w : Nat} → BitVec w → BitVec w → Bool}
    (hop : Op.eval ρ op = bvCmp f) {g : BitVec 64 → BitVec 64 → Prop} [∀ a b, Decidable (g a b)]
    (hfg : ∀ {n : Nat} (x y : BitVec n) (a b : BitVec 64), a.toNat = x.toNat → b.toNat = y.toNat →
      (g a b ↔ f x y = true))
    {v1 v2 : Bcf.Val} {r1 r2 w : BitVec 32} {vl1 vl2 : BitVec 64} {t : Bcf.Ty}
    (h1 : CvRep r1 vl1 v1) (h2 : CvRep r2 vl2 v2)
    (hty : (Op.eval ρ op [v1, v2]).ty = some t) (hw : CvW t w) :
    CvRep w (if g vl1 vl2 then 1#64 else 0#64) (Op.eval ρ op [v1, v2]) := by
  rw [hop] at hty ⊢
  rcases h1.cases with ⟨b1, rfl⟩ | ⟨n, x, rfl⟩
  · simp [bvCmp] at hty
  rcases h2.cases with ⟨b2, rfl⟩ | ⟨m, y, rfl⟩
  · simp [bvCmp] at hty
  by_cases hm : m = n
  · subst hm
    simp [bvCmp] at hty ⊢
    subst hty
    apply CvRep.of_bool hw
    have := hfg x y vl1 vl2 h1.2.2.2 h2.2.2.2
    by_cases hf : f x y = true
    · simp [hf, this.mpr hf]
    · simp only [Bool.not_eq_true] at hf
      simp [hf, show ¬ g vl1 vl2 from fun hg => by simp [this.mp hg] at hf]
  · simp [bvCmp, hm] at hty

/-! ## Words representing `k`-bit vectors -/

section rep
variable {k : Nat} (hk1 : 1 ≤ k) (hk2 : k ≤ 64)
include hk1 hk2

theorem cvrep_and_mW {a : BitVec 64} {x : BitVec k} (h : (a.setWidth k) = x) :
    (a &&& mW (BitVec.ofNat 32 k)).toNat = x.toNat := by
  rw [cv_and_mW hk1 hk2, h]

theorem cvrep_negm {a : BitVec 64} {x : BitVec k} (h : a.toNat = x.toNat) :
    ((0#64 - a) &&& mW (BitVec.ofNat 32 k)).toNat = (-x).toNat := by
  rw [cv_and_mW hk1 hk2, cv_setWidth_sub hk2, cv_trunc_of hk2 h]; simp

theorem cvrep_udiv {a b : BitVec 64} {x y : BitVec k} (ha : a.toNat = x.toNat) (hb : b.toNat = y.toNat) :
    (udivM a b (mW (BitVec.ofNat 32 k))).toNat = (BitVec.smtUDiv x y).toNat := by
  rw [BitVec.smtUDiv_eq]
  unfold udivM
  have e : b = 0#64 ↔ y = 0#k := by
    rw [← BitVec.toNat_inj, ← BitVec.toNat_inj, hb]; simp
  by_cases hy : y = 0#k
  · rw [ite_eq_left (e.mpr hy), ite_eq_left hy, mW_bv_toNat hk1 hk2, BitVec.toNat_allOnes]
  · rw [ite_eq_right (fun h => hy (e.mp h)), ite_eq_right hy, BitVec.toNat_udiv, BitVec.toNat_udiv, ha, hb]

omit hk1 hk2 in
theorem cvrep_umod {a b : BitVec 64} {x y : BitVec k} (ha : a.toNat = x.toNat) (hb : b.toNat = y.toNat) :
    (umodM a b).toNat = (BitVec.umod x y).toNat := by
  show _ = (x % y).toNat
  rw [BitVec.toNat_umod, ← ha, ← hb]
  unfold umodM
  by_cases hy : b = 0#64
  · rw [ite_eq_left hy, hy]; simp
  · rw [ite_eq_right hy, BitVec.toNat_umod]

theorem cvrep_addm {a b : BitVec 64} {x y : BitVec k} (ha : a.toNat = x.toNat) (hb : b.toNat = y.toNat) :
    ((a + b) &&& mW (BitVec.ofNat 32 k)).toNat = (x + y).toNat := by
  rw [cv_and_mW hk1 hk2, BitVec.setWidth_add _ _ hk2, cv_trunc_of hk2 ha, cv_trunc_of hk2 hb]

theorem cvrep_subm {a b : BitVec 64} {x y : BitVec k} (ha : a.toNat = x.toNat) (hb : b.toNat = y.toNat) :
    ((a - b) &&& mW (BitVec.ofNat 32 k)).toNat = (x - y).toNat := by
  rw [cv_and_mW hk1 hk2, cv_setWidth_sub hk2, cv_trunc_of hk2 ha, cv_trunc_of hk2 hb]

omit hk1 hk2 in
theorem cvrep_zero {a : BitVec 64} {x : BitVec k} (ha : a.toNat = x.toNat) : a = 0#64 ↔ x = 0#k := by
  rw [← BitVec.toNat_inj, ← BitVec.toNat_inj, ha]; simp

end rep

theorem cvrep_sdiv {k : Nat} (hk1 : 1 ≤ k) (hk2 : k ≤ 64) {a b : BitVec 64} {x y : BitVec k}
    (ha : a.toNat = x.toNat) (hb : b.toNat = y.toNat) :
    (sdivM a b (mW (BitVec.ofNat 32 k)) (k - 1)).toNat = (BitVec.smtSDiv x y).toNat := by
  have mx := cv_msb_iff_bit hk1 hk2 ha
  have my := cv_msb_iff_bit hk1 hk2 hb
  have na := cvrep_negm hk1 hk2 ha
  have nb := cvrep_negm hk1 hk2 hb
  unfold sdivM BitVec.smtSDiv
  cases hxm : x.msb <;> cases hym : y.msb <;> simp only [hxm, hym] at mx my
  · rw [ite_eq_left ⟨mx.mpr trivial, my.mpr trivial⟩]; exact cvrep_udiv hk1 hk2 ha hb
  · rw [ite_eq_right (fun h => by simp at my; exact my h.2), ite_eq_left (mx.mpr trivial)]
    exact cvrep_negm hk1 hk2 (cvrep_udiv hk1 hk2 ha nb)
  · rw [ite_eq_right (fun h => by simp at mx; exact mx h.1), ite_eq_right (by simpa using mx),
      ite_eq_left (my.mpr trivial)]
    exact cvrep_negm hk1 hk2 (cvrep_udiv hk1 hk2 na hb)
  · rw [ite_eq_right (fun h => by simp at mx; exact mx h.1), ite_eq_right (by simpa using mx),
      ite_eq_right (by simpa using my)]
    exact cvrep_udiv hk1 hk2 na nb

theorem cvrep_smod {k : Nat} (hk1 : 1 ≤ k) (hk2 : k ≤ 64) {a b : BitVec 64} {x y : BitVec k}
    (ha : a.toNat = x.toNat) (hb : b.toNat = y.toNat) :
    (smodM a b (mW (BitVec.ofNat 32 k)) (k - 1)).toNat = (BitVec.smod x y).toNat := by
  have mx := cv_msb_iff_bit hk1 hk2 ha
  have my := cv_msb_iff_bit hk1 hk2 hb
  have na := cvrep_negm hk1 hk2 ha
  have nb := cvrep_negm hk1 hk2 hb
  unfold smodM BitVec.smod
  cases hxm : x.msb <;> cases hym : y.msb <;> simp only [hxm, hym] at mx my
  · rw [ite_eq_left ⟨mx.mpr trivial, my.mpr trivial⟩]; exact cvrep_umod ha hb
  · rw [ite_eq_right (fun h => by simp at my; exact my h.2), ite_eq_left (mx.mpr trivial)]
    have hu := cvrep_umod ha nb
    have hz := cvrep_zero hu
    simp only
    by_cases h0 : BitVec.umod x (-y) = 0#k
    · rw [ite_eq_left (hz.mpr h0), ite_eq_left (show BitVec.umod x (.neg y) = .zero k from h0)]
      rw [show BitVec.umod x (.neg y) = 0#k from h0]; rfl
    · rw [ite_eq_right (fun h => h0 (hz.mp h)), ite_eq_right (show ¬ BitVec.umod x (.neg y) = .zero k from h0)]
      exact cvrep_addm hk1 hk2 hu hb
  · rw [ite_eq_right (fun h => by simp at mx; exact mx h.1), ite_eq_right (by simpa using mx),
      ite_eq_left (my.mpr trivial)]
    have hu := cvrep_umod na hb
    have hz := cvrep_zero hu
    simp only
    by_cases h0 : BitVec.umod (-x) y = 0#k
    · rw [ite_eq_left (hz.mpr h0), ite_eq_left (show BitVec.umod (.neg x) y = .zero k from h0)]
      rw [show BitVec.umod (.neg x) y = 0#k from h0]; rfl
    · rw [ite_eq_right (fun h => h0 (hz.mp h)), ite_eq_right (show ¬ BitVec.umod (.neg x) y = .zero k from h0)]
      exact cvrep_subm hk1 hk2 hb hu
  · rw [ite_eq_right (fun h => by simp at mx; exact mx h.1), ite_eq_right (by simpa using mx),
      ite_eq_right (by simpa using my)]
    exact cvrep_negm hk1 hk2 (cvrep_umod na nb)

theorem cvsem_udiv {ρ : Assign} {w' : Nat} {v1 v2 : Bcf.Val} {r1 r2 w : BitVec 32}
    {vl1 vl2 : BitVec 64} {t : Bcf.Ty} (h1 : CvRep r1 vl1 v1) (h2 : CvRep r2 vl2 v2)
    (hty : (Op.eval ρ (.bvUdiv w') [v1, v2]).ty = some t) (hw : CvW t w) :
    CvRep w (udivM vl1 vl2 (mW w)) (Op.eval ρ (.bvUdiv w') [v1, v2]) := by
  simp only [Op.eval] at hty ⊢
  obtain ⟨x, y, rfl, rfl, rfl, he, hx, hy, -⟩ := cv_bvBin_inv h1 h2 hty
  rw [he]
  obtain ⟨hk1, hk2, rfl⟩ := hw.bv
  exact CvRep.of_bv hw (cvrep_udiv hk1 hk2 hx hy)

theorem cvsem_urem {ρ : Assign} {w' : Nat} {v1 v2 : Bcf.Val} {r1 r2 w : BitVec 32}
    {vl1 vl2 : BitVec 64} {t : Bcf.Ty} (h1 : CvRep r1 vl1 v1) (h2 : CvRep r2 vl2 v2)
    (hty : (Op.eval ρ (.bvUrem w') [v1, v2]).ty = some t) (hw : CvW t w) :
    CvRep w (umodM vl1 vl2) (Op.eval ρ (.bvUrem w') [v1, v2]) := by
  simp only [Op.eval] at hty ⊢
  obtain ⟨x, y, rfl, rfl, rfl, he, hx, hy, -⟩ := cv_bvBin_inv h1 h2 hty
  rw [he]
  obtain ⟨hk1, hk2, rfl⟩ := hw.bv
  exact CvRep.of_bv hw (cvrep_umod hx hy)

theorem cvsem_sdiv {ρ : Assign} {w' : Nat} {v1 v2 : Bcf.Val} {r1 r2 w : BitVec 32}
    {vl1 vl2 : BitVec 64} {t : Bcf.Ty} (h1 : CvRep r1 vl1 v1) (h2 : CvRep r2 vl2 v2)
    (hty : (Op.eval ρ (.bvSdiv w') [v1, v2]).ty = some t) (hw : CvW t w) :
    CvRep w (sdivM vl1 vl2 (mW w) (w.toNat - 1)) (Op.eval ρ (.bvSdiv w') [v1, v2]) := by
  simp only [Op.eval] at hty ⊢
  obtain ⟨x, y, rfl, rfl, rfl, he, hx, hy, -⟩ := cv_bvBin_inv h1 h2 hty
  rw [he]
  obtain ⟨hk1, hk2, rfl⟩ := hw.bv
  rw [bv_toNat_ofNat (by omega)]
  exact CvRep.of_bv hw (cvrep_sdiv hk1 hk2 hx hy)

theorem cvsem_smod {ρ : Assign} {w' : Nat} {v1 v2 : Bcf.Val} {r1 r2 w : BitVec 32}
    {vl1 vl2 : BitVec 64} {t : Bcf.Ty} (h1 : CvRep r1 vl1 v1) (h2 : CvRep r2 vl2 v2)
    (hty : (Op.eval ρ (.bvSmod w') [v1, v2]).ty = some t) (hw : CvW t w) :
    CvRep w (smodM vl1 vl2 (mW w) (w.toNat - 1)) (Op.eval ρ (.bvSmod w') [v1, v2]) := by
  simp only [Op.eval] at hty ⊢
  obtain ⟨x, y, rfl, rfl, rfl, he, hx, hy, -⟩ := cv_bvBin_inv h1 h2 hty
  rw [he]
  obtain ⟨hk1, hk2, rfl⟩ := hw.bv
  rw [bv_toNat_ofNat (by omega)]
  exact CvRep.of_bv hw (cvrep_smod hk1 hk2 hx hy)

/-- The width word of a bit-vector node. -/
theorem CvW.bv_bounds {k : Nat} {w : BitVec 32} (hw : CvW (.bv k) w) :
    1 ≤ w.toNat ∧ w.toNat ≤ 64 := by
  obtain ⟨h1, h2, rfl⟩ := hw.bv
  rw [bv_toNat_ofNat (by omega)]; exact ⟨h1, h2⟩

theorem cv_lt_ofNat64 {k : Nat} (hk : k ≤ 64) {y : BitVec 64} :
    y < BitVec.ofNat 64 k ↔ y.toNat < k := by
  rw [BitVec.lt_def, BitVec.toNat_ofNat]
  rcases Nat.lt_or_ge k 64 with h | h
  · rw [Nat.mod_eq_of_lt (by omega)]
  · have : k = 64 := by omega
    subst this
    simp

theorem cvsem_shl {ρ : Assign} {w' : Nat} {v1 v2 : Bcf.Val} {r1 r2 : BitVec 32}
    {vl1 vl2 : BitVec 64} {t : Bcf.Ty} (h1 : CvRep r1 vl1 v1) (h2 : CvRep r2 vl2 v2)
    (hty : (Op.eval ρ (.bvShl w') [v1, v2]).ty = some t) (hw : CvW t (BitVec.ofNat 32 w')) :
    CvRep (BitVec.ofNat 32 w') (if vl2 < BitVec.ofNat 64 w' then vl1 <<< vl2.toNat &&& mW (BitVec.ofNat 32 w')
      else 0#64) (Op.eval ρ (.bvShl w') [v1, v2]) := by
  simp only [Op.eval] at hty ⊢
  obtain ⟨x, y, rfl, rfl, rfl, he, hx, hy, -⟩ := cv_bvBin_inv h1 h2 hty
  rw [he]
  obtain ⟨hk1, hk2, -⟩ := hw.bv
  apply CvRep.of_bv hw
  rw [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft]
  by_cases hlt : vl2 < BitVec.ofNat 64 w'
  · rw [ite_eq_left hlt, cv_and_mW hk1 hk2, BitVec.toNat_setWidth, BitVec.toNat_shiftLeft,
      Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hk2), hx, hy]
  · rw [ite_eq_right hlt, cv_lt_ofNat64 hk2, hy] at *
    simp only [BitVec.toNat_ofNat, Nat.zero_mod]
    rw [Nat.shiftLeft_eq]
    have hd : 2 ^ w' ∣ 2 ^ y.toNat := Nat.pow_dvd_pow 2 (by omega)
    exact (Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hd (Nat.dvd_mul_left _ _))).symm

theorem cvsem_lshr {ρ : Assign} {w' : Nat} {v1 v2 : Bcf.Val} {r1 r2 : BitVec 32}
    {vl1 vl2 : BitVec 64} {t : Bcf.Ty} (h1 : CvRep r1 vl1 v1) (h2 : CvRep r2 vl2 v2)
    (hty : (Op.eval ρ (.bvLshr w') [v1, v2]).ty = some t) (hw : CvW t (BitVec.ofNat 32 w')) :
    CvRep (BitVec.ofNat 32 w') (if vl2 < BitVec.ofNat 64 w' then vl1 >>> vl2.toNat else 0#64)
      (Op.eval ρ (.bvLshr w') [v1, v2]) := by
  simp only [Op.eval] at hty ⊢
  obtain ⟨x, y, rfl, rfl, rfl, he, hx, hy, -⟩ := cv_bvBin_inv h1 h2 hty
  rw [he]
  obtain ⟨hk1, hk2, -⟩ := hw.bv
  apply CvRep.of_bv hw
  rw [BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight]
  by_cases hlt : vl2 < BitVec.ofNat 64 w'
  · rw [ite_eq_left hlt, BitVec.toNat_ushiftRight, hx, hy]
  · rw [ite_eq_right hlt, cv_lt_ofNat64 hk2, hy] at *
    simp only [BitVec.toNat_ofNat, Nat.zero_mod]
    rw [Nat.shiftRight_eq_div_pow]
    have : x.toNat < 2 ^ y.toNat :=
      Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) (by omega))
    rw [Nat.div_eq_of_lt this]

/-- What `cval` computes for `bvashr`. -/
def ashrC (vl1 vl2 m : BitVec 64) (w' : Nat) : BitVec 64 :=
  if BitVec.ofNat 64 w' ≤ vl2 then (if vl1 >>> (w' - 1) &&& 1#64 = 0#64 then 0#64 else m)
  else if vl1 >>> (w' - 1) &&& 1#64 = 0#64 then vl1 >>> vl2.toNat
  else vl1 >>> vl2.toNat ||| m &&& ~~~(m >>> vl2.toNat)

theorem cv_div_compl {P Q x : Nat} (hP : 0 < P) (hx : x < P * Q) :
    x / P + (P * Q - 1 - x) / P = Q - 1 := by
  have hq : x / P < Q := (Nat.div_lt_iff_lt_mul hP).mpr (by rw [Nat.mul_comm]; exact hx)
  have hr := Nat.mod_lt x hP
  have hd := Nat.div_add_mod x P
  generalize x / P = q at *
  generalize x % P = r at *
  have e : P * Q = P * (Q - 1 - q) + P * q + P := by
    rw [← Nat.mul_add, ← Nat.mul_succ]; congr 1; omega
  have e2 : P * Q - 1 - x = P * (Q - 1 - q) + (P - 1 - r) := by omega
  rw [e2, Nat.mul_add_div hP, Nat.div_eq_of_lt (by omega)]
  omega

theorem cv_pow_sub_one_div {w y : Nat} (h : y ≤ w) : (2 ^ w - 1) / 2 ^ y = 2 ^ (w - y) - 1 := by
  have hP := Nat.two_pow_pos y
  have hQ : 1 ≤ 2 ^ (w - y) := Nat.one_le_two_pow
  have e : 2 ^ w = 2 ^ y * 2 ^ (w - y) := by rw [← Nat.pow_add, Nat.add_sub_cancel' h]
  have e2 : 2 ^ w - 1 = 2 ^ y * (2 ^ (w - y) - 1) + (2 ^ y - 1) := by
    rw [Nat.mul_sub_one, e]
    have : 2 ^ y ≤ 2 ^ y * 2 ^ (w - y) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  rw [e2, Nat.mul_add_div hP, Nat.div_eq_of_lt (by omega)]
  omega

theorem cvsem_ashr {ρ : Assign} {w' : Nat} {v1 v2 : Bcf.Val} {r1 r2 : BitVec 32}
    {vl1 vl2 : BitVec 64} {t : Bcf.Ty} (h1 : CvRep r1 vl1 v1) (h2 : CvRep r2 vl2 v2)
    (hty : (Op.eval ρ (.bvAshr w') [v1, v2]).ty = some t) (hw : CvW t (BitVec.ofNat 32 w')) :
    CvRep (BitVec.ofNat 32 w') (ashrC vl1 vl2 (mW (BitVec.ofNat 32 w')) w')
      (Op.eval ρ (.bvAshr w') [v1, v2]) := by
  simp only [Op.eval] at hty ⊢
  obtain ⟨x, y, rfl, rfl, rfl, he, hx, hy, -⟩ := cv_bvBin_inv h1 h2 hty
  rw [he]
  obtain ⟨hk1, hk2, -⟩ := hw.bv
  apply CvRep.of_bv hw
  have mx := cv_msb_iff_bit hk1 hk2 hx
  have hxl := x.isLt
  rw [BitVec.toNat_sshiftRight, BitVec.msb_eq_decide] at *
  unfold ashrC
  by_cases hge : BitVec.ofNat 64 w' ≤ vl2
  · have hyw : w' ≤ y.toNat := by
      rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hy] at hge; exact hge
    have hpw : 2 ^ w' ≤ 2 ^ y.toNat := Nat.pow_le_pow_right (by decide) hyw
    rw [ite_eq_left hge]
    by_cases hb : vl1 >>> (w' - 1) &&& 1#64 = 0#64
    · have hm := mx.mp hb
      simp only [decide_eq_false_iff_not, Nat.not_le] at hm
      rw [ite_eq_left hb]
      simp only [show ¬ 2 ^ (w' - 1) ≤ x.toNat from Nat.not_le.mpr hm, decide_false,
        Bool.false_eq_true, ↓reduceIte]
      rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (by omega)]; rfl
    · have hm : 2 ^ (w' - 1) ≤ x.toNat := by
        have := (not_congr mx).mp hb; simpa using this
      rw [ite_eq_right hb, mW_bv_toNat hk1 hk2]
      simp only [hm, decide_true, ↓reduceIte]
      have hP : 2 ^ w' = 2 * 2 ^ (w' - 1) := by rw [← Nat.pow_succ']; congr 1; omega
      have hp2 : 2 ^ (w' - 1) ≤ 2 ^ y.toNat := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (by omega)]
      omega
  · have hyw : y.toNat < w' := by
      rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hy] at hge; omega
    rw [ite_eq_right hge]
    by_cases hb : vl1 >>> (w' - 1) &&& 1#64 = 0#64
    · have hm := mx.mp hb
      simp only [decide_eq_false_iff_not, Nat.not_le] at hm
      rw [ite_eq_left hb]
      simp only [show ¬ 2 ^ (w' - 1) ≤ x.toNat from Nat.not_le.mpr hm, decide_false,
        Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ushiftRight, hx, hy]
    · have hm : 2 ^ (w' - 1) ≤ x.toNat := by
        have := (not_congr mx).mp hb; simpa using this
      rw [ite_eq_right hb]
      simp only [hm, decide_true, ↓reduceIte]
      rw [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_not, BitVec.toNat_ushiftRight,
        BitVec.toNat_ushiftRight, mW_bv_toNat hk1 hk2, hx, hy, Nat.shiftRight_eq_div_pow,
        Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, cv_pow_sub_one_div (by omega)]
      have hq : x.toNat / 2 ^ y.toNat < 2 ^ (w' - y.toNat) := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, Nat.sub_add_cancel (by omega)]
        exact hxl
      rw [cv_nat_sext (by omega) (by omega) hk2 hq]
      have e : 2 ^ w' = 2 ^ y.toNat * 2 ^ (w' - y.toNat) := by
        rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
      have hdc := cv_div_compl (P := 2 ^ y.toNat) (Q := 2 ^ (w' - y.toNat)) (x := x.toNat)
        (Nat.two_pow_pos _) (by rw [← e]; exact hxl)
      rw [← e] at hdc
      have hQ1 : 1 ≤ 2 ^ (w' - y.toNat) := Nat.one_le_two_pow
      have hQw : 2 ^ (w' - y.toNat) ≤ 2 ^ w' := Nat.pow_le_pow_right (by decide) (by omega)
      generalize x.toNat / 2 ^ y.toNat = q at *
      generalize (2 ^ w' - 1 - x.toNat) / 2 ^ y.toNat = q' at *
      omega

/-- The children of a comparison: bit-vectors of one width `n`, which is the second
child's result word. -/
theorem cv_cmp_width {f : {w : Nat} → BitVec w → BitVec w → Bool} {v1 v2 : Bcf.Val}
    {r1 r2 : BitVec 32} {vl1 vl2 : BitVec 64} {t : Bcf.Ty} (h1 : CvRep r1 vl1 v1)
    (h2 : CvRep r2 vl2 v2) (hty : (bvCmp f [v1, v2]).ty = some t) :
    ∃ n, 1 ≤ n ∧ n ≤ 64 ∧ r2 = BitVec.ofNat 32 n := by
  rcases h2.cases with ⟨b2, rfl⟩ | ⟨m, y, rfl⟩
  · rcases h1.cases with ⟨b1, rfl⟩ | ⟨n, x, rfl⟩ <;> simp [bvCmp] at hty
  · exact ⟨m, h2.2.1, h2.2.2.1, by rw [← h2.1, bv_ofNat_toNat]⟩

/-- Flipping the top bit of a `k+1`-bit number. -/
theorem cv_xor_top {a k : Nat} (ha : a < 2 ^ (k + 1)) :
    a ^^^ 2 ^ k = if a < 2 ^ k then a + 2 ^ k else a - 2 ^ k := by
  have hd := Nat.div_add_mod (a ^^^ 2 ^ k) (2 ^ k)
  rw [Nat.xor_div_two_pow, Nat.xor_mod_two_pow, Nat.div_self (Nat.two_pow_pos k), Nat.mod_self,
    Nat.xor_zero] at hd
  have hP : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
  have hpos := Nat.two_pow_pos k
  generalize 2 ^ k = P at *
  by_cases h : a < P
  · rw [ite_eq_left h]
    rw [Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h] at hd
    simp at hd; omega
  · rw [ite_eq_right h]
    have h1 : a / P = 1 := by
      apply Nat.le_antisymm
      · have : a / P < 2 := by rw [Nat.div_lt_iff_lt_mul hpos]; omega
        omega
      · exact (Nat.le_div_iff_mul_le hpos).mpr (by omega)
    have h2 : a % P = a - P := by
      have := Nat.div_add_mod a P
      rw [h1] at this; omega
    rw [h1, h2] at hd
    simp at hd; omega

theorem cv_xor_sign {n : Nat} (h1 : 1 ≤ n) (h64 : n ≤ 64) {a : BitVec 64} {x : BitVec n}
    (ha : a.toNat = x.toNat) :
    (a ^^^ 1#64 <<< (n - 1)).toNat =
      if x.msb then x.toNat - 2 ^ (n - 1) else x.toNat + 2 ^ (n - 1) := by
  have hP : 2 ^ (n - 1) < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega)
  rw [BitVec.toNat_xor, BitVec.toNat_shiftLeft, ha]
  simp only [BitVec.toNat_ofNat, Nat.one_mod, Nat.reducePow, Nat.shiftLeft_eq, Nat.one_mul]
  rw [Nat.mod_eq_of_lt hP, cv_xor_top (by rw [Nat.sub_add_cancel h1]; exact x.isLt),
    BitVec.msb_eq_decide]
  by_cases hm : 2 ^ (n - 1) ≤ x.toNat
  · simp [hm, Nat.not_lt.mpr hm]
  · simp [hm, Nat.lt_of_not_le hm]

theorem cv_slt_flip {n : Nat} (h1 : 1 ≤ n) (h64 : n ≤ 64) {a b : BitVec 64} {x y : BitVec n}
    (ha : a.toNat = x.toNat) (hb : b.toNat = y.toNat) :
    (a ^^^ 1#64 <<< (n - 1) < b ^^^ 1#64 <<< (n - 1)) ↔ x.slt y = true := by
  rw [BitVec.lt_def, cv_xor_sign h1 h64 ha, cv_xor_sign h1 h64 hb, BitVec.slt_eq_ult, BitVec.msb_eq_decide,
    BitVec.msb_eq_decide, BitVec.ult]
  have hx := x.isLt; have hy := y.isLt
  have hP : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  generalize 2 ^ (n - 1) = P at *
  by_cases h1 : P ≤ x.toNat <;> by_cases h2 : P ≤ y.toNat <;> simp [h1, h2] <;> omega

theorem cv_sle_flip {n : Nat} (h1 : 1 ≤ n) (h64 : n ≤ 64) {a b : BitVec 64} {x y : BitVec n}
    (ha : a.toNat = x.toNat) (hb : b.toNat = y.toNat) :
    (a ^^^ 1#64 <<< (n - 1) ≤ b ^^^ 1#64 <<< (n - 1)) ↔ x.sle y = true := by
  rw [BitVec.le_def, cv_xor_sign h1 h64 ha, cv_xor_sign h1 h64 hb, BitVec.sle_eq_ule, BitVec.msb_eq_decide,
    BitVec.msb_eq_decide, BitVec.ule]
  have hx := x.isLt; have hy := y.isLt
  have hP : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  generalize 2 ^ (n - 1) = P at *
  by_cases h1 : P ≤ x.toNat <;> by_cases h2 : P ≤ y.toNat <;> simp [h1, h2] <;> omega

/-- Signed comparisons, with the width `n` the second child's result word. -/
theorem cvsem_cmpS {ρ : Assign} {op : Op} {f : {w : Nat} → BitVec w → BitVec w → Bool}
    (hop : Op.eval ρ op = bvCmp f) {g : BitVec 64 → BitVec 64 → Prop} [∀ a b, Decidable (g a b)]
    {n : Nat} (hfg : ∀ (x y : BitVec n) (a b : BitVec 64), a.toNat = x.toNat → b.toNat = y.toNat →
      (g a b ↔ f x y = true))
    {v1 v2 : Bcf.Val} {r1 w : BitVec 32} {vl1 vl2 : BitVec 64} {t : Bcf.Ty}
    (h1 : CvRep r1 vl1 v1) (h2 : CvRep (BitVec.ofNat 32 n) vl2 v2) (hn64 : n ≤ 64)
    (hty : (Op.eval ρ op [v1, v2]).ty = some t) (hw : CvW t w) :
    CvRep w (if g vl1 vl2 then 1#64 else 0#64) (Op.eval ρ op [v1, v2]) := by
  rw [hop] at hty ⊢
  rcases h1.cases with ⟨b1, rfl⟩ | ⟨n1, x, rfl⟩
  · simp [bvCmp] at hty
  rcases h2.cases with ⟨b2, rfl⟩ | ⟨m, y, rfl⟩
  · simp [bvCmp] at hty
  have hmn : m = n := by have := h2.1; rw [bv_toNat_ofNat (by omega)] at this; omega
  subst hmn
  by_cases hm : m = n1
  · subst hm
    simp [bvCmp] at hty ⊢
    subst hty
    apply CvRep.of_bool hw
    have := hfg x y vl1 vl2 h1.2.2.2 h2.2.2.2
    by_cases hf : f x y = true
    · simp [hf, this.mpr hf]
    · simp only [Bool.not_eq_true] at hf
      simp [hf, show ¬ g vl1 vl2 from fun hg => by simp [this.mp hg] at hf]
  · simp [bvCmp, hm] at hty

end Vbcf.Proof
