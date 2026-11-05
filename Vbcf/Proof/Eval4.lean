import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Eval3

/-!
# Vbcf proofs: the Eval family, part 4 — the one-argument group of `cval`
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

open Lean in
/-- `cv_simp` without the pool: for the arithmetic parts of `cval`. -/
macro "cv_simp0" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let h := mkIdent `h
  let hs := mkIdent `hs
  `(tactic| simp (disch := rule_disch) [EmbC.evalE, EmbC.evalBin, EmbC.evalArith, EmbC.evalCast,
      EmbC.evalArgs, EmbC.Env.get, EmbC.Env.ty, EmbC.Env.set, EmbC.Env.assign, EmbC.Val.toIdx,
      ofBool_eq, land_some, land_some', lor_some, lor_some', cvEnv,
      HasCK.ld_val $hs (Holds.ck $h), uv_inj, uv_le, uv_lt, uv_toNat, mod32, uv_add, $ts,*])

macro "cv_simp0" : tactic => `(tactic| cv_simp0 [])

theorem cv_dec_lt {d : BitVec 32} (hd : d ≠ 0#32) : (d - 1#32).toNat < d.toNat := by
  have : d.toNat ≠ 0 := fun e => hd (BitVec.eq_of_toNat_eq (by simpa using e))
  rw [BitVec.toNat_sub]; simp; omega

/-- The common start of the one-argument group: evaluate the child. -/
theorem grpU_core {d : BitVec 32} (IH : ∀ d' : BitVec 32, d'.toNat < d.toNat → CvalSpecD (State := State) d')
    (hd : d ≠ 0#32) {W : World} {sb : Nat} {c : CMem} {posOf : Nat → Nat} {st : VSt} {i : Nat}
    {op : Op} {a : Nat} {hdr code nn par lo hi w cw i0 : BitVec 32}
    {x y z m sbv acc : BitVec 64} {s : (KernelState prog State)} {Q : (Post prog State)} {pb : Nat}
    (h : Holds W s.mem sb c) (hc : VInv posOf c st) (hpool : c.k.pool = some (pb, 0))
    (hn : st.pool[i]? = some ⟨op, #[a]⟩) (hl : ¬ IsLeaf op) (hQ : CvQ W sb c st i Q)
    (K : ∀ (r wk er : BitVec 32) (vl : BitVec 64) (s' : (KernelState prog State)),
      Holds W s'.mem sb (c.wev wk er vl) → r ≠ 0#32 → r ≠ 4294967295#32 →
      (∃ v, memoVal st a = some v ∧ CvRep r vl v) →
      WP Vbcf.prog cvUt Q
        (cvEnv sb (BitVec.ofNat 32 (st.id i)) d hdr code nn par lo hi w r i0 vl y z m sbv acc) s') (h_lv : st.lv i := by vlv) :
    WP Vbcf.prog cvU Q
      (cvEnv sb (BitVec.ofNat 32 (st.id i)) d hdr code nn par lo hi w cw i0 x y z m sbv acc) s := by
  have hi := h_lv
  have hs := prog_ck
  have ha : st.lv a := hc.arg_lv hn a (by simp)
  have hrd := hc.rd1 hn hl
  simp only [cvU, Stmt.block]
  apply WP.cval_child (IH _ (cv_dec_lt hd)) h hc ha (by cv_simp [hrd])
  intro r1 wk1 er1 vl1 s1 h1 hv1
  cv_simp
  apply WP.cw_guard (r := r1) hQ h1 (by cv_simp)
  intro hr1 hr1'
  replace h := h1
  apply WP.assign_seq; cv_simp
  exact K r1 wk1 er1 vl1 s1 h1 hr1 hr1' (hv1 hr1 hr1')

/-! ## Words and their low `k` bits -/

theorem mW_bv {k : Nat} (hk : k ≤ 64) : mW (BitVec.ofNat 32 k) = mask64M (BitVec.ofNat 32 k) := by
  unfold mW
  rw [ite_eq_left]
  rw [show (64#32 : BitVec 32) = BitVec.ofNat 32 64 from rfl, uv_le (by omega) (by omega)]
  exact hk

theorem mW_bool : mW 100#32 = 1#64 := by decide

theorem mask64M_toNat {k : Nat} (h1 : 1 ≤ k) (h2 : k ≤ 64) :
    (mask64M (BitVec.ofNat 32 k)).toNat = 2 ^ k - 1 := by
  unfold mask64M
  have hP : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) h1
  by_cases h64 : k = 64
  · subst h64; decide
  · have hlt : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega)
    rw [ite_eq_right (by rw [show (64#32 : BitVec 32) = BitVec.ofNat 32 64 from rfl, uv_le (by omega) (by omega)]; omega)]
    rw [BitVec.toNat_sub, BitVec.toNat_shiftLeft, bv_toNat_ofNat (by omega)]
    simp only [BitVec.toNat_ofNat, Nat.one_mod, Nat.reducePow, Nat.shiftLeft_eq, Nat.one_mul]
    rw [Nat.mod_eq_of_lt hlt]
    omega

theorem mW_bv_toNat {k : Nat} (h1 : 1 ≤ k) (h2 : k ≤ 64) :
    (mW (BitVec.ofNat 32 k)).toNat = 2 ^ k - 1 := by
  rw [mW_bv h2, mask64M_toNat h1 h2]

/-- `a & m` is the low `k` bits of `a`. -/
theorem cv_and_mW {k : Nat} (h1 : 1 ≤ k) (h2 : k ≤ 64) (a : BitVec 64) :
    (a &&& mW (BitVec.ofNat 32 k)).toNat = (a.setWidth k).toNat := by
  rw [BitVec.toNat_and, mW_bv_toNat h1 h2, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_setWidth]

theorem cv_trunc_of {k : Nat} (_hk : k ≤ 64) {vl : BitVec 64} {x : BitVec k} (h : vl.toNat = x.toNat) :
    vl.setWidth k = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, h, Nat.mod_eq_of_lt x.isLt]

theorem cv_setWidth_neg {k : Nat} (hk : k ≤ 64) (a : BitVec 64) :
    (-a).setWidth k = -(a.setWidth k) := by
  rw [BitVec.neg_eq_not_add, BitVec.setWidth_add _ _ hk, BitVec.setWidth_not hk,
    BitVec.setWidth_ofNat_of_le hk, BitVec.neg_eq_not_add]

theorem cv_setWidth_sub {k : Nat} (hk : k ≤ 64) (a b : BitVec 64) :
    (a - b).setWidth k = a.setWidth k - b.setWidth k := by
  rw [BitVec.sub_eq_add_neg, BitVec.setWidth_add _ _ hk, cv_setWidth_neg hk, ← BitVec.sub_eq_add_neg]

theorem CvRep.of_bv {w : BitVec 32} {k : Nat} {x' : BitVec 64} {y : BitVec k} (hw : CvW (.bv k) w)
    (h : x'.toNat = y.toNat) : CvRep w x' (.bv k y) := by
  obtain ⟨h1, h2, rfl⟩ := hw.bv
  exact ⟨bv_toNat_ofNat (by omega), h1, h2, h⟩

theorem CvRep.of_bool {w : BitVec 32} {b : Bool} {x' : BitVec 64} (hw : CvW .bool w)
    (h : x' = if b then 1#64 else 0#64) : CvRep w x' (.bool b) :=
  ⟨hw.bool, h⟩

theorem cv_memo1 {st : St} (hok : TysOK st.pool st.tys) {i : Nat} {op : Op} {a : Nat}
    (hn : st.pool[i]? = some ⟨op, #[a]⟩) (hl : ¬ IsLeaf op) (hz : ∀ w, op ≠ .bvSize w)
    {v1 : Bcf.Val} (h1 : memoVal st a = some v1) {t : Bcf.Ty} (ht : st.tys[i]? = some t) :
    memoVal st i = some (Op.eval (fun _ => 0) op [v1]) ∧
      (Op.eval (fun _ => 0) op [v1]).ty = some t := by
  have hm := cv_memoVal_1 hok hn hl hz h1
  exact ⟨hm, by rw [cv_memoVal_ty hok hm, ht]⟩

/-! ## One-argument operators -/

theorem cv_bvUn_inv {w' : Nat} {f : BitVec w' → BitVec w'} {v1 : Bcf.Val} {t : Bcf.Ty}
    {r : BitVec 32} {vl : BitVec 64} (h1 : CvRep r vl v1) (hty : (bvUn w' f [v1]).ty = some t) :
    ∃ x : BitVec w', v1 = .bv w' x ∧ t = .bv w' ∧ bvUn w' f [v1] = .bv w' (f x) ∧
      vl.toNat = x.toNat := by
  rcases h1.cases with ⟨b, rfl⟩ | ⟨n, x, rfl⟩
  · simp [bvUn] at hty
  · by_cases hn : n = w'
    · subst hn
      by_cases h0 : n = 0
      · simp [bvUn, h0] at hty
      · simp [bvUn, h0] at hty ⊢
        exact ⟨hty.symm, h1.2.2.2⟩
    · simp [bvUn, hn] at hty

theorem cvsem_neg {ρ : Assign} {w' : Nat} {v1 : Bcf.Val} {r w : BitVec 32} {vl : BitVec 64}
    {t : Bcf.Ty} (h1 : CvRep r vl v1) (hty : (Op.eval ρ (.bvNeg w') [v1]).ty = some t)
    (hw : CvW t w) : CvRep w (-vl &&& mW w) (Op.eval ρ (.bvNeg w') [v1]) := by
  simp only [Op.eval] at hty ⊢
  obtain ⟨x, rfl, rfl, he, hx⟩ := cv_bvUn_inv h1 hty
  rw [he]
  obtain ⟨hk1, hk2, rfl⟩ := hw.bv
  apply CvRep.of_bv hw
  rw [cv_and_mW hk1 hk2, cv_setWidth_neg hk2, cv_trunc_of hk2 hx]

theorem cvsem_not {ρ : Assign} {w' : Nat} {v1 : Bcf.Val} {r w : BitVec 32} {vl : BitVec 64}
    {t : Bcf.Ty} (h1 : CvRep r vl v1) (hty : (Op.eval ρ (.bvNot w') [v1]).ty = some t)
    (hw : CvW t w) : CvRep w (~~~vl &&& mW w) (Op.eval ρ (.bvNot w') [v1]) := by
  simp only [Op.eval] at hty ⊢
  obtain ⟨x, rfl, rfl, he, hx⟩ := cv_bvUn_inv h1 hty
  rw [he]
  obtain ⟨hk1, hk2, rfl⟩ := hw.bv
  apply CvRep.of_bv hw
  rw [cv_and_mW hk1 hk2, BitVec.setWidth_not hk2, cv_trunc_of hk2 hx]

theorem cvsem_bnot {ρ : Assign} {v1 : Bcf.Val} {r w : BitVec 32} {vl : BitVec 64}
    {t : Bcf.Ty} (h1 : CvRep r vl v1) (hty : (Op.eval ρ .boolNot [v1]).ty = some t)
    (hw : CvW t w) : CvRep w (1#64 - vl) (Op.eval ρ .boolNot [v1]) := by
  rcases h1.cases with ⟨b, rfl⟩ | ⟨n, x, rfl⟩
  · simp only [Op.eval, boolNotEval] at hty ⊢
    simp at hty; subst hty
    apply CvRep.of_bool hw
    rw [h1.2]; cases b <;> decide
  · simp [Op.eval, boolNotEval] at hty

theorem cvsem_zext {ρ : Assign} {w' e : Nat} {v1 : Bcf.Val} {r w : BitVec 32} {vl : BitVec 64}
    {t : Bcf.Ty} (h1 : CvRep r vl v1) (hty : (Op.eval ρ (.bvZeroExtend w' e) [v1]).ty = some t)
    (hw : CvW t w) : CvRep w vl (Op.eval ρ (.bvZeroExtend w' e) [v1]) := by
  rcases h1.cases with ⟨b, rfl⟩ | ⟨n, x, rfl⟩
  · simp [Op.eval, bvExtEval] at hty
  · simp only [Op.eval, bvExtEval] at hty ⊢
    by_cases hg : w' ≠ 0 ∧ n + e = w'
    · rw [ite_eq_left hg] at hty ⊢
      simp at hty; subst hty
      apply CvRep.of_bv hw
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [BitVec.toNat_setWidth_of_le (by omega)]
      exact h1.2.2.2
    · simp [hg] at hty

theorem cv_extract_inv {ρ : Assign} {hi lo : Nat} {v1 : Bcf.Val} {r : BitVec 32} {vl : BitVec 64}
    {t : Bcf.Ty} (h1 : CvRep r vl v1) (hty : (Op.eval ρ (.bvExtract hi lo) [v1]).ty = some t) :
    ∃ n x, v1 = .bv n x ∧ lo ≤ hi ∧ hi < n ∧ n ≤ 64 ∧ vl.toNat = x.toNat := by
  rcases h1.cases with ⟨b, rfl⟩ | ⟨n, x, rfl⟩
  · simp [Op.eval, bvExtractEval] at hty
  · simp only [Op.eval, bvExtractEval] at hty
    by_cases hg : lo ≤ hi ∧ hi < n
    · exact ⟨n, x, rfl, hg.1, hg.2, h1.2.2.1, h1.2.2.2⟩
    · simp [hg] at hty

theorem cv_bitof_inv {ρ : Assign} {k : Nat} {v1 : Bcf.Val} {r : BitVec 32} {vl : BitVec 64}
    {t : Bcf.Ty} (h1 : CvRep r vl v1) (hty : (Op.eval ρ (.boolBitof k) [v1]).ty = some t) :
    ∃ n x, v1 = .bv n x ∧ k < n ∧ n ≤ 64 ∧ vl.toNat = x.toNat := by
  rcases h1.cases with ⟨b, rfl⟩ | ⟨n, x, rfl⟩
  · simp [Op.eval, bitofEval] at hty
  · simp only [Op.eval, bitofEval] at hty
    by_cases hg : k < n
    · exact ⟨n, x, rfl, hg, h1.2.2.1, h1.2.2.2⟩
    · simp [hg] at hty

theorem cvsem_extract {ρ : Assign} {hi lo n : Nat} {x : BitVec n} {w : BitVec 32} {vl : BitVec 64}
    {t : Bcf.Ty} (hx : vl.toNat = x.toNat)
    (hty : (Op.eval ρ (.bvExtract hi lo) [.bv n x]).ty = some t) (hw : CvW t w) :
    CvRep w (vl >>> lo &&& mW w) (Op.eval ρ (.bvExtract hi lo) [.bv n x]) := by
  simp only [Op.eval, bvExtractEval] at hty ⊢
  by_cases hg : lo ≤ hi ∧ hi < n
  · rw [ite_eq_left hg] at hty ⊢
    simp at hty; subst hty
    obtain ⟨hk1, hk2, rfl⟩ := hw.bv
    apply CvRep.of_bv hw
    rw [cv_and_mW hk1 hk2, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, hx,
      BitVec.extractLsb_toNat]
  · simp [hg] at hty

theorem cvsem_bitof {ρ : Assign} {k n : Nat} {x : BitVec n} {w : BitVec 32} {vl : BitVec 64}
    {t : Bcf.Ty} (hx : vl.toNat = x.toNat)
    (hty : (Op.eval ρ (.boolBitof k) [.bv n x]).ty = some t) (hw : CvW t w) :
    CvRep w (vl >>> k &&& 1#64) (Op.eval ρ (.boolBitof k) [.bv n x]) := by
  simp only [Op.eval, bitofEval] at hty ⊢
  by_cases hg : k < n
  · rw [ite_eq_left hg] at hty ⊢
    simp at hty; subst hty
    apply CvRep.of_bool hw
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, hx]
    have e1 : (1#64).toNat = 1 := rfl
    rw [e1, Nat.and_one_is_mod]
    have e2 : x.getLsbD k = (x.toNat >>> k % 2 == 1) := by
      rw [BitVec.getLsbD, Nat.testBit, Nat.and_comm, Nat.and_one_is_mod]
      cases Nat.mod_two_eq_zero_or_one (x.toNat >>> k) with
      | inl h0 => simp [h0]
      | inr h1 => simp [h1]
    rw [e2]
    cases Nat.mod_two_eq_zero_or_one (x.toNat >>> k) with
    | inl h0 => simp [h0]
    | inr h1 => simp [h1]
  · simp [hg] at hty

theorem cv_two_pow_mul_sub {A B C : Nat} (hB : 1 ≤ B) (hC : C ≤ A) (hC1 : 1 ≤ C) :
    (A * B - C) % A = A - C := by
  have e : A * B - C = A * (B - 1) + (A - C) := by
    have : A * B = A * (B - 1) + A := by
      rw [← Nat.mul_add_one, Nat.sub_add_cancel hB]
    omega
  rw [e, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

/-- The sign-extension bits `m & ~mask(n)` are `2^w - 2^n`, and or-ing them is adding. -/
theorem cv_nat_sext {n w a : Nat} (_h1 : 1 ≤ n) (hnw : n ≤ w) (hw : w ≤ 64) (ha : a < 2 ^ n) :
    a ||| ((2 ^ w - 1) &&& (2 ^ 64 - 1 - (2 ^ n - 1))) = a + (2 ^ w - 2 ^ n) := by
  have hC : 2 ^ n ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hnw
  have hC1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hB : 1 ≤ 2 ^ (64 - w) := Nat.one_le_two_pow
  have h64 : (2 : Nat) ^ 64 = 2 ^ w * 2 ^ (64 - w) := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' hw]
  rw [Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod,
    show 2 ^ 64 - 1 - (2 ^ n - 1) = 2 ^ 64 - 2 ^ n by omega, h64, cv_two_pow_mul_sub hB hC hC1]
  have hD : 2 ^ w - 2 ^ n = (2 ^ (w - n) - 1) <<< n := by
    rw [Nat.shiftLeft_eq, Nat.sub_mul, Nat.one_mul, ← Nat.pow_add, Nat.sub_add_cancel hnw]
  rw [hD, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt ha]
  omega

theorem cv_msb_iff_bit {n : Nat} (h1 : 1 ≤ n) (h64 : n ≤ 64) {x : BitVec n} {vl : BitVec 64}
    (hx : vl.toNat = x.toNat) : (vl >>> (n - 1) &&& 1#64 = 0#64) ↔ x.msb = false := by
  rw [BitVec.msb_eq_decide, ← BitVec.toNat_inj, BitVec.toNat_and, BitVec.toNat_ushiftRight, hx]
  have e1 : (1#64).toNat = 1 := rfl
  have e0 : (0#64).toNat = 0 := rfl
  rw [e1, e0, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  have hlt := x.isLt
  have hP : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← Nat.pow_one 2, ← Nat.pow_add] ; congr 1; omega
  have hpos : 0 < 2 ^ (n - 1) := Nat.two_pow_pos _
  simp only [decide_eq_false_iff_not, Nat.not_le]
  constructor
  · intro h
    have : x.toNat / 2 ^ (n - 1) < 2 := by
      rw [Nat.div_lt_iff_lt_mul hpos]; omega
    have h0 : x.toNat / 2 ^ (n - 1) = 0 := by
      rcases Nat.lt_or_ge (x.toNat / 2 ^ (n - 1)) 1 with h' | h'
      · exact Nat.lt_one_iff.mp h'
      · exfalso
        generalize x.toNat / 2 ^ (n - 1) = q at h this h'
        have h1 : q = 1 := by omega
        rw [h1] at h; simp at h
    rwa [Nat.div_eq_zero_iff_lt hpos] at h0
  · intro h
    rw [Nat.div_eq_of_lt h]

theorem cvsem_sext {ρ : Assign} {w' e n : Nat} {x : BitVec n} {w : BitVec 32} {vl : BitVec 64}
    {t : Bcf.Ty} (hn1 : 1 ≤ n) (hn64 : n ≤ 64) (hx : vl.toNat = x.toNat)
    (hty : (Op.eval ρ (.bvSignExtend w' e) [.bv n x]).ty = some t) (hw : CvW t w) :
    CvRep w (if vl >>> (n - 1) &&& 1#64 = 0#64 then vl
      else vl ||| mW w &&& ~~~mask64M (BitVec.ofNat 32 n)) (Op.eval ρ (.bvSignExtend w' e) [.bv n x]) := by
  simp only [Op.eval, bvExtEval] at hty ⊢
  by_cases hg : w' ≠ 0 ∧ n + e = w'
  · rw [ite_eq_left hg] at hty ⊢
    simp at hty; subst hty
    obtain ⟨hk1, hk2, rfl⟩ := hw.bv
    apply CvRep.of_bv hw
    simp only [↓reduceIte, BitVec.toNat_signExtend, BitVec.toNat_setWidth_of_le (by omega : n ≤ w')]
    by_cases hb : vl >>> (n - 1) &&& 1#64 = 0#64
    · rw [ite_eq_left hb, (cv_msb_iff_bit hn1 hn64 hx).mp hb, hx]; simp
    · have hm : x.msb = true := by
        have := (not_congr (cv_msb_iff_bit hn1 hn64 hx)).mp hb; simpa using this
      rw [ite_eq_right hb, hm, BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_not, mW_bv_toNat hk1 hk2,
        mask64M_toNat hn1 hn64, hx]
      simp only [↓reduceIte]
      exact cv_nat_sext hn1 (by omega) hk2 x.isLt
  · simp [hg] at hty

/-- `j` copies of the `n`-bit number `xv`, as the C loop builds them. -/
def cvRepN (n xv : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => cvRepN n xv j * 2 ^ n + xv

theorem cvRepN_succ (n xv : Nat) : ∀ j, cvRepN n xv (j + 1) = xv * 2 ^ (n * j) + cvRepN n xv j
  | 0 => by simp [cvRepN]
  | j + 1 => by
    have e1 : cvRepN n xv (j + 1 + 1) = cvRepN n xv (j + 1) * 2 ^ n + xv := rfl
    have e2 : cvRepN n xv (j + 1) = cvRepN n xv j * 2 ^ n + xv := rfl
    have ih : cvRepN n xv j * 2 ^ n + xv = xv * 2 ^ (n * j) + cvRepN n xv j := by
      rw [← e2]; exact cvRepN_succ n xv j
    have h3 : (cvRepN n xv j * 2 ^ n + xv) * 2 ^ n = xv * 2 ^ (n * (j + 1)) + cvRepN n xv j * 2 ^ n := by
      rw [ih, Nat.add_mul, Nat.mul_assoc, ← Nat.pow_add, ← Nat.mul_succ]
    rw [e1, e2]
    omega

theorem cvRepN_lt {n xv : Nat} (hx : xv < 2 ^ n) : ∀ j, cvRepN n xv j < 2 ^ (n * j)
  | 0 => by simp [cvRepN]
  | j + 1 => by
    have ih := cvRepN_lt hx j
    rw [cvRepN, Nat.mul_succ, Nat.pow_add]
    have : cvRepN n xv j * 2 ^ n + xv < (cvRepN n xv j + 1) * 2 ^ n := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    calc cvRepN n xv j * 2 ^ n + xv < (cvRepN n xv j + 1) * 2 ^ n := this
      _ ≤ 2 ^ (n * j) * 2 ^ n := Nat.mul_le_mul_right _ ih

theorem cv_replicate_toNat {n : Nat} (x : BitVec n) : ∀ k, (x.replicate k).toNat = cvRepN n x.toNat k
  | 0 => by simp [BitVec.replicate_zero, cvRepN]
  | k + 1 => by
    rw [BitVec.replicate_succ, BitVec.toNat_cast, BitVec.toNat_append, cv_replicate_toNat x k,
      cvRepN_succ, ← Nat.shiftLeft_add_eq_or_of_lt (cvRepN_lt x.isLt k), Nat.shiftLeft_eq]

/-- One turn of the C loop: `y = (y << n) | x`. -/
theorem cvrep_step {n j k : Nat} (_hn : n < 64) (hjk : j < k) (hnk : n * k ≤ 64) {x : BitVec 64}
    {xv : Nat} (hx : x.toNat = xv) (hxv : xv < 2 ^ n) {yv : BitVec 64} (hy : yv.toNat = cvRepN n xv j) :
    (yv <<< n ||| x).toNat = cvRepN n xv (j + 1) := by
  have hl := cvRepN_lt hxv j
  have hle : n * (j + 1) ≤ 64 := Nat.le_trans (Nat.mul_le_mul_left _ hjk) hnk
  have h1 : cvRepN n xv j * 2 ^ n < 2 ^ 64 := by
    calc cvRepN n xv j * 2 ^ n < 2 ^ (n * j) * 2 ^ n := Nat.mul_lt_mul_of_pos_right hl (Nat.two_pow_pos _)
      _ = 2 ^ (n * (j + 1)) := by rw [← Nat.pow_add, Nat.mul_succ]
      _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hle
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, hy, hx, Nat.shiftLeft_eq, Nat.mod_eq_of_lt h1, cvRepN,
    ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt hxv, Nat.shiftLeft_eq]

theorem cv_repeat_inv {ρ : Assign} {w' k : Nat} {v1 : Bcf.Val} {r : BitVec 32} {vl : BitVec 64}
    {t : Bcf.Ty} (h1 : CvRep r vl v1) (hty : (Op.eval ρ (.bvRepeat w' k) [v1]).ty = some t) :
    ∃ n x, v1 = .bv n x ∧ 1 ≤ n ∧ n ≤ 64 ∧ r = BitVec.ofNat 32 n ∧ vl.toNat = x.toNat ∧
      w' ≠ 0 ∧ n * k = w' := by
  rcases h1.cases with ⟨b, rfl⟩ | ⟨n, x, rfl⟩
  · simp [Op.eval, bvRepeatEval] at hty
  · simp only [Op.eval, bvRepeatEval] at hty
    by_cases hg : w' ≠ 0 ∧ n * k = w'
    · exact ⟨n, x, rfl, h1.2.1, h1.2.2.1, by rw [← h1.1, bv_ofNat_toNat], h1.2.2.2, hg.1, hg.2⟩
    · simp [hg] at hty

theorem cvsem_repeat {ρ : Assign} {w' k n : Nat} {x : BitVec n} {w : BitVec 32} {yv : BitVec 64}
    {t : Bcf.Ty} (hy : yv.toNat = cvRepN n x.toNat k)
    (hty : (Op.eval ρ (.bvRepeat w' k) [.bv n x]).ty = some t) (hw : CvW t w) :
    CvRep w yv (Op.eval ρ (.bvRepeat w' k) [.bv n x]) := by
  simp only [Op.eval, bvRepeatEval] at hty ⊢
  by_cases hg : w' ≠ 0 ∧ n * k = w'
  · rw [dite_eq_left hg] at hty ⊢
    simp at hty; subst hty
    apply CvRep.of_bv hw
    rw [BitVec.toNat_cast, cv_replicate_toNat, hy]
  · simp [hg] at hty

section chains
variable {W : World} {sb : Nat} {c : CMem} {st : VSt} {i : Nat} {Q : (Post prog State)}
  {id d hdr nn par w : BitVec 32} {y z sbv acc : BitVec 64}

theorem chainU_neg (hQ : CvQ W sb c st i Q) {a : Nat} {t : Bcf.Ty} {op : Op} {w' : Nat}
    (hop : op = .bvNeg w') (hn : st.pool[i]? = some ⟨op, #[a]⟩) (hok : TysOK st.pool st.tys)
    (ht : st.tys[i]? = some t) (hw : CvW t w) :
    ∀ (r wk er : BitVec 32) (vl : BitVec 64) (s' : (KernelState prog State)),
      Holds W s'.mem sb (c.wev wk er vl) → r ≠ 0#32 → r ≠ 4294967295#32 →
      (∃ v, memoVal st a = some v ∧ CvRep r vl v) →
      WP Vbcf.prog cvUt Q
        (cvEnv sb id d hdr (BitVec.ofNat 32 (opC op)) nn par (BitVec.ofNat 32 (opLo op))
          (BitVec.ofNat 32 (opHi op)) w r 0#32 vl y z (mW w) sbv acc) s' := by
  intro r wk er vl s' h hr hr' ⟨v1, hm1, hv1⟩
  subst hop
  have hs := prog_ck
  simp only [cvUt, Stmt.block]
  apply WP.seq; apply WP.ite; cv_simp0 [opC]
  apply WP.assign; cv_simp0
  apply WP.cv_finish (w := w) (x' := -vl &&& mW w) hQ h (by simp [Env.get]) (by simp [Env.get])
    (by cv_simp0)
  intro _ _
  obtain ⟨hm, hty⟩ := cv_memo1 hok hn (by simp [IsLeaf, isLeaf]) (by simp) hm1 ht
  exact ⟨_, hm, cvsem_neg hv1 hty hw⟩

theorem chainU_not (hQ : CvQ W sb c st i Q) {a : Nat} {t : Bcf.Ty} {w' : Nat} {op : Op}
    (hop : op = (.bvNot w')) (hn : st.pool[i]? = some ⟨op, #[a]⟩) (hok : TysOK st.pool st.tys)
    (ht : st.tys[i]? = some t) (hw : CvW t w) :
    ∀ (r wk er : BitVec 32) (vl : BitVec 64) (s' : (KernelState prog State)),
      Holds W s'.mem sb (c.wev wk er vl) → r ≠ 0#32 → r ≠ 4294967295#32 →
      (∃ v, memoVal st a = some v ∧ CvRep r vl v) →
      WP Vbcf.prog cvUt Q
        (cvEnv sb id d hdr (BitVec.ofNat 32 (opC op)) nn par (BitVec.ofNat 32 (opLo op))
          (BitVec.ofNat 32 (opHi op)) w r 0#32 vl y z (mW w) sbv acc) s' := by
  intro r wk er vl s' h hr hr' ⟨v1, hm1, hv1⟩
  subst hop
  have hs := prog_ck
  obtain ⟨hm, hty⟩ := cv_memo1 hok hn (by simp [IsLeaf, isLeaf]) (by simp) hm1 ht
  simp only [cvUt, Stmt.block]
  apply WP.seq
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.assign; cv_simp0
  apply WP.cv_finish (w := w) (x' := ~~~vl &&& mW w) hQ h (by simp [Env.get]) (by simp [Env.get])
    (by cv_simp0)
  intro _ _
  exact ⟨_, hm, cvsem_not hv1 hty hw⟩

theorem chainU_bnot (hQ : CvQ W sb c st i Q) {a : Nat} {t : Bcf.Ty} {op : Op}
    (hop : op = .boolNot) (hn : st.pool[i]? = some ⟨op, #[a]⟩) (hok : TysOK st.pool st.tys)
    (ht : st.tys[i]? = some t) (hw : CvW t w) :
    ∀ (r wk er : BitVec 32) (vl : BitVec 64) (s' : (KernelState prog State)),
      Holds W s'.mem sb (c.wev wk er vl) → r ≠ 0#32 → r ≠ 4294967295#32 →
      (∃ v, memoVal st a = some v ∧ CvRep r vl v) →
      WP Vbcf.prog cvUt Q
        (cvEnv sb id d hdr (BitVec.ofNat 32 (opC op)) nn par (BitVec.ofNat 32 (opLo op))
          (BitVec.ofNat 32 (opHi op)) w r 0#32 vl y z (mW w) sbv acc) s' := by
  intro r wk er vl s' h hr hr' ⟨v1, hm1, hv1⟩
  subst hop
  have hs := prog_ck
  obtain ⟨hm, hty⟩ := cv_memo1 hok hn (by simp [IsLeaf, isLeaf]) (by simp) hm1 ht
  simp only [cvUt, Stmt.block]
  apply WP.seq
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.assign; cv_simp0
  apply WP.cv_finish (w := w) (x' := 1#64 - vl) hQ h (by simp [Env.get]) (by simp [Env.get])
    (by cv_simp0)
  intro _ _
  exact ⟨_, hm, cvsem_bnot hv1 hty hw⟩

theorem chainU_zext (hQ : CvQ W sb c st i Q) {a : Nat} {t : Bcf.Ty} {w' e : Nat} {op : Op}
    (hop : op = (.bvZeroExtend w' e)) (hn : st.pool[i]? = some ⟨op, #[a]⟩) (hok : TysOK st.pool st.tys)
    (ht : st.tys[i]? = some t) (hw : CvW t w) :
    ∀ (r wk er : BitVec 32) (vl : BitVec 64) (s' : (KernelState prog State)),
      Holds W s'.mem sb (c.wev wk er vl) → r ≠ 0#32 → r ≠ 4294967295#32 →
      (∃ v, memoVal st a = some v ∧ CvRep r vl v) →
      WP Vbcf.prog cvUt Q
        (cvEnv sb id d hdr (BitVec.ofNat 32 (opC op)) nn par (BitVec.ofNat 32 (opLo op))
          (BitVec.ofNat 32 (opHi op)) w r 0#32 vl y z (mW w) sbv acc) s' := by
  intro r wk er vl s' h hr hr' ⟨v1, hm1, hv1⟩
  subst hop
  have hs := prog_ck
  obtain ⟨hm, hty⟩ := cv_memo1 hok hn (by simp [IsLeaf, isLeaf]) (by simp) hm1 ht
  simp only [cvUt, Stmt.block]
  apply WP.seq
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.skip
  apply WP.cv_finish (w := w) (x' := vl) hQ h (by simp [Env.get]) (by simp [Env.get])
    (by cv_simp0)
  intro _ _
  exact ⟨_, hm, cvsem_zext hv1 hty hw⟩

theorem chainU_extract (hQ : CvQ W sb c st i Q) {a : Nat} {t : Bcf.Ty} {op : Op} {hi lo : Nat}
    (hop : op = (.bvExtract hi lo)) (hn : st.pool[i]? = some ⟨op, #[a]⟩) (hok : TysOK st.pool st.tys)
    (ht : st.tys[i]? = some t) (hw : CvW t w) :
    ∀ (r wk er : BitVec 32) (vl : BitVec 64) (s' : (KernelState prog State)),
      Holds W s'.mem sb (c.wev wk er vl) → r ≠ 0#32 → r ≠ 4294967295#32 →
      (∃ v, memoVal st a = some v ∧ CvRep r vl v) →
      WP Vbcf.prog cvUt Q
        (cvEnv sb id d hdr (BitVec.ofNat 32 (opC op)) nn par (BitVec.ofNat 32 (opLo op))
          (BitVec.ofNat 32 (opHi op)) w r 0#32 vl y z (mW w) sbv acc) s' := by
  intro r wk er vl s' h hr hr' ⟨v1, hm1, hv1⟩
  subst hop
  have hs := prog_ck
  obtain ⟨hm, hty⟩ := cv_memo1 hok hn (by simp [IsLeaf, isLeaf]) (by simp) hm1 ht
  obtain ⟨n, x, rfl, hlh, hhn, hn64, hx⟩ := cv_extract_inv hv1 hty
  have hlo : lo < 64 := by omega
  have hlo' : lo % 18446744073709551616 = lo := Nat.mod_eq_of_lt (by omega)
  simp only [cvUt, Stmt.block]
  apply WP.seq
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.assign; cv_simp0 [opLo, hlo, hlo']
  apply WP.cv_finish (w := w) (x' := vl >>> lo &&& mW w) hQ h (by simp [Env.get]) (by simp [Env.get])
    (by cv_simp0 [opLo, hlo, hlo'])
  intro _ _
  exact ⟨_, hm, cvsem_extract hx hty hw⟩

theorem chainU_bitof (hQ : CvQ W sb c st i Q) {a : Nat} {t : Bcf.Ty} {op : Op} {k : Nat}
    (hop : op = (.boolBitof k)) (hn : st.pool[i]? = some ⟨op, #[a]⟩) (hok : TysOK st.pool st.tys)
    (ht : st.tys[i]? = some t) (hw : CvW t w) :
    ∀ (r wk er : BitVec 32) (vl : BitVec 64) (s' : (KernelState prog State)),
      Holds W s'.mem sb (c.wev wk er vl) → r ≠ 0#32 → r ≠ 4294967295#32 →
      (∃ v, memoVal st a = some v ∧ CvRep r vl v) →
      WP Vbcf.prog cvUt Q
        (cvEnv sb id d hdr (BitVec.ofNat 32 (opC op)) nn par (BitVec.ofNat 32 (opLo op))
          (BitVec.ofNat 32 (opHi op)) w r 0#32 vl y z (mW w) sbv acc) s' := by
  intro r wk er vl s' h hr hr' ⟨v1, hm1, hv1⟩
  subst hop
  have hs := prog_ck
  obtain ⟨hm, hty⟩ := cv_memo1 hok hn (by simp [IsLeaf, isLeaf]) (by simp) hm1 ht
  obtain ⟨n, x, rfl, hkn, hn64, hx⟩ := cv_bitof_inv hv1 hty
  have hlo : k < 64 := by omega
  have hlo' : k % 18446744073709551616 = k := Nat.mod_eq_of_lt (by omega)
  simp only [cvUt, Stmt.block]
  apply WP.seq
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.assign; cv_simp0 [opLo, hlo, hlo']
  apply WP.cv_finish (w := w) (x' := vl >>> k &&& 1#64) hQ h (by simp [Env.get]) (by simp [Env.get])
    (by cv_simp0 [opLo, hlo, hlo'])
  intro _ _
  exact ⟨_, hm, cvsem_bitof hx hty hw⟩

theorem chainU_sext (hQ : CvQ W sb c st i Q) {a : Nat} {t : Bcf.Ty} {op : Op} {w' e : Nat}
    (hop : op = .bvSignExtend w' e) (hn : st.pool[i]? = some ⟨op, #[a]⟩) (hok : TysOK st.pool st.tys)
    (ht : st.tys[i]? = some t) (hw : CvW t w) :
    ∀ (r wk er : BitVec 32) (vl : BitVec 64) (s' : (KernelState prog State)),
      Holds W s'.mem sb (c.wev wk er vl) → r ≠ 0#32 → r ≠ 4294967295#32 →
      (∃ v, memoVal st a = some v ∧ CvRep r vl v) →
      WP Vbcf.prog cvUt Q
        (cvEnv sb id d hdr (BitVec.ofNat 32 (opC op)) nn par (BitVec.ofNat 32 (opLo op))
          (BitVec.ofNat 32 (opHi op)) w r 0#32 vl y z (mW w) sbv acc) s' := by
  intro r wk er vl s' h hr hr' ⟨v1, hm1, hv1⟩
  subst hop
  have hs := prog_ck
  obtain ⟨hm, hty⟩ := cv_memo1 hok hn (by simp [IsLeaf, isLeaf]) (by simp) hm1 ht
  obtain ⟨n, x, rfl, hn1, hn64, hr, hx⟩ : ∃ n x, v1 = .bv n x ∧ 1 ≤ n ∧ n ≤ 64 ∧ r = BitVec.ofNat 32 n ∧
      vl.toNat = x.toNat := by
    rcases hv1.cases with ⟨b, rfl⟩ | ⟨n, x, rfl⟩
    · simp [Op.eval, bvExtEval] at hty
    · exact ⟨n, x, rfl, hv1.2.1, hv1.2.2.1, by rw [← hv1.1, bv_ofNat_toNat], hv1.2.2.2⟩
  subst hr
  have hk : (4294967295 + n) % 4294967296 % 18446744073709551616 = n - 1 := by omega
  have hk' : (4294967295 + n) % 4294967296 = n - 1 := by omega
  have hk2 : (n - 1) % 18446744073709551616 = n - 1 := by omega
  have hlo : n - 1 < 64 := by omega
  have hlo' := hk2
  simp only [cvUt, Stmt.block]
  apply WP.seq
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [hk, hk', hk2, hlo]
  by_cases hb : vl >>> (n - 1) &&& 1#64 = 0#64
  · refine ⟨fun h0 => absurd hb h0, fun _ => ?_⟩
    apply WP.skip
    apply WP.cv_finish (w := w) (x' := vl) hQ h (by simp [Env.get]) (by simp [Env.get]) (by cv_simp0)
    intro _ _
    have := cvsem_sext hn1 hn64 hx hty hw
    rw [ite_eq_left hb] at this
    exact ⟨_, hm, this⟩
  · refine ⟨fun _ => ?_, fun h0 => absurd h0 hb⟩
    apply WP.seq
    apply WP.call (mask64_spec (BitVec.ofNat 32 n)); cv_simp0
    apply WP.assign; cv_simp0
    apply WP.cv_finish (w := w) (x' := vl ||| mW w &&& ~~~mask64M (BitVec.ofNat 32 n)) hQ h
      (by simp [Env.get]) (by simp [Env.get]) (by cv_simp0)
    intro _ _
    have := cvsem_sext hn1 hn64 hx hty hw
    rw [ite_eq_right hb] at this
    exact ⟨_, hm, this⟩

theorem chainU_repeat (hQ : CvQ W sb c st i Q) {a : Nat} {t : Bcf.Ty} {op : Op} {w' k : Nat}
    (hop : op = .bvRepeat w' k) (hn : st.pool[i]? = some ⟨op, #[a]⟩) (hok : TysOK st.pool st.tys)
    (ht : st.tys[i]? = some t) (hw : CvW t w) :
    ∀ (r wk er : BitVec 32) (vl : BitVec 64) (s' : (KernelState prog State)),
      Holds W s'.mem sb (c.wev wk er vl) → r ≠ 0#32 → r ≠ 4294967295#32 →
      (∃ v, memoVal st a = some v ∧ CvRep r vl v) →
      WP Vbcf.prog cvUt Q
        (cvEnv sb id d hdr (BitVec.ofNat 32 (opC op)) nn par (BitVec.ofNat 32 (opLo op))
          (BitVec.ofNat 32 (opHi op)) w r 0#32 vl y z (mW w) sbv acc) s' := by
  intro r wk er vl s' h hr hr' ⟨v1, hm1, hv1⟩
  subst hop
  have hs := prog_ck
  obtain ⟨hm, hty⟩ := cv_memo1 hok hn (by simp [IsLeaf, isLeaf]) (by simp) hm1 ht
  obtain ⟨n, x, rfl, hn1, hn64, rfl, hx, hw0, hnk⟩ := cv_repeat_inv hv1 hty
  have hw64 : w' ≤ 64 := by
    have hty' := hty
    simp [Op.eval, bvRepeatEval, hw0, hnk] at hty'
    subst hty'
    exact hw.bv.2.1
  have hk64 : k ≤ 64 := by
    have : 1 * k ≤ n * k := Nat.mul_le_mul_right _ hn1
    omega
  simp only [cvUt, Stmt.block]
  apply WP.seq
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0
  by_cases hn : n < 64
  · refine ⟨fun _ => ?_, fun h0 => absurd h0 (by omega)⟩
    have hnm : n % 18446744073709551616 = n := Nat.mod_eq_of_lt (by omega)
    apply WP.seq; apply WP.assign; cv_simp0
    apply WP.loop_seq (fun env s => ∃ j yv, j ≤ k ∧ yv.toNat = cvRepN n x.toNat j ∧
      env = cvEnv sb id d hdr (BitVec.ofNat 32 (opC (.bvRepeat w' k))) nn par
        (BitVec.ofNat 32 (opLo (.bvRepeat w' k))) (BitVec.ofNat 32 (opHi (.bvRepeat w' k))) w
        (BitVec.ofNat 32 n) (BitVec.ofNat 32 j) vl yv z (mW w) sbv acc ∧ s = s')
    · exact ⟨0, 0#64, Nat.zero_le _, rfl, rfl, rfl⟩
    · rintro env s ⟨j, yv, hj, hy, rfl, rfl⟩
      cv_simp0 [opHi]
      refine ⟨fun hjk => ?_, fun hjk => ?_⟩
      · have hjk' : j = k := by omega
        subst hjk'
        apply WP.assign; cv_simp0
        apply WP.cv_finish (w := w) (x' := yv) hQ h (by simp [Env.get]) (by simp [Env.get])
          (by cv_simp0)
        intro _ _
        exact ⟨_, hm, cvsem_repeat hy hty hw⟩
      · apply WP.assign_seq; cv_simp0 [hnm, hn]
        apply WP.assign_loop; cv_simp0
        have hjk2 : j < k := by omega
        refine ⟨j + 1, hjk2, ?_, rfl⟩
        have := cvrep_step hn hjk2 (by rw [hnk]; exact hw64) hx x.isLt hy
        rw [BitVec.toNat_or, BitVec.toNat_shiftLeft] at this
        exact this
  · refine ⟨fun h0 => absurd h0 (by omega), fun _ => ?_⟩
    apply WP.skip
    apply WP.cv_finish (w := w) (x' := vl) hQ h (by simp [Env.get]) (by simp [Env.get]) (by cv_simp0)
    intro _ _
    have hn' : n = 64 := by omega
    subst hn'
    have hk1 : k = 1 := by
      rcases Nat.lt_or_ge k 2 with h2 | h2
      · rcases Nat.lt_or_ge k 1 with h3 | h3
        · have : k = 0 := by omega
          subst this; simp at hnk; exact absurd hnk.symm hw0
        · omega
      · have : 64 * 2 ≤ 64 * k := Nat.mul_le_mul_left _ h2
        omega
    subst hk1
    exact ⟨_, hm, cvsem_repeat (by rw [hx]; simp [cvRepN]) hty hw⟩

end chains

/-- The codes of the one-argument group, as the dispatch test leaves them. -/
def CvUnC (k : Nat) : Prop :=
  ¬k = 128 → ¬k = 120 → ¬k = 56 → ¬k = 72 → ¬k = 88 → ¬k = 168 → ¬k = 129 → k = 73

theorem grpU_spec {d : BitVec 32} (IH : ∀ d' : BitVec 32, d'.toNat < d.toNat → CvalSpecD (State := State) d')
    (hd : d ≠ 0#32) {W : World} {sb : Nat} {c : CMem} {posOf : Nat → Nat} {st : VSt} {i : Nat}
    {n : Node} {t : Bcf.Ty} {hdr nn par w cw : BitVec 32}
    {x y z sbv acc : BitVec 64} {s : (KernelState prog State)} {Q : (Post prog State)} {pb : Nat}
    (h : Holds W s.mem sb c) (hc : VInv posOf c st) (hpool : c.k.pool = some (pb, 0))
    (hn : st.pool[i]? = some n) (hop : CvUnC (opC n.op))
    (ht : st.tys[i]? = some t) (hw : CvW t w) (hQ : CvQ W sb c st i Q) (h_lv : st.lv i := by vlv) :
    WP Vbcf.prog cvU Q
      (cvEnv sb (BitVec.ofNat 32 (st.id i)) d hdr (BitVec.ofNat 32 (opC n.op)) nn par
        (BitVec.ofNat 32 (opLo n.op)) (BitVec.ofNat 32 (opHi n.op)) w cw 0#32 x y z (mW w) sbv acc) s := by
  have hi := h_lv
  obtain ⟨op, args⟩ := n
  have hok := hc.ok.tys
  cases op <;> simp only [CvUnC, opC] at hop <;> (try (exfalso; omega))
  all_goals
    obtain ⟨a, he, ha⟩ := hc.args1 hn rfl
    injection he with _ he2
    subst he2
    apply grpU_core IH hd h hc hpool hn (by simp [IsLeaf, isLeaf]) hQ
  · exact chainU_neg hQ rfl hn hok ht hw
  · exact chainU_not hQ rfl hn hok ht hw
  · exact chainU_extract hQ rfl hn hok ht hw
  · exact chainU_sext hQ rfl hn hok ht hw
  · exact chainU_zext hQ rfl hn hok ht hw
  · exact chainU_repeat hQ rfl hn hok ht hw
  · exact chainU_bnot hQ rfl hn hok ht hw
  · exact chainU_bitof hQ rfl hn hok ht hw

end Vbcf.Proof
