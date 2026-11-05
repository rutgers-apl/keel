import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Bitblast2

/-!
# Vbcf proofs: the Bitblast family, part 3 — `bb_neg`, `bb_sub`
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf


/-- What a checking helper that uses the scratch stack guarantees when it returns `r`: the
rule context holds, the stack below the old `sp` is unchanged, `sp` has not gone down, and a
non-zero answer means `P`. -/
def BbChk (W : World) (sb : Nat) (X : Ctx) (c0 : CMem) (prems params : List Nat) (st : VSt)
    (c : CMem) (P : Prop) (r : BitVec 32) (s' : (KernelState prog State)) : Prop :=
  ∃ c', Holds W s'.mem sb c' ∧ RCtx W X c0 prems params c' st ∧
    (r ≠ 0#32 → (∀ j, j < c.k.sp.toNat → c'.stk[j]? = c.stk[j]?) ∧ c.k.sp.toNat ≤ c'.k.sp.toNat ∧ P)

section chk
variable {W : World} {sb : Nat} {X : Ctx} {c0 c c1 c2 : CMem} {prems params : List Nat} {st : VSt}

theorem BbChk.zero {P : Prop} {s' : (KernelState prog State)} (h : Holds W s'.mem sb c1)
    (hR : RCtx W X c0 prems params c1 st) : BbChk W sb X c0 prems params st c P 0#32 s' :=
  ⟨c1, h, hR, fun h0 => absurd rfl h0⟩

theorem bb_pre_trans (hpre1 : ∀ j, j < c.k.sp.toNat → c1.stk[j]? = c.stk[j]?)
    (hsp1 : c.k.sp.toNat ≤ c1.k.sp.toNat)
    (hpre2 : ∀ j, j < c1.k.sp.toNat → c2.stk[j]? = c1.stk[j]?) :
    ∀ j, j < c.k.sp.toNat → c2.stk[j]? = c.stk[j]? := fun j hj => by
  rw [hpre2 j (by omega), hpre1 j hj]

theorem RCtx.bb_sp_ne (hR : RCtx W X c0 prems params c st) :
    (BitVec.ofNat 32 c.k.sp.toNat = 4294967295#32) ↔ False := by
  have := hR.sp_lt; simp only [maxPool] at this
  rw [show (4294967295#32 : BitVec 32) = BitVec.ofNat 32 4294967295 from rfl,
    bv_ofNat_inj (by omega) (by omega)]
  exact ⟨fun e => by omega, False.elim⟩

theorem RCtx.bb_ne_noid (hR : RCtx W X c0 prems params c1 st) {x : BitVec 32}
    (hx : x.toNat ≤ c1.k.sp.toNat) : (x = 4294967295#32) ↔ False := by
  have := hR.sp_lt; simp only [maxPool] at this
  refine ⟨fun e => ?_, False.elim⟩
  subst e; simp at hx; omega

theorem bb_add_toNat' {x : BitVec 32} {k : Nat} (h : x.toNat + k < 4294967296) :
    (x + BitVec.ofNat 32 k).toNat = x.toNat + k := by
  rw [BitVec.toNat_add, bv_toNat_ofNat (by omega)]; omega

theorem RCtx.bb_sp_le (hR : RCtx W X c0 prems params c st) : c.k.sp.toNat ≤ 2147483648 := by
  have := hR.sp_lt; simp only [maxPool] at this; omega

end chk

/-- `l.all (· == x)`, as a name `simp` leaves alone. -/
def bbAllEq (l : List Nat) (x : Nat) : Bool := l.all (· == x)

theorem bb_all_step {l : List Nat} {x k : Nat} {P : Prop} (hk : k < l.length)
    (H : bbAllEq (l.drop k) x = true → P) (he : l[k] = x) :
    bbAllEq (l.drop (k + 1)) x = true → P := fun h' =>
  H (by unfold bbAllEq at h' ⊢; rw [List.drop_eq_getElem_cons hk, List.all_cons, he, h']; simp)

theorem bb_all_end {l : List Nat} {x k : Nat} {P : Prop} (hk : l.length ≤ k)
    (H : bbAllEq (l.drop k) x = true → P) : P :=
  H (by rw [List.drop_of_length_le hk]; rfl)

open Lean in
/-- `bb_swap h1 hR1`: make `h1`, `hR1` the current `h`, `hR`. -/
macro "bb_swap" h1:ident hR1:ident : tactic =>
  `(tactic| (have $(mkIdent `h) := $h1; have $(mkIdent `hR) := $hR1))

/-! ## `bb_neg` -/

def BbNegSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (xb bsb : Nat) (xs bs : List Nat),
    FnSpec (State := State) Vbcf.prog "bb_neg"
      (fun vs s => vs = [.ptr sb 0, uv xb, uv xs.length, uv bsb, uv bs.length] ∧
        Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧ BbRange c st xb xs ∧
        BbRange c st bsb bs)
      (fun _ _ rv s' => ∃ r, rv = some (.u32 r) ∧
        BbChk W sb X c0 prems params st c (Bcf.bbNeg st X.bi xs bs = true) r s')

theorem bb_neg_spec : BbNegSpec (State := State) := by
  intro W sb X c0 c prems params st xb bsb xs bs
  have hs := prog_ck
  apply FnSpec.intro' (fn := bbNeg) rfl
  rintro vs s ⟨rfl, h, hR, hx, hb⟩
  simp [bbNeg, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := bbNeg) rfl
  simp only [bbNeg, Stmt.block, initLocals, List.map, Ty.zero]
  have hxb := hx.bound hR
  have hbb := hb.bound hR
  refine WP.pl_call (bb_pre_spec W sb X c0 c prems params st bsb bs 0) ?_
    ⟨rfl, h, hR, hb, by omega⟩ ?_
  · rule_simp
  rintro s1 r1 ⟨c1, h1, hR1, hcase1⟩
  bb_swap h1 hR1
  rcases hcase1 with rfl | ⟨rfl, hpre1, hsp1, L1, ⟨hL1, hL1p⟩, ht1⟩
  · rule_simp
    apply WP.guard_lit
    rule_simp [noid]
    exact BbChk.zero h hR
  rule_simp
  apply WP.guard_lit
  rule_simp [hR.bb_ne_noid hsp1]
  have hb1 := hb.frame hpre1 hsp1
  have hx1 := hx.frame hpre1 hsp1
  refine WP.pl_call (bb_pre_spec W sb X c0 c1 prems params st bsb bs 1) ?_
    ⟨rfl, h, hR, hb1, by omega⟩ ?_
  · rule_simp
  rintro s2 r2 ⟨c2, h2, hR2, hcase2⟩
  bb_swap h2 hR2
  rcases hcase2 with rfl | ⟨rfl, hpre2, hsp2, L2, ⟨hL2, hL2p⟩, ht2⟩
  · rule_simp
    apply WP.guard_lit
    rule_simp [noid]
    exact BbChk.zero h hR
  rule_simp
  apply WP.guard_lit
  rule_simp [hR.bb_ne_noid hsp2]
  have hpre12 := bb_pre_trans hpre1 hsp1 hpre2
  have hr1 : BbRange c2 st c.k.sp.toNat L1 := ht1.bbRange.frame hpre2 hsp2
  have hx2 := hx1.frame hpre2 hsp2
  have hb2 := hb1.frame hpre2 hsp2
  have hr2 : BbRange c2 st c1.k.sp.toNat L2 := ht2.bbRange
  refine WP.bb_call (bb_zip_not_spec W sb X c0 c2 prems params st c.k.sp.toNat xb L1 xs) ?_
    ⟨rfl, h, hR, hr1, hx2⟩ ?_
  · rule_simp [hL1]
  intro r3 hr3
  rule_simp
  apply WP.guard_lit
  rule_simp
  refine ⟨fun _ => by simp only [RetQ]; exact BbChk.zero h hR, fun hr30 => ?_⟩
  have hspb := hR.bb_sp_le
  apply WP.bb_loop (fun env0 => BbInv s2 env0 "i" [] bs.length
    (fun k => bbAllEq (L2.drop k) X.bi.ff = true → bbAllEq L2 X.bi.ff = true))
  · exact ⟨rfl, 0, [], rfl, by simp [bbSets, Env.set], by omega, fun h => by simpa using h⟩
  rintro env s' ⟨rfl, k, ws, hws, rfl, hk, hres⟩
  obtain rfl := len_shape 0 hws
  simp only [bbSets, List.zip_nil_right]
  rule_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · have hall := bb_all_end (by omega) hres
    refine WP.bb_call (bb_ripple_spec W sb X c0 c2 prems params st c.k.sp.toNat c1.k.sp.toNat bsb
      L1 L2 bs true) ?_ ⟨rfl, h, hR, hr1, hr2, hb2⟩ ?_
    · rule_simp [hL1, hL2]
    intro r4 hr4
    rule_simp
    apply WP.rule_ret
    rule_simp
    refine ⟨c2, h, hR, fun hr40 => ⟨hpre12, by omega, ?_⟩⟩
    have e1 := bb_preSum_of (by omega) hL1p
    have e2 := bb_preAdder_of (by omega) hL2p
    simp only [Bcf.bbNeg, e1, e2]
    unfold bbAllEq at hall
    simp only [hr3 hr30, hall, hr4 hr40, Bool.and_self]
  have hk2 : k < L2.length := by omega
  have hstk := hr2.stk hR h hk2
  have hff := hR.ff_lt
  have hl2 := hr2.lt hk2
  apply WP.guard_lit
  rule_simp [hstk, bb_add_toNat', hr2.rd hk2]
  refine ⟨fun _ => by simp only [LoopQ, RetQ]; exact BbChk.zero h hR,
    fun he => ?_⟩
  apply WP.assign_loop
  rule_simp
  exact ⟨rfl, k + 1, [], rfl, by simp [bbSets, Env.set], by omega, bb_all_step hk2 hres he⟩

/-! ## `bb_sub` -/

def BbSubSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (xb yb bsb : Nat) (xs ys bs : List Nat),
    FnSpec (State := State) Vbcf.prog "bb_sub"
      (fun vs s => vs = [.ptr sb 0, uv xb, uv xs.length, uv yb, uv ys.length, uv bsb, uv bs.length] ∧
        Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧ BbRange c st xb xs ∧
        BbRange c st yb ys ∧ BbRange c st bsb bs)
      (fun _ _ rv s' => ∃ r, rv = some (.u32 r) ∧
        BbChk W sb X c0 prems params st c (Bcf.bbSub st X.bi xs ys bs = true) r s')

theorem bb_sub_spec : BbSubSpec (State := State) := by
  intro W sb X c0 c prems params st xb yb bsb xs ys bs
  have hs := prog_ck
  apply FnSpec.intro' (fn := bbSub) rfl
  rintro vs s ⟨rfl, h, hR, hx, hy, hb⟩
  simp [bbSub, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := bbSub) rfl
  simp only [bbSub, Stmt.block, initLocals, List.map, Ty.zero]
  have hxb := hx.bound hR
  have hyb := hy.bound hR
  have hbb := hb.bound hR
  refine WP.pl_call (bb_pre_spec W sb X c0 c prems params st bsb bs 1) ?_
    ⟨rfl, h, hR, hb, by omega⟩ ?_
  · rule_simp
  rintro s1 r1 ⟨c1, h1, hR1, hcase1⟩
  bb_swap h1 hR1
  rcases hcase1 with rfl | ⟨rfl, hpre1, hsp1, L1, ⟨hL1, hL1p⟩, ht1⟩
  · rule_simp
    apply WP.guard_lit
    rule_simp [noid]
    exact BbChk.zero h hR
  rule_simp
  apply WP.guard_lit
  rule_simp [hR.bb_ne_noid hsp1]
  have hb1 := hb.frame hpre1 hsp1
  have hx1 := hx.frame hpre1 hsp1
  have hy1 := hy.frame hpre1 hsp1
  have hr1 : BbRange c1 st c.k.sp.toNat L1 := ht1.bbRange
  refine WP.bb_call (bb_zip_not_spec W sb X c0 c1 prems params st c.k.sp.toNat yb L1 ys) ?_
    ⟨rfl, h, hR, hr1, hy1⟩ ?_
  · rule_simp [hL1]
  intro r3 hr3
  rule_simp
  apply WP.guard_lit
  rule_simp
  refine ⟨fun _ => by simp only [RetQ]; exact BbChk.zero h hR, fun hr30 => ?_⟩
  refine WP.bb_call (bb_ripple_spec W sb X c0 c1 prems params st xb c.k.sp.toNat bsb
    xs L1 bs true) ?_ ⟨rfl, h, hR, hx1, hr1, hb1⟩ ?_
  · rule_simp [hL1]
  intro r4 hr4
  rule_simp
  apply WP.rule_ret
  rule_simp
  refine ⟨c1, h, hR, fun hr40 => ⟨hpre1, hsp1, ?_⟩⟩
  have e2 := bb_preAdder_of (by omega) hL1p
  simp only [Bcf.bbSub, e2]
  simp only [hr3 hr30, hr4 hr40, Bool.and_self]

end Vbcf.Proof
