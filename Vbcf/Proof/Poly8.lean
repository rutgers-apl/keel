import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Poly7

/-!
# Vbcf proofs: the Poly family, part 8 — `lin_f` (`lin_f_spec : LinFSpec`)
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf


theorem lin_f_specD (d : BitVec 32) (IH : ∀ d' : BitVec 32, d'.toNat < d.toNat → LinFSpecD (State := State) d') :
    LinFSpecD (State := State) d := by
  intro W sb X c0 c prems params st w i
  have hs := prog_ck
  apply FnSpec.intro' (fn := linF) rfl
  rintro vs s ⟨rfl, h, hR, hi, hw1, hw64⟩
  simp [linF, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply RetQ.intro (fn := linF) rfl
  simp only [linF, Stmt.block, initLocals, List.map, Ty.zero]
  apply WP.ite_seq
  rule_simp
  refine ⟨fun hd => ?_, fun hd => ?_⟩
  · apply WP.rule_ret; rule_simp [LoopQ]
    exact PlRet.fail h hR
  apply WP.call_seq (tick_spec W sb c) (by rule_simp) ⟨rfl, h⟩
  rintro rv s1 ⟨rfl, h1⟩
  rw [tickM_wev] at h1
  have hR1 := hR.wev (wk := (tickM c).2.k.work) (er := (tickM c).2.k.err) (vl := c.k.val)
  clear h hR
  have hstk1 : (c.wev (tickM c).2.k.work (tickM c).2.k.err c.k.val).stk = c.stk := rfl
  have hsp1 : (c.wev (tickM c).2.k.work (tickM c).2.k.err c.k.val).k.sp = c.k.sp := rfl
  generalize c.wev (tickM c).2.k.work (tickM c).2.k.err c.k.val = c1 at h1 hR1 hstk1 hsp1
  have h := h1
  have hR := hR1
  clear h1 hR1
  rw [PlRet.stk_eq hstk1, ← hsp1]
  rule_simp
  apply WP.ite_seq; rule_simp
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · apply WP.rule_ret; rule_simp [LoopQ]
    exact PlRet.fail h hR
  obtain ⟨n, hn⟩ := node_of_lt hi
  have hf := hR.core.cinv.rep.fits i n hn
  apply WP.assign_seq; rule_simp [hR.core.cinv.rdHdr hn]
  apply WP.assign_seq; rule_simp
  apply WP.assign_seq; rule_simp [hdr_len_bv hf]
  apply WP.assign_seq; rule_simp [cv_hdr_par hf]
  apply WP.call_seq (mask64_spec (BitVec.ofNat 32 w)) (by rule_simp) rfl
  rintro rv s2 ⟨rfl, rfl⟩
  rule_simp
  apply WP.assign_seq; rule_simp
  show WP Vbcf.prog plT0 _ (plFE sb w st i n d 0#32 0#32 c1.k.sp 0#32 0#32 (tickM c).1 0#64) _
  have hop8 := opC_lt32 n.op
  have htl := hf.tailLen
  have hlo := hf.lo
  have hhi := hf.hi
  by_cases h8 : opC n.op = 0x08
  · obtain ⟨w', v, hop⟩ := opC_bvVal_iff.mp h8
    obtain ⟨op, args⟩ := n
    simp only at hop
    subst hop
    exact lfT0_val h hR hi hn hf hw1 hw64 _ _ _ _ _ _
  unfold plFE
  apply lfT0_skip (by omega) h8
  by_cases h0 : opC n.op = 0 ∧ opLo n.op + opHi n.op * 256 = w
  · obtain ⟨w', hop⟩ := opC_bvAdd_iff.mp h0.1
    obtain ⟨op, args⟩ := n
    simp only at hop
    subst hop
    have hww : w' = w := by simpa [opLo, opHi] using h0.2
    subst hww
    exact lfT1_add IH hd h hR hi hn hf hw1 hw64 _ _ _ _ _ _
  apply lfT1_skip (by omega) (by omega) (by omega) h0
  by_cases h10 : opC n.op = 0x10 ∧ tailLen n = 2
  · obtain ⟨w', hop⟩ := opC_bvSub_iff.mp h10.1
    obtain ⟨op, args⟩ := n
    simp only at hop
    subst hop
    obtain ⟨a, b, rfl⟩ := array_eq_two (a := args) (by simpa [tailLen] using h10.2)
    exact lfT2_sub IH hd h hR hi hn hf hw1 hw64 _ _ _ _ _ _
  apply lfT2_skip (by omega) (by omega) h10
  by_cases h80 : opC n.op = 0x80 ∧ tailLen n = 1
  · obtain ⟨w', hop⟩ := opC_bvNeg_iff.mp h80.1
    obtain ⟨op, args⟩ := n
    simp only at hop
    subst hop
    obtain ⟨a, rfl⟩ := array_eq_one (a := args) (by simpa [tailLen] using h80.2)
    exact lfT3_neg IH hd h hR hi hn hf hw1 hw64 _ _ _ _ _ _
  apply lfT3_skip (by omega) (by omega) h80
  by_cases h20 : opC n.op = 0x20 ∧ tailLen n = 2
  · obtain ⟨w', hop⟩ := opC_bvMul_iff.mp h20.1
    obtain ⟨op, args⟩ := n
    simp only at hop
    subst hop
    obtain ⟨a, b, rfl⟩ := array_eq_two (a := args) (by simpa [tailLen] using h20.2)
    exact lfT4_mul IH hd h hR hi hn hf hw1 hw64 _ _ _ _ _ _
  apply lfT4_skip (by omega) (by omega) h20
  exact lfT5_spec h hR hi hw1 hw64 (pl_lin_rest hn h8 h0 h10 h80 h20) _ _ _ _ _ _ _ _ _ _ _


theorem lin_f_spec_aux : ∀ kd (d : BitVec 32), d.toNat = kd → LinFSpecD (State := State) d := by
  intro kd
  induction kd using Nat.strongRecOn with
  | ind kd ih =>
    intro d hd
    exact lin_f_specD d (fun d' hd' => ih d'.toNat (hd ▸ hd') d' rfl)

/-- **`lin_f` pushes the linear form `lin pool w i`** (or fails). -/
theorem lin_f_spec : LinFSpec (State := State) := fun d => lin_f_spec_aux d.toNat d rfl

end Vbcf.Proof
