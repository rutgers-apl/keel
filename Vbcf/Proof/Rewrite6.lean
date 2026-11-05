import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Rewrite5

/-!
# Vbcf proofs: the Rewrite family, part 6 — `rw_inst`: the leaf cases

`var`, `tt`, `ff`, `lit`: no recursive call.
-/


namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf Vbcf.RwEnc

theorem rw_inst_var (d : BitVec 32) (i : Nat) : RwInstCase (State := State) d (.var i) := by
  intro W sb X c0 c prems params st pos ab args s h hR hat hwf hargs
  have hs := prog_ck
  dsimp only [rwInstTail, rwInst, Stmt.block, rwInstEnv]
  have hi256 : i < 256 := by simpa [wfE] using hwf
  have hsp := hR.sp_lt
  have hal := hargs.2
  simp only [maxPool] at hsp
  apply WP.ite_seq
  rule_simp [tagE, tVar]
  apply WP.rw_guard (RwInstR.fail h)
  rule_simp [auxE]
  intro hi
  obtain ⟨hia, hU⟩ := hargs.1 i args[i] (List.getElem?_eq_getElem hi)
  have hstk := hR.stk_eq h (by omega)
  have hcell : rd c.stk (ab + i) = some (uv (st.id args[i])) := by
    apply rd_u32; unfold U at hU; exact hU
  apply WP.ret
  rule_simp [LoopQ, RetQ, hstk, hcell, auxE]
  exact ⟨c, h, Or.inr ⟨st, args[i], by simp [instE, hi], hR, VExt.refl st, rfl, fun _ _ => rfl,
    hia, rfl⟩⟩

theorem rw_inst_tt (d : BitVec 32) : RwInstCase (State := State) d .tt := by
  intro W sb X c0 c prems params st pos ab args s h hR hat hwf hargs
  have hs := prog_ck
  dsimp only [rwInstTail, rwInst, Stmt.block, rwInstEnv]
  apply WP.ite_seq
  rule_simp [tagE, tVar, tTT]
  apply WP.ite_seq
  rule_simp [tagE, tVar, tTT]
  apply WP.ret
  rule_simp [LoopQ, RetQ]
  exact ⟨c, h, Or.inr ⟨st, X.bi.tt, by simp [instE], hR, VExt.refl st, rfl, fun _ _ => rfl,
    hR.tt_lt, rfl⟩⟩

theorem rw_inst_ff (d : BitVec 32) : RwInstCase (State := State) d .ff := by
  intro W sb X c0 c prems params st pos ab args s h hR hat hwf hargs
  have hs := prog_ck
  dsimp only [rwInstTail, rwInst, Stmt.block, rwInstEnv]
  apply WP.ite_seq
  rule_simp [tagE, tVar, tFF]
  apply WP.ite_seq
  rule_simp [tagE, tTT, tFF]
  apply WP.ite_seq
  rule_simp [tagE, tFF]
  apply WP.ret
  rule_simp [LoopQ, RetQ]
  exact ⟨c, h, Or.inr ⟨st, X.bi.ff, by simp [instE], hR, VExt.refl st, rfl, fun _ _ => rfl,
    hR.ff_lt, rfl⟩⟩

theorem rw_inst_lit (d : BitVec 32) (v : Nat) : RwInstCase (State := State) d (.lit v) := by
  intro W sb X c0 c prems params st pos ab args s h hR hat hwf hargs
  have hs := prog_ck
  dsimp only [rwInstTail, rwInst, Stmt.block, rwInstEnv]
  have hv : v < 4294967296 := by simpa [wfE] using hwf
  have hw1 : RwEnc.words[pos + 1]? = some v := by
    simp only [encE] at hat
    exact hat.tail.head
  have hpl := (rw_head hat hwf).2.2
  apply WP.ite_seq
  rule_simp [tagE, tVar, tLit]
  apply WP.ite_seq
  rule_simp [tagE, tTT, tLit]
  apply WP.ite_seq
  rule_simp [tagE, tFF, tLit]
  apply WP.ite_seq
  rule_simp [tagE, tLit]
  have hcast : (BitVec.ofNat 32 v).setWidth 64 = BitVec.ofNat 64 v := by
    apply BitVec.eq_of_toNat_eq; simp; omega
  apply WP.rule_mkval mkval_lt_specT h hR 32#32 (BitVec.ofNat 64 v) (fun _ => by simp; omega)
  refine ⟨by rule_simp [rw_findConst, rw_tbl_get hw1, hcast], ?_⟩
  intro s' c' r h' hB
  rule_simp
  apply WP.ret
  rule_simp [LoopQ, RetQ]
  exact ⟨c', h', (hB.mono (fun st' i hP => by
    simpa [instE, Nat.mod_eq_of_lt (show v < 18446744073709551616 by omega)] using hP)).rwB⟩

end Vbcf.Proof
