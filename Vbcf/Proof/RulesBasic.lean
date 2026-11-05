import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Access

/-!
# Vbcf proofs: the basic rules
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-- Comparing a list length passed as `u32` with a literal. -/
theorem uvlen_eq {α : Type} {l : List α} (hl : l.length ≤ 255) (k : Nat) (hk : k < 2 ^ 32) :
    (BitVec.ofNat 32 l.length = BitVec.ofNat 32 k) ↔ l.length = k := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [bv_toNat_ofNat (by omega), bv_toNat_ofNat hk] at this
    exact this
  · intro h; rw [h]

/-- The failure result every rule may return: `NOID`, with ownership intact. -/
theorem rule_fail {W : World} {sb : Nat} {_c c' : CMem} {s' : (KernelState prog State)} {_X : Ctx} {_st : VSt}
    {R : St → Nat → Prop} (h : Holds W s'.mem sb c') :
    ∃ c'' r, some (Val.u32 0xffffffff#32) = some (Val.u32 r) ∧ Holds W s'.mem sb c'' ∧
      (r ≠ noid → ∃ st' f, R st' f) :=
  ⟨c', _, rfl, h, fun hne => absurd rfl hne⟩

theorem r_true_elim_spec :
    RuleSpec (State := State) "r_true_elim" (fun X st pr pa => ruleTrueElim X.bi st pr pa) := by
  intro W sb c X st prems params
  have hs := prog_ck
  apply FnSpec.intro' (fn := rTrueElim) rfl
  rintro vs s ⟨rfl, h, hinv, hprem, hpar, hsp⟩
  simp [rTrueElim, bindParams, Mem.hasTy_ptr h.ck rfl]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  apply WP.seq
  apply WP.ite
  ck_simp [uvlen_eq hprem.1 1 (by decide), uvlen_eq hpar.1 0 (by decide)]
  by_cases hnp : prems.length = 1
  · by_cases hna : params = []
    · subst hna
      obtain ⟨p0, rfl⟩ := List.length_eq_one_iff.mp hnp
      simp only [List.length_cons, List.length_nil, ↓reduceIte]
      embc_simp
      apply WP.skip
      obtain ⟨hp0, hcell0⟩ := hprem.2 0 p0 rfl
      obtain ⟨n0, hn0⟩ := node_of_lv hp0
      obtain ⟨pb, hpool⟩ := hinv.poolPtr
      obtain ⟨qb, hpremp⟩ := hinv.premPtr
      have hrep := hinv.core.rep
      have hfit := hrep.fits p0 n0 hn0
      have hoff := hinv.core.off_lt hp0
      have hend := hinv.core.node_end_lt hn0
      apply WP.seq
      apply WP.assign
      ck_simp [hpremp, h.rd_prem hpremp, rd_u32 hcell0]
      apply WP.seq
      apply WP.ite
      ck_simp [hpool, h.rd_pool hpool, bv_toNat_ofNat (show st.id p0 < 2 ^ 32 by omega),
        rd_u32 (hrep.hdr hn0), code_eq_iff hfit 17 (by decide), opC_eq_iff]
      constructor
      · intro _
        apply WP.ret
        ck_simp [retPost, noid]
        exact ⟨_, h⟩
      · intro hop
        obtain ⟨op, args⟩ := n0
        simp only at hop
        subst hop
        have h2 : args.size = 2 := (hinv.core.ok.typed hn0).fixedArity rfl
        have hsz : nodeSize ⟨.eq, args⟩ = 3 := by simp [nodeSize, tailLen, h2]
        have ha0 : U c.pool (st.id p0 + 1) (st.id args[0]) :=
          hrep.arg hn0 (by decide : ¬ IsLeaf Op.eq) (k := 0) (by show 0 < args.size; omega)
        have ha1 : U c.pool (st.id p0 + 2) (st.id args[1]) :=
          hrep.arg hn0 (by decide : ¬ IsLeaf Op.eq) (k := 1) (by show 1 < args.size; omega)
        have hlt0 : st.lv args[0] := st.args_lv hp0 hn0 (by simp)
        have hlt1 : st.lv args[1] := st.args_lv hp0 hn0 (by simp)
        have ho1 := hinv.core.off_lt hlt1
        have ho0 := hinv.core.off_lt hlt0
        apply WP.skip
        apply WP.seq
        apply WP.ite
        ck_simp [hpool, h.rd_pool hpool, idx_add (show st.id p0 + 2 < 2 ^ 32 by omega),
          rd_u32 ha1, ofNat_eq_iff (show st.id args[1] < 2 ^ 32 by omega), hinv.tt.2]
        have httlt : st.lv X.bi.tt := hinv.tt.1
        constructor
        · intro _
          apply WP.ret
          ck_simp [retPost, noid]
          exact ⟨_, h⟩
        · intro htt
          have htt' : args[1] = X.bi.tt := st.id_inj hlt1 httlt htt
          apply WP.skip
          apply WP.ret
          ck_simp [retPost, hpool, h.rd_pool hpool,
            idx_add (show st.id p0 + 1 < 2 ^ 32 by omega), rd_u32 ha0]
          refine ⟨c, h, fun _ => ⟨st, args[0], ?_, hinv, hlt0, ?_, by constructor <;> rfl⟩⟩
          · simp [ruleTrueElim, St.node, hn0, isEqNode, h2, htt']
          · exact bv_toNat_ofNat (by omega)
    · -- wrong number of parameters
      simp only [hnp, ↓reduceIte]
      embc_simp
      refine ⟨fun _ => ?_, fun e => absurd e hna⟩
      apply WP.ret
      ck_simp [retPost, noid]
      exact ⟨_, h⟩
  · -- wrong number of premises
    simp only [hnp, ↓reduceIte]
    embc_simp
    apply WP.ret
    ck_simp [retPost, noid]
    exact ⟨_, h⟩

end Vbcf.Proof
