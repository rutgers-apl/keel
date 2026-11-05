import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Compact4

/-!
# Vbcf proofs: `ck_compact`, part 5 — the roots loop

```
while (j < st->flen) {
  if (st->lr[j] >= st->flen) {
    r = st->facts[j];
    if (r >= lo && r < plen) {
      if (fw[r - lo] == 0) {
        fw[r - lo] = NOID;
        ok = push(st, r);
        if (ok == 0) { kvfree(fw); return 0; }
      }
    }
  }
  j = j + 1;
}
```
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-- The loop invariant of the roots loop. -/
def RootsInv (W : World) (sb fb : Nat) (c0 : CMem) (S : VSt) (nL : Nat) (n : BitVec 32) :
    Env → (KernelState prog State) → Prop := fun env s =>
  ∃ (c : CMem) (fw : Array EmbC.Val) (j r ok : BitVec 32),
    env = cpEnv sb c0.k.lo c0.k.plen n (.ptr fb 0) j r 0 0 0 0 0 0 0 0 ok .null 0 ∧
    Holds (W.addAux fb ⟨.u32, fw⟩) s.mem sb c ∧ MarkInv S.cs nL c0 c fw (fun _ => False) ∧
    j.toNat ≤ c0.k.flen.toNat ∧ RootsUpTo c0 S nL fw j.toNat

/-- `j = j + 1` at the end of the body. -/
theorem roots_next {W : World} {sb fb : Nat} {c0 : CMem} {S : VSt} {nL : Nat} {n : BitVec 32}
    {Q : (Post prog State)} {s : (KernelState prog State)} {c : CMem} {fw : Array EmbC.Val} {j r ok : BitVec 32}
    (h : Holds (W.addAux fb ⟨.u32, fw⟩) s.mem sb c) (hM : MarkInv S.cs nL c0 c fw (fun _ => False))
    (hj : j.toNat < c0.k.flen.toNat) (hR : RootsUpTo c0 S nL fw (j.toNat + 1)) :
    WP prog (.assign "j" (.bin .add (.var "j") (.lit32 1#32))) (LoopQ (RootsInv W sb fb c0 S nL n) Q)
      (cpEnv sb c0.k.lo c0.k.plen n (.ptr fb 0) j r 0 0 0 0 0 0 0 0 ok .null 0) s := by
  apply WP.assign_loop
  embc_simp [cpEnv]
  have h1 : (j + 1#32).toNat = j.toNat + 1 := bv_add_toNat (by have := c0.k.flen.isLt; simp; omega)
  exact ⟨c, fw, j + 1#32, r, ok, rfl, h, hM, by omega, by rw [h1]; exact hR⟩

theorem cp_roots {W : World} {sb : Nat} {ws : Array (BitVec 32)} {X : Ctx} {S : VSt} {off : Nat}
    {rest : List Step} {c0 : CMem} {fb : Nat} {n : BitVec 32}
    (hS : SInv W ws X c0 S off rest) (hW : W.aux fb = none)
    {rest' : Stmt} {env : Env} {s : (KernelState prog State)} (h0 : RootsInv W sb fb c0 S X.nL n env s)
    (K : ∀ (s' : (KernelState prog State)) (c : CMem) (fw : Array EmbC.Val) (r ok : BitVec 32),
      Holds (W.addAux fb ⟨.u32, fw⟩) s'.mem sb c → MarkInv S.cs X.nL c0 c fw (fun _ => False) →
      RootsUpTo c0 S X.nL fw c0.k.flen.toNat →
      WP prog rest' (retPost (some .u32) (CpPost W sb ws X S off rest))
        (cpEnv sb c0.k.lo c0.k.plen n (.ptr fb 0) c0.k.flen r 0 0 0 0 0 0 0 0 ok .null 0) s') :
    WP prog (.seq cpRoots rest') (retPost (some .u32) (CpPost W sb ws X S off rest)) env s := by
  have hs := prog_ck
  have hcore := hS.inv.core.cinv
  have hrep := hcore.rep
  have hnL := hS.nLcs
  have hlo := hS.lo
  have hplen := hrep.len
  have hfl := hS.flen
  have hfs := hS.factsSize
  obtain ⟨lb, hlb⟩ := hS.lrPtr
  obtain ⟨fab, hfab⟩ := hS.factsPtr
  unfold cpRoots
  apply WP.loop_seq (RootsInv W sb fb c0 S X.nL n) h0
  rintro env s ⟨c, fw, j, r, ok, rfl, h, hM, hj, hR⟩
  have hfr := hM.fr
  ck_simp [cpEnv, hfr.flen]
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · -- the loop is done
    have hje : j = c0.k.flen := by bv_omega
    subst hje
    exact K s c fw r ok h hM hR
  · have hjl : j.toNat < c0.k.flen.toNat := by bv_omega
    have hjS : j.toNat < S.facts.size := by omega
    obtain ⟨f, hf⟩ : ∃ f, S.facts[j.toNat]? = some f :=
      ⟨S.facts[j.toNat], Array.getElem?_eq_getElem hjS⟩
    obtain ⟨w, hw, hu⟩ := hS.lrCells j.toNat (by rw [hS.lrSize]; omega)
    have hlb' : c.k.lr = some (lb, 0) := by rw [hfr.lrPtr]; exact hlb
    have hfab' : c.k.facts = some (fab, 0) := by rw [hfr.factsPtr]; exact hfab
    apply WP.seq
    apply WP.ite
    ck_simp [hlb', h.rd_lr hlb', hfr.lr, rd_u32 hu, hfr.flen]
    refine ⟨fun hlive => ?_, fun hdead => ?_⟩
    · -- a fact cited later
      have hwle : c0.k.flen.toNat ≤ w := by
        have := BitVec.le_def.mp hlive; rw [bv_toNat_ofNat hw] at this; exact this
      have hL : LiveFact c0 S j.toNat f := ⟨hf, w, hw, hu, hwle⟩
      obtain ⟨hflt, hlive'⟩ := hS.facts j.toNat f hf
      obtain ⟨hlvf, huf⟩ := hlive' w hw hu hwle
      have hσ := S.σ_lt hlvf
      have hid : S.id f = offs S.cs.pool (S.σ f) := rfl
      have hoff := offs_lt_end hσ
      apply WP.seq
      apply WP.assign
      ck_simp [hfab', h.rd_facts hfab', hfr.facts, rd_u32 huf]
      apply WP.ite
      embc_simp
      have hid32 : S.id f < 2 ^ 32 := by have := c0.k.plen.isLt; omega
      simp only [BitVec.lt_def, bv_toNat_ofNat hid32]
      by_cases hin : c0.k.lo.toNat ≤ S.id f ∧ S.id f < c0.k.plen.toNat
      · -- a node at or above `lo`: mark it
        obtain ⟨hin1, hin2⟩ := hin
        have hge : X.nL ≤ S.σ f := by
          rw [hlo, hid] at hin1; exact (offs_le_iff hnL).mp hin1
        have hk : offs S.cs.pool (S.σ f) - offs S.cs.pool X.nL < fw.size := by
          rw [hM.size]; omega
        have hsub : (BitVec.ofNat 32 (S.id f) - c0.k.lo).toNat =
            offs S.cs.pool (S.σ f) - offs S.cs.pool X.nL := by
          rw [bv_sub_toNat (by rw [bv_toNat_ofNat hid32]; omega), bv_toNat_ofNat hid32, hlo]; rfl
        rw [ite_eq_right (show ¬ S.id f < c0.k.lo.toNat by omega), ite_eq_left hin2]
        refine ⟨fun _ => ?_, fun h0 => absurd h0 (by decide)⟩
        apply WP.ite
        embc_simp [h.rd_aux, hsub]
        rcases hM.cells _ hk with hz | hn
        · -- not yet marked
          simp only [rd_u32 hz]
          refine ⟨fun _ => ?_, fun hne => absurd hne (by simp)⟩
          apply WP.seq
          apply WP.aux_store h rfl
          embc_simp [hsub]
          refine ⟨hk, fun s1 h1 => ?_⟩
          clear h
          have h := h1
          apply WP.seq
          apply WP.call (push_spec _ sb c (BitVec.ofNat 32 (S.id f)))
          embc_simp
          refine ⟨⟨h, hM.stk⟩, ?_⟩
          intro rv s2 c2 h2 hok2 hfr2 hpre2 hcase
          rcases hcase with ⟨rfl, hsp2⟩ | ⟨rfl, hsp2, htop⟩
          · -- out of work or memory
            embc_simp
            apply WP.ite
            embc_simp
            exact WP.cp_fail (fun _ _ h => ⟨rfl, h⟩) h2 hW
          · embc_simp
            apply WP.ite
            embc_simp
            apply WP.skip
            have hspn : c2.k.sp.toNat = c.k.sp.toNat + 1 := by
              have h1' := hok2.cap
              have h2' := hM.stk.cap
              simp only [maxPool] at h1' h2'
              rw [hsp2, BitVec.toNat_add]; simp; omega
            have hM2 := hM.push hge hσ hk hok2 hfr2 hpre2 hspn htop
            refine roots_next h2 hM2 hjl ?_
            intro j' f' hj' hL' hge'
            rcases Nat.lt_or_ge j' j.toNat with hj'' | hj''
            · exact (hR j' f' hj'' hL' hge').set hk
            · have : j' = j.toNat := by omega
              subst this
              obtain ⟨hff, -⟩ := hL'
              rw [hf] at hff
              cases hff
              exact Mk.set_self hk
        · -- already marked
          have hn0 : ¬ (BitVec.ofNat 32 noidN = 0#32) := by decide
          simp only [rd_u32 hn]
          refine ⟨fun h0 => absurd h0 (by simp [hn0]), fun _ => ?_⟩
          apply WP.skip
          refine roots_next h hM hjl ?_
          intro j' f' hj' hL' hge'
          rcases Nat.lt_or_ge j' j.toNat with hj'' | hj''
          · exact hR j' f' hj'' hL' hge'
          · have : j' = j.toNat := by omega
            subst this
            obtain ⟨hff, -⟩ := hL'
            rw [hf] at hff
            cases hff
            exact hn
      · -- a node below `lo`
        have hlow : ¬ X.nL ≤ S.σ f := by
          intro hge
          apply hin
          refine ⟨?_, ?_⟩
          · rw [hlo, hid]; exact offs_le_of_le hge
          · rw [hplen, hid]; exact hoff
        have hidlo : S.id f < c0.k.lo.toNat := by
          rw [hlo, hid]; exact offs_lt_of_lt (Nat.lt_of_not_le hlow) hnL
        rw [ite_eq_left hidlo]
        refine ⟨fun hc => absurd rfl hc, fun _ => ?_⟩
        apply WP.skip
        refine roots_next h hM hjl ?_
        intro j' f' hj' hL' hge'
        rcases Nat.lt_or_ge j' j.toNat with hj'' | hj''
        · exact hR j' f' hj'' hL' hge'
        · have : j' = j.toNat := by omega
          subst this
          obtain ⟨hff, -⟩ := hL'
          rw [hf] at hff
          cases hff
          exact absurd hge' hlow
    · -- not cited later
      apply WP.skip
      refine roots_next h hM hjl ?_
      intro j' f' hj' hL' hge'
      rcases Nat.lt_or_ge j' j.toNat with hj'' | hj''
      · exact hR j' f' hj'' hL' hge'
      · have : j' = j.toNat := by omega
        subst this
        obtain ⟨-, w', hw', hu', hle'⟩ := hL'
        have hww := U.inj32 hu hu' hw hw'
        subst hww
        exfalso
        have := BitVec.lt_def.mp hdead
        rw [bv_toNat_ofNat hw] at this
        omega

end Vbcf.Proof
