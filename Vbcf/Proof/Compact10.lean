import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Compact9

/-!
# Vbcf proofs: `ck_compact`, part 10 — remapping the facts

```
while (j < st->flen) {
  r = st->facts[j];
  if (r >= lo && r < plen) {
    c = fw[r - lo];
    if (c == 0) { c = NOID; }
    st->facts[j] = c;
  }
  j = j + 1;
}
```
A fact still cited later gets its node's new offset; the others get some word.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-- The invariant of the remapping loop. -/
def RemapInv (W : World) (sb fb : Nat) (c0 c1 : CMem) (S : VSt) (n : BitVec 32)
    (keep : Nat → Bool) (fw : Array EmbC.Val) (o cur nodes : BitVec 32) : Env → (KernelState prog State) → Prop :=
  fun env s =>
  ∃ (F : Array EmbC.Val) (j r hdr code ar i cc ok : BitVec 32),
    env = cpEnv sb c0.k.lo c0.k.plen n (.ptr fb 0) j r o hdr code ar i cc cur nodes ok .null 0 ∧
    Holds (W.addAux fb ⟨.u32, fw⟩) s.mem sb { c1 with facts := F } ∧
    j.toNat ≤ c0.k.flen.toNat ∧ F.size = c0.facts.size ∧
    (∀ k, k < F.size → ∃ w, w < 2 ^ 32 ∧ U F k w) ∧
    (∀ k, j.toNat ≤ k → F[k]? = c0.facts[k]?) ∧
    (∀ k f, k < j.toNat → LiveFact c0 S k f → U F k (offK keep S.cs.pool (S.σ f)))

theorem cp_remap {W : World} {sb : Nat} {ws : Array (BitVec 32)} {X : Ctx} {S : VSt} {off : Nat}
    {rest : List Step} {c0 c1 : CMem} {fb : Nat} {n : BitVec 32}
    (hS : SInv W ws X c0 S off rest)
    (hfp : c1.k.facts = c0.k.facts) (hfl : c1.k.flen = c0.k.flen)
    {keep : Nat → Bool} (hpre : ∀ y, y < X.nL → keep y = true)
    (hroot : ∀ j f, LiveFact c0 S j f → keep (S.σ f) = true)
    {fw : Array EmbC.Val} (hF : SlideFw S.cs.pool X.nL keep S.cs.pool.size fw)
    {o cur nodes : BitVec 32} {rest' : Stmt} {env : Env} {s : (KernelState prog State)}
    (h0 : RemapInv W sb fb c0 c1 S n keep fw o cur nodes env s)
    (K : ∀ (s' : (KernelState prog State)) (F : Array EmbC.Val) (r hdr code ar i cc ok : BitVec 32),
      Holds (W.addAux fb ⟨.u32, fw⟩) s'.mem sb { c1 with facts := F } →
      F.size = c0.facts.size → (∀ k, k < F.size → ∃ w, w < 2 ^ 32 ∧ U F k w) →
      (∀ k f, LiveFact c0 S k f → U F k (offK keep S.cs.pool (S.σ f))) →
      WP prog rest' (retPost (some .u32) (CpPost W sb ws X S off rest))
        (cpEnv sb c0.k.lo c0.k.plen n (.ptr fb 0) c0.k.flen r o hdr code ar i cc cur nodes ok .null 0) s') :
    WP prog (.seq cpRemap rest') (retPost (some .u32) (CpPost W sb ws X S off rest)) env s := by
  have hs := prog_ck
  have hcore := hS.inv.core.cinv
  have hrep := hcore.rep
  have hnL := hS.nLcs
  have hlo := hS.lo
  have hplen := hrep.len
  have hfls := hS.flen
  have hfsz := hS.factsSize
  obtain ⟨fab, hfab⟩ := hS.factsPtr
  have hfab1 : c1.k.facts = some (fab, 0) := by rw [hfp]; exact hfab
  have hP32 := c0.k.plen.isLt
  unfold cpRemap
  apply WP.loop_seq (RemapInv W sb fb c0 c1 S n keep fw o cur nodes) h0
  rintro env s ⟨F, j, r, hdr, code, ar, i, cc, ok, rfl, h, hj, hFs, hFc, hFo, hFl⟩
  have hfabF : ({ c1 with facts := F } : CMem).k.facts = some (fab, 0) := hfab1
  ck_simp [cpEnv, hfl]
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · have hje : j = c0.k.flen := by bv_omega
    subst hje
    refine K s F r hdr code ar i cc ok h hFs hFc (fun k f hL => ?_)
    have : k < c0.k.flen.toNat := by
      obtain ⟨hf, -⟩ := hL
      have := lt_size_of_getElem? hf; omega
    exact hFl k f this hL
  have hjl : j.toNat < c0.k.flen.toNat := by bv_omega
  have hjF : j.toNat < F.size := by omega
  obtain ⟨w, hw, hu⟩ := hFc j.toNat hjF
  have hj1 : (j + 1#32).toNat = j.toNat + 1 := bv_add_toNat (by have := c0.k.flen.isLt; simp; omega)
  -- r = st->facts[j]
  apply WP.seq
  apply WP.assign
  ck_simp [hfab1, h.rd_facts hfabF, rd_u32 hu]
  -- what a live fact at `j` reads
  have hlive : ∀ f, LiveFact c0 S j.toNat f → w = S.id f ∧ S.lv f := by
    intro f hL
    obtain ⟨hf, w', hw', hu', hle⟩ := hL
    obtain ⟨-, h2⟩ := hS.facts j.toNat f hf
    obtain ⟨hlv, huf⟩ := h2 w' hw' hu' hle
    have hc0 : U c0.facts j.toNat w := by
      unfold U; rw [← hFo j.toNat (Nat.le_refl _)]; exact hu
    have hid32 : S.id f < 2 ^ 32 := by
      have := offs_le_end S.cs.pool (S.σ f); unfold VSt.id; omega
    exact ⟨U.inj32 hc0 huf hw hid32, hlv⟩
  apply WP.seq
  apply WP.ite
  embc_simp
  simp only [BitVec.lt_def, bv_toNat_ofNat hw]
  by_cases hin : c0.k.lo.toNat ≤ w ∧ w < c0.k.plen.toNat
  · obtain ⟨hin1, hin2⟩ := hin
    have h10 : ¬ (1#32 : BitVec 32) = 0#32 := by decide
    simp only [show ¬ w < c0.k.lo.toNat by omega, hin2, h10, ↓reduceIte]
    refine ⟨fun _ => ?_, fun h0 => absurd h0 (by decide)⟩
    have hsub : (BitVec.ofNat 32 w - c0.k.lo).toNat = w - c0.k.lo.toNat := by
      rw [bv_sub_toNat (by rw [bv_toNat_ofNat hw]; omega), bv_toNat_ofNat hw]
    have hfwk : w - c0.k.lo.toNat < fw.size := by rw [hF.size, ← hlo, ← hplen]; omega
    obtain ⟨v, hv, huv⟩ := hF.cells _ hfwk
    -- c = fw[r - lo]
    apply WP.seq
    apply WP.assign
    embc_simp [h.rd_aux, hsub, rd_u32 huv]
    -- if (c == 0) c = NOID; st->facts[j] = c;
    have hfin : ∀ (v' : Nat), v' < 2 ^ 32 → (v ≠ 0 → v' = v) →
        WP prog (.store (.field (.var "st") "facts") (.var "j") (.var "c"))
          (fun oc env' st' => match oc with
            | .normal => WP prog (.assign "j" (.bin .add (.var "j") (.lit32 1#32)))
                (LoopQ (RemapInv W sb fb c0 c1 S n keep fw o cur nodes)
                  (retPost (some .u32) (CpPost W sb ws X S off rest))) env' st'
            | o' => LoopQ (RemapInv W sb fb c0 c1 S n keep fw o cur nodes)
                  (retPost (some .u32) (CpPost W sb ws X S off rest)) o' env' st')
          (cpEnv sb c0.k.lo c0.k.plen n (.ptr fb 0) j (BitVec.ofNat 32 w) o hdr code ar i
            (BitVec.ofNat 32 v') cur nodes ok .null 0) s := by
      intro v' hv' hvv
      apply WP.ck_store .facts h rfl hfabF
      ck_simp [cpEnv, hfab1]
      refine ⟨hjF, fun s1 h1 => ?_⟩
      apply WP.assign
      embc_simp
      refine ⟨F.setIfInBounds j.toNat (.u32 (BitVec.ofNat 32 v')), j + 1#32, BitVec.ofNat 32 w, hdr, code,
        ar, i, BitVec.ofNat 32 v', ok, rfl, h1, by omega, by rw [Array.size_setIfInBounds]; exact hFs,
        ?_, ?_, ?_⟩
      · intro k hk
        rw [Array.size_setIfInBounds] at hk
        by_cases e : k = j.toNat
        · subst e; exact ⟨v', hv', U.set_self _ hk⟩
        · obtain ⟨w2, hw2, hu2⟩ := hFc k hk
          exact ⟨w2, hw2, (U.set_ne e).mpr hu2⟩
      · intro k hk
        rw [hj1] at hk
        rw [Array.getElem?_setIfInBounds_ne (by omega)]
        exact hFo k (by omega)
      · intro k f hk hL
        rw [hj1] at hk
        by_cases e : k = j.toNat
        · subst e
          obtain ⟨hwid, hlv⟩ := hlive f hL
          have hkf := hroot _ f hL
          have hσ := S.σ_lt hlv
          have hge : X.nL ≤ S.σ f := by
            rw [hwid, hlo] at hin1; exact (offs_le_iff hnL).mp hin1
          have hfwv := hF.node (S.σ f) hge hσ
          simp only [hkf, hσ, ↓reduceIte] at hfwv
          rw [hwid, hlo] at huv
          have hb1 := offK_le_offs (keep := keep) (pool := S.cs.pool) (S.σ f)
          have hb2 := offs_le_end S.cs.pool (S.σ f)
          have hvv' := U.inj32 huv hfwv hv (by omega)
          have hpos : v ≠ 0 := by
            rw [hvv']
            have h1 := offK_mono (keep := keep) (pool := S.cs.pool) hge
            rw [offK_pre hpre hnL X.nL (Nat.le_refl _)] at h1
            have h2 : 0 < offs S.cs.pool X.nL := by
              have := hS.ttL
              have := offs_lt_of_lt (pool := S.cs.pool) (Nat.zero_lt_of_lt this) hnL
              simpa using this
            omega
          have : v' = offK keep S.cs.pool (S.σ f) := by rw [hvv hpos, hvv']
          rw [this]
          exact U.set_self _ hjF
        · rw [U.set_ne e]
          exact hFl k f (by omega) hL
    apply WP.seq
    apply WP.ite
    embc_simp
    by_cases hv0 : v = 0
    · subst hv0
      refine ⟨fun _ => ?_, fun h0 => absurd rfl h0⟩
      apply WP.assign
      embc_simp
      exact hfin noidN (by decide) (fun h => absurd rfl h)
    · have : ¬ (BitVec.ofNat 32 v = 0#32) := by
        rw [ofNat32_inj hv (by decide)]; exact hv0
      refine ⟨fun h0 => absurd h0 this, fun _ => ?_⟩
      apply WP.skip
      exact hfin v hv (fun _ => rfl)
  · -- out of range: unchanged
    have hz : (if w < c0.k.lo.toNat then (0#32 : BitVec 32) else
        (if w < c0.k.plen.toNat then 1#32 else 0#32)) = 0#32 := by
      by_cases h1 : w < c0.k.lo.toNat
      · simp [h1]
      · have h2 : ¬ w < c0.k.plen.toNat := fun h2 => hin ⟨by omega, h2⟩
        simp [h1, h2]
    rw [ite_some_u32, hz]
    dsimp only
    refine ⟨fun hc => absurd rfl hc, fun _ => ?_⟩
    apply WP.skip
    apply WP.assign_loop
    embc_simp
    refine ⟨F, j + 1#32, BitVec.ofNat 32 w, hdr, code, ar, i, cc, ok, rfl, h, by omega, hFs, hFc,
      fun k hk => hFo k (by omega), fun k f hk hL => ?_⟩
    rw [hj1] at hk
    by_cases e : k = j.toNat
    · subst e
      obtain ⟨hwid, hlv⟩ := hlive f hL
      have hσ := S.σ_lt hlv
      have hlow : S.σ f < X.nL := by
        rcases Nat.lt_or_ge (S.σ f) X.nL with hl | hge
        · exact hl
        · exfalso
          apply hin
          rw [hwid, hlo, hplen]
          exact ⟨offs_le_of_le hge, offs_lt_end hσ⟩
      rw [offK_pre hpre hnL _ (Nat.le_of_lt hlow)]
      have : U c0.facts j.toNat w := by unfold U; rw [← hFo j.toNat (Nat.le_refl _)]; exact hu
      unfold U at this ⊢
      rw [hFo j.toNat (Nat.le_refl _)]
      rw [hwid] at this
      exact this
    · exact hFl k f (by omega) hL

end Vbcf.Proof
