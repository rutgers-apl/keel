import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Compact8

/-!
# Vbcf proofs: `ck_compact`, part 9 — the slide

```
while (o < plen) {
  hdr = st->pool[o];
  ar = (hdr >> 8) & 0xff;
  if (plen - o - 1 < ar) { st->err = ERR_LIMIT; kvfree(fw); return 0; }
  if (fw[o - lo] != 0) {
    st->pool[cur] = hdr;
    code = hdr & 0xff;
    i = 0;
    while (i < ar) { … }
    fw[o - lo] = cur;
    cur = cur + 1 + ar;
    nodes = nodes + 1;
  }
  o = o + 1 + ar;
}
```
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-- The invariant of the slide, with node `x` next. -/
def SlideInv (W : World) (sb fb : Nat) (c0 cm : CMem) (S : VSt) (nL : Nat) (n : BitVec 32)
    (posOf : Nat → Nat) (keep : Nat → Bool) (r ok : BitVec 32) : Env → (KernelState prog State) → Prop := fun env s =>
  ∃ (P fw : Array EmbC.Val) (x : Nat) (hdr code ar i cc : BitVec 32),
    env = cpEnv sb c0.k.lo c0.k.plen n (.ptr fb 0) c0.k.flen r (BitVec.ofNat 32 (offs S.cs.pool x))
      hdr code ar i cc (BitVec.ofNat 32 (offK keep S.cs.pool x)) (BitVec.ofNat 32 (cntK keep x - nL))
      ok .null 0 ∧
    Holds (W.addAux fb ⟨.u32, fw⟩) s.mem sb { cm with pool := P } ∧
    nL ≤ x ∧ x ≤ S.cs.pool.size ∧
    SlideCells posOf S.cs.pool keep c0.pool x P ∧ SlideFw S.cs.pool nL keep x fw

theorem SlideFw.zero {pool : Pool} {nL : Nat} {keep : Nat → Bool} {x : Nat} {fw : Array EmbC.Val}
    (hF : SlideFw pool nL keep x fw) {y : Nat} (hy : nL ≤ y) (hys : y < pool.size)
    (hk : keep y = false) : U fw (offs pool y - offs pool nL) 0 := by
  have := hF.node y hy hys
  simp only [hk] at this
  exact this

theorem cp_slide {W : World} {sb : Nat} {ws : Array (BitVec 32)} {X : Ctx} {S : VSt} {off : Nat}
    {rest : List Step} {c0 cm : CMem} {fb : Nat} {n : BitVec 32}
    (hS : SInv W ws X c0 S off rest) (_hW : W.aux fb = none) (hfr : StkFrame c0 cm)
    {keep : Nat → Bool} (hcl : KClosed keep S.cs.pool) (hpre : ∀ y, y < X.nL → keep y = true)
    {r ok : BitVec 32} {rest' : Stmt} {env : Env} {s : (KernelState prog State)}
    (h0 : SlideInv W sb fb c0 cm S X.nL n X.posOf keep r ok env s)
    (K : ∀ (s' : (KernelState prog State)) (P fw : Array EmbC.Val) (hdr code ar i cc : BitVec 32),
      Holds (W.addAux fb ⟨.u32, fw⟩) s'.mem sb { cm with pool := P } →
      SlideCells X.posOf S.cs.pool keep c0.pool S.cs.pool.size P →
      SlideFw S.cs.pool X.nL keep S.cs.pool.size fw →
      WP prog rest' (retPost (some .u32) (CpPost W sb ws X S off rest))
        (cpEnv sb c0.k.lo c0.k.plen n (.ptr fb 0) c0.k.flen r
          (BitVec.ofNat 32 (offs S.cs.pool S.cs.pool.size)) hdr code ar i cc
          (BitVec.ofNat 32 (offK keep S.cs.pool S.cs.pool.size))
          (BitVec.ofNat 32 (cntK keep S.cs.pool.size - X.nL)) ok .null 0) s') :
    WP prog (.seq cpSlide rest') (retPost (some .u32) (CpPost W sb ws X S off rest)) env s := by
  have hs := prog_ck
  have hcore := hS.inv.core.cinv
  have hok := hcore.ok
  have hrep := hcore.rep
  have hnL := hS.nLcs
  have hlo := hS.lo
  have hplen := hrep.len
  obtain ⟨pb, hpb⟩ := hS.inv.poolPtr
  have hpcm : cm.k.pool = some (pb, 0) := by rw [hfr.poolPtr]; exact hpb
  have hP32 := c0.k.plen.isLt
  have hcap := hcore.poolCap
  have hpsz := hcore.poolSize pb 0 hpb
  unfold cpSlide
  apply WP.loop_seq (SlideInv W sb fb c0 cm S X.nL n X.posOf keep r ok) h0
  rintro env s ⟨P, fw, x, hdr, code, ar, i, cc, rfl, h, hx, hxs, hC, hF⟩
  have hpbc : ({ cm with pool := P } : CMem).k.pool = some (pb, 0) := hpcm
  have hox := offs_le_end S.cs.pool x
  have hox32 : offs S.cs.pool x < 2 ^ 32 := by omega
  embc_simp [cpEnv]
  simp only [BitVec.lt_def, bv_toNat_ofNat hox32]
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · -- done
    rw [BitVec.le_def, bv_toNat_ofNat hox32] at hge
    have hxe : x = S.cs.pool.size := by
      rcases Nat.lt_or_ge x S.cs.pool.size with h' | h'
      · have := offs_lt_end h'
        omega
      · omega
    subst hxe
    exact K s P fw hdr code ar i cc h hC hF
  have hxl : x < S.cs.pool.size := by
    rcases Nat.lt_or_ge x S.cs.pool.size with h' | h'
    · exact h'
    · rw [offs_of_size_le h'] at hlt; omega
  obtain ⟨nd, hnd⟩ : ∃ nd, S.cs.pool[x]? = some nd := ⟨_, Array.getElem?_eq_getElem hxl⟩
  have hfit := hrep.fits x nd hnd
  have htl : tailLen nd < 256 := hfit.2.2.1
  have hend := hrep.node_end hnd
  have hhdr := hrep.hdr hnd
  have hPh : P[offs S.cs.pool x]? = some (.u32 (BitVec.ofNat 32 (hdrW nd))) := by
    rw [hC.above _ (Nat.le_refl _)]; exact hhdr
  have hkx' : offK keep S.cs.pool x ≤ offs S.cs.pool x := offK_le_offs x
  have hsucc := offs_succ hnd
  -- hdr = st->pool[o]
  apply WP.seq
  apply WP.assign
  ck_simp [hpcm, h.rd_pool hpbc, bv_toNat_ofNat hox32, rd_u32 hPh]
  -- ar = (hdr >> 8) & 0xff
  apply WP.seq
  apply WP.assign
  ck_simp [hdr_len_bv hfit]
  -- if (plen - o - 1 < ar) …
  apply WP.seq
  apply WP.ite
  ck_simp
  have hbig : ¬ (c0.k.plen - BitVec.ofNat 32 (offs S.cs.pool x) - 1#32 < BitVec.ofNat 32 (tailLen nd)) := by
    unfold nodeSize at hend
    bv_omega
  refine ⟨fun hc => absurd hc hbig, fun _ => ?_⟩
  apply WP.skip
  -- if (fw[o - lo] != 0)
  have hsub : (BitVec.ofNat 32 (offs S.cs.pool x) - c0.k.lo).toNat =
      offs S.cs.pool x - offs S.cs.pool X.nL := by
    have := offs_le_of_le (pool := S.cs.pool) hx
    rw [bv_sub_toNat (by rw [bv_toNat_ofNat hox32]; omega), bv_toNat_ofNat hox32, hlo]
  have hnext_o : BitVec.ofNat 32 (offs S.cs.pool x) + 1#32 + BitVec.ofNat 32 (tailLen nd) =
      BitVec.ofNat 32 (offs S.cs.pool (x + 1)) := by
    rw [hsucc]; unfold nodeSize at hend ⊢
    apply BitVec.eq_of_toNat_eq
    have : offs S.cs.pool x + 1 + tailLen nd < 2 ^ 32 := by omega
    bv_omega
  apply WP.seq
  apply WP.ite
  embc_simp [h.rd_aux, hsub]
  cases hk : keep x with
  | false =>
    -- a dropped node: skip it
    have hz := hF.zero hx hxl hk
    simp only [rd_u32 hz]
    refine ⟨fun hc => absurd hc (by simp), fun _ => ?_⟩
    apply WP.skip
    apply WP.assign_loop
    embc_simp [hnext_o]
    refine ⟨P, fw, x + 1, BitVec.ofNat 32 (hdrW nd), code, BitVec.ofNat 32 (tailLen nd), i, cc, ?_, h,
      by omega, by omega, ?_, ?_⟩
    · rw [offK_succ_drop hk, cntK_succ, hk]; rfl
    · refine ⟨hC.size, fun k hk' => hC.above k (by have := offs_le_succ S.cs.pool x; omega),
        fun y nd' hy hky hnd' => ?_⟩
      rcases Nat.lt_or_ge y x with hyx | hyx
      · exact hC.kept y nd' hyx hky hnd'
      · have : y = x := by omega
        subst this; rw [hk] at hky; cases hky
    · refine ⟨hF.size, hF.cells, fun y hy hys => ?_⟩
      have := hF.node y hy hys
      by_cases hyx : y = x
      · subst hyx; simp only [hk] at this ⊢; exact this
      · by_cases hky : keep y = true
        · simp only [hky, ↓reduceIte] at this ⊢
          by_cases hyx' : y < x
          · rw [ite_eq_left hyx'] at this; rw [ite_eq_left (by omega)]; exact this
          · rw [ite_eq_right hyx'] at this; rw [ite_eq_right (by omega)]; exact this
        · simp only [Bool.not_eq_true] at hky
          simp only [hky] at this ⊢; exact this
  | true =>
    -- a kept node: copy it down
    have hn := hF.node x hx hxl
    simp only [hk, Nat.lt_irrefl, ↓reduceIte] at hn
    simp only [rd_u32 hn]
    refine ⟨fun _ => ?_, fun h0 => absurd h0 (by decide)⟩
    have hkx32 : offK keep S.cs.pool x < 2 ^ 32 := by omega
    have hPsz := hC.size
    -- st->pool[cur] = hdr
    apply WP.seq
    apply WP.ck_store .pool h rfl hpbc
    ck_simp [hpcm, bv_toNat_ofNat hkx32]
    refine ⟨by show _ < P.size; rw [hPsz, hpsz]; unfold nodeSize at hend; omega, fun s1 h1 => ?_⟩
    clear h
    have h : Holds (W.addAux fb ⟨.u32, fw⟩) s1.mem sb
        { cm with pool := P.setIfInBounds (offK keep S.cs.pool x) (.u32 (BitVec.ofNat 32 (hdrW nd))) } := h1
    -- code = hdr & 0xff; i = 0
    apply WP.seq
    apply WP.assign
    ck_simp [uv_and_ff, hdrW_mod256]
    apply WP.seq
    apply WP.assign
    ck_simp
    -- the inner loop
    have hsz1 : (P.setIfInBounds (offK keep S.cs.pool x) (.u32 (BitVec.ofNat 32 (hdrW nd)))).size =
        c0.pool.size := by rw [Array.size_setIfInBounds]; exact hPsz
    refine slide_inner hS hfr hnd hx hcl hk hpre hF ?_
      ⟨_, 0#32, cc, rfl, h, hsz1, ?_, ?_, ?_, by simp⟩
    rotate_left
    · intro k hk'
      simp only [BitVec.toNat_zero, Nat.add_zero] at hk'
      rw [Array.getElem?_setIfInBounds_ne (by omega)]
      exact hC.above k (by omega)
    · intro y nd' hy hky hnd'
      have := offK_add_le (pool := S.cs.pool) hky hnd' hy
      exact WordsAt.setOut (hC.kept y nd' hy hky hnd') (by rw [newW_length]; omega)
    · intro k w hw
      simp only [BitVec.toNat_zero, Nat.add_zero] at hw
      have hk0 : k = 0 := by
        rcases Nat.lt_or_ge k 1 with h' | h'
        · omega
        · rw [List.getElem?_eq_none (by simp; omega)] at hw; cases hw
      subst hk0
      simp [newW] at hw
      subst hw
      exact U.set_self _ (by rw [hPsz, hpsz]; unfold nodeSize at hend; omega)
    -- after the inner loop
    intro s2 P2 cc2 h2 hPs2 hab2 hkp2 hcur2
    -- fw[o - lo] = cur
    have hfwk : offs S.cs.pool x - offs S.cs.pool X.nL < fw.size := by
      rw [hF.size]; have := offs_lt_end hxl; have := offs_le_of_le (pool := S.cs.pool) hx; omega
    apply WP.seq
    apply WP.aux_store h2 rfl
    embc_simp [hsub]
    have hidxfw : 0 + (BitVec.ofNat 32 (offs S.cs.pool x) - c0.k.lo).toNat =
        offs S.cs.pool x - offs S.cs.pool X.nL := by rw [Nat.zero_add, hsub]
    refine ⟨rfl, by rw [hidxfw]; exact hfwk, fun s3 h3 => ?_⟩
    rw [hidxfw] at h3
    -- cur = cur + 1 + ar; nodes = nodes + 1
    have hcntge : X.nL ≤ cntK keep x := by
      have := cntK_mono (keep := keep) hx
      rw [cntK_pre hpre X.nL (Nat.le_refl _)] at this; exact this
    have hcnt32 : cntK keep x + 1 < 2 ^ 32 := by
      have := cntK_le (keep := keep) x
      have := size_le_offs S.cs.pool
      omega
    have hnext_cur : BitVec.ofNat 32 (offK keep S.cs.pool x) + 1#32 + BitVec.ofNat 32 (tailLen nd) =
        BitVec.ofNat 32 (offK keep S.cs.pool (x + 1)) := by
      rw [offK_succ_keep hk hnd]; unfold nodeSize at hend ⊢
      apply BitVec.eq_of_toNat_eq
      have : offK keep S.cs.pool x + 1 + tailLen nd < 2 ^ 32 := by omega
      bv_omega
    have hnext_nodes : BitVec.ofNat 32 (cntK keep x - X.nL) + 1#32 =
        BitVec.ofNat 32 (cntK keep (x + 1) - X.nL) := by
      rw [cntK_succ, hk]
      apply BitVec.eq_of_toNat_eq
      simp only [↓reduceIte]
      have : cntK keep x - X.nL + 1 < 2 ^ 32 := by omega
      rw [show cntK keep x + 1 - X.nL = cntK keep x - X.nL + 1 by omega]
      bv_omega
    apply WP.seq
    apply WP.assign
    embc_simp [cpEnv, hnext_cur]
    apply WP.assign
    embc_simp [hnext_nodes]
    apply WP.assign_loop
    embc_simp [hnext_o]
    refine ⟨P2, _, x + 1, BitVec.ofNat 32 (hdrW nd), BitVec.ofNat 32 (opC nd.op),
      BitVec.ofNat 32 (tailLen nd), BitVec.ofNat 32 (tailLen nd), cc2, rfl, h3, by omega, by omega,
      ⟨hPs2, fun k hk' => hab2 k (by rw [hsucc] at hk'; exact hk'), fun y nd' hy hky hnd' => ?_⟩,
      ⟨by rw [Array.size_setIfInBounds]; exact hF.size, fun k hk' => ?_, fun y hy hys => ?_⟩⟩
    · rcases Nat.lt_or_ge y x with hyx | hyx
      · exact hkp2 y nd' hyx hky hnd'
      · have : y = x := by omega
        subst this; rw [hnd] at hnd'; cases hnd'; exact hcur2
    · rw [Array.size_setIfInBounds] at hk'
      by_cases e : k = offs S.cs.pool x - offs S.cs.pool X.nL
      · subst e; exact ⟨_, hkx32, U.set_self _ hk'⟩
      · obtain ⟨w, hw, hu⟩ := hF.cells k hk'
        exact ⟨w, hw, (U.set_ne e).mpr hu⟩
    · have hold := hF.node y hy hys
      by_cases hyx : y = x
      · subst hyx
        simp only [hk, ↓reduceIte, Nat.lt_succ_self]
        exact U.set_self _ hfwk
      · have hne : offs S.cs.pool y - offs S.cs.pool X.nL ≠ offs S.cs.pool x - offs S.cs.pool X.nL := by
          intro e
          have := offs_le_of_le (pool := S.cs.pool) hy
          have := offs_le_of_le (pool := S.cs.pool) hx
          exact hyx (offs_inj (Nat.le_of_lt hys) (Nat.le_of_lt hxl) (by omega))
        rw [U.set_ne hne]
        by_cases hky : keep y = true
        · simp only [hky, ↓reduceIte] at hold ⊢
          by_cases hyx' : y < x
          · rw [ite_eq_left hyx'] at hold; rw [ite_eq_left (by omega)]; exact hold
          · rw [ite_eq_right hyx'] at hold; rw [ite_eq_right (by omega)]; exact hold
        · simp only [Bool.not_eq_true] at hky
          simp only [hky] at hold ⊢; exact hold

end Vbcf.Proof
