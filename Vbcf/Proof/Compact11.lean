import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Compact10

/-!
# Vbcf proofs: `ck_compact`, part 11 — counting the nodes and sizing the table

```
o = 0;
while (o < lo) {
  ar = (st->pool[o] >> 8) & 0xff;
  if (lo - o - 1 < ar) { st->err = ERR_LIMIT; kvfree(fw); return 0; }
  o = o + 1 + ar;
  nodes = nodes + 1;
}
hc = 1024;
while (hc < 4 * (u64)nodes) {
  ok = tick(st);
  if (ok == 0) { kvfree(fw); return 0; }
  hc = hc * 2;
}
```
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-- The invariant of the counting loop: the state does not change. -/
def CountInv (sb fb : Nat) (c0 : CMem) (S : VSt) (nL : Nat) (n : BitVec 32) (s : (KernelState prog State))
    (cur : BitVec 32) (base : Nat) : Env → (KernelState prog State) → Prop := fun env s' =>
  s' = s ∧ ∃ (y : Nat) (j r hdr code ar i cc ok : BitVec 32),
    env = cpEnv sb c0.k.lo c0.k.plen n (.ptr fb 0) j r (BitVec.ofNat 32 (offs S.cs.pool y)) hdr code ar
      i cc cur (BitVec.ofNat 32 (base + y)) ok .null 0 ∧ y ≤ nL

theorem cp_count {W : World} {sb : Nat} {ws : Array (BitVec 32)} {X : Ctx} {S : VSt} {off : Nat}
    {rest : List Step} {c0 c : CMem} {fb : Nat} {n : BitVec 32} {fw : Array EmbC.Val}
    (hS : SInv W ws X c0 S off rest) {s : (KernelState prog State)}
    (h : Holds (W.addAux fb ⟨.u32, fw⟩) s.mem sb c) (hpp : c.k.pool = c0.k.pool)
    (hhdr : ∀ y nd, y < X.nL → S.cs.pool[y]? = some nd → U c.pool (offs S.cs.pool y) (hdrW nd))
    {cur : BitVec 32} {base : Nat} (hbase : base + X.nL < 2 ^ 32) {rest' : Stmt} {env : Env}
    (h0 : CountInv sb fb c0 S X.nL n s cur base env s)
    (K : ∀ (j r hdr code ar i cc ok : BitVec 32),
      WP prog rest' (retPost (some .u32) (CpPost W sb ws X S off rest))
        (cpEnv sb c0.k.lo c0.k.plen n (.ptr fb 0) j r c0.k.lo hdr code ar i cc cur
          (BitVec.ofNat 32 (base + X.nL)) ok .null 0) s) :
    WP prog (.seq cpCount rest') (retPost (some .u32) (CpPost W sb ws X S off rest)) env s := by
  have hs := prog_ck
  have hcore := hS.inv.core.cinv
  have hrep := hcore.rep
  have hnL := hS.nLcs
  have hlo := hS.lo
  have hplen := hrep.len
  obtain ⟨pb, hpb⟩ := hS.inv.poolPtr
  have hpc : c.k.pool = some (pb, 0) := by rw [hpp]; exact hpb
  have hP32 := c0.k.plen.isLt
  have hloP : offs S.cs.pool X.nL ≤ offs S.cs.pool S.cs.pool.size := offs_le_end _ _
  unfold cpCount
  apply WP.loop_seq (CountInv sb fb c0 S X.nL n s cur base) h0
  rintro env s' ⟨rfl, y, j, r, hdr, code, ar, i, cc, ok, rfl, hy⟩
  have hoy := offs_le_of_le (pool := S.cs.pool) hy
  have hoy32 : offs S.cs.pool y < 2 ^ 32 := by omega
  embc_simp [cpEnv]
  simp only [BitVec.lt_def, bv_toNat_ofNat hoy32]
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · rw [BitVec.le_def, bv_toNat_ofNat hoy32] at hge
    have hye : y = X.nL := by
      rw [hlo] at hge
      rcases Nat.lt_or_ge y X.nL with h' | h'
      · have := offs_lt_of_lt h' hnL; omega
      · omega
    subst hye
    have : BitVec.ofNat 32 (offs S.cs.pool X.nL) = c0.k.lo := by
      apply BitVec.eq_of_toNat_eq; rw [bv_toNat_ofNat hoy32, hlo]
    rw [this]
    exact K j r hdr code ar i cc ok
  have hyl : y < X.nL := by
    rw [hlo] at hlt
    rcases Nat.lt_or_ge y X.nL with h' | h'
    · exact h'
    · have := offs_le_of_le (pool := S.cs.pool) h'; omega
  have hys : y < S.cs.pool.size := by omega
  obtain ⟨nd, hnd⟩ : ∃ nd, S.cs.pool[y]? = some nd := ⟨_, Array.getElem?_eq_getElem hys⟩
  have hfit := hrep.fits y nd hnd
  have htl : tailLen nd < 256 := hfit.2.2.1
  have hsucc := offs_succ hnd
  have hy1 : offs S.cs.pool (y + 1) ≤ offs S.cs.pool X.nL := offs_le_of_le (by omega)
  -- ar = (st->pool[o] >> 8) & 0xff
  apply WP.seq
  apply WP.assign
  ck_simp [hpc, h.rd_pool hpc, bv_toNat_ofNat hoy32, rd_u32 (hhdr y nd hyl hnd), hdr_len_bv hfit]
  -- if (lo - o - 1 < ar) …
  apply WP.seq
  apply WP.ite
  ck_simp
  have hbig : ¬ (c0.k.lo - BitVec.ofNat 32 (offs S.cs.pool y) - 1#32 < BitVec.ofNat 32 (tailLen nd)) := by
    unfold nodeSize at hsucc
    bv_omega
  refine ⟨fun hc => absurd hc hbig, fun _ => ?_⟩
  apply WP.skip
  have hnext_o : BitVec.ofNat 32 (offs S.cs.pool y) + 1#32 + BitVec.ofNat 32 (tailLen nd) =
      BitVec.ofNat 32 (offs S.cs.pool (y + 1)) := by
    rw [hsucc]; unfold nodeSize at hsucc ⊢
    apply BitVec.eq_of_toNat_eq
    have : offs S.cs.pool y + 1 + tailLen nd < 2 ^ 32 := by omega
    bv_omega
  have hnext_n : BitVec.ofNat 32 (base + y) + 1#32 = BitVec.ofNat 32 (base + (y + 1)) := by
    apply BitVec.eq_of_toNat_eq
    have : base + y + 1 < 2 ^ 32 := by omega
    bv_omega
  apply WP.seq
  apply WP.assign
  embc_simp [hnext_o]
  apply WP.assign_loop
  embc_simp [hnext_n]
  exact ⟨rfl, y + 1, j, r, hdr, code, _, i, cc, ok, rfl, by omega⟩

/-- The invariant of the sizing loop: `hc = 2^(10+k)`, and below twice the target. -/
def GrowInv (W : World) (sb fb : Nat) (c0 c : CMem) (n : BitVec 32) (fw : Array EmbC.Val)
    (o cur : BitVec 32) (N : Nat) : Env → (KernelState prog State) → Prop := fun env s =>
  ∃ (wk er j r hdr code ar i cc ok : BitVec 32) (k : Nat),
    env = cpEnv sb c0.k.lo c0.k.plen n (.ptr fb 0) j r o hdr code ar i cc cur (BitVec.ofNat 32 N) ok
      .null (BitVec.ofNat 64 (2 ^ (10 + k))) ∧
    Holds (W.addAux fb ⟨.u32, fw⟩) s.mem sb (c.wev wk er c.k.val) ∧
    (k = 0 ∨ 2 ^ (10 + k) < 8 * N)

theorem cp_grow {W : World} {sb : Nat} {ws : Array (BitVec 32)} {X : Ctx} {S : VSt} {off : Nat}
    {rest : List Step} {c0 c : CMem} {fb : Nat} {n : BitVec 32} {fw : Array EmbC.Val}
    (hW : W.aux fb = none) {o cur : BitVec 32} {N : Nat} (hN : N < 2 ^ 32) {rest' : Stmt}
    {env : Env} {s : (KernelState prog State)} (h0 : GrowInv W sb fb c0 c n fw o cur N env s)
    (K : ∀ (s' : (KernelState prog State)) (wk er j r hdr code ar i cc ok : BitVec 32) (k : Nat),
      Holds (W.addAux fb ⟨.u32, fw⟩) s'.mem sb (c.wev wk er c.k.val) →
      4 * N ≤ 2 ^ (10 + k) → (k = 0 ∨ 2 ^ (10 + k) < 8 * N) →
      WP prog rest' (retPost (some .u32) (CpPost W sb ws X S off rest))
        (cpEnv sb c0.k.lo c0.k.plen n (.ptr fb 0) j r o hdr code ar i cc cur (BitVec.ofNat 32 N) ok
          .null (BitVec.ofNat 64 (2 ^ (10 + k)))) s') :
    WP prog (.seq cpGrow rest') (retPost (some .u32) (CpPost W sb ws X S off rest)) env s := by
  unfold cpGrow
  apply WP.loop_seq (GrowInv W sb fb c0 c n fw o cur N) h0
  rintro env s ⟨wk, er, j, r, hdr, code, ar, i, cc, ok, k, rfl, h, hk⟩
  have hk35 : 10 + k < 35 := by
    rcases hk with e | e
    · omega
    · have : 2 ^ (10 + k) < 2 ^ 35 := by
        have : 8 * N < 2 ^ 35 := by omega
        omega
      exact (Nat.pow_lt_pow_iff_right (by decide)).mp this
  have hpow : 2 ^ (10 + k) < 2 ^ 35 := Nat.pow_lt_pow_right (by decide) hk35
  have hpow64 : 2 ^ (10 + k) < 2 ^ 64 := by
    have : (2 : Nat) ^ 35 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by decide)
    omega
  embc_simp [cpEnv]
  have hN64 : (BitVec.setWidth 64 (BitVec.ofNat 32 N)).toNat = N := by
    rw [BitVec.toNat_setWidth, bv_toNat_ofNat hN]; omega
  have hmul : (4#64 * BitVec.setWidth 64 (BitVec.ofNat 32 N)).toNat = 4 * N := by
    rw [BitVec.toNat_mul, hN64]; simp; omega
  simp only [BitVec.lt_def, hmul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpow64]
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · rw [BitVec.le_def, hmul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpow64] at hge
    exact K s wk er j r hdr code ar i cc ok k h hge hk
  apply WP.seq
  apply WP.call (tick_spec _ sb (c.wev wk er c.k.val))
  embc_simp
  refine ⟨h, ?_⟩
  intro rv s1 hrv h1
  subst hrv
  rw [tickM_wev, wev_wev] at h1
  embc_simp
  apply WP.seq
  apply WP.ite
  embc_simp
  refine ⟨fun h0 => ?_, fun hne => ?_⟩
  · refine WP.cp_fail (ws := ws) (X := X) (st := S) (off := off) (rest := rest)
      (fun e s' h => ⟨rfl, h⟩) h1 hW
  · apply WP.skip
    apply WP.assign_loop
    embc_simp
    have hnext : BitVec.ofNat 64 (2 ^ (10 + k)) * 2#64 = BitVec.ofNat 64 (2 ^ (10 + (k + 1))) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpow64]
      rw [show 10 + (k + 1) = (10 + k) + 1 by omega, Nat.pow_succ]
      simp
      rw [Nat.pow_succ]
    refine ⟨_, _, j, r, hdr, code, ar, i, cc, _, k + 1, by rw [hnext]; rfl, h1, Or.inr ?_⟩
    rw [show 10 + (k + 1) = (10 + k) + 1 by omega, Nat.pow_succ]
    omega

end Vbcf.Proof
