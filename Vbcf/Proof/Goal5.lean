import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Goal4

/-!
# Vbcf proofs: `ck_goal`, part 5 (the argument loop)
-/

namespace Vbcf.Proof

variable {State : Type}
open Bcf EmbC Vbcf
set_option autoImplicit false

/-- Invariant of the argument loop. -/
def AInv (W : World) (sb gb : Nat) (c1 : CMem) (X : Ctx) (st : St) (gws : Array (BitVec 32))
    (n : Node) (σP : Nat → Option Nat) (i : Nat)
    (goal nv sbv q ci ah ph code vlen pv : BitVec 32) : Env → (KernelState prog State) → Prop :=
  fun env s => ∃ (c3 : CMem) (k m a pa : BitVec 32) (μ : Nat → Option Nat),
    env = genv sb gb goal nv c1.k.plen sbv nv q m ci ah ph code vlen k a pa pv 1#32 ∧
    k.toNat ≤ vlen.toNat ∧ Holds W s.mem sb c3 ∧ TailEq c1 c3 ∧
    ArgsOK st.pool gws X.posOf X.goal c1.k.plen.toNat goal.toNat c1.k.nexpr.toNat c3.pool μ σP
      q.toNat i n k.toNat

section
variable {W : World} {sb gb pb : Nat} {c1 : CMem} {X : Ctx} {st : St} {gws : Array (BitVec 32)}
  {goal nv sbv : BitVec 32}

theorem goal_args_wp (hF : GFacts W sb gb pb c1 X st gws goal nv sbv) {Q : (Post prog State)}
    (hQn : ∀ env' s', MInv W sb gb c1 X st gws goal nv sbv env' s' → Q .normal env' s')
    (hQr : ∀ env' s' c2, Holds W s'.mem sb c2 → TailEq c1 c2 →
      Q (.ret (some (.u32 0#32))) env' s')
    {s : (KernelState prog State)} {c2 : CMem} {μ σP : Nat → Option Nat} {i : Nat} {n : Node}
    {q m ci ah ph code vlen a pa pv : BitVec 32}
    (h : Holds W s.mem sb c2) (ht : TailEq c1 c2)
    (hsw : SweepOK st.pool gws X.posOf X.goal c1.k.plen.toNat goal.toNat c1.k.nexpr.toNat c2.pool
      μ σP (q.toNat + 1))
    (hm : μ q.toNat = some i) (hn : st.pool[i]? = some n)
    (h18 : opC n.op ≠ 0x18) (h19 : opC n.op ≠ 0x19) (h08 : opC n.op ≠ 0x08)
    (hci : ci.toNat = offs st.pool i) (hw : wordFn gws q.toNat = hdrW n)
    (hvlen : vlen.toNat = n.args.size) :
    WP Vbcf.prog [cstms|
        while (k < vlen) {
          a = gx[q + 1 + k];
          if (a >= q) { return 0; }
          if ((u64)a + 1ull + (u64)((gx[a] >> 8) & 0xff) > (u64)q) { return 0; }
          pa = st->pool[ci + 1 + k];
          m = st->pool[base + a];
          if (m == 0) { st->pool[base + a] = pa + 1; }
          else if (m != pa + 1) { return 0; }
          k = k + 1;
        }]
      Q (genv sb gb goal nv c1.k.plen sbv nv q m ci ah ph code vlen 0#32 a pa pv 1#32) s := by
  have hs := prog_ck
  have hc1 := hF.core
  have hf := (hF.core.tailEq ht).rep.fits i n hn
  obtain ⟨hQ, -, hfit⟩ := hsw.mdom _ _ hm
  have hvl : hdrVlen (wordFn gws q.toNat) = vlen.toNat := by
    rw [hw]; show hdrW n / 256 % 256 = _; rw [hdrW_len hf, hvlen]
    by_cases hl : IsLeaf n.op
    · rw [hc1.args_nil hn hl]
      rcases isLeaf_iff.mp hl with ⟨_, _, e⟩ | ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, e⟩ <;>
        simp [opC, tailLen, e] at h18 h19 h08 ⊢
    · exact tailLen_of_not_leaf hl
  have hv256 : hdrVlen (wordFn gws q.toNat) < 256 := by unfold hdrVlen; omega
  have hG : goal.toNat + 1 ≤ 2 ^ 30 := by
    have := hF.room; have := hF.nv; have := hF.core.poolCap; simp only [maxPool] at *; omega
  have hoff := hc1.off_lt (lt_size_of_getElem? hn)
  have hend := hc1.node_end_lt hn
  have hpc := hF.core.poolCap
  have hroom := hF.room
  have hnv := hF.nv
  simp only [maxPool] at hpc
  simp only [Stmt.block]
  apply WP.while (AInv W sb gb c1 X st gws n σP i goal nv sbv q ci ah ph code vlen pv)
  · exact ⟨c2, 0#32, m, a, pa, μ, rfl, by simp, h, ht, ⟨hsw, hm, fun k' hk' => by simp at hk'⟩⟩
  clear h ht hsw hm
  rintro env s ⟨c3, kk, m, a, pa, μ, rfl, hkle, h, ht, hA⟩
  have hk := ht.k
  have hc3 := hF.core.tailEq ht
  have hpool3 : c3.k.pool = some (pb, 0) := by rw [hk]; exact hF.pool
  have harr := h.arena hF.arena
  ck_simp [genv]
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · have hkv : kk.toNat = n.args.size := by rw [BitVec.le_def] at hge; omega
    rw [hkv] at hA
    refine hQn _ _ ⟨c3, q, m, ci, ah, ph, code, vlen, kk, a, pa, pv, μ, σP, rfl, by omega, h, ht,
      hA.finish hn hf h18 h19 h08 (hc1.args_nil hn) hw⟩
  have hK : kk.toNat < n.args.size := by rw [BitVec.lt_def] at hlt; omega
  have hnl : ¬ IsLeaf n.op := fun hl => by
    have := hc1.args_nil hn hl; rw [this] at hK; simp at hK
  -- a = gx[q + 1 + k];
  have hidx1 : (q + 1#32 + kk).toNat = q.toNat + 1 + kk.toNat := by
    rw [bv_add_toNat, bv_add_toNat] <;> simp <;> omega
  have hgx := arena_cell (gws := gws) (i := q.toNat + 1 + kk.toNat) (by omega)
  apply WP.assign_seq
  ck_simp [genv, harr.loadArr, hidx1, rd_u32 hgx]
  obtain ⟨A, hAw⟩ : ∃ A, wordFn gws (q.toNat + 1 + kk.toNat) = A := ⟨_, rfl⟩
  have hAv : gws[q.toNat + 1 + kk.toNat]! = BitVec.ofNat 32 A := by
    rw [← hAw]; exact (bv_ofNat_toNat _).symm
  rw [hAv]
  have hAlt : A < 2 ^ 32 := by rw [← hAw]; exact wordFn_lt gws _
  -- if (a >= q) return 0;
  apply WP.ifRet
  ck_simp
  refine ⟨fun _ => hQr _ _ c3 h ht, fun hAq => ?_⟩
  have hAq' : A < q.toNat := by
    rw [BitVec.lt_def, bv_toNat_ofNat hAlt] at hAq; omega
  -- if ((u64)a + 1 + (u64)((gx[a] >> 8) & 0xff) > (u64)q) return 0;
  have hgxa := arena_cell (gws := gws) (i := A) (by omega)
  have hvA : (BitVec.setWidth 64 gws[A]! >>> 8 &&& 255#64).toNat = hdrVlen (wordFn gws A) := by
    have := (gws[A]!).isLt
    rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega),
      Nat.shiftRight_eq_div_pow]
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, nat_and_ff]
    rfl
  have h64 : (BitVec.setWidth 64 (BitVec.ofNat 32 A) + 1#64 +
      (BitVec.setWidth 64 gws[A]! >>> 8 &&& 255#64)).toNat = A + 1 + hdrVlen (wordFn gws A) := by
    have : hdrVlen (wordFn gws A) < 256 := by unfold hdrVlen; omega
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_setWidth, hvA, bv_toNat_ofNat hAlt]
    simp; omega
  apply WP.ifRet
  ck_simp [harr.loadArr, bv_toNat_ofNat hAlt, rd_u32 hgxa]
  refine ⟨fun _ => hQr _ _ c3 h ht, fun hfa => ?_⟩
  have hfa' : A + 1 + hdrVlen (wordFn gws A) ≤ q.toNat := by
    rw [BitVec.le_def, h64, BitVec.toNat_setWidth] at hfa; have := q.isLt; omega
  -- pa = st->pool[ci + 1 + k];
  have hidx2 : (ci + 1#32 + kk).toNat = offs st.pool i + 1 + kk.toNat := by
    have : nodeSize n = 1 + n.args.size := nodeSize_of_not_leaf hnl
    rw [bv_add_toNat, bv_add_toNat] <;> simp <;> omega
  have hpa := hc3.rep.arg hn hnl hK
  apply WP.assign_seq
  ck_simp [genv, hpool3, h.rd_pool hpool3, hidx2, rd_u32 hpa]
  -- m = st->pool[base + a];
  have hAG : A ≤ goal.toNat := by omega
  have hidx3 : (c1.k.plen + BitVec.ofNat 32 A).toNat = c1.k.plen.toNat + A := by
    rw [bv_add_toNat] <;> rw [bv_toNat_ofNat hAlt] <;> omega
  have hmark := hA.sw.mark A hAG
  have hargl : n.args[kk.toNat] < st.pool.size := by
    have := hc1.ok.args_lt hn _ (Array.getElem_mem hK)
    have := lt_size_of_getElem? hn; omega
  have hpaoff := hc1.off_lt hargl
  have hk1 : (kk + 1#32).toNat = kk.toNat + 1 := by
    rw [bv_add_toNat] <;> simp <;> omega
  have hpa1 : BitVec.ofNat 32 (offs st.pool n.args[kk.toNat]) + 1#32 =
      BitVec.ofNat 32 (offs st.pool n.args[kk.toNat] + 1) :=
    bv_add_one_ofNat (bv_toNat_ofNat (by omega)) (by omega)
  apply WP.assign_seq
  cases hμA : μ A with
  | none =>
    rw [encM, hμA] at hmark
    have hmark' : c3.pool[c1.k.plen.toNat + A]? = some (.u32 0#32) := hmark
    ck_simp [genv, hpool3, h.rd_pool hpool3, hidx3, rd_u32 hmark']
    apply WP.seq
    apply WP.ite
    ck_simp
    apply WP.ck_store .pool h (by rfl) hpool3
    ck_simp [genv, hpool3, hidx3, hpa1]
    refine ⟨U_lt_size hmark, fun s' h' => ?_⟩
    apply WP.assign
    ck_simp [genv]
    have hfr := hA.fresh hK hargl (by rw [hAw]; exact hAq') (by rw [hAw]; exact hfa')
      (by have := hF.arena.inside; omega) (by rw [hAw]; exact hμA)
    rw [hAw] at hfr
    refine ⟨_, kk + 1#32, 0#32, BitVec.ofNat 32 A, BitVec.ofNat 32 (offs st.pool n.args[kk.toNat]),
      updF μ A n.args[kk.toNat], rfl, by omega, h', ht.trans (TailEq.wr (by rw [hk]; omega)), ?_⟩
    rw [hk1]; exact hfr
  | some j =>
    rw [encM, hμA] at hmark
    obtain ⟨-, hj, -⟩ := hA.sw.mdom A j hμA
    have hjoff := hc1.off_lt hj
    have hmark' : c3.pool[c1.k.plen.toNat + A]? =
        some (.u32 (BitVec.ofNat 32 (offs st.pool j + 1))) := hmark
    ck_simp [genv, hpool3, h.rd_pool hpool3, hidx3, rd_u32 hmark']
    have hne : BitVec.ofNat 32 (offs st.pool j + 1) ≠ 0#32 := by
      intro e; have := congrArg BitVec.toNat e; rw [bv_toNat_ofNat (by omega)] at this; simp at this
    apply WP.seq
    apply WP.ite
    ck_simp [hne]
    apply WP.ite
    ck_simp [hpa1]
    refine ⟨fun _ => ?_, fun heq => ?_⟩
    · apply WP.ret
      ck_simp
      exact hQr _ _ c3 h ht
    apply WP.skip
    apply WP.assign
    ck_simp [genv]
    have hjeq : j = n.args[kk.toNat] := by
      have := congrArg BitVec.toNat heq
      rw [bv_toNat_ofNat (by omega), bv_toNat_ofNat (by omega)] at this
      exact offs_inj (Nat.le_of_lt hj) (Nat.le_of_lt hargl) (by omega)
    subst hjeq
    have hsm := hA.same hK (by rw [hAw]; exact hAq') (by rw [hAw]; exact hμA)
    refine ⟨c3, kk + 1#32, BitVec.ofNat 32 (offs st.pool n.args[kk.toNat] + 1), BitVec.ofNat 32 A,
      BitVec.ofNat 32 (offs st.pool n.args[kk.toNat]), μ, rfl, by omega, h, ht, ?_⟩
    rw [hk1]; exact hsm

end
end Vbcf.Proof
