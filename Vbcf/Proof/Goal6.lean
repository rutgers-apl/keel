import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Goal5

/-!
# Vbcf proofs: `ck_goal`, part 6 (one position of the sweep)
-/

namespace Vbcf.Proof

variable {State : Type}
open Bcf EmbC Vbcf
set_option autoImplicit false

section
variable {W : World} {sb gb pb : Nat} {c1 : CMem} {X : Ctx} {st : St} {gws : Array (BitVec 32)}
  {goal nv sbv : BitVec 32}

theorem goal_body_wp (hF : GFacts W sb gb pb c1 X st gws goal nv sbv) {Q : (Post prog State)}
    (hQn : ∀ env' s', MInv W sb gb c1 X st gws goal nv sbv env' s' → Q .normal env' s')
    (hQr : ∀ env' s' c2, Holds W s'.mem sb c2 → TailEq c1 c2 →
      Q (.ret (some (.u32 0#32))) env' s')
    {s : (KernelState prog State)} {c2 : CMem} {μ σP : Nat → Option Nat}
    {q m ci ah ph code vlen k a pa pv : BitVec 32}
    (h : Holds W s.mem sb c2) (ht : TailEq c1 c2) (hq0 : 0 < q.toNat)
    (hqle : q.toNat ≤ goal.toNat + 1)
    (hsw : SweepOK st.pool gws X.posOf X.goal c1.k.plen.toNat goal.toNat c1.k.nexpr.toNat c2.pool
      μ σP q.toNat) :
    WP Vbcf.prog [cstms|
        q = q - 1;
        m = st->pool[base + q];
        if (m != 0) {
          ci = m - 1;
          ah = gx[q];
          ph = st->pool[ci];
          code = ph & 0xff;
          if (code == BV_VAR || code == BOOL_VAR) {
            if (ah != (ph & 0xffff00ff)) { return 0; }
            pv = st->pool[ci + 1];
            if (pv >= st->nexpr) { return 0; }
            if (st->pool[sbase + pv] != 0) { return 0; }
            st->pool[sbase + pv] = q + 1;
          } else {
            if (ah != ph) { return 0; }
            vlen = (ah >> 8) & 0xff;
            k = 0;
            if (code == BV_VAL) {
              while (k < vlen) {
                if (gx[q + 1 + k] != st->pool[ci + 1 + k]) { return 0; }
                k = k + 1;
              }
            } else {
              while (k < vlen) {
                a = gx[q + 1 + k];
                if (a >= q) { return 0; }
                if ((u64)a + 1ull + (u64)((gx[a] >> 8) & 0xff) > (u64)q) { return 0; }
                pa = st->pool[ci + 1 + k];
                m = st->pool[base + a];
                if (m == 0) { st->pool[base + a] = pa + 1; }
                else if (m != pa + 1) { return 0; }
                k = k + 1;
              }
            }
          }
        }]
      Q (genv sb gb goal nv c1.k.plen sbv nv q m ci ah ph code vlen k a pa pv 1#32) s := by
  have hs := prog_ck
  have hk := ht.k
  have hc2 := hF.core.tailEq ht
  have hpool2 : c2.k.pool = some (pb, 0) := by rw [hk]; exact hF.pool
  have harr := h.arena hF.arena
  have hG : goal.toNat + 1 ≤ 2 ^ 30 := by
    have := hF.room; have := hF.nv; have := hF.core.poolCap; simp only [maxPool] at *; omega
  have hpc := hF.core.poolCap
  simp only [maxPool] at hpc
  simp only [Stmt.block]
  -- q = q - 1;
  apply WP.assign_seq
  ck_simp [genv]
  have hq1 : (q - 1#32).toNat = q.toNat - 1 := by rw [bv_sub_toNat] <;> simp <;> omega
  obtain ⟨Q', hQ'⟩ : ∃ Q', q.toNat - 1 = Q' := ⟨_, rfl⟩
  rw [hQ'] at hq1
  have hsw' : SweepOK st.pool gws X.posOf X.goal c1.k.plen.toNat goal.toNat c1.k.nexpr.toNat
      c2.pool μ σP ((q - 1#32).toNat + 1) := by
    rw [hq1, show Q' + 1 = q.toNat by omega]; exact hsw
  -- m = st->pool[base + q];
  have hidx : (c1.k.plen + (q - 1#32)).toNat = c1.k.plen.toNat + Q' := by
    rw [bv_add_toNat] <;> rw [hq1] <;> omega
  have hmark := hsw.mark Q' (by omega)
  apply WP.assign_seq
  cases hμ : μ Q' with
  | none =>
    rw [encM, hμ] at hmark
    have hmark' : c2.pool[c1.k.plen.toNat + Q']? = some (.u32 0#32) := hmark
    ck_simp [genv, hpool2, h.rd_pool hpool2, hidx, rd_u32 hmark']
    apply WP.ite
    ck_simp
    apply WP.skip
    exact hQn _ _ ⟨c2, q - 1#32, 0#32, ci, ah, ph, code, vlen, k, a, pa, pv, μ, σP, rfl, by omega, h,
      ht, hsw'.skip (by rw [hq1]; exact hμ)⟩
  | some i =>
    rw [encM, hμ] at hmark
    have hmark' : c2.pool[c1.k.plen.toNat + Q']? =
        some (.u32 (BitVec.ofNat 32 (offs st.pool i + 1))) := hmark
    obtain ⟨hQG, hi, hfit⟩ := hsw.mdom Q' i hμ
    obtain ⟨n, hn⟩ := node_of_lt hi
    have hf := hc2.rep.fits i n hn
    have hoff := hc2.off_lt hi
    have hlt := hdrW_lt hf
    ck_simp [genv, hpool2, h.rd_pool hpool2, hidx, rd_u32 hmark']
    have hne : BitVec.ofNat 32 (offs st.pool i + 1) ≠ 0#32 := by
      intro e; have := congrArg BitVec.toNat e; rw [bv_toNat_ofNat (by omega)] at this; simp at this
    apply WP.ite
    ck_simp [hne]
    -- ci = m - 1; ah = gx[q]; ph = st->pool[ci]; code = ph & 0xff;
    have hci : BitVec.ofNat 32 (offs st.pool i + 1) - 1#32 = BitVec.ofNat 32 (offs st.pool i) := by
      apply BitVec.eq_of_toNat_eq
      rw [bv_sub_toNat] <;> simp <;> omega
    have hgx := arena_cell (gws := gws) (i := Q') (by omega)
    have hhdr := hc2.rep.hdr hn
    apply WP.assign_seq
    ck_simp [genv, hci]
    apply WP.assign_seq
    ck_simp [genv, harr.loadArr, hq1, rd_u32 hgx]
    apply WP.assign_seq
    ck_simp [genv, hpool2, h.rd_pool hpool2, bv_toNat_ofNat (show offs st.pool i < 2 ^ 32 by omega),
      rd_u32 hhdr]
    apply WP.assign_seq
    ck_simp [genv]
    apply WP.ite
    ck_simp [code_eq_iff hf]
    have hμ' : μ (q - 1#32).toNat = some i := by rw [hq1]; exact hμ
    have hci' : (BitVec.ofNat 32 (offs st.pool i)).toNat = offs st.pool i := bv_toNat_ofNat (by omega)
    have hah : gws[Q']! = gws[(q - 1#32).toNat]! := by rw [hq1]
    by_cases hv : opC n.op = 0x18 ∨ opC n.op = 0x19
    · have hv' : (if opC n.op = 24 then some (Val.u32 1#32)
          else some (Val.u32 (if opC n.op = 25 then 1#32 else 0#32))) = some (Val.u32 1#32) := by
        rcases hv with e | e <;> simp [e]
      rw [hv']
      refine ⟨fun _ => ?_, fun e => absurd e (by decide)⟩
      exact goal_var_wp hF hQn hQr h ht hsw' hμ' hn hv hci' hah rfl
    · have h18 : opC n.op ≠ 0x18 := fun e => hv (Or.inl e)
      have h19 : opC n.op ≠ 0x19 := fun e => hv (Or.inr e)
      have hv' : (if opC n.op = 24 then some (Val.u32 1#32)
          else some (Val.u32 (if opC n.op = 25 then 1#32 else 0#32))) = some (Val.u32 0#32) := by
        simp [h18, h19]
      rw [hv']
      refine ⟨fun e => absurd rfl e, fun _ => ?_⟩
      -- if (ah != ph) return 0;
      apply WP.ifRet
      ck_simp
      refine ⟨fun _ => hQr _ _ c2 h ht, fun heq => ?_⟩
      have hw : wordFn gws (q - 1#32).toNat = hdrW n := by
        rw [hq1]
        have := congrArg BitVec.toNat heq
        rw [bv_toNat_ofNat hlt] at this; exact this
      -- vlen = (ah >> 8) & 0xff; k = 0;
      apply WP.assign_seq
      ck_simp [genv, heq]
      apply WP.assign_seq
      ck_simp [genv]
      have hvl : ((BitVec.ofNat 32 (hdrW n) >>> 8) &&& 255#32).toNat = tailLen n := by
        rw [bv_and_ff, bv_shr_8, bv_toNat_ofNat hlt]; exact hdrW_len hf
      apply WP.ite
      ck_simp [code_eq_iff hf]
      by_cases h08 : opC n.op = 0x08
      · simp only [h08]
        refine ⟨fun _ => ?_, fun e => absurd e (by decide)⟩
        exact goal_val_wp hF hQn hQr h ht hsw' hμ' hn h08 hci' hw hvl
      · simp only [h08]
        refine ⟨fun e => e.elim, fun _ => ?_⟩
        have hvl' : ((BitVec.ofNat 32 (hdrW n) >>> 8) &&& 255#32).toNat = n.args.size := by
          rw [hvl]
          by_cases hl : IsLeaf n.op
          · rw [hc2.args_nil hn hl]
            rcases isLeaf_iff.mp hl with ⟨_, _, e⟩ | ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, e⟩ <;>
              simp [opC, tailLen, e] at h18 h19 h08 ⊢
          · exact tailLen_of_not_leaf hl
        exact goal_args_wp hF hQn hQr h ht hsw' hμ' hn h18 h19 h08 hci' hw hvl'

end
end Vbcf.Proof
