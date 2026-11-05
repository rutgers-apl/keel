import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Goal3

namespace Vbcf.Proof

variable {State : Type}
open Bcf EmbC Vbcf
set_option autoImplicit false

section
variable {W : World} {sb gb pb : Nat} {c1 : CMem} {X : Ctx} {st : St} {gws : Array (BitVec 32)}
  {goal nv sbv : BitVec 32}

theorem goal_var_wp (hF : GFacts W sb gb pb c1 X st gws goal nv sbv) {Q : (Post prog State)}
    (hQn : ∀ env' s', MInv W sb gb c1 X st gws goal nv sbv env' s' → Q .normal env' s')
    (hQr : ∀ env' s' c2, Holds W s'.mem sb c2 → TailEq c1 c2 →
      Q (.ret (some (.u32 0#32))) env' s')
    {s : (KernelState prog State)} {c2 : CMem} {μ σP : Nat → Option Nat} {i : Nat} {n : Node}
    {q m ci ah ph code vlen k a pa pv : BitVec 32}
    (h : Holds W s.mem sb c2) (ht : TailEq c1 c2)
    (hsw : SweepOK st.pool gws X.posOf X.goal c1.k.plen.toNat goal.toNat c1.k.nexpr.toNat c2.pool
      μ σP (q.toNat + 1))
    (hm : μ q.toNat = some i) (hn : st.pool[i]? = some n)
    (hv : opC n.op = 0x18 ∨ opC n.op = 0x19)
    (hci : ci.toNat = offs st.pool i) (hah : ah = gws[q.toNat]!)
    (hph : ph = BitVec.ofNat 32 (hdrW n)) :
    WP Vbcf.prog [cstms|
        if (ah != (ph & 0xffff00ff)) { return 0; }
        pv = st->pool[ci + 1];
        if (pv >= st->nexpr) { return 0; }
        if (st->pool[sbase + pv] != 0) { return 0; }
        st->pool[sbase + pv] = q + 1;]
      Q (genv sb gb goal nv c1.k.plen sbv nv q m ci ah ph code vlen k a pa pv 1#32) s := by
  have hs := prog_ck
  have hk := ht.k
  have hc2 := hF.core.tailEq ht
  have hf := hc2.rep.fits i n hn
  have hlt := hdrW_lt hf
  have hpool2 : c2.k.pool = some (pb, 0) := by rw [hk]; exact hF.pool
  have hQ := (hsw.mdom _ _ hm).1
  have hpc := hF.core.poolCap
  have hroom := hF.room
  have hnv := hF.nv
  have hsbv := hF.sbv
  simp only [maxPool] at hpc
  subst hah hph
  simp only [Stmt.block]
  apply WP.ifRet
  ck_simp [genv]
  refine ⟨fun _ => hQr _ _ c2 h ht, fun heq => ?_⟩
  have hw : wordFn gws q.toNat = hdrW n % 256 + hdrW n / 65536 * 65536 := by
    have := congrArg BitVec.toNat heq
    rw [goal_bv_varmask, bv_toNat_ofNat hlt] at this
    exact this
  -- pv = st->pool[ci + 1];
  have htl : (tailW X.posOf (offs st.pool) n)[0]? = some (X.posOf (gvid n.op)) := by
    rw [var_tailW hv]; rfl
  have hpvc := hc2.rep.tail hn htl
  have hpvlt : X.posOf (gvid n.op) < 2 ^ 32 := hf.tail _ (by rw [var_tailW hv]; simp)
  have hci1 : (ci + 1#32).toNat = offs st.pool i + 1 + 0 := by
    have := hc2.off_lt (lt_size_of_getElem? hn)
    rw [bv_add_toNat] <;> simp <;> omega
  apply WP.assign_seq
  ck_simp [hpool2, h.rd_pool hpool2, hci1, rd_u32 hpvc]
  generalize hp : X.posOf (gvid n.op) = p at hpvlt
  -- if (pv >= st->nexpr) return 0;
  apply WP.ifRet
  ck_simp [hk]
  refine ⟨fun _ => hQr _ _ c2 h ht, fun hpl => ?_⟩
  have hpl' : p < c1.k.nexpr.toNat := by
    rw [BitVec.lt_def, bv_toNat_ofNat hpvlt] at hpl; omega
  -- if (st->pool[sbase + pv] != 0) return 0;
  have hsi : (sbv + BitVec.ofNat 32 p).toNat = c1.k.plen.toNat + goal.toNat + 1 + p := by
    rw [bv_add_toNat] <;> rw [bv_toNat_ofNat hpvlt] <;> omega
  have hvc := hsw.vmap p hpl'
  apply WP.ifRet
  cases hsp : σP p with
  | some t =>
    have ht' := hsw.sdom p t hsp
    rw [encS, hsp] at hvc
    have hvc' : c2.pool[c1.k.plen.toNat + goal.toNat + 1 + p]? = some (.u32 (BitVec.ofNat 32 (t + 1))) := hvc
    ck_simp [hpool2, h.rd_pool hpool2, hsi, rd_u32 hvc']
    refine ⟨fun _ => hQr _ _ c2 h ht, fun e => ?_⟩
    have := congrArg BitVec.toNat e
    rw [bv_toNat_ofNat (by omega)] at this; simp at this
  | none =>
    rw [encS, hsp] at hvc
    have hvc' : c2.pool[c1.k.plen.toNat + goal.toNat + 1 + p]? = some (.u32 0#32) := hvc
    ck_simp [hpool2, h.rd_pool hpool2, hsi, rd_u32 hvc']
    have hq1 : q + 1#32 = BitVec.ofNat 32 (q.toNat + 1) := bv_add_one_ofNat rfl (by omega)
    apply WP.ck_store .pool h (by rfl) hpool2
    ck_simp [hpool2, hsi, hq1]
    refine ⟨U_lt_size (hsw.vmap p hpl'), fun s' h' => hQn _ _ ⟨_, q, m, ci, gws[q.toNat]!,
      BitVec.ofNat 32 (hdrW n), code, vlen, k, a, pa, BitVec.ofNat 32 p, μ, updF σP p q.toNat, rfl,
      by omega, h', ht.trans (TailEq.wr (by rw [hk]; omega)), ?_⟩⟩
    exact hsw.var hm hn hf hv (hc2.args_nil hn (var_isLeaf hv)) hw hp hpl' hsp

end
end Vbcf.Proof

namespace Vbcf.Proof

variable {State : Type}
open Bcf EmbC Vbcf

theorem val_tailW {posOf off off' : Nat → Nat} {n : Node} (hv : opC n.op = 0x08) :
    tailW posOf off n = tailW posOf off' n := by
  rcases n with ⟨op, args⟩
  obtain ⟨w, v, e⟩ := opC_bvVal_iff.mp hv
  simp only at e; subst e; rfl

/-- Invariant of the literal comparison loop. -/
def GVInv (sb gb : Nat) (s0 : (KernelState prog State)) (posOf : Nat → Nat) (pool : Pool) (gws : Array (BitVec 32))
    (n : Node) (goal nv base sbv q m ci ah ph code vlen a pa pv : BitVec 32) : Env → (KernelState prog State) → Prop :=
  fun env s => s = s0 ∧ ∃ k : BitVec 32,
    env = genv sb gb goal nv base sbv nv q m ci ah ph code vlen k a pa pv 1#32 ∧
    k.toNat ≤ vlen.toNat ∧
    ∀ k', k' < k.toNat → (tailW posOf (offs pool) n)[k']? = some (wordFn gws (q.toNat + 1 + k'))

section
variable {W : World} {sb gb pb : Nat} {c1 : CMem} {X : Ctx} {st : St} {gws : Array (BitVec 32)}
  {goal nv sbv : BitVec 32}

theorem goal_val_wp (hF : GFacts W sb gb pb c1 X st gws goal nv sbv) {Q : (Post prog State)}
    (hQn : ∀ env' s', MInv W sb gb c1 X st gws goal nv sbv env' s' → Q .normal env' s')
    (hQr : ∀ env' s' c2, Holds W s'.mem sb c2 → TailEq c1 c2 →
      Q (.ret (some (.u32 0#32))) env' s')
    {s : (KernelState prog State)} {c2 : CMem} {μ σP : Nat → Option Nat} {i : Nat} {n : Node}
    {q m ci ah ph code vlen a pa pv : BitVec 32}
    (h : Holds W s.mem sb c2) (ht : TailEq c1 c2)
    (hsw : SweepOK st.pool gws X.posOf X.goal c1.k.plen.toNat goal.toNat c1.k.nexpr.toNat c2.pool
      μ σP (q.toNat + 1))
    (hm : μ q.toNat = some i) (hn : st.pool[i]? = some n) (hv : opC n.op = 0x08)
    (hci : ci.toNat = offs st.pool i) (hw : wordFn gws q.toNat = hdrW n)
    (hvlen : vlen.toNat = tailLen n) :
    WP Vbcf.prog [cstms|
        while (k < vlen) {
          if (gx[q + 1 + k] != st->pool[ci + 1 + k]) { return 0; }
          k = k + 1;
        }]
      Q (genv sb gb goal nv c1.k.plen sbv nv q m ci ah ph code vlen 0#32 a pa pv 1#32) s := by
  have hs := prog_ck
  have hk := ht.k
  have hc2 := hF.core.tailEq ht
  have hf := hc2.rep.fits i n hn
  have hpool2 : c2.k.pool = some (pb, 0) := by rw [hk]; exact hF.pool
  obtain ⟨hQ, -, hfit⟩ := hsw.mdom _ _ hm
  have hvl : hdrVlen (wordFn gws q.toNat) = vlen.toNat := by
    rw [hw, hvlen]; exact hdrW_len hf
  have hG : goal.toNat + 1 ≤ 2 ^ 30 := by
    have := hF.room; have := hF.nv; have := hF.core.poolCap; simp only [maxPool] at *; omega
  have hns : nodeSize n = 1 + tailLen n := rfl
  have hoff := hc2.off_lt (lt_size_of_getElem? hn)
  have hend := hc2.node_end_lt hn
  have harr := h.arena hF.arena
  have hargs : n.args = #[] := hc2.args_nil hn (by
    obtain ⟨_, _, e⟩ := opC_bvVal_iff.mp hv; rw [e]; rfl)
  obtain ⟨argTys, t, -, hty, -, -⟩ := hc2.ok.retype hn
  simp only [Stmt.block]
  apply WP.while (GVInv sb gb s X.posOf st.pool gws n goal nv c1.k.plen sbv q m ci ah ph code vlen a pa pv)
  · exact ⟨rfl, 0#32, rfl, by simp, fun k' hk' => by simp at hk'⟩
  rintro env s' ⟨rfl, kk, rfl, hkle, hpre⟩
  ck_simp [genv]
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · have hkv : kk.toNat = vlen.toNat := by rw [BitVec.le_def] at hge; omega
    refine hQn _ _ ⟨c2, q, m, ci, ah, ph, code, vlen, kk, a, pa, pv, μ, σP, rfl, by omega, h, ht,
      hsw.step hm (glocal_val hn hf hty hv hargs hw (fun k' hk' => hpre k' (by omega)))⟩
  have hK : kk.toNat < vlen.toNat := by rw [BitVec.lt_def] at hlt; omega
  have hlen : kk.toNat < (tailW X.posOf (offs st.pool) n).length := by
    rw [tailW_length]; omega
  have htw : (tailW X.posOf (offs st.pool) n)[kk.toNat]? =
      some (tailW X.posOf (offs st.pool) n)[kk.toNat] := List.getElem?_eq_getElem hlen
  generalize (tailW X.posOf (offs st.pool) n)[kk.toNat] = tw at htw
  have htwlt : tw < 2 ^ 32 := by
    apply hf.tail
    rw [val_tailW (off' := offs st.pool) hv]
    exact List.mem_of_getElem? htw
  have hcell := hc2.rep.tail hn htw
  have hidx1 : (q + 1#32 + kk).toNat = q.toNat + 1 + kk.toNat := by
    rw [bv_add_toNat, bv_add_toNat] <;> simp <;> omega
  have hidx2 : (ci + 1#32 + kk).toNat = offs st.pool i + 1 + kk.toNat := by
    rw [bv_add_toNat, bv_add_toNat] <;> simp <;> omega
  have hgx := arena_cell (gws := gws) (i := q.toNat + 1 + kk.toNat) (by omega)
  apply WP.ifRet
  ck_simp [genv, hpool2, h.rd_pool hpool2, harr.loadArr, hidx1, hidx2, rd_u32 hgx, rd_u32 hcell]
  refine ⟨fun _ => hQr _ _ c2 h ht, fun heq => ?_⟩
  have hweq : wordFn gws (q.toNat + 1 + kk.toNat) = tw := by
    have := congrArg BitVec.toNat heq
    rw [bv_toNat_ofNat htwlt] at this; exact this
  apply WP.assign
  ck_simp [genv]
  have hk1 : (kk + 1#32).toNat = kk.toNat + 1 := by
    rw [bv_add_toNat] <;> simp <;> omega
  refine ⟨rfl, kk + 1#32, rfl, by omega, fun k' hk' => ?_⟩
  rcases Nat.lt_or_ge k' kk.toNat with e | e
  · exact hpre k' e
  · have : k' = kk.toNat := by omega
    subst this; rw [htw, hweq]

end
end Vbcf.Proof
