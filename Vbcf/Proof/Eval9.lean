import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Eval6
import Vbcf.Proof.Eval8

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

theorem cv_hdr_code (n : Node) :
    BitVec.ofNat 32 (hdrW n) &&& 255#32 = BitVec.ofNat 32 (opC n.op) := by
  have h1 := opC_lt n.op
  rw [hdr_code_eq n _ (by omega)]

theorem cv_hdr_par {posOf : Nat → Nat} {n : Node} (hf : Fits posOf n) :
    BitVec.ofNat 32 (hdrW n) >>> 16 = BitVec.ofNat 32 (opLo n.op + opHi n.op * 256) := by
  have := hdrW_lt hf; have := hf.lo; have := hf.hi
  apply BitVec.eq_of_toNat_eq
  rw [bv_shr_16, bv_toNat_ofNat (by omega), bv_toNat_ofNat (by omega), hdrW_params hf]

theorem cv_par_lo {posOf : Nat → Nat} {n : Node} (hf : Fits posOf n) :
    BitVec.ofNat 32 (opLo n.op + opHi n.op * 256) &&& 255#32 = BitVec.ofNat 32 (opLo n.op) := by
  have := hf.lo; have := hf.hi
  apply BitVec.eq_of_toNat_eq
  rw [bv_and_ff, bv_toNat_ofNat (by omega), bv_toNat_ofNat (by omega)]; omega

theorem cv_par_hi {posOf : Nat → Nat} {n : Node} (hf : Fits posOf n) :
    BitVec.ofNat 32 (opLo n.op + opHi n.op * 256) >>> 8 = BitVec.ofNat 32 (opHi n.op) := by
  have := hf.lo; have := hf.hi
  apply BitVec.eq_of_toNat_eq
  rw [bv_shr_8, bv_toNat_ofNat (by omega), bv_toNat_ofNat (by omega)]; omega

theorem CvQ.wev {W : World} {sb : Nat} {c : CMem} {st : VSt} {i : Nat} {Q : (Post prog State)}
    (hQ : CvQ W sb c st i Q) (a b : BitVec 32) (x : BitVec 64) : CvQ W sb (c.wev a b x) st i Q :=
  fun r wk er vl env s' h hv => hQ r wk er vl env s' h hv

theorem cv_split64 {v : Nat} (hv : v < 2 ^ 64) :
    (BitVec.ofNat 64 (v % 4294967296) ||| BitVec.setWidth 64 (BitVec.ofNat 32 (v / 4294967296)) <<< 32).toNat
      = v := by
  have h1 : v / 4294967296 < 2 ^ 32 := by omega
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : v % 4294967296 < 2 ^ 64),
    Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt (by omega : v / 4294967296 < 2 ^ 64), Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega : v / 4294967296 * 2 ^ 32 < 2 ^ 64), Nat.or_comm,
    ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt (by omega : v % 4294967296 < 2 ^ 32),
    Nat.shiftLeft_eq]
  omega

theorem cv_leaf_args {st : St} (hok : PoolOK st) {i : Nat} {n : Node}
    (hn : st.pool[i]? = some n) (hl : IsLeaf n.op) : n.args = #[] := by
  obtain ⟨argTys, t, -, hrt, -, hlen⟩ := hok.retype hn
  have := resultTy_leaf hl hrt
  subst this
  simp at hlen
  exact Array.eq_empty_of_size_eq_zero hlen.symm

theorem cv_opTy_not_list {op : Op} (h : ∀ e, op ≠ .listVal e) (k : Nat) (e : Bool) (k' : Nat) :
    opTy op k ≠ .list e k' := by
  unfold opTy
  split
  · simp
  · split
    · rename_i e' _; exact absurd rfl (h e')
    · simp
    · simp
    · simp

set_option maxHeartbeats 2000000 in
theorem cvT2_spec {d : BitVec 32} (IH : ∀ d' : BitVec 32, d'.toNat < d.toNat → CvalSpecD (State := State) d')
    (hd : d ≠ 0#32) {W : World} {sb : Nat} {c : CMem} {posOf : Nat → Nat} {st : VSt} {i : Nat}
    {n : Node} {t : Bcf.Ty} {w cw : BitVec 32} {s : (KernelState prog State)} {Q : (Post prog State)} {pb : Nat}
    (h : Holds W s.mem sb c) (hc : VInv posOf c st) (hpool : c.k.pool = some (pb, 0))
    (hn : st.pool[i]? = some n) (hf : Fits posOf n) (hl : ¬ IsLeaf n.op)
    (hlist : ∀ e, n.op ≠ .listVal e) (ht : st.tys[i]? = some t) (hw : CvW t w)
    (hQ : CvQ W sb c st i Q) (h_lv : st.lv i := by vlv) :
    WP Vbcf.prog cvT2 Q
      (cvEnv sb (BitVec.ofNat 32 (st.id i)) d (BitVec.ofNat 32 (hdrW n))
        (BitVec.ofNat 32 (opC n.op)) (BitVec.ofNat 32 (tailLen n))
        (BitVec.ofNat 32 (opLo n.op + opHi n.op * 256)) (BitVec.ofNat 32 (opLo n.op))
        (BitVec.ofNat 32 (opHi n.op)) w cw 0#32 0#64 0#64 0#64 (mW w) 0#64 0#64) s := by
  have hi := h_lv
  have hs := prog_ck
  simp only [cvT2, Stmt.block]
  apply WP.ite_seq; cv_simp
  refine ⟨fun hsz => ?_, fun hsz => ?_⟩
  · obtain ⟨w', hw'⟩ := opC_bvSize_iff.mp hsz
    obtain ⟨a, rfl, ha⟩ := hc.args1 hn hw'
    obtain ⟨na, hna⟩ := node_of_lv ha
    obtain ⟨ta, hta, htya, hfita⟩ := hc.tyOf hna
    have hrd := hc.rd1 hn (by simp [IsLeaf, isLeaf])
    obtain ⟨argTys, t', hmap, hrt, ht', -⟩ := hc.ok.retype hn
    rw [ht] at ht'; cases ht'
    simp [mapOpt, hta] at hmap; subst hmap
    cases ta with
    | bv k =>
      simp [Op.resultTy, bvSizeTy, tyGuard] at hrt
      obtain ⟨⟨hw0, hk⟩, rfl⟩ := hrt
      obtain ⟨hw1, hw64, rfl⟩ := hw.bv
      have hm := cv_memoVal_bvSize hn hta
      apply WP.rule_ty_of ty_of_spec
      cv_simp [hrd, hc.rdHdr hna, htya]
      apply WP.seq; apply WP.ck_setVal hs h rfl; cv_simp
      intro s' h'
      apply WP.ret; cv_simp [LoopQ]
      refine hQ _ _ _ _ _ _ h' (fun _ _ => ⟨_, hm, ?_⟩)
      have hk2 : k ≤ 256 := hfita.2
      simp only [Op.eval, bvSizeEval, CvRep, ne_eq, hw0, not_false_eq_true, hk, and_self, ↓reduceIte]
      refine ⟨bv_toNat_ofNat (by omega), hw1, hw64, ?_⟩
      simp [Nat.mod_eq_of_lt hk]
      omega
    | bool => simp [Op.resultTy, bvSizeTy] at hrt
    | list e k' => simp [Op.resultTy, bvSizeTy] at hrt
  apply WP.ite_seq; cv_simp
  refine ⟨fun hop => ?_, fun _ => ?_⟩
  · exact grpU_spec IH hd h hc hpool hn hop ht hw hQ.loopQ
  intros
  apply WP.ite_seq; cv_simp
  refine ⟨fun hop => ?_, fun _ => ?_⟩
  · exact grpB_spec IH hd h hc hpool hn hop ht hw hQ.loopQ
  intros
  apply WP.ite_seq; cv_simp
  refine ⟨fun hop => ?_, fun _ => ?_⟩
  · have hop' : n.op = .boolIte ∨ ∃ k, n.op = .bvIte k := by
      by_cases h40 : opC n.op = 40
      · exact Or.inr (opC_bvIte_iff.mp h40)
      · exact Or.inl (opC_boolIte_iff.mp (hop h40))
    exact grpI_spec IH hd h hc hpool hn hop' ht hw hQ.loopQ
  intros
  apply WP.ite_seq; cv_simp
  refine ⟨fun hop => ?_, fun _ => ?_⟩
  · exact grpN_spec IH hd h hc hpool hn hop ht hw hQ.loopQ
  intros
  apply WP.ret; cv_simp [LoopQ]
  exact hQ _ _ _ _ _ _ h (fun _ h0 => absurd rfl h0)

/-- The rest of `cval` after the type word has been computed. -/
theorem cvT_spec {d : BitVec 32} (IH : ∀ d' : BitVec 32, d'.toNat < d.toNat → CvalSpecD (State := State) d')
    (hd : d ≠ 0#32) {W : World} {sb : Nat} {c : CMem} {posOf : Nat → Nat} {st : VSt} {i : Nat}
    {n : Node} {t : Bcf.Ty} {w cw : BitVec 32} {s : (KernelState prog State)} {Q : (Post prog State)} {pb : Nat}
    (h : Holds W s.mem sb c) (hc : VInv posOf c st) (hpool : c.k.pool = some (pb, 0))
    (hn : st.pool[i]? = some n) (hf : Fits posOf n) (hl : ¬ IsLeaf n.op)
    (hlist : ∀ e, n.op ≠ .listVal e) (ht : st.tys[i]? = some t) (hw : CvW t w)
    (hQ : CvQ W sb c st i Q) (h_lv : st.lv i := by vlv) :
    WP Vbcf.prog cvT Q
      (cvEnv sb (BitVec.ofNat 32 (st.id i)) d (BitVec.ofNat 32 (hdrW n))
        (BitVec.ofNat 32 (opC n.op)) (BitVec.ofNat 32 (tailLen n))
        (BitVec.ofNat 32 (opLo n.op + opHi n.op * 256)) (BitVec.ofNat 32 (opLo n.op))
        (BitVec.ofNat 32 (opHi n.op)) w cw 0#32 0#64 0#64 0#64 0#64 0#64 0#64) s := by
  have hlv_i := h_lv
  have hs := prog_ck
  simp only [cvT, Stmt.block]
  apply WP.assign_seq; cv_simp
  rcases hw with ⟨rfl, rfl⟩ | ⟨k, rfl, hk1, hk64, rfl⟩
  · apply WP.ite_seq; cv_simp
    have := cvT2_spec IH hd h hc hpool hn hf hl hlist ht (Or.inl ⟨rfl, rfl⟩) hQ (cw := cw)
    rw [mW_bool] at this
    exact this
  · apply WP.ite_seq; cv_simp
    refine ⟨fun _ => ?_, fun h' => absurd hk64 (by omega)⟩
    apply WP.call (mask64_spec (BitVec.ofNat 32 k)); cv_simp [LoopQ]
    have := cvT2_spec IH hd h hc hpool hn hf hl hlist ht (Or.inr ⟨k, rfl, hk1, hk64, rfl⟩) hQ (cw := cw)
    rw [mW_bv hk64] at this
    exact this

theorem cval_specD (d : BitVec 32) (IH : ∀ d' : BitVec 32, d'.toNat < d.toNat → CvalSpecD (State := State) d') :
    CvalSpecD (State := State) d := by
  intro W sb c posOf st i
  have hs := prog_ck
  apply FnSpec.intro' (fn := cval) rfl
  rintro vs s ⟨rfl, h, hc, hi⟩
  obtain ⟨n, hn⟩ := node_of_lv hi
  obtain ⟨pb, hpool⟩ := hc.poolPtr_of_node h hi
  have hf := hc.rep.fits i n hn
  simp [cval, bindParams, Mem.hasTy_ptr h.ck rfl]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  have hQ : CvQ (State := State) W sb c st i (retPost (some Ty.u32) (CvalPost W sb c st i)) :=
    fun r wk er vl _ s' h hv => ⟨rfl, r, wk, er, vl, rfl, h, hv⟩
  apply WP.ite_seq; cv_simp
  refine ⟨fun hd => ?_, fun hd => ?_⟩
  · apply WP.ret; cv_simp [LoopQ]
    exact hQ _ c.k.work c.k.err c.k.val [] s (by rw [wev_self]; exact h) (fun _ h => absurd rfl h)
  apply WP.call_seq (tick_spec W sb c) (by cv_simp) ⟨rfl, h⟩
  rintro rv s1 ⟨rfl, h1⟩
  rw [tickM_wev] at h1
  cv_simp
  apply WP.ite_seq; cv_simp
  refine ⟨fun hw0 => ?_, fun hw0 => ?_⟩
  · apply WP.ret; cv_simp [LoopQ]
    exact hQ _ _ _ _ [] s1 h1 (fun _ h => absurd rfl h)
  replace h := h1
  apply WP.assign_seq; cv_simp [hc.rdHdr hn]
  apply WP.assign_seq; cv_simp [cv_hdr_code]
  apply WP.assign_seq; cv_simp [hdr_len_bv hf]
  apply WP.assign_seq; cv_simp [cv_hdr_par hf]
  apply WP.assign_seq; cv_simp [cv_par_lo hf]
  apply WP.assign_seq; cv_simp [cv_par_hi hf]
  apply WP.ite_seq; cv_simp
  refine ⟨fun _ => ?_, fun hnv hnv' => ?_⟩
  · apply WP.ret; cv_simp [LoopQ]
    exact hQ _ _ _ _ _ _ h (fun h0 => absurd rfl h0)
  apply WP.ite_seq; cv_simp
  refine ⟨fun hb => ?_, fun hnb => ?_⟩
  · obtain ⟨b, hb'⟩ := opC_boolVal_iff.mp hb
    have hargs := cv_leaf_args hc.ok hn (by rw [hb']; simp [IsLeaf, isLeaf])
    have hm : memoVal st i = some (.bool b) := by
      rw [cv_memoVal_args hc.ok.tys hn (by simp [hb']) (by simp [hb']) (by simp [hb'])]
      simp [hargs, hb', mapOpt, Op.eval, boolConstEval]
    apply WP.seq; apply WP.ck_setVal hs h rfl; cv_simp [hb', opLo, opHi]
    intro s' h'
    apply WP.ret; cv_simp [LoopQ]
    exact hQ _ _ _ _ _ _ h' (fun _ _ => ⟨_, hm, by cases b <;> simp [CvRep] <;> decide⟩)
  apply WP.ite_seq; cv_simp
  refine ⟨fun hb => ?_, fun hnbv => ?_⟩
  · obtain ⟨w, v, hb'⟩ := opC_bvVal_iff.mp hb
    have hargs := cv_leaf_args hc.ok hn (by rw [hb']; simp [IsLeaf, isLeaf])
    obtain ⟨argTys, t, -, hrt, -, -⟩ := hc.ok.retype hn
    rw [hb'] at hrt
    obtain ⟨hw0, hw64, hv⟩ := resultTy_bvVal hrt
    have hm : memoVal st i = some (.bv w (BitVec.ofNat w v)) := by
      rw [cv_memoVal_args hc.ok.tys hn (by simp [hb']) (by simp [hb']) (by simp [hb'])]
      simp [hargs, hb', mapOpt, Op.eval, bvValEval, hw0, hw64, hv]
    have hc1 := hc.rep.tail hn (k := 0) (w := v % 2 ^ 32) (by simp [tailW, hb']; split <;> simp)
    apply WP.assign_seq; cv_simp [rd_u32 hc1]
    have hfin : ∀ (I : Env → (KernelState prog State) → Prop) (x : BitVec 64), x.toNat = v → ∀ env s',
        env.get "lo" = some (.u32 (BitVec.ofNat 32 w)) →
        Holds W s'.mem sb (c.wev (tickM c).snd.k.work (tickM c).snd.k.err x) →
        WP Vbcf.prog (.ret (some (.var "lo")))
          (LoopQ I (retPost (some Ty.u32) (CvalPost W sb c st i))) env s' := by
      intro I x hx env s' henv h'
      apply WP.ret; simp only [evalE, henv, LoopQ]
      refine hQ _ _ _ _ _ _ h' (fun _ _ => ⟨_, hm, ?_⟩)
      refine ⟨bv_toNat_ofNat (by omega), by omega, hw64, ?_⟩
      rw [hx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
    by_cases hw32 : w ≤ 32
    · have htl : tailLen n = 1 := by simp [tailLen, hb', hw32]
      apply WP.ite_seq; cv_simp [htl]
      apply WP.seq; apply WP.ck_setVal hs h rfl; cv_simp
      intro s' h'
      have hv32 : v < 2 ^ 32 := Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) hw32)
      exact hfin _ _ (by simp; omega) _ _ (by simp [Env.get, hb', opLo]) h'
    · have htl : tailLen n = 2 := by simp [tailLen, hb', hw32]
      have hc2 : U c.pool (st.id i + 2) (v / 2 ^ 32) := by
        have := hc.rep.tail hn (k := 1) (w := v / 2 ^ 32) (by simp [tailW, hb', hw32])
        rwa [Nat.add_assoc] at this
      apply WP.ite_seq; cv_simp [htl, rd_u32 hc2]
      apply WP.assign; cv_simp [LoopQ, rd_u32 hc2]
      apply WP.seq; apply WP.ck_setVal hs h rfl; cv_simp
      intro s' h'
      refine hfin _ _ ?_ _ _ (by simp [Env.get, hb', opLo]) h'
      exact cv_split64 (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) hw64))
  apply WP.ite_seq; cv_simp
  refine ⟨fun hb => ?_, fun hnl => ?_⟩
  · apply WP.ret; cv_simp [LoopQ]
    exact hQ _ _ _ _ _ _ h (fun _ h0 => absurd rfl h0)
  obtain ⟨t, ht, hty, hfit⟩ := hc.tyOf hn
  apply WP.rule_ty_of ty_of_spec
  cv_simp [hty]
  have hl : ¬ IsLeaf n.op := by
    rw [isLeaf_iff_opC]; omega
  have hlist : ∀ e, n.op ≠ .listVal e := by
    intro e he; rw [he] at hnl; exact hnl rfl
  obtain ⟨argTys, t', -, hrt, ht', -⟩ := hc.ok.retype hn
  rw [ht] at ht'; cases ht'
  have hto := resultTy_eq_opTy hrt
  cases t with
  | list e k => exact absurd hto.symm (cv_opTy_not_list hlist _ e k)
  | bool =>
    apply WP.ite_seq; cv_simp
    apply WP.ite_seq; cv_simp
    apply WP.assign; cv_simp [LoopQ]
    exact cvT_spec IH hd h hc.wev hpool hn hf hl hlist ht (Or.inl ⟨rfl, rfl⟩) (hQ.wev _ _ _)
  | bv k =>
    have hk : 1 ≤ k ∧ k ≤ 256 := hfit
    apply WP.ite_seq; cv_simp
    refine ⟨fun hk' hk'' => ?_, fun hk' => ?_⟩
    · apply WP.ret; cv_simp [LoopQ]
      exact hQ _ _ _ _ _ _ h (fun _ h0 => absurd rfl h0)
    have hk64 : k ≤ 64 := hk' (by omega)
    apply WP.ite_seq; cv_simp
    refine ⟨fun h4 => absurd h4 (by omega), fun _ => ?_⟩
    exact cvT_spec IH hd h hc.wev hpool hn hf hl hlist ht (Or.inr ⟨k, rfl, hk.1, hk64, rfl⟩)
      (hQ.wev _ _ _)

theorem cval_spec_aux : ∀ k (d : BitVec 32), d.toNat = k → CvalSpecD (State := State) d := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro d hd
    exact cval_specD d (fun d' hd' => ih d'.toNat (hd ▸ hd') d' rfl)

/-- **`cval` is the Lean constant evaluator `memoVal`** (on values of at most 64 bits). -/
theorem cval_spec : CvalSpec (State := State) := fun d => cval_spec_aux d.toNat d rfl

end Vbcf.Proof
