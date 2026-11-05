import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Compact12
import Vbcf.Proof.Load1

/-!
# Vbcf proofs: `ck_compact`, part 13 — the function

`ck_compact_spec : CkCompactSpec`, assembled from the loop lemmas of parts
5–12: pay, allocate the forwarding table, mark, slide, remap the facts, count
the nodes, size, reallocate and refill the table, free the forwarding table.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-- The checker state after the slide, against the state `c0` on entry. -/
structure CpMid (c0 c : CMem) (P : Array EmbC.Val) (plen : BitVec 32) : Prop where
  pool : c.pool = P
  facts : c.facts = c0.facts
  proof : c.proof = c0.proof
  prem : c.prem = c0.prem
  lr : c.lr = c0.lr
  kpool : c.k.pool = c0.k.pool
  kpcap : c.k.pcap = c0.k.pcap
  khtab : c.k.htab = c0.k.htab
  kfacts : c.k.facts = c0.k.facts
  kflen : c.k.flen = c0.k.flen
  kfcap : c.k.fcap = c0.k.fcap
  knexpr : c.k.nexpr = c0.k.nexpr
  kprem : c.k.prem = c0.k.prem
  kproof : c.k.proof = c0.k.proof
  ktt : c.k.tt = c0.k.tt
  kff : c.k.ff = c0.k.ff
  kgoal : c.k.goal = c0.k.goal
  klr : c.k.lr = c0.k.lr
  klo : c.k.lo = c0.k.lo
  kplen : c.k.plen = plen
  stk : StkOK c

set_option maxHeartbeats 4000000 in
theorem ck_compact_spec : CkCompactSpec (State := State) := by
  intro W sb c ws X st off rest
  have hs := prog_ck
  apply FnSpec.intro' (fn := ckCompact) rfl
  rintro vs s ⟨rfl, h, hS, hlo0⟩
  simp [ckCompact, bindParams, Mem.hasTy_ptr h.ck rfl]
  simp only [Stmt.block, initLocals, List.map, Ty.zero]
  show WP prog _ (retPost (some .u32) (CpPost W sb ws X st off rest)) _ s
  have hcore := hS.inv.core.cinv
  have hok := hcore.ok
  have hrep := hcore.rep
  have hnL := hS.nLcs
  have hlo := hS.lo
  have hplen := hrep.len
  have hP32 := c.k.plen.isLt
  -- lo = st->lo; plen = st->plen; n = plen - lo;
  apply WP.seq
  apply WP.assign
  ck_simp
  apply WP.seq
  apply WP.assign
  ck_simp
  apply WP.seq
  apply WP.assign
  ck_simp
  -- ok = spend(st, n + lo + st->flen); if (ok == 0) return 0;
  apply WP.seq
  apply WP.call (spend_spec W sb c (c.k.plen - c.k.lo + c.k.lo + c.k.flen))
  ck_simp
  refine ⟨h, ?_⟩
  rintro rv s1 rfl h1
  rw [spendM_wev] at h1
  have hsp1 := spendM_fst c (c.k.plen - c.k.lo + c.k.lo + c.k.flen)
  generalize (spendM c (c.k.plen - c.k.lo + c.k.lo + c.k.flen)).2.k.work = wk1 at h1
  generalize (spendM c (c.k.plen - c.k.lo + c.k.lo + c.k.flen)).2.k.err = er1 at h1
  generalize (spendM c (c.k.plen - c.k.lo + c.k.lo + c.k.flen)).1 = ok1 at hsp1 ⊢
  clear h
  have h := h1
  ck_simp
  apply WP.seq
  apply WP.ite
  ck_simp
  refine ⟨fun h0 => ?_, fun hne => ?_⟩
  · apply WP.ret
    ck_simp [retPost, CpPost]
    exact ⟨_, h⟩
  apply WP.skip
  -- if (st->mem < n) { st->err = ERR_LIMIT; return 0; }
  apply WP.seq
  apply WP.ite
  ck_simp
  refine ⟨fun hm => ?_, fun hm => ?_⟩
  · apply WP.seq
    apply WP.ck_setField hs h (by rfl)
    ck_simp
    intro s2 h2
    apply WP.ret
    ck_simp [retPost, CpPost]
    exact ⟨_, h2⟩
  apply WP.skip
  -- st->mem = st->mem - n;
  apply WP.seq
  apply WP.ck_setField hs h (by rfl)
  ck_simp
  intro s2 h2
  clear h
  have h := h2
  -- fw = kvcalloc((u64)n, sizeof(u32));
  have hN : (c.k.plen - c.k.lo).toNat = c.k.plen.toNat - c.k.lo.toNat := by
    rw [bv_sub_toNat (by omega)]
  have hn64 : (BitVec.setWidth 64 (c.k.plen - c.k.lo)).toNat = c.k.plen.toNat - c.k.lo.toNat := by
    simp only [BitVec.toNat_setWidth]; rw [hN]; omega
  have hn0 : BitVec.setWidth 64 (c.k.plen - c.k.lo) ≠ 0#64 := by
    intro e; have := congrArg BitVec.toNat e; rw [hn64] at this; simp at this; omega
  apply WP.seq
  apply WP.ecall
  ck_simp [kvcalloc_run hn0, hn64]
  by_cases horc : (callocResponse (P := Vbcf.prog) hn0 s2).1 ≠ some .null
  case neg =>
    -- out of memory
    simp only [ne_eq, Classical.not_not] at horc
    simp only [horc, ↓reduceIte]
    embc_simp
    apply WP.seq
    apply WP.ite
    embc_simp
    apply WP.seq
    apply WP.ck_setField hs h (by rfl)
    ck_simp
    intro s3 h3
    apply WP.ret
    ck_simp [retPost, CpPost]
    exact ⟨_, h3⟩
  simp only [ne_eq, Classical.not_not] at horc
  simp only [horc, ↓reduceIte]
  -- the forwarding table is block `fb`, held in the local `fw`
  obtain ⟨fb, hfb⟩ : ∃ fb, fb = s2.mem.blocks.size := ⟨_, rfl⟩
  have hW : W.aux fb = none := by rw [hfb]; exact h.aux_ge (Nat.le_refl _)
  have hA := h.allocAux (Array.replicate (c.k.plen.toNat - c.k.lo.toNat) (.u32 0#32))
  rw [← hfb] at hA
  have hfbA := hA.aux_arr
  have hfbB : (s2.mem.alloc Ty.u32 (Array.replicate (c.k.plen.toNat - c.k.lo.toNat) (Val.u32 0#32))).2.block? fb =
      some ⟨.u32, Array.replicate (c.k.plen.toNat - c.k.lo.toNat) (Val.u32 0#32)⟩ := hfbA
  rw [← hfb]
  embc_simp [Mem.hasTy_ptr hfbA rfl]
  apply WP.seq
  apply WP.ite
  embc_simp [hfbB]
  apply WP.skip
  clear h
  have h := hA
  -- st->sp = 0;
  apply WP.seq
  apply WP.ck_setField hs h (by rfl)
  ck_simp
  intro s3 h3
  clear h
  have h := h3
  -- the roots loop
  refine cp_roots hS hW ⟨_, _, 0#32, 0#32, ok1, rfl, h, ?_, by simp, fun j f hj => by simp at hj⟩ ?_
  · refine ⟨by constructor <;> rfl, ⟨hcore.stk.null, hcore.stk.size, by simp; exact hcore.stk.cap.2⟩,
      by simp [hplen, hlo], fun k hk => Or.inl ?_, fun p hp => by simp at hp, fun y _ _ hy => ?_⟩
    · unfold U; simp at hk ⊢; simp [hk]
    · exfalso
      unfold Mk U at hy
      rw [Array.getElem?_replicate] at hy
      split at hy <;> simp [noidN] at hy
  intro s4 c4 fw4 r4 ok4 h4 hM4 hR4
  -- the worklist loop
  refine cp_mark hS hW ⟨c4, fw4, r4, 0#32, 0#32, 0#32, 0#32, 0#32, 0#32, ok4, rfl, h4, hM4, hR4⟩ ?_
  intro s5 c5 fw5 r5 o5 hdr5 code5 ar5 i5 cc5 ok5 h5 hM5 hsp5 hR5
  -- what is kept
  obtain ⟨keep, hkeep⟩ : ∃ keep, keep = keepOf st.cs.pool X.nL fw5 := ⟨_, rfl⟩
  have hcl : KClosed keep st.cs.pool := by
    rw [hkeep]; exact hM5.closed hsp5 (fun i n hn => hok.args_lt hn)
  have hpre : ∀ y, y < X.nL → keep y = true := fun y hy => by rw [hkeep]; exact keepOf_low hy
  have hroot : ∀ j f, LiveFact c st j f → keep (st.σ f) = true := by
    intro j f hL
    rw [hkeep, keepOf_iff]
    rcases Nat.lt_or_ge (st.σ f) X.nL with hlt | hge
    · exact Or.inl hlt
    · right
      have hj : j < c.k.flen.toNat := by
        obtain ⟨hf, -⟩ := hL
        have := lt_size_of_getElem? hf
        rw [hS.flen]; exact this
      exact hR5 j f hj hL hge
  have hloB : c.k.lo = BitVec.ofNat 32 (offs st.cs.pool X.nL) := by
    apply BitVec.eq_of_toNat_eq; rw [hlo, bv_toNat_ofNat (by have := offs_le_end st.cs.pool X.nL; omega)]
  have hfr5 := hM5.fr
  -- cur = lo; o = lo;
  apply WP.seq
  apply WP.assign
  embc_simp [cpEnv]
  apply WP.seq
  apply WP.assign
  embc_simp
  -- the slide
  refine cp_slide (cm := c5) (n := c.k.plen - c.k.lo) (r := r5) (ok := ok5) hS hW hfr5 hcl hpre
    ⟨c5.pool, fw5, X.nL, hdr5, code5, ar5, i5, cc5, ?_, h5, Nat.le_refl _, hnL, ?_, ?_⟩ ?_
  · simp only [cpEnv, offK_pre hpre hnL X.nL (Nat.le_refl _), cntK_pre hpre X.nL (Nat.le_refl _),
      Nat.sub_self, ← hloB]
    rfl
  · refine ⟨by rw [hfr5.pool], fun k _ => by rw [hfr5.pool], fun y nd hy hky hnd => ?_⟩
    rw [hfr5.pool, offK_pre hpre hnL y (Nat.le_of_lt hy)]
    have hw := hrep.cell y nd hnd
    have : newW X.posOf keep st.cs.pool nd = nodeW X.posOf st.cs.pool nd := by
      simp only [newW, nodeW]
      congr 1
      apply tailW_congr
      intro a ha
      exact offK_pre hpre hnL a (by have := hok.args_lt hnd a ha; omega)
    rw [this]; exact hw
  · refine ⟨hM5.size, fun k hk => ?_, fun y hy hys => ?_⟩
    · rcases hM5.cells k hk with h0 | h1
      · exact ⟨0, by decide, h0⟩
      · exact ⟨noidN, by decide, h1⟩
    · have hny : ¬ y < X.nL := by omega
      by_cases hm : Mk st.cs.pool X.nL fw5 y
      · have hk : keep y = true := by rw [hkeep, keepOf_iff]; exact Or.inr hm
        simp only [hk, hny, ↓reduceIte]; exact hm
      · have hk : keep y = false := by
          rw [hkeep]
          cases e : keepOf st.cs.pool X.nL fw5 y
          · rfl
          · rw [keepOf_iff] at e; rcases e with e | e
            · exact absurd e hny
            · exact absurd e hm
        simp only [hk]
        have hk' : offs st.cs.pool y - offs st.cs.pool X.nL < fw5.size := by
          rw [hM5.size]; have := offs_lt_end hys; have := offs_le_of_le (pool := st.cs.pool) hy; omega
        rcases hM5.cells _ hk' with h0 | h1
        · exact h0
        · exact absurd h1 hm
  intro s6 P6 fw6 hdr6 code6 ar6 i6 cc6 h6 hC6 hF6
  have hsz := st.cs.pool.size
  have hoffK32 : offK keep st.cs.pool st.cs.pool.size < 2 ^ 32 := by
    have := offK_le_offs (keep := keep) (pool := st.cs.pool) st.cs.pool.size; omega
  -- st->plen = cur; st->live = cur - lo; j = 0;
  apply WP.seq
  apply WP.ck_setField hs h6 (by rfl)
  ck_simp [cpEnv]
  intro s7 h7
  apply WP.seq
  apply WP.ck_setField hs h7 (by rfl)
  ck_simp
  intro s8 h8
  apply WP.seq
  apply WP.assign
  embc_simp
  obtain ⟨c8, h8, hm8⟩ := Holds.named h8
    (P := fun c8 => CpMid c c8 P6 (BitVec.ofNat 32 (offK keep st.cs.pool st.cs.pool.size)))
    ⟨rfl, hfr5.facts, hfr5.proof, hfr5.prem, hfr5.lr, hfr5.poolPtr, hfr5.pcap, hfr5.htabPtr,
      hfr5.factsPtr, hfr5.flen, hfr5.fcap, hfr5.nexpr, hfr5.premPtr, hfr5.proofPtr, hfr5.tt, hfr5.ff,
      hfr5.goal, hfr5.lrPtr, hfr5.lo, rfl, ⟨hM5.stk.null, hM5.stk.size, hM5.stk.cap⟩⟩
  -- remap the facts
  refine cp_remap (n := c.k.plen - c.k.lo) (c1 := c8) hS hm8.kfacts hm8.kflen hpre hroot hF6
    ⟨c8.facts, 0#32, r5, hdr6, code6, ar6, i6, cc6, ok5, rfl, h8, by simp, by rw [hm8.facts],
      by rw [hm8.facts]; exact hS.factsCells,
      fun k _ => by rw [hm8.facts], fun k f hk => by simp at hk⟩ ?_
  intro s9 F9 r9 hdr9 code9 ar9 i9 cc9 ok9 h9 hFs9 hFc9 hFl9
  -- o = 0; count the nodes below `lo`
  have hcnt_ge : X.nL ≤ cntK keep st.cs.pool.size := by
    have := cntK_mono (keep := keep) hnL
    rw [cntK_pre hpre X.nL (Nat.le_refl _)] at this; exact this
  have hcnt_lt : cntK keep st.cs.pool.size < 2 ^ 32 := by
    have := cntK_le (keep := keep) st.cs.pool.size
    have := size_le_offs st.cs.pool
    omega
  apply WP.seq
  apply WP.assign
  embc_simp [cpEnv]
  refine cp_count (n := c.k.plen - c.k.lo) (base := cntK keep st.cs.pool.size - X.nL)
    (cur := BitVec.ofNat 32 (offK keep st.cs.pool st.cs.pool.size)) hS h9
    (by exact hm8.kpool) ?_ (by omega)
    ⟨rfl, 0, c.k.flen, r9, hdr9, code9, ar9, i9, cc9, ok9, by simp [cpEnv], Nat.zero_le _⟩ ?_
  · intro y nd hy hnd
    have hw := hC6.kept y nd (by omega) (hpre y hy) hnd
    have := hw 0 (hdrW nd) (by simp [newW])
    rw [Nat.add_zero, offK_pre hpre hnL y (Nat.le_of_lt hy)] at this
    show U c8.pool _ _
    rw [hm8.pool]; exact this
  intro j10 r10 hdr10 code10 ar10 i10 cc10 ok10
  rw [show cntK keep st.cs.pool.size - X.nL + X.nL = cntK keep st.cs.pool.size by omega]
  -- hc = 1024; size the table
  apply WP.seq
  apply WP.assign
  embc_simp [cpEnv]
  refine cp_grow (c0 := c) (n := c.k.plen - c.k.lo) (c := { c8 with facts := F9 }) (o := c.k.lo)
    (cur := BitVec.ofNat 32 (offK keep st.cs.pool st.cs.pool.size)) hW hcnt_lt
    ⟨_, _, j10, r10, hdr10, code10, ar10, i10, cc10, ok10, 0, by simp [cpEnv], by rw [wev_self]; exact h9,
      Or.inl rfl⟩ ?_
  intro s11 wk11 er11 j11 r11 hdr11 code11 ar11 i11 cc11 ok11 k11 h11 h4N hk11
  obtain ⟨N, hNdef⟩ : ∃ N, N = cntK keep st.cs.pool.size := ⟨_, rfl⟩
  rw [← hNdef] at h4N hk11 hcnt_lt hcnt_ge
  have hk35 : 10 + k11 < 35 := by
    rcases hk11 with e | e
    · omega
    · have : 2 ^ (10 + k11) < 2 ^ 35 := by omega
      exact (Nat.pow_lt_pow_iff_right (by decide)).mp this
  have hpow64 : 2 ^ (10 + k11) < 2 ^ 64 := by
    have := Nat.pow_lt_pow_right (a := 2) (by decide) hk35
    have : (2 : Nat) ^ 35 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by decide)
    omega
  have h1024 : 1024 ≤ 2 ^ (10 + k11) := by
    rw [Nat.pow_add]; have := Nat.one_le_two_pow (n := k11); omega
  -- if (hc > (u64)MAX_POOL) { st->err = ERR_LIMIT; kvfree(fw); return 0; }
  apply WP.seq
  apply WP.ite
  ck_simp [cpEnv, MAX_POOL]
  refine ⟨fun hgt => ?_, fun hle => ?_⟩
  · apply WP.seq
    apply WP.ck_setField hs h11 (by rfl)
    ck_simp
    intro s12 h12
    exact WP.cp_fail (ws := ws) (X := X) (st := st) (off := off) (rest := rest)
      (fun _ _ h => ⟨rfl, h⟩) h12 hW
  apply WP.skip
  have hle30 : 2 ^ (10 + k11) ≤ 2 ^ 30 := by
    rw [Nat.mod_eq_of_lt hpow64] at hle
    omega
  have hj30 : 10 + k11 ≤ 30 := (Nat.pow_le_pow_iff_right (by decide)).mp hle30
  obtain ⟨H, hHdef⟩ : ∃ H, H = 2 ^ (10 + k11) := ⟨_, rfl⟩
  rw [← hHdef] at h4N hk11 hle30 hpow64 h1024
  rw [← hHdef]
  have hH32 : (BitVec.setWidth 32 (BitVec.ofNat 64 H)) = BitVec.ofNat 32 H := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  have hHt : (BitVec.ofNat 32 H).toNat = H := bv_toNat_ofNat (by omega)
  -- ok = spend(st, (u32)hc); if (ok == 0) { kvfree(fw); return 0; }
  apply WP.seq
  apply WP.call (spend_spec _ sb (({ c8 with facts := F9 } : CMem).wev wk11 er11 c8.k.val)
    (BitVec.ofNat 32 H))
  replace h := h11
  ck_simp [cpEnv, hH32]
  refine ⟨h11, ?_⟩
  rintro rv s12 rfl h12
  rw [spendM_wev, wev_wev] at h12
  replace h := h12
  generalize (spendM (({ c8 with facts := F9 } : CMem).wev wk11 er11 c8.k.val) (BitVec.ofNat 32 H)).2.k.work
    = wk12 at h12 h
  generalize (spendM (({ c8 with facts := F9 } : CMem).wev wk11 er11 c8.k.val) (BitVec.ofNat 32 H)).2.k.err
    = er12 at h12 h
  generalize (spendM (({ c8 with facts := F9 } : CMem).wev wk11 er11 c8.k.val) (BitVec.ofNat 32 H)).1
    = ok12
  embc_simp
  apply WP.seq
  apply WP.ite
  embc_simp
  refine ⟨fun h0 => ?_, fun hne => ?_⟩
  · exact WP.cp_fail (ws := ws) (X := X) (st := st) (off := off) (rest := rest)
      (fun _ _ h => ⟨rfl, h⟩) h12 hW
  apply WP.skip
  -- if (st->mem < (u32)hc) { st->err = ERR_LIMIT; kvfree(fw); return 0; }
  apply WP.seq
  apply WP.ite
  ck_simp [cpEnv, hH32]
  refine ⟨fun hm => ?_, fun hm => ?_⟩
  · apply WP.seq
    apply WP.ck_setField hs h12 (by rfl)
    ck_simp
    intro s13 h13
    exact WP.cp_fail (ws := ws) (X := X) (st := st) (off := off) (rest := rest)
      (fun _ _ h => ⟨rfl, h⟩) h13 hW
  apply WP.skip
  -- st->mem = st->mem - (u32)hc;
  apply WP.seq
  apply WP.ck_setField hs h12 (by rfl)
  ck_simp [cpEnv, hH32]
  intro s13 h13
  replace h := h13
  -- kvfree(st->htab); st->htab = NULL;
  obtain ⟨ob, hob⟩ := hcore.htabPtr
  have hob13 : ({ c8 with facts := F9 } : CMem).k.htab = some (ob, 0) := by
    show c8.k.htab = _; rw [hm8.khtab]; exact hob
  obtain ⟨hobA, hck13, hst13, hH13⟩ := h13.dropArr hs .htab (ob := ob) hob13
  simp only [Arr.field] at hst13 hH13
  have hob8 : c8.k.htab = some (ob, 0) := hob13
  apply WP.seq
  apply WP.ecall
  ck_simp [hob8, Ptr.val, kvfree_run hobA]
  apply WP.seq
  apply WP.setField
  embc_simp [hst13]
  replace h := hH13
  simp only [CMem.setArr, CK.setPtr] at h
  -- st->hcap = 0; st->hcnt = 0;
  apply WP.seq
  apply WP.ck_setField hs h (by rfl)
  ck_simp
  intro s14 h14
  replace h := h14
  apply WP.seq
  apply WP.ck_setField hs h (by rfl)
  ck_simp
  intro s15 h15
  replace h := h15
  -- nt = kvcalloc(hc, sizeof(u32));
  have hH64 : (BitVec.ofNat 64 H).toNat = H := by simp; omega
  have hH0 : BitVec.ofNat 64 H ≠ 0#64 := by
    intro e; have := congrArg BitVec.toNat e; rw [hH64] at this; simp at this; omega
  apply WP.seq
  apply WP.ecall
  ck_simp [cpEnv, kvcalloc_run hH0, hH64]
  by_cases horc2 : (callocResponse (P := Vbcf.prog) hH0 s15).1 ≠ some .null
  case neg =>
    simp only [ne_eq, Classical.not_not] at horc2
    simp only [horc2, ↓reduceIte]
    embc_simp
    apply WP.seq
    apply WP.ite
    embc_simp
    apply WP.seq
    apply WP.ck_setField hs h (by rfl)
    ck_simp
    intro s16 h16
    exact WP.cp_fail (ws := ws) (X := X) (st := st) (off := off) (rest := rest)
      (fun _ _ h => ⟨rfl, h⟩) h16 hW
  simp only [ne_eq, Classical.not_not] at horc2
  simp only [horc2, ↓reduceIte]
  obtain ⟨nb, hnbdef⟩ : ∃ nb, nb = s15.mem.blocks.size := ⟨_, rfl⟩
  obtain ⟨hnew, hck16, hst16, hH16⟩ := h.calloc hs .htab (by rfl) (Array.replicate H (.u32 0#32))
  simp only [Arr.field] at hst16 hH16
  rw [← hnbdef] at hnew hst16 hH16
  rw [← hnbdef]
  embc_simp [Mem.hasTy_ptr hnew rfl]
  apply WP.seq
  apply WP.ite
  embc_simp [hnew]
  apply WP.skip
  -- st->htab = nt;
  apply WP.seq
  apply WP.setField
  embc_simp [hst16]
  replace h := hH16
  simp only [CMem.setArr, CK.setPtr] at h
  -- st->hcap = (u32)hc;
  apply WP.seq
  apply WP.ck_setField hs h (by rfl)
  ck_simp [hH32]
  intro s17 h17
  replace h := h17
  -- o = 0;
  apply WP.seq
  apply WP.assign
  embc_simp
  -- refill the table
  obtain ⟨pb, hpb⟩ := hS.inv.poolPtr
  have hpb8 : c8.k.pool = some (pb, 0) := by rw [hm8.kpool]; exact hpb
  obtain ⟨lp, hlp⟩ : ∃ lp, lp = cpool keep st.cs.pool := ⟨_, rfl⟩
  have hlpend : offs lp lp.size = offK keep st.cs.pool st.cs.pool.size := by rw [hlp]; exact offs_cpool_end
  have hlpsz : lp.size = N := by rw [hlp, cpool_size, hNdef]
  have hoffK_le : offK keep st.cs.pool st.cs.pool.size ≤ c.k.plen.toNat := by
    rw [hplen]; exact offK_le_offs _
  have hcap := hcore.poolCap
  have hrepL : PoolRep X.posOf lp P6 (offs lp lp.size) := by
    rw [hlpend, hlp]
    exact PoolRep.compact hok hcl hrep.fits (fun y nd hk hnd => hC6.kept y nd (lt_size_of_getElem? hnd) hk hnd)
  rw [← hlpend]
  have hzero : (0#32 : BitVec 32) = BitVec.ofNat 32 (offs lp 0) := by simp
  rw [hzero]
  refine cp_refill (c0 := c) (n := c.k.plen - c.k.lo) (nodes := BitVec.ofNat 32 (cntK keep st.cs.pool.size)) hW h (pb := pb)
    (nb := nb) hpb8 rfl (lp := lp) (by exact (hm8.pool ▸ hrepL : _)) (by simp only [maxPool] at hcap; omega)
    ⟨0, Array.replicate H (.u32 0#32), wk12, j11, r11, hdr11, code11, ar11, i11, cc11, ok12, rfl, ?_,
      Nat.zero_le _, ?_, nzCount_replicate _⟩ ?_
  · obtain ⟨-, -, -, hpA⟩ := h.arr .pool pb 0 hpb8
    obtain ⟨-, -, -, hhA⟩ := h.arr .htab nb 0 rfl
    exact ⟨h.ck, hpb8, rfl, hpA, hhA, fun e => h.sep .htab .pool nb pb 0 0 (by decide) rfl hpb8 e,
      fun _ _ _ => rfl, rfl⟩
  · show HtabPart X.posOf lp (Array.replicate H (.u32 0#32)) (BitVec.ofNat 32 H).toNat (fun y => y < 0)
    rw [hHt]
    exact (HtabPart.zero X.posOf lp ⟨10 + k11, hHdef, hj30⟩).mono (fun _ _ hi => absurd hi (Nat.not_lt_zero _))
  intro s18 htab18 wk18 j18 r18 hdr18 code18 ar18 i18 cc18 ok18 hv18 hpart18 hnz18
  have hH18 := h.ofHView hv18 rfl (by rfl)
  obtain ⟨hblk, hfin⟩ := hH18.freeAux hW
  -- kvfree(fw); return 1;
  apply WP.seq
  apply WP.ecall
  embc_simp [cpEnv, kvfree_run hblk]
  apply WP.ret
  embc_simp [retPost, CpPost]
  refine ⟨_, hfin, st.compact keep hok hcl, rfl, ?_⟩
  refine SInv.compact hS hcl hpre hroot ?_ ?_ hFl9 hFc9
  · exact ⟨hm8.proof, hm8.prem, hm8.lr, hFs9, hm8.kpool, hm8.kproof, hm8.kprem, hm8.kfacts, hm8.klr,
      hm8.knexpr, hm8.ktt, hm8.kff, hm8.kgoal, hm8.kflen, hm8.kfcap, hm8.klo⟩
  · have hpsz := hcore.poolSize pb 0 hpb
    have hsz32 : lp.size < 2 ^ 32 := by omega
    refine ⟨cst_ok hok hcl, fun hn => ?_, fun b o _ => ?_, ⟨?_, ?_⟩, ?_, ⟨nb, rfl⟩, ?_,
      ⟨hm8.stk.null, hm8.stk.size, hm8.stk.cap⟩, hcore.posInj⟩
    · have : c8.k.pool = none := hn
      rw [hpb8] at this; cases this
    · show c8.pool.size = c8.k.pcap.toNat
      rw [hm8.pool, hC6.size, hm8.kpcap, hpsz]
    · show c8.k.plen.toNat ≤ c8.k.pcap.toNat
      rw [hm8.kplen, hm8.kpcap, bv_toNat_ofNat hoffK32]; omega
    · show c8.k.pcap.toNat ≤ maxPool
      rw [hm8.kpcap]; exact hcap.2
    · show PoolRep X.posOf (cpool keep st.cs.pool) c8.pool c8.k.plen.toNat
      rw [hm8.pool, hm8.kplen, bv_toNat_ofNat hoffK32, ← hlpend, ← hlp]
      exact hrepL
    · show HtabOK X.posOf (cpool keep st.cs.pool) htab18 (BitVec.ofNat 32 H).toNat
        (BitVec.ofNat 32 lp.size).toNat
      rw [hHt, bv_toNat_ofNat hsz32, ← hlp]
      have hpart' : HtabPart X.posOf lp htab18 H (fun y => y < lp.size) := by
        have := hpart18; rw [show (BitVec.ofNat 32 H).toNat = H from hHt] at this; exact this
      exact hpart'.toOK (fun i hi => hi) rfl hnz18 (by rw [hlpsz]; omega)

end Vbcf.Proof
