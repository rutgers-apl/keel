import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Eval5

/-!
# Vbcf proofs: the Eval family, part 6 — the two-argument group of `cval`
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf


/-- The common start of the two-argument group: evaluate both children. -/
theorem grpB_core {d : BitVec 32} (IH : ∀ d' : BitVec 32, d'.toNat < d.toNat → CvalSpecD (State := State) d')
    (hd : d ≠ 0#32) {W : World} {sb : Nat} {c : CMem} {posOf : Nat → Nat} {st : VSt} {i : Nat}
    {op : Op} {a b : Nat} {hdr code nn par lo hi w cw i0 : BitVec 32}
    {x y z m sbv acc : BitVec 64} {s : (KernelState prog State)} {Q : (Post prog State)} {pb : Nat}
    (h : Holds W s.mem sb c) (hc : VInv posOf c st) (hpool : c.k.pool = some (pb, 0))
    (hn : st.pool[i]? = some ⟨op, #[a, b]⟩) (hl : ¬ IsLeaf op) (hQ : CvQ W sb c st i Q)
    (K : ∀ (r1 r2 wk er : BitVec 32) (vl1 vl2 : BitVec 64) (s' : (KernelState prog State)),
      Holds W s'.mem sb (c.wev wk er vl2) →
      (∃ v, memoVal st a = some v ∧ CvRep r1 vl1 v) →
      (∃ v, memoVal st b = some v ∧ CvRep r2 vl2 v) →
      WP Vbcf.prog cvBt Q
        (cvEnv sb (BitVec.ofNat 32 (st.id i)) d hdr code nn par lo hi w r2 i0 vl1 vl2 z m sbv acc) s') (h_lv : st.lv i := by vlv) :
    WP Vbcf.prog cvB Q
      (cvEnv sb (BitVec.ofNat 32 (st.id i)) d hdr code nn par lo hi w cw i0 x y z m sbv acc) s := by
  have hi := h_lv
  have hs := prog_ck
  have ha : st.lv a := hc.arg_lv hn a (by simp)
  have hb : st.lv b := hc.arg_lv hn b (by simp)
  have hrd := hc.rd2 hn hl
  simp only [cvB, Stmt.block]
  apply WP.cval_child (IH _ (cv_dec_lt hd)) h hc ha (by cv_simp [hrd])
  intro r1 wk1 er1 vl1 s1 h1 hv1
  cv_simp
  apply WP.cw_guard (r := r1) hQ h1 (by cv_simp)
  intro hr1 hr1'
  replace h := h1
  apply WP.assign_seq; cv_simp
  apply WP.cval_child (IH _ (cv_dec_lt hd)) h hc.wev hb (by cv_simp [hrd])
  intro r2 wk2 er2 vl2 s2 h2 hv2
  simp only [wev_wev] at h2
  cv_simp
  apply WP.cw_guard (r := r2) hQ h2 (by cv_simp)
  intro hr2 hr2'
  replace h := h2
  apply WP.assign_seq; cv_simp
  exact K r1 r2 wk2 er2 vl1 vl2 s2 h2 (hv1 hr1 hr1') (hv2 hr2 hr2')

section chainsB
variable {W : World} {sb : Nat} {c : CMem} {st : VSt} {i : Nat} {Q : (Post prog State)}
  {id d hdr nn par w : BitVec 32} {z sbv acc : BitVec 64}

theorem cv_memo2 {st : St} (hok : TysOK st.pool st.tys) {i : Nat} {op : Op} {a b : Nat}
    (hn : st.pool[i]? = some ⟨op, #[a, b]⟩) (hl : ¬ IsLeaf op) (hz : ∀ w, op ≠ .bvSize w)
    {v1 v2 : Bcf.Val} (h1 : memoVal st a = some v1) (h2 : memoVal st b = some v2) {t : Bcf.Ty}
    (ht : st.tys[i]? = some t) :
    memoVal st i = some (Op.eval (fun _ => 0) op [v1, v2]) ∧
      (Op.eval (fun _ => 0) op [v1, v2]).ty = some t := by
  have hm := cv_memoVal_2 hok hn hl hz h1 h2
  exact ⟨hm, by rw [cv_memoVal_ty hok hm, ht]⟩

theorem chainB_sub (hQ : CvQ W sb c st i Q) {a b : Nat} {t : Bcf.Ty} {op : Op} {w' : Nat}
    (hop : op = (.bvSub w')) (hn : st.pool[i]? = some ⟨op, #[a, b]⟩) (hok : TysOK st.pool st.tys)
    (ht : st.tys[i]? = some t) (hw : CvW t w) :
    ∀ (r1 r2 wk er : BitVec 32) (vl1 vl2 : BitVec 64) (s' : (KernelState prog State)),
      Holds W s'.mem sb (c.wev wk er vl2) →
      (∃ v, memoVal st a = some v ∧ CvRep r1 vl1 v) →
      (∃ v, memoVal st b = some v ∧ CvRep r2 vl2 v) →
      WP Vbcf.prog cvBt Q
        (cvEnv sb id d hdr (BitVec.ofNat 32 (opC op)) nn par (BitVec.ofNat 32 (opLo op))
          (BitVec.ofNat 32 (opHi op)) w r2 0#32 vl1 vl2 z (mW w) sbv acc) s' := by
  intro r1 r2 wk er vl1 vl2 s' h ⟨v1, hm1, hv1⟩ ⟨v2, hm2, hv2⟩
  subst hop
  have hs := prog_ck
  obtain ⟨hm, hty⟩ := cv_memo2 hok hn (by simp [IsLeaf, isLeaf]) (by simp) hm1 hm2 ht
  simp only [cvBt, Stmt.block]
  apply WP.seq
  apply WP.ite; cv_simp0 [opC]
  apply WP.assign; cv_simp0
  apply WP.cv_finish (w := w) (x' := vl1 - vl2 &&& mW w) hQ h (by simp [Env.get]) (by simp [Env.get])
    (by cv_simp0)
  intro _ _
  exact ⟨_, hm, cvsem_sub hv1 hv2 hty hw⟩

theorem chainB_eq (hQ : CvQ W sb c st i Q) {a b : Nat} {t : Bcf.Ty} {op : Op}
    (hop : op = .eq) (hn : st.pool[i]? = some ⟨op, #[a, b]⟩) (hok : TysOK st.pool st.tys)
    (ht : st.tys[i]? = some t) (hw : CvW t w) :
    ∀ (r1 r2 wk er : BitVec 32) (vl1 vl2 : BitVec 64) (s' : (KernelState prog State)),
      Holds W s'.mem sb (c.wev wk er vl2) →
      (∃ v, memoVal st a = some v ∧ CvRep r1 vl1 v) →
      (∃ v, memoVal st b = some v ∧ CvRep r2 vl2 v) →
      WP Vbcf.prog cvBt Q
        (cvEnv sb id d hdr (BitVec.ofNat 32 (opC op)) nn par (BitVec.ofNat 32 (opLo op))
          (BitVec.ofNat 32 (opHi op)) w r2 0#32 vl1 vl2 z (mW w) sbv acc) s' := by
  intro r1 r2 wk er vl1 vl2 s' h ⟨v1, hm1, hv1⟩ ⟨v2, hm2, hv2⟩
  subst hop
  have hs := prog_ck
  obtain ⟨hm, hty⟩ := cv_memo2 hok hn (by simp [IsLeaf, isLeaf]) (by simp) hm1 hm2 ht
  simp only [cvBt, Stmt.block]
  apply WP.seq
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.assign; cv_simp0
  apply WP.cv_finish (w := w) (x' := BitVec.setWidth 64 (bw (vl1 = vl2))) hQ h (by simp [Env.get]) (by simp [Env.get])
    (by cv_simp0)
  intro _ _
  refine ⟨_, hm, ?_⟩
  rw [cv_bw64_eq]
  have := cvsem_eqv (neg := false) rfl hv1 hv2 hty hw
  simpa using this

theorem chainB_distinct (hQ : CvQ W sb c st i Q) {a b : Nat} {t : Bcf.Ty} {op : Op}
    (hop : op = .distinct) (hn : st.pool[i]? = some ⟨op, #[a, b]⟩) (hok : TysOK st.pool st.tys)
    (ht : st.tys[i]? = some t) (hw : CvW t w) :
    ∀ (r1 r2 wk er : BitVec 32) (vl1 vl2 : BitVec 64) (s' : (KernelState prog State)),
      Holds W s'.mem sb (c.wev wk er vl2) →
      (∃ v, memoVal st a = some v ∧ CvRep r1 vl1 v) →
      (∃ v, memoVal st b = some v ∧ CvRep r2 vl2 v) →
      WP Vbcf.prog cvBt Q
        (cvEnv sb id d hdr (BitVec.ofNat 32 (opC op)) nn par (BitVec.ofNat 32 (opLo op))
          (BitVec.ofNat 32 (opHi op)) w r2 0#32 vl1 vl2 z (mW w) sbv acc) s' := by
  intro r1 r2 wk er vl1 vl2 s' h ⟨v1, hm1, hv1⟩ ⟨v2, hm2, hv2⟩
  subst hop
  have hs := prog_ck
  obtain ⟨hm, hty⟩ := cv_memo2 hok hn (by simp [IsLeaf, isLeaf]) (by simp) hm1 hm2 ht
  simp only [cvBt, Stmt.block]
  apply WP.seq
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.assign; cv_simp0
  apply WP.cv_finish (w := w) (x' := BitVec.setWidth 64 (bw ¬vl1 = vl2)) hQ h (by simp [Env.get]) (by simp [Env.get])
    (by cv_simp0)
  intro _ _
  refine ⟨_, hm, ?_⟩
  rw [cv_bw64_eq]
  have := cvsem_eqv (neg := true) rfl hv1 hv2 hty hw
  simpa using this

theorem chainB_implies (hQ : CvQ W sb c st i Q) {a b : Nat} {t : Bcf.Ty} {op : Op}
    (hop : op = .implies) (hn : st.pool[i]? = some ⟨op, #[a, b]⟩) (hok : TysOK st.pool st.tys)
    (ht : st.tys[i]? = some t) (hw : CvW t w) :
    ∀ (r1 r2 wk er : BitVec 32) (vl1 vl2 : BitVec 64) (s' : (KernelState prog State)),
      Holds W s'.mem sb (c.wev wk er vl2) →
      (∃ v, memoVal st a = some v ∧ CvRep r1 vl1 v) →
      (∃ v, memoVal st b = some v ∧ CvRep r2 vl2 v) →
      WP Vbcf.prog cvBt Q
        (cvEnv sb id d hdr (BitVec.ofNat 32 (opC op)) nn par (BitVec.ofNat 32 (opLo op))
          (BitVec.ofNat 32 (opHi op)) w r2 0#32 vl1 vl2 z (mW w) sbv acc) s' := by
  intro r1 r2 wk er vl1 vl2 s' h ⟨v1, hm1, hv1⟩ ⟨v2, hm2, hv2⟩
  subst hop
  have hs := prog_ck
  obtain ⟨hm, hty⟩ := cv_memo2 hok hn (by simp [IsLeaf, isLeaf]) (by simp) hm1 hm2 ht
  simp only [cvBt, Stmt.block]
  apply WP.seq
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.assign; cv_simp0
  apply WP.cv_finish (w := w) (x' := 1#64 - vl1 ||| vl2) hQ h (by simp [Env.get]) (by simp [Env.get])
    (by cv_simp0)
  intro _ _
  exact ⟨_, hm, cvsem_implies hv1 hv2 hty hw⟩

theorem chainB_ult (hQ : CvQ W sb c st i Q) {a b : Nat} {t : Bcf.Ty} {op : Op}
    (hop : op = .ult) (hn : st.pool[i]? = some ⟨op, #[a, b]⟩) (hok : TysOK st.pool st.tys)
    (ht : st.tys[i]? = some t) (hw : CvW t w) :
    ∀ (r1 r2 wk er : BitVec 32) (vl1 vl2 : BitVec 64) (s' : (KernelState prog State)),
      Holds W s'.mem sb (c.wev wk er vl2) →
      (∃ v, memoVal st a = some v ∧ CvRep r1 vl1 v) →
      (∃ v, memoVal st b = some v ∧ CvRep r2 vl2 v) →
      WP Vbcf.prog cvBt Q
        (cvEnv sb id d hdr (BitVec.ofNat 32 (opC op)) nn par (BitVec.ofNat 32 (opLo op))
          (BitVec.ofNat 32 (opHi op)) w r2 0#32 vl1 vl2 z (mW w) sbv acc) s' := by
  intro r1 r2 wk er vl1 vl2 s' h ⟨v1, hm1, hv1⟩ ⟨v2, hm2, hv2⟩
  subst hop
  have hs := prog_ck
  obtain ⟨hm, hty⟩ := cv_memo2 hok hn (by simp [IsLeaf, isLeaf]) (by simp) hm1 hm2 ht
  simp only [cvBt, Stmt.block]
  apply WP.seq
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.assign; cv_simp0
  apply WP.cv_finish (w := w) (x' := BitVec.setWidth 64 (bw (vl1 < vl2))) hQ h (by simp [Env.get]) (by simp [Env.get])
    (by cv_simp0)
  intro _ _
  refine ⟨_, hm, ?_⟩
  rw [cv_bw64_eq]
  exact cvsem_cmpU (g := fun a b => a < b) rfl
    (fun x y a b ha hb => by simp [BitVec.lt_def, BitVec.ult, ha, hb]) hv1 hv2 hty hw

theorem chainB_ule (hQ : CvQ W sb c st i Q) {a b : Nat} {t : Bcf.Ty} {op : Op}
    (hop : op = .ule) (hn : st.pool[i]? = some ⟨op, #[a, b]⟩) (hok : TysOK st.pool st.tys)
    (ht : st.tys[i]? = some t) (hw : CvW t w) :
    ∀ (r1 r2 wk er : BitVec 32) (vl1 vl2 : BitVec 64) (s' : (KernelState prog State)),
      Holds W s'.mem sb (c.wev wk er vl2) →
      (∃ v, memoVal st a = some v ∧ CvRep r1 vl1 v) →
      (∃ v, memoVal st b = some v ∧ CvRep r2 vl2 v) →
      WP Vbcf.prog cvBt Q
        (cvEnv sb id d hdr (BitVec.ofNat 32 (opC op)) nn par (BitVec.ofNat 32 (opLo op))
          (BitVec.ofNat 32 (opHi op)) w r2 0#32 vl1 vl2 z (mW w) sbv acc) s' := by
  intro r1 r2 wk er vl1 vl2 s' h ⟨v1, hm1, hv1⟩ ⟨v2, hm2, hv2⟩
  subst hop
  have hs := prog_ck
  obtain ⟨hm, hty⟩ := cv_memo2 hok hn (by simp [IsLeaf, isLeaf]) (by simp) hm1 hm2 ht
  simp only [cvBt, Stmt.block]
  apply WP.seq
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.assign; cv_simp0
  apply WP.cv_finish (w := w) (x' := BitVec.setWidth 64 (bw (vl1 ≤ vl2))) hQ h (by simp [Env.get]) (by simp [Env.get])
    (by cv_simp0)
  intro _ _
  refine ⟨_, hm, ?_⟩
  rw [cv_bw64_eq]
  exact cvsem_cmpU (g := fun a b => a ≤ b) rfl
    (fun x y a b ha hb => by simp [BitVec.le_def, BitVec.ule, ha, hb]) hv1 hv2 hty hw

theorem chainB_ugt (hQ : CvQ W sb c st i Q) {a b : Nat} {t : Bcf.Ty} {op : Op}
    (hop : op = .ugt) (hn : st.pool[i]? = some ⟨op, #[a, b]⟩) (hok : TysOK st.pool st.tys)
    (ht : st.tys[i]? = some t) (hw : CvW t w) :
    ∀ (r1 r2 wk er : BitVec 32) (vl1 vl2 : BitVec 64) (s' : (KernelState prog State)),
      Holds W s'.mem sb (c.wev wk er vl2) →
      (∃ v, memoVal st a = some v ∧ CvRep r1 vl1 v) →
      (∃ v, memoVal st b = some v ∧ CvRep r2 vl2 v) →
      WP Vbcf.prog cvBt Q
        (cvEnv sb id d hdr (BitVec.ofNat 32 (opC op)) nn par (BitVec.ofNat 32 (opLo op))
          (BitVec.ofNat 32 (opHi op)) w r2 0#32 vl1 vl2 z (mW w) sbv acc) s' := by
  intro r1 r2 wk er vl1 vl2 s' h ⟨v1, hm1, hv1⟩ ⟨v2, hm2, hv2⟩
  subst hop
  have hs := prog_ck
  obtain ⟨hm, hty⟩ := cv_memo2 hok hn (by simp [IsLeaf, isLeaf]) (by simp) hm1 hm2 ht
  simp only [cvBt, Stmt.block]
  apply WP.seq
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.assign; cv_simp0
  apply WP.cv_finish (w := w) (x' := BitVec.setWidth 64 (bw (vl2 < vl1))) hQ h (by simp [Env.get]) (by simp [Env.get])
    (by cv_simp0)
  intro _ _
  refine ⟨_, hm, ?_⟩
  rw [cv_bw64_eq]
  exact cvsem_cmpU (f := fun x y => y.ult x) (g := fun a b => b < a) rfl
    (fun x y a b ha hb => by simp [BitVec.lt_def, BitVec.ult, ha, hb]) hv1 hv2 hty hw

theorem chainB_uge (hQ : CvQ W sb c st i Q) {a b : Nat} {t : Bcf.Ty} {op : Op}
    (hop : op = .uge) (hn : st.pool[i]? = some ⟨op, #[a, b]⟩) (hok : TysOK st.pool st.tys)
    (ht : st.tys[i]? = some t) (hw : CvW t w) :
    ∀ (r1 r2 wk er : BitVec 32) (vl1 vl2 : BitVec 64) (s' : (KernelState prog State)),
      Holds W s'.mem sb (c.wev wk er vl2) →
      (∃ v, memoVal st a = some v ∧ CvRep r1 vl1 v) →
      (∃ v, memoVal st b = some v ∧ CvRep r2 vl2 v) →
      WP Vbcf.prog cvBt Q
        (cvEnv sb id d hdr (BitVec.ofNat 32 (opC op)) nn par (BitVec.ofNat 32 (opLo op))
          (BitVec.ofNat 32 (opHi op)) w r2 0#32 vl1 vl2 z (mW w) sbv acc) s' := by
  intro r1 r2 wk er vl1 vl2 s' h ⟨v1, hm1, hv1⟩ ⟨v2, hm2, hv2⟩
  subst hop
  have hs := prog_ck
  obtain ⟨hm, hty⟩ := cv_memo2 hok hn (by simp [IsLeaf, isLeaf]) (by simp) hm1 hm2 ht
  simp only [cvBt, Stmt.block]
  apply WP.seq
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.assign; cv_simp0
  apply WP.cv_finish (w := w) (x' := BitVec.setWidth 64 (bw (vl2 ≤ vl1))) hQ h (by simp [Env.get]) (by simp [Env.get])
    (by cv_simp0)
  intro _ _
  refine ⟨_, hm, ?_⟩
  rw [cv_bw64_eq]
  exact cvsem_cmpU (f := fun x y => y.ule x) (g := fun a b => b ≤ a) rfl
    (fun x y a b ha hb => by simp [BitVec.le_def, BitVec.ule, ha, hb]) hv1 hv2 hty hw

theorem chainB_udiv (hQ : CvQ W sb c st i Q) {a b : Nat} {t : Bcf.Ty} {op : Op} {w' : Nat}
    (hop : op = (.bvUdiv w')) (hn : st.pool[i]? = some ⟨op, #[a, b]⟩) (hok : TysOK st.pool st.tys)
    (ht : st.tys[i]? = some t) (hw : CvW t w) :
    ∀ (r1 r2 wk er : BitVec 32) (vl1 vl2 : BitVec 64) (s' : (KernelState prog State)),
      Holds W s'.mem sb (c.wev wk er vl2) →
      (∃ v, memoVal st a = some v ∧ CvRep r1 vl1 v) →
      (∃ v, memoVal st b = some v ∧ CvRep r2 vl2 v) →
      WP Vbcf.prog cvBt Q
        (cvEnv sb id d hdr (BitVec.ofNat 32 (opC op)) nn par (BitVec.ofNat 32 (opLo op))
          (BitVec.ofNat 32 (opHi op)) w r2 0#32 vl1 vl2 z (mW w) sbv acc) s' := by
  intro r1 r2 wk er vl1 vl2 s' h ⟨v1, hm1, hv1⟩ ⟨v2, hm2, hv2⟩
  subst hop
  have hs := prog_ck
  obtain ⟨hm, hty⟩ := cv_memo2 hok hn (by simp [IsLeaf, isLeaf]) (by simp) hm1 hm2 ht
  have hty' := hty
  simp only [Op.eval] at hty'
  obtain ⟨-, -, -, -, rfl, -, -, -, -, -⟩ := cv_bvBin_inv hv1 hv2 hty'
  obtain ⟨hw1, hw2⟩ := hw.bv_bounds
  simp only [cvBt, Stmt.block]
  apply WP.seq
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.call (udiv_w_spec vl1 vl2 (mW w)); cv_simp0
  apply WP.cv_finish (w := w) (x' := udivM vl1 vl2 (mW w)) hQ h (by simp [Env.get]) (by simp [Env.get])
    (by cv_simp0)
  intro _ _
  exact ⟨_, hm, cvsem_udiv hv1 hv2 hty hw⟩

theorem chainB_urem (hQ : CvQ W sb c st i Q) {a b : Nat} {t : Bcf.Ty} {op : Op} {w' : Nat}
    (hop : op = (.bvUrem w')) (hn : st.pool[i]? = some ⟨op, #[a, b]⟩) (hok : TysOK st.pool st.tys)
    (ht : st.tys[i]? = some t) (hw : CvW t w) :
    ∀ (r1 r2 wk er : BitVec 32) (vl1 vl2 : BitVec 64) (s' : (KernelState prog State)),
      Holds W s'.mem sb (c.wev wk er vl2) →
      (∃ v, memoVal st a = some v ∧ CvRep r1 vl1 v) →
      (∃ v, memoVal st b = some v ∧ CvRep r2 vl2 v) →
      WP Vbcf.prog cvBt Q
        (cvEnv sb id d hdr (BitVec.ofNat 32 (opC op)) nn par (BitVec.ofNat 32 (opLo op))
          (BitVec.ofNat 32 (opHi op)) w r2 0#32 vl1 vl2 z (mW w) sbv acc) s' := by
  intro r1 r2 wk er vl1 vl2 s' h ⟨v1, hm1, hv1⟩ ⟨v2, hm2, hv2⟩
  subst hop
  have hs := prog_ck
  obtain ⟨hm, hty⟩ := cv_memo2 hok hn (by simp [IsLeaf, isLeaf]) (by simp) hm1 hm2 ht
  have hty' := hty
  simp only [Op.eval] at hty'
  obtain ⟨-, -, -, -, rfl, -, -, -, -, -⟩ := cv_bvBin_inv hv1 hv2 hty'
  obtain ⟨hw1, hw2⟩ := hw.bv_bounds
  simp only [cvBt, Stmt.block]
  apply WP.seq
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.call (umod_w_spec vl1 vl2); cv_simp0
  apply WP.cv_finish (w := w) (x' := umodM vl1 vl2) hQ h (by simp [Env.get]) (by simp [Env.get])
    (by cv_simp0)
  intro _ _
  exact ⟨_, hm, cvsem_urem hv1 hv2 hty hw⟩

theorem chainB_sdiv (hQ : CvQ W sb c st i Q) {a b : Nat} {t : Bcf.Ty} {op : Op} {w' : Nat}
    (hop : op = (.bvSdiv w')) (hn : st.pool[i]? = some ⟨op, #[a, b]⟩) (hok : TysOK st.pool st.tys)
    (ht : st.tys[i]? = some t) (hw : CvW t w) :
    ∀ (r1 r2 wk er : BitVec 32) (vl1 vl2 : BitVec 64) (s' : (KernelState prog State)),
      Holds W s'.mem sb (c.wev wk er vl2) →
      (∃ v, memoVal st a = some v ∧ CvRep r1 vl1 v) →
      (∃ v, memoVal st b = some v ∧ CvRep r2 vl2 v) →
      WP Vbcf.prog cvBt Q
        (cvEnv sb id d hdr (BitVec.ofNat 32 (opC op)) nn par (BitVec.ofNat 32 (opLo op))
          (BitVec.ofNat 32 (opHi op)) w r2 0#32 vl1 vl2 z (mW w) sbv acc) s' := by
  intro r1 r2 wk er vl1 vl2 s' h ⟨v1, hm1, hv1⟩ ⟨v2, hm2, hv2⟩
  subst hop
  have hs := prog_ck
  obtain ⟨hm, hty⟩ := cv_memo2 hok hn (by simp [IsLeaf, isLeaf]) (by simp) hm1 hm2 ht
  have hty' := hty
  simp only [Op.eval] at hty'
  obtain ⟨-, -, -, -, rfl, -, -, -, -, -⟩ := cv_bvBin_inv hv1 hv2 hty'
  obtain ⟨hw1, hw2⟩ := hw.bv_bounds
  simp only [cvBt, Stmt.block]
  apply WP.seq
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.call (sdiv_w_spec vl1 vl2 (mW w) w hw1 hw2); cv_simp0
  apply WP.cv_finish (w := w) (x' := sdivM vl1 vl2 (mW w) (w.toNat - 1)) hQ h (by simp [Env.get]) (by simp [Env.get])
    (by cv_simp0)
  intro _ _
  exact ⟨_, hm, cvsem_sdiv hv1 hv2 hty hw⟩

theorem chainB_smod (hQ : CvQ W sb c st i Q) {a b : Nat} {t : Bcf.Ty} {op : Op} {w' : Nat}
    (hop : op = (.bvSmod w')) (hn : st.pool[i]? = some ⟨op, #[a, b]⟩) (hok : TysOK st.pool st.tys)
    (ht : st.tys[i]? = some t) (hw : CvW t w) :
    ∀ (r1 r2 wk er : BitVec 32) (vl1 vl2 : BitVec 64) (s' : (KernelState prog State)),
      Holds W s'.mem sb (c.wev wk er vl2) →
      (∃ v, memoVal st a = some v ∧ CvRep r1 vl1 v) →
      (∃ v, memoVal st b = some v ∧ CvRep r2 vl2 v) →
      WP Vbcf.prog cvBt Q
        (cvEnv sb id d hdr (BitVec.ofNat 32 (opC op)) nn par (BitVec.ofNat 32 (opLo op))
          (BitVec.ofNat 32 (opHi op)) w r2 0#32 vl1 vl2 z (mW w) sbv acc) s' := by
  intro r1 r2 wk er vl1 vl2 s' h ⟨v1, hm1, hv1⟩ ⟨v2, hm2, hv2⟩
  subst hop
  have hs := prog_ck
  obtain ⟨hm, hty⟩ := cv_memo2 hok hn (by simp [IsLeaf, isLeaf]) (by simp) hm1 hm2 ht
  have hty' := hty
  simp only [Op.eval] at hty'
  obtain ⟨-, -, -, -, rfl, -, -, -, -, -⟩ := cv_bvBin_inv hv1 hv2 hty'
  obtain ⟨hw1, hw2⟩ := hw.bv_bounds
  simp only [cvBt, Stmt.block]
  apply WP.seq
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.call (smod_w_spec vl1 vl2 (mW w) w hw1 hw2); cv_simp0
  apply WP.cv_finish (w := w) (x' := smodM vl1 vl2 (mW w) (w.toNat - 1)) hQ h (by simp [Env.get]) (by simp [Env.get])
    (by cv_simp0)
  intro _ _
  exact ⟨_, hm, cvsem_smod hv1 hv2 hty hw⟩

theorem chainB_shl (hQ : CvQ W sb c st i Q) {a b : Nat} {t : Bcf.Ty} {op : Op} {w' : Nat}
    (hop : op = (.bvShl w')) (hn : st.pool[i]? = some ⟨op, #[a, b]⟩) (hok : TysOK st.pool st.tys)
    (ht : st.tys[i]? = some t) (hw : CvW t w) :
    ∀ (r1 r2 wk er : BitVec 32) (vl1 vl2 : BitVec 64) (s' : (KernelState prog State)),
      Holds W s'.mem sb (c.wev wk er vl2) →
      (∃ v, memoVal st a = some v ∧ CvRep r1 vl1 v) →
      (∃ v, memoVal st b = some v ∧ CvRep r2 vl2 v) →
      WP Vbcf.prog cvBt Q
        (cvEnv sb id d hdr (BitVec.ofNat 32 (opC op)) nn par (BitVec.ofNat 32 (opLo op))
          (BitVec.ofNat 32 (opHi op)) w r2 0#32 vl1 vl2 z (mW w) sbv acc) s' := by
  intro r1 r2 wk er vl1 vl2 s' h ⟨v1, hm1, hv1⟩ ⟨v2, hm2, hv2⟩
  subst hop
  have hs := prog_ck
  obtain ⟨hm, hty⟩ := cv_memo2 hok hn (by simp [IsLeaf, isLeaf]) (by simp) hm1 hm2 ht
  have hty' := hty
  simp only [Op.eval] at hty'
  obtain ⟨-, -, -, -, rfl, -, -, -, -, -⟩ := cv_bvBin_inv hv1 hv2 hty'
  obtain ⟨hk1, hk2, rfl⟩ := hw.bv
  simp only [cvBt, Stmt.block]
  apply WP.seq
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.seq; apply WP.assign; cv_simp0
  apply WP.ite; cv_simp0
  by_cases hy : vl2 < BitVec.ofNat 64 w'
  · refine ⟨fun _ => ?_, fun h0 => absurd h0 (by simpa using hy)⟩
    have hlt : vl2.toNat < 64 := by rw [cv_lt_ofNat64 hk2] at hy; omega
    apply WP.assign; cv_simp0 [hlt]
    apply WP.cv_finish (w := BitVec.ofNat 32 w') (x' := vl1 <<< vl2.toNat &&& mW (BitVec.ofNat 32 w')) hQ h (by simp [Env.get]) (by simp [Env.get])
      (by cv_simp0)
    intro _ _
    have := cvsem_shl hv1 hv2 hty hw
    rw [ite_eq_left hy] at this
    exact ⟨_, hm, this⟩
  · refine ⟨fun h0 => absurd h0 hy, fun _ => ?_⟩
    apply WP.skip
    apply WP.cv_finish (w := BitVec.ofNat 32 w') (x' := 0#64) hQ h (by simp [Env.get]) (by simp [Env.get]) (by cv_simp0)
    intro _ _
    have := cvsem_shl hv1 hv2 hty hw
    rw [ite_eq_right hy] at this
    exact ⟨_, hm, this⟩

theorem chainB_lshr (hQ : CvQ W sb c st i Q) {a b : Nat} {t : Bcf.Ty} {op : Op} {w' : Nat}
    (hop : op = (.bvLshr w')) (hn : st.pool[i]? = some ⟨op, #[a, b]⟩) (hok : TysOK st.pool st.tys)
    (ht : st.tys[i]? = some t) (hw : CvW t w) :
    ∀ (r1 r2 wk er : BitVec 32) (vl1 vl2 : BitVec 64) (s' : (KernelState prog State)),
      Holds W s'.mem sb (c.wev wk er vl2) →
      (∃ v, memoVal st a = some v ∧ CvRep r1 vl1 v) →
      (∃ v, memoVal st b = some v ∧ CvRep r2 vl2 v) →
      WP Vbcf.prog cvBt Q
        (cvEnv sb id d hdr (BitVec.ofNat 32 (opC op)) nn par (BitVec.ofNat 32 (opLo op))
          (BitVec.ofNat 32 (opHi op)) w r2 0#32 vl1 vl2 z (mW w) sbv acc) s' := by
  intro r1 r2 wk er vl1 vl2 s' h ⟨v1, hm1, hv1⟩ ⟨v2, hm2, hv2⟩
  subst hop
  have hs := prog_ck
  obtain ⟨hm, hty⟩ := cv_memo2 hok hn (by simp [IsLeaf, isLeaf]) (by simp) hm1 hm2 ht
  have hty' := hty
  simp only [Op.eval] at hty'
  obtain ⟨-, -, -, -, rfl, -, -, -, -, -⟩ := cv_bvBin_inv hv1 hv2 hty'
  obtain ⟨hk1, hk2, rfl⟩ := hw.bv
  simp only [cvBt, Stmt.block]
  apply WP.seq
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.seq; apply WP.assign; cv_simp0
  apply WP.ite; cv_simp0
  by_cases hy : vl2 < BitVec.ofNat 64 w'
  · refine ⟨fun _ => ?_, fun h0 => absurd h0 (by simpa using hy)⟩
    have hlt : vl2.toNat < 64 := by rw [cv_lt_ofNat64 hk2] at hy; omega
    apply WP.assign; cv_simp0 [hlt]
    apply WP.cv_finish (w := BitVec.ofNat 32 w') (x' := vl1 >>> vl2.toNat) hQ h (by simp [Env.get]) (by simp [Env.get])
      (by cv_simp0)
    intro _ _
    have := cvsem_lshr hv1 hv2 hty hw
    rw [ite_eq_left hy] at this
    exact ⟨_, hm, this⟩
  · refine ⟨fun h0 => absurd h0 hy, fun _ => ?_⟩
    apply WP.skip
    apply WP.cv_finish (w := BitVec.ofNat 32 w') (x' := 0#64) hQ h (by simp [Env.get]) (by simp [Env.get]) (by cv_simp0)
    intro _ _
    have := cvsem_lshr hv1 hv2 hty hw
    rw [ite_eq_right hy] at this
    exact ⟨_, hm, this⟩

theorem chainB_ashr (hQ : CvQ W sb c st i Q) {a b : Nat} {t : Bcf.Ty} {op : Op} {w' : Nat}
    (hop : op = (.bvAshr w')) (hn : st.pool[i]? = some ⟨op, #[a, b]⟩) (hok : TysOK st.pool st.tys)
    (ht : st.tys[i]? = some t) (hw : CvW t w) :
    ∀ (r1 r2 wk er : BitVec 32) (vl1 vl2 : BitVec 64) (s' : (KernelState prog State)),
      Holds W s'.mem sb (c.wev wk er vl2) →
      (∃ v, memoVal st a = some v ∧ CvRep r1 vl1 v) →
      (∃ v, memoVal st b = some v ∧ CvRep r2 vl2 v) →
      WP Vbcf.prog cvBt Q
        (cvEnv sb id d hdr (BitVec.ofNat 32 (opC op)) nn par (BitVec.ofNat 32 (opLo op))
          (BitVec.ofNat 32 (opHi op)) w r2 0#32 vl1 vl2 z (mW w) sbv acc) s' := by
  intro r1 r2 wk er vl1 vl2 s' h ⟨v1, hm1, hv1⟩ ⟨v2, hm2, hv2⟩
  subst hop
  have hs := prog_ck
  obtain ⟨hm, hty⟩ := cv_memo2 hok hn (by simp [IsLeaf, isLeaf]) (by simp) hm1 hm2 ht
  have hty' := hty
  simp only [Op.eval] at hty'
  obtain ⟨-, -, -, -, rfl, -, -, -, -, -⟩ := cv_bvBin_inv hv1 hv2 hty'
  obtain ⟨hk1, hk2, rfl⟩ := hw.bv
  simp only [cvBt, Stmt.block]
  apply WP.seq
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  have e1 : (4294967295 + w') % 4294967296 % 18446744073709551616 = w' - 1 := by omega
  have e2 : (4294967295 + w') % 4294967296 = w' - 1 := by omega
  have e3 : w' - 1 < 64 := by omega
  have e4 : (w' - 1) % 18446744073709551616 = w' - 1 := by omega
  apply WP.seq; apply WP.assign; cv_simp0 [e1, e2, e3, e4]
  apply WP.ite; cv_simp0
  have hfin : ∀ (zf : BitVec 64), zf = ashrC vl1 vl2 (mW (BitVec.ofNat 32 w')) w' →
      ∀ env s'', env.get "st" = some (.ptr sb 0) → env.get "w" = some (.u32 (BitVec.ofNat 32 w')) →
      env.get "z" = some (.u64 zf) → Holds W s''.mem sb (c.wev wk er vl2) →
      WP Vbcf.prog ((Stmt.setField (.var "st") "val" (.var "z")).seq (.ret (some (.var "w")))) Q env s'' := by
    intro zf hzf env s'' h1 h2 h3 h'
    apply WP.cv_finish (x' := zf) hQ h' h1 h2 (by simp [evalE, h3])
    intro _ _
    rw [hzf]
    exact ⟨_, hm, cvsem_ashr hv1 hv2 hty hw⟩
  by_cases hy : BitVec.ofNat 64 w' ≤ vl2 <;> by_cases hb : vl1 >>> (w' - 1) &&& 1#64 = 0#64
  · refine ⟨fun _ => ?_, fun h0 => absurd hy (BitVec.not_le.mpr h0)⟩
    apply WP.seq; apply WP.assign; cv_simp0
    apply WP.ite; cv_simp0 [hb]
    apply WP.skip
    exact hfin (0#64) (by simp [ashrC, hy, hb]) _ _ (by simp [Env.get]) (by simp [Env.get])
      (by simp [Env.get]) h
  · refine ⟨fun _ => ?_, fun h0 => absurd hy (BitVec.not_le.mpr h0)⟩
    apply WP.seq; apply WP.assign; cv_simp0
    apply WP.ite; cv_simp0 [hb]
    apply WP.assign; cv_simp0
    exact hfin (mW (BitVec.ofNat 32 w')) (by simp [ashrC, hy, hb]) _ _ (by simp [Env.get]) (by simp [Env.get])
      (by simp [Env.get]) h
  · have hlt : vl2.toNat < 64 := by
      rw [BitVec.le_def] at hy; simp at hy; omega
    refine ⟨fun h0 => absurd h0 hy, fun _ => ?_⟩
    apply WP.seq; apply WP.assign; cv_simp0 [hlt]
    apply WP.ite; cv_simp0 [hb]
    apply WP.skip
    exact hfin (vl1 >>> vl2.toNat) (by simp [ashrC, hy, hb]) _ _ (by simp [Env.get]) (by simp [Env.get])
      (by simp [Env.get]) h
  · have hlt : vl2.toNat < 64 := by
      rw [BitVec.le_def] at hy; simp at hy; omega
    refine ⟨fun h0 => absurd h0 hy, fun _ => ?_⟩
    apply WP.seq; apply WP.assign; cv_simp0 [hlt]
    apply WP.ite; cv_simp0 [hb]
    apply WP.assign; cv_simp0 [hlt]
    exact hfin (vl1 >>> vl2.toNat ||| mW (BitVec.ofNat 32 w') &&& ~~~(mW (BitVec.ofNat 32 w') >>> vl2.toNat)) (by simp [ashrC, hy, hb]) _ _ (by simp [Env.get]) (by simp [Env.get])
      (by simp [Env.get]) h

theorem chainB_slt (hQ : CvQ W sb c st i Q) {a b : Nat} {t : Bcf.Ty} {op : Op}
    (hop : op = .slt) (hn : st.pool[i]? = some ⟨op, #[a, b]⟩) (hok : TysOK st.pool st.tys)
    (ht : st.tys[i]? = some t) (hw : CvW t w) :
    ∀ (r1 r2 wk er : BitVec 32) (vl1 vl2 : BitVec 64) (s' : (KernelState prog State)),
      Holds W s'.mem sb (c.wev wk er vl2) →
      (∃ v, memoVal st a = some v ∧ CvRep r1 vl1 v) →
      (∃ v, memoVal st b = some v ∧ CvRep r2 vl2 v) →
      WP Vbcf.prog cvBt Q
        (cvEnv sb id d hdr (BitVec.ofNat 32 (opC op)) nn par (BitVec.ofNat 32 (opLo op))
          (BitVec.ofNat 32 (opHi op)) w r2 0#32 vl1 vl2 z (mW w) sbv acc) s' := by
  intro r1 r2 wk er vl1 vl2 s' h ⟨v1, hm1, hv1⟩ ⟨v2, hm2, hv2⟩
  subst hop
  have hs := prog_ck
  obtain ⟨hm, hty⟩ := cv_memo2 hok hn (by simp [IsLeaf, isLeaf]) (by simp) hm1 hm2 ht
  obtain ⟨n, hn1, hn64, rfl⟩ := cv_cmp_width hv1 hv2 (by simpa [Op.eval] using hty)
  have e1 : (4294967295 + n) % 4294967296 % 18446744073709551616 = n - 1 := by omega
  have e2 : (4294967295 + n) % 4294967296 = n - 1 := by omega
  have e3 : n - 1 < 64 := by omega
  have e4 : (n - 1) % 18446744073709551616 = n - 1 := by omega
  simp only [cvBt, Stmt.block]
  apply WP.seq
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.seq; apply WP.assign; cv_simp0 [e1, e2, e3, e4]
  apply WP.seq; apply WP.assign; cv_simp0
  apply WP.seq; apply WP.assign; cv_simp0
  apply WP.ite; cv_simp0 [opC]
  apply WP.assign; cv_simp0
  apply WP.cv_finish (w := w) (x' := BitVec.setWidth 64 (bw (vl1 ^^^ 1#64 <<< (n - 1) < vl2 ^^^ 1#64 <<< (n - 1)))) hQ h (by simp [Env.get]) (by simp [Env.get])
    (by cv_simp0)
  intro _ _
  refine ⟨_, hm, ?_⟩
  rw [cv_bw64_eq]
  exact cvsem_cmpS (f := BitVec.slt) (g := fun a b => a ^^^ 1#64 <<< (n - 1) < b ^^^ 1#64 <<< (n - 1)) rfl
    (fun x y a b ha hb => cv_slt_flip hn1 hn64 ha hb) hv1 hv2 hn64 hty hw

theorem chainB_sle (hQ : CvQ W sb c st i Q) {a b : Nat} {t : Bcf.Ty} {op : Op}
    (hop : op = .sle) (hn : st.pool[i]? = some ⟨op, #[a, b]⟩) (hok : TysOK st.pool st.tys)
    (ht : st.tys[i]? = some t) (hw : CvW t w) :
    ∀ (r1 r2 wk er : BitVec 32) (vl1 vl2 : BitVec 64) (s' : (KernelState prog State)),
      Holds W s'.mem sb (c.wev wk er vl2) →
      (∃ v, memoVal st a = some v ∧ CvRep r1 vl1 v) →
      (∃ v, memoVal st b = some v ∧ CvRep r2 vl2 v) →
      WP Vbcf.prog cvBt Q
        (cvEnv sb id d hdr (BitVec.ofNat 32 (opC op)) nn par (BitVec.ofNat 32 (opLo op))
          (BitVec.ofNat 32 (opHi op)) w r2 0#32 vl1 vl2 z (mW w) sbv acc) s' := by
  intro r1 r2 wk er vl1 vl2 s' h ⟨v1, hm1, hv1⟩ ⟨v2, hm2, hv2⟩
  subst hop
  have hs := prog_ck
  obtain ⟨hm, hty⟩ := cv_memo2 hok hn (by simp [IsLeaf, isLeaf]) (by simp) hm1 hm2 ht
  obtain ⟨n, hn1, hn64, rfl⟩ := cv_cmp_width hv1 hv2 (by simpa [Op.eval] using hty)
  have e1 : (4294967295 + n) % 4294967296 % 18446744073709551616 = n - 1 := by omega
  have e2 : (4294967295 + n) % 4294967296 = n - 1 := by omega
  have e3 : n - 1 < 64 := by omega
  have e4 : (n - 1) % 18446744073709551616 = n - 1 := by omega
  simp only [cvBt, Stmt.block]
  apply WP.seq
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.seq; apply WP.assign; cv_simp0 [e1, e2, e3, e4]
  apply WP.seq; apply WP.assign; cv_simp0
  apply WP.seq; apply WP.assign; cv_simp0
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.assign; cv_simp0
  apply WP.cv_finish (w := w) (x' := BitVec.setWidth 64 (bw (vl1 ^^^ 1#64 <<< (n - 1) ≤ vl2 ^^^ 1#64 <<< (n - 1)))) hQ h (by simp [Env.get]) (by simp [Env.get])
    (by cv_simp0)
  intro _ _
  refine ⟨_, hm, ?_⟩
  rw [cv_bw64_eq]
  exact cvsem_cmpS (f := BitVec.sle) (g := fun a b => a ^^^ 1#64 <<< (n - 1) ≤ b ^^^ 1#64 <<< (n - 1)) rfl
    (fun x y a b ha hb => cv_sle_flip hn1 hn64 ha hb) hv1 hv2 hn64 hty hw

theorem chainB_sgt (hQ : CvQ W sb c st i Q) {a b : Nat} {t : Bcf.Ty} {op : Op}
    (hop : op = .sgt) (hn : st.pool[i]? = some ⟨op, #[a, b]⟩) (hok : TysOK st.pool st.tys)
    (ht : st.tys[i]? = some t) (hw : CvW t w) :
    ∀ (r1 r2 wk er : BitVec 32) (vl1 vl2 : BitVec 64) (s' : (KernelState prog State)),
      Holds W s'.mem sb (c.wev wk er vl2) →
      (∃ v, memoVal st a = some v ∧ CvRep r1 vl1 v) →
      (∃ v, memoVal st b = some v ∧ CvRep r2 vl2 v) →
      WP Vbcf.prog cvBt Q
        (cvEnv sb id d hdr (BitVec.ofNat 32 (opC op)) nn par (BitVec.ofNat 32 (opLo op))
          (BitVec.ofNat 32 (opHi op)) w r2 0#32 vl1 vl2 z (mW w) sbv acc) s' := by
  intro r1 r2 wk er vl1 vl2 s' h ⟨v1, hm1, hv1⟩ ⟨v2, hm2, hv2⟩
  subst hop
  have hs := prog_ck
  obtain ⟨hm, hty⟩ := cv_memo2 hok hn (by simp [IsLeaf, isLeaf]) (by simp) hm1 hm2 ht
  obtain ⟨n, hn1, hn64, rfl⟩ := cv_cmp_width hv1 hv2 (by simpa [Op.eval] using hty)
  have e1 : (4294967295 + n) % 4294967296 % 18446744073709551616 = n - 1 := by omega
  have e2 : (4294967295 + n) % 4294967296 = n - 1 := by omega
  have e3 : n - 1 < 64 := by omega
  have e4 : (n - 1) % 18446744073709551616 = n - 1 := by omega
  simp only [cvBt, Stmt.block]
  apply WP.seq
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.seq; apply WP.assign; cv_simp0 [e1, e2, e3, e4]
  apply WP.seq; apply WP.assign; cv_simp0
  apply WP.seq; apply WP.assign; cv_simp0
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.assign; cv_simp0
  apply WP.cv_finish (w := w) (x' := BitVec.setWidth 64 (bw (vl2 ^^^ 1#64 <<< (n - 1) < vl1 ^^^ 1#64 <<< (n - 1)))) hQ h (by simp [Env.get]) (by simp [Env.get])
    (by cv_simp0)
  intro _ _
  refine ⟨_, hm, ?_⟩
  rw [cv_bw64_eq]
  exact cvsem_cmpS (f := fun x y => y.slt x) (g := fun a b => b ^^^ 1#64 <<< (n - 1) < a ^^^ 1#64 <<< (n - 1)) rfl
    (fun x y a b ha hb => cv_slt_flip hn1 hn64 hb ha) hv1 hv2 hn64 hty hw

theorem chainB_sge (hQ : CvQ W sb c st i Q) {a b : Nat} {t : Bcf.Ty} {op : Op}
    (hop : op = .sge) (hn : st.pool[i]? = some ⟨op, #[a, b]⟩) (hok : TysOK st.pool st.tys)
    (ht : st.tys[i]? = some t) (hw : CvW t w) :
    ∀ (r1 r2 wk er : BitVec 32) (vl1 vl2 : BitVec 64) (s' : (KernelState prog State)),
      Holds W s'.mem sb (c.wev wk er vl2) →
      (∃ v, memoVal st a = some v ∧ CvRep r1 vl1 v) →
      (∃ v, memoVal st b = some v ∧ CvRep r2 vl2 v) →
      WP Vbcf.prog cvBt Q
        (cvEnv sb id d hdr (BitVec.ofNat 32 (opC op)) nn par (BitVec.ofNat 32 (opLo op))
          (BitVec.ofNat 32 (opHi op)) w r2 0#32 vl1 vl2 z (mW w) sbv acc) s' := by
  intro r1 r2 wk er vl1 vl2 s' h ⟨v1, hm1, hv1⟩ ⟨v2, hm2, hv2⟩
  subst hop
  have hs := prog_ck
  obtain ⟨hm, hty⟩ := cv_memo2 hok hn (by simp [IsLeaf, isLeaf]) (by simp) hm1 hm2 ht
  obtain ⟨n, hn1, hn64, rfl⟩ := cv_cmp_width hv1 hv2 (by simpa [Op.eval] using hty)
  have e1 : (4294967295 + n) % 4294967296 % 18446744073709551616 = n - 1 := by omega
  have e2 : (4294967295 + n) % 4294967296 = n - 1 := by omega
  have e3 : n - 1 < 64 := by omega
  have e4 : (n - 1) % 18446744073709551616 = n - 1 := by omega
  simp only [cvBt, Stmt.block]
  apply WP.seq
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.seq; apply WP.assign; cv_simp0 [e1, e2, e3, e4]
  apply WP.seq; apply WP.assign; cv_simp0
  apply WP.seq; apply WP.assign; cv_simp0
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.ite; cv_simp0 [opC]
  apply WP.assign; cv_simp0
  apply WP.cv_finish (w := w) (x' := BitVec.setWidth 64 (bw (vl2 ^^^ 1#64 <<< (n - 1) ≤ vl1 ^^^ 1#64 <<< (n - 1)))) hQ h (by simp [Env.get]) (by simp [Env.get])
    (by cv_simp0)
  intro _ _
  refine ⟨_, hm, ?_⟩
  rw [cv_bw64_eq]
  exact cvsem_cmpS (f := fun x y => y.sle x) (g := fun a b => b ^^^ 1#64 <<< (n - 1) ≤ a ^^^ 1#64 <<< (n - 1)) rfl
    (fun x y a b ha hb => cv_sle_flip hn1 hn64 hb ha) hv1 hv2 hn64 hty hw

end chainsB

/-- The codes of the two-argument group, as the dispatch test leaves them. -/
def CvBinC (k : Nat) : Prop :=
  ¬k = 16 → ¬k = 96 → ¬k = 112 → ¬k = 192 → ¬k = 48 → ¬k = 144 → ¬k = 176 → ¬k = 208 →
  ¬k = 17 → ¬k = 81 → ¬k = 33 → ¬k = 49 → ¬k = 97 → ¬k = 113 → ¬k = 161 → ¬k = 177 →
  ¬k = 193 → ¬k = 209 → k = 145

theorem grpB_spec {d : BitVec 32} (IH : ∀ d' : BitVec 32, d'.toNat < d.toNat → CvalSpecD (State := State) d')
    (hd : d ≠ 0#32) {W : World} {sb : Nat} {c : CMem} {posOf : Nat → Nat} {st : VSt} {i : Nat}
    {n : Node} {t : Bcf.Ty} {hdr nn par w cw : BitVec 32}
    {x y z sbv acc : BitVec 64} {s : (KernelState prog State)} {Q : (Post prog State)} {pb : Nat}
    (h : Holds W s.mem sb c) (hc : VInv posOf c st) (hpool : c.k.pool = some (pb, 0))
    (hn : st.pool[i]? = some n) (hop : CvBinC (opC n.op))
    (ht : st.tys[i]? = some t) (hw : CvW t w) (hQ : CvQ W sb c st i Q) (h_lv : st.lv i := by vlv) :
    WP Vbcf.prog cvB Q
      (cvEnv sb (BitVec.ofNat 32 (st.id i)) d hdr (BitVec.ofNat 32 (opC n.op)) nn par
        (BitVec.ofNat 32 (opLo n.op)) (BitVec.ofNat 32 (opHi n.op)) w cw 0#32 x y z (mW w) sbv acc) s := by
  have hi := h_lv
  obtain ⟨op, args⟩ := n
  have hok := hc.ok.tys
  cases op <;> simp only [CvBinC, opC] at hop <;> (try (exfalso; omega))
  all_goals
    obtain ⟨a, b, he, ha, hb⟩ := hc.args2 hn rfl
    injection he with _ he2
    subst he2
    apply grpB_core IH hd h hc hpool hn (by simp [IsLeaf, isLeaf]) hQ
  case bvSub => exact chainB_sub hQ rfl hn hok ht hw
  case bvShl => exact chainB_shl hQ rfl hn hok ht hw
  case bvLshr => exact chainB_lshr hQ rfl hn hok ht hw
  case bvAshr => exact chainB_ashr hQ rfl hn hok ht hw
  case bvUdiv => exact chainB_udiv hQ rfl hn hok ht hw
  case bvUrem => exact chainB_urem hQ rfl hn hok ht hw
  case bvSdiv => exact chainB_sdiv hQ rfl hn hok ht hw
  case bvSmod => exact chainB_smod hQ rfl hn hok ht hw
  case eq => exact chainB_eq hQ rfl hn hok ht hw
  case distinct => exact chainB_distinct hQ rfl hn hok ht hw
  case ugt => exact chainB_ugt hQ rfl hn hok ht hw
  case uge => exact chainB_uge hQ rfl hn hok ht hw
  case sgt => exact chainB_sgt hQ rfl hn hok ht hw
  case sge => exact chainB_sge hQ rfl hn hok ht hw
  case ult => exact chainB_ult hQ rfl hn hok ht hw
  case ule => exact chainB_ule hQ rfl hn hok ht hw
  case slt => exact chainB_slt hQ rfl hn hok ht hw
  case sle => exact chainB_sle hQ rfl hn hok ht hw
  case implies => exact chainB_implies hQ rfl hn hok ht hw

end Vbcf.Proof
