import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Eval2

/-!
# Vbcf proofs: the Eval family, part 3 — the groups of `cval`
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

theorem Holds.ldPool {W : World} {m : Mem} {sb : Nat} {c : CMem} {pb : Nat}
    (h : Holds W m sb c) (hp : c.k.pool = some (pb, 0)) (k : Nat) : m.loadArr pb k = rd c.pool k :=
  h.loadArr (a := .pool) hp k

open Lean in
/-- `cv_simp [facts]`: evaluate C expressions in `cval`'s body.  Uses `h` (the current
`Holds`), `hs`, `hc` (the `CoreInv`), `hpool` (the pool pointer). -/
macro "cv_simp" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let h := mkIdent `h
  let hs := mkIdent `hs
  let hc := mkIdent `hc
  let hpool := mkIdent `hpool
  `(tactic| simp (disch := rule_disch) [EmbC.evalE, EmbC.evalBin, EmbC.evalArith, EmbC.evalCast,
      EmbC.evalArgs, EmbC.Env.get, EmbC.Env.ty, EmbC.Env.set, EmbC.Env.assign, EmbC.Val.toIdx,
      ofBool_eq, land_some, land_some', lor_some, lor_some', cvEnv,
      HasCK.ld_pool $hs (Holds.ck $h), HasCK.ld_val $hs (Holds.ck $h),
      Holds.ldPool $h $hpool, $hpool:term,
      VInv.id_toNat $hc, VInv.id_mod $hc,
      VInv.id_add_toNat $hc, VInv.id_add_mod $hc,
      VInv.id_add2_toNat $hc, VInv.id_add2_mod $hc,
      uv_inj, uv_le, uv_lt, uv_toNat, mod32, uv_add, $ts,*])

macro "cv_simp" : tactic => `(tactic| cv_simp [])

theorem cv_memoVal_list {st : St} (hok : TysOK st.pool st.tys) {i : Nat} {op : Op} {args : Array Nat}
    (hn : st.pool[i]? = some ⟨op, args⟩) (hl : ¬ IsLeaf op) (hz : ∀ w, op ≠ .bvSize w)
    {vs : List Bcf.Val} (hvs : mapOpt (memoVal st) args.toList = some vs) :
    memoVal st i = some (Op.eval (fun _ => 0) op vs) := by
  rw [cv_memoVal_args hok hn (fun w id h => hl (by simp only at h; subst h; simp [IsLeaf, isLeaf]))
    (fun id h => hl (by simp only at h; subst h; simp [IsLeaf, isLeaf])) hz]
  simp [hvs]

theorem cv_memoVal_3 {st : St} (hok : TysOK st.pool st.tys) {i : Nat} {op : Op} {a b e : Nat}
    (hn : st.pool[i]? = some ⟨op, #[a, b, e]⟩) (hl : ¬ IsLeaf op) (hz : ∀ w, op ≠ .bvSize w)
    {v1 v2 v3 : Bcf.Val} (h1 : memoVal st a = some v1) (h2 : memoVal st b = some v2)
    (h3 : memoVal st e = some v3) :
    memoVal st i = some (Op.eval (fun _ => 0) op [v1, v2, v3]) :=
  cv_memoVal_list hok hn hl hz (by simp [mapOpt, h1, h2, h3])

theorem cv_memoVal_2 {st : St} (hok : TysOK st.pool st.tys) {i : Nat} {op : Op} {a b : Nat}
    (hn : st.pool[i]? = some ⟨op, #[a, b]⟩) (hl : ¬ IsLeaf op) (hz : ∀ w, op ≠ .bvSize w)
    {v1 v2 : Bcf.Val} (h1 : memoVal st a = some v1) (h2 : memoVal st b = some v2) :
    memoVal st i = some (Op.eval (fun _ => 0) op [v1, v2]) :=
  cv_memoVal_list hok hn hl hz (by simp [mapOpt, h1, h2])

theorem cv_memoVal_1 {st : St} (hok : TysOK st.pool st.tys) {i : Nat} {op : Op} {a : Nat}
    (hn : st.pool[i]? = some ⟨op, #[a]⟩) (hl : ¬ IsLeaf op) (hz : ∀ w, op ≠ .bvSize w)
    {v1 : Bcf.Val} (h1 : memoVal st a = some v1) :
    memoVal st i = some (Op.eval (fun _ => 0) op [v1]) :=
  cv_memoVal_list hok hn hl hz (by simp [mapOpt, h1])

/-- `st->val = e; return w;`, the end of every group. -/
theorem WP.cv_finish {W : World} {sb : Nat} {c0 : CMem} {st : VSt} {i : Nat} {Q : (Post prog State)}
    {env : Env} {s : (KernelState prog State)} {wk er : BitVec 32} {vl : BitVec 64} {e : Expr} {w : BitVec 32}
    {x' : BitVec 64}
    (hQ : CvQ W sb c0 st i Q) (h : Holds W s.mem sb (c0.wev wk er vl))
    (hst : env.get "st" = some (.ptr sb 0)) (hwv : env.get "w" = some (.u32 w))
    (he : evalE Vbcf.prog env s.mem e = some (.u64 x'))
    (hsem : w ≠ 0#32 → w ≠ 4294967295#32 → ∃ v, memoVal st i = some v ∧ CvRep w x' v) :
    WP Vbcf.prog (.seq (.setField (.var "st") "val" e) (.ret (some (.var "w")))) Q env s := by
  have hs := prog_ck
  apply WP.seq
  apply WP.ck_setVal hs h rfl
  simp only [evalE, hst, he]
  refine ⟨trivial, trivial, fun s' h' => ?_⟩
  apply WP.ret
  simp only [evalE, hwv]
  exact hQ _ _ _ _ _ _ h' hsem

theorem grpI_spec {d : BitVec 32} (IH : ∀ d' : BitVec 32, d'.toNat < d.toNat → CvalSpecD (State := State) d')
    (hd : d ≠ 0#32) {W : World} {sb : Nat} {c : CMem} {posOf : Nat → Nat} {st : VSt} {i : Nat}
    {n : Node} {t : Bcf.Ty} {hdr code nn par lo hi w cw i0 : BitVec 32}
    {x y z m sbv acc : BitVec 64} {s : (KernelState prog State)} {Q : (Post prog State)} {pb : Nat}
    (h : Holds W s.mem sb c) (hc : VInv posOf c st) (hpool : c.k.pool = some (pb, 0))
    (hn : st.pool[i]? = some n) (hop : n.op = .boolIte ∨ ∃ k, n.op = .bvIte k)
    (ht : st.tys[i]? = some t) (hw : CvW t w) (hQ : CvQ W sb c st i Q) (h_lv : st.lv i := by vlv) :
    WP Vbcf.prog cvI Q
      (cvEnv sb (BitVec.ofNat 32 (st.id i)) d hdr code nn par lo hi w cw i0 x y z m sbv acc) s := by
  have hi := h_lv
  have hs := prog_ck
  have hdl : (d - 1#32).toNat < d.toNat := by
    have : d.toNat ≠ 0 := fun e => hd (BitVec.eq_of_toNat_eq (by simpa using e))
    rw [BitVec.toNat_sub]; simp; omega
  obtain ⟨a, b, e, hn', ha, hb, he, hl⟩ : ∃ a b e, st.pool[i]? = some ⟨n.op, #[a, b, e]⟩ ∧
      st.lv a ∧ st.lv b ∧ st.lv e ∧ ¬ IsLeaf n.op := by
    rcases hop with h1 | ⟨k, h1⟩
    · obtain ⟨a, b, e, rfl, ha, hb, he⟩ := hc.args3 hn h1
      exact ⟨a, b, e, hn, ha, hb, he, by rw [h1]; simp [IsLeaf, isLeaf]⟩
    · obtain ⟨a, b, e, rfl, ha, hb, he⟩ := hc.args3 hn h1
      exact ⟨a, b, e, hn, ha, hb, he, by rw [h1]; simp [IsLeaf, isLeaf]⟩
  have hrd := hc.rd3 hn' hl
  simp only [cvI, Stmt.block]
  apply WP.cval_child (IH _ hdl) h hc ha (by cv_simp [hrd])
  intro r1 wk1 er1 vl1 s1 h1 hv1
  cv_simp
  apply WP.cw_guard (r := r1) hQ h1 (by cv_simp)
  intro hr1 hr1'
  replace h := h1
  apply WP.assign_seq; cv_simp
  apply WP.cval_child (IH _ hdl) h hc.wev hb (by cv_simp [hrd])
  intro r2 wk2 er2 vl2 s2 h2 hv2
  simp only [wev_wev] at h2
  cv_simp
  apply WP.cw_guard (r := r2) hQ h2 (by cv_simp)
  intro hr2 hr2'
  replace h := h2
  apply WP.assign_seq; cv_simp
  apply WP.cval_child (IH _ hdl) h hc.wev he (by cv_simp [hrd])
  intro r3 wk3 er3 vl3 s3 h3 hv3
  simp only [wev_wev] at h3
  cv_simp
  apply WP.cw_guard (r := r3) hQ h3 (by cv_simp)
  intro hr3 hr3'
  replace h := h3
  apply WP.assign_seq; cv_simp
  have hfin : ∀ zf : BitVec 64, zf = (if vl1 ≠ 0#64 then vl2 else vl3) → ∀ env s',
      env.get "w" = some (.u32 w) → Holds W s'.mem sb (c.wev wk3 er3 zf) →
      WP Vbcf.prog (.ret (some (.var "w"))) Q env s' := by
    intro zf hzf env s' henv h'
    apply WP.ret
    simp only [evalE, henv]
    refine hQ _ _ _ _ _ _ h' (fun _ _ => ?_)
    obtain ⟨v1, hm1, hr1⟩ := hv1 hr1 hr1'
    obtain ⟨v2, hm2, hr2⟩ := hv2 hr2 hr2'
    obtain ⟨v3, hm3, hr3⟩ := hv3 hr3 hr3'
    have hz : ∀ w, n.op ≠ .bvSize w := by
      intro w hw; rcases hop with h1 | ⟨k, h1⟩ <;> rw [h1] at hw <;> cases hw
    have hm := cv_memoVal_3 hc.ok.tys hn' hl hz hm1 hm2 hm3
    refine ⟨_, hm, ?_⟩
    have hty := cv_memoVal_ty hc.ok.tys hm
    rw [ht] at hty
    rw [hzf]
    exact cvsem_ite hop hr1 hr2 hr3 hty hw
  by_cases hx : vl1 = 0#64
  · apply WP.ite_seq; cv_simp [hx]
    apply WP.seq; apply WP.ck_setVal hs h rfl; cv_simp
    intro s' h'
    exact hfin vl3 (by simp [hx]) _ _ (by simp [Env.get]) h'
  · apply WP.ite_seq; cv_simp [hx]
    apply WP.assign; cv_simp [LoopQ]
    apply WP.seq; apply WP.ck_setVal hs h rfl; cv_simp
    intro s' h'
    exact hfin vl2 (by simp [hx]) _ _ (by simp [Env.get]) h'

end Vbcf.Proof
