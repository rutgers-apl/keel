import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Eval9

/-!
# Vbcf proofs: the Eval family, part 10 — the rules `r_evaluate` and `r_distinct_values`
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-- `if (c) { a } else { b } rest`: both branches continue with `rest`. -/
theorem WP.cv_ite2 {P : Prog} {Q : (Post P State)} {env : Env} {s : (KernelState P State)} {c : Expr} {a b rest : Stmt}
    (H : match evalE P env s.mem c with
      | some (.u32 v) =>
        (v ≠ 0 → WP P a (LoopQ (fun env' s' => WP P rest Q env' s') Q) env s) ∧
        (v = 0 → WP P b (LoopQ (fun env' s' => WP P rest Q env' s') Q) env s)
      | _ => False) :
    WP P (.seq (.ite c a b) rest) Q env s := by
  apply WP.seq
  apply WP.ite
  split at H
  · rename_i v hv
    rw [hv]
    refine ⟨fun hne => WP.mono (H.1 hne) ?_, fun he => WP.mono (H.2 he) ?_⟩ <;>
    · intro o env' s' hq
      cases o with
      | normal => exact hq
      | brk => exact hq.elim
      | ret r => exact hq
  · exact H.elim

/-- A builder call as the last statement of an `if` branch (cf. `WP.rule_build`). -/
theorem WP.cv_build_end {W : World} {X : Ctx} {c0 c : CMem} {prems params : List Nat} {st : VSt}
    {sb : Nat} {s : (KernelState prog State)} {env : Env} {Q : (Post prog State)} {P P' : St → Nat → Prop}
    {f : String} {args : List Expr} {x : Var} {vs : List EmbC.Val}
    {pre : List EmbC.Val → (KernelState prog State) → Prop}
    {post : List EmbC.Val → (KernelState prog State) → Option EmbC.Val → (KernelState prog State) → Prop}
    (hspec : FnSpec (State := State) Vbcf.prog f pre post)
    (hR : RCtx W X c0 prems params c st)
    (hpost : ∀ rv s', post vs s rv s' → BuildPost W sb c X.posOf st.cs P' rv s')
    (htr : ∀ c' cs' x, CoreInv X.posOf c' cs' → P' cs' x →
      ∃ (st' : VSt) (i : Nat), P st'.toSt i ∧ st'.lv i ∧ st'.id i = offs cs'.pool x ∧
        VExt st st' ∧ VInv X.posOf c' st')
    (hargs : evalArgs Vbcf.prog env s.mem args = some vs) (hpre : pre vs s)
    (H : ∀ s' c' r, Holds W s'.mem sb c' → Built W X c0 prems params c st P c' r →
        match env.assign s'.mem x (.u32 r) with
        | none => False
        | some env' => Q .normal env' s') :
    WP Vbcf.prog (.call (some x) f args) Q env s := by
  apply WP.call hspec
  rw [hargs]
  refine ⟨hpre, fun rv s' hp => ?_⟩
  obtain ⟨c', r, rfl, h', hfr, hcase⟩ := hpost rv s' hp
  refine H s' c' r h' ?_
  rcases hcase with ⟨hr, -⟩ | ⟨cs', x', hPi, hc, hri, -⟩
  · exact Or.inl hr
  · obtain ⟨st', i, hP, hi, hid, he, hv⟩ := htr c' cs' x' hc hPi
    exact Or.inr ⟨st', i, hP, hR.after_build h' hfr hv he, he, ⟨hfr.stk, hfr.sp⟩, hi,
      by rw [hid]; exact id_of_toNat hri⟩

theorem r_evaluate_spec :
    RuleSpec (State := State) "r_evaluate" (fun X st pr pa => ruleEvaluate X.ei st pr pa) := by
  rule_begin rEvaluate
  rule_arity rfl ⟨x, rfl⟩
  have hx := hR.params1
  apply WP.rule_expr_at expr_at_spec' h hR x hx
  refine ⟨by rule_simp, ?_⟩
  intro r her
  rule_simp
  rule_guard
  intro hne
  obtain ⟨e, hea, he, rfl⟩ := her.ok hne
  apply WP.call_seq (cval_spec 32#32 W sb c X.posOf st e) (by rule_simp) ⟨rfl, h, hR.core, he⟩
  rintro rv s' ⟨w, wk, er, vl, rfl, h', hv⟩
  replace hR := hR.wev (wk := wk) (er := er) (vl := vl)
  replace h := h'
  rule_simp
  rule_guard
  intro hw0 hwN
  obtain ⟨v, hm, hvr⟩ := hv hw0 hwN
  apply WP.cv_ite2
  rule_simp
  rcases hvr.cases with ⟨b, rfl⟩ | ⟨k, xk, rfl⟩
  · have hw100 : w = 100#32 := hvr.1
    refine ⟨fun _ => ?_, fun h0 => absurd hw100 (by simpa using h0)⟩
    apply WP.cv_build_end (P := fun st' i => pushNode st ⟨.boolVal b, #[]⟩ = some (st', i))
      (mk0_bool_specT W sb (c.wev wk er vl) X.posOf st.cs b) hR (fun _ _ hp => hp)
      (fun c' cs' x hc hp => push_htr hR (n := ⟨.boolVal b, #[]⟩) (by simp) c' cs' x hc
        (by rw [ren_leaf]; exact hp))
      (by rule_simp; rw [hvr.2]; cases b <;> rfl) ⟨rfl, h, hR.core.cinv⟩
    intro s2 c2 lit h hB
    rule_simp
    simp only [LoopQ]
    rule_guard
    intro hne
    obtain ⟨st', l, hP, hR, hext, hstk, hl, rfl⟩ := hB.ok hne
    rw [← hext.id he]
    apply WP.rule_mk_eq mk_eq_specT h hR e l (hext.lt he) hl
    refine ⟨by rule_simp, ?_⟩
    intro s3 c3 r h hB
    rule_simp
    rule_ret
    exact hB.ret h (fun st2 i2 hP2 => by simp [ruleEvaluate, hea, hm, litOf, hP, hP2])
  · obtain ⟨hwk, hk1, hk64, hvx⟩ := hvr
    have hw100 : ¬ w = 100#32 := by
      intro h0; rw [h0] at hwk; simp at hwk; omega
    refine ⟨fun h0 => absurd (by simpa using h0) hw100, fun _ => ?_⟩
    have hfit : w.toNat ≤ 32 → vl.toNat < 2 ^ 32 := by
      intro h32
      rw [hvx]
      exact Nat.lt_of_lt_of_le xk.isLt (Nat.pow_le_pow_right (by decide) (by omega))
    apply WP.cv_build_end (P := fun st' i => pushNode st ⟨.bvVal w.toNat vl.toNat, #[]⟩ = some (st', i))
      (mkval_lt_specT W sb (c.wev wk er vl) X.posOf st.cs w vl) hR
      (fun _ _ hp => hp) (fun c' cs' x hc hp => push_htr hR (n := ⟨.bvVal w.toNat vl.toNat, #[]⟩)
        (by simp) c' cs' x hc (by rw [ren_leaf]; exact hp)) (by rule_simp) ⟨rfl, h, hR.core.cinv, hfit⟩
    intro s2 c2 lit h hB
    rule_simp
    simp only [LoopQ]
    rule_guard
    intro hne
    obtain ⟨st', l, hP, hR, hext, hstk, hl, rfl⟩ := hB.ok hne
    rw [← hext.id he]
    apply WP.rule_mk_eq mk_eq_specT h hR e l (hext.lt he) hl
    refine ⟨by rule_simp, ?_⟩
    intro s3 c3 r h hB
    rule_simp
    rule_ret
    rw [hwk, hvx] at hP
    exact hB.ret h (fun st2 i2 hP2 => by simp [ruleEvaluate, hea, hm, litOf, hP, hP2])

theorem cv_distinct_lean {X : Ctx} {st : St} {x0 x1 a b : Nat} {na nb : Node} {posOf : Nat → Nat}
    (hea : X.ei x0 = some a) (heb : X.ei x1 = some b) (hna : st.pool[a]? = some na)
    (hnb : st.pool[b]? = some nb) (hok : PoolOK st) (hfa : Fits posOf na) (hfb : Fits posOf nb)
    (hcode : (∀ (x x_1 : Nat), ¬na.op = Op.bvVal x x_1) → ¬na.op = Op.boolVal false →
      na.op = Op.boolVal true)
    (hcode2 : opC nb.op = opC na.op)
    (hpar : ∀ (x x_1 : Nat), na.op = Op.bvVal x x_1 →
      BitVec.ofNat 32 (hdrW na) >>> 16 = BitVec.ofNat 32 (hdrW nb) >>> 16)
    (hab : ¬a = b) {st' st2 : St} {i i2 : Nat} (hP : Bcf.mkEq st a b = some (st', i))
    (hP2 : Bcf.mkNot st' i = some (st2, i2)) :
    ruleDistinctValues X.ei st [] [x0, x1] = some (st2, i2) := by
  have hne : na ≠ nb := fun e => hab (hok.nodup a b na hna (e ▸ hnb))
  have hla := cv_leaf_args hok hna
  have hlb := cv_leaf_args hok hnb
  obtain ⟨opa, argsa⟩ := na
  obtain ⟨opb, argsb⟩ := nb
  simp only at hcode hcode2 hpar hla hlb hne
  by_cases hbv : ∃ w v, opa = .bvVal w v
  · obtain ⟨w1, v1, rfl⟩ := hbv
    have hla' := hla (by simp [IsLeaf, isLeaf]); subst hla'
    obtain ⟨w2, v2, rfl⟩ := opC_bvVal_iff.mp (by rw [hcode2]; rfl)
    have hlb' := hlb (by simp [IsLeaf, isLeaf]); subst hlb'
    have hp := hpar w1 v1 rfl
    rw [cv_hdr_par hfa, cv_hdr_par hfb] at hp
    have h1 := hfa.lo; have h2 := hfb.lo; have h3 := hfa.hi; have h4 := hfb.hi
    simp only [opLo, opHi] at hp h1 h2 h3 h4
    rw [bv_ofNat_inj (by omega) (by omega)] at hp
    have hw : w1 = w2 := by omega
    subst hw
    have hv : v1 ≠ v2 := fun e => hne (by rw [e])
    simp [ruleDistinctValues, hea, heb, St.node, hna, hnb, hv, hP, hP2]
  · have hb : ∃ b1, opa = .boolVal b1 := by
      by_cases h0 : opa = .boolVal false
      · exact ⟨false, h0⟩
      · exact ⟨true, hcode (fun x y e => hbv ⟨x, y, e⟩) h0⟩
    obtain ⟨b1, rfl⟩ := hb
    have hla' := hla (by simp [IsLeaf, isLeaf]); subst hla'
    obtain ⟨b2, rfl⟩ := opC_boolVal_iff.mp (by rw [hcode2]; rfl)
    have hlb' := hlb (by simp [IsLeaf, isLeaf]); subst hlb'
    have hv : b1 ≠ b2 := fun e => hne (by rw [e])
    simp [ruleDistinctValues, hea, heb, St.node, hna, hnb, hv, hP, hP2]

theorem r_distinct_values_spec :
    RuleSpec (State := State) "r_distinct_values" (fun X st pr pa => ruleDistinctValues X.ei st pr pa) := by
  rule_begin rDistinctValues
  rule_arity rfl ⟨x0, x1, rfl⟩
  have ⟨hx0, hx1⟩ := hR.params2
  apply WP.rule_expr_at expr_at_spec' h hR x0 hx0
  refine ⟨by rule_simp, ?_⟩
  intro r her
  rule_simp
  rule_guard
  intro hne
  obtain ⟨a, hea, ha, rfl⟩ := her.ok hne
  apply WP.rule_expr_at expr_at_spec' h hR x1 hx1
  refine ⟨by rule_simp, ?_⟩
  intro r her
  rule_simp
  rule_guard
  intro hne
  obtain ⟨b, heb, hb, rfl⟩ := her.ok hne
  obtain ⟨na, hna⟩ := node_of_lv ha
  obtain ⟨nb, hnb⟩ := node_of_lv hb
  rule_assign [hR.core.rdHdr hna]
  rule_guard
  intro hcode
  rule_guard [hR.core.rdHdr hnb]
  intro hcode2
  rule_guard [hR.core.rdHdr hna, hR.core.rdHdr hnb]
  intro hpar
  rule_guard
  intro hab
  have hok0 := hR.core.ok
  have hfa := hR.core.rep.fits _ _ hna
  have hfb := hR.core.rep.fits _ _ hnb
  apply WP.rule_mk_eq mk_eq_specT h hR a b ha hb
  refine ⟨by rule_simp, ?_⟩
  intro s' c' r h hB
  rule_simp
  rule_guard
  intro hne
  obtain ⟨st', i, hP, hR, hext, hstk, hi, rfl⟩ := hB.ok hne
  apply WP.rule_mk_not mk_not_specT h hR i hi
  refine ⟨by rule_simp, ?_⟩
  intro s'' c'' r h hB
  rule_simp
  rule_ret
  exact hB.ret h (fun st2 i2 hP2 => cv_distinct_lean hea heb hna hnb hok0 hfa hfb hcode hcode2 hpar
    hab hP hP2)

end Vbcf.Proof
