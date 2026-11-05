import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Clause2

/-!
# Vbcf proofs: the Clause family, part 3 — `r_resolution`
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf


/-! ## Calling the helpers from a rule -/

section calls
variable {W : World} {X : Ctx} {c0 c : CMem} {prems params : List Nat} {st : VSt}
  {sb : Nat} {s : (KernelState prog State)} {env : Env} {Q : (Post prog State)} {x : Var} {es : List Expr} {rest : Stmt}

/-- `x = cl_lits(st, p, pivot); rest`. -/
theorem WP.rule_cl_lits (h : Holds W s.mem sb c) (hR : RCtx W X c0 prems params c st) (p : Nat)
    (hp : st.lv p) {po : Option Nat} {pw : BitVec 32} (hpw : PivW st po pw)
    {base : Nat} {is : List Nat} (htop : StkTop c st base is)
    (H : evalArgs Vbcf.prog env s.mem es = some [.ptr sb 0, uv (st.id p), .u32 pw] ∧
      ∀ s' r, PushRet W sb X c0 prems params st base is (litsOf st p po) r s' →
        match env.assign s'.mem x (.u32 r) with
        | none => False
        | some env' => WP Vbcf.prog rest Q env' s') :
    WP Vbcf.prog (.seq (.call (some x) "cl_lits" es) rest) Q env s := by
  apply WP.call_seq (cl_lits_spec W sb X c0 c prems params st p po pw base is) H.1
    ⟨rfl, h, hR, hp, hpw, htop⟩
  rintro rv s' ⟨r, rfl, hr⟩
  exact H.2 s' r hr

/-- `cl_erase(st, base, pivot); rest`. -/
theorem WP.rule_cl_erase (h : Holds W s.mem sb c) (hR : RCtx W X c0 prems params c st)
    {po : Option Nat} {pw : BitVec 32} (hpw : PivW st po pw) {base : Nat} {l : List Nat}
    (htop : StkTop c st base l)
    (H : evalArgs Vbcf.prog env s.mem es = some [.ptr sb 0, uv base, .u32 pw] ∧
      ∀ s', EraseRet W sb X c0 c prems params st base (eraseOpt l po) s' →
        WP Vbcf.prog rest Q env s') :
    WP Vbcf.prog (.seq (.call none "cl_erase" es) rest) Q env s := by
  apply WP.seq
  apply WP.call (cl_erase_spec W sb X c0 c prems params st base po pw l)
  rw [H.1]
  exact ⟨⟨rfl, h, hR, hpw, htop⟩, fun rv s' hr => H.2 s' hr⟩

end calls

/-- `a; b` through an intermediate assertion `M` on the normal outcome of `a`. -/
theorem WP.seq_mid {P : Prog} {Q : (Post P State)} {env : Env} {s : (KernelState P State)} {a b : Stmt}
    (M : Env → (KernelState P State) → Prop) (h1 : WP P a (LoopQ M Q) env s)
    (h2 : ∀ env' s', M env' s' → WP P b Q env' s') : WP P (.seq a b) Q env s := by
  apply WP.seq
  refine WP.mono h1 ?_
  intro o env' s' hq
  cases o with
  | normal => exact h2 env' s' hq
  | brk => exact hq.elim
  | ret r => exact hq

theorem cl_mapOpt_snoc {α β : Type} {f : α → Option β} {l : List α} {l' : List β} {a : α} {b : β}
    (h : mapOpt f l = some l') (hb : f a = some b) : mapOpt f (l ++ [a]) = some (l' ++ [b]) := by
  induction l generalizing l' with
  | nil => simp [mapOpt] at h; subst h; simp [mapOpt, hb]
  | cons x l ih =>
    simp only [mapOpt] at h
    rcases hx : f x with _ | y <;> rcases hl : mapOpt f l with _ | ys <;> simp [hx, hl] at h
    subst h
    simp [mapOpt, hx, ih hl]

/-- The clause on the stack once the literals of the first premise are there. -/
def clL0 (st : St) (pols : List Nat) (p0 : Nat) (rest lits : List Nat) (lit : Nat) : List Nat :=
  match lits with
  | [] => litsOf st p0 (clPiv0 st pols 0 lit)
  | _ :: _ => clRcur st pols p0 rest lits

theorem clRcur_snoc {st : St} {pols : List Nat} {p0 : Nat} {rest lits : List Nat} {lit : Nat}
    (h : lits.length < rest.length) :
    clRcur st pols p0 rest (lits ++ [lit]) =
      clRstep st pols lits.length rest[lits.length] lit (clL0 st pols p0 rest lits lit) := by
  cases lits with
  | nil =>
    cases rest with
    | nil => simp at h
    | cons r rest => simp [clRcur, clL0, clRfold]
  | cons l0 ls =>
    simp only [List.cons_append, clRcur, clL0]
    rw [← List.cons_append, clRfold_snoc h]
    simp

/-- `a; b` through an assertion `M env` on the normal outcome of `a`, where `env` is the
environment before `a`. -/
theorem WP.seq_mid_env {P : Prog} {Q : (Post P State)} {env : Env} {s : (KernelState P State)} {a b : Stmt}
    (M : Env → Env → (KernelState P State) → Prop) (h1 : WP P a (LoopQ (M env) Q) env s)
    (h2 : ∀ env' s', M env env' s' → WP P b Q env' s') : WP P (.seq a b) Q env s :=
  WP.seq_mid (M env) h1 h2

/-- After choosing the pivots: `piv0`, `piv1` hold the words of `po0`, `po1`. -/
def PivMid (s : (KernelState prog State)) (st : VSt) (po0 po1 : Option Nat) (env0 env' : Env) (s' : (KernelState prog State)) : Prop :=
  s' = s ∧ ∃ w0 w1, env' = (env0.set "piv0" (.u32 w0)).set "piv1" (.u32 w1) ∧
    PivW st po0 w0 ∧ PivW st po1 w1

/-- After the literals of the first premise are on the stack (step 0) or not (later steps). -/
def LitsMid (W : World) (sb : Nat) (X : Ctx) (c0 : CMem) (prems params : List Nat) (st : VSt)
    (L : List Nat) (env0 env' : Env) (s' : (KernelState prog State)) : Prop :=
  ∃ c' a, env' = env0.set "ok" (.u32 a) ∧ Holds W s'.mem sb c' ∧
    RCtx W X c0 prems params c' st ∧ StkTop c' st 0 L

theorem cw_eq_one {n : Nat} (h : n < 4294967296) : (BitVec.ofNat 32 n = 1#32) ↔ n = 1 := by
  rw [show (1#32 : BitVec 32) = BitVec.ofNat 32 1 from rfl, uv_inj h (by omega)]

/-- Loop invariant of `r_resolution`: `k` steps done, the clause `clRcur … lits` on the stack. -/
def ResInv (W : World) (sb : Nat) (X : Ctx) (c0 : CMem) (st : VSt) (p0 : Nat) (rest params : List Nat)
    (pw : Nat) : Env → (KernelState prog State) → Prop := fun env s' =>
  ∃ (c' : CMem) (k : Nat) (lits : List Nat) (a1 a2 a3 a4 a5 a6 : BitVec 32),
    env = [("st", .ptr (.struct "ck"), .ptr sb 0), ("np", .u32, uv (rest.length + 1)),
      ("na", .u32, uv params.length), ("n", .u32, uv rest.length), ("pw", .u32, uv pw),
      ("i", .u32, uv k), ("lit", .u32, .u32 a1), ("nl", .u32, .u32 a2), ("piv0", .u32, .u32 a3),
      ("piv1", .u32, .u32 a4), ("base", .u32, .u32 0#32), ("mid", .u32, .u32 a5),
      ("ok", .u32, .u32 a6), ("len", .u32, .u32 0#32), ("r", .u32, .u32 0#32)] ∧
    Holds W s'.mem sb c' ∧ RCtx W X c0 (p0 :: rest) params c' st ∧ k ≤ rest.length ∧
    lits.length = k ∧ mapOpt X.ei ((params.drop pw).take k) = some lits ∧
    StkTop c' st 0 (clRcur st (params.take pw) p0 rest lits)

theorem r_resolution_spec :
    RuleSpec (State := State) "r_resolution" (fun X st pr pa => ruleResolution X.bi X.ei st pr pa) := by
  rule_begin rResolution
  rcases prems with _ | ⟨p0, rest⟩
  · rule_guard
  rule_guard
  intro hnp2
  have hlen : rest.length + 1 ≤ 255 := by simpa using hnp
  have hn1 : 1 ≤ rest.length := by omega
  clear hnp hnp2
  rule_assign [cw_sub]
  rule_assign [cw_div]
  rule_guard
  intro hna'
  rule_assign [hsp]
  generalize hpw : (rest.length + 31) / 32 = pw at hna' ⊢
  apply WP.loop_seq (ResInv W sb X c st p0 rest params pw)
  · exact ⟨c, 0, [], _, _, _, _, _, _, rfl, h, hR, by omega, rfl, by simp [mapOpt],
      StkTop.nil (by simp [hsp])⟩
  clear h hR
  rintro env s' ⟨c', k, lits, a1, a2, a3, a4, a5, a6, rfl, h, hR, hk, hlk, hmap, htop⟩
  rule_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · have hkl : k = rest.length := by omega
    subst hkl
    have hres : ruleResolution X.bi X.ei st (p0 :: rest) params =
        mkClause X.bi st (clRcur st (params.take pw) p0 rest lits) := by
      obtain ⟨l0, ls, rfl⟩ : ∃ l0 ls, lits = l0 :: ls := by
        cases lits with
        | nil => simp at hlk; omega
        | cons l0 ls => exact ⟨l0, ls, rfl⟩
      have hdrop : (params.drop pw).take rest.length = params.drop pw :=
        List.take_of_length_le (by rw [List.length_drop]; omega)
      rw [hdrop] at hmap
      unfold ruleResolution
      simp only [polWords, hpw]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), hmap]
      dsimp only
      rw [clRfold_eq (by simp at hlk ⊢; omega)]
      rfl
    generalize clRcur st (params.take pw) p0 rest lits = res at htop hres
    have hsp' : c'.k.sp = BitVec.ofNat 32 res.length := by
      rw [← bv_ofNat_toNat c'.k.sp, htop.1, Nat.zero_add]
    have hrl : res.length ≤ 2147483648 := by
      have e1 := hR.sp_lt
      have e2 := htop.1
      simp only [maxPool] at e1
      omega
    rule_assign [hsp']
    apply WP.ite_seq
    rule_simp [uv_eq_zero_iff, cw_eq_one]
    refine ⟨fun h0 => ?_, fun h0 => ?_⟩
    · rule_ret
      exact hR.ret h hR.ff_lt (by rw [hres, h0]; simp [mkClause, st.lt hR.ff_lt])
    apply WP.ite_seq
    rcases res with _ | ⟨l, _ | ⟨l2, rs⟩⟩
    · simp at h0
    all_goals simp only [List.length_cons, List.length_nil] at hrl
    · have hstk := hR.stk_eq h (by rw [hsp']; simp)
      have hc := htop.cell (j := 0) (by simp)
      rule_simp [hstk, rd_u32 hc, uv_eq_zero_iff, cw_eq_one]
      rule_ret [hstk, rd_u32 hc]
      refine hR.ret h (f := l) (htop.lt_size (j := 0) (by simp)) ?_
      rw [hres]; simp [mkClause]
    · rule_simp [uv_eq_zero_iff, cw_eq_one]
      apply WP.rule_mkn mkn_specT h hR .disj 65#32 0 (l :: l2 :: rs) htop.2 (by have := htop.1; omega)
      refine ⟨by rule_simp, ?_⟩
      intro s' c'' r h hB
      rule_simp
      rule_ret
      exact hB.ret h (fun st' i hP => by rw [hres]; simpa [mkClause, mkDisj] using hP)
  have hq : pw + k < params.length := by omega
  have hpar := hR.par_lt hq
  apply WP.rule_expr_at expr_at_spec' h hR params[pw + k] hpar
  refine ⟨by rule_simp, ?_⟩
  intro r hE
  rule_simp
  rule_guard
  intro hne
  obtain ⟨li, hei, hli, rfl⟩ := hE.ok hne
  apply WP.rule_find_not find_not_spec h hR li hli
  refine ⟨by rule_simp, ?_⟩
  intro nl s' wk er h hF
  have hR := hR.wev (wk := wk) (er := er) (vl := c'.k.val)
  have htop : StkTop (c'.wev wk er c'.k.val) st 0 (clRcur st (params.take pw) p0 rest lits) := htop
  rule_simp
  -- out of work: reject
  rule_guard
  intro herr
  have hF := hF (by simpa using herr)
  generalize c'.wev wk er c'.k.val = c' at h hR htop
  have hw := hR.par_lt (j := k / 32) (by omega)
  have htp := cl_testPol (params := params) (i := k) (pw := pw) (by omega) (by omega)
  apply WP.seq_mid_env (PivMid s' st (clPiv0 st (params.take pw) k li) (clPiv1 st (params.take pw) k li))
  · apply WP.ite
    rule_simp [cw_div, cw_mod, cw_shr hw, cw_and1, (by omega : k % 32 < 32)]
    refine ⟨fun hpol => ?_, fun hpol => ?_⟩
    · apply WP.assign_seq
      rule_simp
      apply WP.assign_loop
      rule_simp
      refine ⟨rfl, _, _, rfl, ?_, ?_⟩
      · simp only [clPiv0, htp, hpol, decide_true, ite_true]
        exact Or.inl ⟨hli, rfl⟩
      · simp only [clPiv1, htp, hpol, decide_true, ite_true]
        exact PivW.of_find hF
    · apply WP.assign_seq
      rule_simp
      apply WP.assign_loop
      rule_simp
      refine ⟨rfl, _, _, rfl, ?_, ?_⟩
      · simp only [clPiv0, htp, hpol]
        exact PivW.of_find hF
      · simp only [clPiv1, htp, hpol]
        exact Or.inl ⟨hli, rfl⟩
  rintro env' s2 ⟨rfl, w0, w1, rfl, hw0, hw1⟩
  rule_simp
  apply WP.seq_mid_env (LitsMid W sb X c (p0 :: rest) params st
    (clL0 st (params.take pw) p0 rest lits li))
  · apply WP.ite
    rule_simp
    refine ⟨fun hk0 => ?_, fun hk0 => ?_⟩
    · -- step 0: the literals of the first premise
      subst hk0
      have hl0 : lits = [] := List.eq_nil_of_length_eq_zero hlk
      subst hl0
      have hp0 := hR.prem_lt (j := 0) (by simp)
      simp only [List.getElem_cons_zero] at hp0
      apply WP.rule_cl_lits h hR p0 hp0 hw0 htop
      refine ⟨by rule_simp [hR.rd_prem (j := 0) (by simp)], ?_⟩
      intro s3 r ⟨c3, h3, hR3, hcase⟩
      rule_simp
      apply WP.ite
      rule_simp
      rcases hcase with rfl | ⟨rfl, htop3⟩
      · simp
        exact WP.rule_fail h3
      · simp
        apply WP.skip
        exact ⟨c3, _, rfl, h3, hR3, by simpa [clL0, clRcur] using htop3⟩
    · apply WP.skip
      obtain ⟨l0, ls, rfl⟩ : ∃ l0 ls, lits = l0 :: ls := by
        cases lits with
        | nil => simp at hlk; omega
        | cons l0 ls => exact ⟨l0, ls, rfl⟩
      exact ⟨c', a6, by simp [Env.set], h, hR, htop⟩
  rintro env' s3 ⟨c3, a7, rfl, h, hR, htop3⟩
  rule_simp
  -- pay for the scan
  apply WP.rule_spend h hR
  rule_simp
  intro s3' wk3 er3 ok3 h _
  have hR := hR.wev (wk := wk3) (er := er3) (vl := c3.k.val)
  have htop3 := htop3.wev (wk := wk3) (er := er3) (vl := c3.k.val)
  rule_guard
  intro hok3
  apply WP.rule_cl_erase h hR hw0 htop3
  refine ⟨by rule_simp, ?_⟩
  rintro s4 ⟨c4, h, hR, htop4, -⟩
  have hsp4 : c4.k.sp = BitVec.ofNat 32
      (eraseOpt (clL0 st (params.take pw) p0 rest lits li) (clPiv0 st (params.take pw) k li)).length := by
    rw [← bv_ofNat_toNat c4.k.sp, htop4.1, Nat.zero_add]
  rule_assign [hsp4]
  have hq1 : st.lv rest[k] := by
    have := hR.prem_lt (j := k + 1) (by simp; omega)
    simpa using this
  apply WP.rule_cl_lits h hR rest[k] hq1 hw1 htop4
  refine ⟨by rule_simp [hR.rd_prem (j := k + 1) (by simp; omega)], ?_⟩
  intro s5 r ⟨c5, h, hR, hcase⟩
  rule_simp
  rule_guard
  intro hr0
  rcases hcase with rfl | ⟨rfl, htop5⟩
  · simp at hr0
  have hsplit := htop5.split
  rw [Nat.zero_add] at hsplit
  -- pay for the scan
  apply WP.rule_spend h hR
  rule_simp
  intro s5' wk5 er5 ok5 h _
  have hR := hR.wev (wk := wk5) (er := er5) (vl := c5.k.val)
  have hsplit := hsplit.wev (wk := wk5) (er := er5) (vl := c5.k.val)
  rule_guard
  intro hok5
  apply WP.rule_cl_erase h hR hw1 hsplit
  refine ⟨by rule_simp, ?_⟩
  rintro s6 ⟨c6, h, hR, htop6, hlow6⟩
  apply WP.assign_loop
  rule_simp
  refine ⟨c6, k + 1, lits ++ [li], _, _, _, _, _, _, rfl, h, hR, by omega, by simp [hlk], ?_, ?_⟩
  · rw [List.take_add_one, List.getElem?_drop, List.getElem?_eq_getElem hq]
    exact cl_mapOpt_snoc hmap hei
  · have e := clRcur_snoc (st := st) (pols := params.take pw) (p0 := p0) (lit := li)
      (show lits.length < rest.length by omega)
    simp only [hlk] at e
    rw [e, clRstep]
    refine StkTop.join ((htop5.2.append_left).frame (fun j hj => ?_)) (by simpa using htop6)
    exact hlow6 j (by simpa using hj)

end Vbcf.Proof
