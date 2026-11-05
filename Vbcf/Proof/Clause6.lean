import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Clause5

/-!
# Vbcf proofs: the Clause family, part 6 — `r_factoring`
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf


/-- `x = cl_dups(st, p, n, na, mb); rest`. -/
theorem WP.rule_cl_dups {W : World} {X : Ctx} {c0 c : CMem} {prems params : List Nat} {st : VSt}
    {sb : Nat} {s : (KernelState prog State)} {env : Env} {Q : (Post prog State)} {x : Var} {es : List Expr} {rest : Stmt}
    (h : Holds W s.mem sb c) (hR : RCtx W X c0 prems params c st) (p : Nat) {args : Array Nat}
    (hn : st.pool[p]? = some ⟨.disj, args⟩) (mb : Nat) (hmb : mb + args.size ≤ c.k.sp.toNat)
    (hm0 : Marks c mb args.size []) (hp : st.lv p := by vlv)
    (H : evalArgs Vbcf.prog env s.mem es =
        some [.ptr sb 0, uv (st.id p), uv args.size, uv params.length, uv mb] ∧
      ∀ s' r, DupsRet W sb X c0 c prems params st args mb r s' →
        match env.assign s'.mem x (.u32 r) with
        | none => False
        | some env' => WP Vbcf.prog rest Q env' s') :
    WP Vbcf.prog (.seq (.call (some x) "cl_dups" es) rest) Q env s := by
  apply WP.call_seq (cl_dups_spec W sb X c0 c prems params st p args mb) H.1
    ⟨rfl, h, hR, hn, hmb, hm0, hp⟩
  rintro rv s' ⟨r, rfl, hr⟩
  exact H.2 s' r hr

/-- The environment of `r_factoring`. -/
def facEnv (sb : Nat) (st : VSt) (p : Nat) (params : List Nat) (args : Array Nat)
    (kb m i : BitVec 32) (wj wx wok : BitVec 32) : Env :=
  [("st", .ptr (.struct "ck"), .ptr sb 0), ("np", .u32, uv 1), ("na", .u32, uv params.length),
    ("p", .u32, uv (st.id p)), ("n", .u32, uv args.size), ("mb", .u32, .u32 0#32),
    ("kb", .u32, .u32 kb), ("m", .u32, .u32 m), ("i", .u32, .u32 i), ("j", .u32, .u32 wj),
    ("x", .u32, .u32 wx), ("ok", .u32, .u32 wok), ("r", .u32, .u32 0#32)]

/-- First loop: `i` zeros pushed. -/
def FacInv1 (W : World) (sb : Nat) (X : Ctx) (c0 : CMem) (st : VSt) (p : Nat) (params : List Nat)
    (args : Array Nat) : Env → (KernelState prog State) → Prop := fun env s' =>
  ∃ (c' : CMem) (i : Nat) (wok : BitVec 32),
    env = facEnv sb st p params args 0#32 0#32 (BitVec.ofNat 32 i) 0#32 0#32 wok ∧
    Holds W s'.mem sb c' ∧ RCtx W X c0 [p] params c' st ∧ i ≤ args.size ∧
    c'.k.sp.toNat = i ∧ Marks c' 0 i []

/-- Second loop: the kept literals of the first `i` positions are on the stack. -/
def FacInv2 (W : World) (sb : Nat) (X : Ctx) (c0 : CMem) (st : VSt) (p : Nat) (params : List Nat)
    (args : Array Nat) (dups : List Nat) : Env → (KernelState prog State) → Prop := fun env s' =>
  ∃ (c' : CMem) (i : Nat) (wok : BitVec 32),
    env = facEnv sb st p params args (BitVec.ofNat 32 args.size) 0#32 (BitVec.ofNat 32 i) 0#32 0#32 wok ∧
    Holds W s'.mem sb c' ∧ RCtx W X c0 [p] params c' st ∧ i ≤ args.size ∧
    StkTop c' st args.size (clKept args dups i) ∧ Marks c' 0 args.size dups

/-- After the body of the second loop. -/
def FacMid2 (W : World) (sb : Nat) (X : Ctx) (c0 : CMem) (st : VSt) (p : Nat) (params : List Nat)
    (args : Array Nat) (dups : List Nat) (i : Nat) (env0 env' : Env) (s' : (KernelState prog State)) : Prop :=
  ∃ (c' : CMem) (wok : BitVec 32), env' = env0.set "ok" (.u32 wok) ∧
    Holds W s'.mem sb c' ∧ RCtx W X c0 [p] params c' st ∧
    StkTop c' st args.size (clKept args dups (i + 1)) ∧ Marks c' 0 args.size dups

/-- Third loop: the duplicates at the first `i` positions are kept literals. -/
def FacInv3 (sb : Nat) (st : VSt) (p : Nat) (params : List Nat)
    (args : Array Nat) (dups : List Nat) (s : (KernelState prog State)) (wok : BitVec 32) :
    Env → (KernelState prog State) → Prop := fun env s' =>
  s' = s ∧ ∃ (i : Nat) (wj wx : BitVec 32),
    env = facEnv sb st p params args (BitVec.ofNat 32 args.size)
      (BitVec.ofNat 32 (clKept args dups args.size).length) (BitVec.ofNat 32 i) wj wx wok ∧
    i ≤ args.size ∧ ∀ i', i' < i → i' ∈ dups → ∃ a, args[i']? = some a ∧ a ∈ clKept args dups args.size

/-- After the body of the third loop. -/
def FacMid3 (s : (KernelState prog State)) (args : Array Nat) (dups : List Nat) (i : Nat) (hi : i < args.size)
    (env0 env' : Env) (s' : (KernelState prog State)) : Prop :=
  s' = s ∧ (i ∈ dups → args[i] ∈ clKept args dups args.size) ∧
    ∃ wj wx, env' = (env0.set "x" (.u32 wx)).set "j" (.u32 wj)

/-- The search loop. -/
def FacInv4 (sb : Nat) (st : VSt) (p : Nat) (params : List Nat) (args : Array Nat)
    (kept : List Nat) (i : Nat) (wok : BitVec 32) (s : (KernelState prog State)) (a : Nat) :
    Env → (KernelState prog State) → Prop := fun env s' =>
  s' = s ∧ ∃ j, env = facEnv sb st p params args (BitVec.ofNat 32 args.size)
      (BitVec.ofNat 32 kept.length) (BitVec.ofNat 32 i) (BitVec.ofNat 32 j)
      (BitVec.ofNat 32 (st.id a)) wok ∧ j ≤ kept.length ∧
    ∀ j', j' < j → kept[j']? ≠ some a

theorem r_factoring_spec :
    RuleSpec (State := State) "r_factoring" (fun _ st pr pa => ruleFactoring st pr pa) := by
  rule_begin rFactoring
  rcases prems with _ | ⟨p, _ | ⟨q, rest⟩⟩
  · rule_guard
  rotate_left
  · rule_guard
    intro h0
    simp at hnp
    rw [uv_inj (by omega) (by omega)] at h0
    simp at h0
  rule_guard
  have hp := hR.prems1
  obtain ⟨n, hn⟩ := node_of_lv hp
  rule_assign
  rule_guard [hR.core.rdHdr hn]
  intro hop
  obtain ⟨args, rfl, hsz, -, hargs⟩ := hR.core.argsN hn hop
  rule_guard
  intro h0
  have hpl : 0 < params.length := by
    cases params with
    | nil => simp at h0
    | cons _ _ => simp
  rule_assign [hR.core.rdN hn]
  rule_assign [hsp]
  apply WP.loop_seq (FacInv1 W sb X c st p params args)
  · exact ⟨c, 0, 0#32, rfl, h, hR, by omega, by simp [hsp], fun d hd => by omega⟩
  clear h hR
  rintro env s1 ⟨c1, i, wok, rfl, h, hR, hi, hsp1, hm1⟩
  simp only [facEnv]
  rule_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  rotate_left
  · apply WP.rule_push h hR
    rule_simp
    intro s2 c2 ok h2 hP
    have hR2 := hP.1
    clear h hR
    have h := h2
    have hR := hR2
    clear h2 hR2
    rule_guard
    intro hok
    rcases hP.2.2 with ⟨e, -⟩ | ⟨e, -, hsp2, htop2⟩
    · exact absurd e hok
    subst e
    apply WP.assign_loop
    rule_simp
    refine ⟨c2, i + 1, 1#32, rfl, h, hR, by omega, by omega, fun d hd => ?_⟩
    unfold U
    rcases Nat.lt_or_ge d i with h3 | h3
    · rw [hP.2.1 _ (by omega)]
      exact hm1 d h3
    · rw [show 0 + d = c1.k.sp.toNat by omega, htop2]
      rfl
  have hin : i = args.size := by omega
  subst hin
  apply WP.rule_cl_dups h hR p hn 0 (by omega) hm1
  refine ⟨by rule_simp, ?_⟩
  rintro s2 r ⟨c2, h2, hR2, hfr, hcase⟩
  clear h hR
  have h := h2
  have hR := hR2
  clear h2 hR2
  rule_simp
  rule_guard
  intro hr0
  rcases hcase with rfl | ⟨rfl, dups, hparse, hmk⟩
  · simp at hr0
  have hsp2 : c2.k.sp = BitVec.ofNat 32 args.size := by
    rw [hfr.1, ← hsp1, bv_ofNat_toNat]
  rule_assign [hsp2]
  rule_assign
  have hspn : c2.k.sp.toNat = args.size := by rw [hfr.1, hsp1]
  apply WP.loop_seq (FacInv2 W sb X c st p params args dups)
  · exact ⟨c2, 0, 1#32, rfl, h, hR, by omega, StkTop.nil hspn, hmk⟩
  clear h hR hmk
  rintro env s3 ⟨c3, i, wok, rfl, h, hR, hi, htop, hmk⟩
  simp only [facEnv]
  rule_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  rotate_left
  · have hstk := hR.stk_eq h (by have := htop.1; omega)
    have hai := hargs i hlt
    apply WP.seq_mid_env (FacMid2 W sb X c st p params args dups i)
    · by_cases hdi : i ∈ dups
      · have hcell : c3.stk[i]? = some (.u32 1#32) := by simpa [U, hdi] using hmk i hlt
        apply WP.ite
        rule_simp [hstk, rd_u32 hcell]
        apply WP.skip
        refine ⟨c3, wok, by simp [Env.set], h, hR, ?_, hmk⟩
        rw [clKept_succ hlt, ite_eq_left hdi, List.append_nil]
        exact htop
      · have hcell : c3.stk[i]? = some (.u32 0#32) := by simpa [U, hdi] using hmk i hlt
        apply WP.ite
        rule_simp [hstk, rd_u32 hcell]
        apply WP.rule_push h hR
        rule_simp [hR.core.rdN hn]
        intro s4 c4 ok h4 hP
        have hR4 := hP.1
        apply WP.ite
        rule_simp
        refine ⟨fun hok => WP.rule_fail h4, fun hok => WP.skip ?_⟩
        refine ⟨c4, ok, rfl, h4, hR4, ?_, fun d hd => ?_⟩
        · rw [clKept_succ hlt, ite_eq_right hdi]
          exact StkTop.push htop hP hok hai
        · unfold U
          rw [hP.2.1 _ (by have := htop.1; omega)]
          exact hmk d hd
    rintro env' s4 ⟨c4, wok', rfl, h4, hR4, htop4, hmk4⟩
    apply WP.assign_loop
    rule_simp
    exact ⟨c4, i + 1, wok', rfl, h4, hR4, by omega, htop4, hmk4⟩
  have hin : i = args.size := by omega
  subst hin
  have hkl : (clKept args dups args.size).length ≤ args.size := by
    unfold clKept
    exact Nat.le_trans (List.length_filterMap_le _ _)
      (Nat.le_trans (List.length_filter_le _ _) (by simp))
  have hsp3 : c3.k.sp = BitVec.ofNat 32 (args.size + (clKept args dups args.size).length) := by
    rw [← bv_ofNat_toNat c3.k.sp, htop.1]
  rule_assign [hsp3, cw_sub]
  -- pay for the nested scan
  apply WP.rule_spend h hR
  rule_simp
  intro s3 wk3 er3 wok h _
  have hR := hR.wev (wk := wk3) (er := er3) (vl := c3.k.val)
  have htop := htop.wev (wk := wk3) (er := er3) (vl := c3.k.val)
  have hmk : Marks (c3.wev wk3 er3 c3.k.val) 0 args.size dups := hmk
  rw [show c3.k.sp = (c3.wev wk3 er3 c3.k.val).k.sp from rfl] at hsp3
  generalize c3.wev wk3 er3 c3.k.val = c3 at h hR htop hmk hsp3
  rule_guard
  intro hwok
  rule_assign
  apply WP.loop_seq (FacInv3 sb st p params args dups s3 wok)
  · exact ⟨rfl, 0, 0#32, 0#32, by simp [facEnv], by omega, fun i' h1 => by omega⟩
  rintro env s4 ⟨rfl, i, wj, wx, rfl, hi, hdone⟩
  simp only [facEnv]
  rule_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  rotate_left
  · have hstk := hR.stk_eq h (by have := htop.1; omega)
    have hai := hargs i hlt
    apply WP.seq_mid_env (FacMid3 s4 args dups i hlt)
    · by_cases hdi : i ∈ dups
      · have hcell : c3.stk[i]? = some (.u32 1#32) := by simpa [U, hdi] using hmk i hlt
        apply WP.ite
        rule_simp [hstk, rd_u32 hcell]
        rule_assign [hR.core.rdN hn]
        rule_assign
        generalize hK : clKept args dups args.size = kept at htop hkl hsp3 ⊢
        apply WP.loop_seq (FacInv4 sb st p params args kept i wok s4 args[i])
        · exact ⟨rfl, 0, rfl, by omega, fun j' h1 => by omega⟩
        rintro env s5 ⟨rfl, j, rfl, hj, hjne⟩
        simp only [facEnv]
        by_cases hjk : j < kept.length
        · have hc := htop.cell hjk
          have hkj := htop.lt_size hjk
          rule_simp [hstk, rd_u32 hc]
          refine ⟨fun hex => ?_, fun _ hne => ?_⟩
          · have hex := hex hjk
            apply WP.ite
            rule_simp
            refine ⟨fun e => absurd e (by omega), fun _ => WP.skip ?_⟩
            refine ⟨rfl, fun _ => ?_, BitVec.ofNat 32 j, BitVec.ofNat 32 (st.id args[i]),
              by simp [Env.set]⟩
            rw [hK, ← hex]
            exact List.getElem_mem hjk
          · apply WP.assign_loop
            rule_simp
            refine ⟨rfl, j + 1, rfl, by omega, fun j' h1 => ?_⟩
            rcases Nat.lt_or_ge j' j with h2 | h2
            · exact hjne j' h2
            · rw [show j' = j by omega, List.getElem?_eq_getElem hjk]
              exact fun e => hne (Option.some.inj e)
        · have hjl : j = kept.length := by omega
          subst hjl
          rule_simp
          apply WP.ite
          rule_simp
          exact WP.rule_fail h
      · have hcell : c3.stk[i]? = some (.u32 0#32) := by simpa [U, hdi] using hmk i hlt
        apply WP.ite
        rule_simp [hstk, rd_u32 hcell]
        apply WP.skip
        exact ⟨rfl, fun e => absurd e hdi, wj, wx, by simp [Env.set]⟩
    rintro env' s5 ⟨rfl, hmem, wj', wx', rfl⟩
    apply WP.assign_loop
    rule_simp
    refine ⟨rfl, i + 1, wj', wx', rfl, by omega, fun i' h1 h2 => ?_⟩
    rcases Nat.lt_or_ge i' i with h3 | h3
    · exact hdone i' h3 h2
    · rw [show i' = i by omega] at h2 ⊢
      exact ⟨_, Array.getElem?_eq_getElem hlt, hmem h2⟩
  have hin : i = args.size := by omega
  subst hin
  have hsub : subsetB args.toList (keptLits args dups) = true := by
    rw [subsetB_eq, List.all_eq_true]
    intro a ha
    simp only [decide_eq_true_eq]
    obtain ⟨k, hk, e⟩ := List.getElem_of_mem ha
    simp only [Array.length_toList, Array.getElem_toList] at hk e
    subst e
    by_cases hkd : k ∈ dups
    · obtain ⟨a', ha', hm⟩ := hdone k hk hkd
      rw [Array.getElem?_eq_getElem hk] at ha'
      cases ha'
      exact hm
    · exact clKept_mem hk hk hkd
  have hLean : ruleFactoring st [p] params =
      match clKept args dups args.size with
      | [l] => some (st, l)
      | _ => mkDisj st (clKept args dups args.size).toArray := by
    simp only [ruleFactoring, St.node, hn, Option.bind_some, isDisjNode, List.isEmpty_iff, h0,
      ite_false, hparse, hsub, ite_true]
    rfl
  generalize hK : clKept args dups args.size = kept at htop hkl hsp3 hLean ⊢
  have hkl2 : kept.length < 4294967296 := by omega
  by_cases h1 : kept.length = 1
  · obtain ⟨l, rfl⟩ := List.length_eq_one_iff.mp h1
    have hstk := hR.stk_eq h (by have := htop.1; simp at this; omega)
    have hc : c3.stk[args.size]? = some (uv (st.id l)) := by
      simpa using htop.cell (j := 0) (by simp)
    apply WP.ite_seq
    rule_simp [cw_eq_one]
    rule_ret [hstk, rd_u32 hc]
    refine hR.ret h (f := l) (htop.lt_size (j := 0) (by simp)) ?_
    rw [hLean]
  · apply WP.ite_seq
    rule_simp [cw_eq_one, h1]
    apply WP.rule_mkn mkn_specT h hR .disj 65#32 args.size kept htop.2 (by have := htop.1; omega)
    refine ⟨by rule_simp, ?_⟩
    intro s5 c5 r h hB
    rule_simp
    rule_ret
    refine hB.ret h (fun st' i hP => ?_)
    rw [hLean]
    rcases kept with _ | ⟨l, _ | ⟨l2, rs⟩⟩
    · simpa [mkDisj] using hP
    · simp at h1
    · simpa [mkDisj] using hP

end Vbcf.Proof
