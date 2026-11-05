import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Bool1

/-!
# Vbcf proofs: the Bool family, part 2 — the helpers
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-- Entering a helper body: from the `HQ` postcondition to the `retPost` that `FnSpec.intro'`
wants. -/
theorem WP.h_body {fn : Fn} (hr : fn.ret = some .u32) {W : World} {sb : Nat} {X : Ctx}
    {c0 c : CMem} {prems params : List Nat} {st : VSt} {P : St → Nat → Prop} {env : Env}
    {s : (KernelState prog State)} (H : WP Vbcf.prog fn.body (HQ W sb X c0 prems params c st P) env s) :
    WP Vbcf.prog fn.body (retPost fn.ret (HPost W sb X c0 prems params c st P)) env s := by
  rw [hr]
  exact WP.mono H (fun o env s hq => HQ.retPost o env s hq)

open Lean in
/-- `h_guard [facts]`: `if (cond) { return NOID; }` inside a helper. -/
macro "h_guard" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (apply WP.h_guard $(mkIdent `h); rule_simp [$ts,*]))
macro "h_guard" : tactic => `(tactic| h_guard [])

theorem stk_trans {c c1 c2 : CMem} (h1 : c1.stk = c.stk ∧ c1.k.sp = c.k.sp)
    (h2 : c2.stk = c1.stk ∧ c2.k.sp = c1.k.sp) : c2.stk = c.stk ∧ c2.k.sp = c.k.sp :=
  ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

/-! ## `bl_head_of` -/

def HeadOfSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (e : Nat) (neg : Bool),
    FnSpec (State := State) Vbcf.prog "bl_head_of"
      (fun vs s => vs = [.ptr sb 0, uv (st.id e), .u32 (if neg then 1#32 else 0#32)] ∧
        Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧ st.lv e)
      (fun _ _ => HPost W sb X c0 prems params c st (fun st' i => headOf st e neg = some (st', i)))

theorem bl_head_of_spec : HeadOfSpec (State := State) := by
  intro W sb X c0 c prems params st e neg
  have hs := prog_ck
  apply FnSpec.intro' (fn := blHeadOf) rfl
  rintro vs s ⟨rfl, h, hR, he⟩
  simp [blHeadOf, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply WP.h_body (fn := blHeadOf) rfl
  simp only [blHeadOf, Stmt.block, initLocals, List.map, Ty.zero]
  apply WP.ite_seq
  cases neg
  · rule_simp
    rule_ret
    exact HRet.id h hR he (by simp [headOf])
  · rule_simp
    apply WP.rule_mk_not mk_not_specT h hR e he
    refine ⟨by rule_simp, ?_⟩
    intro s' c' r h hB
    rule_simp
    rule_ret
    exact HRet.of_built h hB (fun st' i hP => by simp [headOf, hP])

/-! ## `bl_equiv_elim_clause` and `bl_not_equiv_elim_clause` -/

def EquivElimClauseSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (a b form : Nat),
    FnSpec (State := State) Vbcf.prog "bl_equiv_elim_clause"
      (fun vs s => vs = [.ptr sb 0, uv (st.id a), uv (st.id b), uv form] ∧
        Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧ st.lv a ∧
        st.lv b ∧ form < 4294967296)
      (fun _ _ => HPost W sb X c0 prems params c st
        (fun st' i => equivElimClause st a b form = some (st', i)))

theorem bl_equiv_elim_clause_spec : EquivElimClauseSpec (State := State) := by
  intro W sb X c0 c prems params st a b form
  have hs := prog_ck
  apply FnSpec.intro' (fn := blEquivElimClause) rfl
  rintro vs s ⟨rfl, h, hR, ha, hb, hf⟩
  simp [blEquivElimClause, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply WP.h_body (fn := blEquivElimClause) rfl
  simp only [blEquivElimClause, Stmt.block, initLocals, List.map, Ty.zero]
  apply WP.ite_seq
  rule_simp
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · apply WP.rule_mk_not mk_not_specT h hR a ha
    refine ⟨by rule_simp, ?_⟩
    intro s' c' r h hB
    rule_simp
    h_guard
    intro hne
    obtain ⟨st', i, hP, hR, hext, hstk, hi, rfl⟩ := hB.ok hne
    have hb' := hext.lt hb
    rw [← hext.id hb]
    apply WP.rule_mk2 mk2_specT h hR .disj 65#32 i b hi hb'
    refine ⟨by rule_simp, ?_⟩
    intro s' c' r h hB'
    rule_simp
    rule_ret
    exact HRet.of_built2 h hext hstk hB' (fun st2 i2 hP2 => by
      simp [equivElimClause, h0, hP, mkDisj, hP2])
  apply WP.ite_seq
  rule_simp
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  · apply WP.rule_mk_not mk_not_specT h hR b hb
    refine ⟨by rule_simp, ?_⟩
    intro s' c' r h hB
    rule_simp
    h_guard
    intro hne
    obtain ⟨st', i, hP, hR, hext, hstk, hi, rfl⟩ := hB.ok hne
    have ha' := hext.lt ha
    rw [← hext.id ha]
    apply WP.rule_mk2 mk2_specT h hR .disj 65#32 a i ha' hi
    refine ⟨by rule_simp, ?_⟩
    intro s' c' r h hB'
    rule_simp
    rule_ret
    exact HRet.of_built2 h hext hstk hB' (fun st2 i2 hP2 => by
      simp [equivElimClause, h1, hP, mkDisj, hP2])
  exact WP.h_fail h

def NotEquivElimClauseSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (a b form : Nat),
    FnSpec (State := State) Vbcf.prog "bl_not_equiv_elim_clause"
      (fun vs s => vs = [.ptr sb 0, uv (st.id a), uv (st.id b), uv form] ∧
        Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧ st.lv a ∧
        st.lv b ∧ form < 4294967296)
      (fun _ _ => HPost W sb X c0 prems params c st
        (fun st' i => notEquivElimClause st a b form = some (st', i)))

theorem bl_not_equiv_elim_clause_spec : NotEquivElimClauseSpec (State := State) := by
  intro W sb X c0 c prems params st a b form
  have hs := prog_ck
  apply FnSpec.intro' (fn := blNotEquivElimClause) rfl
  rintro vs s ⟨rfl, h, hR, ha, hb, hf⟩
  simp [blNotEquivElimClause, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply WP.h_body (fn := blNotEquivElimClause) rfl
  simp only [blNotEquivElimClause, Stmt.block, initLocals, List.map, Ty.zero]
  apply WP.ite_seq
  rule_simp
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · apply WP.rule_mk2 mk2_specT h hR .disj 65#32 a b ha hb
    refine ⟨by rule_simp, ?_⟩
    intro s' c' r h hB
    rule_simp
    rule_ret
    exact HRet.of_built h hB (fun st2 i2 hP2 => by simp [notEquivElimClause, h0, mkDisj, hP2])
  apply WP.ite_seq
  rule_simp
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  · apply WP.rule_mk_not mk_not_specT h hR a ha
    refine ⟨by rule_simp, ?_⟩
    intro s1 c1 r h hB
    rule_simp
    h_guard
    intro hne
    obtain ⟨st1, i, hP, hR, hext, hstk, hi, rfl⟩ := hB.ok hne
    have hb1 := hext.lt hb
    rw [← hext.id hb]
    apply WP.rule_mk_not mk_not_specT h hR b hb1
    refine ⟨by rule_simp, ?_⟩
    intro s2 c2 r h hB
    rule_simp
    h_guard
    intro hne
    obtain ⟨st2, j, hP', hR, hext', hstk', hj, rfl⟩ := hB.ok hne
    have hi2 := hext'.lt hi
    rw [← hext'.id hi]
    apply WP.rule_mk2 mk2_specT h hR .disj 65#32 i j hi2 hj
    refine ⟨by rule_simp, ?_⟩
    intro s' c' r h hB
    rule_simp
    rule_ret
    exact HRet.of_built2 h (hext.trans hext') (stk_trans hstk hstk') hB (fun st3 i3 hP3 => by
      simp [notEquivElimClause, h1, hP, hP', mkDisj, hP3])
  exact WP.h_fail h

/-! ## `bl_cnf_pos_clause` and `bl_cnf_neg_clause` -/

def CnfPosClauseSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (e a b form : Nat) (neg : Bool),
    FnSpec (State := State) Vbcf.prog "bl_cnf_pos_clause"
      (fun vs s => vs = [.ptr sb 0, uv (st.id e), uv (st.id a), uv (st.id b),
          uv form, .u32 (if neg then 1#32 else 0#32)] ∧
        Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧ st.lv e ∧
        st.lv a ∧ st.lv b ∧ form < 4294967296)
      (fun _ _ => HPost W sb X c0 prems params c st
        (fun st' i => cnfPosClause st e a b form neg = some (st', i)))

theorem bl_cnf_pos_clause_spec : CnfPosClauseSpec (State := State) := by
  intro W sb X c0 c prems params st e a b form neg
  have hs := prog_ck
  apply FnSpec.intro' (fn := blCnfPosClause) rfl
  rintro vs s ⟨rfl, h, hR, he, ha, hb, hf⟩
  simp [blCnfPosClause, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply WP.h_body (fn := blCnfPosClause) rfl
  simp only [blCnfPosClause, Stmt.block, initLocals, List.map, Ty.zero]
  apply WP.rule_hcall (bl_head_of_spec W sb X c0 c prems params st e neg) (by rule_simp)
    ⟨rfl, h, hR, he⟩
  intro s1 c1 r h hB
  rule_simp
  h_guard
  intro hne
  obtain ⟨st1, k, hP, hR, hext, hstk, hk, rfl⟩ := hB.ok hne
  have ha1 := hext.lt ha
  have hb1 := hext.lt hb
  rw [← hext.id ha, ← hext.id hb]
  apply WP.ite_seq
  rule_simp
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · apply WP.rule_mk_not mk_not_specT h hR a ha1
    refine ⟨by rule_simp, ?_⟩
    intro s2 c2 r h hB
    rule_simp
    h_guard
    intro hne
    obtain ⟨st2, i, hP', hR, hext', hstk', hi, rfl⟩ := hB.ok hne
    have hk2 := hext'.lt hk
    have hb2 := hext'.lt hb1
    rw [← hext'.id hk, ← hext'.id hb1]
    apply WP.rule_mk3 mk3_specT h hR .disj 65#32 k i b hk2 hi hb2
    refine ⟨by rule_simp, ?_⟩
    intro s' c' r h hB
    rule_simp
    rule_ret
    exact HRet.of_built2 h (hext.trans hext') (stk_trans hstk hstk') hB (fun st3 i3 hP3 => by
      simp [cnfPosClause, hP, h0, hP', mkDisj, hP3])
  apply WP.ite_seq
  rule_simp
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  · apply WP.rule_mk_not mk_not_specT h hR b hb1
    refine ⟨by rule_simp, ?_⟩
    intro s2 c2 r h hB
    rule_simp
    h_guard
    intro hne
    obtain ⟨st2, i, hP', hR, hext', hstk', hi, rfl⟩ := hB.ok hne
    have hk2 := hext'.lt hk
    have ha2 := hext'.lt ha1
    rw [← hext'.id hk, ← hext'.id ha1]
    apply WP.rule_mk3 mk3_specT h hR .disj 65#32 k a i hk2 ha2 hi
    refine ⟨by rule_simp, ?_⟩
    intro s' c' r h hB
    rule_simp
    rule_ret
    exact HRet.of_built2 h (hext.trans hext') (stk_trans hstk hstk') hB (fun st3 i3 hP3 => by
      simp [cnfPosClause, hP, h1, hP', mkDisj, hP3])
  exact WP.h_fail h

def CnfNegClauseSpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (e a b lit : Nat) (neg : Bool),
    FnSpec (State := State) Vbcf.prog "bl_cnf_neg_clause"
      (fun vs s => vs = [.ptr sb 0, uv (st.id e), uv (st.id a), uv (st.id b),
          uv lit, .u32 (if neg then 1#32 else 0#32)] ∧
        Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧ st.lv e ∧
        st.lv a ∧ st.lv b ∧ lit < 4294967296)
      (fun _ _ => HPost W sb X c0 prems params c st
        (fun st' i => cnfNegClause st e a b lit neg = some (st', i)))

theorem bl_cnf_neg_clause_spec : CnfNegClauseSpec (State := State) := by
  intro W sb X c0 c prems params st e a b lit neg
  have hs := prog_ck
  apply FnSpec.intro' (fn := blCnfNegClause) rfl
  rintro vs s ⟨rfl, h, hR, he, ha, hb, hf⟩
  simp [blCnfNegClause, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply WP.h_body (fn := blCnfNegClause) rfl
  simp only [blCnfNegClause, Stmt.block, initLocals, List.map, Ty.zero]
  apply WP.rule_hcall (bl_head_of_spec W sb X c0 c prems params st e neg) (by rule_simp)
    ⟨rfl, h, hR, he⟩
  intro s1 c1 r h hB
  rule_simp
  h_guard
  intro hne
  obtain ⟨st1, k, hP, hR, hext, hstk, hk, rfl⟩ := hB.ok hne
  have ha1 := hext.lt ha
  have hb1 := hext.lt hb
  rw [← hext.id ha, ← hext.id hb]
  apply WP.ite_seq
  rule_simp
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · apply WP.rule_mk3 mk3_specT h hR .disj 65#32 k a b hk ha1 hb1
    refine ⟨by rule_simp, ?_⟩
    intro s' c' r h hB
    rule_simp
    rule_ret
    exact HRet.of_built2 h hext hstk hB (fun st3 i3 hP3 => by
      simp [cnfNegClause, hP, h0, mkDisj, hP3])
  apply WP.ite_seq
  rule_simp
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  · apply WP.rule_mk_not mk_not_specT h hR a ha1
    refine ⟨by rule_simp, ?_⟩
    intro s2 c2 r h hB
    rule_simp
    h_guard
    intro hne
    obtain ⟨st2, i, hP', hR, hext', hstk', hi, rfl⟩ := hB.ok hne
    have hk2 := hext'.lt hk
    have hb2 := hext'.lt hb1
    rw [← hext'.id hk, ← hext'.id hb1]
    apply WP.rule_mk_not mk_not_specT h hR b hb2
    refine ⟨by rule_simp, ?_⟩
    intro s3 c3 r h hB
    rule_simp
    h_guard
    intro hne
    obtain ⟨st3, j, hP'', hR, hext'', hstk'', hj, rfl⟩ := hB.ok hne
    have hk3 := hext''.lt hk2
    have hi3 := hext''.lt hi
    rw [← hext''.id hk2, ← hext''.id hi]
    apply WP.rule_mk3 mk3_specT h hR .disj 65#32 k i j hk3 hi3 hj
    refine ⟨by rule_simp, ?_⟩
    intro s' c' r h hB
    rule_simp
    rule_ret
    exact HRet.of_built2 h ((hext.trans hext').trans hext'')
      (stk_trans (stk_trans hstk hstk') hstk'') hB (fun st4 i4 hP4 => by
      simp [cnfNegClause, hP, h1, hP', hP'', mkDisj, hP4])
  exact WP.h_fail h

/-! ## `bl_ite_eq_body` -/

def IteEqBodySpec : Prop :=
  ∀ (W : World) (sb : Nat) (X : Ctx) (c0 c : CMem) (prems params : List Nat) (st : VSt)
    (e d a b : Nat),
    FnSpec (State := State) Vbcf.prog "bl_ite_eq_body"
      (fun vs s => vs = [.ptr sb 0, uv (st.id e), uv (st.id d), uv (st.id a),
          uv (st.id b)] ∧
        Holds W s.mem sb c ∧ RCtx W X c0 prems params c st ∧ st.lv e ∧
        st.lv d ∧ st.lv a ∧ st.lv b)
      (fun _ _ => HPost W sb X c0 prems params c st
        (fun st' i => iteEqBody st e d a b = some (st', i)))

theorem bl_ite_eq_body_spec : IteEqBodySpec (State := State) := by
  intro W sb X c0 c prems params st e d a b
  have hs := prog_ck
  apply FnSpec.intro' (fn := blIteEqBody) rfl
  rintro vs s ⟨rfl, h, hR, he, hd, ha, hb⟩
  simp [blIteEqBody, bindParams, Mem.hasTy_ptr h.ck rfl]
  apply WP.h_body (fn := blIteEqBody) rfl
  simp only [blIteEqBody, Stmt.block, initLocals, List.map, Ty.zero]
  apply WP.rule_mk_eq mk_eq_specT h hR e a he ha
  refine ⟨by rule_simp, ?_⟩
  intro s1 c1 r h hB
  rule_simp
  h_guard
  intro hne
  obtain ⟨st1, i, hP, hR, hext, hstk, hi, rfl⟩ := hB.ok hne
  have he1 := hext.lt he
  have hb1 := hext.lt hb
  have hd1 := hext.lt hd
  rw [← hext.id he, ← hext.id hb, ← hext.id hd]
  apply WP.rule_mk_eq mk_eq_specT h hR e b he1 hb1
  refine ⟨by rule_simp, ?_⟩
  intro s2 c2 r h hB
  rule_simp
  h_guard
  intro hne
  obtain ⟨st2, j, hP', hR, hext', hstk', hj, rfl⟩ := hB.ok hne
  have hd2 := hext'.lt hd1
  have hi2 := hext'.lt hi
  rw [← hext'.id hd1, ← hext'.id hi]
  apply WP.rule_mk3 mk3_specT h hR .boolIte 41#32 d i j hd2 hi2 hj
  refine ⟨by rule_simp, ?_⟩
  intro s' c' r h hB
  rule_simp
  rule_ret
  exact HRet.of_built2 h (hext.trans hext') (stk_trans hstk hstk') hB (fun st3 i3 hP3 => by
    simp [iteEqBody, hP, hP', hP3])

end Vbcf.Proof
