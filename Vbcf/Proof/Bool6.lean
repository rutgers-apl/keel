import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Bool2

/-!
# Vbcf proofs: the Bool family, part 6 — the CNF rules for `=`, `xor`, `ite`, and `ITE_EQ`
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

theorem r_cnf_equiv_pos_spec :
    RuleSpec (State := State) "r_cnf_equiv_pos" (fun X st pr pa => ruleCnfEquivPos X.ei st pr pa) := by
  rule_begin rCnfEquivPos
  rule_arity rfl ⟨x, k, rfl⟩
  have ⟨hx, hk⟩ := hR.params2
  apply WP.rule_expr_at expr_at_spec' h hR x hx
  refine ⟨by rule_simp, ?_⟩
  intro r her
  rule_simp
  rule_guard
  intro hne
  obtain ⟨e, hee, he, rfl⟩ := her.ok hne
  obtain ⟨n, hn⟩ := node_of_lv he
  rule_guard [hR.core.rdHdr hn]
  intro hop
  obtain ⟨a, b, rfl, ha, hb⟩ := hR.core.args2 hn hop
  apply WP.rule_hcall (bl_cnf_pos_clause_spec W sb X c c [] [x, k] st e a b k true)
    (by rule_simp [hR.core.rd2 hn]) ⟨rfl, h, hR, he, ha, hb, hk⟩
  intro s' c' r h hB
  rule_simp
  rule_ret
  exact hB.ret h (fun st' i hP => by simp [ruleCnfEquivPos, hee, St.node, hn, isEqNode, hP])

theorem r_cnf_equiv_neg_spec :
    RuleSpec (State := State) "r_cnf_equiv_neg" (fun X st pr pa => ruleCnfEquivNeg X.ei st pr pa) := by
  rule_begin rCnfEquivNeg
  rule_arity rfl ⟨x, k, rfl⟩
  have ⟨hx, hk⟩ := hR.params2
  apply WP.rule_expr_at expr_at_spec' h hR x hx
  refine ⟨by rule_simp, ?_⟩
  intro r her
  rule_simp
  rule_guard
  intro hne
  obtain ⟨e, hee, he, rfl⟩ := her.ok hne
  obtain ⟨n, hn⟩ := node_of_lv he
  rule_guard [hR.core.rdHdr hn]
  intro hop
  obtain ⟨a, b, rfl, ha, hb⟩ := hR.core.args2 hn hop
  apply WP.rule_hcall (bl_cnf_neg_clause_spec W sb X c c [] [x, k] st e a b k false)
    (by rule_simp [hR.core.rd2 hn]) ⟨rfl, h, hR, he, ha, hb, hk⟩
  intro s' c' r h hB
  rule_simp
  rule_ret
  exact hB.ret h (fun st' i hP => by simp [ruleCnfEquivNeg, hee, St.node, hn, isEqNode, hP])

theorem r_cnf_xor_pos_spec :
    RuleSpec (State := State) "r_cnf_xor_pos" (fun X st pr pa => ruleCnfXorPos X.ei st pr pa) := by
  rule_begin rCnfXorPos
  rule_arity rfl ⟨x, k, rfl⟩
  have ⟨hx, hk⟩ := hR.params2
  apply WP.rule_expr_at expr_at_spec' h hR x hx
  refine ⟨by rule_simp, ?_⟩
  intro r her
  rule_simp
  rule_guard
  intro hne
  obtain ⟨e, hee, he, rfl⟩ := her.ok hne
  obtain ⟨n, hn⟩ := node_of_lv he
  rule_guard [hR.core.rdHdr hn]
  intro hop
  obtain ⟨args, rfl, hsz, -, hargs⟩ := hR.core.argsN hn hop
  rule_guard [hR.core.rdN hn]
  intro h2
  obtain ⟨a, b, rfl⟩ := array_eq_two h2
  have ha := hargs 0 (by simp)
  have hb := hargs 1 (by simp)
  simp only [List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ] at ha hb
  apply WP.rule_hcall (bl_cnf_neg_clause_spec W sb X c c [] [x, k] st e a b k true)
    (by rule_simp [hR.core.rd2 hn]) ⟨rfl, h, hR, he, ha, hb, hk⟩
  intro s' c' r h hB
  rule_simp
  rule_ret
  exact hB.ret h (fun st' i hP => by simp [ruleCnfXorPos, hee, St.node, hn, isXor2Node, hP])

theorem r_cnf_xor_neg_spec :
    RuleSpec (State := State) "r_cnf_xor_neg" (fun X st pr pa => ruleCnfXorNeg X.ei st pr pa) := by
  rule_begin rCnfXorNeg
  rule_arity rfl ⟨x, k, rfl⟩
  have ⟨hx, hk⟩ := hR.params2
  apply WP.rule_expr_at expr_at_spec' h hR x hx
  refine ⟨by rule_simp, ?_⟩
  intro r her
  rule_simp
  rule_guard
  intro hne
  obtain ⟨e, hee, he, rfl⟩ := her.ok hne
  obtain ⟨n, hn⟩ := node_of_lv he
  rule_guard [hR.core.rdHdr hn]
  intro hop
  obtain ⟨args, rfl, hsz, -, hargs⟩ := hR.core.argsN hn hop
  rule_guard [hR.core.rdN hn]
  intro h2
  obtain ⟨a, b, rfl⟩ := array_eq_two h2
  have ha := hargs 0 (by simp)
  have hb := hargs 1 (by simp)
  simp only [List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ] at ha hb
  apply WP.rule_hcall (bl_cnf_pos_clause_spec W sb X c c [] [x, k] st e a b k false)
    (by rule_simp [hR.core.rd2 hn]) ⟨rfl, h, hR, he, ha, hb, hk⟩
  intro s' c' r h hB
  rule_simp
  rule_ret
  exact hB.ret h (fun st' i hP => by simp [ruleCnfXorNeg, hee, St.node, hn, isXor2Node, hP])

theorem r_ite_eq_spec :
    RuleSpec (State := State) "r_ite_eq" (fun X st pr pa => ruleIteEq X.ei st pr pa) := by
  rule_begin rIteEq
  rule_arity rfl ⟨x, rfl⟩
  have hx := hR.params1
  apply WP.rule_expr_at expr_at_spec' h hR x hx
  refine ⟨by rule_simp, ?_⟩
  intro r her
  rule_simp
  rule_guard
  intro hne
  obtain ⟨e, hee, he, rfl⟩ := her.ok hne
  obtain ⟨n, hn⟩ := node_of_lv he
  rule_assign [hR.core.rdHdr hn]
  rule_guard
  intro hop
  by_cases hbi : n.op = .boolIte
  · obtain ⟨d, a, b, rfl, hd, ha, hb⟩ := hR.core.args3 hn hbi
    rule_guard [hR.core.rdN hn]
    intro _
    apply WP.rule_hcall (bl_ite_eq_body_spec W sb X c c [] [x] st e d a b)
      (by rule_simp [hR.core.rd3 hn]) ⟨rfl, h, hR, he, hd, ha, hb⟩
    intro s' c' r h hB
    rule_simp
    rule_ret
    exact hB.ret h (fun st' i hP => by simp [ruleIteEq, hee, St.node, hn, three, hP])
  · obtain ⟨w, hw⟩ := hop hbi
    obtain ⟨d, a, b, rfl, hd, ha, hb⟩ := hR.core.args3 hn hw
    have hl : ¬ IsLeaf (Op.bvIte w) := by simp [IsLeaf, isLeaf]
    rule_guard [hR.core.rdN hn hl]
    intro _
    apply WP.rule_hcall (bl_ite_eq_body_spec W sb X c c [] [x] st e d a b)
      (by rule_simp [hR.core.rd3 hn hl]) ⟨rfl, h, hR, he, hd, ha, hb⟩
    intro s' c' r h hB
    rule_simp
    rule_ret
    exact hB.ret h (fun st' i hP => by simp [ruleIteEq, hee, St.node, hn, three, hP])

theorem r_cnf_ite_pos_spec :
    RuleSpec (State := State) "r_cnf_ite_pos" (fun X st pr pa => ruleCnfItePos X.ei st pr pa) := by
  rule_begin rCnfItePos
  rule_arity rfl ⟨x, k, rfl⟩
  have ⟨hx, hk⟩ := hR.params2
  apply WP.rule_expr_at expr_at_spec' h hR x hx
  refine ⟨by rule_simp, ?_⟩
  intro r her
  rule_simp
  rule_guard
  intro hne
  obtain ⟨e, hee, he, rfl⟩ := her.ok hne
  obtain ⟨n, hn⟩ := node_of_lv he
  rule_guard [hR.core.rdHdr hn]
  intro hop
  obtain ⟨d, a, b, rfl, hd, ha, hb⟩ := hR.core.args3 hn hop
  rule_assign
  apply WP.rule_mk_not mk_not_specT h hR e he
  refine ⟨by rule_simp, ?_⟩
  intro s1 c1 r h hB
  rule_simp
  rule_guard
  intro hne
  obtain ⟨st1, i, hP, hR, hext, hstk, hi, rfl⟩ := hB.ok hne
  have he1 := hext.lt he
  have hn1 := hext.get hn
  have hd1 := hext.lt hd
  have ha1 := hext.lt ha
  have hb1 := hext.lt hb
  rw [← hext.id he]
  apply WP.ite_seq
  rule_simp
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · apply WP.rule_mk_not mk_not_specT h hR d hd1
    refine ⟨by rule_simp [hR.core.rd3 hn1], ?_⟩
    intro s2 c2 r h hB
    rule_simp
    rule_guard
    intro hne
    obtain ⟨st2, j, hP', hR, hext', hstk', hj, rfl⟩ := hB.ok hne
    have he2 := hext'.lt he1
    rw [← hext'.id he1, ← hext'.id hi]
    apply WP.rule_mk3 mk3_specT h hR .disj 65#32 i j a (hext'.lt hi) hj (hext'.lt ha1)
    refine ⟨by rule_simp [hR.core.rd3 (hext'.get hn1)], ?_⟩
    intro s' c' r h hB
    rule_simp
    rule_ret
    exact hB.ret h (fun st3 i3 hP3 => by
      simp [ruleCnfItePos, hee, St.node, hn, isBoolIteNode, hP, h0, hP', mkDisj, hP3])
  apply WP.ite_seq
  rule_simp
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  · apply WP.rule_mk3 mk3_specT h hR .disj 65#32 i d b hi hd1 hb1
    refine ⟨by rule_simp [hR.core.rd3 hn1], ?_⟩
    intro s' c' r h hB
    rule_simp
    rule_ret
    exact hB.ret h (fun st3 i3 hP3 => by
      simp [ruleCnfItePos, hee, St.node, hn, isBoolIteNode, hP, h1, mkDisj, hP3])
  apply WP.ite_seq
  rule_simp
  refine ⟨fun h2 => ?_, fun h2 => ?_⟩
  · apply WP.rule_mk3 mk3_specT h hR .disj 65#32 i a b hi ha1 hb1
    refine ⟨by rule_simp [hR.core.rd3 hn1], ?_⟩
    intro s' c' r h hB
    rule_simp
    rule_ret
    exact hB.ret h (fun st3 i3 hP3 => by
      simp [ruleCnfItePos, hee, St.node, hn, isBoolIteNode, hP, h2, mkDisj, hP3])
  exact WP.rule_fail h

theorem r_cnf_ite_neg_spec :
    RuleSpec (State := State) "r_cnf_ite_neg" (fun X st pr pa => ruleCnfIteNeg X.ei st pr pa) := by
  rule_begin rCnfIteNeg
  rule_arity rfl ⟨x, k, rfl⟩
  have ⟨hx, hk⟩ := hR.params2
  apply WP.rule_expr_at expr_at_spec' h hR x hx
  refine ⟨by rule_simp, ?_⟩
  intro r her
  rule_simp
  rule_guard
  intro hne
  obtain ⟨e, hee, he, rfl⟩ := her.ok hne
  obtain ⟨n, hn⟩ := node_of_lv he
  rule_guard [hR.core.rdHdr hn]
  intro hop
  obtain ⟨d, a, b, rfl, hd, ha, hb⟩ := hR.core.args3 hn hop
  rule_assign
  apply WP.ite_seq
  rule_simp
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · apply WP.rule_mk_not mk_not_specT h hR d hd
    refine ⟨by rule_simp [hR.core.rd3 hn], ?_⟩
    intro s1 c1 r h hB
    rule_simp
    rule_guard
    intro hne
    obtain ⟨st1, i, hP, hR, hext, hstk, hi, rfl⟩ := hB.ok hne
    have he1 := hext.lt he
    rw [← hext.id he]
    apply WP.rule_mk_not mk_not_specT h hR a (hext.lt ha)
    refine ⟨by rule_simp [hR.core.rd3 (hext.get hn)], ?_⟩
    intro s2 c2 r h hB
    rule_simp
    rule_guard
    intro hne
    obtain ⟨st2, j, hP', hR, hext', hstk', hj, rfl⟩ := hB.ok hne
    rw [← hext'.id he1, ← hext'.id hi]
    apply WP.rule_mk3 mk3_specT h hR .disj 65#32 e i j (hext'.lt he1) (hext'.lt hi) hj
    refine ⟨by rule_simp, ?_⟩
    intro s' c' r h hB
    rule_simp
    rule_ret
    exact hB.ret h (fun st3 i3 hP3 => by
      simp [ruleCnfIteNeg, hee, St.node, hn, isBoolIteNode, h0, hP, hP', mkDisj, hP3])
  apply WP.ite_seq
  rule_simp
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  · apply WP.rule_mk_not mk_not_specT h hR b hb
    refine ⟨by rule_simp [hR.core.rd3 hn], ?_⟩
    intro s1 c1 r h hB
    rule_simp
    rule_guard
    intro hne
    obtain ⟨st1, i, hP, hR, hext, hstk, hi, rfl⟩ := hB.ok hne
    have he1 := hext.lt he
    rw [← hext.id he]
    apply WP.rule_mk3 mk3_specT h hR .disj 65#32 e d i he1 (hext.lt hd) hi
    refine ⟨by rule_simp [hR.core.rd3 (hext.get hn)], ?_⟩
    intro s' c' r h hB
    rule_simp
    rule_ret
    exact hB.ret h (fun st3 i3 hP3 => by
      simp [ruleCnfIteNeg, hee, St.node, hn, isBoolIteNode, h1, hP, mkDisj, hP3])
  apply WP.ite_seq
  rule_simp
  refine ⟨fun h2 => ?_, fun h2 => ?_⟩
  · apply WP.rule_mk_not mk_not_specT h hR a ha
    refine ⟨by rule_simp [hR.core.rd3 hn], ?_⟩
    intro s1 c1 r h hB
    rule_simp
    rule_guard
    intro hne
    obtain ⟨st1, i, hP, hR, hext, hstk, hi, rfl⟩ := hB.ok hne
    have he1 := hext.lt he
    rw [← hext.id he]
    apply WP.rule_mk_not mk_not_specT h hR b (hext.lt hb)
    refine ⟨by rule_simp [hR.core.rd3 (hext.get hn)], ?_⟩
    intro s2 c2 r h hB
    rule_simp
    rule_guard
    intro hne
    obtain ⟨st2, j, hP', hR, hext', hstk', hj, rfl⟩ := hB.ok hne
    rw [← hext'.id he1, ← hext'.id hi]
    apply WP.rule_mk3 mk3_specT h hR .disj 65#32 e i j (hext'.lt he1) (hext'.lt hi) hj
    refine ⟨by rule_simp, ?_⟩
    intro s' c' r h hB
    rule_simp
    rule_ret
    exact hB.ret h (fun st3 i3 hP3 => by
      simp [ruleCnfIteNeg, hee, St.node, hn, isBoolIteNode, h2, hP, hP', mkDisj, hP3])
  exact WP.rule_fail h

end Vbcf.Proof
