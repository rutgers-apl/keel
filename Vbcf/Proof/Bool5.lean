import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Bool4

/-!
# Vbcf proofs: the Bool family, part 5 — `NOT_AND` and the CNF rules for `and`, `or`, `=>`
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

theorem r_not_and_spec :
    RuleSpec (State := State) "r_not_and" (fun _ st pr pa => ruleNotAnd st pr pa) := by
  rule_begin rNotAnd
  rule_guard
  intro h1
  obtain ⟨p, rfl⟩ := List.length_eq_one_iff.mp h1
  have hp := hR.prems1
  obtain ⟨n, hn⟩ := node_of_lv hp
  rule_assign
  rule_guard [hR.core.rdHdr hn]
  intro hop
  obtain ⟨q, rfl, hq⟩ := hR.core.args1 hn hop
  obtain ⟨n', hn'⟩ := node_of_lv hq
  rule_assign [hR.core.rd1 hn]
  rule_guard [hR.core.rdHdr hn']
  intro hop'
  obtain ⟨args, rfl, hsz, -, hargs⟩ := hR.core.argsN hn' hop'
  rule_assign [hsp]
  apply WP.rule_mk_nots h hR q hn' (by decide) (StkTop.nil (base := 0) (by simp [hsp]))
  refine ⟨by rule_simp, ?_⟩
  rintro s1 ok ⟨c1, h, hok⟩
  rule_simp
  rule_guard
  intro hne
  rcases hok with rfl | ⟨rfl, st1, nas, hnots, hR, hext, htop⟩
  · exact absurd rfl hne
  have hlen := mkNots_length hnots
  simp only [Array.length_toList] at hlen
  have hq1 := hext.lt hq
  rw [← hext.id hq]
  apply WP.rule_mkn mkn_specT h hR .disj 65#32 0 nas htop.2 (by have := htop.1; simp at this; omega)
  refine ⟨by rule_simp [hR.core.rdN (hext.get hn'), hlen], ?_⟩
  intro s' c' r h hB
  rule_simp
  rule_ret
  exact hB.ret h (fun st' i hP => by
    simp [ruleNotAnd, St.node, hn, hn', isNotNode, isConjNode, hnots, mkDisj, hP])

theorem r_cnf_and_pos_spec :
    RuleSpec (State := State) "r_cnf_and_pos" (fun X st pr pa => ruleCnfAndPos X.ei st pr pa) := by
  rule_begin rCnfAndPos
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
  rule_assign
  rule_guard [hR.core.rdN hn]
  intro hka
  apply WP.rule_mk_not mk_not_specT h hR e he
  refine ⟨by rule_simp, ?_⟩
  intro s' c' r h hB
  rule_simp
  rule_guard
  intro hne
  obtain ⟨st', i, hP, hR, hext, hstk, hi, rfl⟩ := hB.ok hne
  have he' := hext.lt he
  rw [← hext.id he]
  apply WP.rule_mk2 mk2_specT h hR .disj 65#32 i args[k] hi (hext.lt (hargs k hka))
  refine ⟨by rule_simp [hR.core.rdN (hext.get hn)], ?_⟩
  intro s' c' r h hB
  rule_simp
  rule_ret
  exact hB.ret h (fun st2 i2 hP2 => by
    simp [ruleCnfAndPos, hee, St.node, hn, isConjNode, hka, hP, mkDisj, hP2])

theorem r_cnf_or_neg_spec :
    RuleSpec (State := State) "r_cnf_or_neg" (fun X st pr pa => ruleCnfOrNeg X.ei st pr pa) := by
  rule_begin rCnfOrNeg
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
  rule_assign
  rule_guard [hR.core.rdN hn]
  intro hka
  apply WP.rule_mk_not mk_not_specT h hR args[k] (hargs k hka)
  refine ⟨by rule_simp [hR.core.rdN hn], ?_⟩
  intro s' c' r h hB
  rule_simp
  rule_guard
  intro hne
  obtain ⟨st', i, hP, hR, hext, hstk, hi, rfl⟩ := hB.ok hne
  have he' := hext.lt he
  rw [← hext.id he]
  apply WP.rule_mk2 mk2_specT h hR .disj 65#32 e i he' hi
  refine ⟨by rule_simp, ?_⟩
  intro s' c' r h hB
  rule_simp
  rule_ret
  exact hB.ret h (fun st2 i2 hP2 => by
    simp [ruleCnfOrNeg, hee, St.node, hn, isDisjNode, hka, hP, mkDisj, hP2])

theorem r_cnf_and_neg_spec :
    RuleSpec (State := State) "r_cnf_and_neg" (fun X st pr pa => ruleCnfAndNeg X.ei st pr pa) := by
  rule_begin rCnfAndNeg
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
  rule_guard [hR.core.rdHdr hn]
  intro hop
  obtain ⟨args, rfl, hsz, -, hargs⟩ := hR.core.argsN hn hop
  rule_assign [hsp]
  apply WP.rule_push h hR
  rule_simp
  intro s1 c1 ok1 h1 hPu
  have htop1 := fun hok => StkTop.push (StkTop.nil (base := 0) (by simp [hsp])) hPu hok he
  have hR1 := hPu.1
  clear h hR
  have h := h1
  have hR := hR1
  clear h1 hR1
  rule_guard
  intro hok
  apply WP.rule_mk_nots h hR e hn (by decide) (htop1 hok)
  refine ⟨by rule_simp, ?_⟩
  rintro s2 ok ⟨c2, h2, hok2⟩
  clear h
  have h := h2
  rule_simp
  rule_guard
  intro hne
  rcases hok2 with rfl | ⟨rfl, st1, nas, hnots, hR, hext, htop⟩
  · exact absurd rfl hne
  have hlen := mkNots_length hnots
  simp only [Array.length_toList] at hlen
  have he1 := hext.lt he
  rw [← hext.id he]
  apply WP.rule_mkn mkn_specT h hR .disj 65#32 0 ([e] ++ nas) htop.2
    (by have := htop.1; simp at this ⊢; omega)
  refine ⟨by rule_simp [hR.core.rdN (hext.get hn), hlen, Nat.add_comm], ?_⟩
  intro s' c' r h hB
  rule_simp
  rule_ret
  exact hB.ret h (fun st' i hP => by
    simp [ruleCnfAndNeg, hee, St.node, hn, isConjNode, hnots, mkDisj]
    simpa using hP)

theorem r_cnf_or_pos_spec :
    RuleSpec (State := State) "r_cnf_or_pos" (fun X st pr pa => ruleCnfOrPos X.ei st pr pa) := by
  rule_begin rCnfOrPos
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
  rule_guard [hR.core.rdHdr hn]
  intro hop
  obtain ⟨args, rfl, hsz, -, hargs⟩ := hR.core.argsN hn hop
  apply WP.rule_mk_not mk_not_specT h hR e he
  refine ⟨by rule_simp, ?_⟩
  intro s' c' r h hB
  rule_simp
  rule_guard
  intro hne
  obtain ⟨st', i, hP, hR, hext, hstk, hi, rfl⟩ := hB.ok hne
  have he' := hext.lt he
  have hn' := hext.get hn
  rw [← hext.id he]
  rule_assign [hstk.2, hsp]
  apply WP.rule_push h hR
  rule_simp
  intro s1 c1 ok1 h1 hPu
  have htop1 := fun hok => StkTop.push (StkTop.nil (base := 0) (by simp [hstk.2, hsp])) hPu hok hi
  have hR1 := hPu.1
  clear h hR
  have h := h1
  have hR := hR1
  clear h1 hR1
  rule_guard
  intro hok
  apply WP.rule_push_args h hR e hn' (show ¬ IsLeaf Op.disj by decide) (htop1 hok)
  refine ⟨by rule_simp, ?_⟩
  intro s2 c2 ok2 h2 hR2 hok2
  clear h hR
  have h := h2
  have hR := hR2
  clear h2 hR2
  rule_simp
  rule_guard
  intro hne
  rcases hok2 with rfl | ⟨rfl, htop⟩
  · exact absurd rfl hne
  apply WP.rule_mkn mkn_specT h hR .disj 65#32 0 ([i] ++ args.toList) htop.2
    (by have := htop.1; simp at this ⊢; omega)
  refine ⟨by rule_simp [hR.core.rdN hn', Nat.add_comm], ?_⟩
  intro s' c' r h hB
  rule_simp
  rule_ret
  exact hB.ret h (fun st2 i2 hP2 => by
    simp [ruleCnfOrPos, hee, St.node, hn, isDisjNode, hP, mkDisj]
    simpa using hP2)

theorem r_cnf_implies_pos_spec :
    RuleSpec (State := State) "r_cnf_implies_pos" (fun X st pr pa => ruleCnfImpliesPos X.ei st pr pa) := by
  rule_begin rCnfImpliesPos
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
  rule_guard [hR.core.rdHdr hn]
  intro hop
  obtain ⟨a, b, rfl, ha, hb⟩ := hR.core.args2 hn hop
  apply WP.rule_mk_not mk_not_specT h hR e he
  refine ⟨by rule_simp, ?_⟩
  intro s1 c1 r h hB
  rule_simp
  rule_guard
  intro hne
  obtain ⟨st1, i, hP, hR, hext, hstk, hi, rfl⟩ := hB.ok hne
  have he1 := hext.lt he
  rw [← hext.id he]
  apply WP.rule_mk_not mk_not_specT h hR a (hext.lt ha)
  refine ⟨by rule_simp [hR.core.rd2 (hext.get hn)], ?_⟩
  intro s2 c2 r h hB
  rule_simp
  rule_guard
  intro hne
  obtain ⟨st2, j, hP', hR, hext', hstk', hj, rfl⟩ := hB.ok hne
  have he2 := hext'.lt he1
  rw [← hext'.id he1, ← hext'.id hi]
  apply WP.rule_mk3 mk3_specT h hR .disj 65#32 i j b (hext'.lt hi) hj (hext'.lt (hext.lt hb))
  refine ⟨by rule_simp [hR.core.rd2 (hext'.get (hext.get hn))], ?_⟩
  intro s' c' r h hB
  rule_simp
  rule_ret
  exact hB.ret h (fun st3 i3 hP3 => by
    simp [ruleCnfImpliesPos, hee, St.node, hn, isImpliesNode, hP, hP', mkDisj, hP3])

theorem r_cnf_implies_neg_spec :
    RuleSpec (State := State) "r_cnf_implies_neg" (fun X st pr pa => ruleCnfImpliesNeg X.ei st pr pa) := by
  rule_begin rCnfImpliesNeg
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
  rule_assign
  apply WP.ite_seq
  rule_simp
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · apply WP.rule_mk2 mk2_specT h hR .disj 65#32 e a he ha
    refine ⟨by rule_simp [hR.core.rd2 hn], ?_⟩
    intro s' c' r h hB
    rule_simp
    rule_ret
    exact hB.ret h (fun st' i hP => by
      simp [ruleCnfImpliesNeg, hee, St.node, hn, isImpliesNode, h0, mkDisj, hP])
  apply WP.ite_seq
  rule_simp
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  · apply WP.rule_mk_not mk_not_specT h hR b hb
    refine ⟨by rule_simp [hR.core.rd2 hn], ?_⟩
    intro s' c' r h hB
    rule_simp
    rule_guard
    intro hne
    obtain ⟨st', i, hP, hR, hext, hstk, hi, rfl⟩ := hB.ok hne
    have he' := hext.lt he
    rw [← hext.id he]
    apply WP.rule_mk2 mk2_specT h hR .disj 65#32 e i he' hi
    refine ⟨by rule_simp, ?_⟩
    intro s' c' r h hB
    rule_simp
    rule_ret
    exact hB.ret h (fun st2 i2 hP2 => by
      simp [ruleCnfImpliesNeg, hee, St.node, hn, isImpliesNode, h1, hP, mkDisj, hP2])
  exact WP.rule_fail h

end Vbcf.Proof
