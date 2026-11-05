import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Bool2

/-!
# Vbcf proofs: the Bool family, part 3 — the elimination rules with premises
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

theorem r_implies_elim_spec :
    RuleSpec (State := State) "r_implies_elim" (fun _ st pr pa => ruleImpliesElim st pr pa) := by
  rule_begin rImpliesElim
  rule_arity ⟨p, rfl⟩ rfl
  have hp := hR.prems1
  obtain ⟨n, hn⟩ := node_of_lv hp
  rule_assign
  rule_guard [hR.core.rdHdr hn, uv_code_eq n, uv_opC_eq n]
  intro hop
  obtain ⟨a, b, rfl, ha, hb⟩ := hR.core.args2 hn hop
  apply WP.rule_mk_not mk_not_specT h hR a ha
  refine ⟨by rule_simp [hR.core.rd2 hn], ?_⟩
  intro s' c' r h hB
  rule_simp
  rule_guard
  intro hne
  obtain ⟨st', i, hP, hR, hext, hstk, hi, rfl⟩ := hB.ok hne
  have hp' := hext.lt hp
  rw [← hext.id hp]
  apply WP.rule_mk2 mk2_specT h hR .disj 65#32 i b hi (hext.lt hb)
  refine ⟨by rule_simp [hR.core.rd2 (hext.get hn)], ?_⟩
  intro s' c' r h hB
  rule_simp
  rule_ret
  exact hB.ret h (fun st2 i2 hP2 => by
    simp [ruleImpliesElim, St.node, hn, isImpliesNode, hP, mkDisj, hP2])

theorem r_not_implies_elim_spec :
    RuleSpec (State := State) "r_not_implies_elim" (fun _ st pr pa => ruleNotImpliesElim st pr pa) := by
  rule_begin rNotImpliesElim
  rule_arity ⟨p, rfl⟩ ⟨k, rfl⟩
  have hp := hR.prems1
  have hk := hR.params1
  obtain ⟨n, hn⟩ := node_of_lv hp
  rule_assign
  rule_guard [hR.core.rdHdr hn]
  intro hop
  obtain ⟨q, rfl, hq⟩ := hR.core.args1 hn hop
  obtain ⟨n', hn'⟩ := node_of_lv hq
  rule_assign [hR.core.rd1 hn]
  rule_guard [hR.core.rdHdr hn']
  intro hop'
  obtain ⟨a, b, rfl, ha, hb⟩ := hR.core.args2 hn' hop'
  rule_assign
  apply WP.ite_seq
  rule_simp
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · rule_ret [hR.core.rd2 hn']
    exact hR.ret h ha (by simp [ruleNotImpliesElim, St.node, hn, hn', isNotNode, isImpliesNode, h0])
  apply WP.ite_seq
  rule_simp
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  · apply WP.rule_mk_not mk_not_specT h hR b hb
    refine ⟨by rule_simp [hR.core.rd2 hn'], ?_⟩
    intro s' c' r h hB
    rule_simp
    rule_ret
    exact hB.ret h (fun st' i hP => by
      simp [ruleNotImpliesElim, St.node, hn, hn', isNotNode, isImpliesNode, h1, hP])
  exact WP.rule_fail h

theorem r_equiv_elim_spec :
    RuleSpec (State := State) "r_equiv_elim" (fun _ st pr pa => ruleEquivElim st pr pa) := by
  rule_begin rEquivElim
  rule_arity ⟨p, rfl⟩ ⟨k, rfl⟩
  have hp := hR.prems1
  have hk := hR.params1
  obtain ⟨n, hn⟩ := node_of_lv hp
  rule_assign
  rule_guard [hR.core.rdHdr hn]
  intro hop
  obtain ⟨a, b, rfl, ha, hb⟩ := hR.core.args2 hn hop
  apply WP.rule_hcall (bl_equiv_elim_clause_spec W sb X c c [p] [k] st a b k)
    (by rule_simp [hR.core.rd2 hn]) ⟨rfl, h, hR, ha, hb, hk⟩
  intro s' c' r h hB
  rule_simp
  rule_ret
  exact hB.ret h (fun st' i hP => by simp [ruleEquivElim, St.node, hn, isEqNode, hP])

theorem r_not_equiv_elim_spec :
    RuleSpec (State := State) "r_not_equiv_elim" (fun _ st pr pa => ruleNotEquivElim st pr pa) := by
  rule_begin rNotEquivElim
  rule_arity ⟨p, rfl⟩ ⟨k, rfl⟩
  have hp := hR.prems1
  have hk := hR.params1
  obtain ⟨n, hn⟩ := node_of_lv hp
  rule_assign
  rule_guard [hR.core.rdHdr hn]
  intro hop
  obtain ⟨q, rfl, hq⟩ := hR.core.args1 hn hop
  obtain ⟨n', hn'⟩ := node_of_lv hq
  rule_assign [hR.core.rd1 hn]
  rule_guard [hR.core.rdHdr hn']
  intro hop'
  obtain ⟨a, b, rfl, ha, hb⟩ := hR.core.args2 hn' hop'
  apply WP.rule_hcall (bl_not_equiv_elim_clause_spec W sb X c c [p] [k] st a b k)
    (by rule_simp [hR.core.rd2 hn']) ⟨rfl, h, hR, ha, hb, hk⟩
  intro s' c' r h hB
  rule_simp
  rule_ret
  exact hB.ret h (fun st' i hP => by
    simp [ruleNotEquivElim, St.node, hn, hn', isNotNode, isEqNode, hP])

theorem r_xor_elim_spec :
    RuleSpec (State := State) "r_xor_elim" (fun _ st pr pa => ruleXorElim st pr pa) := by
  rule_begin rXorElim
  rule_arity ⟨p, rfl⟩ ⟨k, rfl⟩
  have hp := hR.prems1
  have hk := hR.params1
  obtain ⟨n, hn⟩ := node_of_lv hp
  rule_assign
  rule_guard [hR.core.rdHdr hn]
  intro hop
  obtain ⟨args, rfl, hsz, -, hargs⟩ := hR.core.argsN hn hop
  rule_guard [hR.core.rdN hn]
  intro h2
  obtain ⟨a, b, rfl⟩ := array_eq_two h2
  have ha := hargs 0 (by simp)
  have hb := hargs 1 (by simp)
  simp only [List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ] at ha hb
  apply WP.rule_hcall (bl_not_equiv_elim_clause_spec W sb X c c [p] [k] st a b k)
    (by rule_simp [hR.core.rd2 hn]) ⟨rfl, h, hR, ha, hb, hk⟩
  intro s' c' r h hB
  rule_simp
  rule_ret
  exact hB.ret h (fun st' i hP => by simp [ruleXorElim, St.node, hn, isXor2Node, hP])

theorem r_not_xor_elim_spec :
    RuleSpec (State := State) "r_not_xor_elim" (fun _ st pr pa => ruleNotXorElim st pr pa) := by
  rule_begin rNotXorElim
  rule_arity ⟨p, rfl⟩ ⟨k, rfl⟩
  have hp := hR.prems1
  have hk := hR.params1
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
  rule_guard [hR.core.rdN hn']
  intro h2
  obtain ⟨a, b, rfl⟩ := array_eq_two h2
  have ha := hargs 0 (by simp)
  have hb := hargs 1 (by simp)
  simp only [List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ] at ha hb
  rule_assign
  apply WP.seq
  apply WP.ite
  rule_simp
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · apply WP.assign
    rule_simp
    apply WP.rule_hcall (bl_equiv_elim_clause_spec W sb X c c [p] [k] st a b 1)
      (by rule_simp [hR.core.rd2 hn']) ⟨rfl, h, hR, ha, hb, by omega⟩
    intro s' c' r h hB
    rule_simp
    rule_ret
    exact hB.ret h (fun st' i hP => by
      simp [ruleNotXorElim, St.node, hn, hn', isNotNode, isXor2Node, h0, hP])
  apply WP.ite
  rule_simp
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  · apply WP.assign
    rule_simp
    apply WP.rule_hcall (bl_equiv_elim_clause_spec W sb X c c [p] [k] st a b 0)
      (by rule_simp [hR.core.rd2 hn']) ⟨rfl, h, hR, ha, hb, by omega⟩
    intro s' c' r h hB
    rule_simp
    rule_ret
    exact hB.ret h (fun st' i hP => by
      simp [ruleNotXorElim, St.node, hn, hn', isNotNode, isXor2Node, h1, hP])
  · apply WP.assign
    rule_simp
    apply WP.rule_hcall (bl_equiv_elim_clause_spec W sb X c c [p] [k] st a b 2)
      (by rule_simp [hR.core.rd2 hn']) ⟨rfl, h, hR, ha, hb, by omega⟩
    intro s' c' r h hB
    rule_simp
    rule_ret
    exact hB.ret h (fun st' i hP => by
      simp [ruleNotXorElim, St.node, hn, hn', isNotNode, isXor2Node, h0, h1, hP])

theorem r_ite_elim_spec :
    RuleSpec (State := State) "r_ite_elim" (fun _ st pr pa => ruleIteElim st pr pa) := by
  rule_begin rIteElim
  rule_arity ⟨p, rfl⟩ ⟨k, rfl⟩
  have hp := hR.prems1
  have hk := hR.params1
  obtain ⟨n, hn⟩ := node_of_lv hp
  rule_assign
  rule_guard [hR.core.rdHdr hn]
  intro hop
  obtain ⟨d, a, b, rfl, hd, ha, hb⟩ := hR.core.args3 hn hop
  rule_assign
  apply WP.ite_seq
  rule_simp
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  · apply WP.rule_mk2 mk2_specT h hR .disj 65#32 d b hd hb
    refine ⟨by rule_simp [hR.core.rd3 hn], ?_⟩
    intro s' c' r h hB
    rule_simp
    rule_ret
    exact hB.ret h (fun st' i hP => by
      simp [ruleIteElim, St.node, hn, isBoolIteNode, h1, mkDisj, hP])
  apply WP.ite_seq
  rule_simp
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · apply WP.rule_mk_not mk_not_specT h hR d hd
    refine ⟨by rule_simp [hR.core.rd3 hn], ?_⟩
    intro s' c' r h hB
    rule_simp
    rule_guard
    intro hne
    obtain ⟨st', i, hP, hR, hext, hstk, hi, rfl⟩ := hB.ok hne
    have hp' := hext.lt hp
    rw [← hext.id hp]
    apply WP.rule_mk2 mk2_specT h hR .disj 65#32 i a hi (hext.lt ha)
    refine ⟨by rule_simp [hR.core.rd3 (hext.get hn)], ?_⟩
    intro s' c' r h hB
    rule_simp
    rule_ret
    exact hB.ret h (fun st2 i2 hP2 => by
      simp [ruleIteElim, St.node, hn, isBoolIteNode, h0, hP, mkDisj, hP2])
  exact WP.rule_fail h

theorem r_not_ite_elim_spec :
    RuleSpec (State := State) "r_not_ite_elim" (fun _ st pr pa => ruleNotIteElim st pr pa) := by
  rule_begin rNotIteElim
  rule_arity ⟨p, rfl⟩ ⟨k, rfl⟩
  have hp := hR.prems1
  have hk := hR.params1
  obtain ⟨n, hn⟩ := node_of_lv hp
  rule_assign
  rule_guard [hR.core.rdHdr hn]
  intro hop
  obtain ⟨q, rfl, hq⟩ := hR.core.args1 hn hop
  obtain ⟨n', hn'⟩ := node_of_lv hq
  rule_assign [hR.core.rd1 hn]
  rule_guard [hR.core.rdHdr hn']
  intro hop'
  obtain ⟨d, a, b, rfl, hd, ha, hb⟩ := hR.core.args3 hn' hop'
  rule_assign
  apply WP.ite_seq
  rule_simp
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  · apply WP.rule_mk_not mk_not_specT h hR b hb
    refine ⟨by rule_simp [hR.core.rd3 hn'], ?_⟩
    intro s' c' r h hB
    rule_simp
    rule_guard
    intro hne
    obtain ⟨st', i, hP, hR, hext, hstk, hi, rfl⟩ := hB.ok hne
    have hq' := hext.lt hq
    rw [← hext.id hq]
    apply WP.rule_mk2 mk2_specT h hR .disj 65#32 d i (hext.lt hd) hi
    refine ⟨by rule_simp [hR.core.rd3 (hext.get hn')], ?_⟩
    intro s' c' r h hB
    rule_simp
    rule_ret
    exact hB.ret h (fun st2 i2 hP2 => by
      simp [ruleNotIteElim, St.node, hn, hn', isNotNode, isBoolIteNode, h1, hP, mkDisj, hP2])
  apply WP.ite_seq
  rule_simp
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · apply WP.rule_mk_not mk_not_specT h hR d hd
    refine ⟨by rule_simp [hR.core.rd3 hn'], ?_⟩
    intro s1 c1 r h hB
    rule_simp
    rule_guard
    intro hne
    obtain ⟨st1, i, hP, hR, hext, hstk, hi, rfl⟩ := hB.ok hne
    have hq1 := hext.lt hq
    rw [← hext.id hq]
    apply WP.rule_mk_not mk_not_specT h hR a (hext.lt ha)
    refine ⟨by rule_simp [hR.core.rd3 (hext.get hn')], ?_⟩
    intro s2 c2 r h hB
    rule_simp
    rule_guard
    intro hne
    obtain ⟨st2, j, hP', hR, hext', hstk', hj, rfl⟩ := hB.ok hne
    rw [← hext'.id hi]
    apply WP.rule_mk2 mk2_specT h hR .disj 65#32 i j (hext'.lt hi) hj
    refine ⟨by rule_simp, ?_⟩
    intro s' c' r h hB
    rule_simp
    rule_ret
    exact hB.ret h (fun st3 i3 hP3 => by
      simp [ruleNotIteElim, St.node, hn, hn', isNotNode, isBoolIteNode, h0, hP, hP', mkDisj, hP3])
  exact WP.rule_fail h

end Vbcf.Proof
