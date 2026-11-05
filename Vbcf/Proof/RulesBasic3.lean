import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Bool1

/-!
# Vbcf proofs: the basic rules (continued): rules without loops
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

theorem r_true_intro_spec :
    RuleSpec (State := State) "r_true_intro" (fun X st pr pa => ruleTrueIntro X.bi st pr pa) := by
  rule_begin rTrueIntro
  rule_arity ⟨p, rfl⟩ rfl
  have hp := hR.prems1
  apply WP.rule_mk_eq mk_eq_specT h hR p X.bi.tt hp hR.tt_lt
  refine ⟨by rule_simp, ?_⟩
  intro s' c' r h hB
  rule_simp
  rule_ret
  exact hB.ret h (fun st' i hP => by simp [ruleTrueIntro, hP])

theorem r_false_intro_spec :
    RuleSpec (State := State) "r_false_intro" (fun X st pr pa => ruleFalseIntro X.bi st pr pa) := by
  rule_begin rFalseIntro
  rule_arity ⟨p, rfl⟩ rfl
  have hp := hR.prems1
  obtain ⟨n, hn⟩ := node_of_lv hp
  rule_assign
  rule_guard [hR.core.rdHdr hn]
  intro hop
  obtain ⟨a, rfl, ha⟩ := hR.core.args1 hn hop
  apply WP.rule_mk_eq mk_eq_specT h hR a X.bi.ff ha hR.ff_lt
  refine ⟨by rule_simp [hR.core.rd1 hn], ?_⟩
  intro s' c' r h hB
  rule_simp
  rule_ret
  exact hB.ret h (fun st' i hP => by simp [ruleFalseIntro, St.node, hn, isNotNode, hP])

theorem r_false_elim_spec :
    RuleSpec (State := State) "r_false_elim" (fun X st pr pa => ruleFalseElim X.bi st pr pa) := by
  rule_begin rFalseElim
  rule_arity ⟨p, rfl⟩ rfl
  have hp := hR.prems1
  obtain ⟨n, hn⟩ := node_of_lv hp
  rule_assign
  rule_guard [hR.core.rdHdr hn]
  intro hop
  obtain ⟨a, b, rfl, ha, hb⟩ := hR.core.args2 hn hop
  rule_guard [hR.core.rd2 hn]
  intro hbf
  apply WP.rule_mk_not mk_not_specT h hR a ha
  refine ⟨by rule_simp [hR.core.rd2 hn], ?_⟩
  intro s' c' r h hB
  rule_simp
  rule_ret
  exact hB.ret h (fun st' i hP => by simp [ruleFalseElim, St.node, hn, isEqNode, hbf, hP])

theorem r_symm_spec :
    RuleSpec (State := State) "r_symm" (fun _ st pr pa => ruleSymm st pr pa) := by
  rule_begin rSymm
  rule_arity ⟨p, rfl⟩ rfl
  have hp := hR.prems1
  obtain ⟨n, hn⟩ := node_of_lv hp
  rule_assign
  apply WP.ite_seq
  rule_simp [hR.core.rdHdr hn]
  refine ⟨fun hop => ?_, fun hop => ?_⟩
  · obtain ⟨a, b, rfl, ha, hb⟩ := hR.core.args2 hn hop
    apply WP.rule_mk_eq mk_eq_specT h hR b a hb ha
    refine ⟨by rule_simp [hR.core.rd2 hn], ?_⟩
    intro s' c' r h hB
    rule_simp
    rule_ret
    exact hB.ret h (fun st' i hP => by simp [ruleSymm, St.node, hn, isEqNode, hP])
  rule_guard [hR.core.rdHdr hn]
  intro hop'
  obtain ⟨q, rfl, hq⟩ := hR.core.args1 hn hop'
  obtain ⟨n', hn'⟩ := node_of_lv hq
  rule_assign [hR.core.rd1 hn]
  rule_guard [hR.core.rdHdr hn']
  intro hop2
  obtain ⟨a, b, rfl, ha, hb⟩ := hR.core.args2 hn' hop2
  apply WP.rule_mk_eq mk_eq_specT h hR b a hb ha
  refine ⟨by rule_simp [hR.core.rd2 hn'], ?_⟩
  intro s' c' r h hB
  rule_simp
  rule_guard
  intro hne
  obtain ⟨st', i, hP, hR, hext, hstk, hi, rfl⟩ := hB.ok hne
  apply WP.rule_mk_not mk_not_specT h hR i hi
  refine ⟨by rule_simp, ?_⟩
  intro s' c' r h hB
  rule_simp
  rule_ret
  exact hB.ret h (fun st2 i2 hP2 => by
    simp [ruleSymm, St.node, hn, hn', isEqNode, isNotNode, hP, hP2])

theorem r_not_or_elim_spec :
    RuleSpec (State := State) "r_not_or_elim" (fun _ st pr pa => ruleNotOrElim st pr pa) := by
  rule_begin rNotOrElim
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
  rule_assign
  rule_guard [hR.core.rdN hn']
  intro hka
  apply WP.rule_mk_not mk_not_specT h hR args[k] (hargs k hka)
  refine ⟨by rule_simp [hR.core.rdN hn'], ?_⟩
  intro s' c' r h hB
  rule_simp
  rule_ret
  exact hB.ret h (fun st' i hP => by
    simp [ruleNotOrElim, St.node, hn, hn', isNotNode, isDisjNode, hka, hP])

theorem r_split_spec :
    RuleSpec (State := State) "r_split" (fun X st pr pa => ruleSplit X.ei st pr pa) := by
  rule_begin rSplit
  rule_arity rfl ⟨x, rfl⟩
  have hx := hR.params1
  apply WP.rule_expr_at expr_at_spec' h hR x hx
  refine ⟨by rule_simp, ?_⟩
  intro r her
  rule_simp
  rule_guard
  intro hne
  obtain ⟨a, hea, ha, rfl⟩ := her.ok hne
  apply WP.rule_mk_not mk_not_specT h hR a ha
  refine ⟨by rule_simp, ?_⟩
  intro s' c' r h hB
  rule_simp
  rule_guard
  intro hne
  obtain ⟨st', i, hP, hR, hext, hstk, hi, rfl⟩ := hB.ok hne
  rw [← hext.id ha]
  apply WP.rule_mk2 mk2_specT h hR .disj 65#32 a i (hext.lt ha) hi
  refine ⟨by rule_simp, ?_⟩
  intro s' c' r h hB
  rule_simp
  rule_ret
  exact hB.ret h (fun st2 i2 hP2 => by simp [ruleSplit, hea, hP, mkDisj, hP2])

theorem r_assume_spec :
    RuleSpec (State := State) "r_assume" (fun X st pr pa => ruleAssume X.goal X.ei st pr pa) := by
  rule_begin rAssume
  rule_arity rfl ⟨x, rfl⟩
  have hx := hR.params1
  apply WP.rule_expr_at expr_at_spec' h hR x hx
  refine ⟨by rule_simp, ?_⟩
  intro r her
  unfold EiRes at her
  split at her
  · subst her
    rule_simp
    rule_guard
  · rename_i g hg
    obtain ⟨hgl, rfl⟩ := her
    obtain ⟨n, hn⟩ := node_of_lv hgl
    rule_simp
    rule_guard
    intro hgoal
    apply WP.rule_ty_of ty_of_spec
    obtain ⟨t, ht, hty, hfit⟩ := hR.core.tyOf hn
    rule_simp [hR.core.rdHdr hn, hty]
    rule_guard [uv_tyW_eq_bool hfit]
    intro htb
    subst htb
    rule_ret
    subst hgoal
    exact hR.ret h hgl (by simp [ruleAssume, hg, st.lt hgl, ht])

theorem r_refl_spec :
    RuleSpec (State := State) "r_refl" (fun X st pr pa => ruleRefl X.ei st pr pa) := by
  rule_begin rRefl
  rule_arity rfl ⟨x, rfl⟩
  have hx := hR.params1
  apply WP.rule_expr_at expr_at_spec' h hR x hx
  refine ⟨by rule_simp, ?_⟩
  intro r her
  rule_simp
  rule_guard
  intro hne
  obtain ⟨a, hea, ha, rfl⟩ := her.ok hne
  obtain ⟨n, hn⟩ := node_of_lv ha
  apply WP.rule_ty_of ty_of_spec
  obtain ⟨t, ht, hty, hfit⟩ := hR.core.tyOf hn
  rule_simp [hR.core.rdHdr hn, hty]
  rule_guard [uv_tyW_ge_list hfit]
  intro hsc
  apply WP.rule_mk_eq mk_eq_specT h hR a a ha ha
  refine ⟨by rule_simp, ?_⟩
  intro s' c' r h hB
  rule_simp
  rule_ret
  exact hB.ret h (fun st' i hP => by simp_all [ruleRefl])

end Vbcf.Proof
