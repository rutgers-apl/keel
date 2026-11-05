import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.RuleLib

/-!
# Vbcf proofs: the basic rules (continued)
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

theorem r_eq_resolve_spec :
    RuleSpec (State := State) "r_eq_resolve" (fun _ st pr pa => ruleEqResolve st pr pa) := by
  rule_begin rEqResolve
  rule_arity ⟨p, q, rfl⟩ rfl
  have ⟨hp, hq⟩ := hR.prems2
  obtain ⟨n, hn⟩ := node_of_lv hq
  rule_assign
  rule_guard [hR.core.rdHdr hn]
  intro hop
  obtain ⟨a, b, rfl, ha, hb⟩ := hR.core.args2 hn hop
  rule_guard [hR.core.rd2 hn]
  intro hap
  rule_ret [hR.core.rd2 hn]
  exact hR.ret h hb (by simp [ruleEqResolve, St.node, hn, isEqNode, hap])

theorem r_modus_ponens_spec :
    RuleSpec (State := State) "r_modus_ponens" (fun _ st pr pa => ruleModusPonens st pr pa) := by
  rule_begin rModusPonens
  rule_arity ⟨p, q, rfl⟩ rfl
  have ⟨hp, hq⟩ := hR.prems2
  obtain ⟨n, hn⟩ := node_of_lv hq
  rule_assign
  rule_guard [hR.core.rdHdr hn]
  intro hop
  obtain ⟨a, b, rfl, ha, hb⟩ := hR.core.args2 hn hop
  rule_guard [hR.core.rd2 hn]
  intro hap
  rule_ret [hR.core.rd2 hn]
  exact hR.ret h hb (by simp [ruleModusPonens, St.node, hn, isImpliesNode, hap])

theorem r_not_not_elim_spec :
    RuleSpec (State := State) "r_not_not_elim" (fun _ st pr pa => ruleNotNotElim st pr pa) := by
  rule_begin rNotNotElim
  rule_arity ⟨p, rfl⟩ rfl
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
  obtain ⟨a, rfl, ha⟩ := hR.core.args1 hn' hop'
  rule_ret [hR.core.rd1 hn']
  exact hR.ret h ha (by simp [ruleNotNotElim, St.node, hn, hn', isNotNode])

theorem r_contra_spec :
    RuleSpec (State := State) "r_contra" (fun X st pr pa => ruleContra X.bi st pr pa) := by
  rule_begin rContra
  rule_arity ⟨p, q, rfl⟩ rfl
  have ⟨hp, hq⟩ := hR.prems2
  obtain ⟨n, hn⟩ := node_of_lv hq
  rule_assign
  rule_guard [hR.core.rdHdr hn]
  intro hop
  obtain ⟨a, rfl, ha⟩ := hR.core.args1 hn hop
  rule_guard [hR.core.rd1 hn]
  intro hap
  rule_ret
  exact hR.ret h hR.ff_lt (by simp [ruleContra, St.node, hn, isNotNode, hap, st.lt hR.ff_lt])

theorem r_and_elim_spec :
    RuleSpec (State := State) "r_and_elim" (fun _ st pr pa => ruleAndElim st pr pa) := by
  rule_begin rAndElim
  rule_arity ⟨p, rfl⟩ ⟨k, rfl⟩
  have hp := hR.prems1
  have hk := hR.params1
  obtain ⟨n, hn⟩ := node_of_lv hp
  rule_assign
  rule_guard [hR.core.rdHdr hn]
  intro hop
  obtain ⟨args, rfl, hsz, -, hargs⟩ := hR.core.argsN hn hop
  rule_assign
  rule_guard [hR.core.rdN hn]
  intro hka
  rule_ret [hR.core.rdN hn]
  exact hR.ret h (hargs k hka) (by simp [ruleAndElim, St.node, hn, isConjNode, hka])

end Vbcf.Proof
