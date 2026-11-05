import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.RulesBasic3

/-!
# Vbcf proofs: the basic rules with loops (`r_trans`, `r_and_intro`)
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-- Loop invariant of `r_trans`: `j + 1` premises read, the chain so far ends in `bj`. -/
def TransInv (sb : Nat) (s : (KernelState prog State)) (st : VSt) (rest : List Nat) (na a b : Nat) :
    Env → (KernelState prog State) → Prop := fun env s' =>
  s' = s ∧ ∃ (j : Nat) (pw : BitVec 32) (bj : Nat),
    env = [("st", .ptr (.struct "ck"), .ptr sb 0), ("np", .u32, uv (rest.length + 1)),
      ("na", .u32, uv na), ("p", .u32, .u32 pw), ("lhs", .u32, uv (st.id a)),
      ("rhs", .u32, uv (st.id bj)), ("i", .u32, uv (j + 1)), ("r", .u32, .u32 0#32)] ∧
    j ≤ rest.length ∧ st.lv bj ∧
    transChain st rest a b = transChain st (rest.drop j) a bj

theorem r_trans_spec :
    RuleSpec (State := State) "r_trans" (fun _ st pr pa => ruleTrans st pr pa) := by
  rule_begin rTrans
  rcases prems with _ | ⟨p, rest⟩
  · rule_guard
  have hlen : rest.length + 1 ≤ 255 := by simpa using hnp
  rcases params with _ | ⟨x, xs⟩
  rotate_left
  · rule_guard
    intro h0
    simp at hna
    rw [uv_eq_zero_iff (by omega)] at h0
    omega
  rule_guard
  have hp := hR.prem_lt (j := 0) (by simp)
  simp only [List.getElem_cons_zero] at hp
  obtain ⟨n, hn⟩ := node_of_lv hp
  rule_assign
  rule_guard [hR.core.rdHdr hn]
  intro hop
  obtain ⟨a, b, rfl, ha, hb⟩ := hR.core.args2 hn hop
  rule_assign [hR.core.rd2 hn]
  rule_assign [hR.core.rd2 hn]
  rule_assign
  apply WP.loop_seq (TransInv sb s st rest 0 a b)
  · exact ⟨rfl, 0, _, b, rfl, by omega, hb, by simp⟩
  rintro env s' ⟨rfl, j, pw, bj, rfl, hj, hbj, hchain⟩
  rule_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · have hjr : j = rest.length := by omega
    subst hjr
    simp only [List.drop_length, transChain] at hchain
    apply WP.rule_mk_eq mk_eq_specT h hR a bj ha hbj
    refine ⟨by rule_simp, ?_⟩
    intro s' c' r h hB
    rule_simp
    rule_ret
    exact hB.ret h (fun st' i hP => by
      simp [ruleTrans, St.node, hn, isEqNode, hchain, hP])
  · have hq := hR.prem_lt (j := j + 1) (by simp; omega)
    simp only [List.getElem_cons_succ] at hq
    obtain ⟨n', hn'⟩ := node_of_lv hq
    rule_assign [hR.rd_prem (j := j + 1) (by simp; omega)]
    rule_guard [hR.core.rdHdr hn']
    intro hop'
    obtain ⟨a', b', hab, ha', hb'⟩ := hR.core.args2 hn' hop'
    rw [hab] at hn'
    rule_guard [hR.core.rd2 hn']
    intro hab'
    rule_assign [hR.core.rd2 hn']
    apply WP.assign_loop
    rule_simp
    refine ⟨rfl, j + 1, _, b', rfl, by omega, hb', ?_⟩
    rw [hchain, List.drop_eq_getElem_cons hlt]
    simp [transChain, St.node, hn', isEqNode, hab']

/-- Loop invariant of `r_and_intro`: the first `k` premises are on the stack. -/
def AndIntroInv (W : World) (sb : Nat) (X : Ctx) (c0 : CMem) (st : VSt) (prems : List Nat) :
    Env → (KernelState prog State) → Prop := fun env s' =>
  ∃ (c' : CMem) (k : Nat) (ok : BitVec 32),
    env = [("st", .ptr (.struct "ck"), .ptr sb 0), ("np", .u32, uv prems.length),
      ("na", .u32, uv 0), ("i", .u32, uv k), ("ok", .u32, .u32 ok), ("r", .u32, .u32 0#32),
      ("base", .u32, .u32 0#32)] ∧
    Holds W s'.mem sb c' ∧ RCtx W X c0 prems [] c' st ∧ k ≤ prems.length ∧
    StkTop c' st 0 (prems.take k)

theorem r_and_intro_spec :
    RuleSpec (State := State) "r_and_intro" (fun _ st pr pa => ruleAndIntro st pr pa) := by
  rule_begin rAndIntro
  rcases params with _ | ⟨x, xs⟩
  rotate_left
  · rule_guard
    intro h0
    simp at hna
    rw [uv_eq_zero_iff (by omega)] at h0
    omega
  rule_guard
  apply WP.ite_seq
  rule_simp
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  · obtain ⟨p, rfl⟩ := List.length_eq_one_iff.mp h1
    have hp := hR.prems1
    rule_ret
    exact hR.ret h hp (by simp [ruleAndIntro])
  rule_guard
  intro h2
  rule_assign [hsp]
  apply WP.loop_seq (AndIntroInv W sb X c st prems)
  · exact ⟨c, 0, _, rfl, h, hR, by omega, StkTop.nil (by simp [hsp])⟩
  clear h hR
  rintro env s' ⟨c', k, ok, rfl, h, hR, hk, htop⟩
  rule_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · have hkl : k = prems.length := by omega
    subst hkl
    rw [List.take_length] at htop
    apply WP.rule_mkn mkn_specT h hR .conj 1#32 0 prems htop.2 (by have := htop.1; omega)
    refine ⟨by rule_simp, ?_⟩
    intro s' c' r h hB
    rule_simp
    rule_ret
    exact hB.ret h (fun st' i hP => by
      rcases prems with _ | ⟨p, _ | ⟨q, rest⟩⟩
      · simp at h2
      · simp at h2
      · simpa [ruleAndIntro, mkConj] using hP)
  · apply WP.rule_push h hR
    rule_simp [hR.rd_prem hlt]
    intro s2 c2 ok2 h2' hP
    have htop' := fun hok => StkTop.push htop hP hok (hR.prem_lt hlt)
    have hR2 := hP.1
    clear h hR
    have h := h2'
    have hR := hR2
    clear h2' hR2
    rule_guard
    intro hok
    apply WP.assign_loop
    rule_simp
    refine ⟨c2, k + 1, ok2, rfl, h, hR, by omega, ?_⟩
    rw [List.take_succ_eq_append_getElem hlt]
    exact htop' hok

end Vbcf.Proof
