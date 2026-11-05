import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Bitblast13

/-!
# Vbcf proofs: the Bitblast family, part 14 — `r_bitblast`
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf


/-- After the bit-blast check: `ok` holds `r`, and a non-zero `r` means the Lean rule succeeds. -/
def BbRuleMid (W : World) (sb : Nat) (X : Ctx) (c : CMem) (x : Nat) (st : VSt) (e : Nat)
    (env0 env' : Env) (s' : (KernelState prog State)) : Prop :=
  ∃ (r : BitVec 32) (c' : CMem), env' = env0.set "ok" (.u32 r) ∧ Holds W s'.mem sb c' ∧
    RCtx W X c [] [x] c' st ∧ (r ≠ 0#32 → ruleBitblast X.bi X.ei st [] [x] = some (st.toSt, e))

theorem r_bitblast_spec :
    RuleSpec (State := State) "r_bitblast" (fun X st pr pa => ruleBitblast X.bi X.ei st pr pa) := by
  rule_begin rBitblast
  rule_arity rfl ⟨x, rfl⟩
  have hx := hR.params1
  apply WP.rule_expr_at expr_at_spec' h hR x hx
  refine ⟨by rule_simp, ?_⟩
  intro r her
  rule_simp
  rule_guard
  intro hne
  obtain ⟨e, hee, he, rfl⟩ := her.ok hne
  obtain ⟨ne, hne'⟩ := node_of_lv he
  rule_guard [hR.core.rdHdr hne']
  intro hop
  obtain ⟨a, b, rfl, ha, hb⟩ := hR.core.args2 hne' hop
  rule_assign [hR.core.rd2 hne']
  rule_assign [hR.core.rd2 hne']
  obtain ⟨na, hna⟩ := node_of_lv ha
  apply WP.rule_ty_of ty_of_spec
  obtain ⟨t, ht, hty, hfit⟩ := hR.core.tyOf hna
  rule_simp [hR.core.rdHdr hna, hty]
  have hiseq : (st.pool[e]?).bind isEqNode = some (a, b) := by simp [hne', isEqNode]
  apply WP.seq_mid_env (BbRuleMid W sb X c x st e)
  · apply WP.ite
    rule_simp [uv_lt (show tyW t < 4294967296 from tyW_lt_two_pow hfit) (show 4096 < 4294967296 by omega)]
    obtain ⟨argTys, t', -, hrt, ht', -⟩ := hR.core.ok.retype hna
    rw [ht] at ht'
    simp only [Option.some.injEq] at ht'
    subst ht'
    refine ⟨fun hlt => ?_, fun hge => ?_⟩
    · obtain ⟨w, rfl⟩ := (tyW_lt_bool_iff hfit).mp hlt
      have hbv : opC na.op % 8 = 0 := (resultTy_bv_iff hrt).mp ⟨w, rfl⟩
      obtain ⟨nb, hnb⟩ := node_of_lv hb
      apply WP.ifRet
      rule_simp [hR.core.rdHdr hnb]
      refine ⟨fun _ => by simp only [LoopQ, RuleQ]; exact RuleRet.fail h, fun hfb => ?_⟩
      obtain ⟨opb, bs⟩ := nb
      simp only at hfb
      subst hfb
      refine WP.bb_call_last (bb_term_spec W sb X c c [] [x] st a b na bs) ?_
        ⟨rfl, h, hR, hna, by vlv, hbv, hnb, by vlv⟩ ?_
      · rule_simp
      rintro s2 r ⟨c', h', hR', hres⟩
      rule_simp
      simp only [LoopQ]
      refine ⟨r, c', by simp [Env.set], h', hR', fun hr0 => ?_⟩
      obtain ⟨-, -, hbt⟩ := hres hr0
      simp [ruleBitblast, hee, hiseq, ht, bitsOf, hnb, hbt]
    · apply WP.ite
      rule_simp [uv_tyW_eq_bool hfit]
      refine ⟨fun hbool => ?_, fun hnbool => ?_⟩
      · subst hbool
        refine WP.bb_call_last (bb_atom_spec W sb X c c [] [x] st a b na) ?_
          ⟨rfl, h, hR, hna, by vlv, hb⟩ ?_
        · rule_simp
        rintro s2 r ⟨c', h', hR', hres⟩
        rule_simp
        simp only [LoopQ]
        refine ⟨r, c', by simp [Env.set], h', hR', fun hr0 => ?_⟩
        obtain ⟨-, -, hat⟩ := hres hr0
        simp [ruleBitblast, hee, hiseq, ht, hat]
      · apply WP.ret
        simp only [evalE, LoopQ, RuleQ]
        exact RuleRet.fail h
  rintro env' s' ⟨r, c', rfl, h', hR', hres⟩
  have h := h'
  have hR := hR'
  rule_simp
  rule_guard
  intro hr0
  rule_ret
  exact hR.ret h he (hres hr0)

end Vbcf.Proof
