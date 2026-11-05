import Vbcf.Proof.Bool3
import Vbcf.Proof.Bool5
import Vbcf.Proof.Bool6

/-!
# Vbcf proofs: the Bool family (`Vbcf/Rules/Bool.lean`)

* `Bool1`: shared infrastructure (`HRet`/`HQ`/`HPost`, `Built.trans`, `CoreInv.rd*_ext`,
  `WP.h_guard`, `WP.h_fail`, `WP.rule_hcall`, `WP.ite_seq2`, `WP.guard_lit`).
* `Bool2`: the helpers `bl_head_of_spec`, `bl_equiv_elim_clause_spec`,
  `bl_not_equiv_elim_clause_spec`, `bl_cnf_pos_clause_spec`, `bl_cnf_neg_clause_spec`,
  `bl_ite_eq_body_spec` (each stated on the Lean helper it mirrors).
* `Bool3`: `r_implies_elim`, `r_not_implies_elim`, `r_equiv_elim`, `r_not_equiv_elim`,
  `r_xor_elim`, `r_not_xor_elim`, `r_ite_elim`, `r_not_ite_elim`.
* `Bool4`: `bl_mk_nots_spec` (`Bcf.mkNots`), and the call rules `WP.rule_mk_nots`,
  `WP.rule_push_args`.
* `Bool5`: `r_not_and`, `r_cnf_and_pos`, `r_cnf_and_neg`, `r_cnf_or_pos`, `r_cnf_or_neg`,
  `r_cnf_implies_pos`, `r_cnf_implies_neg`.
* `Bool6`: `r_cnf_equiv_pos`, `r_cnf_equiv_neg`, `r_cnf_xor_pos`, `r_cnf_xor_neg`,
  `r_cnf_ite_pos`, `r_cnf_ite_neg`, `r_ite_eq`.

Every rule theorem `r_x_spec` has exactly the type of the corresponding field of `RuleSpecs`.
-/
