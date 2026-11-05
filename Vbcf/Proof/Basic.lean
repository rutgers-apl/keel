import Vbcf.Proof.RulesBasic
import Vbcf.Proof.RulesBasic2
import Vbcf.Proof.RulesBasic3
import Vbcf.Proof.RulesBasic4
import Vbcf.Proof.RulesBasic5

/-!
# Vbcf proofs: the basic rules (`Vbcf/Rules/Basic.lean`)

All seventeen rule functions of `Vbcf/Rules/Basic.lean` meet the `RuleSpec` that
`RuleSpecs` (in `ReplaySpecs.lean`) expects:

* `RulesBasic`:  `r_true_elim_spec`;
* `RulesBasic2`: `r_eq_resolve_spec`, `r_modus_ponens_spec`, `r_not_not_elim_spec`,
  `r_contra_spec`, `r_and_elim_spec`;
* `RulesBasic3`: `r_true_intro_spec`, `r_false_intro_spec`, `r_false_elim_spec`, `r_symm_spec`,
  `r_not_or_elim_spec`, `r_split_spec`, `r_assume_spec`, `r_refl_spec`;
* `RulesBasic4`: `r_trans_spec`, `r_and_intro_spec` (loops over the premises);
* `RulesBasic5`: `r_cong_spec` (two loops filling the scratch stack, two `mkn`).
-/
