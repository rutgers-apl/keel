import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.KeepFacts1
import Vbcf.Proof.Replay2

/-!
# Vbcf proofs: the Lean rules keep the fact array

Discharges the hypothesis `RulesKeepFacts` of `Vbcf.Proof.Replay2`: no rule of
`Bcf.applyRule` (with the rewrite table `Bcf.rwTable`) changes `St.facts`.
The rule-by-rule argument, generic in the rewrite table, is
`Vbcf.Proof.KF.applyRule_keep` in `Vbcf.Proof.KeepFacts1`.
-/

namespace Vbcf.Proof

variable {State : Type}

theorem rulesKeepFacts : RulesKeepFacts :=
  fun g bi ei st r prems params st' f h =>
    KF.applyRule_keep Bcf.rwTable g bi ei st r prems params st' f h

end Vbcf.Proof
