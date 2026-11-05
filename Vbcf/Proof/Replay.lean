import Vbcf.Proof.Replay1
import Vbcf.Proof.Replay2
import Vbcf.Proof.Replay3
import Vbcf.Proof.Replay4
import Vbcf.Proof.Replay5
import Vbcf.Proof.Replay6
import Vbcf.Proof.Replay7
import Vbcf.Proof.Replay8
import Vbcf.Proof.Replay9

/-!
# Vbcf proofs: the replay phase and the entry points

* `Replay1` — `ck_rule` (`ck_rule_spec : RuleSpecs → CkRuleSpec`);
* `Replay2` — the step invariant `SInv`, `RulesKeepFacts`;
* `Replay3` — `ck_step` (`ck_step_spec`);
* `Replay4` — `Shape` (blocks never change size; `FnSpec.withShape`), `Mem.fill`,
  `ck_free` (`ck_free_spec`);
* `Replay5` — `Accepts`, `accepts_of_replay`, `SInv.next`, `CkRunSpec`, `RunInv`,
  `GoalMid` (after the goal comparison);
* `Replay6` — `ck_run` (`ck_run_spec`), with the goal comparison (`GoalSpec`) and
  `goalRefuted_of` (the verifier's goal is refuted, via `GoalSem.arena_refuted`);
* `Replay7` — `vbcf_check` (`vbcf_check_spec : … → VbcfCheckSpec`);
* `Replay8` — `vbcf_check_proof` (`vbcf_check_proof_spec : VbcfCheckSpec → VbcfCheckProofSpec`);
* `Replay9` — with the loading phase and `ck_compact` (`Compact`) discharged: `vbcf_check_full`,
  `vbcf_check_proof_full`, the soundness corollaries `vbcf_check_sound`,
  `vbcf_check_proof_sound`, and the memory statements `vbcf_check_mem`,
  `vbcf_check_proof_mem`.  Remaining hypotheses: `RuleSpecs`, `RulesKeepFacts`,
  `GoalSpec`.
-/
