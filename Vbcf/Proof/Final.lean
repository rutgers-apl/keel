import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Replay
import Vbcf.Proof.KeepFacts
import Vbcf.Proof.Basic
import Vbcf.Proof.Bool
import Vbcf.Proof.Clause
import Vbcf.Proof.Eval
import Vbcf.Proof.Aci
import Vbcf.Proof.Poly
import Vbcf.Proof.Rewrite
import Vbcf.Proof.Bitblast
import Vbcf.Proof.Goal

/-!
# Vbcf proofs: assembly

`ruleSpecs` collects one proved `RuleSpec` per rule function into `RuleSpecs`;
with `ck_goal_spec`, the entry theorems of `Replay9` then hold unconditionally:

* `vbcf_check_proof_sound'`: `vbcf_check_proof(goal_exprs, goal, p, size)`
  never gets stuck, leaves the memory exactly as it found it, and if it returns
  0 then the proof it copied from user space decodes and its goal holds under
  no assignment, as does the verifier's goal if one is passed
  (`vbcf_check_proof_goal_sound'` states that case alone);
* `vbcf_check_sound'`: the same for `vbcf_check` on an in-kernel buffer,
  changing no block other than the buffer's.
-/

namespace Vbcf.Proof

variable {State : Type}
open Bcf

/-- Every rule function meets its specification. -/
theorem ruleSpecs : RuleSpecs (State := State) where
  assume := r_assume_spec
  refl := r_refl_spec
  symm := r_symm_spec
  trans := r_trans_spec
  cong := r_cong_spec
  trueIntro := r_true_intro_spec
  trueElim := r_true_elim_spec
  falseIntro := r_false_intro_spec
  falseElim := r_false_elim_spec
  eqResolve := r_eq_resolve_spec
  modusPonens := r_modus_ponens_spec
  notNotElim := r_not_not_elim_spec
  contra := r_contra_spec
  andElim := r_and_elim_spec
  andIntro := r_and_intro_spec
  notOrElim := r_not_or_elim_spec
  split := r_split_spec
  evaluate := r_evaluate_spec
  impliesElim := r_implies_elim_spec
  notImpliesElim := r_not_implies_elim_spec
  equivElim := r_equiv_elim_spec
  notEquivElim := r_not_equiv_elim_spec
  xorElim := r_xor_elim_spec
  notXorElim := r_not_xor_elim_spec
  iteElim := r_ite_elim_spec
  notIteElim := r_not_ite_elim_spec
  notAnd := r_not_and_spec
  cnfAndPos := r_cnf_and_pos_spec
  cnfAndNeg := r_cnf_and_neg_spec
  cnfOrPos := r_cnf_or_pos_spec
  cnfOrNeg := r_cnf_or_neg_spec
  cnfImpliesPos := r_cnf_implies_pos_spec
  cnfImpliesNeg := r_cnf_implies_neg_spec
  cnfEquivPos := r_cnf_equiv_pos_spec
  cnfEquivNeg := r_cnf_equiv_neg_spec
  cnfXorPos := r_cnf_xor_pos_spec
  cnfXorNeg := r_cnf_xor_neg_spec
  cnfItePos := r_cnf_ite_pos_spec
  cnfIteNeg := r_cnf_ite_neg_spec
  iteEq := r_ite_eq_spec
  distinctValues := r_distinct_values_spec
  resolution := r_resolution_spec
  factoring := r_factoring_spec
  reordering := r_reordering_spec
  absorb := r_absorb_spec
  aciNorm := r_aci_norm_spec
  polyNorm := r_poly_norm_spec
  polyNormEq := r_poly_norm_eq_spec
  rewrite := r_rewrite_spec
  bitblast := r_bitblast_spec

open EmbC in
/-- **Soundness of the C entry point against the verifier's goal**,
unconditionally: given the verifier's arena (block `gb` holding the words
`gws`, with the goal node inside it — `hdrVlen` is its argument count),
`vbcf_check_proof` never gets stuck, leaves every memory block as it found
it, and if it returns 0 then the verifier's goal holds under no assignment. -/
theorem vbcf_check_proof_goal_sound' (gb : Nat) (gws : Array (BitVec 32)) (goal size : BitVec 32) :
    FnSpec (State := State) Vbcf.prog "vbcf_check_proof"
      (fun vs s => vs = [.ptr gb 0, .u32 goal, .uptr, .u32 size] ∧
        s.mem.block? gb = some ⟨.u32, gws.map EmbC.Val.u32⟩ ∧ goal.toNat < gws.size ∧
        goal.toNat + 1 + hdrVlen (wordFn gws goal.toNat) ≤ gws.size)
      (fun _ s rv s' => (∀ b, s'.mem.block? b = s.mem.block? b) ∧ ∃ r, rv = some (.u32 r) ∧
        (r = 0#32 → ∀ ρ, ¬ Bcf.arenaHolds (wordFn gws) ρ goal.toNat)) := by
  apply FnSpec.mono (vbcf_check_proof_sound ruleSpecs rulesKeepFacts ck_goal_spec (some (gb, gws)) goal size)
  · rintro vs s rv s' _ ⟨hm, r, hr, hacc⟩
    exact ⟨hm, r, hr, fun h0 => (hacc h0).2⟩

open EmbC in
/-- **Soundness of the C entry point**, unconditionally, for every goal
argument: `vbcf_check_proof` never gets stuck, leaves every memory block as it
found it, and if it returns 0 then the words it copied from the caller decode
to a proof whose goal holds under no assignment, and so does the verifier's
goal if one was passed. -/
theorem vbcf_check_proof_sound' (ga : GArg) (goal size : BitVec 32) :
    FnSpec (State := State) Vbcf.prog "vbcf_check_proof"
      (fun vs s => vs = [gxVal ga, .u32 goal, .uptr, .u32 size] ∧ ArenaIn s.mem goal.toNat ga)
      (fun _ s rv s' => (∀ b, s'.mem.block? b = s.mem.block? b) ∧ ∃ r, rv = some (.u32 r) ∧
        (r = 0#32 → (∃ P g,
          Bcf.decode (wordsToBytes (copiedWords s (size.toNat / 4))) = .ok P ∧
          ∀ ρ, ¬ holds P.pool ρ g) ∧ GoalRefuted goal.toNat ga)) :=
  vbcf_check_proof_sound ruleSpecs rulesKeepFacts ck_goal_spec ga goal size

open EmbC in
/-- **Soundness of the C in-kernel entry point**, unconditionally. -/
theorem vbcf_check_sound' (pb : Nat) (ws : Array (BitVec 32)) (n : BitVec 32) (ga : GArg)
    (goal : BitVec 32) :
    FnSpec (State := State) Vbcf.prog "vbcf_check"
      (fun vs s => vs = [gxVal ga, .u32 goal, .ptr pb 0, .u32 n] ∧
        s.mem.block? pb = some ⟨.u32, ws.map EmbC.Val.u32⟩ ∧ n.toNat = ws.size ∧
        ArenaIn s.mem goal.toNat ga ∧ ArenaNot pb ga)
      (fun _ s rv s' => OnlyBlockChanged s.mem s'.mem pb ∧ ∃ r, rv = some (.u32 r) ∧
        (r = 0#32 → (∃ P g, Bcf.decode (wordsToBytes ws) = .ok P ∧ ∀ ρ, ¬ holds P.pool ρ g) ∧
          GoalRefuted goal.toNat ga)) :=
  vbcf_check_sound ruleSpecs rulesKeepFacts ck_goal_spec pb ws n ga goal

end Vbcf.Proof
