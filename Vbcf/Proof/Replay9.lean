import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Replay8
import Vbcf.Proof.Load
import Vbcf.Proof.Compact

/-!
# Vbcf proofs: the entry points, with the loading phase discharged

`ck_init_spec`, `ck_load_spec`, `ck_scan_spec` (from `Vbcf.Proof.Load`) discharge
the loading-phase hypotheses, `ck_compact_spec` (from `Vbcf.Proof.Compact`) the
compaction between steps.  What remains assumed: `RuleSpecs` (the fifty
rule functions), `RulesKeepFacts` (a statement about the Lean rules alone) and
`GoalSpec` (the goal comparison).

* `vbcf_check_full`, `vbcf_check_proof_full`: `VbcfCheckSpec`, `VbcfCheckProofSpec`;
* `vbcf_check_sound`, `vbcf_check_proof_sound`: **if the C entry returns 0, the
  goal of the proof it checked is unsatisfiable** (`Bcf.checkBcf_sound`), **and so
  is the verifier's goal** when one is passed;
* `vbcf_check_mem`, `vbcf_check_proof_mem`: on every return, memory is as
  `OnlyBlockChanged` (resp. exact equality) says.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

theorem vbcf_check_full (hR : RuleSpecs (State := State)) (hK : RulesKeepFacts) (hG : GoalSpec (State := State)) : VbcfCheckSpec (State := State) :=
  vbcf_check_spec hR hK ck_init_spec ck_load_spec ck_scan_spec hG ck_compact_spec

theorem vbcf_check_proof_full (hR : RuleSpecs (State := State)) (hK : RulesKeepFacts) (hG : GoalSpec (State := State)) :
    VbcfCheckProofSpec (State := State) :=
  vbcf_check_proof_spec (vbcf_check_full hR hK hG)

/-- **Soundness of `vbcf_check`**: never stuck; if it returns 0, the words
decode to a proof whose goal is unsatisfiable, and the verifier's goal (if one
is passed) is unsatisfiable. -/
theorem vbcf_check_sound (hR : RuleSpecs (State := State)) (hK : RulesKeepFacts) (hG : GoalSpec (State := State)) :
    ∀ (pb : Nat) (ws : Array (BitVec 32)) (n : BitVec 32) (ga : GArg) (goal : BitVec 32),
      FnSpec (State := State) Vbcf.prog "vbcf_check"
        (fun vs s => vs = [gxVal ga, .u32 goal, .ptr pb 0, .u32 n] ∧
          s.mem.block? pb = some ⟨.u32, ws.map EmbC.Val.u32⟩ ∧ n.toNat = ws.size ∧
          ArenaIn s.mem goal.toNat ga ∧ ArenaNot pb ga)
        (fun _ s rv s' => OnlyBlockChanged s.mem s'.mem pb ∧ ∃ r, rv = some (.u32 r) ∧
          (r = 0#32 → (∃ P g, Bcf.decode (wordsToBytes ws) = .ok P ∧ ∀ ρ, ¬ holds P.pool ρ g) ∧
            GoalRefuted goal.toNat ga)) := by
  intro pb ws n ga goal
  apply FnSpec.mono (vbcf_check_full hR hK hG pb ws n ga goal)
  rintro vs s rv s' _ ⟨hm, r, hr, hacc⟩
  refine ⟨hm, r, hr, fun h0 => ?_⟩
  obtain ⟨⟨P, g, hd, hc⟩, hg⟩ := hacc h0
  exact ⟨⟨P, g, hd, checkBcf_sound P hc⟩, hg⟩

/-- **Soundness of `vbcf_check_proof`**: never stuck; if it returns 0, the
proof made of the words it copied in decodes, its goal is unsatisfiable, and
the verifier's goal (if one is passed) is unsatisfiable.  Memory is left
exactly as it was. -/
theorem vbcf_check_proof_sound (hR : RuleSpecs (State := State)) (hK : RulesKeepFacts) (hG : GoalSpec (State := State)) :
    ∀ (ga : GArg) (goal size : BitVec 32),
      FnSpec (State := State) Vbcf.prog "vbcf_check_proof"
        (fun vs s => vs = [gxVal ga, .u32 goal, .uptr, .u32 size] ∧ ArenaIn s.mem goal.toNat ga)
        (fun _ s rv s' => (∀ b, s'.mem.block? b = s.mem.block? b) ∧ ∃ r, rv = some (.u32 r) ∧
          (r = 0#32 → (∃ P g,
            Bcf.decode (wordsToBytes (copiedWords s (size.toNat / 4))) = .ok P ∧
            ∀ ρ, ¬ holds P.pool ρ g) ∧ GoalRefuted goal.toNat ga)) := by
  intro ga goal size
  apply FnSpec.mono (vbcf_check_proof_full hR hK hG ga goal size)
  rintro vs s rv s' _ ⟨hm, r, hr, hacc⟩
  refine ⟨hm, r, hr, fun h0 => ?_⟩
  obtain ⟨⟨P, g, hd, hc⟩, hg⟩ := hacc h0
  exact ⟨⟨P, g, hd, checkBcf_sound P hc⟩, hg⟩

/-- **Memory, `vbcf_check`**: on every return, only the proof block may have
changed, and it keeps its size. -/
theorem vbcf_check_mem (hR : RuleSpecs (State := State)) (hK : RulesKeepFacts) (hG : GoalSpec (State := State)) :
    ∀ (pb : Nat) (ws : Array (BitVec 32)) (n : BitVec 32) (ga : GArg) (goal : BitVec 32),
      FnSpec (State := State) Vbcf.prog "vbcf_check"
        (fun vs s => vs = [gxVal ga, .u32 goal, .ptr pb 0, .u32 n] ∧
          s.mem.block? pb = some ⟨.u32, ws.map EmbC.Val.u32⟩ ∧ n.toNat = ws.size ∧
          ArenaIn s.mem goal.toNat ga ∧ ArenaNot pb ga)
        (fun _ s _ s' => OnlyBlockChanged s.mem s'.mem pb) := by
  intro pb ws n ga goal
  exact FnSpec.mono (vbcf_check_full hR hK hG pb ws n ga goal) (fun _ _ _ _ _ h => h.1)

/-- **Memory, `vbcf_check_proof`**: on every return, every block is as before
(the copy buffer is freed, nothing else is touched). -/
theorem vbcf_check_proof_mem (hR : RuleSpecs (State := State)) (hK : RulesKeepFacts) (hG : GoalSpec (State := State)) :
    ∀ (ga : GArg) (goal size : BitVec 32),
      FnSpec (State := State) Vbcf.prog "vbcf_check_proof"
        (fun vs s => vs = [gxVal ga, .u32 goal, .uptr, .u32 size] ∧ ArenaIn s.mem goal.toNat ga)
        (fun _ s _ s' => ∀ b, s'.mem.block? b = s.mem.block? b) := by
  intro ga goal size
  exact FnSpec.mono (vbcf_check_proof_full hR hK hG ga goal size) (fun _ _ _ _ _ h => h.1)

end Vbcf.Proof
