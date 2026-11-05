import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.GoalSpecs
import Vbcf.Proof.LoadSpec

/-!
# Vbcf proofs: the verifier's goal (meaning of a match)

* `arena_eval_of_goalOK`: when `GoalOK pool w g goal` holds, the pool's goal
  `g` under the renamed state `ρ ∘ σ` has the value of the arena's goal under
  `ρ`.
* `arena_refuted`: so when the Lean checker refutes the proof's goal, no state
  makes the verifier's goal true.
-/

namespace Vbcf.Proof

variable {State : Type}
open Bcf
set_option autoImplicit false

/-! ## Evaluation of the arena -/

theorem arenaEvalF_stable (w : Nat → Nat) (ρ : Assign) (q : Nat) :
    ∀ f f', q < f → q < f' → arenaEvalF w ρ f q = arenaEvalF w ρ f' q := by
  induction q using Nat.strongRecOn with
  | ind q ih =>
    intro f f' hf hf'
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    obtain ⟨g', rfl⟩ : ∃ g', f' = g' + 1 := ⟨f' - 1, by omega⟩
    simp only [arenaEvalF]
    cases arenaNode w q with
    | none => rfl
    | some n =>
      simp only
      congr 1
      apply List.map_congr_left
      intro a _
      split
      · exact ih a (by assumption) g g' (by omega) (by omega)
      · rfl

theorem arenaEval_unfold (w : Nat → Nat) (ρ : Assign) (q : Nat) :
    arenaEval w ρ q =
      match arenaNode w q with
      | none => .bad
      | some n => n.op.eval ρ (n.args.toList.map (fun a => if a < q then arenaEval w ρ a else .bad)) := by
  unfold arenaEval
  conv => lhs; rw [arenaEvalF]
  cases arenaNode w q with
  | none => rfl
  | some n =>
    simp only
    congr 1
    apply List.map_congr_left
    intro a _
    split
    · exact arenaEvalF_stable w ρ a _ _ (by assumption) (by omega)
    · rfl

/-! ## A match evaluates alike -/

/-- A non-variable operator does not read the state. -/
theorem Op.eval_nonvar {op : Op} (h : isVarOp op = false) (ρ ρ' : Assign) :
    op.eval ρ = op.eval ρ' := by
  cases op <;> simp_all [isVarOp, Op.eval]

/-- The state of the pool's variables: `σ` renames a pool variable to an arena
position, whose value `ρ` gives. -/
def renameSt (ρ : Assign) (σ : Nat → Option Nat) : Assign := fun d => ρ ((σ d).getD 0)

theorem arena_eval_of_match {pool : Pool} {w : Nat → Nat} {μ σ : Nat → Option Nat}
    (hwf : WF pool) (hM : ∀ q i, μ q = some i → GLocal pool w μ σ q i) (ρ : Assign) :
    ∀ q i, μ q = some i → eval pool (renameSt ρ σ) i = arenaEval w ρ q := by
  intro q
  induction q using Nat.strongRecOn with
  | ind q ih =>
    intro i hμ
    obtain ⟨n, hn, hcase⟩ := hM q i hμ
    rw [eval_node hwf _ hn, arenaEval_unfold]
    rcases hcase with ⟨wd, d, hop, hargs, ha, hσ⟩ | ⟨d, hop, hargs, ha, hσ⟩ |
      ⟨hnv, an, ha, hop, hsz, hk⟩
    · rw [ha, hop, hargs]
      simp only [Op.eval, List.map_nil, bvVarEval, renameSt, hσ, Option.getD_some]
    · rw [ha, hop, hargs]
      simp only [Op.eval, List.map_nil, renameSt, hσ, Option.getD_some]
    · rw [ha]
      simp only
      rw [hop, Op.eval_nonvar hnv (renameSt ρ σ) ρ]
      congr 1
      apply List.ext_getElem
      · simp [hsz]
      · intro k h1 h2
        simp only [List.length_map, Array.length_toList] at h1 h2
        have hk' := hk k h1
        simp only [List.getElem_map, Array.getElem_toList]
        have e : an.args[k] = an.args[k]! := by
          rw [getElem!_pos an.args k (by omega)]
        rw [e]; simp only [hk'.1, ↓reduceIte]
        exact ih _ hk'.1 _ hk'.2

/-- **A match evaluates alike**: under `GoalOK`, the arena's goal in state `ρ`
has the value of the pool's goal in the renamed state. -/
theorem arena_eval_of_goalOK {pool : Pool} {w : Nat → Nat} {g goal : Nat} (hwf : WF pool)
    (h : GoalOK pool w g goal) : ∃ σ : Nat → Option Nat,
      ∀ ρ, eval pool (renameSt ρ σ) g = arenaEval w ρ goal := by
  obtain ⟨μ, σ, hg, hM⟩ := h
  exact ⟨σ, fun ρ => arena_eval_of_match hwf hM ρ goal g hg⟩

/-! ## The verifier's goal is refuted -/

/-- If the Lean checker accepts the proof loaded as `st2` (the bridge, with
the scanned goal `g`) and the C matched `g` with the arena's goal, then no
state makes the arena's goal true. -/
theorem arena_refuted {ws : Array (BitVec 32)} {st0 st1 st2 : St} {tt ff : Nat}
    {pm : Nat → Option Nat} {steps : List Step} {gpos D g : Nat} {P : RawProof}
    {remap : Array Nat} {graw : Nat} {w : Nat → Nat} {goal : Nat}
    (htt : pushNode initSt ⟨.boolVal true, #[]⟩ = some (st0, tt))
    (hff : pushNode st0 ⟨.boolVal false, #[]⟩ = some (st1, ff))
    (hb : LoadBridge ws st1 st2 pm steps gpos D P remap) (hgoal : pm gpos = some g)
    (hcheck : checkBcf P = some graw) (hok : GoalOK st2.pool w g goal) :
    ∀ ρ, ¬ arenaHolds w ρ goal := by
  intro ρ hρ
  -- the raw goal is the one the checker reports, and canonicalises to `g`
  have hidx : idxOf (wordFn ws) D gpos = some graw := by
    have hc := check_of_bridge rwTable htt hff hb
    unfold checkBcf at hcheck
    rw [hcheck, hgoal] at hc
    simp only at hc
    split at hc
    · simp at hc
    · split at hc
      · split at hc
        · exact hc.symm
        · simp at hc
      · simp at hc
  have hei := hb.ei gpos
  rw [hgoal, Bcf.exprIdx, hb.posmap, hidx] at hei
  simp only [Option.bind_some] at hei
  have hgr : remap[graw]? = some g := hei
  -- invariants of the loaded pool
  have hok0 : TysOK initSt.pool initSt.tys := ⟨rfl, by intro i n hn; simp [initSt] at hn⟩
  have hok1 := pushNode_tysOK hff (pushNode_tysOK htt hok0)
  obtain ⟨hcinv, hok2⟩ := canonicalize_inv hok1 hb.canon
  have hj : graw < P.pool.size := by
    rcases Nat.lt_or_ge graw P.pool.size with h' | h'
    · exact h'
    · have := hcinv.1
      rw [Array.getElem?_eq_none (by omega)] at hgr
      exact absurd hgr (by simp)
  obtain ⟨σ, hσ⟩ := arena_eval_of_goalOK hok2.wf hok
  have h2 : holds st2.pool (renameSt ρ σ) g := by
    unfold holds; rw [hσ ρ]; exact hρ
  have hraw := (holds_of_canon hcinv hok2 (renameSt ρ σ) hj hgr).mpr h2
  exact checkBcf_sound P hcheck _ hraw

end Vbcf.Proof
