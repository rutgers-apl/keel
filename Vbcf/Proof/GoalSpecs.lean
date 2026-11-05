import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Specs
import Vbcf.Proof.LoadSpec1
import Bcf.Goal

/-!
# Vbcf proofs: the verifier's goal (statements)

`ck_goal(st, gx, goal)` compares the proof's goal (the canonical pool node
`X.goal`) with node `goal` of the verifier's arena `gx` (`Bcf.arenaNode`).

* `ArenaOK W gb gws goal`: what the verifier must guarantee about its
  argument — block `gb` existed before the checker was entered, holds the
  words `gws`, and the goal node lies inside it.  Nothing else is assumed
  about the arena: every other read is guarded by the C.
* `GLocal`, `GoalOK`: what a successful comparison establishes, as a matching
  `μ` of arena positions to pool indices and a variable renaming `σ` (pool
  variable identity ↦ arena position), checked node by node.
* `GoalSpec`: the specification of `ck_goal`.

`GoalSem.lean` proves that `GoalOK` makes the two goals evaluate alike.
-/

namespace Vbcf.Proof

variable {State : Type}
open Bcf
set_option autoImplicit false

/-- Variable operators: their meaning depends on the state. -/
def isVarOp : Op → Bool
  | .bvVar _ _ => true
  | .boolVar _ => true
  | _ => false

/-- Arena node `q` matches pool node `i`, given the matching `μ` of its
arguments and the renaming `σ`: a variable matches a variable of the same
sort renamed to it by `σ`; any other node matches a node with the same
operator whose arguments are earlier arena nodes matched to its arguments. -/
def GLocal (pool : Pool) (w : Nat → Nat) (μ σ : Nat → Option Nat) (q i : Nat) : Prop :=
  ∃ n, pool[i]? = some n ∧
    ((∃ wd d, n.op = .bvVar wd d ∧ n.args = #[] ∧ arenaNode w q = some ⟨.bvVar wd q, #[]⟩ ∧
        σ d = some q) ∨
     (∃ d, n.op = .boolVar d ∧ n.args = #[] ∧ arenaNode w q = some ⟨.boolVar q, #[]⟩ ∧
        σ d = some q) ∨
     (isVarOp n.op = false ∧ ∃ an, arenaNode w q = some an ∧ an.op = n.op ∧
        an.args.size = n.args.size ∧
        ∀ k (hk : k < n.args.size), an.args[k]! < q ∧ μ an.args[k]! = some n.args[k]))

/-- The comparison succeeded: arena node `goal` is matched with pool node `g`,
and every matched pair is checked. -/
def GoalOK (pool : Pool) (w : Nat → Nat) (g goal : Nat) : Prop :=
  ∃ μ σ : Nat → Option Nat, μ goal = some g ∧ ∀ q i, μ q = some i → GLocal pool w μ σ q i

/-- The verifier's goal argument: block `gb` existed when the checker was
entered, is not the proof's block, holds the words `gws`, and the goal node
(its header and its `vlen` argument words) lies inside it. -/
structure ArenaOK (W : World) (gb : Nat) (gws : Array (BitVec 32)) (goal : Nat) : Prop where
  old : gb < W.base.blocks.size
  notProof : gb ≠ W.pb
  block : W.base.block? gb = some ⟨.u32, gws.map EmbC.Val.u32⟩
  inside : goal < gws.size
  fits : goal + 1 + hdrVlen (wordFn gws goal) ≤ gws.size

/-- `ck_goal(st, gx, goal)`, called between steps (in fact right after
`ck_scan`): never stuck; keeps the step invariant for the same Lean state and
changes nothing a step relies on (`StepFrame`); returns non-zero only if the
proof's goal matches arena node `goal`. -/
def GoalSpec : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem) (X : Ctx) (st : St) (gb : Nat) (gws : Array (BitVec 32))
    (goal : BitVec 32),
    EmbC.FnSpec (State := State) Vbcf.prog "ck_goal"
      (fun vs s => vs = [.ptr sb 0, .ptr gb 0, .u32 goal] ∧ Holds W s.mem sb c ∧ RInv0 W X c st ∧
        ArenaOK W gb gws goal.toNat)
      (fun _ _ rv s' => ∃ c' r, rv = some (.u32 r) ∧ Holds W s'.mem sb c' ∧ RInv0 W X c' st ∧
        StepFrame c c' ∧ (r ≠ 0#32 → GoalOK st.pool (wordFn gws) X.goal goal.toNat))

end Vbcf.Proof
