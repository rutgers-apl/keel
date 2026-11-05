import Bcf.Format
import Bcf.Semantics

/-!
# The verifier's goal

The verifier hands the checker its goal as an *expression arena*: an array of
`struct bcf_expr` (the same node encoding as a proof's expression section,
read here as 32-bit words `w`) and the word position `goal` of the goal node.
An argument of a node is the word position of another node; a variable is
identified by its position.  This file gives that encoding its meaning, by
the same `decodeNode` and `Op.eval` as proofs: `arenaHolds w ρ goal` is "the
verifier's goal is true in state `ρ`".  Like the rest of the semantics, it is
part of the trusted base.

Only nodes reachable from `goal` through arguments that point to *earlier*
positions matter; an argument pointing elsewhere makes its node `bad`.
-/

namespace Bcf

/-- The node at word position `q` of the arena `w`: its header word, then
`vlen` argument words.  A variable's identity is `q`. -/
def arenaNode (w : Nat → Nat) (q : Nat) : Option Node :=
  let hdr := w q
  let vlen := (hdr >>> 8) &&& 0xff
  decodeNode q (hdr &&& 0xff) vlen ((hdr >>> 16) &&& 0xffff)
    ((List.range vlen).map (fun k => w (q + 1 + k))).toArray

/-- Evaluation of arena nodes, with fuel (as `evalF`). -/
def arenaEvalF (w : Nat → Nat) (ρ : Assign) : Nat → Nat → Val
  | 0, _ => .bad
  | fuel + 1, q =>
    match arenaNode w q with
    | none => .bad
    | some n =>
      n.op.eval ρ (n.args.toList.map (fun a => if a < q then arenaEvalF w ρ fuel a else .bad))

/-- The value of the arena node at position `q` in state `ρ`. -/
def arenaEval (w : Nat → Nat) (ρ : Assign) (q : Nat) : Val := arenaEvalF w ρ (q + 1) q

/-- "The arena node at position `q` is true in state `ρ`." -/
def arenaHolds (w : Nat → Nat) (ρ : Assign) (q : Nat) : Prop := arenaEval w ρ q = .bool true

end Bcf
