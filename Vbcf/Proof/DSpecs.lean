import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.ReplaySpecs
import Vbcf.Proof.Interned

/-!
# Vbcf proofs: structural contracts of the loading phase

The contracts of `ck_init`, `ck_load` and `ck_scan` used by the direct soundness
proof. They describe the built-in nodes with `Interned`, the range of the
loader's position map, and the scanner's step layout with `StepsAt`. The
last-reference array and fixed loaded prefix support replay compaction.
-/

namespace Vbcf.Proof

variable {State : Type}
open Bcf

/-! ### The structural contract of `ck_init` -/

/-- The two built-in nodes, described structurally: `true` interned into the empty
pool at index `tt`, then `false` at index `ff`. -/
def DBuiltin2 (st1 : St) (tt ff : Nat) : Prop :=
  ∃ st0, Interned initSt ⟨.boolVal true, #[]⟩ st0 tt ∧ Interned st0 ⟨.boolVal false, #[]⟩ st1 ff

/-- After `ck_init` succeeds (structural form of `InitDone`). -/
structure DInitDone (c : CMem) (st1 : St) (tt ff : Nat) : Prop where
  b2 : DBuiltin2 st1 tt ff
  core : ∀ posOf : Nat → Nat, (∀ a b, posOf a = posOf b → a = b) → CoreInv posOf c st1
  tt : c.k.tt.toNat = offs st1.pool tt
  ff : c.k.ff.toNat = offs st1.pool ff
  prem : PremOK c
  factsNull : c.k.facts = none
  flen : c.k.flen = 0#32
  proofNull : c.k.proof = none
  parNull : c.k.par = none
  lrNull : c.k.lr = none

/-- The structural specification of `ck_init`. -/
def DInitSpec : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem) (nw g : BitVec 32),
    EmbC.FnSpec (State := State) Vbcf.prog "ck_init"
      (fun vs s => vs = [.ptr sb 0, .u32 nw, .u32 g] ∧ Holds W s.mem sb c ∧ c.k = zeroCK)
      (fun _ _ rv s' => ∃ c', Holds W s'.mem sb c' ∧ c'.proof = c.proof ∧
        (rv = some (.u32 0#32) ∨
         (rv = some (.u32 1#32) ∧ ∃ st1 tt ff, DInitDone c' st1 tt ff)))

/-- The built-in nodes are in the pool, and there are no facts yet. -/
theorem DBuiltin2.nodes {st1 : St} {tt ff : Nat} (hb : DBuiltin2 st1 tt ff) :
    st1.pool[tt]? = some ⟨.boolVal true, #[]⟩ ∧ st1.pool[ff]? = some ⟨.boolVal false, #[]⟩ ∧
    st1.facts = #[] := by
  obtain ⟨st0, h0, h1⟩ := hb
  refine ⟨?_, h1.get, ?_⟩
  · rw [h1.prefix tt h0.lt]; exact h0.get
  · rw [h1.facts, h0.facts]; rfl


/-! ### The structural contract of `ck_load` -/

/-- After `ck_load` succeeds (structural form of `LoadDone`): the header is valid,
the checker state represents a ghost pool `st2` (extending nothing in particular:
it is described by `CoreInv`), the proof block holds the position map `pm` where
the expressions were and the original words elsewhere, every mapped position
names a node of `st2`, and no position at or beyond the end of the expression
section is mapped. -/
structure DLoadDone (W : World) (ws : Array (BitVec 32)) (c : CMem) (tt ff : Nat) (st2 : St)
    (pm : Nat → Option Nat) : Prop where
  hsz : 3 ≤ ws.size
  hmagic : wordFn ws 0 = 0x0BCF
  hne : wordFn ws 1 ≠ 0
  hns : 2 ≤ wordFn ws 2
  hlen : 3 + wordFn ws 1 + wordFn ws 2 = ws.size
  pmLt : ∀ {a i : Nat}, pm a = some i → i < st2.pool.size
  pmNone : ∀ {a : Nat}, wordFn ws 1 ≤ a → pm a = none
  core : CoreInv (posOfW (wordFn ws)) c st2
  proofPtr : c.k.proof = some (W.pb, 0)
  psize : c.proof.size ≤ 2 ^ 32
  nexpr : c.k.nexpr.toNat = wordFn ws 1
  proofSize : c.proof.size = ws.size
  map : ∀ p, p < wordFn ws 1 →
    U c.proof (3 + p) (match pm p with | none => 0 | some i => offs st2.pool i + 1)
  rest : ∀ q, (q < 3 ∨ 3 + wordFn ws 1 ≤ q) → q < ws.size → U c.proof q (wordFn ws q)
  ttNode : st2.pool[tt]? = some ⟨.boolVal true, #[]⟩
  ffNode : st2.pool[ff]? = some ⟨.boolVal false, #[]⟩
  tt : c.k.tt.toNat = offs st2.pool tt
  ff : c.k.ff.toNat = offs st2.pool ff
  prem : PremOK c
  factsNull : c.k.facts = none
  flen : c.k.flen = 0#32
  noFacts : st2.facts = #[]
  lrNull : c.k.lr = none
  lo : c.k.lo = c.k.plen

/-- The structural loading specification for the direct proof. -/
def DLoadSpec : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem) (ws : Array (BitVec 32)) (n : BitVec 32) (st1 : St)
    (tt ff : Nat),
    EmbC.FnSpec (State := State) Vbcf.prog "ck_load"
      (fun vs s => vs = [.ptr sb 0, .ptr W.pb 0, .u32 n] ∧ Holds W s.mem sb c ∧
        DInitDone c st1 tt ff ∧ c.proof = ws.map EmbC.Val.u32 ∧ n.toNat = ws.size)
      (fun _ _ rv s' => ∃ c', Holds W s'.mem sb c' ∧
        (rv = some (.u32 0#32) ∨
         (rv = some (.u32 1#32) ∧ ∃ st2 pm, DLoadDone W ws c' tt ff st2 pm)))

/-- `DLoadDone` without `factsNull`: what survives `ck_scan`'s allocation of the
fact array. -/
structure DLoadDone' (W : World) (ws : Array (BitVec 32)) (c : CMem) (tt ff : Nat) (st2 : St)
    (pm : Nat → Option Nat) : Prop where
  hsz : 3 ≤ ws.size
  hmagic : wordFn ws 0 = 0x0BCF
  hne : wordFn ws 1 ≠ 0
  hns : 2 ≤ wordFn ws 2
  hlen : 3 + wordFn ws 1 + wordFn ws 2 = ws.size
  pmLt : ∀ {a i : Nat}, pm a = some i → i < st2.pool.size
  pmNone : ∀ {a : Nat}, wordFn ws 1 ≤ a → pm a = none
  core : CoreInv (posOfW (wordFn ws)) c st2
  proofPtr : c.k.proof = some (W.pb, 0)
  psize : c.proof.size ≤ 2 ^ 32
  nexpr : c.k.nexpr.toNat = wordFn ws 1
  proofSize : c.proof.size = ws.size
  map : ∀ p, p < wordFn ws 1 →
    U c.proof (3 + p) (match pm p with | none => 0 | some i => offs st2.pool i + 1)
  rest : ∀ q, (q < 3 ∨ 3 + wordFn ws 1 ≤ q) → q < ws.size → U c.proof q (wordFn ws q)
  ttNode : st2.pool[tt]? = some ⟨.boolVal true, #[]⟩
  ffNode : st2.pool[ff]? = some ⟨.boolVal false, #[]⟩
  tt : c.k.tt.toNat = offs st2.pool tt
  ff : c.k.ff.toNat = offs st2.pool ff
  prem : PremOK c
  flen : c.k.flen = 0#32
  noFacts : st2.facts = #[]
  lo : c.k.lo = c.k.plen

/-! ### The structural contract of `ck_scan` -/

/-- After `ck_scan` succeeds (structural form of `ScanDone`): the step section is
laid out as the steps `steps` (`StepsAt`, from offset 0 to its end), the goal
position `gpos` is mapped to the node `g`, whose id is in the `goal` field, and
the fact array is allocated with one cell per step. -/
structure DScanDone (W : World) (ws : Array (BitVec 32)) (c : CMem) (tt ff : Nat) (st2 : St)
    (pm : Nat → Option Nat) (steps : List Step) (gpos g : Nat) : Prop where
  ld : DLoadDone' W ws c tt ff st2 pm
  layout : StepsAt (wordFn ws) (3 + wordFn ws 1) (wordFn ws 2) 0 steps
  goal : pm gpos = some g
  goalFld : c.k.goal.toNat = offs st2.pool g
  factsPtr : ∃ b, c.k.facts = some (b, 0)
  factsSize : c.facts.size = steps.length
  fcap : c.k.fcap.toNat = steps.length
  factsCells : ∀ j, j < steps.length → ∃ w, w < 2 ^ 32 ∧ U c.facts j w
  lrPtr : ∃ b, c.k.lr = some (b, 0)
  lrSize : c.lr.size = steps.length
  lrCells : ∀ j, j < steps.length → ∃ w, w < 2 ^ 32 ∧ U c.lr j w

/-- The structural scanner specification for the direct proof. -/
def DScanSpec : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem) (ws : Array (BitVec 32)) (st2 : St) (tt ff : Nat)
    (pm : Nat → Option Nat),
    EmbC.FnSpec (State := State) Vbcf.prog "ck_scan"
      (fun vs s => vs = [.ptr sb 0] ∧ Holds W s.mem sb c ∧ DLoadDone W ws c tt ff st2 pm)
      (fun _ _ rv s' => ∃ c', Holds W s'.mem sb c' ∧
        (rv = some (.u32 0#32) ∨
         (rv = some (.u32 1#32) ∧ ∃ steps gpos g, DScanDone W ws c' tt ff st2 pm steps gpos g)))

end Vbcf.Proof
