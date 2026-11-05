import EmbC.Kernel
import Vbcf.Prog
import Bcf.Final

/-!
# Vbcf proofs: a one-pass loader over words (definitions)

`Bcf.decode` + `Bcf.canonicalize` + `Bcf.positionMap` load a proof in several
passes over a `ByteArray`.  The C checker (`ck_load`, `ck_scan`) does it in one
pass over an array of 32-bit words.  This file defines the one-pass loader on
the Lean side, as plain structural recursions over a word function
`w : Nat → Nat` (`w i` is word `i` of the proof):

* `posOfW w d` — the position of the `d`-th expression (walking headers);
* `loadNode` / `loadExprs` — the expression loop of `ck_load`;
* `scanSteps` — the loop of `ck_scan`.

`LoadSpec.lean` proves that when these succeed, the real Lean functions
succeed with the corresponding results.
-/

namespace Vbcf.Proof

variable {State : Type}
open Bcf
set_option autoImplicit false

/-! ## Words to bytes -/

/-- The little-endian byte image of an array of 32-bit words. -/
def wordsToBytes (ws : Array (BitVec 32)) : ByteArray :=
  ⟨Array.ofFn (n := 4 * ws.size) fun j =>
    UInt8.ofNat (ws[j.val / 4]!.toNat / 2 ^ (8 * (j.val % 4)))⟩

/-- Word `i` of the proof, as a natural number (0 beyond the end). -/
def wordFn (ws : Array (BitVec 32)) (i : Nat) : Nat := ws[i]!.toNat

/-! ## Header fields -/

/-- `code` field of an expression header: `hdr & 0xff`. -/
def hdrCode (h : Nat) : Nat := h % 256
/-- `vlen` field of an expression header: `(hdr >> 8) & 0xff`. -/
def hdrVlen (h : Nat) : Nat := h / 256 % 256
/-- `params` field of an expression header: `hdr >> 16`. -/
def hdrParams (h : Nat) : Nat := h / 65536

/-! ## Positions -/

/-- The position (word offset within the expression section, which starts at
word 3) of the `d`-th expression: start at 0 and skip `1 + vlen` words per
expression.  Defined for every `d`, whatever the input. -/
def posOfW (w : Nat → Nat) : Nat → Nat
  | 0 => 0
  | d + 1 => posOfW w d + 1 + hdrVlen (w (3 + posOfW w d))

/-- The `j < n` with `posOfW w j = a`, if any: the dense index of the
expression at position `a` among the first `n` expressions. -/
def idxOf (w : Nat → Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | n + 1, a => if posOfW w n = a then some n else idxOf w n a

/-- The position map determined by the canonical ids `remap` of the first
`remap.size` expressions: position ↦ canonical id. -/
def pmOf (w : Nat → Nat) (remap : Array Nat) (a : Nat) : Option Nat :=
  (idxOf w remap.size a).bind (fun j => remap[j]?)

/-- Record `p ↦ r` in a position map. -/
def pmSet (pm : Nat → Option Nat) (p r : Nat) : Nat → Option Nat :=
  fun q => if q = p then some r else pm q

/-! ## The expression loader -/

/-- The `vlen` words after the header at position `p`. -/
def argWords (w : Nat → Nat) (p vlen : Nat) : List Nat :=
  (List.range vlen).map (fun k => w (4 + p + k))

/-- The canonical node for the expression at position `p`, which is the
`d`-th expression; `pm` maps the positions of earlier expressions to their
canonical ids. -/
def loadNode (w : Nat → Nat) (p d : Nat) (pm : Nat → Option Nat) : Option Node :=
  if hdrCode (w (3 + p)) = 0x18 ∨ hdrCode (w (3 + p)) = 0x19 then
    if hdrVlen (w (3 + p)) = 0 then
      decodeNode d (hdrCode (w (3 + p))) 0 (hdrParams (w (3 + p))) #[]
    else none
  else if hdrCode (w (3 + p)) = 0x08 then
    decodeNode d (hdrCode (w (3 + p))) (hdrVlen (w (3 + p))) (hdrParams (w (3 + p)))
      (argWords w p (hdrVlen (w (3 + p)))).toArray
  else
    match decodeNode d (hdrCode (w (3 + p))) (hdrVlen (w (3 + p))) (hdrParams (w (3 + p)))
        (argWords w p (hdrVlen (w (3 + p)))).toArray with
    | none => none
    | some n =>
      match mapOpt (fun a => if a < p then pm a else none) (argWords w p (hdrVlen (w (3 + p)))) with
      | none => none
      | some args => some ⟨n.op, args.toArray⟩

/-- The loop of `ck_load`: from position `p` (the `d`-th expression) with
state `st` and position map `pm`, load expressions up to position `ne`. -/
def loadExprs (w : Nat → Nat) (ne : Nat) :
    Nat → Nat → Nat → St → (Nat → Option Nat) → Option (St × (Nat → Option Nat))
  | 0, p, _, st, pm => if p = ne then some (st, pm) else none
  | fuel + 1, p, d, st, pm =>
    if p < ne then
      if p + 1 + hdrVlen (w (3 + p)) ≤ ne then
        match loadNode w p d pm with
        | none => none
        | some n =>
          match pushNode st n with
          | none => none
          | some (st', r) =>
            loadExprs w ne fuel (p + 1 + hdrVlen (w (3 + p))) (d + 1) st' (pmSet pm p r)
      else none
    else if p = ne then some (st, pm) else none

/-! ## The step scanner -/

/-- Rule code of a step header: `hdr & 0xffff`. -/
def stepRule (h : Nat) : Nat := h % 65536
/-- Premise count of a step header: `(hdr >> 16) & 0xff`. -/
def stepPc (h : Nat) : Nat := h / 65536 % 256
/-- Parameter count of a step header: `hdr >> 24`. -/
def stepAc (h : Nat) : Nat := h / 16777216

/-- The step whose header is at word `q`. -/
def stepAt (w : Nat → Nat) (q : Nat) : Step :=
  ⟨Rule.ofCode (stepRule (w q)),
   ((List.range (stepPc (w q))).map (fun k => w (q + 1 + k))).toArray,
   ((List.range (stepAc (w q))).map (fun k => w (q + 1 + stepPc (w q) + k))).toArray⟩

/-- The loop of `ck_scan` over the step section (`ns` words starting at word
`base`), from offset `p` with the C's accumulators: the number of ASSUME steps
seen, whether one of them did not have exactly one parameter, and the
parameter of the last good one.  Returns the steps from `p` on and the goal
position. -/
def scanSteps (w : Nat → Nat) (base ns : Nat) :
    Nat → Nat → Nat → Bool → Nat → Option (List Step × Nat)
  | 0, p, nassume, bad, gpos =>
    if p = ns then (if nassume = 1 ∧ bad = false then some ([], gpos) else none) else none
  | fuel + 1, p, nassume, bad, gpos =>
    if p < ns then
      if p + 1 + stepPc (w (base + p)) + stepAc (w (base + p)) ≤ ns then
        match scanSteps w base ns fuel (p + 1 + stepPc (w (base + p)) + stepAc (w (base + p)))
            (if stepRule (w (base + p)) = 1 then nassume + 1 else nassume)
            (if stepRule (w (base + p)) = 1 ∧ stepAc (w (base + p)) ≠ 1 then true else bad)
            (if stepRule (w (base + p)) = 1 ∧ stepAc (w (base + p)) = 1
              then w (base + p + 1 + stepPc (w (base + p))) else gpos) with
        | none => none
        | some (rest, g) => some (stepAt w (base + p) :: rest, g)
      else none
    else if p = ns then (if nassume = 1 ∧ bad = false then some ([], gpos) else none) else none

end Vbcf.Proof
