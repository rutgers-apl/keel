import Vbcf.Rules.Rewrite
open Bcf

def allOps : List RwOp := [.not, .eq, .neq, .implies, .conj, .disj, .xor, .ult, .ule, .ugt, .uge, .slt, .sle, .sgt, .sge,
  .bvadd, .bvsub, .bvmul, .bvneg, .bvnot, .bvshl, .bvlshr, .bvashr, .bvor, .bvand, .bvxor, .bvudiv, .bvurem, .concat, .bvsize]

def opOfCode (c : Nat) : Option RwOp := allOps.find? (fun op => (Vbcf.opCode (op.node 0)).1 == c)

mutual
partial def decE (w : Array Nat) (pos : Nat) : Option RwExpr := do
  let h ← w[pos]?
  let tag := h % 256
  let aux := (h / 256) % 256
  let len := h / 65536
  let nxt (p : Nat) : Option Nat := do let x ← w[p]?; pure (p + x / 65536)
  if tag = 0 then (if len = 1 then some (.var aux) else none)
  else if tag = 1 then some .tt
  else if tag = 2 then some .ff
  else if tag = 3 then do let v ← w[pos+1]?; if len = 2 then pure (.lit v) else none
  else if tag = 4 then do
    let a ← decE w (pos+1); let p2 ← nxt (pos+1); let b ← decE w p2
    if (← nxt p2) = pos + len then pure (.symVal a b) else none
  else if tag = 5 then do
    let a ← decE w (pos+1)
    if (← nxt (pos+1)) = pos + len then pure (.bvmax a) else none
  else if tag = 6 then do
    let op ← opOfCode aux
    let as ← decA w (pos+1) (pos+len)
    pure (.app op as)
  else if tag = 7 ∨ tag = 8 then do
    let a ← decE w (pos+1); let p2 ← nxt (pos+1); let b ← decE w p2; let p3 ← nxt p2; let c ← decE w p3
    if (← nxt p3) ≠ pos + len then none
    else if tag = 7 then pure (.ite a b c) else pure (.extract a b c)
  else if tag = 9 ∨ tag = 10 ∨ tag = 11 then do
    let a ← decE w (pos+1); let p2 ← nxt (pos+1); let b ← decE w p2
    if (← nxt p2) ≠ pos + len then none
    else if tag = 9 then pure (.zext a b) else if tag = 10 then pure (.sext a b) else pure (.repeat a b)
  else none
partial def decA (w : Array Nat) (pos stop : Nat) : Option RwArgs := do
  if pos = stop then pure .nil
  else if pos > stop then none
  else
    let a ← decE w pos
    let h ← w[pos]?
    let rest ← decA w (pos + h / 65536) stop
    pure (.cons a rest)
end

mutual
partial def beqE : RwExpr → RwExpr → Bool
  | .var i, .var j => i == j
  | .tt, .tt => true
  | .ff, .ff => true
  | .lit a, .lit b => a == b
  | .symVal a b, .symVal c d => beqE a c && beqE b d
  | .bvmax a, .bvmax b => beqE a b
  | .app o as, .app p bs => o == p && beqA as bs
  | .ite a b c, .ite d e f => beqE a d && beqE b e && beqE c f
  | .extract a b c, .extract d e f => beqE a d && beqE b e && beqE c f
  | .zext a b, .zext c d => beqE a c && beqE b d
  | .sext a b, .sext c d => beqE a c && beqE b d
  | .repeat a b, .repeat c d => beqE a c && beqE b d
  | _, _ => false
partial def beqA : RwArgs → RwArgs → Bool
  | .nil, .nil => true
  | .cons a r, .cons b s => beqE a b && beqA r s
  | _, _ => false
end

mutual
partial def depthE : RwExpr → Nat
  | .symVal a b => 1 + max (depthE a) (depthE b)
  | .bvmax a => 1 + depthE a
  | .app _ as => 1 + depthA as
  | .ite a b c => 1 + max (depthE a) (max (depthE b) (depthE c))
  | .extract a b c => 1 + max (depthE a) (max (depthE b) (depthE c))
  | .zext a b => 1 + max (depthE a) (depthE b)
  | .sext a b => 1 + max (depthE a) (depthE b)
  | .repeat a b => 1 + max (depthE a) (depthE b)
  | _ => 1
partial def depthA : RwArgs → Nat
  | .nil => 0
  | .cons a r => max (depthE a) (depthA r)
end

def decTy (t : Nat) : Option RwTy :=
  let k := t % 256
  if k = 0 then some .any else if k = 1 then some .bool else if k = 2 then some (.bv (t / 256))
  else if k = 3 then some .bvq else if k = 4 then some .bools else if k = 5 then some .bvqs else none

def optEq : Option RwExpr → Option RwExpr → Bool
  | none, none => true
  | some a, some b => beqE a b
  | _, _ => false

def main : IO Unit := do
  let w := Vbcf.RwEnc.words.toArray
  IO.println s!"words={w.size} max={w.foldl max 0} lt32={w.all (· < 2^32)}"
  IO.println s!"constdef size={Vbcf.rwTblDef.words.size} faithful={(Vbcf.rwTblDef.words.toList.map (·.toNat)) == Vbcf.RwEnc.words}"
  let mut ok := 0
  let mut bad := 0
  let mut none_ := 0
  let mut maxDepth := 0
  let mut maxLen := 0
  for i in [0:Vbcf.RwEnc.bound] do
    let off := w[i]!
    match rwTable i with
    | none =>
      if off = 0 then none_ := none_ + 1
      else
        bad := bad + 1
        IO.println s!"{i}: index nonzero for undefined rule"
    | some r =>
      if off = 0 then
        bad := bad + 1
        IO.println s!"{i}: missing"
      else
        let np := w[off]!
        let ps := (List.range np).map (fun k => decTy w[off + 4 + k]!)
        let c := if w[off+1]! = 0 then none else decE w w[off+1]!
        let l := decE w w[off+2]!
        let rr := decE w w[off+3]!
        let good := ps == r.params.map some && optEq c r.cond && optEq l (some r.lhs) && optEq rr (some r.rhs)
          && (w[off+1]! = 0) == r.cond.isNone
        for e in [r.cond, some r.lhs, some r.rhs] do
          match e with
          | some e => maxDepth := max maxDepth (depthE e); maxLen := max maxLen (Vbcf.RwEnc.encE e).length
          | none => pure ()
        if good then ok := ok + 1
        else
          bad := bad + 1
          IO.println s!"{i}: MISMATCH"
  IO.println s!"rules ok={ok} bad={bad} undefined={none_} maxDepth={maxDepth} maxPatternLen={maxLen}"
  -- no rule beyond the bound (spot check)
  IO.println s!"beyond bound defined: {((List.range 5000).filter (fun i => i ≥ Vbcf.RwEnc.bound && (rwTable i).isSome)).length}"
  IO.println s!"opcodes distinct: {(allOps.map (fun op => (Vbcf.opCode (op.node 0)).1)).eraseDups.length} of {allOps.length}"
