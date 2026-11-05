import Bcf.Syntax

/-!
# Vbcf: how a Lean node is laid out in the C pool

`opCode` gives the wire-format `code` and `params` of an operator; it is the
inverse of `Bcf.decodeNode`.  This is specification-side Lean, shared by the
test tooling now and by the refinement proofs later.
-/

namespace Vbcf
open Bcf

/-- The `code` byte of an operator. -/
def opC : Op → Nat
  | .bvVar _ _ => 0x18
  | .bvVal _ _ => 0x08
  | .bvIte _ => 0x28
  | .bvNeg _ => 0x80
  | .bvNot _ => 0x78
  | .bvExtract _ _ => 0x38
  | .bvSignExtend _ _ => 0x48
  | .bvZeroExtend _ _ => 0x58
  | .bvSize _ => 0x68
  | .bvRepeat _ _ => 0xa8
  | .bvSub _ => 0x10
  | .bvShl _ => 0x60
  | .bvLshr _ => 0x70
  | .bvAshr _ => 0xc0
  | .bvUdiv _ => 0x30
  | .bvUrem _ => 0x90
  | .bvSdiv _ => 0xb0
  | .bvSmod _ => 0xd0
  | .bvAdd _ => 0x00
  | .bvMul _ => 0x20
  | .bvOr _ => 0x40
  | .bvAnd _ => 0x50
  | .bvXor _ => 0xa0
  | .bvConcat _ => 0x98
  | .bvFromBool => 0x88
  | .boolVal _ => 0x09
  | .boolVar _ => 0x19
  | .boolNot => 0x81
  | .boolBitof _ => 0x49
  | .eq => 0x11
  | .distinct => 0x51
  | .ugt => 0x21
  | .uge => 0x31
  | .sgt => 0x61
  | .sge => 0x71
  | .ult => 0xa1
  | .ule => 0xb1
  | .slt => 0xc1
  | .sle => 0xd1
  | .implies => 0x91
  | .boolIte => 0x29
  | .conj => 0x01
  | .disj => 0x41
  | .boolXor => 0x39
  | .listVal _ => 0x0a

/-- The low parameter byte. -/
def opLo : Op → Nat
  | .bvVar w _ => w
  | .bvVal w _ => w
  | .bvIte w => w
  | .bvNeg w => w
  | .bvNot w => w
  | .bvExtract _ lo => lo
  | .bvSignExtend w _ => w
  | .bvZeroExtend w _ => w
  | .bvSize w => w
  | .bvRepeat w _ => w
  | .bvSub w => w
  | .bvShl w => w
  | .bvLshr w => w
  | .bvAshr w => w
  | .bvUdiv w => w
  | .bvUrem w => w
  | .bvSdiv w => w
  | .bvSmod w => w
  | .bvAdd w => w
  | .bvMul w => w
  | .bvOr w => w
  | .bvAnd w => w
  | .bvXor w => w
  | .bvConcat w => w
  | .bvFromBool => 0
  | .boolVal b => (if b then 1 else 0)
  | .boolVar _ => 0
  | .boolNot => 0
  | .boolBitof i => i
  | .eq => 0
  | .distinct => 0
  | .ugt => 0
  | .uge => 0
  | .sgt => 0
  | .sge => 0
  | .ult => 0
  | .ule => 0
  | .slt => 0
  | .sle => 0
  | .implies => 0
  | .boolIte => 0
  | .conj => 0
  | .disj => 0
  | .boolXor => 0
  | .listVal e => (if e then 1 else 0)

/-- The high parameter byte. -/
def opHi : Op → Nat
  | .bvVar _ _ => 0
  | .bvVal _ _ => 0
  | .bvIte _ => 0
  | .bvNeg _ => 0
  | .bvNot _ => 0
  | .bvExtract hi _ => hi
  | .bvSignExtend _ e => e
  | .bvZeroExtend _ e => e
  | .bvSize _ => 0
  | .bvRepeat _ k => k
  | .bvSub _ => 0
  | .bvShl _ => 0
  | .bvLshr _ => 0
  | .bvAshr _ => 0
  | .bvUdiv _ => 0
  | .bvUrem _ => 0
  | .bvSdiv _ => 0
  | .bvSmod _ => 0
  | .bvAdd _ => 0
  | .bvMul _ => 0
  | .bvOr _ => 0
  | .bvAnd _ => 0
  | .bvXor _ => 0
  | .bvConcat _ => 0
  | .bvFromBool => 0
  | .boolVal _ => 0
  | .boolVar _ => 0
  | .boolNot => 0
  | .boolBitof _ => 0
  | .eq => 0
  | .distinct => 0
  | .ugt => 0
  | .uge => 0
  | .sgt => 0
  | .sge => 0
  | .ult => 0
  | .ule => 0
  | .slt => 0
  | .sle => 0
  | .implies => 0
  | .boolIte => 0
  | .conj => 0
  | .disj => 0
  | .boolXor => 0
  | .listVal _ => 0

/-- `(code, params)` of an operator. -/
def opCode (op : Op) : Nat × Nat := (opC op, opLo op + opHi op * 256)

/-- Number of words that follow a node's header in the C pool. -/
def tailLen (n : Node) : Nat :=
  match n.op with
  | .bvVar _ _ => 1
  | .boolVar _ => 1
  | .bvVal w _ => if w ≤ 32 then 1 else 2
  | .boolVal _ => 0
  | _ => n.args.size

/-- The header word. -/
def hdrW (n : Node) : Nat := opC n.op + tailLen n * 256 + (opLo n.op + opHi n.op * 256) * 65536

/-- The words after the header.  `posOf` maps a variable's identity (its
index in the raw input pool) to its position in the input; `off` maps a child
(a Lean pool index) to what the C pool stores for it. -/
def tailW (posOf off : Nat → Nat) (n : Node) : List Nat :=
  match n.op with
  | .bvVar _ id => [posOf id]
  | .boolVar id => [posOf id]
  | .bvVal w v => if w ≤ 32 then [v % 2 ^ 32] else [v % 2 ^ 32, v / 2 ^ 32]
  | .boolVal _ => []
  | _ => n.args.toList.map off

/-- Header and tail with children as Lean pool indices (used by the trace tool). -/
def nodeWords (posOf : Nat → Nat) (n : Node) : Nat × List Nat :=
  (hdrW n, tailW posOf id n)

end Vbcf
