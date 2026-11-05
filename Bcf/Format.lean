import Bcf.Syntax
import Std.Data.HashMap

/-!
# Decoder for the BCF binary proof format

Untrusted front end: turns the bytes of a `.bcf` file into a raw pool
and steps, exactly following `struct bcf_proof_header`, `struct
bcf_expr` and `struct bcf_proof_step` from `uapi/linux/bcf.h`.  Every
`params` constraint that `type_check_*` enforces on reserved bits is
enforced here, so a proof the kernel rejects for a malformed encoding
is rejected here too.
-/

namespace Bcf

inductive Rule where
  -- core
  | assume | evaluate | distinctValues | aciNorm | absorb | rewrite | refl | symm | trans | cong
  | trueIntro | trueElim | falseIntro | falseElim
  -- boolean
  | resolution | factoring | reordering | split | eqResolve | modusPonens | notNotElim | contra
  | andElim | andIntro | notOrElim | impliesElim | notImpliesElim | equivElim | notEquivElim
  | xorElim | notXorElim | iteElim | notIteElim | notAnd
  | cnfAndPos | cnfAndNeg | cnfOrPos | cnfOrNeg | cnfImpliesPos | cnfImpliesNeg
  | cnfEquivPos | cnfEquivNeg | cnfXorPos | cnfXorNeg | cnfItePos | cnfIteNeg | iteEq
  -- bit-vector
  | bitblast | polyNorm | polyNormEq
  | unknown (code : Nat)
  deriving DecidableEq, Repr, Inhabited

def Rule.ofCode (code : Nat) : Rule :=
  let cls := code &&& 0xe000
  let idx := code &&& 0x1fff
  let core := [Rule.assume, .evaluate, .distinctValues, .aciNorm, .absorb, .rewrite, .refl, .symm,
    .trans, .cong, .trueIntro, .trueElim, .falseIntro, .falseElim]
  let bool := [Rule.resolution, .factoring, .reordering, .split, .eqResolve, .modusPonens,
    .notNotElim, .contra, .andElim, .andIntro, .notOrElim, .impliesElim, .notImpliesElim,
    .equivElim, .notEquivElim, .xorElim, .notXorElim, .iteElim, .notIteElim, .notAnd,
    .cnfAndPos, .cnfAndNeg, .cnfOrPos, .cnfOrNeg, .cnfImpliesPos, .cnfImpliesNeg,
    .cnfEquivPos, .cnfEquivNeg, .cnfXorPos, .cnfXorNeg, .cnfItePos, .cnfIteNeg, .iteEq]
  let bv := [Rule.bitblast, .polyNorm, .polyNormEq]
  let tbl := if cls = 0 then core else if cls = 0x2000 then bool else if cls = 0x4000 then bv else []
  if idx = 0 then .unknown code else (tbl[idx - 1]?).getD (.unknown code)

structure Step where
  rule     : Rule
  premises : Array Nat
  params   : Array Nat
  deriving Repr, Inhabited

structure RawProof where
  pool  : Pool
  steps : Array Step
  deriving Repr, Inhabited

/-! ## Words -/

def u32At (b : ByteArray) (off : Nat) : Nat :=
  b[off]!.toNat ||| (b[off+1]!.toNat <<< 8) ||| (b[off+2]!.toNat <<< 16) ||| (b[off+3]!.toNat <<< 24)

/-! ## Expression nodes -/

/-- Decode one node header and its argument words.  `idx` is the node's
pool index, used as the identity of variables. -/
def decodeNode (idx : Nat) (code vlen params : Nat) (words : Array Nat) : Option Node := do
  let ty := code &&& 7
  let op := code &&& 0xf8
  let lo := params &&& 0xff
  let hi := (params >>> 8) &&& 0xff
  let ids : Array Nat := words
  if ty = 0 then
    -- bit-vector; `lo` is the width except for extract and from_bool
    match op with
    | 0x18 => guard (hi = 0); pure ⟨.bvVar lo idx, #[]⟩
    | 0x08 =>
      guard (hi = 0)
      guard (lo ≠ 0 ∧ vlen ≤ 2 ∧ vlen = (lo + 31) / 32)
      let v := if vlen = 2 then words[0]! ||| (words[1]! <<< 32) else words[0]!
      pure ⟨.bvVal lo v, #[]⟩
    | 0x28 => guard (hi = 0); pure ⟨.bvIte lo, ids⟩
    | 0x80 => guard (hi = 0); pure ⟨.bvNeg lo, ids⟩
    | 0x78 => guard (hi = 0); pure ⟨.bvNot lo, ids⟩
    | 0x38 => pure ⟨.bvExtract hi lo, ids⟩
    | 0x48 => pure ⟨.bvSignExtend lo hi, ids⟩
    | 0x58 => pure ⟨.bvZeroExtend lo hi, ids⟩
    | 0x68 => guard (hi = 0); pure ⟨.bvSize lo, ids⟩
    | 0xa8 => pure ⟨.bvRepeat lo hi, ids⟩
    | 0x10 => guard (hi = 0); pure ⟨.bvSub lo, ids⟩
    | 0x60 => guard (hi = 0); pure ⟨.bvShl lo, ids⟩
    | 0x70 => guard (hi = 0); pure ⟨.bvLshr lo, ids⟩
    | 0xc0 => guard (hi = 0); pure ⟨.bvAshr lo, ids⟩
    | 0x30 => guard (hi = 0); pure ⟨.bvUdiv lo, ids⟩
    | 0x90 => guard (hi = 0); pure ⟨.bvUrem lo, ids⟩
    | 0xb0 => guard (hi = 0); pure ⟨.bvSdiv lo, ids⟩
    | 0xd0 => guard (hi = 0); pure ⟨.bvSmod lo, ids⟩
    | 0x00 => guard (hi = 0); pure ⟨.bvAdd lo, ids⟩
    | 0x20 => guard (hi = 0); pure ⟨.bvMul lo, ids⟩
    | 0x40 => guard (hi = 0); pure ⟨.bvOr lo, ids⟩
    | 0x50 => guard (hi = 0); pure ⟨.bvAnd lo, ids⟩
    | 0xa0 => guard (hi = 0); pure ⟨.bvXor lo, ids⟩
    | 0x98 => guard (hi = 0); pure ⟨.bvConcat lo, ids⟩
    | 0x88 => guard (params = 0); pure ⟨.bvFromBool, ids⟩
    | _ => none
  else if ty = 1 then
    match op with
    | 0x08 => guard (params &&& 0xfffe = 0); pure ⟨.boolVal (params &&& 1 = 1), #[]⟩
    | 0x18 => guard (params = 0); pure ⟨.boolVar idx, #[]⟩
    | 0x80 => guard (params = 0); pure ⟨.boolNot, ids⟩
    | 0x48 => guard (hi = 0); pure ⟨.boolBitof lo, ids⟩
    | 0x10 => guard (params = 0); pure ⟨.eq, ids⟩
    | 0x50 => guard (params = 0); pure ⟨.distinct, ids⟩
    | 0x20 => guard (params = 0); pure ⟨.ugt, ids⟩
    | 0x30 => guard (params = 0); pure ⟨.uge, ids⟩
    | 0x60 => guard (params = 0); pure ⟨.sgt, ids⟩
    | 0x70 => guard (params = 0); pure ⟨.sge, ids⟩
    | 0xa0 => guard (params = 0); pure ⟨.ult, ids⟩
    | 0xb0 => guard (params = 0); pure ⟨.ule, ids⟩
    | 0xc0 => guard (params = 0); pure ⟨.slt, ids⟩
    | 0xd0 => guard (params = 0); pure ⟨.sle, ids⟩
    | 0x90 => guard (params = 0); pure ⟨.implies, ids⟩
    | 0x28 => guard (params = 0); pure ⟨.boolIte, ids⟩
    | 0x00 => guard (params = 0); pure ⟨.conj, ids⟩
    | 0x40 => guard (params = 0); pure ⟨.disj, ids⟩
    | 0x38 => guard (params = 0); pure ⟨.boolXor, ids⟩
    | _ => none
  else if ty = 2 then
    guard (op = 0x08 ∧ hi = 0)
    let elemBool ← if lo = 0 then some false else if lo = 1 then some true else none
    pure ⟨.listVal elemBool, ids⟩
  else none

/-- The argument words of the node whose header is at byte `p`. -/
def nodeWordsAt (b : ByteArray) (p vlen : Nat) : Array Nat :=
  ((List.range vlen).map (fun k => u32At b (p + 4 + 4 * k))).toArray

/-- Decode expression nodes from byte `p` up to byte `stop`.  `idx` is the
word position of the node at `p` within the section.  Every node takes at
least four bytes, so `fuel` only has to exceed the number of words left. -/
def decodeExprsGo (b : ByteArray) (stop : Nat) : Nat → Nat → Nat → Pool → Option Pool
  | 0, p, _, pool => if p = stop then some pool else none
  | fuel + 1, p, idx, pool =>
    if p < stop then
      let hdr := u32At b p
      let code := hdr &&& 0xff
      let vlen := (hdr >>> 8) &&& 0xff
      let params := (hdr >>> 16) &&& 0xffff
      if p + 4 + 4 * vlen ≤ stop then
        -- an argument may only name an *earlier* node index (a node header position)
        match decodeNode idx code vlen params (nodeWordsAt b p vlen) with
        | some n => decodeExprsGo b stop fuel (p + 4 + 4 * vlen) (idx + 1 + vlen) (pool.push n)
        | none => none
      else none
    else if p = stop then some pool else none

/-- Decode the expression section: `exprWords` u32 words starting at `off`. -/
def decodeExprs (b : ByteArray) (off exprWords : Nat) : Option Pool :=
  decodeExprsGo b (off + 4 * exprWords) (exprWords + 1) off 0 #[]

/-- The raw format indexes expressions by header position, not by node
number.  Renumber so that indices are dense node numbers. -/
def densify (pool : Pool) : Option Pool := do
  -- position -> dense index
  let mut posToIdx : Std.HashMap Nat Nat := {}
  let mut pos := 0
  let mut out : Pool := #[]
  for h : i in [0:pool.size] do
    let n := pool[i]
    posToIdx := posToIdx.insert pos i
    let vlen := match n.op with
      | .bvVal w _ => (w + 31) / 32
      | _ => n.args.size
    let mut args := #[]
    for a in n.args do
      match posToIdx[a]? with
      | some j => if j < i then args := args.push j else none
      | none => none
    -- variable identities: use the dense index
    let op := match n.op with
      | .bvVar w _ => Op.bvVar w i
      | .boolVar _ => Op.boolVar i
      | o => o
    out := out.push ⟨op, args⟩
    pos := pos + 1 + vlen
  pure out

/-- Decode proof steps from byte `p` up to byte `stop`. -/
def decodeStepsGo (b : ByteArray) (stop : Nat) : Nat → Nat → Array Step → Option (Array Step)
  | 0, p, steps => if p = stop then some steps else none
  | fuel + 1, p, steps =>
    if p < stop then
      let hdr := u32At b p
      let rule := hdr &&& 0xffff
      let pc := (hdr >>> 16) &&& 0xff
      let ac := (hdr >>> 24) &&& 0xff
      if p + 4 + 4 * (pc + ac) ≤ stop then
        let prems := ((List.range pc).map (fun k => u32At b (p + 4 + 4 * k))).toArray
        let params := ((List.range ac).map (fun k => u32At b (p + 4 + 4 * (pc + k)))).toArray
        decodeStepsGo b stop fuel (p + 4 + 4 * (pc + ac)) (steps.push ⟨Rule.ofCode rule, prems, params⟩)
      else none
    else if p = stop then some steps else none

def decodeSteps (b : ByteArray) (off stepWords : Nat) : Option (Array Step) :=
  decodeStepsGo b (off + 4 * stepWords) (stepWords + 1) off #[]

/-- Decode a whole proof file. -/
def decode (b : ByteArray) : Except String RawProof := do
  if b.size < 12 ∨ b.size % 4 ≠ 0 then throw "bad size"
  let magic := u32At b 0
  let exprWords := u32At b 4
  let stepWords := u32At b 8
  if magic ≠ 0x0BCF then throw "bad magic"
  if exprWords = 0 ∨ stepWords < 2 then throw "empty proof"
  if 12 + 4 * (exprWords + stepWords) ≠ b.size then throw "size mismatch"
  let some raw := decodeExprs b 12 exprWords | throw "malformed expressions"
  let some pool := densify raw | throw "bad expression reference"
  let some steps := decodeSteps b (12 + 4 * exprWords) stepWords | throw "malformed steps"
  pure { pool, steps }

/-- Step parameters and premises refer to expressions by *position*;
translate a position into a dense node index. -/
def positionMap (raw : Pool) : Std.HashMap Nat Nat := Id.run do
  let mut m : Std.HashMap Nat Nat := {}
  let mut pos := 0
  for h : i in [0:raw.size] do
    let n := raw[i]
    m := m.insert pos i
    let vlen := match n.op with
      | .bvVal w _ => (w + 31) / 32
      | _ => n.args.size
    pos := pos + 1 + vlen
  pure m

end Bcf
