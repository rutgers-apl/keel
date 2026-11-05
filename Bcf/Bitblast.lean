import Bcf.Rw.Pattern

/-!
# BITBLAST: structural checks of bit-blasted circuits

BCF's BITBLAST step asserts `t = from_bool(b₀, …, bₙ₋₁)` for a bit-vector
term `t`, or `p = φ` for a comparison atom `p`, where the boolean circuit
must be exactly BCF's canonical circuit for the operator (`check_bb_term`,
`check_bb_atom` in `bcf_checker.c`).  The checks below mirror those
functions; `BitblastSound.lean` proves each accepted equation valid.
-/

namespace Bcf

/-- The bit nodes of a `from_bool` node, least significant first. -/
def bitsOf (st : St) (i : Nat) : Option (List Nat) :=
  match st.pool[i]? with
  | some ⟨.bvFromBool, args⟩ => some args.toList
  | _ => none

def isNode (st : St) (i : Nat) (n : Node) : Bool := st.pool[i]? == some n

def isNotOf (st : St) (i a : Nat) : Bool := isNode st i ⟨.boolNot, #[a]⟩
def isEqOf (st : St) (i a b : Nat) : Bool := isNode st i ⟨.eq, #[a, b]⟩
def isXorOf (st : St) (i a b : Nat) : Bool := isNode st i ⟨.boolXor, #[a, b]⟩
def isConjOf (st : St) (i a b : Nat) : Bool := isNode st i ⟨.conj, #[a, b]⟩

/-- `f i b` for every bit `b` at position `i`. -/
def allIdx (f : Nat → Nat → Bool) : Nat → List Nat → Bool
  | _, [] => true
  | i, b :: bs => f i b && allIdx f (i + 1) bs

/-- Pointwise check of two equally long lists. -/
def zipAll (f : Nat → Nat → Bool) : List Nat → List Nat → Bool
  | [], [] => true
  | x :: xs, y :: ys => f x y && zipAll f xs ys
  | _, _ => false

/-- `x = from_bool(bitof 0 x, …)`. -/
def bbVar (st : St) (a : Nat) (bs : List Nat) : Bool :=
  allIdx (fun i b => isNode st b ⟨.boolBitof i, #[a]⟩) 0 bs

/-- A literal: each bit is the builtin `true` or `false`. -/
def bbVal (bi : Builtins) (v : Nat) (bs : List Nat) : Bool :=
  allIdx (fun i b => if v.testBit i then b == bi.tt else b == bi.ff) 0 bs

/-- A left-nested chain `op(op(op(c₀, c₁), c₂), …)`, given the column
in reverse order. -/
def chainRev (st : St) (op : Op) : List Nat → Nat → Bool
  | [], _ => false
  | [x], b => b == x
  | x :: rest, b =>
    match st.pool[b]? with
    | some ⟨op', args⟩ =>
      match args.toList with
      | [l, r] => op' == op && r == x && chainRev st op rest l
      | _ => false
    | none => false

/-- Bitwise operator over several operands (`bb_bitwise_op`). -/
def bbBitwise (st : St) (op : Op) (xss : List (List Nat)) : Nat → List Nat → Bool
  | _, [] => true
  | i, b :: bs =>
    match mapOpt (fun xs => xs[i]?) xss with
    | some col => chainRev st op col.reverse b && bbBitwise st op xss (i + 1) bs
    | none => false

/-- The carry into bit `j`: `(a[j-1] ∧ b[j-1]) ∨ ((a[j-1] ⊕ b[j-1]) ∧ c[j-1])`. -/
def carryNode (st : St) (pa pb pc c : Nat) : Bool :=
  match st.pool[c]? with
  | some ⟨.disj, args⟩ =>
    match args.toList with
    | [u, v] =>
      isConjOf st u pa pb &&
      (match st.pool[v]? with
       | some ⟨.conj, vargs⟩ =>
         match vargs.toList with
         | [x, w] => isXorOf st x pa pb && w == pc
         | _ => false
       | _ => false)
    | _ => false
  | _ => false

/-- Ripple-carry sum bits after the first: `r[j] = (a[j] ⊕ b[j]) ⊕ c[j]`. -/
def rippleGo (st : St) : List Nat → List Nat → List Nat → Nat → Nat → Nat → Bool
  | [], [], [], _, _, _ => true
  | a :: as, b :: bs, r :: rs, pa, pb, pc =>
    match st.pool[r]? with
    | some ⟨.boolXor, args⟩ =>
      match args.toList with
      | [s, c] => isXorOf st s a b && carryNode st pa pb pc c && rippleGo st as bs rs a b c
      | _ => false
    | _ => false
  | _, _, _, _, _, _ => false

/-- `res` is the ripple-carry sum of `a` and `b` with the given initial carry. -/
def ripple (st : St) (bi : Builtins) (a b res : List Nat) (init : Bool) : Bool :=
  match a, b, res with
  | a0 :: as, b0 :: bs, r0 :: rs =>
    match st.pool[r0]? with
    | some ⟨.boolXor, args⟩ =>
      match args.toList with
      | [s, c] => isXorOf st s a0 b0 && c == (if init then bi.tt else bi.ff) && rippleGo st as bs rs a0 b0 c
      | _ => false
    | _ => false
  | _, _, _ => false

/-- The first summand vector of a sum (`extract_pre_sum`). -/
def preSum (st : St) : List Nat → Option (List Nat)
  | [] => some []
  | r :: rs =>
    match st.pool[r]? with
    | some ⟨_, args⟩ =>
      match args.toList with
      | s :: _ =>
        match st.pool[s]? with
        | some ⟨_, sargs⟩ =>
          match sargs.toList with
          | p :: _ => (preSum st rs).map (p :: ·)
          | [] => none
        | none => none
      | [] => none
    | none => none

/-- The second summand vector of a sum (`extract_pre_adder`). -/
def preAdder (st : St) : List Nat → Option (List Nat)
  | [] => some []
  | r :: rs =>
    match st.pool[r]? with
    | some ⟨_, args⟩ =>
      match args.toList with
      | s :: _ =>
        match st.pool[s]? with
        | some ⟨_, sargs⟩ =>
          match sargs.toList with
          | _ :: q :: _ => (preAdder st rs).map (q :: ·)
          | _ => none
        | none => none
      | [] => none
    | none => none

/-- Multi-operand addition, peeled one ripple adder at a time from the
last operand (`bb_bv_add`). -/
def bbAddRev (st : St) (bi : Builtins) : List (List Nat) → List Nat → Bool
  | [], _ => false
  | [x0], sum => sum == x0
  | xk :: rest, sum =>
    match preSum st sum with
    | some pre => ripple st bi pre xk sum false && bbAddRev st bi rest pre
    | none => false

/-- `-x = ~x + 0 + 1`. -/
def bbNeg (st : St) (bi : Builtins) (xs bs : List Nat) : Bool :=
  match preSum st bs, preAdder st bs with
  | some pre, some adder =>
    zipAll (fun p x => isNotOf st p x) pre xs && adder.all (· == bi.ff) && ripple st bi pre adder bs true
  | _, _ => false

/-- `x - y = x + ~y + 1`. -/
def bbSub (st : St) (bi : Builtins) (xs ys bs : List Nat) : Bool :=
  match preAdder st bs with
  | some adder => zipAll (fun q y => isNotOf st q y) adder ys && ripple st bi xs adder bs true
  | none => false

/-- Sign extension: the low bits, then copies of the sign bit. -/
def bbSext (xs bs : List Nat) (e : Nat) : Bool :=
  match xs.getLast? with
  | some s => bs == xs ++ List.replicate e s
  | none => false

/-- The unsigned comparator chain over bits given most significant first
(`bb_ult`): `res = ((l = r) ∧ rest) ∨ (¬l ∧ r)`, base `¬l₀ ∧ r₀`
(or `(¬l₀ ∧ r₀) ∨ (l₀ = r₀)` for `≤`). -/
def ultBase (st : St) (l0 r0 res : Nat) : Bool :=
  match st.pool[res]? with
  | some ⟨.conj, args⟩ =>
    match args.toList with
    | [n, r] => r == r0 && isNotOf st n l0
    | _ => false
  | _ => false

def ultGo (st : St) (withEq : Bool) : List Nat → List Nat → Nat → Bool
  | [l0], [r0], res =>
    if withEq then
      match st.pool[res]? with
      | some ⟨.disj, args⟩ =>
        match args.toList with
        | [res', e0] => isEqOf st e0 l0 r0 && ultBase st l0 r0 res'
        | _ => false
      | _ => false
    else ultBase st l0 r0 res
  | l :: ls, r :: rs, res =>
    match st.pool[res]? with
    | some ⟨.disj, args⟩ =>
      match args.toList with
      | [L, R] =>
        (match st.pool[L]? with
         | some ⟨.conj, largs⟩ =>
           match largs.toList with
           | [e, rest] => isEqOf st e l r && ultGo st withEq ls rs rest
           | _ => false
         | _ => false) &&
        (match st.pool[R]? with
         | some ⟨.conj, rargs⟩ =>
           match rargs.toList with
           | [n, r'] => isNotOf st n l && r' == r
           | _ => false
         | _ => false)
      | _ => false
    | _ => false
  | _, _, _ => false

/-! ### Shifts and bit-vector ite -/

/-- The arguments of a boolean ite node `ite(c, t, e)`. -/
def bbIteArgs (st : St) (r : Nat) : Option (Nat × Nat × Nat) :=
  match st.pool[r]? with
  | some ⟨.boolIte, args⟩ =>
    match args.toList with
    | [c, t, e] => some (c, t, e)
    | _ => none
  | _ => none

/-- A `false` literal node (`is_false`). -/
def isFalseNode (st : St) (f : Nat) : Bool := isNode st f ⟨.boolVal false, #[]⟩

/-- `bb_shift_limit`: every result bit is `ite(cond, res[j], fill)` with the
shared guard `cond`; returns the guarded vector `res`. -/
def bbShiftLimit (st : St) (cond : Nat) (isFill : Nat → Bool) : List Nat → Option (List Nat)
  | [] => some []
  | b :: bs =>
    match bbIteArgs st b with
    | some (c, r, f) =>
      if c == cond && isFill f then (bbShiftLimit st cond isFill bs).map (r :: ·) else none
    | none => none

/-- The literal `width` as `n` builtin `true`/`false` bits (`bb_size`). -/
def bbWidthBits (bi : Builtins) (width n : Nat) : List Nat :=
  (List.range n).map fun i => if width.testBit i then bi.tt else bi.ff

/-- `order_base_2 n`: the least `k` with `n ≤ 2^k` (0 for `n ≤ 1`). -/
def bbLog2 (n : Nat) : Nat := if n ≤ 1 then 0 else Nat.log2 (n - 1) + 1

/-- `mapOpt` with the position passed to `f`. -/
def bbMapIdx (f : Nat → Nat → Option Nat) : Nat → List Nat → Option (List Nat)
  | _, [] => some []
  | j, x :: xs =>
    match f j x, bbMapIdx f (j + 1) xs with
    | some y, some ys => some (y :: ys)
    | _, _ => none

/-- One stage of the left-shift barrel shifter (`bb_bv_lsh`) with shift bit
`b` and threshold `T`: `res[j] = ite(b, inject, pre[j])` where `inject` is
`false` for `j < T` and `pre[j - T]` otherwise.  Returns `pre`. -/
def bbLshStage (st : St) (b T : Nat) (res : List Nat) : Option (List Nat) :=
  match bbMapIdx (fun _ r => (bbIteArgs st r).map (·.2.2)) 0 res with
  | some pre =>
    if allIdx (fun j r =>
        match bbIteArgs st r with
        | some (c, inj, _) => c == b && (if j < T then isFalseNode st inj else pre[j - T]? == some inj)
        | none => false) 0 res
    then some pre else none
  | none => none

/-- One stage of the right-shift barrel shifter (`bb_rsh`), `w = res.length`:
for `j + T ≥ w`, `res[j] = ite(b, fill, pre[j])`; otherwise
`res[j] = ite(¬b, pre[j], pre[j + T])`.  Returns `pre`. -/
def bbRshStage (st : St) (isFill : Nat → Bool) (b T : Nat) (res : List Nat) : Option (List Nat) :=
  match bbMapIdx (fun j r => (bbIteArgs st r).map fun (_, t, e) => if j + T ≥ res.length then e else t) 0 res with
  | some pre =>
    if allIdx (fun j r =>
        match bbIteArgs st r with
        | some (c, t, e) =>
          if j + T ≥ res.length then c == b && isFill t
          else isNotOf st c b && pre[j + T]? == some e
        | none => false) 0 res
    then some pre else none
  | none => none

/-- The stages `L-1, …, 0` of a barrel shifter, peeled from the outermost;
stage `i` uses shift bit `ys[i]` and threshold `2^i`. -/
def bbStages (stage : Nat → Nat → List Nat → Option (List Nat)) (ys : List Nat) :
    Nat → List Nat → Option (List Nat)
  | 0, res => some res
  | i + 1, res =>
    match ys[i]? with
    | some b =>
      match stage b (2 ^ i) res with
      | some pre => bbStages stage ys i pre
      | none => none
    | none => none

/-- A shift `x <op> y`: `bs[j] = ite(y <ᵤ width, res[j], fill)` with the
guard the unsigned comparator chain, and `res` a barrel shifter over `xs`
with `ceil(log2 width)` stages. -/
def bbShift (st : St) (bi : Builtins) (isFill : Nat → Bool)
    (stage : Nat → Nat → List Nat → Option (List Nat)) (xs ys bs : List Nat) : Bool :=
  match bs with
  | [] => false
  | b0 :: _ =>
    match bbIteArgs st b0 with
    | some (cond, _, _) =>
      ultGo st false ys.reverse (bbWidthBits bi xs.length ys.length).reverse cond &&
      (match bbShiftLimit st cond isFill bs with
       | some res =>
         match bbStages stage ys (bbLog2 xs.length) res with
         | some fin => fin == xs
         | none => false
       | none => false)
    | none => false

/-- The sign bit of `xs` (fill of an arithmetic right shift). -/
def isLastOf (xs : List Nat) (f : Nat) : Bool := xs.getLast? == some f

/-- One bit of a bit-vector ite (`bb_bv_ite`): `(¬c ∨ t) ∧ (c ∨ e)`. -/
def bbIteBit (st : St) (c t e b : Nat) : Bool :=
  match st.pool[b]? with
  | some ⟨.conj, args⟩ =>
    match args.toList with
    | [d1, d2] =>
      isNode st d2 ⟨.disj, #[c, e]⟩ &&
      (match st.pool[d1]? with
       | some ⟨.disj, dargs⟩ =>
         match dargs.toList with
         | [n, t'] => isNotOf st n c && t' == t
         | _ => false
       | _ => false)
    | _ => false
  | _ => false

def bbIte (st : St) (c : Nat) (ts es bs : List Nat) : Bool :=
  allIdx (fun i b =>
    match ts[i]?, es[i]? with
    | some t, some e => bbIteBit st c t e b
    | _, _ => false) 0 bs

def bbTerm (st : St) (bi : Builtins) (a : Nat) (bs : List Nat) : Bool :=
  match st.pool[a]? with
  | some ⟨.bvVar _ _, _⟩ => bbVar st a bs
  | some ⟨.bvVal _ v, _⟩ => bbVal bi v bs
  | some ⟨.bvIte _, args⟩ =>
    match args.toList with
    | [c, t, e] =>
      match bitsOf st t, bitsOf st e with
      | some ts, some es => bbIte st c ts es bs
      | _, _ => false
    | _ => false
  | some ⟨op, args⟩ =>
    match mapOpt (bitsOf st) args.toList with
    | none => false
    | some xss =>
      match op, xss with
      | .bvNot _, [xs] => zipAll (fun b x => isNotOf st b x) bs xs
      | .bvNeg _, [xs] => bbNeg st bi xs bs
      | .bvAdd _, _ => bbAddRev st bi xss.reverse bs
      | .bvSub _, [xs, ys] => bbSub st bi xs ys bs
      | .bvAnd _, _ => bbBitwise st .conj xss 0 bs
      | .bvOr _, _ => bbBitwise st .disj xss 0 bs
      | .bvXor _, _ => bbBitwise st .boolXor xss 0 bs
      | .bvConcat _, _ => bs == xss.reverse.flatten
      | .bvExtract hi lo, [xs] => bs == (xs.drop lo).take (hi - lo + 1)
      | .bvSignExtend _ e, [xs] => bbSext xs bs e
      | .bvShl _, [xs, ys] => bbShift st bi (isFalseNode st) (bbLshStage st) xs ys bs
      | .bvLshr _, [xs, ys] => bbShift st bi (isFalseNode st) (bbRshStage st (isFalseNode st)) xs ys bs
      | .bvAshr _, [xs, ys] => bbShift st bi (isLastOf xs) (bbRshStage st (isLastOf xs)) xs ys bs
      | _, _ => false
  | none => false

/-- Signed comparator (`bb_slt`): sign bits first, then the unsigned chain. -/
def sltChain (st : St) (withEq : Bool) (ls rs : List Nat) (res : Nat) : Bool :=
  match ls, rs with
  | ls_s :: ls', rs_s :: rs' =>
    ls'.length ≥ 1 &&
    (match st.pool[res]? with
     | some ⟨.disj, args⟩ =>
       match args.toList with
       | [S, N] =>
         (match st.pool[N]? with
          | some ⟨.conj, nargs⟩ =>
            match nargs.toList with
            | [l, nr] => l == ls_s && isNotOf st nr rs_s
            | _ => false
          | _ => false) &&
         (match st.pool[S]? with
          | some ⟨.conj, sargs⟩ =>
            match sargs.toList with
            | [e, rest] => isEqOf st e ls_s rs_s && ultGo st withEq ls' rs' rest
            | _ => false
          | _ => false)
       | _ => false
     | _ => false)
  | _, _ => false

def bbAtom (st : St) (a b : Nat) : Bool :=
  match st.pool[a]? with
  | some ⟨op, args⟩ =>
    match args.toList with
    | [x, y] =>
      match bitsOf st x, bitsOf st y with
      | some xs, some ys =>
        match op with
        | .eq =>
          match st.pool[b]? with
          | some ⟨.conj, cs⟩ => eqBits st cs.toList xs ys
          | _ => false
        | .ult => ultGo st false xs.reverse ys.reverse b
        | .ule => ultGo st true xs.reverse ys.reverse b
        | .slt => sltChain st false xs.reverse ys.reverse b
        | .sle => sltChain st true xs.reverse ys.reverse b
        | _ => false
      | _, _ => false
    | _ => false
  | none => false
where
  eqBits (st : St) : List Nat → List Nat → List Nat → Bool
    | [], [], [] => true
    | c :: cs, x :: xs, y :: ys => isEqOf st c x y && eqBits st cs xs ys
    | _, _, _ => false

end Bcf
