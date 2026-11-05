import Bcf.State

/-!
# The REWRITE engine

BCF's rewrite table (`bcf_rewrites.h`) is a set of schematic equations
`lhs = rhs` over parameters `V(i)`, optionally guarded by a condition
that must be proved by earlier steps.  A step names a rewrite and gives
the parameter expressions; the checker instantiates both sides
(`instantiate`, mirroring `parse_rw_expr`/`convert_rw_expr`) and
concludes `lhs = rhs`.

`denote` is the value-level meaning of a pattern; `RwSound.lean` proves
that instantiation agrees with it and, per rewrite, that both sides
denote the same value.
-/

namespace Bcf

/-- Built-in `true` and `false` nodes. -/
structure Builtins where
  tt : Nat
  ff : Nat
  deriving Repr, Inhabited

/-! ## Constant expressions -/

/-- `true` when node `i` contains no variables (fuel-bounded). -/
def noVarsF (pool : Pool) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, i =>
    match pool[i]? with
    | none => false
    | some n =>
      match n.op with
      | .bvVar _ _ => false
      | .boolVar _ => false
      | .bvSize _ => true   -- the width of a variable is a constant
      | _ => n.args.all (fun a => a < i && noVarsF pool fuel a)

def noVars (pool : Pool) (i : Nat) : Bool := noVarsF pool (i + 1) i

/-- Constant evaluation (`eval_const_expr`): fails on variables and reads
the width of a `bvsize` operand from the type memo instead of evaluating
it, so it is cheap on large terms.  `cval_eval` shows it agrees with
`eval` under every assignment. -/
def cvalF (st : St) : Nat → Nat → Option Val
  | 0, _ => none
  | f + 1, i =>
    match st.pool[i]? with
    | none => none
    | some n =>
      match n.op with
      | .bvVar _ _ => none
      | .boolVar _ => none
      | .bvSize w =>
        match n.args.toList with
        | [a] =>
          match st.tys[a]? with
          | some (.bv m) => some (Op.eval (fun _ => 0) (.bvSize w) [.bv m 0])
          | _ => none
        | _ => none
      | op =>
        match mapOpt (fun a => if a < i then cvalF st f a else none) n.args.toList with
        | some vs => some (Op.eval (fun _ => 0) op vs)
        | none => none

def cval (st : St) (i : Nat) : Option Val := cvalF st (i + 1) i

/-- One step of memoised constant evaluation: the value of node `i`
from the values of its (earlier) children in `memo`. -/
def memoStep (st : St) (memo : Array (Option Val)) (i : Nat) : Option Val :=
  match st.pool[i]? with
  | none => none
  | some n =>
    match n.op with
    | .bvVar _ _ => none
    | .boolVar _ => none
    | .bvSize w =>
      match n.args.toList with
      | [a] =>
        match st.tys[a]? with
        | some (.bv m) => some (Op.eval (fun _ => 0) (.bvSize w) [.bv m 0])
        | _ => none
      | _ => none
    | op =>
      match mapOpt (fun a => if a < i then (memo[a]?).bind id else none) n.args.toList with
      | some vs => some (Op.eval (fun _ => 0) op vs)
      | none => none

def memoPush (st : St) (m : Array (Option Val)) (k : Nat) : Array (Option Val) :=
  m.push (memoStep st m k)

/-- Values of nodes `0 .. k-1`, computed bottom-up in linear time. -/
def memoBuild (st : St) : Nat → Array (Option Val)
  | 0 => #[]
  | k + 1 => memoPush st (memoBuild st k) k

/-- The value of node `i`, memoised (`memoVal_eval`). -/
def memoVal (st : St) (i : Nat) : Option Val := memoStep st (memoBuild st i) i

/-- The constant value of a variable-free bit-vector node, as a number. -/
def constNat (st : St) (i : Nat) : Option Nat :=
  match cval st i with
  | some (.bv _ x) => some x.toNat
  | _ => none

/-! ## Patterns -/

/-- Parameter types of a rewrite (`Q`, `Bool`, `BV(w)`, `BVQ`, `Bools`, `BVQs`). -/
inductive RwTy where
  | any | bool | bv (w : Nat) | bvq | bools | bvqs
  deriving DecidableEq, Repr

/-- Operators that take their arguments as sub-patterns. -/
inductive RwOp where
  | not | eq | neq | implies | conj | disj | xor
  | ult | ule | ugt | uge | slt | sle | sgt | sge
  | bvadd | bvsub | bvmul | bvneg | bvnot | bvshl | bvlshr | bvashr | bvor | bvand | bvxor
  | bvudiv | bvurem
  | concat | bvsize
  deriving DecidableEq, Repr

mutual
inductive RwExpr where
  | var (i : Nat)
  | tt | ff
  /-- `bv_val(32, v)` -/
  | lit (v : Nat)
  /-- `bv_sym_val(val, sz)`: the literal of width `sz` and value `val`, both constants. -/
  | symVal (val sz : RwExpr)
  /-- `bvmax(sz)`: all ones. -/
  | bvmax (sz : RwExpr)
  | app (op : RwOp) (args : RwArgs)
  | ite (c t e : RwExpr)
  | extract (hi lo x : RwExpr)
  | zext (e x : RwExpr)
  | sext (e x : RwExpr)
  | repeat (n x : RwExpr)
inductive RwArgs where
  | nil
  | cons (a : RwExpr) (rest : RwArgs)
end

def RwArgs.ofList : List RwExpr → RwArgs
  | [] => .nil
  | a :: rest => .cons a (RwArgs.ofList rest)

/-- Variadic operators that collapse to their single argument (`reducible_variadic`). -/
def RwOp.reducible : RwOp → Bool
  | .conj | .disj | .xor | .bvadd | .bvmul | .bvor | .bvand | .bvxor | .concat => true
  | _ => false

/-- The pool operator for a pattern operator at width `w`. -/
def RwOp.node : RwOp → Nat → Op
  | .not, _ => .boolNot
  | .eq, _ => .eq
  | .neq, _ => .distinct
  | .implies, _ => .implies
  | .conj, _ => .conj
  | .disj, _ => .disj
  | .xor, _ => .boolXor
  | .ult, _ => .ult
  | .ule, _ => .ule
  | .ugt, _ => .ugt
  | .uge, _ => .uge
  | .slt, _ => .slt
  | .sle, _ => .sle
  | .sgt, _ => .sgt
  | .sge, _ => .sge
  | .bvadd, w => .bvAdd w
  | .bvsub, w => .bvSub w
  | .bvmul, w => .bvMul w
  | .bvneg, w => .bvNeg w
  | .bvnot, w => .bvNot w
  | .bvshl, w => .bvShl w
  | .bvlshr, w => .bvLshr w
  | .bvashr, w => .bvAshr w
  | .bvor, w => .bvOr w
  | .bvand, w => .bvAnd w
  | .bvxor, w => .bvXor w
  | .bvudiv, w => .bvUdiv w
  | .bvurem, w => .bvUrem w
  | .concat, w => .bvConcat w
  | .bvsize, _ => .bvSize 32

/-! ## Instantiation -/

/-- Width of the first bit-vector among the types. -/
def firstBv : List Ty → Nat
  | [] => 0
  | .bv w :: _ => w
  | _ :: rest => firstBv rest

/-- Sum of the widths (0 if some type is not a bit-vector). -/
def sumBv : List Ty → Nat
  | [] => 0
  | .bv w :: rest => w + sumBv rest
  | _ :: _ => 0

/-- The width to give a pattern operator, from its argument types
(`convert_rw_expr`'s "Resolve bv size"). -/
def RwOp.width (op : RwOp) (tys : List Ty) : Nat :=
  match op with
  | .concat => sumBv tys
  | .bvsize => 32
  | _ => firstBv tys

/-- Elements contributed by an argument node: a list node is spliced. -/
def spliceIdx (st : St) (i : Nat) : Option (List Nat) :=
  match st.tys[i]? with
  | some (.list _ _) =>
    match st.pool[i]? with
    | some ⟨.listVal _, elems⟩ => some elems.toList
    | _ => none
  | some _ => some [i]
  | none => none

/-- The literal node for a constant of width `sz` and value `v`. -/
def pushLit (st : St) (sz v : Nat) : Option (St × Nat) :=
  if sz ≤ 255 then pushNode st ⟨.bvVal sz v, #[]⟩ else none

/-- Build the node of `op` over already-instantiated arguments. -/
def pushApp (st : St) (op : RwOp) (is : List Nat) : Option (St × Nat) :=
  match is with
  | [] => none
  | [i] => if op.reducible then some (st, i) else
      match mapOpt (fun a => st.tys[a]?) is with
      | some tys => pushNode st ⟨op.node (op.width tys), is.toArray⟩
      | none => none
  | _ =>
      match mapOpt (fun a => st.tys[a]?) is with
      | some tys => pushNode st ⟨op.node (op.width tys), is.toArray⟩
      | none => none

mutual
/-- Instantiate a pattern: `args` are the parameter nodes. -/
def instE (bi : Builtins) (args : Array Nat) : RwExpr → St → Option (St × Nat)
  | .var i, st => match args[i]? with
    | some a => some (st, a)
    | none => none
  | .tt, st => some (st, bi.tt)
  | .ff, st => some (st, bi.ff)
  | .lit v, st => pushNode st ⟨.bvVal 32 v, #[]⟩
  | .symVal val sz, st =>
    match instE bi args val st with
    | some (st1, v) =>
      match instE bi args sz st1 with
      | some (st2, s) =>
        match constNat st2 v, constNat st2 s with
        | some vn, some sn => pushLit st2 sn vn
        | _, _ => none
      | none => none
    | none => none
  | .bvmax sz, st =>
    match instE bi args sz st with
    | some (st1, s) =>
      match constNat st1 s with
      | some sn => pushLit st1 sn (2 ^ sn - 1)
      | none => none
    | none => none
  | .app op as, st =>
    match instA bi args as st with
    | some (st1, is) => pushApp st1 op is
    | none => none
  | .ite c t e, st =>
    match instE bi args c st with
    | some (st1, ci) =>
      match instE bi args t st1 with
      | some (st2, ti) =>
        match instE bi args e st2 with
        | some (st3, ei) =>
          match st3.tys[ti]? with
          | some .bool => pushNode st3 ⟨.boolIte, #[ci, ti, ei]⟩
          | some (.bv w) => pushNode st3 ⟨.bvIte w, #[ci, ti, ei]⟩
          | _ => none
        | none => none
      | none => none
    | none => none
  | .extract hi lo x, st =>
    match instE bi args hi st with
    | some (st1, hi') =>
      match instE bi args lo st1 with
      | some (st2, lo') =>
        match instE bi args x st2 with
        | some (st3, xi) =>
          match constNat st3 hi', constNat st3 lo' with
          | some h, some l => if h ≤ 255 ∧ l ≤ 255 then pushNode st3 ⟨.bvExtract h l, #[xi]⟩ else none
          | _, _ => none
        | none => none
      | none => none
    | none => none
  | .zext e x, st =>
    match instE bi args e st with
    | some (st1, e') =>
      match instE bi args x st1 with
      | some (st2, xi) =>
        match constNat st2 e', st2.tys[xi]? with
        | some k, some (.bv n) => if k ≤ 255 then pushNode st2 ⟨.bvZeroExtend (n + k) k, #[xi]⟩ else none
        | _, _ => none
      | none => none
    | none => none
  | .sext e x, st =>
    match instE bi args e st with
    | some (st1, e') =>
      match instE bi args x st1 with
      | some (st2, xi) =>
        match constNat st2 e', st2.tys[xi]? with
        | some k, some (.bv n) => if k ≤ 255 then pushNode st2 ⟨.bvSignExtend (n + k) k, #[xi]⟩ else none
        | _, _ => none
      | none => none
    | none => none
  | .repeat n x, st =>
    match instE bi args n st with
    | some (st1, n') =>
      match instE bi args x st1 with
      | some (st2, xi) =>
        match constNat st2 n', st2.tys[xi]? with
        | some k, some (.bv m) => if k ≤ 255 then pushNode st2 ⟨.bvRepeat (m * k) k, #[xi]⟩ else none
        | _, _ => none
      | none => none
    | none => none

def instA (bi : Builtins) (args : Array Nat) : RwArgs → St → Option (St × List Nat)
  | .nil, st => some (st, [])
  | .cons a rest, st =>
    match instE bi args a st with
    | some (st1, i) =>
      match spliceIdx st1 i with
      | some items =>
        match instA bi args rest st1 with
        | some (st2, is) => some (st2, items ++ is)
        | none => none
      | none => none
    | none => none
end

/-! ## Value semantics -/

/-- Width of the first bit-vector value. -/
def RwOp.widthV (op : RwOp) (vs : List Val) : Nat :=
  match Val.tys vs with
  | some tys => op.width tys
  | none => 0

/-- Value of an operator applied to spliced argument values. -/
def appVal (op : RwOp) (vs : List Val) : Val :=
  match vs with
  | [] => .bad
  | [v] => if op.reducible then v else Op.eval (fun _ => 0) (op.node (op.widthV vs)) vs
  | _ => Op.eval (fun _ => 0) (op.node (op.widthV vs)) vs

def spliceVal : Val → List Val
  | .list _ vs => vs
  | v => [v]

mutual
def denoteE (env : Nat → Val) : RwExpr → Val
  | .var i => env i
  | .tt => .bool true
  | .ff => .bool false
  | .lit v => bvValEval 32 v []
  | .symVal val sz =>
    match denoteE env val, denoteE env sz with
    | .bv _ x, .bv _ s => bvValEval s.toNat x.toNat []
    | _, _ => .bad
  | .bvmax sz =>
    match denoteE env sz with
    | .bv _ s => bvValEval s.toNat (2 ^ s.toNat - 1) []
    | _ => .bad
  | .app op as => appVal op (denoteA env as)
  | .ite c t e =>
    match denoteE env t with
    | .bool _ => boolIteEval [denoteE env c, denoteE env t, denoteE env e]
    | .bv w _ => bvIteEval w [denoteE env c, denoteE env t, denoteE env e]
    | _ => .bad
  | .extract hi lo x =>
    match denoteE env hi, denoteE env lo with
    | .bv _ h, .bv _ l => bvExtractEval h.toNat l.toNat [denoteE env x]
    | _, _ => .bad
  | .zext e x =>
    match denoteE env e, denoteE env x with
    | .bv _ k, .bv n xv => bvExtEval false (n + k.toNat) k.toNat [.bv n xv]
    | _, _ => .bad
  | .sext e x =>
    match denoteE env e, denoteE env x with
    | .bv _ k, .bv n xv => bvExtEval true (n + k.toNat) k.toNat [.bv n xv]
    | _, _ => .bad
  | .repeat n x =>
    match denoteE env n, denoteE env x with
    | .bv _ k, .bv m xv => bvRepeatEval (m * k.toNat) k.toNat [.bv m xv]
    | _, _ => .bad

def denoteA (env : Nat → Val) : RwArgs → List Val
  | .nil => []
  | .cons a rest => spliceVal (denoteE env a) ++ denoteA env rest
end

/-! ## The rewrite table -/

structure RwRule where
  params : List RwTy
  cond : Option RwExpr
  lhs : RwExpr
  rhs : RwExpr

namespace RwExpr

def mk (op : RwOp) (l : List RwExpr) : RwExpr := app op (RwArgs.ofList l)
def V (i : Nat) : RwExpr := var i
def l0 : RwExpr := lit 0
def l1 : RwExpr := lit 1
def not' (a : RwExpr) := mk .not [a]
def eq' (a b : RwExpr) := mk .eq [a, b]
def neq' (a b : RwExpr) := mk .neq [a, b]
def conj' (l : List RwExpr) := mk .conj l
def xor' (l : List RwExpr) := mk .xor l
def ult' (a b : RwExpr) := mk .ult [a, b]
def ule' (a b : RwExpr) := mk .ule [a, b]
def slt' (a b : RwExpr) := mk .slt [a, b]
def sle' (a b : RwExpr) := mk .sle [a, b]
def sge' (a b : RwExpr) := mk .sge [a, b]
def bvadd' (l : List RwExpr) := mk .bvadd l
def bvsub' (a b : RwExpr) := mk .bvsub [a, b]
def bvmul' (l : List RwExpr) := mk .bvmul l
def bvshl' (a b : RwExpr) := mk .bvshl [a, b]
def bvashr' (a b : RwExpr) := mk .bvashr [a, b]
def bvand' (l : List RwExpr) := mk .bvand l
def bvor' (l : List RwExpr) := mk .bvor l
def concat' (l : List RwExpr) := mk .concat l
def bvsize' (a : RwExpr) := mk .bvsize [a]
def implies' (a b : RwExpr) := mk .implies [a, b]
def disj' (l : List RwExpr) := mk .disj l
def ugt' (a b : RwExpr) := mk .ugt [a, b]
def uge' (a b : RwExpr) := mk .uge [a, b]
def sgt' (a b : RwExpr) := mk .sgt [a, b]
def bvneg' (a : RwExpr) := mk .bvneg [a]
def bvnot' (a : RwExpr) := mk .bvnot [a]
def bvlshr' (a b : RwExpr) := mk .bvlshr [a, b]
def bvxor' (l : List RwExpr) := mk .bvxor l
def bvudiv' (a b : RwExpr) := mk .bvudiv [a, b]
def bvurem' (a b : RwExpr) := mk .bvurem [a, b]

end RwExpr

/-- `rw_type_check`.  Bit-vector widths are bounded as in BCF (a `u8`
field), which the rewrites with signed 32-bit size arithmetic rely on. -/
def rwTyOK (t : RwTy) (ty : Option Ty) : Bool :=
  match t, ty with
  | .any, some _ => true
  | .bool, some .bool => true
  | .bv w, some (.bv w') => w == w'
  | .bvq, some (.bv w) => w ≤ 255
  | .bools, some (.list true _) => true
  | .bvqs, some (.list false _) => true
  | _, _ => false

def paramsOK (st : St) : List RwTy → List Nat → Bool
  | [], [] => true
  | t :: ts, a :: as => rwTyOK t st.tys[a]? && paramsOK st ts as
  | _, _ => false

end Bcf
