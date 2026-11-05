import EmbC.Kernel

/-!
# EmbC: expression evaluation and runtime types

**This file is part of the trusted base**: it is what we claim the printed C
means.  Statement execution is defined by `Semantics.next`.

* Runtime errors lead the source machine to a *stuck* state:
  out-of-bounds or dangling access, reading uninitialised memory, division
  by zero, an over-wide shift, mixing 32- and 64-bit operands, a value of
  the wrong type reaching a variable, field, parameter or return.

The implicit conversions of C never happen on a run that is not stuck,
because every place C would convert is a place the runtime checks that
the types already agree.
-/

namespace EmbC

/-! ## Local variables -/

/-- A frame: each variable with its declared type and current value. -/
abbrev Env := List (Var × Ty × Val)

def Env.get : Env → Var → Option Val
  | [], _ => none
  | (y, _, v) :: rest, x => if y = x then some v else Env.get rest x

def Env.ty : Env → Var → Option Ty
  | [], _ => none
  | (y, t, _) :: rest, x => if y = x then some t else Env.ty rest x

def Env.set : Env → Var → Val → Env
  | [], _, _ => []
  | (y, t, w) :: rest, x, v => if y = x then (y, t, v) :: rest else (y, t, w) :: Env.set rest x v

/-- Assignment to a declared variable, checked against its declared type. -/
def Env.assign (env : Env) (m : Mem) (x : Var) (v : Val) : Option Env :=
  match env.ty x with
  | none => none
  | some t => if m.hasTy v t then some (env.set x v) else none

/-! ## Expressions -/

def evalArith {w : Nat} (mk : BitVec w → Val) (op : BinOp) (a b : BitVec w) : Option Val :=
  match op with
  | .add => some (mk (a + b))
  | .sub => some (mk (a - b))
  | .mul => some (mk (a * b))
  | .div => if b = 0 then none else some (mk (a / b))
  | .mod => if b = 0 then none else some (mk (a % b))
  | .band => some (mk (a &&& b))
  | .bor => some (mk (a ||| b))
  | .bxor => some (mk (a ^^^ b))
  | .shl => if b.toNat < w then some (mk (a <<< b.toNat)) else none
  | .shr => if b.toNat < w then some (mk (a >>> b.toNat)) else none
  | .eq => some (.ofBool (decide (a = b)))
  | .ne => some (.ofBool (decide (a ≠ b)))
  | .lt => some (.ofBool (decide (a < b)))
  | .le => some (.ofBool (decide (a ≤ b)))
  | .gt => some (.ofBool (decide (b < a)))
  | .ge => some (.ofBool (decide (b ≤ a)))

/-- Pointer equality.  Defined only against `NULL` or inside one live block. -/
def ptrEq (m : Mem) : Val → Val → Option Bool
  | .null, .null => some true
  | .ptr b _, .null => if (m.block? b).isSome then some false else none
  | .null, .ptr b _ => if (m.block? b).isSome then some false else none
  | .ptr b o, .ptr b' o' => if b = b' ∧ (m.block? b).isSome then some (decide (o = o')) else none
  | _, _ => none

def evalBin (m : Mem) (op : BinOp) : Val → Val → Option Val
  | .u32 a, .u32 b => evalArith .u32 op a b
  | .u64 a, .u64 b => evalArith .u64 op a b
  | a, b =>
    match op with
    | .eq => (ptrEq m a b).map Val.ofBool
    | .ne => (ptrEq m a b).map (fun r => Val.ofBool (!r))
    | _ => none

def evalCast : Ty → Val → Option Val
  | .u32, .u32 v => some (.u32 v)
  | .u64, .u64 v => some (.u64 v)
  | .u64, .u32 v => some (.u64 (v.setWidth 64))
  | .u32, .u64 v => some (.u32 (v.setWidth 32))
  | _, _ => none

def evalE (P : Prog) (env : Env) (m : Mem) : Expr → Option Val
  | .var x => env.get x
  | .lit32 v => some (.u32 v)
  | .lit64 v => some (.u64 v)
  | .null => some .null
  | .named _ v => some (.u32 v)
  | .cload g i =>
    match P.findConst g, evalE P env m i with
    | some c, some vi =>
      match vi.toIdx with
      | some k =>
        match c.words[k]? with
        | some w => some (.u32 w)
        | none => none
      | none => none
    | _, _ => none
  | .bin op a b =>
    match evalE P env m a, evalE P env m b with
    | some va, some vb => evalBin m op va vb
    | _, _ => none
  | .lnot a =>
    match evalE P env m a with
    | some (.u32 v) => some (.ofBool (decide (v = 0)))
    | _ => none
  | .bnot a =>
    match evalE P env m a with
    | some (.u32 v) => some (.u32 (~~~v))
    | some (.u64 v) => some (.u64 (~~~v))
    | _ => none
  | .land a b =>
    match evalE P env m a with
    | some (.u32 x) =>
      if x = 0 then some (.u32 0) else
      match evalE P env m b with
      | some (.u32 y) => some (.ofBool (decide (y ≠ 0)))
      | _ => none
    | _ => none
  | .lor a b =>
    match evalE P env m a with
    | some (.u32 x) =>
      if x ≠ 0 then some (.u32 1) else
      match evalE P env m b with
      | some (.u32 y) => some (.ofBool (decide (y ≠ 0)))
      | _ => none
    | _ => none
  | .cast t a =>
    match evalE P env m a with
    | some v => evalCast t v
    | none => none
  | .index p i =>
    match evalE P env m p, evalE P env m i with
    | some (.ptr b off), some vi =>
      match vi.toIdx with
      | some k => m.loadArr b (off + k)
      | none => none
    | _, _ => none
  | .field p f =>
    match evalE P env m p with
    | some (.ptr b off) => if off = 0 then m.loadField P b f else none
    | _ => none
  | .padd p i =>
    match evalE P env m p, evalE P env m i with
    | some (.ptr b off), some vi =>
      match vi.toIdx, m.block? b with
      | some k, some blk =>
        if blk.elem.isStruct then none else
        if off + k ≤ blk.cells.size then some (.ptr b (off + k)) else none
      | _, _ => none
    | _, _ => none

def evalArgs (P : Prog) (env : Env) (m : Mem) : List Expr → Option (List Val)
  | [] => some []
  | e :: es =>
    match evalE P env m e, evalArgs P env m es with
    | some v, some vs => some (v :: vs)
    | _, _ => none

/-! ## Statements -/

inductive Outcome where
  | normal
  | brk
  | ret (v : Option Val)
  deriving Repr, Inhabited

inductive Res (α : Type) where
  | timeout
  | stuck
  | ok (a : α)
  deriving Repr, Inhabited

/-- Bind actual arguments to parameters, checking their types. -/
def bindParams (m : Mem) : List (Var × Ty) → List Val → Option Env
  | [], [] => some []
  | (x, t) :: ps, v :: vs =>
    if m.hasTy v t then
      match bindParams m ps vs with
      | some env => some ((x, t, v) :: env)
      | none => none
    else none
  | _, _ => none

/-- Locals start at zero.  (The printer emits the same initialisers.) -/
def initLocals (ls : List (Var × Ty)) : Env := ls.map fun (x, t) => (x, t, t.zero)

/-- Store a call's result into its destination variable, if it has one. -/
def assignDst (env : Env) (m : Mem) : Option Var → Option Val → Option Env
  | none, _ => some env
  | some x, some v => env.assign m x v
  | some _, none => none

end EmbC
