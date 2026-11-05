/-!
# EmbC: a small C subset embedded in Lean — syntax

The language is deliberately tiny.  Values are unsigned 32- and 64-bit
integers and pointers.  There is no signed arithmetic, no integer
promotion, no address-of, no pointer casts, and no `goto`.  Memory is
reached only through pointers handed out by kernel allocation functions
(`Ext`), whose behaviour is given by trusted specifications in
`EmbC/Kernel.lean`.

Everything here is plain data: `EmbC/Semantics.lean` gives it meaning and
`EmbC/Print.lean` turns it into C text.
-/

namespace EmbC

/-- C types.  `struct` may only appear under a pointer. -/
inductive Ty where
  | u32
  | u64
  | ptr (elem : Ty)
  | struct (name : String)
  /-- The kernel's `bpfptr_t`: an opaque handle to memory the caller supplied
  (user or kernel).  It can only be passed to `copy_from_bpfptr`. -/
  | bpfptr
  deriving DecidableEq, Repr, Inhabited

abbrev Var := String

inductive BinOp where
  | add | sub | mul | div | mod
  | band | bor | bxor | shl | shr
  | eq | ne | lt | le | gt | ge
  deriving DecidableEq, Repr, Inhabited

/-- Side-effect-free expressions.  Calls are statements, not expressions. -/
inductive Expr where
  | var (x : Var)
  | lit32 (v : BitVec 32)
  | lit64 (v : BitVec 64)
  | null
  /-- A named `u32` constant; printed as its name, backed by a `#define`. -/
  | named (name : String) (v : BitVec 32)
  /-- Read of a global constant table, `g[i]`. -/
  | cload (g : String) (i : Expr)
  | bin (op : BinOp) (a b : Expr)
  /-- Logical negation `!a`. -/
  | lnot (a : Expr)
  /-- Bitwise complement `~a`. -/
  | bnot (a : Expr)
  /-- Short-circuit `a && b`. -/
  | land (a b : Expr)
  /-- Short-circuit `a || b`. -/
  | lor (a b : Expr)
  /-- Integer conversion between `u32` and `u64`. -/
  | cast (t : Ty) (a : Expr)
  /-- Array read `p[i]`. -/
  | index (p i : Expr)
  /-- Struct field read `p->f`. -/
  | field (p : Expr) (f : String)
  /-- Pointer offset `p + i`, staying inside (or one past) the block. -/
  | padd (p i : Expr)
  deriving Repr, Inhabited

/-- Kernel functions the language may call.  Each has a trusted
specification (`Ext.run`) and a fixed C rendering. -/
inductive Ext where
  /-- `kvcalloc(n, sizeof(t), GFP)`: a zeroed array of `n` cells, or `NULL`. -/
  | kvcalloc (t : Ty)
  /-- `kzalloc(sizeof(struct s), GFP)`: one zeroed struct, or `NULL`. -/
  | kzalloc (s : String)
  /-- `kvrealloc(p, array_size(n, sizeof(t)), GFP)`. -/
  | kvrealloc (t : Ty)
  /-- `kvfree(p)`. -/
  | kvfree
  /-- `copy_from_bpfptr(dst, src, array_size(n, sizeof(u32))) != 0`: copy `n`
  words from the caller's memory; non-zero on failure. -/
  | copyFromBpfptr
  /-- `signal_pending(current) != 0`. -/
  | signalPending
  /-- `cond_resched()`. -/
  | condResched
  deriving DecidableEq, Repr, Inhabited

inductive Stmt where
  | skip
  | assign (x : Var) (e : Expr)
  /-- `p[i] = e` -/
  | store (p i e : Expr)
  /-- `p->f = e` -/
  | setField (p : Expr) (f : String) (e : Expr)
  | seq (a b : Stmt)
  | ite (c : Expr) (a b : Stmt)
  | while (c : Expr) (body : Stmt)
  | call (dst : Option Var) (f : String) (args : List Expr)
  | ecall (dst : Option Var) (f : Ext) (args : List Expr)
  | ret (e : Option Expr)
  | brk
  deriving Repr, Inhabited

structure Fn where
  name : String
  params : List (Var × Ty)
  /-- `none` is `void`. -/
  ret : Option Ty
  locals : List (Var × Ty)
  body : Stmt
  deriving Repr, Inhabited

structure StructDef where
  name : String
  fields : List (String × Ty)
  deriving Repr, Inhabited

/-- A global read-only table of `u32` words. -/
structure ConstDef where
  name : String
  words : Array (BitVec 32)
  deriving Repr, Inhabited

structure Prog where
  structs : List StructDef
  fns : List Fn
  consts : List ConstDef := []
  deriving Repr, Inhabited

def Prog.findConst (P : Prog) (g : String) : Option ConstDef := P.consts.find? (·.name == g)

def Prog.findFn (P : Prog) (f : String) : Option Fn := P.fns.find? (·.name == f)

def Prog.findStruct (P : Prog) (s : String) : Option StructDef := P.structs.find? (·.name == s)

/-- Position and type of a field in a field list. -/
def fieldIn : List (String × Ty) → String → Option (Nat × Ty)
  | [], _ => none
  | (g, t) :: rest, f =>
    if g = f then some (0, t) else
    match fieldIn rest f with
    | some (i, t') => some (i + 1, t')
    | none => none

/-- Position and type of a field inside its struct. -/
def StructDef.field? (d : StructDef) (f : String) : Option (Nat × Ty) := fieldIn d.fields f

/-- Sequence a list of statements. -/
def Stmt.block : List Stmt → Stmt
  | [] => .skip
  | [s] => s
  | s :: rest => .seq s (Stmt.block rest)

end EmbC
