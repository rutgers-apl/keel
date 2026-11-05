import EmbC.Syntax

/-!
# EmbC: the C printer

**This file is part of the trusted base.**  It must print each construct as
C text whose meaning is the one `EmbC/Semantics.lean` gives it.  To keep
that claim easy to audit, every compound operand is parenthesised, literals
carry their suffixes, and locals get explicit initialisers.  Comparisons and
the logical operators have C type `int`; they are cast to `u32` exactly where
that type would matter, as an operand of an arithmetic or bitwise operator
(`Expr.arithOperand`).

The output expects `u32`, `u64`, `NULL`, `array_size`, the allocation
functions and `GFP_KERNEL_ACCOUNT` to be in scope: from kernel headers in
the kernel, or from `EmbC/c/embc_user.h` when testing in userspace.
-/

namespace EmbC

def Ty.cName : Ty → String
  | .u32 => "u32"
  | .u64 => "u64"
  | .ptr t => t.cName ++ " *"
  | .struct s => "struct " ++ s
  | .bpfptr => "bpfptr_t"

/-- A declaration of `x` at type `t`, e.g. `u32 *x`. -/
def Ty.decl (t : Ty) (x : String) : String :=
  match t with
  | .ptr _ => t.cName ++ x
  | _ => t.cName ++ " " ++ x

/-- The initialiser matching `Ty.zero`. -/
def Ty.zeroInit : Ty → String
  | .ptr _ => "NULL"
  | _ => "0"

def BinOp.sym : BinOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .mod => "%"
  | .band => "&" | .bor => "|" | .bxor => "^" | .shl => "<<" | .shr => ">>"
  | .eq => "==" | .ne => "!=" | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="

/-- Operators whose C result has type `int`, with value 0 or 1. -/
def BinOp.isCmp : BinOp → Bool
  | .eq | .ne | .lt | .le | .gt | .ge => true
  | _ => false

/-- Expressions whose C text has type `int`: comparisons and the logical
operators.  Their value is 0 or 1. -/
def Expr.isBool : Expr → Bool
  | .bin op _ _ => op.isCmp
  | .lnot _ | .land _ _ | .lor _ _ => true
  | _ => false

/-- Expressions that need no parentheses as an operand: names, literals and
postfix expressions. -/
def Expr.isAtom : Expr → Bool
  | .var _ | .lit32 _ | .lit64 _ | .null | .named _ _ | .cload _ _ | .index _ _ | .field _ _ => true
  | _ => false

/-- The text `s` of `e` in operand position: parenthesised unless `e` is an atom. -/
def Expr.operand (e : Expr) (s : String) : String :=
  if e.isAtom then s else "(" ++ s ++ ")"

/-- `operand`, and cast to `u32` when `e` has C type `int`: as an operand of an
arithmetic or bitwise operator an `int` would take part in the computation
(`~(a < b)` is a negative `int`, `(a < b) << 31` a signed overflow).  In
every other position — a condition, an operand of `!`, `&&`, `||` or of a
comparison, an assigned or returned value, an argument, an index — C either
converts the value 0 or 1 to the unsigned type of the context unchanged or
only tests it against zero, so no cast is printed there. -/
def Expr.arithOperand (e : Expr) (s : String) : String :=
  if e.isBool then "(u32)(" ++ s ++ ")" else e.operand s

/-- The C text of `e`, without enclosing parentheses; this is the form used
where the grammar needs none (conditions, right-hand sides, `return`,
arguments, indices). -/
def Expr.toC : Expr → String
  | .var x => x
  | .lit32 v => toString v.toNat ++ "u"
  | .lit64 v => toString v.toNat ++ "ull"
  | .null => "NULL"
  | .named n _ => n
  | .cload g i => g ++ "[" ++ i.toC ++ "]"
  | .bin op a b =>
    if op.isCmp then a.operand a.toC ++ " " ++ op.sym ++ " " ++ b.operand b.toC
    else a.arithOperand a.toC ++ " " ++ op.sym ++ " " ++ b.arithOperand b.toC
  | .lnot a => "!" ++ a.operand a.toC
  | .bnot a => "~" ++ a.arithOperand a.toC
  | .land a b => a.operand a.toC ++ " && " ++ b.operand b.toC
  | .lor a b => a.operand a.toC ++ " || " ++ b.operand b.toC
  | .cast t a => "(" ++ t.cName ++ ")" ++ a.operand a.toC
  | .index p i => p.operand p.toC ++ "[" ++ i.toC ++ "]"
  | .field p f => p.operand p.toC ++ "->" ++ f
  | .padd p i => p.operand p.toC ++ " + " ++ i.operand i.toC

/-- The fixed C rendering of each kernel call. -/
def Ext.toC : Ext → List String → String
  | .kvcalloc t, [n] => "kvcalloc(" ++ n ++ ", sizeof(" ++ t.cName ++ "), GFP_KERNEL_ACCOUNT)"
  | .kzalloc s, [] => "kzalloc(sizeof(struct " ++ s ++ "), GFP_KERNEL_ACCOUNT)"
  | .kvrealloc t, [p, n] =>
    "kvrealloc(" ++ p ++ ", array_size(" ++ n ++ ", sizeof(" ++ t.cName ++ ")), GFP_KERNEL_ACCOUNT)"
  | .kvfree, [p] => "kvfree(" ++ p ++ ")"
  | .copyFromBpfptr, [dst, src, n] =>
    "copy_from_bpfptr(" ++ dst ++ ", " ++ src ++ ", array_size(" ++ n ++ ", sizeof(u32))) != 0"
  | .signalPending, [] => "signal_pending(current) != 0"
  | .condResched, [] => "cond_resched()"
  | _, _ => "EMBC_BAD_EXTERN_CALL"

def dstPrefix : Option Var → String
  | none => ""
  | some x => x ++ " = "

def Stmt.toLines (ind : String) : Stmt → List String
  | .skip => []
  | .assign x e => [ind ++ x ++ " = " ++ e.toC ++ ";"]
  | .store p i e => [ind ++ p.operand p.toC ++ "[" ++ i.toC ++ "] = " ++ e.toC ++ ";"]
  | .setField p f e => [ind ++ p.operand p.toC ++ "->" ++ f ++ " = " ++ e.toC ++ ";"]
  | .seq a b => a.toLines ind ++ b.toLines ind
  | .ite c a b =>
    let thenPart := [ind ++ "if (" ++ c.toC ++ ") {"] ++ a.toLines (ind ++ "\t")
    match b with
    | .ite _ _ _ =>
      -- `else if`: the nested statement's own lines open with `if (` and
      -- close their own brace
      match b.toLines ind with
      | first :: rest => thenPart ++ [ind ++ "} else " ++ (first.drop ind.length).toString] ++ rest
      | [] => thenPart ++ [ind ++ "}"]
    | _ =>
      match b.toLines (ind ++ "\t") with
      | [] => thenPart ++ [ind ++ "}"]
      | ls => thenPart ++ [ind ++ "} else {"] ++ ls ++ [ind ++ "}"]
  | .while c body =>
    [ind ++ "while (" ++ c.toC ++ ") {"] ++ body.toLines (ind ++ "\t") ++ [ind ++ "}"]
  | .call dst f args =>
    [ind ++ dstPrefix dst ++ f ++ "(" ++ ", ".intercalate (args.map Expr.toC) ++ ");"]
  | .ecall dst f args => [ind ++ dstPrefix dst ++ f.toC (args.map Expr.toC) ++ ";"]
  | .ret none => [ind ++ "return;"]
  | .ret (some e) => [ind ++ "return " ++ e.toC ++ ";"]
  | .brk => [ind ++ "break;"]

def Fn.signature (fn : Fn) : String :=
  let ret := match fn.ret with
    | none => "void "
    | some t => t.decl ""
  let ret := if ret.endsWith " " || ret.endsWith "*" then ret else ret ++ " "
  let params := match fn.params with
    | [] => "void"
    | ps => ", ".intercalate (ps.map fun (x, t) => t.decl x)
  "static " ++ ret ++ fn.name ++ "(" ++ params ++ ")"

def Fn.toLines (fn : Fn) : List String :=
  [fn.signature, "{"]
    ++ fn.locals.map (fun (x, t) => "\t" ++ t.decl x ++ " = " ++ t.zeroInit ++ ";")
    ++ (if fn.locals.isEmpty then [] else [""])
    ++ fn.body.toLines "\t"
    ++ ["}"]

def StructDef.toLines (d : StructDef) : List String :=
  ["struct " ++ d.name ++ " {"] ++ d.fields.map (fun (f, t) => "\t" ++ t.decl f ++ ";") ++ ["};"]

/-! ## Identifier hygiene

Names are spliced into the output verbatim, so they must be C identifiers. -/

def isCIdent (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => (c.isAlpha || c == '_') && cs.all (fun c => c.isAlphanum || c == '_')

def Expr.names : Expr → List String
  | .var x => [x]
  | .lit32 _ | .lit64 _ | .null | .named _ _ => []
  | .cload g i => g :: i.names
  | .bin _ a b | .land a b | .lor a b | .index a b | .padd a b => a.names ++ b.names
  | .lnot a | .bnot a | .cast _ a => a.names
  | .field p f => f :: p.names

def Ty.names : Ty → List String
  | .struct s => [s]
  | .ptr t => t.names
  | _ => []

def Ext.names : Ext → List String
  | .kvcalloc t | .kvrealloc t => t.names
  | .kzalloc s => [s]
  | .kvfree | .copyFromBpfptr | .signalPending | .condResched => []

def Stmt.names : Stmt → List String
  | .skip | .brk | .ret none => []
  | .assign x e => x :: e.names
  | .store p i e => p.names ++ i.names ++ e.names
  | .setField p f e => f :: p.names ++ e.names
  | .seq a b => a.names ++ b.names
  | .ite c a b => c.names ++ a.names ++ b.names
  | .while c b => c.names ++ b.names
  | .call dst f args => f :: dst.toList ++ args.flatMap Expr.names
  | .ecall dst f args => f.names ++ dst.toList ++ args.flatMap Expr.names
  | .ret (some e) => e.names

/-- Named constants used by an expression, with their values. -/
def Expr.nameds : Expr → List (String × BitVec 32)
  | .named n v => [(n, v)]
  | .var _ | .lit32 _ | .lit64 _ | .null => []
  | .cload _ i => i.nameds
  | .bin _ a b | .land a b | .lor a b | .index a b | .padd a b => a.nameds ++ b.nameds
  | .lnot a | .bnot a | .cast _ a => a.nameds
  | .field p _ => p.nameds

def Stmt.nameds : Stmt → List (String × BitVec 32)
  | .skip | .brk | .ret none => []
  | .assign _ e => e.nameds
  | .store p i e => p.nameds ++ i.nameds ++ e.nameds
  | .setField p _ e => p.nameds ++ e.nameds
  | .seq a b => a.nameds ++ b.nameds
  | .ite c a b => c.nameds ++ a.nameds ++ b.nameds
  | .while c b => c.nameds ++ b.nameds
  | .call _ _ args | .ecall _ _ args => args.flatMap Expr.nameds
  | .ret (some e) => e.nameds

/-- Keep the first definition of each name; report a name given two values. -/
def dedupNameds : List (String × BitVec 32) → List (String × BitVec 32) → Except String (List (String × BitVec 32))
  | [], acc => .ok acc.reverse
  | (n, v) :: rest, acc =>
    match acc.find? (·.1 == n) with
    | some (_, v') => if v' = v then dedupNameds rest acc else .error ("constant " ++ n ++ " has two values")
    | none => dedupNameds rest ((n, v) :: acc)

def ConstDef.toLines (c : ConstDef) : List String :=
  let rec rows (ws : List (BitVec 32)) (fuel : Nat) : List String :=
    match fuel, ws with
    | 0, _ | _, [] => []
    | fuel + 1, ws =>
      ("\t" ++ ", ".intercalate ((ws.take 8).map fun w => toString w.toNat ++ "u") ++ ",")
        :: rows (ws.drop 8) fuel
  ["static const u32 " ++ c.name ++ "[" ++ toString c.words.size ++ "] = {"]
    ++ rows c.words.toList c.words.size ++ ["};"]

def Prog.names (P : Prog) : List String :=
  P.structs.flatMap (fun d => d.name :: d.fields.flatMap (fun (f, t) => f :: t.names))
    ++ P.consts.map (·.name)
    ++ P.fns.flatMap (fun fn =>
        fn.name :: (fn.params ++ fn.locals).flatMap (fun (x, t) => x :: t.names)
          ++ (fn.ret.map Ty.names).getD [] ++ fn.body.names)

/-- Print a whole program.  Fails if a name is not a C identifier, if a named
constant has two values, or if a named constant shares its name with anything
else (the `#define` would silently rewrite it). -/
def Prog.toC (P : Prog) : Except String String := do
  let names := P.names
  if let some bad := names.find? (fun s => !isCIdent s) then
    throw ("not a C identifier: " ++ bad.quote)
  let nameds ← dedupNameds (P.fns.flatMap (fun fn => fn.body.nameds)) []
  if let some (bad, _) := nameds.find? (fun (n, _) => !isCIdent n || names.contains n) then
    throw ("bad or clashing constant name: " ++ bad.quote)
  if P.consts.any (fun c => c.words.isEmpty) then throw "empty constant table"
  let defines := nameds.map (fun (n, v) => "#define " ++ n ++ " " ++ toString v.toNat ++ "u")
  let structs := P.structs.flatMap (fun d => d.toLines ++ [""])
  let consts := P.consts.flatMap (fun c => c.toLines ++ [""])
  let protos := P.fns.map (fun fn => fn.signature ++ ";")
  let fns := P.fns.flatMap (fun fn => "" :: fn.toLines)
  pure ("\n".intercalate
    (["/* Generated by EmbC from a Lean definition. Do not edit. */", ""]
      ++ defines ++ (if defines.isEmpty then [] else [""])
      ++ structs ++ consts ++ protos ++ fns) ++ "\n")

end EmbC
