import EmbC.Syntax

/-!
# EmbC: C-like notation for writing programs

Pure convenience.  `c_fn% ...` and `c_struct% ...` expand to ordinary
`Fn` and `StructDef` values; nothing here is trusted, because the theorems
and the printer both work on the expanded value.

```
c_fn% u32 sum(u32 *a, u32 n) {
  u32 i; u32 s;
  while (i < n) { s = s + a[i]; i = i + 1; }
  return s;
}
```

Kernel calls are written as in C: `p = kvcalloc(n, sizeof(u32));`,
`p = kvrealloc(p, array_size(n, sizeof(u32)));`, `p = kzalloc(sizeof(struct s));`,
`kvfree(p);`, `r = copy_from_bpfptr(dst, src, n);` (`n` words; `r` is 0 on
success), `r = signal_pending();`, `cond_resched();`.

Literals: `5` is a `u32`, `5ull` is a `u64`, `NULL` is the null pointer.
`{t}` splices a Lean term of type `Expr`.  An `ALL_CAPS` identifier refers to
a Lean constant of type `Expr`, normally declared with `c_const% NAME := value`,
and prints as a `#define`.  `@tbl[i]` reads a global constant table.
-/

namespace EmbC

declare_syntax_cat cty (behavior := both)
syntax ident : cty
syntax &"struct" ident : cty
syntax cty "*" : cty

declare_syntax_cat cexp
syntax:max ident : cexp
syntax:max num : cexp
syntax:max num &"ull" : cexp
syntax:max "(" cexp ")" : cexp
syntax:max "{" term "}" : cexp
/-- Read of a global constant table: `@tbl[i]`. -/
syntax:max "@" ident "[" cexp "]" : cexp
syntax:max cexp:max "[" cexp "]" : cexp
syntax:max cexp:max "->" ident : cexp
syntax:75 "!" cexp:75 : cexp
syntax:75 "~" cexp:75 : cexp
syntax:75 "(" cty ")" cexp:75 : cexp
syntax:70 cexp:70 " * " cexp:71 : cexp
syntax:70 cexp:70 " / " cexp:71 : cexp
syntax:70 cexp:70 " % " cexp:71 : cexp
syntax:65 cexp:65 " + " cexp:66 : cexp
syntax:65 cexp:65 " - " cexp:66 : cexp
syntax:60 cexp:60 " << " cexp:61 : cexp
syntax:60 cexp:60 " >> " cexp:61 : cexp
syntax:55 cexp:55 " < " cexp:56 : cexp
syntax:55 cexp:55 " <= " cexp:56 : cexp
syntax:55 cexp:55 " > " cexp:56 : cexp
syntax:55 cexp:55 " >= " cexp:56 : cexp
syntax:50 cexp:50 " == " cexp:51 : cexp
syntax:50 cexp:50 " != " cexp:51 : cexp
syntax:45 cexp:45 " & " cexp:46 : cexp
syntax:44 cexp:44 " ^ " cexp:45 : cexp
syntax:43 cexp:43 " | " cexp:44 : cexp
syntax:40 cexp:40 " && " cexp:41 : cexp
syntax:35 cexp:35 " || " cexp:36 : cexp
/-- Pointer offset, written `p +> i` to keep it apart from integer `+`. -/
syntax:65 cexp:65 " +> " cexp:66 : cexp

declare_syntax_cat cstm
syntax cexp " = " cexp ";" : cstm
syntax ident " = " ident "(" cexp,* ")" ";" : cstm
syntax ident "(" cexp,* ")" ";" : cstm
syntax ident " = " &"kvcalloc" "(" cexp "," &"sizeof" "(" cty ")" ")" ";" : cstm
syntax ident " = " &"kzalloc" "(" &"sizeof" "(" cty ")" ")" ";" : cstm
syntax ident " = " &"kvrealloc" "(" cexp "," &"array_size" "(" cexp "," &"sizeof" "(" cty ")" ")" ")" ";" : cstm
syntax "if" "(" cexp ")" "{" cstm* "}" : cstm
syntax "if" "(" cexp ")" "{" cstm* "}" "else" "{" cstm* "}" : cstm
syntax "if" "(" cexp ")" "{" cstm* "}" "else" cstm : cstm
syntax "while" "(" cexp ")" "{" cstm* "}" : cstm
syntax "return" cexp ";" : cstm
syntax "return" ";" : cstm
syntax "break" ";" : cstm

syntax "[cty|" cty "]" : term
syntax "[cexp|" cexp "]" : term
syntax "[cstm|" cstm "]" : term
syntax "[cstms|" cstm* "]" : term

open Lean in
macro_rules
  | `([cty| $x:ident]) =>
    match x.getId with
    | `u32 => `(Ty.u32)
    | `u64 => `(Ty.u64)
    | `bpfptr_t => `(Ty.bpfptr)
    | _ => Macro.throwErrorAt x "unknown C type (expected u32, u64, bpfptr_t, struct S, or a pointer)"
  | `([cty| struct $s:ident]) => `(Ty.struct $(quote s.getId.toString))
  | `([cty| $t:cty *]) => `(Ty.ptr [cty| $t])

open Lean in
macro_rules
  | `([cexp| $x:ident]) =>
    let n := x.getId.toString
    if x.getId == `NULL then `(Expr.null)
    -- an ALL_CAPS name refers to a Lean constant of type `Expr` (a named constant)
    else if n.length > 1 && n.all (fun c => c.isUpper || c.isDigit || c == '_') then `(($x : Expr))
    else `(Expr.var $(quote n))
  | `([cexp| @ $g:ident [ $i:cexp ]]) => `(Expr.cload $(quote g.getId.toString) [cexp| $i])
  | `([cexp| $n:num]) => `(Expr.lit32 $n)
  | `([cexp| $n:num ull]) => `(Expr.lit64 $n)
  | `([cexp| ($e:cexp)]) => `([cexp| $e])
  | `([cexp| {$t:term}]) => `(($t : Expr))
  | `([cexp| $p:cexp [ $i:cexp ]]) => `(Expr.index [cexp| $p] [cexp| $i])
  | `([cexp| $p:cexp -> $f:ident]) => `(Expr.field [cexp| $p] $(quote f.getId.toString))
  | `([cexp| ! $a:cexp]) => `(Expr.lnot [cexp| $a])
  | `([cexp| ~ $a:cexp]) => `(Expr.bnot [cexp| $a])
  | `([cexp| ($t:cty) $a:cexp]) => `(Expr.cast [cty| $t] [cexp| $a])
  | `([cexp| $a:cexp * $b:cexp]) => `(Expr.bin .mul [cexp| $a] [cexp| $b])
  | `([cexp| $a:cexp / $b:cexp]) => `(Expr.bin .div [cexp| $a] [cexp| $b])
  | `([cexp| $a:cexp % $b:cexp]) => `(Expr.bin .mod [cexp| $a] [cexp| $b])
  | `([cexp| $a:cexp + $b:cexp]) => `(Expr.bin .add [cexp| $a] [cexp| $b])
  | `([cexp| $a:cexp - $b:cexp]) => `(Expr.bin .sub [cexp| $a] [cexp| $b])
  | `([cexp| $a:cexp << $b:cexp]) => `(Expr.bin .shl [cexp| $a] [cexp| $b])
  | `([cexp| $a:cexp >> $b:cexp]) => `(Expr.bin .shr [cexp| $a] [cexp| $b])
  | `([cexp| $a:cexp < $b:cexp]) => `(Expr.bin .lt [cexp| $a] [cexp| $b])
  | `([cexp| $a:cexp <= $b:cexp]) => `(Expr.bin .le [cexp| $a] [cexp| $b])
  | `([cexp| $a:cexp > $b:cexp]) => `(Expr.bin .gt [cexp| $a] [cexp| $b])
  | `([cexp| $a:cexp >= $b:cexp]) => `(Expr.bin .ge [cexp| $a] [cexp| $b])
  | `([cexp| $a:cexp == $b:cexp]) => `(Expr.bin .eq [cexp| $a] [cexp| $b])
  | `([cexp| $a:cexp != $b:cexp]) => `(Expr.bin .ne [cexp| $a] [cexp| $b])
  | `([cexp| $a:cexp & $b:cexp]) => `(Expr.bin .band [cexp| $a] [cexp| $b])
  | `([cexp| $a:cexp ^ $b:cexp]) => `(Expr.bin .bxor [cexp| $a] [cexp| $b])
  | `([cexp| $a:cexp | $b:cexp]) => `(Expr.bin .bor [cexp| $a] [cexp| $b])
  | `([cexp| $a:cexp && $b:cexp]) => `(Expr.land [cexp| $a] [cexp| $b])
  | `([cexp| $a:cexp || $b:cexp]) => `(Expr.lor [cexp| $a] [cexp| $b])
  | `([cexp| $a:cexp +> $b:cexp]) => `(Expr.padd [cexp| $a] [cexp| $b])

open Lean in
macro_rules
  | `([cstms| $ss:cstm*]) => do
    let ts ← ss.mapM fun s => `([cstm| $s])
    `(Stmt.block [$ts,*])

open Lean in
macro_rules
  | `([cstm| $lhs:cexp = $e:cexp ;]) =>
    match lhs with
    | `(cexp| $x:ident) => `(Stmt.assign $(quote x.getId.toString) [cexp| $e])
    | `(cexp| $p:cexp [ $i:cexp ]) => `(Stmt.store [cexp| $p] [cexp| $i] [cexp| $e])
    | `(cexp| $p:cexp -> $f:ident) => `(Stmt.setField [cexp| $p] $(quote f.getId.toString) [cexp| $e])
    | _ => Macro.throwErrorAt lhs "cannot assign to this expression"
  | `([cstm| $x:ident = $f:ident ( $args:cexp,* ) ;]) => do
    let as ← args.getElems.mapM fun a => `([cexp| $a])
    if f.getId == `copy_from_bpfptr then
      `(Stmt.ecall (some $(quote x.getId.toString)) Ext.copyFromBpfptr [$as,*])
    else if f.getId == `signal_pending then
      `(Stmt.ecall (some $(quote x.getId.toString)) Ext.signalPending [$as,*])
    else `(Stmt.call (some $(quote x.getId.toString)) $(quote f.getId.toString) [$as,*])
  | `([cstm| $f:ident ( $args:cexp,* ) ;]) => do
    let as ← args.getElems.mapM fun a => `([cexp| $a])
    if f.getId == `kvfree then `(Stmt.ecall none Ext.kvfree [$as,*])
    else if f.getId == `cond_resched then `(Stmt.ecall none Ext.condResched [$as,*])
    else `(Stmt.call none $(quote f.getId.toString) [$as,*])
  | `([cstm| $x:ident = kvcalloc ( $n:cexp , sizeof ( $t:cty ) ) ;]) =>
    `(Stmt.ecall (some $(quote x.getId.toString)) (Ext.kvcalloc [cty| $t]) [[cexp| $n]])
  | `([cstm| $x:ident = kzalloc ( sizeof ( struct $s:ident ) ) ;]) =>
    `(Stmt.ecall (some $(quote x.getId.toString)) (Ext.kzalloc $(quote s.getId.toString)) [])
  | `([cstm| $x:ident = kvrealloc ( $p:cexp , array_size ( $n:cexp , sizeof ( $t:cty ) ) ) ;]) =>
    `(Stmt.ecall (some $(quote x.getId.toString)) (Ext.kvrealloc [cty| $t]) [[cexp| $p], [cexp| $n]])
  | `([cstm| if ( $c:cexp ) { $a:cstm* }]) => `(Stmt.ite [cexp| $c] [cstms| $a*] Stmt.skip)
  | `([cstm| if ( $c:cexp ) { $a:cstm* } else { $b:cstm* }]) =>
    `(Stmt.ite [cexp| $c] [cstms| $a*] [cstms| $b*])
  | `([cstm| if ( $c:cexp ) { $a:cstm* } else $b:cstm]) =>
    `(Stmt.ite [cexp| $c] [cstms| $a*] [cstm| $b])
  | `([cstm| while ( $c:cexp ) { $a:cstm* }]) => `(Stmt.while [cexp| $c] [cstms| $a*])
  | `([cstm| return $e:cexp ;]) => `(Stmt.ret (some [cexp| $e]))
  | `([cstm| return ;]) => `(Stmt.ret none)
  | `([cstm| break ;]) => `(Stmt.brk)

syntax cparam := cty ident
syntax cdecl := atomic(cty ident) ";"
syntax "c_fn% " cty ident "(" cparam,* ")" "{" cdecl* cstm* "}" : term
syntax "c_struct% " ident "{" cdecl* "}" : term

open Lean in
def expandBinders (bs : Array (TSyntax `cty × Ident)) : MacroM (TSyntax `term) := do
  let ts ← bs.mapM fun (t, x) => `(($(quote x.getId.toString), [cty| $t]))
  `([$ts,*])

open Lean in
def splitParam : TSyntax ``cparam → MacroM (TSyntax `cty × Ident)
  | `(cparam| $t:cty $x:ident) => pure (t, x)
  | _ => Macro.throwUnsupported

open Lean in
def splitDecl : TSyntax ``cdecl → MacroM (TSyntax `cty × Ident)
  | `(cdecl| $t:cty $x:ident ;) => pure (t, x)
  | _ => Macro.throwUnsupported

open Lean in
macro_rules
  | `(c_fn% $r:cty $f:ident ( $ps:cparam,* ) { $ds:cdecl* $ss:cstm* }) => do
    let ps ← expandBinders (← ps.getElems.mapM splitParam)
    let ds ← expandBinders (← ds.mapM splitDecl)
    let ret ← match r with
      | `(cty| $x:ident) => if x.getId == `void then `(none) else `(some [cty| $r])
      | _ => `(some [cty| $r])
    `(({ name := $(quote f.getId.toString), params := $ps, ret := $ret, locals := $ds,
         body := [cstms| $ss*] } : Fn))
  | `(c_struct% $s:ident { $ds:cdecl* }) => do
    let ds ← expandBinders (← ds.mapM splitDecl)
    `(({ name := $(quote s.getId.toString), fields := $ds } : StructDef))

/-- `c_const% NAME := 5` declares a named `u32` constant for use in `c_fn%` bodies. -/
macro "c_const% " n:ident " := " v:term : command =>
  `(@[reducible] def $n : Expr := Expr.named $(Lean.quote n.getId.toString) $v)

end EmbC
