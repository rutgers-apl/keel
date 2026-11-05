import Lean
import EmbC.Clight.Lowering

/-!
# Access to the lowering's private helpers

`EmbC/Clight/Lowering.lean` keeps its helpers `private`.  The proof needs to
reason about them, so this file registers public *aliases* (name-resolution
synonyms, exactly what `export` creates) pointing at the very same private
constants.  No definition is copied or changed.
-/

open Lean Elab Command in
/-- `expose_private M ns a b c` makes `EmbC.Clight.Priv.a` resolve to the private
declaration `ns.a` of module `M`. -/
elab "expose_private " mod:ident ns:ident ids:ident* : command => do
  for id in ids do
    let base := id.getId
    let priv := (Name.num (`_private ++ mod.getId) 0) ++ (ns.getId ++ base)
    unless (← getEnv).contains priv do throwError "not found {priv}"
    modifyEnv fun env => addAlias env (`EmbC.Clight.Priv ++ base) priv

expose_private EmbC.Clight.Lowering EmbC.Clight
  sequence intType accepts pointerType checkType checkScalar checkName
  LowerContext LowerContext.mk LowerContext.program LowerContext.variables
  LowerContext.result LowerContext.freshPrefix
  LowerState LowerState.mk LowerState.next LowerState.temps
  LowerM
  LowerExpr LowerExpr.mk LowerExpr.sourceType LowerExpr.prelude LowerExpr.expr
  fresh capture lookupVariable requireType requireInteger binop comparison boolExpr
  pointerElement arrayElement fieldType fieldExpr lowerExpr lowerArgs checkArgs
  lowerDestination kernelTypes lowerStmt initializeLocal lowerFunction lowerConstant
