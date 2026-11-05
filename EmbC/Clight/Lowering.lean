import EmbC.Clight.Kernel

/-!
# Direct EmbC-to-Clight embedding

This translation builds Clight syntax directly. It does not parse the output
of the C printer. Parameters and source locals are Clight temporaries, using
`CC.FunctionEntry2`; locals receive the same initial values as `initLocals`.
Short-circuit expressions introduce fresh temporaries and conditional
statements, including inside loop conditions. Kernel calls use the abstract
wrappers described in `EmbC.Clight.Kernel`.
-/

namespace EmbC.Clight

private def sequence (a b : CC.Stmt) : CC.Stmt :=
  match a, b with
  | .Sskip, _ => b
  | _, .Sskip => a
  | _, _ => .Ssequence a b

private def intType : Ty → Bool
  | .u32 | .u64 => true
  | _ => false

private def accepts (expected : Ty) (actual : Option Ty) : Bool :=
  match actual, expected with
  | none, .ptr _ => true
  | some t, _ => t == expected
  | _, _ => false

private def pointerType : Option Ty → Bool
  | none | some (.ptr _) => true
  | _ => false

private def checkType (P : Prog) : Ty → Except String Unit
  | .struct s =>
    if (P.findStruct s).isSome then pure () else throw s!"unknown struct {s}"
  | .ptr t => checkType P t
  | _ => pure ()

private def checkScalar (P : Prog) (t : Ty) : Except String Unit := do
  checkType P t
  if t.isStruct then throw "struct values must occur behind pointers"

/-- Clean encodes characters as bytes, so accept ASCII C identifiers only. -/
private def checkName (s : String) : Except String Unit := do
  let valid := match s.toList with
    | [] => false
    | c :: cs => c.toNat < 128 && (c.isAlpha || c == '_') &&
      cs.all (fun c => c.toNat < 128 && (c.isAlphanum || c == '_'))
  if !valid then throw s!"not an ASCII C identifier: {s}"

private structure LowerContext where
  program : Prog
  variables : List (Var × Ty)
  result : Option Ty
  freshPrefix : String

private structure LowerState where
  next : Nat := 0
  temps : List (CC.Ident × CC.Ty) := []

private abbrev LowerM := StateT LowerState (Except String)

/-- A missing source type records the polymorphic null literal. -/
private structure LowerExpr where
  sourceType : Option Ty
  prelude : CC.Stmt := .Sskip
  expr : CC.Expr

private def fresh (ctx : LowerContext) (t : CC.Ty) : LowerM CC.Ident := do
  let st : LowerState ← get
  let id := CC.identOfString (ctx.freshPrefix ++ toString st.next)
  set ({ next := st.next + 1, temps := st.temps ++ [(id, t)] } : LowerState)
  pure id

/-- Force evaluation before lowering the next operand or argument. -/
private def capture (ctx : LowerContext) (e : LowerExpr) : LowerM LowerExpr := do
  let id ← fresh ctx (CC.typeof e.expr)
  pure { e with prelude := sequence e.prelude (.Sset id e.expr),
                expr := .Etempvar id (CC.typeof e.expr) }

private def lookupVariable (ctx : LowerContext) (x : Var) : LowerM Ty := do
  match ctx.variables.find? (·.1 == x) with
  | none => throw s!"unknown local variable {x}"
  | some (_, t) => pure t

private def requireType (expected : Ty) (e : LowerExpr) : LowerM Unit := do
  if !accepts expected e.sourceType then throw "expression type does not match declaration"

private def requireInteger (e : LowerExpr) : LowerM Unit := do
  if !(e.sourceType.any intType) then throw "an unsigned integer expression is required"

private def binop : EmbC.BinOp → CC.Binop
  | .add => .Oadd | .sub => .Osub | .mul => .Omul
  | .div => .Odiv | .mod => .Omod
  | .band => .Oand | .bor => .Oor | .bxor => .Oxor
  | .shl => .Oshl | .shr => .Oshr
  | .eq => .Oeq | .ne => .One | .lt => .Olt
  | .le => .Ole | .gt => .Ogt | .ge => .Oge

private def comparison : EmbC.BinOp → Bool
  | .eq | .ne | .lt | .le | .gt | .ge => true
  | _ => false

private def boolExpr (e : CC.Expr) : CC.Expr :=
  .Ecast (.Ebinop .One e (.Econst_int 0 CC.tuint) CC.tint) CC.tuint

private def pointerElement (e : LowerExpr) : LowerM Ty := do
  match e.sourceType with
  | some (.ptr t) => pure t
  | _ => throw "a typed pointer expression is required"

private def arrayElement (e : LowerExpr) : LowerM Ty := do
  let t ← pointerElement e
  if t.isStruct then throw "struct pointers do not support array indexing or offsets"
  pure t

private def fieldType (ctx : LowerContext) (p : LowerExpr) (f : String) : LowerM Ty := do
  match ← pointerElement p with
  | .struct s =>
    match ctx.program.findStruct s with
    | none => throw s!"unknown struct {s}"
    | some d =>
      match d.field? f with
      | none => throw s!"unknown field {s}.{f}"
      | some (_, t) => pure t
  | _ => throw "field access requires a pointer to a struct"

private def fieldExpr (p : LowerExpr) (f : String) (t : Ty) : CC.Expr :=
  match p.sourceType with
  | some (.ptr elem) =>
    .Efield (.Ederef p.expr (type elem)) (CC.identOfString f) (type t)
  | _ => p.expr -- Rejected by `fieldType` before this helper is called.

private def lowerExpr (ctx : LowerContext) : EmbC.Expr → LowerM LowerExpr
  | .var x => do
    let t ← lookupVariable ctx x
    pure { sourceType := some t, expr := .Etempvar (CC.identOfString x) (type t) }
  | .lit32 v | .named _ v =>
    pure { sourceType := some .u32, expr := .Econst_int v CC.tuint }
  | .lit64 v => pure { sourceType := some .u64, expr := .Econst_long v CC.tulong }
  | .null => pure { sourceType := none, expr := .Ecast (.Econst_long 0 CC.tulong) (CC.tptr .Tvoid) }
  | .cload g i => do
    let c ← match ctx.program.findConst g with
      | none => throw s!"unknown constant table {g}"
      | some c => pure c
    let i ← lowerExpr ctx i >>= capture ctx
    requireInteger i
    let a := CC.Expr.Evar (CC.identOfString g) (CC.tarray CC.tuint c.words.size)
    pure { sourceType := some .u32, prelude := i.prelude,
           expr := .Ederef (.Ebinop .Oadd a i.expr (CC.tptr CC.tuint)) CC.tuint }
  | .bin op a b => do
    let a ← lowerExpr ctx a >>= capture ctx
    let b ← lowerExpr ctx b >>= capture ctx
    let isInt := a.sourceType.any intType && a.sourceType == b.sourceType
    let isPtr := (op == .eq || op == .ne) && pointerType a.sourceType && pointerType b.sourceType
    if !(isInt || isPtr) then throw "binary operands must have matching integer types or support pointer equality"
    let prelude := sequence a.prelude b.prelude
    if comparison op then
      pure { sourceType := some .u32, prelude,
             expr := .Ecast (.Ebinop (binop op) a.expr b.expr CC.tint) CC.tuint }
    else
      pure { sourceType := a.sourceType, prelude,
             expr := .Ebinop (binop op) a.expr b.expr (CC.typeof a.expr) }
  | .lnot a => do
    let a ← lowerExpr ctx a
    requireType .u32 a
    pure { sourceType := some .u32, prelude := a.prelude,
           expr := .Ecast (.Eunop .Onotbool a.expr CC.tint) CC.tuint }
  | .bnot a => do
    let a ← lowerExpr ctx a
    requireInteger a
    pure { a with expr := .Eunop .Onotint a.expr (CC.typeof a.expr) }
  | .land a b => do
    let a ← lowerExpr ctx a >>= capture ctx
    requireType .u32 a
    let b ← lowerExpr ctx b
    requireType .u32 b
    let id ← fresh ctx CC.tuint
    pure { sourceType := some .u32,
           prelude := sequence a.prelude (.Sifthenelse a.expr
             (sequence b.prelude (.Sset id (boolExpr b.expr))) (.Sset id (.Econst_int 0 CC.tuint))),
           expr := .Etempvar id CC.tuint }
  | .lor a b => do
    let a ← lowerExpr ctx a >>= capture ctx
    requireType .u32 a
    let b ← lowerExpr ctx b
    requireType .u32 b
    let id ← fresh ctx CC.tuint
    pure { sourceType := some .u32,
           prelude := sequence a.prelude (.Sifthenelse a.expr
             (.Sset id (.Econst_int 1 CC.tuint)) (sequence b.prelude (.Sset id (boolExpr b.expr)))),
           expr := .Etempvar id CC.tuint }
  | .cast t a => do
    let a ← lowerExpr ctx a
    requireInteger a
    if !intType t then throw "only u32/u64 integer casts are supported"
    pure { sourceType := some t, prelude := a.prelude, expr := .Ecast a.expr (type t) }
  | .index p i => do
    let p ← lowerExpr ctx p >>= capture ctx
    let t ← arrayElement p
    let i ← lowerExpr ctx i >>= capture ctx
    requireInteger i
    pure { sourceType := some t, prelude := sequence p.prelude i.prelude,
           expr := .Ederef (.Ebinop .Oadd p.expr i.expr (type (.ptr t))) (type t) }
  | .field p f => do
    let p ← lowerExpr ctx p
    let t ← fieldType ctx p f
    pure { sourceType := some t, prelude := p.prelude, expr := fieldExpr p f t }
  | .padd p i => do
    let p ← lowerExpr ctx p >>= capture ctx
    let t ← arrayElement p
    let i ← lowerExpr ctx i >>= capture ctx
    requireInteger i
    pure { sourceType := some (.ptr t), prelude := sequence p.prelude i.prelude,
           expr := .Ebinop .Oadd p.expr i.expr (type (.ptr t)) }

private def lowerArgs (ctx : LowerContext) : List EmbC.Expr → LowerM (CC.Stmt × List LowerExpr)
  | [] => pure (.Sskip, [])
  | e :: es => do
    let e ← lowerExpr ctx e >>= capture ctx
    let (prelude, es) ← lowerArgs ctx es
    pure (sequence e.prelude prelude, e :: es)

private def checkArgs : List Ty → List LowerExpr → LowerM Unit
  | [], [] => pure ()
  | t :: ts, a :: args => do requireType t a; checkArgs ts args
  | _, _ => throw "call argument count does not match signature"

private def lowerDestination (ctx : LowerContext) (dst : Option Var)
    (ret : Option Ty) : LowerM (Option CC.Ident) := do
  match dst with
  | none => pure none
  | some x =>
    let t ← lookupVariable ctx x
    if ret != some t then throw s!"call result does not match destination {x}"
    pure (some (CC.identOfString x))

private def kernelTypes (ctx : LowerContext) (ext : Ext)
    (args : List LowerExpr) : LowerM (List CC.Ty × Option Ty) := do
  match ext with
  | .kvcalloc t =>
    checkScalar ctx.program t
    checkArgs [.u64] args
    pure ([CC.tulong], some (.ptr t))
  | .kzalloc s =>
    checkType ctx.program (.struct s)
    checkArgs [] args
    pure ([], some (.ptr (.struct s)))
  | .kvrealloc t =>
    checkScalar ctx.program t
    checkArgs [.ptr t, .u64] args
    pure ([type (.ptr t), CC.tulong], some (.ptr t))
  | .kvfree =>
    match args with
    | [p] =>
      if !pointerType p.sourceType then throw "kvfree requires a pointer"
      pure ([CC.tptr .Tvoid], none)
    | _ => throw "kvfree requires one argument"
  | .copyFromBpfptr =>
    checkArgs [.ptr .u32, .bpfptr, .u64] args
    pure ([type (.ptr .u32), type .bpfptr, CC.tulong], some .u32)
  | .signalPending =>
    checkArgs [] args
    pure ([], some .u32)
  | .condResched =>
    checkArgs [] args
    pure ([], none)

private def lowerStmt (ctx : LowerContext) (loopDepth : Nat) : EmbC.Stmt → LowerM CC.Stmt
  | .skip => pure .Sskip
  | .assign x e => do
    let t ← lookupVariable ctx x
    let e ← lowerExpr ctx e
    requireType t e
    pure (sequence e.prelude (.Sset (CC.identOfString x) e.expr))
  | .store p i e => do
    let p ← lowerExpr ctx p >>= capture ctx
    let t ← arrayElement p
    let i ← lowerExpr ctx i >>= capture ctx
    requireInteger i
    let e ← lowerExpr ctx e
    requireType t e
    let lhs := CC.Expr.Ederef (.Ebinop .Oadd p.expr i.expr (type (.ptr t))) (type t)
    pure (sequence p.prelude (sequence i.prelude (sequence e.prelude (.Sassign lhs e.expr))))
  | .setField p f e => do
    let p ← lowerExpr ctx p >>= capture ctx
    let t ← fieldType ctx p f
    let e ← lowerExpr ctx e
    requireType t e
    pure (sequence p.prelude (sequence e.prelude (.Sassign (fieldExpr p f t) e.expr)))
  | .seq a b => do
    let a ← lowerStmt ctx loopDepth a
    let b ← lowerStmt ctx loopDepth b
    pure (sequence a b)
  | .ite c a b => do
    let c ← lowerExpr ctx c
    requireType .u32 c
    let a ← lowerStmt ctx loopDepth a
    let b ← lowerStmt ctx loopDepth b
    pure (sequence c.prelude (.Sifthenelse c.expr a b))
  | .while c body => do
    let c ← lowerExpr ctx c
    requireType .u32 c
    let body ← lowerStmt ctx (loopDepth + 1) body
    pure (.Sloop (sequence c.prelude
      (.Ssequence (.Sifthenelse c.expr .Sskip .Sbreak) body)) .Sskip)
  | .call dst f args => do
    let fn ← match ctx.program.findFn f with
      | none => throw s!"unknown function {f}"
      | some fn => pure fn
    let (prelude, args) ← lowerArgs ctx args
    checkArgs (fn.params.map (·.2)) args
    let dst ← lowerDestination ctx dst fn.ret
    let fty := CC.Ty.Tfunction (fn.params.map (fun p => type p.2))
      (fn.ret.map type |>.getD .Tvoid) CC.cc_default
    pure (sequence prelude (.Scall dst (.Evar (CC.identOfString f) fty) (args.map (·.expr))))
  | .ecall dst ext args => do
    let (prelude, args) ← lowerArgs ctx args
    let (types, ret) ← kernelTypes ctx ext args
    let dst ← lowerDestination ctx dst ret
    pure (sequence prelude (.Sbuiltin dst (kernelExternal ext) types (args.map (·.expr))))
  | .ret none => do
    if ctx.result.isSome then throw "non-void function returns without a value"
    pure (.Sreturn none)
  | .ret (some e) => do
    let t ← match ctx.result with
      | none => throw "void function returns a value"
      | some t => pure t
    let e ← lowerExpr ctx e
    requireType t e
    pure (sequence e.prelude (.Sreturn (some e.expr)))
  | .brk => do
    if loopDepth == 0 then throw "break occurs outside a loop"
    pure .Sbreak

private def initializeLocal (x : Var) : Ty → CC.Stmt
  | .u32 => .Sset (CC.identOfString x) (.Econst_int 0 CC.tuint)
  | .u64 => .Sset (CC.identOfString x) (.Econst_long 0 CC.tulong)
  | .ptr t => .Sset (CC.identOfString x) (.Ecast (.Econst_long 0 CC.tulong) (type (.ptr t)))
  | _ => .Sskip -- Opaque handles start undefined, as in `Ty.zero`.

private def lowerFunction (P : Prog) (fn : Fn) : Except String CC.Function := do
  let declarations := fn.params ++ fn.locals
  if !(declarations.map (·.1)).Nodup then throw s!"duplicate variable in {fn.name}"
  for (x, t) in declarations do
    checkName x
    checkScalar P t
  for t in fn.ret.toList do checkScalar P t
  let longest := declarations.foldl (fun n d => max n d.1.length) 0
  let ctx : LowerContext :=
    { program := P, variables := declarations, result := fn.ret,
      freshPrefix := String.ofList (List.replicate (longest + 1) '_') }
  let (body, st) ← (lowerStmt ctx 0 fn.body).run {}
  let initialization := fn.locals.foldr (fun (x, t) rest => sequence (initializeLocal x t) rest) .Sskip
  pure { fn_return := (fn.ret.map type).getD .Tvoid, fn_callconv := CC.cc_default,
         fn_params := fn.params.map fun (x, t) => (CC.identOfString x, type t),
         fn_vars := [], fn_temps := (fn.locals.map fun (x, t) => (CC.identOfString x, type t)) ++ st.temps,
         fn_body := sequence initialization body }

private def lowerConstant (c : ConstDef) : CC.Ident × CC.GlobDef CC.FunDef CC.Ty :=
  (CC.identOfString c.name, .Gvar
    { gvar_info := CC.tarray CC.tuint c.words.size,
      gvar_init := c.words.toList.map CC.InitData.Init_int32,
      gvar_readonly := true, gvar_volatile := false })

/-- Fixed syntax-directed embedding, rejecting invalid declarations and types.
`prog_main` records the first source function; the refinement statement uses
function-call initial states rather than Clight's special C `main` signature. -/
def lowerProgram (P : Prog) : Except String CC.Program := do
  if !(P.structs.map (·.name)).Nodup then throw "duplicate struct name"
  if !((P.fns.map (·.name)) ++ P.consts.map (·.name)).Nodup then throw "duplicate global name"
  for d in P.structs do
    checkName d.name
    if !(d.fields.map (·.1)).Nodup then throw s!"duplicate field in {d.name}"
    for (f, t) in d.fields do
      checkName f
      checkScalar P t
  for fn in P.fns do checkName fn.name
  for c in P.consts do checkName c.name
  if !(CC.buildCompositeEnv (composites P)).isOK then throw "invalid Clight composite layout"
  let main ← match P.fns with
    | [] => throw "a program must declare at least one function"
    | fn :: _ => pure (CC.identOfString fn.name)
  let functions ← P.fns.mapM fun fn => do
    let f ← lowerFunction P fn
    pure (CC.identOfString fn.name, CC.GlobDef.Gfun (CC.FunDef.Internal f))
  pure (CC.mkprogram (composites P) (functions ++ P.consts.map lowerConstant)
    (P.fns.map fun fn => CC.identOfString fn.name) main)

end EmbC.Clight

namespace EmbC

/-- The specific Clight AST corresponding to this EmbC program. -/
def Prog.toClight (P : Prog) : Except String CC.Program := Clight.lowerProgram P

end EmbC
