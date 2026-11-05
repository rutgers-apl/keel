import Bcf

open Bcf

/-- Diagnostic replay: like `Bcf.replay` but reports the first failing step. -/
def replayDiag (goal : Nat) (bi : Builtins) (posmap : Std.HashMap Nat Nat) (remap : Array Nat)
    (steps : Array Step) (st : St) : Except String St := Id.run do
  let mut st := st
  let mut k := 0
  let ei := exprIdx posmap remap
  for s in steps do
    let some prems := getFacts st.facts s.premises.toList
      | return .error s!"step {k} {repr s.rule}: bad premise reference"
    let params := s.params.toList
    match applyRule rwTable goal bi ei st s.rule prems params with
    | some (st', f) => st := st'.addFact f
    | none => return .error s!"step {k} {repr s.rule}: rejected"
    k := k + 1
  return .ok st

def checkDiag (p : RawProof) : Except String Nat := do
  let some (st0, tt) := pushNode initSt ⟨.boolVal true, #[]⟩ | throw "builtin true"
  let some (st1, ff) := pushNode st0 ⟨.boolVal false, #[]⟩ | throw "builtin false"
  let some (st2, remap) := canonicalize p.pool st1 | throw "expression pool rejected (ordering or typing)"
  let posmap := positionMap p.pool
  let some gpos := findGoal p.steps | throw "no unique ASSUME"
  let some graw := posmap[gpos]? | throw "goal position"
  let some g := remap[graw]? | throw "goal index"
  let st3 ← replayDiag g ⟨tt, ff⟩ posmap remap p.steps st2
  let some last := st3.facts[st3.facts.size - 1]? | throw "no steps"
  if last = ff then pure graw else throw "last fact is not false"

/-- Report the first raw node that canonicalisation rejects. -/
def diagPool (raw : Pool) : String := Id.run do
  let some (st1, _) := (pushNode initSt ⟨.boolVal true, #[]⟩).bind (fun (st, _) => pushNode st ⟨.boolVal false, #[]⟩)
    | return "builtins"
  let mut acc := (st1, (#[] : Array Nat))
  for i in [0:raw.size] do
    match canonStep raw acc i with
    | some acc' => acc := acc'
    | none =>
      let n := raw[i]!
      let argTys := n.args.toList.map (fun a => (acc.2[a]?).bind (fun c => acc.1.tys[c]?))
      return s!"node {i}: {repr n.op} args={repr n.args} argTys={repr argTys}"
  return "pool ok"

/-- Report why EVALUATE fails on a parameter. -/
def diagEval (st : St) (e : Nat) : String :=
  s!"memo={repr (memoVal st e)} node={repr (st.pool[e]?.map (·.op))} ty={repr st.tys[e]?}"

def runDiag (path : String) : IO Unit := do
  let bytes ← IO.FS.readBinFile path
  match decode bytes with
  | .error e => IO.println s!"DECODE: {e}"
  | .ok p =>
    IO.println (diagPool p.pool)
    -- walk steps, report first failure in detail
    let some (st0, tt) := pushNode initSt ⟨.boolVal true, #[]⟩ | return
    let some (st1, ff) := pushNode st0 ⟨.boolVal false, #[]⟩ | return
    let some (st2, remap) := canonicalize p.pool st1 | return
    let posmap := positionMap p.pool
    let some gpos := findGoal p.steps | IO.println "no goal"; return
    let some graw := posmap[gpos]? | return
    let some g := remap[graw]? | return
    let mut st := st2
    let mut k := 0
    let ei := exprIdx posmap remap
    for s in p.steps do
      let some prems := getFacts st.facts s.premises.toList | IO.println s!"step {k}: bad premise"; return
      let params := s.params.toList
      match applyRule rwTable g ⟨tt, ff⟩ ei st s.rule prems params with
      | some (st', f) => st := st'.addFact f
      | none =>
        IO.println s!"step {k} {repr s.rule}: rejected; prems={repr prems} params={repr params}"
        for q in prems do IO.println s!"  premise node {q}: {repr (st.pool[q]?)}"
        if s.rule = .evaluate then
          for e in (params.filterMap ei) do IO.println s!"  {diagEval st e}"
        if s.rule = .aciNorm then
          for e in (params.filterMap ei) do
            match (st.node e).bind isEqNode with
            | some (a, b) =>
              IO.println s!"  a={a} nf={repr (aciNF st.pool a)} node={repr (st.pool[a]?.map (·.op))}"
              IO.println s!"  b={b} nf={repr (aciNF st.pool b)} node={repr (st.pool[b]?.map (·.op))}"
              IO.println s!"  flatten(a)={repr ((st.pool[a]?).map (fun n => flatten st.pool n.op a))}"
            | none => pure ()
        return
      k := k + 1
    IO.println "all steps ok"

/-- Render a canonical node as an S-expression, to a depth limit. -/
partial def render (pool : Pool) (depth : Nat) (i : Nat) : String :=
  match pool[i]? with
  | none => s!"?{i}"
  | some n =>
    let head := match n.op with
      | .bvVar w id => s!"x{id}:{w}"
      | .bvVal w v => s!"{v}:{w}"
      | .boolVal b => toString b
      | .boolVar id => s!"b{id}"
      | .bvExtract hi lo => s!"extract[{hi}:{lo}]"
      | .bvSignExtend w e => s!"sext{e}→{w}"
      | .bvZeroExtend w e => s!"zext{e}→{w}"
      | .bvRepeat w k => s!"repeat{k}→{w}"
      | .boolBitof k => s!"bit{k}"
      | .bvConcat w => s!"concat:{w}"
      | .bvFromBool => "fromBool"
      | .bvSize w => s!"bvsize:{w}"
      | op => (repr op).pretty.replace "Bcf.Op." ""
    if n.args.isEmpty then head
    else if depth = 0 then s!"({head} …)"
    else s!"({head} {" ".intercalate (n.args.toList.map (render pool (depth - 1)))})"

/-- Print the parameter expressions of every step using `rule`. -/
def dumpRule (rule : Rule) (limit : Nat) (path : String) : IO Unit := do
  let bytes ← IO.FS.readBinFile path
  let .ok p := decode bytes | IO.println "decode failed"
  let some (st0, _) := pushNode initSt ⟨.boolVal true, #[]⟩ | return
  let some (st1, _) := pushNode st0 ⟨.boolVal false, #[]⟩ | return
  let some (st2, remap) := canonicalize p.pool st1 | IO.println "canon failed"
  let posmap := positionMap p.pool
  let mut k := 0
  for s in p.steps do
    if s.rule = rule ∧ k < limit then
      let es := s.params.toList.filterMap (exprIdx posmap remap)
      IO.println s!"{repr rule} params={repr s.params}"
      for e in es do IO.println s!"    {render st2.pool 6 e}"
      k := k + 1

def runFile (path : String) : IO (String × Bool) := do
  let bytes ← IO.FS.readBinFile path
  match decode bytes with
  | .error e => return (s!"DECODE: {e}", false)
  | .ok p =>
    -- the verdict comes from the verified function; the diagnostic replay
    -- only explains a rejection
    match checkBcf p with
    | some _ => return ("ACCEPT", true)
    | none =>
      match checkDiag p with
      | .error e => return (s!"REJECT: {e}", false)
      | .ok _ => return ("REJECT (diagnostic replay found no failing step)", false)

/-- Print every step as it is replayed (to locate slow steps). -/
def runTrace (path : String) : IO Unit := do
  let bytes ← IO.FS.readBinFile path
  match decode bytes with
  | .error e => IO.println s!"DECODE: {e}"
  | .ok p =>
    let some (st0, tt) := pushNode initSt ⟨.boolVal true, #[]⟩ | return
    let some (st1, ff) := pushNode st0 ⟨.boolVal false, #[]⟩ | return
    let some (st2, remap) := canonicalize p.pool st1 | IO.println "pool rejected"; return
    let posmap := positionMap p.pool
    let some gpos := findGoal p.steps | IO.println "no goal"; return
    let some graw := posmap[gpos]? | return
    let some g := remap[graw]? | return
    let mut st := st2
    let mut k := 0
    let ei := exprIdx posmap remap
    let out ← IO.getStdout
    for s in p.steps do
      let some prems := getFacts st.facts s.premises.toList | IO.println s!"step {k}: bad premise"; return
      let params := s.params.toList
      out.putStrLn s!"step {k} {repr s.rule} params={repr params} pool={st.pool.size}"
      out.flush
      match applyRule rwTable g ⟨tt, ff⟩ ei st s.rule prems params with
      | some (st', f) => st := st'.addFact f
      | none => IO.println s!"step {k} {repr s.rule}: rejected"; return
      k := k + 1
    IO.println "all steps ok"

def main (args : List String) : IO UInt32 := do
  if args.head? = some "--trace" then
    for f in args.tail do
      IO.println s!"== {f}"
      runTrace f
    return 0
  if args.head? = some "--dump" then
    -- --dump <rule> <limit> <files...>
    let rule := match args[1]? with
      | some "polyNorm" => Rule.polyNorm | some "rewrite" => Rule.rewrite | some "aciNorm" => Rule.aciNorm
      | some "absorb" => Rule.absorb | some "bitblast" => Rule.bitblast | some "evaluate" => Rule.evaluate
      | _ => Rule.polyNormEq
    let limit := (args[2]?.bind String.toNat?).getD 3
    for f in args.drop 3 do
      IO.println s!"== {f}"
      dumpRule rule limit f
    return 0
  if args.head? = some "--diag" then
    for f in args.tail do
      IO.println s!"== {f}"
      runDiag f
    return 0
  let files := args
  if files.isEmpty then
    IO.println "usage: bcfcheck <proof.bcf>..."
    return 2
  let mut nOk := 0
  let mut nTotal := 0
  for f in files do
    let (msg, ok) ← runFile f
    IO.println s!"{f}: {msg}"
    nTotal := nTotal + 1
    if ok then nOk := nOk + 1
  IO.println s!"accepted {nOk} of {nTotal}"
  return if nOk = nTotal then 0 else 1
