import Bcf
import Vbcf.Enc
open Bcf

mutual
def varsE : RwExpr → List Nat
  | .var i => [i]
  | .tt => [] | .ff => [] | .lit _ => []
  | .symVal a b => varsE a ++ varsE b
  | .bvmax a => varsE a
  | .app _ as => varsA as
  | .ite a b c => varsE a ++ varsE b ++ varsE c
  | .extract a b c => varsE a ++ varsE b ++ varsE c
  | .zext a b => varsE a ++ varsE b
  | .sext a b => varsE a ++ varsE b
  | .repeat a b => varsE a ++ varsE b
def varsA : RwArgs → List Nat
  | .nil => []
  | .cons a r => varsE a ++ varsA r
end

def argsList : RwArgs → List RwExpr
  | .nil => []
  | .cons a r => a :: argsList r

def conjuncts : RwExpr → List RwExpr
  | .app .conj as => argsList as
  | e => [e]

/-- equations `V k = e` usable to determine `V k`. -/
def eqnOf : RwExpr → Option (Nat × RwExpr)
  | .app .eq (.cons (.var k) (.cons e .nil)) => if (varsE e).contains k then none else some (k, e)
  | _ => none

def push! (st : St) (n : Node) : St × Nat :=
  match pushNode st n with
  | some r => r
  | none => panic! s!"push failed {repr n.op}"

structure Atoms where
  st : St
  anyC : Array Nat
  boolC : Array Nat
  bv1C : Array Nat
  bvqC : Array Nat
  boolsC : Array Nat
  bvqsC : Array Nat
  goal : Nat

def mkAtoms : Atoms := Id.run do
  let (st, _) := push! initSt ⟨.boolVal true, #[]⟩
  let (st, _) := push! st ⟨.boolVal false, #[]⟩
  let (st, p) := push! st ⟨.boolVar 100, #[]⟩
  let (st, q) := push! st ⟨.boolVar 101, #[]⟩
  let (st, r) := push! st ⟨.boolVar 102, #[]⟩
  let (st, x8) := push! st ⟨.bvVar 8 103, #[]⟩
  let (st, y8) := push! st ⟨.bvVar 8 104, #[]⟩
  let (st, z8) := push! st ⟨.bvVar 8 105, #[]⟩
  let (st, a1) := push! st ⟨.bvVar 1 106, #[]⟩
  let (st, b1) := push! st ⟨.bvVar 1 107, #[]⟩
  let (st, x16) := push! st ⟨.bvVar 16 108, #[]⟩
  let (st, y16) := push! st ⟨.bvVar 16 109, #[]⟩
  let (st, x24) := push! st ⟨.bvVar 24 110, #[]⟩
  let (st, x32) := push! st ⟨.bvVar 32 111, #[]⟩
  let (st, c5) := push! st ⟨.bvVal 8 5, #[]⟩
  let (st, c9) := push! st ⟨.bvVal 8 9, #[]⟩
  let (st, k10) := push! st ⟨.bvVal 1 0, #[]⟩
  let (st, k11) := push! st ⟨.bvVal 1 1, #[]⟩
  let (st, lpq) := push! st ⟨.listVal true, #[p, q]⟩
  let (st, lp) := push! st ⟨.listVal true, #[r]⟩
  let (st, le) := push! st ⟨.listVal true, #[]⟩
  let (st, lxy) := push! st ⟨.listVal false, #[x8, y8]⟩
  let (st, lx) := push! st ⟨.listVal false, #[z8]⟩
  let (st, lx16) := push! st ⟨.listVal false, #[x16]⟩
  let (st, lxy16) := push! st ⟨.listVal false, #[y16, x16]⟩
  let (st, lx24) := push! st ⟨.listVal false, #[x24]⟩
  let (st, lbe) := push! st ⟨.listVal false, #[]⟩
  let (st, y32) := push! st ⟨.bvVar 32 112, #[]⟩
  let (st, lx32) := push! st ⟨.listVal false, #[x32]⟩
  let (st, lxy32) := push! st ⟨.listVal false, #[y32, x32]⟩
  return { st, goal := p
           anyC := #[p, q, x8, y8, 0, 1, c5, c9, r, z8, x16]
           boolC := #[p, q, r, 0, 1]
           bv1C := #[a1, b1, k10, k11]
           bvqC := #[x8, y8, z8, x16, y16, a1, b1, c5, c9, x24, x32, k11, x8, x16, y32]
           boolsC := #[lpq, lp, le]
           bvqsC := #[lxy, lx, lx16, lxy16, lx24, lbe, lbe, lx32, lxy32] }

def dom32 : Array Nat := #[0,1,2,3,4,5,6,7,8,9,15,16,23,24,31,32,200,0xff00,0xffff,0x80,0,1,2,3,7,8,15,16,0xffffffff,64,255,256]

/-- Values for the rules whose condition needs `n = 2^size - 2^exponent` (158, 159),
which `dom32` hits too rarely. -/
def domPow2 : Array Nat := #[7, 8, 0x80, 16, 0xff00, 0xc0, 6, 0xfff0, 4, 12]

def nextRng (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % (2 ^ 64)
def pick (s : Nat) (a : Array Nat) : Nat := a[(s / 65536) % a.size]!

inductive Cat where | accept | guardfail | fail
  deriving DecidableEq, Repr

structure Inst where
  st : St            -- state with atoms, literal args and cond nodes
  args : List Nat
  conds : List Nat   -- nodes to EVALUATE as premises
  cat : Cat

def bi : Builtins := ⟨0, 1⟩

/-- One random trial. -/
def trial (A : Atoms) (r : RwRule) (seed : Nat) (dom : Array Nat := dom32) : Option Inst × Nat := Id.run do
  let mut s := seed
  let np := r.params.length
  let eqns := match r.cond with
    | some c => (conjuncts c).filterMap eqnOf
    | none => []
  let det := eqns.map (·.1)
  let mut st := A.st
  let mut args : Array (Option Nat) := Array.replicate np none
  let mut k := 0
  for t in r.params do
    if !det.contains k then
      s := nextRng s
      match t with
      | .any => args := args.set! k (some (pick s A.anyC))
      | .bool => args := args.set! k (some (pick s A.boolC))
      | .bv 1 => args := args.set! k (some (pick s A.bv1C))
      | .bv w =>
        let v := pick s dom
        let (st', i) := push! st ⟨.bvVal w (v % 2 ^ w), #[]⟩
        st := st'
        args := args.set! k (some i)
      | .bvq => args := args.set! k (some (pick s A.bvqC))
      | .bools => args := args.set! k (some (pick s A.boolsC))
      | .bvqs => args := args.set! k (some (pick s A.bvqsC))
    k := k + 1
  -- solve determined parameters
  for _ in [0:np] do
    for (kk, e) in eqns do
      if args[kk]! = none ∧ (varsE e).all (fun v => (args[v]?.bind id).isSome) then
        let cur := args.map (·.getD 0)
        match instE bi cur e st with
        | none => return (none, s)
        | some (tmp, i) =>
          match cval tmp i with
          | some (.bv w v) =>
            match pushNode st ⟨.bvVal w v.toNat, #[]⟩ with
            | some (st', l) => st := st'; args := args.set! kk (some l)
            | none => return (none, s)
          | some (.bool b) => args := args.set! kk (some (if b then 0 else 1))
          | _ => return (none, s)
  if args.any (·.isNone) then return (none, s)
  let al := args.toList.map (·.getD 0)
  let aa := al.toArray
  let pok := paramsOK st r.params al
  -- condition nodes
  let (st2, conds, condOK) : St × List Nat × Bool :=
    match r.cond with
    | none => (st, [], true)
    | some c =>
      if !pok then (st, [], false) else
      match instE bi aa c st with
      | none => (st, [], false)
      | some (st1, ci) =>
        let cs := match st1.node ci with
          | some ⟨.conj, cs⟩ => cs.toList
          | _ => [ci]
        (st1, cs, cs.all (fun c => match cval st1 c with | some (.bool true) => true | _ => false))
  if !condOK then return (none, s)
  let gOK := pok
  let concl := pok && (match r.cond with
    | none => (rwConclude bi aa r st2).isSome
    | some _ => (rwConclude bi aa r st2).isSome)
  let cat := if pok && gOK && concl then Cat.accept else if pok && concl && !gOK then Cat.guardfail else Cat.fail
  return (some ⟨st2, al, conds, cat⟩, s)

def nodeFileWords (pos : Nat → Nat) (n : Node) : List Nat :=
  let (code, params) := Vbcf.opCode n.op
  let tail : List Nat := match n.op with
    | .bvVar _ _ => []
    | .boolVar _ => []
    | .boolVal _ => []
    | .bvVal w v => if w ≤ 32 then [v % 2 ^ 32] else [v % 2 ^ 32, v / 2 ^ 32]
    | _ => n.args.toList.map pos
  (code ||| (tail.length <<< 8) ||| (params <<< 16)) :: tail

def stepWords (rule : Nat) (prems params : List Nat) : List Nat :=
  (rule ||| (prems.length <<< 16) ||| (params.length <<< 24)) :: (prems ++ params)

def toBytes (ws : List Nat) : ByteArray := Id.run do
  let mut b := ByteArray.empty
  for w in ws do
    b := b.push (UInt8.ofNat (w % 256))
    b := b.push (UInt8.ofNat ((w / 256) % 256))
    b := b.push (UInt8.ofNat ((w / 65536) % 256))
    b := b.push (UInt8.ofNat ((w / 16777216) % 256))
  return b

/-- variant: 0 = as is; 1 = drop last premise; 2 = reverse premises; 3 = drop last arg;
4 = swap first two args; 5 = extra premise (the assumption); 6 = first premise replaced by the assumption -/
def fileWords (goal : Nat) (rid : Nat) (I : Inst) (variant : Nat) : List Nat := Id.run do
  let mut posOf : Array Nat := #[]
  let mut pos := 0
  let mut ex : List Nat := []
  for n in I.st.pool do
    let ws := nodeFileWords (fun i => posOf[i]!) n
    posOf := posOf.push pos
    pos := pos + ws.length
    ex := ex ++ ws
  let mut steps := stepWords 1 [] [posOf[goal]!]
  let mut prems : List Nat := []
  let mut k := 1
  for c in I.conds do
    steps := steps ++ stepWords 2 [] [posOf[c]!]
    prems := prems ++ [k]
    k := k + 1
  let mut args := I.args.map (fun a => posOf[a]!)
  if variant = 1 then prems := prems.dropLast
  if variant = 2 then prems := prems.reverse
  if variant = 3 then args := args.dropLast
  if variant = 4 then
    match args with
    | a :: b :: rest => args := b :: a :: rest
    | _ => pure ()
  if variant = 5 then prems := prems ++ [0]
  if variant = 6 then
    match prems with
    | _ :: rest => prems := 0 :: rest
    | [] => pure ()
  steps := steps ++ stepWords 6 prems (rid :: args)
  return [0x0BCF, ex.length, steps.length] ++ ex ++ steps

def main (argv : List String) : IO Unit := do
  let dir := argv[0]!
  let maxTrials := (argv[1]?.bind String.toNat?).getD 20000
  let A := mkAtoms
  let mut summary := ""
  for rid in [1:166] do
    match rwTable rid with
    | none => pure ()
    | some r =>
      let mut s := 12345 + rid * 7919
      let mut acc : List Inst := []
      let mut gf : List Inst := []
      let mut fl : List Inst := []
      let mut seen : List (List Nat) := []
      let mut t := 0
      while t < maxTrials ∧ acc.length < 4 do
        let (res, s') := trial A r s (if rid == 158 || rid == 159 then domPow2 else dom32)
        s := s'
        t := t + 1
        match res with
        | none => pure ()
        | some I =>
          -- argument ids depend on the per-trial literals; compare by rendered nodes instead
          let key := I.args.map (fun a => match I.st.pool[a]? with
            | some ⟨.bvVal w v, _⟩ => 1000000 + w * 100000 + v
            | _ => a)
          if !seen.contains key then
            seen := key :: seen
            match I.cat with
            | .accept => acc := I :: acc
            | .guardfail => if gf.length < 3 then gf := I :: gf
            | .fail => if fl.length < 2 then fl := I :: fl
      let mut n := 0
      for I in acc do
        for v in [0, 1, 2, 3, 4, 5, 6] do
          if v = 0 ∨ (v = 1 ∧ I.conds.length ≥ 1) ∨ (v = 2 ∧ I.conds.length ≥ 2) ∨ v = 3
             ∨ (v = 4 ∧ I.args.length ≥ 2) ∨ v = 5 ∨ (v = 6 ∧ I.conds.length ≥ 1) then
            IO.FS.writeBinFile s!"{dir}/rw{rid}_a{n}_v{v}.bcf" (toBytes (fileWords A.goal rid I v))
        n := n + 1
      n := 0
      for I in gf do
        IO.FS.writeBinFile s!"{dir}/rw{rid}_g{n}_v0.bcf" (toBytes (fileWords A.goal rid I 0))
        n := n + 1
      n := 0
      for I in fl do
        IO.FS.writeBinFile s!"{dir}/rw{rid}_f{n}_v0.bcf" (toBytes (fileWords A.goal rid I 0))
        n := n + 1
      summary := summary ++ s!"{rid} accept={acc.length} guardfail={gf.length} fail={fl.length} trials={t}\n"
      IO.println s!"{rid} accept={acc.length} guardfail={gf.length} fail={fl.length} trials={t}"
  IO.FS.writeFile s!"{dir}/SUMMARY.txt" summary
