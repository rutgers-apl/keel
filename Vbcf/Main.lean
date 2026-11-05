import Bcf
import EmbC.Print
import EmbC.Semantics
import EmbC.Testing.Kernel
import EmbC.Cost
import Vbcf.Prog
import Vbcf.Enc

/-!
# `vbcf`: driver for the EmbC checker

* `vbcf print` writes the checker as C.
* `vbcf run <file.bcf> [-g <arena> <goal>]` runs it in the EmbC interpreter
  (slow; for testing that the printed C and the semantics agree), with the
  verifier's goal read from the word file `<arena>`, or with no goal.
* `vbcf cost <file.bcf>` runs it with the cost model (`EmbC/Cost.lean`) and
  prints the verdict, the cost (machine transitions plus words allocated or
  copied by kernel calls) and the input size in words.
* `vbcf trace <file.bcf>` replays the proof with the *Lean* checker and
  writes, in the C pool's encoding, every node it creates and every fact it
  concludes.  `Vbcf/c/trace_test.c` compares the C checker against it.
-/

open EmbC

def readWords (path : String) : IO (Array (BitVec 32)) := do
  let b ← IO.FS.readBinFile path
  let n := b.size / 4
  let mut ws : Array (BitVec 32) := Array.mkEmpty n
  for i in [0:n] do
    ws := ws.push (BitVec.ofNat 32 (Bcf.u32At b (4 * i)))
  pure ws

/-- Run `vbcf_check_proof` in the interpreter.  `goal` is the verifier's
arena (placed in block 0) and the goal's position in it, or `none` for a
`NULL` arena. Fault indices number allocation, copy, and signal invocations,
starting at zero. The world holds the actual caller buffer separately from
these counters. The arena block is not counted as live. -/
def runInterp (path : String) (goal : Option (Array (BitVec 32) × Nat)) (fails : List Nat) :
    IO String := do
  let ws ← readWords path
  let world : Testing.World := { input := ws, failingCalls := fails }
  let size := (← IO.FS.readBinFile path).size
  let (m0, gx, g, arenaBlocks) : Mem × Val × Nat × Nat := match goal with
    | none => (Mem.empty, .null, 0, 0)
    | some (aw, g) => (⟨#[some ⟨.u32, aw.map Val.u32⟩]⟩, .ptr 0 0, g, 1)
  match Vbcf.prog.run (2 ^ 62) "vbcf_check_proof"
      [gx, .u32 (BitVec.ofNat 32 g), .uptr, .u32 (BitVec.ofNat 32 size)] ⟨m0, Testing.oracle Vbcf.prog world⟩ with
  | .timeout => pure "timeout"
  | .stuck => pure "stuck"
  | .ok (some (.u32 v), st) =>
    let live := (st.mem.blocks.toList.filter Option.isSome).length - arenaBlocks
    pure s!"{v.toNat} live={live}"
  | .ok _ => pure "bad result"

/-- Run `vbcf_check_proof` with the cost model, with no goal and no failing
allocation: the verdict, the cost and the number of input words. -/
def runCost (path : String) : IO String := do
  let ws ← readWords path
  let n := ws.size
  let world : Testing.World := { input := ws }
  let size := (← IO.FS.readBinFile path).size
  match Vbcf.prog.runC (2 ^ 62) "vbcf_check_proof"
      [.null, .u32 0, .uptr, .u32 (BitVec.ofNat 32 size)] ⟨Mem.empty, Testing.oracle Vbcf.prog world⟩ with
  | .timeout => pure "timeout"
  | .stuck => pure "stuck"
  | .ok (some (.u32 v), _, c) => pure s!"{v.toNat} cost={c.t} alloc={c.m} words={n}"
  | .ok _ => pure "bad result"

/-! ## Trace of the Lean checker -/

open Bcf in
def nodeLine (posOf : Array Nat) (n : Node) : String :=
  let (hdr, ws) := Vbcf.nodeWords (fun i => posOf[i]!) n
  ws.foldl (fun s w => s ++ " " ++ toString w) s!"N {hdr}"

open Bcf in
def runTrace (path : String) : IO UInt32 := do
  let out ← IO.getStdout
  let bytes ← IO.FS.readBinFile path
  match decode bytes with
  | .error e => out.putStrLn s!"D {e}"; return 0
  | .ok p =>
    -- position of each raw node
    let mut posOf : Array Nat := #[]
    let mut pos := 0
    for n in p.pool do
      posOf := posOf.push pos
      let vlen := match n.op with
        | .bvVal w _ => (w + 31) / 32
        | _ => n.args.size
      pos := pos + 1 + vlen
    let some (st0, tt) := pushNode initSt ⟨.boolVal true, #[]⟩ | out.putStrLn "D builtin"; return 0
    let some (st1, ff) := pushNode st0 ⟨.boolVal false, #[]⟩ | out.putStrLn "D builtin"; return 0
    let some (st2, remap) := canonicalize p.pool st1 | out.putStrLn "D canon"; return 0
    let mut buf := ""
    for n in st2.pool do
      buf := buf ++ nodeLine posOf n ++ "\n"
      if buf.length > 60000 then out.putStr buf; buf := ""
    for h : i in [0:remap.size] do
      buf := buf ++ s!"M {posOf[i]!} {remap[i]}\n"
      if buf.length > 60000 then out.putStr buf; buf := ""
    buf := buf ++ "C\n"
    let posmap := positionMap p.pool
    let some gpos := findGoal p.steps | out.putStr buf; out.putStrLn "D goal"; return 0
    let some graw := posmap[gpos]? | out.putStr buf; out.putStrLn "D goal"; return 0
    let some g := remap[graw]? | out.putStr buf; out.putStrLn "D goal"; return 0
    let ei := exprIdx posmap remap
    let mut st := st2
    let mut k := 0
    for s in p.steps do
      let some prems := getFacts st.facts s.premises.toList
        | out.putStr buf; out.putStrLn s!"X {k} premise"; return 0
      let old := st.pool.size
      match applyRule rwTable g ⟨tt, ff⟩ ei st s.rule prems s.params.toList with
      | none => out.putStr buf; out.putStrLn s!"X {k} {repr s.rule}"; return 0
      | some (st', f) =>
        for j in [old:st'.pool.size] do
          buf := buf ++ nodeLine posOf st'.pool[j]! ++ "\n"
        buf := buf ++ s!"S {f}\n"
        if buf.length > 60000 then out.putStr buf; buf := ""
        st := st'.addFact f
      k := k + 1
    out.putStr buf
    match st.facts[st.facts.size - 1]? with
    | some last => out.putStrLn (if last = ff then "A" else "R")
    | none => out.putStrLn "R"
    return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["print"] =>
    match Prog.toC Vbcf.prog with
    | .ok s => IO.print s; pure 0
    | .error e => IO.eprintln e; pure 1
  | "run" :: path :: "-g" :: arena :: g :: fails =>
    let aw ← readWords arena
    IO.println (← runInterp path (some (aw, g.toNat!)) (fails.map String.toNat!)); pure 0
  | "run" :: path :: fails =>
    IO.println (← runInterp path none (fails.map String.toNat!)); pure 0
  | ["cost", path] => IO.println (← runCost path); pure 0
  | ["trace", path] => runTrace path
  | _ => IO.eprintln "usage: vbcf print | run <file.bcf> [-g <arena> <goal>] [failing-call-index]* | cost <file.bcf> | trace <file.bcf>"; pure 2
