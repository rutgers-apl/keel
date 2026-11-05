import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Specs
import Vbcf.Proof.LoadSpec
import Vbcf.Proof.GoalSpecs
import Bcf.Final

/-!
# Vbcf proofs: the contract for loading, replay, and the entry points

Statements only.  `RuleSpecs` bundles the specification of all fifty rule
functions.  `InitSpec`, `LoadSpec`, `ScanSpec` describe the three phases
before the step loop; their postconditions (`InitDone`, `LoadDone`,
`ScanDone`) are the interface between the proof of the loading phase and the
proof of the replay phase.  `VbcfCheckSpec` and `BcfCheckUserSpec` are the
top-level results.
-/

namespace Vbcf.Proof

variable {State : Type}
open Bcf

/-- Every rule function meets `RuleSpec` for the Lean rule `applyRule` dispatches to. -/
structure RuleSpecs : Prop where
  assume : RuleSpec (State := State) "r_assume" (fun X st pr pa => ruleAssume X.goal X.ei st pr pa)
  refl : RuleSpec (State := State) "r_refl" (fun X st pr pa => ruleRefl X.ei st pr pa)
  symm : RuleSpec (State := State) "r_symm" (fun _ st pr pa => ruleSymm st pr pa)
  trans : RuleSpec (State := State) "r_trans" (fun _ st pr pa => ruleTrans st pr pa)
  cong : RuleSpec (State := State) "r_cong" (fun _ st pr pa => ruleCong st pr pa)
  trueIntro : RuleSpec (State := State) "r_true_intro" (fun X st pr pa => ruleTrueIntro X.bi st pr pa)
  trueElim : RuleSpec (State := State) "r_true_elim" (fun X st pr pa => ruleTrueElim X.bi st pr pa)
  falseIntro : RuleSpec (State := State) "r_false_intro" (fun X st pr pa => ruleFalseIntro X.bi st pr pa)
  falseElim : RuleSpec (State := State) "r_false_elim" (fun X st pr pa => ruleFalseElim X.bi st pr pa)
  eqResolve : RuleSpec (State := State) "r_eq_resolve" (fun _ st pr pa => ruleEqResolve st pr pa)
  modusPonens : RuleSpec (State := State) "r_modus_ponens" (fun _ st pr pa => ruleModusPonens st pr pa)
  notNotElim : RuleSpec (State := State) "r_not_not_elim" (fun _ st pr pa => ruleNotNotElim st pr pa)
  contra : RuleSpec (State := State) "r_contra" (fun X st pr pa => ruleContra X.bi st pr pa)
  andElim : RuleSpec (State := State) "r_and_elim" (fun _ st pr pa => ruleAndElim st pr pa)
  andIntro : RuleSpec (State := State) "r_and_intro" (fun _ st pr pa => ruleAndIntro st pr pa)
  notOrElim : RuleSpec (State := State) "r_not_or_elim" (fun _ st pr pa => ruleNotOrElim st pr pa)
  split : RuleSpec (State := State) "r_split" (fun X st pr pa => ruleSplit X.ei st pr pa)
  evaluate : RuleSpec (State := State) "r_evaluate" (fun X st pr pa => ruleEvaluate X.ei st pr pa)
  impliesElim : RuleSpec (State := State) "r_implies_elim" (fun _ st pr pa => ruleImpliesElim st pr pa)
  notImpliesElim : RuleSpec (State := State) "r_not_implies_elim" (fun _ st pr pa => ruleNotImpliesElim st pr pa)
  equivElim : RuleSpec (State := State) "r_equiv_elim" (fun _ st pr pa => ruleEquivElim st pr pa)
  notEquivElim : RuleSpec (State := State) "r_not_equiv_elim" (fun _ st pr pa => ruleNotEquivElim st pr pa)
  xorElim : RuleSpec (State := State) "r_xor_elim" (fun _ st pr pa => ruleXorElim st pr pa)
  notXorElim : RuleSpec (State := State) "r_not_xor_elim" (fun _ st pr pa => ruleNotXorElim st pr pa)
  iteElim : RuleSpec (State := State) "r_ite_elim" (fun _ st pr pa => ruleIteElim st pr pa)
  notIteElim : RuleSpec (State := State) "r_not_ite_elim" (fun _ st pr pa => ruleNotIteElim st pr pa)
  notAnd : RuleSpec (State := State) "r_not_and" (fun _ st pr pa => ruleNotAnd st pr pa)
  cnfAndPos : RuleSpec (State := State) "r_cnf_and_pos" (fun X st pr pa => ruleCnfAndPos X.ei st pr pa)
  cnfAndNeg : RuleSpec (State := State) "r_cnf_and_neg" (fun X st pr pa => ruleCnfAndNeg X.ei st pr pa)
  cnfOrPos : RuleSpec (State := State) "r_cnf_or_pos" (fun X st pr pa => ruleCnfOrPos X.ei st pr pa)
  cnfOrNeg : RuleSpec (State := State) "r_cnf_or_neg" (fun X st pr pa => ruleCnfOrNeg X.ei st pr pa)
  cnfImpliesPos : RuleSpec (State := State) "r_cnf_implies_pos" (fun X st pr pa => ruleCnfImpliesPos X.ei st pr pa)
  cnfImpliesNeg : RuleSpec (State := State) "r_cnf_implies_neg" (fun X st pr pa => ruleCnfImpliesNeg X.ei st pr pa)
  cnfEquivPos : RuleSpec (State := State) "r_cnf_equiv_pos" (fun X st pr pa => ruleCnfEquivPos X.ei st pr pa)
  cnfEquivNeg : RuleSpec (State := State) "r_cnf_equiv_neg" (fun X st pr pa => ruleCnfEquivNeg X.ei st pr pa)
  cnfXorPos : RuleSpec (State := State) "r_cnf_xor_pos" (fun X st pr pa => ruleCnfXorPos X.ei st pr pa)
  cnfXorNeg : RuleSpec (State := State) "r_cnf_xor_neg" (fun X st pr pa => ruleCnfXorNeg X.ei st pr pa)
  cnfItePos : RuleSpec (State := State) "r_cnf_ite_pos" (fun X st pr pa => ruleCnfItePos X.ei st pr pa)
  cnfIteNeg : RuleSpec (State := State) "r_cnf_ite_neg" (fun X st pr pa => ruleCnfIteNeg X.ei st pr pa)
  iteEq : RuleSpec (State := State) "r_ite_eq" (fun X st pr pa => ruleIteEq X.ei st pr pa)
  distinctValues : RuleSpec (State := State) "r_distinct_values" (fun X st pr pa => ruleDistinctValues X.ei st pr pa)
  resolution : RuleSpec (State := State) "r_resolution" (fun X st pr pa => ruleResolution X.bi X.ei st pr pa)
  factoring : RuleSpec (State := State) "r_factoring" (fun _ st pr pa => ruleFactoring st pr pa)
  reordering : RuleSpec (State := State) "r_reordering" (fun _ st pr pa => ruleReordering st pr pa)
  absorb : RuleSpec (State := State) "r_absorb" (fun X st pr pa => ruleAbsorb X.ei st pr pa)
  aciNorm : RuleSpec (State := State) "r_aci_norm" (fun X st pr pa => ruleAciNorm X.ei st pr pa)
  polyNorm : RuleSpec (State := State) "r_poly_norm" (fun X st pr pa => rulePolyNorm X.ei st pr pa)
  polyNormEq : RuleSpec (State := State) "r_poly_norm_eq" (fun _ st pr pa => rulePolyNormEq st pr pa)
  rewrite : RuleSpec (State := State) "r_rewrite" (fun X st pr pa => ruleRewrite rwTable X.bi X.ei st pr pa)
  bitblast : RuleSpec (State := State) "r_bitblast" (fun X st pr pa => ruleBitblast X.bi X.ei st pr pa)

/-! ## Loading -/

/-- The struct as `kzalloc` leaves it. -/
def zeroCK : CK :=
  { pool := none, plen := 0, pcap := 0, htab := none, hcap := 0, hcnt := 0, facts := none,
    flen := 0, fcap := 0, nexpr := 0, stk := none, sp := 0, scap := 0, prem := none, par := none,
    proof := none, tt := 0, ff := 0, goal := 0, err := 0, work := 0, val := 0, mem := 0,
    lr := none, lo := 0, live := 0 }

/-- The Lean checker's first two pushes: `true`, then `false`. -/
def Builtin2 (st1 : St) (tt ff : Nat) : Prop :=
  ∃ st0, pushNode initSt ⟨.boolVal true, #[]⟩ = some (st0, tt) ∧
    pushNode st0 ⟨.boolVal false, #[]⟩ = some (st1, ff)

/-- The premise buffer: 256 initialised cells. -/
structure PremOK (c : CMem) : Prop where
  ptr : ∃ b, c.k.prem = some (b, 0)
  size : c.prem.size = 256
  cells : ∀ j, j < 256 → ∃ w, w < 2 ^ 32 ∧ U c.prem j w

/-- After `ck_init` succeeds. -/
structure InitDone (c : CMem) (st1 : St) (tt ff : Nat) : Prop where
  b2 : Builtin2 st1 tt ff
  core : ∀ posOf : Nat → Nat, (∀ a b, posOf a = posOf b → a = b) → CoreInv posOf c st1
  tt : c.k.tt.toNat = offs st1.pool tt
  ff : c.k.ff.toNat = offs st1.pool ff
  prem : PremOK c
  factsNull : c.k.facts = none
  flen : c.k.flen = 0#32
  proofNull : c.k.proof = none
  parNull : c.k.par = none
  lrNull : c.k.lr = none

def InitSpec : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem) (nw g : BitVec 32),
    EmbC.FnSpec (State := State) Vbcf.prog "ck_init"
      (fun vs s => vs = [.ptr sb 0, .u32 nw, .u32 g] ∧ Holds W s.mem sb c ∧ c.k = zeroCK)
      (fun _ _ rv s' => ∃ c', Holds W s'.mem sb c' ∧ c'.proof = c.proof ∧
        (rv = some (.u32 0#32) ∨
         (rv = some (.u32 1#32) ∧ ∃ st1 tt ff, InitDone c' st1 tt ff)))

/-- After `ck_load` succeeds: the header is valid, the expression section
has been loaded (`LoadInv` at the end of the section), the checker state
represents the canonical pool, and the proof block holds the position map
where the expressions were and the original words elsewhere. -/
structure LoadDone (W : World) (ws : Array (BitVec 32)) (c : CMem) (tt ff : Nat) (st1 st2 : St)
    (pm : Nat → Option Nat) (D : Nat) : Prop where
  hsz : 3 ≤ ws.size
  hmagic : wordFn ws 0 = 0x0BCF
  hne : wordFn ws 1 ≠ 0
  hns : 2 ≤ wordFn ws 2
  hlen : 3 + wordFn ws 1 + wordFn ws 2 = ws.size
  b2 : Builtin2 st1 tt ff
  load : LoadInv (wordFn ws) st1 (wordFn ws 1) D st2 pm
  core : CoreInv (posOfW (wordFn ws)) c st2
  proofPtr : c.k.proof = some (W.pb, 0)
  psize : c.proof.size ≤ 2 ^ 32
  nexpr : c.k.nexpr.toNat = wordFn ws 1
  proofSize : c.proof.size = ws.size
  map : ∀ p, p < wordFn ws 1 →
    U c.proof (3 + p) (match pm p with | none => 0 | some i => offs st2.pool i + 1)
  rest : ∀ q, (q < 3 ∨ 3 + wordFn ws 1 ≤ q) → q < ws.size → U c.proof q (wordFn ws q)
  ttNode : st2.pool[tt]? = some ⟨.boolVal true, #[]⟩
  ffNode : st2.pool[ff]? = some ⟨.boolVal false, #[]⟩
  tt : c.k.tt.toNat = offs st2.pool tt
  ff : c.k.ff.toNat = offs st2.pool ff
  prem : PremOK c
  factsNull : c.k.facts = none
  flen : c.k.flen = 0#32
  noFacts : st2.facts = #[]
  lrNull : c.k.lr = none
  lo : c.k.lo = c.k.plen

def LoadSpec : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem) (ws : Array (BitVec 32)) (n : BitVec 32) (st1 : St)
    (tt ff : Nat),
    EmbC.FnSpec (State := State) Vbcf.prog "ck_load"
      (fun vs s => vs = [.ptr sb 0, .ptr W.pb 0, .u32 n] ∧ Holds W s.mem sb c ∧
        InitDone c st1 tt ff ∧ c.proof = ws.map EmbC.Val.u32 ∧ n.toNat = ws.size)
      (fun _ _ rv s' => ∃ c', Holds W s'.mem sb c' ∧
        (rv = some (.u32 0#32) ∨
         (rv = some (.u32 1#32) ∧ ∃ st2 pm D, LoadDone W ws c' tt ff st1 st2 pm D)))

/-- `LoadDone` without `factsNull`: what survives `ck_scan`'s allocation of the
fact array. -/
structure LoadDone' (W : World) (ws : Array (BitVec 32)) (c : CMem) (tt ff : Nat) (st1 st2 : St)
    (pm : Nat → Option Nat) (D : Nat) : Prop where
  hsz : 3 ≤ ws.size
  hmagic : wordFn ws 0 = 0x0BCF
  hne : wordFn ws 1 ≠ 0
  hns : 2 ≤ wordFn ws 2
  hlen : 3 + wordFn ws 1 + wordFn ws 2 = ws.size
  b2 : Builtin2 st1 tt ff
  load : LoadInv (wordFn ws) st1 (wordFn ws 1) D st2 pm
  core : CoreInv (posOfW (wordFn ws)) c st2
  proofPtr : c.k.proof = some (W.pb, 0)
  psize : c.proof.size ≤ 2 ^ 32
  nexpr : c.k.nexpr.toNat = wordFn ws 1
  proofSize : c.proof.size = ws.size
  map : ∀ p, p < wordFn ws 1 →
    U c.proof (3 + p) (match pm p with | none => 0 | some i => offs st2.pool i + 1)
  rest : ∀ q, (q < 3 ∨ 3 + wordFn ws 1 ≤ q) → q < ws.size → U c.proof q (wordFn ws q)
  ttNode : st2.pool[tt]? = some ⟨.boolVal true, #[]⟩
  ffNode : st2.pool[ff]? = some ⟨.boolVal false, #[]⟩
  tt : c.k.tt.toNat = offs st2.pool tt
  ff : c.k.ff.toNat = offs st2.pool ff
  prem : PremOK c
  flen : c.k.flen = 0#32
  noFacts : st2.facts = #[]
  lo : c.k.lo = c.k.plen

/-- After `ck_scan` succeeds: additionally the step section is well-formed,
the goal is known, and the fact array and the last-reference array `lr` are
allocated with one cell per step.  (What `lr` holds is not needed: `ck_step`
only rejects on it, and `ck_compact` keeps every fact it says is still cited.) -/
structure ScanDone (W : World) (ws : Array (BitVec 32)) (c : CMem) (tt ff : Nat) (st1 st2 : St)
    (pm : Nat → Option Nat) (D : Nat) (steps : List Step) (gpos g : Nat) : Prop where
  ld : LoadDone' W ws c tt ff st1 st2 pm D
  scan : scanSteps (wordFn ws) (3 + wordFn ws 1) (wordFn ws 2) (wordFn ws 2) 0 0 false 0
    = some (steps, gpos)
  goal : pm gpos = some g
  goalFld : c.k.goal.toNat = offs st2.pool g
  factsPtr : ∃ b, c.k.facts = some (b, 0)
  factsSize : c.facts.size = steps.length
  fcap : c.k.fcap.toNat = steps.length
  factsCells : ∀ j, j < steps.length → ∃ w, w < 2 ^ 32 ∧ U c.facts j w
  lrPtr : ∃ b, c.k.lr = some (b, 0)
  lrSize : c.lr.size = steps.length
  lrCells : ∀ j, j < steps.length → ∃ w, w < 2 ^ 32 ∧ U c.lr j w

def ScanSpec : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem) (ws : Array (BitVec 32)) (st1 st2 : St) (tt ff : Nat)
    (pm : Nat → Option Nat) (D : Nat),
    EmbC.FnSpec (State := State) Vbcf.prog "ck_scan"
      (fun vs s => vs = [.ptr sb 0] ∧ Holds W s.mem sb c ∧ LoadDone W ws c tt ff st1 st2 pm D)
      (fun _ _ rv s' => ∃ c', Holds W s'.mem sb c' ∧
        (rv = some (.u32 0#32) ∨
         (rv = some (.u32 1#32) ∧ ∃ steps gpos g, ScanDone W ws c' tt ff st1 st2 pm D steps gpos g)))

/-! ## The entry points -/

/-- Memory after a call that kept nothing: block `pb` is still a `u32` array
of the same size (its contents may differ), every other block is exactly as
before, and in particular nothing new is live. -/
def OnlyBlockChanged (m m' : EmbC.Mem) (pb : Nat) : Prop :=
  (∀ b, b ≠ pb → m'.block? b = m.block? b) ∧
  ∃ cells cells', m.block? pb = some ⟨.u32, cells⟩ ∧ m'.block? pb = some ⟨.u32, cells'⟩ ∧
    cells'.size = cells.size

/-! ### The verifier's goal argument -/

/-- The verifier's goal argument of an entry point: `none` is a `NULL` arena,
`some (gb, gws)` is block `gb` holding the words `gws`. -/
abbrev GArg := Option (Nat × Array (BitVec 32))

/-- The pointer value passed for a goal argument. -/
def gxVal : GArg → EmbC.Val
  | none => .null
  | some (gb, _) => .ptr gb 0

/-- What the verifier guarantees about its goal argument in memory `m`: the
arena block holds its words and the goal node lies inside it. -/
def ArenaIn (m : EmbC.Mem) (goal : Nat) : GArg → Prop
  | none => True
  | some (gb, gws) => m.block? gb = some ⟨.u32, gws.map EmbC.Val.u32⟩ ∧ goal < gws.size ∧
      goal + 1 + hdrVlen (wordFn gws goal) ≤ gws.size

/-- The arena is not block `pb`. -/
def ArenaNot (pb : Nat) : GArg → Prop
  | none => True
  | some (gb, _) => gb ≠ pb

/-- **The verifier's goal is refuted**: no state makes node `goal` of the arena
true.  Nothing is claimed for a `NULL` arena. -/
def GoalRefuted (goal : Nat) : GArg → Prop
  | none => True
  | some (_, gws) => ∀ ρ, ¬ Bcf.arenaHolds (wordFn gws) ρ goal

/-- `vbcf_check(goal_exprs, goal, proof, nwords)`: never stuck, frees everything
it allocated, and returns 0 only if the Lean checker accepts the proof those
words encode and the verifier's goal is refuted. -/
def VbcfCheckSpec : Prop :=
  ∀ (pb : Nat) (ws : Array (BitVec 32)) (n : BitVec 32) (ga : GArg) (goal : BitVec 32),
    EmbC.FnSpec (State := State) Vbcf.prog "vbcf_check"
      (fun vs s => vs = [gxVal ga, .u32 goal, .ptr pb 0, .u32 n] ∧
        s.mem.block? pb = some ⟨.u32, ws.map EmbC.Val.u32⟩ ∧ n.toNat = ws.size ∧
        ArenaIn s.mem goal.toNat ga ∧ ArenaNot pb ga)
      (fun _ s rv s' => OnlyBlockChanged s.mem s'.mem pb ∧ ∃ r, rv = some (.u32 r) ∧
        (r = 0#32 → (∃ P g, Bcf.decode (wordsToBytes ws) = .ok P ∧ checkBcf P = some g) ∧
          GoalRefuted goal.toNat ga))

/-- The buffer and state produced by the entry point's input allocation. -/
def inputAllocation (st : EmbC.KernelState prog State) (n : Nat) :=
  EmbC.Ext.answer Vbcf.prog (.kvcalloc .u32) [.u64 (BitVec.ofNat 64 n)] st

/-- The actual copy reply after the entry point's successful allocation. -/
def inputCopy (st : EmbC.KernelState prog State) (n : Nat) :=
  let allocated := inputAllocation st n
  EmbC.Ext.answer Vbcf.prog .copyFromBpfptr
    [(allocated.1.getD .null), .uptr, .u64 (BitVec.ofNat 64 n)] allocated.2

/-- Words actually delivered into the entry point's private copy buffer.
This reads the returned heap, not a predicted sequence of future choices. -/
def copiedWords (st : EmbC.KernelState prog State) (n : Nat) : Array (BitVec 32) :=
  match (inputAllocation st n).1 with
  | some (.ptr b 0) =>
    match (inputCopy st n).2.mem.block? b with
    | some blk => blk.cells.map (fun v => match v with | .u32 w => w | _ => 0)
    | none => #[]
  | _ => #[]

/-- `vbcf_check_proof(goal_exprs, goal, proof, proof_size)`: never stuck,
leaves memory exactly as it found it, and returns 0 only if the Lean checker
accepts the proof made of the words it copied in and the verifier's goal is
refuted. -/
def VbcfCheckProofSpec : Prop :=
  ∀ (ga : GArg) (goal size : BitVec 32),
    EmbC.FnSpec (State := State) Vbcf.prog "vbcf_check_proof"
      (fun vs s => vs = [gxVal ga, .u32 goal, .uptr, .u32 size] ∧ ArenaIn s.mem goal.toNat ga)
      (fun _ s rv s' => (∀ b, s'.mem.block? b = s.mem.block? b) ∧ ∃ r, rv = some (.u32 r) ∧
        (r = 0#32 → (∃ P g,
          Bcf.decode (wordsToBytes (copiedWords s (size.toNat / 4))) = .ok P ∧
          checkBcf P = some g) ∧ GoalRefuted goal.toNat ga))

end Vbcf.Proof
