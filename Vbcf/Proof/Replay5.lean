import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.Replay4

/-!
# Vbcf proofs: the replay loop of `ck_run` (pure part)

* `Accepts ws`: the Lean checker accepts the proof made of the words `ws`;
  `accepts_of_replay`: it does when the replay of the scanned steps from the
  loaded state ends with `false`.
* `SInv.next`: the step invariant after one iteration of the loop (the step's
  conclusion stored at `facts[flen]`, `flen` incremented, `off` advanced).
* `CkRunSpec`, `RunPost`, `RunInv`: the statement and the loop invariant.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC Bcf

/-- The Lean checker accepts the proof made of the words `ws`. -/
def Accepts (ws : Array (BitVec 32)) : Prop :=
  ∃ P g, Bcf.decode (wordsToBytes ws) = .ok P ∧ checkBcf P = some g

/-- **Acceptance**, from the bridge and a replay ending with the fact `false`. -/
theorem accepts_of_replay {ws : Array (BitVec 32)} {st0 st1 st2 st3 : St} {tt ff g : Nat}
    {pm : Nat → Option Nat} {steps : List Step} {gpos D : Nat} {P : RawProof} {remap : Array Nat}
    (htt : pushNode initSt ⟨.boolVal true, #[]⟩ = some (st0, tt))
    (hff : pushNode st0 ⟨.boolVal false, #[]⟩ = some (st1, ff))
    (hb : LoadBridge ws st1 st2 pm steps gpos D P remap) (hgoal : pm gpos = some g)
    (hreplay : replay rwTable g ⟨tt, ff⟩ pm steps st2 = some st3)
    (hlast : st3.facts[st3.facts.size - 1]? = some ff) : Accepts ws := by
  have hc := check_of_bridge rwTable htt hff hb
  simp only [hgoal, hreplay, hlast, ↓reduceIte] at hc
  have hg := hb.ei gpos
  rw [hgoal, Bcf.exprIdx, hb.posmap] at hg
  cases hi : idxOf (wordFn ws) D gpos with
  | none => rw [hi] at hg; simp at hg
  | some graw => exact ⟨P, graw, hb.decode_ok, by unfold checkBcf; rw [hc, hi]⟩

theorem lt_uv_iff {x : BitVec 32} {n : Nat} (h : n < 2 ^ 32) :
    x < BitVec.ofNat 32 n ↔ x.toNat < n := by
  rw [BitVec.lt_def, bv_toNat_ofNat h]

/-- Recording a fact extends a view. -/
theorem VExt.withFact {S0 S : VSt} (he : VExt S0 S) (f : Nat) : VExt S0 (S.withFact f) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, he.lv, he.σ, he.cs⟩
  · have := he.lean.size; simp only [VSt.withFact_toSt, addFact_pool]; exact this
  · intro i hi; simp only [VSt.withFact_toSt, addFact_pool]; exact he.lean.node i hi
  · intro i hi; simp only [VSt.withFact_toSt]; rw [St.addFact_eq]; exact he.lean.tys i hi
  · intro i hi; simp only [VSt.withFact_toSt, addFact_pool]; exact he.lean.offs i hi

/-- `RInv` does not look at the facts. -/
theorem RInv.withFact {W : World} {X : Ctx} {c : CMem} {st : VSt} (h : RInv W X c st) (f : Nat) :
    RInv W X c (st.withFact f) where
  core := ⟨h.core.cinv, fun i n hn => h.core.fitsAll i n (by simpa [addFact_pool] using hn)⟩
  poolPtr := h.poolPtr
  ttNode := by simp only [VSt.withFact_toSt, addFact_pool]; exact h.ttNode
  ffNode := by simp only [VSt.withFact_toSt, addFact_pool]; exact h.ffNode
  tt := h.tt
  ff := h.ff
  goal := h.goal
  proofPtr := h.proofPtr
  nexpr := h.nexpr
  nexprBound := h.nexprBound
  ei := h.ei
  eiOut := h.eiOut
  premPtr := h.premPtr
  premSize := h.premSize
  premCells := h.premCells
  floor := fun S0 h0 => (h.floor S0 h0).withFact f

/-- **One iteration of the loop.**  `c3` is the C state after `ck_step` returned
`c'` and the loop stored the conclusion's id at `facts[flen]` and incremented
`flen`. -/
theorem SInv.next {W : World} {ws : Array (BitVec 32)} {X : Ctx} {c c' c3 : CMem} {st st' : VSt}
    {off : Nat} {s : Step} {rest : List Step} {prems : List Nat} {f : Nat}
    (hK : RulesKeepFacts) (hS : SInv W ws X c st off (s :: rest))
    (hget : getFacts st.facts s.premises.toList = some prems)
    (happ : applyRule rwTable X.goal X.bi X.ei st s.rule prems s.params.toList = some (st'.toSt, f))
    (hinv' : RInv W X c' st') (hflv : st'.lv f) (hfr : StepFrame c c') (hext : VExt st st')
    (hpool : c3.pool = c'.pool) (hhtab : c3.htab = c'.htab) (hstk : c3.stk = c'.stk)
    (hproof : c3.proof = c'.proof) (hprem : c3.prem = c'.prem) (hlr : c3.lr = c'.lr)
    (hk : c3.k = { c'.k with flen := c'.k.flen + 1#32 })
    (hfacts : c3.facts =
      c'.facts.setIfInBounds c'.k.flen.toNat (.u32 (BitVec.ofNat 32 (st'.id f)))) :
    SInv W ws X c3 (st'.withFact f)
      (off + 1 + stepPc (wordFn ws (3 + wordFn ws 1 + off)) + stepAc (wordFn ws (3 + wordFn ws 1 + off)))
      rest := by
  obtain ⟨hlt, hle, hseq, hrest⟩ := hS.steps
  have hkeep := hK _ _ _ _ _ _ _ _ _ happ
  obtain ⟨hpre, hsz, hflt, hsound⟩ := hS.leanStep hget happ
  have hflen : c'.k.flen.toNat = st.facts.size := by rw [hfr.flen]; exact hS.flen
  have hfsz := hS.factsSize
  have hlt32 := hS.factsLt
  simp only [List.length_cons] at hfsz
  have hc3sz : c3.facts.size = c.facts.size := by rw [hfacts, hfr.facts]; simp
  have hc3lr : c3.lr = c.lr := by rw [hlr, hfr.lr]
  have hflen3 : c3.k.flen.toNat = st.facts.size + 1 := by
    rw [hk]
    show (c'.k.flen + 1#32).toNat = _
    rw [BitVec.toNat_add, hflen]
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    omega
  have hinv3 : RInv W X c3 st' :=
    hinv'.same hpool hhtab hstk hproof (by rw [hk]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
      (by rw [hk]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) (by rw [hk]; exact hinv'.core.stk.cap.1)
      ⟨by rw [hprem]; exact hinv'.premSize, by rw [hprem]; exact hinv'.premCells⟩
  have hfacts' : (st'.withFact f).facts = st.facts.push f := by
    simp only [VSt.withFact_toSt]; rw [St.addFact_eq, hkeep]
  refine
    { inv := hinv3.withFact f
      noFloor := hS.noFloor
      wsz := hS.wsz
      nexpr := by rw [hk]; show c'.k.nexpr.toNat = _; rw [hfr.nexpr]; exact hS.nexpr
      hlen := hS.hlen
      proofSize := by rw [hproof, hfr.proof]; exact hS.proofSize
      words := by rw [hproof, hfr.proof]; exact hS.words
      factsPtr := by rw [hk]; show ∃ b, c'.k.facts = _; rw [hfr.factsPtr]; exact hS.factsPtr
      flen := by rw [hflen3, hfacts']; simp
      factsSize := by rw [hfacts', hc3sz]; simp only [Array.size_push]; omega
      fcap := by rw [hk, hc3sz]; show c'.k.fcap.toNat = _; rw [hfr.fcap]; exact hS.fcap
      factsCells := ?_
      lrPtr := by rw [hk]; show ∃ b, c'.k.lr = _; rw [hfr.lrPtr]; exact hS.lrPtr
      lrSize := by rw [hc3lr, hc3sz]; exact hS.lrSize
      lrCells := by rw [hc3lr]; exact hS.lrCells
      facts := ?_
      loaded := fun i hi => by
        obtain ⟨h1, h2⟩ := hS.loaded i hi
        exact ⟨hext.lt h1, by show st'.σ i < X.nL; rw [hext.σ i h1]; exact h2⟩
      nLcs := Nat.le_trans hS.nLcs hext.cs.size
      lo := by
        rw [hk]; show c'.k.lo.toNat = _; rw [hfr.lo, hS.lo]
        exact (hext.cs.offs _ hS.nLcs).symm
      ttL := hS.ttL
      ffL := hS.ffL
      goalL := hS.goalL
      eiL := hS.eiL
      steps := hrest
      sound := ?_ }
  · intro j hj
    rw [hc3sz] at hj
    by_cases hjf : j = st.facts.size
    · refine ⟨st'.id f, ?_, ?_⟩
      · have := hinv'.core.off_lt hflv; omega
      · unfold U; rw [hfacts, hflen, hjf, Array.getElem?_setIfInBounds]
        simp only [↓reduceIte]; rw [hfr.facts]
        simp [show st.facts.size < c.facts.size by omega]
    · obtain ⟨w, hw, hu⟩ := hS.factsCells j hj
      refine ⟨w, hw, ?_⟩
      unfold U at hu ⊢
      rw [hfacts, hflen, Array.getElem?_setIfInBounds, hfr.facts]
      simp only [Ne.symm hjf, ↓reduceIte]; exact hu
  · intro j g hg
    rw [hfacts'] at hg
    rw [Array.getElem?_push] at hg
    by_cases hj : j = st.facts.size
    · simp only [hj, ↓reduceIte, Option.some.injEq] at hg
      subst hg
      refine ⟨by simp only [VSt.withFact_toSt, addFact_pool]; exact st'.lt hflv, fun w _ _ _ => ⟨hflv, ?_⟩⟩
      rw [hj]
      unfold U
      rw [hfacts, hflen, Array.getElem?_setIfInBounds]
      simp only [↓reduceIte]
      rw [hfr.facts]
      simp only [show st.facts.size < c.facts.size by omega, ↓reduceIte]
      rfl
    · simp only [hj, ↓reduceIte] at hg
      obtain ⟨hg1, hg2⟩ := hS.facts j g hg
      refine ⟨by simp only [VSt.withFact_toSt, addFact_pool]; exact Nat.lt_of_lt_of_le hg1 hsz,
        fun w hw32 hw hle => ?_⟩
      rw [hc3lr] at hw
      obtain ⟨hlv, hu⟩ := hg2 w hw32 hw (by rw [hS.flen]; omega)
      refine ⟨hext.lt hlv, ?_⟩
      show U c3.facts j (st'.id g)
      rw [hext.id hlv]
      unfold U at hu ⊢
      rw [hfacts, hflen, Array.getElem?_setIfInBounds, hfr.facts]
      simp only [Ne.symm hj, ↓reduceIte]
      exact hu
  · intro ρ hρ k g hg
    simp only [VSt.withFact_toSt] at hρ hg ⊢
    rw [St.addFact_eq] at hg hρ ⊢
    exact hsound ρ hρ k g hg

/-! ## `ck_compact` -/

/-- `ck_compact(st)` between two steps: never stuck, keeps `Holds`, and if it
returns non-zero the step invariant holds for a new view of the same Lean state. -/
def CkCompactSpec : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem) (ws : Array (BitVec 32)) (X : Ctx) (st : VSt) (off : Nat)
    (rest : List Step),
    FnSpec (State := State) Vbcf.prog "ck_compact"
      (fun vs s => vs = [.ptr sb 0] ∧ Holds W s.mem sb c ∧ SInv W ws X c st off rest ∧
        c.k.lo.toNat < c.k.plen.toNat)
      (fun _ _ rv s' => ∃ c' r, rv = some (.u32 r) ∧ Holds W s'.mem sb c' ∧
        (r ≠ 0#32 → ∃ st' : VSt, st'.toSt = st.toSt ∧ SInv W ws X c' st' off rest))

/-- The last fact, just stored by the step loop, is the id of its node (a compaction may
drop it later, but none runs after the last step). -/
def LastOK (c : CMem) (st : VSt) : Prop :=
  0 < st.facts.size → ∃ f, st.facts[st.facts.size - 1]? = some f ∧ st.lv f ∧
    U c.facts (st.facts.size - 1) (st.id f)

/-! ## The statement -/

def RunPost (W : World) (sb : Nat) (ws : Array (BitVec 32)) (ga : GArg) (goal : Nat) :
    Option EmbC.Val → (KernelState prog State) → Prop :=
  fun rv s' => ∃ c' r, rv = some (.u32 r) ∧ Holds W s'.mem sb c' ∧
    (r ≠ 0#32 → Accepts ws ∧ GoalRefuted goal ga)

/-- The verifier's goal argument as `ck_run` sees it: the arena, if any, is a
block of the world at entry (`ArenaOK`). -/
def ArenaW (W : World) (goal : Nat) : GArg → Prop
  | none => True
  | some (gb, gws) => ArenaOK W gb gws goal

/-- `ck_run(st, proof, nwords, gx, goal)` on a freshly zeroed struct: never
stuck, keeps `Holds`, and returns non-zero only if the Lean checker accepts
the words and the verifier's goal is refuted. -/
def CkRunSpec : Prop :=
  ∀ (W : World) (sb : Nat) (c : CMem) (ws : Array (BitVec 32)) (n : BitVec 32) (ga : GArg)
    (goal : BitVec 32),
    FnSpec (State := State) Vbcf.prog "ck_run"
      (fun vs s => vs = [.ptr sb 0, .ptr W.pb 0, .u32 n, gxVal ga, .u32 goal] ∧
        Holds W s.mem sb c ∧ c.k = zeroCK ∧
        c.proof = ws.map EmbC.Val.u32 ∧ n.toNat = ws.size ∧ ArenaW W goal.toNat ga)
      (fun _ _ => RunPost W sb ws ga goal.toNat)

/-- What the goal comparison established about the loaded state `st2` with
goal `g` (nothing for a `NULL` arena). -/
def GoalPend (st2 : St) (g goal : Nat) : GArg → Prop
  | none => True
  | some (_, gws) => GoalOK st2.pool (wordFn gws) g goal

/-- The local variables of `ck_run`. -/
def runEnv (W : World) (sb : Nat) (n : BitVec 32) (ga : GArg) (goal : BitVec 32)
    (okv off ns fv hdrv sigv : EmbC.Val) : Env :=
  [("st", .ptr (.struct "ck"), .ptr sb 0), ("proof", .ptr .u32, .ptr W.pb 0),
    ("nwords", .u32, .u32 n), ("gx", .ptr .u32, gxVal ga), ("goal", .u32, .u32 goal),
    ("ok", .u32, okv), ("off", .u32, off), ("ns", .u32, ns), ("f", .u32, fv), ("hdr", .u32, hdrv),
    ("sig", .u32, sigv)]

/-- The invariant of the step loop: after the steps before `off`, the C state
represents the Lean state `st`, and replaying all steps from the loaded state
is replaying the remaining ones from `st`. -/
def RunInv (W : World) (sb : Nat) (ws : Array (BitVec 32)) (n : BitVec 32) (ga : GArg)
    (goal : BitVec 32) (X : Ctx) (steps : List Step) (st2 : St) : Env → (KernelState prog State) → Prop := fun env s =>
  ∃ (c : CMem) (st : VSt) (off : BitVec 32) (rest : List Step) (okv fv hdrv sigv : BitVec 32),
    env = runEnv W sb n ga goal (.u32 okv) (.u32 off) (uv (wordFn ws 2)) (.u32 fv) (.u32 hdrv)
      (.u32 sigv) ∧
    Holds W s.mem sb c ∧ SInv W ws X c st off.toNat rest ∧ (rest = [] → LastOK c st) ∧
    replay rwTable X.goal X.bi X.ei steps st2 = replay rwTable X.goal X.bi X.ei rest st.toSt

/-- After the goal comparison: either `ck_run` returned (with `RunPost`), or
it goes on with the scanned state, the comparison's result recorded. -/
def GoalMid (W : World) (sb : Nat) (ws : Array (BitVec 32)) (n : BitVec 32) (ga : GArg)
    (goal : BitVec 32) (X : Ctx) (steps : List Step) (st2 : St) : (Post prog State) := fun o env s =>
  match o with
  | .normal => ∃ (c : CMem) (okv : BitVec 32),
      env = runEnv W sb n ga goal (.u32 okv) (.u32 0#32) (.u32 0#32) (.u32 0#32) (.u32 0#32)
        (.u32 0#32) ∧
      Holds W s.mem sb c ∧ (∃ S : VSt, S.toSt = st2 ∧ SInv W ws X c S 0 steps) ∧
      GoalPend st2 X.goal goal.toNat ga
  | .ret rv => match rv with
    | some v => s.mem.hasTy v .u32 = true ∧ RunPost W sb ws ga goal.toNat (some v) s
    | none => False
  | .brk => False

end Vbcf.Proof
