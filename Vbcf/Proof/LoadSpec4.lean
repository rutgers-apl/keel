import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.LoadSpec3

/-!
# Vbcf proofs: the step scanner

`scanSteps` (the loop of `ck_scan`) against `Bcf.decodeSteps` and
`Bcf.findGoal`, a forward invariant `ScanInv` for the scanning loop, and
`StepsAt`, which says which steps start at a given offset (for the replay
loop).
-/

namespace Vbcf.Proof

variable {State : Type}
open Bcf
set_option autoImplicit false

/-! ## The step section -/

theorem LoadSpec.getElem?_tail_ne {α : Type} {l : List α} {x a : α} (hx : x ∉ l) {k : Nat}
    (h : (a :: l)[k]? = some x) : k = 0 := by
  cases k with
  | zero => rfl
  | succ k =>
    simp only [List.getElem?_cons_succ] at h
    exact absurd (List.mem_of_getElem? h) hx

theorem LoadSpec.and_e000_1fff (c : Nat) (hc : c < 65536) : (c &&& 0xe000) ||| (c &&& 0x1fff) = c := by
  rw [← Nat.and_or_distrib_left]
  show c &&& 0xffff = c
  rw [LoadSpec.and_ffff]; omega

/-- Among 16-bit rule codes, only `1` is ASSUME. -/
theorem ofCode_assume (c : Nat) (hc : c < 65536) : Rule.ofCode c = .assume ↔ c = 1 := by
  constructor
  · intro h
    have hs := LoadSpec.and_e000_1fff c hc
    unfold Rule.ofCode at h
    simp only at h
    split at h
    · cases h
    · rename_i hidx
      cases hg : (if c &&& 0xe000 = 0 then
            [Rule.assume, .evaluate, .distinctValues, .aciNorm, .absorb, .rewrite, .refl, .symm,
              .trans, .cong, .trueIntro, .trueElim, .falseIntro, .falseElim]
          else if c &&& 0xe000 = 0x2000 then
            [Rule.resolution, .factoring, .reordering, .split, .eqResolve, .modusPonens,
              .notNotElim, .contra, .andElim, .andIntro, .notOrElim, .impliesElim, .notImpliesElim,
              .equivElim, .notEquivElim, .xorElim, .notXorElim, .iteElim, .notIteElim, .notAnd,
              .cnfAndPos, .cnfAndNeg, .cnfOrPos, .cnfOrNeg, .cnfImpliesPos, .cnfImpliesNeg,
              .cnfEquivPos, .cnfEquivNeg, .cnfXorPos, .cnfXorNeg, .cnfItePos, .cnfIteNeg, .iteEq]
          else if c &&& 0xe000 = 0x4000 then [Rule.bitblast, .polyNorm, .polyNormEq] else [])[(c &&& 0x1fff) - 1]? with
      | none => rw [hg] at h; cases h
      | some r =>
        rw [hg] at h
        simp only [Option.getD_some] at h
        subst h
        split at hg
        · rename_i hcls
          have := LoadSpec.getElem?_tail_ne (by decide) hg
          rw [hcls] at hs
          have h1 : c &&& 0x1fff = 1 := by omega
          rw [h1] at hs
          exact hs.symm
        · split at hg
          · exact absurd (List.mem_of_getElem? hg) (by decide)
          · split at hg
            · exact absurd (List.mem_of_getElem? hg) (by decide)
            · simp at hg
  · rintro rfl; rfl

theorem LoadSpec.step_fields (h : Nat) (hh : h < 2 ^ 32) :
    h &&& 0xffff = stepRule h ∧ (h >>> 16) &&& 0xff = stepPc h ∧ (h >>> 24) &&& 0xff = stepAc h := by
  refine ⟨LoadSpec.and_ffff h, ?_, ?_⟩
  · rw [LoadSpec.and_ff, LoadSpec.shr16]; rfl
  · rw [LoadSpec.and_ff, LoadSpec.shr24]; unfold stepAc; omega

theorem decodeStepsGo_step (ws : Array (BitVec 32)) (ne ns fuel p P stop : Nat) (acc : Array Step)
    (hP : P = 4 * (3 + ne + p)) (hstop : stop = 4 * (3 + ne + ns))
    (hb : p + 1 + stepPc (wordFn ws (3 + ne + p)) + stepAc (wordFn ws (3 + ne + p)) ≤ ns)
    (hsz : 3 + ne + ns ≤ ws.size) :
    decodeStepsGo (wordsToBytes ws) stop (fuel + 1) P acc =
      decodeStepsGo (wordsToBytes ws) stop fuel
        (P + 4 + 4 * (stepPc (wordFn ws (3 + ne + p)) + stepAc (wordFn ws (3 + ne + p))))
        (acc.push (stepAt (wordFn ws) (3 + ne + p))) := by
  have hw : u32At (wordsToBytes ws) P = wordFn ws (3 + ne + p) :=
    LoadSpec.u32At_word ws _ (3 + ne + p) hP (by omega)
  obtain ⟨f1, f2, f3⟩ := LoadSpec.step_fields _ (wordFn_lt ws (3 + ne + p))
  rw [decodeStepsGo]
  simp only [hw, f1, f2, f3]
  have h1 : P < stop := by omega
  have h2 : P + 4 + 4 * (stepPc (wordFn ws (3 + ne + p)) + stepAc (wordFn ws (3 + ne + p))) ≤ stop := by
    omega
  simp only [h1, h2, ↓reduceIte]
  congr 2
  unfold stepAt
  congr 2
  · apply List.map_congr_left
    intro k hk
    simp only [List.mem_range] at hk
    exact LoadSpec.u32At_word ws _ (3 + ne + p + 1 + k) (by omega) (by omega)
  · apply List.map_congr_left
    intro k hk
    simp only [List.mem_range] at hk
    exact LoadSpec.u32At_word ws _ (3 + ne + p + 1 + stepPc (wordFn ws (3 + ne + p)) + k) (by omega) (by omega)

theorem decodeStepsGo_done (b : ByteArray) (stop fuel : Nat) (acc : Array Step) :
    decodeStepsGo b stop fuel stop acc = some acc := by
  cases fuel <;> simp [decodeStepsGo]

theorem scanSteps_decode {ws : Array (BitVec 32)} {ne ns stop : Nat}
    (hstop : stop = 4 * (3 + ne + ns)) (hsz : 3 + ne + ns ≤ ws.size) :
    ∀ (fuel p nassume : Nat) (bad : Bool) (g : Nat) (rest : List Step) (g' : Nat),
      scanSteps (wordFn ws) (3 + ne) ns fuel p nassume bad g = some (rest, g') →
      ∀ (fuel' P : Nat) (acc : Array Step), P = 4 * (3 + ne + p) → ns ≤ p + fuel' →
        decodeStepsGo (wordsToBytes ws) stop fuel' P acc = some (acc ++ rest.toArray) := by
  intro fuel
  induction fuel with
  | zero =>
    intro p na bad g rest g' h fuel' P acc hP _
    simp only [scanSteps] at h
    split at h
    · rename_i hp
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        have : P = stop := by omega
        subst this
        simp [decodeStepsGo_done]
      · simp at h
    · simp at h
  | succ fuel ih =>
    intro p na bad g rest g' h fuel' P acc hP hf
    simp only [scanSteps] at h
    split at h
    · rename_i hlt
      split at h
      · rename_i hb
        split at h
        · simp at h
        · rename_i rest0 g0 hrec
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨fuel', rfl⟩ : ∃ f, fuel' = f + 1 := ⟨fuel' - 1, by omega⟩
          rw [decodeStepsGo_step ws ne ns fuel' p P stop acc hP hstop (by simpa [Nat.add_assoc] using hb) hsz]
          rw [ih _ _ _ _ _ _ hrec fuel' _ _ (by omega) (by omega)]
          simp [Nat.add_assoc]
      · simp at h
    · split at h
      · rename_i hp
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, _⟩ := h
          have : P = stop := by omega
          subst this
          simp [decodeStepsGo_done]
        · simp at h
      · simp at h

theorem stepRule_lt (h : Nat) : stepRule h < 65536 := by unfold stepRule; omega

theorem stepAt_assume (w : Nat → Nat) (q : Nat) :
    (stepAt w q).rule = .assume ↔ stepRule (w q) = 1 :=
  ofCode_assume _ (stepRule_lt _)

/-- What the scanner's accumulators mean. -/
theorem scanSteps_goal {w : Nat → Nat} {base ns : Nat} :
    ∀ (fuel p nassume : Nat) (bad : Bool) (g : Nat) (rest : List Step) (g' : Nat),
      scanSteps w base ns fuel p nassume bad g = some (rest, g') →
      bad = false ∧
      ((nassume = 1 ∧ rest.filter (·.rule = .assume) = [] ∧ g' = g) ∨
       (nassume = 0 ∧ ∃ s, rest.filter (·.rule = .assume) = [s] ∧ s.params.toList = [g'])) := by
  intro fuel
  induction fuel with
  | zero =>
    intro p na bad g rest g' h
    simp only [scanSteps] at h
    split at h
    · split at h
      · rename_i hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hc.2, Or.inl ⟨hc.1, rfl, rfl⟩⟩
      · simp at h
    · simp at h
  | succ fuel ih =>
    intro p na bad g rest g' h
    simp only [scanSteps] at h
    split at h
    · split at h
      · split at h
        · simp at h
        · rename_i rest0 g0 hrec
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨hbad, hcase⟩ := ih _ _ _ _ _ _ hrec
          by_cases hr : stepRule (w (base + p)) = 1
          · have hass : (stepAt w (base + p)).rule = .assume := (stepAt_assume w _).2 hr
            simp only [hr, ↓reduceIte, true_and] at hbad hcase
            have hac : stepAc (w (base + p)) = 1 ∧ bad = false := by
              by_cases hac : stepAc (w (base + p)) = 1
              · simpa [hac] using hbad
              · simp [hac] at hbad
            refine ⟨hac.2, Or.inr ?_⟩
            rcases hcase with ⟨hna, hf, hg⟩ | ⟨hna, _⟩
            · refine ⟨by omega, stepAt w (base + p), ?_, ?_⟩
              · simp [hass, hf]
              · simp only [hac.1, ↓reduceIte] at hg
                subst hg
                simp [stepAt, hac.1]
            · omega
          · have hass : ¬ (stepAt w (base + p)).rule = .assume := fun h => hr ((stepAt_assume w _).1 h)
            simp only [hr, ↓reduceIte, false_and] at hbad hcase
            refine ⟨hbad, ?_⟩
            simpa [List.filter_cons, hass] using hcase
      · simp at h
    · split at h
      · split at h
        · rename_i hc
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨hc.2, Or.inl ⟨hc.1, rfl, rfl⟩⟩
        · simp at h
      · simp at h

theorem scanSteps_findGoal {w : Nat → Nat} {base ns fuel : Nat} {steps : List Step} {gpos : Nat}
    (h : scanSteps w base ns fuel 0 0 false 0 = some (steps, gpos)) :
    findGoal steps.toArray = some gpos := by
  obtain ⟨_, hcase⟩ := scanSteps_goal _ _ _ _ _ _ _ h
  rcases hcase with ⟨h0, _⟩ | ⟨_, s, hf, hp⟩
  · omega
  · unfold findGoal
    simp only [hf, hp]


/-! ## Fuel does not matter -/

theorem scanSteps_fuel {w : Nat → Nat} {base ns : Nat} :
    ∀ (f1 f2 p nassume : Nat) (bad : Bool) (g : Nat), ns ≤ p + f1 → ns ≤ p + f2 →
      scanSteps w base ns f1 p nassume bad g = scanSteps w base ns f2 p nassume bad g := by
  intro f1
  induction f1 with
  | zero =>
    intro f2 p na bad g h1 h2
    cases f2 with
    | zero => rfl
    | succ f2 => simp only [scanSteps, show ¬ p < ns by omega, ↓reduceIte]
  | succ f1 ih =>
    intro f2 p na bad g h1 h2
    cases f2 with
    | zero => simp only [scanSteps, show ¬ p < ns by omega, ↓reduceIte]
    | succ f2 =>
      simp only [scanSteps]
      split
      · split
        · rw [ih f2 _ _ _ _ (by omega) (by omega)]
        · rfl
      · rfl

/-! ## The steps from an offset -/

/-- `rest` is the list of steps that start at offset `p` of the step section
and fill it exactly. -/
def StepsAt (w : Nat → Nat) (base ns : Nat) : Nat → List Step → Prop
  | p, [] => p = ns
  | p, s :: rest =>
    p < ns ∧ p + 1 + stepPc (w (base + p)) + stepAc (w (base + p)) ≤ ns ∧ s = stepAt w (base + p) ∧
      StepsAt w base ns (p + 1 + stepPc (w (base + p)) + stepAc (w (base + p))) rest

theorem scanSteps_stepsAt {w : Nat → Nat} {base ns : Nat} :
    ∀ (fuel p nassume : Nat) (bad : Bool) (g : Nat) (rest : List Step) (g' : Nat),
      scanSteps w base ns fuel p nassume bad g = some (rest, g') → StepsAt w base ns p rest := by
  intro fuel
  induction fuel with
  | zero =>
    intro p na bad g rest g' h
    simp only [scanSteps] at h
    split at h
    · rename_i hp
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        exact hp
      · simp at h
    · simp at h
  | succ fuel ih =>
    intro p na bad g rest g' h
    simp only [scanSteps] at h
    split at h
    · rename_i hlt
      split at h
      · rename_i hb
        split at h
        · simp at h
        · rename_i rest0 g0 hrec
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨hlt, hb, rfl, ih _ _ _ _ _ _ hrec⟩
      · simp at h
    · split at h
      · rename_i hp
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, _⟩ := h
          exact hp
        · simp at h
      · simp at h

/-! ## The scanner's forward invariant -/

/-- The scanning loop, started at offset 0 with zeroed accumulators, has
reached offset `p` with accumulators `nassume`, `bad`, `gpos`, having passed
the steps `pre`. -/
inductive ScanInv (w : Nat → Nat) (base ns : Nat) : Nat → Nat → Bool → Nat → List Step → Prop
  | init : ScanInv w base ns 0 0 false 0 []
  | step {p nassume : Nat} {bad : Bool} {gpos : Nat} {pre : List Step} :
    ScanInv w base ns p nassume bad gpos pre → p < ns →
    p + 1 + stepPc (w (base + p)) + stepAc (w (base + p)) ≤ ns →
    ScanInv w base ns (p + 1 + stepPc (w (base + p)) + stepAc (w (base + p)))
      (if stepRule (w (base + p)) = 1 then nassume + 1 else nassume)
      (if stepRule (w (base + p)) = 1 ∧ stepAc (w (base + p)) ≠ 1 then true else bad)
      (if stepRule (w (base + p)) = 1 ∧ stepAc (w (base + p)) = 1
        then w (base + p + 1 + stepPc (w (base + p))) else gpos)
      (pre ++ [stepAt w (base + p)])

theorem ScanInv.le {w : Nat → Nat} {base ns p nassume : Nat} {bad : Bool} {gpos : Nat}
    {pre : List Step} (h : ScanInv w base ns p nassume bad gpos pre) : p ≤ ns := by
  cases h with
  | init => exact Nat.zero_le _
  | step _ _ hb => exact hb

theorem ScanInv.resume {w : Nat → Nat} {base ns p nassume : Nat} {bad : Bool} {gpos : Nat}
    {pre : List Step} (h : ScanInv w base ns p nassume bad gpos pre) :
    ∀ (rest : List Step) (g' : Nat),
      scanSteps w base ns (ns - p) p nassume bad gpos = some (rest, g') →
      scanSteps w base ns ns 0 0 false 0 = some (pre ++ rest, g') := by
  induction h with
  | init => intro rest g' h; simpa using h
  | @step p na bad g pre _ hlt hb ih =>
    intro rest g' h
    have : scanSteps w base ns (ns - p) p na bad g = some (stepAt w (base + p) :: rest, g') := by
      obtain ⟨k, hk⟩ : ∃ k, ns - p = k + 1 := ⟨ns - p - 1, by omega⟩
      rw [hk]
      simp only [scanSteps, hlt, hb, ↓reduceIte]
      rw [scanSteps_fuel k (ns - (p + 1 + stepPc (w (base + p)) + stepAc (w (base + p)))) _ _ _ _
        (by omega) (by omega), h]
    simpa using ih _ _ this

/-- At the end of the loop, the C's final test (`nassume == 1 && !bad`) makes
the scanner succeed with the steps passed and the goal position found. -/
theorem ScanInv.finish {w : Nat → Nat} {base ns : Nat} {gpos : Nat} {steps : List Step}
    (h : ScanInv w base ns ns 1 false gpos steps) :
    scanSteps w base ns ns 0 0 false 0 = some (steps, gpos) := by
  have := h.resume [] gpos (by cases ns <;> simp [scanSteps])
  simpa using this

end Vbcf.Proof
