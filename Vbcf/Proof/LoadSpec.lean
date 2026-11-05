import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.LoadSpec4

/-!
# Vbcf proofs: the one-pass loader refines the Lean loader

The bridge between the C's one-pass loading of a proof (`ck_load`, `ck_scan`)
and the Lean checker's multi-pass loading (`Bcf.decode`, `Bcf.canonicalize`,
`Bcf.positionMap`, `Bcf.findGoal`).

* `LoadSpec1` — the definitions: `wordsToBytes`, `posOfW`, `loadNode`,
  `loadExprs`, `scanSteps`.
* `LoadSpec2` — basic lemmas and the loader's forward invariant `LoadInv`.
* `LoadSpec3` — each Lean pass, from a successful incremental run.
* `LoadSpec4` — the step scanner, `ScanInv`, `StepsAt`.
* this file — `load_bridge` and `check_of_load`.
-/

namespace Vbcf.Proof

variable {State : Type}
open Bcf
set_option autoImplicit false

/-! ## The whole decoder -/

theorem decode_spec {ws : Array (BitVec 32)} {st1 : St} {D : Nat} {T : Loaded} {steps : List Step}
    {gpos fuelS : Nat}
    (hsz : 3 ≤ ws.size) (hmagic : wordFn ws 0 = 0x0BCF) (hne : wordFn ws 1 ≠ 0)
    (hns : 2 ≤ wordFn ws 2) (hlen : 3 + wordFn ws 1 + wordFn ws 2 = ws.size)
    (hT : specN (wordFn ws) st1 D = some T) (hD : posOfW (wordFn ws) D = wordFn ws 1)
    (hscan : scanSteps (wordFn ws) (3 + wordFn ws 1) (wordFn ws 2) fuelS 0 0 false 0 =
      some (steps, gpos)) :
    decode (wordsToBytes ws) = .ok ⟨T.dense, steps.toArray⟩ := by
  have h0 : u32At (wordsToBytes ws) 0 = wordFn ws 0 := LoadSpec.u32At_word ws 0 0 rfl (by omega)
  have h1 : u32At (wordsToBytes ws) 4 = wordFn ws 1 := LoadSpec.u32At_word ws 4 1 rfl (by omega)
  have h2 : u32At (wordsToBytes ws) 8 = wordFn ws 2 := LoadSpec.u32At_word ws 8 2 rfl (by omega)
  have hE := decodeExprs_spec hT hD (by omega)
  have hDn := densify_spec hT
  have hS : decodeSteps (wordsToBytes ws) (12 + 4 * wordFn ws 1) (wordFn ws 2) = some steps.toArray := by
    unfold decodeSteps
    have := scanSteps_decode (ws := ws) (ne := wordFn ws 1) (ns := wordFn ws 2) (stop := 12 + 4 * wordFn ws 1 + 4 * wordFn ws 2) (by omega) (by omega) _ _ _ _ _ _ _ hscan
      (wordFn ws 2 + 1) (12 + 4 * wordFn ws 1) #[] (by omega) (by omega)
    simpa using this
  have c1 : ¬ (4 * ws.size < 12 ∨ 4 * ws.size % 4 ≠ 0) := by omega
  have c3 : ¬ (wordFn ws 1 = 0 ∨ wordFn ws 2 < 2) := by omega
  have c4 : ¬ (12 + 4 * (wordFn ws 1 + wordFn ws 2) ≠ 4 * ws.size) := by omega
  unfold decode
  simp only [wordsToBytes_size, h0, h1, h2, hmagic, hE, hDn, hS, c1, c3, c4, ↓reduceIte, ne_eq,
    not_true_eq_false]
  rfl

/-! ## Facts about the loader's state -/

theorem LoadInv.pos {w : Nat → Nat} {st1 : St} {p d : Nat} {st : St} {pm : Nat → Option Nat}
    (h : LoadInv w st1 p d st pm) : p = posOfW w d := h.1

/-- The position map knows exactly the positions of the expressions loaded so far. -/
theorem LoadInv.pm_eq_some {w : Nat → Nat} {st1 : St} {p d : Nat} {st : St} {pm : Nat → Option Nat}
    (h : LoadInv w st1 p d st pm) {a i : Nat} (hi : pm a = some i) :
    ∃ j, j < d ∧ a = posOfW w j ∧ i < st.pool.size := by
  obtain ⟨_, t, ht, rfl, hpm⟩ := h
  rw [hpm a, pmOf, (specN_sizes ht).2.2] at hi
  cases hj : idxOf w d a with
  | none => rw [hj] at hi; simp at hi
  | some j =>
    rw [hj] at hi
    obtain ⟨hjd, hja⟩ := (idxOf_eq_some w _ _ _).1 hj
    obtain ⟨t0, t', rn, dargs, cargs, r, _, _, _, _, _, _, hp, _, _, _, _, _, hr, hsz⟩ := specN_at ht hjd
    simp only [Option.bind_some] at hi
    rw [hr] at hi; simp only [Option.some.injEq] at hi; subst hi
    exact ⟨j, hjd, hja.symm, Nat.lt_of_lt_of_le (pushNode_size hp).2 hsz⟩

theorem LoadInv.pm_lt {w : Nat → Nat} {st1 : St} {p d : Nat} {st : St} {pm : Nat → Option Nat}
    (h : LoadInv w st1 p d st pm) {a i : Nat} (hi : pm a = some i) : i < st.pool.size := by
  obtain ⟨_, _, _, h'⟩ := h.pm_eq_some hi; exact h'

theorem LoadInv.pm_none {w : Nat → Nat} {st1 : St} {p d : Nat} {st : St} {pm : Nat → Option Nat}
    (h : LoadInv w st1 p d st pm) {a : Nat} (ha : p ≤ a) : pm a = none := by
  cases hi : pm a with
  | none => rfl
  | some i =>
    obtain ⟨j, hjd, hja, _⟩ := h.pm_eq_some hi
    have := posOfW_strictMono w hjd
    have := h.pos
    omega

theorem LoadInv.pm_pos {w : Nat → Nat} {st1 : St} {p d : Nat} {st : St} {pm : Nat → Option Nat}
    (h : LoadInv w st1 p d st pm) {j : Nat} (hj : j < d) : ∃ i, pm (posOfW w j) = some i := by
  obtain ⟨_, t, ht, rfl, hpm⟩ := h
  obtain ⟨t0, t', rn, dargs, cargs, r, _, _, _, _, _, _, _, _, _, _, _, _, hr, _⟩ := specN_at ht hj
  refine ⟨r, ?_⟩
  rw [hpm, pmOf, (specN_sizes ht).2.2, idxOf_posOfW w hj]
  exact hr

theorem reidx_var (o : Op) (d : Nat) :
    (∀ wd id, reidx o d = .bvVar wd id → id = d) ∧ (∀ id, reidx o d = .boolVar id → id = d) := by
  cases o <;> simp [reidx] <;> intros <;> simp_all

/-! ## The bridge -/

/-- What the bridge delivers: the Lean loader's results `P` and `remap` for
the bytes of `ws`, and how they relate to the one-pass loader's results `st2`,
`pm` (after `D` expressions), `steps` and `gpos`. -/
structure LoadBridge (ws : Array (BitVec 32)) (st1 st2 : St) (pm : Nat → Option Nat)
    (steps : List Step) (gpos : Nat) (D : Nat) (P : RawProof) (remap : Array Nat) : Prop where
  /-- the Lean decoder accepts the bytes -/
  decode_ok : Bcf.decode (wordsToBytes ws) = .ok P
  /-- canonicalisation of the decoded pool gives the loader's state -/
  canon : canonicalize P.pool st1 = some (st2, remap)
  /-- the loader's position map is the Lean checker's `exprIdx` -/
  ei : ∀ p, Bcf.exprIdx (positionMap P.pool) remap p = pm p
  steps_eq : P.steps.toList = steps
  goal : findGoal P.steps = some gpos
  /-- there are `D` expressions, and they fill the expression section -/
  size : P.pool.size = D
  remap_size : remap.size = D
  pos_end : posOfW (wordFn ws) D = wordFn ws 1
  /-- the `d`-th expression is the one at position `posOfW w d` -/
  posmap : ∀ p, (positionMap P.pool)[p]? = idxOf (wordFn ws) D p
  pm_pos : ∀ d : Nat, d < D → pm (posOfW (wordFn ws) d) = remap[d]?
  /-- variables are identified by their dense index -/
  var_id : ∀ (d : Nat) (n : Node), P.pool[d]? = some n →
    (∀ wd id, n.op = .bvVar wd id → id = d) ∧ (∀ id, n.op = .boolVar id → id = d)
  pm_none : ∀ p, wordFn ws 1 ≤ p → pm p = none
  pm_lt : ∀ (p i : Nat), pm p = some i → i < st2.pool.size

/-- **The bridge**, from the loader's forward invariant at the end of the
expression section. -/
theorem load_bridge_inv {ws : Array (BitVec 32)} {st1 st2 : St} {pm : Nat → Option Nat}
    {steps : List Step} {gpos D fuelS : Nat}
    (hsz : 3 ≤ ws.size) (hmagic : wordFn ws 0 = 0x0BCF) (hne : wordFn ws 1 ≠ 0)
    (hns : 2 ≤ wordFn ws 2) (hlen : 3 + wordFn ws 1 + wordFn ws 2 = ws.size)
    (hload : LoadInv (wordFn ws) st1 (wordFn ws 1) D st2 pm)
    (hscan : scanSteps (wordFn ws) (3 + wordFn ws 1) (wordFn ws 2) fuelS 0 0 false 0 =
      some (steps, gpos)) :
    ∃ (P : RawProof) (remap : Array Nat), LoadBridge ws st1 st2 pm steps gpos D P remap := by
  have hload' := hload
  obtain ⟨hD, T, hT, rfl, hpm⟩ := hload
  obtain ⟨_, hds, hrs⟩ := specN_sizes hT
  have hpm' : ∀ p, Bcf.exprIdx (positionMap T.dense) T.remap p = pm p := by
    intro p
    rw [hpm p, Bcf.exprIdx, positionMap_spec hT, pmOf, hrs]
  refine ⟨⟨T.dense, steps.toArray⟩, T.remap,
    decode_spec hsz hmagic hne hns hlen hT hD.symm hscan, canonicalize_spec hT, hpm', rfl,
    scanSteps_findGoal hscan, hds, hrs, hD.symm, positionMap_spec hT, ?_, ?_,
    fun p hp => hload'.pm_none hp, fun p i hi => hload'.pm_lt hi⟩
  · intro d hd
    rw [hpm, pmOf, hrs, idxOf_posOfW _ hd]; rfl
  · intro d n hn
    have hn' : T.dense[d]? = some n := hn
    have hd : d < D := by
      rcases Nat.lt_or_ge d T.dense.size with h' | h'
      · omega
      · rw [Array.getElem?_eq_none h'] at hn'; cases hn'
    obtain ⟨t0, t', rn, dargs, cargs, r, _, _, _, _, _, _, _, _, _, _, _, hTd, _⟩ := specN_at hT hd
    rw [hTd] at hn'
    simp only [Option.some.injEq] at hn'; subst hn'
    exact reidx_var rn.op d

/-- **The bridge**: if the header checks pass, the one-pass expression loader
returns `(st2, pm)` and the step scanner returns `(steps, gpos)`, then the
Lean decoder accepts the bytes of `ws`, and canonicalising its pool gives
`st2`, with `pm` as the position-to-canonical-index map. -/
theorem load_bridge {ws : Array (BitVec 32)} {st1 st2 : St} {pm : Nat → Option Nat}
    {steps : List Step} {gpos fuelE fuelS : Nat}
    (hsz : 3 ≤ ws.size) (hmagic : wordFn ws 0 = 0x0BCF) (hne : wordFn ws 1 ≠ 0)
    (hns : 2 ≤ wordFn ws 2) (hlen : 3 + wordFn ws 1 + wordFn ws 2 = ws.size)
    (hload : loadExprs (wordFn ws) (wordFn ws 1) fuelE 0 0 st1 (fun _ => none) = some (st2, pm))
    (hscan : scanSteps (wordFn ws) (3 + wordFn ws 1) (wordFn ws 2) fuelS 0 0 false 0 =
      some (steps, gpos)) :
    ∃ (D : Nat) (P : RawProof) (remap : Array Nat), LoadBridge ws st1 st2 pm steps gpos D P remap := by
  obtain ⟨D, hinv⟩ := loadExprs_inv _ _ _ _ _ (LoadInv.init _ st1) hload
  exact ⟨D, load_bridge_inv hsz hmagic hne hns hlen hinv hscan⟩

/-! ## The checker -/

/-- What `Bcf.check` computes, in terms of the one-pass loader's results:
replay the scanned steps from the loaded state, with the loader's position map
as `ei`, and compare the last fact with `false`.  The result is the dense
index of the goal expression. -/
theorem check_of_bridge {ws : Array (BitVec 32)} {st0 st1 st2 : St} {tt ff : Nat}
    {pm : Nat → Option Nat} {steps : List Step} {gpos D : Nat} {P : RawProof} {remap : Array Nat}
    (tbl : Nat → Option RwRule)
    (htt : pushNode initSt ⟨.boolVal true, #[]⟩ = some (st0, tt))
    (hff : pushNode st0 ⟨.boolVal false, #[]⟩ = some (st1, ff))
    (hb : LoadBridge ws st1 st2 pm steps gpos D P remap) :
    check tbl P =
      match pm gpos with
      | none => none
      | some g =>
        match replay tbl g ⟨tt, ff⟩ pm steps st2 with
        | none => none
        | some st3 =>
          match st3.facts[st3.facts.size - 1]? with
          | some last => if last = ff then idxOf (wordFn ws) D gpos else none
          | none => none := by
  have hei : Bcf.exprIdx (positionMap P.pool) remap = pm := funext hb.ei
  have hg := hb.ei gpos
  unfold check checkWith
  simp only [htt, hff, hb.canon, hb.goal, hei, hb.steps_eq]
  unfold Bcf.exprIdx at hg
  rw [← hb.posmap gpos]
  cases hi : (positionMap P.pool)[gpos]? with
  | none => rw [hi] at hg; rw [← hg]; rfl
  | some graw =>
    rw [hi] at hg
    simp only [Option.bind_some] at hg
    rw [← hg]
    dsimp only
    cases hr : remap[graw]? <;> rfl

/-- **The Lean checker accepts** when the replay of the scanned steps from the
loaded state ends with the fact `false`. -/
theorem check_of_load {ws : Array (BitVec 32)} {st0 st1 st2 st3 : St} {tt ff g : Nat}
    {pm : Nat → Option Nat} {steps : List Step} {gpos fuelE fuelS : Nat}
    (tbl : Nat → Option RwRule)
    (hsz : 3 ≤ ws.size) (hmagic : wordFn ws 0 = 0x0BCF) (hne : wordFn ws 1 ≠ 0)
    (hns : 2 ≤ wordFn ws 2) (hlen : 3 + wordFn ws 1 + wordFn ws 2 = ws.size)
    (htt : pushNode initSt ⟨.boolVal true, #[]⟩ = some (st0, tt))
    (hff : pushNode st0 ⟨.boolVal false, #[]⟩ = some (st1, ff))
    (hload : loadExprs (wordFn ws) (wordFn ws 1) fuelE 0 0 st1 (fun _ => none) = some (st2, pm))
    (hscan : scanSteps (wordFn ws) (3 + wordFn ws 1) (wordFn ws 2) fuelS 0 0 false 0 =
      some (steps, gpos))
    (hgoal : pm gpos = some g)
    (hreplay : replay tbl g ⟨tt, ff⟩ pm steps st2 = some st3)
    (hlast : st3.facts[st3.facts.size - 1]? = some ff) :
    ∃ (P : RawProof) (graw : Nat), Bcf.decode (wordsToBytes ws) = .ok P ∧ check tbl P = some graw := by
  obtain ⟨D, P, remap, hb⟩ := load_bridge hsz hmagic hne hns hlen hload hscan
  have hc := check_of_bridge tbl htt hff hb
  simp only [hgoal, hreplay, hlast, ↓reduceIte] at hc
  have hg := hb.ei gpos
  rw [hgoal, Bcf.exprIdx, hb.posmap] at hg
  cases hi : idxOf (wordFn ws) D gpos with
  | none => rw [hi] at hg; simp at hg
  | some graw => exact ⟨P, graw, hb.decode_ok, by rw [hc, hi]⟩

end Vbcf.Proof
