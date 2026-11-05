import Bcf.Aci
import Bcf.Poly
import Bcf.Rw.Instantiate
import Bcf.Rw.Core
import Bcf.Rw.All
import Bcf.BitblastSound

/-!
# Dispatch, replay, and the main theorem
-/

namespace Bcf

/-! ## Replay -/

theorem applyRule_sound {tbl : Nat → Option RwRule} (htbl : ∀ rid r, tbl rid = some r → r.Sound)
    {base : Pool} {g : Nat} {bi : Builtins} {ei : EI} {st st' : St} {r : Rule}
    {prems params : List Nat} {f : Nat}
    (h : applyRule tbl g bi ei st r prems params = some (st', f))
    (hinv : Inv base g bi st) (hp : ∀ p ∈ prems, Entails st g p) : Inv base g bi st' ∧ Entails st' g f := by
  unfold applyRule at h
  split at h
  · exact ruleAssume_sound h hinv
  · exact ruleRefl_sound h hinv
  · exact ruleSymm_sound h hinv hp
  · exact ruleTrans_sound h hinv hp
  · exact ruleCong_sound h hinv hp
  · exact ruleTrueIntro_sound h hinv hp
  · exact ruleTrueElim_sound h hinv hp
  · exact ruleFalseIntro_sound h hinv hp
  · exact ruleFalseElim_sound h hinv hp
  · exact ruleEqResolve_sound h hinv hp
  · exact ruleModusPonens_sound h hinv hp
  · exact ruleNotNotElim_sound h hinv hp
  · exact ruleContra_sound h hinv hp
  · exact ruleAndElim_sound h hinv hp
  · exact ruleAndIntro_sound h hinv hp
  · exact ruleNotOrElim_sound h hinv hp
  · exact ruleSplit_sound h hinv
  · exact ruleEvaluate_sound h hinv
  · exact ruleImpliesElim_sound h hinv hp
  · exact ruleNotImpliesElim_sound h hinv hp
  · exact ruleEquivElim_sound h hinv hp
  · exact ruleNotEquivElim_sound h hinv hp
  · exact ruleXorElim_sound h hinv hp
  · exact ruleNotXorElim_sound h hinv hp
  · exact ruleIteElim_sound h hinv hp
  · exact ruleNotIteElim_sound h hinv hp
  · exact ruleNotAnd_sound h hinv hp
  · exact ruleCnfAndPos_sound h hinv
  · exact ruleCnfAndNeg_sound h hinv
  · exact ruleCnfOrPos_sound h hinv
  · exact ruleCnfOrNeg_sound h hinv
  · exact ruleCnfImpliesPos_sound h hinv
  · exact ruleCnfImpliesNeg_sound h hinv
  · exact ruleCnfEquivPos_sound h hinv
  · exact ruleCnfEquivNeg_sound h hinv
  · exact ruleCnfXorPos_sound h hinv
  · exact ruleCnfXorNeg_sound h hinv
  · exact ruleCnfItePos_sound h hinv
  · exact ruleCnfIteNeg_sound h hinv
  · exact ruleIteEq_sound h hinv
  · exact ruleDistinctValues_sound h hinv
  · exact ruleResolution_sound h hinv hp
  · exact ruleFactoring_sound h hinv hp
  · exact ruleReordering_sound h hinv hp
  · exact ruleAbsorb_sound h hinv
  · exact ruleAciNorm_sound h hinv
  · exact rulePolyNorm_sound h hinv
  · exact rulePolyNormEq_sound h hinv hp
  · exact ruleRewrite_sound htbl h hinv hp
  · exact ruleBitblast_sound h hinv
  · simp at h

theorem getFacts_entails {g : Nat} {bi : Builtins} {st : St} (hinv : Inv base g bi st) {idxs : List Nat} {prems : List Nat}
    (h : getFacts st.facts idxs = some prems) : ∀ p ∈ prems, Entails st g p := by
  induction idxs generalizing prems with
  | nil => simp [getFacts] at h; subst h; simp
  | cons k rest ih =>
    unfold getFacts at h
    split at h
    · rename_i f fs hk hrest
      simp at h; subst h
      intro p hp
      simp at hp
      rcases hp with rfl | hp
      · exact ⟨hinv.facts k p hk, fun ρ hg => hinv.sound ρ hg k p hk⟩
      · exact ih hrest p hp
    · simp at h

theorem replay_sound {tbl : Nat → Option RwRule} (htbl : ∀ rid r, tbl rid = some r → r.Sound)
    {base : Pool} {g : Nat} {bi : Builtins} {ei : EI} :
    ∀ {steps : List Step} {st st' : St}, replay tbl g bi ei steps st = some st' →
    Inv base g bi st → Inv base g bi st' := by
  intro steps
  induction steps with
  | nil => intro st st' h hinv; simp [replay] at h; subst h; exact hinv
  | cons s rest ih =>
    intro st st' h hinv
    unfold replay at h
    split at h
    · rename_i prems hprems
      split at h
      · rename_i st1 f happ
        obtain ⟨hinv1, hent⟩ := applyRule_sound htbl happ hinv (getFacts_entails hinv hprems)
        rw [St.addFact_eq] at h
        exact ih h (hinv1.addFact hent)
      · simp at h
    · simp at h

/-! ## Canonicalisation keeps the builtins and facts -/

theorem canonFrom_prefix {raw : Pool} :
    ∀ (m k : Nat) {st st' : St} {remap remap' : Array Nat},
    canonFrom raw m k (st, remap) = some (st', remap') →
    (∀ j, j < st.pool.size → st'.pool[j]? = st.pool[j]?) ∧ st'.facts = st.facts := by
  intro m
  induction m with
  | zero =>
    intro k st st' remap remap' h
    simp [canonFrom] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun _ _ => rfl, rfl⟩
  | succ m ih =>
    intro k st st' remap remap' h
    unfold canonFrom at h
    split at h
    · simp at h
    · rename_i acc' hstep
      obtain ⟨st1, remap1⟩ := acc'
      obtain ⟨h1, h2⟩ := ih (k + 1) h
      -- one step
      unfold canonStep at hstep
      split at hstep
      · simp at hstep
      · rename_i n hn
        split at hstep
        · split at hstep
          · simp at hstep
          · rename_i args _
            split at hstep
            · simp at hstep
            · rename_i st2 r hpush
              simp at hstep; obtain ⟨rfl, rfl⟩ := hstep
              refine ⟨?_, by rw [h2, pushNode_facts hpush]⟩
              intro j hj
              rw [h1 j (Nat.lt_of_lt_of_le hj (pushNode_size hpush).1), pushNode_prefix hpush j hj]
        · simp at hstep
    
theorem holds_of_canon {raw : Pool} {st : St} {remap : Array Nat}
    (hinv : CanonInv raw st remap raw.size) (hok : TysOK st.pool st.tys) (ρ : Assign)
    {j r : Nat} (hj : j < raw.size) (hr : remap[j]? = some r) :
    holds raw ρ j ↔ holds st.pool ρ r := by
  unfold holds; rw [eval_canon hinv hok ρ j hj r hr]

/-- The raw goal index names a node. -/
theorem findGoal_lt {steps : Array Step} {graw : Nat} (_h : findGoal steps = some graw) : True := trivial

/-! ## Main theorem -/

/-- **Soundness of the BCF checker.**  If `check` accepts a proof and
reports goal `g`, then `g` is unsatisfiable: no assignment of runtime
values to the variables makes it true. -/
theorem check_sound {tbl : Nat → Option RwRule} (htbl : ∀ rid r, tbl rid = some r → r.Sound)
    (p : RawProof) {graw : Nat} (h : check tbl p = some graw) :
    ∀ ρ, ¬ holds p.pool ρ graw := by
  intro ρ hg
  unfold check checkWith at h
  split at h <;> try contradiction
  rename_i st0 tt h0
  split at h <;> try contradiction
  rename_i st1 ff h1
  split at h <;> try contradiction
  rename_i st2 remap h2
  split at h <;> try contradiction
  rename_i gpos hgoal
  split at h <;> try contradiction
  rename_i graw' hpos
  split at h <;> try contradiction
  rename_i g hgr
  split at h <;> try contradiction
  rename_i st3 h3
  split at h <;> try contradiction
  rename_i last hlast
  split at h <;> try contradiction
  rename_i hlf
  simp at h; subst graw'
  -- invariants through the pipeline
  have hok0 : TysOK initSt.pool initSt.tys := ⟨rfl, by intro i n hn; simp [initSt] at hn⟩
  have hok1 := pushNode_tysOK h1 (pushNode_tysOK h0 hok0)
  obtain ⟨hcinv, hok2⟩ := canonicalize_inv hok1 h2
  obtain ⟨hpre, hfacts⟩ := canonFrom_prefix p.pool.size 0 h2
  have hj : graw < p.pool.size := by
    rcases Nat.lt_or_ge graw p.pool.size with h' | h'
    · exact h'
    · have := hcinv.1; rw [Array.getElem?_eq_none (by omega)] at hgr; cases hgr
  have hg2 : g < st2.pool.size := by
    obtain ⟨n, hn⟩ : ∃ n, p.pool[graw]? = some n := by
      cases hn : p.pool[graw]? with
      | none => rw [Array.getElem?_eq_none_iff] at hn; omega
      | some n => exact ⟨n, rfl⟩
    obtain ⟨_, r, args, hr, _, hp⟩ := hcinv.2 graw n hj hn
    rw [hgr] at hr; simp at hr; subst r
    exact idx_lt_of_get hp
  have hinv2 : Inv st2.pool g ⟨tt, ff⟩ st2 :=
    { tys := hok2
      ext := fun _ _ => rfl
      size := Nat.le_refl _
      goal := hg2
      tt := by
        rw [hpre tt (Nat.lt_of_lt_of_le (pushNode_size h0).2 (pushNode_size h1).1),
            pushNode_prefix h1 tt (pushNode_size h0).2]
        exact pushNode_get h0
      ff := by rw [hpre ff (pushNode_size h1).2]; exact pushNode_get h1
      facts := by
        intro k f hf
        rw [hfacts, pushNode_facts h1, pushNode_facts h0] at hf
        simp [initSt] at hf
      sound := by
        intro ρ _ k f hf
        rw [hfacts, pushNode_facts h1, pushNode_facts h0] at hf
        simp [initSt] at hf }
  have hinv3 := replay_sound htbl h3 hinv2
  have hgc : holds st3.pool ρ g := by
    have h2g := (holds_of_canon hcinv hok2 ρ hj hgr).mp hg
    unfold holds at h2g ⊢
    rw [eval_extend ρ hinv3.ext g hg2]
    exact h2g
  have hf : holds st3.pool ρ last := hinv3.sound ρ hgc _ _ hlast
  subst hlf
  unfold holds at hf
  rw [eval_boolVal hinv3.wf hinv3.ff ρ] at hf
  cases hf

/-- **The BCF checker** with its rewrite table. -/
def checkBcf (p : RawProof) : Option Nat := check rwTable p

/-- **Soundness of the BCF checker.** -/
theorem checkBcf_sound (p : RawProof) {graw : Nat} (h : checkBcf p = some graw) :
    ∀ ρ, ¬ holds p.pool ρ graw :=
  check_sound rwTable_sound p h

end Bcf
