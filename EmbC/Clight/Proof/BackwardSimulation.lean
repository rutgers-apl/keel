import EmbC.Clight.Proof.Backward

/-!
# A stepwise backward simulation from deterministic segments

The simulation diagram and local safety guard follow CompCert's
`Smallstep.bsim_properties`. Initial states are explicit predicates and final
results/memories are related by `FR`, since these traced semantics do not carry
CompCert's symbol environments or a common integer result type. Program/symbol
representation is supplied separately by the embedding's `ProgramRel`.

`Seg` includes the intermediate target states of a segment, not just
the pairs in `Inv`. Its natural-number index counts the remaining deterministic
target steps. Each such step stutters in the source and decreases the index;
the boundary step is matched by a non-empty source run and prepares a new
segment. Source errors are permitted in the relation, but cannot satisfy the
local safety guard.
-/

namespace EmbC.Clight.Behaviors

open CC (E0 Trace)

variable {C₁ R₁ M₁ C₂ R₂ M₂ : Type}

/-- CompCert's local safety: every silently reachable state is final or can
step. This is not a global assumption excluding errors after future events. -/
def Safe (S : Semantics C₁ R₁ M₁) (c : C₁) : Prop :=
  ∀ c', Star S.step c E0 c' →
    (∃ r m, S.final c' r m) ∨ ∃ t c'', S.step c' t c''

/-- The standard backward diagram: one target step is matched by source
progress, or by a source star with a strictly decreasing well-founded index.
The initial-state clauses follow CompCert's `bsim_match_initial_states`. -/
structure BackwardSimulation (S : Semantics C₁ R₁ M₁) (T : Semantics C₂ R₂ M₂)
    (sourceInitial : C₁ → Prop) (targetInitial : C₂ → Prop)
    (FR : R₁ → M₁ → R₂ → M₂ → Prop) (Index : Type) where
  order : Index → Index → Prop
  order_wf : WellFounded order
  matchStates : Index → C₁ → C₂ → Prop
  initial_states_exist : ∀ c, sourceInitial c → ∃ X, targetInitial X
  match_initial_states : ∀ c X, sourceInitial c → targetInitial X →
    ∃ i c', sourceInitial c' ∧ matchStates i c' X
  match_final_states : ∀ i c X r' m', matchStates i c X → Safe S c →
    T.final X r' m' → ∃ c' r m,
      Star S.step c E0 c' ∧ S.final c' r m ∧ FR r m r' m'
  progress : ∀ i c X, matchStates i c X → Safe S c →
    (∃ r m, T.final X r m) ∨ ∃ t X', T.step X t X'
  simulation : ∀ X t X', T.step X t X' → ∀ i c,
    matchStates i c X → Safe S c → ∃ i' c',
      (Plus S.step c t c' ∨ (Star S.step c t c' ∧ order i' i)) ∧
      matchStates i' c' X'

variable (S : Semantics C₁ R₁ M₁) (T : Semantics C₂ R₂ M₂)
  (Inv : C₁ → C₂ → Prop) (FR : R₁ → M₁ → R₂ → M₂ → Prop)

variable {S T Inv FR}

theorem Safe.not_silent_stuck {c failed : C₁} (hs : Safe S c)
    (hp : Star S.step c E0 failed) (hf : Stuck S failed) : False := by
  rcases hs failed hp with ⟨r, m, hr⟩ | ⟨t, c', ht⟩
  · exact hf.2 r m hr
  · exact hf.1 t c' ht

theorem Seg.progress {n c X} (h : Seg S T Inv FR n c X)
    (hs : Safe S c) : (∃ r m, T.final X r m) ∨ ∃ t Y, T.step X t Y := by
  cases h with
  | error hp hf => exact (hs.not_silent_stuck hp hf).elim
  | final _ _ _ hex _ => exact .inl hex
  | pending hp hex _ =>
    right
    cases hp with
    | refl => exact hex
    | step hd _ => exact ⟨E0, _, hd.1⟩

theorem Seg.match_final
    (hnostep : ∀ X r m, T.final X r m → ∀ t Y, ¬ T.step X t Y)
    {n c X r' m'} (h : Seg S T Inv FR n c X) (hs : Safe S c)
    (hf : T.final X r' m') :
    ∃ c' r m, Star S.step c E0 c' ∧ S.final c' r m ∧ FR r m r' m' := by
  cases h with
  | error hp hst => exact (hs.not_silent_stuck hp hst).elim
  | final hp hfin _ _ hfr => exact ⟨_, _, _, hp, hfin, hfr _ _ hf⟩
  | pending hp hex _ =>
    cases hp with
    | refl => obtain ⟨t, Y, ht⟩ := hex; exact (hnostep _ _ _ hf t Y ht).elim
    | step hd _ => exact (hnostep _ _ _ hf E0 _ hd.1).elim

/-- The stepwise diagram, including target-only silent steps inside a segment.
An arbitrary boundary outcome is handled by `hall`; no target determinism
assumption is made at that boundary. -/
theorem Seg.simulation (hseg : ∀ c X, Inv c X → ∃ n, Seg S T Inv FR n c X)
    {X t X'} (ht : T.step X t X') {n c} (h : Seg S T Inv FR n c X)
    (hs : Safe S c) : ∃ n' c',
      (Plus S.step c t c' ∨ (Star S.step c t c' ∧ n' < n)) ∧
      Seg S T Inv FR n' c' X' := by
  cases h with
  | error hp hf => exact (hs.not_silent_stuck hp hf).elim
  | final _ _ hn _ _ => exact (hn t X' ht).elim
  | pending hp hex hall =>
    cases hp with
    | refl =>
      obtain ⟨c', hp', hi⟩ := hall _ _ ht
      obtain ⟨n', hm⟩ := hseg _ _ hi
      exact ⟨n', c', .inl hp', hm⟩
    | @step k X Y boundary hd tail =>
      obtain ⟨rfl, rfl⟩ := hd.2 _ _ ht
      exact ⟨k, c, .inr ⟨Star.refl c, by omega⟩, .pending tail hex hall⟩

/-- Convert the segment argument to a standard well-founded backward
simulation. Initial states and final-state non-stepping are the usual separate
obligations; all intermediate matching and stuttering is derived here. -/
def backwardSimulation_of_segments
    (hseg : ∀ c X, Inv c X → ∃ n, Seg S T Inv FR n c X)
    (hnostep : ∀ X r m, T.final X r m → ∀ t Y, ¬ T.step X t Y)
    (sourceInitial : C₁ → Prop) (targetInitial : C₂ → Prop)
    (hex : ∀ c, sourceInitial c → ∃ X, targetInitial X)
    (hinit : ∀ c X, sourceInitial c → targetInitial X →
      ∃ c', sourceInitial c' ∧ Inv c' X) :
    BackwardSimulation S T sourceInitial targetInitial FR Nat where
  order := Nat.lt
  order_wf := Nat.lt_wfRel.wf
  matchStates := Seg S T Inv FR
  initial_states_exist := hex
  match_initial_states := by
    intro c X hc hX
    obtain ⟨c', hc', hi⟩ := hinit c X hc hX
    obtain ⟨n, hn⟩ := hseg _ _ hi
    exact ⟨n, c', hc', hn⟩
  match_final_states := fun _ _ _ _ _ h hs hf => h.match_final hnostep hs hf
  progress := fun _ _ _ h hs => h.progress hs
  simulation := fun _ _ _ ht _ _ h hs => h.simulation hseg ht hs

end EmbC.Clight.Behaviors
