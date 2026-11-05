import EmbC.Clight.Proof.BehaviorsLemmas

/-!
# Segment property and infinite-run helpers

Generic and independent of EmbC and Clight.  Suppose every pair of related
states `(c, X)` satisfies one of:

* the source silently reaches a stuck, non-final state;
* the source silently reaches a final state, and `X` is final with no step;
* the target deterministically and silently reaches a state `Tb` that can
  step, and every step of `Tb` is matched by a non-empty source run with the
  same trace, ending in related states.

The standard backward simulation is derived from this property in
`BackwardSimulation`; its behavior theorem is proved independently from the
simulation record in `BackwardSimulationBehaviors`.
-/

namespace EmbC.Clight.Behaviors

open CC (E0 Eapp Trace)

section Generic

variable {C₁ R₁ M₁ C₂ R₂ M₂ : Type}

/-- A state that can neither step nor terminate. -/
def Stuck (sem : Semantics C₁ R₁ M₁) (c : C₁) : Prop :=
  (∀ t n, ¬ sem.step c t n) ∧ (∀ r m, ¬ sem.final c r m)

/-- A silent step that is the only step of its source state. -/
def DetStep {C : Type} (step : C → Trace → C → Prop) (x y : C) : Prop :=
  step x E0 y ∧ ∀ t z, step x t z → t = E0 ∧ z = y

inductive DetPath {C : Type} (step : C → Trace → C → Prop) : C → C → Prop where
  | refl (x) : DetPath step x x
  | step {x y z} : DetStep step x y → DetPath step y z → DetPath step x z

/-- A deterministic silent path with its exact length. -/
inductive DetPathN {C : Type} (step : C → Trace → C → Prop) : Nat → C → C → Prop where
  | refl (X) : DetPathN step 0 X X
  | step {n X Y Z} : DetStep step X Y → DetPathN step n Y Z →
      DetPathN step (n + 1) X Z

theorem DetPath.counted {C : Type} {step : C → Trace → C → Prop} {X Y : C}
    (hp : DetPath step X Y) : ∃ n, DetPathN step n X Y := by
  induction hp with
  | refl X => exact ⟨0, .refl X⟩
  | step hd _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, .step hd hn⟩

theorem DetPathN.detPath {C : Type} {step : C → Trace → C → Prop} {n : Nat} {X Y : C}
    (hp : DetPathN step n X Y) : DetPath step X Y := by
  induction hp with
  | refl X => exact .refl X
  | step hd _ ih => exact .step hd ih

/-- The indexed segment relation includes each intermediate target state.
Its index counts the remaining deterministic silent target steps. -/
inductive Seg (S : Semantics C₁ R₁ M₁) (T : Semantics C₂ R₂ M₂)
    (Inv : C₁ → C₂ → Prop) (FR : R₁ → M₁ → R₂ → M₂ → Prop) : Nat → C₁ → C₂ → Prop where
  | error {c X failed} : Star S.step c E0 failed → Stuck S failed →
      Seg S T Inv FR 0 c X
  | final {c X c' r m} : Star S.step c E0 c' → S.final c' r m →
      (∀ t Y, ¬ T.step X t Y) → (∃ r' m', T.final X r' m') →
      (∀ r' m', T.final X r' m' → FR r m r' m') →
      Seg S T Inv FR 0 c X
  | pending {n c X boundary} : DetPathN T.step n X boundary →
      (∃ t Y, T.step boundary t Y) →
      (∀ t Y, T.step boundary t Y → ∃ c', Plus S.step c t c' ∧ Inv c' Y) →
      Seg S T Inv FR n c X

private def InfiniteRun.cons' {C : Type} {step : C → Trace → C → Prop} {s s' : C} {t : Trace}
    (h : step s t s') (run : InfiniteRun step s') : InfiniteRun step s where
  states n := match n with
    | 0 => s
    | n + 1 => run.states n
  traces n := match n with
    | 0 => t
    | n + 1 => run.traces n
  initial := rfl
  steps n := match n with
    | 0 => by simpa [run.initial] using h
    | n + 1 => run.steps n

private theorem InfiniteRun.cons'_prefix {C : Type} {step : C → Trace → C → Prop} {s s' : C}
    {t : Trace} (h : step s t s') (run : InfiniteRun step s') (n : Nat) :
    (InfiniteRun.cons' h run).prefix (n + 1) = t ++ run.prefix n := by
  induction n with
  | zero => simp [InfiniteRun.prefix, InfiniteRun.cons', Eapp, E0]
  | succ n ih =>
    show Eapp ((InfiniteRun.cons' h run).prefix (n + 1)) _ = _
    rw [ih]
    simp [InfiniteRun.prefix, InfiniteRun.cons', Eapp, List.append_assoc]

/-- Prepending a finite run to an eventually silent infinite run. -/
theorem star_silent_run {C : Type} {step : C → Trace → C → Prop} {s s' : C} {t : Trace}
    (hs : Star step s t s') (run : InfiniteRun step s') (hsil : ∀ n, run.traces n = E0) :
    ∃ run' : InfiniteRun step s, ∃ k0, run'.prefix k0 = t ∧
      ∀ k, k0 ≤ k → run'.traces k = E0 := by
  induction hs with
  | refl => exact ⟨run, 0, rfl, fun k _ => hsil k⟩
  | @step s₁ s₂ s₃ t₁ t₂ a _ ih =>
    obtain ⟨run', k0, hk0, hsil'⟩ := ih run hsil
    refine ⟨InfiniteRun.cons' a run', k0 + 1, ?_, ?_⟩
    · rw [InfiniteRun.cons'_prefix, hk0]; rfl
    · intro k hk
      cases k with
      | zero => omega
      | succ k => exact hsil' k (by omega)

/-- An infinite run whose trace eventually stops growing describes divergence. -/
theorem diverges_of_run {sem : Semantics C₁ R₁ M₁} {c : C₁} {t : Trace}
    (run : InfiniteRun sem.step c) (hle : ∀ k, run.prefix k <+: t)
    (hge : ∃ k, t <+: run.prefix k) : Behaves sem c (.diverges t) := by
  obtain ⟨k1, hk1⟩ := hge
  have heq : ∀ k, k1 ≤ k → run.prefix k = t := by
    intro k hk
    exact ((hk1.trans (run.prefix_mono hk))).eq_of_length
      (Nat.le_antisymm (hk1.trans (run.prefix_mono hk)).length_le (hle k).length_le) |>.symm
  refine ⟨run.states k1, by rw [← heq k1 (Nat.le_refl _)]; exact run.star_prefix k1,
    run.drop k1, fun n => ?_⟩
  have h1 := heq (k1 + n + 1) (by omega)
  have h2 := heq (k1 + n) (by omega)
  rw [InfiniteRun.prefix_succ, h2] at h1
  show run.traces (k1 + n) = E0
  simpa [E0] using h1

end Generic

end EmbC.Clight.Behaviors
