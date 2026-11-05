import EmbC.Clight.Proof.BehaviorsLemmas

/-! A standalone forward simulation, including initial and final states. -/

namespace EmbC.Clight.Behaviors

variable {C₁ R₁ M₁ C₂ R₂ M₂ : Type}

/-- CompCert-style forward simulation with the existing well-founded natural
stuttering index, initial-state matching and represented final outcomes.
Program/symbol representation remains the embedding's separate `ProgramRel`. -/
structure ForwardSimulation (S : Semantics C₁ R₁ M₁) (T : Semantics C₂ R₂ M₂)
    (sourceInitial : C₁ → Prop) (targetInitial : C₂ → Prop)
    (FR : R₁ → M₁ → R₂ → M₂ → Prop) extends FwdSim S T where
  match_initial_states : ∀ c, sourceInitial c → ∃ i X, targetInitial X ∧ rel i c X
  match_final_states : ∀ i c X r m, rel i c X → S.final c r m →
    ∃ r' m', T.final X r' m' ∧ FR r m r' m'

theorem ForwardSimulation.behaves {S : Semantics C₁ R₁ M₁} {T : Semantics C₂ R₂ M₂}
    {sourceInitial : C₁ → Prop} {targetInitial : C₂ → Prop}
    {FR : R₁ → M₁ → R₂ → M₂ → Prop}
    (F : ForwardSimulation S T sourceInitial targetInitial FR)
    {i : Nat} {c : C₁} {X : C₂} (hr : F.rel i c X)
    {B : Behavior R₁ M₁} (hb : Behaves S c B) :
    ∃ B', Behaves T X B' ∧ Matches FR B B' :=
  F.toFwdSim.behaves FR F.match_final_states hr hb

end EmbC.Clight.Behaviors
