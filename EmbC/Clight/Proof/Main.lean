import EmbC.Clight.Proof.Step

/-!
# Final-state matching for the simulations
-/

namespace EmbC.Clight.Proof

open EmbC EmbC.Clight Behaviors

/-- Final-state relation of the statement. -/
def FinalRel (P : Prog) (cp : CC.Program) (m0 : Mem) (j0 : MemoryInjection)
    (rv : Option Val) (st : MachineStore) (w : CC.Val) (cm : CC.Mem) : Prop :=
  ∃ j', j0.Extends j' m0 ∧ retRel P st.mem j' rv w ∧
    memoryRel P j' st.mem cm ∧ ConstRel P cp.globalenv j' st.mem cm

theorem matches_improves {P : Prog} {cp : CC.Program} {m0 : Mem} {j0 : MemoryInjection}
    {B : SourceBehavior} {B' : TargetBehavior}
    (h : Matches (FinalRel P cp m0 j0) B B') : Improves P cp m0 j0 B B' := by
  cases B <;> cases B' <;> first | exact h | exact h.elim | exact ⟨h.1, h.2⟩

theorem rel_final {P : Prog} {ge : CC.CGenv} {cp : CC.Program} (hge : ge = cp.globalenv)
    {j0 : MemoryInjection} {m0 : Mem} {i : Nat}
    {c : Semantics.State} {T : CC.State} {rv : Option Val} {st : MachineStore}
    (hrel : Rel P ge j0 m0 i c T) (hc : c = .returned rv st .stop) :
    ∃ w cm, T = .Returnstate w .Kstop cm ∧ FinalRel P cp m0 j0 rv st w cm := by
  subst hc hge
  rcases hrel.2 with ⟨_, j, cm, ⟨h1, _, h3, h4⟩, hm⟩ | hd
  · rcases hm with ⟨w, K, hw, hK, rfl⟩ | ⟨_, _, _, _, _, _, _, _, hk, _⟩
    · cases hK
      exact ⟨w, cm, rfl, j, h1, hw, h3, h4⟩
    · cases hk
  · cases hd with
    | stuck hf => exact (hf.2.1 ⟨_, _, rfl⟩).elim
    | step hn _ => simp [Semantics.next, Semantics.nextCore] at hn

end EmbC.Clight.Proof
