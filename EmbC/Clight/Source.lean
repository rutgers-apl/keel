import EmbC.Semantics
import EmbC.Kernel.Conformance
import CCLib.Clight

/-! Observable contract semantics for the EmbC source machine.

Internal transitions use the common control machine. External transitions range
over public responses realizable by intrinsically certified oracles. The
comparison semantics does not retain an oracle's private representation.
-/

namespace EmbC.Semantics

abbrev Observations :=
  Ext → List Val → MachineStore → Option Val → MachineStore → CC.Trace → Prop

/-- Every permitted kernel outcome admits at least one observation. -/
def ObservationsTotal (obs : Observations) : Prop :=
  ∀ (P : Prog) (ext : Ext) (args : List Val) (st : MachineStore)
    (rv : Option Val) (st' : MachineStore),
    Oracle.Returns P ⟨ext, args, st.mem⟩ ⟨rv, st'.mem⟩ →
      ∃ trace, obs ext args st rv st' trace

/-- The call/return protocol, with an outcome permitted by the kernel contract. -/
def External (P : Prog) (source : State) (ext : Ext) (args : List Val)
    (st : MachineStore) (rv : Option Val) (st' : MachineStore) (target : State) : Prop :=
  ∃ k, source = .call (.external ext) args st k ∧
    Oracle.Returns P ⟨ext, args, st.mem⟩ ⟨rv, st'.mem⟩ ∧
    target = .returned rv st' k

inductive Step (P : Prog) (obs : Observations) : State → CC.Trace → State → Prop where
  | silent (source target) :
      next P source = some (.silent target) → Step P obs source CC.E0 target
  | external (source target ext args st rv st' trace) :
      External P source ext args st rv st' target →
      obs ext args st rv st' trace → Step P obs source trace target

/-- The internal classifier never selects an external outcome. -/
theorem next_ne_external {P : Prog} {c target : State} {ext : Ext} {args : List Val}
    {before after : MachineStore} {rv : Option Val}
    (h : next P c = some (.external ext args before rv after target)) : False := by
  cases c with
  | regular stmt env mem world k =>
    cases stmt <;> simp only [next, nextCore, returnTarget] at h
    all_goals repeat' split at h
    all_goals simp_all
  | callstate f args mem world k =>
    cases f <;> simp only [next, nextCore] at h
    all_goals repeat' split at h
    all_goals simp_all
  | returnstate result mem world k =>
    cases k <;> simp only [next, nextCore] at h
    all_goals repeat' split at h
    all_goals simp_all

/-- Every observable contract step is an unlabelled contract step. -/
theorem Step.raw {P : Prog} {obs : Observations} {c c' : State} {trace : CC.Trace}
    (h : Step P obs c trace c') : rawStep P c c' := by
  cases h with
  | silent _ hn => exact .inl ⟨_, hn, rfl⟩
  | external _ ext args before rv after _ he _ =>
    obtain ⟨k, rfl, ha, rfl⟩ := he
    cases before with
    | mk mem world =>
      cases after with
      | mk mem' world' =>
        cases world
        cases world'
        exact .inr ⟨ext, args, mem, k, rv, mem', rfl, ha, rfl⟩

end EmbC.Semantics
