import EmbC.Clight.Source
import EmbC.Clight.Behaviors

/-!
# Observable execution with an intrinsic stateful oracle

Each executable state contains its certified oracle. Observations depend only
on the call, public reply, and trace, and do not inspect that oracle.
-/

namespace EmbC.Clight.WorldSource

abbrev Observations := Kernel.Call → Kernel.Reply → CC.Trace → Prop

/-- Every response realizable by a certified oracle has an observable trace. -/
def ObservationsTotal (obs : Observations) : Prop :=
  ∀ (P : Prog) (call : Kernel.Call) (reply : Kernel.Reply),
    Oracle.Returns P call reply → ∃ trace, obs call reply trace

def contractObservations (obs : Observations) : Semantics.Observations :=
  fun ext args before result after trace =>
    obs ⟨ext, args, before.mem⟩ ⟨result, after.mem⟩ trace

inductive Step {State : Type} (P : Prog) (obs : Observations) :
    Semantics.ExecState P State → CC.Trace → Semantics.ExecState P State → Prop where
  | silent (source target) :
      Semantics.nextFor P source = some (.silent target) → Step P obs source CC.E0 target
  | external (source target ext args before result after trace) :
      Semantics.nextFor P source = some (.external ext args before result after target) →
      obs ⟨ext, args, before.mem⟩ ⟨result, after.mem⟩ trace → Step P obs source trace target

def semantics {State : Type} (P : Prog) (obs : Observations) :
    Behaviors.Semantics (Semantics.ExecState P State) (Option Val) (KernelState P State) :=
  { step := Step P obs
    final := fun config result after => config = .returned result after .stop }

/-- An observable kernel transition follows the shared call/return protocol. -/
theorem next_external_inv {State : Type} {P : Prog}
    {c target : Semantics.ExecState P State} {ext : Ext} {args : List Val}
    {before after : KernelState P State} {result : Option Val}
    (h : Semantics.nextFor P c = some (.external ext args before result after target)) :
    ∃ k, c = .call (.external ext) args before k ∧
      Ext.run P ext args before = some (result, after) ∧ target = .returned result after k := by
  cases c with
  | regular stmt env mem oracle k =>
    cases stmt <;> simp only [Semantics.nextFor, Semantics.nextCore, Semantics.returnTarget] at h
    all_goals repeat' split at h
    all_goals simp_all
  | callstate f args₀ mem oracle k =>
    cases f with
    | internal name =>
      simp only [Semantics.nextFor, Semantics.nextCore] at h
      repeat' split at h
      all_goals simp_all
    | external ext₀ =>
      simp only [Semantics.nextFor, Semantics.nextCore] at h
      split at h
      · simp at h
      rename_i result₀ after₀ hrun
      simp only [Option.some.injEq, Semantics.Action.external.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
      exact ⟨k, rfl, hrun, rfl⟩
  | returnstate result₀ mem oracle k =>
    cases k <;> simp only [Semantics.nextFor, Semantics.nextCore] at h
    all_goals repeat' split at h
    all_goals simp_all

/-- Returning to the outer caller is independent of the oracle component. -/
theorem final_oracle_iff {State Other : Type} (c : Semantics.State State) (oracle : Other) :
    Semantics.final (c.withOracle oracle) ↔ Semantics.final c := by
  cases c with
  | regular => simp [Semantics.final, Semantics.State.withOracle, Semantics.State.returned]
  | callstate => simp [Semantics.final, Semantics.State.withOracle, Semantics.State.returned]
  | returnstate result mem current k =>
    constructor
    · rintro ⟨rv, state, h⟩
      have hk := (Semantics.State.returnstate.inj h).2.2.2
      subst k
      exact ⟨result, ⟨mem, current⟩, rfl⟩
    · rintro ⟨rv, state, h⟩
      have hk := (Semantics.State.returnstate.inj h).2.2.2
      subst k
      exact ⟨result, ⟨mem, oracle⟩, rfl⟩

/-- Total observations cannot make a defined executable step disappear. -/
theorem next_none_of_no_step {State : Type} {P : Prog} {obs : Observations}
    (ht : ObservationsTotal obs) {c : Semantics.ExecState P State}
    (hn : ∀ trace target, ¬ Step P obs c trace target) : Semantics.nextFor P c = none := by
  cases hnext : Semantics.nextFor P c with
  | none => rfl
  | some action =>
    cases action with
    | silent target => exact (hn _ _ (.silent _ _ hnext)).elim
    | external ext args before result after target =>
      obtain ⟨_, _, hrun, _⟩ := next_external_inv hnext
      obtain ⟨trace, ho⟩ := ht P _ _ (Ext.run_spec hrun)
      exact (hn _ _ (.external _ _ _ _ _ _ _ _ hnext ho)).elim

/-- Internal execution is preserved when the oracle component is forgotten. -/
theorem next_silent_contract {State : Type} {P : Prog}
    {c c' : Semantics.ExecState P State}
    (h : Semantics.nextFor P c = some (.silent c')) :
    Semantics.next P (c.withOracle ()) = some (.silent (c'.withOracle ())) := by
  cases c with
  | regular stmt env mem current k =>
    cases stmt <;> simp only [Semantics.nextFor, Semantics.next, Semantics.nextCore,
      Semantics.State.withOracle, Semantics.returnTarget] at h ⊢
    all_goals repeat' split at h
    all_goals try simp only [Option.map, Option.some.injEq,
      Semantics.Action.silent.injEq, reduceCtorEq] at h
    all_goals try subst c'
    all_goals simp_all
  | callstate f args mem current k =>
    cases f <;> simp only [Semantics.nextFor, Semantics.next, Semantics.nextCore,
      Semantics.State.withOracle] at h ⊢
    all_goals repeat' split at h
    all_goals try simp only [Option.some.injEq,
      Semantics.Action.silent.injEq, reduceCtorEq] at h
    all_goals try subst c'
    all_goals simp_all
  | returnstate result mem current k =>
    cases k <;> simp only [Semantics.nextFor, Semantics.next, Semantics.nextCore,
      Semantics.State.withOracle] at h ⊢
    all_goals repeat' split at h
    all_goals try simp only [Option.some.injEq,
      Semantics.Action.silent.injEq, reduceCtorEq] at h
    all_goals try subst c'
    all_goals simp_all

/-- The intrinsic certificate makes every executable response a source step. -/
theorem step_contract {State : Type} {P : Prog} {obs : Observations}
    {c c' : Semantics.ExecState P State} {trace : CC.Trace}
    (h : Step P obs c trace c') :
    Semantics.Step P (contractObservations obs) (c.withOracle ()) trace (c'.withOracle ()) := by
  cases h with
  | silent _ hn => exact .silent _ _ (next_silent_contract hn)
  | external _ ext args before result after _ hn ho =>
    obtain ⟨k, rfl, hrun, rfl⟩ := next_external_inv hn
    exact .external _ _ ext args ⟨before.mem, ()⟩ result ⟨after.mem, ()⟩ trace
      ⟨k, rfl, Ext.run_spec hrun, rfl⟩ ho

/-- Undefined executable calls have no successor in the comparison semantics. -/
theorem next_none_contract {State : Type} {P : Prog} {c : Semantics.ExecState P State}
    (hn : Semantics.nextFor P c = none) :
    Semantics.next P (c.withOracle ()) = none ∧ ¬ Semantics.KernelReady P (c.withOracle ()) := by
  cases c with
  | regular stmt env mem oracle k =>
    constructor
    · cases stmt <;> simp only [Semantics.nextFor, Semantics.next, Semantics.nextCore,
        Semantics.State.withOracle, Semantics.returnTarget] at hn ⊢
      all_goals repeat' split at hn
      all_goals simp_all
    · simp [Semantics.KernelReady, Semantics.State.withOracle]
  | callstate f args mem oracle k =>
    cases f with
    | internal name =>
      constructor
      · simp only [Semantics.nextFor, Semantics.next, Semantics.nextCore,
          Semantics.State.withOracle] at hn ⊢
        repeat' split at hn
        all_goals simp_all
      · simp [Semantics.KernelReady, Semantics.State.withOracle]
    | external ext =>
      have hrun : Ext.run P ext args ⟨mem, oracle⟩ = none := by
        simp only [Semantics.nextFor, Semantics.nextCore] at hn
        cases h : Ext.run P ext args ⟨mem, oracle⟩ <;> simp_all
      refine ⟨rfl, ?_⟩
      have hd := (Ext.run_none_iff_not_defined (P := P) ext args ⟨mem, oracle⟩).mp hrun
      simpa [Semantics.KernelReady, Semantics.State.withOracle] using hd
  | returnstate result mem oracle k =>
    constructor
    · cases k <;> simp only [Semantics.nextFor, Semantics.next, Semantics.nextCore,
        Semantics.State.withOracle] at hn ⊢
      all_goals repeat' split at hn
      all_goals simp_all
    · simp [Semantics.KernelReady, Semantics.State.withOracle]

end EmbC.Clight.WorldSource
