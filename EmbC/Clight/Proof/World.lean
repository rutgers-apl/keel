import EmbC.Clight.Proof.Backward
import EmbC.Clight.Proof.Defs
import EmbC.Clight.WorldSource

/-! Executable intrinsic oracles refine the public comparison machine.
The proof forgets the certified oracle component and preserves all observations, including
terminal failures. No complete environment implementation is used.
-/

namespace EmbC.Clight.WorldProof

open Behaviors

/-- Retain traces, results, and public final memory, forgetting private state. -/
def erasePrivate {Result State Public : Type} (publicPart : State → Public) :
    Behavior Result State → Behavior Result Public
  | .terminates trace result memory => .terminates trace result (publicPart memory)
  | .diverges trace => .diverges trace
  | .reacts trace => .reacts trace
  | .goesWrong trace => .goesWrong trace

/-- A lockstep lift that preserves terminal failures realizes every behavior,
including failure, with exactly the same public outcome. -/
theorem behaves_of_lockstep
    {C₁ C₂ Result M₁ M₂ Public : Type}
    {S : Behaviors.Semantics C₁ Result M₁} {T : Behaviors.Semantics C₂ Result M₂}
    (rel : C₁ → C₂ → Prop) (public₁ : M₁ → Public) (public₂ : M₂ → Public)
    (hstep : ∀ c q t c', rel c q → S.step c t c' →
      ∃ q', T.step q t q' ∧ rel c' q')
    (hfinal : ∀ c q r m, rel c q → S.final c r m →
      ∃ m', T.final q r m' ∧ public₁ m = public₂ m')
    (hstuck : ∀ c q, rel c q → Behaviors.Stuck S c → Behaviors.Stuck T q)
    {c : C₁} {q : C₂} (hr : rel c q) {B : Behavior Result M₁}
    (hB : Behaves S c B) :
    ∃ B', Behaves T q B' ∧ erasePrivate public₁ B = erasePrivate public₂ B' := by
  let F : FwdSim S T :=
    { rel := fun _ => rel
      sim := by
        intro _ c q t c' hr hs
        obtain ⟨q', hq, hr'⟩ := hstep c q t c' hr hs
        exact ⟨0, q', hr', .inl (Plus.one hq)⟩ }
  have hf : ∀ i c q r m, F.rel i c q → S.final c r m →
      ∃ r' m', T.final q r' m' ∧ r = r' ∧ public₁ m = public₂ m' := by
    intro _ c q r m hr hfin
    obtain ⟨m', hm', heq⟩ := hfinal c q r m hr hfin
    exact ⟨r, m', hm', rfl, heq⟩
  cases B with
  | goesWrong trace =>
      obtain ⟨failed, hs, hn, hf⟩ := hB
      obtain ⟨_, q', hs', hr'⟩ := F.star (i := 0) hr hs
      have hfailed := hstuck failed q' hr' ⟨hn, hf⟩
      exact ⟨.goesWrong trace, ⟨q', hs', hfailed⟩, rfl⟩
  | terminates trace result memory =>
      obtain ⟨B', hb', hm⟩ := F.behaves
        (fun r m r' m' => r = r' ∧ public₁ m = public₂ m') hf (i := 0) hr hB
      cases B' <;> simp only [Matches] at hm
      all_goals try contradiction
      rename_i trace' result' memory'
      rcases hm with ⟨rfl, rfl, heq⟩
      exact ⟨.terminates trace result memory', hb', by simp [erasePrivate, heq]⟩
  | diverges trace =>
      obtain ⟨B', hb', hm⟩ := F.behaves
        (fun r m r' m' => r = r' ∧ public₁ m = public₂ m') hf (i := 0) hr hB
      cases B' <;> simp only [Matches] at hm
      all_goals try contradiction
      rename_i trace'
      exact ⟨.diverges trace', hb', by simp [erasePrivate, hm]⟩
  | reacts trace =>
      obtain ⟨B', hb', hm⟩ := F.behaves
        (fun r m r' m' => r = r' ∧ public₁ m = public₂ m') hf (i := 0) hr hB
      cases B' <;> simp only [Matches] at hm
      all_goals try contradiction
      rename_i trace'
      exact ⟨.reacts trace', hb', by simp [erasePrivate, hm]⟩

theorem contractObservations_total {obs : WorldSource.Observations}
    (ht : WorldSource.ObservationsTotal obs) :
    Semantics.ObservationsTotal (WorldSource.contractObservations obs) := by
  intro P ext args before result after hr
  exact ht P _ _ hr

/-- An intrinsic-oracle failure is also stuck in the comparison machine. -/
theorem stuck_contract {State : Type} {P : Prog} {obs : WorldSource.Observations}
    (ht : WorldSource.ObservationsTotal obs) {c : Semantics.ExecState P State}
    (h : Stuck (WorldSource.semantics P obs) c) :
    Stuck (Proof.sourceSemantics P (WorldSource.contractObservations obs)) (c.withOracle ()) := by
  have hn := WorldSource.next_none_of_no_step ht h.1
  obtain ⟨hn', hready⟩ := WorldSource.next_none_contract hn
  constructor
  · intro trace target hs
    cases hs with
    | silent _ hs => rw [hn'] at hs; cases hs
    | external _ ext args before result after _ he _ =>
      obtain ⟨k, heq, ha, _⟩ := he
      apply hready
      cases before with
      | mk mem oracle =>
        cases oracle
        exact ⟨ext, args, mem, k, heq, ha.defined⟩
  · intro result after hfin
    have hf : Semantics.final (c.withOracle ()) := ⟨result, after, hfin⟩
    obtain ⟨rv, state, hstate⟩ := (WorldSource.final_oracle_iff c ()).mp hf
    exact h.2 rv state hstate

/-- Every execution with an intrinsic oracle has a comparison execution with
exactly the same trace, result, and public final memory. -/
theorem behavior_to_contract {State : Type} {P : Prog} {obs : WorldSource.Observations}
    (ht : WorldSource.ObservationsTotal obs) {c : Semantics.ExecState P State}
    {B : Behavior (Option Val) (KernelState P State)}
    (hB : Behaves (WorldSource.semantics P obs) c B) :
    ∃ B', Behaves (Proof.sourceSemantics P (WorldSource.contractObservations obs))
      (c.withOracle ()) B' ∧
      erasePrivate (fun st : KernelState P State => st.mem) B =
        erasePrivate (fun st : MachineStore => st.mem) B' := by
  apply behaves_of_lockstep (fun c q => q = c.withOracle ())
    (fun st : KernelState P State => st.mem) (fun st : MachineStore => st.mem)
    ?_ ?_ ?_ rfl hB
  · rintro c q trace c' rfl hs
    exact ⟨c'.withOracle (), WorldSource.step_contract hs, rfl⟩
  · rintro c q result state rfl hfinal
    change c = .returned result state .stop at hfinal
    subst c
    exact ⟨⟨state.mem, ()⟩, rfl, rfl⟩
  · rintro c q rfl hs
    exact stuck_contract ht hs

/-- Public behaviors of all certified intrinsic oracles, including their
initial private states. No completeness of an individual oracle is assumed. -/
def publicBehaviors (P : Prog) (obs : WorldSource.Observations) (entry : String)
    (args : List Val) (mem : Mem) (behavior : Behavior (Option Val) Mem) : Prop :=
  ∃ (State : Type) (oracle : Oracle P State) (B : Behavior (Option Val) (KernelState P State)),
    Behaves (WorldSource.semantics P obs) (Semantics.initial entry args ⟨mem, oracle⟩) B ∧
      erasePrivate (fun st : KernelState P State => st.mem) B = behavior

/-- Public behaviors with per-call responses realizable by certified oracles. -/
def contractBehaviors (P : Prog) (obs : WorldSource.Observations) (entry : String)
    (args : List Val) (mem : Mem) (behavior : Behavior (Option Val) Mem) : Prop :=
  ∃ B : Behavior (Option Val) MachineStore,
    Behaves (Proof.sourceSemantics P (WorldSource.contractObservations obs))
      (Semantics.initial entry args ⟨mem, ()⟩) B ∧
    erasePrivate (fun st : MachineStore => st.mem) B = behavior

/-- Forgetting the oracle preserves public behaviors, including undefined
execution, in the comparison semantics. -/
theorem publicBehavior_contractBehavior {P : Prog} {obs : WorldSource.Observations}
    (ht : WorldSource.ObservationsTotal obs) {entry : String} {args : List Val}
    {mem : Mem} {behavior : Behavior (Option Val) Mem}
    (h : publicBehaviors P obs entry args mem behavior) :
    contractBehaviors P obs entry args mem behavior := by
  obtain ⟨State, oracle, B, hb, heq⟩ := h
  obtain ⟨B', hb', heq'⟩ := behavior_to_contract ht hb
  exact ⟨B', hb', heq'.symm.trans heq⟩

end EmbC.Clight.WorldProof
