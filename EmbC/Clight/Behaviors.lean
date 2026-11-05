import CCLib.Clight

/-! Finite and infinite observable behaviors of a traced transition system. -/

namespace EmbC.Clight.Behaviors

abbrev InfiniteTrace := Nat → CC.Event

inductive Behavior (Result Memory : Type) where
  | terminates (trace : CC.Trace) (result : Result) (memory : Memory)
  | diverges (trace : CC.Trace)
  | reacts (trace : InfiniteTrace)
  | goesWrong (trace : CC.Trace)

structure Semantics (State Result Memory : Type) where
  step : State → CC.Trace → State → Prop
  final : State → Result → Memory → Prop

/-- A finite execution records the concatenation of all step traces. -/
inductive Star {State : Type} (step : State → CC.Trace → State → Prop) :
    State → CC.Trace → State → Prop where
  | refl (s) : Star step s CC.E0 s
  | step {s₁ s₂ s₃ t₁ t₂} :
      step s₁ t₁ s₂ → Star step s₂ t₂ s₃ →
      Star step s₁ (CC.Eapp t₁ t₂) s₃

structure InfiniteRun {State : Type}
    (step : State → CC.Trace → State → Prop) (start : State) where
  states : Nat → State
  traces : Nat → CC.Trace
  initial : states 0 = start
  steps : ∀ n, step (states n) (traces n) (states (n + 1))

/-- The events emitted by the first `n` transitions of an infinite run. -/
def InfiniteRun.prefix {State : Type} {step : State → CC.Trace → State → Prop}
    {start : State} (run : InfiniteRun step start) : Nat → CC.Trace
  | 0 => CC.E0
  | n + 1 => CC.Eapp (run.prefix n) (run.traces n)

def tracePrefix (finite : CC.Trace) (stream : InfiniteTrace) : Prop :=
  ∀ (i : Nat), i < finite.length → finite[i]? = some (stream i)

/-- A reactive run emits precisely the given stream, with unboundedly many events. -/
def ReactiveTrace {State : Type} {step : State → CC.Trace → State → Prop}
    {start : State} (run : InfiniteRun step start) (stream : InfiniteTrace) : Prop :=
  (∀ n, tracePrefix (run.prefix n) stream) ∧
  ∀ n, ∃ k, n ≤ (run.prefix k).length

def Behaves {State Result Memory : Type} (sem : Semantics State Result Memory)
    (start : State) : Behavior Result Memory → Prop
  | .terminates trace result memory =>
      ∃ finish, Star sem.step start trace finish ∧ sem.final finish result memory
  | .diverges trace =>
      ∃ tail, Star sem.step start trace tail ∧
        ∃ run : InfiniteRun sem.step tail, ∀ n, run.traces n = CC.E0
  | .reacts stream =>
      ∃ run : InfiniteRun sem.step start, ReactiveTrace run stream
  | .goesWrong trace =>
      ∃ stuck, Star sem.step start trace stuck ∧
        (∀ trace next, ¬ sem.step stuck trace next) ∧
        (∀ result memory, ¬ sem.final stuck result memory)

/-- Compare finite observations without dropping or changing target events. -/
def Prefix {Result Memory : Type} (trace : CC.Trace) : Behavior Result Memory → Prop
  | .terminates observed _ _ => List.IsPrefix trace observed
  | .diverges observed => List.IsPrefix trace observed
  | .reacts stream => tracePrefix trace stream
  | .goesWrong observed => List.IsPrefix trace observed

end EmbC.Clight.Behaviors
