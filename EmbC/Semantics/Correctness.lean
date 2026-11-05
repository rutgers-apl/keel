import EmbC.Semantics

/-!
# Correctness of the bounded driver for the source machine
-/

namespace EmbC.Semantics

variable {State : Type}

open EmbC

variable (P : Prog)

/-- Raw executions of a fixed length. -/
inductive RSN : Nat → (ExecState P State) → (ExecState P State) → Prop
  | refl (c) : RSN 0 c c
  | step {n a b c} : rawStepFor P a b → RSN n b c → RSN (n + 1) a c

/-- Configurations without successor. -/
def Terminal (c : (ExecState P State)) : Prop := ∀ d, ¬ rawStepFor P c d

variable {P}

theorem rawStep_of_next {c : (ExecState P State)} {act : (ExecAction P State)} (h : nextFor P c = some act) :
    rawStepFor P c act.target := ⟨act, h, rfl⟩

theorem rawStep_det {a b c : (ExecState P State)} (h₁ : rawStepFor P a b) (h₂ : rawStepFor P a c) : b = c := by
  obtain ⟨a₁, e₁, t₁⟩ := h₁
  obtain ⟨a₂, e₂, t₂⟩ := h₂
  rw [e₁] at e₂
  cases e₂
  exact t₁.symm.trans t₂

theorem RSN.one {a b : (ExecState P State)} (h : rawStepFor P a b) : RSN P 1 a b := RSN.step h (RSN.refl b)

theorem RSN.trans {n m : Nat} {a b c : (ExecState P State)} (h₁ : RSN P n a b) (h₂ : RSN P m b c) :
    RSN P (n + m) a c := by
  induction h₁ with
  | refl => simpa using h₂
  | step s _ ih =>
    have := RSN.step s (ih h₂)
    rwa [Nat.add_right_comm] at this

theorem RSN.rawStar {n : Nat} {a b : (ExecState P State)} (h : RSN P n a b) : RawStar (rawStepFor P) a b := by
  induction h with
  | refl c => exact RawStar.refl c
  | step s _ ih => exact RawStar.step _ _ _ s ih

theorem RawStar.rsn {a b : (ExecState P State)} (h : RawStar (rawStepFor P) a b) : ∃ n, RSN P n a b := by
  induction h with
  | refl c => exact ⟨0, RSN.refl c⟩
  | step _ _ _ s _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, RSN.step s hn⟩

theorem terminal_failed {c : (ExecState P State)} (h : FailedFor P c) : Terminal P c := by
  intro d ⟨act, hn, _⟩
  rw [h.1] at hn
  cases hn

theorem terminal_returned (rv : Option Val) (st : (KernelState P State)) :
    Terminal P (.returned rv st .stop) := by
  intro d ⟨act, h, _⟩; simp [nextFor, nextCore] at h

/-- A terminal state is either a final return or undefined behavior. -/
theorem next_none_cases {c : (ExecState P State)} (h : nextFor P c = none) :
    final c ∨ FailedFor P c := by
  by_cases hf : final c
  · exact .inl hf
  · exact .inr ⟨h, hf⟩

theorem next_none_of_terminal {c : (ExecState P State)} (h : Terminal P c) : nextFor P c = none := by
  cases hn : nextFor P c with
  | none => rfl
  | some a => exact (h _ (rawStep_of_next hn)).elim

/-- A successful bounded run reaches the same final machine state. -/
theorem run_ok_reachable {fuel : Nat} {c : (ExecState P State)} {rv : Option Val} {st : (KernelState P State)}
    (h : run P fuel c = .ok (rv, st)) :
    RawStar (rawStepFor P) c (.returned rv st .stop) := by
  induction fuel generalizing c with
  | zero => simp [run, runCore] at h
  | succ n ih =>
    cases hn : nextFor P c with
    | some a =>
      exact .step _ _ _ (rawStep_of_next hn) (ih (by simpa [run, runCore, hn] using h))
    | none =>
      cases c with
      | regular s env mem orc k => simp [run, runCore, hn] at h
      | callstate f vs mem orc k => simp [run, runCore, hn] at h
      | returnstate rv' mem orc k =>
        cases k <;> simp [run, runCore, hn] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .refl _

/-- A stuck run reaches a non-final state with no successor. -/
theorem run_stuck_reachable {fuel : Nat} {c : (ExecState P State)} (h : run P fuel c = .stuck) :
    ∃ failed, RawStar (rawStepFor P) c failed ∧ FailedFor P failed := by
  induction fuel generalizing c with
  | zero => simp [run, runCore] at h
  | succ n ih =>
    cases hn : nextFor P c with
    | some a =>
      obtain ⟨failed, hr, hf⟩ := ih (by simpa [run, runCore, hn] using h)
      exact ⟨failed, .step _ _ _ (rawStep_of_next hn) hr, hf⟩
    | none =>
      refine ⟨c, .refl _, hn, ?_⟩
      rintro ⟨rv, st, rfl⟩
      simp [run, runCore, nextFor, nextCore] at h

/-- Following `n` machine steps consumes exactly `n` units of runner fuel. -/
theorem RSN.run {n fuel : Nat} {a b : (ExecState P State)} (h : RSN P n a b) :
    run P (n + fuel) a = run P fuel b := by
  induction h with
  | refl => simp
  | @step n a b c hs ht ih =>
    obtain ⟨act, hn, rfl⟩ := hs
    rw [Nat.add_right_comm n 1 fuel]
    simpa only [Semantics.run, Semantics.runCore, hn] using ih

theorem run_ok_path {fuel : Nat} {f : String} {args : List Val} {st : (KernelState P State)}
    {rv : Option Val} {st' : (KernelState P State)} (h : P.run fuel f args st = .ok (rv, st')) :
    RawStar (rawStepFor P) (initial f args st) (.returned rv st' .stop) :=
  run_ok_reachable h

theorem run_stuck_path {fuel : Nat} {f : String} {args : List Val} {st : (KernelState P State)}
    (h : P.run fuel f args st = .stuck) :
    ∃ failed, RawStar (rawStepFor P) (initial f args st) failed ∧ FailedFor P failed :=
  run_stuck_reachable h

theorem run_of_terminal {f : String} {args : List Val} {st : (KernelState P State)} {T : (ExecState P State)}
    (h : RawStar (rawStepFor P) (initial f args st) T) (ht : Terminal P T) :
    ∃ fuel, P.run fuel f args st ≠ .timeout ∧
      ((∃ rv st', P.run fuel f args st = .ok (rv, st') ∧ T = .returned rv st' .stop) ∨
       (P.run fuel f args st = .stuck ∧ FailedFor P T)) := by
  obtain ⟨n, hn⟩ := h.rsn
  have hr : P.run (n + 1) f args st = run P 1 T := hn.run
  have hnext := next_none_of_terminal ht
  rcases next_none_cases hnext with ⟨rv, st', rfl⟩ | hf
  · simp only [run, runCore, nextFor, nextCore] at hr
    exact ⟨n + 1, by simp [hr], .inl ⟨rv, st', hr, rfl⟩⟩
  · have hrun : run P 1 T = .stuck := by
      cases T with
      | regular s env mem orc k => simp [run, runCore, hnext]
      | callstate f vs mem orc k => simp [run, runCore, hnext]
      | returnstate rv mem orc k =>
        cases k with
        | stop => exact (hf.2 ⟨rv, ⟨mem, orc⟩, rfl⟩).elim
        | seq | loop | function | call => simp [run, runCore, hnext]
    rw [hrun] at hr
    exact ⟨n + 1, by simp [hr], .inr ⟨hr, hf⟩⟩

/-- The driver recognizes exactly finite final/failure executions and diverges
exactly when every fuel budget times out. -/
def RunnerCorrect (P : Prog) : Prop :=
  ∀ (f : String) (args : List Val) (st : (KernelState P State)),
    (∀ (rv : Option Val) (st' : (KernelState P State)),
      RawStar (rawStepFor P) (initial f args st) (.returned rv st' .stop) ↔
        ∃ fuel, P.run fuel f args st = .ok (rv, st')) ∧
    ((∃ failed, RawStar (rawStepFor P) (initial f args st) failed ∧ FailedFor P failed) ↔
      ∃ fuel, P.run fuel f args st = .stuck) ∧
    (RawInfiniteFor P (initial f args st) ↔
      ∀ fuel, P.run fuel f args st = .timeout)

/-- The successor function of the deterministic machine. -/
def succ (P : Prog) (c : (ExecState P State)) : (ExecState P State) :=
  match nextFor P c with
  | some a => a.target
  | none => c

def iter (P : Prog) (c : (ExecState P State)) : Nat → (ExecState P State)
  | 0 => c
  | n + 1 => succ P (iter P c n)

theorem terminal_of_next_none {c : (ExecState P State)} (h : nextFor P c = none) : Terminal P c := by
  intro d ⟨a, ha, _⟩; rw [h] at ha; cases ha

theorem rawStep_succ {c : (ExecState P State)} (h : ¬ Terminal P c) : rawStepFor P c (succ P c) := by
  cases hn : nextFor P c with
  | none => exact absurd (terminal_of_next_none hn) h
  | some a => simp only [succ, hn]; exact rawStep_of_next hn

theorem infinite_states_eq {states : Nat → (ExecState P State)} (hs : ∀ n, rawStepFor P (states n) (states (n + 1))) :
    ∀ m i X, RSN P m (states i) X → X = states (i + m) := by
  intro m
  induction m with
  | zero => intro i X h; cases h; rfl
  | succ m ih =>
    intro i X h
    cases h with
    | step s rest =>
      rw [rawStep_det s (hs i)] at rest
      rw [ih _ _ rest]; congr 1; omega

theorem runnerCorrect : RunnerCorrect (State := State) P := by
  intro f args st
  refine ⟨fun rv st' => ⟨fun h => ?_, fun ⟨fuel, h⟩ => run_ok_path h⟩,
    ⟨fun ⟨failed, h, hf⟩ => ?_, fun ⟨fuel, h⟩ => run_stuck_path h⟩,
    ⟨fun h fuel => ?_, fun h => ?_⟩⟩
  · obtain ⟨fuel, -, h'⟩ := run_of_terminal h (terminal_returned _ _)
    rcases h' with ⟨rv', st'', hr, he⟩ | ⟨hr, hf⟩
    · cases st'; cases st''; cases he; exact ⟨fuel, hr⟩
    · exact (hf.2 ⟨rv, st', rfl⟩).elim
  · obtain ⟨fuel, -, h'⟩ := run_of_terminal h (terminal_failed hf)
    rcases h' with ⟨rv', st'', hr, he⟩ | ⟨hr, _⟩
    · exact (hf.2 ⟨rv', st'', he⟩).elim
    · exact ⟨fuel, hr⟩
  · obtain ⟨states, h0, hs⟩ := h
    cases hr : P.run fuel f args st with
    | timeout => rfl
    | ok r =>
      obtain ⟨rv, st'⟩ := r
      obtain ⟨n, hn⟩ := (run_ok_path hr).rsn
      rw [← h0] at hn
      have := infinite_states_eq hs n 0 _ hn
      have hstep := hs (0 + n)
      rw [← this] at hstep
      exact absurd hstep (terminal_returned _ _ _)
    | stuck =>
      obtain ⟨failed, hf, hfail⟩ := run_stuck_path hr
      obtain ⟨n, hn⟩ := hf.rsn
      rw [← h0] at hn
      have := infinite_states_eq hs n 0 _ hn
      have hstep := hs (0 + n)
      rw [← this] at hstep
      exact absurd hstep (terminal_failed hfail _)
  · have hnt : ∀ n, RSN P n (initial f args st) (iter P (initial f args st) n) ∧
        ¬ Terminal P (iter P (initial f args st) n) := by
      intro n
      have hnot : ∀ X, RawStar (rawStepFor P) (initial f args st) X → ¬ Terminal P X := by
        intro X hX ht
        obtain ⟨fuel, hne, -⟩ := run_of_terminal hX ht
        exact hne (h fuel)
      induction n with
      | zero => exact ⟨RSN.refl _, hnot _ (RawStar.refl _)⟩
      | succ n ih =>
        have h1 : RSN P (n + 1) (initial f args st) (iter P (initial f args st) (n + 1)) :=
          ih.1.trans (RSN.one (rawStep_succ ih.2))
        exact ⟨h1, hnot _ h1.rawStar⟩
    exact ⟨iter P (initial f args st), rfl, fun n => rawStep_succ (hnt n).2⟩

end EmbC.Semantics
