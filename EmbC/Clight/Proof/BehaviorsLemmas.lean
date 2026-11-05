import EmbC.Clight.Behaviors

/-!
# Generic facts about behaviors and forward simulations

Everything here is independent of EmbC and Clight: finite and infinite runs,
existence of a behavior for every state, prepending a finite run to a behavior,
and the preservation of behaviors by a forward simulation with a well-founded
(natural-number) stuttering index.
-/

namespace EmbC.Clight.Behaviors

open CC (E0 Eapp Trace)

section Basic

variable {C : Type} {step : C → Trace → C → Prop}

theorem Star.one {s₁ s₂ : C} {t : Trace} (h : step s₁ t s₂) : Star step s₁ t s₂ := by
  have := Star.step h (Star.refl s₂)
  simpa [Eapp, E0] using this

theorem Star.trans {s₁ s₂ s₃ : C} {t₁ t₂ : Trace} (h₁ : Star step s₁ t₁ s₂)
    (h₂ : Star step s₂ t₂ s₃) : Star step s₁ (t₁ ++ t₂) s₃ := by
  induction h₁ with
  | refl => simpa [E0] using h₂
  | step h _ ih =>
    have := Star.step h (ih h₂)
    simpa [Eapp, List.append_assoc] using this

/-- Non-empty finite runs. -/
inductive Plus (step : C → Trace → C → Prop) : C → Trace → C → Prop where
  | intro {s₁ s₂ s₃ t₁ t₂} : step s₁ t₁ s₂ → Star step s₂ t₂ s₃ → Plus step s₁ (t₁ ++ t₂) s₃

theorem Plus.inv {s₁ s₃ : C} {t : Trace} (h : Plus step s₁ t s₃) :
    ∃ s₂ t₁ t₂, step s₁ t₁ s₂ ∧ Star step s₂ t₂ s₃ ∧ t = t₁ ++ t₂ := by
  cases h with
  | intro a b => exact ⟨_, _, _, a, b, rfl⟩

theorem Plus.star {s₁ s₂ : C} {t : Trace} (h : Plus step s₁ t s₂) : Star step s₁ t s₂ := by
  cases h with
  | intro h₁ h₂ => exact Star.step h₁ h₂

theorem Plus.one {s₁ s₂ : C} {t : Trace} (h : step s₁ t s₂) : Plus step s₁ t s₂ := by
  simpa [E0] using Plus.intro h (Star.refl s₂)

theorem Plus.trans_star {s₁ s₂ s₃ : C} {t₁ t₂ : Trace} (h₁ : Plus step s₁ t₁ s₂)
    (h₂ : Star step s₂ t₂ s₃) : Plus step s₁ (t₁ ++ t₂) s₃ := by
  cases h₁ with
  | intro a b => simpa [List.append_assoc] using Plus.intro a (Star.trans b h₂)

theorem Star.trans_plus {s₁ s₂ s₃ : C} {t₁ t₂ : Trace} (h₁ : Star step s₁ t₁ s₂)
    (h₂ : Plus step s₂ t₂ s₃) : Plus step s₁ (t₁ ++ t₂) s₃ := by
  induction h₁ with
  | refl => simpa [E0] using h₂
  | step a _ ih =>
    have := Plus.intro a (ih h₂).star
    simpa [Eapp, List.append_assoc] using this

/-- Finite runs of a fixed length. -/
inductive StarN (step : C → Trace → C → Prop) : Nat → C → Trace → C → Prop where
  | refl (s) : StarN step 0 s [] s
  | step {n s₁ s₂ s₃ t₁ t₂} : step s₁ t₁ s₂ → StarN step n s₂ t₂ s₃ →
      StarN step (n + 1) s₁ (t₁ ++ t₂) s₃

theorem Star.starN {s₁ s₂ : C} {t : Trace} (h : Star step s₁ t s₂) :
    ∃ n, StarN step n s₁ t s₂ := by
  induction h with
  | refl s => exact ⟨0, by simpa [E0] using StarN.refl (step := step) s⟩
  | step a _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by simpa [Eapp] using StarN.step a hn⟩

theorem StarN.star {n : Nat} {s₁ s₂ : C} {t : Trace} (h : StarN step n s₁ t s₂) :
    Star step s₁ t s₂ := by
  induction h with
  | refl s => simpa [E0] using Star.refl (step := step) s
  | step a _ ih => simpa [Eapp] using Star.step a ih

theorem InfiniteRun.prefix_succ {start : C} (run : InfiniteRun step start) (n : Nat) :
    run.prefix (n + 1) = run.prefix n ++ run.traces n := rfl

theorem InfiniteRun.prefix_zero {start : C} (run : InfiniteRun step start) :
    run.prefix 0 = [] := rfl

theorem InfiniteRun.prefix_mono {start : C} (run : InfiniteRun step start) {n k : Nat}
    (h : n ≤ k) : run.prefix n <+: run.prefix k := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih =>
    rw [InfiniteRun.prefix_succ]
    exact ih.trans (List.prefix_append _ _)

theorem InfiniteRun.star_prefix {start : C} (run : InfiniteRun step start) (n : Nat) :
    Star step start (run.prefix n) (run.states n) := by
  induction n with
  | zero => rw [run.initial]; simpa [InfiniteRun.prefix] using Star.refl (step := step) start
  | succ n ih =>
    rw [InfiniteRun.prefix_succ]
    exact Star.trans ih (Star.one (run.steps n))

/-- The tail of an infinite run. -/
def InfiniteRun.drop {start : C} (run : InfiniteRun step start) (N : Nat) :
    InfiniteRun step (run.states N) where
  states n := run.states (N + n)
  traces n := run.traces (N + n)
  initial := rfl
  steps n := run.steps (N + n)

theorem tracePrefix_of_prefix {l₁ l₂ : Trace} {stream : InfiniteTrace}
    (h : l₁ <+: l₂) (h₂ : tracePrefix l₂ stream) : tracePrefix l₁ stream := by
  intro i hi
  have hi2 : i < l₂.length := Nat.lt_of_lt_of_le hi h.length_le
  rw [← h₂ i hi2]
  rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi2]
  rw [h.getElem hi]

end Basic

/-! ## Flattening a sequence of non-empty runs into one infinite run -/

section Flatten

variable {C : Type} {R : C → Trace → C → Prop}

private structure FState (C : Type) where
  s : C
  τ : Trace
  i : Nat
  d : Nat

private def FInv (R : C → Trace → C → Prop) (x : Nat → C) (U : Nat → Trace)
    (q : FState C) : Prop :=
  ∃ t, StarN R q.d q.s t (x q.i) ∧ q.τ ++ t = U q.i

private theorem flatten_step (x : Nat → C) (U : Nat → Trace)
    (hplus : ∀ i, ∃ u, Plus R (x i) u (x (i + 1)) ∧ U i ++ u = U (i + 1))
    (q : FState C) (hq : FInv R x U q) :
    ∃ q' : FState C, ∃ t₁, R q.s t₁ q'.s ∧ q'.τ = q.τ ++ t₁ ∧ FInv R x U q' ∧
      ((q'.i = q.i ∧ q'.d < q.d) ∨ (q'.i = q.i + 1 ∧ q.d = 0)) := by
  obtain ⟨s, τ, i, d⟩ := q
  obtain ⟨t, hstar, hτ⟩ := hq
  simp only at hstar hτ ⊢
  generalize hxi : x i = xi at hstar
  cases hstar with
  | refl =>
    obtain ⟨u, hp, hu⟩ := hplus i
    rw [hxi] at hp
    obtain ⟨s₂, t₁, t₂, a, b, rfl⟩ := hp.inv
    obtain ⟨d', hd'⟩ := b.starN
    refine ⟨⟨s₂, τ ++ t₁, i + 1, d'⟩, t₁, a, rfl, ⟨t₂, hd', ?_⟩, Or.inr ⟨rfl, rfl⟩⟩
    simp only [List.append_nil] at hτ
    simp only
    rw [← hu, ← hτ, List.append_assoc]
  | @step n _ s₂ _ t₁ t₂ a b =>
    refine ⟨⟨s₂, τ ++ t₁, i, n⟩, t₁, a, rfl, ⟨t₂, hxi ▸ b, ?_⟩, Or.inl ⟨rfl, by simp⟩⟩
    simp only
    rw [← hτ, List.append_assoc]

private noncomputable def flatSeq (x : Nat → C) (U : Nat → Trace) (hU : U 0 = [])
    (hplus : ∀ i, ∃ u, Plus R (x i) u (x (i + 1)) ∧ U i ++ u = U (i + 1)) :
    Nat → {q : FState C // FInv R x U q}
  | 0 => ⟨⟨x 0, [], 0, 0⟩, [], StarN.refl _, by simp [hU]⟩
  | n + 1 =>
    let q := flatSeq x U hU hplus n
    ⟨Classical.choose (flatten_step x U hplus q.1 q.2),
      (Classical.choose_spec (Classical.choose_spec (flatten_step x U hplus q.1 q.2))).2.2.1⟩

private noncomputable def flatTrace (x : Nat → C) (U : Nat → Trace) (hU : U 0 = [])
    (hplus : ∀ i, ∃ u, Plus R (x i) u (x (i + 1)) ∧ U i ++ u = U (i + 1)) (n : Nat) : Trace :=
  let q := flatSeq x U hU hplus n
  Classical.choose (Classical.choose_spec (flatten_step x U hplus q.1 q.2))

private theorem flatSeq_spec (x : Nat → C) (U : Nat → Trace) (hU : U 0 = [])
    (hplus : ∀ i, ∃ u, Plus R (x i) u (x (i + 1)) ∧ U i ++ u = U (i + 1)) (n : Nat) :
    R (flatSeq x U hU hplus n).1.s (flatTrace x U hU hplus n) (flatSeq x U hU hplus (n + 1)).1.s ∧
    (flatSeq x U hU hplus (n + 1)).1.τ =
      (flatSeq x U hU hplus n).1.τ ++ flatTrace x U hU hplus n ∧
    (((flatSeq x U hU hplus (n + 1)).1.i = (flatSeq x U hU hplus n).1.i ∧
        (flatSeq x U hU hplus (n + 1)).1.d < (flatSeq x U hU hplus n).1.d) ∨
      ((flatSeq x U hU hplus (n + 1)).1.i = (flatSeq x U hU hplus n).1.i + 1 ∧
        (flatSeq x U hU hplus n).1.d = 0)) := by
  have h := Classical.choose_spec (Classical.choose_spec
    (flatten_step x U hplus (flatSeq x U hU hplus n).1 (flatSeq x U hU hplus n).2))
  exact ⟨h.1, h.2.1, h.2.2.2⟩

private theorem flatten_of_seq (x : Nat → C) (U : Nat → Trace) (F : Nat → FState C)
    (tr : Nat → Trace) (hinv : ∀ n, FInv R x U (F n))
    (h0 : F 0 = ⟨x 0, [], 0, 0⟩)
    (hspec : ∀ n, R (F n).s (tr n) (F (n + 1)).s ∧ (F (n + 1)).τ = (F n).τ ++ tr n ∧
      (((F (n + 1)).i = (F n).i ∧ (F (n + 1)).d < (F n).d) ∨
        ((F (n + 1)).i = (F n).i + 1 ∧ (F n).d = 0))) :
    ∃ run : InfiniteRun R (x 0),
      (∀ k, ∃ i, run.prefix k <+: U i) ∧ (∀ i, ∃ k, run.prefix k = U i) := by
  let run : InfiniteRun R (x 0) :=
    { states := fun n => (F n).s
      traces := tr
      initial := by simp [h0]
      steps := fun n => (hspec n).1 }
  have hpre : ∀ k, run.prefix k = (F k).τ := by
    intro k
    induction k with
    | zero => simp [h0]; rfl
    | succ k ih =>
      rw [InfiniteRun.prefix_succ, ih, (hspec k).2.1]
  refine ⟨run, ?_, ?_⟩
  · intro k
    obtain ⟨t, _, hτ⟩ := hinv k
    exact ⟨(F k).i, hpre k ▸ ⟨t, hτ⟩⟩
  · have reach0 : ∀ k, ∃ k', (F k').i = (F k).i ∧ (F k').d = 0 := by
      intro k
      suffices H : ∀ d k, (F k).d = d → ∃ k', (F k').i = (F k).i ∧ (F k').d = 0 from
        H _ k rfl
      intro d
      induction d using Nat.strongRecOn with
      | ind d ih =>
        intro k hk
        cases d with
        | zero => exact ⟨k, rfl, hk⟩
        | succ d =>
          rcases (hspec k).2.2 with ⟨hi, hd⟩ | ⟨_, hd⟩
          · obtain ⟨k', h1, h2⟩ := ih _ (by omega) (k + 1) rfl
            exact ⟨k', h1.trans hi, h2⟩
          · omega
    have reach : ∀ i, ∃ k, (F k).i = i ∧ (F k).d = 0 := by
      intro i
      induction i with
      | zero => exact ⟨0, by simp [h0], by simp [h0]⟩
      | succ i ih =>
        obtain ⟨k, hi, hd⟩ := ih
        have hnext : (F (k + 1)).i = i + 1 := by
          rcases (hspec k).2.2 with ⟨_, hd'⟩ | ⟨hi', _⟩
          · omega
          · omega
        obtain ⟨k', h1, h2⟩ := reach0 (k + 1)
        exact ⟨k', h1.trans hnext, h2⟩
    intro i
    obtain ⟨k, hi, hd⟩ := reach i
    obtain ⟨t, hstar, hτ⟩ := hinv k
    rw [hd] at hstar
    generalize hxi : x (F k).i = xi at hstar
    cases hstar
    exact ⟨k, by rw [hpre k, ← hi]; simpa using hτ⟩

theorem flatten (x : Nat → C) (U : Nat → Trace) (hU : U 0 = [])
    (hplus : ∀ i, ∃ u, Plus R (x i) u (x (i + 1)) ∧ U i ++ u = U (i + 1)) :
    ∃ run : InfiniteRun R (x 0),
      (∀ k, ∃ i, run.prefix k <+: U i) ∧ (∀ i, ∃ k, run.prefix k = U i) :=
  flatten_of_seq x U (fun n => (flatSeq x U hU hplus n).1) (flatTrace x U hU hplus)
    (fun n => (flatSeq x U hU hplus n).2) rfl (flatSeq_spec x U hU hplus)

end Flatten

/-! ## Forward simulations -/

structure FwdSim {C₁ R₁ M₁ C₂ R₂ M₂ : Type}
    (S : Semantics C₁ R₁ M₁) (T : Semantics C₂ R₂ M₂) where
  rel : Nat → C₁ → C₂ → Prop
  sim : ∀ i s₁ s₂ t s₁', rel i s₁ s₂ → S.step s₁ t s₁' →
    ∃ i' s₂', rel i' s₁' s₂' ∧ (Plus T.step s₂ t s₂' ∨ (t = E0 ∧ s₂' = s₂ ∧ i' < i))

namespace FwdSim

variable {C₁ R₁ M₁ C₂ R₂ M₂ : Type} {S : Semantics C₁ R₁ M₁} {T : Semantics C₂ R₂ M₂}

theorem star (F : FwdSim S T) {i : Nat} {s₁ s₂ s₁' : _} {t : Trace}
    (hrel : F.rel i s₁ s₂) (h : Star S.step s₁ t s₁') :
    ∃ i' s₂', Star T.step s₂ t s₂' ∧ F.rel i' s₁' s₂' := by
  induction h generalizing i s₂ with
  | refl => exact ⟨i, s₂, by simpa [E0] using Star.refl (step := T.step) s₂, hrel⟩
  | step a _ ih =>
    obtain ⟨i', s₂', hr, hp⟩ := F.sim _ _ _ _ _ hrel a
    obtain ⟨i'', s₂'', hs, hr'⟩ := ih hr
    refine ⟨i'', s₂'', ?_, hr'⟩
    rcases hp with hp | ⟨rfl, rfl, _⟩
    · simpa [Eapp] using (hp.trans_star hs).star
    · simpa [Eapp, E0] using hs

theorem chunk (F : FwdSim S T) {start : C₁} (run : InfiniteRun S.step start) :
    ∀ i n s₂, F.rel i (run.states n) s₂ →
      ∃ n' i' s₂' u, n < n' ∧ Plus T.step s₂ u s₂' ∧ F.rel i' (run.states n') s₂' ∧
        run.prefix n ++ u = run.prefix n' := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro n s₂ hrel
    obtain ⟨i', s₂', hr, hp⟩ := F.sim _ _ _ _ _ hrel (run.steps n)
    rcases hp with hp | ⟨ht, hs, hlt⟩
    · exact ⟨n + 1, i', s₂', run.traces n, by omega, hp, hr, rfl⟩
    · rw [hs] at hr
      obtain ⟨n', i'', s₂'', u, hn, hp, hr', hu⟩ := ih i' hlt (n + 1) s₂ hr
      refine ⟨n', i'', s₂'', u, by omega, hp, hr', ?_⟩
      rw [← hu, InfiniteRun.prefix_succ, ht]
      simp [E0]

private structure Chunk (C₂ : Type) where
  n : Nat
  i : Nat
  s : C₂

theorem forever (F : FwdSim S T) {start : C₁} (run : InfiniteRun S.step start)
    {i : Nat} {s₂ : C₂} (hrel : F.rel i start s₂) :
    ∃ run' : InfiniteRun T.step s₂,
      (∀ k, ∃ n, run'.prefix k <+: run.prefix n) ∧
      (∀ n, ∃ k, run.prefix n <+: run'.prefix k) := by
  let Inv : Chunk C₂ → Prop := fun c => F.rel c.i (run.states c.n) c.s
  have hstep : ∀ c : {c // Inv c}, ∃ c' : {c // Inv c}, ∃ u, c.1.n < c'.1.n ∧
      Plus T.step c.1.s u c'.1.s ∧ run.prefix c.1.n ++ u = run.prefix c'.1.n := by
    intro c
    obtain ⟨n', i', s₂', u, hn, hp, hr, hu⟩ := F.chunk run c.1.i c.1.n c.1.s c.2
    exact ⟨⟨⟨n', i', s₂'⟩, hr⟩, u, hn, hp, hu⟩
  let seq : Nat → {c // Inv c} := fun k => Nat.rec
    (motive := fun _ => {c // Inv c})
    ⟨⟨0, i, s₂⟩, by simp only [Inv]; rw [run.initial]; exact hrel⟩
    (fun _ c => Classical.choose (hstep c)) k
  have hseq : ∀ k, seq (k + 1) = Classical.choose (hstep (seq k)) := fun _ => rfl
  have hspec : ∀ k, ∃ u, (seq k).1.n < (seq (k + 1)).1.n ∧
      Plus T.step (seq k).1.s u (seq (k + 1)).1.s ∧
      run.prefix (seq k).1.n ++ u = run.prefix (seq (k + 1)).1.n := by
    intro k; rw [hseq]; exact Classical.choose_spec (hstep (seq k))
  have hn : ∀ k, k ≤ (seq k).1.n := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih => obtain ⟨_, h, _⟩ := hspec k; omega
  obtain ⟨run', h1, h2⟩ := flatten (R := T.step) (fun k => (seq k).1.s)
    (fun k => run.prefix (seq k).1.n) rfl (fun k => by
      obtain ⟨u, _, hp, hu⟩ := hspec k
      exact ⟨u, hp, hu⟩)
  refine ⟨run', ?_, ?_⟩
  · intro k
    obtain ⟨c, hc⟩ := h1 k
    exact ⟨_, hc⟩
  · intro n
    obtain ⟨k, hk⟩ := h2 n
    exact ⟨k, hk ▸ run.prefix_mono (by have := hn n; omega)⟩

end FwdSim

/-! ## Every state has a behavior -/

section Exists

variable {C R M : Type}

noncomputable def prependStream (t : Trace) (stream : InfiniteTrace) : InfiniteTrace :=
  fun i => if h : i < t.length then t[i] else stream (i - t.length)

noncomputable def prependBehavior (t : Trace) : Behavior R M → Behavior R M
  | .terminates t' r m => .terminates (t ++ t') r m
  | .diverges t' => .diverges (t ++ t')
  | .reacts stream => .reacts (prependStream t stream)
  | .goesWrong t' => .goesWrong (t ++ t')

theorem prefix_prependBehavior (t : Trace) (B : Behavior R M) :
    Prefix t (prependBehavior t B) := by
  cases B with
  | terminates => exact List.prefix_append _ _
  | diverges => exact List.prefix_append _ _
  | goesWrong => exact List.prefix_append _ _
  | reacts stream =>
    intro i hi
    simp [prependStream, hi]

private def InfiniteRun.cons {step : C → Trace → C → Prop} {s s' : C} {t : Trace}
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

private theorem InfiniteRun.cons_prefix {step : C → Trace → C → Prop} {s s' : C} {t : Trace}
    (h : step s t s') (run : InfiniteRun step s') (n : Nat) :
    (InfiniteRun.cons h run).prefix (n + 1) = t ++ run.prefix n := by
  induction n with
  | zero => simp [InfiniteRun.prefix, InfiniteRun.cons, Eapp, E0]
  | succ n ih =>
    show Eapp ((InfiniteRun.cons h run).prefix (n + 1)) _ = _
    rw [ih]
    simp [InfiniteRun.prefix, InfiniteRun.cons, Eapp, List.append_assoc]

private theorem prependStream_append (t₁ t₂ : Trace) (stream : InfiniteTrace) :
    prependStream (t₁ ++ t₂) stream = prependStream t₁ (prependStream t₂ stream) := by
  funext i
  simp only [prependStream, List.length_append]
  by_cases h1 : i < t₁.length
  · have : i < t₁.length + t₂.length := by omega
    simp [h1, this, List.getElem_append_left h1]
  · by_cases h2 : i < t₁.length + t₂.length
    · have h3 : i - t₁.length < t₂.length := by omega
      simp [h1, h2, h3, List.getElem_append_right (Nat.le_of_not_lt h1)]
    · have h3 : ¬ (i - t₁.length < t₂.length) := by omega
      simp [h1, h2, h3, Nat.sub_add_eq]

private theorem tracePrefix_prepend {t l : Trace} {stream : InfiniteTrace}
    (h : tracePrefix l stream) : tracePrefix (t ++ l) (prependStream t stream) := by
  intro i hi
  simp only [prependStream]
  by_cases h1 : i < t.length
  · simp [h1, List.getElem?_append_left h1]
  · simp only [h1, dite_false]
    rw [List.getElem?_append_right (Nat.le_of_not_lt h1)]
    exact h _ (by simp at hi; omega)

private theorem reacts_cons {step : C → Trace → C → Prop} {s s' : C} {t : Trace}
    (h : step s t s') (run : InfiniteRun step s') {stream : InfiniteTrace}
    (hr : ReactiveTrace run stream) :
    ReactiveTrace (InfiniteRun.cons h run) (prependStream t stream) := by
  constructor
  · intro n
    cases n with
    | zero => intro i hi; simp [InfiniteRun.prefix, E0] at hi
    | succ n => rw [InfiniteRun.cons_prefix]; exact tracePrefix_prepend (hr.1 n)
  · intro n
    obtain ⟨k, hk⟩ := hr.2 n
    exact ⟨k + 1, by rw [InfiniteRun.cons_prefix]; simp; omega⟩

theorem behaves_prepend (sem : Semantics C R M) {s s' : C} {t : Trace}
    (hstar : Star sem.step s t s') {B : Behavior R M} (hB : Behaves sem s' B) :
    Behaves sem s (prependBehavior t B) := by
  induction hstar generalizing B with
  | refl =>
    have hnil : ∀ st : InfiniteTrace, prependStream [] st = st := by
      intro st; funext i; simp [prependStream]
    cases B <;> simp_all [prependBehavior, E0]
  | @step s₁ s₂ s₃ t₁ t₂ a _ ih =>
    have ih' := ih hB
    cases B with
    | terminates t' r m =>
      obtain ⟨fin, hs, hf⟩ := ih'
      exact ⟨fin, by simpa [Eapp, List.append_assoc] using Star.step a hs, hf⟩
    | diverges t' =>
      obtain ⟨tail, hs, hr⟩ := ih'
      exact ⟨tail, by simpa [Eapp, List.append_assoc] using Star.step a hs, hr⟩
    | goesWrong t' =>
      obtain ⟨st, hs, hr⟩ := ih'
      exact ⟨st, by simpa [Eapp, List.append_assoc] using Star.step a hs, hr⟩
    | reacts stream =>
      obtain ⟨run, hr⟩ := ih'
      refine ⟨InfiniteRun.cons a run, ?_⟩
      show ReactiveTrace _ (prependStream (Eapp t₁ t₂) stream)
      rw [Eapp, prependStream_append]
      exact reacts_cons a run hr

theorem exists_behavior (sem : Semantics C R M) (s : C) : ∃ B, Behaves sem s B := by
  classical
  by_cases hstuck : ∃ t s', Star sem.step s t s' ∧ ∀ t' s'', ¬ sem.step s' t' s''
  · obtain ⟨t, s', hs, hn⟩ := hstuck
    by_cases hfin : ∃ r m, sem.final s' r m
    · obtain ⟨r, m, hf⟩ := hfin
      exact ⟨.terminates t r m, s', hs, hf⟩
    · exact ⟨.goesWrong t, s', hs, hn, fun r m h => hfin ⟨r, m, h⟩⟩
  · have hstep : ∀ x : {x : C × Trace // Star sem.step s x.2 x.1},
        ∃ t' s'', sem.step x.1.1 t' s'' := by
      intro x
      apply Classical.byContradiction
      intro hno
      exact hstuck ⟨x.1.2, x.1.1, x.2, fun t' s'' h => hno ⟨t', s'', h⟩⟩
    let nxt : {x : C × Trace // Star sem.step s x.2 x.1} →
        {x : C × Trace // Star sem.step s x.2 x.1} := fun x =>
      ⟨(Classical.choose (Classical.choose_spec (hstep x)), x.1.2 ++ Classical.choose (hstep x)),
        Star.trans x.2 (Star.one (Classical.choose_spec (Classical.choose_spec (hstep x))))⟩
    let seq : Nat → {x : C × Trace // Star sem.step s x.2 x.1} := fun n =>
      Nat.rec (motive := fun _ => {x : C × Trace // Star sem.step s x.2 x.1})
        ⟨(s, []), by simpa [E0] using Star.refl (step := sem.step) s⟩ (fun _ x => nxt x) n
    let run : InfiniteRun sem.step s :=
      { states := fun n => (seq n).1.1
        traces := fun n => Classical.choose (hstep (seq n))
        initial := rfl
        steps := fun n => Classical.choose_spec (Classical.choose_spec (hstep (seq n))) }
    by_cases hfin : ∃ N, ∀ n, N ≤ n → run.traces n = []
    · obtain ⟨N, hN⟩ := hfin
      exact ⟨.diverges (run.prefix N), run.states N, run.star_prefix N, run.drop N,
        fun n => hN (N + n) (by omega)⟩
    · have hinf : ∀ N, ∃ n, N ≤ n ∧ run.traces n ≠ [] := by
        intro N
        apply Classical.byContradiction
        intro hno
        exact hfin ⟨N, fun n hn => Classical.byContradiction fun h => hno ⟨n, hn, h⟩⟩
      have hunb : ∀ L, ∃ k, L ≤ (run.prefix k).length := by
        intro L
        induction L with
        | zero => exact ⟨0, Nat.zero_le _⟩
        | succ L ih =>
          obtain ⟨k, hk⟩ := ih
          obtain ⟨n, hn, hne⟩ := hinf k
          refine ⟨n + 1, ?_⟩
          rw [InfiniteRun.prefix_succ, List.length_append]
          have h1 := (run.prefix_mono hn).length_le
          have h2 : 0 < (run.traces n).length := List.length_pos_iff.mpr hne
          omega
      let stream : InfiniteTrace := fun i =>
        (run.prefix (Classical.choose (hunb (i + 1))))[i]'(by
          have := Classical.choose_spec (hunb (i + 1)); omega)
      refine ⟨.reacts stream, run, ?_, ?_⟩
      · intro n i hi
        have hk := Classical.choose_spec (hunb (i + 1))
        show _ = some ((run.prefix (Classical.choose (hunb (i + 1))))[i]'(by omega))
        rw [List.getElem?_eq_getElem hi]
        congr 1
        rcases Nat.le_total n (Classical.choose (hunb (i + 1))) with h | h
        · exact (run.prefix_mono h).getElem hi
        · exact ((run.prefix_mono h).getElem (by omega)).symm
      · intro n
        exact hunb n

end Exists

/-! ## Behavior preservation -/

def Matches {R₁ M₁ R₂ M₂ : Type} (FR : R₁ → M₁ → R₂ → M₂ → Prop) :
    Behavior R₁ M₁ → Behavior R₂ M₂ → Prop
  | .terminates t r m, .terminates t' r' m' => t = t' ∧ FR r m r' m'
  | .diverges t, .diverges t' => t = t'
  | .reacts s, .reacts s' => s = s'
  | .goesWrong t, B' => Prefix t B'
  | _, _ => False

theorem InfiniteRun.prefix_nil {C : Type} {step : C → Trace → C → Prop} {start : C}
    (run : InfiniteRun step start) (h : ∀ n, run.traces n = E0) : ∀ n, run.prefix n = [] := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => rw [InfiniteRun.prefix_succ, ih, h n]; rfl

theorem FwdSim.behaves {C₁ R₁ M₁ C₂ R₂ M₂ : Type} {S : Semantics C₁ R₁ M₁}
    {T : Semantics C₂ R₂ M₂} (F : FwdSim S T) (FR : R₁ → M₁ → R₂ → M₂ → Prop)
    (hfinal : ∀ i s₁ s₂ r m, F.rel i s₁ s₂ → S.final s₁ r m →
      ∃ r' m', T.final s₂ r' m' ∧ FR r m r' m')
    {i : Nat} {s₁ : C₁} {s₂ : C₂} (hrel : F.rel i s₁ s₂) {B : Behavior R₁ M₁}
    (hB : Behaves S s₁ B) : ∃ B', Behaves T s₂ B' ∧ Matches FR B B' := by
  cases B with
  | terminates t r m =>
    obtain ⟨fin, hs, hf⟩ := hB
    obtain ⟨i', s₂', hs', hr⟩ := F.star hrel hs
    obtain ⟨r', m', hf', hfr⟩ := hfinal _ _ _ _ _ hr hf
    exact ⟨.terminates t r' m', ⟨s₂', hs', hf'⟩, rfl, hfr⟩
  | diverges t =>
    obtain ⟨tail, hs, run, hrun⟩ := hB
    obtain ⟨i', s₂', hs', hr⟩ := F.star hrel hs
    obtain ⟨run', h1, _⟩ := F.forever run hr
    have hnil := run.prefix_nil hrun
    have hnil' : ∀ k, run'.prefix k = [] := by
      intro k
      obtain ⟨n, hn⟩ := h1 k
      rw [hnil n] at hn
      exact List.prefix_nil.mp hn
    refine ⟨.diverges t, ⟨s₂', hs', run', fun n => ?_⟩, rfl⟩
    have := hnil' (n + 1)
    rw [InfiniteRun.prefix_succ] at this
    exact (List.append_eq_nil_iff.mp this).2
  | reacts stream =>
    obtain ⟨run, hr1, hr2⟩ := hB
    obtain ⟨run', h1, h2⟩ := F.forever run hrel
    refine ⟨.reacts stream, ⟨run', ?_, ?_⟩, rfl⟩
    · intro k
      obtain ⟨n, hn⟩ := h1 k
      exact tracePrefix_of_prefix hn (hr1 n)
    · intro N
      obtain ⟨n, hn⟩ := hr2 N
      obtain ⟨k, hk⟩ := h2 n
      exact ⟨k, Nat.le_trans hn hk.length_le⟩
  | goesWrong t =>
    obtain ⟨st, hs, _, _⟩ := hB
    obtain ⟨i', s₂', hs', _⟩ := F.star hrel hs
    obtain ⟨B0, hB0⟩ := exists_behavior T s₂'
    exact ⟨prependBehavior t B0, behaves_prepend T hs' hB0, prefix_prependBehavior t B0⟩

end EmbC.Clight.Behaviors
