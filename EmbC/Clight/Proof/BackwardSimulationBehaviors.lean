import EmbC.Clight.Proof.BackwardSimulation

/-!
# Behaviors from a standard backward simulation

This proof uses only the simulation record, not the segment property or its
behavior-preservation theorem. A failed local safety guard gives a silently
reachable source error. Well-founded induction rules out infinite sequences
of target steps matched by no source steps.
-/

namespace EmbC.Clight.Behaviors

open CC (E0 Eapp Trace)

variable {C₁ R₁ M₁ C₂ R₂ M₂ Index : Type}
  {S : Semantics C₁ R₁ M₁} {T : Semantics C₂ R₂ M₂}
  {sourceInitial : C₁ → Prop} {targetInitial : C₂ → Prop}
  {FR : R₁ → M₁ → R₂ → M₂ → Prop}

theorem not_safe_stuck {c : C₁} (h : ¬ Safe S c) :
    ∃ failed, Star S.step c E0 failed ∧ Stuck S failed := by
  classical
  by_cases hex : ∃ failed, Star S.step c E0 failed ∧ Stuck S failed
  · exact hex
  · exfalso
    apply h
    intro failed hp
    by_cases hf : ∃ r m, S.final failed r m
    · exact .inl hf
    by_cases hs : ∃ t c', S.step failed t c'
    · exact .inr hs
    exact (hex ⟨failed, hp, (fun t c' ht => hs ⟨t, c', ht⟩),
      (fun r m hr => hf ⟨r, m, hr⟩)⟩).elim

theorem BackwardSimulation.finite
    (B : BackwardSimulation S T sourceInitial targetInitial FR Index) :
    ∀ n i c X t Y, B.matchStates i c X → StarN T.step n X t Y →
      (∃ failed u, Star S.step c u failed ∧ Stuck S failed ∧ u <+: t) ∨
      ∃ i' c', Star S.step c t c' ∧ B.matchStates i' c' Y ∧ Safe S c' := by
  classical
  intro n
  induction n with
  | zero =>
    intro i c X t Y hr hp
    cases hp
    by_cases hs : Safe S c
    · exact .inr ⟨i, c, Star.refl c, hr, hs⟩
    · obtain ⟨failed, hp, hf⟩ := not_safe_stuck hs
      exact .inl ⟨failed, E0, hp, hf, List.nil_prefix⟩
  | succ n ih =>
    intro i c X t Y hr hp
    by_cases hs : Safe S c
    · cases hp with
      | @step _ _ X' _ t₁ t₂ ht tail =>
        obtain ⟨i', c', hmove, hr'⟩ := B.simulation _ _ _ ht _ _ hr hs
        have hstar : Star S.step c t₁ c' := hmove.elim Plus.star And.left
        rcases ih i' c' X' t₂ Y hr' tail with ⟨failed, u, hp', hf, hu⟩ |
            ⟨i'', c'', hp', hr'', hs'⟩
        · exact .inl ⟨failed, t₁ ++ u, hstar.trans hp', hf,
            (List.prefix_append_right_inj t₁).mpr hu⟩
        · exact .inr ⟨i'', c'', hstar.trans hp', hr'', hs'⟩
    · obtain ⟨failed, hp', hf⟩ := not_safe_stuck hs
      exact .inl ⟨failed, E0, hp', hf, List.nil_prefix⟩

/-- The alternate diagram separates genuine source progress from a target-only
silent step with unchanged source state and decreasing rank. -/
theorem BackwardSimulation.simulation'
    (B : BackwardSimulation S T sourceInitial targetInitial FR Index)
    {X t X'} (ht : T.step X t X') {i c} (hr : B.matchStates i c X) (hs : Safe S c) :
    (∃ i' c', Plus S.step c t c' ∧ B.matchStates i' c' X') ∨
    ∃ i', B.order i' i ∧ t = E0 ∧ B.matchStates i' c X' := by
  obtain ⟨i', c', hm, hr'⟩ := B.simulation _ _ _ ht _ _ hr hs
  rcases hm with hp | ⟨hp, ho⟩
  · exact .inl ⟨i', c', hp, hr'⟩
  · cases hp with
    | refl => exact .inr ⟨i', ho, rfl, hr'⟩
    | step h tail => exact .inl ⟨i', _, Plus.intro h tail, hr'⟩

private structure BRunState (Index C : Type) where
  index : Index
  source : C
  position : Nat

theorem BackwardSimulation.infinite
    (B : BackwardSimulation S T sourceInitial targetInitial FR Index)
    {i : Index} {c : C₁} {X : C₂} (hr : B.matchStates i c X)
    (run : InfiniteRun T.step X) :
    (∃ failed u k, Star S.step c u failed ∧ Stuck S failed ∧ u <+: run.prefix k) ∨
    ∃ run' : InfiniteRun S.step c,
      (∀ k, ∃ n, run'.prefix k <+: run.prefix n) ∧
      (∀ n, ∃ k, run.prefix n <+: run'.prefix k) := by
  classical
  let Good : BRunState Index C₁ → Prop := fun q =>
    Star S.step c (run.prefix q.position) q.source ∧
      B.matchStates q.index q.source (run.states q.position)
  by_cases hbad : ∃ q, Good q ∧ ¬ Safe S q.source
  · obtain ⟨q, ⟨hp, _⟩, hs⟩ := hbad
    obtain ⟨failed, hp', hf⟩ := not_safe_stuck hs
    exact .inl ⟨failed, run.prefix q.position, q.position,
      by simpa [E0] using hp.trans hp', hf, List.prefix_refl _⟩
  right
  have hsafe : ∀ q, Good q → Safe S q.source := by
    intro q hq
    by_cases hs : Safe S q.source
    · exact hs
    · exact (hbad ⟨q, hq, hs⟩).elim
  have hchunk : ∀ j c₁ n, Good ⟨j, c₁, n⟩ →
      ∃ q' : BRunState Index C₁, Good q' ∧ ∃ u,
        n < q'.position ∧ Plus S.step c₁ u q'.source ∧
        run.prefix n ++ u = run.prefix q'.position := by
    intro j
    refine B.order_wf.induction (C := fun j => ∀ c₁ n, Good ⟨j, c₁, n⟩ →
      ∃ q' : BRunState Index C₁, Good q' ∧ ∃ u,
        n < q'.position ∧ Plus S.step c₁ u q'.source ∧
        run.prefix n ++ u = run.prefix q'.position) j ?_
    intro j ih c₁ n hq
    rcases B.simulation' (run.steps n) hq.2 (hsafe _ hq) with
      ⟨j', c', hp, hr'⟩ | ⟨j', ho, ht, hr'⟩
    · refine ⟨⟨j', c', n + 1⟩, ⟨?_, hr'⟩, run.traces n, by simp, hp, rfl⟩
      exact hq.1.trans hp.star
    · have hpre : run.prefix (n + 1) = run.prefix n := by
        rw [InfiniteRun.prefix_succ, ht]; simp [E0]
      have hq' : Good ⟨j', c₁, n + 1⟩ := ⟨hpre.symm ▸ hq.1, hr'⟩
      obtain ⟨q', hg, u, hn, hp, he⟩ := ih j' ho c₁ (n + 1) hq'
      exact ⟨q', hg, u, by omega, hp, by simpa only [hpre] using he⟩
  have hnext : ∀ q : {q // Good q}, ∃ q' : {q // Good q}, ∃ u,
      q.1.position < q'.1.position ∧ Plus S.step q.1.source u q'.1.source ∧
        run.prefix q.1.position ++ u = run.prefix q'.1.position := by
    intro q
    obtain ⟨q', hg, u, hn, hp, he⟩ := hchunk q.1.index q.1.source q.1.position q.2
    exact ⟨⟨q', hg⟩, u, hn, hp, he⟩
  let seq : Nat → {q // Good q} := fun k => Nat.rec
    (motive := fun _ => {q // Good q})
    ⟨⟨i, c, 0⟩, by
      refine ⟨Star.refl c, ?_⟩
      simpa only [run.initial] using hr⟩
    (fun _ q => Classical.choose (hnext q)) k
  have hspec : ∀ k, ∃ u,
      (seq k).1.position < (seq (k + 1)).1.position ∧
      Plus S.step (seq k).1.source u (seq (k + 1)).1.source ∧
      run.prefix (seq k).1.position ++ u = run.prefix (seq (k + 1)).1.position := by
    intro k
    exact Classical.choose_spec (hnext (seq k))
  have hn : ∀ k, k ≤ (seq k).1.position := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih => obtain ⟨_, hh, _, _⟩ := hspec k; omega
  obtain ⟨run', h1, h2⟩ := flatten (R := S.step)
    (fun k => (seq k).1.source) (fun k => run.prefix (seq k).1.position) rfl
    (fun k => by obtain ⟨u, _, hp, he⟩ := hspec k; exact ⟨u, hp, he⟩)
  exact ⟨run', fun k => by
    obtain ⟨n, hn⟩ := h1 k
    exact ⟨_, hn⟩, fun n => by
    obtain ⟨k, hk⟩ := h2 n
    exact ⟨k, hk ▸ run.prefix_mono (hn n)⟩⟩

/-- Unconditional behavior improvement from the standard simulation record.
Source errors discharge unsafe cases; a global source-safety premise is not
needed. Kernel/oracle choices belong to the source step relation supplied to
the record, and are not assumed deterministic. -/
theorem BackwardSimulation.behaves
    (B : BackwardSimulation S T sourceInitial targetInitial FR Index)
    {i : Index} {c : C₁} {X : C₂} (hr : B.matchStates i c X)
    {B' : Behavior R₂ M₂} (hb : Behaves T X B') :
    ∃ B₁, Behaves S c B₁ ∧ Matches FR B₁ B' := by
  cases B' with
  | terminates t r' m' =>
    obtain ⟨fin, hp, hf⟩ := hb
    obtain ⟨n, hn⟩ := hp.starN
    rcases B.finite n i c X t fin hr hn with ⟨failed, u, hp', hst, hu⟩ |
        ⟨i', c', hp', hr', hs⟩
    · exact ⟨.goesWrong u, ⟨failed, hp', hst⟩, hu⟩
    · obtain ⟨fin', r, m, htail, hf', hfr⟩ := B.match_final_states _ _ _ _ _ hr' hs hf
      exact ⟨.terminates t r m, ⟨fin', by simpa [E0] using hp'.trans htail, hf'⟩,
        rfl, hfr⟩
  | goesWrong t =>
    obtain ⟨fin, hp, hno, hnf⟩ := hb
    obtain ⟨n, hn⟩ := hp.starN
    rcases B.finite n i c X t fin hr hn with ⟨failed, u, hp', hst, hu⟩ |
        ⟨i', c', _, hr', hs⟩
    · exact ⟨.goesWrong u, ⟨failed, hp', hst⟩, hu⟩
    · rcases B.progress _ _ _ hr' hs with ⟨r, m, hf⟩ | ⟨t', Y, ht⟩
      · exact (hnf r m hf).elim
      · exact (hno t' Y ht).elim
  | diverges t =>
    obtain ⟨tail, hp, run0, hsil⟩ := hb
    obtain ⟨run, k0, hk0, hsil'⟩ := star_silent_run hp run0 hsil
    have hle : ∀ k, run.prefix k <+: t := by
      intro k
      rcases Nat.le_total k k0 with h | h
      · exact hk0 ▸ run.prefix_mono h
      · suffices H : ∀ d, run.prefix (k0 + d) = t by
          obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
          rw [H d]; exact List.prefix_refl _
        intro d
        induction d with
        | zero => exact hk0
        | succ d ih =>
          rw [← Nat.add_assoc, InfiniteRun.prefix_succ, ih, hsil' _ (by omega)]
          simp [E0]
    rcases B.infinite hr run with ⟨failed, u, k, hp', hst, hu⟩ | ⟨run', h1, h2⟩
    · exact ⟨.goesWrong u, ⟨failed, hp', hst⟩, hu.trans (hle k)⟩
    · refine ⟨.diverges t, diverges_of_run run' (fun k => ?_) ?_, rfl⟩
      · obtain ⟨n, hn⟩ := h1 k; exact hn.trans (hle n)
      · obtain ⟨k, hk⟩ := h2 k0; exact ⟨k, hk0 ▸ hk⟩
  | reacts stream =>
    obtain ⟨run, hr1, hr2⟩ := hb
    rcases B.infinite hr run with ⟨failed, u, k, hp', hst, hu⟩ | ⟨run', h1, h2⟩
    · exact ⟨.goesWrong u, ⟨failed, hp', hst⟩, tracePrefix_of_prefix hu (hr1 k)⟩
    · refine ⟨.reacts stream, ⟨run', ?_, ?_⟩, rfl⟩
      · intro k
        obtain ⟨n, hn⟩ := h1 k; exact tracePrefix_of_prefix hn (hr1 n)
      · intro n
        obtain ⟨k, hk⟩ := hr2 n
        obtain ⟨m, hm⟩ := h2 k
        exact ⟨m, Nat.le_trans hk hm.length_le⟩

end EmbC.Clight.Behaviors
