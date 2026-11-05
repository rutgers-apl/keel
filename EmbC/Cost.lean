import EmbC.Cost.Rules

/-!
# Costed total correctness over the operational machine

`Prog.runC` instruments `Semantics.nextFor` and erases to `Prog.run` with the
same machine-step fuel. Both statement and function cost contracts reason
directly about this runner. `FnCost.run` combines finite cost execution
with the ordinary partial-correctness specification.
-/

namespace EmbC

variable {State : Type}

section rules
variable {P : Prog} {Q : (CPost P State)} {env : Env} {st : (KernelState P State)}

/-- A cost and a partial-correctness specification together: the call
finishes, its result satisfies the specification, and its cost the bound. -/
theorem FnCost.withSpec {f : String} {pre prec : List Val → (KernelState P State) → Prop}
    {post : List Val → (KernelState P State) → Option Val → (KernelState P State) → Prop}
    {postc : List Val → (KernelState P State) → Option Val → (KernelState P State) → Cost → Prop}
    (hs : FnSpec P f pre post) (hc : FnCost P f prec postc) :
    FnCost P f (fun vs st => pre vs st ∧ prec vs st)
      (fun vs st rv st' c => post vs st rv st' ∧ postc vs st rv st' c) := by
  intro vs st ⟨hp, hpc⟩
  obtain ⟨fuel, hf⟩ := hc vs st hpc
  refine ⟨fuel, ?_⟩
  have hw := hs fuel vs st hp
  rw [← runC_erase] at hw
  revert hf hw
  cases P.runC fuel f vs st with
  | timeout => intro hf; exact hf.elim
  | stuck => intro _ _; trivial
  | ok r => obtain ⟨rv, st', c⟩ := r; intro hf hw; exact ⟨hw, hf⟩

/-- **Total correctness with a cost.**  A function with a partial-correctness
specification and a cost returns, for some fuel, with a result satisfying both. -/
theorem FnCost.run {f : String} {pre prec : List Val → (KernelState P State) → Prop}
    {post : List Val → (KernelState P State) → Option Val → (KernelState P State) → Prop}
    {postc : List Val → (KernelState P State) → Option Val → (KernelState P State) → Cost → Prop}
    (hs : FnSpec P f pre post) (hc : FnCost P f prec postc) {vs : List Val}
    (hp : pre vs st) (hpc : prec vs st) :
    ∃ fuel rv st' c, P.run fuel f vs st = .ok (rv, st') ∧ P.runC fuel f vs st = .ok (rv, st', c) ∧
      post vs st rv st' ∧ postc vs st rv st' c := by
  obtain ⟨fuel, hf⟩ := hc vs st hpc
  have hw := hs fuel vs st hp
  have he := runC_erase P fuel f vs st
  rw [← he] at hw
  revert hf hw he
  cases hr : P.runC fuel f vs st with
  | timeout => intro hf; exact hf.elim
  | stuck => intro _ hw; exact hw.elim
  | ok r =>
    obtain ⟨rv, st', c⟩ := r
    intro hf hw he
    exact ⟨fuel, rv, st', c, he.symm, hr, hw, hf⟩

end rules

end EmbC
