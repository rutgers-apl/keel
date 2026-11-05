import EmbC.Cost.Continuation

/-! Function cost rules for actual call and return machine states. -/

namespace EmbC

variable {State : Type}
open Semantics

section
variable {P : Prog} {Q : (CPost P State)} {env : Env} {st : (KernelState P State)}

/-- Calling a function whose actual execution satisfies a cost contract. -/
theorem WPC.call {dst : Option Var} {f : String} {args : List Expr}
    {pre : List Val → (KernelState P State) → Prop}
    {post : List Val → (KernelState P State) → Option Val → (KernelState P State) → Cost → Prop}
    (hspec : FnCost P f pre post)
    (h : match evalArgs P env st.mem args with
      | none => True
      | some vs => pre vs st ∧ ∀ rv st' cost, post vs st rv st' cost →
        match assignDst env st'.mem dst rv with
        | none => True
        | some env' => Q .normal env' st' (cost + 2)) :
    WPC P (.call dst f args) Q env st := by
  intro k R hk
  cases ha : evalArgs P env st.mem args with
  | none =>
    apply MachineValidC.failed
    · simp [Semantics.nextFor, Semantics.nextCore, ha]
    · simp [Semantics.final, EmbC.Semantics.State.exec]
  | some vs =>
    have hp := h
    simp only [ha] at hp
    obtain ⟨hpre, hpost⟩ := hp
    have hc : MachineValidC P (post vs st) (Semantics.initial f vs st) true :=
      hspec vs st hpre
    have hcallee : MachineValidC P (fun rv st' cost => R rv st' (1 + cost))
        ((Semantics.initial f vs st).append (.call dst env k)) true := by
      apply MachineValidC.append_call hc
      intro rv st' cost hpc
      cases hb : assignDst env st'.mem dst rv with
      | none =>
        apply MachineValidC.failed
        · simp [Semantics.nextFor, Semantics.nextCore, hb]
        · simp [Semantics.final, EmbC.Semantics.State.returned]
      | some env' =>
        have hq : Q .normal env' st' (cost + 2) := by
          simpa only [hb] using hpost rv st' cost hpc
        have ho := hk .normal env' st' (cost + 2) hq
        apply MachineValidC.step
          (action := .silent (.exec .skip env' st' k))
          (by simp [Semantics.nextFor, Semantics.nextCore, hb])
        simp only [machineNextFresh, machineStepCost, Action.target]
        apply MachineValidC.mono ho
        intro rv' st'' later hr
        have heq : cost + 2 + later = 1 + (cost + (1 + later)) := by
          apply Cost.ext <;> simp <;> omega
        simpa only [heq] using hr
    apply MachineValidC.step
      (action := .silent (.call (.internal f) vs st (.call dst env k)))
      (by simp [Semantics.nextFor, Semantics.nextCore, ha])
    simp only [machineNextFresh, machineStepCost, Action.target]
    have ht : MachineValidC P (fun rv st' cost => R rv st' (1 + cost))
        (.call (.internal f) vs st (.call dst env k)) true := by
      simpa only [Semantics.initial, EmbC.Semantics.State.append, Cont.append] using hcallee
    exact ht.call_fresh false

/-- A function-body cost assertion includes the return-type boundary check. -/
def retPostC (rt : Option Ty) (R : Option Val → (KernelState P State) → Cost → Prop) : (CPost P State) :=
  fun o _ st' cost => match o, rt with
  | .normal, none => R none st' (cost + 1)
  | .ret none, none => R none st' cost
  | .ret (some value), some ty => st'.mem.hasTy value ty = true → R (some value) st' cost
  | _, _ => True

/-- A statement cost proof supplies a function contract by entering the
function body and checking its actual return continuation. -/
theorem FnCost.intro {f : String} {fn : Fn}
    {pre : List Val → (KernelState P State) → Prop}
    {post : List Val → (KernelState P State) → Option Val → (KernelState P State) → Cost → Prop}
    (hf : P.findFn f = some fn)
    (h : ∀ vs st, pre vs st → match bindParams st.mem fn.params vs with
      | none => True
      | some penv => WPC P fn.body (retPostC fn.ret (fun rv st' cost => post vs st rv st' (1 + cost)))
          (penv ++ initLocals fn.locals) st) : FnCost P f pre post := by
  intro vs st hp
  change MachineValidC P (post vs st) (Semantics.initial f vs st) true
  cases hb : bindParams st.mem fn.params vs with
  | none =>
    apply MachineValidC.failed
    · simp [Semantics.initial, Semantics.nextFor, Semantics.nextCore, hf, hb]
    · simp [Semantics.final, Semantics.initial, EmbC.Semantics.State.call, EmbC.Semantics.State.returned]
  | some penv =>
    have hw : WPC P fn.body (retPostC fn.ret (fun rv st' cost => post vs st rv st' (1 + cost)))
        (penv ++ initLocals fn.locals) st := by simpa only [hb] using h vs st hp
    have hbody : MachineValidC P (fun rv st' cost => post vs st rv st' (1 + cost))
        (.exec fn.body (penv ++ initLocals fn.locals) st (.function fn.ret .stop)) true := by
      apply hw
      intro o env' st' cost hpost
      cases o with
      | normal =>
        cases hrt : fn.ret with
        | none =>
          have hp' : post vs st none st' (1 + (cost + 1)) := by simpa [retPostC, hrt] using hpost
          change MachineValidC P (fun rv st'' c => post vs st rv st'' (1 + (cost + c)))
            (.exec .skip env' st' (.function none .stop)) false
          apply MachineValidC.step (action := .silent (.returned none st' .stop))
            (by simp [Semantics.nextFor, Semantics.nextCore])
          simp only [machineNextFresh, machineStepCost, Action.target]
          apply MachineValidC.final
          simpa using hp'
        | some ty =>
          apply MachineValidC.failed
          · simp [Semantics.nextFor, Semantics.nextCore]
          · simp [Semantics.final, EmbC.Semantics.State.exec]
      | brk =>
        apply MachineValidC.failed
        · simp [Semantics.nextFor, Semantics.nextCore]
        · simp [Semantics.final, EmbC.Semantics.State.exec]
      | ret rv =>
        cases rv with
        | none =>
          cases hrt : fn.ret with
          | none =>
            have hp' : post vs st none st' (1 + cost) := by simpa [retPostC, hrt] using hpost
            simp only [PostValidC, returnTarget, Cont.returnCont]
            apply MachineValidC.final
            simpa using hp'
          | some ty => simp [PostValidC, returnTarget, Cont.returnCont]
        | some value =>
          cases hrt : fn.ret with
          | none => simp [PostValidC, returnTarget, Cont.returnCont]
          | some ty =>
            by_cases ht : st'.mem.hasTy value ty = true
            · have hp' : post vs st (some value) st' (1 + cost) := by
                have hh : st'.mem.hasTy value ty = true → post vs st (some value) st' (1 + cost) := by
                  simpa [retPostC, hrt] using hpost
                exact hh ht
              simp only [PostValidC, returnTarget, Cont.returnCont, ht, ↓reduceIte]
              apply MachineValidC.final
              simpa using hp'
            · simp [PostValidC, returnTarget, Cont.returnCont, ht]
    apply MachineValidC.step
      (action := .silent (.exec fn.body (penv ++ initLocals fn.locals) st (.function fn.ret .stop)))
      (by simp [Semantics.initial, Semantics.nextFor, Semantics.nextCore, hf, hb])
    simpa only [Semantics.initial, machineStepCost, machineNextFresh, Action.target, Cost.zero_add] using hbody

theorem FnCost.mono {f : String} {pre pre' : List Val → (KernelState P State) → Prop}
    {post post' : List Val → (KernelState P State) → Option Val → (KernelState P State) → Cost → Prop}
    (h : FnCost P f pre post) (hpre : ∀ vs st, pre' vs st → pre vs st)
    (hpost : ∀ vs st rv st' cost, pre' vs st → post vs st rv st' cost → post' vs st rv st' cost) :
    FnCost P f pre' post' := by
  intro vs st hp
  obtain ⟨fuel, hc⟩ := h vs st (hpre vs st hp)
  exact ⟨fuel, CallResC.sat_mono hc (fun rv st' cost hh => hpost vs st rv st' cost hp hh)⟩

/-- Recursive function costs by well-founded induction on their inputs. -/
theorem FnCost.rec {f : String} {pre : List Val → (KernelState P State) → Prop}
    {post : List Val → (KernelState P State) → Option Val → (KernelState P State) → Cost → Prop}
    (μ : List Val → (KernelState P State) → Nat)
    (h : ∀ m, FnCost P f (fun vs st => pre vs st ∧ μ vs st < m) post →
      FnCost P f (fun vs st => pre vs st ∧ μ vs st = m) post) : FnCost P f pre post := by
  have H : ∀ m, FnCost P f (fun vs st => pre vs st ∧ μ vs st < m) post := by
    intro m
    induction m with
    | zero => intro vs st hp; exact absurd hp.2 (Nat.not_lt_zero _)
    | succ m ih =>
      intro vs st hp
      by_cases hm : μ vs st < m
      · exact ih vs st ⟨hp.1, hm⟩
      · exact h m ih vs st ⟨hp.1, by have := hp.2; omega⟩
  intro vs st hp
  exact H (μ vs st + 1) vs st ⟨hp, Nat.lt_succ_self _⟩

end
end EmbC
