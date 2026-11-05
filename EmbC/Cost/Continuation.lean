import EmbC.Cost.Logic

/-! Total cost reasoning by composition of operational continuations. -/

namespace EmbC

variable {State : Type}
open Semantics

theorem CallResC.sat_add_iff (r : (CallResC P State)) (cost : Cost)
    (R : Option Val → (KernelState P State) → Cost → Prop) :
    CallResC.sat (CallResC.add r cost) R ↔ r.sat (fun rv st c => R rv st (cost + c)) := by
  cases r with
  | timeout | stuck => rfl
  | ok result => rcases result with ⟨rv, st, c⟩; rfl

theorem MachineValidC.mono {P : Prog} {R R' : Option Val → (KernelState P State) → Cost → Prop}
    {state : (Semantics.ExecState P State)} {fresh : Bool} (h : MachineValidC P R state fresh)
    (hq : ∀ rv st cost, R rv st cost → R' rv st cost) :
    MachineValidC P R' state fresh := by
  obtain ⟨fuel, h⟩ := h
  refine ⟨fuel, ?_⟩
  cases hr : machineRunC P fuel state fresh with
  | timeout => simpa [hr, CallResC.sat] using h
  | stuck => trivial
  | ok result =>
    rcases result with ⟨rv, st, cost⟩
    exact hq rv st cost (by simpa [hr, CallResC.sat] using h)

theorem MachineValidC.step {P : Prog} {R : Option Val → (KernelState P State) → Cost → Prop}
    {state : (Semantics.ExecState P State)} {fresh : Bool} {action : (ExecAction P State)}
    (hn : Semantics.nextFor P state = some action)
    (h : MachineValidC P (fun rv st cost => R rv st (machineStepCost P state fresh + cost))
      action.target (machineNextFresh P state)) : MachineValidC P R state fresh := by
  obtain ⟨fuel, h⟩ := h
  refine ⟨fuel + 1, ?_⟩
  simp only [machineRunC, machineRunCCore, hn]
  exact (CallResC.sat_add_iff _ _ _).mpr h

theorem MachineValidC.failed {P : Prog} {R : Option Val → (KernelState P State) → Cost → Prop}
    {state : (Semantics.ExecState P State)} {fresh : Bool}
    (hn : Semantics.nextFor P state = none) (hf : ¬ Semantics.final state) :
    MachineValidC P R state fresh := by
  refine ⟨1, ?_⟩
  simp only [machineRunC, machineRunCCore, hn]
  cases state with
  | regular | callstate => trivial
  | returnstate rv mem orc k =>
    cases k with
    | stop => exact (hf ⟨rv, ⟨mem, orc⟩, rfl⟩).elim
    | seq | loop | function | call => trivial

theorem MachineValidC.final {P : Prog} {R : Option Val → (KernelState P State) → Cost → Prop}
    {rv : Option Val} {st : (KernelState P State)} {fresh : Bool} (h : R rv st 0) :
    MachineValidC P R (.returned rv st .stop) fresh := by
  exact ⟨1, h⟩

theorem machineRunC_returned_fresh (P : Prog) (fuel : Nat) (rv : Option Val)
    (st : (KernelState P State)) (k : Cont) (a b : Bool) :
    machineRunC P fuel (.returned rv st k) a = machineRunC P fuel (.returned rv st k) b := by
  cases fuel <;> rfl

theorem machineRunC_call_fresh (P : Prog) (fuel : Nat) (callee : Callee)
    (args : List Val) (st : (KernelState P State)) (k : Cont) (a b : Bool) :
    machineRunC P fuel (.call callee args st k) a = machineRunC P fuel (.call callee args st k) b := by
  cases fuel <;> cases callee <;> rfl

theorem MachineValidC.returned_fresh {P : Prog} {R : Option Val → (KernelState P State) → Cost → Prop}
    {rv : Option Val} {st : (KernelState P State)} {k : Cont} {a : Bool}
    (h : MachineValidC P R (.returned rv st k) a) (b : Bool) :
    MachineValidC P R (.returned rv st k) b := by
  obtain ⟨fuel, h⟩ := h
  exact ⟨fuel, by simpa only [machineRunC_returned_fresh P fuel rv st k b a] using h⟩

theorem MachineValidC.call_fresh {P : Prog} {R : Option Val → (KernelState P State) → Cost → Prop}
    {callee : Callee} {args : List Val} {st : (KernelState P State)} {k : Cont} {a : Bool}
    (h : MachineValidC P R (.call callee args st k) a) (b : Bool) :
    MachineValidC P R (.call callee args st k) b := by
  obtain ⟨fuel, h⟩ := h
  exact ⟨fuel, by simpa only [machineRunC_call_fresh P fuel callee args st k b a] using h⟩

theorem machineStepCost_append_call (P : Prog) (state : (Semantics.ExecState P State)) (fresh : Bool)
    (dst : Option Var) (env : Env) (k : Cont) :
    machineStepCost P (state.append (.call dst env k)) fresh = machineStepCost P state fresh := by
  cases state with
  | regular s env mem orc cont => cases s <;> rfl
  | callstate callee args mem orc cont => cases callee <;> rfl
  | returnstate => rfl

theorem machineNextFresh_append_call (P : Prog) (state : (Semantics.ExecState P State))
    (dst : Option Var) (env : Env) (k : Cont) :
    machineNextFresh P (state.append (.call dst env k)) = machineNextFresh P state := by
  cases state with
  | regular s env mem orc cont =>
    cases s <;> try rfl
    case skip => cases cont <;> rfl
  | callstate callee args mem orc cont => cases callee <;> rfl
  | returnstate => rfl

theorem append_call_not_final (state : (Semantics.ExecState P State)) (dst : Option Var)
    (env : Env) (k : Cont) : ¬ Semantics.final (state.append (.call dst env k)) := by
  cases state with
  | regular | callstate => simp [Semantics.final, EmbC.Semantics.State.append, EmbC.Semantics.State.returned]
  | returnstate rv mem orc cont =>
    cases cont <;> simp [Semantics.final, EmbC.Semantics.State.append, EmbC.Semantics.State.returned, Cont.append]

/-- A completed callee computation can be followed by a caller. Costs from
the callee prefix are added to costs of the resumed caller; no evaluator
other than the operational machine is involved. -/
theorem MachineValidC.append_call {P : Prog}
    {Post R : Option Val → (KernelState P State) → Cost → Prop}
    {state : (Semantics.ExecState P State)} {fresh : Bool} {dst : Option Var} {env : Env} {k : Cont}
    (hc : MachineValidC P Post state fresh)
    (hk : ∀ rv st cost, Post rv st cost →
      MachineValidC P (fun rv' st' cost' => R rv' st' (cost + cost'))
        (.returned rv st (.call dst env k)) false) :
    MachineValidC P R (state.append (.call dst env k)) fresh := by
  obtain ⟨fuel, hc⟩ := hc
  induction fuel generalizing state fresh Post R with
  | zero => simp [machineRunC, machineRunCCore, CallResC.sat] at hc
  | succ fuel ih =>
    by_cases hf : ∃ rv st, state = .returned rv st .stop
    · obtain ⟨rv, st, rfl⟩ := hf
      have hp : Post rv st 0 := by simpa [machineRunC, machineRunCCore, Semantics.nextFor, Semantics.nextCore, CallResC.sat] using hc
      have ht := (hk rv st 0 hp).mono (fun rv' st' c h => by simpa using h)
      change MachineValidC P R (.returned rv st (.call dst env k)) fresh
      exact ht.returned_fresh fresh
    · have hnf : ∀ rv st, state ≠ .returned rv st .stop := by
        intro rv st he; exact hf ⟨rv, st, he⟩
      cases hn : Semantics.nextFor P state with
      | none =>
        apply MachineValidC.failed
        · rw [Semantics.next_append_call hnf, hn]; rfl
        · exact append_call_not_final state dst env k
      | some action =>
        have ht : (machineRunC P fuel action.target (machineNextFresh P state)).sat
            (fun rv st cost => Post rv st (machineStepCost P state fresh + cost)) := by
          apply (CallResC.sat_add_iff _ _ _).mp
          simpa only [machineRunC, machineRunCCore, hn] using hc
        apply MachineValidC.step (action := action.append (.call dst env k))
          (by rw [Semantics.next_append_call hnf, hn]; rfl)
        simp only [Action.append_target, machineStepCost_append_call, machineNextFresh_append_call]
        refine ih ?_ ht
        intro rv st cost hp
        exact (hk rv st (machineStepCost P state fresh + cost) hp).mono
          (fun rv' st' c h => by simpa only [Cost.add_assoc] using h)

end EmbC
