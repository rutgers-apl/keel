import EmbC.Cost.Basic

/-! Cost instrumentation of the operational machine. Every execution
transition obtained from `Semantics.nextFor` costs one unit, in addition to
external-operation work. The legacy `fresh` flag changes no accounting.
-/

namespace EmbC

variable {State : Type}

/-- Add the cost of an earlier transition to a completed function run. -/
def CallResC.add (r : CallResCCore State) (k : Cost) : CallResCCore State :=
  match r with
  | .ok (rv, st, c) => .ok (rv, st, k + c)
  | .timeout => .timeout
  | .stuck => .stuck

@[simp] theorem CallResC.erase_add (r : CallResCCore State) (k : Cost) :
    (CallResC.add r k).eraseC = r.eraseC := by
  cases r with
  | ok result => rcases result with ⟨rv, st, c⟩; rfl
  | timeout => rfl
  | stuck => rfl

/-- Every actual transition costs one unit. External work is charged
when the external operation returns. The final state has no transition. -/
def machineStepCost (P : Prog) (state : Semantics.State State) (_fresh : Bool) : Cost :=
  match state with
  | .callstate (.external ext) args _ _ _ => 1 + Ext.costC P ext args
  | _ => 1

/-- Whether a transition enters a new source statement. Primitive updates,
loop exits, break propagation and result binding introduce administrative
states; branch/sequence/loop entries resume source statements. -/
def machineNextFresh (P : Prog) (state : Semantics.State State) : Bool :=
  match state with
  | .regular (.skip) _ _ _ k => match k with
    | .seq .. | .loop .. => true
    | _ => false
  | .regular (.seq ..) _ _ _ _
  | .regular (.ite ..) _ _ _ _ => true
  | .regular (.while condition _) env mem _ _ =>
    match evalE P env mem condition with
    | some (.u32 value) => value != 0
    | _ => false
  | .callstate (.internal _) _ _ _ _ => true
  | _ => false

/-- The sole bounded cost driver, parameterized by the operational successor.
The ghost flag changes no transition, result, memory or oracle. -/
abbrev machineRunCCore (P : Prog)
    (step : Semantics.State State → Option (Semantics.Action State)) :
    Nat → Semantics.State State → Bool → CallResCCore State
  | 0, _, _ => .timeout
  | fuel + 1, state, fresh =>
    match step state with
    | some action =>
      CallResC.add (machineRunCCore P step fuel action.target (machineNextFresh P state))
        (machineStepCost P state fresh)
    | none => match state with
      | .returnstate rv mem orc .stop => .ok (rv, ⟨mem, orc⟩, 0)
      | _ => .stuck

/-- Cost execution uses the oracle carried by the executable state. -/
def machineRunC (P : Prog) : Nat → Semantics.ExecState P State → Bool → CallResC P State :=
  machineRunCCore P (Semantics.nextFor P)

/-- The cost runner has exactly the operational machine's step budget. -/
def Prog.runC (P : Prog) (fuel : Nat) (f : String) (vs : List Val)
    (st : KernelState P State) : CallResC P State :=
  machineRunC P fuel (Semantics.initial f vs st) true

theorem machineRunCCore_erase (P : Prog)
    (step : Semantics.State State → Option (Semantics.Action State)) : ∀ fuel state fresh,
    (machineRunCCore P step fuel state fresh).eraseC = Semantics.runCore step fuel state := by
  intro fuel
  induction fuel with
  | zero => intro state fresh; rfl
  | succ fuel ih =>
    intro state fresh
    simp only [machineRunCCore, Semantics.runCore]
    cases hn : step state with
    | some action => simp only [CallResC.erase_add]; exact ih _ _
    | none =>
      cases state with
      | regular | callstate => rfl
      | returnstate rv mem orc cont => cases cont <;> rfl

theorem machineRunC_erase (P : Prog) : ∀ fuel state fresh,
    (machineRunC (State := State) P fuel state fresh).eraseC = Semantics.run P fuel state :=
  machineRunCCore_erase P (Semantics.nextFor P)

theorem runC_erase (P : Prog) (fuel : Nat) (f : String) (vs : List Val)
    (st : KernelState P State) : (P.runC fuel f vs st).eraseC = P.run fuel f vs st :=
  machineRunC_erase P fuel (Semantics.initial f vs st) true

theorem machineRunCCore_mono {P : Prog}
    {step : Semantics.State State → Option (Semantics.Action State)}
    {n m : Nat} {state : Semantics.State State} {fresh : Bool} {r : CallResCCore State}
    (h : machineRunCCore P step n state fresh = r) (hr : r ≠ .timeout) (hnm : n ≤ m) :
    machineRunCCore P step m state fresh = r := by
  induction n generalizing m state fresh r with
  | zero => simp [machineRunCCore] at h; subst r; exact (hr rfl).elim
  | succ n ih =>
    cases m with
    | zero => omega
    | succ m =>
      simp only [machineRunCCore] at h ⊢
      cases hn : step state with
      | none => simpa [hn] using h
      | some action =>
        simp only [hn] at h ⊢
        cases hs : machineRunCCore P step n action.target (machineNextFresh P state) with
        | timeout => simp [hs, CallResC.add] at h; subst r; exact (hr rfl).elim
        | stuck =>
          have hm := ih (m := m) hs (by simp) (by omega)
          simpa [hs, hm] using h
        | ok result =>
          have hm := ih (m := m) hs (by simp) (by omega)
          simpa [hs, hm] using h

theorem machineRunC_mono {P : Prog} {n m : Nat} {state : Semantics.ExecState P State}
    {fresh : Bool} {r : CallResC P State} (h : machineRunC P n state fresh = r)
    (hr : r ≠ .timeout) (hnm : n ≤ m) : machineRunC P m state fresh = r :=
  machineRunCCore_mono h hr hnm

theorem runC_mono (P : Prog) {fuel : Nat} {f : String} {vs : List Val}
    {st : KernelState P State} (hne : P.runC fuel f vs st ≠ .timeout) :
    ∀ m, fuel ≤ m → P.runC m f vs st = P.runC fuel f vs st := by
  intro m hm
  exact machineRunC_mono rfl hne hm

end EmbC
