import EmbC.Cost.Machine

/-!
Direct total-cost assertions for the operational machine. Statement
assertions quantify over the actual continuation; function assertions
observe `Prog.runC` itself. Failure is admitted here and excluded when a
cost theorem is combined with an ordinary safety specification.
-/

namespace EmbC

variable {State : Type}

abbrev CPost (P : Prog) (State : Type) := Outcome → Env → (KernelState P State) → Cost → Prop

/-- A completed machine result satisfies its postcondition; failure is
allowed, but exhausting the execution budget is not. -/
def CallResC.sat (r : (CallResC P State)) (R : Option Val → (KernelState P State) → Cost → Prop) : Prop :=
  match r with
  | .timeout => False
  | .stuck => True
  | .ok (rv, st, c) => R rv st c

theorem CallResC.sat_ne {r : (CallResC P State)} {R : Option Val → (KernelState P State) → Cost → Prop}
    (h : r.sat R) : r ≠ .timeout := by
  intro he; subst he; exact h

theorem CallResC.sat_mono {r : (CallResC P State)}
    {R R' : Option Val → (KernelState P State) → Cost → Prop} (h : r.sat R)
    (hr : ∀ rv st c, R rv st c → R' rv st c) : r.sat R' := by
  cases r with
  | timeout => exact h
  | stuck => trivial
  | ok result => rcases result with ⟨rv, st, c⟩; exact hr rv st c h

/-- A finite run of the actual costed operational machine. -/
def MachineValidC (P : Prog) (R : Option Val → (KernelState P State) → Cost → Prop)
    (state : (Semantics.ExecState P State)) (fresh : Bool) : Prop :=
  ∃ fuel, (machineRunC P fuel state fresh).sat R

/-- A statement outcome resumes its real continuation. The cost already
spent by the statement is added to the continuation's eventual cost. -/
def PostValidC (P : Prog) (R : Option Val → (KernelState P State) → Cost → Prop)
    (o : Outcome) (env : Env) (st : (KernelState P State)) (cost : Cost) (k : Semantics.Cont) : Prop :=
  let after := fun rv st' c => R rv st' (cost + c)
  match o with
  | .normal => MachineValidC P after (.exec .skip env st k) false
  | .brk => MachineValidC P after (.exec .brk env st k) false
  | .ret rv => match Semantics.returnTarget rv st k with
    | none => True
    | some target => MachineValidC P after target false

/-- Total cost correctness of a statement, directly over the machine and
all continuations satisfying its logical outcome obligations. -/
def WPC (P : Prog) (s : Stmt) (Q : (CPost P State)) (env : Env) (st : (KernelState P State)) : Prop :=
  ∀ (k : Semantics.Cont) (R : Option Val → (KernelState P State) → Cost → Prop),
    (∀ o env' st' c, Q o env' st' c → PostValidC P R o env' st' c k) →
    MachineValidC P R (.exec s env st k) true

/-- A function's actual costed execution terminates or fails in finite
machine-step fuel and satisfies its cost postcondition if it returns. -/
def FnCost (P : Prog) (f : String) (pre : List Val → (KernelState P State) → Prop)
    (post : List Val → (KernelState P State) → Option Val → (KernelState P State) → Cost → Prop) : Prop :=
  ∀ vs st, pre vs st → ∃ fuel, (P.runC fuel f vs st).sat (post vs st)

def CPost.shift (Q : (CPost P State)) (k : Cost) : (CPost P State) := fun o env st c => Q o env st (k + c)

@[simp] theorem CPost.shift_apply (Q : (CPost P State)) (k : Cost) (o : Outcome) (env : Env)
    (st : (KernelState P State)) (c : Cost) : Q.shift k o env st c = Q o env st (k + c) := rfl

theorem WPC.mono {P : Prog} {s : Stmt} {Q Q' : (CPost P State)} {env : Env} {st : (KernelState P State)}
    (h : WPC P s Q env st) (hq : ∀ o env' st' c, Q o env' st' c → Q' o env' st' c) :
    WPC P s Q' env st := by
  intro k R hk
  exact h k R (fun o env' st' c ho => hk o env' st' c (hq o env' st' c ho))

end EmbC
