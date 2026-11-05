import EmbC.Eval

/-!
# EmbC operational semantics

The machine has regular, call, and return states, as in CompCert. `nextCore`
is the single execution core; `nextFor` uses the certified oracle carried in each state.
An undefined non-final state has no successor. `run` supplies a finite
step budget to this same machine. Contract transitions admit all specified replies.
-/

namespace EmbC.Semantics

inductive Cont where
  | stop
  | seq (next : Stmt) (k : Cont)
  | loop (condition : Expr) (body : Stmt) (k : Cont)
  | function (returnType : Option Ty) (k : Cont)
  | call (dst : Option Var) (caller : Env) (k : Cont)

/-- Internal functions and kernel operations share the call-state protocol. -/
inductive Callee where
  | internal (name : String)
  | external (ext : Ext)

/-- A machine state. The heap and private oracle are components, not control states. -/
inductive State (External : Type := Unit) where
  | regular (stmt : Stmt) (env : Env) (mem : Mem) (oracle : External) (k : Cont)
  | callstate (callee : Callee) (args : List Val) (mem : Mem) (oracle : External) (k : Cont)
  | returnstate (result : Option Val) (mem : Mem) (oracle : External) (k : Cont)

abbrev ExecState (P : Prog) (State : Type) := EmbC.Semantics.State (Oracle P State)

variable {External : Type}

/-- Reducible construction helpers for kernel specifications, which package
memory and oracle together. The machine itself stores them as separate fields. -/
abbrev State.exec (stmt : Stmt) (env : Env) (st : MachineStore External) (k : Cont) : State External :=
  .regular stmt env st.mem st.oracle k

abbrev State.call (callee : Callee) (args : List Val) (st : MachineStore External) (k : Cont) : State External :=
  .callstate callee args st.mem st.oracle k

abbrev State.returned (rv : Option Val) (st : MachineStore External) (k : Cont) : State External :=
  .returnstate rv st.mem st.oracle k

def initial (f : String) (args : List Val) (st : MachineStore External) : State External :=
  .call (.internal f) args st .stop

def stateKernelState : State External → MachineStore External
  | .regular _ _ mem orc _ | .callstate _ _ mem orc _ | .returnstate _ mem orc _ => ⟨mem, orc⟩

def stateEnv : State External → Option Env
  | .regular _ env _ _ _ => some env
  | _ => none

/-- A final state is a return to the top-level caller. -/
def final (c : State External) : Prop := ∃ rv st, c = .returned rv st .stop

/-- Replace only the private oracle; control, locals, and heap are unchanged. -/
def State.withOracle {Other : Type} (c : State External) (oracle : Other) : State Other :=
  match c with
  | .regular s env mem _ k => .regular s env mem oracle k
  | .callstate f args mem _ k => .callstate f args mem oracle k
  | .returnstate rv mem _ k => .returnstate rv mem oracle k

/-- Find the enclosing function, discarding statement and loop continuations.
A return is not allowed to cross an already suspended caller. -/
def Cont.returnCont : Cont → Option (Option Ty × Cont)
  | .seq _ k | .loop _ _ k => k.returnCont
  | .function rt k => some (rt, k)
  | .stop | .call _ _ _ => none

/-- Evaluate the function-boundary check after evaluating a return expression.
This is a transition helper, not an additional machine-state form. -/
def returnTarget (rv : Option Val) (st : MachineStore External) (k : Cont) : Option (State External) :=
  match k.returnCont with
  | some (none, k') => match rv with
    | none => some (.returned none st k')
    | some _ => none
  | some (some t, k') => match rv with
    | some v => if st.mem.hasTy v t then some (.returned (some v) st k') else none
    | none => none
  | none => none

inductive Action (External : Type := Unit) where
  | silent (target : State External)
  | external (ext : Ext) (args : List Val) (before : MachineStore External)
      (result : Option Val) (after : MachineStore External) (target : State External)

abbrev ExecAction (P : Prog) (State : Type) := Action (Oracle P State)

def Action.target : Action External → State External
  | .silent target | .external _ _ _ _ _ target => target

/-- One machine step. Undefined operations have no successor. Kernel calls
produce their observation when they return; binding a result is a later step,
so even a subsequent binding failure retains the observation and updated heap. -/
abbrev nextCore (P : Prog)
    (kernel : Ext → List Val → MachineStore External → Option (Option Val × MachineStore External)) :
    State External → Option (Action External)
  | .regular stmt env mem orc k =>
    let st : MachineStore External := ⟨mem, orc⟩
    match stmt with
    | .skip => match k with
      | .seq b k' => some (.silent (.exec b env st k'))
      | .loop condition body k' => some (.silent (.exec (.while condition body) env st k'))
      | .function none k' => some (.silent (.returned none st k'))
      | _ => none
    | .assign x e =>
      match evalE P env st.mem e with
      | none => none
      | some v => match env.assign st.mem x v with
        | none => none
        | some env' => some (.silent (.exec .skip env' st k))
    | .store p i e =>
      match evalE P env st.mem p, evalE P env st.mem i, evalE P env st.mem e with
      | some (.ptr b off), some vi, some v =>
        match vi.toIdx with
        | none => none
        | some index => match st.mem.storeArr b (off + index) v with
          | none => none
          | some mem => some (.silent (.exec .skip env { st with mem } k))
      | _, _, _ => none
    | .setField p field e =>
      match evalE P env st.mem p, evalE P env st.mem e with
      | some (.ptr b off), some v =>
        if off = 0 then
          match st.mem.storeField P b field v with
          | none => none
          | some mem => some (.silent (.exec .skip env { st with mem } k))
        else none
      | _, _ => none
    | .seq a b => some (.silent (.exec a env st (.seq b k)))
    | .ite condition a b =>
      match evalE P env st.mem condition with
      | some (.u32 v) => some (.silent (.exec (if v = 0 then b else a) env st k))
      | _ => none
    | .while condition body =>
      match evalE P env st.mem condition with
      | some (.u32 v) =>
        if v = 0 then some (.silent (.exec .skip env st k))
        else some (.silent (.exec body env st (.loop condition body k)))
      | _ => none
    | .call dst f args =>
      match evalArgs P env st.mem args with
      | none => none
      | some vs => some (.silent (.call (.internal f) vs st (.call dst env k)))
    | .ecall dst ext args =>
      match evalArgs P env st.mem args with
      | none => none
      | some vs => some (.silent (.call (.external ext) vs st (.call dst env k)))
    | .ret none => (returnTarget none st k).map .silent
    | .ret (some e) =>
      match evalE P env st.mem e with
      | none => none
      | some v => (returnTarget (some v) st k).map .silent
    | .brk => match k with
      | .seq _ k' => some (.silent (.exec .brk env st k'))
      | .loop _ _ k' => some (.silent (.exec .skip env st k'))
      | _ => none
  | .callstate (.internal f) vs mem orc k =>
    let st : MachineStore External := ⟨mem, orc⟩
    match P.findFn f with
    | none => none
    | some fn => match bindParams st.mem fn.params vs with
      | none => none
      | some penv => some (.silent (.exec fn.body (penv ++ initLocals fn.locals) st (.function fn.ret k)))
  | .callstate (.external ext) vs mem orc k =>
    let st : MachineStore External := ⟨mem, orc⟩
    match kernel ext vs st with
    | none => none
    | some (rv, st') => some (.external ext vs st rv st' (.returned rv st' k))
  | .returnstate rv mem orc (.call dst env k) =>
    let st : MachineStore External := ⟨mem, orc⟩
    match assignDst env st.mem dst rv with
    | none => none
    | some env' => some (.silent (.exec .skip env' st k))
  | .returnstate _ _ _ _ => none

/-- Internal control transitions, with external responses specified separately. -/
def next (P : Prog) : State → Option Action := nextCore P (fun _ _ _ => none)

/-- Kernel execution uses the certified oracle stored in the machine state. -/
abbrev nextFor {State : Type} (P : Prog) :
    ExecState P State → Option (ExecAction P State) :=
  nextCore P (Ext.run P)

/-- An external call whose public precondition holds. -/
def KernelReady (P : Prog) (c : State) : Prop :=
  ∃ ext args mem k, c = .callstate (.external ext) args mem () k ∧
    Kernel.Defined P ⟨ext, args, mem⟩

/-- Contract undefined behavior: no control step or permitted external response. -/
def Failed (P : Prog) (c : State) : Prop :=
  next P c = none ∧ ¬ final c ∧ ¬ KernelReady P c

/-- Contract execution admits every response meeting the kernel specification. -/
def rawStep (P : Prog) (source target : State) : Prop :=
  (∃ action, next P source = some action ∧ action.target = target) ∨
  ∃ ext args mem k result mem',
    source = .callstate (.external ext) args mem () k ∧
    Oracle.Returns P ⟨ext, args, mem⟩ ⟨result, mem'⟩ ∧
    target = .returnstate result mem' () k

def FailedFor {State : Type} (P : Prog) (c : ExecState P State) : Prop :=
  nextFor P c = none ∧ ¬ final c

def rawStepFor {State : Type} (P : Prog)
    (source target : ExecState P State) : Prop :=
  ∃ action, nextFor P source = some action ∧ action.target = target

inductive RawStar {α : Type} (R : α → α → Prop) : α → α → Prop where
  | refl (state) : RawStar R state state
  | step (source middle target) :
      R source middle → RawStar R middle target → RawStar R source target

def RawInfinite (P : Prog) (start : State) : Prop :=
  ∃ states : Nat → State,
    states 0 = start ∧ ∀ n, rawStep P (states n) (states (n + 1))

def RawInfiniteFor {State : Type} (P : Prog) (start : ExecState P State) : Prop :=
  ∃ states : Nat → ExecState P State,
    states 0 = start ∧ ∀ n, rawStepFor P (states n) (states (n + 1))

/-- Bounded execution calls `next` once per unit of fuel. -/
abbrev runCore (step : State External → Option (Action External)) :
    Nat → State External → Res (Option Val × MachineStore External)
  | 0, _ => .timeout
  | fuel + 1, c =>
    match step c with
    | some action => runCore step fuel action.target
    | none => match c with
      | .returnstate rv mem orc .stop => .ok (rv, ⟨mem, orc⟩)
      | _ => .stuck

/-- Execute the sole bounded driver with the oracle carried in each state. -/
def run {State : Type} (P : Prog) :
    Nat → ExecState P State → Res (Option Val × KernelState P State) :=
  runCore (nextFor P)

/-- Partial correctness of a bounded run. -/
def ValidFor {State : Type} (P : Prog) (fuel : Nat)
    (R : Option Val → KernelState P State → Prop) (c : ExecState P State) : Prop :=
  match run P fuel c with
  | .timeout => True
  | .stuck => False
  | .ok (rv, st) => R rv st

theorem run_mono {P : Prog} {State : Type} {n m : Nat} {c : (ExecState P State)} {r : Res (Option Val × (KernelState P State))}
    (h : run P n c = r) (hr : r ≠ .timeout) (hnm : n ≤ m) : run P m c = r := by
  induction n generalizing m c with
  | zero => simp [run, runCore] at h; subst r; exact (hr rfl).elim
  | succ n ih =>
    cases m with
    | zero => omega
    | succ m =>
      simp only [run, runCore] at h ⊢
      cases hn : nextFor P c with
      | none => simpa [hn] using h
      | some a => simp only [hn] at h ⊢; exact ih h (by omega)

theorem ValidFor.down {P : Prog} {State : Type} {n m : Nat} {R : Option Val → (KernelState P State) → Prop} {c : (ExecState P State)}
    (h : ValidFor P m R c) (hnm : n ≤ m) : ValidFor P n R c := by
  unfold ValidFor
  cases hr : run P n c with
  | timeout => trivial
  | stuck => simp [ValidFor, run_mono hr (by simp) hnm] at h
  | ok r => simpa [ValidFor, run_mono hr (by simp) hnm] using h

theorem ValidFor.step {P : Prog} {State : Type} {n : Nat} {R : Option Val → (KernelState P State) → Prop}
    {c : (ExecState P State)} {a : (ExecAction P State)} (hn : nextFor P c = some a)
    (h : ValidFor P n R a.target) : ValidFor P (n + 1) R c := by
  simpa [ValidFor, run, runCore, hn] using h

theorem ValidFor.next {P : Prog} {State : Type} {R : Option Val → (KernelState P State) → Prop}
    {c : (ExecState P State)} {a : (ExecAction P State)} (hn : nextFor P c = some a)
    (h : ∀ n, ValidFor P n R c) : ∀ n, ValidFor P n R a.target := by
  intro n
  simpa [ValidFor, run, runCore, hn] using h (n + 1)

end EmbC.Semantics

namespace EmbC

/-- Run a function with the certified oracle carried in the initial state. -/
def Prog.run {State : Type} (P : Prog) (fuel : Nat)
    (f : String) (vs : List Val) (st : KernelState P State) :
    Res (Option Val × KernelState P State) :=
  Semantics.run P fuel (Semantics.initial f vs st)

end EmbC
