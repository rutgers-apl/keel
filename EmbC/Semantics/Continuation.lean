import EmbC.Semantics

/-! Continuation composition for modular proofs about the source machine. -/

namespace EmbC.Semantics

variable {State : Type}

def Cont.append : Cont → Cont → Cont
  | .stop, outer => outer
  | .seq b k, outer => .seq b (k.append outer)
  | .loop c b k, outer => .loop c b (k.append outer)
  | .function rt k, outer => .function rt (k.append outer)
  | .call dst env k, outer => .call dst env (k.append outer)

def State.append (c : (EmbC.Semantics.State State)) (outer : Cont) : (EmbC.Semantics.State State) :=
  match c with
  | .regular s env mem orc k => .regular s env mem orc (k.append outer)
  | .callstate f vs mem orc k => .callstate f vs mem orc (k.append outer)
  | .returnstate rv mem orc k => .returnstate rv mem orc (k.append outer)

def Action.append (a : (Action State)) (outer : Cont) : (Action State) :=
  match a with
  | .silent c => .silent (c.append outer)
  | .external ext args before rv after c =>
    .external ext args before rv after (c.append outer)

theorem Action.append_target (a : (Action State)) (outer : Cont) :
    (a.append outer).target = a.target.append outer := by cases a <;> rfl

theorem Cont.returnCont_append_call (cont : Cont) (dst : Option Var) (env : Env) (k : Cont) :
    (cont.append (.call dst env k)).returnCont =
      cont.returnCont.map (fun (rt, inner) => (rt, inner.append (.call dst env k))) := by
  induction cont <;> simp_all [Cont.returnCont, Cont.append]

theorem returnTarget_append_call (rv : Option Val) (st : MachineStore State)
    (cont : Cont) (dst : Option Var) (env : Env) (k : Cont) :
    returnTarget rv st (cont.append (.call dst env k)) =
      (returnTarget rv st cont).map (fun c => c.append (.call dst env k)) := by
  simp only [returnTarget, Cont.returnCont_append_call]
  cases hc : cont.returnCont with
  | none => rfl
  | some pair =>
    rcases pair with ⟨rt, inner⟩
    cases rt <;> cases rv <;> simp [EmbC.Semantics.State.append]

/-- Attaching a caller commutes with each callee step, until its return. -/
theorem next_append_call {P : Prog} {c : (ExecState P State)} {dst : Option Var} {env : Env} {k : Cont}
    (h : ∀ rv st, c ≠ .returned rv st .stop) :
    nextFor P (c.append (.call dst env k)) =
      (nextFor P c).map (fun a => a.append (.call dst env k)) := by
  cases c with
  | regular s e mem orc cont =>
    let st : (KernelState P State) := ⟨mem, orc⟩
    cases s with
    | skip =>
      cases cont <;> simp [EmbC.Semantics.State.append, Cont.append, nextFor, nextCore, Action.append]
      case function rt cont => cases rt <;> rfl
    | brk => cases cont <;> rfl
    | ret expr =>
      cases expr with
      | none =>
        simp only [EmbC.Semantics.State.append, nextFor, nextCore, returnTarget_append_call, Option.map_map]
        rfl
      | some e' =>
        simp only [EmbC.Semantics.State.append, nextFor, nextCore]
        cases he : evalE P e st.mem e' <;>
          simp [returnTarget_append_call, Option.map_map, Function.comp_def, Action.append]
    | assign | store | setField | seq | ite | «while» | call | ecall =>
      simp only [EmbC.Semantics.State.append, nextFor, nextCore]
      all_goals repeat' split
      all_goals simp_all [EmbC.Semantics.State.append, Cont.append, Action.append]
  | callstate f vs mem orc cont =>
    cases f <;> simp only [EmbC.Semantics.State.append, nextFor, nextCore]
    all_goals repeat' split
    all_goals simp_all [EmbC.Semantics.State.append, Cont.append, Action.append]
  | returnstate rv mem orc cont =>
    cases cont
    · exact (h rv ⟨mem, orc⟩ rfl).elim
    all_goals simp only [EmbC.Semantics.State.append, Cont.append, nextFor, nextCore]
    all_goals repeat' split
    all_goals simp_all [EmbC.Semantics.State.append, Action.append]

/-- A safe callee can be used with any caller satisfying its return postcondition. -/
theorem ValidFor.append_call {P : Prog} {Post R : Option Val → (KernelState P State) → Prop}
    {c : (ExecState P State)} {dst : Option Var} {env : Env} {k : Cont} {n : Nat}
    (hc : ∀ fuel, ValidFor P fuel Post c)
    (hk : ∀ rv st, Post rv st → ValidFor P n R (.returned rv st (.call dst env k))) :
    ValidFor P n R (c.append (.call dst env k)) := by
  induction n generalizing c with
  | zero => trivial
  | succ n ih =>
    by_cases hf : ∃ rv st, c = .returned rv st .stop
    · obtain ⟨rv, st, rfl⟩ := hf
      have hp : Post rv st := by simpa [ValidFor, run, runCore, Semantics.nextFor, Semantics.nextCore] using hc 1
      exact hk rv st hp
    · have hne : ∀ rv st, c ≠ .returned rv st .stop := by
        intro rv st he; exact hf ⟨rv, st, he⟩
      cases hn : Semantics.nextFor P c with
      | none =>
        have bad := hc 1
        cases c with
        | regular s e mem orc cont => simp [ValidFor, run, runCore, hn] at bad
        | callstate f vs mem orc cont => simp [ValidFor, run, runCore, hn] at bad
        | returnstate rv mem orc cont =>
          cases cont with
          | stop => exact (hne rv ⟨mem, orc⟩ rfl).elim
          | seq | loop | function | call => simp [ValidFor, run, runCore, hn] at bad
      | some a =>
        apply ValidFor.step (by rw [next_append_call hne, hn]; rfl)
        rw [Action.append_target]
        exact ih (ValidFor.next hn hc) (fun rv st hp => (hk rv st hp).down (by omega))

end EmbC.Semantics
