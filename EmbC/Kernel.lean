import EmbC.Memory

/-!
# EmbC: intrinsically specified kernel interfaces

The trusted kernel contracts appear directly in the result type of `Oracle.step`.
An oracle carries both its private state and a certified state transformer; no
separate compatibility assertion is needed to execute it.
-/

namespace EmbC

namespace Kernel

structure Call where
  operation : Ext
  args : List Val
  before : Mem

structure Reply where
  result : Option Val
  after : Mem

end Kernel

/-- The public heap together with an arbitrary external component. -/
structure MachineStore (State : Type := Unit) where
  mem : Mem
  oracle : State

/-- Field values of a freshly zeroed struct. -/
def StructDef.zeroCells (d : StructDef) : Array Val := (d.fields.map (·.2.zero)).toArray

/-- Preserved cells followed by uninitialized cells after array growth. -/
def reallocCells (old : Array Val) (n : Nat) : Array Val :=
  old.extract 0 n ++ Array.replicate (n - old.size) Val.undef

structure Oracle (P : Prog) (State : Type) where
  state : State
  step : (call : Kernel.Call) → State →
    { answer : Option (Kernel.Reply × State) //
      let m := call.before
      match call.operation, call.args with
      | .kvcalloc t, [.u64 n] =>
        if n = 0 ∨ t.isStruct then answer = none else
        ∃ next,
          answer = some (⟨some .null, m⟩, next) ∨
          answer = some (⟨some (.ptr m.blocks.size 0),
            (m.alloc t (Array.replicate n.toNat t.zero)).2⟩, next)
      | .kzalloc name, [] =>
        match P.findStruct name with
        | none => answer = none
        | some d =>
          ∃ next,
            answer = some (⟨some .null, m⟩, next) ∨
            answer = some (⟨some (.ptr m.blocks.size 0),
              (m.alloc (.struct name) d.zeroCells).2⟩, next)
      | .kvrealloc t, [pointer, .u64 n] =>
        if n = 0 ∨ t.isStruct then answer = none else
        match pointer with
        | .null =>
          ∃ next,
            answer = some (⟨some .null, m⟩, next) ∨
            answer = some (⟨some (.ptr m.blocks.size 0),
              (m.alloc t (Array.replicate n.toNat .undef)).2⟩, next)
        | .ptr b off =>
          if off ≠ 0 then answer = none else
          match m.block? b with
          | none => answer = none
          | some block =>
            if block.elem ≠ t then answer = none else
            ∃ next,
              answer = some (⟨some .null, m⟩, next) ∨
              answer = some (⟨some (.ptr m.blocks.size 0),
                ((m.free b).alloc t
                  (reallocCells block.cells n.toNat)).2⟩, next)
        | _ => answer = none
      | .kvfree, [.null] =>
        ∃ next, answer = some (⟨none, m⟩, next)
      | .kvfree, [.ptr b off] =>
        if off ≠ 0 then answer = none else
        match m.block? b with
        | none => answer = none
        | some _ => ∃ next, answer = some (⟨none, m.free b⟩, next)
      | .copyFromBpfptr, [.ptr b off, .uptr, .u64 n] =>
        match m.block? b with
        | none => answer = none
        | some block =>
          if block.elem ≠ .u32 ∨ off + n.toNat > block.cells.size then
            answer = none
          else
            ∃ next,
              answer = some (⟨some (.u32 1),
                m.fill b off (List.replicate n.toNat .undef)⟩, next) ∨
              ∃ words : List (BitVec 32),
                words.length = n.toNat ∧
                answer = some (⟨some (.u32 0),
                  m.fill b off (words.map Val.u32)⟩, next)
      | .signalPending, [] =>
        ∃ next,
          answer = some (⟨some (.u32 0), m⟩, next) ∨
          answer = some (⟨some (.u32 1), m⟩, next)
      | .condResched, [] =>
        ∃ next, answer = some (⟨none, m⟩, next)
      | _, _ => answer = none }

/-- A runtime store contains the complete certified oracle. -/
abbrev KernelState (P : Prog) (State : Type) := MachineStore (Oracle P State)

namespace Oracle

/-- One invocation updates the private state while retaining the certified step. -/
def ask {P : Prog} {State : Type} (o : Oracle P State)
    (call : Kernel.Call) : Option (Kernel.Reply × Oracle P State) :=
  (o.step call o.state).val.map fun (reply, next) =>
    (reply, { o with state := next })

/-- A public outcome is realizable by an intrinsically certified oracle. -/
def Returns (P : Prog) (call : Kernel.Call) (reply : Kernel.Reply) : Prop :=
  ∃ (State : Type) (o : Oracle P State) (next : State),
    (o.step call o.state).val = some (reply, next)

end Oracle

namespace Kernel

/-- Valid calls depend only on the operation, arguments, and current memory. -/
def Defined (P : Prog) (call : Call) : Prop :=
  match call.operation, call.args with
  | .kvcalloc t, [.u64 n] => n ≠ 0 ∧ t.isStruct = false
  | .kzalloc name, [] => ∃ d, P.findStruct name = some d
  | .kvrealloc t, [p, .u64 n] => n ≠ 0 ∧ t.isStruct = false ∧
    match p with
    | .null => True
    | .ptr b off => off = 0 ∧ ∃ blk, call.before.block? b = some blk ∧ blk.elem = t
    | _ => False
  | .kvfree, [p] => match p with
    | .null => True
    | .ptr b off => off = 0 ∧ ∃ blk, call.before.block? b = some blk
    | _ => False
  | .copyFromBpfptr, [.ptr b off, .uptr, .u64 n] =>
    ∃ blk, call.before.block? b = some blk ∧ blk.elem = .u32 ∧
      off + n.toNat ≤ blk.cells.size
  | .signalPending, [] | .condResched, [] => True
  | _, _ => False

/-- Invoke the certified transformer carried by the runtime store. -/
def run {State : Type} (P : Prog) (operation : Ext) (args : List Val)
    (st : KernelState P State) : Option (Option Val × KernelState P State) :=
  (st.oracle.step ⟨operation, args, st.mem⟩ st.oracle.state).val.map fun (reply, next) =>
    (reply.result, ⟨reply.after, { st.oracle with state := next }⟩)

/-- Execution returns an outcome admitted by the oracle's own certificate. -/
theorem run_spec {State : Type} {P : Prog} {ext : Ext} {args : List Val}
    {st st' : KernelState P State} {rv : Option Val}
    (h : run P ext args st = some (rv, st')) :
    Oracle.Returns P ⟨ext, args, st.mem⟩ ⟨rv, st'.mem⟩ := by
  unfold run at h
  cases hr : (st.oracle.step ⟨ext, args, st.mem⟩ st.oracle.state).val with
  | none => simp [hr] at h
  | some response =>
    rcases response with ⟨reply, next⟩
    simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨State, st.oracle, next, hr⟩

end Kernel

abbrev Ext.run {State : Type} (P : Prog) (operation : Ext) (args : List Val)
    (st : KernelState P State) : Option (Option Val × KernelState P State) :=
  Kernel.run P operation args st

namespace Ext

theorem run_spec {State : Type} {P : Prog} {ext : Ext} {args : List Val}
    {st st' : KernelState P State} {rv : Option Val}
    (h : Ext.run P ext args st = some (rv, st')) :
    Oracle.Returns P ⟨ext, args, st.mem⟩ ⟨rv, st'.mem⟩ := Kernel.run_spec h

/-- The actual result of the invocation; invalid calls alone use the fallback. -/
def answer {State : Type} (P : Prog) (ext : Ext) (args : List Val)
    (st : KernelState P State) : Option Val × KernelState P State :=
  (Ext.run P ext args st).getD (none, st)

end Ext

end EmbC
