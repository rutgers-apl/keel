import EmbC.Kernel

/-! Test-only kernel environment. Input words describe caller memory, while
fault indices count past allocation, copy, and signal invocations. This module
is used only by executable regressions and native comparison drivers. -/

namespace EmbC.Testing

/-- A concrete caller buffer and a fault-injection policy. Counters describe
calls already made; the world contains no schedule of future replies. -/
structure World where
  input : Array (BitVec 32) := #[]
  failingCalls : List Nat := []
  calls : Nat := 0
  allocations : Nat := 0
  copies : Nat := 0
  deriving Repr

/-- The caller's input, padded with zero words if the requested view is longer. -/
def inputWords (input : Array (BitVec 32)) (n : Nat) : List (BitVec 32) :=
  (List.range n).map fun i => input[i]?.getD 0

/-- A direct test implementation of the logical contracts. Failure is a policy
for the current call, and `signal` is the current task's pending-signal flag. -/
def reply (P : Prog) (input : Array (BitVec 32)) (failure signal : Bool)
    (call : Kernel.Call) : Option Kernel.Reply :=
  match call.operation, call.args with
  | .kvcalloc t, [.u64 n] =>
    if n = 0 ∨ t.isStruct then none else
    if failure then some ⟨some .null, call.before⟩ else
      some ⟨some (.ptr call.before.blocks.size 0),
        (call.before.alloc t (Array.replicate n.toNat t.zero)).2⟩
  | .kzalloc name, [] =>
    match P.findStruct name with
    | none => none
    | some d =>
      if failure then some ⟨some .null, call.before⟩ else
        some ⟨some (.ptr call.before.blocks.size 0),
          (call.before.alloc (.struct name) d.zeroCells).2⟩
  | .kvrealloc t, [p, .u64 n] =>
    if n = 0 ∨ t.isStruct then none else
    match p with
    | .null =>
      if failure then some ⟨some .null, call.before⟩ else
        some ⟨some (.ptr call.before.blocks.size 0),
          (call.before.alloc t (Array.replicate n.toNat .undef)).2⟩
    | .ptr b off =>
      match call.before.block? b with
      | none => none
      | some blk =>
        if off ≠ 0 ∨ blk.elem ≠ t then none else
        if failure then some ⟨some .null, call.before⟩ else
          some ⟨some (.ptr call.before.blocks.size 0),
            ((call.before.free b).alloc t (reallocCells blk.cells n.toNat)).2⟩
    | _ => none
  | .kvfree, [p] =>
    match p with
    | .null => some ⟨none, call.before⟩
    | .ptr b off =>
      match call.before.block? b with
      | none => none
      | some _ => if off ≠ 0 then none else some ⟨none, call.before.free b⟩
    | _ => none
  | .copyFromBpfptr, [.ptr b off, .uptr, .u64 n] =>
    match call.before.block? b with
    | none => none
    | some blk =>
      if blk.elem ≠ .u32 ∨ off + n.toNat > blk.cells.size then none else
      if failure then
        some ⟨some (.u32 1), call.before.fill b off (List.replicate n.toNat .undef)⟩
      else
        some ⟨some (.u32 0), call.before.fill b off ((inputWords input n.toNat).map .u32)⟩
  | .signalPending, [] => some ⟨some (.u32 (if signal then 1 else 0)), call.before⟩
  | .condResched, [] => some ⟨none, call.before⟩
  | _, _ => none

def World.after (world : World) (operation : Ext) : World :=
  match operation with
  | .kvcalloc _ | .kzalloc _ | .kvrealloc _ =>
    { world with calls := world.calls + 1, allocations := world.allocations + 1 }
  | .copyFromBpfptr => { world with calls := world.calls + 1, copies := world.copies + 1 }
  | .signalPending => { world with calls := world.calls + 1 }
  | .kvfree | .condResched => world

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
def makeOracle {State : Type} (P : Prog) (initial : State)
    (input : State → Array (BitVec 32)) (failure signal : State → Bool)
    (after : State → Ext → State) : Oracle P State where
  state := initial
  step call current :=
    ⟨(reply P (input current) (failure current) (signal current) call).map fun answer =>
      (answer, after current call.operation), by
      unfold reply
      split <;> simp_all only
      all_goals repeat (split <;> simp_all)
      all_goals repeat' first | split | intro
      all_goals try simp_all
      all_goals try exact ⟨_, Or.inl rfl⟩
      all_goals try exact ⟨_, Or.inr rfl⟩
      all_goals try exact ⟨_, rfl⟩
      all_goals try exact ⟨_, Or.inr ⟨_, by simp [inputWords], rfl⟩⟩
      all_goals exact ⟨_, _, by simp [inputWords], rfl, rfl⟩⟩


def oracle (P : Prog) (initial : World := {}) : Oracle P World :=
  makeOracle P initial World.input
    (fun world => world.failingCalls.contains world.calls)
    (fun world => world.failingCalls.contains world.calls)
    World.after

end EmbC.Testing
