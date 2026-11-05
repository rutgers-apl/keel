import EmbC.Semantics
import EmbC.Testing.Kernel

/-! Executable regressions for a Boolean private world. -/

namespace EmbC.Semantics.WorldTests

/-- The whole private world is the current task's pending-signal flag.
Every accepted invocation toggles it; the flag also requests allocation or
copy failure in this test environment. -/
def toggleOracle (P : Prog) (initial : Bool) : Oracle P Bool :=
  Testing.makeOracle P initial (fun _ => #[]) id id (fun flag _ => !flag)

def signals : Fn := {
  name := "signals", params := [], ret := some .u32,
  locals := [("x", .u32), ("y", .u32)],
  body := .seq (.ecall (some "x") .signalPending [])
    (.seq (.ecall (some "y") .signalPending [])
      (.ret (some (.bin .add (.bin .mul (.var "x") (.lit32 10)) (.var "y")))))
}

def allocation : Fn := {
  name := "allocation", params := [], ret := some (.ptr .u32),
  locals := [("p", .ptr .u32)],
  body := .seq (.ecall (some "p") (.kvcalloc .u32) [.lit64 1])
    (.ret (some (.var "p")))
}

def prog : Prog := { structs := [], fns := [signals, allocation] }

/-- Two calls observe different replies and restore the initial Boolean world. -/
def signalResult (initial : Bool) (expected : BitVec 32) : Bool :=
  match prog.run 40 "signals" [] ⟨Mem.empty, toggleOracle prog initial⟩ with
  | .ok (some (.u32 value), state) => value = expected && state.oracle.state = initial
  | _ => false

#guard signalResult false 1
#guard signalResult true 10

/-- Allocation failure is a valid null result, rather than undefined behavior. -/
def allocationFailure : Bool :=
  match prog.run 20 "allocation" [] ⟨Mem.empty, toggleOracle prog true⟩ with
  | .ok (some .null, state) => state.oracle.state = false && state.mem.blocks.size = 0
  | _ => false

#guard allocationFailure

/- Invalid arguments are rejected despite the oracle's allocation-failure flag. -/
#guard (Kernel.run prog (.kvcalloc .u32) [.u64 0]
  (⟨Mem.empty, toggleOracle prog true⟩ : KernelState prog Bool)).isNone

#guard (Kernel.run prog .signalPending [.u32 1]
  (⟨Mem.empty, toggleOracle prog false⟩ : KernelState prog Bool)).isNone


/- Even a heap-preserving call may update the environment's private world. -/
#guard match Kernel.run prog .condResched []
    (⟨Mem.empty, toggleOracle prog false⟩ : KernelState prog Bool) with
  | some (none, state) => state.oracle.state && state.mem.blocks.isEmpty
  | _ => false

/- Copying reads actual caller memory; the counters track calls, not words. -/
#guard
  let before := (Mem.empty.alloc .u32 #[.u32 0, .u32 0]).2
  let world : Testing.World := { input := #[17, 42] }
  match Kernel.run prog .copyFromBpfptr [.ptr 0 0, .uptr, .u64 2]
      (⟨before, Testing.oracle prog world⟩ : KernelState prog Testing.World) with
  | some (some (.u32 0), state) =>
    state.mem.loadArr 0 0 == some (.u32 17) &&
    state.mem.loadArr 0 1 == some (.u32 42) &&
    state.oracle.state.calls == 1 && state.oracle.state.copies == 1
  | _ => false

end EmbC.Semantics.WorldTests
