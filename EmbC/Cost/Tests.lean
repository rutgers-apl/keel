import EmbC.Cost.Machine
import EmbC.Semantics.Tests

/-! Regressions for cost accounting across source and administrative states. -/

namespace EmbC.Cost.Tests

def voidFn (name : String) (body : Stmt) : Fn :=
  { name, params := [], ret := none, locals := [], body }

def prog : Prog := { Semantics.Tests.prog with
  fns := Semantics.Tests.prog.fns ++ [
    voidFn "empty" .skip,
    voidFn "two_skips" (.seq .skip .skip),
    voidFn "false_loop" (.while (.lit32 0) .skip),
    voidFn "break_loop" (.while (.lit32 1) (.seq .skip .brk)),
    voidFn "allocate" (.ecall none (.kvcalloc .u32) [.lit64 4]),
    voidFn "bind_failure" (.ecall (some "missing") .signalPending [])
  ] }

inductive Observation where
  | timeout
  | stuck
  | returned (value : Option Nat) (kernelCalls : Nat) (blocks : Nat) (cost : EmbC.Cost)
  deriving DecidableEq, Repr

def observe : CallResC prog Nat → Observation
  | .timeout => .timeout
  | .stuck => .stuck
  | .ok (rv, st, cost) =>
    .returned (rv.bind fun v => match v with | .u32 n => some n.toNat | _ => none)
      st.oracle.state st.mem.blocks.size cost

def actual (fuel : Nat) (name : String) : Observation :=
  observe (prog.runC fuel name [] ⟨Mem.empty, Semantics.Tests.oracle prog 0⟩)

-- Function entry, sequencing, loop bookkeeping and call binding all cost one.
#guard actual 100 "empty" = .returned none 0 0 2
#guard actual 100 "two_skips" = .returned none 0 0 4
#guard actual 100 "false_loop" = .returned none 0 0 3
#guard actual 100 "break_loop" = .returned none 0 0 6
#guard actual 100 "allocate" = .returned none 1 1 ⟨13, 4⟩
#guard actual 100 "bind_failure" = .stuck

#guard actual 100 "caller" = .returned (some 10) 0 0 28
#guard actual 100 "early_return" = .returned (some 42) 0 0 5
#guard actual 100 "short_circuit" = .returned (some 1) 0 0 2
#guard actual 100 "external" = .returned (some 0) 1 0 7
#guard actual 100 "division" = .stuck
#guard actual 100 "missing_return" = .stuck
#guard actual 100 "unknown" = .stuck
#guard actual 0 "callee" = .timeout
#guard actual 2 "callee" = .timeout
#guard actual 3 "callee" = .returned (some 7) 0 0 2
#guard actual 100 "diverge" = .timeout

end EmbC.Cost.Tests
