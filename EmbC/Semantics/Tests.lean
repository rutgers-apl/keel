import EmbC.DSL
import EmbC.Semantics
import EmbC.Testing.Kernel

/-! Execution regressions for continuation composition, errors, and budgets. -/

namespace EmbC.Semantics.Tests

def callee : Fn := c_fn% u32 callee() { return 7; }

def caller : Fn := c_fn% u32 caller() {
  u32 x;
  x = callee();
  while (x < 12) {
    x = x + 1;
    if (x == 10) { break; }
  }
  return x;
}

def earlyReturn : Fn := c_fn% u32 early_return() {
  while (1) { if (1) { return 42; } }
  return 0;
}

def shortCircuit : Fn := c_fn% u32 short_circuit() {
  return (0 && (1 / 0)) + (1 || (1 / 0));
}

def division : Fn := c_fn% u32 division() { return 1 / 0; }
def missingReturn : Fn := c_fn% u32 missing_return() { return; }
def diverge : Fn := c_fn% u32 diverge() { while (1) {} return 0; }
def external : Fn := c_fn% u32 external() {
  u32 x;
  x = signal_pending();
  return x;
}

def prog : Prog := {
  structs := [], consts := [],
  fns := [callee, caller, earlyReturn, shortCircuit, division, missingReturn, diverge, external]
}

inductive Result where
  | timeout | stuck | value (n : Nat) | other
  deriving DecidableEq, Repr

/-- A call counter is the whole private world. The pending-signal flag
alternates with the number of prior calls; other calls use normal outcomes. -/
def oracle (P : Prog) (initial : Nat := 0) : Oracle P Nat :=
  Testing.makeOracle P initial (fun _ => #[]) (fun _ => false)
    (fun calls => calls % 2 == 1) (fun calls _ => calls + 1)

def result (fuel : Nat) (name : String) (calls : Nat := 0) : Result :=
  match prog.run fuel name [] ⟨Mem.empty, oracle prog calls⟩ with
  | .timeout => .timeout
  | .stuck => .stuck
  | .ok (some (.u32 v), _) => .value v.toNat
  | .ok _ => .other

#guard result 100 "caller" = .value 10
#guard result 100 "early_return" = .value 42
#guard result 100 "short_circuit" = .value 1
#guard result 100 "division" = .stuck
#guard result 100 "missing_return" = .stuck
#guard result 100 "unknown" = .stuck
#guard result 0 "callee" = .timeout
#guard result 2 "callee" = .timeout
#guard result 3 "callee" = .value 7
#guard result 100 "diverge" = .timeout
#guard result 100 "external" 0 = .value 0
#guard result 100 "external" 1 = .value 1

/-- Successful external calls emit before a later destination-binding failure. -/
def observedBeforeBindingFailure : Bool :=
  let st : KernelState prog Nat := ⟨Mem.empty, oracle prog 1⟩
  let call : Semantics.ExecState prog Nat :=
    .call (.external .signalPending) [] st (.call (some "missing") [] .stop)
  match Semantics.nextFor prog call with
  | some (.external .signalPending [] _ (some (.u32 v)) after target) =>
    v = 1 && after.oracle.state = 2 &&
      match target with
      | .returnstate _ _ _ (.call (some "missing") [] .stop) =>
        (Semantics.nextFor prog target).isNone
      | _ => false
  | _ => false

#guard observedBeforeBindingFailure

end EmbC.Semantics.Tests
