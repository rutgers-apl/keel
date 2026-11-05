import Lean
import EmbC.Logic

/-! Cost values and the kernel-operation accounting shared by the machine and its proof rules. -/

namespace EmbC

/-- The cost of a run: the time `t` (machine transitions and kernel-call work)
and the words `m` obtained from the allocator.  A numeral `n : Cost` is `n`
units of time and no words. -/
structure Cost where
  t : Nat
  m : Nat
  deriving DecidableEq, Repr

namespace Cost

instance : Add Cost := ⟨fun a b => ⟨a.t + b.t, a.m + b.m⟩⟩
instance (n : Nat) : OfNat Cost n := ⟨⟨n, 0⟩⟩

@[simp] theorem add_t (a b : Cost) : (a + b).t = a.t + b.t := rfl
@[simp] theorem add_m (a b : Cost) : (a + b).m = a.m + b.m := rfl
@[simp] theorem lit_t (n : Nat) : (OfNat.ofNat n : Cost).t = n := rfl
@[simp] theorem lit_m (n : Nat) : (OfNat.ofNat n : Cost).m = 0 := rfl
@[simp] theorem zero_t : (0 : Cost).t = 0 := rfl
@[simp] theorem zero_m : (0 : Cost).m = 0 := rfl
@[simp] theorem one_t : (1 : Cost).t = 1 := rfl
@[simp] theorem one_m : (1 : Cost).m = 0 := rfl
@[simp] theorem mk_t (a b : Nat) : (Cost.mk a b).t = a := rfl
@[simp] theorem mk_m (a b : Nat) : (Cost.mk a b).m = b := rfl

theorem ext {a b : Cost} (ht : a.t = b.t) (hm : a.m = b.m) : a = b := by
  cases a; cases b; simp only at ht hm; subst ht; subst hm; rfl

theorem add_assoc (a b c : Cost) : a + b + c = a + (b + c) :=
  ext (Nat.add_assoc _ _ _) (Nat.add_assoc _ _ _)
theorem add_comm (a b : Cost) : a + b = b + a := ext (Nat.add_comm _ _) (Nat.add_comm _ _)
@[simp] theorem zero_add (a : Cost) : 0 + a = a := ext (Nat.zero_add _) (Nat.zero_add _)
@[simp] theorem add_zero (a : Cost) : a + 0 = a := ext (Nat.add_zero _) (Nat.add_zero _)

end Cost

open Lean Meta in
/-- `(n : Cost).t = n` for a numeral `n`. -/
simproc reduceCostT (Cost.t _) := fun e => do
  let_expr Cost.t c ← e | return .continue
  let_expr OfNat.ofNat _ lit _ ← c | return .continue
  let some n := lit.rawNatLit? | return .continue
  return .done { expr := mkNatLit n }

open Lean Meta in
/-- `(n : Cost).m = 0` for a numeral `n`. -/
simproc reduceCostM (Cost.m _) := fun e => do
  let_expr Cost.m c ← e | return .continue
  let_expr OfNat.ofNat _ lit _ ← c | return .continue
  let some _ := lit.rawNatLit? | return .continue
  return .done { expr := mkNatLit 0 }

/-- The words a kernel call obtains from the allocator. -/
def Ext.words (P : Prog) : Ext → List Val → Nat
  | .kvcalloc _, [.u64 n] => n.toNat
  | .kzalloc s, [] =>
    match P.findStruct s with
    | some d => d.fields.length
    | none => 0
  | .kvrealloc _, [_, .u64 n] => n.toNat
  | _, _ => 0

/-- The time a kernel call takes beyond one step: twice the words it allocates
(zeroed or copied once, freed once), or the words it copies in. -/
def Ext.cost (P : Prog) : Ext → List Val → Nat
  | .copyFromBpfptr, [_, _, .u64 n] => n.toNat
  | f, vs => 2 * Ext.words P f vs

/-- The cost of a kernel call beyond one step. -/
def Ext.costC (P : Prog) (f : Ext) (vs : List Val) : Cost := ⟨Ext.cost P f vs, Ext.words P f vs⟩


/-- A costed result of the shared machine, parameterized by its external payload. -/
abbrev CallResCCore (External : Type) := Res (Option Val × MachineStore External × Cost)

/-- A costed executable result carries its stateful oracle. -/
abbrev CallResC (P : Prog) (State : Type) := CallResCCore (Oracle P State)

/-- Forget the cost of a call. -/
def Res.eraseC {External : Type} : CallResCCore External → Res (Option Val × MachineStore External)
  | .ok (rv, st, _) => .ok (rv, st)
  | .timeout => .timeout
  | .stuck => .stuck

end EmbC
