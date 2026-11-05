import EmbC.Cost.Continuation

namespace EmbC

variable {State : Type}
open Semantics

private theorem regular_failed {P : Prog} {R : Option Val → (KernelState P State) → Cost → Prop}
    {s : Stmt} {env : Env} {st : (KernelState P State)} {k : Cont}
    (hn : Semantics.nextFor P (.exec s env st k) = none) :
    MachineValidC P R (.exec s env st k) true :=
  MachineValidC.failed hn (by simp [Semantics.final, EmbC.Semantics.State.exec, EmbC.Semantics.State.returned])

private theorem regular_one {P : Prog} {R : Option Val → (KernelState P State) → Cost → Prop}
    {s : Stmt} {env : Env} {st : (KernelState P State)} {k : Cont} {target : (ExecState P State)} {cost : Cost}
    (hn : Semantics.nextFor P (.exec s env st k) = some (.silent target))
    (hf : machineNextFresh P (.exec s env st k) = false)
    (hc : machineStepCost P (.exec s env st k) true = cost)
    (ht : MachineValidC P (fun rv st c => R rv st (cost + c)) target false) :
    MachineValidC P R (.exec s env st k) true := by
  apply MachineValidC.step hn
  simpa only [Action.target, hf, hc] using ht

private theorem skip_fresh (P : Prog) (fuel : Nat) (env : Env) (st : (KernelState P State)) (k : Cont) :
    machineRunC P fuel (.exec .skip env st k) true =
      machineRunC P fuel (.exec .skip env st k) false := by
  cases fuel <;> rfl

private theorem brk_fresh (P : Prog) (fuel : Nat) (env : Env) (st : (KernelState P State)) (k : Cont) :
    machineRunC P fuel (.exec .brk env st k) true =
      machineRunC P fuel (.exec .brk env st k) false := by
  cases fuel <;> rfl

section rules
variable {P : Prog} {Q : (CPost P State)} {env : Env} {st : (KernelState P State)}

/-- Completion states leave their actual control transition to the continuation. -/
theorem WPC.skip (h : Q .normal env st 0) : WPC P .skip Q env st := by
  intro k R hk
  obtain ⟨fuel, hf⟩ := hk .normal env st 0 h
  refine ⟨fuel, ?_⟩
  rw [skip_fresh]
  simpa only [Cost.zero_add] using hf

theorem WPC.brk (h : Q .brk env st 0) : WPC P .brk Q env st := by
  intro k R hk
  obtain ⟨fuel, hf⟩ := hk .brk env st 0 h
  refine ⟨fuel, ?_⟩
  rw [brk_fresh]
  simpa only [Cost.zero_add] using hf

theorem WPC.retVoid (h : Q (.ret none) env st 1) : WPC P (.ret none) Q env st := by
  intro k R hk
  have ht := hk (.ret none) env st 1 h
  cases hr : returnTarget none st k with
  | none => exact regular_failed (by simp [Semantics.nextFor, Semantics.nextCore, hr])
  | some target =>
    apply regular_one (target := target) (cost := 1) (by simp [Semantics.nextFor, Semantics.nextCore, hr]) rfl rfl
    simpa only [PostValidC, hr] using ht

theorem WPC.ret {e : Expr}
    (h : match evalE P env st.mem e with
      | none => True
      | some v => Q (.ret (some v)) env st 1) :
    WPC P (.ret (some e)) Q env st := by
  intro k R hk
  cases he : evalE P env st.mem e with
  | none => exact regular_failed (by simp [Semantics.nextFor, Semantics.nextCore, he])
  | some v =>
    have ht := hk (.ret (some v)) env st 1 (by simpa [he] using h)
    cases hr : returnTarget (some v) st k with
    | none => exact regular_failed (by simp [Semantics.nextFor, Semantics.nextCore, he, hr])
    | some target =>
      apply regular_one (target := target) (cost := 1) (by simp [Semantics.nextFor, Semantics.nextCore, he, hr]) rfl rfl
      simpa only [PostValidC, hr] using ht

theorem WPC.ret_any {e : Expr} (h : ∀ v, Q (.ret (some v)) env st 1) :
    WPC P (.ret (some e)) Q env st := by
  apply WPC.ret
  split
  · trivial
  · exact h _

theorem WPC.assign {x : Var} {e : Expr}
    (h : match evalE P env st.mem e with
      | none => True
      | some v =>
        match env.assign st.mem x v with
        | none => True
        | some env' => Q .normal env' st 1) :
    WPC P (.assign x e) Q env st := by
  intro k R hk
  cases he : evalE P env st.mem e with
  | none => exact regular_failed (by simp [Semantics.nextFor, Semantics.nextCore, he])
  | some v =>
    cases ha : env.assign st.mem x v with
    | none => exact regular_failed (by simp [Semantics.nextFor, Semantics.nextCore, he, ha])
    | some env' =>
      apply regular_one (target := .exec .skip env' st k) (cost := 1)
        (by simp [Semantics.nextFor, Semantics.nextCore, he, ha]) rfl rfl
      exact hk .normal env' st 1 (by simpa [he, ha] using h)

theorem WPC.store {p i e : Expr}
    (h : match evalE P env st.mem p, evalE P env st.mem i, evalE P env st.mem e with
      | some (.ptr b off), some vi, some v =>
        match vi.toIdx with
        | none => True
        | some index =>
          match st.mem.storeArr b (off + index) v with
          | none => True
          | some mem => Q .normal env { st with mem } 1
      | _, _, _ => True) :
    WPC P (.store p i e) Q env st := by
  intro k R hk
  cases hp : evalE P env st.mem p with
  | none => exact regular_failed (by simp [Semantics.nextFor, Semantics.nextCore, hp])
  | some vp =>
    cases hi : evalE P env st.mem i with
    | none => exact regular_failed (by cases vp <;> simp [Semantics.nextFor, Semantics.nextCore, hp, hi])
    | some vi =>
      cases he : evalE P env st.mem e with
      | none => exact regular_failed (by cases vp <;> simp [Semantics.nextFor, Semantics.nextCore, hp, hi, he])
      | some v =>
        cases vp with
        | ptr b off =>
          cases hv : vi.toIdx with
          | none => exact regular_failed (by simp [Semantics.nextFor, Semantics.nextCore, hp, hi, he, hv])
          | some index =>
            cases hm : st.mem.storeArr b (off + index) v with
            | none => exact regular_failed (by simp [Semantics.nextFor, Semantics.nextCore, hp, hi, he, hv, hm])
            | some mem =>
              apply regular_one (target := .exec .skip env { st with mem } k) (cost := 1)
                (by simp [Semantics.nextFor, Semantics.nextCore, hp, hi, he, hv, hm]) rfl rfl
              exact hk .normal env { st with mem } 1 (by simpa [hp, hi, he, hv, hm] using h)
        | _ => exact regular_failed (by simp [Semantics.nextFor, Semantics.nextCore, hp, hi, he])

theorem WPC.setField {p e : Expr} {f : String}
    (h : match evalE P env st.mem p, evalE P env st.mem e with
      | some (.ptr b off), some v =>
        off = 0 →
        match st.mem.storeField P b f v with
        | none => True
        | some mem => Q .normal env { st with mem } 1
      | _, _ => True) :
    WPC P (.setField p f e) Q env st := by
  intro k R hk
  cases hp : evalE P env st.mem p with
  | none => exact regular_failed (by simp [Semantics.nextFor, Semantics.nextCore, hp])
  | some vp =>
    cases he : evalE P env st.mem e with
    | none => exact regular_failed (by cases vp <;> simp [Semantics.nextFor, Semantics.nextCore, hp, he])
    | some v =>
      cases vp with
      | ptr b off =>
        by_cases ho : off = 0
        · cases hm : st.mem.storeField P b f v with
          | none => exact regular_failed (by simp [Semantics.nextFor, Semantics.nextCore, hp, he, ho, hm])
          | some mem =>
            apply regular_one (target := .exec .skip env { st with mem } k) (cost := 1)
              (by simp [Semantics.nextFor, Semantics.nextCore, hp, he, ho, hm]) rfl rfl
            exact hk .normal env { st with mem } 1 (by simpa [hp, he, ho, hm] using h)
        · exact regular_failed (by simp [Semantics.nextFor, Semantics.nextCore, hp, he, ho])
      | _ => exact regular_failed (by simp [Semantics.nextFor, Semantics.nextCore, hp, he])

@[simp] theorem Mem.hasTy_u64_u32 {m : Mem} {v : BitVec 64} : m.hasTy (.u64 v) .u32 = false := rfl
@[simp] theorem Mem.hasTy_ptr_u32 {m : Mem} {b o : Nat} : m.hasTy (.ptr b o) .u32 = false := rfl
@[simp] theorem Mem.hasTy_null_u32 {m : Mem} : m.hasTy .null .u32 = false := rfl
@[simp] theorem Mem.hasTy_uptr_u32 {m : Mem} : m.hasTy .uptr .u32 = false := rfl
@[simp] theorem Mem.hasTy_undef_u32 {m : Mem} : m.hasTy .undef .u32 = false := rfl

theorem Mem.hasTy_u32_inv {m : Mem} {v : Val} (h : m.hasTy v .u32 = true) : ∃ n, v = .u32 n := by
  cases v with
  | u32 n => exact ⟨n, rfl⟩
  | u64 _ => exact Bool.noConfusion h
  | ptr _ _ => exact Bool.noConfusion h
  | null => exact Bool.noConfusion h
  | uptr => exact Bool.noConfusion h
  | undef => exact Bool.noConfusion h

/-- An assignment to a `u32` variable, whatever value it receives. -/
theorem WPC.assign_u32 {x : Var} {e : Expr} (hx : env.ty x = some .u32)
    (h : ∀ n : BitVec 32, Q .normal (env.set x (.u32 n)) st 1) : WPC P (.assign x e) Q env st := by
  apply WPC.assign
  cases evalE P env st.mem e with
  | none => trivial
  | some v =>
    simp only [Env.assign, hx]
    by_cases ht : st.mem.hasTy v .u32 = true
    · obtain ⟨n, rfl⟩ := Mem.hasTy_u32_inv ht
      simp only [Mem.hasTy_u32, ↓reduceIte]
      exact h n
    · simp only [ht]; trivial

/-- An assignment whatever the value. -/
theorem WPC.assign_any {x : Var} {e : Expr}
    (h : ∀ v env', env.assign st.mem x v = some env' → Q .normal env' st 1) :
    WPC P (.assign x e) Q env st := by
  apply WPC.assign
  split
  · trivial
  · rename_i v _
    cases he : env.assign st.mem x v with
    | none => trivial
    | some env' => exact h v env' he

/-- An assignment of a value masked with `k`: whatever it is, it is at most `k`. -/
theorem WPC.assign_band {x : Var} {e : Expr} {k : BitVec 32} (hx : env.ty x = some .u32)
    (h : ∀ n : BitVec 32, n.toNat ≤ k.toNat → Q .normal (env.set x (.u32 n)) st 1) :
    WPC P (.assign x (.bin .band e (.lit32 k))) Q env st := by
  apply WPC.assign
  simp only [evalE]
  cases evalE P env st.mem e with
  | none => trivial
  | some v =>
    cases v with
    | u32 a =>
      simp only [evalBin, evalArith, Env.assign, hx, Mem.hasTy_u32, ↓reduceIte]
      refine h _ ?_
      rw [BitVec.toNat_and]; exact Nat.and_le_right
    | _ => simp [evalBin]


theorem WPC.ecall {dst : Option Var} {f : Ext} {args : List Expr}
    (h : match evalArgs P env st.mem args with
      | none => True
      | some vs =>
        match Ext.run P f vs st with
        | none => True
        | some (rv, st') =>
          match assignDst env st'.mem dst rv with
          | none => True
          | some env' => Q .normal env' st' (Ext.costC P f vs + 3)) :
    WPC P (.ecall dst f args) Q env st := by
  intro k R hk
  cases ha : evalArgs P env st.mem args with
  | none => exact regular_failed (by simp [Semantics.nextFor, Semantics.nextCore, ha])
  | some vs =>
    cases hr : Ext.run P f vs st with
    | none =>
      exact ⟨2, by simp [machineRunC, machineRunCCore, Semantics.nextFor, Semantics.nextCore, ha, hr, Action.target, CallResC.add, CallResC.sat]⟩
    | some result =>
      rcases result with ⟨rv, st'⟩
      cases hb : assignDst env st'.mem dst rv with
      | none =>
        exact ⟨3, by simp [machineRunC, machineRunCCore, Semantics.nextFor, Semantics.nextCore, ha, hr, hb, Action.target, CallResC.add, CallResC.sat]⟩
      | some env' =>
        obtain ⟨fuel, hf⟩ := hk .normal env' st' (Ext.costC P f vs + 3)
          (by simpa [ha, hr, hb] using h)
        refine ⟨fuel + 3, ?_⟩
        simp only [machineRunC, machineRunCCore, Semantics.nextFor, Semantics.nextCore, ha, hr, hb, machineNextFresh,
          machineStepCost, Action.target]
        change CallResC.sat (CallResC.add (CallResC.add
          (CallResC.add (machineRunC P fuel (.exec .skip env' st' k) false) 1)
          (1 + Ext.costC P f vs)) 1) R
        cases hs : machineRunC P fuel (.exec .skip env' st' k) false with
        | timeout => simp [hs, CallResC.sat] at hf
        | stuck => trivial
        | ok result =>
          rcases result with ⟨rv', st'', cost⟩
          have hcost : (1 : Cost) + ((1 + Ext.costC P f vs) + (1 + cost)) =
              (Ext.costC P f vs + 3) + cost := by
            apply Cost.ext <;> simp <;> omega
          simpa [CallResC.add, CallResC.sat, hs, hcost] using hf

/-- Cost reasoning for a kernel call uses only its public reply contract. -/
theorem WPC.ecall_spec {dst : Option Var} {f : Ext} {args : List Expr} {vs : List Val}
    (ha : evalArgs P env st.mem args = some vs)
    (h : ∀ rv (after : KernelState P State),
      Oracle.Returns P ⟨f, vs, st.mem⟩ ⟨rv, after.mem⟩ →
      match assignDst env after.mem dst rv with
      | none => True
      | some env' => Q .normal env' after (Ext.costC P f vs + 3)) :
    WPC P (.ecall dst f args) Q env st := by
  apply WPC.ecall
  cases hr : Ext.run P f vs st with
  | none => simp only [ha, hr]
  | some result =>
    rcases result with ⟨rv, after⟩
    simpa only [ha, hr] using h rv after (Ext.run_spec hr)

end rules
end EmbC
