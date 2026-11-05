import EmbC.Cost.Continuation

namespace EmbC

variable {State : Type}
open Semantics

private theorem admin_cost (a b : Cost) : 1 + a + (1 + b) = a + 2 + b := by
  apply Cost.ext <;> simp <;> omega


/-- Moving an already incurred cost into the final result predicate. -/
theorem PostValidC.prefix (P : Prog) (R : Option Val → (KernelState P State) → Cost → Prop)
    (o : Outcome) (env : Env) (st : (KernelState P State)) (cost extra : Cost) (k : Cont) :
    PostValidC P (fun rv st' c => R rv st' (extra + c)) o env st cost k ↔
      PostValidC P R o env st (extra + cost) k := by
  cases o <;> simp [PostValidC, Cost.add_assoc]

theorem MachineValidC.skip_seq {P : Prog} {R : Option Val → (KernelState P State) → Cost → Prop}
    {env : Env} {st : (KernelState P State)} {b : Stmt} {k : Cont}
    (h : MachineValidC P (fun rv st c => R rv st (1 + c)) (.exec b env st k) true) :
    MachineValidC P R (.exec .skip env st (.seq b k)) false := by
  apply MachineValidC.step (by rfl : Semantics.nextFor P (.exec .skip env st (.seq b k)) =
    some (.silent (.exec b env st k)))
  simpa [machineStepCost, machineNextFresh, Cost.zero_add, Action.target] using h

theorem MachineValidC.brk_seq {P : Prog} {R : Option Val → (KernelState P State) → Cost → Prop}
    {env : Env} {st : (KernelState P State)} {b : Stmt} {k : Cont}
    (h : MachineValidC P (fun rv st c => R rv st (1 + c)) (.exec .brk env st k) false) :
    MachineValidC P R (.exec .brk env st (.seq b k)) false := by
  apply MachineValidC.step (by rfl : Semantics.nextFor P (.exec .brk env st (.seq b k)) =
    some (.silent (.exec .brk env st k)))
  simpa [machineStepCost, machineNextFresh, Cost.zero_add, Action.target] using h

theorem MachineValidC.skip_loop {P : Prog} {R : Option Val → (KernelState P State) → Cost → Prop}
    {env : Env} {st : (KernelState P State)} {condition : Expr} {body : Stmt} {k : Cont}
    (h : MachineValidC P (fun rv st c => R rv st (1 + c)) (.exec (.while condition body) env st k) true) :
    MachineValidC P R (.exec .skip env st (.loop condition body k)) false := by
  apply MachineValidC.step (by rfl : Semantics.nextFor P (.exec .skip env st (.loop condition body k)) =
    some (.silent (.exec (.while condition body) env st k)))
  simpa [machineStepCost, machineNextFresh, Cost.zero_add, Action.target] using h

theorem MachineValidC.brk_loop {P : Prog} {R : Option Val → (KernelState P State) → Cost → Prop}
    {env : Env} {st : (KernelState P State)} {condition : Expr} {body : Stmt} {k : Cont}
    (h : MachineValidC P (fun rv st c => R rv st (1 + c)) (.exec .skip env st k) false) :
    MachineValidC P R (.exec .brk env st (.loop condition body k)) false := by
  apply MachineValidC.step (by rfl : Semantics.nextFor P (.exec .brk env st (.loop condition body k)) =
    some (.silent (.exec .skip env st k)))
  simpa [machineStepCost, machineNextFresh, Cost.zero_add, Action.target] using h

section rules
variable {P : Prog} {Q : (CPost P State)} {env : Env} {st : (KernelState P State)}

theorem WPC.seq {a b : Stmt}
    (h : WPC P a (fun o env' st' c =>
      match o with
      | .normal => WPC P b (Q.shift (c + 2)) env' st'
      | .brk => Q .brk env' st' (c + 2)
      | .ret rv => Q (.ret rv) env' st' (c + 1)) env st) :
    WPC P (.seq a b) Q env st := by
  intro k R hk
  apply MachineValidC.step (by rfl : Semantics.nextFor P (.exec (.seq a b) env st k) =
    some (.silent (.exec a env st (.seq b k))))
  change MachineValidC P (fun rv st' c => R rv st' (1 + c))
    (.exec a env st (.seq b k)) true
  apply h
  intro o env' st' cost ho
  rw [PostValidC.prefix]
  cases o with
  | normal =>
    apply MachineValidC.skip_seq
    have hb := ho k (fun rv t c => R rv t ((cost + 2) + c))
    have hbody := hb (fun o e t c hq => by
      rw [PostValidC.prefix]
      exact hk o e t ((cost + 2) + c) hq)
    simpa only [admin_cost] using hbody
  | brk =>
    apply MachineValidC.brk_seq
    have hp := hk .brk env' st' (cost + 2) ho
    change MachineValidC P (fun rv t c => R rv t ((cost + 2) + c))
      (.exec .brk env' st' k) false at hp
    simpa only [admin_cost] using hp
  | ret rv =>
    have hp := hk (.ret rv) env' st' (cost + 1) ho
    simpa only [PostValidC, returnTarget, Cont.returnCont, Cost.add_comm cost 1] using hp

theorem WPC.ite {c : Expr} {a b : Stmt}
    (h : match evalE P env st.mem c with
      | some (.u32 v) => (v ≠ 0 → WPC P a (Q.shift 1) env st) ∧ (v = 0 → WPC P b (Q.shift 1) env st)
      | _ => True) :
    WPC P (.ite c a b) Q env st := by
  intro k R hk
  cases hc : evalE P env st.mem c with
  | none =>
    apply MachineValidC.failed (by simp [Semantics.nextFor, Semantics.nextCore, hc])
    simp [Semantics.final, EmbC.Semantics.State.exec]
  | some value =>
    cases value with
    | u32 v =>
      have hs : (v ≠ 0 → WPC P a (Q.shift 1) env st) ∧
          (v = 0 → WPC P b (Q.shift 1) env st) := by simpa [hc] using h
      by_cases hz : v = 0
      · have hz' : v = 0#32 := hz
        apply MachineValidC.step
          (by simp [Semantics.nextFor, Semantics.nextCore, hc, hz'] : Semantics.nextFor P (.exec (.ite c a b) env st k) =
            some (.silent (.exec b env st k)))
        change MachineValidC P (fun rv st' cost => R rv st' (1 + cost)) (.exec b env st k) true
        apply hs.2 hz
        intro o e t cost hq
        rw [PostValidC.prefix]
        exact hk o e t (1 + cost) hq
      · have hz' : v ≠ 0#32 := hz
        apply MachineValidC.step
          (by simp [Semantics.nextFor, Semantics.nextCore, hc, hz'] : Semantics.nextFor P (.exec (.ite c a b) env st k) =
            some (.silent (.exec a env st k)))
        change MachineValidC P (fun rv st' cost => R rv st' (1 + cost)) (.exec a env st k) true
        apply hs.1 hz
        intro o e t cost hq
        rw [PostValidC.prefix]
        exact hk o e t (1 + cost) hq
    | _ =>
      apply MachineValidC.failed (by simp [Semantics.nextFor, Semantics.nextCore, hc])
      simp [Semantics.final, EmbC.Semantics.State.exec]

theorem WPC.ite_any {c : Expr} {a b : Stmt} (ha : WPC P a (Q.shift 1) env st)
    (hb : WPC P b (Q.shift 1) env st) : WPC P (.ite c a b) Q env st := by
  apply WPC.ite
  split
  · exact ⟨fun _ => ha, fun _ => hb⟩
  · trivial


/-- Total loop correctness, with an explicit decreasing measure and the
cost of completed iterations in the invariant. -/
theorem WPC.while {c : Expr} {body : Stmt}
    (I : Env → (KernelState P State) → Cost → Prop) (μ : Env → (KernelState P State) → Nat) (h0 : I env st 0)
    (hstep : ∀ env st k, I env st k →
      match evalE P env st.mem c with
      | some (.u32 v) =>
        (v = 0 → Q .normal env st (k + 1)) ∧
        (v ≠ 0 → WPC P body (fun o env' st' cb =>
          match o with
          | .normal => μ env' st' < μ env st ∧ I env' st' (k + cb + 2)
          | .brk => Q .normal env' st' (k + cb + 2)
          | .ret r => Q (.ret r) env' st' (k + cb + 1)) env st)
      | _ => True) :
    WPC P (.while c body) Q env st := by
  suffices H : ∀ m env st cost, μ env st ≤ m → I env st cost →
      WPC P (.while c body) (Q.shift cost) env st by
    exact (H _ env st 0 (Nat.le_refl _) h0).mono
      (fun o e t cost hq => by simpa [CPost.shift] using hq)
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro env st cost hm hI k R hk
    have hs := hstep env st cost hI
    cases hc : evalE P env st.mem c with
    | none =>
      apply MachineValidC.failed (by simp [Semantics.nextFor, Semantics.nextCore, hc])
      simp [Semantics.final, EmbC.Semantics.State.exec]
    | some value =>
      cases value with
      | u32 v =>
        simp only [hc] at hs
        by_cases hz : v = 0
        · have hz' : v = 0#32 := hz
          apply MachineValidC.step
            (by simp [Semantics.nextFor, Semantics.nextCore, hc, hz'] : Semantics.nextFor P (.exec (.while c body) env st k) =
              some (.silent (.exec .skip env st k)))
          have hp := hk .normal env st 1 (hs.1 hz)
          simpa [PostValidC, machineNextFresh, hc, hz, machineStepCost, Action.target] using hp
        · have hz' : v ≠ 0#32 := hz
          have hbeq : (v == 0#32) = false := beq_eq_false_iff_ne.mpr hz'
          apply MachineValidC.step
            (by simp [Semantics.nextFor, Semantics.nextCore, hc, hz'] : Semantics.nextFor P (.exec (.while c body) env st k) =
              some (.silent (.exec body env st (.loop c body k))))
          have hfresh : machineNextFresh P (.exec (.while c body) env st k) = true := by
            simp [machineNextFresh, hc, bne, hbeq]
          simp only [hfresh, machineStepCost, Action.target]
          apply hs.2 hz
          intro o env' st' cb ho
          rw [PostValidC.prefix]
          cases o with
          | normal =>
            apply MachineValidC.skip_loop
            have hlt : μ env' st' < m := by have := ho.1; omega
            have hw := ih (μ env' st') hlt env' st' (cost + cb + 2) (Nat.le_refl _) ho.2
            simp only [admin_cost]
            apply hw k (fun rv t c => R rv t ((cb + 2) + c))
            intro o e t c hq
            rw [PostValidC.prefix]
            apply hk o e t ((cb + 2) + c)
            simpa only [CPost.shift, Cost.add_assoc] using hq
          | brk =>
            apply MachineValidC.brk_loop
            have hq : Q.shift cost .normal env' st' (cb + 2) := by
              simpa only [CPost.shift, Cost.add_assoc] using ho
            have hp := hk .normal env' st' (cb + 2) hq
            simpa only [PostValidC, admin_cost] using hp
          | ret rv =>
            have hq : Q.shift cost (.ret rv) env' st' (1 + cb) := by
              simpa only [CPost.shift, Cost.add_assoc, Cost.add_comm cb 1] using ho
            have hp := hk (.ret rv) env' st' (1 + cb) hq
            simpa only [PostValidC, returnTarget, Cont.returnCont] using hp
      | _ =>
        apply MachineValidC.failed (by simp [Semantics.nextFor, Semantics.nextCore, hc])
        simp [Semantics.final, EmbC.Semantics.State.exec]

end rules
end EmbC
