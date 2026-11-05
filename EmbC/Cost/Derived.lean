import EmbC.Cost.Functions
import EmbC.Cost.Structural
import EmbC.Cost.Primitives

namespace EmbC

variable {State : Type}

section rules
variable {P : Prog} {Q : (CPost P State)} {env : Env} {st : (KernelState P State)}

def Stmt.size : Stmt → Nat
  | .seq a b => a.size + b.size + 1
  | .ite _ a b => max a.size b.size + 1
  | .while _ body => body.size + 1
  | _ => 1

/-- No loops, calls or kernel calls. -/
def Stmt.straight : Stmt → Bool
  | .seq a b => a.straight && b.straight
  | .ite _ a b => a.straight && b.straight
  | .while .. | .call .. | .ecall .. => false
  | _ => true

/-- Straight-line and without stores. -/
def Stmt.pure : Stmt → Bool
  | .seq a b => a.pure && b.pure
  | .ite _ a b => a.pure && b.pure
  | .skip | .assign .. | .ret _ | .brk => true
  | _ => false

theorem WPC.straight {s : Stmt} (hs : s.straight = true) :
    WPC P s (fun _ _ _ c => c.t ≤ 2 * s.size ∧ c.m = 0) env st := by
  induction s generalizing env st with
  | skip => exact WPC.skip (by simp [Stmt.size])
  | brk => exact WPC.brk (by simp [Stmt.size])
  | ret e =>
    cases e with
    | none => exact WPC.retVoid (by simp [Stmt.size])
    | some e => apply WPC.ret; split <;> simp [Stmt.size]
  | assign x e =>
    apply WPC.assign
    split
    · trivial
    · split <;> simp [Stmt.size]
  | store p i e =>
    apply WPC.store
    split
    · split
      · trivial
      · split <;> simp [Stmt.size]
    · trivial
  | setField p f e =>
    apply WPC.setField
    split
    · intro _; split <;> simp [Stmt.size]
    · trivial
  | seq a b iha ihb =>
    simp only [Stmt.straight, Bool.and_eq_true] at hs
    apply WPC.seq
    apply WPC.mono (iha hs.1)
    intro o env' st' c hc
    cases o with
    | normal =>
      apply WPC.mono (ihb hs.2)
      intro o2 env2 st2 c2 hc2
      simp only [CPost.shift, Stmt.size, Cost.add_t, Cost.add_m, reduceCostT, reduceCostM]; omega
    | brk => simp only [Stmt.size, Cost.add_t, Cost.add_m, reduceCostT, reduceCostM]; omega
    | ret v => simp only [Stmt.size, Cost.add_t, Cost.add_m, reduceCostT, reduceCostM]; omega
  | ite c a b iha ihb =>
    simp only [Stmt.straight, Bool.and_eq_true] at hs
    apply WPC.ite_any
    · apply WPC.mono (iha hs.1)
      intro o env' st' n hn
      simp only [CPost.shift, Stmt.size, Cost.add_t, Cost.add_m, reduceCostT, reduceCostM]; omega
    · apply WPC.mono (ihb hs.2)
      intro o env' st' n hn
      simp only [CPost.shift, Stmt.size, Cost.add_t, Cost.add_m, reduceCostT, reduceCostM]; omega
  | «while» c body => simp [Stmt.straight] at hs
  | call dst f args => simp [Stmt.straight] at hs
  | ecall dst f args => simp [Stmt.straight] at hs

theorem WPC.pure {s : Stmt} (hs : s.pure = true) :
    WPC P s (fun _ _ st' c => st' = st ∧ c.t ≤ 2 * s.size ∧ c.m = 0) env st := by
  induction s generalizing env st with
  | skip => exact WPC.skip (by simp [Stmt.size])
  | brk => exact WPC.brk (by simp [Stmt.size])
  | ret e =>
    cases e with
    | none => exact WPC.retVoid (by simp [Stmt.size])
    | some e => apply WPC.ret; split <;> simp [Stmt.size]
  | assign x e =>
    apply WPC.assign
    split
    · trivial
    · split <;> simp [Stmt.size]
  | seq a b iha ihb =>
    simp only [Stmt.pure, Bool.and_eq_true] at hs
    apply WPC.seq
    apply WPC.mono (iha hs.1)
    rintro o env' st' c ⟨rfl, hc⟩
    cases o with
    | normal =>
      apply WPC.mono (ihb hs.2)
      rintro o2 env2 st2 c2 ⟨rfl, hc2⟩
      simp only [CPost.shift, Stmt.size, Cost.add_t, Cost.add_m, reduceCostT, reduceCostM]
      exact ⟨by trivial, by omega⟩
    | brk =>
      simp only [Stmt.size, Cost.add_t, Cost.add_m, reduceCostT, reduceCostM]
      exact ⟨by trivial, by omega⟩
    | ret v =>
      simp only [Stmt.size, Cost.add_t, Cost.add_m, reduceCostT, reduceCostM]
      exact ⟨by trivial, by omega⟩
  | ite c a b iha ihb =>
    simp only [Stmt.pure, Bool.and_eq_true] at hs
    apply WPC.ite_any
    · apply WPC.mono (iha hs.1)
      rintro o env' st' n ⟨rfl, hn⟩
      simp only [CPost.shift, Stmt.size, Cost.add_t, Cost.add_m, reduceCostT, reduceCostM]
      exact ⟨by trivial, by omega⟩
    · apply WPC.mono (ihb hs.2)
      rintro o env' st' n ⟨rfl, hn⟩
      simp only [CPost.shift, Stmt.size, Cost.add_t, Cost.add_m, reduceCostT, reduceCostM]
      exact ⟨by trivial, by omega⟩
  | store p i e => simp [Stmt.pure] at hs
  | setField p f e => simp [Stmt.pure] at hs
  | «while» c body => simp [Stmt.pure] at hs
  | call dst f args => simp [Stmt.pure] at hs
  | ecall dst f args => simp [Stmt.pure] at hs

/-- What a call's result does to a `u32` destination. -/
theorem assignDst_u32 {env env' : Env} {m : Mem} {x : Var} {rv : Option Val}
    (hx : env.ty x = some .u32) (h : assignDst env m (some x) rv = some env') :
    ∃ n, rv = some (.u32 n) ∧ env' = env.set x (.u32 n) := by
  cases rv with
  | none => simp [assignDst] at h
  | some v =>
    simp only [assignDst_some, Env.assign, hx] at h
    split at h
    · rename_i ht
      obtain ⟨n, rfl⟩ := Mem.hasTy_u32_inv ht
      simp only [Option.some.injEq] at h
      exact ⟨n, rfl, h.symm⟩
    · simp at h

/-- Calling a function whose cost needs nothing of its arguments or of the state. -/
theorem WPC.call_any {dst : Option Var} {f : String} {args : List Expr}
    {post : List Val → (KernelState P State) → Option Val → (KernelState P State) → Cost → Prop}
    (hspec : FnCost P f (fun _ _ => True) post)
    (h : ∀ vs rv st' c env', post vs st rv st' c → assignDst env st'.mem dst rv = some env' →
      Q .normal env' st' (c + 2)) :
    WPC P (.call dst f args) Q env st := by
  apply WPC.call hspec
  split
  · trivial
  · rename_i vs _
    refine ⟨trivial, fun rv st' c hp => ?_⟩
    cases hd : assignDst env st'.mem dst rv with
    | none => trivial
    | some env' => exact h vs rv st' c env' hp hd


/-- Straight-line function costs include the body, entry, and possible void fallthrough. -/
theorem FnCost.straight {f : String} {fn : Fn} (hf : P.findFn f = some fn)
    (hs : fn.body.straight = true) :
    FnCost (State := State) P f (fun _ _ => True) (fun _ _ _ _ c => c.t ≤ 2 * fn.body.size + 2 ∧ c.m = 0) := by
  apply FnCost.intro hf
  intro vs st _
  split
  · trivial
  · apply WPC.mono (WPC.straight hs)
    intro o env' st' c hc
    simp only [retPostC]
    split <;> simp only [Cost.add_t, Cost.add_m, reduceCostT, reduceCostM]
    all_goals first | trivial | (constructor <;> omega) | (intro _; constructor <;> omega)

/-- A function whose body is straight-line code without stores also leaves the state alone. -/
theorem FnCost.pure {f : String} {fn : Fn} (hf : P.findFn f = some fn) (hs : fn.body.pure = true) :
    FnCost (State := State) P f (fun _ _ => True) (fun _ st _ st' c => st' = st ∧ c.t ≤ 2 * fn.body.size + 2 ∧ c.m = 0) := by
  apply FnCost.intro hf
  intro vs st _
  split
  · trivial
  · apply WPC.mono (WPC.pure hs)
    intro o env' st' c hc
    simp only [retPostC]
    split <;> simp only [Cost.add_t, Cost.add_m, reduceCostT, reduceCostM]
    all_goals first
      | trivial
      | exact ⟨hc.1, by omega, by omega⟩
      | (intro _; exact ⟨hc.1, by omega, by omega⟩)


end rules
end EmbC
