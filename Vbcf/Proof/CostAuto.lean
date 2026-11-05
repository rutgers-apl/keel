import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.CostBase
import Vbcf.Proof.CostReg

/-!
# Vbcf cost proofs: the amortised specification, and the automation

Every cost proof states an `Amort`: its time is paid at `A` per unit of work
spent and its words at one per unit of memory budget spent, with an allowance
`B rv` (time, depending on the value returned: a failing call may have done
unpaid work, and it ends the run) and `Bm` (words), and it hands `S rv` time
back to its caller (the slack of its own spending: a call that ticked and
returned `rv` can pay for the loop iteration that made it).

`wpc_auto` walks a function body with one rule per statement; it stops at a
loop, at a store to the budget cells, at a kernel call, and at a call whose
cost lemma is not registered (`fncost_register`).  `wpc_finish` closes a
postcondition goal by arithmetic.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC

set_option maxHeartbeats 1000000

/-- The amortised cost of a call (see the module comment). -/
def Amort (sb A : Nat) (B : Option Val → Nat) (Bm : Nat) (S : Option Val → Nat) :
    List Val → (KernelState prog State) → Option Val → (KernelState prog State) → Cost → Prop := fun _ st rv st' c =>
  ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
    c.t + A * w'.toNat + S rv ≤ A * wk st.mem sb + B rv ∧
    c.m + mm'.toNat ≤ mk st.mem sb + Bm

/-- The same allowance whatever is returned. -/
def allow (b : Nat) : Option Val → Nat := fun _ => b

/-- Allowance `bf` when the call returned `r` (its failure value), `b` otherwise. -/
def allowFail (r : BitVec 32) (bf b : Nat) : Option Val → Nat :=
  fun rv => if rv = some (.u32 r) then bf else b

@[simp] theorem allow_apply (b : Nat) (rv : Option Val) : allow b rv = b := rfl
@[simp] theorem allowFail_apply (r : BitVec 32) (bf b : Nat) (rv : Option Val) :
    allowFail r bf b rv = if rv = some (.u32 r) then bf else b := rfl

/-- The precondition of a cost proof: the arguments, and that the budget cells exist. -/
abbrev BudPre (sb : Nat) (args : List Val) : List Val → (KernelState prog State) → Prop := fun vs st =>
  vs = args ∧ ∃ w mm : BitVec 32, Budget st.mem sb w mm

/-- No slack. -/
def noSlack : Option Val → Nat := fun _ => 0

/-- Slack `s` when the call returned `r`. -/
def slackOn (r : BitVec 32) (s : Nat) : Option Val → Nat :=
  fun rv => if rv = some (.u32 r) then s else 0

/-- Slack `s` unless the call returned `r` (its failure value). -/
def slackUnless (r : BitVec 32) (s : Nat) : Option Val → Nat :=
  fun rv => if rv = some (.u32 r) then 0 else s

@[simp] theorem slackUnless_apply (r : BitVec 32) (s : Nat) (rv : Option Val) :
    slackUnless r s rv = if rv = some (.u32 r) then 0 else s := rfl

/-- Slack `s` when the call returned `r1` or `r2`. -/
def slackOr (r1 r2 : BitVec 32) (s : Nat) : Option Val → Nat :=
  fun rv => if rv = some (.u32 r1) ∨ rv = some (.u32 r2) then s else 0

@[simp] theorem noSlack_apply (rv : Option Val) : noSlack rv = 0 := rfl
@[simp] theorem slackOr_apply (r1 r2 : BitVec 32) (s : Nat) (rv : Option Val) :
    slackOr r1 r2 s rv = if rv = some (.u32 r1) ∨ rv = some (.u32 r2) then s else 0 := rfl
@[simp] theorem slackOn_apply (r : BitVec 32) (s : Nat) (rv : Option Val) :
    slackOn r s rv = if rv = some (.u32 r) then s else 0 := rfl

theorem Amort.mono {sb A Bm Bm' : Nat} {B B' S S' : Option Val → Nat} {vs : List Val} {st : (KernelState prog State)}
    {rv : Option Val} {st' : (KernelState prog State)} {c : Cost} (h : Amort sb A B Bm S vs st rv st' c)
    (hB : B rv ≤ B' rv) (hBm : Bm ≤ Bm') (hS : S' rv ≤ S rv) : Amort sb A B' Bm' S' vs st rv st' c := by
  obtain ⟨w', mm', hb, ht, hm⟩ := h
  exact ⟨w', mm', hb, by omega, by omega⟩

/-- A function whose body is straight-line code without stores, including
entry and administrative transitions. -/
theorem FnCost.amort_of_pure {f : String} {fn : Fn} (hf : Vbcf.prog.findFn f = some fn)
    (hs : fn.body.pure = true) (sb A : Nat) (args : List Val) :
    FnCost (State := State) Vbcf.prog f (BudPre sb args) (Amort sb A (allow (2 * fn.body.size + 2)) 0 noSlack) := by
  refine FnCost.mono (FnCost.pure hf hs) (fun _ _ _ => trivial) ?_
  rintro vs st rv st' c ⟨-, w, mm, hb⟩ ⟨rfl, ht, hm⟩
  exact ⟨w, mm, hb, by rw [hb.wk]; simp [noSlack, allow]; omega, by rw [hb.mk]; omega⟩

/-- A function whose body is straight-line code: its cost is at most twice
its size plus two, and it
allocates nothing, but the budget cells may have changed (it may have stored
to them), so it is not `Amort`.  Used only by hand. -/
theorem FnCost.straight' {f : String} {fn : Fn} (hf : Vbcf.prog.findFn f = some fn)
    (hs : fn.body.straight = true) :
    FnCost (State := State) Vbcf.prog f (fun _ _ => True) (fun _ _ _ _ c => c.t ≤ 2 * fn.body.size + 2 ∧ c.m = 0) :=
  FnCost.straight hf hs

/-! ## Destinations of calls -/

theorem Mem.hasTy_u64_inv {m : Mem} {v : Val} (h : m.hasTy v .u64 = true) : ∃ n, v = .u64 n := by
  cases v with
  | u64 n => exact ⟨n, rfl⟩
  | u32 _ => exact Bool.noConfusion h
  | ptr _ _ => exact Bool.noConfusion h
  | null => exact Bool.noConfusion h
  | uptr => exact Bool.noConfusion h
  | undef => exact Bool.noConfusion h

/-- A `u32` destination (the assignment first, so that `rfl` can decide the type). -/
theorem assignDst_u32' {env env' : Env} {m : Mem} {x : Var} {rv : Option Val}
    (h : assignDst env m (some x) rv = some env') (hx : env.ty x = some .u32) :
    ∃ n, rv = some (.u32 n) ∧ env' = env.set x (.u32 n) := assignDst_u32 hx h

/-- A `u64` destination. -/
theorem assignDst_u64' {env env' : Env} {m : Mem} {x : Var} {rv : Option Val}
    (h : assignDst env m (some x) rv = some env') (hx : env.ty x = some .u64) :
    ∃ n, rv = some (.u64 n) ∧ env' = env.set x (.u64 n) := by
  cases rv with
  | none => simp [assignDst] at h
  | some v =>
    simp only [assignDst_some, Env.assign, hx] at h
    split at h
    · rename_i ht
      obtain ⟨n, rfl⟩ := Mem.hasTy_u64_inv ht
      simp only [Option.some.injEq] at h
      exact ⟨n, rfl, h.symm⟩
    · simp at h

/-- No destination. -/
theorem assignDst_none' {env env' : Env} {m : Mem} {rv : Option Val}
    (h : assignDst env m none rv = some env') : env' = env := by
  rw [assignDst_none] at h; exact (Option.some.inj h).symm

/-! ## Calls whose arguments the proof cannot evaluate

A cost proof knows nothing of the pool, so an argument read from it is an
unknown value.  But the call binds its parameters only when the values have
the declared types, and gets stuck otherwise, which `WPC` allows; so the
caller only has to meet the callee's precondition for values of those types. -/

theorem bindParams_ne_none_cons {m : Mem} {x : Var} {t : Ty} {ps : List (Var × Ty)} {vs : List Val}
    (h : bindParams m ((x, t) :: ps) vs ≠ none) :
    ∃ v vs', vs = v :: vs' ∧ m.hasTy v t = true ∧ bindParams m ps vs' ≠ none := by
  cases vs with
  | nil => exact absurd rfl h
  | cons v vs' =>
    refine ⟨v, vs', rfl, ?_, ?_⟩
    · by_cases ht : m.hasTy v t = true
      · exact ht
      · simp [bindParams, ht] at h
    · intro hn
      simp only [bindParams] at h
      split at h
      · rw [hn] at h; exact h rfl
      · exact h rfl

theorem bindParams_ne_none_nil {m : Mem} {vs : List Val} (h : bindParams m [] vs ≠ none) : vs = [] := by
  cases vs with
  | nil => rfl
  | cons v vs' => exact absurd rfl h

/-- `WPC.call` for arguments that may not evaluate: the precondition is needed only
for values of the parameters' types, and the cost lemma is chosen once those values
are known. -/
theorem WPC.call_shape {P : Prog} {Q : (CPost P State)} {env : Env} {st : (KernelState P State)} {dst : Option Var}
    {f : String} {args : List Expr} {fn : Fn} {ps : List (Var × Ty)}
    (h : ∀ vs, evalArgs P env st.mem args = some vs → bindParams st.mem ps vs ≠ none →
      ∃ (pre : List Val → (KernelState P State) → Prop) (post : List Val → (KernelState P State) → Option Val → (KernelState P State) → Cost → Prop),
        FnCost (State := State) P f pre post ∧ pre vs st ∧ ∀ rv st' c, post vs st rv st' c →
          match assignDst env st'.mem dst rv with
          | none => True
          | some env' => Q .normal env' st' (c + 2))
    (hf : P.findFn f = some fn := by rfl) (hps : fn.params = ps := by rfl) :
    WPC P (.call dst f args) Q env st := by
  subst hps
  cases hv : evalArgs P env st.mem args with
  | none =>
    have hempty : FnCost (State := State) P f (fun _ _ => False) (fun _ _ _ _ _ => False) := by
      intro vs st hp; exact hp.elim
    apply WPC.call hempty
    simp [hv]
  | some vs =>
    by_cases hbp : bindParams st.mem fn.params vs = none
    · have hbad : FnCost (State := State) P f (fun vs' st' => vs' = vs ∧ st' = st)
          (fun _ _ _ _ _ => False) := by
        rintro vs' st' ⟨rfl, rfl⟩
        exact ⟨1, by simp [Prog.runC, machineRunC, machineRunCCore, Semantics.initial,
          Semantics.nextFor, Semantics.nextCore, hf, hbp, CallResC.sat]⟩
      apply WPC.call hbad
      rw [hv]
      exact ⟨⟨rfl, rfl⟩, fun _ _ _ hp => hp.elim⟩
    · obtain ⟨pre, post, hspec, hpre, hk⟩ := h vs hv hbp
      apply WPC.call hspec
      rw [hv]
      exact ⟨hpre, hk⟩

theorem evalArgs_cons' {P : Prog} {env : Env} {m : Mem} {e : Expr} {es : List Expr} {vs : List Val}
    (h : evalArgs P env m (e :: es) = some vs) :
    ∃ v vs', evalE P env m e = some v ∧ evalArgs P env m es = some vs' ∧ vs = v :: vs' := by
  simp only [evalArgs] at h
  split at h
  · rename_i v vs' h1 h2; simp only [Option.some.injEq] at h; exact ⟨v, vs', h1, h2, h.symm⟩
  · simp at h

open Lean Elab Command Meta in
/-- `fncost_register "f" fnDef f_cost`: proves once that `prog.findFn "f" = some fnDef`
(`fnDef_find`) and `fnDef.params = <its list>` (`fnDef_params`), and registers the cost
lemma `f_cost` for `wpc_call`.  The lemma's rate parameter must be named `A`; its other
arguments are found by unification or, for propositions, by `assumption`. -/
elab "fncost_register " nm:str fn:ident lem:ident : command => do
  let fnName := fn.getId
  let findName := fnName.appendAfter "_find"
  let paramsName := fnName.appendAfter "_params"
  let ps ← liftTermElabM do
    let fnE ← Term.elabTerm fn none
    let e ← mkAppM ``EmbC.Fn.params #[fnE]
    let r ← reduce e
    PrettyPrinter.delab r
  elabCommand (← `(theorem $(mkIdent findName) : Vbcf.prog.findFn $nm = some $fn := rfl))
  elabCommand (← `(theorem $(mkIdent paramsName) : EmbC.Fn.params $fn = $ps := rfl))
  let lemName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo lem
  let findFull ← liftCoreM <| realizeGlobalConstNoOverload (mkIdent findName)
  let paramsFull ← liftCoreM <| realizeGlobalConstNoOverload (mkIdent paramsName)
  modifyEnv fun env => fncostRegistry.addEntry env (nm.getString, findFull, paramsFull, lemName)

/-- A `return e` whose value is named, and known when `e` evaluates. -/
theorem WPC.ret_val {P : Prog} {Q : (CPost P State)} {env : Env} {st : (KernelState P State)} {e : Expr}
    (h : ∀ v, evalE P env st.mem e = some v → Q (.ret (some v)) env st 1) :
    WPC P (.ret (some e)) Q env st := by
  apply WPC.ret
  cases hv : evalE P env st.mem e with
  | none => trivial
  | some v => exact h v hv

/-! ## The tactics -/

/-- The arithmetic of costs: a goal about `.t` and `.m` of sums of costs and numerals. -/
macro "cost_simp" : tactic =>
  `(tactic| simp only [Cost.add_t, Cost.add_m, Cost.zero_t, Cost.zero_m, Cost.one_t, Cost.one_m,
    Cost.mk_t, Cost.mk_m, reduceCostT, reduceCostM, CPost.shift_apply, slackOn_apply, slackUnless_apply,
    slackOr_apply, noSlack_apply, allow_apply, allowFail_apply, Option.some.injEq, Val.u32.injEq,
    ↓reduceIte, BitVec.reduceEq, or_false, false_or, or_true, true_or] at *)
macro "cost_arith" : tactic => `(tactic| ((try cost_simp); ((try simp +arith only) <;> omega)))

/-- The simp set that exposes the next statement after a rule. -/
macro "wpc_simp" : tactic =>
  `(tactic| try simp only [CPost.shift_apply, Env.set, String.reduceEq, ↓reduceIte])

/-- A parameter's value has its type: a `u32` or `u64` value is named. -/
macro "wpc_ty" h:ident : tactic =>
  `(tactic| first | (obtain ⟨_, _e2⟩ := Mem.hasTy_u32_inv $h; subst _e2) | (obtain ⟨_, _e2⟩ := Mem.hasTy_u64_inv $h; subst _e2) | skip)

/-- After a call: the destination gets the returned word. -/
macro "wpc_dst" : tactic =>
  `(tactic| (split <;> first | trivial | (rename_i _env' _hasg; (first | (obtain ⟨_r, _h1, _h2⟩ := assignDst_u32' _hasg rfl; subst _h1; subst _h2) | (obtain ⟨_r, _h1, _h2⟩ := assignDst_u64' _hasg rfl; subst _h1; subst _h2) | (have _h2 := assignDst_none' _hasg; subst _h2)); wpc_simp)))

open Lean Elab Tactic Meta in
/-- A call of a function with a registered cost lemma: `WPC.call_shape`, the arguments
read off the callee's parameter types (one `u32` or `u64` value per parameter, the
first one, the struct, evaluated), then the cost lemma with its `A` set to the proof's
`A`, its propositional arguments by `assumption` and the rest by unification. -/
elab "wpc_call" : tactic => do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  let some call := ty.find? (fun e => e.isAppOfArity ``EmbC.Stmt.call 3)
    | throwError "wpc_call: the goal is not a call"
  let fname ← match call.getArg! 1 with
    | .lit (.strVal s) => pure s
    | _ => throwError "wpc_call: the callee is not a literal name"
  let some (_, findName, paramsName, lemName) :=
      (fncostRegistry.getState (← getEnv)).find? (·.1 == fname)
    | throwError "wpc_call: no cost lemma registered for {fname}"
  evalTactic (← `(tactic| (have _hbc := ‹Budget _ _ _ _›; apply WPC.call_shape (hf := $(mkIdent findName)) (hps := $(mkIdent paramsName)); intro _vs _hargs _hbp0; obtain ⟨_v0, _vs0, _h0, _hargs0, _e0⟩ := evalArgs_cons' _hargs; subst _e0; (try (simp only [evalE, Env.get, String.reduceEq, ↓reduceIte, Option.some.injEq] at _h0; subst _h0)); obtain ⟨_v1, _vs1, _e1, _ht1, _hbp1⟩ := bindParams_ne_none_cons _hbp0; (first | subst _e1 | (simp only [List.cons.injEq] at _e1; obtain ⟨_e1a, _e1b⟩ := _e1; subst _e1a; subst _e1b)); wpc_ty _ht1; (try (obtain ⟨_v2, _vs2, _e2, _ht2, _hbp2⟩ := bindParams_ne_none_cons _hbp1; subst _e2; wpc_ty _ht2)); (try (obtain ⟨_v3, _vs3, _e3, _ht3, _hbp3⟩ := bindParams_ne_none_cons _hbp2; subst _e3; wpc_ty _ht3)); (try (obtain ⟨_v4, _vs4, _e4, _ht4, _hbp4⟩ := bindParams_ne_none_cons _hbp3; subst _e4; wpc_ty _ht4)); (try (obtain ⟨_v5, _vs5, _e5, _ht5, _hbp5⟩ := bindParams_ne_none_cons _hbp4; subst _e5; wpc_ty _ht5)); (try (obtain ⟨_v6, _vs6, _e6, _ht6, _hbp6⟩ := bindParams_ne_none_cons _hbp5; subst _e6; wpc_ty _ht6)); (try (obtain ⟨_v7, _vs7, _e7, _ht7, _hbp7⟩ := bindParams_ne_none_cons _hbp6; subst _e7; wpc_ty _ht7)); (try (obtain ⟨_v8, _vs8, _e8, _ht8, _hbp8⟩ := bindParams_ne_none_cons _hbp7; subst _e8; wpc_ty _ht8)); (try (have _en1 := bindParams_ne_none_nil _hbp1; subst _en1)); (try (have _en2 := bindParams_ne_none_nil _hbp2; subst _en2)); (try (have _en3 := bindParams_ne_none_nil _hbp3; subst _en3)); (try (have _en4 := bindParams_ne_none_nil _hbp4; subst _en4)); (try (have _en5 := bindParams_ne_none_nil _hbp5; subst _en5)); (try (have _en6 := bindParams_ne_none_nil _hbp6; subst _en6)); (try (have _en7 := bindParams_ne_none_nil _hbp7; subst _en7)); (try (have _en8 := bindParams_ne_none_nil _hbp8; subst _en8)))))
  -- the cost lemma, now that the argument values exist
  let goal ← getMainGoal
  let (pre, post, specGoal, rest) ← do
    let gs ← evalTacticAt (← `(tactic| refine ⟨?pre, ?post, ?spec, ?rest⟩)) goal
    let find (n : Name) : TacticM MVarId := do
      for g in gs do
        if (← g.getTag).eraseMacroScopes == n then return g
      throwError "wpc_call: no goal {n} among {← gs.mapM (·.getTag)}"
    pure (← find `pre, ← find `post, ← find `spec, ← find `rest)
  specGoal.withContext do
    let lemE ← mkConstWithFreshMVarLevels lemName
    let (args, binders, _) ← forallMetaTelescope (← inferType lemE)
    let app := mkAppN lemE args
    -- the rate is the proof's `A`
    let names := (← inferType lemE).getForallBinderNames
    for a in args, nm in names do
      if nm == `A then
        let aFVar ← getLocalDeclFromUserName `A
        unless ← isDefEq a (mkFVar aFVar.fvarId) do throwError "wpc_call: cannot set A"
    let appTy ← instantiateMVars (← inferType app)
    unless appTy.isAppOfArity ``EmbC.FnCost 5 do
      throwError "wpc_call: {lemName} is not a cost lemma"
    let specTy ← instantiateMVars (← specGoal.getType)
    unless specTy.isAppOfArity ``EmbC.FnCost 5 do
      throwError "wpc_call: unexpected spec goal {specTy}"
    for i in [:2] do
      unless ← isDefEq (appTy.getArg! i) (specTy.getArg! i) do
        throwError "wpc_call: incompatible oracle context for {lemName}"
    unless ← isDefEq (appTy.getArg! 2) (specTy.getArg! 2) do
      throwError "wpc_call: the cost lemma {lemName} is for another function"
    pre.assign (appTy.getArg! 3)
    post.assign (appTy.getArg! 4)
    specGoal.assign app
    -- Propositional arguments (e.g. `6 ≤ A`) from the context, including
    -- weaker rate thresholds implied by the caller's threshold.
    for a in args, bi in binders do
      let _ := bi
      let a ← instantiateMVars a
      if a.isMVar then
        let aTy ← instantiateMVars (← inferType a)
        if ← isProp aTy then
          let mv := a.mvarId!
          try mv.assumption catch _ =>
            let savedState ← saveState
            let savedGoals ← getGoals
            try
              setGoals [mv]
              evalTactic (← `(tactic| omega))
              setGoals savedGoals
            catch _ => savedState.restore
  replaceMainGoal [rest]
  evalTactic (← `(tactic| (refine ⟨⟨rfl, _, _, _hbc⟩, ?_⟩; rintro _rv _st' _c ⟨_w', _mm', _hb', _ht, _hm⟩; rw [Budget.wk _hbc] at _ht; rw [Budget.mk _hbc] at _hm; wpc_dst)))

/-! ## Helpers from the leaf proofs: assignments whose value the proof can see, the stack range -/

/-! ## Helpers: assignments whose value the proof can see -/

/-- An assignment, with the value named when it evaluates. -/
theorem WPC.assign_eval {P : Prog} {Q : (CPost P State)} {env : Env} {st : (KernelState P State)} {x : Var} {e : Expr}
    (h : ∀ v, evalE P env st.mem e = some v →
      match env.assign st.mem x v with
      | none => True
      | some env' => Q .normal env' st 1) :
    WPC P (.assign x e) Q env st := by
  apply WPC.assign
  cases hv : evalE P env st.mem e with
  | none => trivial
  | some v => exact h v hv

/-- An assignment of a value shifted right by `k`: whatever it is, it is below `2^(32-k)`. -/
theorem WPC.assign_shr {P : Prog} {Q : (CPost P State)} {env : Env} {st : (KernelState P State)} {x : Var} {e : Expr}
    {k : BitVec 32} (hx : env.ty x = some .u32)
    (h : ∀ n : BitVec 32, n.toNat < 2 ^ (32 - k.toNat) → Q .normal (env.set x (.u32 n)) st 1) :
    WPC P (.assign x (.bin .shr e (.lit32 k))) Q env st := by
  apply WPC.assign
  simp only [evalE]
  cases evalE P env st.mem e with
  | none => trivial
  | some v =>
    cases v with
    | u32 a =>
      by_cases hk : k.toNat < 32
      · simp only [evalBin, evalArith, hk, ↓reduceIte, Env.assign, hx, Mem.hasTy_u32]
        refine h _ ?_
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
        have ha := a.isLt
        have h2 : 2 ^ 32 = 2 ^ (32 - k.toNat) * 2 ^ k.toNat := by
          rw [← Nat.pow_add]; congr 1; omega
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
        omega
      · simp [evalBin, evalArith, hk]
    | _ => simp [evalBin]


/-- The value of local `x`, if it is a `u32`. -/
def envU32 (env : Env) (x : Var) : Nat :=
  match env.get x with
  | some (.u32 v) => v.toNat
  | _ => 0

/-- Close the "next iteration" goal of a counted loop: the measure drops and the
invariant holds again with the counter `i + 1` (`h : (i + 1#32).toNat = i.toNat + 1`). -/
macro "loop_next" h:ident : tactic => `(tactic| (simp only [envU32, Env.get, String.reduceEq, ↓reduceIte,
  List.cons.injEq, Prod.mk.injEq, Val.u32.injEq, and_assoc, true_and, and_true, exists_eq', exists_eq_left,
  exists_and_left, exists_and_right, exists_const, exists_eq_left', Cost.add_t, Cost.add_m, Cost.one_t,
  Cost.one_m, Cost.zero_t, Cost.zero_m, reduceCostT, reduceCostM, $h:ident]; and_intros <;> omega))

/-- `loop_next` when the invariant also carries the budget and struct cells. -/
macro "loop_nextB" h:ident : tactic => `(tactic| (simp only [envU32, Env.get, String.reduceEq, ↓reduceIte,
  List.cons.injEq, Prod.mk.injEq, Val.u32.injEq, and_assoc, true_and, and_true, exists_eq', exists_eq_left,
  exists_and_left, exists_and_right, exists_const, exists_eq_left', Cost.add_t, Cost.add_m, Cost.one_t,
  Cost.one_m, Cost.zero_t, Cost.zero_m, reduceCostT, reduceCostM, $h:ident]; and_intros <;>
  (first | assumption | exact (‹Budget _ _ _ _›).1 | exact (‹Budget _ _ _ _›).2 | omega)))

/-! ## Helpers: the stack range -/

/-- An array store keeps the budget and any struct cell. -/
theorem WPC.store_bud_fld {Q : (CPost prog State)} {env : Env} {st : (KernelState prog State)} {sb i : Nat} {v : Val}
    {w mm : BitVec 32} {p j e : Expr} (hb : Budget st.mem sb w mm) (hf : Fld st.mem sb i v)
    (h : ∀ m', Budget m' sb w mm → Fld m' sb i v → Q .normal env { st with mem := m' } 1) :
    WPC Vbcf.prog (.store p j e) Q env st := by
  apply WPC.store
  split
  · split
    · trivial
    · split
      · trivial
      · rename_i m' hs; exact h m' (hb.storeArr hs) (hf.storeArr hs)
  · trivial

/-- The stack-range precondition: `st->sp = base + n` without wrapping. -/
def SpPre (sb : Nat) (base n : BitVec 32) (m : Mem) : Prop :=
  ∃ sp : BitVec 32, Fld m sb 11 (.u32 sp) ∧ base.toNat + n.toNat = sp.toNat


theorem le_mul_succ {C m k b : Nat} (hk : k ≤ C * m) (hb : b ≤ C) : k + b ≤ C * (m + 1) := by
  rw [Nat.mul_succ]; omega

/-! ## Helpers from the core proofs: calls whose arguments are locals, joins, charges -/

/-! ## Helpers: calls whose arguments are locals -/

open Lean Meta in
/-- Introduce the equations at the head of the goal, substituting each one
between variables so that the later-declared variable (the callee's fresh
argument value) is the one eliminated. -/
partial def introEqsSubst (g : MVarId) : MetaM MVarId := do
  let ty ← instantiateMVars (← g.getType)
  unless ty.isForall do return g
  unless ← isProp ty.bindingDomain! do return g
  unless ty.bindingDomain!.isAppOfArity ``Eq 3 do
    let (_, g) ← g.intro1
    return ← introEqsSubst g
  let (h, g) ← g.intro1
  let g ← g.withContext do
    let some (_, a, b) := (← instantiateMVars (← h.getType)).eq? | return g
    let elimB : Option Bool ←
      if a.isFVar && b.isFVar then
        pure (some ((← b.fvarId!.getDecl).index > (← a.fvarId!.getDecl).index))
      else if b.isFVar then pure (some true)
      else if a.isFVar then pure (some false)
      else pure none
    match elimB with
    | none => return g
    | some symm => try return (← substCore g h symm).2 catch _ => return g
  introEqsSubst g

open Lean Elab Tactic Meta in
/-- After `wpc_call`: every hypothesis `evalArgs … args = some vs` whose
arguments are locals and literals (no pool or field reads) is evaluated, so
that the callee's argument values are the caller's locals (and what is known
of them, e.g. a mask bound from `WPC.assign_band`, carries over). -/
elab "cost_args" : tactic => do
  let mut names : Array Name := #[]
  for d in (← withMainContext getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``Eq 3 && (ty.getArg! 1).isAppOfArity ``EmbC.evalArgs 4 then
      let args := (ty.getArg! 1).getArg! 3
      let bad := (args.find? fun e => e.isConstOf ``EmbC.Expr.index || e.isConstOf ``EmbC.Expr.field
        || e.isConstOf ``EmbC.Expr.padd).isSome
      unless bad do names := names.push d.userName
  for nm in names do
    let some d := (← withMainContext getLCtx).findFromUserName? nm | continue
    let g ← getMainGoal
    let (_, g') ← g.revert #[d.fvarId]
    replaceMainGoal [g']
    evalTactic (← `(tactic| (intro _ha; (try simp only [evalArgs, evalE, evalBin, evalArith, evalCast,
      Env.get, String.reduceEq, ↓reduceIte, Option.some.injEq, List.cons.injEq, Val.u32.injEq,
      Val.u64.injEq, and_true, true_and] at _ha); revert _ha; (try simp only [and_imp]))))
    let g ← getMainGoal
    replaceMainGoal [← introEqsSubst g]

open Lean Elab Tactic Meta in
/-- `name_bud st w m h`: give names to the most recent budget hypothesis
`Budget s.mem sb w' mm'` (after a call, whose result names are inaccessible):
the state `st`, the budgets `w`, `m`, the hypothesis `h`. -/
elab "name_bud " st:ident w:ident m:ident h:ident : tactic => withMainContext do
  let mut g ← getMainGoal
  for d in (← getLCtx).decls.toList.reverse do
    let some d := d | continue
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``Vbcf.Proof.Budget 4 then
      let memE := ty.getArg! 0
      let wE := ty.getArg! 2
      let mE := ty.getArg! 3
      g ← g.rename d.fvarId h.getId
      if wE.isFVar then g ← g.rename wE.fvarId! w.getId
      if mE.isFVar then g ← g.rename mE.fvarId! m.getId
      if memE.isAppOfArity ``EmbC.MachineStore.mem 2 && (memE.getArg! 1).isFVar then
        g ← g.rename (memE.getArg! 1).fvarId! st.getId
      break
  replaceMainGoal [g]


open Lean Elab Tactic Meta in
/-- Clear the hypotheses about evaluation (`evalE`, `evalArgs`, `bindParams`,
`assignDst`, `hasTy`), which the arithmetic of `wpc_finish` never needs. -/
elab "cost_clean" : tactic => withMainContext do
  let names := [``EmbC.evalE, ``EmbC.evalArgs, ``EmbC.bindParams, ``EmbC.assignDst, ``EmbC.Mem.hasTy]
  let mut g ← getMainGoal
  for d in (← getLCtx).getFVars.reverse do
    let some ld := (← getLCtx).find? d.fvarId! | continue
    if ld.isImplementationDetail then continue
    let ty ← instantiateMVars ld.type
    if (ty.find? fun e => names.any e.isConstOf).isSome then
      try g ← g.clear d.fvarId! catch _ => pure ()
  replaceMainGoal [g]




/-- `if (c) { x = f(...); } b`: the two branches join before `b` (so that `b`
is proved once, not once per branch), with `x` any value and at most `K`
more time paid. -/
theorem WPC.ite_call_join {P : Prog} {Q : (CPost P State)} {env : Env} {st : (KernelState P State)} {sb A K : Nat}
    {w mm : BitVec 32} {c : Expr} {x : Var} {f : String} {args : List Expr} {b : Stmt}
    (hbud : Budget st.mem sb w mm)
    (ha : WPC P (.call (some x) f args) (fun o env' st' k => o = .normal ∧
      ∃ v, env' = env.set x (.u32 v) ∧ ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
        k.t + A * w'.toNat ≤ A * w.toNat + K ∧ k.m + mm'.toNat ≤ mm.toNat) env st)
    (hskip : ∃ v, env = env.set x (.u32 v))
    (hb : ∀ (v : BitVec 32) (st' : (KernelState P State)) (k : Cost) (w' mm' : BitVec 32), Budget st'.mem sb w' mm' →
      k.t + A * w'.toNat ≤ A * w.toNat + K + 2 → k.m + mm'.toNat ≤ mm.toNat →
      WPC P b (Q.shift (k + 2)) (env.set x (.u32 v)) st') :
    WPC P (.seq (.ite c (.call (some x) f args) .skip) b) Q env st := by
  apply WPC.seq
  apply WPC.mono (Q := fun o env' st' k => o = .normal ∧
      ∃ v, env' = env.set x (.u32 v) ∧ ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
        k.t + A * w'.toNat ≤ A * w.toNat + K + 2 ∧ k.m + mm'.toNat ≤ mm.toNat)
  · apply WPC.ite_any
    · apply WPC.mono ha
      rintro o env' st' k ⟨rfl, v, rfl, w', mm', hb', hk, hkm⟩
      exact ⟨rfl, v, rfl, w', mm', hb', by simp; omega, by simp; omega⟩
    · apply WPC.skip
      obtain ⟨v, hv⟩ := hskip
      exact ⟨rfl, v, hv, w, mm, hbud, by simp; omega, by simp⟩
  · rintro o env' st' k ⟨rfl, v, rfl, w', mm', hb', hk, hkm⟩
    exact hb v st' k w' mm' hb' hk hkm

/-- One `WPC.ite_call_join` with the call's allowance bounded by `K`. -/
macro "wpc_join " A:term:max K:term:max : tactic => `(tactic|
  (refine WPC.ite_call_join (A := $A) (K := $K) ‹Budget _ _ _ _› ?_ ⟨0#32, by simp [Env.set]⟩ ?_;
   (wpc_call; cost_args;
    refine ⟨by first | trivial | rfl, _, rfl, _, _, ‹Budget _ _ _ _›, ?_, ?_⟩ <;> cost_arith);
   intro _v _st _k _w _mm _hb _hk _hkm; wpc_simp))

/-- A postcondition at an equal cost. -/
theorem CPost.cost_eq {P : Prog} {Q : (CPost P State)} {o : Outcome} {env : Env} {st : (KernelState P State)} {c c' : Cost}
    (h : Q o env st c) (ht : c.t = c'.t) (hm : c.m = c'.m) : Q o env st c' := by
  rw [← Cost.ext ht hm]; exact h

theorem WPC.charge_work {Q : (CPost prog State)} {env : Env} {st : (KernelState prog State)} {sb : Nat} {w mm k : BitVec 32}
    {E : Expr} {rest : Stmt} (hb : Budget st.mem sb w mm)
    (hst : env.get "st" = some (.ptr sb 0))
    (hE : evalE Vbcf.prog env st.mem E = some (.u32 k))
    (hfail : ∀ m', Budget m' sb w mm → Q (.ret (some (.u32 0#32))) env { st with mem := m' } ⟨6, 0⟩)
    (hok : k ≤ w → ∀ m', Budget m' sb (w - k) mm →
      WPC Vbcf.prog rest (Q.shift ⟨6, 0⟩) env { st with mem := m' }) :
    WPC Vbcf.prog (.seq (.ite (.bin .lt (.field (.var "st") "work") E)
        (.seq (.setField (.var "st") "err" ERR_LIMIT) (.ret (some (.lit32 0#32)))) .skip)
      (.seq (.setField (.var "st") "work" (.bin .sub (.field (.var "st") "work") E)) rest)) Q env st := by
  apply WPC.seq
  apply WPC.ite
  simp only [evalE, hst, hE, hb.ld_work, ↓reduceIte, evalBin, evalArith]
  by_cases hlt : w < k
  · simp only [hlt, Val.ofBool, decide_true, ↓reduceIte]
    refine ⟨fun _ => ?_, fun h => absurd h (by decide)⟩
    apply WPC.seq
    apply WPC.setField_bud hb (by decide) (by decide)
    intro m' hb'
    apply WPC.ret
    simp only [evalE, CPost.shift_apply]
    exact CPost.cost_eq (hfail m' hb') (by cost_simp) (by cost_simp)
  · simp only [hlt, Val.ofBool, decide_false, ↓reduceIte, Bool.false_eq_true]
    refine ⟨fun h => absurd rfl h, fun _ => ?_⟩
    apply WPC.skip
    simp only [CPost.shift_apply]
    apply WPC.seq
    apply WPC.setWork (x := w - k) hb (by simp [evalE, hst]) (by simp [evalE, hst, hE, hb.ld_work, evalBin, evalArith])
    intro m' hb'
    have hle : k ≤ w := by
      rw [BitVec.le_def]; rw [BitVec.lt_def] at hlt; omega
    apply WPC.mono (hok hle m' hb')
    intro o env' st' c hq
    simp only [CPost.shift_apply] at hq ⊢
    exact CPost.cost_eq hq (by cost_simp; omega) (by cost_simp; omega)
theorem WPC.charge_mem {Q : (CPost prog State)} {env : Env} {st : (KernelState prog State)} {sb : Nat} {w mm k : BitVec 32}
    {E : Expr} {rest : Stmt} (hb : Budget st.mem sb w mm)
    (hst : env.get "st" = some (.ptr sb 0))
    (hE : evalE Vbcf.prog env st.mem E = some (.u32 k))
    (hfail : ∀ m', Budget m' sb w mm → Q (.ret (some (.u32 0#32))) env { st with mem := m' } ⟨6, 0⟩)
    (hok : k ≤ mm → ∀ m', Budget m' sb w (mm - k) →
      WPC Vbcf.prog rest (Q.shift ⟨6, 0⟩) env { st with mem := m' }) :
    WPC Vbcf.prog (.seq (.ite (.bin .lt (.field (.var "st") "mem") E)
        (.seq (.setField (.var "st") "err" ERR_LIMIT) (.ret (some (.lit32 0#32)))) .skip)
      (.seq (.setField (.var "st") "mem" (.bin .sub (.field (.var "st") "mem") E)) rest)) Q env st := by
  apply WPC.seq
  apply WPC.ite
  simp only [evalE, hst, hE, hb.ld_mem, ↓reduceIte, evalBin, evalArith]
  by_cases hlt : mm < k
  · simp only [hlt, Val.ofBool, decide_true, ↓reduceIte]
    refine ⟨fun _ => ?_, fun h => absurd h (by decide)⟩
    apply WPC.seq
    apply WPC.setField_bud hb (by decide) (by decide)
    intro m' hb'
    apply WPC.ret
    simp only [evalE, CPost.shift_apply]
    exact CPost.cost_eq (hfail m' hb') (by cost_simp) (by cost_simp)
  · simp only [hlt, Val.ofBool, decide_false, ↓reduceIte, Bool.false_eq_true]
    refine ⟨fun h => absurd rfl h, fun _ => ?_⟩
    apply WPC.skip
    simp only [CPost.shift_apply]
    apply WPC.seq
    apply WPC.setMem (x := mm - k) hb (by simp [evalE, hst]) (by simp [evalE, hst, hE, hb.ld_mem, evalBin, evalArith])
    intro m' hb'
    have hle : k ≤ mm := by
      rw [BitVec.le_def]; rw [BitVec.lt_def] at hlt; omega
    apply WPC.mono (hok hle m' hb')
    intro o env' st' c hq
    simp only [CPost.shift_apply] at hq ⊢
    exact CPost.cost_eq hq (by cost_simp; omega) (by cost_simp; omega)
/-- An assignment to a `u64` variable, whatever value it receives. -/
theorem WPC.assign_u64 {P : Prog} {Q : (CPost P State)} {env : Env} {st : (KernelState P State)} {x : Var} {e : Expr}
    (hx : env.ty x = some .u64)
    (h : ∀ n : BitVec 64, Q .normal (env.set x (.u64 n)) st 1) : WPC P (.assign x e) Q env st := by
  apply WPC.assign
  cases evalE P env st.mem e with
  | none => trivial
  | some v =>
    simp only [Env.assign, hx]
    by_cases ht : st.mem.hasTy v .u64 = true
    · obtain ⟨n, rfl⟩ := Mem.hasTy_u64_inv ht
      simp only [ht, ↓reduceIte]
      exact h n
    · simp only [ht]; trivial

/-- `if (c) { x = e; } b` with `x` a `u32`: the branches join before `b`, `x` any value. -/
theorem WPC.ite_assign_join {P : Prog} {Q : (CPost P State)} {env : Env} {st : (KernelState P State)} {c e : Expr} {x : Var}
    {b : Stmt} (hx : env.ty x = some .u32) (hskip : ∃ v, env = env.set x (.u32 v))
    (hb : ∀ (v : BitVec 32) (k : Cost), k.t ≤ 2 → k.m = 0 →
      WPC P b (Q.shift (k + 2)) (env.set x (.u32 v)) st) :
    WPC P (.seq (.ite c (.assign x e) .skip) b) Q env st := by
  apply WPC.seq
  apply WPC.mono (Q := fun o env' st' k => o = .normal ∧ st' = st ∧ k.t ≤ 2 ∧ k.m = 0 ∧
    ∃ v, env' = env.set x (.u32 v))
  · apply WPC.ite_any
    · apply WPC.assign_u32 hx
      intro n
      exact ⟨rfl, rfl, by cost_arith, by cost_simp, n, rfl⟩
    · apply WPC.skip
      exact ⟨rfl, rfl, by cost_arith, by cost_simp, hskip⟩
  · rintro o env' st' k ⟨rfl, rfl, hkt, hkm, v, rfl⟩
    exact hb v k hkt hkm

/-! ## Helpers for `ck_hgrow`: a struct cell kept across the budget stores -/

/-- `WPC.charge_work` keeping a struct cell `i` other than `work`. -/
theorem WPC.charge_work_fld {Q : (CPost prog State)} {env : Env} {st : (KernelState prog State)} {sb i : Nat} {v : Val}
    {w mm k : BitVec 32} {E : Expr} {rest : Stmt} (hb : Budget st.mem sb w mm)
    (hfld : Fld st.mem sb i v) (hi : ∀ t, fieldIn ckS.fields "work" ≠ some (i, t))
    (hst : env.get "st" = some (.ptr sb 0))
    (hE : evalE Vbcf.prog env st.mem E = some (.u32 k))
    (hfail : ∀ m', Budget m' sb w mm → Q (.ret (some (.u32 0#32))) env { st with mem := m' } ⟨6, 0⟩)
    (hok : k ≤ w → ∀ m', Budget m' sb (w - k) mm → Fld m' sb i v →
      WPC Vbcf.prog rest (Q.shift ⟨6, 0⟩) env { st with mem := m' }) :
    WPC Vbcf.prog (.seq (.ite (.bin .lt (.field (.var "st") "work") E)
        (.seq (.setField (.var "st") "err" ERR_LIMIT) (.ret (some (.lit32 0#32)))) .skip)
      (.seq (.setField (.var "st") "work" (.bin .sub (.field (.var "st") "work") E)) rest)) Q env st := by
  apply WPC.seq
  apply WPC.ite
  simp only [evalE, hst, hE, hb.ld_work, ↓reduceIte, evalBin, evalArith]
  by_cases hlt : w < k
  · simp only [hlt, Val.ofBool, decide_true, ↓reduceIte]
    refine ⟨fun _ => ?_, fun h => absurd h (by decide)⟩
    apply WPC.seq
    apply WPC.setField_bud hb (by decide) (by decide)
    intro m' hb'
    apply WPC.ret
    simp only [evalE, CPost.shift_apply]
    exact CPost.cost_eq (hfail m' hb') (by cost_simp) (by cost_simp)
  · simp only [hlt, Val.ofBool, decide_false, ↓reduceIte, Bool.false_eq_true]
    refine ⟨fun h => absurd rfl h, fun _ => ?_⟩
    apply WPC.skip
    simp only [CPost.shift_apply]
    apply WPC.seq
    apply WPC.setField
    simp only [evalE, hst, hE, hb.ld_work, evalBin, evalArith, ↓reduceIte]
    intro _
    cases hs : st.mem.storeField Vbcf.prog sb "work" (.u32 (w - k)) with
    | none => trivial
    | some m' =>
      have hle : k ≤ w := by
        rw [BitVec.le_def]; rw [BitVec.lt_def] at hlt; omega
      apply WPC.mono (hok hle m' (hb.setWork hs) (hfld.storeField hs hi))
      intro o env' st' c hq
      simp only [CPost.shift_apply] at hq ⊢
      exact CPost.cost_eq hq (by cost_simp; omega) (by cost_simp; omega)

/-- `WPC.charge_mem` keeping a struct cell `i` other than `mem`. -/
theorem WPC.charge_mem_fld {Q : (CPost prog State)} {env : Env} {st : (KernelState prog State)} {sb i : Nat} {v : Val}
    {w mm k : BitVec 32} {E : Expr} {rest : Stmt} (hb : Budget st.mem sb w mm)
    (hfld : Fld st.mem sb i v) (hi : ∀ t, fieldIn ckS.fields "mem" ≠ some (i, t))
    (hst : env.get "st" = some (.ptr sb 0))
    (hE : evalE Vbcf.prog env st.mem E = some (.u32 k))
    (hfail : ∀ m', Budget m' sb w mm → Q (.ret (some (.u32 0#32))) env { st with mem := m' } ⟨6, 0⟩)
    (hok : k ≤ mm → ∀ m', Budget m' sb w (mm - k) → Fld m' sb i v →
      WPC Vbcf.prog rest (Q.shift ⟨6, 0⟩) env { st with mem := m' }) :
    WPC Vbcf.prog (.seq (.ite (.bin .lt (.field (.var "st") "mem") E)
        (.seq (.setField (.var "st") "err" ERR_LIMIT) (.ret (some (.lit32 0#32)))) .skip)
      (.seq (.setField (.var "st") "mem" (.bin .sub (.field (.var "st") "mem") E)) rest)) Q env st := by
  apply WPC.seq
  apply WPC.ite
  simp only [evalE, hst, hE, hb.ld_mem, ↓reduceIte, evalBin, evalArith]
  by_cases hlt : mm < k
  · simp only [hlt, Val.ofBool, decide_true, ↓reduceIte]
    refine ⟨fun _ => ?_, fun h => absurd h (by decide)⟩
    apply WPC.seq
    apply WPC.setField_bud hb (by decide) (by decide)
    intro m' hb'
    apply WPC.ret
    simp only [evalE, CPost.shift_apply]
    exact CPost.cost_eq (hfail m' hb') (by cost_simp) (by cost_simp)
  · simp only [hlt, Val.ofBool, decide_false, ↓reduceIte, Bool.false_eq_true]
    refine ⟨fun h => absurd rfl h, fun _ => ?_⟩
    apply WPC.skip
    simp only [CPost.shift_apply]
    apply WPC.seq
    apply WPC.setField
    simp only [evalE, hst, hE, hb.ld_mem, evalBin, evalArith, ↓reduceIte]
    intro _
    cases hs : st.mem.storeField Vbcf.prog sb "mem" (.u32 (mm - k)) with
    | none => trivial
    | some m' =>
      have hle : k ≤ mm := by
        rw [BitVec.le_def]; rw [BitVec.lt_def] at hlt; omega
      apply WPC.mono (hok hle m' (hb.setMem hs) (hfld.storeField hs hi))
      intro o env' st' c hq
      simp only [CPost.shift_apply] at hq ⊢
      exact CPost.cost_eq hq (by cost_simp; omega) (by cost_simp; omega)

/-- The struct has a cell 4 (`hcap`) when it has its budget cells. -/
theorem Budget.fld4 {m : Mem} {sb : Nat} {w mm : BitVec 32} (hb : Budget m sb w mm) :
    ∃ v, Fld m sb 4 v := by
  obtain ⟨cells, hblk, hc⟩ := hb.1
  have h20 : 20 < cells.size := by
    rcases Nat.lt_or_ge 20 cells.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at hc; simp at hc
  exact ⟨cells[4]'(by omega), cells, hblk, Array.getElem?_eq_getElem _⟩

/-- A `u32 *` value is not a pointer to the struct. -/
theorem ptr_u32_ne_sb {m : Mem} {sb i : Nat} {x v : Val} (hfld : Fld m sb i x)
    (hty : m.hasTy v (.ptr .u32) = true) : ∀ b, v = .ptr b 0 → b ≠ sb := by
  rintro b rfl rfl
  obtain ⟨cells, hblk, -⟩ := hfld
  unfold Mem.hasTy at hty
  simp only [hblk] at hty
  exact absurd hty (by decide)

/-- An assignment, whatever the value (of the variable's type). -/
theorem WPC.assign_set {P : Prog} {Q : (CPost P State)} {env : Env} {st : (KernelState P State)} {x : Var} {e : Expr}
    (h : ∀ v t, env.ty x = some t → st.mem.hasTy v t = true → Q .normal (env.set x v) st 1) :
    WPC P (.assign x e) Q env st := by
  apply WPC.assign
  cases hv : evalE P env st.mem e with
  | none => trivial
  | some v =>
    simp only [Env.assign]
    cases ht : env.ty x with
    | none => trivial
    | some t =>
      simp only []
      by_cases hty : st.mem.hasTy v t = true
      · simp only [hty, ↓reduceIte]; exact h v t ht hty
      · simp only [hty]; trivial

theorem Fld.load_undef {m : Mem} {sb i : Nat} {f : String} {t : Ty} (h : Fld m sb i .undef)
    (hf : fieldIn ckS.fields f = some (i, t)) : m.loadField Vbcf.prog sb f = none := by
  obtain ⟨cells, hb, hc⟩ := h
  have hslot : m.fieldSlot Vbcf.prog sb f = some (⟨.struct "ck", cells⟩, i, t) := by
    unfold Mem.fieldSlot; rw [hb]; simp [prog_ck, StructDef.field?, hf]
  unfold Mem.loadField
  simp only [hslot, hc]

theorem costC_kvfree (v : Val) : Ext.costC prog .kvfree [v] = ⟨0, 0⟩ := by
  simp [Ext.costC, Ext.cost, Ext.words]

/-- `x = 1 + (e & k)`: whatever the value, it is between 1 and `k + 1`. -/
theorem WPC.assign_one_band {P : Prog} {Q : (CPost P State)} {env : Env} {st : (KernelState P State)} {x : Var} {e : Expr}
    {k : BitVec 32} (hx : env.ty x = some .u32) (hk : k.toNat < 4294967295)
    (h : ∀ n : BitVec 32, 1 ≤ n.toNat → n.toNat ≤ k.toNat + 1 → Q .normal (env.set x (.u32 n)) st 1) :
    WPC P (.assign x (.bin .add (.lit32 1#32) (.bin .band e (.lit32 k)))) Q env st := by
  apply WPC.assign
  simp only [evalE]
  cases evalE P env st.mem e with
  | none => trivial
  | some v =>
    cases v with
    | u32 a =>
      simp only [evalBin, evalArith, Env.assign, hx, Mem.hasTy_u32, ↓reduceIte]
      have hb : (a &&& k).toNat ≤ k.toNat := by rw [BitVec.toNat_and]; exact Nat.and_le_right
      generalize a &&& k = y at hb ⊢
      have he : (1#32 + y).toNat = y.toNat + 1 := by
        rw [BitVec.toNat_add]; simp; omega
      exact h _ (by omega) (by omega)
    | _ => simp [evalBin]

/-- `a; b` through an intermediate condition `J` on the states after `a`. -/
theorem WPC.seq_join {P : Prog} {Q : (CPost P State)} {env : Env} {st : (KernelState P State)} {a b : Stmt}
    (J : Env → (KernelState P State) → Cost → Prop)
    (ha : WPC P a (fun o env' st' k => match o with
      | .normal => J env' st' k
      | .brk => Q .brk env' st' (k + 2)
      | .ret rv => Q (.ret rv) env' st' (k + 1)) env st)
    (hb : ∀ env' st' k, J env' st' k → WPC P b (Q.shift (k + 2)) env' st') :
    WPC P (.seq a b) Q env st := by
  apply WPC.seq
  apply WPC.mono ha
  intro o env' st' k h
  cases o with
  | normal => exact hb _ _ _ h
  | brk => exact h
  | ret r => exact h

/-- An `if` on a call's result `r` held in a local: both branches, each knowing
whether the condition held (`r = c` or `r ≠ c`), which settles the call's slack. -/
macro "wpc_ite_case" : tactic => `(tactic| (apply WPC.ite; simp only [evalE, Env.get, String.reduceEq, ↓reduceIte, evalBin, evalArith, Val.ofBool]; constructor <;> intro _hc <;> simp at _hc <;> (first | subst _hc | (simp only [_hc, slackUnless_apply, slackOr_apply, slackOn_apply, Option.some.injEq, Val.u32.injEq, ↓reduceIte] at *) | skip)))


/-- One statement of the body (the first rule that applies): sequencing, `skip`,
an `if` (both branches, whatever the condition), a return, an assignment (the
value kept when it evaluates from locals and literals, the bound kept for a
masked, shifted or `1 + (e & k)` value, else any value of the variable's type),
an array store (keeping the budget and the most recent struct cell `Fld`), a
store to a field other than the budget cells, or a call with a registered cost
lemma (`wpc_call`, then `cost_args` so the callee's arguments are the caller's
locals). -/
syntax "wpc_step" : tactic
macro_rules | `(tactic| wpc_step) => `(tactic| first
  | apply WPC.seq
  | (apply WPC.skip; wpc_simp)
  | apply WPC.ite_any
  | (apply WPC.ret_val; intro _v _hv; (try (simp only [evalE, evalBin, evalArith, Env.get, String.reduceEq, ↓reduceIte, Option.some.injEq, Budget.ld_work ‹Budget _ _ _ _›, Budget.ld_mem ‹Budget _ _ _ _›] at _hv; subst _hv)); wpc_simp)
  | (apply WPC.retVoid; wpc_simp)
  | (apply WPC.brk; wpc_simp)
  | (apply WPC.assign_eval; intro _v _hv;
      simp only [evalE, evalBin, evalArith, evalCast, Env.get, String.reduceEq, ↓reduceIte,
        Option.some.injEq, Nat.reduceMod, Nat.reduceLT, BitVec.toNat_ofNat] at _hv; subst _hv;
      simp only [Env.assign, Env.ty, String.reduceEq, ↓reduceIte, Mem.hasTy_u32, Mem.hasTy_u64]; wpc_simp)
  | (refine WPC.assign_band ?_ ?_; (rfl); intro _n _hn; simp only [BitVec.toNat_ofNat] at _hn; wpc_simp)
  | (refine WPC.assign_one_band ?_ ?_ ?_; (rfl); (decide); intro _n _hn1 _hn; simp only [BitVec.toNat_ofNat] at _hn; wpc_simp)
  | (refine WPC.assign_shr ?_ ?_; (rfl); intro _n _hn; wpc_simp)
  | (refine WPC.assign_u32 ?_ ?_; (rfl); intro _n; wpc_simp)
  | (refine WPC.assign_u64 ?_ ?_; (rfl); intro _n; wpc_simp)
  | (apply WPC.assign_set; intro _v _t _hty _hv; simp only [Env.ty, String.reduceEq, ↓reduceIte, Option.some.injEq] at _hty; subst _hty; wpc_simp)
  | (apply WPC.assign_any; intro _v _env' _henv; wpc_simp)
  | (apply WPC.store_bud_fld ‹Budget _ _ _ _› ‹Fld _ _ _ _›; intro _m' _hb _hf; wpc_simp)
  | (apply WPC.store_bud ‹Budget _ _ _ _›; intro _m' _hb; wpc_simp)
  | (refine WPC.setField_bud ‹Budget _ _ _ _› ?_ ?_ ?_; (decide); (decide); intro _m' _hb; wpc_simp)
  | (wpc_call; cost_args))

/-- Every statement of every open goal until a loop, a budget store, a kernel call or
an unregistered call. -/
macro "wpc_auto" : tactic => `(tactic| repeat (any_goals wpc_step))

open Lean in
/-- Close an `Amort` postcondition by arithmetic, with the current budget cells
(`hwk`/`hmk` from `fncost_body` give the entry values); the numeral sums are
normalised before `omega` (which is very slow on deeply nested sums). -/
macro "wpc_finish" : tactic => do
  let hwk := mkIdent `hwk
  let hmk := mkIdent `hmk
  `(tactic| ((try simp only [retPostC]); (try intro _); simp only [CPost.shift_apply, Amort, slackOn_apply, slackUnless_apply, slackOr_apply, noSlack_apply, allow_apply, allowFail_apply]; refine ⟨_, _, ‹Budget _ _ _ _›, ?_, ?_⟩ <;> ((try simp only [Cost.add_t, Cost.add_m, Cost.zero_t, Cost.zero_m, Cost.one_t, Cost.one_m, Cost.mk_t, Cost.mk_m, reduceCostT, reduceCostM, slackOn_apply, slackUnless_apply, slackOr_apply, noSlack_apply, allow_apply, allowFail_apply, Option.some.injEq, Val.u32.injEq, ↓reduceIte, BitVec.reduceEq, or_false, false_or, or_true, true_or, $hwk:ident, $hmk:ident] at *); ((try simp +arith only) <;> omega))))

/-- `wpc_finish` on every open goal it can close, after `cost_clean`. -/
macro "wpc_done" : tactic => `(tactic| all_goals (try (cost_clean; wpc_finish)))


open Lean in
/-- After `apply FnCost.intro (fn := f) rfl` and `rintro vs st ⟨rfl, w, mm, hb⟩`: name the
budget values (`hwk`, `hmk`) and open the body. -/
macro "fncost_body" fn:term : tactic => do
  let hb := mkIdent `hb
  let hwk := mkIdent `hwk
  let hmk := mkIdent `hmk
  `(tactic| (have $hwk := Budget.wk $hb; have $hmk := Budget.mk $hb; simp [$fn:term, bindParams, Budget.hasTy $hb]; simp only [Stmt.block, initLocals, List.map, List.cons_append, List.nil_append, Ty.zero]))

end Vbcf.Proof
