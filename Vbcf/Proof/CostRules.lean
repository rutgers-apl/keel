import EmbC.Kernel
import Vbcf.Prog
import Vbcf.Proof.CostMid
import Vbcf.Proof.CostBool2
import Vbcf.Proof.CostAci
import EmbC.Semantics.Correctness

/-!
# Vbcf cost proofs: the rule functions (poly, clause, aci, bit-blast)

Per function `(A ≥, B, S)`, lines of proof, `auto` when `wpc_auto` and a finishing
tactic did it alone (`rl_done` is `wpc_done` that also splits on the callees'
`allowFail`/`slackUnless` conditions).  `Bm = 0` everywhere.

* `lin_term` (100, 200, `slackUnless 0 A`; 12), `lin_atom` (100, 350, `slackUnless 0 A`; 12):
  `wpc_ite_case` after the first push.
* `odd_mul_sub` (–, 80, noSlack; 5, auto), `r_poly_norm_eq` (100, 26000; 5, auto).
* `bb_ite` (–, 60·255+30; 38): counted loop over a mask.
* `aci_flat` (150, `allowFail 0 200 20`, `slackUnless 0 35`; ~110): recursion on the depth
  (`FnCost.rec`, as `aci_absorb`), the children paid by their slack.
* `aci_nf` (150, `allowFail NOID 600 300`; ~105): `st->sp` read after `aci_flat`
  (`rl_sp_or`), kept across `spend` and `aci_sort` by the frame lemma; the C checks give
  `SpPre` and `n ≤ 1024`; `spend(n(n-1)/2)` pays `aci_sort` + `aci_uniq` (`rl_sort_paid`).
* `r_aci_norm` (150, 3000; ~75): the comparison loop (`i < la`) paid by the C's `spend(la)`.
* `r_resolution` (100, 500·np+11000; ~80): `spend(st->sp - base)` pays `cl_erase`
  (`rl_cl_erase_cost`: valid for any `sp`, also `sp < base`), joins for the pivots and
  the `i == 0` block.
* `r_factoring` (100, 80·na+2300000; ~200): `push` with `st->sp` tracked (`rl_push_sp`), so
  `m = st->sp - kb ≤ n ≤ 255` and the duplicate search is a constant.
* `lin_add` (300, `allowFail 0 1000 100`, `slackUnless 0 150`; ~200): the C's reject
  `b1 < b0 || e < b1 || e > MAX_POOL` bounds the merge (paid by `spend(e - b0)`), the tail
  loops pay by their pushes, the copy by `spend(n)`.
* `lin_f` (400, `allowFail 0 3000 100`, `slackUnless 0 100`; ~420): recursion on the depth,
  joins for the fall-through `if`s; the C's reject `st->sp < base || st->sp > MAX_POOL`
  before each `spend` gives `lin_scale`'s precondition (`rl_spend_scale`).
* `r_poly_norm` (400, 7000; ~75): the comparison loop paid by `spend(n)`.
* Bit-blast helpers not in the task's call graph (their signatures span two lines), proved
  here and registered: `bb_ripple` (–, 100·nx+50; 31), `bb_sub` (300, 20·nb+100·nx+400; 5),
  `bb_ult` (–, 60·nl+100; 32), `bb_slt` (–, 60·nl+200; 17), `bb_shift_limit` (100, 100; 37),
  `bb_rsh_stage` (100, 40·n+150; 56), `bb_shift` (100, 60·ny+1300·nb+8000; 99; the stage
  loop runs at most 31 times: each continuing iteration is below 31).
* `bb_neg` (300, 120·nb+500; 30), `bb_add` (300, 20500·nb+82000; 71), `bb_atom` (100, 20000; 5,
  auto), `bb_term` (300, 5400000; 36), `r_bitblast` (300, 5410000; 6, auto).

Helpers (prefixed `rl_`): `rl_ite_cases`, `rl_finish`, `rl_done`, `rl_ite_case`,
`rl_slack_simp`, `rl_name`, `rl_args` (one fact per call argument, so an argument is
known even when another reads the pool); the frame lemma `rl_next_frame`/`rl_frame_cost`
(a function that never stores field `f0`, never frees and calls only such functions keeps
the cell) with `rl_spend_sp`, `rl_aci_sort_sp`; `rl_push_sp` (`push` moves `st->sp` up by
one; `rl_and` combines two cost facts about one call); `rl_cl_erase_cost`; the joins
`rl_join`, `rl_ite_join`, `rl_ite_assign2_join`; `rl_spend_erase`, `rl_spend_scale`.
-/

namespace Vbcf.Proof

variable {State : Type}
open EmbC

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

theorem rl_ite_pos {c : Prop} [Decidable c] {α : Sort _} {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

theorem rl_ite_neg {c : Prop} [Decidable c] {α : Sort _} {a b : α} (h : ¬ c) : (if c then a else b) = b := by
  simp [h]

open Lean Elab Tactic Meta in
/-- The condition of the first `if` (without bound variables) in a hypothesis or the goal. -/
def rlFindIteCond (e : Lean.Expr) : Option Lean.Expr :=
  (e.find? fun t => t.isAppOfArity ``ite 5 && !(t.getArg! 1).hasLooseBVars).map (·.getArg! 1)

open Lean Elab Tactic Meta in
/-- Split on the condition of an `if` in the context (typically the slack of a call
whose result is returned: `slackUnless 0#32 s (some (.u32 r))`). -/
elab "rl_ite_cases" : tactic => withMainContext do
  let mut cond? : Option Lean.Expr := none
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ty.isAppOf ``LE.le || ty.isAppOf ``LT.lt do continue
    if let some c := rlFindIteCond ty then
      cond? := some c
      break
  if cond?.isNone then cond? := rlFindIteCond (← instantiateMVars (← getMainTarget))
  let some c := cond? | throwError "rl_ite_cases: no if"
  let cStx ← Term.exprToSyntax c
  evalTactic (← `(tactic| (by_cases _hc : $cStx <;> first | simp only [rl_ite_pos _hc] at * | simp only [rl_ite_neg _hc] at *)))

/-- An `if` on a call's result: both branches, the callee's allowance and slack settled
by the condition (`wpc_ite_case`, which also expands `allowFail` and keeps the condition). -/
macro "rl_ite_case" : tactic => `(tactic| (apply WPC.ite; simp only [evalE, Env.get, String.reduceEq,
  ↓reduceIte, evalBin, evalArith, Val.ofBool]; constructor <;> intro _hc <;> simp at _hc <;>
  (try simp only [slackUnless_apply, slackOr_apply, slackOn_apply, allowFail_apply, Option.some.injEq,
    Val.u32.injEq] at *) <;>
  (first | (subst _hc; (try simp only [eq_self_iff_true, ite_true, ↓reduceIte] at *)) |
    (simp only [rl_ite_neg _hc] at *) | skip)))


theorem rl_evalArgs_cons {P : Prog} {env : Env} {m : Mem} {e : Expr} {es : List Expr} {v : Val}
    {vs : List Val} (h : evalArgs P env m (e :: es) = some (v :: vs)) :
    evalE P env m e = some v ∧ evalArgs P env m es = some vs := by
  obtain ⟨v', vs', h1, h2, h3⟩ := evalArgs_cons' h
  simp only [List.cons.injEq] at h3
  obtain ⟨rfl, rfl⟩ := h3
  exact ⟨h1, h2⟩

open Lean Elab Tactic Meta in
/-- After `wpc_call`: split every `evalArgs … (e :: es) = some (v :: vs)` into one fact per
argument and evaluate each argument that reads only locals and literals (so that a callee's
argument is known even when another argument of the call reads the pool). -/
elab "rl_args" : tactic => do
  for _ in [0:200] do
    let some fv ← withMainContext do
        for d in (← getLCtx).decls.toList.reverse.filterMap id do
          if d.isImplementationDetail then continue
          let ty ← instantiateMVars d.type
          if ty.isAppOfArity ``Eq 3 && (ty.getArg! 1).isAppOfArity ``EmbC.evalArgs 4 then
            let args := (ty.getArg! 1).getArg! 3
            let rhs := ty.getArg! 2
            if args.isAppOfArity ``List.cons 3 && rhs.isAppOfArity ``Option.some 2 &&
                (rhs.getArg! 1).isAppOfArity ``List.cons 3 then
              return some d.fvarId
        return none
      | return
    let g ← getMainGoal
    let (_, g') ← g.revert #[fv]
    replaceMainGoal [g']
    evalTactic (← `(tactic| (intro _ha; obtain ⟨_he, _hr⟩ := rl_evalArgs_cons _ha; clear _ha; (try (simp only [evalE, evalBin, evalArith, evalCast, Env.get, String.reduceEq, ↓reduceIte, Option.some.injEq, Val.u32.injEq, Val.u64.injEq] at _he; first | subst _he | clear _he)))))

open Lean Elab Tactic Meta in
/-- `rl_name "x" => v`: name the value of local `x` (a word) in the environment of the goal. -/
elab "rl_name " x:str " => " nm:ident : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  -- the environment of the `WPC` goal (its fourth argument), else the whole goal
  let envE := if tgt.isAppOfArity ``EmbC.WPC 6 then tgt.getArg! 4 else tgt
  let found := envE.find? fun e =>
    e.isAppOfArity ``Prod.mk 4 && (match e.getArg! 2 with
      | .lit (.strVal s) => s == x.getString
      | _ => false) &&
    (let r := e.getArg! 3
     r.isAppOfArity ``Prod.mk 4 && (r.getArg! 3).isAppOfArity ``EmbC.Val.u32 1 &&
       ((r.getArg! 3).getArg! 0).isFVar)
  let some e := found | throwError "rl_name: no word local {x.getString} with a variable value"
  let v := ((e.getArg! 3).getArg! 3).getArg! 0
  replaceMainGoal [← (← getMainGoal).rename v.fvarId! nm.getId]

macro "rl_slack_simp" : tactic => `(tactic| simp only [slackUnless_apply, slackOr_apply, slackOn_apply,
  allowFail_apply, Option.some.injEq, Val.u32.injEq] at *)

open Lean in
/-- `wpc_finish`, splitting on the `if`s left by the callees' allowances and slack
(a call whose result is returned: its slack depends on whether it failed). -/
macro "rl_finish" : tactic => do
  let hwk := mkIdent `hwk
  let hmk := mkIdent `hmk
  `(tactic| ((try simp only [retPostC]); (try intro _); simp only [CPost.shift_apply, Amort, slackOn_apply, slackUnless_apply, slackOr_apply, noSlack_apply, allow_apply, allowFail_apply]; refine ⟨_, _, ‹Budget _ _ _ _›, ?_, ?_⟩ <;> ((try simp only [Cost.add_t, Cost.add_m, Cost.zero_t, Cost.zero_m, Cost.one_t, Cost.one_m, Cost.mk_t, Cost.mk_m, reduceCostT, reduceCostM, slackOn_apply, slackUnless_apply, slackOr_apply, noSlack_apply, allow_apply, allowFail_apply, Option.some.injEq, Val.u32.injEq, ↓reduceIte, BitVec.reduceEq, or_false, false_or, or_true, true_or, $hwk:ident, $hmk:ident] at *); (repeat' rl_ite_cases); all_goals ((try simp +arith only) <;> omega))))

/-- `wpc_done`, then `rl_finish` on what is left. -/
macro "rl_done" : tactic => `(tactic| (wpc_done; all_goals (try (cost_clean; rl_finish))))

/-! ## A struct cell kept by a call: the frame of the functions that never store it -/

/-- `s` never stores to field `f0`, never frees, and calls only functions in `F`. -/
def rl_keeps (f0 : String) (F : List String) : Stmt → Bool
  | .setField _ g _ => g != f0
  | .seq a b => rl_keeps f0 F a && rl_keeps f0 F b
  | .ite _ a b => rl_keeps f0 F a && rl_keeps f0 F b
  | .while _ b => rl_keeps f0 F b
  | .call _ g _ => F.contains g
  | .ecall _ e _ => match e with
    | .kvfree => false
    | _ => true
  | _ => true

/-- Every function of `F` keeps field `f0` (and calls only functions of `F`). -/
def rl_FrameOK (f0 : String) (F : List String) : Prop :=
  ∀ g, F.contains g = true → ∃ fn, prog.findFn g = some fn ∧ rl_keeps f0 F fn.body = true

/-- Pending statements also obey the frame restriction. -/
def rl_cont_keeps (f0 : String) (F : List String) : Semantics.Cont → Prop
  | .stop => True
  | .seq s k | .loop _ s k => rl_keeps f0 F s = true ∧ rl_cont_keeps f0 F k
  | .function _ k | .call _ _ k => rl_cont_keeps f0 F k

/-- The active statement or callee, and every pending continuation, keep the cell. -/
def rl_state_keeps (f0 : String) (F : List String) : (Semantics.ExecState prog State) → Prop
  | .regular s _ _ _ k => rl_keeps f0 F s = true ∧ rl_cont_keeps f0 F k
  | .callstate (.internal g) _ _ _ k => F.contains g = true ∧ rl_cont_keeps f0 F k
  | .callstate (.external e) _ _ _ k =>
    (match e with | .kvfree => false | _ => true) = true ∧ rl_cont_keeps f0 F k
  | .returnstate _ _ _ k => rl_cont_keeps f0 F k

theorem rl_returnCont_keeps {f0 : String} {F : List String} {k k' : Semantics.Cont}
    {rt : Option Ty} (hk : rl_cont_keeps f0 F k)
    (hr : k.returnCont = some (rt, k')) : rl_cont_keeps f0 F k' := by
  induction k with
  | stop | call => simp [Semantics.Cont.returnCont] at hr
  | seq s k ih | loop condition s k ih => exact ih hk.2 hr
  | function rt0 k =>
    simp only [Semantics.Cont.returnCont, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact hk

theorem rl_next_keeps {f0 : String} {F : List String} (hF : rl_FrameOK f0 F)
    {q : (Semantics.ExecState prog State)} {a : (Semantics.ExecAction prog State)} (hk : rl_state_keeps f0 F q)
    (hn : Semantics.nextFor prog q = some a) : rl_state_keeps f0 F a.target := by
  cases q with
  | regular s env mem orc k =>
    obtain ⟨hs, hk⟩ := hk
    cases s <;> simp only [Semantics.nextFor, Semantics.nextCore, Semantics.returnTarget] at hn
    all_goals repeat' split at hn
    all_goals cases hn
    all_goals try have hr := rl_returnCont_keeps hk (by assumption)
    all_goals simp_all [Semantics.Action.target, rl_state_keeps, rl_cont_keeps, rl_keeps,
      Bool.and_eq_true]
  | callstate f vs mem orc k =>
    cases f with
    | internal g =>
      obtain ⟨hg, hk⟩ := hk
      obtain ⟨fn, hfn, hb⟩ := hF g hg
      simp only [Semantics.nextFor, Semantics.nextCore, hfn] at hn
      split at hn
      · cases hn
      · cases hn
        exact ⟨hb, hk⟩
    | external ext =>
      simp only [Semantics.nextFor, Semantics.nextCore] at hn
      split at hn
      · cases hn
      · cases hn
        exact hk.2
  | returnstate rv mem orc k =>
    cases k <;> simp only [Semantics.nextFor, Semantics.nextCore] at hn
    all_goals repeat' split at hn
    all_goals cases hn
    all_goals exact ⟨rfl, hk⟩

theorem rl_next_frame {f0 : String} {i : Nat} {t0 : Ty}
    (hf0 : fieldIn ckS.fields f0 = some (i, t0)) {F : List String}
    {sb : Nat} {v : Val} {q : (Semantics.ExecState prog State)} {a : (Semantics.ExecAction prog State)}
    (hk : rl_state_keeps f0 F q) (hn : Semantics.nextFor prog q = some a)
    (hf : Fld (Semantics.stateKernelState q).mem sb i v) :
    Fld (Semantics.stateKernelState a.target).mem sb i v := by
  cases q with
  | regular s env mem orc k =>
    cases s <;> simp only [Semantics.nextFor, Semantics.nextCore, Semantics.returnTarget] at hn
    all_goals repeat' split at hn
    all_goals cases hn
    all_goals simp only [Semantics.Action.target, Semantics.stateKernelState] at *
    all_goals try contradiction
    all_goals first
      | exact hf
      | exact Fld.storeArr hf (by assumption)
      | exact Fld.storeField hf (by assumption) (fieldIn_ne_of_ne hf0
          (by simpa only [rl_state_keeps, rl_keeps, bne_iff_ne] using hk.1))
  | callstate f vs mem orc k =>
    cases f <;> simp only [Semantics.nextFor, Semantics.nextCore] at hn
    all_goals repeat' split at hn
    all_goals cases hn
    all_goals simp only [Semantics.Action.target, Semantics.stateKernelState] at *
    all_goals first
      | exact hf
      | exact Fld.ext hf (by assumption) (by
          rintro b _ rfl
          simp [rl_state_keeps] at hk)
  | returnstate rv mem orc k =>
    cases k <;> simp only [Semantics.nextFor, Semantics.nextCore] at hn
    all_goals repeat' split at hn
    all_goals cases hn
    all_goals exact hf

theorem rl_frame_path {f0 : String} {i : Nat} {t0 : Ty}
    (hf0 : fieldIn ckS.fields f0 = some (i, t0)) {F : List String}
    (hF : rl_FrameOK f0 F) {sb : Nat} {v : Val} {q q' : (Semantics.ExecState prog State)}
    (h : Semantics.RawStar (Semantics.rawStepFor prog) q q') :
    rl_state_keeps f0 F q → Fld (Semantics.stateKernelState q).mem sb i v →
      Fld (Semantics.stateKernelState q').mem sb i v := by
  induction h with
  | refl => intro _ hf; exact hf
  | step _ _ _ hs _ ih =>
    intro hk hf
    obtain ⟨a, hn, rfl⟩ := hs
    exact ih (rl_next_keeps hF hk hn) (rl_next_frame hf0 hk hn hf)

/-- A function of `F` keeps cell `i` (field `f0`) along its operational execution. -/
theorem rl_frame_cost {f0 : String} {i : Nat} {t0 : Ty}
    (hf0 : fieldIn ckS.fields f0 = some (i, t0)) {F : List String}
    (hF : rl_FrameOK f0 F) {sb : Nat} {v : Val} {g : String} (hg : F.contains g = true)
    {pre : List Val → (KernelState prog State) → Prop}
    {post : List Val → (KernelState prog State) → Option Val → (KernelState prog State) → Cost → Prop}
    (h : FnCost (State := State) prog g pre post) :
    FnCost (State := State) prog g (fun vs st => pre vs st ∧ Fld st.mem sb i v)
      (fun vs st rv st' c => post vs st rv st' c ∧ Fld st'.mem sb i v) := by
  rintro vs st ⟨hp, hf⟩
  obtain ⟨fuel, hfl⟩ := h vs st hp
  refine ⟨fuel, ?_⟩
  have hresult : ∀ result : (CallResC prog State), prog.runC fuel g vs st = result →
      result.sat (post vs st) →
      result.sat (fun rv st' c => post vs st rv st' c ∧ Fld st'.mem sb i v) := by
    intro result hr
    cases result with
    | timeout => intro hfl; exact hfl
    | stuck => intro _; trivial
    | ok r =>
      obtain ⟨rv, st', c⟩ := r
      intro hfl
      refine ⟨hfl, ?_⟩
      have he : prog.run fuel g vs st = .ok (rv, st') := by
        rw [← runC_erase, hr]
        rfl
      exact rl_frame_path hf0 hF (Semantics.run_ok_path he) ⟨hg, trivial⟩ hf
  exact hresult _ rfl hfl

theorem rl_frame_spend : rl_FrameOK "sp" ["spend"] := by
  intro g hg
  simp only [List.contains_cons, List.contains_nil, Bool.or_false, beq_iff_eq] at hg
  subst hg
  exact ⟨_, rfl, by decide⟩


/-- `a && b` evaluated to a non-zero word: `a` did. -/
theorem rl_land_fst {P : Prog} {env : Env} {m : Mem} {a b : Expr} {v : BitVec 32}
    (h : evalE P env m (.land a b) = some (.u32 v)) (hv : v ≠ 0#32) :
    ∃ x : BitVec 32, evalE P env m a = some (.u32 x) ∧ x ≠ 0#32 := by
  simp only [evalE] at h
  split at h
  · rename_i x hx
    by_cases hx0 : x = 0#32
    · subst hx0
      simp at h
      first | exact absurd h hv | exact absurd h.symm hv
    · exact ⟨x, hx, hx0⟩
  · simp at h

theorem lin_term_cost (sb A : Nat) (hA : 100 ≤ A) (a : BitVec 32) (c : BitVec 64) :
    FnCost (State := State) prog "lin_term" (BudPre sb [.ptr sb 0, .u32 a, .u64 c])
      (Amort sb A (allow 200) 0 (slackUnless 0#32 A)) := by
  apply FnCost.intro (fn := linTerm) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body linTerm
  have hA6 : 6 ≤ A := by omega
  apply WPC.seq
  wpc_step
  apply WPC.seq
  wpc_ite_case
  · wpc_auto
    wpc_done
  wpc_auto
  wpc_done

fncost_register "lin_term" linTerm lin_term_cost

theorem lin_atom_cost (sb A : Nat) (hA : 100 ≤ A) (a : BitVec 32) (m : BitVec 64) :
    FnCost (State := State) prog "lin_atom" (BudPre sb [.ptr sb 0, .u32 a, .u64 m])
      (Amort sb A (allow 350) 0 (slackUnless 0#32 A)) := by
  apply FnCost.intro (fn := linAtom) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body linAtom
  have hA6 : 6 ≤ A := by omega
  apply WPC.seq
  wpc_step
  apply WPC.seq
  wpc_ite_case
  · wpc_auto
    wpc_done
  wpc_auto
  wpc_done

fncost_register "lin_atom" linAtom lin_atom_cost

theorem odd_mul_sub_cost (sb A : Nat) (m : BitVec 32) :
    FnCost (State := State) prog "odd_mul_sub" (BudPre sb [.ptr sb 0, .u32 m])
      (Amort sb A (allow 80) 0 noSlack) := by
  apply FnCost.intro (fn := oddMulSub) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body oddMulSub
  wpc_auto
  wpc_done

fncost_register "odd_mul_sub" oddMulSub odd_mul_sub_cost

theorem r_poly_norm_eq_cost (sb A : Nat) (hA : 100 ≤ A) (np na : BitVec 32) :
    FnCost (State := State) prog "r_poly_norm_eq" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow 26000) 0 noSlack) := by
  apply FnCost.intro (fn := rPolyNormEq) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body rPolyNormEq
  wpc_auto
  wpc_done

fncost_register "r_poly_norm_eq" rPolyNormEq r_poly_norm_eq_cost

theorem bb_ite_cost (sb A : Nat) (c t e b : BitVec 32) :
    FnCost (State := State) prog "bb_ite" (BudPre sb [.ptr sb 0, .u32 c, .u32 t, .u32 e, .u32 b])
      (Amort sb A (allow (60 * 255 + 30)) 0 noSlack) := by
  apply FnCost.intro (fn := bbIte) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body bbIte
  apply WPC.seq
  refine WPC.assign_band (by rfl) ?_
  intro n hn
  wpc_simp
  have hn' : n.toNat ≤ 255 := by simpa using hn
  apply WPC.seq
  refine WPC.assign_band (by rfl) ?_
  intro nt _
  wpc_simp
  apply WPC.seq
  refine WPC.assign_band (by rfl) ?_
  intro ne _
  wpc_simp
  apply WPC.seq
  apply WPC.while
    (I := fun env' st' k => ∃ i ok : BitVec 32,
      env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("c", .u32, .u32 c), ("t", .u32, .u32 t),
        ("e", .u32, .u32 e), ("b", .u32, .u32 b), ("n", .u32, .u32 n), ("nt", .u32, .u32 nt),
        ("ne", .u32, .u32 ne), ("i", .u32, .u32 i), ("ok", .u32, .u32 ok)] ∧
      i.toNat ≤ n.toNat ∧ ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
      k.t + A * w'.toNat ≤ A * w0.toNat + 60 * i.toNat ∧ k.m + mm'.toNat ≤ mm.toNat)
    (μ := fun env' _ => n.toNat - envU32 env' "i")
  · exact ⟨0#32, 0#32, rfl, by simp, w0, mm, hb, by simp, by simp⟩
  rintro env' st' k ⟨i, ok, rfl, hin, w', mm', hb', hk, hkm⟩
  embc_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · wpc_auto
    wpc_done
  have hlt' : i.toNat < n.toNat := by simpa [BitVec.lt_def] using hlt
  have hi1 : (i + 1#32).toNat = i.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
  wpc_auto
  wpc_done
  all_goals mid_next hi1

fncost_register "bb_ite" bbIte bb_ite_cost

/-! ## `aci_flat` -/

/-- `aci_flat`'s arguments (all words). -/
def rl_FlatArgs (sb : Nat) (vs : List Val) : Prop :=
  ∃ (rop i d : BitVec 32), vs = [.ptr sb 0, .u32 rop, .u32 i, .u32 d]

theorem rl_aci_flat_cost (sb A : Nat) (hA : 150 ≤ A) :
    FnCost (State := State) prog "aci_flat"
      (fun vs st => rl_FlatArgs sb vs ∧ ∃ w mm : BitVec 32, Budget st.mem sb w mm)
      (Amort sb A (allowFail 0#32 200 20) 0 (slackUnless 0#32 35)) := by
  apply FnCost.rec (fun vs _ => depthArg vs)
  intro m IH
  apply FnCost.intro (fn := aciFlat) rfl
  rintro vs st ⟨⟨⟨rop, i, d, rfl⟩, w, mm, hb⟩, hm⟩
  simp only [depthArg] at hm
  have hA6 : 6 ≤ A := by omega
  fncost_body aciFlat
  -- if (depth == 0) return 0;
  apply WPC.seq
  apply WPC.ite
  embc_simp
  constructor
  · intro hd
    wpc_auto
    wpc_done
  intro hd
  apply WPC.skip
  wpc_simp
  -- r = tick(st); if (r == 0) return 0;
  apply WPC.seq
  wpc_step
  apply WPC.seq
  wpc_ite_case
  · wpc_auto
    wpc_done
  apply WPC.skip
  wpc_simp
  -- r = aci_same(rop, st->pool[i]);
  apply WPC.seq
  wpc_step
  apply WPC.seq
  apply WPC.ite_any
  · -- the children
    apply WPC.seq
    refine WPC.assign_band (by rfl) ?_
    intro n hn
    wpc_simp
    have hn' : n.toNat ≤ 255 := by simpa using hn
    name_bud st2 w2 mm2 hb2
    apply WPC.seq
    apply WPC.while
      (I := fun env' st' k => ∃ (kk r' : BitVec 32),
        env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("rop", .u32, .u32 rop), ("i", .u32, .u32 i),
          ("depth", .u32, .u32 d), ("r", .u32, .u32 r'), ("n", .u32, .u32 n), ("k", .u32, .u32 kk)] ∧
        kk.toNat ≤ n.toNat ∧ ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
        k.t + A * w'.toNat ≤ A * w2.toNat ∧ k.m + mm'.toNat ≤ mm2.toNat)
      (μ := fun env' _ => n.toNat - envU32 env' "k")
    · exact ⟨0#32, _, rfl, by simp, w2, mm2, hb2, by simp, by simp⟩
    rintro env' st' k ⟨kk, r', rfl, hkn, w', mm', hb', hk, hkm⟩
    embc_simp
    refine ⟨fun hge => ?_, fun hlt => ?_⟩
    · wpc_auto
      wpc_done
    have hlt' : kk.toNat < n.toNat := by simpa [BitVec.lt_def] using hlt
    have hk1 : (kk + 1#32).toNat = kk.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    -- r = aci_flat(st, rop, st->pool[i + 1 + k], depth - 1);
    apply WPC.seq
    have hbc := hb'
    refine WPC.call_shape (fn := aciFlat) (hf := rfl) (hps := rfl) ?_
    intro vs1 hargs hbp
    obtain ⟨v0, vs2, h0, hargs1, rfl⟩ := evalArgs_cons' hargs
    simp only [evalE, Env.get, ↓reduceIte, Option.some.injEq] at h0
    subst h0
    obtain ⟨v1, vs3, e1, -, hbp1⟩ := bindParams_ne_none_cons hbp
    simp only [List.cons.injEq] at e1
    obtain ⟨rfl, rfl⟩ := e1
    obtain ⟨v2, vs4, rfl, ht2, hbp2⟩ := bindParams_ne_none_cons hbp1
    obtain ⟨rop', rfl⟩ := Mem.hasTy_u32_inv ht2
    obtain ⟨v3, vs5, rfl, ht3, hbp3⟩ := bindParams_ne_none_cons hbp2
    obtain ⟨x', rfl⟩ := Mem.hasTy_u32_inv ht3
    obtain ⟨v4, vs6, rfl, ht4, hbp4⟩ := bindParams_ne_none_cons hbp3
    obtain ⟨d', rfl⟩ := Mem.hasTy_u32_inv ht4
    obtain rfl := bindParams_ne_none_nil hbp4
    obtain ⟨a1, t1, -, hv1, he1⟩ := evalArgs_cons' hargs1
    obtain ⟨a2, t2, -, hv2, he2⟩ := evalArgs_cons' hv1
    obtain ⟨a3, t3, h3, hv3, he3⟩ := evalArgs_cons' hv2
    simp [evalArgs] at hv3
    subst hv3
    simp only [List.cons.injEq] at he1 he2 he3
    obtain ⟨-, rfl⟩ := he1
    obtain ⟨-, rfl⟩ := he2
    obtain ⟨rfl, -⟩ := he3
    simp [evalE, evalBin, evalArith, Env.get] at h3
    have hd0 : d.toNat ≠ 0 := fun e => hd (BitVec.eq_of_toNat_eq (by simpa using e))
    have hd1 : (d - 1#32).toNat < d.toNat := by rw [BitVec.toNat_sub]; simp; omega
    subst h3
    refine ⟨_, _, IH, ⟨⟨⟨rop', x', d - 1#32, rfl⟩, w', mm', hbc⟩, by simp [depthArg]; omega⟩, ?_⟩
    rintro rv st3 c3 ⟨w3, mm3, hb3, hc3, hm3⟩
    rw [hbc.wk] at hc3
    rw [hbc.mk] at hm3
    split
    · trivial
    rename_i env3 hasg3
    obtain ⟨r3, rfl, rfl⟩ := assignDst_u32' hasg3 rfl
    wpc_simp
    -- if (r == 0) return 0;
    apply WPC.seq
    apply WPC.ite
    embc_simp
    constructor
    · intro hr3
      subst hr3
      wpc_auto
      rl_done
    intro hr3
    simp only [allowFail_apply, slackUnless_apply, Option.some.injEq, Val.u32.injEq, hr3, ↓reduceIte] at hc3
    apply WPC.skip
    wpc_simp
    wpc_auto
    mid_next hk1
  · apply WPC.skip
    wpc_simp
    -- r = aci_nil(st, rop, i); if (r != 0) return 1; r = push(st, i); return r;
    apply WPC.seq
    wpc_step
    apply WPC.seq
    apply WPC.ite_any
    · wpc_auto
      wpc_done
    apply WPC.skip
    wpc_simp
    apply WPC.seq
    wpc_step
    apply WPC.ret_val
    intro v hv
    simp only [evalE, Env.get, String.reduceEq, ↓reduceIte, Option.some.injEq] at hv
    subst hv
    rl_done

theorem aci_flat_cost (sb A : Nat) (hA : 150 ≤ A) (rop i d : BitVec 32) :
    FnCost (State := State) prog "aci_flat" (BudPre sb [.ptr sb 0, .u32 rop, .u32 i, .u32 d])
      (Amort sb A (allowFail 0#32 200 20) 0 (slackUnless 0#32 35)) :=
  FnCost.mono (rl_aci_flat_cost sb A hA) (fun _ _ ⟨h, hb⟩ => ⟨⟨rop, i, d, h⟩, hb⟩)
    (fun _ _ _ _ _ _ h => h)

fncost_register "aci_flat" aciFlat aci_flat_cost

/-! ## `aci_nf`, `r_aci_norm` -/

/-- The struct has a cell 11 (`sp`) when it has its budget cells. -/
theorem rl_fld11 {m : Mem} {sb : Nat} {w mm : BitVec 32} (hb : Budget m sb w mm) :
    ∃ v, Fld m sb 11 v := by
  obtain ⟨cells, hblk, hc⟩ := hb.1
  have h20 : 20 < cells.size := by
    rcases Nat.lt_or_ge 20 cells.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at hc; simp at hc
  exact ⟨cells[11]'(by omega), cells, hblk, Array.getElem?_eq_getElem _⟩

/-- `st->sp` is a word, or reading it as one fails. -/
theorem rl_sp_or {m : Mem} {sb : Nat} {w mm : BitVec 32} (hb : Budget m sb w mm) :
    (∃ sp : BitVec 32, Fld m sb 11 (.u32 sp)) ∨
      ∀ v, m.loadField prog sb "sp" = some v → ∀ sp : BitVec 32, v ≠ .u32 sp := by
  obtain ⟨v, hv⟩ := rl_fld11 hb
  cases v with
  | u32 sp => exact Or.inl ⟨sp, hv⟩
  | undef => exact Or.inr (fun v' h => by rw [Fld.load_undef hv fi_sp] at h; simp at h)
  | u64 x => exact Or.inr (fun v' h => by rw [hv.load fi_sp (by simp)] at h; cases h; simp)
  | ptr b o => exact Or.inr (fun v' h => by rw [hv.load fi_sp (by simp)] at h; cases h; simp)
  | null => exact Or.inr (fun v' h => by rw [hv.load fi_sp (by simp)] at h; cases h; simp)
  | uptr => exact Or.inr (fun v' h => by rw [hv.load fi_sp (by simp)] at h; cases h; simp)

theorem rl_spend_sp (sb A : Nat) (hA : 6 ≤ A) (k sp : BitVec 32) :
    FnCost (State := State) prog "spend"
      (fun vs st => BudPre sb [.ptr sb 0, .u32 k] vs st ∧ Fld st.mem sb 11 (.u32 sp))
      (fun vs st rv st' c => Amort sb A (allow 8) 0 (slackUnless 0#32 (A * k.toNat)) vs st rv st' c ∧
        Fld st'.mem sb 11 (.u32 sp)) :=
  rl_frame_cost fi_sp rl_frame_spend (by decide) (spend_cost sb A hA k)

theorem rl_frame_aci_sort : rl_FrameOK "sp" ["aci_sort"] := by
  intro g hg
  simp only [List.contains_cons, List.contains_nil, Bool.or_false, beq_iff_eq] at hg
  subst hg
  exact ⟨_, rfl, by decide⟩

theorem rl_aci_sort_sp (sb A : Nat) (base n sp : BitVec 32) :
    FnCost (State := State) prog "aci_sort"
      (fun vs st => (BudPre sb [.ptr sb 0, .u32 base] vs st ∧ SpPre sb base n st.mem ∧
        base.toNat < 4294967295) ∧ Fld st.mem sb 11 (.u32 sp))
      (fun vs st rv st' c => Amort sb A (allow ((8 * n.toNat + 20) * n.toNat + 20)) 0 noSlack vs st rv st' c ∧
        Fld st'.mem sb 11 (.u32 sp)) :=
  rl_frame_cost fi_sp rl_frame_aci_sort (by decide) (aci_sort_cost sb A base n)

/-- The value of `n * (n - 1) / 2` for `n ≤ 1024`. -/
theorem rl_tri_toNat {n : BitVec 32} (hn : n.toNat ≤ 1024) :
    (n * (n - 1#32) / 2#32).toNat = n.toNat * (n.toNat - 1) / 2 := by
  rcases Nat.eq_zero_or_pos n.toNat with h0 | hpos
  · have : n = 0#32 := BitVec.eq_of_toNat_eq (by simpa using h0)
    subst this; simp
  · have h1 : (n - 1#32).toNat = n.toNat - 1 := by rw [BitVec.toNat_sub]; simp; omega
    have hle : n.toNat * (n.toNat - 1) ≤ 1024 * 1024 := Nat.mul_le_mul hn (by omega)
    rw [BitVec.toNat_udiv, BitVec.toNat_mul, h1]
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]

/-- `aci_sort` and `aci_uniq` on `n ≤ 1024` words are paid by `spend(n (n - 1) / 2)`. -/
theorem rl_sort_paid {A n : Nat} (hA : 100 ≤ A) :
    (8 * n + 20) * n + 20 + (10 * n + 20) ≤ A * (n * (n - 1) / 2) + 100 := by
  have h2 : n * (n - 1) ≤ 2 * (n * (n - 1) / 2) + 1 := by omega
  have hA' : 100 * (n * (n - 1) / 2) ≤ A * (n * (n - 1) / 2) := Nat.mul_le_mul_right _ hA
  have hsq : (8 * n + 20) * n = 8 * (n * n) + 20 * n := by
    rw [Nat.add_mul, Nat.mul_assoc]
  have hsub : n * (n - 1) = n * n - n := by rw [Nat.mul_sub_one]
  rcases Nat.lt_or_ge n 2 with h | h
  · have : n * n ≤ 1 := by
      rcases Nat.lt_or_ge n 1 with h' | h'
      · have : n = 0 := by omega
        subst this; simp
      · have : n = 1 := by omega
        subst this; simp
    omega
  · have : 2 * n ≤ n * n := Nat.mul_le_mul_right n h
    omega

theorem aci_nf_cost (sb A : Nat) (hA : 150 ≤ A) (i : BitVec 32) :
    FnCost (State := State) prog "aci_nf" (BudPre sb [.ptr sb 0, .u32 i])
      (Amort sb A (allowFail 0xffffffff#32 600 300) 0 noSlack) := by
  apply FnCost.intro (fn := aciNf) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body aciNf
  have hA6 : 6 ≤ A := by omega
  have hA100 : 100 ≤ A := by omega
  -- hdr = st->pool[i]; r = aci_assoc(hdr); if (r == 0) return 0; base = st->sp;
  apply WPC.seq; wpc_step
  apply WPC.seq; wpc_step
  apply WPC.seq; apply WPC.ite_any
  · wpc_auto; rl_done
  apply WPC.skip; wpc_simp
  apply WPC.seq; wpc_step
  -- r = aci_flat(st, hdr & ACI_OPMASK, i, MAX_DEPTH); if (r == 0) return NOID;
  apply WPC.seq; wpc_step
  apply WPC.seq; rl_ite_case
  · wpc_auto; rl_done
  apply WPC.skip; wpc_simp
  -- code = hdr & 0xff; if (code == BV_CONCAT) return 1;
  apply WPC.seq; wpc_step
  apply WPC.seq; apply WPC.ite_any
  · wpc_auto; rl_done
  apply WPC.skip; wpc_simp
  -- n = st->sp - base;
  name_bud st2 w2 mm2 hb2
  cost_clean
  rcases rl_sp_or hb2 with ⟨sp, hsp⟩ | hbad
  rotate_left
  · apply WPC.seq; apply WPC.assign
    simp only [evalE, Env.get, String.reduceEq, ↓reduceIte]
    cases hl : st2.mem.loadField prog sb "sp" with
    | none => simp
    | some v =>
      have := hbad v hl
      cases v <;> simp_all [evalBin]
  have hspl := hsp.load fi_sp (by simp)
  apply WPC.seq; apply WPC.assign
  simp only [evalE, Env.get, String.reduceEq, ↓reduceIte, hspl, evalBin, evalArith, Env.assign, Env.ty,
    Mem.hasTy_u32]
  wpc_simp
  rl_name "base" => base
  rl_name "r" => r1
  -- if (n > MAX_SORT) ...; if (base > MAX_POOL) ...; if (st->sp < base) ...
  apply WPC.seq; apply WPC.ite; embc_simp; constructor
  · intro _; wpc_auto; rl_done
  intro hn
  have hn' : (sp - base).toNat ≤ 1024 := by
    have := BitVec.le_def.mp hn; simpa using this
  apply WPC.skip; wpc_simp
  apply WPC.seq; apply WPC.ite; embc_simp; constructor
  · intro _; wpc_auto; rl_done
  intro hbase
  have hbase' : base.toNat ≤ 1073741824 := by
    have := BitVec.le_def.mp hbase; simpa using this
  apply WPC.skip; wpc_simp
  apply WPC.seq; apply WPC.ite; embc_simp [hspl]; constructor
  · intro _; wpc_auto; rl_done
  intro hge
  have hge' : base ≤ sp := by simpa using hge
  have hsub := bv_sub_toNat_of_le hge'
  have hge'' : base.toNat ≤ sp.toNat := BitVec.le_def.mp hge'
  apply WPC.skip; wpc_simp
  -- r = spend(st, n * (n - 1) / 2);
  apply WPC.seq
  have hbc := hb2
  apply WPC.call_shape (fn := spend) (hf := spend_find) (hps := spend_params)
  intro vs1 hargs _
  simp [evalArgs, evalE, Env.get, evalBin, evalArith] at hargs
  subst hargs
  refine ⟨_, _, rl_spend_sp sb A hA6 _ sp, ⟨⟨rfl, _, _, hbc⟩, hsp⟩, ?_⟩
  rintro rv st3 c3 ⟨⟨w3, mm3, hb3, ht3, hm3⟩, hsp3⟩
  rw [hbc.wk] at ht3
  rw [hbc.mk] at hm3
  wpc_dst
  -- if (r == 0) return NOID;
  apply WPC.seq; rl_ite_case
  · wpc_auto; rl_done
  apply WPC.skip; wpc_simp
  -- aci_sort(st, base);
  have hsp3' : SpPre sb base (sp - base) st3.mem := ⟨sp, hsp3, by omega⟩
  have hbase2 : base.toNat < 4294967295 := by omega
  apply WPC.seq
  apply WPC.call_shape (fn := aciSort) (hf := aciSort_find) (hps := aciSort_params)
  intro vs1 hargs _
  simp [evalArgs, evalE, Env.get] at hargs
  subst hargs
  refine ⟨_, _, rl_aci_sort_sp sb A base (sp - base) sp, ⟨⟨⟨rfl, _, _, hb3⟩, hsp3', hbase2⟩, hsp3⟩, ?_⟩
  rintro rv st4 c4 ⟨⟨w4, mm4, hb4, ht4, hm4⟩, hsp4⟩
  rw [hb3.wk] at ht4
  rw [hb3.mk] at hm4
  wpc_dst
  have hpaid := rl_sort_paid (n := (sp - base).toNat) hA100
  rw [rl_tri_toNat hn'] at ht3
  -- if (code != BV_XOR) { aci_uniq(st, base); } return 1;
  apply WPC.seq; apply WPC.ite_any
  · have hsp4' : SpPre sb base (sp - base) st4.mem := ⟨sp, hsp4, by omega⟩
    apply WPC.call_shape (fn := aciUniq) (hf := aciUniq_find) (hps := aciUniq_params)
    intro vs1 hargs _
    simp [evalArgs, evalE, Env.get] at hargs
    subst hargs
    refine ⟨_, _, aci_uniq_cost sb A base (sp - base), ⟨⟨rfl, _, _, hb4⟩, hsp4'⟩, ?_⟩
    rintro rv st5 c5 ⟨w5, mm5, hb5, ht5, hm5⟩
    rw [hb4.wk] at ht5
    rw [hb4.mk] at hm5
    wpc_dst
    wpc_auto
    rl_done
  apply WPC.skip; wpc_simp
  wpc_auto
  rl_done

fncost_register "aci_nf" aciNf aci_nf_cost

theorem r_aci_norm_cost (sb A : Nat) (hA : 150 ≤ A) (np na : BitVec 32) :
    FnCost (State := State) prog "r_aci_norm" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow 3000) 0 noSlack) := by
  apply FnCost.intro (fn := rAciNorm) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body rAciNorm
  have hA6 : 6 ≤ A := by omega
  apply WPC.seq; apply WPC.ite_any
  · wpc_auto; rl_done
  apply WPC.skip; wpc_simp
  apply WPC.seq; wpc_step
  iterate 2
    apply WPC.seq; apply WPC.ite_any
    · wpc_auto; rl_done
    apply WPC.skip; wpc_simp
  apply WPC.seq; wpc_step
  apply WPC.seq; wpc_step
  apply WPC.seq; apply WPC.ite_any
  · wpc_auto; rl_done
  apply WPC.skip; wpc_simp
  -- ba = st->sp; ra = aci_nf(st, a); if (ra == NOID) return NOID;
  apply WPC.seq; wpc_step
  apply WPC.seq; wpc_step
  apply WPC.seq; rl_ite_case
  · wpc_auto; rl_done
  apply WPC.skip; wpc_simp
  -- la = st->sp - ba; r = spend(st, la); if (r == 0) return NOID;  (pays the comparison)
  apply WPC.seq; wpc_step
  rl_name "la" => la
  have hpay : 10 * la.toNat ≤ A * la.toNat := Nat.mul_le_mul_right _ (by omega)
  apply WPC.seq; wpc_step
  apply WPC.seq; rl_ite_case
  · wpc_auto; rl_done
  apply WPC.skip; wpc_simp
  wpc_auto
  rl_done
  -- the comparison: at most `la` steps, paid by the spend of `la`
  all_goals
    name_bud st1 w1 mm1 hb1
    cost_clean
    rl_name "e" => e
    rl_name "a" => a
    rl_name "b" => b
    rl_name "ra" => ra
    rl_name "rb" => rb
    rl_name "ba" => ba
    rl_name "bb" => bb
    rl_name "lb" => lb
    rl_name "r" => r
    apply WPC.while
      (I := fun env' st' k => st' = st1 ∧ ∃ i : BitVec 32,
        env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("np", .u32, .u32 np), ("na", .u32, .u32 na),
          ("e", .u32, .u32 e), ("a", .u32, .u32 a), ("b", .u32, .u32 b), ("ra", .u32, .u32 ra),
          ("rb", .u32, .u32 rb), ("ba", .u32, .u32 ba), ("bb", .u32, .u32 bb), ("la", .u32, .u32 la),
          ("lb", .u32, .u32 lb), ("i", .u32, .u32 i), ("r", .u32, .u32 r)] ∧
        i.toNat ≤ la.toNat ∧ k.t ≤ 6 * i.toNat ∧ k.m = 0)
      (μ := fun env' _ => la.toNat - envU32 env' "i")
    · exact ⟨rfl, 0#32, rfl, by simp, by simp, by simp⟩
    rintro env' st' k ⟨hst, i, rfl, hin, hk, hkm⟩
    subst hst
    split
    · rename_i v hv
      constructor
      · intro _
        wpc_auto
        rl_done
      · intro hv0
        obtain ⟨x0, hx0, hx0ne⟩ := rl_land_fst hv hv0
        have hil : i.toNat < la.toNat := by
          simp only [evalE, Env.get, String.reduceEq, ↓reduceIte, evalBin, evalArith, Val.ofBool,
            Option.some.injEq, Val.u32.injEq] at hx0
          rcases Nat.lt_or_ge i.toNat la.toNat with hc | hc
          · exact hc
          exfalso
          have : ¬ i < la := by rw [BitVec.lt_def]; omega
          simp [this] at hx0
          exact hx0ne hx0.symm
        have hi1 : (i + 1#32).toNat = i.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
        apply WPC.assign
        simp only [evalE, Env.get, String.reduceEq, ↓reduceIte, evalBin, evalArith, Env.assign, Env.ty,
          Mem.hasTy_u32]
        refine ⟨?_, trivial, i + 1#32, by simp [Env.set], by omega, ?_, ?_⟩
        · simp only [envU32, Env.get, Env.set, String.reduceEq, ↓reduceIte, hi1]; omega
        · cost_arith
        · cost_arith
    · trivial

fncost_register "r_aci_norm" rAciNorm r_aci_norm_cost

/-! ## Joins -/

/-- `if (c) { x = e1; y = e2; } else { x = e3; y = e4; } b`: one continuation. -/
theorem rl_ite_assign2_join {P : Prog} {Q : (CPost P State)} {env : Env} {st : (KernelState P State)} {c e1 e2 e3 e4 : Expr}
    {x y : Var} {b : Stmt} (hx : env.ty x = some .u32) (hy : ∀ v, (env.set x (.u32 v)).ty y = some .u32)
    (hb : ∀ p0 p1 : BitVec 32, WPC P b (Q.shift ⟨7, 0⟩) ((env.set x (.u32 p0)).set y (.u32 p1)) st) :
    WPC P (.seq (.ite c (.seq (.assign x e1) (.assign y e2)) (.seq (.assign x e3) (.assign y e4))) b)
      Q env st := by
  apply WPC.seq
  apply WPC.mono (Q := fun o env' st' k => o = .normal ∧ st' = st ∧ k = ⟨5, 0⟩ ∧
    ∃ p0 p1, env' = (env.set x (.u32 p0)).set y (.u32 p1))
  · apply WPC.ite_any
    · apply WPC.seq
      apply WPC.assign_u32 hx
      intro n
      apply WPC.assign_u32 (hy n)
      intro n2
      exact ⟨rfl, rfl, Cost.ext (by cost_simp) (by cost_simp), n, n2, rfl⟩
    · apply WPC.seq
      apply WPC.assign_u32 hx
      intro n
      apply WPC.assign_u32 (hy n)
      intro n2
      exact ⟨rfl, rfl, Cost.ext (by cost_simp) (by cost_simp), n, n2, rfl⟩
  · rintro o env' st' k ⟨rfl, rfl, rfl, p0, p1, rfl⟩
    apply WPC.mono (hb p0 p1)
    intro o e s c h
    exact CPost.cost_eq h (by cost_simp; try omega) (by cost_simp; try omega)

/-- `if (c) { … } b` where the branch may return, and otherwise only changes the word
local `x`, at most `K` more time paid: the two ways join before `b`. -/
theorem rl_ite_join {Q : (CPost prog State)} {env : Env} {st : (KernelState prog State)} {sb A K : Nat} {w mm : BitVec 32}
    {c : Expr} {a b : Stmt} (x : Var) (hbud : Budget st.mem sb w mm) (hskip : ∃ v, env = env.set x (.u32 v))
    (ha : WPC prog a (fun o env' st' k => match o with
      | .normal => ∃ v, env' = env.set x (.u32 v) ∧ ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
          k.t + A * w'.toNat ≤ A * w.toNat + K ∧ k.m + mm'.toNat ≤ mm.toNat
      | .brk => Q .brk env' st' (1 + k + 2)
      | .ret rv => Q (.ret rv) env' st' (1 + k + 1)) env st)
    (hb : ∀ (v : BitVec 32) (st' : (KernelState prog State)) (k : Cost) (w' mm' : BitVec 32), Budget st'.mem sb w' mm' →
      k.t + A * w'.toNat ≤ A * w.toNat + K + 2 → k.m + mm'.toNat ≤ mm.toNat →
      WPC prog b (Q.shift (k + 2)) (env.set x (.u32 v)) st') :
    WPC prog (.seq (.ite c a .skip) b) Q env st := by
  apply WPC.seq
  apply WPC.mono (Q := fun o env' st' k => match o with
    | .normal => ∃ v, env' = env.set x (.u32 v) ∧ ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
        k.t + A * w'.toNat ≤ A * w.toNat + K + 2 ∧ k.m + mm'.toNat ≤ mm.toNat
    | .brk => Q .brk env' st' (k + 2)
    | .ret rv => Q (.ret rv) env' st' (k + 1))
  · apply WPC.ite_any
    · apply WPC.mono ha
      intro o env' st' k h
      cases o with
      | normal =>
        obtain ⟨v, rfl, w', mm', hb', hk, hkm⟩ := h
        exact ⟨v, rfl, w', mm', hb', by simp; omega, by simp; omega⟩
      | brk => simpa using h
      | ret r => simpa using h
    · apply WPC.skip
      obtain ⟨v, hv⟩ := hskip
      exact ⟨v, hv, w, mm, hbud, by simp; omega, by simp⟩
  · intro o env' st' k h
    cases o with
    | normal =>
      obtain ⟨v, rfl, w', mm', hb', hk, hkm⟩ := h
      exact hb v st' k w' mm' hb' hk hkm
    | brk => exact h
    | ret r => exact h

/-- `a; b` where `a` may return and otherwise ends in an environment related to the
current one by `E` (some locals changed), at most `K` more time paid: one continuation. -/
theorem rl_join {Q : (CPost prog State)} {env : Env} {st : (KernelState prog State)} {sb A K : Nat} {w mm : BitVec 32}
    {a b : Stmt} (E : Env → Env → Prop) (hbud : Budget st.mem sb w mm)
    (ha : WPC prog a (fun o env' st' k => match o with
      | .normal => E env env' ∧ ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
          k.t + A * w'.toNat ≤ A * w.toNat + K ∧ k.m + mm'.toNat ≤ mm.toNat
      | .brk => Q .brk env' st' (k + 2)
      | .ret rv => Q (.ret rv) env' st' (k + 1)) env st)
    (hb : ∀ (env' : Env) (st' : (KernelState prog State)) (k : Cost) (w' mm' : BitVec 32), E env env' →
      Budget st'.mem sb w' mm' → k.t + A * w'.toNat ≤ A * w.toNat + K → k.m + mm'.toNat ≤ mm.toNat →
      WPC prog b (Q.shift (k + 2)) env' st') :
    WPC prog (.seq a b) Q env st := by
  have _ := hbud
  apply WPC.seq
  apply WPC.mono ha
  intro o env' st' k h
  cases o with
  | normal =>
    obtain ⟨he, w', mm', hb', hk, hkm⟩ := h
    exact hb env' st' k w' mm' he hb' hk hkm
  | brk => exact h
  | ret r => exact h

/-! ## `r_resolution`, `r_factoring`: stack lengths read from `st->sp` -/

/-- `cl_erase(st, base, pivot)` for any `sp`: when `sp < base` the search stops at once
and the shift runs only if `base + 1` wraps, at most `sp + 1 = (sp - base) mod 2^32`
times; so its cost is linear in `(sp - base).toNat` whatever the order. -/
theorem rl_cl_erase_cost (sb A : Nat) (base pivot sp : BitVec 32) :
    FnCost (State := State) prog "cl_erase"
      (fun vs st => BudPre sb [.ptr sb 0, .u32 base, .u32 pivot] vs st ∧ Fld st.mem sb 11 (.u32 sp))
      (Amort sb A (allow (10 * (sp - base).toNat + 20)) 0 noSlack) := by
  by_cases hle : base ≤ sp
  · refine FnCost.mono (cl_erase_cost sb A base pivot (sp - base)) ?_ (fun _ _ _ _ _ _ h => h)
    rintro vs st ⟨h1, h2⟩
    exact ⟨h1, sp, h2, by rw [bv_sub_toNat_of_le hle]; have := BitVec.le_def.mp hle; omega⟩
  apply FnCost.intro (fn := clErase) rfl
  rintro vs st ⟨⟨rfl, w, mm, hb⟩, hsp⟩
  fncost_body clErase
  have hspl := hsp.load fi_sp (by simp)
  have hlt : sp.toNat < base.toNat := by have := BitVec.not_le.mp hle; exact BitVec.lt_def.mp this
  have hnlt : ¬ base < sp := fun h => by have := BitVec.lt_def.mp h; omega
  have hne : ¬ base = sp := fun h => by subst h; omega
  have hk : (sp - base).toNat = sp.toNat + 4294967296 - base.toNat := by
    rw [BitVec.toNat_sub]; omega
  apply WPC.seq; wpc_step
  -- the search: `base < sp` is false, it stops at once
  apply WPC.seq
  apply WPC.while (I := fun env' st' k => st' = st ∧ env' = [("st", .ptr (.struct "ck"), .ptr sb 0),
      ("base", .u32, .u32 base), ("pivot", .u32, .u32 pivot), ("i", .u32, .u32 base)] ∧ k = 0)
    (μ := fun _ _ => 0)
  · exact ⟨rfl, rfl, rfl⟩
  rintro env' st' k ⟨rfl, rfl, rfl⟩
  embc_simp [hspl, hnlt]
  -- if (i == st->sp) return;  (it is not)
  apply WPC.seq
  apply WPC.ite
  embc_simp [hspl, hne]
  apply WPC.skip
  wpc_simp
  -- the shift: runs only after `i + 1` wraps
  apply WPC.seq
  apply WPC.while
    (I := fun env2 st2 k2 => ∃ c : Nat, env2 = [("st", .ptr (.struct "ck"), .ptr sb 0),
        ("base", .u32, .u32 base), ("pivot", .u32, .u32 pivot), ("i", .u32, .u32 (base + BitVec.ofNat 32 c))] ∧
      Budget st2.mem sb w mm ∧ Fld st2.mem sb 11 (.u32 sp) ∧ c ≤ (sp - base).toNat ∧
      k2.t ≤ 6 * c ∧ k2.m = 0)
    (μ := fun env2 _ => (sp - base).toNat + 1 - (envU32 env2 "i" + 4294967296 - base.toNat) % 4294967296)
  · exact ⟨0, by simp, hb, hsp, by omega, by simp, by simp⟩
  rintro env2 st2 k2 ⟨c, rfl, hb2, hsp2, hck, hk2, hkm2⟩
  have hspl2 := hsp2.load fi_sp (by simp)
  have hc32 : c < 4294967296 := by have := (sp - base).isLt; omega
  have hic : (base + BitVec.ofNat 32 c).toNat = (base.toNat + c) % 4294967296 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  embc_simp [hspl2]
  refine ⟨fun hge => ?_, fun hlt2 => ?_⟩
  · apply WPC.setField_bud hb2 (by decide) (by decide)
    intro m' hb3
    simp only [retPostC, CPost.shift_apply, Amort, allow_apply, noSlack_apply]
    refine ⟨w, mm, hb3, ?_, ?_⟩
    · rw [hwk]; simp only [Cost.add_t, Cost.one_t, reduceCostT]; omega
    · rw [hmk]; simp only [Cost.add_m, Cost.one_m, reduceCostM]; omega
  have hlt3 : (base + BitVec.ofNat 32 c + 1#32).toNat < sp.toNat := BitVec.lt_def.mp hlt2
  have hi1 : (base + BitVec.ofNat 32 c + 1#32).toNat = (base.toNat + c + 1) % 4294967296 := by
    rw [BitVec.toNat_add, hic]; simp <;> omega
  have hc1 : c + 1 ≤ (sp - base).toNat := by omega
  apply WPC.seq
  apply WPC.store_bud_fld hb2 hsp2
  intro m' hb3 hsp3
  wpc_simp
  apply WPC.assign
  embc_simp
  have he : base + BitVec.ofNat 32 c + 1#32 = base + BitVec.ofNat 32 (c + 1) := by
    apply BitVec.eq_of_toNat_eq; rw [hi1, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [he]
  have hic1 : (base + BitVec.ofNat 32 (c + 1)).toNat = (base.toNat + c + 1) % 4294967296 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  simp only [envU32, Env.get, String.reduceEq, ↓reduceIte, hic, hic1]
  refine ⟨by omega, c + 1, rfl, hb3, hsp3, hc1, ?_, ?_⟩
  · omega
  · omega

/-- `rl_cl_erase_cost` with the allowance at rate `A` (so a `spend` of the same length pays it). -/
theorem rl_cl_erase_costA (sb A : Nat) (hA : 10 ≤ A) (base pivot sp : BitVec 32) :
    FnCost (State := State) prog "cl_erase"
      (fun vs st => BudPre sb [.ptr sb 0, .u32 base, .u32 pivot] vs st ∧ Fld st.mem sb 11 (.u32 sp))
      (Amort sb A (allow (A * (sp - base).toNat + 20)) 0 noSlack) :=
  FnCost.mono (rl_cl_erase_cost sb A base pivot sp) (fun _ _ h => h)
    (fun _ _ _ _ _ _ h => Amort.mono h (by
      simp only [allow_apply]; have := Nat.mul_le_mul_right (sp - base).toNat hA; omega) (Nat.le_refl _)
      (Nat.le_refl _))

/-- `evalBin` of a non-word `st->sp` against a word, other than `==`/`!=`: no value. -/
theorem rl_evalBin_bad {m : Mem} (v : Val) (hv : ∀ sp : BitVec 32, v ≠ .u32 sp) (op : BinOp)
    (hop : op ≠ .eq ∧ op ≠ .ne) (x : BitVec 32) : evalBin m op v (.u32 x) = none := by
  cases v <;> cases op <;> simp_all [evalBin]

/-- `if (st->sp < x || …) …` when `st->sp` is not a word: the condition does not evaluate. -/
theorem rl_guard_bad {Q : (CPost prog State)} {env : Env} {st : (KernelState prog State)} {sb : Nat} {X : Var} {x : BitVec 32}
    {E2 : Expr} {a b : Stmt}
    (hbad : ∀ v, st.mem.loadField prog sb "sp" = some v → ∀ sp : BitVec 32, v ≠ .u32 sp)
    (hst : env.get "st" = some (.ptr sb 0)) (hX : env.get X = some (.u32 x)) :
    WPC prog (.ite (.lor (.bin .lt (.field (.var "st") "sp") (.var X)) E2) a b) Q env st := by
  apply WPC.ite
  simp only [evalE, hst, hX, ↓reduceIte]
  cases hl : st.mem.loadField prog sb "sp" with
  | none => simp
  | some v => simp [rl_evalBin_bad v (hbad v hl) .lt (by decide) x]

theorem rl_sub_sp_none {m : Mem} {sb : Nat}
    (hbad : ∀ v, m.loadField prog sb "sp" = some v → ∀ sp : BitVec 32, v ≠ .u32 sp) (x : BitVec 32)
    (v : Val) (hv : m.loadField prog sb "sp" = some v) : evalBin m .sub v (.u32 x) = none := by
  have := hbad v hv
  cases v <;> simp_all [evalBin]

/-- `ok = spend(st, st->sp - x); …` when `st->sp` is not a word: the argument does not evaluate. -/
theorem rl_spend_bad {Q : (CPost prog State)} {env : Env} {st : (KernelState prog State)} {sb : Nat} {dst : Option Var} {X : Var}
    {rest : Stmt} {x : BitVec 32}
    (hbad : ∀ v, st.mem.loadField prog sb "sp" = some v → ∀ sp : BitVec 32, v ≠ .u32 sp)
    (hst : env.get "st" = some (.ptr sb 0)) (hX : env.get X = some (.u32 x)) :
    WPC prog (.seq (.call dst "spend" [.var "st", .bin .sub (.field (.var "st") "sp") (.var X)]) rest)
      Q env st := by
  apply WPC.seq
  apply WPC.call_shape (fn := spend) (hf := spend_find) (hps := spend_params)
  intro vs hargs _
  exfalso
  simp only [evalArgs, evalE, hst, hX, ↓reduceIte] at hargs
  cases hl : st.mem.loadField prog sb "sp" with
  | none => simp [hl] at hargs
  | some v => simp [hl, rl_sub_sp_none hbad x v hl] at hargs

open Lean in
/-- `ok = spend(st, st->sp - X); if (ok == 0) return NOID; cl_erase(st, X, P);`: the
spend pays for the erase (`rl_cl_erase_cost`, `st->sp` kept by `spend`).  Leaves the
goal after the erase. -/
macro "rl_spend_erase" : tactic => do
  let A := mkIdent `A
  `(tactic| (
    have _hbc := ‹Budget _ _ _ _›
    rcases rl_sp_or _hbc with ⟨_sp, _hsp⟩ | _hbad
    rotate_left
    · exact rl_spend_bad _hbad (by simp [Env.get]) (by simp only [Env.get, String.reduceEq, ↓reduceIte]; rfl)
    have _hspl := _hsp.load fi_sp (by simp)
    apply WPC.seq
    apply WPC.call_shape (fn := spend) (hf := spend_find) (hps := spend_params)
    intro _vs _hargs _
    simp [evalArgs, evalE, Env.get, evalBin, evalArith, _hspl] at _hargs
    subst _hargs
    refine ⟨_, _, rl_spend_sp _ $A (by omega) _ _sp, ⟨⟨rfl, _, _, _hbc⟩, _hsp⟩, ?_⟩
    rintro _rv _st1 _c1 ⟨⟨_w1, _mm1, _hb1, _ht1, _hm1⟩, _hsp1⟩
    rw [Budget.wk _hbc] at _ht1
    rw [Budget.mk _hbc] at _hm1
    wpc_dst
    apply WPC.seq
    rl_ite_case
    · wpc_auto; rl_done
    apply WPC.skip; wpc_simp
    apply WPC.seq
    apply WPC.call_shape (fn := clErase) (hf := clErase_find) (hps := clErase_params)
    intro _vs _hargs _
    simp [evalArgs, evalE, Env.get] at _hargs
    subst _hargs
    refine ⟨_, _, rl_cl_erase_costA _ $A (by omega) _ _ _sp, ⟨⟨rfl, _, _, _hb1⟩, _hsp1⟩, ?_⟩
    rintro _rv _st2 _c2 ⟨_w2, _mm2, _hb2, _ht2, _hm2⟩
    rw [Budget.wk _hb1] at _ht2
    rw [Budget.mk _hb1] at _hm2
    wpc_dst))

theorem r_resolution_cost (sb A : Nat) (hA : 100 ≤ A) (np na : BitVec 32) :
    FnCost (State := State) prog "r_resolution" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow (500 * np.toNat + 11000)) 0 noSlack) := by
  apply FnCost.intro (fn := rResolution) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body rResolution
  have hA6 : 6 ≤ A := by omega
  have hA20 : 20 ≤ A := by omega
  -- if (np < 2) return NOID;
  apply WPC.seq; apply WPC.ite; embc_simp; constructor
  · intro _; wpc_auto; rl_done
  intro hnp
  have hnp' : 2 ≤ np.toNat := by have := BitVec.le_def.mp hnp; simpa using this
  have hn1 : (np - 1#32).toNat = np.toNat - 1 := by rw [BitVec.toNat_sub]; simp; omega
  apply WPC.skip; wpc_simp
  -- n = np - 1; pw = (n + 31) / 32; if (na != pw + n) return NOID; base = st->sp;
  apply WPC.seq; wpc_step
  apply WPC.seq; wpc_step
  apply WPC.seq; apply WPC.ite_any
  · wpc_auto; rl_done
  apply WPC.skip; wpc_simp
  apply WPC.seq; wpc_step
  rl_name "base" => base
  apply WPC.seq
  apply WPC.while
    (I := fun env' st' k => ∃ pw i lit nl piv0 piv1 mid ok : BitVec 32,
      env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("np", .u32, .u32 np), ("na", .u32, .u32 na),
        ("n", .u32, .u32 (np - 1#32)), ("pw", .u32, .u32 pw), ("i", .u32, .u32 i),
        ("lit", .u32, .u32 lit), ("nl", .u32, .u32 nl), ("piv0", .u32, .u32 piv0), ("piv1", .u32, .u32 piv1),
        ("base", .u32, .u32 base), ("mid", .u32, .u32 mid), ("ok", .u32, .u32 ok),
        ("len", .u32, .u32 0#32), ("r", .u32, .u32 0#32)] ∧
      i.toNat ≤ np.toNat - 1 ∧ ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
      k.t + A * w'.toNat ≤ A * w0.toNat + 500 * i.toNat ∧ k.m + mm'.toNat ≤ mm.toNat)
    (μ := fun env' _ => np.toNat - 1 - envU32 env' "i")
  · exact ⟨_, 0#32, 0#32, 0#32, 0#32, 0#32, 0#32, 0#32, rfl, by simp, w0, mm, hb, by cost_arith, by cost_arith⟩
  rintro env' st' k ⟨pw, i, lit, nl, piv0, piv1, mid, ok, rfl, hin, w', mm', hb', hk, hkm⟩
  embc_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · -- after the loop: len = st->sp - base; ...; r = mkn(...)
    wpc_auto
    rl_done
  have hlt' : i.toNat < np.toNat - 1 := by
    have := BitVec.lt_def.mp hlt; rw [hn1] at this; exact this
  have hi1 : (i + 1#32).toNat = i.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
  -- lit = expr_at(...); if (lit == NOID) ...; nl = find_not(st, lit); if (st->err != 0) ...
  apply WPC.seq; wpc_step
  apply WPC.seq; apply WPC.ite_any
  · wpc_auto; rl_done
  apply WPC.skip; wpc_simp
  apply WPC.seq; wpc_step
  apply WPC.seq; apply WPC.ite_any
  · wpc_auto; rl_done
  apply WPC.skip; wpc_simp
  -- the pivots: one continuation
  refine rl_ite_assign2_join (by rfl) (fun _ => by rfl) ?_
  intro p0 p1
  wpc_simp
  -- if (i == 0) { ok = cl_lits(st, st->prem[0], piv0); if (ok == 0) return NOID; }: one continuation
  name_bud st1 w1 mm1 hb1
  refine rl_ite_join (A := A) (K := 140) "ok" hb1 ⟨ok, by simp [Env.set]⟩ ?_ ?_
  · apply WPC.seq; wpc_step
    apply WPC.ite_any
    · wpc_auto; rl_done
    apply WPC.skip
    simp only [CPost.shift_apply]
    refine ⟨?v, ?henv, _, _, ‹Budget _ _ _ _›, ?_, ?_⟩
    case henv => rfl
    all_goals cost_arith
  intro v st2 k2 w2 mm2 hb2 hk2 hkm2
  wpc_simp
  rl_spend_erase
  -- mid = st->sp; ok = cl_lits(st, st->prem[i + 1], piv1); if (ok == 0) return NOID;
  apply WPC.seq; wpc_step
  apply WPC.seq; wpc_step
  apply WPC.seq; apply WPC.ite_any
  · wpc_auto; rl_done
  apply WPC.skip; wpc_simp
  rl_spend_erase
  -- i = i + 1
  wpc_auto
  cost_clean
  simp only [allow_apply, noSlack_apply] at *
  refine ⟨?_, pw, i + 1#32, ⟨_, _, _, _, _, _, rfl⟩, ?_, _, _, ‹Budget _ _ _ _›, ?_, ?_⟩
  · simp only [envU32, Env.get, String.reduceEq, ↓reduceIte, hi1]; omega
  · omega
  · cost_arith
  · cost_arith

fncost_register "r_resolution" rResolution r_resolution_cost

/-! ## `push` moves `st->sp` up by one -/

/-- Two cost facts about the same call. -/
theorem rl_and {f : String} {pre : List Val → (KernelState prog State) → Prop}
    {post1 post2 : List Val → (KernelState prog State) → Option Val → (KernelState prog State) → Cost → Prop}
    (h1 : FnCost (State := State) prog f pre post1) (h2 : FnCost (State := State) prog f pre post2) :
    FnCost (State := State) prog f pre (fun vs st rv st' c => post1 vs st rv st' c ∧ post2 vs st rv st' c) := by
  intro vs st hp
  obtain ⟨f1, hf1⟩ := h1 vs st hp
  obtain ⟨f2, hf2⟩ := h2 vs st hp
  refine ⟨max f1 f2, ?_⟩
  rw [runC_mono prog (CallResC.sat_ne hf1) _ (Nat.le_max_left f1 f2)]
  have e2 := runC_mono prog (CallResC.sat_ne hf2) _ (Nat.le_max_right f1 f2)
  rw [runC_mono prog (CallResC.sat_ne hf1) _ (Nat.le_max_left f1 f2)] at e2
  have hsat : ∀ result : (CallResC prog State), result.sat (post1 vs st) →
      result.sat (post2 vs st) →
      result.sat (fun rv st' c => post1 vs st rv st' c ∧ post2 vs st rv st' c) := by
    intro result
    cases result with
    | timeout => intro h; exact h.elim
    | stuck => intro _ _; trivial
    | ok r =>
      obtain ⟨rv, st', c⟩ := r
      intro h1 h2
      exact ⟨h1, h2⟩
  rw [e2] at hf1 ⊢
  exact hsat _ hf1 hf2

/-- A kernel call in `push` (`kvrealloc`): keeps cell 11, names the result. -/
macro "rl_fecall" : tactic => `(tactic| (apply WPC.ecall_fld (by assumption); intro _vs _hvs; refine ⟨fun _ _ _h => (nomatch _h), ?_⟩; intro _rv _st' _hf; cases _rv; (simp [assignDst]); (simp only [assignDst_some, Env.assign, Env.ty, String.reduceEq, ↓reduceIte]; rename_i _ns; by_cases _hty : _st'.mem.hasTy _ns (.ptr .u32) = true <;> simp only [_hty, ↓reduceIte, Env.set, String.reduceEq] <;> (try trivial))))

/-- One statement of `push` that keeps `st->sp` (its cell 11). -/
macro "rl_fstep" : tactic => `(tactic| first
  | apply WPC.seq
  | apply WPC.ite_any
  | (apply WPC.skip; wpc_simp)
  | (apply WPC.ret_val; intro _v _hv; simp only [evalE, Option.some.injEq] at _hv; subst _hv;
     simp only [retPostC, CPost.shift_apply]; (try intro _);
     first | exact Or.inl rfl | exact Or.inl trivial | exact Or.inr ‹_› | exact ‹_› | trivial)
  | (apply WPC.setField; simp only [evalE, Env.get, String.reduceEq, ↓reduceIte,
       (‹Fld _ _ 11 _›).load fi_sp (by simp), evalBin, evalArith]; intro _; split; trivial;
     rename_i _m' _hs; have := Fld.storeField_same ‹Fld _ _ 11 _› _hs fi_sp; wpc_simp)
  | (refine WPC.setField_fld (by assumption) ?_ ?_; (intro _t; exact fieldIn_ne_of_ne fi_sp (by decide) _t);
     intro _m' _hf; wpc_simp)
  | (apply WPC.store_fld (by assumption); intro _m' _hf; wpc_simp)
  | rl_fecall
  | (apply WPC.assign_eval; intro _v _hv;
      simp only [evalE, evalBin, evalArith, evalCast, Env.get, String.reduceEq, ↓reduceIte,
        Option.some.injEq, Nat.reduceMod, Nat.reduceLT, BitVec.toNat_ofNat] at _hv; subst _hv;
      simp only [Env.assign, Env.ty, String.reduceEq, ↓reduceIte, Mem.hasTy_u32, Mem.hasTy_u64]; wpc_simp)
  | (refine WPC.assign_u32 ?_ ?_; (rfl); intro _n; wpc_simp))

theorem rl_push_sp_only (sb : Nat) (sp v : BitVec 32) :
    FnCost (State := State) prog "push"
      (fun vs st => BudPre sb [.ptr sb 0, .u32 v] vs st ∧ Fld st.mem sb 11 (.u32 sp))
      (fun _ _ rv st' _ => rv = some (.u32 0#32) ∨ Fld st'.mem sb 11 (.u32 (sp + 1#32))) := by
  apply FnCost.intro (fn := push) rfl
  rintro vs st ⟨⟨rfl, w, mm, hb⟩, hsp⟩
  fncost_body push
  repeat (any_goals rl_fstep)
  all_goals done

theorem rl_ofNat_succ (kb : BitVec 32) (c : Nat) :
    kb + BitVec.ofNat 32 c + 1#32 = kb + BitVec.ofNat 32 (c + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- `a && b` evaluated to a non-zero word: so did `b`. -/
theorem rl_land_snd {P : Prog} {env : Env} {m : Mem} {a b : Expr} {v : BitVec 32}
    (h : evalE P env m (.land a b) = some (.u32 v)) (hv : v ≠ 0#32) :
    ∃ y : BitVec 32, evalE P env m b = some (.u32 y) ∧ y ≠ 0#32 := by
  simp only [evalE] at h
  split at h
  · split at h
    · simp only [Option.some.injEq, Val.u32.injEq] at h; exact absurd h.symm hv
    · split at h
      · rename_i y hy
        refine ⟨y, hy, fun hy0 => hv ?_⟩
        subst hy0
        simpa [Val.ofBool] using h.symm
      · simp at h
  · simp at h

theorem rl_push_sp (sb A : Nat) (hA : 6 ≤ A) (v sp : BitVec 32) :
    FnCost (State := State) prog "push"
      (fun vs st => BudPre sb [.ptr sb 0, .u32 v] vs st ∧ Fld st.mem sb 11 (.u32 sp))
      (fun vs st rv st' c => Amort sb A (allow 56) 0 (slackUnless 0#32 A) vs st rv st' c ∧
        (rv = some (.u32 0#32) ∨ Fld st'.mem sb 11 (.u32 (sp + 1#32)))) :=
  rl_and (FnCost.mono (push_cost sb A hA v) (fun _ _ h => h.1) (fun _ _ _ _ _ _ h => h))
    (rl_push_sp_only sb sp v)

theorem r_factoring_cost (sb A : Nat) (hA : 100 ≤ A) (np na : BitVec 32) :
    FnCost (State := State) prog "r_factoring" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow (80 * na.toNat + 2300000)) 0 noSlack) := by
  apply FnCost.intro (fn := rFactoring) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body rFactoring
  have hA6 : 6 ≤ A := by omega
  -- the checks; n = (st->pool[p] >> 8) & 0xff; mb = st->sp;
  apply WPC.seq; apply WPC.ite_any
  · wpc_auto; rl_done
  apply WPC.skip; wpc_simp
  apply WPC.seq; wpc_step
  iterate 2
    apply WPC.seq; apply WPC.ite_any
    · wpc_auto; rl_done
    apply WPC.skip; wpc_simp
  apply WPC.seq
  refine WPC.assign_band (by rfl) ?_
  intro n hn
  wpc_simp
  have hn' : n.toNat ≤ 255 := by simpa using hn
  apply WPC.seq; wpc_step
  rl_name "p" => p
  rl_name "mb" => mb
  -- the marks: each push pays for its iteration
  apply WPC.seq
  apply WPC.while
    (I := fun env' st' k => ∃ i ok : BitVec 32,
      env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("np", .u32, .u32 np), ("na", .u32, .u32 na),
        ("p", .u32, .u32 p), ("n", .u32, .u32 n), ("mb", .u32, .u32 mb), ("kb", .u32, .u32 0#32),
        ("m", .u32, .u32 0#32), ("i", .u32, .u32 i), ("j", .u32, .u32 0#32), ("x", .u32, .u32 0#32),
        ("ok", .u32, .u32 ok), ("r", .u32, .u32 0#32)] ∧
      i.toNat ≤ n.toNat ∧ ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
      k.t + A * w'.toNat ≤ A * w0.toNat ∧ k.m + mm'.toNat ≤ mm.toNat)
    (μ := fun env' _ => n.toNat - envU32 env' "i")
  · exact ⟨0#32, 0#32, rfl, by simp, w0, mm, hb, by cost_arith, by cost_arith⟩
  rintro env' st' k ⟨i, ok, rfl, hin, w', mm', hb', hk, hkm⟩
  embc_simp
  refine ⟨fun hge => ?_, fun hlt => ?body⟩
  case body =>
    have hlt' : i.toNat < n.toNat := by simpa [BitVec.lt_def] using hlt
    have hi1 : (i + 1#32).toNat = i.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    apply WPC.seq; wpc_step
    apply WPC.seq; wpc_ite_case
    · wpc_auto; wpc_done
    wpc_auto
    wpc_done
    all_goals mid_next hi1
  -- ok = cl_dups(st, p, n, na, mb); if (ok == 0) return NOID; kb = st->sp; i = 0;
  apply WPC.seq; wpc_step
  apply WPC.seq; apply WPC.ite_any
  · wpc_auto; rl_done
  apply WPC.skip; wpc_simp
  name_bud st1 w1 mm1 hb1
  cost_clean
  rcases rl_sp_or hb1 with ⟨kb, hkb⟩ | hbad
  rotate_left
  · apply WPC.seq; apply WPC.assign
    simp only [evalE, Env.get, ↓reduceIte]
    cases hl : st1.mem.loadField prog sb "sp" with
    | none => simp
    | some v =>
      have := hbad v hl
      cases v <;> simp_all [Env.assign, Env.ty]
  have hkbl := hkb.load fi_sp (by simp)
  apply WPC.seq; apply WPC.assign
  simp only [evalE, Env.get, String.reduceEq, ↓reduceIte, hkbl, Env.assign, Env.ty, Mem.hasTy_u32]
  wpc_simp
  apply WPC.seq; wpc_step
  -- the kept literals: each push moves `sp` by one, so `sp = kb + cnt` with `cnt ≤ i`
  apply WPC.seq
  apply WPC.while
    (I := fun env' st' k => ∃ (i ok : BitVec 32) (cnt : Nat),
      env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("np", .u32, .u32 np), ("na", .u32, .u32 na),
        ("p", .u32, .u32 p), ("n", .u32, .u32 n), ("mb", .u32, .u32 mb), ("kb", .u32, .u32 kb),
        ("m", .u32, .u32 0#32), ("i", .u32, .u32 i), ("j", .u32, .u32 0#32), ("x", .u32, .u32 0#32),
        ("ok", .u32, .u32 ok), ("r", .u32, .u32 0#32)] ∧
      i.toNat ≤ n.toNat ∧ cnt ≤ i.toNat ∧ ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
      Fld st'.mem sb 11 (.u32 (kb + BitVec.ofNat 32 cnt)) ∧
      k.t + A * w'.toNat ≤ A * w1.toNat + 30 * i.toNat ∧ k.m + mm'.toNat ≤ mm1.toNat)
    (μ := fun env' _ => n.toNat - envU32 env' "i")
  · exact ⟨0#32, _, 0, rfl, by simp, by simp, w1, mm1, hb1, by simpa using hkb, by cost_arith, by cost_arith⟩
  rintro env' st' k ⟨i, ok, cnt, rfl, hin, hcnt, w', mm', hb', hsp', hk, hkm⟩
  embc_simp
  refine ⟨fun hge => ?_, fun hlt => ?body⟩
  case body =>
    have hlt' : i.toNat < n.toNat := by simpa [BitVec.lt_def] using hlt
    have hi1 : (i + 1#32).toNat = i.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    apply WPC.seq
    apply WPC.ite_any
    · apply WPC.seq
      apply WPC.call_shape (fn := push) (hf := push_find) (hps := push_params)
      intro vs1 hargs hbp
      obtain ⟨v0, vs2, h0, -, rfl⟩ := evalArgs_cons' hargs
      simp only [evalE, Env.get, ↓reduceIte, Option.some.injEq] at h0
      subst h0
      obtain ⟨v1, vs3, e1, -, hbp1⟩ := bindParams_ne_none_cons hbp
      simp only [List.cons.injEq] at e1
      obtain ⟨rfl, rfl⟩ := e1
      obtain ⟨v2, vs4, rfl, ht2, hbp2⟩ := bindParams_ne_none_cons hbp1
      obtain ⟨pv, rfl⟩ := Mem.hasTy_u32_inv ht2
      obtain rfl := bindParams_ne_none_nil hbp2
      refine ⟨_, _, rl_push_sp sb A hA6 pv _, ⟨⟨rfl, _, _, hb'⟩, hsp'⟩, ?_⟩
      rintro rv st2 c2 ⟨⟨w2, mm2, hb2, ht2, hm2⟩, hsp2⟩
      rw [hb'.wk] at ht2
      rw [hb'.mk] at hm2
      split
      · trivial
      rename_i env2 hasg
      obtain ⟨r2, rfl, rfl⟩ := assignDst_u32' hasg rfl
      wpc_simp
      apply WPC.ite
      embc_simp
      constructor
      · intro hr
        wpc_auto
        rl_done
      intro hr
      have hsp3 : Fld st2.mem sb 11 (.u32 (kb + BitVec.ofNat 32 (cnt + 1))) := by
        rw [← rl_ofNat_succ]
        rcases hsp2 with h | h
        · simp only [Option.some.injEq, Val.u32.injEq] at h; exact absurd h hr
        · exact h
      simp only [slackUnless_apply, Option.some.injEq, Val.u32.injEq, hr, ↓reduceIte, allow_apply] at ht2
      apply WPC.skip
      wpc_simp
      apply WPC.assign
      simp only [evalE, Env.get, String.reduceEq, ↓reduceIte, evalBin, evalArith, Env.assign, Env.ty,
        Mem.hasTy_u32]
      dsimp only [CPost.shift]
      refine ⟨?_, i + 1#32, ⟨r2, by simp [Env.set]⟩, by omega, cnt + 1, by omega, w2, mm2, hb2, hsp3, ?_, ?_⟩
      · simp only [envU32, Env.get, Env.set, String.reduceEq, ↓reduceIte, hi1]; omega
      · cost_arith
      · cost_arith
    · apply WPC.skip
      wpc_simp
      apply WPC.assign
      simp only [evalE, Env.get, String.reduceEq, ↓reduceIte, evalBin, evalArith, Env.assign, Env.ty,
        Mem.hasTy_u32]
      dsimp only [CPost.shift]
      refine ⟨?_, i + 1#32, ⟨ok, by simp [Env.set]⟩, by omega, cnt, by omega, w', mm', hb', hsp', ?_, ?_⟩
      · simp only [envU32, Env.get, Env.set, String.reduceEq, ↓reduceIte, hi1]; omega
      · cost_arith
      · cost_arith
  -- m = st->sp - kb  (= cnt ≤ n ≤ 255)
  have hge' : n.toNat ≤ i.toNat := by
    have := BitVec.not_lt.mp (by simpa using hge); exact BitVec.le_def.mp this
  have hspl := hsp'.load fi_sp (by simp)
  have hc32 : cnt < 4294967296 := by omega
  have hm : kb + BitVec.ofNat 32 cnt - kb = BitVec.ofNat 32 cnt := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hmn : (BitVec.ofNat 32 cnt).toNat = cnt := by simp only [BitVec.toNat_ofNat]; omega
  apply WPC.seq; apply WPC.assign
  simp only [evalE, Env.get, String.reduceEq, ↓reduceIte, hspl, evalBin, evalArith, Env.assign, Env.ty,
    Mem.hasTy_u32, hm]
  wpc_simp
  -- ok = spend(st, (n - m) * m); if (ok == 0) return NOID; i = 0;
  apply WPC.seq; wpc_step
  apply WPC.seq; apply WPC.ite_any
  · wpc_auto; rl_done
  apply WPC.skip; wpc_simp
  apply WPC.seq; wpc_step
  name_bud st3 w3 mm3 hb3
  cost_clean
  -- the duplicates: each found in the kept list, `m ≤ 255` comparisons each
  apply WPC.seq
  apply WPC.while
    (I := fun env' st' k => st' = st3 ∧ ∃ i2 j x ok : BitVec 32,
      env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("np", .u32, .u32 np), ("na", .u32, .u32 na),
        ("p", .u32, .u32 p), ("n", .u32, .u32 n), ("mb", .u32, .u32 mb), ("kb", .u32, .u32 kb),
        ("m", .u32, .u32 (BitVec.ofNat 32 cnt)), ("i", .u32, .u32 i2), ("j", .u32, .u32 j), ("x", .u32, .u32 x),
        ("ok", .u32, .u32 ok), ("r", .u32, .u32 0#32)] ∧
      i2.toNat ≤ n.toNat ∧ k.t ≤ 2600 * i2.toNat ∧ k.m = 0)
    (μ := fun env' _ => n.toNat - envU32 env' "i")
  · exact ⟨rfl, 0#32, 0#32, 0#32, _, rfl, by simp, by simp, by simp⟩
  rintro env2 st4 k4 ⟨hst4, i2, j, x, ok2, rfl, hin2, hk4, hkm4⟩
  subst hst4
  embc_simp
  refine ⟨fun hge2 => ?_, fun hlt2 => ?body2⟩
  case body2 =>
    have hlt2' : i2.toNat < n.toNat := by simpa [BitVec.lt_def] using hlt2
    have hi21 : (i2 + 1#32).toNat = i2.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    -- if (st->stk[mb + i] != 0) { x = ...; j = 0; while (...) j++; if (j == m) return NOID; } i = i + 1;
    apply WPC.seq_join (J := fun env' st' k => st' = st4 ∧ ∃ j2 x2 : BitVec 32,
        env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("np", .u32, .u32 np), ("na", .u32, .u32 na),
          ("p", .u32, .u32 p), ("n", .u32, .u32 n), ("mb", .u32, .u32 mb), ("kb", .u32, .u32 kb),
          ("m", .u32, .u32 (BitVec.ofNat 32 cnt)), ("i", .u32, .u32 i2), ("j", .u32, .u32 j2),
          ("x", .u32, .u32 x2), ("ok", .u32, .u32 ok2), ("r", .u32, .u32 0#32)] ∧
        k.t ≤ 2590 ∧ k.m = 0)
    · apply WPC.ite_any
      · apply WPC.seq; wpc_step
        rl_name "x" => xv
        apply WPC.seq; wpc_step
        apply WPC.seq
        apply WPC.while
          (I := fun env' st' k => st' = st4 ∧ ∃ j2 : BitVec 32,
            env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("np", .u32, .u32 np), ("na", .u32, .u32 na),
              ("p", .u32, .u32 p), ("n", .u32, .u32 n), ("mb", .u32, .u32 mb), ("kb", .u32, .u32 kb),
              ("m", .u32, .u32 (BitVec.ofNat 32 cnt)), ("i", .u32, .u32 i2), ("j", .u32, .u32 j2),
              ("x", .u32, .u32 xv), ("ok", .u32, .u32 ok2), ("r", .u32, .u32 0#32)] ∧
            j2.toNat ≤ cnt ∧ k.t ≤ 6 * j2.toNat ∧ k.m = 0)
          (μ := fun env' _ => cnt - envU32 env' "j")
        · exact ⟨rfl, 0#32, rfl, by simp, by simp, by simp⟩
        rintro env3 st5 k5 ⟨rfl, j2, rfl, hj2, hk5, hkm5⟩
        split
        · rename_i v hv
          constructor
          · intro _
            apply WPC.ite_any
            · wpc_auto
              rl_done
            · apply WPC.skip
              simp only [CPost.shift_apply]
              refine ⟨by first | rfl | trivial, j2, xv, rfl, ?_, ?_⟩ <;> first | cost_arith | cost_simp
          · intro hv0
            obtain ⟨x0, hx0, hx0ne⟩ := rl_land_fst hv hv0
            have hjm : j2.toNat < cnt := by
              simp only [evalE, Env.get, String.reduceEq, ↓reduceIte, evalBin, evalArith, Val.ofBool,
                Option.some.injEq, Val.u32.injEq] at hx0
              rcases Nat.lt_or_ge j2.toNat cnt with hc | hc
              · exact hc
              exfalso
              have : ¬ j2 < BitVec.ofNat 32 cnt := by rw [BitVec.lt_def, hmn]; omega
              simp [this] at hx0
              exact hx0ne hx0.symm
            have hj21 : (j2 + 1#32).toNat = j2.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
            apply WPC.assign
            simp only [evalE, Env.get, String.reduceEq, ↓reduceIte, evalBin, evalArith, Env.assign, Env.ty,
              Mem.hasTy_u32]
            refine ⟨?_, trivial, j2 + 1#32, by simp [Env.set], by omega, ?_, ?_⟩
            · simp only [envU32, Env.get, Env.set, String.reduceEq, ↓reduceIte, hj21]; omega
            · cost_arith
            · cost_arith
        · trivial
      · apply WPC.skip
        simp only [CPost.shift_apply]
        refine ⟨by first | rfl | trivial, j, x, rfl, ?_, ?_⟩ <;> first | cost_arith | cost_simp
    · rintro env5 st5 k5 ⟨hst5, j5, x5, rfl, hk5, hkm5⟩
      subst hst5
      apply WPC.assign
      simp only [evalE, Env.get, String.reduceEq, ↓reduceIte, evalBin, evalArith, Env.assign, Env.ty,
        Mem.hasTy_u32]
      dsimp only [CPost.shift]
      refine ⟨?_, rfl, i2 + 1#32, ⟨j5, x5, ok2, by simp [Env.set]⟩, by omega, ?_, hkm4, ?_⟩
      · simp only [envU32, Env.get, Env.set, String.reduceEq, ↓reduceIte, hi21]; omega
      · cost_arith
      · first | cost_arith | cost_simp
  wpc_auto
  rl_done

fncost_register "r_factoring" rFactoring r_factoring_cost

/-! ## `lin_add`, `lin_f`, `r_poly_norm`, `odd_mul_sub`, `r_poly_norm_eq` -/

/-- `lin_add`: the C rejects `b1 < b0 || e < b1 || e > MAX_POOL` (`e = st->sp`), so the
merge steps `i ∈ [b1+2, e+2]` and `j ∈ [b0+2, b1+2]` by 3 without wrapping and costs at
most `10·((i - b1) + (j - b0)) ≤ 10·(e - b0 + 4)`, paid by `spend(e - b0)`; each output term
and each copied tail word pays by its push (`lin_term`, `push` slack); the copy down to
`b0` is paid by `spend(n)`, `n = st->sp - e`. -/
theorem lin_add_cost (sb A : Nat) (hA : 300 ≤ A) (b0 b1 : BitVec 32) (m : BitVec 64) :
    FnCost (State := State) prog "lin_add" (BudPre sb [.ptr sb 0, .u32 b0, .u32 b1, .u64 m])
      (Amort sb A (allowFail 0#32 1000 100) 0 (slackUnless 0#32 150)) := by
  apply FnCost.intro (fn := linAdd) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body linAdd
  have hA6 : 6 ≤ A := by omega
  have hA100 : 100 ≤ A := by omega
  -- e = st->sp;
  rcases rl_sp_or hb with ⟨e, he⟩ | hbad
  rotate_left
  · apply WPC.seq; apply WPC.assign
    simp only [evalE, Env.get, ↓reduceIte]
    cases hl : st.mem.loadField prog sb "sp" with
    | none => simp
    | some v =>
      have := hbad v hl
      cases v <;> simp_all [Env.assign, Env.ty]
  have hel := he.load fi_sp (by simp)
  apply WPC.seq; apply WPC.assign
  simp only [evalE, Env.get, String.reduceEq, ↓reduceIte, hel, Env.assign, Env.ty, Mem.hasTy_u32]
  wpc_simp
  -- if (b1 < b0 || e < b1 || e > MAX_POOL) return 0;
  apply WPC.seq; apply WPC.ite; embc_simp
  by_cases h1 : b1 < b0
  · simp only [h1, ↓reduceIte]
    refine ⟨fun _ => ?_, fun h => absurd h (by decide)⟩
    wpc_auto; rl_done
  by_cases h2 : e < b1
  · simp only [h1, h2, ↓reduceIte, BitVec.reduceEq]
    refine ⟨fun _ => ?_, fun h => absurd h (by decide)⟩
    wpc_auto; rl_done
  by_cases h3 : 1073741824#32 < e
  · simp only [h1, h2, h3, ↓reduceIte, BitVec.reduceEq]
    refine ⟨fun _ => ?_, fun h => absurd h (by decide)⟩
    wpc_auto; rl_done
  simp only [h1, h2, h3, ↓reduceIte]
  refine ⟨fun h => (h (by first | rfl | trivial)).elim, fun _ => ?_⟩
  simp only [BitVec.lt_def, BitVec.toNat_ofNat, Nat.not_lt] at h1 h2 h3
  apply WPC.skip; wpc_simp
  have heb : (e - b0).toNat = e.toNat - b0.toNat := by rw [BitVec.toNat_sub]; omega
  have hpay1 : 10 * (e - b0).toNat ≤ A * (e - b0).toNat := Nat.mul_le_mul_right _ (by omega)
  -- ok = spend(st, e - b0); c = lin_get64(..); d = lin_get64(..); ok = lin_push64(..)
  apply WPC.seq; wpc_step
  apply WPC.seq; rl_ite_case
  · wpc_auto; rl_done
  apply WPC.skip; wpc_simp
  apply WPC.seq; wpc_step
  apply WPC.seq; wpc_step
  apply WPC.seq; wpc_step
  apply WPC.seq; rl_ite_case
  · wpc_auto; rl_done
  apply WPC.skip; wpc_simp
  apply WPC.seq; wpc_step
  apply WPC.seq; wpc_step
  name_bud st1 w1 mm1 hb1
  cost_clean
  rl_name "ok" => ok0
  have hi0 : (b1 + 2#32).toNat = b1.toNat + 2 := by rw [BitVec.toNat_add]; simp; omega
  have hj0 : (b0 + 2#32).toNat = b0.toNat + 2 := by rw [BitVec.toNat_add]; simp; omega
  -- the merge: each step moves `i` or `j` (or both) by 3 inside `stk[b0..e)`, paid by the spend
  apply WPC.seq
  apply WPC.while
    (I := fun env' st' k => ∃ (i j a b ok : BitVec 32) (c d : BitVec 64),
      env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("b0", .u32, .u32 b0), ("b1", .u32, .u32 b1),
        ("m", .u64, .u64 m), ("e", .u32, .u32 e), ("i", .u32, .u32 i), ("j", .u32, .u32 j),
        ("a", .u32, .u32 a), ("b", .u32, .u32 b), ("n", .u32, .u32 0#32), ("ok", .u32, .u32 ok),
        ("c", .u64, .u64 c), ("d", .u64, .u64 d)] ∧
      b1.toNat + 2 ≤ i.toNat ∧ i.toNat ≤ e.toNat + 2 ∧ b0.toNat + 2 ≤ j.toNat ∧ j.toNat ≤ b1.toNat + 2 ∧
      ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
      k.t + A * w'.toNat ≤ A * w1.toNat + 10 * ((i.toNat - b1.toNat) + (j.toNat - b0.toNat)) ∧
      k.m + mm'.toNat ≤ mm1.toNat)
    (μ := fun env' _ => (e.toNat + 3 - envU32 env' "i") + (b1.toNat + 3 - envU32 env' "j"))
  · exact ⟨_, _, _, _, _, _, _, rfl, by omega, by omega, by omega, by omega, w1, mm1, hb1, by simp, by simp⟩
  rintro env' st' k ⟨i, j, a, b, ok, c, d, rfl, hi1, hi2, hj1, hj2, w', mm', hb', hk, hkm⟩
  split
  rotate_left
  · trivial
  rename_i v hv
  refine ⟨fun hv0 => ?exit, fun hv0 => ?_⟩
  case exit =>
    dsimp only
    -- the rest of `p`: each push pays for its iteration
    apply WPC.seq
    apply WPC.while
      (I := fun env2 st2 k2 => ∃ i2 ok2 : BitVec 32,
        env2 = [("st", .ptr (.struct "ck"), .ptr sb 0), ("b0", .u32, .u32 b0), ("b1", .u32, .u32 b1),
          ("m", .u64, .u64 m), ("e", .u32, .u32 e), ("i", .u32, .u32 i2), ("j", .u32, .u32 j),
          ("a", .u32, .u32 a), ("b", .u32, .u32 b), ("n", .u32, .u32 0#32), ("ok", .u32, .u32 ok2),
          ("c", .u64, .u64 c), ("d", .u64, .u64 d)] ∧
        i2.toNat ≤ e.toNat + 2 ∧ ∃ w2 mm2 : BitVec 32, Budget st2.mem sb w2 mm2 ∧
        k2.t + A * w2.toNat ≤ A * w'.toNat ∧ k2.m + mm2.toNat ≤ mm'.toNat)
      (μ := fun env2 _ => e.toNat + 3 - envU32 env2 "i")
    · exact ⟨i, ok, rfl, hi2, w', mm', hb', by simp, by simp⟩
    rintro env2 st2 k2 ⟨i2, ok2, rfl, hi22, w2, mm2, hb2, hk2, hkm2⟩
    embc_simp
    refine ⟨fun hge2 => ?_, fun hlt2 => ?body2⟩
    case body2 =>
      have hlt2' : i2.toNat < e.toNat := by simpa [BitVec.lt_def] using hlt2
      have hi21 : (i2 + 1#32).toNat = i2.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
      apply WPC.seq; wpc_step
      apply WPC.seq; wpc_ite_case
      · wpc_auto; wpc_done
      wpc_auto
      wpc_done
      all_goals mid_next hi21
    -- the rest of `q`
    apply WPC.seq
    apply WPC.while
      (I := fun env3 st3 k3 => ∃ j3 ok3 : BitVec 32,
        env3 = [("st", .ptr (.struct "ck"), .ptr sb 0), ("b0", .u32, .u32 b0), ("b1", .u32, .u32 b1),
          ("m", .u64, .u64 m), ("e", .u32, .u32 e), ("i", .u32, .u32 i2), ("j", .u32, .u32 j3),
          ("a", .u32, .u32 a), ("b", .u32, .u32 b), ("n", .u32, .u32 0#32), ("ok", .u32, .u32 ok3),
          ("c", .u64, .u64 c), ("d", .u64, .u64 d)] ∧
        j3.toNat ≤ b1.toNat + 2 ∧ ∃ w3 mm3 : BitVec 32, Budget st3.mem sb w3 mm3 ∧
        k3.t + A * w3.toNat ≤ A * w2.toNat ∧ k3.m + mm3.toNat ≤ mm2.toNat)
      (μ := fun env3 _ => b1.toNat + 3 - envU32 env3 "j")
    · exact ⟨j, ok2, rfl, hj2, w2, mm2, hb2, by simp, by simp⟩
    rintro env3 st3 k3 ⟨j3, ok3, rfl, hj33, w3, mm3, hb3, hk3, hkm3⟩
    embc_simp
    refine ⟨fun hge3 => ?_, fun hlt3 => ?body3⟩
    case body3 =>
      have hlt3' : j3.toNat < b1.toNat := by simpa [BitVec.lt_def] using hlt3
      have hj31 : (j3 + 1#32).toNat = j3.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
      apply WPC.seq; wpc_step
      apply WPC.seq; wpc_ite_case
      · wpc_auto; wpc_done
      wpc_auto
      wpc_done
      all_goals mid_next hj31
    -- n = st->sp - e; ok = spend(st, n); if (ok == 0) return 0; i = 0;
    apply WPC.seq; wpc_step
    rl_name "n" => n
    have hpay2 : 10 * n.toNat ≤ A * n.toNat := Nat.mul_le_mul_right _ (by omega)
    apply WPC.seq; wpc_step
    apply WPC.seq; rl_ite_case
    · wpc_auto; rl_done
    apply WPC.skip; wpc_simp
    apply WPC.seq; wpc_step
    rl_name "ok" => ok4
    name_bud st4 w4 mm4 hb4
    cost_clean
    -- the copy down to `b0`: `n` words, paid by the spend of `n`
    apply WPC.seq
    apply WPC.while
      (I := fun env5 st5 k5 => ∃ i5 : BitVec 32,
        env5 = [("st", .ptr (.struct "ck"), .ptr sb 0), ("b0", .u32, .u32 b0), ("b1", .u32, .u32 b1),
          ("m", .u64, .u64 m), ("e", .u32, .u32 e), ("i", .u32, .u32 i5), ("j", .u32, .u32 j3),
          ("a", .u32, .u32 a), ("b", .u32, .u32 b), ("n", .u32, .u32 n), ("ok", .u32, .u32 ok4),
          ("c", .u64, .u64 c), ("d", .u64, .u64 d)] ∧
        i5.toNat ≤ n.toNat ∧ ∃ w5 mm5 : BitVec 32, Budget st5.mem sb w5 mm5 ∧
        k5.t + A * w5.toNat ≤ A * w4.toNat + 10 * i5.toNat ∧ k5.m + mm5.toNat ≤ mm4.toNat)
      (μ := fun env5 _ => n.toNat - envU32 env5 "i")
    · exact ⟨0#32, rfl, by simp, w4, mm4, hb4, by simp, by simp⟩
    rintro env5 st5 k5 ⟨i5, rfl, hi55, w5, mm5, hb5, hk5, hkm5⟩
    embc_simp
    refine ⟨fun hge5 => ?_, fun hlt5 => ?body5⟩
    case body5 =>
      have hlt5' : i5.toNat < n.toNat := by simpa [BitVec.lt_def] using hlt5
      have hi51 : (i5 + 1#32).toNat = i5.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
      wpc_auto
      wpc_done
      all_goals mid_next hi51
    wpc_auto
    rl_done
  obtain ⟨x0, hx0, hx0ne⟩ := rl_land_fst hv hv0
  obtain ⟨y0, hy0, hy0ne⟩ := rl_land_snd hv hv0
  have hie : i.toNat < e.toNat := by
    simp only [evalE, Env.get, String.reduceEq, ↓reduceIte, evalBin, evalArith, Val.ofBool,
      Option.some.injEq, Val.u32.injEq] at hx0
    rcases Nat.lt_or_ge i.toNat e.toNat with hc | hc
    · exact hc
    exfalso
    have : ¬ i < e := by rw [BitVec.lt_def]; omega
    simp [this] at hx0
    exact hx0ne hx0.symm
  have hjb : j.toNat < b1.toNat := by
    simp only [evalE, Env.get, String.reduceEq, ↓reduceIte, evalBin, evalArith, Val.ofBool,
      Option.some.injEq, Val.u32.injEq] at hy0
    rcases Nat.lt_or_ge j.toNat b1.toNat with hc | hc
    · exact hc
    exfalso
    have : ¬ j < b1 := by rw [BitVec.lt_def]; omega
    simp [this] at hy0
    exact hy0ne hy0.symm
  have hi3 : (i + 3#32).toNat = i.toNat + 3 := by rw [BitVec.toNat_add]; simp; omega
  have hj3 : (j + 3#32).toNat = j.toNat + 3 := by rw [BitVec.toNat_add]; simp; omega
  apply WPC.seq; wpc_step
  apply WPC.seq; wpc_step
  apply WPC.ite_any
  · apply WPC.seq; wpc_step
    apply WPC.seq; wpc_step
    apply WPC.seq; rl_ite_case
    · wpc_auto; rl_done
    apply WPC.skip; wpc_simp
    wpc_step
    cost_clean
    refine ⟨?_, i + 3#32, j, _, _, _, _, _, rfl, by omega, by omega, by omega, by omega, _, _,
      ‹Budget _ _ _ _›, ?_, ?_⟩
    · simp only [envU32, Env.get, String.reduceEq, ↓reduceIte, hi3]; omega
    · cost_arith
    · cost_arith
  apply WPC.ite_any
  · apply WPC.seq; wpc_step
    apply WPC.seq; wpc_step
    apply WPC.seq; rl_ite_case
    · wpc_auto; rl_done
    apply WPC.skip; wpc_simp
    wpc_step
    cost_clean
    refine ⟨?_, i, j + 3#32, _, _, _, _, _, rfl, by omega, by omega, by omega, by omega, _, _,
      ‹Budget _ _ _ _›, ?_, ?_⟩
    · simp only [envU32, Env.get, String.reduceEq, ↓reduceIte, hj3]; omega
    · cost_arith
    · cost_arith
  apply WPC.seq; wpc_step
  apply WPC.seq; wpc_step
  apply WPC.seq; wpc_step
  apply WPC.seq; apply WPC.ite_any
  rotate_left
  apply WPC.skip; wpc_simp
  rotate_left
  apply WPC.seq; wpc_step
  rl_ite_case
  · wpc_auto; rl_done
  apply WPC.skip; wpc_simp
  all_goals
    apply WPC.seq; wpc_step
    wpc_step
    cost_clean
    refine ⟨?_, i + 3#32, j + 3#32, _, _, _, _, _, rfl, by omega, by omega, by omega, by omega, _, _,
      ‹Budget _ _ _ _›, ?_, ?_⟩
    · simp only [envU32, Env.get, String.reduceEq, ↓reduceIte, hi3, hj3]; omega
    · cost_arith
    · cost_arith

fncost_register "lin_add" linAdd lin_add_cost

/-- `rl_lin_scale` at rate `A` (a `spend` of the same length pays it). -/
theorem rl_lin_scale_costA (sb A : Nat) (hA : 10 ≤ A) (b0 : BitVec 32) (k m : BitVec 64) (n : BitVec 32) :
    FnCost (State := State) prog "lin_scale"
      (fun vs st => BudPre sb [.ptr sb 0, .u32 b0, .u64 k, .u64 m] vs st ∧ SpPre sb b0 n st.mem ∧
        b0.toNat + n.toNat < 4294967293)
      (Amort sb A (allow (A * n.toNat + 30)) 0 noSlack) :=
  FnCost.mono (lin_scale_cost sb A b0 k m n) (fun _ _ h => h)
    (fun _ _ _ _ _ _ h => Amort.mono h (by
      simp only [allow_apply]; have := Nat.mul_le_mul_right n.toNat hA; omega) (Nat.le_refl _)
      (Nat.le_refl _))

/-- `lin_scale` on `stk[b0..sp)`. -/
theorem rl_lin_scale_sp (sb A : Nat) (hA : 10 ≤ A) (b0 : BitVec 32) (k m : BitVec 64) (sp : BitVec 32) :
    FnCost (State := State) prog "lin_scale"
      (fun vs st => BudPre sb [.ptr sb 0, .u32 b0, .u64 k, .u64 m] vs st ∧ SpPre sb b0 (sp - b0) st.mem ∧
        b0.toNat + (sp - b0).toNat < 4294967293)
      (Amort sb A (allow (A * (sp - b0).toNat + 30)) 0 noSlack) :=
  rl_lin_scale_costA sb A hA b0 k m (sp - b0)

open Lean in
/-- `if (st->sp < base || st->sp > MAX_POOL) return 0; ok = spend(st, st->sp - base);
if (ok == 0) return 0; lin_scale(st, base, k, m);` in `lin_f`: the reject gives
`SpPre sb base (sp - base)` and no wrap for `lin_scale_cost`, the spend pays the scaling. -/
macro "rl_spend_scale" : tactic => do
  let A := mkIdent `A
  `(tactic| (
    have _hbc := ‹Budget _ _ _ _›
    rcases rl_sp_or _hbc with ⟨_sp, _hsp⟩ | _hbad
    rotate_left
    · apply WPC.seq
      exact rl_guard_bad _hbad (by simp [Env.get]) (by simp only [Env.get, String.reduceEq, ↓reduceIte]; rfl)
    have _hspl := _hsp.load fi_sp (by simp)
    -- if (st->sp < base || st->sp > MAX_POOL) return 0;
    apply WPC.seq
    apply WPC.ite
    embc_simp [_hspl]
    split
    rotate_left
    · trivial
    rename_i _v _hv
    refine ⟨fun _ => ?_, fun _h0 => ?_⟩
    · wpc_auto; rl_done
    subst _h0
    split at _hv
    · simp at _hv
    rename_i _hg1
    split at _hv
    · simp at _hv
    rename_i _hg2
    simp [BitVec.lt_def] at _hg1 _hg2
    apply WPC.skip; wpc_simp
    apply WPC.seq
    apply WPC.call_shape (fn := spend) (hf := spend_find) (hps := spend_params)
    intro _vs _hargs _
    simp [evalArgs, evalE, Env.get, evalBin, evalArith, _hspl] at _hargs
    subst _hargs
    refine ⟨_, _, rl_spend_sp _ $A (by omega) _ _sp, ⟨⟨rfl, _, _, _hbc⟩, _hsp⟩, ?_⟩
    rintro _rv _st1 _c1 ⟨⟨_w1, _mm1, _hb1, _ht1, _hm1⟩, _hsp1⟩
    rw [Budget.wk _hbc] at _ht1
    rw [Budget.mk _hbc] at _hm1
    wpc_dst
    apply WPC.seq
    rl_ite_case
    · wpc_auto; rl_done
    apply WPC.skip; wpc_simp
    apply WPC.seq
    apply WPC.call_shape (fn := linScale) (hf := linScale_find) (hps := linScale_params)
    intro _vs _hargs _
    simp [evalArgs, evalE, Env.get] at _hargs
    subst _hargs
    refine ⟨_, _, rl_lin_scale_sp _ $A (by omega) _ _ _ _sp, ⟨⟨rfl, _, _, _hb1⟩, ⟨_sp, _hsp1, ?_⟩, ?_⟩, ?_⟩
    · rw [BitVec.toNat_sub]; omega
    · rw [BitVec.toNat_sub]; omega
    rintro _rv _st2 _c2 ⟨_w2, _mm2, _hb2, _ht2, _hm2⟩
    rw [Budget.wk _hb1] at _ht2
    rw [Budget.mk _hb1] at _hm2
    wpc_dst))

/-- `lin_f`'s arguments. -/
def rl_LinFArgs (sb : Nat) (vs : List Val) : Prop :=
  ∃ (w id d : BitVec 32), vs = [.ptr sb 0, .u32 w, .u32 id, .u32 d]

theorem rl_lin_f_cost (sb A : Nat) (hA : 400 ≤ A) :
    FnCost (State := State) prog "lin_f"
      (fun vs st => rl_LinFArgs sb vs ∧ ∃ w mm : BitVec 32, Budget st.mem sb w mm)
      (Amort sb A (allowFail 0#32 3000 100) 0 (slackUnless 0#32 100)) := by
  apply FnCost.rec (fun vs _ => depthArg vs)
  intro md IH
  apply FnCost.intro (fn := linF) rfl
  rintro vs st ⟨⟨⟨w, id, d, rfl⟩, w0, mm, hb⟩, hm⟩
  simp only [depthArg] at hm
  have hA6 : 6 ≤ A := by omega
  have hA100 : 100 ≤ A := by omega
  have hA300 : 300 ≤ A := by omega
  fncost_body linF
  -- if (depth == 0) return 0;
  apply WPC.seq; apply WPC.ite; embc_simp; constructor
  · intro hd; wpc_auto; rl_done
  intro hd
  have hd0 : d.toNat ≠ 0 := fun e => hd (BitVec.eq_of_toNat_eq (by simpa using e))
  have hd1 : (d - 1#32).toNat < d.toNat := by rw [BitVec.toNat_sub]; simp; omega
  apply WPC.skip; wpc_simp
  -- ok = tick(st); if (ok == 0) return 0;
  apply WPC.seq; wpc_step
  apply WPC.seq; rl_ite_case
  · wpc_auto; rl_done
  apply WPC.skip; wpc_simp
  -- hdr = ...; code = hdr & 0xff; n = (hdr >> 8) & 0xff; wn = hdr >> 16; m = mask64(w); base = st->sp;
  apply WPC.seq; wpc_step
  apply WPC.seq; wpc_step
  apply WPC.seq
  refine WPC.assign_band (by rfl) ?_
  intro n hn
  wpc_simp
  have hn' : n.toNat ≤ 255 := by simpa using hn
  apply WPC.seq; wpc_step
  apply WPC.seq; wpc_step
  apply WPC.seq; wpc_step
  rl_name "base" => base
  name_bud st1 w1 mm1 hb1
  -- if (code == BV_VAL) { ok = poly_lit_val(st, w, id); if (ok != 0) { ...; return ok; } }
  refine rl_join (A := A) (K := 40) (fun e e' => ∃ v : BitVec 32, e' = e.set "ok" (.u32 v)) hb1 ?_ ?_
  · apply WPC.ite_any
    · apply WPC.seq; wpc_step
      apply WPC.ite_any
      · wpc_auto; rl_done
      · apply WPC.skip
        simp only [CPost.shift_apply]
        refine ⟨⟨?rlv1, ?rleq1⟩, _, _, ‹Budget _ _ _ _›, ?_, ?_⟩
        case rleq1 => rfl
        all_goals first | cost_arith | cost_simp
    · apply WPC.skip
      simp only [CPost.shift_apply]
      refine ⟨⟨?rlv2, ?rleq2⟩, _, _, ‹Budget _ _ _ _›, ?_, ?_⟩
      case rleq2 => rfl
      all_goals first | cost_arith | cost_simp
  rintro env2 st2 k2 w2 mm2 ⟨v2, rfl⟩ hb2 hk2 hkm2
  simp only [Env.set, String.reduceEq, ↓reduceIte]
  -- if (code == BV_ADD && wn == w) { ... return 1; }: the sum of the children
  apply WPC.seq; apply WPC.ite_any
  · apply WPC.seq; wpc_step
    apply WPC.seq; rl_ite_case
    · wpc_auto; rl_done
    apply WPC.skip; wpc_simp
    apply WPC.seq; wpc_step
    name_bud st3 w3 mm3 hb3
    cost_clean
    apply WPC.seq
    apply WPC.while
      (I := fun env' st' k => ∃ (hdr code wn a b mid i ok : BitVec 32) (mv kv : BitVec 64),
        env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("w", .u32, .u32 w), ("id", .u32, .u32 id),
          ("depth", .u32, .u32 d), ("hdr", .u32, .u32 hdr), ("code", .u32, .u32 code), ("n", .u32, .u32 n),
          ("wn", .u32, .u32 wn), ("a", .u32, .u32 a), ("b", .u32, .u32 b), ("base", .u32, .u32 base),
          ("mid", .u32, .u32 mid), ("i", .u32, .u32 i), ("ok", .u32, .u32 ok), ("m", .u64, .u64 mv),
          ("k", .u64, .u64 kv)] ∧
        i.toNat ≤ n.toNat ∧ ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
        k.t + A * w'.toNat ≤ A * w3.toNat ∧ k.m + mm'.toNat ≤ mm3.toNat)
      (μ := fun env' _ => envU32 env' "i")
    · exact ⟨_, _, _, _, _, _, _, _, _, _, rfl, by simp, w3, mm3, hb3, by simp, by simp⟩
    rintro env' st' k ⟨hdr', code', wn', a', b', mid', i', ok', mv', kv', rfl, hin, w', mm', hb', hk, hkm⟩
    embc_simp
    refine ⟨fun hz => ?_, fun hpos => ?_⟩
    · wpc_auto
      rl_done
    have hi0 : 0 < i'.toNat := by
      have : i'.toNat ≠ 0 := fun e => hpos (BitVec.eq_of_toNat_eq (by simpa using e))
      omega
    have hi1 : (i' - 1#32).toNat = i'.toNat - 1 := by rw [BitVec.toNat_sub]; simp; omega
    apply WPC.seq; wpc_step
    apply WPC.seq; wpc_step
    apply WPC.seq; wpc_step
    apply WPC.seq; apply WPC.ite_any
    have _hbc := ‹Budget _ _ _ _›
    refine WPC.call_shape (fn := linF) (hf := rfl) (hps := rfl) ?_
    intro _vs1 _hargs _hbp
    obtain ⟨_v0, _vs2, _h0, _hargs1, rfl⟩ := evalArgs_cons' _hargs
    simp only [evalE, Env.get, ↓reduceIte, Option.some.injEq] at _h0
    subst _h0
    obtain ⟨_v1, _vs3, _e1, -, _hbp1⟩ := bindParams_ne_none_cons _hbp
    simp only [List.cons.injEq] at _e1
    obtain ⟨rfl, rfl⟩ := _e1
    obtain ⟨_v2, _vs4, rfl, _ht2, _hbp2⟩ := bindParams_ne_none_cons _hbp1
    obtain ⟨_w', rfl⟩ := Mem.hasTy_u32_inv _ht2
    obtain ⟨_v3, _vs5, rfl, _ht3, _hbp3⟩ := bindParams_ne_none_cons _hbp2
    obtain ⟨_x', rfl⟩ := Mem.hasTy_u32_inv _ht3
    obtain ⟨_v4, _vs6, rfl, _ht4, _hbp4⟩ := bindParams_ne_none_cons _hbp3
    obtain ⟨_d', rfl⟩ := Mem.hasTy_u32_inv _ht4
    obtain rfl := bindParams_ne_none_nil _hbp4
    obtain ⟨_a1, _t1, -, _hv1, _he1⟩ := evalArgs_cons' _hargs1
    obtain ⟨_a2, _t2, -, _hv2, _he2⟩ := evalArgs_cons' _hv1
    obtain ⟨_a3, _t3, _h3, _hv3, _he3⟩ := evalArgs_cons' _hv2
    simp [evalArgs] at _hv3
    subst _hv3
    simp only [List.cons.injEq] at _he1
    obtain ⟨-, rfl⟩ := _he1
    simp only [List.cons.injEq] at _he2
    obtain ⟨-, rfl⟩ := _he2
    simp only [List.cons.injEq] at _he3
    obtain ⟨rfl, -⟩ := _he3
    simp [evalE, evalBin, evalArith, Env.get] at _h3
    subst _h3
    refine ⟨_, _, IH, ⟨⟨⟨_w', _x', _, rfl⟩, _, _, _hbc⟩, ?_⟩, ?_⟩
    · simp [depthArg]
      omega
    rintro _rv _st3 _c3 ⟨_w3, _mm3, _hb3, _hc3, _hm3⟩
    rw [Budget.wk _hbc] at _hc3
    rw [Budget.mk _hbc] at _hm3
    wpc_dst
    rotate_left
    wpc_step
    all_goals (apply WPC.seq; rl_ite_case; (· wpc_auto; rl_done); apply WPC.skip; wpc_simp)
    all_goals (apply WPC.seq; wpc_step)
    all_goals (rl_ite_case; (· wpc_auto; rl_done); apply WPC.skip; wpc_simp)
    all_goals
      cost_clean
      refine ⟨?_, _, _, _, _, _, _, i' - 1#32, ⟨_, _, _, rfl⟩, by omega, _, _, ‹Budget _ _ _ _›, ?_, ?_⟩
      · simp only [envU32, Env.get, String.reduceEq, ↓reduceIte, hi1]; omega
      · cost_arith
      · cost_arith
  apply WPC.skip; wpc_simp
  -- if (code == BV_SUB && n == 2) { a = ..; b = ..; if (...) { b, scale, a, add; return } }
  name_bud st4 w4 mm4 hb4
  refine rl_join (A := A) (K := 20)
    (fun e e' => ∃ u v : BitVec 32, e' = (e.set "a" (.u32 u)).set "b" (.u32 v)) hb4 ?_ ?_
  · apply WPC.ite_any
    · apply WPC.seq; wpc_step
      apply WPC.seq; wpc_step
      apply WPC.ite_any
      · apply WPC.seq
        have _hbc := ‹Budget _ _ _ _›
        refine WPC.call_shape (fn := linF) (hf := rfl) (hps := rfl) ?_
        intro _vs1 _hargs _hbp
        obtain ⟨_v0, _vs2, _h0, _hargs1, rfl⟩ := evalArgs_cons' _hargs
        simp only [evalE, Env.get, ↓reduceIte, Option.some.injEq] at _h0
        subst _h0
        obtain ⟨_v1, _vs3, _e1, -, _hbp1⟩ := bindParams_ne_none_cons _hbp
        simp only [List.cons.injEq] at _e1
        obtain ⟨rfl, rfl⟩ := _e1
        obtain ⟨_v2, _vs4, rfl, _ht2, _hbp2⟩ := bindParams_ne_none_cons _hbp1
        obtain ⟨_w', rfl⟩ := Mem.hasTy_u32_inv _ht2
        obtain ⟨_v3, _vs5, rfl, _ht3, _hbp3⟩ := bindParams_ne_none_cons _hbp2
        obtain ⟨_x', rfl⟩ := Mem.hasTy_u32_inv _ht3
        obtain ⟨_v4, _vs6, rfl, _ht4, _hbp4⟩ := bindParams_ne_none_cons _hbp3
        obtain ⟨_d', rfl⟩ := Mem.hasTy_u32_inv _ht4
        obtain rfl := bindParams_ne_none_nil _hbp4
        obtain ⟨_a1, _t1, -, _hv1, _he1⟩ := evalArgs_cons' _hargs1
        obtain ⟨_a2, _t2, -, _hv2, _he2⟩ := evalArgs_cons' _hv1
        obtain ⟨_a3, _t3, _h3, _hv3, _he3⟩ := evalArgs_cons' _hv2
        simp [evalArgs] at _hv3
        subst _hv3
        simp only [List.cons.injEq] at _he1
        obtain ⟨-, rfl⟩ := _he1
        simp only [List.cons.injEq] at _he2
        obtain ⟨-, rfl⟩ := _he2
        simp only [List.cons.injEq] at _he3
        obtain ⟨rfl, -⟩ := _he3
        simp [evalE, evalBin, evalArith, Env.get] at _h3
        subst _h3
        refine ⟨_, _, IH, ⟨⟨⟨_w', _x', _, rfl⟩, _, _, _hbc⟩, ?_⟩, ?_⟩
        · simp [depthArg]
          omega
        rintro _rv _st3 _c3 ⟨_w3, _mm3, _hb3, _hc3, _hm3⟩
        rw [Budget.wk _hbc] at _hc3
        rw [Budget.mk _hbc] at _hm3
        wpc_dst
        apply WPC.seq; rl_ite_case
        · wpc_auto; rl_done
        apply WPC.skip; wpc_simp
        rl_spend_scale
        apply WPC.seq; wpc_step
        apply WPC.seq
        have _hbc := ‹Budget _ _ _ _›
        refine WPC.call_shape (fn := linF) (hf := rfl) (hps := rfl) ?_
        intro _vs1 _hargs _hbp
        obtain ⟨_v0, _vs2, _h0, _hargs1, rfl⟩ := evalArgs_cons' _hargs
        simp only [evalE, Env.get, ↓reduceIte, Option.some.injEq] at _h0
        subst _h0
        obtain ⟨_v1, _vs3, _e1, -, _hbp1⟩ := bindParams_ne_none_cons _hbp
        simp only [List.cons.injEq] at _e1
        obtain ⟨rfl, rfl⟩ := _e1
        obtain ⟨_v2, _vs4, rfl, _ht2, _hbp2⟩ := bindParams_ne_none_cons _hbp1
        obtain ⟨_w', rfl⟩ := Mem.hasTy_u32_inv _ht2
        obtain ⟨_v3, _vs5, rfl, _ht3, _hbp3⟩ := bindParams_ne_none_cons _hbp2
        obtain ⟨_x', rfl⟩ := Mem.hasTy_u32_inv _ht3
        obtain ⟨_v4, _vs6, rfl, _ht4, _hbp4⟩ := bindParams_ne_none_cons _hbp3
        obtain ⟨_d', rfl⟩ := Mem.hasTy_u32_inv _ht4
        obtain rfl := bindParams_ne_none_nil _hbp4
        obtain ⟨_a1, _t1, -, _hv1, _he1⟩ := evalArgs_cons' _hargs1
        obtain ⟨_a2, _t2, -, _hv2, _he2⟩ := evalArgs_cons' _hv1
        obtain ⟨_a3, _t3, _h3, _hv3, _he3⟩ := evalArgs_cons' _hv2
        simp [evalArgs] at _hv3
        subst _hv3
        simp only [List.cons.injEq] at _he1
        obtain ⟨-, rfl⟩ := _he1
        simp only [List.cons.injEq] at _he2
        obtain ⟨-, rfl⟩ := _he2
        simp only [List.cons.injEq] at _he3
        obtain ⟨rfl, -⟩ := _he3
        simp [evalE, evalBin, evalArith, Env.get] at _h3
        subst _h3
        refine ⟨_, _, IH, ⟨⟨⟨_w', _x', _, rfl⟩, _, _, _hbc⟩, ?_⟩, ?_⟩
        · simp [depthArg]
          omega
        rintro _rv _st3 _c3 ⟨_w3, _mm3, _hb3, _hc3, _hm3⟩
        rw [Budget.wk _hbc] at _hc3
        rw [Budget.mk _hbc] at _hm3
        wpc_dst
        apply WPC.seq; rl_ite_case
        · wpc_auto; rl_done
        apply WPC.skip; wpc_simp
        wpc_auto
        rl_done
      · apply WPC.skip
        simp only [CPost.shift_apply]
        refine ⟨⟨?su1, ?sv1, ?seq1⟩, _, _, ‹Budget _ _ _ _›, ?_, ?_⟩
        case seq1 => rfl
        all_goals first | cost_arith | cost_simp
    · apply WPC.skip
      simp only [CPost.shift_apply]
      refine ⟨⟨?su2, ?sv2, ?seq2⟩, _, _, ‹Budget _ _ _ _›, ?_, ?_⟩
      case seq2 => rfl
      all_goals first | cost_arith | cost_simp
  rintro env5 st5 k5 w5 mm5 ⟨u5, v5, rfl⟩ hb5 hk5 hkm5
  simp only [Env.set, String.reduceEq, ↓reduceIte]
  -- if (code == BV_NEG && n == 1) { a = ..; if (...) { a; scale; return 1; } }
  refine rl_join (A := A) (K := 20) (fun e e' => ∃ u : BitVec 32, e' = e.set "a" (.u32 u)) hb5 ?_ ?_
  · apply WPC.ite_any
    · apply WPC.seq; wpc_step
      apply WPC.ite_any
      · apply WPC.seq
        have _hbc := ‹Budget _ _ _ _›
        refine WPC.call_shape (fn := linF) (hf := rfl) (hps := rfl) ?_
        intro _vs1 _hargs _hbp
        obtain ⟨_v0, _vs2, _h0, _hargs1, rfl⟩ := evalArgs_cons' _hargs
        simp only [evalE, Env.get, ↓reduceIte, Option.some.injEq] at _h0
        subst _h0
        obtain ⟨_v1, _vs3, _e1, -, _hbp1⟩ := bindParams_ne_none_cons _hbp
        simp only [List.cons.injEq] at _e1
        obtain ⟨rfl, rfl⟩ := _e1
        obtain ⟨_v2, _vs4, rfl, _ht2, _hbp2⟩ := bindParams_ne_none_cons _hbp1
        obtain ⟨_w', rfl⟩ := Mem.hasTy_u32_inv _ht2
        obtain ⟨_v3, _vs5, rfl, _ht3, _hbp3⟩ := bindParams_ne_none_cons _hbp2
        obtain ⟨_x', rfl⟩ := Mem.hasTy_u32_inv _ht3
        obtain ⟨_v4, _vs6, rfl, _ht4, _hbp4⟩ := bindParams_ne_none_cons _hbp3
        obtain ⟨_d', rfl⟩ := Mem.hasTy_u32_inv _ht4
        obtain rfl := bindParams_ne_none_nil _hbp4
        obtain ⟨_a1, _t1, -, _hv1, _he1⟩ := evalArgs_cons' _hargs1
        obtain ⟨_a2, _t2, -, _hv2, _he2⟩ := evalArgs_cons' _hv1
        obtain ⟨_a3, _t3, _h3, _hv3, _he3⟩ := evalArgs_cons' _hv2
        simp [evalArgs] at _hv3
        subst _hv3
        simp only [List.cons.injEq] at _he1
        obtain ⟨-, rfl⟩ := _he1
        simp only [List.cons.injEq] at _he2
        obtain ⟨-, rfl⟩ := _he2
        simp only [List.cons.injEq] at _he3
        obtain ⟨rfl, -⟩ := _he3
        simp [evalE, evalBin, evalArith, Env.get] at _h3
        subst _h3
        refine ⟨_, _, IH, ⟨⟨⟨_w', _x', _, rfl⟩, _, _, _hbc⟩, ?_⟩, ?_⟩
        · simp [depthArg]
          omega
        rintro _rv _st3 _c3 ⟨_w3, _mm3, _hb3, _hc3, _hm3⟩
        rw [Budget.wk _hbc] at _hc3
        rw [Budget.mk _hbc] at _hm3
        wpc_dst
        apply WPC.seq; rl_ite_case
        · wpc_auto; rl_done
        apply WPC.skip; wpc_simp
        rl_spend_scale
        wpc_auto
        rl_done
      · apply WPC.skip
        simp only [CPost.shift_apply]
        refine ⟨⟨?nu1, ?neq1⟩, _, _, ‹Budget _ _ _ _›, ?_, ?_⟩
        case neq1 => rfl
        all_goals first | cost_arith | cost_simp
    · apply WPC.skip
      simp only [CPost.shift_apply]
      refine ⟨⟨?nu2, ?neq2⟩, _, _, ‹Budget _ _ _ _›, ?_, ?_⟩
      case neq2 => rfl
      all_goals first | cost_arith | cost_simp
  rintro env6 st6 k6 w6 mm6 ⟨u6, rfl⟩ hb6 hk6 hkm6
  simp only [Env.set, String.reduceEq, ↓reduceIte]
  -- if (code == BV_MUL && n == 2) { a = ..; b = ..; if (...) { two tries with a literal factor } }
  refine rl_join (A := A) (K := 100)
    (fun e e' => ∃ u v z : BitVec 32, e' = ((e.set "a" (.u32 u)).set "b" (.u32 v)).set "ok" (.u32 z)) hb6 ?_ ?_
  · apply WPC.ite_any
    · apply WPC.seq; wpc_step
      apply WPC.seq; wpc_step
      apply WPC.ite_any
      · apply WPC.seq; wpc_step
        apply WPC.seq; apply WPC.ite_any
        · apply WPC.seq; wpc_step
          apply WPC.seq
          have _hbc := ‹Budget _ _ _ _›
          refine WPC.call_shape (fn := linF) (hf := rfl) (hps := rfl) ?_
          intro _vs1 _hargs _hbp
          obtain ⟨_v0, _vs2, _h0, _hargs1, rfl⟩ := evalArgs_cons' _hargs
          simp only [evalE, Env.get, ↓reduceIte, Option.some.injEq] at _h0
          subst _h0
          obtain ⟨_v1, _vs3, _e1, -, _hbp1⟩ := bindParams_ne_none_cons _hbp
          simp only [List.cons.injEq] at _e1
          obtain ⟨rfl, rfl⟩ := _e1
          obtain ⟨_v2, _vs4, rfl, _ht2, _hbp2⟩ := bindParams_ne_none_cons _hbp1
          obtain ⟨_w', rfl⟩ := Mem.hasTy_u32_inv _ht2
          obtain ⟨_v3, _vs5, rfl, _ht3, _hbp3⟩ := bindParams_ne_none_cons _hbp2
          obtain ⟨_x', rfl⟩ := Mem.hasTy_u32_inv _ht3
          obtain ⟨_v4, _vs6, rfl, _ht4, _hbp4⟩ := bindParams_ne_none_cons _hbp3
          obtain ⟨_d', rfl⟩ := Mem.hasTy_u32_inv _ht4
          obtain rfl := bindParams_ne_none_nil _hbp4
          obtain ⟨_a1, _t1, -, _hv1, _he1⟩ := evalArgs_cons' _hargs1
          obtain ⟨_a2, _t2, -, _hv2, _he2⟩ := evalArgs_cons' _hv1
          obtain ⟨_a3, _t3, _h3, _hv3, _he3⟩ := evalArgs_cons' _hv2
          simp [evalArgs] at _hv3
          subst _hv3
          simp only [List.cons.injEq] at _he1
          obtain ⟨-, rfl⟩ := _he1
          simp only [List.cons.injEq] at _he2
          obtain ⟨-, rfl⟩ := _he2
          simp only [List.cons.injEq] at _he3
          obtain ⟨rfl, -⟩ := _he3
          simp [evalE, evalBin, evalArith, Env.get] at _h3
          subst _h3
          refine ⟨_, _, IH, ⟨⟨⟨_w', _x', _, rfl⟩, _, _, _hbc⟩, ?_⟩, ?_⟩
          · simp [depthArg]
            omega
          rintro _rv _st3 _c3 ⟨_w3, _mm3, _hb3, _hc3, _hm3⟩
          rw [Budget.wk _hbc] at _hc3
          rw [Budget.mk _hbc] at _hm3
          wpc_dst
          apply WPC.seq; rl_ite_case
          · wpc_auto; rl_done
          apply WPC.skip; wpc_simp
          rl_spend_scale
          wpc_auto
          rl_done
        apply WPC.skip; wpc_simp
        apply WPC.seq; wpc_step
        apply WPC.ite_any
        · apply WPC.seq; wpc_step
          apply WPC.seq
          have _hbc := ‹Budget _ _ _ _›
          refine WPC.call_shape (fn := linF) (hf := rfl) (hps := rfl) ?_
          intro _vs1 _hargs _hbp
          obtain ⟨_v0, _vs2, _h0, _hargs1, rfl⟩ := evalArgs_cons' _hargs
          simp only [evalE, Env.get, ↓reduceIte, Option.some.injEq] at _h0
          subst _h0
          obtain ⟨_v1, _vs3, _e1, -, _hbp1⟩ := bindParams_ne_none_cons _hbp
          simp only [List.cons.injEq] at _e1
          obtain ⟨rfl, rfl⟩ := _e1
          obtain ⟨_v2, _vs4, rfl, _ht2, _hbp2⟩ := bindParams_ne_none_cons _hbp1
          obtain ⟨_w', rfl⟩ := Mem.hasTy_u32_inv _ht2
          obtain ⟨_v3, _vs5, rfl, _ht3, _hbp3⟩ := bindParams_ne_none_cons _hbp2
          obtain ⟨_x', rfl⟩ := Mem.hasTy_u32_inv _ht3
          obtain ⟨_v4, _vs6, rfl, _ht4, _hbp4⟩ := bindParams_ne_none_cons _hbp3
          obtain ⟨_d', rfl⟩ := Mem.hasTy_u32_inv _ht4
          obtain rfl := bindParams_ne_none_nil _hbp4
          obtain ⟨_a1, _t1, -, _hv1, _he1⟩ := evalArgs_cons' _hargs1
          obtain ⟨_a2, _t2, -, _hv2, _he2⟩ := evalArgs_cons' _hv1
          obtain ⟨_a3, _t3, _h3, _hv3, _he3⟩ := evalArgs_cons' _hv2
          simp [evalArgs] at _hv3
          subst _hv3
          simp only [List.cons.injEq] at _he1
          obtain ⟨-, rfl⟩ := _he1
          simp only [List.cons.injEq] at _he2
          obtain ⟨-, rfl⟩ := _he2
          simp only [List.cons.injEq] at _he3
          obtain ⟨rfl, -⟩ := _he3
          simp [evalE, evalBin, evalArith, Env.get] at _h3
          subst _h3
          refine ⟨_, _, IH, ⟨⟨⟨_w', _x', _, rfl⟩, _, _, _hbc⟩, ?_⟩, ?_⟩
          · simp [depthArg]
            omega
          rintro _rv _st3 _c3 ⟨_w3, _mm3, _hb3, _hc3, _hm3⟩
          rw [Budget.wk _hbc] at _hc3
          rw [Budget.mk _hbc] at _hm3
          wpc_dst
          apply WPC.seq; rl_ite_case
          · wpc_auto; rl_done
          apply WPC.skip; wpc_simp
          rl_spend_scale
          wpc_auto
          rl_done
        · apply WPC.skip
          simp only [CPost.shift_apply]
          refine ⟨⟨?mu1, ?mv1, ?mz1, ?meq1⟩, _, _, ‹Budget _ _ _ _›, ?_, ?_⟩
          case meq1 => rfl
          all_goals first | cost_arith | cost_simp
      · apply WPC.skip
        simp only [CPost.shift_apply]
        refine ⟨⟨?mu2, ?mv2, ?mz2, ?meq2⟩, _, _, ‹Budget _ _ _ _›, ?_, ?_⟩
        case meq2 => rfl
        all_goals first | cost_arith | cost_simp
    · apply WPC.skip
      simp only [CPost.shift_apply]
      refine ⟨⟨?mu3, ?mv3, ?mz3, ?meq3⟩, _, _, ‹Budget _ _ _ _›, ?_, ?_⟩
      case meq3 => rfl
      all_goals first | cost_arith | cost_simp
  rintro env7 st7 k7 w7 mm7 ⟨u7, v7, z7, rfl⟩ hb7 hk7 hkm7
  simp only [Env.set, String.reduceEq, ↓reduceIte]
  -- ok = lin_atom(st, id, m); return ok;
  wpc_auto
  rl_done


theorem lin_f_cost (sb A : Nat) (hA : 400 ≤ A) (w id d : BitVec 32) :
    FnCost (State := State) prog "lin_f" (BudPre sb [.ptr sb 0, .u32 w, .u32 id, .u32 d])
      (Amort sb A (allowFail 0#32 3000 100) 0 (slackUnless 0#32 100)) :=
  FnCost.mono (rl_lin_f_cost sb A hA) (fun _ _ ⟨h, hb⟩ => ⟨⟨w, id, d, h⟩, hb⟩)
    (fun _ _ _ _ _ _ h => h)

fncost_register "lin_f" linF lin_f_cost

theorem r_poly_norm_cost (sb A : Nat) (hA : 400 ≤ A) (np na : BitVec 32) :
    FnCost (State := State) prog "r_poly_norm" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow 7000) 0 noSlack) := by
  apply FnCost.intro (fn := rPolyNorm) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body rPolyNorm
  have hA6 : 6 ≤ A := by omega
  apply WPC.seq; apply WPC.ite_any
  · wpc_auto; rl_done
  apply WPC.skip; wpc_simp
  apply WPC.seq; wpc_step
  iterate 2
    apply WPC.seq; apply WPC.ite_any
    · wpc_auto; rl_done
    apply WPC.skip; wpc_simp
  apply WPC.seq; wpc_step
  apply WPC.seq; wpc_step
  apply WPC.seq; wpc_step
  apply WPC.seq; apply WPC.ite_any
  · wpc_auto; rl_done
  apply WPC.skip; wpc_simp
  apply WPC.seq; wpc_step
  -- the two normal forms
  iterate 2
    apply WPC.seq; wpc_step
    apply WPC.seq; rl_ite_case
    · wpc_auto; rl_done
    apply WPC.skip; wpc_simp
    try (apply WPC.seq; wpc_step)
  -- n = mid - base; if (st->sp - mid != n) return NOID; ok = spend(st, n); if (ok == 0) return NOID;
  apply WPC.seq; apply WPC.ite_any
  · wpc_auto; rl_done
  apply WPC.skip; wpc_simp
  apply WPC.seq; wpc_step
  apply WPC.seq; rl_ite_case
  · wpc_auto; rl_done
  apply WPC.skip; wpc_simp
  -- the comparison: at most `n` iterations, paid by the spend of `n`
  rl_name "base" => base
  rl_name "mid" => mid
  rl_name "e" => e
  rl_name "a" => a
  rl_name "b" => b
  rl_name "w" => w
  rl_name "ok" => ok
  name_bud st3 w3 mm3 hb3
  cost_clean
  have hpay : 10 * (mid - base).toNat ≤ A * (mid - base).toNat := Nat.mul_le_mul_right _ (by omega)
  apply WPC.seq
  apply WPC.while
    (I := fun env' st' k => st' = st3 ∧ ∃ i : BitVec 32,
      env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("np", .u32, .u32 np), ("na", .u32, .u32 na),
        ("e", .u32, .u32 e), ("a", .u32, .u32 a), ("b", .u32, .u32 b), ("w", .u32, .u32 w),
        ("base", .u32, .u32 base), ("mid", .u32, .u32 mid), ("n", .u32, .u32 (mid - base)),
        ("i", .u32, .u32 i), ("ok", .u32, .u32 ok)] ∧
      i.toNat ≤ (mid - base).toNat ∧ k.t ≤ 10 * i.toNat ∧ k.m = 0)
    (μ := fun env' _ => (mid - base).toNat - envU32 env' "i")
  · exact ⟨rfl, 0#32, rfl, by simp, by simp, by simp⟩
  rintro env' st' k ⟨hst, i, rfl, hin, hk, hkm⟩
  subst hst
  embc_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · wpc_auto
    rl_done
  have hlt' : i.toNat < (mid - base).toNat := by simpa [BitVec.lt_def] using hlt
  have hi1 : (i + 1#32).toNat = i.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
  apply WPC.seq; apply WPC.ite_any
  · wpc_auto
    rl_done
  apply WPC.skip; wpc_simp
  apply WPC.assign
  simp only [evalE, Env.get, String.reduceEq, ↓reduceIte, evalBin, evalArith, Env.assign, Env.ty,
    Mem.hasTy_u32]
  dsimp only [CPost.shift]
  have hmb : (mid - base).toNat = (4294967296 - base.toNat + mid.toNat) % 4294967296 := by
    rw [BitVec.toNat_sub]
  refine ⟨?_, rfl, i + 1#32, by simp [Env.set], by omega, ?_, hkm, ?_⟩
  · simp only [envU32, Env.get, Env.set, String.reduceEq, ↓reduceIte, hi1]; omega
  · cost_arith
  · first | cost_arith | cost_simp

fncost_register "r_poly_norm" rPolyNorm r_poly_norm_cost

/-! ## The bit-blast helpers `bb_add`/`bb_neg`/`bb_atom`/`bb_term` call (not in the
call graph of the task: their signatures span two lines) -/

theorem bb_ripple_cost (sb A : Nat) (xb nx yb ny rb nr init : BitVec 32) :
    FnCost (State := State) prog "bb_ripple"
      (BudPre sb [.ptr sb 0, .u32 xb, .u32 nx, .u32 yb, .u32 ny, .u32 rb, .u32 nr, .u32 init])
      (Amort sb A (allow (100 * nx.toNat + 50)) 0 noSlack) := by
  apply FnCost.intro (fn := bbRipple) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body bbRipple
  apply WPC.seq
  apply WPC.ite_any
  · wpc_auto; wpc_done
  apply WPC.skip
  wpc_simp
  apply WPC.seq
  apply WPC.while
    (I := fun env' st' k => ∃ i a b r s c pa pb pc ok : BitVec 32,
      env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("xb", .u32, .u32 xb), ("nx", .u32, .u32 nx),
        ("yb", .u32, .u32 yb), ("ny", .u32, .u32 ny), ("rb", .u32, .u32 rb), ("nr", .u32, .u32 nr),
        ("init", .u32, .u32 init), ("i", .u32, .u32 i), ("a", .u32, .u32 a), ("b", .u32, .u32 b),
        ("r", .u32, .u32 r), ("s", .u32, .u32 s), ("c", .u32, .u32 c), ("pa", .u32, .u32 pa),
        ("pb", .u32, .u32 pb), ("pc", .u32, .u32 pc), ("ok", .u32, .u32 ok)] ∧
      i.toNat ≤ nx.toNat ∧ ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
      k.t + A * w'.toNat ≤ A * w0.toNat + 100 * i.toNat ∧ k.m + mm'.toNat ≤ mm.toNat)
    (μ := fun env' _ => nx.toNat - envU32 env' "i")
  · exact ⟨0#32, 0#32, 0#32, 0#32, 0#32, 0#32, 0#32, 0#32, 0#32, 0#32, rfl, by simp, w0, mm, hb, by simp,
      by simp⟩
  rintro env' st' k ⟨i, a, b, r, s, c, pa, pb, pc, ok, rfl, hin, w', mm', hb', hk, hkm⟩
  embc_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · wpc_auto
    wpc_done
  have hlt' : i.toNat < nx.toNat := by simpa [BitVec.lt_def] using hlt
  have hi1 : (i + 1#32).toNat = i.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
  wpc_auto
  wpc_done
  all_goals mid_next hi1

fncost_register "bb_ripple" bbRipple bb_ripple_cost

theorem bb_sub_cost (sb A : Nat) (hA : 300 ≤ A) (xb nx yb ny bsb nb : BitVec 32) :
    FnCost (State := State) prog "bb_sub" (BudPre sb [.ptr sb 0, .u32 xb, .u32 nx, .u32 yb, .u32 ny, .u32 bsb, .u32 nb])
      (Amort sb A (allow (20 * nb.toNat + 100 * nx.toNat + 400)) 0 noSlack) := by
  have hA100 : 100 ≤ A := by omega
  apply FnCost.intro (fn := bbSub) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body bbSub
  wpc_auto
  rl_done

fncost_register "bb_sub" bbSub bb_sub_cost

theorem bb_ult_cost (sb A : Nat) (weq lb nl rb nr res : BitVec 32) :
    FnCost (State := State) prog "bb_ult" (BudPre sb [.ptr sb 0, .u32 weq, .u32 lb, .u32 nl, .u32 rb, .u32 nr, .u32 res])
      (Amort sb A (allow (60 * nl.toNat + 100)) 0 noSlack) := by
  apply FnCost.intro (fn := bbUlt) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body bbUlt
  apply WPC.seq
  apply WPC.ite_any
  · wpc_auto; wpc_done
  apply WPC.skip
  wpc_simp
  apply WPC.seq; wpc_step
  apply WPC.seq; wpc_step
  -- the walk down from the top bit: `i` from `nl` down to 1
  apply WPC.seq
  apply WPC.while
    (I := fun env' st' k => ∃ i l r cur cl cr ok : BitVec 32,
      env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("weq", .u32, .u32 weq), ("lb", .u32, .u32 lb),
        ("nl", .u32, .u32 nl), ("rb", .u32, .u32 rb), ("nr", .u32, .u32 nr), ("res", .u32, .u32 res),
        ("i", .u32, .u32 i), ("l", .u32, .u32 l), ("r", .u32, .u32 r), ("cur", .u32, .u32 cur),
        ("cl", .u32, .u32 cl), ("cr", .u32, .u32 cr), ("ok", .u32, .u32 ok)] ∧
      i.toNat ≤ nl.toNat ∧ ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
      k.t + A * w'.toNat ≤ A * w0.toNat + 60 * (nl.toNat - i.toNat) ∧ k.m + mm'.toNat ≤ mm.toNat)
    (μ := fun env' _ => envU32 env' "i")
  · exact ⟨_, 0#32, 0#32, _, 0#32, 0#32, 0#32, rfl, by simp, w0, mm, hb, by simp, by simp⟩
  rintro env' st' k ⟨i, l, r, cur, cl, cr, ok, rfl, hin, w', mm', hb', hk, hkm⟩
  embc_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · wpc_auto
    rl_done
  have hlt' : 1 < i.toNat := by simpa [BitVec.lt_def] using hlt
  have hi1 : (i - 1#32).toNat = i.toNat - 1 := by rw [BitVec.toNat_sub]; simp; omega
  wpc_auto
  wpc_done
  all_goals mid_next hi1

fncost_register "bb_ult" bbUlt bb_ult_cost

theorem bb_slt_cost (sb A : Nat) (weq lb nl rb nr res : BitVec 32) :
    FnCost (State := State) prog "bb_slt" (BudPre sb [.ptr sb 0, .u32 weq, .u32 lb, .u32 nl, .u32 rb, .u32 nr, .u32 res])
      (Amort sb A (allow (60 * nl.toNat + 200)) 0 noSlack) := by
  apply FnCost.intro (fn := bbSlt) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body bbSlt
  apply WPC.seq
  apply WPC.ite_any
  · wpc_auto; wpc_done
  apply WPC.skip
  wpc_simp
  apply WPC.seq; apply WPC.ite; embc_simp; constructor
  · intro _; wpc_auto; wpc_done
  intro hnl
  have hnl' : 2 ≤ nl.toNat := by have := BitVec.le_def.mp hnl; simpa using this
  have hn1 : (nl - 1#32).toNat = nl.toNat - 1 := by rw [BitVec.toNat_sub]; simp; omega
  apply WPC.skip; wpc_simp
  wpc_auto
  all_goals (try rl_args)
  rl_done

fncost_register "bb_slt" bbSlt bb_slt_cost

theorem bb_shift_limit_cost (sb A : Nat) (hA : 100 ≤ A) (cond arith xb nx bsb nb : BitVec 32) :
    FnCost (State := State) prog "bb_shift_limit"
      (BudPre sb [.ptr sb 0, .u32 cond, .u32 arith, .u32 xb, .u32 nx, .u32 bsb, .u32 nb])
      (Amort sb A (allow 100) 0 noSlack) := by
  apply FnCost.intro (fn := bbShiftLimit) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body bbShiftLimit
  have hA6 : 6 ≤ A := by omega
  apply WPC.seq; wpc_step
  apply WPC.seq
  apply WPC.while
    (I := fun env' st' k => ∃ base i b ok : BitVec 32,
      env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("cond", .u32, .u32 cond), ("arith", .u32, .u32 arith),
        ("xb", .u32, .u32 xb), ("nx", .u32, .u32 nx), ("bsb", .u32, .u32 bsb), ("nb", .u32, .u32 nb),
        ("base", .u32, .u32 base), ("i", .u32, .u32 i), ("b", .u32, .u32 b), ("ok", .u32, .u32 ok)] ∧
      i.toNat ≤ nb.toNat ∧ ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
      k.t + A * w'.toNat ≤ A * w0.toNat ∧ k.m + mm'.toNat ≤ mm.toNat)
    (μ := fun env' _ => nb.toNat - envU32 env' "i")
  · exact ⟨_, 0#32, 0#32, 0#32, rfl, by simp, w0, mm, hb, by simp, by simp⟩
  rintro env' st' k ⟨base, i, b, ok, rfl, hin, w', mm', hb', hk, hkm⟩
  embc_simp
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · wpc_auto
    wpc_done
  have hlt' : i.toNat < nb.toNat := by simpa [BitVec.lt_def] using hlt
  have hi1 : (i + 1#32).toNat = i.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
  apply WPC.seq; wpc_step
  iterate 2
    apply WPC.seq; apply WPC.ite_any
    · wpc_auto; wpc_done
    apply WPC.skip; wpc_simp
  apply WPC.seq; wpc_step
  apply WPC.seq; apply WPC.ite_any
  · wpc_auto; wpc_done
  apply WPC.skip; wpc_simp
  apply WPC.seq; wpc_step
  apply WPC.seq; wpc_ite_case
  · wpc_auto; wpc_done
  wpc_auto
  wpc_done
  all_goals mid_next hi1

fncost_register "bb_shift_limit" bbShiftLimit bb_shift_limit_cost

theorem bb_rsh_stage_cost (sb A : Nat) (hA : 100 ≤ A) (arith xb nx b t rb n : BitVec 32) :
    FnCost (State := State) prog "bb_rsh_stage"
      (BudPre sb [.ptr sb 0, .u32 arith, .u32 xb, .u32 nx, .u32 b, .u32 t, .u32 rb, .u32 n])
      (Amort sb A (allow (40 * n.toNat + 150)) 0 noSlack) := by
  apply FnCost.intro (fn := bbRshStage) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body bbRshStage
  have hA6 : 6 ≤ A := by omega
  apply WPC.seq
  wpc_step
  -- the pushes: each paid by its `push`
  apply WPC.seq
  apply WPC.while
    (I := fun env' st' c => ∃ base j r ok : BitVec 32,
      env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("arith", .u32, .u32 arith), ("xb", .u32, .u32 xb),
        ("nx", .u32, .u32 nx), ("b", .u32, .u32 b), ("t", .u32, .u32 t), ("rb", .u32, .u32 rb),
        ("n", .u32, .u32 n), ("base", .u32, .u32 base), ("j", .u32, .u32 j), ("r", .u32, .u32 r),
        ("ok", .u32, .u32 ok)] ∧
      j.toNat ≤ n.toNat ∧ ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
      c.t + A * w'.toNat ≤ A * w0.toNat ∧ c.m + mm'.toNat ≤ mm.toNat)
    (μ := fun env' _ => n.toNat - envU32 env' "j")
  · exact ⟨_, 0#32, 0#32, 0#32, rfl, by simp, w0, mm, hb, by simp, by simp⟩
  rintro env' st' c ⟨base, j, r, ok, rfl, hjn, w', mm', hb', hk, hkm⟩
  embc_simp
  refine ⟨fun hge => ?_, fun hlt => ?body⟩
  case body =>
    have hlt' : j.toNat < n.toNat := by simpa [BitVec.lt_def] using hlt
    have hj1 : (j + 1#32).toNat = j.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    apply WPC.seq; wpc_step
    apply WPC.seq; apply WPC.ite_any
    · wpc_auto; wpc_done
    apply WPC.skip; wpc_simp
    apply WPC.seq; apply WPC.ite_any
    all_goals (wpc_step)
    all_goals (apply WPC.seq; wpc_ite_case; (· wpc_auto; wpc_done); wpc_auto; wpc_done)
    all_goals mid_next hj1
  -- the checks
  apply WPC.seq; wpc_step
  name_bud st1 w1 mm1 hb1
  apply WPC.seq
  apply WPC.while
    (I := fun env2 st2 k2 => ∃ j r ok : BitVec 32,
      env2 = [("st", .ptr (.struct "ck"), .ptr sb 0), ("arith", .u32, .u32 arith), ("xb", .u32, .u32 xb),
        ("nx", .u32, .u32 nx), ("b", .u32, .u32 b), ("t", .u32, .u32 t), ("rb", .u32, .u32 rb),
        ("n", .u32, .u32 n), ("base", .u32, .u32 base), ("j", .u32, .u32 j), ("r", .u32, .u32 r),
        ("ok", .u32, .u32 ok)] ∧
      j.toNat ≤ n.toNat ∧ ∃ w' mm' : BitVec 32, Budget st2.mem sb w' mm' ∧
      k2.t + A * w'.toNat ≤ A * w1.toNat + 40 * j.toNat ∧ k2.m + mm'.toNat ≤ mm1.toNat)
    (μ := fun env2 _ => n.toNat - envU32 env2 "j")
  · exact ⟨0#32, _, _, rfl, by simp, w1, mm1, hb1, by simp, by simp⟩
  rintro env2 st2 k2 ⟨j2, r2, ok2, rfl, hjn2, w2, mm2, hb2, hk2, hkm2⟩
  embc_simp
  refine ⟨fun hge2 => ?_, fun hlt2 => ?_⟩
  · wpc_auto
    rl_done
  have hlt2' : j2.toNat < n.toNat := by simpa [BitVec.lt_def] using hlt2
  have hj21 : (j2 + 1#32).toNat = j2.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
  wpc_auto
  wpc_done
  all_goals mid_next hj21

fncost_register "bb_rsh_stage" bbRshStage bb_rsh_stage_cost

theorem bb_shift_cost (sb A : Nat) (hA : 100 ≤ A) (kind xb nx yb ny bsb nb : BitVec 32) :
    FnCost (State := State) prog "bb_shift"
      (BudPre sb [.ptr sb 0, .u32 kind, .u32 xb, .u32 nx, .u32 yb, .u32 ny, .u32 bsb, .u32 nb])
      (Amort sb A (allow (60 * ny.toNat + 1300 * nb.toNat + 8000)) 0 noSlack) := by
  apply FnCost.intro (fn := bbShift) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body bbShift
  have hA6 : 6 ≤ A := by omega
  -- if (kind == 2) arith = 1;
  refine WPC.ite_assign_join (by rfl) ⟨0#32, by simp [Env.set]⟩ ?_
  intro arith kArith hkArith hkmArith
  wpc_simp
  -- if (nb == 0) return 0; b0 = ...; if (...) return 0; cond = ...; wb = st->sp;
  apply WPC.seq; apply WPC.ite_any
  · wpc_auto; wpc_done
  apply WPC.skip; wpc_simp
  apply WPC.seq; wpc_step
  apply WPC.seq; apply WPC.ite_any
  · wpc_auto; wpc_done
  apply WPC.skip; wpc_simp
  apply WPC.seq; wpc_step
  apply WPC.seq; wpc_step
  rl_name "b0" => b0
  rl_name "cond" => cond
  rl_name "wb" => wb
  name_bud st1 w1 mm1 hb1
  -- the bits of `nx`: each pushed, each push pays
  apply WPC.seq
  apply WPC.while
    (I := fun env' st' c => ∃ i bit res ok : BitVec 32,
      env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("kind", .u32, .u32 kind), ("xb", .u32, .u32 xb),
        ("nx", .u32, .u32 nx), ("yb", .u32, .u32 yb), ("ny", .u32, .u32 ny), ("bsb", .u32, .u32 bsb),
        ("nb", .u32, .u32 nb), ("arith", .u32, .u32 arith), ("b0", .u32, .u32 b0), ("cond", .u32, .u32 cond),
        ("wb", .u32, .u32 wb), ("i", .u32, .u32 i), ("bit", .u32, .u32 bit), ("res", .u32, .u32 res),
        ("ok", .u32, .u32 ok)] ∧
      i.toNat ≤ ny.toNat ∧ ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
      c.t + A * w'.toNat ≤ A * w1.toNat ∧ c.m + mm'.toNat ≤ mm1.toNat)
    (μ := fun env' _ => ny.toNat - envU32 env' "i")
  · exact ⟨0#32, 0#32, 0#32, 0#32, rfl, by simp, w1, mm1, hb1, by simp, by simp⟩
  rintro env' st' c ⟨i, bit, res, ok, rfl, hin, w', mm', hb', hk, hkm⟩
  embc_simp
  refine ⟨fun hge => ?_, fun hlt => ?body⟩
  case body =>
    have hlt' : i.toNat < ny.toNat := by simpa [BitVec.lt_def] using hlt
    have hi1 : (i + 1#32).toNat = i.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    apply WPC.seq; wpc_step
    refine WPC.ite_assign_join (by rfl) ⟨0#32, by simp [Env.set]⟩ ?_
    intro bit2 kBit hkBit hkmBit
    wpc_simp
    apply WPC.seq; apply WPC.ite_any
    all_goals wpc_step
    all_goals (apply WPC.seq; wpc_ite_case; (· wpc_auto; wpc_done); wpc_auto; wpc_done)
    all_goals mid_next hi1
  -- ok = bb_ult(...); res = bb_shift_limit(...); i = bb_log2(nx);
  wpc_auto
  rl_done
  name_bud st2 w2 mm2 hb2
  cost_clean
  -- the stages: `i` from `bb_log2(nx)` down, each continuing iteration below 31
  obtain ⟨K, hK⟩ : ∃ K, K = 40 * nb.toNat + 200 := ⟨_, rfl⟩
  apply WPC.while
    (I := fun env' st' c => ∃ i bit res ok : BitVec 32,
      env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("kind", .u32, .u32 kind), ("xb", .u32, .u32 xb),
        ("nx", .u32, .u32 nx), ("yb", .u32, .u32 yb), ("ny", .u32, .u32 ny), ("bsb", .u32, .u32 bsb),
        ("nb", .u32, .u32 nb), ("arith", .u32, .u32 arith), ("b0", .u32, .u32 b0), ("cond", .u32, .u32 cond),
        ("wb", .u32, .u32 wb), ("i", .u32, .u32 i), ("bit", .u32, .u32 bit), ("res", .u32, .u32 res),
        ("ok", .u32, .u32 ok)] ∧
      ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
      c.t + A * w'.toNat ≤ A * w2.toNat + K * (31 - i.toNat) ∧ c.m + mm'.toNat ≤ mm2.toNat)
    (μ := fun env' _ => envU32 env' "i")
  · exact ⟨_, _, _, _, rfl, w2, mm2, hb2, by simp, by simp⟩
  rintro env' st' c ⟨i, bit, res, ok, rfl, w', mm', hb', hk, hkm⟩
  have hK31 : K * (31 - i.toNat) ≤ K * 31 := Nat.mul_le_mul_left _ (by omega)
  embc_simp
  refine ⟨fun hz => ?_, fun hpos => ?_⟩
  · wpc_auto
    rl_done
  have hi0 : 0 < i.toNat := by
    have : i.toNat ≠ 0 := fun e => hpos (BitVec.eq_of_toNat_eq (by simpa using e))
    omega
  have hi1 : (i - 1#32).toNat = i.toNat - 1 := by rw [BitVec.toNat_sub]; simp; omega
  apply WPC.seq; wpc_step
  apply WPC.seq; apply WPC.ite_any
  · wpc_auto; rl_done
  apply WPC.skip; wpc_simp
  apply WPC.seq; apply WPC.ite; embc_simp; constructor
  · intro _; wpc_auto; rl_done
  intro h31
  have h31' : (i - 1#32).toNat < 31 := by
    have := BitVec.lt_def.mp (BitVec.not_le.mp (by simpa using h31)); simpa using this
  have hstep : K * (31 - i.toNat) + K = K * (31 - (i - 1#32).toNat) := by
    rw [show 31 - (i - 1#32).toNat = (31 - i.toNat) + 1 by omega, Nat.mul_succ]
  apply WPC.skip; wpc_simp
  apply WPC.seq; apply WPC.ite_any
  all_goals wpc_step
  all_goals (try rl_args)
  all_goals (apply WPC.ite_any; (· wpc_auto; rl_done); apply WPC.skip; wpc_simp)
  all_goals
    cost_clean
    refine ⟨?_, i - 1#32, ⟨_, _, _, rfl⟩, _, _, ‹Budget _ _ _ _›, ?_, ?_⟩
    · simp only [envU32, Env.get, String.reduceEq, ↓reduceIte, hi1]; omega
    · cost_arith
    · cost_arith

fncost_register "bb_shift" bbShift bb_shift_cost

/-! ## `bb_neg`, `bb_add`, `bb_atom`, `bb_term`, `r_bitblast` -/

theorem bb_neg_cost (sb A : Nat) (hA : 300 ≤ A) (xb nx bsb nb : BitVec 32) :
    FnCost (State := State) prog "bb_neg" (BudPre sb [.ptr sb 0, .u32 xb, .u32 nx, .u32 bsb, .u32 nb])
      (Amort sb A (allow (120 * nb.toNat + 500)) 0 noSlack) := by
  have hA100 : 100 ≤ A := by omega
  apply FnCost.intro (fn := bbNeg) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body bbNeg
  iterate 2
    apply WPC.seq; wpc_step
    apply WPC.seq; rl_ite_case
    · wpc_auto; rl_done
    apply WPC.skip; wpc_simp
  wpc_auto
  rl_done
  all_goals
    name_bud st1 w1 mm1 hb1
    cost_clean
    rl_name "pre" => pre
    rl_name "adder" => adder
    rl_name "ok" => ok
    apply WPC.while
      (I := fun env' st' k => ∃ i : BitVec 32,
        env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("xb", .u32, .u32 xb), ("nx", .u32, .u32 nx),
          ("bsb", .u32, .u32 bsb), ("nb", .u32, .u32 nb), ("pre", .u32, .u32 pre),
          ("adder", .u32, .u32 adder), ("i", .u32, .u32 i), ("ok", .u32, .u32 ok)] ∧
        i.toNat ≤ nb.toNat ∧ ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
        k.t + A * w'.toNat ≤ A * w1.toNat + 10 * i.toNat ∧ k.m + mm'.toNat ≤ mm1.toNat)
      (μ := fun env' _ => nb.toNat - envU32 env' "i")
    · exact ⟨0#32, rfl, by simp, w1, mm1, hb1, by simp, by simp⟩
    rintro env' st' k ⟨i, rfl, hin, w', mm', hb', hk, hkm⟩
    embc_simp
    refine ⟨fun hge => ?_, fun hlt => ?_⟩
    · wpc_auto
      rl_done
    have hlt' : i.toNat < nb.toNat := by simpa [BitVec.lt_def] using hlt
    have hi1 : (i + 1#32).toNat = i.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    wpc_auto
    wpc_done
    all_goals mid_next hi1

fncost_register "bb_neg" bbNeg bb_neg_cost

theorem bb_atom_cost (sb A : Nat) (hA : 100 ≤ A) (a b : BitVec 32) :
    FnCost (State := State) prog "bb_atom" (BudPre sb [.ptr sb 0, .u32 a, .u32 b])
      (Amort sb A (allow 20000) 0 noSlack) := by
  apply FnCost.intro (fn := bbAtom) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body bbAtom
  wpc_auto
  rl_done

fncost_register "bb_atom" bbAtom bb_atom_cost

theorem bb_add_cost (sb A : Nat) (hA : 300 ≤ A) (a bsb nb : BitVec 32) :
    FnCost (State := State) prog "bb_add" (BudPre sb [.ptr sb 0, .u32 a, .u32 bsb, .u32 nb])
      (Amort sb A (allow (20500 * nb.toNat + 82000)) 0 noSlack) := by
  have hA100 : 100 ≤ A := by omega
  apply FnCost.intro (fn := bbAdd) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body bbAdd
  apply WPC.seq
  refine WPC.assign_band (by rfl) ?_
  intro n hn
  wpc_simp
  have hn' : n.toNat ≤ 255 := by simpa using hn
  apply WPC.seq; apply WPC.ite_any
  · wpc_auto; wpc_done
  apply WPC.skip; wpc_simp
  apply WPC.seq; wpc_step
  apply WPC.seq; wpc_step
  -- the operands from the last: `k` from `n` down to 1, one ripple check each
  obtain ⟨K, hK⟩ : ∃ K, K = 80 * nb.toNat + 320 := ⟨_, rfl⟩
  apply WPC.seq
  apply WPC.while
    (I := fun env' st' c => ∃ k x nx xb sb' pre ok : BitVec 32,
      env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("a", .u32, .u32 a), ("bsb", .u32, .u32 bsb),
        ("nb", .u32, .u32 nb), ("n", .u32, .u32 n), ("k", .u32, .u32 k), ("x", .u32, .u32 x),
        ("nx", .u32, .u32 nx), ("xb", .u32, .u32 xb), ("sb", .u32, .u32 sb'), ("pre", .u32, .u32 pre),
        ("i", .u32, .u32 0#32), ("ok", .u32, .u32 ok)] ∧
      k.toNat ≤ n.toNat ∧ ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
      c.t + A * w'.toNat ≤ A * w0.toNat + K * (n.toNat - k.toNat) ∧ c.m + mm'.toNat ≤ mm.toNat)
    (μ := fun env' _ => envU32 env' "k")
  · exact ⟨_, _, _, _, _, _, _, rfl, by simp, w0, mm, hb, by simp, by simp⟩
  rintro env' st' c ⟨k, x, nx, xb, sb', pre, ok, rfl, hkn, w', mm', hb', hk, hkm⟩
  have hK255 : K * (n.toNat - k.toNat) ≤ K * 255 := Nat.mul_le_mul_left _ (by omega)
  embc_simp
  refine ⟨fun hge => ?_, fun hlt => ?body⟩
  case body =>
    have hk1 : 1 < k.toNat := by simpa [BitVec.lt_def] using hlt
    have hkm1 : (k - 1#32).toNat = k.toNat - 1 := by rw [BitVec.toNat_sub]; simp; omega
    have hstep : K * (n.toNat - k.toNat) + K = K * (n.toNat - (k - 1#32).toNat) := by
      rw [show n.toNat - (k - 1#32).toNat = (n.toNat - k.toNat) + 1 by omega, Nat.mul_succ]
    iterate 3 (apply WPC.seq; wpc_step)
    apply WPC.seq; wpc_step
    apply WPC.seq; rl_ite_case
    · wpc_auto; rl_done
    apply WPC.skip; wpc_simp
    wpc_auto
    rl_done
    all_goals
      cost_clean
      refine ⟨?_, k - 1#32, ⟨_, _, _, _, _, _, rfl⟩, by omega, _, _, ‹Budget _ _ _ _›, ?_, ?_⟩
      · simp only [envU32, Env.get, String.reduceEq, ↓reduceIte, hkm1]; omega
      · cost_arith
      · cost_arith
  -- the last operand: compared bit by bit with the sum
  wpc_auto
  rl_done
  all_goals
    name_bud st1 w1 mm1 hb1
    cost_clean
    rl_name "x" => x2
    rl_name "nx" => nx2
    apply WPC.while
      (I := fun env2 st2 k2 => ∃ i2 : BitVec 32,
        env2 = [("st", .ptr (.struct "ck"), .ptr sb 0), ("a", .u32, .u32 a), ("bsb", .u32, .u32 bsb),
          ("nb", .u32, .u32 nb), ("n", .u32, .u32 n), ("k", .u32, .u32 k), ("x", .u32, .u32 x2),
          ("nx", .u32, .u32 nx2), ("xb", .u32, .u32 xb), ("sb", .u32, .u32 sb'), ("pre", .u32, .u32 pre),
          ("i", .u32, .u32 i2), ("ok", .u32, .u32 ok)] ∧
        i2.toNat ≤ nb.toNat ∧ ∃ w2 mm2 : BitVec 32, Budget st2.mem sb w2 mm2 ∧
        k2.t + A * w2.toNat ≤ A * w1.toNat + 10 * i2.toNat ∧ k2.m + mm2.toNat ≤ mm1.toNat)
      (μ := fun env2 _ => nb.toNat - envU32 env2 "i")
    · exact ⟨0#32, rfl, by simp, w1, mm1, hb1, by simp, by simp⟩
    rintro env2 st2 k2 ⟨i2, rfl, hin2, w2, mm2, hb2, hk2, hkm2⟩
    embc_simp
    refine ⟨fun hge2 => ?_, fun hlt2 => ?_⟩
    · wpc_auto
      rl_done
    have hlt2' : i2.toNat < nb.toNat := by simpa [BitVec.lt_def] using hlt2
    have hi21 : (i2 + 1#32).toNat = i2.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    wpc_auto
    wpc_done
    all_goals mid_next hi21

fncost_register "bb_add" bbAdd bb_add_cost

theorem bb_term_cost (sb A : Nat) (hA : 300 ≤ A) (a b : BitVec 32) :
    FnCost (State := State) prog "bb_term" (BudPre sb [.ptr sb 0, .u32 a, .u32 b])
      (Amort sb A (allow 5400000) 0 noSlack) := by
  have hA100 : 100 ≤ A := by omega
  apply FnCost.intro (fn := bbTerm) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body bbTerm
  wpc_auto
  rl_done
  all_goals
    name_bud st1 w1 mm1 hb1
    cost_clean
    rl_name "hdr" => hdr
    rl_name "n" => n
    rl_name "nb" => nb
    have hn' : n.toNat ≤ 255 := by
      have := ‹n.toNat ≤ 255 % 2 ^ 32›; simpa using this
    have hnb' : nb.toNat ≤ 255 := by
      have := ‹nb.toNat ≤ 255 % 2 ^ 32›; simpa using this
    apply WPC.while
      (I := fun env' st' k => ∃ i x : BitVec 32,
        env' = [("st", .ptr (.struct "ck"), .ptr sb 0), ("a", .u32, .u32 a), ("b", .u32, .u32 b),
          ("hdr", .u32, .u32 hdr), ("code", .u32, .u32 (hdr &&& 255#32)), ("n", .u32, .u32 n),
          ("nb", .u32, .u32 nb), ("i", .u32, .u32 i), ("x", .u32, .u32 x), ("y", .u32, .u32 0#32),
          ("nx", .u32, .u32 0#32), ("ny", .u32, .u32 0#32), ("bsb", .u32, .u32 0#32), ("xb", .u32, .u32 0#32),
          ("yb", .u32, .u32 0#32), ("ok", .u32, .u32 0#32)] ∧
        i.toNat ≤ n.toNat ∧ ∃ w' mm' : BitVec 32, Budget st'.mem sb w' mm' ∧
        k.t + A * w'.toNat ≤ A * w1.toNat + 10 * i.toNat ∧ k.m + mm'.toNat ≤ mm1.toNat)
      (μ := fun env' _ => n.toNat - envU32 env' "i")
    · exact ⟨0#32, 0#32, rfl, by simp, w1, mm1, hb1, by simp, by simp⟩
    rintro env' st' k ⟨i, x, rfl, hin, w', mm', hb', hk, hkm⟩
    embc_simp
    refine ⟨fun hge => ?_, fun hlt => ?_⟩
    · wpc_auto
      rl_done
    have hlt' : i.toNat < n.toNat := by simpa [BitVec.lt_def] using hlt
    have hi1 : (i + 1#32).toNat = i.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    wpc_auto
    wpc_done
    all_goals mid_next hi1

fncost_register "bb_term" bbTerm bb_term_cost

theorem r_bitblast_cost (sb A : Nat) (hA : 300 ≤ A) (np na : BitVec 32) :
    FnCost (State := State) prog "r_bitblast" (BudPre sb [.ptr sb 0, .u32 np, .u32 na])
      (Amort sb A (allow 5410000) 0 noSlack) := by
  have hA100 : 100 ≤ A := by omega
  apply FnCost.intro (fn := rBitblast) rfl
  rintro vs st ⟨rfl, w0, mm, hb⟩
  fncost_body rBitblast
  wpc_auto
  rl_done

fncost_register "r_bitblast" rBitblast r_bitblast_cost

end Vbcf.Proof
