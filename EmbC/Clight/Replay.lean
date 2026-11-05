import EmbC.Logic
import EmbC.Clight.World

/-!
# From oracle safety to contract safety

The checker's specifications quantify over certified oracles, and the Clight theorems quantify
over the contract semantics. This file connects the two in the direction those theorems need.
`replayOracle` answers each valid call with the next reply on a list, so a contract execution
is also an execution under the oracle that replays its replies. A contract failure is then a
failure under that oracle, and a contract result is a result under that oracle.
-/

namespace EmbC

namespace Oracle

/-- The same certified replies with another private state. -/
def transport {P : Prog} {S₀ S₁ : Type} (o : Oracle P S₀) (init : S₁) (g : S₁ → S₀)
    (f : S₁ → S₁) : Oracle P S₁ where
  state := init
  step call s := ⟨(o.step call (g s)).val.map (fun x => (x.1, f s)), by
    have hc := (o.step call (g s)).property
    generalize (o.step call (g s)).val = a at hc ⊢
    rcases call with ⟨operation, args, before⟩
    dsimp only at hc ⊢
    split at hc
    all_goals subst_vars
    all_goals repeat' split at hc
    all_goals first
      | (subst_vars; simp_all; done)
      | skip
    all_goals (obtain ⟨n, hn⟩ := hc)
    all_goals (try rcases hn with hn | hn)
    all_goals (try obtain ⟨w, hl, hn⟩ := hn)
    all_goals (try subst hn)
    all_goals first
      | (simp_all; done)
      | (split <;> first | contradiction | exact ⟨f s, .inr ⟨w, hl, rfl⟩⟩)⟩

theorem transport_val {P : Prog} {S₀ S₁ : Type} (o : Oracle P S₀) (init : S₁) (g : S₁ → S₀)
    (f : S₁ → S₁) (call : Kernel.Call) (s : S₁) :
    ((transport o init g f).step call s).val =
      (o.step call (g s)).val.map (fun x => (x.1, f s)) := rfl

/-- Answer a call with the next reply on the list when the contract allows that reply, and
with some allowed reply otherwise. Invalid calls have no answer, as every oracle's contract
requires. -/
noncomputable def replayOracle (P : Prog) (rs : List Kernel.Reply) :
    Oracle P (List Kernel.Reply) where
  state := rs
  step call s :=
    open Classical in
    match s with
    | r :: rest =>
      if h : Returns P call r then
        let o := h.choose_spec.choose
        (transport o rest (fun _ => o.state) (fun _ => rest)).step call s
      else
        let o := Classical.choice (exists_oracle P)
        (transport o s (fun _ => o.state) id).step call s
    | [] =>
      let o := Classical.choice (exists_oracle P)
      (transport o s (fun _ => o.state) id).step call s

theorem replayOracle_step_cons {P : Prog} {rs rest : List Kernel.Reply} {call : Kernel.Call}
    {r : Kernel.Reply} (h : Returns P call r) :
    ((replayOracle P rs).step call (r :: rest)).val = some (r, rest) := by
  obtain ⟨next, hn⟩ := h.choose_spec.choose_spec
  have hs : ((replayOracle P rs).step call (r :: rest)).val =
      (((h.choose_spec.choose).step call (h.choose_spec.choose).state).val).map
        (fun x => (x.1, rest)) := by
    simp only [replayOracle, h, ↓reduceDIte]
    rfl
  rw [hs, hn]
  rfl

end Oracle

namespace Clight

open Semantics in
/-- Forgetting a replaced oracle gives back the contract state. -/
theorem withOracle_unit {External : Type} (c : EmbC.Semantics.State) (o : External) :
    (c.withOracle o).withOracle () = c := by
  cases c <;> rfl

/-- A contract control step is the same step under any oracle. -/
theorem next_silent_lift {State : Type} {P : Prog} {c c' : Semantics.State}
    (o : Oracle P State) (h : Semantics.next P c = some (.silent c')) :
    Semantics.nextFor P (c.withOracle o) = some (.silent (c'.withOracle o)) := by
  cases c with
  | regular stmt env mem current k =>
    cases stmt <;> simp only [Semantics.nextFor, Semantics.next, Semantics.nextCore,
      Semantics.State.withOracle, Semantics.returnTarget] at h ⊢
    all_goals repeat' split at h
    all_goals try simp only [Option.map, Option.some.injEq,
      Semantics.Action.silent.injEq, reduceCtorEq] at h
    all_goals try subst c'
    all_goals simp_all
  | callstate f args mem current k =>
    cases f <;> simp only [Semantics.nextFor, Semantics.next, Semantics.nextCore,
      Semantics.State.withOracle] at h ⊢
    all_goals repeat' split at h
    all_goals try simp only [Option.some.injEq,
      Semantics.Action.silent.injEq, reduceCtorEq] at h
    all_goals try subst c'
    all_goals simp_all
  | returnstate result mem current k =>
    cases k <;> simp only [Semantics.nextFor, Semantics.next, Semantics.nextCore,
      Semantics.State.withOracle] at h ⊢
    all_goals repeat' split at h
    all_goals try simp only [Option.some.injEq,
      Semantics.Action.silent.injEq, reduceCtorEq] at h
    all_goals try subst c'
    all_goals simp_all

theorem run_of_next {State : Type} {P : Prog} {c : Semantics.ExecState P State}
    {a : Semantics.ExecAction P State} (h : Semantics.nextFor P c = some a) (fuel : Nat) :
    Semantics.run P (fuel + 1) c = Semantics.run P fuel a.target := by
  simp [Semantics.run, Semantics.runCore, h]

theorem run_replay_cons {P : Prog} {ext : Ext} {args : List Val} {m : Mem} {rest : List Kernel.Reply}
    {r : Kernel.Reply} (h : Oracle.Returns P ⟨ext, args, m⟩ r) :
    Ext.run P ext args ⟨m, Oracle.replayOracle P (r :: rest)⟩ =
      some (r.result, ⟨r.after, Oracle.replayOracle P rest⟩) := by
  have hs : ((Oracle.replayOracle P (r :: rest)).step ⟨ext, args, m⟩ (r :: rest)).val =
      some (r, rest) := Oracle.replayOracle_step_cons h
  simp only [Ext.run, Kernel.run]
  rw [show (Oracle.replayOracle P (r :: rest)).state = r :: rest from rfl, hs]
  rfl

/-- A contract execution is an execution under the oracle that replays its replies. -/
theorem replay_star {P : Prog} {obs : Semantics.Observations} {c d : Semantics.State}
    {trace : CC.Trace} (h : Behaviors.Star (Semantics.Step P obs) c trace d) :
    ∃ rs : List Kernel.Reply, ∀ tail, ∃ n, ∀ fuel,
      Semantics.run P (n + fuel) (c.withOracle (Oracle.replayOracle P (rs ++ tail))) =
        Semantics.run P fuel (d.withOracle (Oracle.replayOracle P tail)) := by
  induction h with
  | refl s => exact ⟨[], fun tail => ⟨0, fun fuel => by simp⟩⟩
  | step hs _ ih =>
    obtain ⟨rs, hrs⟩ := ih
    cases hs with
    | silent _ hn =>
      refine ⟨rs, fun tail => ?_⟩
      obtain ⟨n, hk⟩ := hrs tail
      refine ⟨n + 1, fun fuel => ?_⟩
      rw [Nat.add_right_comm, run_of_next (next_silent_lift _ hn)]
      exact hk fuel
    | external _ ext args st rv st' _ he _ =>
      obtain ⟨k, rfl, ha, rfl⟩ := he
      refine ⟨⟨rv, st'.mem⟩ :: rs, fun tail => ?_⟩
      obtain ⟨n, hk⟩ := hrs tail
      refine ⟨n + 1, fun fuel => ?_⟩
      rw [Nat.add_right_comm]
      have hnext : Semantics.nextFor P
          ((Semantics.State.call (.external ext) args st k).withOracle
            (Oracle.replayOracle P (⟨rv, st'.mem⟩ :: (rs ++ tail)))) =
          some (.external ext args ⟨st.mem, Oracle.replayOracle P (⟨rv, st'.mem⟩ :: (rs ++ tail))⟩
            rv ⟨st'.mem, Oracle.replayOracle P (rs ++ tail)⟩
            (.returned rv ⟨st'.mem, Oracle.replayOracle P (rs ++ tail)⟩ k)) := by
        simp only [Semantics.nextFor, Semantics.nextCore, Semantics.State.withOracle,
          run_replay_cons ha]
      exact (run_of_next hnext _).trans (hk fuel)

/-- A state with no contract step has no step under any oracle. -/
theorem nextFor_none_of_contract_stuck {State : Type} {P : Prog} {obs : Semantics.Observations}
    (ht : Semantics.ObservationsTotal obs) {d : Semantics.State}
    (hn : ∀ trace next, ¬ Semantics.Step P obs d trace next) (o : Oracle P State) :
    Semantics.nextFor P (d.withOracle o) = none := by
  cases hnext : Semantics.nextFor P (d.withOracle o) with
  | none => rfl
  | some action =>
    cases action with
    | silent target =>
      have hs := WorldSource.next_silent_contract hnext
      rw [withOracle_unit] at hs
      exact (hn _ _ (.silent _ _ hs)).elim
    | external ext args before result after target =>
      obtain ⟨k, hc, hrun, _⟩ := WorldSource.next_external_inv hnext
      have hret := Ext.run_spec hrun
      have hd : d = .call (.external ext) args ⟨before.mem, ()⟩ k := by
        have := congrArg (fun c => Semantics.State.withOracle c ()) hc
        simp only [withOracle_unit] at this
        exact this
      obtain ⟨trace, ho⟩ := ht P ext args ⟨before.mem, ()⟩ result ⟨after.mem, ()⟩ hret
      exact (hn trace _ (.external _ _ ext args ⟨before.mem, ()⟩ result ⟨after.mem, ()⟩ trace
        ⟨k, hd, hret, rfl⟩ ho)).elim

/-- A failed contract execution fails under the oracle that replays its replies. -/
theorem contract_wrong_replays {P : Prog} {obs : Semantics.Observations}
    (ht : Semantics.ObservationsTotal obs) {f : String} {args : List Val} {m : Mem}
    {trace : CC.Trace}
    (h : Behaviors.Behaves (sourceSemantics P obs) (Semantics.initial f args ⟨m, ()⟩)
      (.goesWrong trace)) :
    ∃ rs fuel, P.run fuel f args ⟨m, Oracle.replayOracle P rs⟩ = .stuck := by
  obtain ⟨d, hstar, hn, hfinal⟩ := h
  obtain ⟨rs, hrs⟩ := replay_star hstar
  obtain ⟨n, hk⟩ := hrs []
  refine ⟨rs, n + 1, ?_⟩
  have hk1 := hk 1
  simp only [List.append_nil] at hk1
  have hd : Semantics.run P 1 (d.withOracle (Oracle.replayOracle P [])) = .stuck := by
    have hnone := nextFor_none_of_contract_stuck ht hn (Oracle.replayOracle P [])
    simp only [Semantics.run, Semantics.runCore, hnone]
    cases d with
    | regular => rfl
    | callstate => rfl
    | returnstate rv mem w k =>
      cases k with
      | stop => exact (hfinal rv ⟨mem, w⟩ rfl).elim
      | _ => rfl
  exact hk1.trans hd

/-- A finished contract execution finishes the same way under the oracle that replays it. -/
theorem contract_terminates_replays {P : Prog} {obs : Semantics.Observations}
    {f : String} {args : List Val} {m : Mem} {trace : CC.Trace} {rv : Option Val}
    {st' : MachineStore}
    (h : Behaviors.Behaves (sourceSemantics P obs) (Semantics.initial f args ⟨m, ()⟩)
      (.terminates trace rv st')) :
    ∃ rs fuel o',
      P.run fuel f args ⟨m, Oracle.replayOracle P rs⟩ = .ok (rv, ⟨st'.mem, o'⟩) := by
  obtain ⟨d, hstar, hfinal⟩ := h
  obtain ⟨rs, hrs⟩ := replay_star hstar
  obtain ⟨n, hk⟩ := hrs []
  refine ⟨rs, n + 1, Oracle.replayOracle P [], ?_⟩
  have hk1 := hk 1
  simp only [List.append_nil] at hk1
  refine hk1.trans ?_
  change d = _ at hfinal
  subst d
  rfl

/-- **Oracle safety gives contract safety.** A function that gets stuck under no certified
oracle has no failing contract execution. -/
theorem contract_safe_of_oracle_safe {P : Prog} {obs : Semantics.Observations}
    (ht : Semantics.ObservationsTotal obs) {f : String} {args : List Val} {m : Mem}
    (hsafe : ∀ rs fuel, P.run fuel f args ⟨m, Oracle.replayOracle P rs⟩ ≠ .stuck) :
    SourceSafe P obs f args m := by
  intro trace h
  obtain ⟨rs, fuel, hrun⟩ := contract_wrong_replays ht h
  exact hsafe rs fuel hrun

/-- **A specification of an EmbC function holds of its Clight translation.** Suppose `F`
meets `pre`, `post` for every certified oracle, and `pre` holds of the initial memory and
arguments under every oracle. Under the assumptions of `embc_clight_behavior_equivalence`, no
Clight execution of `F` goes wrong, and every Clight execution that returns corresponds to an
EmbC execution under a certified oracle that satisfies `post`. -/
theorem clight_of_fnSpec (obs : Semantics.Observations)
    (hObservations : Semantics.ObservationsTotal obs)
    (hKernel : KernelCompatible obs) (hKernelBackward : KernelBackwardCompatible obs)
    (P : Prog) (cp : CC.Program) (hWellFormed : wellFormed P)
    (hTranslation : P.toClight = .ok cp) (f : String) (args : List Val) (m : Mem)
    (hentry : (P.findFn f).isSome = true) (hadm : Admissible P f args ⟨m, ()⟩)
    (j : MemoryInjection) (cm : CC.Mem) (cargs : List CC.Val)
    (hmem : memoryRel P j m cm) (hconst : ConstRel P cp.globalenv j m cm)
    (hargs : argsRel P m j args cargs)
    {pre : List Val → KernelState P (List Kernel.Reply) → Prop}
    {post : List Val → KernelState P (List Kernel.Reply) → Option Val →
      KernelState P (List Kernel.Reply) → Prop}
    (hspec : FnSpec (State := List Kernel.Reply) P f pre post)
    (hpre : ∀ o : Oracle P (List Kernel.Reply), pre args ⟨m, o⟩) :
    ∃ (b : CC.Block) (cf : CC.Function),
      CC.Genv.findSymbol cp.globalenv.genv_genv (CC.identOfString f) = some b ∧
      CC.Genv.findFunctPtr cp.globalenv.genv_genv b = some (.Internal cf) ∧
      (∀ trace, ¬ Behaviors.Behaves (targetSemantics cp)
        (.Callstate (.Internal cf) cargs .Kstop cm) (.goesWrong trace)) ∧
      (∀ trace value cm', Behaviors.Behaves (targetSemantics cp)
          (.Callstate (.Internal cf) cargs .Kstop cm) (.terminates trace value cm') →
        ∃ (o o' : Oracle P (List Kernel.Reply)) (rv : Option Val) (m' : Mem),
          post args ⟨m, o⟩ rv ⟨m', o'⟩ ∧
          ∃ j', j.Extends j' m ∧ retRel P m' j' rv value ∧ memoryRel P j' m' cm' ∧
            ConstRel P cp.globalenv j' m' cm') := by
  have hsafe : SourceSafe P obs f args m :=
    contract_safe_of_oracle_safe hObservations (fun rs fuel hrun => by
      have := hspec fuel args ⟨m, Oracle.replayOracle P rs⟩ (hpre _)
      rw [hrun] at this
      exact this)
  obtain ⟨b, cf, hb, hcf, _, hback⟩ :=
    embc_clight_behavior_equivalence obs hObservations hKernel hKernelBackward P cp
      hWellFormed hTranslation f args m hentry hadm hsafe j cm cargs hmem hconst hargs
  refine ⟨b, cf, hb, hcf, ?_, ?_⟩
  · intro trace hwrong
    obtain ⟨source, _, hmatch⟩ := hback _ hwrong
    cases source <;> simp [BehaviorMatches, Improves] at hmatch
  · intro trace value cm' hterm
    obtain ⟨source, hsource, hmatch⟩ := hback _ hterm
    cases source with
    | terminates strace rv st' =>
      obtain ⟨_, j', hext, hret, hm, hc⟩ := hmatch
      obtain ⟨rs, fuel, o', hrun⟩ := contract_terminates_replays hsource
      have hp := hspec fuel args ⟨m, Oracle.replayOracle P rs⟩ (hpre _)
      rw [hrun] at hp
      exact ⟨_, o', rv, st'.mem, hp, j', hext, hret, hm, hc⟩
    | diverges _ => exact hmatch.elim
    | reacts _ => exact hmatch.elim
    | goesWrong _ => exact hmatch.elim

end Clight

end EmbC
