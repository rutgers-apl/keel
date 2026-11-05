import EmbC.Clight.Proof.StepExec

/-!
# Simulation of continuation steps: statement outcomes and returns
-/

namespace EmbC.Clight.Proof

open EmbC EmbC.Clight

section Cont

variable {P : Prog} {cp : CC.Program} {obs : Semantics.Observations} {j0 : MemoryInjection}
  {m0 : Mem} {j : MemoryInjection} {cm : CC.Mem} {fn : Fn} {cf : CC.Function} {env : Env}
  {le : CC.TempEnv} {st : MachineStore} {k : Semantics.Cont} {K : CC.Cont} {s' : CC.Stmt}

/-- A normal outcome at the target position `Sskip`. -/
theorem normal_skip
    (had : AdmFrom P (.exec .skip env st k)) (hg : GInv P cp.globalenv j0 m0 j st.mem cm)
    (hfn : FnOK P fn cf) (hk : KR P st.mem j (some (fn, cf)) k K)
    (henv : EnvRel (fnContext P fn) st.mem j env le)
    {t : CC.Trace} {c' : Semantics.State} (hstep : Semantics.Step P obs (.exec .skip env st k) t c') :
    SimGoal P cp.globalenv j0 m0 (mu (.exec .skip env st k)) c'
      (.State cf .Sskip K CC.emptyEnv le cm) t := by
  cases hk with
  | @seq _ _ b k' b' K' hb hk' =>
    have hn : Semantics.next P (.exec .skip env st (.seq b k')) =
        some (.silent (.exec b env st k')) := rfl
    obtain ⟨rfl, rfl⟩ := step_silent hn hstep
    exact goal_plus (had.silent hn) hg (match_exec hfn (.exec hb hk') henv) (tplus_one rfl)
  | @seqSkip _ _ b k' _ hb hk' =>
    have hn : Semantics.next P (.exec .skip env st (.seq b k')) =
        some (.silent (.exec b env st k')) := rfl
    obtain ⟨rfl, rfl⟩ := step_silent hn hstep
    exact goal_stutter (had.silent hn) hg (match_exec hfn (.execSkip hb (.normal hk')) henv)
      (by simp only [mu, M]; omega)
  | @loop _ _ c body k' s1 K' hb hk' =>
    have hn : Semantics.next P (.exec .skip env st (.loop c body k')) =
        some (.silent (.exec (.while c body) env st k')) := rfl
    obtain ⟨rfl, rfl⟩ := step_silent hn hstep
    exact goal_plus (had.silent hn) hg (match_exec hfn (.exec hb hk') henv)
      (tplus_of_plus_star (tplus_one rfl) (tstar_one rfl))
  | @fn _ _ k' _ hk' =>
    cases hr : fn.ret with
    | none =>
      have hn : Semantics.next P (.exec .skip env st (.function fn.ret k')) =
          some (.silent (.returned none st k')) := by rw [hr]; rfl
      obtain ⟨rfl, rfl⟩ := step_silent hn hstep
      refine goal_plus (had.silent hn) hg (.inl ⟨.Vundef, K, rfl, hk', rfl⟩) ?_
      cases hk' <;> exact tplus_one rfl
    | some rt =>
      have hn : Semantics.next P (.exec .skip env st (.function fn.ret k')) = none := by
        rw [hr]; rfl
      exact (step_none hn hstep).elim

theorem outcome_normal
    (had : AdmFrom P (.exec .skip env st k)) (hg : GInv P cp.globalenv j0 m0 j st.mem cm)
    (hfn : FnOK P fn cf) (hpos : Pos P st.mem j fn cf (.normal k) s' K)
    (henv : EnvRel (fnContext P fn) st.mem j env le)
    {t : CC.Trace} {c' : Semantics.State} (hstep : Semantics.Step P obs (.exec .skip env st k) t c') :
    SimGoal P cp.globalenv j0 m0 (mu (.exec .skip env st k)) c'
      (.State cf s' K CC.emptyEnv le cm) t := by
  generalize heq : SPos.normal k = sp at hpos
  induction hpos with
  | exec hls hk =>
    cases heq
    obtain ⟨d, σ, σ', hls⟩ := hls
    cases hls
    exact normal_skip had hg hfn hk henv hstep
  | execSkip hls hp ih =>
    cases heq
    exact ih rfl
  | normal hk => cases heq; exact normal_skip had hg hfn hk henv hstep
  | @normalSeq b k' s' K hp ih =>
    cases heq
    have hn : Semantics.next P (.exec .skip env st (.seq b k')) =
        some (.silent (.exec b env st k')) := rfl
    obtain ⟨rfl, rfl⟩ := step_silent hn hstep
    exact goal_stutter (had.silent hn) hg (match_exec hfn hp henv) (by simp only [mu, M, W]; omega)
  | brk hk => cases heq

theorem outcome_brk
    (had : AdmFrom P (.exec .brk env st k)) (hg : GInv P cp.globalenv j0 m0 j st.mem cm)
    (hfn : FnOK P fn cf) (hpos : Pos P st.mem j fn cf (.brk k) s' K)
    (henv : EnvRel (fnContext P fn) st.mem j env le)
    {t : CC.Trace} {c' : Semantics.State} (hstep : Semantics.Step P obs (.exec .brk env st k) t c') :
    SimGoal P cp.globalenv j0 m0 (mu (.exec .brk env st k)) c'
      (.State cf s' K CC.emptyEnv le cm) t := by
  have hbrk : ∀ {K}, KR P st.mem j (some (fn, cf)) k K →
      SimGoal P cp.globalenv j0 m0 (mu (.exec .brk env st k)) c'
        (.State cf .Sbreak K CC.emptyEnv le cm) t := by
    intro K hk
    cases hk with
    | @seq _ _ b k' b' K' hb hk' =>
      have hn : Semantics.next P (.exec .brk env st (.seq b k')) =
          some (.silent (.exec .brk env st k')) := rfl
      obtain ⟨rfl, rfl⟩ := step_silent hn hstep
      exact goal_plus (had.silent hn) hg ⟨fn, cf, .Sbreak, K', le, hfn, .brk hk', henv, rfl⟩
        (tplus_one rfl)
    | @seqSkip _ _ b k' _ hb hk' =>
      have hn : Semantics.next P (.exec .brk env st (.seq b k')) =
          some (.silent (.exec .brk env st k')) := rfl
      obtain ⟨rfl, rfl⟩ := step_silent hn hstep
      exact goal_stutter (had.silent hn) hg ⟨fn, cf, .Sbreak, K, le, hfn, .brk hk', henv, rfl⟩
        (by simp only [mu, M]; omega)
    | @loop _ _ c body k' s1 K' hb hk' =>
      have hn : Semantics.next P (.exec .brk env st (.loop c body k')) =
          some (.silent (.exec .skip env st k')) := rfl
      obtain ⟨rfl, rfl⟩ := step_silent hn hstep
      exact goal_plus (had.silent hn) hg (match_normal hfn hk' henv) (tplus_one rfl)
    | @fn _ _ k' _ hk' =>
      have hn : Semantics.next P (.exec .brk env st (.function fn.ret k')) = none := by
        cases fn.ret <;> rfl
      exact (step_none hn hstep).elim

  cases hpos with
  | exec hls hk =>
    obtain ⟨d, σ, σ', hls⟩ := hls
    cases hls
    exact hbrk hk
  | execSkip hls hp =>
    obtain ⟨d, σ, σ', hls⟩ := hls
    cases hls
  | brk hk => exact hbrk hk

theorem returned_step {rv : Option Val} {T : CC.State}
    (had : AdmFrom P (.returned rv st k)) (hg : GInv P cp.globalenv j0 m0 j st.mem cm)
    (hmatch : MatchC P cp.globalenv st.mem j cm (.returned rv st k) T)
    {t : CC.Trace} {c' : Semantics.State} (hstep : Semantics.Step P obs (.returned rv st k) t c') :
    SimGoal P cp.globalenv j0 m0 (mu (.returned rv st k)) c' T t := by
  have hassign : ∀ {fn : Fn} {cf : CC.Function} {dst : Option Var} {env : Env} {le : CC.TempEnv} {w : CC.Val}, FnOK P fn cf →
      EnvRel (fnContext P fn) st.mem j env le → retRel P st.mem j rv w →
      ∀ {env'}, assignDst env st.mem dst rv = some env' →
      EnvRel (fnContext P fn) st.mem j env'
        (CC.setOpttemp (dst.map CC.identOfString) w le) := by
    intro fn cf dst env le w hfn henv hw env' ha
    have hc := ctxOK_fnContext (lowerFunction_inv hfn.low)
    cases dst with
    | none => simp only [assignDst, Option.some.injEq] at ha; subst ha; exact henv
    | some x =>
      cases rv with
      | none => simp [assignDst] at ha
      | some v =>
        simp only [assignDst] at ha
        obtain ⟨t', ht', hhas, rfl⟩ := env_assign_inv ha
        exact henv.set hc ht' (ValTy.of_hasTy hhas) hw
  rcases hmatch with ⟨w, K, hw, hk, rfl⟩ | ⟨fn, cf, dst, env, k', K, le, w, rfl, hfn, hk, henv, hw, rfl⟩
  · cases hk with
    | stop => exact (step_none rfl hstep).elim
    | @call fn cf dst env k' le K' hfn henv hk' =>
      generalize ha : assignDst env st.mem dst rv = oa
      rcases oa with _ | env'
      · have hn : Semantics.next P (.returned rv st (.call dst env k')) = none := by
          simp [Semantics.next, Semantics.nextCore, ha]
        exact (step_none hn hstep).elim
      have hn : Semantics.next P (.returned rv st (.call dst env k')) =
          some (.silent (.exec .skip env' st k')) := by simp [Semantics.next, Semantics.nextCore, ha]
      obtain ⟨rfl, rfl⟩ := step_silent hn hstep
      exact goal_plus (had.silent hn) hg (match_normal hfn hk' (hassign hfn henv hw ha))
        (tplus_one rfl)
  · generalize ha : assignDst env st.mem dst rv = oa
    rcases oa with _ | env'
    · have hn : Semantics.next P (.returned rv st (.call dst env k')) = none := by
        simp [Semantics.next, Semantics.nextCore, ha]
      exact (step_none hn hstep).elim
    have hn : Semantics.next P (.returned rv st (.call dst env k')) =
        some (.silent (.exec .skip env' st k')) := by simp [Semantics.next, Semantics.nextCore, ha]
    obtain ⟨rfl, rfl⟩ := step_silent hn hstep
    exact goal_stutter (had.silent hn) hg (match_normal hfn hk (hassign hfn henv hw ha))
      (by simp only [mu, W]; omega)

end Cont

end EmbC.Clight.Proof
