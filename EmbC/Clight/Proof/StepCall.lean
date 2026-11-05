import EmbC.Clight.Proof.StepCont

/-!
# Simulation of internal calls
-/

namespace EmbC.Clight.Proof

open EmbC EmbC.Clight

theorem LA_types {ctx : LCtx} : ∀ {σ es pre rs σ'}, LA ctx σ es pre rs σ' →
    ∀ r ∈ rs, CC.typeof r.ex = tyO r.ty := by
  intro σ es pre rs σ' h
  induction h with
  | nil => intro r hr; cases hr
  | cons he _ ih =>
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact (LE_static he).2
    · exact ih r hr

theorem hasTy_undef (m : Mem) (t : Ty) : m.hasTy .undef t = false := by cases t <;> rfl

theorem castsOK_of {ge : CC.CGenv} {cm : CC.Mem} {P : Prog} {m : Mem} {j : MemoryInjection}
    {le : CC.TempEnv} : ∀ {ps : List (Var × Ty)} {rs : List LX} {vs : List Val} {ws : List CC.Val}
    {penv : Env}, ArgsR ge cm P m j le rs vs ws → ArgsOK (ps.map (·.2)) rs →
    bindParams m ps vs = some penv → (∀ r ∈ rs, CC.typeof r.ex = tyO r.ty) →
    CastsOK cm rs (ps.map (fun p => type p.2)) ws
  | [], [], [], [], _, .nil, .nil, _, _ => .nil
  | (x, t) :: ps, r :: rs, v :: vs, w :: ws, penv, .cons _ hty hrel _ hr, .cons hacc hok, hb, hts => by
    simp only [bindParams] at hb
    split at hb
    · rename_i hhas
      generalize hb' : bindParams m ps vs = ob at hb
      rcases ob with _ | penv'
      · cases hb
      have hu : v ≠ .undef := by
        intro h; subst h; rw [hasTy_undef] at hhas; cases hhas
      refine .cons ?_ (castsOK_of hr hok hb' fun r' hr' => hts r' (.tail _ hr'))
      rw [hts r (.head _)]
      exact cast_accepts hrel hty hacc hu cm
    · cases hb
  | [], _ :: _, _, _, _, _, h, _, _ => by cases h
  | _ :: _, [], _, _, _, _, h, _, _ => by cases h

theorem typeOfFunction_lowered {P : Prog} {fn : Fn} {cf : CC.Function}
    (h : Priv.lowerFunction P fn = .ok cf) : CC.typeOfFunction cf = funTy fn := by
  obtain ⟨_, _, _, rfl⟩ := (lowerFunction_inv h).body
  simp [CC.typeOfFunction, CC.typeOfParams, funTy, List.map_map]

section Call

variable {P : Prog} {cp : CC.Program} {obs : Semantics.Observations} {j0 : MemoryInjection}
  {m0 : Mem} {j : MemoryInjection} {cm : CC.Mem} {fn : Fn} {cf : CC.Function} {env : Env}
  {le : CC.TempEnv} {st : MachineStore} {k : Semantics.Cont} {K : CC.Cont} {d : Nat} {σ σ' : LSt}
  {s' : CC.Stmt}

theorem exec_call (hs : SCtx P cp) {dst : Option Var} {f : String} {args : List EmbC.Expr}
    (had : AdmFrom P (.exec (.call dst f args) env st k))
    (hg : GInv P cp.globalenv j0 m0 j st.mem cm)
    (hfn : FnOK P fn cf) (hls : LS (fnContext P fn) d σ (.call dst f args) s' σ')
    (hk : KR P st.mem j (some (fn, cf)) k K) (henv : EnvRel (fnContext P fn) st.mem j env le)
    {t : CC.Trace} {c' : Semantics.State}
    (hstep : Semantics.Step P obs (.exec (.call dst f args) env st k) t c') :
    SimGoal P cp.globalenv j0 m0 (mu (.exec (.call dst f args) env st k)) c'
      (.State cf s' K CC.emptyEnv le cm) t := by
  cases hls with
  | @call _ _ _ _ _ fn' pre rs _ dst' hfind hla hargsok hdst =>
    have hfits := had.here
    have hx := xctx_of hs hfn hg.2.2.1 hg.2.2.2 hfits.1
    have hc := ctxOK_fnContext (lowerFunction_inv hfn.low)
    rw [hx.prog] at hfind
    generalize hva : evalArgs P env st.mem args = ova
    rcases ova with _ | vs
    · have hn : Semantics.next P (.exec (.call dst f args) env st k) = none := by
        simp [Semantics.next, Semantics.nextCore, hva]
      exact (step_none hn hstep).elim
    have hn : Semantics.next P (.exec (.call dst f args) env st k) =
        some (.silent (.call (.internal f) vs st (.call dst env k))) := by
      simp [Semantics.next, Semantics.nextCore, hva]
    obtain ⟨rfl, rfl⟩ := step_silent hn hstep
    by_cases hb : bindParams st.mem fn'.params vs = none
    · have hn2 : Semantics.next P (.call (.internal f) vs st (.call dst env k)) = none := by
        simp [Semantics.next, Semantics.nextCore, hfind, hb]
      refine goal_doom (n := 0) (had.silent hn) (.stuck ⟨hn2, by simp [Semantics.final], by simp [Semantics.KernelReady]⟩) ?_
      have := M_pos k
      simp only [mu, W]; omega
    obtain ⟨penv, hpenv⟩ := Option.ne_none_iff_exists'.mp hb
    obtain ⟨le', ws, prun, fr, hAR⟩ := args_sim hx hfits.2 hla henv hva
    have har := hAR le' (Agree.refl _ _ _)
    obtain ⟨hmem', hname⟩ := findFn_mem hfind
    obtain ⟨b, cf', hsym, hptr, hlow'⟩ := genv_find_fn hs.wf hs.low hmem'
    rw [hname] at hsym
    have hcasts := castsOK_of har hargsok hpenv (LA_types hla)
    have htype := typeOfFunction_lowered hlow'
    have hdst' : dst' = dst.map CC.identOfString := by
      rcases hdst with ⟨rfl, rfl⟩ | ⟨x, _, rfl, _, _, rfl⟩ <;> rfl
    subst hdst'
    refine goal_plus (had.silent hn) hg
      ⟨fn', cf', ws, _, hfind, ⟨hmem', hlow'⟩, argsR_rel har,
        KR.call hfn (henv.frame hc fr) hk, rfl⟩ ?_
    refine tplus_of_star_plus (prun.seq_star K) (tplus_one ?_)
    simp only [CC.doStep, funTy, CC.typeof, CC.Cop.classifyFun]
    rw [ev_evar_global hsym rfl, evalList_of har hcasts]
    have hff : CC.Genv.findFunct cp.globalenv.genv_genv (.Vptr b CC.Integers.Ptrofs.zero) =
        some (.Internal cf') := by
      have h0 : CC.Integers.Ptrofs.eq CC.Integers.Ptrofs.zero CC.Integers.Ptrofs.zero = true := by
        decide
      simp only [CC.Genv.findFunct, h0, ite_true, hptr]
    dsimp only
    rw [hff]
    have hty : CC.typeOfFundef (.Internal cf') = funTy fn' := htype
    simp only [funTy] at hty
    simp only [hty, ite_true]

end Call

end EmbC.Clight.Proof
