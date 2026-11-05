import EmbC.Clight.Proof.StepCall

/-!
# Simulation of kernel calls
-/

namespace EmbC.Clight.Proof

open EmbC EmbC.Clight

theorem ne_undef_acc {m : Mem} {v : Val} {t : Ty} {o : Option Ty} (hacc : Priv.accepts t o = true)
    (ho : ValTyO m v o) (ht : t ≠ .bpfptr) : v ≠ .undef := by
  cases o with
  | none => simp only [ValTyO] at ho; subst ho; intro h; cases h
  | some t' =>
    have : t' = t := by simpa [Priv.accepts] using hacc
    subst this
    exact ValTy.ne_undef_of_not_bpfptr ho ht

theorem cast_one {P : Prog} {m : Mem} {j : MemoryInjection} {cm : CC.Mem} {r : LX} {v : Val}
    {w : CC.Val} {t : Ty} (hts : CC.typeof r.ex = tyO r.ty) (hacc : Priv.accepts t r.ty = true)
    (hty : ValTyO m v r.ty) (hrel : valRel P m j v w) (hu : v ≠ .undef) :
    CC.Cop.semCast w (CC.typeof r.ex) (type t) cm = some w := by
  rw [hts]; exact cast_accepts hrel hty hacc hu cm

theorem kt_casts {ge : CC.CGenv} {cm : CC.Mem} {P : Prog} {m : Mem} {j : MemoryInjection}
    {le : CC.TempEnv} {ext : Ext} {rs : List LX} {types : List CC.Ty} {ret : Option Ty}
    {vs : List Val} {ws : List CC.Val} {st : MachineStore}
    (hkt : KT P ext rs types ret) (har : ArgsR ge cm P m j le rs vs ws)
    (hts : ∀ r ∈ rs, CC.typeof r.ex = tyO r.ty) (hdefined : Kernel.Defined P ⟨ext, vs, st.mem⟩) :
    CastsOK cm rs types ws := by
  cases hkt with
  | kvcalloc _ ha =>
    cases har with
    | cons _ ty1 rel1 _ har' =>
      cases har'
      exact .cons (cast_one (t := .u64) (hts _ (.head _)) ha ty1 rel1 (ne_undef_acc ha ty1 (by decide)))
        .nil
  | kzalloc => cases har; exact .nil
  | kvrealloc _ hp hn =>
    cases har with
    | cons _ ty1 rel1 _ har' =>
      cases har' with
      | cons _ ty2 rel2 _ har'' =>
        cases har''
        exact .cons (cast_one (hts _ (.head _)) hp ty1 rel1 (ne_undef_acc hp ty1 (by intro h; cases h)))
          (.cons (cast_one (t := .u64) (hts _ (.tail _ (.head _))) hn ty2 rel2
            (ne_undef_acc hn ty2 (by decide))) .nil)
  | kvfree hp =>
    cases har with
    | @cons r _ v _ w _ _ ty1 rel1 _ har' =>
      cases har'
      refine .cons ?_ .nil
      rw [hts _ (.head _)]
      obtain ⟨X, hX⟩ := pointerType_tyO hp
      rw [hX]
      apply cast_ptr_ptr
      rcases pointerType_val hp ty1 with rfl | ⟨b, off, rfl⟩
      · simp only [valRel] at rel1; subst rel1; exact .inr rfl
      · obtain ⟨_, _, rfl⟩ := rel1; exact .inl ⟨_, _, rfl⟩
  | copyFromBpfptr hd hs hn =>
    cases har with
    | @cons _ _ vd _ _ _ _ ty1 rel1 _ har' =>
      cases har' with
      | @cons _ _ vs' _ _ _ _ ty2 rel2 _ har'' =>
        cases har'' with
        | @cons _ _ vn _ _ _ _ ty3 rel3 _ har''' =>
          cases har'''
          have hu : vs' ≠ .undef := by
            intro h; subst h
            cases vd <;> cases vn <;> simp [Kernel.Defined] at hdefined
          exact .cons (cast_one (hts _ (.head _)) hd ty1 rel1 (ne_undef_acc hd ty1 (by decide)))
            (.cons (cast_one (hts _ (.tail _ (.head _))) hs ty2 rel2 hu)
              (.cons (cast_one (t := .u64) (hts _ (.tail _ (.tail _ (.head _)))) hn ty3 rel3
                (ne_undef_acc hn ty3 (by decide))) .nil))
  | signalPending => cases har; exact .nil
  | condResched => cases har; exact .nil

private theorem tstar_split {ge : CC.CGenv} {X Y : CC.State} {t : CC.Trace}
    (h : TStar ge X t Y) : (X = Y ∧ t = CC.E0) ∨ TPlus ge X t Y := by
  cases h with
  | refl => exact .inl ⟨rfl, rfl⟩
  | step a b => exact .inr (.intro a b)

section ECall

variable {P : Prog} {cp : CC.Program} {obs : Semantics.Observations} {j0 : MemoryInjection}
  {m0 : Mem} {j : MemoryInjection} {cm : CC.Mem} {fn : Fn} {cf : CC.Function} {env : Env}
  {le : CC.TempEnv} {st : MachineStore} {k : Semantics.Cont} {K : CC.Cont} {d : Nat} {σ σ' : LSt}
  {s' : CC.Stmt}

theorem exec_ecall (hs : SCtx P cp) {dst : Option Var}
    {ext : Ext} {args : List EmbC.Expr}
    (had : AdmFrom P (.exec (.ecall dst ext args) env st k))
    (hg : GInv P cp.globalenv j0 m0 j st.mem cm)
    (hfn : FnOK P fn cf) (hls : LS (fnContext P fn) d σ (.ecall dst ext args) s' σ')
    (hk : KR P st.mem j (some (fn, cf)) k K) (henv : EnvRel (fnContext P fn) st.mem j env le)
    {t : CC.Trace} {c' : Semantics.State}
    (hstep : Semantics.Step P obs (.exec (.ecall dst ext args) env st k) t c') :
    SimGoal P cp.globalenv j0 m0 (mu (.exec (.ecall dst ext args) env st k)) c'
      (.State cf s' K CC.emptyEnv le cm) t := by
  cases hls with
  | @ecall _ _ _ _ _ pre rs _ types ret dst' hla hkt hdst =>
    have hfits := had.here
    have hx := xctx_of hs hfn hg.2.2.1 hg.2.2.2 hfits.1
    have hc := ctxOK_fnContext (lowerFunction_inv hfn.low)
    generalize hva : evalArgs P env st.mem args = ova
    rcases ova with _ | vs
    · have hn : Semantics.next P (.exec (.ecall dst ext args) env st k) = none := by
        simp [Semantics.next, Semantics.nextCore, hva]
      exact (step_none hn hstep).elim
    have hn : Semantics.next P (.exec (.ecall dst ext args) env st k) =
        some (.silent (.call (.external ext) vs st (.call dst env k))) := by
      simp [Semantics.next, Semantics.nextCore, hva]
    obtain ⟨rfl, rfl⟩ := step_silent hn hstep
    classical
    by_cases hdefined : Kernel.Defined P ⟨ext, vs, st.mem⟩
    case neg =>
      have hf : Semantics.Failed P (.call (.external ext) vs st (.call dst env k)) := by
        refine ⟨by simp [Semantics.next, Semantics.nextCore], by simp [Semantics.final], ?_⟩
        cases st with
        | mk mem world =>
          cases world
          simpa [Semantics.KernelReady, Semantics.State.call] using hdefined
      exact goal_doom (n := 0) (had.silent hn) (.stuck hf)
        (by have := M_pos k; simp [mu, W]; omega)
    obtain ⟨le', ws, prun, fr, hAR⟩ := args_sim hx hfits.2 hla henv hva
    have har := hAR le' (Agree.refl _ _ _)
    have hcasts := kt_casts hkt har (LA_types hla) hdefined
    have hdst'' : dst' = dst.map CC.identOfString := by
      rcases hdst with ⟨rfl, rfl⟩ | ⟨x, _, rfl, _, _, rfl⟩ <;> rfl
    subst hdst''
    have hm : MatchC P cp.globalenv st.mem j cm
        (.call (.external ext) vs st (.call dst env k))
        (.State cf (.Sbuiltin (dst.map CC.identOfString) (kernelExternal ext) types (rs.map LX.ex))
          K CC.emptyEnv le' cm) :=
      ⟨fn, cf, dst, env, k, K, le', rs.map LX.ex, types, ws, rfl, hfn, hk,
        henv.frame hc fr, argsR_rel har,
        CC.doEvalExprlist_sound _ _ _ _ _ _ _ (evalList_of har hcasts), rfl⟩
    have hp : TStar cp.globalenv
        (.State cf (Priv.sequence pre
          (.Sbuiltin (dst.map CC.identOfString) (kernelExternal ext) types (rs.map LX.ex)))
          K CC.emptyEnv le cm) CC.E0
        (.State cf (.Sbuiltin (dst.map CC.identOfString) (kernelExternal ext) types (rs.map LX.ex))
          K CC.emptyEnv le' cm) := prun.seq_star K
    rcases tstar_split hp with ⟨heq, -⟩ | hp
    · rw [heq]
      exact goal_stutter (had.silent hn) hg hm (by have := M_pos k; simp [mu, W]; omega)
    · exact goal_plus (had.silent hn) hg hm hp

/-- The external outcome occurs between the shared call and return states.
Result binding belongs to the following return-state transition. -/
theorem external_step (hKernel : KernelCompatible obs) (hs : SCtx P cp)
    {ext : Ext} {vs : List Val} {ces : List CC.Expr} {types : List CC.Ty} {cargs : List CC.Val}
    {dst : Option Var}
    (had : AdmFrom P (.call (.external ext) vs st (.call dst env k)))
    (hg : GInv P cp.globalenv j0 m0 j st.mem cm)
    (hfn : FnOK P fn cf) (hk : KR P st.mem j (some (fn, cf)) k K)
    (henv : EnvRel (fnContext P fn) st.mem j env le)
    (hargs : argsRel P st.mem j vs cargs)
    (hev : CC.EvalExprlist cp.globalenv CC.emptyEnv le cm ces types cargs)
    {t : CC.Trace} {c' : Semantics.State}
    (hstep : Semantics.Step P obs (.call (.external ext) vs st (.call dst env k)) t c') :
    ∃ i' T', Rel P cp.globalenv j0 m0 i' c' T' ∧
      TExt cp.globalenv
        (.State cf (.Sbuiltin (dst.map CC.identOfString) (kernelExternal ext) types ces)
          K CC.emptyEnv le cm) t T' := by
  cases hstep with
  | silent _ hn => simp [Semantics.next, Semantics.nextCore] at hn
  | external _ ext' vs' before rv after _ he hobs =>
    obtain ⟨k0, hc, hallowed, rfl⟩ := he
    cases st with
    | mk mem world =>
      cases before with
      | mk mem' world' =>
        cases world
        cases world'
        simp only [Semantics.State.call, Semantics.State.callstate.injEq,
          Semantics.Callee.external.injEq, true_and] at hc
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hc
        have had' := had.external (after := after) hallowed
        obtain ⟨j', cm', crv, hext, hcall, hret, hmem', hconst'⟩ :=
          hKernel P cp.globalenv hs.cenv ext vs ⟨mem, ()⟩ rv after j cm cargs t
            hg.2.2.1 hg.2.2.2 hargs hallowed had'.here.1 hobs
        have hgrow := MemGrow.returns hallowed
        refine ⟨_, _, ⟨had', .inl ⟨rfl, j', cm', hg.update hgrow hext hmem' hconst', ?_⟩⟩,
          _, .refl _, CC.Step.builtin _ _ _ _ _ _ _ _ _ _ _ _ _ hev hcall⟩
        exact .inr ⟨fn, cf, dst, env, k, K, le, crv, rfl, hfn, hk.mono hgrow hext,
          henv.mono hgrow hext, hret, rfl⟩

end ECall

end EmbC.Clight.Proof
